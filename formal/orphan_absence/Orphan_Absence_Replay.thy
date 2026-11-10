(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Replay: re-applying a stream, duplicated events and
  re-emitted absence entries leave the replayed sink state unchanged, and
  the safety and convergence results of Orphan_Absence carry over to every
  in-order at-least-once delivery of the emission.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core) and
  to Orphan_Absence. Nothing in the archived development is modified.
*)
theory Orphan_Absence_Replay
  imports Orphan_Absence
begin

text \<open>
  The model applies an emitted stream once, in order. A real pipeline
  delivers at least once: a reader that restarts resumes from an earlier
  position of the same stream and applies some items again, and this can
  happen at every hop between the connector and the sink. This theory shows
  that re-reads of one fixed stream, in order, through any finite chain of
  such hops, to a sink that is not rolled back, do not change the state the
  sink ends in.

  A connector restart is a different case. The connector resumes from a
  committed offset before the crash point. The sink then applies the old
  stream up to the crash, then the log events between the committed offset
  and the crash again, without the old close entries, and then the
  re-executed chunks. For the re-executed chunks, safety follows from
  @{text absent_replay_safe} taken from the sink state at the resume point,
  since that theorem holds from any initial sink state. The theory
  @{text Orphan_Absence_Restart} states the stream across one restart as a whole.

  What is proved is the plain in-order sink: a block re-applied immediately
  after itself, or re-applied as part of an in-order replay to the end of
  the stream. The paper's idempotence of re-applying a chunk info record at
  a versioned sink (stored positions, a conditional range delete, range
  tombstones) is not backed here. The versioned mode stays outside the
  model. Results:

  \<^item> Idempotence: re-applying any suffix of an applied stream, re-applying a
    stream from any earlier prefix, repeating a block or a single event in
    place, and re-applying a unit's close block right after itself all leave
    the replayed state unchanged.
  \<^item> Re-emitting an absence entry for a key is a no-op when the stream's
    last event for the key is a delete, or when the stream has no event for
    the key and the initial sink state does not hold it. Without that
    hypothesis it is not a no-op: an absence entry re-emitted after an
    insert for the same key removes the row.
  \<^item> An in-order at-least-once reader is modeled by its cursor over the
    stream: it reads the event at the cursor and advances, or it rewinds the
    cursor to any earlier position, and it stops at the end of the stream.
    Whatever such a reader delivers replays to the same state as the stream
    itself, and so does any finite chain of such readers (multi-hop
    delivery).
  \<^item> Transfer: the safety theorem @{text absent_replay_safe} and the
    convergence theorem @{text self_stabilization} hold verbatim for every
    such delivery of the emission. In the per-key form, a key's result
    holds for every stream whose events for that key form such a delivery
    of the emission's events for that key. A keyed topic with several
    partitions, each delivered in order at least once, yields such streams
    for every key.

  Everything reduces to the per-key reading of the replay: the last event for
  a key decides, and absent any event the initial value persists. The core
  states this as @{thm [source] state_after_key}, with the two halves
  @{thm [source] state_after_last_event} (the key's last event decides) and
  @{thm [source] state_after_no_events} (no event, the initial value). This
  theory reuses them and does not restate them.

  Out-of-order re-delivery of one key's events is not in scope. A stale
  event delivered after a newer one for the same key, with no later re-read
  of the newer one, changes the state. The fixture at the end shows this,
  and shows that such a stream is outside the delivery class defined here.
  The paper leaves out-of-order delivery to the versioned mode, which is
  outside the model.
\<close>

subsection \<open>Re-applying a suffix, or restarting after an applied prefix, changes nothing\<close>

text \<open>
  A consumer that has applied a stream @{text xs} and then receives again
  any suffix of it, in order, ends in the state it was in. The suffix may be
  the whole stream. Note that @{text "suffix zs xs"} is the library's
  @{text "\<exists>ys. xs = ys @ zs"}.
\<close>

lemma replay_suffix_idempotent:
  assumes "suffix zs xs"
  shows "state_after (state_after D xs) zs = state_after D xs"
proof -
  obtain ys where xs: "xs = ys @ zs"
    using assms by (auto simp: suffix_def)
  have "state_after (state_after D xs) zs = state_after D (xs @ zs)"
    by (rule state_after_append[symmetric])
  also have "\<dots> = state_after D xs"
  proof (rule ext)
    fix k
    show "state_after D (xs @ zs) k = state_after D xs k"
    proof (cases "evs_for k zs = []")
      case True
      then show ?thesis
        by (rule state_after_append_no_k)
    next
      case False
      have ne_long: "evs_for k (xs @ zs) \<noteq> []"
        using False by simp
      have ne_xs: "evs_for k xs \<noteq> []"
        using False xs by simp
      have "state_after D (xs @ zs) k = ev_img (last (evs_for k (xs @ zs)))"
        by (rule state_after_last_event[OF ne_long])
      also have "\<dots> = ev_img (last (evs_for k zs))"
        using False by (simp add: last_append)
      also have "\<dots> = ev_img (last (evs_for k xs))"
        using False xs by (simp add: last_append)
      also have "\<dots> = state_after D xs k"
        by (rule state_after_last_event[OF ne_xs, symmetric])
      finally show ?thesis .
    qed
  qed
  finally show ?thesis .
qed

lemma replay_block_twice:
  "state_after (state_after D bs) bs = state_after D bs"
  by (rule replay_suffix_idempotent[OF suffix_order.refl])

text \<open>
  A consumer that has applied a prefix @{text ys} of the stream, restarts
  from the beginning and applies the whole stream ends in the state of a
  single application.
\<close>

lemma replay_from_prefix:
  assumes "prefix ys xs"
  shows "state_after (state_after D ys) xs = state_after D xs"
proof -
  obtain ws where xs: "xs = ys @ ws"
    using assms by (auto simp: prefix_def)
  have "state_after (state_after D ys) xs
          = state_after (state_after (state_after D ys) ys) ws"
    by (simp add: xs state_after_append)
  also have "\<dots> = state_after (state_after D ys) ws"
    by (simp add: replay_block_twice)
  also have "\<dots> = state_after D xs"
    by (simp add: xs state_after_append)
  finally show ?thesis .
qed

subsection \<open>Repetitions in place change nothing\<close>

text \<open>
  A block delivered twice in a row, anywhere in the stream, changes nothing.
  No assumption on the block is needed: in particular its keys need not be
  distinct, since the second copy rewrites every key of the block with the
  value the first copy left.
\<close>

lemma repeat_block_noop:
  "state_after D (xs @ bs @ bs @ zs) = state_after D (xs @ bs @ zs)"
  by (simp add: state_after_append replay_block_twice)

lemma duplicate_in_place_noop:
  "state_after D (xs @ e # e # zs) = state_after D (xs @ e # zs)"
  using repeat_block_noop[of D xs "[e]" zs] by simp

lemma repeat_in_place_noop:
  "state_after D (xs @ replicate (Suc n) e @ zs) = state_after D (xs @ e # zs)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "state_after D (xs @ replicate (Suc (Suc n)) e @ zs)
          = state_after D (xs @ e # e # (replicate n e @ zs))"
    by simp
  also have "\<dots> = state_after D (xs @ e # (replicate n e @ zs))"
    by (rule duplicate_in_place_noop)
  also have "\<dots> = state_after D (xs @ replicate (Suc n) e @ zs)"
    by simp
  also have "\<dots> = state_after D (xs @ e # zs)"
    by (rule Suc.IH)
  finally show ?case .
qed

text \<open>
  The unit's close block (its survivors and its enumerated absence entries,
  emitted at its high edge) re-applied right after itself, anywhere in a
  stream, changes nothing. This is the block lemma for that block, so it
  needs neither @{text svl_ok2} nor distinct keys.
\<close>

context capture_plan
begin

lemma close_block_reapply_noop:
  "state_after D (xs @ map snd (close_block svl u) @ map snd (close_block svl u) @ zs)
     = state_after D (xs @ map snd (close_block svl u) @ zs)"
  by (rule repeat_block_noop)

end  (* context capture_plan *)

subsection \<open>A re-emitted absence entry is a no-op\<close>

text \<open>
  A delete for a key the sink does not hold leaves the sink as it is, at the
  end of a stream or anywhere inside one.
\<close>

lemma delete_absent_noop:
  assumes "D k = None"
  shows "state_after D [Event k None] = D"
  using assms by (simp add: state_after_def apply_ev_def fun_upd_idem)

lemma delete_absent_in_stream_noop:
  assumes absent: "state_after D xs k = None"
  shows "state_after D (xs @ Event k None # zs) = state_after D (xs @ zs)"
proof -
  have "state_after D (xs @ Event k None # zs)
          = state_after (state_after (state_after D xs) [Event k None]) zs"
    by (simp add: state_after_def)
  also have "\<dots> = state_after (state_after D xs) zs"
    by (simp only: delete_absent_noop[of "state_after D xs" k, OF absent])
  also have "\<dots> = state_after D (xs @ zs)"
    by (rule state_after_append[symmetric])
  finally show ?thesis .
qed

text \<open>
  The paper's ``a duplicate absence event is a no-op'': appending an absence
  entry for @{text k} to a stream changes nothing when the stream's last
  event for @{text k} is a delete, or when the stream has no event for
  @{text k} and the initial sink state does not hold @{text k}.
\<close>

lemma absence_reemit_noop:
  assumes "(evs_for k S \<noteq> [] \<and> ev_img (last (evs_for k S)) = None)
           \<or> (evs_for k S = [] \<and> D0 k = None)"
  shows "state_after D0 (S @ [Event k None]) = state_after D0 S"
proof -
  from assms consider
      (deleted) "evs_for k S \<noteq> []" and "ev_img (last (evs_for k S)) = None"
    | (never) "evs_for k S = []" and "D0 k = None"
    by auto
  then have absent: "state_after D0 S k = None"
  proof cases
    case deleted
    then show ?thesis by (simp add: state_after_last_event)
  next
    case never
    then show ?thesis by (simp add: state_after_no_events)
  qed
  show ?thesis
    using delete_absent_in_stream_noop[OF absent, of "[]"] by simp
qed

subsection \<open>In-order at-least-once delivery\<close>

text \<open>
  A reader of a stream @{text xs} keeps a cursor, a position in
  @{text xs}. @{text "reads_from xs c ys"} says: a reader whose cursor is
  at @{text c} delivers @{text ys} until it stops. It may read the item at
  the cursor and advance, rewind the cursor to any earlier position (a
  restart from an older committed offset; rewinding to the cursor itself is
  allowed and does nothing), and it stops only at the end of the stream.
  Nothing is skipped and nothing is reordered, but anything may be read
  again any number of times. An at-least-once delivery of @{text xs} is
  what such a reader delivers from position 0. The sink applies every
  delivered item, in delivery order, to one persistent state: a restart of
  the reader does not roll the sink back. The rule @{text rewind} does not
  bound the outer cursor, so @{text reads_from} also admits a reader that
  starts beyond the end of the stream. An at-least-once delivery starts at
  position 0, from where the cursor never leaves the stream.
\<close>

inductive reads_from :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
  for xs :: "'a list" where
  finish:  "reads_from xs (length xs) []"
| advance: "\<lbrakk> c < length xs; reads_from xs (Suc c) ys \<rbrakk> \<Longrightarrow>
              reads_from xs c (xs ! c # ys)"
| rewind:  "\<lbrakk> c' \<le> c; reads_from xs c' ys \<rbrakk> \<Longrightarrow> reads_from xs c ys"

definition at_least_once :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "at_least_once xs ys \<longleftrightarrow> reads_from xs 0 ys"

text \<open>
  Multi-hop delivery: a connector's output is read at least once by a
  transport, whose output is read at least once by a sink, and so on. A
  redelivery of @{text xs} is the end of any finite chain of such hops,
  including the empty chain.
\<close>

definition redelivered :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "redelivered = at_least_once\<^sup>*\<^sup>*"

subsubsection \<open>The delivery class contains the expected streams\<close>

text \<open>
  Reading straight ahead from @{text i} to @{text j} delivers the segment
  between them, in order.
\<close>

lemma reads_from_forward:
  assumes rd: "reads_from xs j ys" and ij: "i \<le> j" and jn: "j \<le> length xs"
  shows "reads_from xs i (take (j - i) (drop i xs) @ ys)"
  using ij
proof (induction "j - i" arbitrary: i)
  case 0
  then have "i = j" by linarith
  then show ?case using rd by simp
next
  case (Suc d)
  have i_lt: "i < length xs"
    using Suc.hyps(2) jn by linarith
  have gap: "j - i = Suc (j - Suc i)"
    using Suc.hyps(2) by linarith
  have "reads_from xs (Suc i) (take (j - Suc i) (drop (Suc i) xs) @ ys)"
    by (rule Suc.hyps(1)) (use Suc.hyps(2) in linarith)+
  then have "reads_from xs i (xs ! i # take (j - Suc i) (drop (Suc i) xs) @ ys)"
    by (rule reads_from.advance[OF i_lt])
  moreover have "xs ! i # take (j - Suc i) (drop (Suc i) xs) @ ys = take (j - i) (drop i xs) @ ys"
    by (simp only: gap Cons_nth_drop_Suc[OF i_lt, symmetric] take_Suc_Cons append_Cons)
  ultimately show ?case
    by (simp only:)
qed

lemma reads_from_drop:
  assumes "i \<le> length xs"
  shows "reads_from xs i (drop i xs)"
  using reads_from_forward[OF reads_from.finish assms order.refl] by simp

lemma at_least_once_refl: "at_least_once xs xs"
  using reads_from_drop[of 0 xs] by (simp add: at_least_once_def)

text \<open>
  The basic restart: the reader has applied the first @{text j} items,
  rewinds to an earlier position @{text i} and reads from there to the end.
\<close>

lemma at_least_once_rewind_once:
  assumes ij: "i \<le> j" and jn: "j \<le> length xs"
  shows "at_least_once xs (take j xs @ drop i xs)"
proof -
  have "i \<le> length xs"
    using ij jn by linarith
  then have "reads_from xs i (drop i xs)"
    by (rule reads_from_drop)
  then have "reads_from xs j (drop i xs)"
    by (rule reads_from.rewind[OF ij])
  then have "reads_from xs 0 (take (j - 0) (drop 0 xs) @ drop i xs)"
    by (rule reads_from_forward) (use jn in simp_all)
  then show ?thesis
    by (simp add: at_least_once_def)
qed

text \<open>
  The streams the design names are instances: a consumer that applied a
  prefix @{text ws} and restarts from any position inside it, a re-delivery
  of a suffix at the end, a block delivered twice in a row, and a single
  event delivered twice in a row.
\<close>

lemma at_least_once_restart:
  assumes pre: "prefix ws xs" and i: "i \<le> length ws"
  shows "at_least_once xs (ws @ drop i xs)"
proof -
  have ws: "take (length ws) xs = ws"
    using pre by (auto simp: prefix_def)
  have "length ws \<le> length xs"
    using pre by (rule prefix_length_le)
  then have "at_least_once xs (take (length ws) xs @ drop i xs)"
    by (rule at_least_once_rewind_once[OF i])
  then show ?thesis
    by (simp only: ws)
qed

lemma at_least_once_suffix:
  "at_least_once xs (xs @ drop i xs)"
proof (cases "i \<le> length xs")
  case True
  then show ?thesis
    using at_least_once_rewind_once[OF True order.refl] by simp
next
  case False
  then have "length xs \<le> i"
    by linarith
  then have "drop i xs = []"
    by simp
  then show ?thesis
    using at_least_once_refl[of xs] by simp
qed

lemma at_least_once_block_dup:
  "at_least_once (xs @ bs @ zs) (xs @ bs @ bs @ zs)"
proof -
  have "at_least_once (xs @ bs @ zs)
          (take (length xs + length bs) (xs @ bs @ zs) @ drop (length xs) (xs @ bs @ zs))"
    by (rule at_least_once_rewind_once) simp_all
  then show ?thesis by simp
qed

lemma at_least_once_dup_in_place:
  "at_least_once (xs @ e # zs) (xs @ e # e # zs)"
  using at_least_once_block_dup[of xs "[e]" zs] by simp

lemma redelivered_refl: "redelivered xs xs"
  by (simp add: redelivered_def)

lemma redelivered_hop:
  assumes "redelivered xs ys" and "at_least_once ys zs"
  shows "redelivered xs zs"
  using assms unfolding redelivered_def by (rule rtranclp.rtrancl_into_rtrancl)

lemma redelivered_block_dup:
  "redelivered xs (ys @ bs @ zs) \<Longrightarrow> redelivered xs (ys @ bs @ bs @ zs)"
  by (rule redelivered_hop[OF _ at_least_once_block_dup])

lemma redelivered_dup_in_place:
  "redelivered xs (ys @ e # zs) \<Longrightarrow> redelivered xs (ys @ e # e # zs)"
  by (rule redelivered_hop[OF _ at_least_once_dup_in_place])

lemma redelivered_suffix:
  "redelivered xs ys \<Longrightarrow> redelivered xs (ys @ drop i ys)"
  by (rule redelivered_hop[OF _ at_least_once_suffix])

subsubsection \<open>Every delivery replays to the same state\<close>

text \<open>
  The invariant of a reader at cursor @{text c} whose sink is in state
  @{text \<sigma>}: every key either already holds the value that the first
  @{text c} items of @{text xs} give it (replayed from @{text D}), or
  @{text xs} still has an event for the key at or after the cursor. Reading
  ahead keeps this, since the item read decides its own key. Rewinding keeps
  it, since a key with no event at or after the new cursor has the same value
  at both cursors. At the end of the stream the second alternative is
  impossible, so the sink holds the replay of the whole stream.
\<close>

definition settled ::
    "('k, 'v) state \<Rightarrow> ('k, 'v) event list \<Rightarrow> nat \<Rightarrow> ('k, 'v) state \<Rightarrow> bool" where
  "settled D xs c \<sigma> \<longleftrightarrow>
     (\<forall>k. \<sigma> k = state_after D (take c xs) k \<or> evs_for k (drop c xs) \<noteq> [])"

lemma state_after_Cons:
  "state_after \<sigma> (e # P) = state_after (apply_ev \<sigma> e) P"
  by (simp add: state_after_def)

lemma settled_start: "settled D xs 0 D"
  by (simp add: settled_def)

lemma settled_finish:
  assumes "settled D xs (length xs) \<sigma>"
  shows "\<sigma> = state_after D xs"
  using assms by (simp add: settled_def fun_eq_iff)

lemma settled_advance:
  assumes c: "c < length xs" and st: "settled D xs c \<sigma>"
  shows "settled D xs (Suc c) (apply_ev \<sigma> (xs ! c))"
  unfolding settled_def
proof
  fix k
  have tk: "take (Suc c) xs = take c xs @ [xs ! c]"
    using c by (rule take_Suc_conv_app_nth)
  have dr: "drop c xs = xs ! c # drop (Suc c) xs"
    using c by (rule Cons_nth_drop_Suc[symmetric])
  show "apply_ev \<sigma> (xs ! c) k = state_after D (take (Suc c) xs) k
        \<or> evs_for k (drop (Suc c) xs) \<noteq> []"
  proof (cases "ev_key (xs ! c) = k")
    case True
    have "apply_ev \<sigma> (xs ! c) k = ev_img (xs ! c)"
      using True by (simp add: apply_ev_def)
    moreover have "state_after D (take (Suc c) xs) k = ev_img (xs ! c)"
      using True by (simp add: tk state_after_snoc apply_ev_def)
    ultimately show ?thesis by simp
  next
    case False
    have same: "apply_ev \<sigma> (xs ! c) k = \<sigma> k"
      using False by (simp add: apply_ev_def)
    have src: "state_after D (take (Suc c) xs) k = state_after D (take c xs) k"
      using False by (simp add: tk state_after_snoc apply_ev_def)
    have log: "evs_for k (drop (Suc c) xs) = evs_for k (drop c xs)"
      using False by (simp add: dr evs_for_def)
    have "\<sigma> k = state_after D (take c xs) k \<or> evs_for k (drop c xs) \<noteq> []"
      using st by (simp add: settled_def)
    then show ?thesis
      using same src log by simp
  qed
qed

lemma settled_rewind:
  assumes le: "c' \<le> c" and st: "settled D xs c \<sigma>"
  shows "settled D xs c' \<sigma>"
  unfolding settled_def
proof
  fix k
  define W where "W = take (c - c') (drop c' xs)"
  have tk: "take c xs = take c' xs @ W"
    using le take_add[of c' "c - c'" xs] by (simp add: W_def)
  have dr: "drop c' xs = W @ drop c xs"
  proof -
    have shift: "drop c xs = drop (c - c') (drop c' xs)"
      using le by simp
    show ?thesis
      unfolding W_def shift by (rule append_take_drop_id[symmetric])
  qed
  show "\<sigma> k = state_after D (take c' xs) k \<or> evs_for k (drop c' xs) \<noteq> []"
  proof (cases "evs_for k (drop c' xs) = []")
    case False
    then show ?thesis by simp
  next
    case True
    then have quiet_W: "evs_for k W = []" and quiet_rest: "evs_for k (drop c xs) = []"
      using dr by simp_all
    have "\<sigma> k = state_after D (take c xs) k \<or> evs_for k (drop c xs) \<noteq> []"
      using st by (simp add: settled_def)
    with quiet_rest have "\<sigma> k = state_after D (take c xs) k"
      by simp
    also have "\<dots> = state_after D (take c' xs) k"
      using quiet_W by (simp add: tk state_after_append_no_k)
    finally show ?thesis by simp
  qed
qed

lemma reads_from_replay:
  assumes "reads_from xs c ys" and "settled D xs c \<sigma>"
  shows "state_after \<sigma> ys = state_after D xs"
  using assms
proof (induction arbitrary: \<sigma>)
  case finish
  then have "\<sigma> = state_after D xs"
    by (rule settled_finish)
  then show ?case
    by simp
next
  case (advance c ys)
  have "state_after \<sigma> (xs ! c # ys) = state_after (apply_ev \<sigma> (xs ! c)) ys"
    by (rule state_after_Cons)
  also have "\<dots> = state_after D xs"
    by (rule advance.IH[OF settled_advance[OF advance.hyps(1) advance.prems]])
  finally show ?case .
next
  case (rewind c' c ys)
  show ?case
    by (rule rewind.IH[OF settled_rewind[OF rewind.hyps(1) rewind.prems]])
qed

theorem at_least_once_replay:
  assumes "at_least_once xs ys"
  shows "state_after D ys = state_after D xs"
  using reads_from_replay[OF assms[unfolded at_least_once_def] settled_start] .

theorem redelivered_replay:
  assumes "redelivered xs ys"
  shows "state_after D ys = state_after D xs"
  using assms unfolding redelivered_def
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step ys zs)
  have "state_after D zs = state_after D ys"
    by (rule at_least_once_replay[OF step.hyps(2)])
  then show ?case
    using step.IH by simp
qed

subsection \<open>Transfer of the safety and convergence results\<close>

text \<open>
  Because every redelivery of the emission replays to the same state, from
  every initial sink state, the two main results of @{text Orphan_Absence}
  hold for the stream the sink actually applies, whatever in-place
  duplications, restarts and suffix re-deliveries it went through on the
  way: each scoped key ends at the canonical replay value or is a surviving
  orphan (never a wrong value, never a deleted live row), and under coverage
  every scoped key ends at the source state at the frontier.
\<close>

context capture_contract
begin

theorem absent_replay_safe_at_least_once:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and red: "redelivered (emission svl s0) S"
  shows "state_after D0 S k = sink_at f k
         \<or> (state_after D0 S k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> absent_untouched (the_unit k)
            \<and> k \<notin> set (svl (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
proof -
  have same: "state_after D0 S = state_after D0 (emission svl s0)"
    by (rule redelivered_replay[OF red])
  show ?thesis
    unfolding same by (rule absent_replay_safe[OF svl s0lo k])
qed

theorem self_stabilization_at_least_once:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and cov: "covers svl D0 s0"
      and red: "redelivered (emission svl s0) S"
  shows "\<forall>k \<in> scope. state_after D0 S k = state_after \<sigma>0 (pfx f) k"
proof -
  have same: "state_after D0 S = state_after D0 (emission svl s0)"
    by (rule redelivered_replay[OF red])
  show ?thesis
    unfolding same by (rule self_stabilization[OF svl s0lo cov])
qed

end  (* context capture_contract *)

subsection \<open>Per-key delivery\<close>

text \<open>
  A topic with several partitions preserves order only inside a partition.
  When the message key is the row key, all events of one key go to one
  partition. This is the paper's requirement in Section 5.3. Events of
  different keys may then arrive in a different interleaving than the
  emission's, so the stream the sink applies need not be a redelivery of
  the emission. The per-key form asks less: the events the sink applies for
  a key form a redelivery of the emission's events for that key.

  A keyed topic with several partitions, each delivered in order at least
  once, without compaction affecting the read, instantiates the per-key
  form. This is a lemma below, @{text partitioned_delivery_per_key}. The
  remaining assumptions are only that each partition is delivered in order
  at least once (a redelivery in the sense above) and that the message key
  is the row key (the partition is a function of the row key). A fresh
  consumer of a compacted topic, which sees only a key's later records, is
  not a per-key redelivery (the fixture
  @{text compacted_read_not_per_key_redelivery}) and is outside the model.
\<close>

lemma evs_for_idem: "evs_for k (evs_for k P) = evs_for k P"
  by (simp add: evs_for_def)

lemma redelivered_key_replay:
  assumes "redelivered (evs_for k E) (evs_for k S)"
  shows "state_after D S k = state_after D E k"
proof -
  have "state_after D S k = state_after D (evs_for k S) k"
    by (rule replay_per_key[OF evs_for_idem, symmetric])
  also have "\<dots> = state_after D (evs_for k E) k"
    using redelivered_replay[OF assms, of D] by simp
  also have "\<dots> = state_after D E k"
    by (rule replay_per_key[OF evs_for_idem])
  finally show ?thesis .
qed

lemma redelivered_per_key_replay:
  assumes per_key: "\<And>k. redelivered (evs_for k E) (evs_for k S)"
  shows "state_after D S = state_after D E"
  by (rule ext) (rule redelivered_key_replay[OF per_key])

subsubsection \<open>Filtering a delivery, and partitioned topics\<close>

(* The proofs of length_filter_take_mono, reads_from_filter,
   at_least_once_filter, redelivered_filter and redelivered_evs_for, and of
   reads_from_empty_end, reads_from_last, reads_from_hd, reads_from_nonempty
   and redelivered_hd_last further below, are adapted from the blind
   reviewer's probe theory (review round 2, 2026-11-07). *)

text \<open>
  Filtering a delivery by any predicate on items gives a delivery of the
  filtered stream: the reader's cursor over the stream maps to the number
  of kept items before it, reading a kept item advances the mapped cursor,
  reading a dropped item leaves it, and a rewind maps to a rewind.
\<close>

lemma length_filter_take_mono:
  assumes "c' \<le> c"
  shows "length (filter P (take c' xs)) \<le> length (filter P (take c xs))"
proof -
  have "take c' xs = take c' (take c xs)"
    using assms by (simp add: min_absorb1)
  then have "prefix (take c' xs) (take c xs)"
    by (metis take_is_prefix)
  then obtain zs where "take c xs = take c' xs @ zs"
    by (auto simp: prefix_def)
  then show ?thesis by simp
qed

lemma reads_from_filter:
  "reads_from xs c ys \<Longrightarrow>
     reads_from (filter P xs) (length (filter P (take c xs))) (filter P ys)"
proof (induction rule: reads_from.induct)
  case finish
  then show ?case by (simp add: reads_from.finish)
next
  case (advance c ys)
  have tk: "take (Suc c) xs = take c xs @ [xs ! c]"
    using advance.hyps(1) by (rule take_Suc_conv_app_nth)
  show ?case
  proof (cases "P (xs ! c)")
    case True
    define m where "m = length (filter P (take c xs))"
    have split: "filter P xs = filter P (take c xs) @ xs ! c # filter P (drop (Suc c) xs)"
    proof -
      have "xs = take c xs @ xs ! c # drop (Suc c) xs"
        using advance.hyps(1) by (simp add: id_take_nth_drop)
      then have "filter P xs = filter P (take c xs @ xs ! c # drop (Suc c) xs)"
        by simp
      then show ?thesis using True by simp
    qed
    have m_lt: "m < length (filter P xs)"
      using split by (simp add: m_def)
    have nth: "filter P xs ! m = xs ! c"
      using split by (simp add: m_def nth_append)
    have "reads_from (filter P xs) (Suc m) (filter P ys)"
      using advance.IH True by (simp add: tk m_def)
    then have "reads_from (filter P xs) m (filter P xs ! m # filter P ys)"
      by (rule reads_from.advance[OF m_lt])
    then show ?thesis
      using True nth by (simp add: m_def)
  next
    case False
    then show ?thesis
      using advance.IH by (simp add: tk)
  qed
next
  case (rewind c' c ys)
  show ?case
    by (rule reads_from.rewind[OF length_filter_take_mono[OF rewind.hyps(1)] rewind.IH])
qed

lemma at_least_once_filter:
  "at_least_once xs ys \<Longrightarrow> at_least_once (filter P xs) (filter P ys)"
  unfolding at_least_once_def using reads_from_filter[of xs 0 ys P] by simp

lemma redelivered_filter:
  "redelivered xs ys \<Longrightarrow> redelivered (filter P xs) (filter P ys)"
  unfolding redelivered_def
  by (induction rule: rtranclp_induct)
     (auto intro: rtranclp.rtrancl_into_rtrancl at_least_once_filter)

lemma redelivered_evs_for:
  "redelivered xs ys \<Longrightarrow> redelivered (evs_for k xs) (evs_for k ys)"
  unfolding evs_for_def by (rule redelivered_filter)

text \<open>
  A partitioned topic. The map @{text part} assigns every key its
  partition, so the partition is a function of the row key. Partition
  @{text p} carries the emission's events for its keys, in emission order,
  and the sink receives a redelivery @{text "T p"} of it. The sink applies
  the partitions' deliveries in some interleaving @{text S}: for every key,
  the sink's events for that key are the events for that key in its own
  partition's delivery. Then every key's events form a redelivery of the
  emission's events for that key, which is the per-key hypothesis.
\<close>

lemma partitioned_delivery_per_key:
  assumes parts: "\<And>p. redelivered (filter (\<lambda>e. part (ev_key e) = p) E) (T p)"
      and interleave: "\<And>k'. evs_for k' S = evs_for k' (T (part k'))"
  shows "redelivered (evs_for k E) (evs_for k S)"
proof -
  have own: "evs_for k (filter (\<lambda>e. part (ev_key e) = part k) E) = evs_for k E"
    unfolding evs_for_def filter_filter by (rule filter_cong) auto
  have "redelivered (evs_for k (filter (\<lambda>e. part (ev_key e) = part k) E))
                    (evs_for k (T (part k)))"
    by (rule redelivered_evs_for[OF parts])
  then show ?thesis
    by (simp only: own interleave)
qed

text \<open>
  Every redelivery of a stream starts with the stream's first item and ends
  with its last. This is what excludes a compacted read below.
\<close>

lemma reads_from_empty_end:
  "reads_from xs c ys \<Longrightarrow> ys = [] \<Longrightarrow> length xs \<le> c"
  by (induction rule: reads_from.induct) auto

lemma reads_from_last:
  "reads_from xs c ys \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> last ys = last xs"
proof (induction rule: reads_from.induct)
  case finish
  then show ?case by simp
next
  case (advance c ys)
  show ?case
  proof (cases "ys = []")
    case True
    then have "length xs \<le> Suc c"
      using reads_from_empty_end[OF advance.hyps(2)] by simp
    with advance.hyps(1) have "c = length xs - 1"
      by linarith
    moreover have "xs \<noteq> []"
      using advance.hyps(1) by auto
    ultimately show ?thesis
      using True by (simp add: last_conv_nth)
  next
    case False
    then show ?thesis
      using advance.IH by simp
  qed
next
  case (rewind c' c ys)
  then show ?case by simp
qed

lemma reads_from_hd:
  "reads_from xs c ys \<Longrightarrow> c = 0 \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> hd ys = xs ! 0"
  by (induction rule: reads_from.induct) auto

lemma reads_from_nonempty:
  "reads_from xs c ys \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> xs \<noteq> []"
  by (induction rule: reads_from.induct) auto

lemma redelivered_hd_last:
  assumes "redelivered xs ys" and "ys \<noteq> []"
  shows "xs \<noteq> [] \<and> hd ys = hd xs \<and> last ys = last xs"
  using assms unfolding redelivered_def
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step ys zs)
  have rd: "reads_from ys 0 zs"
    using step.hyps(2) by (simp add: at_least_once_def)
  have ys_ne: "ys \<noteq> []"
    using reads_from_nonempty[OF rd step.prems] .
  have "hd zs = ys ! 0"
    using reads_from_hd[OF rd refl step.prems] .
  moreover have "last zs = last ys"
    using reads_from_last[OF rd step.prems] .
  ultimately show ?case
    using step.IH[OF ys_ne] ys_ne by (simp add: hd_conv_nth)
qed

context capture_contract
begin

theorem absent_replay_safe_at_least_once_per_key:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and per_key: "redelivered (evs_for k (emission svl s0)) (evs_for k S)"
  shows "state_after D0 S k = sink_at f k
         \<or> (state_after D0 S k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> absent_untouched (the_unit k)
            \<and> k \<notin> set (svl (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
proof -
  have same: "state_after D0 S k = state_after D0 (emission svl s0) k"
    by (rule redelivered_key_replay[OF per_key])
  show ?thesis
    unfolding same by (rule absent_replay_safe[OF svl s0lo k])
qed

theorem self_stabilization_at_least_once_per_key:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and cov: "covers svl D0 s0"
      and per_key: "\<And>k. k \<in> scope \<Longrightarrow>
                      redelivered (evs_for k (emission svl s0)) (evs_for k S)"
  shows "\<forall>k \<in> scope. state_after D0 S k = state_after \<sigma>0 (pfx f) k"
proof
  fix k assume k: "k \<in> scope"
  have same: "state_after D0 S k = state_after D0 (emission svl s0) k"
    by (rule redelivered_key_replay[OF per_key[OF k]])
  have "\<forall>k \<in> scope. state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
    by (rule self_stabilization[OF svl s0lo cov])
  with k same show "state_after D0 S k = state_after \<sigma>0 (pfx f) k"
    by simp
qed

end  (* context capture_contract *)

subsection \<open>Fixtures\<close>

text \<open>
  The orphan fixture of @{text Orphan_Absence}, delivered twice in full: the
  orphan at key 4 is still removed and key 3 still ends at 7. The transfer
  theorem applies to the doubled stream through the suffix instance of the
  delivery class, so its hypotheses are met by a concrete redelivery.
\<close>

lemma wit_redelivered_orphan_removed:
  "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0 @ orph.emission (\<lambda>_. [3, 4]) 0) 4 = None"
proof -
  have red: "redelivered (orph.emission (\<lambda>_. [3, 4]) 0)
               (orph.emission (\<lambda>_. [3, 4]) 0 @ drop 0 (orph.emission (\<lambda>_. [3, 4]) 0))"
    by (rule redelivered_suffix[OF redelivered_refl])
  have "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0 @ orph.emission (\<lambda>_. [3, 4]) 0) 4
          = state_after s0_w (sc.pfx 2) 4"
    using orph.self_stabilization_at_least_once[OF orph_svl_ok2 orph_s0lo orph_covers red]
    by simp
  also have "\<dots> = None"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

lemma wit_redelivered_present_kept:
  "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0 @ orph.emission (\<lambda>_. [3, 4]) 0) 3 = Some 7"
proof -
  have red: "redelivered (orph.emission (\<lambda>_. [3, 4]) 0)
               (orph.emission (\<lambda>_. [3, 4]) 0 @ drop 0 (orph.emission (\<lambda>_. [3, 4]) 0))"
    by (rule redelivered_suffix[OF redelivered_refl])
  have "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0 @ orph.emission (\<lambda>_. [3, 4]) 0) 3
          = state_after s0_w (sc.pfx 2) 3"
    using orph.self_stabilization_at_least_once[OF orph_svl_ok2 orph_s0lo orph_covers red]
    by simp
  also have "\<dots> = Some 7"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

text \<open>
  Out-of-order re-delivery of one key's events is outside the class. The
  stream sets key 1 to 1 and then to 2. Delivering the first event once
  more at the end, with no later re-read of the second, leaves the sink at
  1 instead of 2. So that stream is not a redelivery, and the in-order
  restriction of the model is needed.
\<close>

lemma out_of_order_redelivery_differs:
  "state_after (\<lambda>_. None)
       [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)]
   \<noteq> state_after (\<lambda>_. None) [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)]"
proof
  assume eq: "state_after (\<lambda>_. None)
                  [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)]
              = state_after (\<lambda>_. None) [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)]"
  have stale: "state_after (\<lambda>_. None)
                  [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)] 1 = Some 1"
    by (simp add: state_after_def apply_ev_def)
  have fresh: "state_after (\<lambda>_. None)
                  [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)] 1 = Some 2"
    by (simp add: state_after_def apply_ev_def)
  show False
    using fun_cong[OF eq, of 1] stale fresh by simp
qed

lemma out_of_order_not_redelivered:
  "\<not> redelivered [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)]
                 [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)]"
proof
  assume "redelivered [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)]
                      [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)]"
  then have "state_after (\<lambda>_. None)
                 [Event (1::nat) (Some (1::nat)), Event 1 (Some 2), Event 1 (Some 1)]
             = state_after (\<lambda>_. None) [Event (1::nat) (Some (1::nat)), Event 1 (Some 2)]"
    by (rule redelivered_replay)
  with out_of_order_redelivery_differs show False ..
qed

text \<open>
  Two keys on two partitions: the sink applies key 2's event before key 1's.
  Each key's events are unchanged, so the per-key hypothesis holds (with the
  empty chain of hops for each key), and the stream replays like the
  emission from every initial state.
\<close>

lemma wit_partition_reorder_per_key:
  "redelivered (evs_for k [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)])
               (evs_for k [Event (2::nat) (Some (2::nat)), Event 1 (Some 1)])"
proof -
  have "evs_for k [Event (2::nat) (Some (2::nat)), Event 1 (Some 1)]
          = evs_for k [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)]"
    by (auto simp: evs_for_def)
  then show ?thesis
    by (simp add: redelivered_refl)
qed

lemma wit_partition_reorder_replay:
  "state_after D [Event (2::nat) (Some (2::nat)), Event 1 (Some 1)]
     = state_after D [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)]"
  by (rule redelivered_per_key_replay[OF wit_partition_reorder_per_key])

text \<open>
  The same reordering obtained from the partition lemma: each key is its own
  partition, each partition is delivered exactly once, and the sink applies
  key 2's partition first.
\<close>

lemma wit_partitioned_delivery:
  "redelivered (evs_for k [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)])
               (evs_for k [Event (2::nat) (Some (2::nat)), Event 1 (Some 1)])"
proof (rule partitioned_delivery_per_key[where part = "\<lambda>k. k"
         and T = "\<lambda>p. filter (\<lambda>e. ev_key e = p)
                              [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)]"])
  fix p :: nat
  show "redelivered (filter (\<lambda>e. ev_key e = p) [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)])
          (filter (\<lambda>e. ev_key e = p) [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)])"
    by (rule redelivered_refl)
next
  fix k' :: nat
  show "evs_for k' [Event (2::nat) (Some (2::nat)), Event 1 (Some 1)]
        = evs_for k' (filter (\<lambda>e. ev_key e = k') [Event (1::nat) (Some (1::nat)), Event 2 (Some 2)])"
    by (auto simp: evs_for_def)
qed

(* The fixture rw_E, rw_part, rw_T, rw_S and its four lemmas below are
   adapted from the blind reviewer's probe theory (review round 3,
   2026-11-07; lemmas T3_parts, S3_interleave, S3_not_redelivery, S3_per_key). *)

text \<open>
  A non-degenerate instance of the partition lemma. Partition 0 holds keys 1
  and 3, partition 1 holds key 2. Partition 0 is delivered with a rewind
  inside it (key 1's event is read twice), and the sink applies partition
  1's delivery first. The resulting stream is not a redelivery of the
  emission, since it starts with a different item, yet the lemma gives the
  per-key hypothesis for every key.
\<close>

definition rw_E :: "(nat, nat) event list" where
  "rw_E = [Event 1 (Some 1), Event 2 (Some 2), Event 3 (Some 3)]"

definition rw_part :: "nat \<Rightarrow> nat" where
  "rw_part k = (if k = 2 then 1 else 0)"

definition rw_T :: "nat \<Rightarrow> (nat, nat) event list" where
  "rw_T p = (if p = 0 then [Event 1 (Some 1), Event 1 (Some 1), Event 3 (Some 3)]
             else if p = 1 then [Event 2 (Some 2)] else [])"

definition rw_S :: "(nat, nat) event list" where
  "rw_S = [Event 2 (Some 2), Event 1 (Some 1), Event 1 (Some 1), Event 3 (Some 3)]"

lemma wit_rewind_parts:
  "redelivered (filter (\<lambda>e. rw_part (ev_key e) = p) rw_E) (rw_T p)"
proof -
  consider (zero) "p = 0" | (one) "p = 1" | (other) "p \<noteq> 0 \<and> p \<noteq> 1"
    by blast
  then show ?thesis
  proof cases
    case zero
    have "at_least_once [Event (1::nat) (Some (1::nat)), Event 3 (Some 3)]
            (take 1 [Event (1::nat) (Some (1::nat)), Event 3 (Some 3)]
             @ drop 0 [Event (1::nat) (Some (1::nat)), Event 3 (Some 3)])"
      by (rule at_least_once_rewind_once) simp_all
    then have "at_least_once [Event (1::nat) (Some (1::nat)), Event 3 (Some 3)] (rw_T 0)"
      by (simp add: rw_T_def)
    then show ?thesis
      using zero redelivered_hop[OF redelivered_refl] by (simp add: rw_E_def rw_part_def)
  next
    case one
    then show ?thesis
      by (simp add: rw_E_def rw_part_def rw_T_def redelivered_refl)
  next
    case other
    then show ?thesis
      by (simp add: rw_E_def rw_part_def rw_T_def redelivered_refl)
  qed
qed

lemma wit_rewind_interleave: "evs_for k' rw_S = evs_for k' (rw_T (rw_part k'))"
  by (auto simp: rw_S_def rw_T_def rw_part_def evs_for_def)

lemma wit_rewind_not_redelivered: "\<not> redelivered rw_E rw_S"
  using redelivered_hd_last[of rw_E rw_S] by (auto simp: rw_E_def rw_S_def)

lemma wit_partitioned_delivery_rewind: "redelivered (evs_for k rw_E) (evs_for k rw_S)"
  by (rule partitioned_delivery_per_key[OF wit_rewind_parts wit_rewind_interleave])

text \<open>
  The per-key hypothesis of the transfer theorems is asked for the key in
  question only. A sink that applies only one table's keys meets it for its
  own keys: here the sink drops key 9's event, and key 1 still meets it.
\<close>

lemma wit_own_key_only:
  "redelivered (evs_for 1 [Event (1::nat) (Some (1::nat)), Event 9 (Some 9)])
               (evs_for 1 [Event (1::nat) (Some (1::nat))])"
  by (simp add: evs_for_def redelivered_refl)

text \<open>
  A fresh consumer of a compacted topic sees only a key's later records.
  Here the key's insert was compacted away and only its delete is read.
  That read is not a per-key redelivery, since a redelivery starts with the
  stream's first item.
\<close>

lemma compacted_read_not_per_key_redelivery:
  "\<not> redelivered (evs_for 4 [Event (4::nat) (Some (5::nat)), Event 4 None])
                 (evs_for 4 [Event (4::nat) None])"
proof
  assume "redelivered (evs_for 4 [Event (4::nat) (Some (5::nat)), Event 4 None])
                      (evs_for 4 [Event (4::nat) None])"
  then have "redelivered [Event (4::nat) (Some (5::nat)), Event 4 None] [Event 4 None]"
    by (simp add: evs_for_def)
  then show False
    using redelivered_hd_last[of "[Event (4::nat) (Some (5::nat)), Event 4 None]" "[Event 4 None]"]
    by simp
qed

end
