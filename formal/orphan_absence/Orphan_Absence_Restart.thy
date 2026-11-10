(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Restart: the stream a sink sees across a connector restart.
  A pass is interrupted by a crash. The connector resumes streaming from its
  committed offset, which lies at or after the pass's consumption start, so
  it delivers the log segment from the committed offset to the crash a
  second time. It re-executes at least every chunk that had not closed by
  the crash. The sink applies all of it, in order, to one persistent state,
  from an arbitrary initial sink state.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core), to
  Orphan_Absence, Orphan_Absence_Composition and Orphan_Absence_Interleaved.
  Nothing in the archived development is modified.
*)
theory Orphan_Absence_Restart
  imports Orphan_Absence_Interleaved
begin

text \<open>
  A connector runs a pass P1 with consumption start @{text s0}. It crashes
  after it has emitted everything up to log position @{text crash}: its log
  events from @{text s0} to just before the crash, and its close blocks at
  the positions from @{text s0} to the crash. It had committed its offset at
  the coordinate @{text cmt}, at or after @{text s0} and at or before the
  crash. A commit before the pass started is not stated in this theory. On
  restart it
  resumes streaming from @{text cmt}, so it delivers the log events from
  @{text cmt} to the crash a second time, without close entries. It
  re-executes at least every chunk of P1 that had not closed by the crash.
  The re-executed chunks form a second capture contract P2 over the same
  log, with fresh windows that open at or after the crash. The sink
  applies, in this order and to one persistent state, P1's emission up to
  the crash, the re-delivered log segment, and P2's emission. Results:

  \<^item> The first part of the stream is a prefix of P1's emission. It is P1's
    emission run up to the crash: its close blocks at the positions from
    @{text s0} to the crash and its log events from @{text s0} to just
    before the crash. With the committed offset and the crash both at P1's
    frontier, nothing is re-delivered and the stream is the sequential
    composition of @{text Orphan_Absence_Composition}. A crash after P1's
    frontier reduces to a crash at the frontier, with the crash taken as
    P1's frontier (@{text pass_restart_after_frontier}).
  \<^item> Safety: every key of either scope ends at the source state at P2's
    frontier @{text f2}, or it is absent there, no close entry delivered
    before the crash lists it, P2 does not list it, no log event from
    @{text s0} to @{text f2} mentions it, and the sink keeps its initial
    value.
  \<^item> Convergence: under coverage of exactly those keys, the sink ends at
    the source state on both scopes.
  \<^item> Fixtures: an orphan removed by a close entry delivered before the
    crash stays removed after the restart, even when the re-executed chunk
    does not list it. A key inserted between that close and the crash keeps
    its live row. A crash before the close, with a re-executed chunk that
    does not list the orphan, leaves it in place, in the second branch of
    the safety theorem. While a re-delivered segment is applied, the sink
    can hold a deleted row that the log has inserted again, and it ends at
    the source value.

  Both theorems speak about the sink after the whole stream. While the
  re-delivered segment is applied, the sink can hold an older value of a
  key for a while, for example a deleted row that the log has inserted
  again (@{text wit_restart_transient_mid}). The guarantees of the safety
  theorem hold at P2's frontier.

  The crash sits right after the close blocks at its position. A crash
  after the log event at the position before, but before those close
  blocks, or in the middle of a close block, is modeled by a sub-contract
  of P1: it drops the units at that position whose close blocks were not
  delivered, or the keys of a partly delivered unit that were not
  delivered. Those keys then lie in P2's scope, because their chunk is
  re-executed. This modeling remark is argued here in prose and is not a
  theorem of this theory.

  The proof is per key. It rests on the observation of
  @{text Orphan_Absence_Interleaved}: every item of the stream carries the
  source value of its key at its own tag. The stream as a whole is not in
  position order, since the re-delivered segment goes back to @{text cmt}.
  But the part after the restart is in position order and carries every log
  event from @{text cmt} to @{text f2}, and the part before the restart is
  in position order and carries every log event from @{text s0} to the
  crash. If the part after the restart has an item for the key, its last
  item decides, and no later log event of the key exists. Otherwise the key
  has no log event from @{text cmt} on, and the last item of the first part
  decides, with no log event of the key after it.
\<close>

subsection \<open>Items of a pass's emission: cases, tags, values\<close>

context capture_plan
begin

lemma emission_t_item_cases:
  assumes "x \<in> set (emission_t svl s0)"
  obtains (event) q where "den s0 \<le> q" "q < den f" "x = (Suc q, L ! q)"
    | (close) q where "den s0 \<le> q \<and> q < den f \<or> q = den f" "x \<in> set (closes_at svl q)"
proof -
  have "(\<exists>q. den s0 \<le> q \<and> q < den f \<and>
             (x \<in> set (closes_at svl q) \<or> x = (Suc q, L ! q)))
        \<or> x \<in> set (closes_at svl (den f))"
    using assms unfolding emission_t_def by auto
  then show thesis using that by blast
qed

lemma emission_t_tag_le:
  assumes "x \<in> set (emission_t svl s0)"
  shows "fst x \<le> den f"
  using assms
proof (cases rule: emission_t_item_cases)
  case (event q)
  then show ?thesis by simp
next
  case (close q)
  have "fst x = q" by (rule closes_at_tag[OF close(2)])
  then show ?thesis using close(1) by auto
qed

text \<open>
  Every item is tagged at or after the consumption start, except the close
  entries at the frontier when the consumption start lies beyond it.
\<close>

lemma emission_t_tag_ge:
  assumes "x \<in> set (emission_t svl s0)"
  shows "den s0 \<le> fst x \<or> fst x = den f"
  using assms
proof (cases rule: emission_t_item_cases)
  case (event q)
  then show ?thesis by simp
next
  case (close q)
  have "fst x = q" by (rule closes_at_tag[OF close(2)])
  then show ?thesis using close(1) by auto
qed

lemma emission_t_event_in:
  assumes "den s0 \<le> q" and "q < den f"
  shows "(Suc q, L ! q) \<in> set (emission_t svl s0)"
proof -
  have "(Suc q, L ! q) \<in> set (closes_at svl q @ [(Suc q, L ! q)])" by simp
  moreover have "q \<in> set [den s0..<den f]" using assms by simp
  ultimately show ?thesis unfolding emission_t_def by auto
qed

end  (* context capture_plan *)

context capture_contract
begin

text \<open>
  Every item of a pass's emission carries the source value of its key at its
  own tag: a log event by @{text event_honest}, a close entry by
  @{text listed_entry_honest}.
\<close>

lemma emission_item_honest:
  assumes svl: "svl_ok2 svl" and x: "x \<in> set (emission_t svl s0)"
  shows "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) (ev_key (snd x))"
  using x
proof (cases rule: emission_t_item_cases)
  case (event q)
  have q_len: "q < length L" using event(2) den_le_len[of f] by simp
  have "ev_img (L ! q) = state_after \<sigma>0 (take (Suc q) L) (ev_key (L ! q))"
    by (rule event_honest[OF q_len refl])
  then show ?thesis using event(3) by simp
next
  case (close q)
  obtain u k' where u: "u \<in> set units" and k': "k' \<in> set (svl u)"
    and xe: "x = (den (u_hi u), Event k' (u_refresh u k'))"
    using closes_at_item[OF close(2)] by blast
  have "u_refresh u k' = state_after \<sigma>0 (pfx (u_hi u)) k'"
    by (rule listed_entry_honest[OF svl u k'])
  then show ?thesis using xe by (simp add: pfx_def)
qed

text \<open>
  A unit that closes at or after the consumption start has its close entries
  in the emission.
\<close>

lemma close_entry_in_emission:
  assumes u: "u \<in> set units" and listed: "k \<in> set (svl u)"
      and s0hi: "den s0 \<le> den (u_hi u)"
  shows "(den (u_hi u), Event k (u_refresh u k)) \<in> set (emission_t svl s0)"
proof -
  define x where "x = (den (u_hi u), Event k (u_refresh u k))"
  obtain i where i: "i < length units" and ui: "units ! i = u"
    using u by (meson in_set_conv_nth)
  have in_block: "x \<in> set (if den (u_hi (units ! i)) = den (u_hi u)
                             then close_block svl (units ! i) else [])"
    using listed ui by (simp add: x_def close_block_def)
  have i_in: "i \<in> set [0..<length units]" using i by simp
  have in_closes: "x \<in> set (closes_at svl (den (u_hi u)))"
    unfolding closes_at_def using in_block i_in by auto
  have hi_f: "den (u_hi u) \<le> den f" using bracket_hi_f[OF u] by (simp add: cle_def)
  consider (inside) "den (u_hi u) < den f" | (at_end) "den (u_hi u) = den f"
    using hi_f by linarith
  then show ?thesis
  proof cases
    case inside
    have "den (u_hi u) \<in> set [den s0..<den f]" using s0hi inside by simp
    then show ?thesis using in_closes unfolding x_def emission_t_def by auto
  next
    case at_end
    then show ?thesis using in_closes unfolding x_def emission_t_def by simp
  qed
qed

text \<open>
  The form of @{text unlisted_quiet_absent} at any coordinate @{text g} at or
  after the key's own close: a key of the scope that the enumeration does
  not list, and that no log event from @{text s0} to @{text g} mentions, is
  absent at @{text g}. Only the key's own unit enters, as in
  @{text contract_cut_unit}.
\<close>

lemma unlisted_quiet_absent_at:
  assumes svl: "svl_ok2 svl"
      and k: "k \<in> scope"
      and s0lo: "s0 \<sqsubseteq> u_lo (the_unit k)"
      and hi_g: "u_hi (the_unit k) \<sqsubseteq> g"
      and unlisted: "k \<notin> set (svl (the_unit k))"
      and quiet: "evs_for k (win s0 g) = []"
  shows "state_after \<sigma>0 (pfx g) k = None"
proof -
  define u where "u = the_unit k"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have s0_lo: "s0 \<sqsubseteq> u_lo u" using s0lo by (simp add: u_def)
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" by (rule bracket_lo_hi[OF u_in])
  have hi_g': "u_hi u \<sqsubseteq> g" using hi_g by (simp add: u_def)
  have lo_g: "u_lo u \<sqsubseteq> g" using lo_hi hi_g' by (rule cle_trans)
  have quiet_lo_g: "evs_for k (win (u_lo u) g) = []"
    using evs_for_win_split[OF s0_lo lo_g] quiet by simp
  have quiet_win: "evs_for k (win (u_lo u) (u_hi u)) = []"
    using evs_for_win_split[OF lo_hi hi_g'] quiet_lo_g by simp
  have refresh_none: "u_refresh u k = None"
  proof (rule ccontr)
    assume "u_refresh u k \<noteq> None"
    then have "k \<in> survivors u" using k_dom quiet_win by (simp add: survivors_def)
    then have "k \<in> set (svl u)" by (rule svl2_surv[OF svl u_in])
    with unlisted show False by (simp add: u_def)
  qed
  have "sink_at g k = u_refresh u k"
    using quiet_lo_g by (simp add: sink_at_def flip: u_def)
  then show ?thesis using contract_cut_unit[OF k hi_g] refresh_none by simp
qed

end  (* context capture_contract *)

context coordinate_space
begin

text \<open>A window without a log event of the key at any of its positions.\<close>

lemma evs_for_win_quiet:
  assumes quiet: "\<And>q. den a \<le> q \<Longrightarrow> q < den b \<Longrightarrow> ev_key (L ! q) \<noteq> k"
  shows "evs_for k (win a b) = []"
proof (cases "den a \<le> den b")
  case True
  then have ab: "a \<sqsubseteq> b" by (simp add: cle_def)
  have "kposs k (den a) (den b) = []"
    using quiet by (auto simp: kposs_def filter_empty_conv)
  then show ?thesis using evs_for_win_kposs[OF ab] by simp
next
  case False
  then have "win a b = []" by (simp add: win_def)
  then show ?thesis by simp
qed

end  (* context coordinate_space *)

text \<open>
  On a list in tag order, keeping the items tagged at most @{text h} keeps a
  prefix.
\<close>

lemma filter_tag_le_sorted:
  assumes "sorted (map fst S)"
  shows "filter (\<lambda>x. fst x \<le> h) S = takeWhile (\<lambda>x. fst x \<le> h) S"
  using assms
proof (induction S)
  case Nil
  then show ?case by simp
next
  case (Cons x S)
  have sS: "sorted (map fst S)" and x_le: "\<forall>y \<in> set S. fst x \<le> fst y"
    using Cons.prems by auto
  show ?case
  proof (cases "fst x \<le> h")
    case True
    then show ?thesis using Cons.IH[OF sS] by simp
  next
    case False
    then have "\<forall>y \<in> set S. \<not> fst y \<le> h" using x_le by auto
    then have "filter (\<lambda>x. fst x \<le> h) S = []" by (rule filter_False)
    then show ?thesis using False by simp
  qed
qed

subsection \<open>A pass interrupted by a crash, and its restart, over one log\<close>

text \<open>
  P1 is the pass as planned, with consumption start @{text s0} and frontier
  @{text f1}. P2 is the contract of the chunks re-executed after the crash,
  with frontier @{text f2}. The coordinate @{text cmt} is the committed
  offset, @{text crash} the position up to which P1 had emitted. The
  assumptions:

  \<^item> @{text cmt_le_crash}: the committed offset is at or before the crash.
  \<^item> @{text crash_le_f1}: the crash is at or before P1's frontier, so P1's
    emission reaches the crash. This loses no generality. A connector that
    crashes after P1's frontier has closed every unit of P1 by the crash, and
    P1 with the crash as its frontier is then an instance of this locale
    (@{text pass_restart_after_frontier}, after the locale).
  \<^item> @{text crash_le_f2}: P2's frontier is at or after the crash.
  \<^item> @{text crash_le_lo2}: every re-executed chunk opens at or after the
    crash.
  \<^item> @{text reexec}: every unit of P1 whose close lies after the crash is
    re-read by P2: its domain lies in P2's scope. A connector that
    re-executes every chunk not completed in the committed state, every unit
    whose close lies after @{text cmt}, meets this assumption. So does a
    connector that re-executes only the chunks not closed by the crash. The
    committed offset determines only the re-delivered segment.

  The consumption start @{text s0} is a parameter of the stream, as in
  @{text Orphan_Absence_Composition}. The theorems take two premises on it:
  every unit of P1 starts at or after it, and the committed offset lies at
  or after it (@{text s0cmt}). A commit before the pass started is not
  modeled. No assumption relates P2's units to P1's units beyond
  @{text reexec}.
\<close>

locale pass_restart =
  P1: capture_contract L den \<sigma>0 U1 sc1 f1 +
  P2: capture_contract L den \<sigma>0 U2 sc2 f2
  for L :: "('k, 'v) event list" and den :: "'c \<Rightarrow> nat"
  and \<sigma>0 :: "('k, 'v) state"
  and U1 :: "('k, 'v, 'c) cunit list" and sc1 :: "'k set" and f1 :: 'c
  and U2 :: "('k, 'v, 'c) cunit list" and sc2 :: "'k set" and f2 :: 'c +
  fixes cmt :: 'c and crash :: 'c
  assumes cmt_le_crash: "den cmt \<le> den crash"
      and crash_le_f1: "den crash \<le> den f1"
      and crash_le_f2: "den crash \<le> den f2"
      and crash_le_lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den crash \<le> den (u_lo u)"
      and reexec: "\<And>u. u \<in> set U1 \<Longrightarrow> den crash < den (u_hi u) \<Longrightarrow> u_dom u \<subseteq> sc2"
begin

text \<open>
  The stream the sink sees, as a plain event list: P1's emission cut at the
  crash, then the log segment from @{text cmt} to the crash, then P2's
  emission from the crash. A log event at position @{text q} carries the
  tag @{text "Suc q"}, so the items of P1's emission tagged at most the
  crash are its log events from @{text s0} to just before the crash and its
  close blocks at the positions from @{text s0} to the crash
  (@{text cut_blocks} below). Under the premise @{text s0cmt} of the
  theorems, the log segment from @{text cmt} to the crash is delivered a
  second time.
\<close>

definition restart_stream ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> ('k, 'v) event list" where
  "restart_stream svl1 svl2 s0 =
     map snd (filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0))
     @ map (\<lambda>q. L ! q) [den cmt..<den crash]
     @ P2.emission svl2 crash"

text \<open>
  The two parts as timed lists: the part delivered before the crash, and
  the part delivered after the restart, each item with its position tag.
\<close>

definition cut_t ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "cut_t svl1 s0 = filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0)"

definition resumed_t ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "resumed_t svl2 = map (\<lambda>q. (Suc q, L ! q)) [den cmt..<den crash] @ P2.emission_t svl2 crash"

lemma restart_stream_timed:
  "restart_stream svl1 svl2 s0 = map snd (cut_t svl1 s0) @ map snd (resumed_t svl2)"
  by (simp add: restart_stream_def cut_t_def resumed_t_def P2.emission_def comp_def)

subsubsection \<open>The part before the crash is P1's emission run up to the crash\<close>

lemma restart_cut_prefix:
  "prefix (map snd (filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0)))
          (P1.emission svl1 s0)"
proof -
  have "filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0)
          = takeWhile (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0)"
    by (rule filter_tag_le_sorted[OF P1.emission_t_sorted])
  then have "prefix (filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0))
                    (P1.emission_t svl1 s0)"
    by (simp add: takeWhile_is_prefix)
  then show ?thesis unfolding P1.emission_def by (rule map_mono_prefix)
qed

text \<open>
  When the consumption start is at or before the crash, the part before the
  crash is block by block the emission of P1 with the crash in place of the
  frontier: the close blocks at the positions from @{text s0} to the crash,
  and the log events at the positions from @{text s0} to just before the
  crash. The hypothesis holds under the premise @{text s0cmt} of the
  theorems, by @{text cmt_le_crash}.
\<close>

lemma cut_blocks:
  assumes s0c: "den s0 \<le> den crash"
  shows "cut_t svl1 s0 =
           concat (map (\<lambda>q. P1.closes_at svl1 q @ [(Suc q, L ! q)]) [den s0..<den crash])
           @ P1.closes_at svl1 (den crash)"
proof -
  define G where "G = (\<lambda>q. P1.closes_at svl1 q @ [(Suc q, L ! q)])"
  define Q where "Q = (\<lambda>x :: nat \<times> ('k, 'v) event. fst x \<le> den crash)"
  have closes_tag: "fst x = q" if "x \<in> set (P1.closes_at svl1 q)" for x q
    using that by (rule P1.closes_at_tag)
  have G_tag: "fst x = q \<or> fst x = Suc q" if xq: "x \<in> set (G q)" for x q
  proof -
    have "x \<in> set (P1.closes_at svl1 q) \<or> x = (Suc q, L ! q)" using xq by (auto simp: G_def)
    then show ?thesis
    proof
      assume "x \<in> set (P1.closes_at svl1 q)"
      then have "fst x = q" by (rule closes_tag)
      then show ?thesis ..
    next
      assume "x = (Suc q, L ! q)"
      then show ?thesis by simp
    qed
  qed
  have before: "filter Q (concat (map G [den s0..<den crash]))
                  = concat (map G [den s0..<den crash])"
  proof (rule filter_True, intro ballI)
    fix x assume "x \<in> set (concat (map G [den s0..<den crash]))"
    then obtain q where q: "q < den crash" and xq: "x \<in> set (G q)" by auto
    show "Q x" using G_tag[OF xq] q by (auto simp: Q_def)
  qed
  have at_crash: "filter Q (P1.closes_at svl1 (den crash)) = P1.closes_at svl1 (den crash)"
  proof (rule filter_True, intro ballI)
    fix x assume "x \<in> set (P1.closes_at svl1 (den crash))"
    then have "fst x = den crash" by (rule closes_tag)
    then show "Q x" by (simp add: Q_def)
  qed
  consider (inside) "den crash < den f1" | (at_end) "den crash = den f1"
    using crash_le_f1 by linarith
  then show ?thesis
  proof cases
    case inside
    have split: "[den s0..<den f1] = [den s0..<den crash] @ [den crash..<den f1]"
      by (rule upt_split[OF s0c crash_le_f1])
    have head: "[den crash..<den f1] = den crash # [Suc (den crash)..<den f1]"
      using inside by (simp add: upt_rec)
    have mid: "filter Q (G (den crash)) = P1.closes_at svl1 (den crash)"
      using at_crash by (simp add: G_def Q_def)
    have after: "filter Q (concat (map G [Suc (den crash)..<den f1])) = []"
    proof (rule filter_False, intro ballI)
      fix x assume "x \<in> set (concat (map G [Suc (den crash)..<den f1]))"
      then obtain q where q: "Suc (den crash) \<le> q" and xq: "x \<in> set (G q)" by auto
      show "\<not> Q x" using G_tag[OF xq] q by (auto simp: Q_def)
    qed
    have trail: "filter Q (P1.closes_at svl1 (den f1)) = []"
    proof (rule filter_False, intro ballI)
      fix x assume "x \<in> set (P1.closes_at svl1 (den f1))"
      then have "fst x = den f1" by (rule closes_tag)
      then show "\<not> Q x" using inside by (simp add: Q_def)
    qed
    have "cut_t svl1 s0
            = filter Q (concat (map G [den s0..<den f1]) @ P1.closes_at svl1 (den f1))"
      by (simp add: cut_t_def P1.emission_t_def G_def Q_def)
    also have "\<dots> = filter Q (concat (map G [den s0..<den crash])) @ filter Q (G (den crash))
                    @ filter Q (concat (map G [Suc (den crash)..<den f1]))
                    @ filter Q (P1.closes_at svl1 (den f1))"
      by (simp add: split head)
    also have "\<dots> = concat (map G [den s0..<den crash]) @ P1.closes_at svl1 (den crash)"
      unfolding before mid after trail by simp
    finally show ?thesis by (simp add: G_def)
  next
    case at_end
    have all: "filter Q (P1.emission_t svl1 s0) = P1.emission_t svl1 s0"
    proof (rule filter_True, intro ballI)
      fix x assume "x \<in> set (P1.emission_t svl1 s0)"
      then have "fst x \<le> den f1" by (rule P1.emission_t_tag_le)
      then show "Q x" using at_end by (simp add: Q_def)
    qed
    have "cut_t svl1 s0 = P1.emission_t svl1 s0"
      using all by (simp add: cut_t_def Q_def)
    also have "\<dots> = concat (map G [den s0..<den crash]) @ P1.closes_at svl1 (den crash)"
      using at_end by (simp add: P1.emission_t_def G_def)
    finally show ?thesis by (simp add: G_def)
  qed
qed

text \<open>
  With the committed offset and the crash both at P1's frontier nothing is
  re-delivered. P1 and P2 then form an instance of the locale
  @{text pass_then_read} of @{text Orphan_Absence_Composition}, and the
  stream is P1's emission followed by P2's emission from P1's frontier,
  which is that locale's stream @{text composed} by its definition.
\<close>

lemma restart_at_frontier_read_after:
  assumes crash_f1: "den crash = den f1"
  shows "pass_then_read L den \<sigma>0 U1 sc1 f1 U2 sc2 f2"
  by unfold_locales (use crash_f1 crash_le_f2 crash_le_lo2 in auto)

lemma restart_at_frontier:
  assumes cmt_f1: "den cmt = den f1" and crash_f1: "den crash = den f1"
  shows "restart_stream svl1 svl2 s0 = P1.emission svl1 s0 @ P2.emission svl2 f1"
proof -
  have all: "filter (\<lambda>x. fst x \<le> den crash) (P1.emission_t svl1 s0) = P1.emission_t svl1 s0"
  proof (rule filter_True, intro ballI)
    fix x assume "x \<in> set (P1.emission_t svl1 s0)"
    then have "fst x \<le> den f1" by (rule P1.emission_t_tag_le)
    then show "fst x \<le> den crash" using crash_f1 by simp
  qed
  have no_seg: "[den cmt..<den crash] = []" using cmt_f1 crash_f1 by simp
  have same_start: "P2.emission svl2 crash = P2.emission svl2 f1"
    using crash_f1 by (simp add: P2.emission_def P2.emission_t_def)
  show ?thesis
    unfolding restart_stream_def all no_seg same_start by (simp add: P1.emission_def)
qed

subsubsection \<open>Tags, values and completeness of the two parts\<close>

lemma cut_item:
  assumes "x \<in> set (cut_t svl1 s0)"
  shows "x \<in> set (P1.emission_t svl1 s0)"
  using assms by (simp add: cut_t_def)

lemma cut_tag_le:
  assumes "x \<in> set (cut_t svl1 s0)"
  shows "fst x \<le> den crash"
  using assms by (simp add: cut_t_def)

lemma cut_sorted: "sorted (map fst (cut_t svl1 s0))"
  unfolding cut_t_def by (rule sorted_map_fst_filter[OF P1.emission_t_sorted])

lemma cut_honest:
  assumes svl1: "P1.svl_ok2 svl1" and x: "x \<in> set (cut_t svl1 s0)"
  shows "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) (ev_key (snd x))"
  by (rule P1.emission_item_honest[OF svl1 cut_item[OF x]])

text \<open>The part before the crash carries every log event from @{text s0} to the crash.\<close>

lemma cut_complete:
  assumes s0q: "den s0 \<le> q" and q: "q < den crash" and key: "ev_key (L ! q) = k"
  shows "(Suc q, L ! q) \<in> set (P1.titems_for k (cut_t svl1 s0))"
proof -
  have "q < den f1" using q crash_le_f1 by simp
  then have "(Suc q, L ! q) \<in> set (P1.emission_t svl1 s0)"
    by (rule P1.emission_t_event_in[OF s0q])
  then show ?thesis using q key by (simp add: cut_t_def P1.titems_for_def)
qed

lemma resumed_item_cases:
  assumes "x \<in> set (resumed_t svl2)"
  obtains (redelivered) q where "den cmt \<le> q" "q < den crash" "x = (Suc q, L ! q)"
    | (re_executed) "x \<in> set (P2.emission_t svl2 crash)"
proof -
  have "(\<exists>q. den cmt \<le> q \<and> q < den crash \<and> x = (Suc q, L ! q))
        \<or> x \<in> set (P2.emission_t svl2 crash)"
    using assms unfolding resumed_t_def by auto
  then show thesis using that by blast
qed

lemma resumed_tag_ge:
  assumes "x \<in> set (resumed_t svl2)"
  shows "den cmt \<le> fst x"
  using assms
proof (cases rule: resumed_item_cases)
  case (redelivered q)
  then show ?thesis by simp
next
  case re_executed
  have "den crash \<le> fst x \<or> fst x = den f2" by (rule P2.emission_t_tag_ge[OF re_executed])
  then show ?thesis using cmt_le_crash crash_le_f2 by auto
qed

lemma resumed_tag_le:
  assumes "x \<in> set (resumed_t svl2)"
  shows "fst x \<le> den f2"
  using assms
proof (cases rule: resumed_item_cases)
  case (redelivered q)
  then show ?thesis using crash_le_f2 by simp
next
  case re_executed
  then show ?thesis by (rule P2.emission_t_tag_le)
qed

text \<open>
  The part after the restart is in position order: the re-delivered events
  are tagged at most the crash, and P2's items at least the crash.
\<close>

lemma resumed_sorted: "sorted (map fst (resumed_t svl2))"
proof -
  have s1: "sorted (map Suc [den cmt..<den crash])" by (rule sorted_map_Suc) simp
  have s2: "sorted (map fst (P2.emission_t svl2 crash))" by (rule P2.emission_t_sorted)
  have cross: "a \<le> b"
    if a: "a \<in> set (map Suc [den cmt..<den crash])"
    and b: "b \<in> set (map fst (P2.emission_t svl2 crash))" for a b
  proof -
    have a_le: "a \<le> den crash" using a by auto
    obtain x where x: "x \<in> set (P2.emission_t svl2 crash)" and bx: "b = fst x"
      using b by auto
    have "den crash \<le> fst x \<or> fst x = den f2" by (rule P2.emission_t_tag_ge[OF x])
    then have "den crash \<le> b" using bx crash_le_f2 by auto
    then show ?thesis using a_le by simp
  qed
  have "sorted (map Suc [den cmt..<den crash] @ map fst (P2.emission_t svl2 crash))"
    unfolding sorted_append using s1 s2 cross by blast
  then show ?thesis by (simp add: resumed_t_def comp_def)
qed

lemma resumed_honest:
  assumes svl2: "P2.svl_ok2 svl2" and x: "x \<in> set (resumed_t svl2)"
  shows "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) (ev_key (snd x))"
  using x
proof (cases rule: resumed_item_cases)
  case (redelivered q)
  have q_len: "q < length L" using redelivered(2) P1.den_le_len[of crash] by simp
  have "ev_img (L ! q) = state_after \<sigma>0 (take (Suc q) L) (ev_key (L ! q))"
    by (rule event_honest[OF q_len refl])
  then show ?thesis using redelivered(3) by simp
next
  case re_executed
  then show ?thesis by (rule P2.emission_item_honest[OF svl2])
qed

text \<open>The part after the restart carries every log event from @{text cmt} to @{text f2}.\<close>

lemma resumed_complete:
  assumes cq: "den cmt \<le> q" and q: "q < den f2" and key: "ev_key (L ! q) = k"
  shows "(Suc q, L ! q) \<in> set (P1.titems_for k (resumed_t svl2))"
proof (cases "q < den crash")
  case True
  have "q \<in> set [den cmt..<den crash]" using cq True by simp
  then have "(Suc q, L ! q) \<in> (\<lambda>q. (Suc q, L ! q)) ` set [den cmt..<den crash]"
    by (rule rev_image_eqI) simp
  then have "(Suc q, L ! q) \<in> set (map (\<lambda>q. (Suc q, L ! q)) [den cmt..<den crash])"
    by (simp only: set_map)
  then show ?thesis using key by (simp add: resumed_t_def P1.titems_for_def)
next
  case False
  then have "den crash \<le> q" by simp
  then have "(Suc q, L ! q) \<in> set (P2.emission_t svl2 crash)"
    by (rule P2.emission_t_event_in[OF _ q])
  then show ?thesis using key by (simp add: resumed_t_def P1.titems_for_def)
qed

subsubsection \<open>A key with an item ends at the source state\<close>

text \<open>
  If the part after the restart has an item for the key, that part decides
  the key, and it ends at the source state at @{text f2}, from any state
  the part before the crash left.
\<close>

lemma resumed_key_replay:
  assumes svl2: "P2.svl_ok2 svl2"
      and ne: "P1.titems_for k (resumed_t svl2) \<noteq> []"
  shows "state_after D (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
proof -
  define T where "T = P1.titems_for k (resumed_t svl2)"
  define D1 where "D1 = state_after D (map snd (cut_t svl1 s0))"
  have T_ne: "T \<noteq> []" using ne by (simp add: T_def)
  have T_item: "x \<in> set (resumed_t svl2)" and T_key: "ev_key (snd x) = k"
    if "x \<in> set T" for x
    using that by (simp_all add: T_def P1.titems_for_def)
  have keyed: "\<And>x. x \<in> set T \<Longrightarrow> ev_key (snd x) = k" by (rule T_key)
  have honest: "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k" if "x \<in> set T" for x
    using resumed_honest[OF svl2 T_item[OF that]] T_key[OF that] by simp
  have sorted: "sorted (map fst T)"
    unfolding T_def P1.titems_for_def by (rule sorted_map_fst_filter[OF resumed_sorted])
  have low: "den cmt \<le> fst x" if "x \<in> set T" for x
    by (rule resumed_tag_ge[OF T_item[OF that]])
  have high: "fst x \<le> den f2" if "x \<in> set T" for x
    by (rule resumed_tag_le[OF T_item[OF that]])
  have complete: "(Suc q, L ! q) \<in> set T"
    if "den cmt \<le> q" "q < den f2" "ev_key (L ! q) = k" for q
    unfolding T_def by (rule resumed_complete[OF that])
  have "state_after D (restart_stream svl1 svl2 s0) k
          = state_after D1 (map snd (resumed_t svl2)) k"
    by (simp add: restart_stream_timed state_after_append D1_def)
  also have "\<dots> = state_after D1 (map snd T) k"
    by (rule replay_per_key) (simp add: P1.evs_for_map_snd T_def P1.titems_for_def)
  also have "\<dots> = state_after \<sigma>0 (take (den f2) L) k"
    by (rule honest_stream_last[OF T_ne keyed honest sorted low high complete])
  also have "\<dots> = state_after \<sigma>0 (P1.pfx f2) k"
    by (simp add: P1.pfx_def)
  finally show ?thesis .
qed

text \<open>
  If the part after the restart has nothing for the key, but the part
  before the crash has, the key has no log event from @{text cmt} to
  @{text f2}, and the last item of the part before the crash decides. Every
  tag of that part lies at or after @{text s0}: it does so, or it is P1's
  frontier, which lies after @{text s0} by @{text s0cmt}. So the list of the
  key's items before the crash carries every log event of the key from
  @{text s0} up to @{text f2}, and the key ends at the source state at
  @{text f2}. This covers the close entry of a unit that closed after
  @{text cmt} and at or before the crash, which P2 need not list again.
\<close>

lemma cut_key_replay:
  assumes svl1: "P1.svl_ok2 svl1"
      and s0cmt: "den s0 \<le> den cmt"
      and none_after: "P1.titems_for k (resumed_t svl2) = []"
      and ne: "P1.titems_for k (cut_t svl1 s0) \<noteq> []"
  shows "state_after D (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
proof -
  define T where "T = P1.titems_for k (cut_t svl1 s0)"
  have T_ne: "T \<noteq> []" using ne by (simp add: T_def)
  have T_item: "x \<in> set (cut_t svl1 s0)" and T_key: "ev_key (snd x) = k"
    if "x \<in> set T" for x
    using that by (simp_all add: T_def P1.titems_for_def)
  have keyed: "\<And>x. x \<in> set T \<Longrightarrow> ev_key (snd x) = k" by (rule T_key)
  have honest: "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k" if "x \<in> set T" for x
    using cut_honest[OF svl1 T_item[OF that]] T_key[OF that] by simp
  have sorted: "sorted (map fst T)"
    unfolding T_def P1.titems_for_def by (rule sorted_map_fst_filter[OF cut_sorted])
  have low: "den s0 \<le> fst x" if "x \<in> set T" for x
  proof -
    have "den s0 \<le> fst x \<or> fst x = den f1"
      by (rule P1.emission_t_tag_ge[OF cut_item[OF T_item[OF that]]])
    then show ?thesis using s0cmt cmt_le_crash crash_le_f1 by auto
  qed
  have high: "fst x \<le> den f2" if "x \<in> set T" for x
    using cut_tag_le[OF T_item[OF that]] crash_le_f2 by simp
  have complete: "(Suc q, L ! q) \<in> set T"
    if q: "den s0 \<le> q" "q < den f2" and key: "ev_key (L ! q) = k" for q
  proof (cases "den cmt \<le> q")
    case True
    have "(Suc q, L ! q) \<in> set (P1.titems_for k (resumed_t svl2))"
      by (rule resumed_complete[OF True q(2) key])
    with none_after show ?thesis by simp
  next
    case False
    have q_crash: "q < den crash" using False cmt_le_crash by simp
    show ?thesis unfolding T_def by (rule cut_complete[OF q(1) q_crash key])
  qed
  have T_fix: "P1.titems_for k T = T" by (simp add: T_def P1.titems_for_def)
  have evs_T: "evs_for k (map snd T) = map snd T"
    using T_fix by (simp add: P1.evs_for_map_snd)
  have evs_S: "evs_for k (restart_stream svl1 svl2 s0) = map snd T"
    using none_after by (simp add: restart_stream_timed P1.evs_for_map_snd T_def)
  have "state_after D (restart_stream svl1 svl2 s0) k = state_after D (map snd T) k"
    by (rule replay_per_key) (simp only: evs_S evs_T)
  also have "\<dots> = state_after \<sigma>0 (take (den f2) L) k"
    by (rule honest_stream_last[OF T_ne keyed honest sorted low high complete])
  also have "\<dots> = state_after \<sigma>0 (P1.pfx f2) k"
    by (simp add: P1.pfx_def)
  finally show ?thesis .
qed

subsubsection \<open>Safety and convergence\<close>

text \<open>
  Safety. A key of either scope ends at the source state at @{text f2}, or
  the stream has no item for it at all. In the second case the sink keeps
  its initial value, and the key is absent at @{text f2}: if P2 covers it,
  because P2 does not list it and it is quiet from the crash on; otherwise
  its unit in P1 closed at or before the crash (by @{text reexec}), so its
  close block was delivered before the crash without it. No unit of P1 that
  closed at or before the crash lists it, P2 does not list it, and no log
  event from @{text s0} to @{text f2} mentions it. In particular no unit of
  P1 that closed at or before @{text cmt} lists it. The theorem speaks
  about the sink after the whole stream, at P2's frontier.
\<close>

theorem restart_safe:
  assumes svl1: "P1.svl_ok2 svl1" and svl2: "P2.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0cmt: "den s0 \<le> den cmt"
      and k: "k \<in> sc1 \<union> sc2"
  shows "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k
         \<or> (state_after D0 (restart_stream svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P1.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> den (u_hi (P1.the_unit k)) \<le> den crash
                 \<longrightarrow> k \<notin> set (svl1 (P1.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (P2.the_unit k)))
            \<and> evs_for k (P1.win s0 f2) = [])"
proof -
  define A where "A = P1.titems_for k (cut_t svl1 s0)"
  define B where "B = P1.titems_for k (resumed_t svl2)"
  consider (resumed) "B \<noteq> []" | (cut) "B = []" "A \<noteq> []" | (silent) "B = []" "A = []"
    by blast
  then show ?thesis
  proof cases
    case resumed
    have "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
      by (rule resumed_key_replay[OF svl2 resumed[unfolded B_def]])
    then show ?thesis ..
  next
    case cut
    have "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
      by (rule cut_key_replay[OF svl1 s0cmt cut(1)[unfolded B_def] cut(2)[unfolded A_def]])
    then show ?thesis ..
  next
    case silent
    have none_cut: "P1.titems_for k (cut_t svl1 s0) = []" using silent(2) by (simp add: A_def)
    have none_res: "P1.titems_for k (resumed_t svl2) = []" using silent(1) by (simp add: B_def)
    have kept: "state_after D0 (restart_stream svl1 svl2 s0) k = D0 k"
    proof -
      have "evs_for k (restart_stream svl1 svl2 s0) = []"
        by (simp add: restart_stream_timed P1.evs_for_map_snd none_cut none_res)
      then show ?thesis by (rule state_after_no_events)
    qed
    have quiet_from_cmt: "ev_key (L ! q) \<noteq> k" if q: "den cmt \<le> q" "q < den f2" for q
    proof
      assume key: "ev_key (L ! q) = k"
      have "(Suc q, L ! q) \<in> set (P1.titems_for k (resumed_t svl2))"
        by (rule resumed_complete[OF q key])
      with none_res show False by simp
    qed
    have quiet_pos: "ev_key (L ! q) \<noteq> k" if q: "den s0 \<le> q" "q < den f2" for q
    proof (cases "q < den crash")
      case True
      show ?thesis
      proof
        assume key: "ev_key (L ! q) = k"
        have "(Suc q, L ! q) \<in> set (P1.titems_for k (cut_t svl1 s0))"
          by (rule cut_complete[OF q(1) True key])
        with none_cut show False by simp
      qed
    next
      case False
      then have "den cmt \<le> q" using cmt_le_crash by simp
      then show ?thesis by (rule quiet_from_cmt[OF _ q(2)])
    qed
    have quiet: "evs_for k (P1.win s0 f2) = []"
      by (rule P1.evs_for_win_quiet) (rule quiet_pos)
    have quiet_crash: "evs_for k (P1.win crash f2) = []"
    proof (rule P1.evs_for_win_quiet)
      fix q assume q: "den crash \<le> q" "q < den f2"
      have "den cmt \<le> q" using q(1) cmt_le_crash by simp
      then show "ev_key (L ! q) \<noteq> k" by (rule quiet_from_cmt[OF _ q(2)])
    qed
    have P2_unlisted: "k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (P2.the_unit k))"
    proof
      assume k2: "k \<in> sc2"
      show "k \<notin> set (svl2 (P2.the_unit k))"
      proof
        assume listed: "k \<in> set (svl2 (P2.the_unit k))"
        define u where "u = P2.the_unit k"
        have u_in: "u \<in> set U2" using P2.the_unit_props(1)[OF k2] by (simp add: u_def)
        have crash_hi: "den crash \<le> den (u_hi u)"
          using crash_le_lo2[OF u_in] P2.bracket_lo_hi[OF u_in] by (simp add: P1.cle_def)
        have "(den (u_hi u), Event k (u_refresh u k)) \<in> set (P2.emission_t svl2 crash)"
          by (rule P2.close_entry_in_emission[where svl = svl2, OF u_in listed[folded u_def] crash_hi])
        then have "(den (u_hi u), Event k (u_refresh u k))
                     \<in> set (P1.titems_for k (resumed_t svl2))"
          by (simp add: resumed_t_def P1.titems_for_def)
        with none_res show False by simp
      qed
    qed
    have P1_unlisted: "k \<in> sc1 \<longrightarrow> den (u_hi (P1.the_unit k)) \<le> den crash
                         \<longrightarrow> k \<notin> set (svl1 (P1.the_unit k))"
    proof (intro impI)
      assume k1: "k \<in> sc1" and hi_crash: "den (u_hi (P1.the_unit k)) \<le> den crash"
      show "k \<notin> set (svl1 (P1.the_unit k))"
      proof
        assume listed: "k \<in> set (svl1 (P1.the_unit k))"
        define u where "u = P1.the_unit k"
        have u_in: "u \<in> set U1" using P1.the_unit_props(1)[OF k1] by (simp add: u_def)
        have s0_hi: "den s0 \<le> den (u_hi u)"
          using s0lo[OF u_in] P1.bracket_lo_hi[OF u_in] by (simp add: P1.cle_def)
        have "(den (u_hi u), Event k (u_refresh u k)) \<in> set (P1.emission_t svl1 s0)"
          by (rule P1.close_entry_in_emission[where svl = svl1, OF u_in listed[folded u_def] s0_hi])
        then have "(den (u_hi u), Event k (u_refresh u k))
                     \<in> set (P1.titems_for k (cut_t svl1 s0))"
          using hi_crash by (simp add: cut_t_def P1.titems_for_def u_def)
        with none_cut show False by simp
      qed
    qed
    have src_none: "state_after \<sigma>0 (P1.pfx f2) k = None"
    proof (cases "k \<in> sc2")
      case k2: True
      have nl2: "k \<notin> set (svl2 (P2.the_unit k))" using P2_unlisted k2 by simp
      have P2_lo: "\<And>u. u \<in> set U2 \<Longrightarrow> P1.cle crash (u_lo u)"
        using crash_le_lo2 by (simp add: P1.cle_def)
      show ?thesis by (rule P2.unlisted_quiet_absent[OF svl2 P2_lo k2 nl2 quiet_crash])
    next
      case k2: False
      then have k1: "k \<in> sc1" using k by simp
      define u where "u = P1.the_unit k"
      have u_in: "u \<in> set U1" and k_dom: "k \<in> u_dom u"
        using P1.the_unit_props[OF k1] by (simp_all add: u_def)
      have hi_crash: "den (u_hi u) \<le> den crash"
      proof (rule ccontr)
        assume "\<not> den (u_hi u) \<le> den crash"
        then have "u_dom u \<subseteq> sc2" using reexec[OF u_in] by simp
        with k_dom k2 show False by auto
      qed
      have nl1: "k \<notin> set (svl1 (P1.the_unit k))"
        using P1_unlisted k1 hi_crash by (simp add: u_def)
      have s0_lo: "P1.cle s0 (u_lo (P1.the_unit k))"
        using s0lo[OF u_in] by (simp add: P1.cle_def u_def)
      have hi_f2: "P1.cle (u_hi (P1.the_unit k)) f2"
        using hi_crash crash_le_f2 by (simp add: P1.cle_def u_def)
      show ?thesis by (rule P1.unlisted_quiet_absent_at[OF svl1 k1 s0_lo hi_f2 nl1 quiet])
    qed
    show ?thesis using kept src_none P1_unlisted P2_unlisted quiet by blast
  qed
qed

text \<open>
  Convergence. Every key the sink holds that is absent at @{text f2} and
  quiet from @{text s0} to @{text f2} must be listed, either by the close
  entry of its unit in P1, when that unit closed at or before the crash, or
  by P2.
\<close>

theorem restart_converges:
  assumes svl1: "P1.svl_ok2 svl1" and svl2: "P2.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0cmt: "den s0 \<le> den cmt"
      and cover: "\<And>k. k \<in> sc1 \<union> sc2 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow>
                    state_after \<sigma>0 (P1.pfx f2) k = None \<Longrightarrow>
                    evs_for k (P1.win s0 f2) = [] \<Longrightarrow>
                    (k \<in> sc1 \<and> den (u_hi (P1.the_unit k)) \<le> den crash
                       \<and> k \<in> set (svl1 (P1.the_unit k))) \<or>
                    (k \<in> sc2 \<and> k \<in> set (svl2 (P2.the_unit k)))"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
proof
  fix k assume k: "k \<in> sc1 \<union> sc2"
  have disj: "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k
         \<or> (state_after D0 (restart_stream svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P1.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> den (u_hi (P1.the_unit k)) \<le> den crash
                 \<longrightarrow> k \<notin> set (svl1 (P1.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (P2.the_unit k)))
            \<and> evs_for k (P1.win s0 f2) = [])"
    by (rule restart_safe[OF svl1 svl2 s0lo s0cmt k])
  from disj show "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
  proof
    assume "state_after D0 (restart_stream svl1 svl2 s0) k = state_after \<sigma>0 (P1.pfx f2) k"
    then show ?thesis .
  next
    assume o: "state_after D0 (restart_stream svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P1.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> den (u_hi (P1.the_unit k)) \<le> den crash
                 \<longrightarrow> k \<notin> set (svl1 (P1.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (P2.the_unit k)))
            \<and> evs_for k (P1.win s0 f2) = []"
    show ?thesis
    proof (cases "D0 k = None")
      case True
      then show ?thesis using o by simp
    next
      case False
      have src_none: "state_after \<sigma>0 (P1.pfx f2) k = None" using o by simp
      have quiet: "evs_for k (P1.win s0 f2) = []" using o by simp
      have "(k \<in> sc1 \<and> den (u_hi (P1.the_unit k)) \<le> den crash
               \<and> k \<in> set (svl1 (P1.the_unit k))) \<or>
            (k \<in> sc2 \<and> k \<in> set (svl2 (P2.the_unit k)))"
        by (rule cover[OF k False src_none quiet])
      then show ?thesis using o by auto
    qed
  qed
qed

end  (* locale pass_restart *)

text \<open>
  A crash after P1's frontier. Every unit of P1 has closed by the crash, so
  P1 with the crash as its frontier is a capture contract
  (@{text contract_with_frontier}), and together with P2 it is an instance
  of @{text pass_restart}. The assumption @{text reexec} holds because no
  unit of P1 closes after the crash. The first part of that instance's
  stream is the whole emission of P1 with the crash as its frontier. That
  this equals P1's own emission followed by the log events from P1's
  frontier to the crash is argued in prose and not stated as a lemma.
\<close>

lemma pass_restart_after_frontier:
  assumes P1: "capture_contract L den \<sigma>0 U1 sc1 f1"
      and P2: "capture_contract L den \<sigma>0 U2 sc2 f2"
      and f1_crash: "den f1 \<le> den crash"
      and cmt_crash: "den cmt \<le> den crash"
      and crash_f2: "den crash \<le> den f2"
      and crash_lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den crash \<le> den (u_lo u)"
  shows "pass_restart L den \<sigma>0 U1 sc1 crash U2 sc2 f2 cmt crash"
proof -
  interpret Q1: capture_contract L den \<sigma>0 U1 sc1 f1 by (rule P1)
  have hi_crash: "den (u_hi u) \<le> den crash" if u: "u \<in> set U1" for u
    using Q1.bracket_hi_f[OF u] f1_crash by (simp add: Q1.cle_def)
  have P1': "capture_contract L den \<sigma>0 U1 sc1 crash"
    by (rule Q1.contract_with_frontier) (use hi_crash in \<open>simp add: Q1.cle_def\<close>)
  interpret Q1': capture_contract L den \<sigma>0 U1 sc1 crash by (rule P1')
  interpret Q2: capture_contract L den \<sigma>0 U2 sc2 f2 by (rule P2)
  show ?thesis
  proof (unfold_locales)
    show "den cmt \<le> den crash" by (rule cmt_crash)
  next
    show "den crash \<le> den crash" by simp
  next
    show "den crash \<le> den f2" by (rule crash_f2)
  next
    fix u assume "u \<in> set U2"
    then show "den crash \<le> den (u_lo u)" by (rule crash_lo2)
  next
    fix u assume u: "u \<in> set U1" and late: "den crash < den (u_hi u)"
    have "den (u_hi u) \<le> den crash" by (rule hi_crash[OF u])
    with late show "u_dom u \<subseteq> sc2" by simp
  qed
qed

subsection \<open>Fixtures: an orphan stays removed, a live row stays live\<close>

text \<open>
  The orphan and re-insert fixtures use the witness log
  @{text "L_s = [Event 3 (Some 7), Event 1 (Some 1)]"} with
  @{text "den_w c = min c 2"}, and a crash at position 2, after the whole
  log. The first is the orphan fixture of @{text Orphan_Absence}: one chunk
  owns keys 3 and 4 with bracket (1, 2], reads key 3 as present and key 4
  as absent, and closes at position 2. The sink holds the orphan key 4. The
  connector had committed offset 1, before the close, so on restart it
  delivers the event at position 1 again and re-executes the chunk with
  bracket (2, 2]. The re-executed chunk uses the core's survivor-only
  enumeration and does not list key 4. The close entry delivered before the
  crash does, and the orphan stays removed.
\<close>

definition rx_unit :: "(nat, nat, nat) cunit" where
  "rx_unit = \<lparr>u_dom = {3, 4}, u_lo = 2, u_hi = 2,
              u_refresh = (\<lambda>k. if k = 3 then Some 7 else None)\<rparr>"

interpretation rx: capture_contract L_s den_w s0_w "[rx_unit]" "{3, 4}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [rx_unit]. u_dom u) = {3, 4}"
    by (simp add: rx_unit_def)
next
  fix i j
  assume "i < length [rx_unit]" "j < length [rx_unit]" "i \<noteq> j"
  then show "u_dom ([rx_unit] ! i) \<inter> u_dom ([rx_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [rx_unit]"
  then show "sc.cle (u_lo u) (u_hi u)"
    by (simp add: rx_unit_def sc.cle_def den_w_def)
next
  fix u assume "u \<in> set [rx_unit]"
  then show "sc.cle (u_hi u) 2"
    by (simp add: rx_unit_def sc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [rx_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. sc.cle (u_lo u) c \<and> sc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (sc.pfx c) k"
    unfolding sc.cle_def sc.pfx_def
    by (intro exI[of _ 2])
       (auto simp add: rx_unit_def den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
qed

interpretation rs: pass_restart L_s den_w s0_w "[orph_unit]" "{3, 4}" 2
                     "[rx_unit]" "{3, 4}" 2 1 2
  by unfold_locales (simp_all add: den_w_def orph_unit_def rx_unit_def)

lemma rx_svl_ok2: "rx.svl_ok2 (\<lambda>_. [3])"
proof -
  have win: "sc.win (u_lo rx_unit) (u_hi rx_unit) = []"
    unfolding sc.win_def by (simp add: rx_unit_def den_w_def)
  have "rx.survivors rx_unit = {3}"
    using win by (auto simp: rx.survivors_def rx_unit_def)
  then show ?thesis by (simp add: rx.svl_ok2_def)
qed

text \<open>
  The stream, computed: P1's emission up to the crash (here all of it, with
  the absent entry for key 4 at its close), the event at position 1 again,
  and the re-executed chunk's entry for key 3.
\<close>

lemma wit_restart_stream_orphan:
  "rs.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0
     = [Event 3 (Some 7), Event 1 (Some 1), Event 3 (Some 7), Event 4 None,
        Event 1 (Some 1), Event 3 (Some 7)]"
  unfolding rs.restart_stream_def orph.emission_t_def rx.emission_def rx.emission_t_def
            orph.closes_at_def rx.closes_at_def orph.close_block_def rx.close_block_def
  by (simp add: orph_unit_def rx_unit_def den_w_def L_s_def upt_rec)

text \<open>
  The orphan stays removed, through the convergence theorem: key 4 is
  listed by the close entry of its unit in P1, which closed at the crash.
\<close>

lemma wit_restart_orphan_stays_removed:
  "state_after D0_o (rs.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0) 4 = None"
proof -
  have s0cmt: "den_w 0 \<le> den_w 1" by (simp add: den_w_def)
  have conv: "\<forall>k \<in> {3, 4} \<union> {3, 4}.
      state_after D0_o (rs.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0) k
        = state_after s0_w (sc.pfx 2) k"
  proof (rule rs.restart_converges[OF orph_svl_ok2 rx_svl_ok2 orph_s0lo_den s0cmt])
    fix k :: nat
    assume "k \<in> {3, 4} \<union> {3, 4}" and "D0_o k \<noteq> None"
    then have k4: "k = 4" by (auto simp: D0_o_def)
    show "(k \<in> {3, 4} \<and> den_w (u_hi (orph.the_unit k)) \<le> den_w 2
             \<and> k \<in> set ((\<lambda>_. [3, 4]) (orph.the_unit k))) \<or>
          (k \<in> {3, 4} \<and> k \<in> set ((\<lambda>_. [3]) (rx.the_unit k)))"
      using k4 by (simp add: den_w_def)
  qed
  then show ?thesis using src_4_none by simp
qed

text \<open>
  For contrast, the same pass crashes at position 1, before its chunk
  closes, with the same committed offset. The absent entry for key 4 is
  never delivered, nothing is re-delivered, and the re-executed chunk does
  not list key 4. The orphan stays. Key 4 is in the second branch of
  @{text restart_safe} (@{text wit_restart_before_close_second_branch}),
  and not in the first, since the sink keeps value 9 while the source has
  no row. The coverage premise of @{text restart_converges} fails for key 4
  (@{text wit_restart_before_close_cover_fails}).
\<close>

interpretation rs0: pass_restart L_s den_w s0_w "[orph_unit]" "{3, 4}" 2
                      "[rx_unit]" "{3, 4}" 2 1 1
  by unfold_locales (simp_all add: den_w_def orph_unit_def rx_unit_def)

lemma wit_restart_stream_before_close:
  "rs0.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0
     = [Event 3 (Some 7), Event 1 (Some 1), Event 3 (Some 7)]"
  unfolding rs0.restart_stream_def orph.emission_t_def rx.emission_def rx.emission_t_def
            orph.closes_at_def rx.closes_at_def orph.close_block_def rx.close_block_def
  by (simp add: orph_unit_def rx_unit_def den_w_def L_s_def upt_rec)

lemma wit_restart_before_close_keeps_orphan:
  "state_after D0_o (rs0.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0) 4 = Some 9"
  unfolding wit_restart_stream_before_close
  by (simp add: D0_o_def state_after_def apply_ev_def)

lemma wit_restart_before_close_second_branch:
  "state_after D0_o (rs0.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0) 4 = D0_o 4
   \<and> state_after s0_w (sc.pfx 2) 4 = None
   \<and> (4 \<in> {3, 4::nat} \<longrightarrow> den_w (u_hi (orph.the_unit 4)) \<le> den_w 1
        \<longrightarrow> 4 \<notin> set ((\<lambda>_. [3, 4::nat]) (orph.the_unit 4)))
   \<and> (4 \<in> {3, 4::nat} \<longrightarrow> 4 \<notin> set ((\<lambda>_. [3::nat]) (rx.the_unit 4)))
   \<and> evs_for 4 (sc.win 0 2) = []"
proof -
  have the4: "orph.the_unit 4 = orph_unit"
    using orph.the_unit_props[of 4] by simp
  have kept: "state_after D0_o (rs0.restart_stream (\<lambda>_. [3, 4]) (\<lambda>_. [3]) 0) 4 = D0_o 4"
    using wit_restart_before_close_keeps_orphan by (simp add: D0_o_def)
  have late: "\<not> den_w (u_hi orph_unit) \<le> den_w 1"
    by (simp add: orph_unit_def den_w_def)
  have quiet: "evs_for 4 (sc.win 0 2) = []"
    unfolding sc.win_def by (simp add: den_w_def L_s_def evs_for_def)
  show ?thesis using kept src_4_none the4 late quiet by simp
qed

lemma wit_restart_before_close_cover_fails:
  "D0_o 4 \<noteq> None
   \<and> state_after s0_w (sc.pfx 2) 4 = None
   \<and> evs_for 4 (sc.win 0 2) = []
   \<and> \<not> ((4 \<in> {3, 4::nat} \<and> den_w (u_hi (orph.the_unit 4)) \<le> den_w 1
            \<and> 4 \<in> set ((\<lambda>_. [3, 4::nat]) (orph.the_unit 4)))
          \<or> (4 \<in> {3, 4::nat} \<and> 4 \<in> set ((\<lambda>_. [3::nat]) (rx.the_unit 4))))"
proof -
  have the4: "orph.the_unit 4 = orph_unit"
    using orph.the_unit_props[of 4] by simp
  have late: "\<not> den_w (u_hi orph_unit) \<le> den_w 1"
    by (simp add: orph_unit_def den_w_def)
  have quiet: "evs_for 4 (sc.win 0 2) = []"
    unfolding sc.win_def by (simp add: den_w_def L_s_def evs_for_def)
  show ?thesis using src_4_none the4 late quiet by (simp add: D0_o_def)
qed

text \<open>
  The second fixture: a chunk owns key 1 with bracket (1, 1], read at 1
  where key 1 is absent, and lists key 1 as absent. Key 1 is then inserted
  at position 1, between the close and the crash. The sink starts with a
  stale row for key 1. The connector had committed offset 0, before the
  close, so on restart it delivers both events again and re-executes the
  chunk with bracket (2, 2], where key 1 is present. The absent entry
  delivered before the crash removes the stale row, the insert follows it,
  and after the restart the re-delivered insert and the re-executed chunk
  keep the live row.
\<close>

definition ri_unit :: "(nat, nat, nat) cunit" where
  "ri_unit = \<lparr>u_dom = {1}, u_lo = 1, u_hi = 1, u_refresh = (\<lambda>_. None)\<rparr>"

definition rj_unit :: "(nat, nat, nat) cunit" where
  "rj_unit = \<lparr>u_dom = {1}, u_lo = 2, u_hi = 2,
              u_refresh = (\<lambda>k. if k = 1 then Some 1 else None)\<rparr>"

definition D0_r :: "(nat, nat) state" where
  "D0_r = (\<lambda>k. if k = 1 then Some 9 else None)"

lemma ri_contract: "capture_contract L_s den_w s0_w [ri_unit] {1} 2"
proof -
  have empty: "\<And>k. k \<in> {1} \<Longrightarrow> state_after s0_w (sc.pfx 1) k = None"
    unfolding sc.pfx_def
    by (auto simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  show ?thesis
    unfolding ri_unit_def
    by (rule sc.absence_assertion_contract[where c = 1, OF _ _ _ empty])
       (simp_all add: sc.cle_def den_w_def)
qed

interpretation ri: capture_contract L_s den_w s0_w "[ri_unit]" "{1}" 2
  by (rule ri_contract)

interpretation rj: capture_contract L_s den_w s0_w "[rj_unit]" "{1}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [rj_unit]. u_dom u) = {1}"
    by (simp add: rj_unit_def)
next
  fix i j
  assume "i < length [rj_unit]" "j < length [rj_unit]" "i \<noteq> j"
  then show "u_dom ([rj_unit] ! i) \<inter> u_dom ([rj_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [rj_unit]"
  then show "sc.cle (u_lo u) (u_hi u)"
    by (simp add: rj_unit_def sc.cle_def den_w_def)
next
  fix u assume "u \<in> set [rj_unit]"
  then show "sc.cle (u_hi u) 2"
    by (simp add: rj_unit_def sc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [rj_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. sc.cle (u_lo u) c \<and> sc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (sc.pfx c) k"
    unfolding sc.cle_def sc.pfx_def
    by (intro exI[of _ 2])
       (auto simp add: rj_unit_def den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
qed

interpretation rt: pass_restart L_s den_w s0_w "[ri_unit]" "{1}" 2
                     "[rj_unit]" "{1}" 2 0 2
  by unfold_locales (simp_all add: den_w_def ri_unit_def rj_unit_def)

lemma ri_svl_ok2: "ri.svl_ok2 (\<lambda>_. [1])"
proof -
  have win: "sc.win (u_lo ri_unit) (u_hi ri_unit) = []"
    unfolding sc.win_def by (simp add: ri_unit_def den_w_def)
  have "ri.survivors ri_unit = {}"
    by (auto simp: ri.survivors_def ri_unit_def)
  moreover have "ri.absent_untouched ri_unit = {1}"
    using win by (auto simp: ri.absent_untouched_def ri_unit_def)
  ultimately show ?thesis by (simp add: ri.svl_ok2_def)
qed

lemma rj_svl_ok2: "rj.svl_ok2 (\<lambda>_. [1])"
proof -
  have win: "sc.win (u_lo rj_unit) (u_hi rj_unit) = []"
    unfolding sc.win_def by (simp add: rj_unit_def den_w_def)
  have "rj.survivors rj_unit = {1}"
    using win by (auto simp: rj.survivors_def rj_unit_def)
  then show ?thesis by (simp add: rj.svl_ok2_def)
qed

text \<open>
  The stream, computed. For key 1: the absent entry at the close, the
  insert, the insert again, and the re-executed chunk's entry with the live
  value.
\<close>

lemma wit_restart_stream_insert:
  "rt.restart_stream (\<lambda>_. [1]) (\<lambda>_. [1]) 0
     = [Event 3 (Some 7), Event 1 None, Event 1 (Some 1),
        Event 3 (Some 7), Event 1 (Some 1), Event 1 (Some 1)]"
  unfolding rt.restart_stream_def ri.emission_t_def rj.emission_def rj.emission_t_def
            ri.closes_at_def rj.closes_at_def ri.close_block_def rj.close_block_def
  by (simp add: ri_unit_def rj_unit_def den_w_def L_s_def upt_rec)

lemma wit_restart_live_row_kept:
  "state_after D0_r (rt.restart_stream (\<lambda>_. [1]) (\<lambda>_. [1]) 0) 1 = Some 1"
proof -
  have s0lo: "\<And>u. u \<in> set [ri_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: ri_unit_def den_w_def)
  have conv: "\<forall>k \<in> {1} \<union> {1}.
      state_after D0_r (rt.restart_stream (\<lambda>_. [1]) (\<lambda>_. [1]) 0) k
        = state_after s0_w (sc.pfx 2) k"
  proof (rule rt.restart_converges[OF ri_svl_ok2 rj_svl_ok2 s0lo order_refl])
    fix k :: nat
    assume "k \<in> {1} \<union> {1}"
    then have k1: "k = 1" by simp
    show "(k \<in> {1} \<and> den_w (u_hi (ri.the_unit k)) \<le> den_w 2
             \<and> k \<in> set ((\<lambda>_. [1]) (ri.the_unit k))) \<or>
          (k \<in> {1} \<and> k \<in> set ((\<lambda>_. [1]) (rj.the_unit k)))"
      using k1 by simp
  qed
  have "state_after s0_w (sc.pfx 2) 1 = Some 1"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  then show ?thesis using conv by simp
qed

subsection \<open>Fixture: the sink can hold an older value while the segment is re-delivered\<close>

text \<open>
  The log sets key 5 to 1, deletes it, and sets it to 2. The pass's one
  chunk owns key 5, reads it at position 3, after the whole log, and closes
  there. The connector committed offset 0 and crashed at position 3, after
  the close, so it delivers the whole log a second time. No chunk is
  re-executed, since none closes after the crash. The stream has seven
  items. After six of them the sink has key 5 deleted while the source
  holds 2. The last item sets it to 2 again, as @{text restart_converges}
  states for the end of the stream.
\<close>

definition L_t :: "(nat, nat) event list" where
  "L_t = [Event 5 (Some 1), Event 5 None, Event 5 (Some 2)]"

definition den_t :: "nat \<Rightarrow> nat" where
  "den_t c = min c 3"

interpretation tc: coordinate_space L_t den_t
  by unfold_locales (simp add: den_t_def L_t_def)

definition tr_unit :: "(nat, nat, nat) cunit" where
  "tr_unit = \<lparr>u_dom = {5}, u_lo = 3, u_hi = 3,
              u_refresh = (\<lambda>k. if k = 5 then Some 2 else None)\<rparr>"

interpretation tr1: capture_contract L_t den_t s0_w "[tr_unit]" "{5}" 3
proof (unfold_locales)
  show "(\<Union>u\<in>set [tr_unit]. u_dom u) = {5}"
    by (simp add: tr_unit_def)
next
  fix i j
  assume "i < length [tr_unit]" "j < length [tr_unit]" "i \<noteq> j"
  then show "u_dom ([tr_unit] ! i) \<inter> u_dom ([tr_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [tr_unit]"
  then show "tc.cle (u_lo u) (u_hi u)"
    by (simp add: tr_unit_def tc.cle_def den_t_def)
next
  fix u assume "u \<in> set [tr_unit]"
  then show "tc.cle (u_hi u) 3"
    by (simp add: tr_unit_def tc.cle_def den_t_def)
next
  fix u k assume "u \<in> set [tr_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. tc.cle (u_lo u) c \<and> tc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (tc.pfx c) k"
    unfolding tc.cle_def tc.pfx_def
    by (intro exI[of _ 3])
       (auto simp add: tr_unit_def den_t_def L_t_def s0_w_def state_after_def apply_ev_def)
qed

interpretation tr2: capture_contract L_t den_t s0_w "[]" "{}" 3
  by unfold_locales simp_all

interpretation rtr: pass_restart L_t den_t s0_w "[tr_unit]" "{5}" 3 "[]" "{}" 3 0 3
  by unfold_locales (simp_all add: den_t_def tr_unit_def)

lemma tr1_svl_ok2: "tr1.svl_ok2 (\<lambda>_. [5])"
proof -
  have win: "tc.win (u_lo tr_unit) (u_hi tr_unit) = []"
    unfolding tc.win_def by (simp add: tr_unit_def den_t_def)
  have "tr1.survivors tr_unit = {5}"
    using win by (auto simp: tr1.survivors_def tr_unit_def)
  then show ?thesis by (simp add: tr1.svl_ok2_def)
qed

lemma tr2_svl_ok2: "tr2.svl_ok2 (\<lambda>_. [])"
  by (simp add: tr2.svl_ok2_def)

lemma wit_restart_stream_transient:
  "rtr.restart_stream (\<lambda>_. [5]) (\<lambda>_. []) 0
     = [Event 5 (Some 1), Event 5 None, Event 5 (Some 2), Event 5 (Some 2),
        Event 5 (Some 1), Event 5 None, Event 5 (Some 2)]"
  unfolding rtr.restart_stream_def tr1.emission_t_def tr2.emission_def tr2.emission_t_def
            tr1.closes_at_def tr2.closes_at_def tr1.close_block_def tr2.close_block_def
  by (simp add: tr_unit_def den_t_def L_t_def upt_rec)

lemma wit_transient_source: "state_after s0_w (tc.pfx 3) 5 = Some 2"
  unfolding tc.pfx_def by (simp add: den_t_def L_t_def s0_w_def state_after_def apply_ev_def)

lemma wit_restart_transient_mid:
  "state_after s0_w (take 6 (rtr.restart_stream (\<lambda>_. [5]) (\<lambda>_. []) 0)) 5 = None"
  unfolding wit_restart_stream_transient by (simp add: state_after_def apply_ev_def)

lemma wit_restart_transient_end:
  "state_after s0_w (rtr.restart_stream (\<lambda>_. [5]) (\<lambda>_. []) 0) 5 = Some 2"
proof -
  have s0lo: "\<And>u. u \<in> set [tr_unit] \<Longrightarrow> den_t 0 \<le> den_t (u_lo u)"
    by (simp add: tr_unit_def den_t_def)
  have conv: "\<forall>k \<in> {5} \<union> {}.
      state_after s0_w (rtr.restart_stream (\<lambda>_. [5]) (\<lambda>_. []) 0) k
        = state_after s0_w (tc.pfx 3) k"
  proof (rule rtr.restart_converges[OF tr1_svl_ok2 tr2_svl_ok2 s0lo order_refl])
    fix k :: nat
    assume "k \<in> {5} \<union> {}" and held: "s0_w k \<noteq> None"
    then show "(k \<in> {5} \<and> den_t (u_hi (tr1.the_unit k)) \<le> den_t 3
             \<and> k \<in> set ((\<lambda>_. [5]) (tr1.the_unit k))) \<or>
          (k \<in> {} \<and> k \<in> set ((\<lambda>_. []) (tr2.the_unit k)))"
      by (simp add: s0_w_def)
  qed
  then show ?thesis using wit_transient_source by simp
qed

end
