(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Interleaved: a full pass and a bracketed read served while
  the pass is still running (a repair request), merged into one stream by
  log position and applied to the same sink, from an arbitrary initial sink
  state.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core), to
  Orphan_Absence and to Orphan_Absence_Composition. Nothing in the archived
  development is modified.
*)
theory Orphan_Absence_Interleaved
  imports Orphan_Absence_Composition "HOL-Library.Multiset"
begin

text \<open>
  The theory @{text Orphan_Absence_Composition} applies a full pass P and
  then a later bracketed read R, the read starting at the pass's frontier.
  Here R is served while P is still running: every unit of R lies inside the
  span of P, from P's consumption start @{text s0} to its frontier
  @{text f1}. The sink receives one stream: the pass's timed emission with
  R's close blocks inserted at their own log positions, each log event once.
  Results:

  \<^item> The stream is in position order. Per key, it is the pass's own
    per-key emission with R's entry for the key, if any, inserted at the
    position of R's close, after anything the pass emits at that position.
  \<^item> Safety: every key of either scope ends at the source state at
    @{text f1}, or it is absent there, neither read listed it, no log event
    from @{text s0} to @{text f1} mentions it, and the sink keeps its
    initial value.
  \<^item> Convergence: under coverage of exactly those keys, the sink ends at
    the source state on both scopes.
  \<^item> A request that lists every key it reads as absent and untouched
    completes the pass when every key the pass leaves wrong is in its scope.
    For a key-list request it suffices that every key the pass leaves wrong
    was requested, each key read at its own coordinate inside the pass.

  The proof rests on one observation. Every entry of the stream for a key
  carries the source value of that key at the entry's own position. A log
  event does so by definition. A close entry does so because its key is
  untouched inside its unit's window, so the read value (O2) is still the
  source value at the close (window invariance). A stream in position order
  that also carries every log event of the key therefore ends at the source
  value at the frontier, whichever of the two closes comes first when they
  sit at distinct positions. For this reason no assumption on how R's
  windows sit relative to P's chunk windows is needed.

  At an equal position the stream @{text inter_t} puts P's close block
  before R's, and the per-key characterization is stated for that order.
  The safety and convergence theorems are also proved for the reverse tie
  order, the stream @{text inter_t_rev} with R's block first
  (@{text pass_with_request_safe_rev}, @{text pass_with_request_converges_rev}),
  and for any stream in position order that carries the same items, however
  it breaks ties at each position
  (@{text pass_with_request_safe_any}, @{text pass_with_request_converges_any}).
  So no tie rule is an assumption of those results.
\<close>

subsection \<open>Position-tagged lists\<close>

text \<open>
  A timed list pairs every item with a position tag. The streams below are
  built block by block: the block of log position @{text p} holds close
  entries tagged @{text p}, then the log event at @{text p}, tagged
  @{text "Suc p"}. Such a list is in tag order.
\<close>

lemma sorted_const_list:
  assumes "\<And>t. t \<in> set xs \<Longrightarrow> t = c"
  shows "sorted xs"
  using assms by (induction xs) auto

lemma sorted_map_fst_filter:
  "sorted (map fst S) \<Longrightarrow> sorted (map fst (filter Q S))"
  by (induction S) auto

lemma sorted_le_last:
  assumes "sorted xs" and "x \<in> set xs"
  shows "x \<le> last xs"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases "ys = []")
    case True
    then show ?thesis using Cons.prems by simp
  next
    case ne: False
    have y_le: "\<forall>z \<in> set ys. y \<le> z" and s_ys: "sorted ys"
      using Cons.prems(1) by simp_all
    have last_in: "last ys \<in> set ys" using ne by simp
    have "x \<le> last ys"
    proof (cases "x = y")
      case True
      then show ?thesis using bspec[OF y_le last_in] by simp
    next
      case False
      then have "x \<in> set ys" using Cons.prems(2) by simp
      then show ?thesis by (rule Cons.IH[OF s_ys])
    qed
    then show ?thesis using ne by simp
  qed
qed

text \<open>
  A list built from such blocks is in tag order. The second conjunct, the
  bound on the tags, carries the induction.
\<close>

lemma blocks_sorted:
  fixes C :: "nat \<Rightarrow> (nat \<times> 'a) list" and z :: "nat \<Rightarrow> 'a"
  assumes C: "\<And>p x. x \<in> set (C p) \<Longrightarrow> fst x = p"
  shows "sorted (map fst (concat (map (\<lambda>p. C p @ [(Suc p, z p)]) [a..<b]) @ C b))
         \<and> (\<forall>x \<in> set (concat (map (\<lambda>p. C p @ [(Suc p, z p)]) [a..<b]) @ C b). fst x \<le> b)"
proof (induction b)
  case 0
  have "sorted (map fst (C 0))"
    by (rule sorted_const_list[where c = 0]) (use C in auto)
  then show ?case using C by auto
next
  case (Suc b)
  define X where "X = concat (map (\<lambda>p. C p @ [(Suc p, z p)]) [a..<b]) @ C b"
  have sX: "sorted (map fst X)" and bX: "\<forall>x \<in> set X. fst x \<le> b"
    using Suc.IH by (simp_all add: X_def)
  have tail_eq: "\<And>t. t \<in> set (map fst ((Suc b, z b) # C (Suc b))) \<Longrightarrow> t = Suc b"
    using C by auto
  have s_tail: "sorted (map fst ((Suc b, z b) # C (Suc b)))"
    by (rule sorted_const_list[OF tail_eq])
  have s_last: "sorted (map fst (C (Suc b)))"
    by (rule sorted_const_list[where c = "Suc b"]) (use C in auto)
  show ?case
  proof (cases "a \<le> b")
    case True
    have eq: "concat (map (\<lambda>p. C p @ [(Suc p, z p)]) [a..<Suc b]) @ C (Suc b)
                = X @ (Suc b, z b) # C (Suc b)"
      using True by (simp add: X_def)
    have "sorted (map fst X @ map fst ((Suc b, z b) # C (Suc b)))"
      unfolding sorted_append using sX s_tail bX tail_eq by fastforce
    then have "sorted (map fst (X @ (Suc b, z b) # C (Suc b)))" by simp
    moreover have "\<forall>x \<in> set (X @ (Suc b, z b) # C (Suc b)). fst x \<le> Suc b"
      using bX C by fastforce
    ultimately show ?thesis using eq by simp
  next
    case False
    then have "[a..<Suc b] = []" by simp
    then show ?thesis using s_last C by auto
  qed
qed

text \<open>
  @{text "insert_at h ys S"} places @{text ys} after every item of @{text S}
  tagged at most @{text h} and before every item tagged later. On a list in
  tag order this is insertion at position @{text h}, right after the items
  already tagged @{text h} (@{text insert_at_sorted}). With nothing to
  insert it gives the list back (@{text insert_at_Nil}).
\<close>

definition insert_at :: "nat \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list" where
  "insert_at h ys S = filter (\<lambda>x. fst x \<le> h) S @ ys @ filter (\<lambda>x. h < fst x) S"

lemma insert_at_split:
  assumes U: "\<forall>x \<in> set U. fst x \<le> h" and V: "\<forall>x \<in> set V. h < fst x"
  shows "insert_at h ys (U @ V) = U @ ys @ V"
proof -
  have U1: "filter (\<lambda>x. fst x \<le> h) U = U" using U by (rule filter_True)
  have U2: "filter (\<lambda>x. h < fst x) U = []" using U by (auto simp: filter_empty_conv)
  have V1: "filter (\<lambda>x. fst x \<le> h) V = []" using V by (auto simp: filter_empty_conv)
  have V2: "filter (\<lambda>x. h < fst x) V = V" using V by (rule filter_True)
  show ?thesis by (simp add: insert_at_def U1 U2 V1 V2)
qed

lemma insert_at_sorted:
  assumes "sorted (map fst S)"
  shows "insert_at h ys S = takeWhile (\<lambda>x. fst x \<le> h) S @ ys @ dropWhile (\<lambda>x. fst x \<le> h) S"
  using assms
proof (induction S)
  case Nil
  then show ?case by (simp add: insert_at_def)
next
  case (Cons x S)
  have sS: "sorted (map fst S)" and x_le: "\<forall>y \<in> set S. fst x \<le> fst y"
    using Cons.prems by auto
  show ?case
  proof (cases "fst x \<le> h")
    case True
    then have "\<not> h < fst x" by simp
    then show ?thesis
      using True Cons.IH[OF sS] by (simp add: insert_at_def)
  next
    case False
    then have all_later: "\<forall>y \<in> set (x # S). h < fst y" using x_le by auto
    have "insert_at h ys (x # S) = ys @ x # S"
      using insert_at_split[of "[]" h "x # S" ys] all_later by simp
    then show ?thesis using False by simp
  qed
qed

lemma insert_at_Nil:
  assumes "sorted (map fst S)"
  shows "insert_at h [] S = S"
  using insert_at_sorted[OF assms, of h "[]"] by simp

text \<open>
  The merge lemma. A list built from blocks @{text "A p @ B p @ E p"},
  where @{text "A p"} is tagged @{text p}, @{text "E p"} is tagged
  @{text "Suc p"}, and @{text B} is empty except for @{text "B h = ys"}, is
  the same list without @{text B} with @{text ys} inserted at @{text h}.
\<close>

lemma concat_blocks_insert:
  fixes A B E :: "nat \<Rightarrow> (nat \<times> 'a) list"
  assumes A_tag: "\<And>p x. x \<in> set (A p) \<Longrightarrow> fst x = p"
      and E_tag: "\<And>p x. x \<in> set (E p) \<Longrightarrow> fst x = Suc p"
      and B_at: "\<And>p. B p = (if p = h then ys else [])"
      and ah: "a \<le> h" and hb: "h \<le> b"
  shows "concat (map (\<lambda>p. A p @ B p @ E p) [a..<b]) @ A b @ B b
         = insert_at h ys (concat (map (\<lambda>p. A p @ E p) [a..<b]) @ A b)"
proof -
  define G where "G = (\<lambda>p. A p @ E p)"
  have G_tag: "fst x = p \<or> fst x = Suc p" if x: "x \<in> set (G p)" for x p
  proof -
    have "x \<in> set (A p) \<or> x \<in> set (E p)" using x by (simp add: G_def)
    then show ?thesis
    proof
      assume "x \<in> set (A p)"
      then have "fst x = p" by (rule A_tag)
      then show ?thesis ..
    next
      assume "x \<in> set (E p)"
      then have "fst x = Suc p" by (rule E_tag)
      then show ?thesis ..
    qed
  qed
  have away: "concat (map (\<lambda>p. A p @ B p @ E p) qs) = concat (map G qs)"
    if "h \<notin> set qs" for qs
    using that by (induction qs) (auto simp: G_def B_at)
  have before: "fst x \<le> h" if x: "x \<in> set (concat (map G [a..<h]))" for x
  proof -
    obtain p where p: "p \<in> set [a..<h]" and xp: "x \<in> set (G p)"
      using x by auto
    have "p < h" using p by simp
    then show ?thesis using G_tag[OF xp] by auto
  qed
  consider (inside) "h < b" | (at_end) "h = b" using hb by linarith
  then show ?thesis
  proof cases
    case inside
    have split: "[a..<b] = [a..<h] @ [h..<b]" by (rule upt_split[OF ah hb])
    have head: "[h..<b] = h # [Suc h..<b]" using inside by (simp add: upt_rec)
    have after: "h < fst x" if x: "x \<in> set (concat (map G [Suc h..<b]))" for x
    proof -
      obtain p where p: "p \<in> set [Suc h..<b]" and xp: "x \<in> set (G p)"
        using x by auto
      have "h < p" using p by simp
      then show ?thesis using G_tag[OF xp] by auto
    qed
    have away1: "concat (map (\<lambda>p. A p @ B p @ E p) [a..<h]) = concat (map G [a..<h])"
      by (rule away) simp
    have away2: "concat (map (\<lambda>p. A p @ B p @ E p) [Suc h..<b]) = concat (map G [Suc h..<b])"
      by (rule away) simp
    have Bh: "B h = ys" and Bb: "B b = []" using B_at inside by simp_all
    have U: "\<forall>x \<in> set (concat (map G [a..<h]) @ A h). fst x \<le> h"
      using before A_tag by fastforce
    have V: "\<forall>x \<in> set (E h @ concat (map G [Suc h..<b]) @ A b). h < fst x"
      using E_tag after A_tag inside by fastforce
    have "concat (map (\<lambda>p. A p @ B p @ E p) [a..<b]) @ A b @ B b
          = concat (map (\<lambda>p. A p @ B p @ E p) [a..<h]) @ (A h @ B h @ E h)
            @ concat (map (\<lambda>p. A p @ B p @ E p) [Suc h..<b]) @ A b @ B b"
      by (simp add: split head)
    also have "\<dots> = (concat (map G [a..<h]) @ A h) @ ys
                    @ (E h @ concat (map G [Suc h..<b]) @ A b)"
      unfolding away1 away2 Bh Bb by simp
    also have "\<dots> = insert_at h ys ((concat (map G [a..<h]) @ A h)
                                    @ (E h @ concat (map G [Suc h..<b]) @ A b))"
      by (rule insert_at_split[OF U V, symmetric])
    also have "\<dots> = insert_at h ys (concat (map G [a..<b]) @ A b)"
      by (simp add: split head G_def)
    finally show ?thesis by (simp add: G_def)
  next
    case at_end
    have away0: "concat (map (\<lambda>p. A p @ B p @ E p) [a..<b]) = concat (map G [a..<b])"
      by (rule away) (simp add: at_end)
    have Bb: "B b = ys" using B_at at_end by simp
    have U: "\<forall>x \<in> set (concat (map G [a..<b]) @ A b). fst x \<le> h"
      using before A_tag at_end by fastforce
    have V: "\<forall>x \<in> set ([] :: (nat \<times> 'a) list). h < fst x" by simp
    have "concat (map (\<lambda>p. A p @ B p @ E p) [a..<b]) @ A b @ B b
          = (concat (map G [a..<b]) @ A b) @ ys @ []"
      unfolding away0 Bb by simp
    also have "\<dots> = insert_at h ys ((concat (map G [a..<b]) @ A b) @ [])"
      by (rule insert_at_split[OF U V, symmetric])
    finally show ?thesis by (simp add: G_def)
  qed
qed

subsection \<open>Source values at log positions\<close>

text \<open>
  The source value of key @{text k} at log position @{text n} is
  @{text "state_after \<sigma>0 (take n L) k"}. A log event for @{text k} at
  position @{text p} carries the source value at @{text "Suc p"}, and the
  value does not change across positions that carry no event for @{text k}.
\<close>

lemma take_state_quiet:
  assumes nm: "n \<le> m"
      and quiet: "\<And>p. n \<le> p \<Longrightarrow> p < m \<Longrightarrow> ev_key (L ! p) \<noteq> k"
  shows "state_after \<sigma>0 (take m L) k = state_after \<sigma>0 (take n L) k"
proof -
  have split: "take m L = take n L @ drop n (take m L)"
    using nm by (metis append_take_drop_id min.absorb1 take_take)
  have keys: "ev_key x \<noteq> k" if x: "x \<in> set (drop n (take m L))" for x
  proof -
    obtain j where j: "j < length (drop n (take m L))" and xj: "x = drop n (take m L) ! j"
      using x by (metis in_set_conv_nth)
    have nj: "n + j < m" using j by auto
    have n_len: "n \<le> length (take m L)"
    proof -
      have "j < min (length L) m - n" using j by simp
      then have "n < min (length L) m" by linarith
      then show ?thesis by simp
    qed
    have "x = take m L ! (n + j)" using xj nth_drop[OF n_len, of j] by simp
    also have "\<dots> = L ! (n + j)" using nj by simp
    finally show ?thesis using quiet[of "n + j"] nj by simp
  qed
  have none: "evs_for k (drop n (take m L)) = []"
    using keys by (auto simp: evs_for_def filter_empty_conv)
  have "state_after \<sigma>0 (take n L @ drop n (take m L)) k = state_after \<sigma>0 (take n L) k"
    by (rule state_after_append_no_k[OF none])
  then show ?thesis by (simp only: split[symmetric])
qed

lemma event_honest:
  assumes p: "p < length L" and key: "ev_key (L ! p) = k"
  shows "ev_img (L ! p) = state_after \<sigma>0 (take (Suc p) L) k"
proof -
  have "take (Suc p) L = take p L @ [L ! p]"
    using p by (rule take_Suc_conv_app_nth)
  then have "state_after \<sigma>0 (take (Suc p) L) k
               = apply_ev (state_after \<sigma>0 (take p L)) (L ! p) k"
    by (simp add: state_after_snoc)
  also have "\<dots> = ev_img (L ! p)"
    using key by (simp add: apply_ev_def)
  finally show ?thesis by simp
qed

text \<open>
  The key step. Take a timed list @{text T} for one key @{text k}, in tag
  order, whose items are all tagged between positions @{text a} and
  @{text b}, each carrying the source value of @{text k} at its own tag,
  and which carries every log event of @{text k} from @{text a} to
  @{text b}. If @{text T} is not empty, it replays, from any initial
  state, to the source value at @{text b}: its last item has the largest
  tag, and no log event of @{text k} lies between that tag and @{text b}.
\<close>

lemma honest_stream_last:
  fixes T :: "(nat \<times> ('k, 'v) event) list"
  assumes ne: "T \<noteq> []"
      and keyed: "\<And>x. x \<in> set T \<Longrightarrow> ev_key (snd x) = k"
      and honest: "\<And>x. x \<in> set T \<Longrightarrow> ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k"
      and sorted: "sorted (map fst T)"
      and low: "\<And>x. x \<in> set T \<Longrightarrow> a \<le> fst x"
      and high: "\<And>x. x \<in> set T \<Longrightarrow> fst x \<le> b"
      and complete: "\<And>p. a \<le> p \<Longrightarrow> p < b \<Longrightarrow> ev_key (L ! p) = k \<Longrightarrow> (Suc p, L ! p) \<in> set T"
  shows "state_after D (map snd T) k = state_after \<sigma>0 (take b L) k"
proof -
  define t where "t = fst (last T)"
  have last_in: "last T \<in> set T" using ne by simp
  have evs: "evs_for k (map snd T) = map snd T"
    using keyed by (auto simp: evs_for_def filter_id_conv)
  have evs_ne: "evs_for k (map snd T) \<noteq> []" using evs ne by simp
  have max: "fst x \<le> t" if "x \<in> set T" for x
  proof -
    have "fst x \<in> set (map fst T)" using that by simp
    then have "fst x \<le> last (map fst T)" by (rule sorted_le_last[OF sorted])
    then show ?thesis using ne by (simp add: t_def last_map)
  qed
  have tb: "t \<le> b" using high[OF last_in] by (simp add: t_def)
  have quiet: "ev_key (L ! p) \<noteq> k" if tp: "t \<le> p" and pb: "p < b" for p
  proof
    assume key: "ev_key (L ! p) = k"
    have "a \<le> p" using low[OF last_in] tp by (simp add: t_def)
    then have "(Suc p, L ! p) \<in> set T" using complete pb key by blast
    then have "Suc p \<le> t" using max by fastforce
    with tp show False by simp
  qed
  have "state_after D (map snd T) k = ev_img (last (evs_for k (map snd T)))"
    by (rule state_after_last_event[OF evs_ne])
  also have "\<dots> = ev_img (snd (last T))"
    using ne by (simp add: evs last_map)
  also have "\<dots> = state_after \<sigma>0 (take t L) k"
    using honest[OF last_in] by (simp add: t_def)
  also have "\<dots> = state_after \<sigma>0 (take b L) k"
    by (rule take_state_quiet[OF tb quiet, symmetric])
  finally show ?thesis .
qed

subsection \<open>Close entries: their tags, and the value they carry\<close>

context capture_plan
begin

lemma closes_at_item:
  assumes "x \<in> set (closes_at svl p)"
  shows "\<exists>u \<in> set units. \<exists>k \<in> set (svl u).
           x = (den (u_hi u), Event k (u_refresh u k)) \<and> den (u_hi u) = p"
proof -
  obtain i where i: "i < length units" and hi: "den (u_hi (units ! i)) = p"
    and x: "x \<in> set (close_block svl (units ! i))"
    using assms by (auto simp: closes_at_def split: if_splits)
  obtain k where k: "k \<in> set (svl (units ! i))"
    and xk: "x = (den (u_hi (units ! i)), Event k (u_refresh (units ! i) k))"
    using x by (auto simp: close_block_def)
  show ?thesis using nth_mem[OF i] k xk hi by blast
qed

lemma closes_at_tag:
  assumes "x \<in> set (closes_at svl p)"
  shows "fst x = p"
  using closes_at_item[OF assms] by auto

text \<open>
  The pass's own timed emission is in tag order, hence so is its emission
  for any single key.
\<close>

lemma emission_t_sorted: "sorted (map fst (emission_t svl s0))"
proof -
  have "sorted (map fst (concat (map (\<lambda>p. closes_at svl p @ [(Suc p, L ! p)]) [den s0..<den f])
                         @ closes_at svl (den f)))"
    using blocks_sorted[where C = "closes_at svl" and z = "(!) L" and a = "den s0" and b = "den f",
                        OF closes_at_tag] by simp
  then show ?thesis by (simp add: emission_t_def)
qed

lemma titems_emission_sorted: "sorted (map fst (titems_for k (emission_t svl s0)))"
  unfolding titems_for_def by (rule sorted_map_fst_filter[OF emission_t_sorted])

end  (* context capture_plan *)

context capture_contract
begin

text \<open>
  An enumerated close entry carries the source value at its unit's close:
  the key is untouched inside the unit's window, so the value read at the
  O2 coordinate is still the source value at the high edge.
\<close>

lemma listed_entry_honest:
  assumes svl: "svl_ok2 svl" and u_in: "u \<in> set units" and listed: "k \<in> set (svl u)"
  shows "u_refresh u k = state_after \<sigma>0 (pfx (u_hi u)) k"
proof -
  have k_dom: "k \<in> u_dom u" using svl2_sub_dom[OF svl u_in] listed by auto
  have quiet: "evs_for k (win (u_lo u) (u_hi u)) = []"
    by (rule svl2_untouched[OF svl u_in listed])
  obtain c where c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u"
    and honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
    using O2_honest[OF u_in k_dom] by blast
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" by (rule bracket_lo_hi[OF u_in])
  have "state_after \<sigma>0 (pfx c) k = state_after \<sigma>0 (pfx (u_lo u)) k"
    by (rule win_invariant_state[OF c_lo c_hi quiet])
  also have "\<dots> = state_after \<sigma>0 (pfx (u_hi u)) k"
    by (rule win_invariant_state[OF lo_hi cle_refl quiet, symmetric])
  finally show ?thesis using honest by simp
qed

text \<open>
  A key of the scope that the enumeration does not list, and that no
  consumed log event mentions, is absent at the frontier: had it been read
  as present, it would be a survivor and therefore listed.
\<close>

lemma unlisted_quiet_absent:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and unlisted: "k \<notin> set (svl (the_unit k))"
      and quiet: "evs_for k (win s0 f) = []"
  shows "state_after \<sigma>0 (pfx f) k = None"
proof -
  define u where "u = the_unit k"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have s0_lo: "s0 \<sqsubseteq> u_lo u" by (rule s0lo[OF u_in])
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" by (rule bracket_lo_hi[OF u_in])
  have hi_f: "u_hi u \<sqsubseteq> f" by (rule bracket_hi_f[OF u_in])
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have quiet_lo_f: "evs_for k (win (u_lo u) f) = []"
    using evs_for_win_split[OF s0_lo lo_f] quiet by simp
  have quiet_win: "evs_for k (win (u_lo u) (u_hi u)) = []"
    using evs_for_win_split[OF lo_hi hi_f] quiet_lo_f by simp
  have refresh_none: "u_refresh u k = None"
  proof (rule ccontr)
    assume "u_refresh u k \<noteq> None"
    then have "k \<in> survivors u" using k_dom quiet_win by (simp add: survivors_def)
    then have "k \<in> set (svl u)" by (rule svl2_surv[OF svl u_in])
    with unlisted show False by (simp add: u_def)
  qed
  have "sink_at f k = u_refresh u k"
    using quiet_lo_f by (simp add: sink_at_def flip: u_def)
  then show ?thesis using contract_cut[OF k] refresh_none by simp
qed

text \<open>
  The frontier enters a contract only as the bound on the high edges, so a
  contract whose units all close at or before a coordinate @{text g} is
  also a contract with frontier @{text g}. A request contract given with
  some later frontier is therefore an instance of the locale below as soon
  as its units close inside the pass.
\<close>

lemma contract_with_frontier:
  assumes hi_g: "\<And>u. u \<in> set units \<Longrightarrow> u_hi u \<sqsubseteq> g"
  shows "capture_contract L den \<sigma>0 units scope g"
proof (unfold_locales)
  show "(\<Union>u\<in>set units. u_dom u) = scope" by (rule O1_cover)
next
  fix i j
  assume "i < length units" "j < length units" "i \<noteq> j"
  then show "u_dom (units ! i) \<inter> u_dom (units ! j) = {}" by (rule O1_disjoint)
next
  fix u assume "u \<in> set units"
  then show "u_lo u \<sqsubseteq> u_hi u" by (rule bracket_lo_hi)
next
  fix u assume "u \<in> set units"
  then show "u_hi u \<sqsubseteq> g" by (rule hi_g)
next
  fix u k assume "u \<in> set units" and "k \<in> u_dom u"
  then show "\<exists>c. u_lo u \<sqsubseteq> c \<and> c \<sqsubseteq> u_hi u \<and> u_refresh u k = state_after \<sigma>0 (pfx c) k"
    by (rule O2_honest)
qed

end  (* context capture_contract *)

subsection \<open>A pass and a request served inside it, over one log\<close>

text \<open>
  The request R is any capture contract over the same log whose units close
  at or before the pass's frontier @{text f1}. Its frontier is taken to be
  @{text f1}, which loses no generality by @{text contract_with_frontier}.
  That every unit of R starts at or after the pass's consumption start
  @{text s0} is a premise of the theorems below, next to the pass's own
  consumption-start premise, because @{text s0} is a parameter of the
  stream, as in @{text Orphan_Absence_Composition}. No assumption relates
  R's windows to P's chunk windows: they may overlap, and R's close may come
  before or after the close of the chunk that covers the same key. At an
  equal position the stream puts P's block first, as the definition below
  does. The reverse tie order, and any other order at equal positions, is
  treated at the end of the locale.
\<close>

locale pass_with_request =
  P: capture_contract L den \<sigma>0 U1 sc1 f1 +
  R: capture_contract L den \<sigma>0 U2 sc2 f1
  for L :: "('k, 'v) event list" and den :: "'c \<Rightarrow> nat"
  and \<sigma>0 :: "('k, 'v) state"
  and U1 :: "('k, 'v, 'c) cunit list" and sc1 :: "'k set" and f1 :: 'c
  and U2 :: "('k, 'v, 'c) cunit list" and sc2 :: "'k set"
begin

text \<open>
  The interleaved stream, block by block over the pass's consumed log
  positions: P's close blocks at the position, then R's close blocks at the
  position, then the log event at the position. Units whose high edge sits
  at the frontier close after the last consumed event, P's before R's. This
  is the pass's timed emission @{text "P.emission_t svl1 s0"} with R's close
  blocks merged in by position, R after P at equal positions.
\<close>

definition inter_t ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "inter_t svl1 svl2 s0 =
     concat (map (\<lambda>p. P.closes_at svl1 p @ R.closes_at svl2 p @ [(Suc p, L ! p)])
                 [den s0..<den f1])
     @ P.closes_at svl1 (den f1) @ R.closes_at svl2 (den f1)"

definition inter ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> ('k, 'v) event list" where
  "inter svl1 svl2 s0 = map snd (inter_t svl1 svl2 s0)"

subsubsection \<open>The stream is the pass's emission with R's close blocks merged in\<close>

text \<open>
  Three sanity facts pin the definition down. With an empty enumeration for
  R the stream is the pass's emission. As a multiset, the stream is the
  pass's emission plus R's close blocks at the positions @{text s0} to
  @{text f1}: nothing of the pass's emission is dropped or repeated, and
  nothing else is added. And the stream is in position order.
\<close>

lemma inter_t_no_request: "inter_t svl1 (\<lambda>_. []) s0 = P.emission_t svl1 s0"
proof -
  have nil: "R.closes_at (\<lambda>_. []) p = []" for p
    by (auto simp: R.closes_at_def R.close_block_def)
  show ?thesis by (simp add: inter_t_def P.emission_t_def nil)
qed

lemma inter_t_mset:
  "mset (inter_t svl1 svl2 s0) =
     mset (P.emission_t svl1 s0)
     + mset (concat (map (R.closes_at svl2) [den s0..<den f1]) @ R.closes_at svl2 (den f1))"
proof -
  have blocks: "mset (concat (map (\<lambda>p. A p @ B p @ E p) ps))
                  = mset (concat (map (\<lambda>p. A p @ E p) ps)) + mset (concat (map B ps))"
    for A B E :: "nat \<Rightarrow> (nat \<times> ('k, 'v) event) list" and ps
    by (induction ps) (simp_all add: ac_simps)
  show ?thesis
    unfolding inter_t_def P.emission_t_def
    using blocks[where A = "P.closes_at svl1" and B = "R.closes_at svl2"
                   and E = "\<lambda>p. [(Suc p, L ! p)]" and ps = "[den s0..<den f1]"]
    by (simp add: ac_simps)
qed

lemma inter_t_sorted: "sorted (map fst (inter_t svl1 svl2 s0))"
proof -
  have C: "fst x = p" if "x \<in> set (P.closes_at svl1 p @ R.closes_at svl2 p)" for x p
    using that by (auto dest: P.closes_at_tag R.closes_at_tag)
  have "sorted (map fst (concat (map (\<lambda>p. (P.closes_at svl1 p @ R.closes_at svl2 p)
                                            @ [(Suc p, L ! p)]) [den s0..<den f1])
                         @ (P.closes_at svl1 (den f1) @ R.closes_at svl2 (den f1))))"
    using blocks_sorted[where C = "\<lambda>p. P.closes_at svl1 p @ R.closes_at svl2 p" and z = "(!) L"
                          and a = "den s0" and b = "den f1", OF C] by simp
  then show ?thesis by (simp add: inter_t_def)
qed

subsubsection \<open>What an item of the stream is\<close>

lemma inter_t_item_cases:
  assumes "x \<in> set (inter_t svl1 svl2 s0)"
  obtains (event) p where "den s0 \<le> p" "p < den f1" "x = (Suc p, L ! p)"
    | (P_close) p where "den s0 \<le> p \<and> p < den f1 \<or> p = den f1" "x \<in> set (P.closes_at svl1 p)"
    | (R_close) p where "den s0 \<le> p \<and> p < den f1 \<or> p = den f1" "x \<in> set (R.closes_at svl2 p)"
proof -
  have "(\<exists>p. den s0 \<le> p \<and> p < den f1 \<and>
             (x \<in> set (P.closes_at svl1 p) \<or> x \<in> set (R.closes_at svl2 p)
              \<or> x = (Suc p, L ! p)))
        \<or> x \<in> set (P.closes_at svl1 (den f1)) \<or> x \<in> set (R.closes_at svl2 (den f1))"
    using assms unfolding inter_t_def by auto
  then show thesis using that by blast
qed

text \<open>
  Every item of the stream carries the source value of its own key at its
  own tag: a log event by @{text event_honest}, a close entry of either read
  by @{text listed_entry_honest}.
\<close>

lemma inter_item_honest:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and x: "x \<in> set (inter_t svl1 svl2 s0)"
  shows "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) (ev_key (snd x))"
  using x
proof (cases rule: inter_t_item_cases)
  case (event p)
  have p_len: "p < length L" using event(2) P.den_le_len[of f1] by simp
  have "ev_img (L ! p) = state_after \<sigma>0 (take (Suc p) L) (ev_key (L ! p))"
    by (rule event_honest[OF p_len refl])
  then show ?thesis using event(3) by simp
next
  case (P_close p)
  obtain u k' where u: "u \<in> set U1" and k': "k' \<in> set (svl1 u)"
    and xe: "x = (den (u_hi u), Event k' (u_refresh u k'))"
    using P.closes_at_item[OF P_close(2)] by blast
  have "u_refresh u k' = state_after \<sigma>0 (P.pfx (u_hi u)) k'"
    by (rule P.listed_entry_honest[OF svl1 u k'])
  then show ?thesis using xe by (simp add: P.pfx_def)
next
  case (R_close p)
  obtain u k' where u: "u \<in> set U2" and k': "k' \<in> set (svl2 u)"
    and xe: "x = (den (u_hi u), Event k' (u_refresh u k'))"
    using R.closes_at_item[OF R_close(2)] by blast
  have "u_refresh u k' = state_after \<sigma>0 (P.pfx (u_hi u)) k'"
    by (rule R.listed_entry_honest[OF svl2 u k'])
  then show ?thesis using xe by (simp add: P.pfx_def)
qed

lemma inter_t_tag_bounds:
  assumes s0f1: "den s0 \<le> den f1" and x: "x \<in> set (inter_t svl1 svl2 s0)"
  shows "den s0 \<le> fst x \<and> fst x \<le> den f1"
  using x
proof (cases rule: inter_t_item_cases)
  case (event p)
  then show ?thesis by simp
next
  case (P_close p)
  have "fst x = p" by (rule P.closes_at_tag[OF P_close(2)])
  then show ?thesis using P_close(1) s0f1 by auto
next
  case (R_close p)
  have "fst x = p" by (rule R.closes_at_tag[OF R_close(2)])
  then show ?thesis using R_close(1) s0f1 by auto
qed

lemma inter_key_complete:
  assumes p: "den s0 \<le> p" "p < den f1" and key: "ev_key (L ! p) = k"
  shows "(Suc p, L ! p) \<in> set (P.titems_for k (inter_t svl1 svl2 s0))"
proof -
  have "(Suc p, L ! p) \<in> set (P.closes_at svl1 p @ R.closes_at svl2 p @ [(Suc p, L ! p)])"
    by simp
  moreover have "p \<in> set [den s0..<den f1]" using p by simp
  ultimately have "(Suc p, L ! p) \<in> set (inter_t svl1 svl2 s0)"
    unfolding inter_t_def by auto
  then show ?thesis using key by (simp add: P.titems_for_def)
qed

subsubsection \<open>The per-key characterization\<close>

text \<open>
  Per key, the interleaved stream is the pass's own per-key emission with
  R's close entry for the key, if R lists it, inserted at the position of
  R's close, after anything the pass emits at that position. The pass's
  per-key emission is in tag order (@{text P.titems_emission_sorted}), so
  by @{text insert_at_sorted} the entry goes right after the last item of
  the key tagged at or before R's close.
\<close>

theorem titems_inter:
  assumes svl2: "R.svl_ok2 svl2"
      and s0hi2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_hi u)"
  shows "P.titems_for k (inter_t svl1 svl2 s0) =
           (if k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k))
            then insert_at (den (u_hi (R.the_unit k)))
                   [(den (u_hi (R.the_unit k)), Event k (u_refresh (R.the_unit k) k))]
                   (P.titems_for k (P.emission_t svl1 s0))
            else P.titems_for k (P.emission_t svl1 s0))"
proof -
  define A where "A = (\<lambda>p. P.titems_for k (P.closes_at svl1 p))"
  define B where "B = (\<lambda>p. P.titems_for k (R.closes_at svl2 p))"
  define E where "E = (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])"
  have inter_dist: "P.titems_for k (inter_t svl1 svl2 s0)
        = concat (map (\<lambda>p. A p @ B p @ E p) [den s0..<den f1]) @ A (den f1) @ B (den f1)"
    unfolding inter_t_def P.titems_for_def A_def B_def E_def
    by (simp add: filter_concat_map comp_def cong: map_cong if_cong)
  have emis_dist: "P.titems_for k (P.emission_t svl1 s0)
        = concat (map (\<lambda>p. A p @ E p) [den s0..<den f1]) @ A (den f1)"
    unfolding P.emission_t_def P.titems_for_def A_def E_def
    by (simp add: filter_concat_map comp_def cong: map_cong if_cong)
  have A_tag: "fst x = p" if "x \<in> set (A p)" for p x
  proof -
    have "x \<in> set (P.closes_at svl1 p)" using that by (simp add: A_def P.titems_for_def)
    then show ?thesis by (rule P.closes_at_tag)
  qed
  have E_tag: "fst x = Suc p" if "x \<in> set (E p)" for p x
    using that by (auto simp: E_def split: if_splits)
  show ?thesis
  proof (cases "k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k))")
    case listed: True
    define h where "h = den (u_hi (R.the_unit k))"
    define r where "r = (h, Event k (u_refresh (R.the_unit k) k))"
    have k2: "k \<in> sc2" using listed by simp
    have u_in: "R.the_unit k \<in> set U2" by (rule R.the_unit_props(1)[OF k2])
    have B_at: "B p = (if p = h then [r] else [])" for p
      using R.titems_closes_at2[OF svl2 k2, of p] listed by (auto simp: B_def h_def r_def)
    have ah: "den s0 \<le> h" using s0hi2[OF u_in] by (simp add: h_def)
    have hb: "h \<le> den f1" using R.bracket_hi_f[OF u_in] by (simp add: h_def P.cle_def)
    have "P.titems_for k (inter_t svl1 svl2 s0)
            = insert_at h [r] (concat (map (\<lambda>p. A p @ E p) [den s0..<den f1]) @ A (den f1))"
      unfolding inter_dist by (rule concat_blocks_insert[OF A_tag E_tag B_at ah hb])
    then show ?thesis using listed emis_dist by (simp add: h_def r_def)
  next
    case unlisted: False
    have B_nil: "B p = []" for p
    proof (cases "k \<in> sc2")
      case True
      then show ?thesis using R.titems_closes_at2[OF svl2 True, of p] unlisted by (simp add: B_def)
    next
      case False
      then show ?thesis using R.titems_closes_at_out[OF svl2 False, of p] by (simp add: B_def)
    qed
    have "P.titems_for k (inter_t svl1 svl2 s0) = P.titems_for k (P.emission_t svl1 s0)"
      unfolding inter_dist emis_dist B_nil by simp
    then show ?thesis by (simp only: if_not_P[OF unlisted])
  qed
qed

subsubsection \<open>A key that the stream mentions ends at the source state\<close>

text \<open>
  If the interleaved stream carries anything for a key, the key ends at the
  source state at the frontier, from any initial sink state. This needs no
  per-unit consumption-start premise, only that the consumption start lies at
  or before the frontier: otherwise only the stream's own items enter.
\<close>

lemma inter_key_replay:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0f1: "den s0 \<le> den f1"
      and ne: "P.titems_for k (inter_t svl1 svl2 s0) \<noteq> []"
  shows "state_after D (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof -
  define T where "T = P.titems_for k (inter_t svl1 svl2 s0)"
  have T_ne: "T \<noteq> []" using ne by (simp add: T_def)
  have T_item: "x \<in> set (inter_t svl1 svl2 s0)" and T_key: "ev_key (snd x) = k"
    if "x \<in> set T" for x
    using that by (simp_all add: T_def P.titems_for_def)
  have keyed: "\<And>x. x \<in> set T \<Longrightarrow> ev_key (snd x) = k" by (rule T_key)
  have honest: "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k" if "x \<in> set T" for x
    using inter_item_honest[OF svl1 svl2 T_item[OF that]] T_key[OF that] by simp
  have sorted: "sorted (map fst T)"
    unfolding T_def P.titems_for_def by (rule sorted_map_fst_filter[OF inter_t_sorted])
  have low: "den s0 \<le> fst x" and high: "fst x \<le> den f1" if "x \<in> set T" for x
    using inter_t_tag_bounds[OF s0f1 T_item[OF that]] by simp_all
  have complete: "(Suc p, L ! p) \<in> set T"
    if "den s0 \<le> p" "p < den f1" "ev_key (L ! p) = k" for p
    unfolding T_def by (rule inter_key_complete[OF that])
  have evs: "evs_for k (inter svl1 svl2 s0) = evs_for k (map snd T)"
    by (simp add: inter_def P.evs_for_map_snd T_def P.titems_for_def)
  have "state_after D (inter svl1 svl2 s0) k = state_after D (map snd T) k"
    by (rule replay_per_key[OF evs])
  also have "\<dots> = state_after \<sigma>0 (take (den f1) L) k"
    by (rule honest_stream_last[OF T_ne keyed honest sorted low high complete])
  also have "\<dots> = state_after \<sigma>0 (P.pfx f1) k"
    by (simp add: P.pfx_def)
  finally show ?thesis .
qed

subsubsection \<open>Safety and convergence\<close>

theorem pass_with_request_safe:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and k: "k \<in> sc1 \<union> sc2"
  shows "state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k
         \<or> (state_after D0 (inter svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f1) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f1) = [])"
proof -
  define T where "T = P.titems_for k (inter_t svl1 svl2 s0)"
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  have R_s0lo: "\<And>u. u \<in> set U2 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo2 by (simp add: P.cle_def)
  have s0hi2: "den s0 \<le> den (u_hi u)" if u: "u \<in> set U2" for u
  proof -
    have "den (u_lo u) \<le> den (u_hi u)" using R.bracket_lo_hi[OF u] by (simp add: P.cle_def)
    then show ?thesis using s0lo2[OF u] by simp
  qed
  have s0f1: "den s0 \<le> den f1"
  proof (cases "k \<in> sc1")
    case True
    have u: "P.the_unit k \<in> set U1" by (rule P.the_unit_props(1)[OF True])
    have "P.cle s0 (u_lo (P.the_unit k))" by (rule P_s0lo[OF u])
    also have "P.cle (u_lo (P.the_unit k)) (u_hi (P.the_unit k))" by (rule P.bracket_lo_hi[OF u])
    also have "P.cle (u_hi (P.the_unit k)) f1" by (rule P.bracket_hi_f[OF u])
    finally show ?thesis by (simp add: P.cle_def)
  next
    case False
    then have k2: "k \<in> sc2" using k by simp
    have u: "R.the_unit k \<in> set U2" by (rule R.the_unit_props(1)[OF k2])
    have "P.cle s0 (u_lo (R.the_unit k))" by (rule R_s0lo[OF u])
    also have "P.cle (u_lo (R.the_unit k)) (u_hi (R.the_unit k))" by (rule R.bracket_lo_hi[OF u])
    also have "P.cle (u_hi (R.the_unit k)) f1" by (rule R.bracket_hi_f[OF u])
    finally show ?thesis by (simp add: P.cle_def)
  qed
  consider (mentioned) "T \<noteq> []" | (silent) "T = []" by blast
  then show ?thesis
  proof cases
    case mentioned
    have "state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
      by (rule inter_key_replay[OF svl1 svl2 s0f1 mentioned[unfolded T_def]])
    then show ?thesis ..
  next
    case silent
    have kept: "state_after D0 (inter svl1 svl2 s0) k = D0 k"
    proof -
      have "evs_for k (inter svl1 svl2 s0) = []"
        using silent by (simp add: inter_def P.evs_for_map_snd T_def)
      then show ?thesis by (rule state_after_no_events)
    qed
    have char: "T = (if k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k))
                     then insert_at (den (u_hi (R.the_unit k)))
                            [(den (u_hi (R.the_unit k)), Event k (u_refresh (R.the_unit k) k))]
                            (P.titems_for k (P.emission_t svl1 s0))
                     else P.titems_for k (P.emission_t svl1 s0))"
      unfolding T_def by (rule titems_inter[OF svl2 s0hi2])
    have R_unlisted: "\<not> (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
    proof
      assume listed: "k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k))"
      have "T = insert_at (den (u_hi (R.the_unit k)))
                  [(den (u_hi (R.the_unit k)), Event k (u_refresh (R.the_unit k) k))]
                  (P.titems_for k (P.emission_t svl1 s0))"
        using char listed by simp
      then have "T \<noteq> []" by (simp add: insert_at_def)
      with silent show False by simp
    qed
    have T_pass: "T = P.titems_for k (P.emission_t svl1 s0)"
      using char by (simp only: if_not_P[OF R_unlisted])
    have P_empty: "P.titems_for k (P.emission_t svl1 s0) = []"
      using T_pass silent by simp
    have quiet: "evs_for k (P.win s0 f1) = []"
    proof -
      have no_ev: "ev_key (L ! p) \<noteq> k" if p: "p \<in> set [den s0..<den f1]" for p
      proof
        assume key: "ev_key (L ! p) = k"
        have "den s0 \<le> p" "p < den f1" using p by simp_all
        then have "(Suc p, L ! p) \<in> set T"
          unfolding T_def by (rule inter_key_complete[OF _ _ key])
        with silent show False by simp
      qed
      have "P.kposs k (den s0) (den f1) = []"
        using no_ev by (simp add: P.kposs_def filter_empty_conv)
      moreover have "P.cle s0 f1" using s0f1 by (simp add: P.cle_def)
      ultimately show ?thesis using P.evs_for_win_kposs by simp
    qed
    have P_unlisted: "k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k))"
    proof
      assume k1: "k \<in> sc1"
      have master: "P.titems_for k (P.emission_t svl1 s0) =
             map (\<lambda>p. (Suc p, L ! p)) (P.kposs k (den s0) (den (u_hi (P.the_unit k))))
             @ (if k \<in> set (svl1 (P.the_unit k))
                then [(den (u_hi (P.the_unit k)),
                       Event k (u_refresh (P.the_unit k) k))] else [])
             @ map (\<lambda>p. (Suc p, L ! p)) (P.kposs k (den (u_hi (P.the_unit k))) (den f1))"
        by (rule P.titems_emission_master2[OF svl1 P_s0lo k1])
      have "k \<in> set (svl1 (P.the_unit k)) \<Longrightarrow> P.titems_for k (P.emission_t svl1 s0) \<noteq> []"
        unfolding master by simp
      with P_empty show "k \<notin> set (svl1 (P.the_unit k))" by blast
    qed
    have src_none: "state_after \<sigma>0 (P.pfx f1) k = None"
    proof (cases "k \<in> sc1")
      case k1: True
      have nl1: "k \<notin> set (svl1 (P.the_unit k))" using P_unlisted k1 by simp
      show ?thesis using P.unlisted_quiet_absent[OF svl1 P_s0lo k1 nl1 quiet] .
    next
      case False
      then have k2: "k \<in> sc2" using k by simp
      have nl2: "k \<notin> set (svl2 (R.the_unit k))" using R_unlisted k2 by simp
      show ?thesis using R.unlisted_quiet_absent[OF svl2 R_s0lo k2 nl2 quiet] .
    qed
    show ?thesis
      using kept src_none R_unlisted P_unlisted quiet by auto
  qed
qed

theorem pass_with_request_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and cover: "\<And>k. k \<in> sc1 \<union> sc2 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow>
                    state_after \<sigma>0 (P.pfx f1) k = None \<Longrightarrow>
                    evs_for k (P.win s0 f1) = [] \<Longrightarrow>
                    (k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
                    (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof
  fix k assume k: "k \<in> sc1 \<union> sc2"
  have disj: "state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k
         \<or> (state_after D0 (inter svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f1) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f1) = [])"
    by (rule pass_with_request_safe[OF svl1 svl2 s0lo s0lo2 k])
  from disj show "state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
  proof
    assume "state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
    then show ?thesis .
  next
    assume o: "state_after D0 (inter svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f1) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f1) = []"
    show ?thesis
    proof (cases "D0 k = None")
      case True
      then show ?thesis using o by simp
    next
      case False
      have src_none: "state_after \<sigma>0 (P.pfx f1) k = None" using o by simp
      have quiet: "evs_for k (P.win s0 f1) = []" using o by simp
      have "(k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
            (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
        by (rule cover[OF k False src_none quiet])
      then show ?thesis using o by auto
    qed
  qed
qed

subsubsection \<open>A request that lists its absent keys completes the pass\<close>

corollary pass_with_listing_request_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and lists_absent: "\<And>u. u \<in> set U2 \<Longrightarrow> R.absent_untouched u \<subseteq> set (svl2 u)"
      and in_scope: "\<And>k. k \<in> sc1 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow> P.sink_at f1 k = None \<Longrightarrow>
                       k \<notin> set (svl1 (P.the_unit k)) \<Longrightarrow>
                       evs_for k (P.win s0 f1) = [] \<Longrightarrow> k \<in> sc2"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof (rule pass_with_request_converges[OF svl1 svl2 s0lo s0lo2])
  fix k
  assume k: "k \<in> sc1 \<union> sc2" and held: "D0 k \<noteq> None"
     and src_none: "state_after \<sigma>0 (P.pfx f1) k = None"
     and quiet: "evs_for k (P.win s0 f1) = []"
  show "(k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
        (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  proof (cases "k \<in> sc2")
    case k2: True
    define u where "u = R.the_unit k"
    have u_in: "u \<in> set U2" and k_dom: "k \<in> u_dom u"
      using R.the_unit_props[OF k2] u_def by auto
    have lo_hi: "P.cle (u_lo u) (u_hi u)" by (rule R.bracket_lo_hi[OF u_in])
    have hi_f1: "P.cle (u_hi u) f1" by (rule R.bracket_hi_f[OF u_in])
    have s0_lo: "P.cle s0 (u_lo u)" using s0lo2[OF u_in] by (simp add: P.cle_def)
    have lo_f1: "P.cle (u_lo u) f1" using lo_hi hi_f1 by (rule P.cle_trans)
    have lo_f1_q: "evs_for k (P.win (u_lo u) f1) = []"
      using P.evs_for_win_split[OF s0_lo lo_f1] quiet by simp
    have win_q: "evs_for k (P.win (u_lo u) (u_hi u)) = []"
      using P.evs_for_win_split[OF lo_hi hi_f1] lo_f1_q by simp
    obtain c where c_lo: "P.cle (u_lo u) c" and c_hi: "P.cle c (u_hi u)"
      and honest: "u_refresh u k = state_after \<sigma>0 (P.pfx c) k"
      using R.O2_honest[OF u_in k_dom] by blast
    have c_f1: "P.cle c f1" using c_hi hi_f1 by (rule P.cle_trans)
    have "state_after \<sigma>0 (P.pfx c) k = state_after \<sigma>0 (P.pfx (u_lo u)) k"
      by (rule P.win_invariant_state[OF c_lo c_f1 lo_f1_q])
    also have "\<dots> = state_after \<sigma>0 (P.pfx f1) k"
      by (rule P.win_invariant_state[OF lo_f1 P.cle_refl lo_f1_q, symmetric])
    finally have "u_refresh u k = None" using honest src_none by simp
    then have "k \<in> R.absent_untouched u"
      using k_dom win_q by (simp add: R.absent_untouched_def)
    then have "k \<in> set (svl2 u)" using lists_absent[OF u_in] by auto
    then show ?thesis using k2 u_def by simp
  next
    case k2: False
    then have k1: "k \<in> sc1" using k by simp
    have sink_none: "P.sink_at f1 k = None"
      using P.contract_cut[OF k1] src_none by simp
    have "k \<in> set (svl1 (P.the_unit k))"
      using in_scope[OF k1 held sink_none] quiet k2 by blast
    then show ?thesis using k1 by simp
  qed
qed

text \<open>
  The keys a pass leaves wrong are exactly the unlisted keys of its scope
  that the sink holds, that are absent at the pass's frontier, and that no
  log event during the pass mentions. This is a fact about the pass alone.
  Statement and proof are those of @{text Orphan_Absence_Composition}.
\<close>

lemma pass_leaves_wrong_iff:
  assumes svl1: "P.svl_ok2 svl1"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and k1: "k \<in> sc1"
  shows "state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k \<longleftrightarrow>
           D0 k \<noteq> None \<and> P.sink_at f1 k = None \<and>
           k \<notin> set (svl1 (P.the_unit k)) \<and> evs_for k (P.win s0 f1) = []"
proof
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  assume wrong: "state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k"
  have "state_after D0 (P.emission svl1 s0) k = P.sink_at f1 k
        \<or> (state_after D0 (P.emission svl1 s0) k = D0 k
           \<and> P.sink_at f1 k = None
           \<and> k \<in> P.absent_untouched (P.the_unit k)
           \<and> k \<notin> set (svl1 (P.the_unit k))
           \<and> evs_for k (P.win s0 f1) = [])"
    by (rule P.absent_replay_safe[OF svl1 P_s0lo k1])
  then show "D0 k \<noteq> None \<and> P.sink_at f1 k = None \<and>
             k \<notin> set (svl1 (P.the_unit k)) \<and> evs_for k (P.win s0 f1) = []"
    using wrong by auto
next
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  assume r: "D0 k \<noteq> None \<and> P.sink_at f1 k = None \<and>
             k \<notin> set (svl1 (P.the_unit k)) \<and> evs_for k (P.win s0 f1) = []"
  have nl: "k \<notin> set (svl1 (P.the_unit k))" and pass_q: "evs_for k (P.win s0 f1) = []"
    using r by simp_all
  have "state_after D0 (P.emission svl1 s0) k = D0 k"
    by (rule P.unlisted_quiet_key_kept[OF svl1 P_s0lo k1 nl pass_q])
  then show "state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k"
    using r by simp
qed

text \<open>
  For a key-list request served inside the pass, the request's scope holds
  every requested key that is absent at the coordinate @{text "rc k"} where
  the request reads it, each coordinate inside the pass's span (a request
  that runs in batches reads each batch at its own coordinate). Then it
  suffices that every key the pass leaves wrong was requested.
\<close>

corollary request_in_pass_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and lists_absent: "\<And>u. u \<in> set U2 \<Longrightarrow> R.absent_untouched u \<subseteq> set (svl2 u)"
      and s0_rc: "\<And>k. k \<in> K \<Longrightarrow> den s0 \<le> den (rc k)"
      and rc_f1: "\<And>k. k \<in> K \<Longrightarrow> den (rc k) \<le> den f1"
      and sc2_abs: "\<And>k. k \<in> K \<Longrightarrow> state_after \<sigma>0 (P.pfx (rc k)) k = None \<Longrightarrow> k \<in> sc2"
      and asked: "\<And>k. k \<in> sc1 \<Longrightarrow>
                    state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k \<Longrightarrow> k \<in> K"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof (rule pass_with_listing_request_converges[OF svl1 svl2 s0lo s0lo2 lists_absent])
  fix k
  assume k1: "k \<in> sc1" and held: "D0 k \<noteq> None" and sink_none: "P.sink_at f1 k = None"
     and nl: "k \<notin> set (svl1 (P.the_unit k))" and quiet: "evs_for k (P.win s0 f1) = []"
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  have kept: "state_after D0 (P.emission svl1 s0) k = D0 k"
    by (rule P.unlisted_quiet_key_kept[OF svl1 P_s0lo k1 nl quiet])
  have wrong: "state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k"
    using kept held sink_none by simp
  have kK: "k \<in> K" by (rule asked[OF k1 wrong])
  have s0rc: "P.cle s0 (rc k)" using s0_rc[OF kK] by (simp add: P.cle_def)
  have rcf1: "P.cle (rc k) f1" using rc_f1[OF kK] by (simp add: P.cle_def)
  have s0_f1: "P.cle s0 f1" using s0rc rcf1 by (rule P.cle_trans)
  have "state_after \<sigma>0 (P.pfx (rc k)) k = state_after \<sigma>0 (P.pfx s0) k"
    by (rule P.win_invariant_state[OF s0rc rcf1 quiet])
  also have "\<dots> = state_after \<sigma>0 (P.pfx f1) k"
    by (rule P.win_invariant_state[OF s0_f1 P.cle_refl quiet, symmetric])
  also have "\<dots> = None"
    using P.contract_cut[OF k1] sink_none by simp
  finally have "state_after \<sigma>0 (P.pfx (rc k)) k = None" .
  then show "k \<in> sc2" by (rule sc2_abs[OF kK])
qed

subsubsection \<open>The reverse tie order at equal positions\<close>

text \<open>
  The stream @{text inter_t} puts P's close block before R's when both sit at
  the same position. The variant below puts R's block first. Both streams
  carry the same items, both are in position order, and every item is
  honest at its tag, so they replay to the same value on every key of either
  scope. Safety and convergence therefore hold for either tie order.
\<close>

definition inter_t_rev ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "inter_t_rev svl1 svl2 s0 =
     concat (map (\<lambda>p. R.closes_at svl2 p @ P.closes_at svl1 p @ [(Suc p, L ! p)])
                 [den s0..<den f1])
     @ R.closes_at svl2 (den f1) @ P.closes_at svl1 (den f1)"

definition inter_rev ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> ('k, 'v) event list" where
  "inter_rev svl1 svl2 s0 = map snd (inter_t_rev svl1 svl2 s0)"

lemma inter_t_rev_set: "set (inter_t_rev svl1 svl2 s0) = set (inter_t svl1 svl2 s0)"
  by (auto simp: inter_t_rev_def inter_t_def)

lemma inter_t_rev_sorted: "sorted (map fst (inter_t_rev svl1 svl2 s0))"
proof -
  have C: "fst x = p" if "x \<in> set (R.closes_at svl2 p @ P.closes_at svl1 p)" for x p
    using that by (auto dest: P.closes_at_tag R.closes_at_tag)
  have "sorted (map fst (concat (map (\<lambda>p. (R.closes_at svl2 p @ P.closes_at svl1 p)
                                            @ [(Suc p, L ! p)]) [den s0..<den f1])
                         @ (R.closes_at svl2 (den f1) @ P.closes_at svl1 (den f1))))"
    using blocks_sorted[where C = "\<lambda>p. R.closes_at svl2 p @ P.closes_at svl1 p" and z = "(!) L"
                          and a = "den s0" and b = "den f1", OF C] by simp
  then show ?thesis by (simp add: inter_t_rev_def)
qed

lemma inter_rev_key_replay:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0f1: "den s0 \<le> den f1"
      and ne: "P.titems_for k (inter_t_rev svl1 svl2 s0) \<noteq> []"
  shows "state_after D (inter_rev svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof -
  define T where "T = P.titems_for k (inter_t_rev svl1 svl2 s0)"
  have T_ne: "T \<noteq> []" using ne by (simp add: T_def)
  have T_set: "set T = set (P.titems_for k (inter_t svl1 svl2 s0))"
    by (simp add: T_def P.titems_for_def inter_t_rev_set)
  have T_item: "x \<in> set (inter_t svl1 svl2 s0)" and T_key: "ev_key (snd x) = k"
    if "x \<in> set T" for x
    using that by (simp_all add: T_set P.titems_for_def)
  have keyed: "\<And>x. x \<in> set T \<Longrightarrow> ev_key (snd x) = k" by (rule T_key)
  have honest: "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k" if "x \<in> set T" for x
    using inter_item_honest[OF svl1 svl2 T_item[OF that]] T_key[OF that] by simp
  have sorted: "sorted (map fst T)"
    unfolding T_def P.titems_for_def by (rule sorted_map_fst_filter[OF inter_t_rev_sorted])
  have low: "den s0 \<le> fst x" and high: "fst x \<le> den f1" if "x \<in> set T" for x
    using inter_t_tag_bounds[OF s0f1 T_item[OF that]] by simp_all
  have complete: "(Suc p, L ! p) \<in> set T"
    if "den s0 \<le> p" "p < den f1" "ev_key (L ! p) = k" for p
    unfolding T_set by (rule inter_key_complete[OF that])
  have evs: "evs_for k (inter_rev svl1 svl2 s0) = evs_for k (map snd T)"
    by (simp add: inter_rev_def P.evs_for_map_snd T_def P.titems_for_def)
  have "state_after D (inter_rev svl1 svl2 s0) k = state_after D (map snd T) k"
    by (rule replay_per_key[OF evs])
  also have "\<dots> = state_after \<sigma>0 (take (den f1) L) k"
    by (rule honest_stream_last[OF T_ne keyed honest sorted low high complete])
  also have "\<dots> = state_after \<sigma>0 (P.pfx f1) k"
    by (simp add: P.pfx_def)
  finally show ?thesis .
qed

text \<open>Under either tie order, every key replays to the same value.\<close>

lemma inter_rev_same_replay:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0f1: "den s0 \<le> den f1"
  shows "state_after D (inter_rev svl1 svl2 s0) k = state_after D (inter svl1 svl2 s0) k"
proof -
  define T where "T = P.titems_for k (inter_t svl1 svl2 s0)"
  define T' where "T' = P.titems_for k (inter_t_rev svl1 svl2 s0)"
  have sets: "set T' = set T"
    by (simp add: T_def T'_def P.titems_for_def inter_t_rev_set)
  consider (silent) "T = []" | (mentioned) "T \<noteq> []" by blast
  then show ?thesis
  proof cases
    case silent
    then have "T' = []" using sets by simp
    then have "evs_for k (inter_rev svl1 svl2 s0) = []"
      by (simp add: inter_rev_def P.evs_for_map_snd T'_def)
    moreover have "evs_for k (inter svl1 svl2 s0) = []"
      using silent by (simp add: inter_def P.evs_for_map_snd T_def)
    ultimately show ?thesis by (simp add: state_after_no_events)
  next
    case mentioned
    then have "T' \<noteq> []" using sets by auto
    then have "state_after D (inter_rev svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
      unfolding T'_def by (rule inter_rev_key_replay[OF svl1 svl2 s0f1])
    moreover have "state_after D (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
      using mentioned unfolding T_def by (rule inter_key_replay[OF svl1 svl2 s0f1])
    ultimately show ?thesis by simp
  qed
qed

lemma s0_le_f1_of_key:
  assumes s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and k: "k \<in> sc1 \<union> sc2"
  shows "den s0 \<le> den f1"
proof (cases "k \<in> sc1")
  case True
  have u: "P.the_unit k \<in> set U1" by (rule P.the_unit_props(1)[OF True])
  have "den (u_lo (P.the_unit k)) \<le> den (u_hi (P.the_unit k))"
    using P.bracket_lo_hi[OF u] by (simp add: P.cle_def)
  moreover have "den (u_hi (P.the_unit k)) \<le> den f1"
    using P.bracket_hi_f[OF u] by (simp add: P.cle_def)
  ultimately show ?thesis using s0lo[OF u] by simp
next
  case False
  then have k2: "k \<in> sc2" using k by simp
  have u: "R.the_unit k \<in> set U2" by (rule R.the_unit_props(1)[OF k2])
  have "den (u_lo (R.the_unit k)) \<le> den (u_hi (R.the_unit k))"
    using R.bracket_lo_hi[OF u] by (simp add: P.cle_def)
  moreover have "den (u_hi (R.the_unit k)) \<le> den f1"
    using R.bracket_hi_f[OF u] by (simp add: P.cle_def)
  ultimately show ?thesis using s0lo2[OF u] by simp
qed

theorem pass_with_request_safe_rev:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and k: "k \<in> sc1 \<union> sc2"
  shows "state_after D0 (inter_rev svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k
         \<or> (state_after D0 (inter_rev svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f1) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f1) = [])"
proof -
  have s0f1: "den s0 \<le> den f1" by (rule s0_le_f1_of_key[OF s0lo s0lo2 k])
  have same: "state_after D0 (inter_rev svl1 svl2 s0) k = state_after D0 (inter svl1 svl2 s0) k"
    by (rule inter_rev_same_replay[OF svl1 svl2 s0f1])
  show ?thesis
    unfolding same by (rule pass_with_request_safe[OF svl1 svl2 s0lo s0lo2 k])
qed

theorem pass_with_request_converges_rev:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and cover: "\<And>k. k \<in> sc1 \<union> sc2 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow>
                    state_after \<sigma>0 (P.pfx f1) k = None \<Longrightarrow>
                    evs_for k (P.win s0 f1) = [] \<Longrightarrow>
                    (k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
                    (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (inter_rev svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
proof
  fix k assume k: "k \<in> sc1 \<union> sc2"
  have s0f1: "den s0 \<le> den f1" by (rule s0_le_f1_of_key[OF s0lo s0lo2 k])
  have same: "state_after D0 (inter_rev svl1 svl2 s0) k = state_after D0 (inter svl1 svl2 s0) k"
    by (rule inter_rev_same_replay[OF svl1 svl2 s0f1])
  have "\<forall>k \<in> sc1 \<union> sc2.
          state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
    by (rule pass_with_request_converges[OF svl1 svl2 s0lo s0lo2 cover])
  then show "state_after D0 (inter_rev svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
    using same k by simp
qed

subsubsection \<open>Any tie order at equal positions\<close>

text \<open>
  More generally, take any timed list @{text T} with the same items as
  @{text inter_t} and in position order. It may break ties differently at
  different positions, or interleave P's and R's entries within one
  position. It replays to the same value as @{text inter_t} on every key,
  so safety and convergence hold for it unchanged. The lemma
  @{text inter_any_same_replay} and its proof are adopted from the blind
  review of this theory (lemma @{text probe_any_tie_order} of the
  reviewer's probe theory). The stream @{text inter_t_rev} is one such list
  (@{text inter_t_rev_set}, @{text inter_t_rev_sorted}).
\<close>

lemma inter_any_same_replay:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0f1: "den s0 \<le> den f1"
      and T_set: "set T = set (inter_t svl1 svl2 s0)"
      and T_sorted: "sorted (map fst T)"
  shows "state_after D (map snd T) k = state_after D (inter svl1 svl2 s0) k"
proof -
  define Tk where "Tk = P.titems_for k T"
  define T0 where "T0 = P.titems_for k (inter_t svl1 svl2 s0)"
  have sets: "set Tk = set T0" by (simp add: Tk_def T0_def P.titems_for_def T_set)
  consider (silent) "T0 = []" | (mentioned) "T0 \<noteq> []" by blast
  then show ?thesis
  proof cases
    case silent
    then have "Tk = []" using sets by simp
    then have "evs_for k (map snd T) = []" by (simp add: P.evs_for_map_snd Tk_def)
    moreover have "evs_for k (inter svl1 svl2 s0) = []"
      using silent by (simp add: inter_def P.evs_for_map_snd T0_def)
    ultimately show ?thesis by (simp add: state_after_no_events)
  next
    case mentioned
    have Tk_ne: "Tk \<noteq> []" using mentioned sets by auto
    have Tk_item: "x \<in> set (inter_t svl1 svl2 s0)" and Tk_key: "ev_key (snd x) = k"
      if "x \<in> set Tk" for x
      using that by (simp_all add: Tk_def P.titems_for_def T_set)
    have keyed: "\<And>x. x \<in> set Tk \<Longrightarrow> ev_key (snd x) = k" by (rule Tk_key)
    have honest: "ev_img (snd x) = state_after \<sigma>0 (take (fst x) L) k" if "x \<in> set Tk" for x
      using inter_item_honest[OF svl1 svl2 Tk_item[OF that]] Tk_key[OF that] by simp
    have sorted: "sorted (map fst Tk)"
      unfolding Tk_def P.titems_for_def by (rule sorted_map_fst_filter[OF T_sorted])
    have low: "den s0 \<le> fst x" and high: "fst x \<le> den f1" if "x \<in> set Tk" for x
      using inter_t_tag_bounds[OF s0f1 Tk_item[OF that]] by simp_all
    have complete: "(Suc p, L ! p) \<in> set Tk"
      if "den s0 \<le> p" "p < den f1" "ev_key (L ! p) = k" for p
      unfolding sets T0_def by (rule inter_key_complete[OF that])
    have "state_after D (map snd T) k = state_after D (map snd Tk) k"
      by (rule replay_per_key) (simp add: P.evs_for_map_snd Tk_def P.titems_for_def)
    also have "\<dots> = state_after \<sigma>0 (take (den f1) L) k"
      by (rule honest_stream_last[OF Tk_ne keyed honest sorted low high complete])
    also have "\<dots> = state_after D (inter svl1 svl2 s0) k"
      using inter_key_replay[OF svl1 svl2 s0f1 mentioned[unfolded T0_def]]
      by (simp add: P.pfx_def)
    finally show ?thesis .
  qed
qed

theorem pass_with_request_safe_any:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and T_set: "set T = set (inter_t svl1 svl2 s0)"
      and T_sorted: "sorted (map fst T)"
      and k: "k \<in> sc1 \<union> sc2"
  shows "state_after D0 (map snd T) k = state_after \<sigma>0 (P.pfx f1) k
         \<or> (state_after D0 (map snd T) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f1) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f1) = [])"
proof -
  have s0f1: "den s0 \<le> den f1" by (rule s0_le_f1_of_key[OF s0lo s0lo2 k])
  have same: "state_after D0 (map snd T) k = state_after D0 (inter svl1 svl2 s0) k"
    by (rule inter_any_same_replay[OF svl1 svl2 s0f1 T_set T_sorted])
  show ?thesis
    unfolding same by (rule pass_with_request_safe[OF svl1 svl2 s0lo s0lo2 k])
qed

theorem pass_with_request_converges_any:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and T_set: "set T = set (inter_t svl1 svl2 s0)"
      and T_sorted: "sorted (map fst T)"
      and cover: "\<And>k. k \<in> sc1 \<union> sc2 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow>
                    state_after \<sigma>0 (P.pfx f1) k = None \<Longrightarrow>
                    evs_for k (P.win s0 f1) = [] \<Longrightarrow>
                    (k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
                    (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (map snd T) k = state_after \<sigma>0 (P.pfx f1) k"
proof
  fix k assume k: "k \<in> sc1 \<union> sc2"
  have s0f1: "den s0 \<le> den f1" by (rule s0_le_f1_of_key[OF s0lo s0lo2 k])
  have same: "state_after D0 (map snd T) k = state_after D0 (inter svl1 svl2 s0) k"
    by (rule inter_any_same_replay[OF svl1 svl2 s0f1 T_set T_sorted])
  have "\<forall>k \<in> sc1 \<union> sc2.
          state_after D0 (inter svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f1) k"
    by (rule pass_with_request_converges[OF svl1 svl2 s0lo s0lo2 cover])
  then show "state_after D0 (map snd T) k = state_after \<sigma>0 (P.pfx f1) k"
    using same k by simp
qed

end  (* locale pass_with_request *)

subsection \<open>Fixtures: a request served inside the pass removes the orphan\<close>

text \<open>
  The pass of the orphan fixture of @{text Orphan_Absence}, run with the
  core's survivor-only enumeration from coordinate 0 to frontier 2, leaves
  the orphan key 4 in the sink. Its one chunk owns keys 3 and 4 with
  bracket (1, 2] and closes at position 2. Three requests for key 4 are
  served inside the pass's span, the second at its frontier, each the
  one-unit contract of @{text absence_assertion_contract}:

  \<^item> One with bracket (0, 1], read at 1, closes before the chunk does.
  \<^item> The request of @{text Orphan_Absence_Composition}, bracket (2, 2],
    read at 2, closes at the pass's frontier, after the chunk at the same
    position. Its stream is the sequential composition of that theory.
  \<^item> One with bracket (0, 2], read at 1, has a window that overlaps the
    chunk's window, which a non-overlap assumption would exclude.

  Each interleaved stream removes the orphan.
\<close>

definition rqb_unit :: "(nat, nat, nat) cunit" where
  "rqb_unit = \<lparr>u_dom = {4}, u_lo = 0, u_hi = 1, u_refresh = (\<lambda>_. None)\<rparr>"

definition rqo_unit :: "(nat, nat, nat) cunit" where
  "rqo_unit = \<lparr>u_dom = {4}, u_lo = 0, u_hi = 2, u_refresh = (\<lambda>_. None)\<rparr>"

lemma src_4_none: "state_after s0_w (sc.pfx c) 4 = None"
proof -
  have "\<forall>x \<in> set (sc.pfx c). ev_key x \<noteq> 4"
    unfolding sc.pfx_def using set_take_subset[of "den_w c" L_s] by (auto simp: L_s_def)
  then have "evs_for 4 (sc.pfx c) = []" by (simp add: evs_for_def filter_empty_conv)
  then show ?thesis by (simp add: state_after_no_events s0_w_def)
qed

lemma rqb_contract: "capture_contract L_s den_w s0_w [rqb_unit] {4} 2"
proof -
  have empty: "\<And>k. k \<in> {4} \<Longrightarrow> state_after s0_w (sc.pfx 1) k = None"
    using src_4_none by simp
  show ?thesis
    unfolding rqb_unit_def
    by (rule sc.absence_assertion_contract[where c = 1, OF _ _ _ empty])
       (simp_all add: sc.cle_def den_w_def)
qed

lemma rqo_contract: "capture_contract L_s den_w s0_w [rqo_unit] {4} 2"
proof -
  have empty: "\<And>k. k \<in> {4} \<Longrightarrow> state_after s0_w (sc.pfx 1) k = None"
    using src_4_none by simp
  show ?thesis
    unfolding rqo_unit_def
    by (rule sc.absence_assertion_contract[where c = 1, OF _ _ _ empty])
       (simp_all add: sc.cle_def den_w_def)
qed

interpretation rqb: capture_contract L_s den_w s0_w "[rqb_unit]" "{4}" 2
  by (rule rqb_contract)

interpretation rqo: capture_contract L_s den_w s0_w "[rqo_unit]" "{4}" 2
  by (rule rqo_contract)

interpretation pwb: pass_with_request L_s den_w s0_w "[orph_unit]" "{3, 4}" 2 "[rqb_unit]" "{4}"
  by intro_locales

interpretation pwa: pass_with_request L_s den_w s0_w "[orph_unit]" "{3, 4}" 2 "[rq_unit]" "{4}"
  by intro_locales

interpretation pwo: pass_with_request L_s den_w s0_w "[orph_unit]" "{3, 4}" 2 "[rqo_unit]" "{4}"
  by intro_locales

lemma rqb_absent_untouched: "rqb.absent_untouched rqb_unit = {4}"
proof -
  have "evs_for 4 (sc.win (u_lo rqb_unit) (u_hi rqb_unit)) = []"
    unfolding sc.win_def by (simp add: rqb_unit_def den_w_def L_s_def evs_for_def)
  then show ?thesis by (auto simp: rqb.absent_untouched_def rqb_unit_def)
qed

lemma rqb_svl_ok2: "rqb.svl_ok2 (\<lambda>_. [4])"
proof -
  have "rqb.survivors rqb_unit = {}" by (auto simp: rqb.survivors_def rqb_unit_def)
  then show ?thesis using rqb_absent_untouched by (simp add: rqb.svl_ok2_def)
qed

lemma rqo_absent_untouched: "rqo.absent_untouched rqo_unit = {4}"
proof -
  have "evs_for 4 (sc.win (u_lo rqo_unit) (u_hi rqo_unit)) = []"
    unfolding sc.win_def by (simp add: rqo_unit_def den_w_def L_s_def evs_for_def)
  then show ?thesis by (auto simp: rqo.absent_untouched_def rqo_unit_def)
qed

lemma rqo_svl_ok2: "rqo.svl_ok2 (\<lambda>_. [4])"
proof -
  have "rqo.survivors rqo_unit = {}" by (auto simp: rqo.survivors_def rqo_unit_def)
  then show ?thesis using rqo_absent_untouched by (simp add: rqo.svl_ok2_def)
qed

lemma orph_s0lo_den: "\<And>u. u \<in> set [orph_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
  by (simp add: orph_unit_def den_w_def)

text \<open>
  The two streams, computed. Before the chunk closes, the request's absent
  entry for key 4 precedes the log event at position 1 and the chunk's close
  entry for key 3. After the chunk closes, it comes last, and the stream is
  exactly the sequential composition of @{text Orphan_Absence_Composition}.
\<close>

lemma wit_stream_before_close:
  "pwb.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0
     = [Event 3 (Some 7), Event 4 None, Event 1 (Some 1), Event 3 (Some 7)]"
  unfolding pwb.inter_def pwb.inter_t_def orph.closes_at_def rqb.closes_at_def
            orph.close_block_def rqb.close_block_def
  by (simp add: orph_unit_def rqb_unit_def den_w_def L_s_def upt_rec)

lemma wit_stream_after_close:
  "pwa.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0
     = [Event 3 (Some 7), Event 1 (Some 1), Event 3 (Some 7), Event 4 None]"
  unfolding pwa.inter_def pwa.inter_t_def orph.closes_at_def rq.closes_at_def
            orph.close_block_def rq.close_block_def
  by (simp add: orph_unit_def rq_unit_def den_w_def L_s_def upt_rec)

lemma wit_after_close_is_composition:
  "pwa.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0 = pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0"
proof -
  have "pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0
          = [Event 3 (Some 7), Event 1 (Some 1), Event 3 (Some 7), Event 4 None]"
    unfolding pr.composed_def orph.emission_def rq.emission_def
              orph.emission_t_def rq.emission_t_def orph.closes_at_def rq.closes_at_def
              orph.close_block_def rq.close_block_def
    by (simp add: orph_unit_def rq_unit_def den_w_def L_s_def upt_rec)
  then show ?thesis using wit_stream_after_close by simp
qed

text \<open>A request that closes before the chunk does removes the orphan.\<close>

lemma wit_request_before_close:
  "state_after D0_o (pwb.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) 4 = None"
proof -
  have s0lo2: "\<And>u. u \<in> set [rqb_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: rqb_unit_def den_w_def)
  have conv: "\<forall>k \<in> {3, 4} \<union> {4}.
      state_after D0_o (pwb.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) k = state_after s0_w (sc.pfx 2) k"
  proof (rule pwb.pass_with_request_converges[OF orph_svl_ok2_core rqb_svl_ok2 orph_s0lo_den s0lo2])
    fix k :: nat
    assume "k \<in> {3, 4} \<union> {4}" and "D0_o k \<noteq> None"
    then have k4: "k = 4" by (auto simp: D0_o_def)
    show "(k \<in> {3, 4} \<and> k \<in> set ((\<lambda>_. [3]) (orph.the_unit k))) \<or>
          (k \<in> {4} \<and> k \<in> set ((\<lambda>_. [4]) (rqb.the_unit k)))"
      using k4 by simp
  qed
  then show ?thesis using src_4_none by simp
qed

text \<open>
  A request that closes after the chunk, through the request corollary: the
  request asks for key 4, read at coordinate 2, and the pass leaves no other
  key wrong, because it lists key 3.
\<close>

lemma wit_request_after_close:
  "state_after D0_o (pwa.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) 4 = None"
proof -
  have s0lo2: "\<And>u. u \<in> set [rq_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: rq_unit_def den_w_def)
  have lists: "\<And>u. u \<in> set [rq_unit] \<Longrightarrow> rq.absent_untouched u \<subseteq> set ((\<lambda>_. [4]) u)"
    using rq_absent_untouched by simp
  have s0_rc: "\<And>k. k \<in> {4::nat} \<Longrightarrow> den_w 0 \<le> den_w ((\<lambda>_. 2::nat) k)"
    by (simp add: den_w_def)
  have rc_f1: "\<And>k. k \<in> {4::nat} \<Longrightarrow> den_w ((\<lambda>_. 2::nat) k) \<le> den_w 2" by simp
  have sc2_abs: "\<And>k. k \<in> {4::nat} \<Longrightarrow>
                   state_after s0_w (sc.pfx ((\<lambda>_. 2::nat) k)) k = None \<Longrightarrow> k \<in> {4}"
    by simp
  have asked: "\<And>k. k \<in> {3, 4} \<Longrightarrow>
                 state_after D0_o (orph.emission (\<lambda>_. [3]) 0) k \<noteq> orph.sink_at 2 k \<Longrightarrow>
                 k \<in> {4::nat}"
  proof -
    fix k :: nat
    assume k1: "k \<in> {3, 4}"
       and wrong: "state_after D0_o (orph.emission (\<lambda>_. [3]) 0) k \<noteq> orph.sink_at 2 k"
    have "k \<notin> set ((\<lambda>_. [3::nat]) (orph.the_unit k))"
      using pwa.pass_leaves_wrong_iff[OF orph_svl_ok2_core orph_s0lo_den k1] wrong by blast
    then show "k \<in> {4}" using k1 by simp
  qed
  have conv: "\<forall>k \<in> {3, 4} \<union> {4}.
      state_after D0_o (pwa.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) k = state_after s0_w (sc.pfx 2) k"
    by (rule pwa.request_in_pass_converges[OF orph_svl_ok2_core rq_svl_ok2 orph_s0lo_den s0lo2
                                               lists s0_rc rc_f1 sc2_abs asked])
  then show ?thesis using src_4_none by simp
qed

text \<open>A request whose window overlaps the chunk's window removes the orphan too.\<close>

lemma rqo_overlaps_chunk:
  "\<not> (den_w (u_hi rqo_unit) \<le> den_w (u_lo orph_unit)
      \<or> den_w (u_hi orph_unit) \<le> den_w (u_lo rqo_unit))"
  by (simp add: rqo_unit_def orph_unit_def den_w_def)

lemma wit_request_overlapping_chunk:
  "state_after D0_o (pwo.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) 4 = None"
proof -
  have s0lo2: "\<And>u. u \<in> set [rqo_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: rqo_unit_def den_w_def)
  have conv: "\<forall>k \<in> {3, 4} \<union> {4}.
      state_after D0_o (pwo.inter (\<lambda>_. [3]) (\<lambda>_. [4]) 0) k = state_after s0_w (sc.pfx 2) k"
  proof (rule pwo.pass_with_request_converges[OF orph_svl_ok2_core rqo_svl_ok2 orph_s0lo_den s0lo2])
    fix k :: nat
    assume "k \<in> {3, 4} \<union> {4}" and "D0_o k \<noteq> None"
    then have k4: "k = 4" by (auto simp: D0_o_def)
    show "(k \<in> {3, 4} \<and> k \<in> set ((\<lambda>_. [3]) (orph.the_unit k))) \<or>
          (k \<in> {4} \<and> k \<in> set ((\<lambda>_. [4]) (rqo.the_unit k)))"
      using k4 by simp
  qed
  then show ?thesis using src_4_none by simp
qed

end
