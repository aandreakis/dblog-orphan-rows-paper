(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Composition: a full pass followed by a later bracketed read
  (a repair request, or another pass), applied to the same sink in stream
  order, from an arbitrary initial sink state.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core) and
  to Orphan_Absence. Nothing in the archived development is modified.
*)
theory Orphan_Absence_Composition
  imports Orphan_Absence
begin

text \<open>
  A full pass P emits the window-discard stream with enumerated absences from
  its consumption start @{text s0} to its frontier @{text f1}. A later
  bracketed read R, whose consumption starts at @{text f1} and ends at
  @{text f2}, emits its own stream. The sink applies P's stream and then R's,
  in order, from an arbitrary initial state. R is any capture contract over
  the same log, so a key-list request built by @{text absence_assertion_contract}
  is one instance and another pass is another. Results:

  \<^item> Safety: every key of either scope ends at the source state at
    @{text f2}, or it is absent there, neither read listed it, no log event
    from @{text s0} to @{text f2} mentions it, and the sink keeps its initial
    value.
  \<^item> Convergence: under coverage of exactly those keys, the sink ends at the
    source state on both scopes.
  \<^item> A later read that lists every key it reads as absent and untouched
    completes the pass when every key the pass leaves wrong is in its scope,
    and for a request whose scope holds every requested key that is absent
    where the request reads it (each batch at its own coordinate), it
    suffices that every key the pass leaves wrong was requested. The keys the
    pass leaves wrong are exactly the unlisted keys of its scope that the sink
    holds, that are absent at the pass's frontier, and that no log event
    during the pass mentions.
\<close>

subsection \<open>A key outside a contract's scope sees only its own log events\<close>

context capture_contract
begin

lemma titems_closes_at_out:
  assumes svl: "svl_ok2 svl" and k: "k \<notin> scope"
  shows "titems_for k (closes_at svl p) = []"
proof -
  have each: "titems_for k (if den (u_hi (units ! i)) = p
                            then close_block svl (units ! i) else []) = []"
    if i: "i < length units" for i
  proof -
    have ui_in: "units ! i \<in> set units" using i by simp
    have "k \<notin> set (svl (units ! i))"
      using svl2_sub_dom[OF svl ui_in] dom_sub_scope[OF ui_in] k by auto
    then show ?thesis
      using titems_close_block2[OF svl ui_in] by (simp add: titems_for_def)
  qed
  have "titems_for k (closes_at svl p) =
          concat (map (\<lambda>i. titems_for k (if den (u_hi (units ! i)) = p
                                          then close_block svl (units ! i) else []))
                      [0..<length units])"
    unfolding closes_at_def titems_for_def
    by (simp add: filter_concat_map comp_def if_distrib cong: if_cong)
  also have "\<dots> = []"
    using each by (simp add: concat_eq_Nil_conv)
  finally show ?thesis .
qed

lemma titems_emission_out:
  assumes svl: "svl_ok2 svl" and k: "k \<notin> scope"
  shows "titems_for k (emission_t svl s0) =
           map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den f))"
proof -
  have "titems_for k (emission_t svl s0) =
        concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
        @ titems_for k (closes_at svl (den f))"
    unfolding emission_t_def titems_for_def
    by (simp add: filter_concat_map comp_def cong: map_cong if_cong)
  also have "\<dots> = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                            [den s0..<den f])"
    using titems_closes_at_out[OF svl k] by simp
  also have "\<dots> = map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den f))"
    by (simp add: concat_if_map_filter kposs_def)
  finally show ?thesis .
qed

lemma emission_out_of_scope:
  assumes svl: "svl_ok2 svl" and s0f: "s0 \<sqsubseteq> f" and k: "k \<notin> scope"
  shows "evs_for k (emission svl s0) = evs_for k (win s0 f)"
  unfolding emission_def evs_for_map_snd
  using titems_emission_out[OF svl k] evs_for_win_kposs[OF s0f]
  by (simp add: comp_def)

lemma emission_out_of_scope_replay:
  assumes svl: "svl_ok2 svl" and s0f: "s0 \<sqsubseteq> f" and k: "k \<notin> scope"
  shows "state_after D (emission svl s0) k = state_after D (win s0 f) k"
  by (rule replay_per_key[OF emission_out_of_scope[OF svl s0f k]])

end  (* context capture_contract *)

subsection \<open>Two reads over one log, applied in stream order\<close>

locale pass_then_read =
  P: capture_contract L den \<sigma>0 U1 sc1 f1 +
  R: capture_contract L den \<sigma>0 U2 sc2 f2
  for L :: "('k, 'v) event list" and den :: "'c \<Rightarrow> nat"
  and \<sigma>0 :: "('k, 'v) state"
  and U1 :: "('k, 'v, 'c) cunit list" and sc1 :: "'k set" and f1 :: 'c
  and U2 :: "('k, 'v, 'c) cunit list" and sc2 :: "'k set" and f2 :: 'c +
  assumes f1_le_f2: "den f1 \<le> den f2"
      and f1_le_lo2: "\<And>u. u \<in> set U2 \<Longrightarrow> den f1 \<le> den (u_lo u)"
begin

definition composed ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c
       \<Rightarrow> ('k, 'v) event list" where
  "composed svl1 svl2 s0 = P.emission svl1 s0 @ R.emission svl2 f1"

lemma src_quiet_mid:
  assumes "evs_for k (P.win f1 f2) = []"
  shows "state_after \<sigma>0 (P.pfx f2) k = state_after \<sigma>0 (P.pfx f1) k"
proof -
  have f1_f2: "P.cle f1 f2" using f1_le_f2 by (simp add: P.cle_def)
  show ?thesis
    by (rule P.win_invariant_state[OF f1_f2 P.cle_refl assms])
qed

lemma win_last_src:
  assumes ab: "den a \<le> den b" and ne: "evs_for k (P.win a b) \<noteq> []"
  shows "state_after X (P.win a b) k = state_after \<sigma>0 (P.pfx b) k"
proof -
  have le: "P.cle a b" using ab by (simp add: P.cle_def)
  have split: "evs_for k (P.pfx b) = evs_for k (P.pfx a) @ evs_for k (P.win a b)"
    by (rule P.evs_for_pfx_split[OF le])
  have pne: "evs_for k (P.pfx b) \<noteq> []" using split ne by auto
  have "state_after X (P.win a b) k = ev_img (last (evs_for k (P.win a b)))"
    by (rule state_after_last_event[OF ne])
  also have "\<dots> = ev_img (last (evs_for k (P.pfx b)))"
    using split ne by (simp add: last_append)
  also have "\<dots> = state_after \<sigma>0 (P.pfx b) k"
    by (rule state_after_last_event[OF pne, symmetric])
  finally show ?thesis .
qed

theorem pass_then_read_safe:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0f1: "den s0 \<le> den f1"
      and k: "k \<in> sc1 \<union> sc2"
  shows "state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k
         \<or> (state_after D0 (composed svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f2) = [])"
proof -
  define D1 where "D1 = state_after D0 (P.emission svl1 s0)"
  have final: "state_after D0 (composed svl1 svl2 s0) k
                 = state_after D1 (R.emission svl2 f1) k"
    by (simp add: composed_def state_after_append D1_def)
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  have R_s0lo: "\<And>u. u \<in> set U2 \<Longrightarrow> P.cle f1 (u_lo u)"
    using f1_le_lo2 by (simp add: P.cle_def)
  have s0_f1: "P.cle s0 f1" using s0f1 by (simp add: P.cle_def)
  have f1_f2: "P.cle f1 f2" using f1_le_f2 by (simp add: P.cle_def)
  have win_split: "evs_for k (P.win s0 f2)
                     = evs_for k (P.win s0 f1) @ evs_for k (P.win f1 f2)"
    by (rule P.evs_for_win_split[OF s0_f1 f1_f2])
  show ?thesis
  proof (cases "k \<in> sc2")
    case k2: True
    have R_disj: "state_after D1 (R.emission svl2 f1) k = R.sink_at f2 k
         \<or> (state_after D1 (R.emission svl2 f1) k = D1 k
            \<and> R.sink_at f2 k = None
            \<and> k \<in> R.absent_untouched (R.the_unit k)
            \<and> k \<notin> set (svl2 (R.the_unit k))
            \<and> evs_for k (P.win f1 f2) = [])"
      by (rule R.absent_replay_safe[OF svl2 R_s0lo k2])
    have R_cut: "R.sink_at f2 k = state_after \<sigma>0 (P.pfx f2) k"
      by (rule R.contract_cut[OF k2])
    from R_disj show ?thesis
    proof
      assume "state_after D1 (R.emission svl2 f1) k = R.sink_at f2 k"
      then show ?thesis using final R_cut by simp
    next
      assume Ro: "state_after D1 (R.emission svl2 f1) k = D1 k
            \<and> R.sink_at f2 k = None
            \<and> k \<in> R.absent_untouched (R.the_unit k)
            \<and> k \<notin> set (svl2 (R.the_unit k))
            \<and> evs_for k (P.win f1 f2) = []"
      have fin_D1: "state_after D0 (composed svl1 svl2 s0) k = D1 k"
        using final Ro by simp
      have src_none: "state_after \<sigma>0 (P.pfx f2) k = None"
        using R_cut Ro by simp
      have nl2: "k \<notin> set (svl2 (R.the_unit k))"
        using Ro by simp
      have mid_q: "evs_for k (P.win f1 f2) = []"
        using Ro by simp
      have src_mid: "state_after \<sigma>0 (P.pfx f2) k = state_after \<sigma>0 (P.pfx f1) k"
        by (rule src_quiet_mid[OF mid_q])
      show ?thesis
      proof (cases "k \<in> sc1")
        case k1: True
        have P_disj: "state_after D0 (P.emission svl1 s0) k = P.sink_at f1 k
           \<or> (state_after D0 (P.emission svl1 s0) k = D0 k
              \<and> P.sink_at f1 k = None
              \<and> k \<in> P.absent_untouched (P.the_unit k)
              \<and> k \<notin> set (svl1 (P.the_unit k))
              \<and> evs_for k (P.win s0 f1) = [])"
          by (rule P.absent_replay_safe[OF svl1 P_s0lo k1])
        have P_cut: "P.sink_at f1 k = state_after \<sigma>0 (P.pfx f1) k"
          by (rule P.contract_cut[OF k1])
        from P_disj show ?thesis
        proof
          assume "state_after D0 (P.emission svl1 s0) k = P.sink_at f1 k"
          then have "D1 k = state_after \<sigma>0 (P.pfx f2) k"
            using P_cut src_mid by (simp add: D1_def)
          then show ?thesis using fin_D1 by simp
        next
          assume Po: "state_after D0 (P.emission svl1 s0) k = D0 k
              \<and> P.sink_at f1 k = None
              \<and> k \<in> P.absent_untouched (P.the_unit k)
              \<and> k \<notin> set (svl1 (P.the_unit k))
              \<and> evs_for k (P.win s0 f1) = []"
          have quiet: "evs_for k (P.win s0 f2) = []"
            using win_split Po mid_q by simp
          have "D1 k = D0 k"
            using Po by (simp add: D1_def)
          then show ?thesis
            using Po fin_D1 src_none nl2 quiet by simp
        qed
      next
        case k1: False
        have D1_out: "D1 k = state_after D0 (P.win s0 f1) k"
          unfolding D1_def by (rule P.emission_out_of_scope_replay[OF svl1 s0_f1 k1])
        show ?thesis
        proof (cases "evs_for k (P.win s0 f1) = []")
          case True
          have "D1 k = D0 k"
            using D1_out True by (simp add: state_after_no_events)
          moreover have "evs_for k (P.win s0 f2) = []"
            using win_split True mid_q by simp
          ultimately show ?thesis
            using fin_D1 src_none nl2 k1 by simp
        next
          case False
          have "D1 k = state_after \<sigma>0 (P.pfx f1) k"
            using D1_out win_last_src[OF s0f1 False] by simp
          then show ?thesis
            using fin_D1 src_mid by simp
        qed
      qed
    qed
  next
    case k2: False
    then have k1: "k \<in> sc1" using k by simp
    have fin_win: "state_after D0 (composed svl1 svl2 s0) k = state_after D1 (P.win f1 f2) k"
      using final R.emission_out_of_scope_replay[OF svl2 f1_f2 k2] by simp
    have P_disj: "state_after D0 (P.emission svl1 s0) k = P.sink_at f1 k
       \<or> (state_after D0 (P.emission svl1 s0) k = D0 k
          \<and> P.sink_at f1 k = None
          \<and> k \<in> P.absent_untouched (P.the_unit k)
          \<and> k \<notin> set (svl1 (P.the_unit k))
          \<and> evs_for k (P.win s0 f1) = [])"
      by (rule P.absent_replay_safe[OF svl1 P_s0lo k1])
    have P_cut: "P.sink_at f1 k = state_after \<sigma>0 (P.pfx f1) k"
      by (rule P.contract_cut[OF k1])
    show ?thesis
    proof (cases "evs_for k (P.win f1 f2) = []")
      case mid_ne: False
      have "state_after D1 (P.win f1 f2) k = state_after \<sigma>0 (P.pfx f2) k"
        by (rule win_last_src[OF f1_le_f2 mid_ne])
      then show ?thesis using fin_win by simp
    next
      case mid_q: True
      have fin_D1: "state_after D0 (composed svl1 svl2 s0) k = D1 k"
        using fin_win mid_q by (simp add: state_after_no_events)
      have src_mid: "state_after \<sigma>0 (P.pfx f2) k = state_after \<sigma>0 (P.pfx f1) k"
        by (rule src_quiet_mid[OF mid_q])
      from P_disj show ?thesis
      proof
        assume "state_after D0 (P.emission svl1 s0) k = P.sink_at f1 k"
        then have "D1 k = state_after \<sigma>0 (P.pfx f2) k"
          using P_cut src_mid by (simp add: D1_def)
        then show ?thesis using fin_D1 by simp
      next
        assume Po: "state_after D0 (P.emission svl1 s0) k = D0 k
            \<and> P.sink_at f1 k = None
            \<and> k \<in> P.absent_untouched (P.the_unit k)
            \<and> k \<notin> set (svl1 (P.the_unit k))
            \<and> evs_for k (P.win s0 f1) = []"
        have quiet: "evs_for k (P.win s0 f2) = []"
          using win_split Po mid_q by simp
        have src_none: "state_after \<sigma>0 (P.pfx f2) k = None"
          using src_mid P_cut Po by simp
        have "D1 k = D0 k"
          using Po by (simp add: D1_def)
        then show ?thesis
          using Po fin_D1 k2 quiet src_none by simp
      qed
    qed
  qed
qed

theorem pass_then_read_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0f1: "den s0 \<le> den f1"
      and cover: "\<And>k. k \<in> sc1 \<union> sc2 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow>
                    state_after \<sigma>0 (P.pfx f2) k = None \<Longrightarrow>
                    evs_for k (P.win s0 f2) = [] \<Longrightarrow>
                    (k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
                    (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k"
proof
  fix k assume k: "k \<in> sc1 \<union> sc2"
  have disj: "state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k
         \<or> (state_after D0 (composed svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f2) = [])"
    by (rule pass_then_read_safe[OF svl1 svl2 s0lo s0f1 k])
  from disj show "state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k"
  proof
    assume "state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k"
    then show ?thesis .
  next
    assume o: "state_after D0 (composed svl1 svl2 s0) k = D0 k
            \<and> state_after \<sigma>0 (P.pfx f2) k = None
            \<and> (k \<in> sc1 \<longrightarrow> k \<notin> set (svl1 (P.the_unit k)))
            \<and> (k \<in> sc2 \<longrightarrow> k \<notin> set (svl2 (R.the_unit k)))
            \<and> evs_for k (P.win s0 f2) = []"
    show ?thesis
    proof (cases "D0 k = None")
      case True
      then show ?thesis using o by simp
    next
      case False
      have src_none: "state_after \<sigma>0 (P.pfx f2) k = None" using o by simp
      have quiet: "evs_for k (P.win s0 f2) = []" using o by simp
      have "(k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
            (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
        by (rule cover[OF k False src_none quiet])
      then show ?thesis using o by auto
    qed
  qed
qed

subsection \<open>A later read that lists its absent keys completes the pass\<close>

corollary pass_then_request_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0f1: "den s0 \<le> den f1"
      and lists_absent: "\<And>u. u \<in> set U2 \<Longrightarrow> R.absent_untouched u \<subseteq> set (svl2 u)"
      and in_scope: "\<And>k. k \<in> sc1 \<Longrightarrow> D0 k \<noteq> None \<Longrightarrow> P.sink_at f1 k = None \<Longrightarrow>
                       k \<notin> set (svl1 (P.the_unit k)) \<Longrightarrow>
                       evs_for k (P.win s0 f2) = [] \<Longrightarrow> k \<in> sc2"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k"
proof (rule pass_then_read_converges[OF svl1 svl2 s0lo s0f1])
  fix k
  assume k: "k \<in> sc1 \<union> sc2" and held: "D0 k \<noteq> None"
     and src_none: "state_after \<sigma>0 (P.pfx f2) k = None"
     and quiet: "evs_for k (P.win s0 f2) = []"
  have s0_f1: "P.cle s0 f1" using s0f1 by (simp add: P.cle_def)
  have f1_f2: "P.cle f1 f2" using f1_le_f2 by (simp add: P.cle_def)
  have mid_q: "evs_for k (P.win f1 f2) = []"
    using P.evs_for_win_split[OF s0_f1 f1_f2] quiet by simp
  have src_f1: "state_after \<sigma>0 (P.pfx f1) k = None"
    using src_quiet_mid[OF mid_q] src_none by simp
  show "(k \<in> sc1 \<and> k \<in> set (svl1 (P.the_unit k))) \<or>
        (k \<in> sc2 \<and> k \<in> set (svl2 (R.the_unit k)))"
  proof (cases "k \<in> sc2")
    case k2: True
    define u where "u = R.the_unit k"
    have u_in: "u \<in> set U2" and k_dom: "k \<in> u_dom u"
      using R.the_unit_props[OF k2] u_def by auto
    have lo_hi: "P.cle (u_lo u) (u_hi u)" by (rule R.bracket_lo_hi[OF u_in])
    have hi_f2: "P.cle (u_hi u) f2" by (rule R.bracket_hi_f[OF u_in])
    have f1_lo: "P.cle f1 (u_lo u)" using f1_le_lo2[OF u_in] by (simp add: P.cle_def)
    have lo_f2: "P.cle (u_lo u) f2" using lo_hi hi_f2 by (rule P.cle_trans)
    have lo_f2_q: "evs_for k (P.win (u_lo u) f2) = []"
      using P.evs_for_win_split[OF f1_lo lo_f2] mid_q by simp
    have win_q: "evs_for k (P.win (u_lo u) (u_hi u)) = []"
      using P.evs_for_win_split[OF lo_hi hi_f2] lo_f2_q by simp
    obtain c where c_lo: "P.cle (u_lo u) c" and c_hi: "P.cle c (u_hi u)"
      and honest: "u_refresh u k = state_after \<sigma>0 (P.pfx c) k"
      using R.O2_honest[OF u_in k_dom] by blast
    have c_f2: "P.cle c f2" using c_hi hi_f2 by (rule P.cle_trans)
    have "state_after \<sigma>0 (P.pfx c) k = state_after \<sigma>0 (P.pfx (u_lo u)) k"
      by (rule P.win_invariant_state[OF c_lo c_f2 lo_f2_q])
    also have "\<dots> = state_after \<sigma>0 (P.pfx f2) k"
      by (rule P.win_invariant_state[OF lo_f2 P.cle_refl lo_f2_q, symmetric])
    finally have "u_refresh u k = None" using honest src_none by simp
    then have "k \<in> R.absent_untouched u"
      using k_dom win_q by (simp add: R.absent_untouched_def)
    then have "k \<in> set (svl2 u)" using lists_absent[OF u_in] by auto
    then show ?thesis using k2 u_def by simp
  next
    case k2: False
    then have k1: "k \<in> sc1" using k by simp
    have sink_none: "P.sink_at f1 k = None"
      using P.contract_cut[OF k1] src_f1 by simp
    have "k \<in> set (svl1 (P.the_unit k))"
      using in_scope[OF k1 held sink_none] quiet k2 by blast
    then show ?thesis using k1 by simp
  qed
qed

text \<open>
  The keys a pass leaves wrong are exactly the unlisted keys of its scope that
  the sink holds, that are absent at the frontier, and that no log event during
  the pass mentions.
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
  For a key-list request, the later read's scope holds every requested key
  that is absent at the coordinate @{text "rc k"} where the request reads it
  (the domain of @{text absence_assertion_contract}). A request that runs in
  batches reads each batch at its own coordinate, so the coordinate is given
  per key. Then it suffices that every key the pass leaves wrong was
  requested.
\<close>

corollary request_after_pass_converges:
  assumes svl1: "P.svl_ok2 svl1" and svl2: "R.svl_ok2 svl2"
      and s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> den s0 \<le> den (u_lo u)"
      and s0f1: "den s0 \<le> den f1"
      and lists_absent: "\<And>u. u \<in> set U2 \<Longrightarrow> R.absent_untouched u \<subseteq> set (svl2 u)"
      and f1_rc: "\<And>k. k \<in> K \<Longrightarrow> den f1 \<le> den (rc k)"
      and rc_f2: "\<And>k. k \<in> K \<Longrightarrow> den (rc k) \<le> den f2"
      and sc2_abs: "\<And>k. k \<in> K \<Longrightarrow> state_after \<sigma>0 (P.pfx (rc k)) k = None \<Longrightarrow> k \<in> sc2"
      and asked: "\<And>k. k \<in> sc1 \<Longrightarrow>
                    state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k \<Longrightarrow> k \<in> K"
  shows "\<forall>k \<in> sc1 \<union> sc2.
           state_after D0 (composed svl1 svl2 s0) k = state_after \<sigma>0 (P.pfx f2) k"
proof (rule pass_then_request_converges[OF svl1 svl2 s0lo s0f1 lists_absent])
  fix k
  assume k1: "k \<in> sc1" and held: "D0 k \<noteq> None" and sink_none: "P.sink_at f1 k = None"
     and nl: "k \<notin> set (svl1 (P.the_unit k))" and quiet: "evs_for k (P.win s0 f2) = []"
  have P_s0lo: "\<And>u. u \<in> set U1 \<Longrightarrow> P.cle s0 (u_lo u)"
    using s0lo by (simp add: P.cle_def)
  have s0_f1: "P.cle s0 f1" using s0f1 by (simp add: P.cle_def)
  have f1_f2: "P.cle f1 f2" using f1_le_f2 by (simp add: P.cle_def)
  have pass_q: "evs_for k (P.win s0 f1) = []"
    using P.evs_for_win_split[OF s0_f1 f1_f2] quiet by simp
  have mid_q: "evs_for k (P.win f1 f2) = []"
    using P.evs_for_win_split[OF s0_f1 f1_f2] quiet by simp
  have kept: "state_after D0 (P.emission svl1 s0) k = D0 k"
    by (rule P.unlisted_quiet_key_kept[OF svl1 P_s0lo k1 nl pass_q])
  have wrong: "state_after D0 (P.emission svl1 s0) k \<noteq> P.sink_at f1 k"
    using kept held sink_none by simp
  have kK: "k \<in> K" by (rule asked[OF k1 wrong])
  have f1rc: "P.cle f1 (rc k)" using f1_rc[OF kK] by (simp add: P.cle_def)
  have rcf2: "P.cle (rc k) f2" using rc_f2[OF kK] by (simp add: P.cle_def)
  have "state_after \<sigma>0 (P.pfx (rc k)) k = state_after \<sigma>0 (P.pfx f1) k"
    by (rule P.win_invariant_state[OF f1rc rcf2 mid_q])
  also have "\<dots> = None"
    using P.contract_cut[OF k1] sink_none by simp
  finally have "state_after \<sigma>0 (P.pfx (rc k)) k = None" .
  then show "k \<in> sc2" by (rule sc2_abs[OF kK])
qed

end  (* locale pass_then_read *)

subsection \<open>Fixture: a request completes a pass that left an orphan\<close>

text \<open>
  The pass of the orphan fixture of @{text Orphan_Absence}, run with the
  core's survivor-only enumeration, leaves the orphan key 4 in the sink. A
  later request for key 4, read at coordinate 2 where key 4 is absent, is the
  one-unit contract of @{text absence_assertion_contract}, and the composed
  stream removes the orphan.
\<close>

definition rq_unit :: "(nat, nat, nat) cunit" where
  "rq_unit = \<lparr>u_dom = {4}, u_lo = 2, u_hi = 2, u_refresh = (\<lambda>_. None)\<rparr>"

lemma rq_contract: "capture_contract L_s den_w s0_w [rq_unit] {4} 2"
proof -
  have empty: "\<And>k. k \<in> {4} \<Longrightarrow> state_after s0_w (sc.pfx 2) k = None"
    unfolding sc.pfx_def
    by (auto simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  show ?thesis
    unfolding rq_unit_def
    by (rule sc.absence_assertion_contract[where c = 2, OF _ _ _ empty])
       (simp_all add: sc.cle_def den_w_def)
qed

interpretation rq: capture_contract L_s den_w s0_w "[rq_unit]" "{4}" 2
  by (rule rq_contract)

interpretation pr: pass_then_read L_s den_w s0_w "[orph_unit]" "{3, 4}" 2 "[rq_unit]" "{4}" 2
  by unfold_locales (simp_all add: den_w_def rq_unit_def)

lemma rq_win_4: "evs_for 4 (sc.win (u_lo rq_unit) (u_hi rq_unit)) = []"
  unfolding sc.win_def by (simp add: rq_unit_def den_w_def L_s_def evs_for_def)

lemma rq_survivors: "rq.survivors rq_unit = {}"
  by (auto simp: rq.survivors_def rq_unit_def)

lemma rq_absent_untouched: "rq.absent_untouched rq_unit = {4}"
  using rq_win_4 by (auto simp: rq.absent_untouched_def rq_unit_def)

lemma rq_svl_ok2: "rq.svl_ok2 (\<lambda>_. [4])"
  using rq_survivors rq_absent_untouched by (simp add: rq.svl_ok2_def)

lemma wit_request_completes_pass:
  "state_after D0_o (pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0) 4 = None"
proof -
  have s0lo: "\<And>u. u \<in> set [orph_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: orph_unit_def den_w_def)
  have s0f1: "den_w 0 \<le> den_w 2" by (simp add: den_w_def)
  have conv: "\<forall>k \<in> {3, 4} \<union> {4}.
      state_after D0_o (pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0) k = state_after s0_w (sc.pfx 2) k"
  proof (rule pr.pass_then_read_converges[OF orph_svl_ok2_core rq_svl_ok2 s0lo s0f1])
    fix k :: nat
    assume "k \<in> {3, 4} \<union> {4}" and "D0_o k \<noteq> None"
    then have k4: "k = 4" by (auto simp: D0_o_def)
    show "(k \<in> {3, 4} \<and> k \<in> set ((\<lambda>_. [3]) (orph.the_unit k))) \<or>
          (k \<in> {4} \<and> k \<in> set ((\<lambda>_. [4]) (rq.the_unit k)))"
      using k4 by simp
  qed
  have "state_after s0_w (sc.pfx 2) 4 = None"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  then show ?thesis using conv by simp
qed

text \<open>
  The same result through the request corollary: the request asks for key 4,
  read at coordinate 2, and the pass leaves no other key wrong, because it
  lists key 3.
\<close>

lemma wit_request_after_pass:
  "state_after D0_o (pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0) 4 = None"
proof -
  have s0lo: "\<And>u. u \<in> set [orph_unit] \<Longrightarrow> den_w 0 \<le> den_w (u_lo u)"
    by (simp add: orph_unit_def den_w_def)
  have s0f1: "den_w 0 \<le> den_w 2" by (simp add: den_w_def)
  have lists: "\<And>u. u \<in> set [rq_unit] \<Longrightarrow> rq.absent_untouched u \<subseteq> set ((\<lambda>_. [4]) u)"
    using rq_absent_untouched by simp
  have f1_rc: "\<And>k. k \<in> {4::nat} \<Longrightarrow> den_w 2 \<le> den_w ((\<lambda>_. 2::nat) k)" by simp
  have rc_f2: "\<And>k. k \<in> {4::nat} \<Longrightarrow> den_w ((\<lambda>_. 2::nat) k) \<le> den_w 2" by simp
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
      using pr.pass_leaves_wrong_iff[OF orph_svl_ok2_core s0lo k1] wrong by blast
    then show "k \<in> {4}" using k1 by simp
  qed
  have conv: "\<forall>k \<in> {3, 4} \<union> {4}.
      state_after D0_o (pr.composed (\<lambda>_. [3]) (\<lambda>_. [4]) 0) k = state_after s0_w (sc.pfx 2) k"
    by (rule pr.request_after_pass_converges[OF orph_svl_ok2_core rq_svl_ok2 s0lo s0f1 lists
                                               f1_rc rc_f2 sc2_abs asked])
  have "state_after s0_w (sc.pfx 2) 4 = None"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  then show ?thesis using conv by simp
qed

end
