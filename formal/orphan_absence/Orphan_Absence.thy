(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence: window-discard emission with enumerated absence entries,
  replayed from an arbitrary initial sink state.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core).
  Nothing in the archived development is modified.
*)
theory Orphan_Absence
  imports DBLog_Framework_Core.Merge_Disciplines DBLog_Framework_Core.Contract_Witnesses
begin

text \<open>
  The window-discard discipline emits, at a unit's high edge, one entry
  @{text "Event k (u_refresh u k)"} per enumerated key. The archived
  development enumerates exactly the survivors: keys read as PRESENT and
  untouched inside the bracket. Absence is then represented by omission,
  which is sound only for a replay that starts from the empty state.

  This theory widens the enumeration. A key read as ABSENT and untouched
  inside the bracket may also be listed; its entry is @{text "Event k None"},
  an explicit absence (the ``absent event'' or, expanded at the sink, the
  ``range record''). The replay is then taken from an ARBITRARY initial sink
  state @{text D0}. Results:

  \<^item> Safety for every enumeration inside the admissible set: each scoped
    key either agrees with the canonical replay at the frontier, or it is
    an untouched key read as absent, not enumerated, with no consumed event,
    whose sink value is simply left as it was (a surviving orphan). No
    other outcome exists: no wrong value, no deleted live row.
  \<^item> Convergence (self-stabilization): when the enumeration covers every
    absent untouched key that the sink holds, the replay from @{text D0}
    equals the source state at the frontier on the whole scope.
  \<^item> Existence: for a finite sink and finitely many survivors per unit,
    a covering enumeration exists (the sink-expanded range record).

  The enumeration is a parameter. Choosing the sink's own keys in the unit's
  domain gives the range record applied at the sink; choosing the keys a
  connector read from the sink gives the connector-side absent events;
  choosing all gap keys of a dense key type gives dense enumeration. Late
  emission is the same statement for a unit whose high edge is the later
  emission coordinate, since O2 lets the read coordinate sit anywhere inside
  the bracket.
\<close>

subsection \<open>Replay depends on a key's own events only\<close>

text \<open>
  Per-key transport neutrality in one line: two emitted streams with the same
  events for @{text k} replay to the same value at @{text k}, from any
  initial state. A keyed absent event therefore needs only per-key order.
\<close>

lemma replay_per_key:
  "evs_for k S' = evs_for k S \<Longrightarrow> state_after D0 S' k = state_after D0 S k"
  by (simp add: state_after_key)

context capture_contract
begin

subsection \<open>Admissible enumerations\<close>

definition absent_untouched :: "('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "absent_untouched u =
     {k \<in> u_dom u. u_refresh u k = None \<and>
                    evs_for k (win (u_lo u) (u_hi u)) = []}"

definition svl_ok2 :: "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> bool" where
  "svl_ok2 svl \<longleftrightarrow>
     (\<forall>u \<in> set units. distinct (svl u) \<and>
                        survivors u \<subseteq> set (svl u) \<and>
                        set (svl u) \<subseteq> survivors u \<union> absent_untouched u)"

lemma svl_ok_imp_ok2: "svl_ok svl \<Longrightarrow> svl_ok2 svl"
  by (auto simp: svl_ok_def svl_ok2_def)

lemma absent_untouched_sub_dom: "absent_untouched u \<subseteq> u_dom u"
  by (auto simp: absent_untouched_def)

lemma svl2_distinct: "svl_ok2 svl \<Longrightarrow> u \<in> set units \<Longrightarrow> distinct (svl u)"
  by (simp add: svl_ok2_def)

lemma svl2_sub_dom:
  assumes "svl_ok2 svl" and "u \<in> set units"
  shows "set (svl u) \<subseteq> u_dom u"
proof -
  have "set (svl u) \<subseteq> survivors u \<union> absent_untouched u"
    using assms by (simp add: svl_ok2_def)
  then show ?thesis
    using survivors_sub_dom absent_untouched_sub_dom by blast
qed

lemma svl2_untouched:
  assumes "svl_ok2 svl" and "u \<in> set units" and "k \<in> set (svl u)"
  shows "evs_for k (win (u_lo u) (u_hi u)) = []"
proof -
  have "k \<in> survivors u \<union> absent_untouched u"
    using assms by (auto simp: svl_ok2_def)
  then show ?thesis
    by (auto simp: survivors_def absent_untouched_def)
qed

lemma svl2_surv:
  "svl_ok2 svl \<Longrightarrow> u \<in> set units \<Longrightarrow> k \<in> survivors u \<Longrightarrow> k \<in> set (svl u)"
  by (auto simp: svl_ok2_def)

subsection \<open>Per-key characterization of the widened emission\<close>

lemma titems_close_block2:
  assumes svl: "svl_ok2 svl" and u_in: "u \<in> set units"
  shows "titems_for k (close_block svl u) =
           (if k \<in> set (svl u)
            then [(den (u_hi u), Event k (u_refresh u k))] else [])"
proof -
  have dis: "distinct (svl u)"
    using svl2_distinct[OF svl u_in] .
  have "titems_for k (close_block svl u) =
          map (\<lambda>k'. (den (u_hi u), Event k' (u_refresh u k')))
              (filter (\<lambda>k'. k' = k) (svl u))"
    by (simp add: titems_for_def close_block_def filter_map comp_def)
  then show ?thesis
    using distinct_filter_eq[OF dis] by simp
qed

lemma titems_closes_at2:
  assumes svl: "svl_ok2 svl" and k: "k \<in> scope"
  shows "titems_for k (closes_at svl p) =
           (if den (u_hi (the_unit k)) = p \<and> k \<in> set (svl (the_unit k))
            then [(p, Event k (u_refresh (the_unit k) k))] else [])"
proof -
  obtain i0 where i0: "i0 < length units" "units ! i0 = the_unit k"
    using the_unit_props(1)[OF k] by (meson in_set_conv_nth)
  have others: "titems_for k (if den (u_hi (units ! i)) = p
                              then close_block svl (units ! i) else []) = []"
    if i: "i < length units" and ne: "i \<noteq> i0" for i
  proof -
    have ui_in: "units ! i \<in> set units" using i by simp
    have "k \<notin> set (svl (units ! i))"
    proof
      assume "k \<in> set (svl (units ! i))"
      then have "k \<in> u_dom (units ! i)"
        using svl2_sub_dom[OF svl ui_in] by auto
      then have eq: "units ! i = the_unit k"
        using covering_unit_unique[OF ui_in _ the_unit_props(1)[OF k]
                                       the_unit_props(2)[OF k]] by blast
      have "i = i0"
        by (rule the_unit_position_unique[OF k i eq i0(1) i0(2)])
      with ne show False ..
    qed
    then show ?thesis
      using titems_close_block2[OF svl ui_in]
      by (simp add: titems_for_def)
  qed
  have "titems_for k (closes_at svl p) =
          concat (map (\<lambda>i. titems_for k (if den (u_hi (units ! i)) = p
                                          then close_block svl (units ! i) else []))
                      [0..<length units])"
    unfolding closes_at_def titems_for_def
    by (simp add: filter_concat_map comp_def if_distrib
             cong: if_cong)
  also have "\<dots> = titems_for k (if den (u_hi (units ! i0)) = p
                                 then close_block svl (units ! i0) else [])"
    by (rule concat_map_upt_single[OF others i0(1)])
  finally show ?thesis
    using titems_close_block2[OF svl the_unit_props(1)[OF k]] i0(2)
    by (simp add: titems_for_def)
qed

lemma titems_emission_master2:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
  shows "titems_for k (emission_t svl s0) =
           map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den (u_hi (the_unit k))))
           @ (if k \<in> set (svl (the_unit k))
              then [(den (u_hi (the_unit k)),
                     Event k (u_refresh (the_unit k) k))] else [])
           @ map (\<lambda>p. (Suc p, L ! p)) (kposs k (den (u_hi (the_unit k))) (den f))"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units"
    using the_unit_props(1)[OF k] u_def by simp
  have s0_le_lo: "den s0 \<le> den (u_lo u)"
    using s0lo[OF u_in] by (simp add: cle_def)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using bracket_lo_hi[OF u_in] by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using bracket_hi_f[OF u_in] by (simp add: cle_def hp_def)
  have s0_le_hp: "den s0 \<le> hp"
    using s0_le_lo lo_le_hp by simp

  have closes: "\<And>p. titems_for k (closes_at svl p) =
           (if hp = p \<and> k \<in> set (svl u)
            then [(p, Event k (u_refresh u k))] else [])"
    using titems_closes_at2[OF svl k] by (simp add: u_def hp_def)

  have dist: "titems_for k (emission_t svl s0) =
        concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
        @ titems_for k (closes_at svl (den f))"
    unfolding emission_t_def titems_for_def
    by (simp add: filter_concat_map comp_def cong: map_cong if_cong)

  show ?thesis
  proof (cases "hp < den f")
    case False
    then have hp_f: "hp = den f"
      using hp_le_f by simp
    have no_close: "\<And>p. p \<in> set [den s0..<den f] \<Longrightarrow>
                      titems_for k (closes_at svl p) = []"
      using closes hp_f by auto
    have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
          = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                    [den s0..<den f])"
      using no_close by (intro arg_cong[where f = concat] map_cong) auto
    also have "\<dots> = map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) (den f))"
      by (simp add: concat_if_map_filter kposs_def)
    finally show ?thesis
      using dist closes hp_f
      by (simp add: u_def hp_def kposs_def)
  next
    case True
    have split: "[den s0..<den f] = [den s0..<hp] @ [hp..<den f]"
      using s0_le_hp hp_le_f by (rule upt_split)
    have head: "[hp..<den f] = hp # [Suc hp..<den f]"
      using True by (simp add: upt_rec)
    have pre: "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
          = map (\<lambda>p. (Suc p, L ! p)) (kposs k (den s0) hp)"
    proof -
      have "\<And>p. p \<in> set [den s0..<hp] \<Longrightarrow> titems_for k (closes_at svl p) = []"
        using closes by auto
      then have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
            = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                      [den s0..<hp])"
        by (intro arg_cong[where f = concat] map_cong) auto
      then show ?thesis
        by (simp add: concat_if_map_filter kposs_def)
    qed
    have post: "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
          = map (\<lambda>p. (Suc p, L ! p)) (kposs k (Suc hp) (den f))"
    proof -
      have "\<And>p. p \<in> set [Suc hp..<den f] \<Longrightarrow> titems_for k (closes_at svl p) = []"
        using closes by auto
      then have "concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
            = concat (map (\<lambda>p. if ev_key (L ! p) = k then [(Suc p, L ! p)] else [])
                      [Suc hp..<den f])"
        by (intro arg_cong[where f = concat] map_cong) auto
      then show ?thesis
        by (simp add: concat_if_map_filter kposs_def)
    qed
    have closes_hp: "titems_for k (closes_at svl hp)
          = (if k \<in> set (svl u) then [(hp, Event k (u_refresh u k))] else [])"
      using closes[of hp] by simp
    have trail: "titems_for k (closes_at svl (den f)) = []"
      using closes True by auto
    have kposs_peel: "kposs k hp (den f)
          = (if ev_key (L ! hp) = k then hp # kposs k (Suc hp) (den f)
             else kposs k (Suc hp) (den f))"
      unfolding kposs_def using head by simp
    have peel: "titems_for k (emission_t svl s0)
            = concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
              @ titems_for k (closes_at svl hp)
              @ (if ev_key (L ! hp) = k then [(Suc hp, L ! hp)] else [])
              @ concat (map (\<lambda>p. titems_for k (closes_at svl p)
                          @ (if ev_key (L ! p) = k then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
              @ titems_for k (closes_at svl (den f))"
      unfolding dist by (simp add: split head)
    show ?thesis
      unfolding peel pre post trail closes_hp
      by (simp add: kposs_peel flip: u_def hp_def)
  qed
qed

subsection \<open>Safety: any admissible enumeration, any initial state\<close>

text \<open>
  For every scoped key the replay from an arbitrary initial state @{text D0}
  either equals the canonical replay at the frontier, or the key is an
  absent untouched key that was not enumerated and has no consumed event,
  and the sink keeps whatever it held. Nothing else can happen.
\<close>

theorem absent_replay_safe:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
  shows "state_after D0 (emission svl s0) k = sink_at f k
         \<or> (state_after D0 (emission svl s0) k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> absent_untouched (the_unit k)
            \<and> k \<notin> set (svl (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have s0_lo: "s0 \<sqsubseteq> u_lo u" using s0lo[OF u_in] .
  have s0_f: "s0 \<sqsubseteq> f" using s0_lo lo_f by (rule cle_trans)
  have s0_le_lo: "den s0 \<le> den (u_lo u)"
    using s0_lo by (simp add: cle_def)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)
  have s0_le_hp: "den s0 \<le> hp" using s0_le_lo lo_le_hp by simp

  have master: "evs_for k (emission svl s0) =
          map ((!) L) (kposs k (den s0) hp)
          @ (if k \<in> set (svl u) then [Event k (u_refresh u k)] else [])
          @ map ((!) L) (kposs k hp (den f))"
    unfolding emission_def evs_for_map_snd
    using titems_emission_master2[OF svl s0lo k]
    by (simp add: u_def hp_def comp_def if_distrib map_append
             cong: if_cong)

  have win_lo_hi: "evs_for k (win (u_lo u) (u_hi u))
                     = map ((!) L) (kposs k (den (u_lo u)) hp)"
    using evs_for_win_kposs[OF lo_hi] by (simp add: hp_def)
  have win_lo_f: "evs_for k (win (u_lo u) f)
                     = map ((!) L) (kposs k (den (u_lo u)) (den f))"
    using evs_for_win_kposs[OF lo_f] by simp
  have win_s0_f: "evs_for k (win s0 f)
                     = map ((!) L) (kposs k (den s0) (den f))"
    using evs_for_win_kposs[OF s0_f] by simp
  have kposs_lo_f_split:
      "kposs k (den (u_lo u)) (den f)
         = kposs k (den (u_lo u)) hp @ kposs k hp (den f)"
    using lo_le_hp hp_le_f by (rule kposs_split)
  have kposs_s0_hp_split:
      "kposs k (den s0) hp
         = kposs k (den s0) (den (u_lo u)) @ kposs k (den (u_lo u)) hp"
    using s0_le_lo lo_le_hp by (rule kposs_split)
  have kposs_s0_f_split:
      "kposs k (den s0) (den f)
         = kposs k (den s0) hp @ kposs k hp (den f)"
    using s0_le_hp hp_le_f by (rule kposs_split)

  show ?thesis
  proof (cases "kposs k (den (u_lo u)) (den f) = []")
    case False
    then have sink: "sink_at f k
                       = ev_img (last (map ((!) L) (kposs k (den (u_lo u)) (den f))))"
      by (simp add: sink_at_def win_lo_f flip: u_def)
    have "state_after D0 (emission svl s0) k = sink_at f k"
    proof (cases "kposs k hp (den f) = []")
      case post_ne: False
      have last_sink: "last (kposs k (den (u_lo u)) (den f)) = last (kposs k hp (den f))"
        using kposs_lo_f_split post_ne by (simp add: last_append)
      have stream_ne: "evs_for k (emission svl s0) \<noteq> []"
        using master post_ne by auto
      have last_stream: "last (evs_for k (emission svl s0))
                           = (!) L (last (kposs k hp (den f)))"
        using master post_ne by (simp add: last_append last_map)
      have "state_after D0 (emission svl s0) k
              = ev_img (L ! last (kposs k hp (den f)))"
        using state_after_last_event[OF stream_ne] last_stream by simp
      moreover have "sink_at f k = ev_img (L ! last (kposs k hp (den f)))"
        using sink last_sink False by (simp add: last_map)
      ultimately show ?thesis by simp
    next
      case post_e: True
      have win_ne: "kposs k (den (u_lo u)) hp \<noteq> []"
        using False kposs_lo_f_split post_e by auto
      have not_listed: "k \<notin> set (svl u)"
        using svl2_untouched[OF svl u_in] win_lo_hi win_ne by auto
      have master': "evs_for k (emission svl s0)
                       = map ((!) L) (kposs k (den s0) hp)"
        using master not_listed post_e by simp
      have s0_ne: "kposs k (den s0) hp \<noteq> []"
        using kposs_s0_hp_split win_ne by auto
      have last_pre: "last (kposs k (den s0) hp) = last (kposs k (den (u_lo u)) hp)"
        using kposs_s0_hp_split win_ne by (simp add: last_append)
      have last_sink: "last (kposs k (den (u_lo u)) (den f))
                         = last (kposs k (den (u_lo u)) hp)"
        using kposs_lo_f_split post_e by simp
      have "state_after D0 (emission svl s0) k
              = ev_img (L ! last (kposs k (den (u_lo u)) hp))"
        by (subst state_after_key)
           (simp add: master' s0_ne last_pre last_map)
      moreover have "sink_at f k = ev_img (L ! last (kposs k (den (u_lo u)) hp))"
        using sink last_sink False by (simp add: last_map)
      ultimately show ?thesis by simp
    qed
    then show ?thesis ..
  next
    case True
    have win_e: "kposs k (den (u_lo u)) hp = []"
     and post_e: "kposs k hp (den f) = []"
      using True kposs_lo_f_split by auto
    have no_win_evs: "evs_for k (win (u_lo u) (u_hi u)) = []"
      using win_lo_hi win_e by simp
    have sink: "sink_at f k = u_refresh u k"
      using True by (simp add: sink_at_def win_lo_f flip: u_def)
    have pre_only: "kposs k (den s0) hp = kposs k (den s0) (den (u_lo u))"
      using kposs_s0_hp_split win_e by simp
    show ?thesis
    proof (cases "k \<in> set (svl u)")
      case listed: True
      have "evs_for k (emission svl s0)
              = map ((!) L) (kposs k (den s0) hp) @ [Event k (u_refresh u k)]"
        using master listed post_e by simp
      then have "state_after D0 (emission svl s0) k = u_refresh u k"
        by (simp add: state_after_key last_append)
      then show ?thesis using sink by simp
    next
      case not_listed: False
      have refresh_none: "u_refresh u k = None"
      proof (rule ccontr)
        assume "u_refresh u k \<noteq> None"
        then have "k \<in> survivors u"
          using k_dom no_win_evs by (simp add: survivors_def)
        then have "k \<in> set (svl u)"
          using svl2_surv[OF svl u_in] by simp
        with not_listed show False ..
      qed
      have master': "evs_for k (emission svl s0)
                       = map ((!) L) (kposs k (den s0) (den (u_lo u)))"
        using master not_listed post_e pre_only by simp
      from O2_honest[OF u_in k_dom] obtain c where
        c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u" and
        honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
        by blast
      show ?thesis
      proof (cases "kposs k (den s0) (den (u_lo u)) = []")
        case pre_e: True
        then have no_evs: "evs_for k (emission svl s0) = []"
          using master' by simp
        then have repl: "state_after D0 (emission svl s0) k = D0 k"
          by (simp add: state_after_no_events)
        have in_abs: "k \<in> absent_untouched u"
          using k_dom refresh_none no_win_evs by (simp add: absent_untouched_def)
        have quiet: "evs_for k (win s0 f) = []"
          using win_s0_f kposs_s0_f_split pre_only pre_e post_e by simp
        show ?thesis
          using repl sink refresh_none in_abs not_listed quiet
          by (simp add: u_def)
      next
        case pre_ne: False
        define q where "q = last (kposs k (den s0) (den (u_lo u)))"
        have lo_le_c: "den (u_lo u) \<le> den c" using c_lo by (simp add: cle_def)
        have c_le_hp: "den c \<le> hp" using c_hi by (simp add: cle_def hp_def)
        have win_lo_c_e: "kposs k (den (u_lo u)) (den c) = []"
          using win_e kposs_split[OF lo_le_c c_le_hp] by auto
        have c_split: "kposs k 0 (den c)
                         = kposs k 0 (den s0) @ kposs k (den s0) (den (u_lo u))"
          using kposs_split[OF le0 s0_le_lo, of k]
                kposs_split[OF _ lo_le_c, of 0 k] win_lo_c_e
          by (metis append_Nil2 le0 s0_le_lo order_trans)
        have pfx_ne: "evs_for k (pfx c) \<noteq> []"
          using evs_for_pfx_kposs c_split pre_ne by simp
        have last_pfx: "last (kposs k 0 (den c)) = q"
          using c_split pre_ne q_def by (simp add: last_append)
        have "state_after \<sigma>0 (pfx c) k = ev_img (L ! q)"
          using state_after_last_event[OF pfx_ne] evs_for_pfx_kposs last_pfx pre_ne
          by (simp add: last_map last_append c_split)
        with honest refresh_none have img_q: "ev_img (L ! q) = None" by simp
        have "state_after D0 (emission svl s0) k = ev_img (L ! q)"
          by (subst state_after_key)
             (simp add: master' pre_ne q_def last_map)
        then have "state_after D0 (emission svl s0) k = sink_at f k"
          using sink refresh_none img_q by simp
        then show ?thesis ..
      qed
    qed
  qed
qed

subsection \<open>Convergence under coverage\<close>

text \<open>
  Coverage: every absent untouched key that the sink holds, and for which
  the consumed stream carries no event, is enumerated. Under coverage the
  replay from @{text D0} is the canonical replay, and by the contract
  theorem the source state at the frontier.
\<close>

theorem absent_replay:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and cover: "\<lbrakk> D0 k \<noteq> None; k \<in> absent_untouched (the_unit k);
                    evs_for k (win s0 f) = [] \<rbrakk> \<Longrightarrow> k \<in> set (svl (the_unit k))"
  shows "state_after D0 (emission svl s0) k = sink_at f k"
proof -
  from absent_replay_safe[OF svl s0lo k, of D0] show ?thesis
  proof
    assume "state_after D0 (emission svl s0) k = sink_at f k"
    then show ?thesis .
  next
    assume orphan: "state_after D0 (emission svl s0) k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> absent_untouched (the_unit k)
            \<and> k \<notin> set (svl (the_unit k))
            \<and> evs_for k (win s0 f) = []"
    show ?thesis
    proof (cases "D0 k = None")
      case True
      then show ?thesis using orphan by simp
    next
      case False
      then have "k \<in> set (svl (the_unit k))"
        using cover orphan by blast
      with orphan show ?thesis by simp
    qed
  qed
qed

theorem absent_replay_cut:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and cover: "\<lbrakk> D0 k \<noteq> None; k \<in> absent_untouched (the_unit k);
                    evs_for k (win s0 f) = [] \<rbrakk> \<Longrightarrow> k \<in> set (svl (the_unit k))"
  shows "state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
  by (rule trans[OF absent_replay[OF svl s0lo k cover] contract_cut[OF k]])

definition covers :: "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> ('k, 'v) state \<Rightarrow> 'c \<Rightarrow> bool" where
  "covers svl D0 s0 \<longleftrightarrow>
     (\<forall>u \<in> set units. \<forall>k \<in> absent_untouched u.
        D0 k \<noteq> None \<longrightarrow> evs_for k (win s0 f) = [] \<longrightarrow> k \<in> set (svl u))"

theorem self_stabilization:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and cov: "covers svl D0 s0"
  shows "\<forall>k \<in> scope. state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
proof
  fix k assume k: "k \<in> scope"
  have u_in: "the_unit k \<in> set units"
    using the_unit_props(1)[OF k] .
  show "state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
  proof (rule absent_replay_cut[OF svl s0lo k])
    assume "D0 k \<noteq> None" "k \<in> absent_untouched (the_unit k)" "evs_for k (win s0 f) = []"
    then show "k \<in> set (svl (the_unit k))"
      using cov u_in by (simp add: covers_def)
  qed
qed

subsection \<open>Existence: the sink-expanded enumeration\<close>

text \<open>
  A sink with finitely many rows admits a covering enumeration when every
  unit has finitely many survivors: list the survivors together with the
  absent untouched keys the sink holds. This is the range record as the sink
  applies it: delete, in the unit's domain, every key it holds that is
  neither a returned row nor touched inside the bracket.
\<close>

lemma svl2_exists_covering:
  assumes fin_surv: "\<And>u. u \<in> set units \<Longrightarrow> finite (survivors u)"
      and fin_sink: "finite {k. D0 k \<noteq> None}"
  shows "\<exists>svl. svl_ok2 svl \<and> covers svl D0 s0"
proof -
  define tgt where
    "tgt = (\<lambda>u. survivors u \<union> (absent_untouched u \<inter> {k. D0 k \<noteq> None}))"
  define svl where
    "svl = (\<lambda>u. SOME xs. distinct xs \<and> set xs = tgt u)"
  have fin_tgt: "finite (tgt u)" if u: "u \<in> set units" for u
  proof -
    have "finite (absent_untouched u \<inter> {k. D0 k \<noteq> None})"
      using fin_sink by (rule finite_subset[rotated]) auto
    then show ?thesis
      using fin_surv[OF u] by (simp add: tgt_def)
  qed
  have svl_props: "distinct (svl u) \<and> set (svl u) = tgt u"
    if u: "u \<in> set units" for u
  proof -
    have "\<exists>xs. distinct xs \<and> set xs = tgt u"
      using finite_distinct_list[OF fin_tgt[OF u]] by metis
    then show ?thesis
      unfolding svl_def by (rule someI_ex)
  qed
  have "svl_ok2 svl"
    unfolding svl_ok2_def
  proof (intro ballI conjI)
    fix u assume u: "u \<in> set units"
    show "distinct (svl u)" using svl_props[OF u] by simp
    show "survivors u \<subseteq> set (svl u)"
      using svl_props[OF u] by (simp add: tgt_def)
    show "set (svl u) \<subseteq> survivors u \<union> absent_untouched u"
      using svl_props[OF u] by (auto simp: tgt_def)
  qed
  moreover have "covers svl D0 s0"
    unfolding covers_def
  proof (intro ballI impI)
    fix u k assume u: "u \<in> set units" and k: "k \<in> absent_untouched u"
      and held: "D0 k \<noteq> None" and "evs_for k (win s0 f) = []"
    show "k \<in> set (svl u)"
      using svl_props[OF u] k held by (simp add: tgt_def)
  qed
  ultimately show ?thesis by blast
qed

theorem range_record_converges:
  assumes s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and fin_surv: "\<And>u. u \<in> set units \<Longrightarrow> finite (survivors u)"
      and fin_sink: "finite {k. D0 k \<noteq> None}"
  shows "\<exists>svl. svl_ok2 svl \<and>
           (\<forall>k \<in> scope. state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k)"
proof -
  obtain svl where ok: "svl_ok2 svl" and cov: "covers svl D0 s0"
    using svl2_exists_covering[OF fin_surv fin_sink] by blast
  then show ?thesis
    using self_stabilization[OF ok s0lo cov] by blast
qed

subsection \<open>Partial enumerations: completeness equals coverage\<close>

text \<open>
  A connector that lists candidates from a stale or partial sink read
  obtains an admissible enumeration whenever it keeps only keys read as
  absent and untouched. The safety theorem then says: every key the read
  reported is repaired, every live row is kept, and the only keys left
  wrong are orphans the read did not report. This is the formal content of
  ``staleness of the sink read is harmless''.
\<close>

theorem partial_enumeration_safe:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and listed_or_clear: "k \<in> set (svl (the_unit k)) \<or> D0 k = None"
  shows "state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
proof (rule absent_replay_cut[OF svl s0lo k])
  assume "D0 k \<noteq> None"
  then show "k \<in> set (svl (the_unit k))"
    using listed_or_clear by auto
qed

subsection \<open>Unlisted quiet keys are left alone, and coverage is necessary\<close>

lemma unlisted_quiet_key_kept:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and k: "k \<in> scope"
      and unlisted: "k \<notin> set (svl (the_unit k))"
      and quiet: "evs_for k (win s0 f) = []"
  shows "state_after D0 (emission svl s0) k = D0 k"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units"
    using the_unit_props(1)[OF k] u_def by simp
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have s0_lo: "s0 \<sqsubseteq> u_lo u" using s0lo[OF u_in] .
  have s0_f: "s0 \<sqsubseteq> f" using s0_lo lo_hi hi_f cle_trans by blast
  have s0_le_hp: "den s0 \<le> hp"
    using s0_lo lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)
  have master: "evs_for k (emission svl s0) =
          map ((!) L) (kposs k (den s0) hp)
          @ (if k \<in> set (svl u) then [Event k (u_refresh u k)] else [])
          @ map ((!) L) (kposs k hp (den f))"
    unfolding emission_def evs_for_map_snd
    using titems_emission_master2[OF svl s0lo k]
    by (simp add: u_def hp_def comp_def if_distrib map_append
             cong: if_cong)
  have "kposs k (den s0) (den f) = []"
    using quiet evs_for_win_kposs[OF s0_f] by simp
  then have "kposs k (den s0) hp = [] \<and> kposs k hp (den f) = []"
    using kposs_split[OF s0_le_hp hp_le_f] by simp
  then have "evs_for k (emission svl s0) = []"
    using master unlisted by (simp add: u_def)
  then show ?thesis
    by (simp add: state_after_no_events)
qed

theorem coverage_necessary:
  assumes svl: "svl_ok2 svl"
      and s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and conv: "\<forall>k \<in> scope. state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
  shows "covers svl D0 s0"
  unfolding covers_def
proof (intro ballI impI)
  fix u k
  assume u: "u \<in> set units" and ka: "k \<in> absent_untouched u"
     and held: "D0 k \<noteq> None" and quiet: "evs_for k (win s0 f) = []"
  have k_dom: "k \<in> u_dom u" and refresh_none: "u_refresh u k = None"
    using ka by (auto simp: absent_untouched_def)
  have k_sc: "k \<in> scope" using dom_sub_scope[OF u] k_dom by auto
  have u_eq: "u = the_unit k"
    using covering_unit_unique[OF u k_dom the_unit_props(1)[OF k_sc] the_unit_props(2)[OF k_sc]] .
  have lo_f: "u_lo u \<sqsubseteq> f"
    using bracket_lo_hi[OF u] bracket_hi_f[OF u] by (rule cle_trans)
  have s0_lo: "s0 \<sqsubseteq> u_lo u" using s0lo[OF u] .
  have "evs_for k (win s0 f) = evs_for k (win s0 (u_lo u)) @ evs_for k (win (u_lo u) f)"
    by (rule evs_for_win_split[OF s0_lo lo_f])
  with quiet have quiet_lo: "evs_for k (win (u_lo u) f) = []" by simp
  have src_none: "state_after \<sigma>0 (pfx f) k = None"
    using contract_cut[OF k_sc] quiet_lo refresh_none
    by (simp add: sink_at_def flip: u_eq)
  show "k \<in> set (svl u)"
  proof (rule ccontr)
    assume "k \<notin> set (svl u)"
    then have "state_after D0 (emission svl s0) k = D0 k"
      using unlisted_quiet_key_kept[OF svl s0lo k_sc] quiet u_eq by simp
    with conv k_sc src_none held show False by simp
  qed
qed

text \<open>
  A complete sink read, taken at any consumed position @{text "g u"} before
  the frontier, provides coverage: a key the sink holds at that position
  with no consumed event is still the initial value, so it is reported.
  The premise @{text rd} states the read on the log-only state at
  @{text "g u"}. For a key the unit does not list, that is the sink's state
  there, since no close entry of any unit writes it (domains are disjoint,
  and a unit's close block writes only the keys it lists). A listed key needs
  no coverage argument.
\<close>

lemma sink_read_covers:
  assumes g_ok: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> g u \<and> g u \<sqsubseteq> f"
      and rd: "\<And>u k. \<lbrakk> u \<in> set units; k \<in> absent_untouched u;
                      state_after D0 (win s0 (g u)) k \<noteq> None \<rbrakk> \<Longrightarrow> k \<in> set (svl u)"
  shows "covers svl D0 s0"
  unfolding covers_def
proof (intro ballI impI)
  fix u k
  assume u: "u \<in> set units" and ka: "k \<in> absent_untouched u"
     and held: "D0 k \<noteq> None" and quiet: "evs_for k (win s0 f) = []"
  have s0_g: "s0 \<sqsubseteq> g u" and g_f: "g u \<sqsubseteq> f" using g_ok[OF u] by auto
  have "evs_for k (win s0 f) = evs_for k (win s0 (g u)) @ evs_for k (win (g u) f)"
    by (rule evs_for_win_split[OF s0_g g_f])
  with quiet have "evs_for k (win s0 (g u)) = []" by simp
  then have "state_after D0 (win s0 (g u)) k = D0 k"
    by (rule state_after_no_events)
  with held have "state_after D0 (win s0 (g u)) k \<noteq> None" by simp
  then show "k \<in> set (svl u)" using rd[OF u ka] by simp
qed

subsection \<open>The chunk record: a key range with its selected and changed keys\<close>

text \<open>
  The paper's chunk info record names a key range, the unit's domain, and two
  key lists, the selected keys the read returned and the changed keys
  touched inside the bracket, whose union is the except set below. A sink
  applies it by deleting every key it holds in the range that is on
  neither list, and by upserting the surviving returned rows. Stated in
  those terms, the keys the sink deletes are exactly the absent untouched
  keys it holds, so the record is the covering enumeration of the previous
  subsection. An except set that over-approximates inside the range still yields an
  admissible enumeration, hence a safe one, a robustness result the paper
  does not rely on, since its two lists are exact.
\<close>

definition except_keys :: "('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "except_keys u =
     {k \<in> u_dom u. u_refresh u k \<noteq> None} \<union>
     {k \<in> u_dom u. evs_for k (win (u_lo u) (u_hi u)) \<noteq> []}"

lemma dom_minus_except: "u_dom u - except_keys u = absent_untouched u"
  by (auto simp: except_keys_def absent_untouched_def)

definition record_enum ::
  "('k, 'v, 'c) cunit \<Rightarrow> 'k set \<Rightarrow> ('k, 'v) state \<Rightarrow> 'k set" where
  "record_enum u E D = survivors u \<union> ((u_dom u - E) \<inter> {k. D k \<noteq> None})"

lemma record_enum_ok2:
  assumes E_sup: "\<And>u. u \<in> set units \<Longrightarrow> except_keys u \<subseteq> E u"
      and svl_set: "\<And>u. u \<in> set units \<Longrightarrow>
                      distinct (svl u) \<and> set (svl u) = record_enum u (E u) D0"
  shows "svl_ok2 svl"
  unfolding svl_ok2_def
proof (intro ballI conjI)
  fix u assume u: "u \<in> set units"
  show "distinct (svl u)" using svl_set[OF u] by simp
  show "survivors u \<subseteq> set (svl u)"
    using svl_set[OF u] by (simp add: record_enum_def)
  have sub: "u_dom u - E u \<subseteq> absent_untouched u"
    using E_sup[OF u] dom_minus_except[of u] by auto
  show "set (svl u) \<subseteq> survivors u \<union> absent_untouched u"
    using svl_set[OF u] sub by (auto simp: record_enum_def)
qed

lemma record_enum_covers:
  assumes svl_set: "\<And>u. u \<in> set units \<Longrightarrow>
                      set (svl u) = record_enum u (except_keys u) D0"
  shows "covers svl D0 s0"
  unfolding covers_def
proof (intro ballI impI)
  fix u k
  assume u: "u \<in> set units" and ka: "k \<in> absent_untouched u"
     and held: "D0 k \<noteq> None" and "evs_for k (win s0 f) = []"
  have "k \<in> u_dom u - except_keys u"
    using ka dom_minus_except[of u] by simp
  then show "k \<in> set (svl u)"
    using svl_set[OF u] held by (auto simp: record_enum_def)
qed

theorem chunk_record_converges:
  assumes s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and svl_set: "\<And>u. u \<in> set units \<Longrightarrow>
                      distinct (svl u) \<and> set (svl u) = record_enum u (except_keys u) D0"
  shows "\<forall>k \<in> scope. state_after D0 (emission svl s0) k = state_after \<sigma>0 (pfx f) k"
proof -
  have ok: "svl_ok2 svl"
    by (rule record_enum_ok2[OF _ svl_set]) (rule subset_refl)
  have cov: "covers svl D0 s0"
  proof (rule record_enum_covers)
    fix u assume "u \<in> set units"
    then show "set (svl u) = record_enum u (except_keys u) D0"
      using svl_set by simp
  qed
  show ?thesis by (rule self_stabilization[OF ok s0lo cov])
qed

theorem except_overapprox_safe:
  assumes s0lo: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_lo u"
      and E_sup: "\<And>u. u \<in> set units \<Longrightarrow> except_keys u \<subseteq> E u"
      and svl_set: "\<And>u. u \<in> set units \<Longrightarrow>
                      distinct (svl u) \<and> set (svl u) = record_enum u (E u) D0"
      and k: "k \<in> scope"
  shows "state_after D0 (emission svl s0) k = sink_at f k
         \<or> (state_after D0 (emission svl s0) k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> absent_untouched (the_unit k)
            \<and> k \<notin> set (svl (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
  by (rule absent_replay_safe[OF record_enum_ok2[OF E_sup svl_set] s0lo k])

end  (* context capture_contract *)

subsection \<open>A certified absence is a unit of the contract\<close>

text \<open>
  The tail assertion of the design: a key set observed empty at a
  coordinate inside a bracket forms a one-unit capture contract with
  refresh @{text None}. The design uses it for the keys above the observed
  maximum (and above the last returned key), so that its domain is disjoint
  from every chunk range.
\<close>

context coordinate_space
begin

lemma absence_assertion_contract:
  fixes \<sigma>0 :: "('k, 'v) state"
  assumes lo_c: "lo \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> hi" and hi_f: "hi \<sqsubseteq> f"
      and empty: "\<And>k. k \<in> T \<Longrightarrow> state_after \<sigma>0 (pfx c) k = None"
  shows "capture_contract L den \<sigma>0
           [\<lparr>u_dom = T, u_lo = lo, u_hi = hi, u_refresh = ((\<lambda>_. None) :: ('k, 'v) state)\<rparr>] T f"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case by simp
next
  case (2 i j)
  then show ?case by simp
next
  case (3 u)
  then show ?case using lo_c c_hi cle_trans by auto
next
  case (4 u)
  then show ?case using hi_f by simp
next
  case (5 u k)
  then show ?case using lo_c c_hi empty by (auto intro!: exI[where x = c])
qed

end  (* context coordinate_space *)

subsection \<open>Splitting a unit: rows at the high edge, absents later\<close>

text \<open>
  The design emits a chunk's surviving rows at its high watermark and its
  absence entries at a later position. In the contract this is a unit
  replaced by two: the present keys keep the original bracket, the absent
  keys get the bracket widened to the emission position. The read witness
  of O2 lies in the original bracket, hence in the widened one, so both
  halves are honest, and the halves partition the domain, so the plan is
  still a strict partition. Two list lemmas carry the index bookkeeping.
\<close>

lemma split_index_subset:
  fixes D :: "'a \<Rightarrow> 'k set"
  assumes b: "D b \<subseteq> D a" and c: "D c \<subseteq> D a"
      and i: "i < length (xs @ b # c # ys)"
  shows "D ((xs @ b # c # ys) ! i) \<subseteq>
           D ((xs @ a # ys) ! (if i < length xs then i
                                else if i \<le> Suc (length xs) then length xs else i - 1))"
proof (cases "i < length xs")
  case True
  then show ?thesis by (simp add: nth_append)
next
  case False
  then consider (eq) "i = length xs" | (suc) "i = Suc (length xs)" | (gt) "i > Suc (length xs)"
    by linarith
  then show ?thesis
  proof cases
    case eq
    then show ?thesis using b by (simp add: nth_append)
  next
    case suc
    then show ?thesis using c by (simp add: nth_append)
  next
    case gt
    then obtain k where i_eq: "i = Suc (Suc (length xs) + k)"
      using less_iff_Suc_add by auto
    have n1: "(xs @ b # c # ys) ! i = ys ! k"
      unfolding i_eq by (simp add: nth_append)
    have n2: "(xs @ a # ys) ! (i - 1) = ys ! k"
      unfolding i_eq by (simp add: nth_append)
    have sel: "(if i < length xs then i else if i \<le> Suc (length xs) then length xs else i - 1) = i - 1"
      using gt by simp
    show ?thesis unfolding sel n1 n2 by simp
  qed
qed

lemma split_index_ne:
  assumes "i \<noteq> j" and "\<not> (i \<in> {m, Suc m} \<and> j \<in> {m, Suc m})"
  shows "(if i < m then i else if i \<le> Suc m then m else i - 1)
         \<noteq> (if j < m then j else if j \<le> Suc m then m else j - 1)"
  using assms by (auto split: if_splits)

lemma split_index_bound:
  assumes "i < length (xs @ b # c # ys)"
  shows "(if i < length xs then i else if i \<le> Suc (length xs) then length xs else i - 1)
         < length (xs @ a # ys)"
  using assms by auto

context coordinate_space
begin

lemma late_absence_split:
  fixes u :: "('k, 'v, 'c) cunit" and \<sigma>0 :: "('k, 'v) state"
  assumes cc: "capture_contract L den \<sigma>0 (us1 @ u # us2) sc f"
      and hi_q: "u_hi u \<sqsubseteq> q" and q_f: "q \<sqsubseteq> f"
  defines "u1 \<equiv> u\<lparr>u_dom := {k \<in> u_dom u. u_refresh u k \<noteq> None}\<rparr>"
      and "u2 \<equiv> u\<lparr>u_dom := {k \<in> u_dom u. u_refresh u k = None}, u_hi := q\<rparr>"
  shows "capture_contract L den \<sigma>0 (us1 @ u1 # u2 # us2) sc f"
proof -
  interpret old: capture_contract L den \<sigma>0 "us1 @ u # us2" sc f by (rule cc)
  define m where "m = length us1"
  have u_in: "u \<in> set (us1 @ u # us2)" by simp
  have dom1_sub: "u_dom u1 \<subseteq> u_dom u" and dom2_sub: "u_dom u2 \<subseteq> u_dom u"
    by (auto simp: u1_def u2_def)
  have dom_union: "u_dom u1 \<union> u_dom u2 = u_dom u" by (auto simp: u1_def u2_def)
  have dom12: "u_dom u1 \<inter> u_dom u2 = {}" by (auto simp: u1_def u2_def)
  have lo1: "u_lo u1 = u_lo u" and hi1: "u_hi u1 = u_hi u" and rf1: "u_refresh u1 = u_refresh u"
    by (simp_all add: u1_def)
  have lo2: "u_lo u2 = u_lo u" and hi2: "u_hi u2 = q" and rf2: "u_refresh u2 = u_refresh u"
    by (simp_all add: u2_def)
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using old.bracket_lo_hi[OF u_in] .
  have lo_q: "u_lo u \<sqsubseteq> q" using lo_hi hi_q by (rule cle_trans)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 1
    have "(\<Union>x\<in>set (us1 @ u1 # u2 # us2). u_dom x) = (\<Union>x\<in>set (us1 @ u # us2). u_dom x)"
      using dom_union by auto
    then show ?case using old.O1_cover by simp
  next
    case (2 i j)
    let ?F = "\<lambda>i. if i < length us1 then i else if i \<le> Suc (length us1) then length us1 else i - 1"
    show ?case
    proof (cases "i \<in> {length us1, Suc (length us1)} \<and> j \<in> {length us1, Suc (length us1)}")
      case True
      have dom21: "u_dom u2 \<inter> u_dom u1 = {}" using dom12 by auto
      from True 2(3) have "(i = length us1 \<and> j = Suc (length us1)) \<or>
                            (i = Suc (length us1) \<and> j = length us1)" by auto
      then show ?thesis
      proof (elim disjE conjE)
        assume "i = length us1" "j = Suc (length us1)"
        then show ?thesis using dom12 by (simp add: nth_append)
      next
        assume "i = Suc (length us1)" "j = length us1"
        then show ?thesis using dom21 by (simp add: nth_append)
      qed
    next
      case False
      have fi: "?F i \<noteq> ?F j" using split_index_ne[OF 2(3) False] .
      have bi: "?F i < length (us1 @ u # us2)" using split_index_bound[OF 2(1)] .
      have bj: "?F j < length (us1 @ u # us2)" using split_index_bound[OF 2(2)] .
      have si: "u_dom ((us1 @ u1 # u2 # us2) ! i) \<subseteq> u_dom ((us1 @ u # us2) ! ?F i)"
        using split_index_subset[OF dom1_sub dom2_sub 2(1)] .
      have sj: "u_dom ((us1 @ u1 # u2 # us2) ! j) \<subseteq> u_dom ((us1 @ u # us2) ! ?F j)"
        using split_index_subset[OF dom1_sub dom2_sub 2(2)] .
      have "u_dom ((us1 @ u # us2) ! ?F i) \<inter> u_dom ((us1 @ u # us2) ! ?F j) = {}"
        using old.O1_disjoint[OF bi bj fi] .
      with si sj show ?thesis by blast
    qed
  next
    case (3 x)
    then have "x \<in> set us1 \<union> set us2 \<or> x = u1 \<or> x = u2" by auto
    then show ?case
      using old.bracket_lo_hi lo1 hi1 lo2 hi2 lo_hi lo_q by auto
  next
    case (4 x)
    then have "x \<in> set us1 \<union> set us2 \<or> x = u1 \<or> x = u2" by auto
    then show ?case
      using old.bracket_hi_f hi1 hi2 q_f by auto
  next
    case (5 x k)
    then have "x \<in> set us1 \<union> set us2 \<or> x = u1 \<or> x = u2" by auto
    then show ?case
    proof (elim disjE)
      assume "x \<in> set us1 \<union> set us2"
      then show ?case using old.O2_honest 5(2) by auto
    next
      assume x1: "x = u1"
      then have "k \<in> u_dom u" using 5(2) dom1_sub by auto
      from old.O2_honest[OF u_in this] obtain c where
        "u_lo u \<sqsubseteq> c" "c \<sqsubseteq> u_hi u" "u_refresh u k = state_after \<sigma>0 (pfx c) k" by blast
      then show ?case using x1 lo1 hi1 rf1 by auto
    next
      assume x2: "x = u2"
      then have "k \<in> u_dom u" using 5(2) dom2_sub by auto
      from old.O2_honest[OF u_in this] obtain c where
        c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u"
        and hon: "u_refresh u k = state_after \<sigma>0 (pfx c) k" by blast
      have "c \<sqsubseteq> q" using c_hi hi_q by (rule cle_trans)
      then show ?case using x2 lo2 hi2 rf2 c_lo hon by auto
    qed
  qed
qed

end  (* context coordinate_space *)

subsection \<open>Fixture: an orphan in the initial sink state is removed\<close>

text \<open>
  Reuses the witness log @{text L_s} and coordinate space @{text sc} of the
  core's fixtures: @{text "L_s = [Event 3 (Some 7), Event 1 (Some 1)]"},
  @{text "den_w c = min c 2"}, @{text "s0_w = (\<lambda>_. None)"}. One unit owns
  keys 3 and 4 with bracket (1, 2]; key 3 is read as present with value 7,
  key 4 as absent. The sink starts with an orphan: it holds key 4 with
  value 9. Enumerating key 4 as an absent entry removes the orphan; the
  survivor-only enumeration of the core leaves it in place.
\<close>

definition orph_unit :: "(nat, nat, nat) cunit" where
  "orph_unit = \<lparr>u_dom = {3, 4}, u_lo = 1, u_hi = 2,
                u_refresh = (\<lambda>k. if k = 3 then Some 7 else None)\<rparr>"

definition D0_o :: "(nat, nat) state" where
  "D0_o = (\<lambda>k. if k = 4 then Some 9 else None)"

interpretation orph: capture_contract L_s den_w s0_w "[orph_unit]" "{3, 4}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [orph_unit]. u_dom u) = {3, 4}"
    by (simp add: orph_unit_def)
next
  fix i j
  assume "i < length [orph_unit]" "j < length [orph_unit]" "i \<noteq> j"
  then show "u_dom ([orph_unit] ! i) \<inter> u_dom ([orph_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [orph_unit]"
  then show "sc.cle (u_lo u) (u_hi u)"
    by (simp add: orph_unit_def sc.cle_def den_w_def)
next
  fix u assume "u \<in> set [orph_unit]"
  then show "sc.cle (u_hi u) 2"
    by (simp add: orph_unit_def sc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [orph_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. sc.cle (u_lo u) c \<and> sc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (sc.pfx c) k"
    unfolding sc.cle_def sc.pfx_def
    by (intro exI[of _ 1])
       (auto simp add: orph_unit_def den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
qed

lemma orph_win_4: "evs_for 4 (sc.win (u_lo orph_unit) (u_hi orph_unit)) = []"
  unfolding sc.win_def
  by (simp add: orph_unit_def den_w_def L_s_def evs_for_def)

lemma orph_win_3: "evs_for 3 (sc.win (u_lo orph_unit) (u_hi orph_unit)) = []"
  unfolding sc.win_def
  by (simp add: orph_unit_def den_w_def L_s_def evs_for_def)

lemma orph_survivors: "orph.survivors orph_unit = {3}"
  using orph_win_3 orph_win_4 by (auto simp: orph.survivors_def orph_unit_def)

lemma orph_absent_untouched: "orph.absent_untouched orph_unit = {4}"
  using orph_win_3 orph_win_4 by (auto simp: orph.absent_untouched_def orph_unit_def)

lemma orph_svl_ok2: "orph.svl_ok2 (\<lambda>_. [3, 4])"
  using orph_survivors orph_absent_untouched by (simp add: orph.svl_ok2_def)

lemma orph_covers: "orph.covers (\<lambda>_. [3, 4]) D0_o 0"
  using orph_absent_untouched by (simp add: orph.covers_def)

lemma orph_s0lo: "\<And>u. u \<in> set [orph_unit] \<Longrightarrow> sc.cle 0 (u_lo u)"
  by (simp add: orph_unit_def sc.cle_def den_w_def)

text \<open>With the absent entry enumerated, the orphan is gone.\<close>

lemma wit_orphan_removed:
  "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0) 4 = None"
proof -
  have "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0) 4 = state_after s0_w (sc.pfx 2) 4"
    using orph.self_stabilization[OF orph_svl_ok2 orph_s0lo orph_covers] by simp
  also have "\<dots> = None"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

lemma wit_orphan_present_kept:
  "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0) 3 = Some 7"
proof -
  have "state_after D0_o (orph.emission (\<lambda>_. [3, 4]) 0) 3 = state_after s0_w (sc.pfx 2) 3"
    using orph.self_stabilization[OF orph_svl_ok2 orph_s0lo orph_covers] by simp
  also have "\<dots> = Some 7"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

text \<open>The survivor-only enumeration of the core keeps the orphan.\<close>

lemma orph_svl_ok2_core: "orph.svl_ok2 (\<lambda>_. [3])"
  using orph_survivors orph_absent_untouched by (simp add: orph.svl_ok2_def)

lemma wit_orphan_kept_by_omission:
  "state_after D0_o (orph.emission (\<lambda>_. [3]) 0) 4 = Some 9"
proof -
  have the4: "orph.the_unit 4 = orph_unit"
    using orph.the_unit_props[of 4] by simp
  have quiet: "evs_for 4 (sc.win 0 2) = []"
    unfolding sc.win_def by (simp add: den_w_def L_s_def evs_for_def)
  have "state_after D0_o (orph.emission (\<lambda>_. [3]) 0) 4 = D0_o 4"
    by (rule orph.unlisted_quiet_key_kept[OF orph_svl_ok2_core orph_s0lo])
       (simp_all add: the4 quiet)
  then show ?thesis by (simp add: D0_o_def)
qed

subsection \<open>Fixture: the read-at-high unit (Flink CDC) is a zero-width bracket\<close>

text \<open>
  Flink CDC folds the window's events into the chunk image and emits the
  merged image at the high watermark, so its unit reads the source at the
  high watermark itself: the bracket has @{text "u_lo = u_hi"} and the
  window is empty. The locale admits this (@{text bracket_lo_hi} is not
  strict), no key is excluded, the survivors are the present keys, and the
  absent keys of the range are exactly the keys missing from the merged
  image. The same orphan is removed by enumerating it. This is the design's
  "read-at-hi unit without exclusion" for Flink CDC.
\<close>

definition rah_unit :: "(nat, nat, nat) cunit" where
  "rah_unit = \<lparr>u_dom = {3, 4}, u_lo = 2, u_hi = 2,
               u_refresh = (\<lambda>k. if k = 3 then Some 7 else None)\<rparr>"

interpretation rah: capture_contract L_s den_w s0_w "[rah_unit]" "{3, 4}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [rah_unit]. u_dom u) = {3, 4}"
    by (simp add: rah_unit_def)
next
  fix i j
  assume "i < length [rah_unit]" "j < length [rah_unit]" "i \<noteq> j"
  then show "u_dom ([rah_unit] ! i) \<inter> u_dom ([rah_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [rah_unit]"
  then show "sc.cle (u_lo u) (u_hi u)"
    by (simp add: rah_unit_def sc.cle_def den_w_def)
next
  fix u assume "u \<in> set [rah_unit]"
  then show "sc.cle (u_hi u) 2"
    by (simp add: rah_unit_def sc.cle_def den_w_def)
next
  fix u k assume "u \<in> set [rah_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. sc.cle (u_lo u) c \<and> sc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after s0_w (sc.pfx c) k"
    unfolding sc.cle_def sc.pfx_def
    by (intro exI[of _ 2])
       (auto simp add: rah_unit_def den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
qed

lemma rah_win_empty: "sc.win (u_lo rah_unit) (u_hi rah_unit) = []"
  unfolding sc.win_def by (simp add: rah_unit_def den_w_def L_s_def)

lemma rah_survivors: "rah.survivors rah_unit = {3}"
  using rah_win_empty by (auto simp: rah.survivors_def rah_unit_def evs_for_def)

lemma rah_absent_untouched: "rah.absent_untouched rah_unit = {4}"
  using rah_win_empty by (auto simp: rah.absent_untouched_def rah_unit_def evs_for_def)

lemma rah_svl_ok2: "rah.svl_ok2 (\<lambda>_. [3, 4])"
  using rah_survivors rah_absent_untouched by (simp add: rah.svl_ok2_def)

lemma rah_covers: "rah.covers (\<lambda>_. [3, 4]) D0_o 0"
  using rah_absent_untouched by (simp add: rah.covers_def)

lemma rah_s0lo: "\<And>u. u \<in> set [rah_unit] \<Longrightarrow> sc.cle 0 (u_lo u)"
  by (simp add: rah_unit_def sc.cle_def den_w_def)

text \<open>With the window empty, "range minus emitted keys" is the whole absent set.\<close>

lemma wit_read_at_hi_orphan_removed:
  "state_after D0_o (rah.emission (\<lambda>_. [3, 4]) 0) 4 = None"
proof -
  have "state_after D0_o (rah.emission (\<lambda>_. [3, 4]) 0) 4 = state_after s0_w (sc.pfx 2) 4"
    using rah.self_stabilization[OF rah_svl_ok2 rah_s0lo rah_covers] by simp
  also have "\<dots> = None"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

lemma wit_read_at_hi_present_kept:
  "state_after D0_o (rah.emission (\<lambda>_. [3, 4]) 0) 3 = Some 7"
proof -
  have "state_after D0_o (rah.emission (\<lambda>_. [3, 4]) 0) 3 = state_after s0_w (sc.pfx 2) 3"
    using rah.self_stabilization[OF rah_svl_ok2 rah_s0lo rah_covers] by simp
  also have "\<dots> = Some 7"
    unfolding sc.pfx_def by (simp add: den_w_def L_s_def s0_w_def state_after_def apply_ev_def)
  finally show ?thesis .
qed

end
