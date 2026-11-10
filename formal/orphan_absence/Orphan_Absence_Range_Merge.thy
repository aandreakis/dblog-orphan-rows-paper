(* SPDX-License-Identifier: BSD-3-Clause *)
(*
  Orphan_Absence_Range_Merge: Flink CDC's buffered range merge with
  statements of absence and the re-emitted held-back deletes, replayed
  from an arbitrary initial sink state.

  Additive to the Generalized DBLog contract core (DBLog_Framework_Core).
  Nothing in the archived development is modified.
*)
theory Orphan_Absence_Range_Merge
  imports DBLog_Framework_Core.Range_Merge
begin

text \<open>
  The core's buffered range merge (theory @{text Range_Merge}) models Flink
  CDC: the window's events are upserted onto the chunk buffer, a gate holds
  back every scoped event below its unit's high edge, and the close block
  emits @{text "Event k (merged u k)"} for each enumerated key. The core
  enumerates exactly the keys present in the merged image and proves the
  replay from the EMPTY map.

  This theory widens the enumeration. A key absent from the merged image may
  be listed as well; its close entry is then @{text "Event k None"}, a
  statement of absence. Every key whose held-back events end in a delete must
  be listed (@{text forced}): these are the deletes the connector re-emits at
  the close, whether or not a statement of absence is emitted. An event is
  held back when the gate holds it back from the stream, which carries the log
  from the consumption start @{text s0}, or when the window merges it into the
  buffer. When the stream starts inside the window, the merged events begin
  earlier, at the window's start. The replay is then taken from an ARBITRARY
  initial sink state @{text D0}. Results:

  \<^item> Safety: every scoped key either agrees with the canonical replay at the
    frontier, or it is absent at the source, not listed, without any event in
    the consumed segment, and the sink keeps what it held.
  \<^item> Convergence: under coverage of the absent keys the sink holds and the
    stream never mentions, the replay is the source state at the frontier, and
    coverage is necessary.
  \<^item> The forced keys are exactly the keys whose last held-back event is a
    delete, and the fixtures show that without them a row in sync before the
    pass stays in the sink, for a delete before the window and inside it, the
    latter also when the stream starts at the chunk's close.
\<close>

context capture_plan
begin

definition rm_absent :: "('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "rm_absent u = {k \<in> u_dom u. merged u k = None}"

text \<open>
  The held-back events of a unit start at @{text "held_from s0 u"}, the
  earlier of the consumption start and the window's start, and end at the
  unit's high edge.
\<close>

definition held_from :: "'c \<Rightarrow> ('k, 'v, 'c) cunit \<Rightarrow> 'c" where
  "held_from s0 u = (if den s0 \<le> den (u_lo u) then s0 else u_lo u)"

definition forced :: "'c \<Rightarrow> ('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "forced s0 u = {k \<in> rm_absent u. evs_for k (win (held_from s0 u) (u_hi u)) \<noteq> []}"

lemma held_from_le_s0: "held_from s0 u \<sqsubseteq> s0"
  by (auto simp: held_from_def cle_def)

lemma held_from_le_lo: "held_from s0 u \<sqsubseteq> u_lo u"
  by (auto simp: held_from_def cle_def)

lemma held_from_early: "s0 \<sqsubseteq> u_lo u \<Longrightarrow> held_from s0 u = s0"
  by (simp add: held_from_def cle_def)

definition rml_ok2 :: "'c \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> bool" where
  "rml_ok2 s0 rml \<longleftrightarrow>
     (\<forall>u \<in> set units. distinct (rml u) \<and>
                        rm_present u \<union> forced s0 u \<subseteq> set (rml u) \<and>
                        set (rml u) \<subseteq> u_dom u)"

definition rm_covers ::
    "'c \<Rightarrow> (('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> ('k, 'v) state \<Rightarrow> bool" where
  "rm_covers s0 rml D0 \<longleftrightarrow>
     (\<forall>u \<in> set units. \<forall>k \<in> rm_absent u.
        D0 k \<noteq> None \<longrightarrow> evs_for k (win s0 f) = [] \<longrightarrow> k \<in> set (rml u))"

end  (* context capture_plan *)

context capture_contract
begin

subsection \<open>The widened enumeration\<close>

lemma rml2_distinct: "rml_ok2 s0 rml \<Longrightarrow> u \<in> set units \<Longrightarrow> distinct (rml u)"
  by (simp add: rml_ok2_def)

lemma rml2_sub_dom: "rml_ok2 s0 rml \<Longrightarrow> u \<in> set units \<Longrightarrow> set (rml u) \<subseteq> u_dom u"
  by (simp add: rml_ok2_def)

lemma rml2_present:
  "rml_ok2 s0 rml \<Longrightarrow> u \<in> set units \<Longrightarrow> k \<in> rm_present u \<Longrightarrow> k \<in> set (rml u)"
  by (auto simp: rml_ok2_def)

lemma rml2_forced:
  "rml_ok2 s0 rml \<Longrightarrow> u \<in> set units \<Longrightarrow> k \<in> forced s0 u \<Longrightarrow> k \<in> set (rml u)"
  by (auto simp: rml_ok2_def)

lemma titems_rm_close_block2:
  assumes rml: "rml_ok2 s0 rml" and u_in: "u \<in> set units"
  shows "titems_for k (rm_close_block rml u) =
           (if k \<in> set (rml u)
            then [(den (u_hi u), Event k (merged u k))] else [])"
proof -
  have dis: "distinct (rml u)"
    using rml2_distinct[OF rml u_in] .
  have "titems_for k (rm_close_block rml u) =
          map (\<lambda>k'. (den (u_hi u), Event k' (merged u k')))
              (filter (\<lambda>k'. k' = k) (rml u))"
    by (simp add: titems_for_def rm_close_block_def filter_map comp_def)
  then show ?thesis
    using distinct_filter_eq[OF dis] by simp
qed

lemma titems_rm_closes_at2:
  assumes rml: "rml_ok2 s0 rml" and k: "k \<in> scope"
  shows "titems_for k (rm_closes_at rml p) =
           (if den (u_hi (the_unit k)) = p \<and> k \<in> set (rml (the_unit k))
            then [(p, Event k (merged (the_unit k) k))] else [])"
proof -
  obtain i0 where i0: "i0 < length units" "units ! i0 = the_unit k"
    using the_unit_props(1)[OF k] by (meson in_set_conv_nth)
  have others: "titems_for k (if den (u_hi (units ! i)) = p
                              then rm_close_block rml (units ! i) else []) = []"
    if i: "i < length units" and ne: "i \<noteq> i0" for i
  proof -
    have ui_in: "units ! i \<in> set units" using i by simp
    have "k \<notin> set (rml (units ! i))"
    proof
      assume "k \<in> set (rml (units ! i))"
      then have "k \<in> u_dom (units ! i)"
        using rml2_sub_dom[OF rml ui_in] by auto
      then have eq: "units ! i = the_unit k"
        using covering_unit_unique[OF ui_in _ the_unit_props(1)[OF k]
                                       the_unit_props(2)[OF k]] by blast
      have "i = i0"
        by (rule the_unit_position_unique[OF k i eq i0(1) i0(2)])
      with ne show False ..
    qed
    then show ?thesis
      using titems_rm_close_block2[OF rml ui_in]
      by (simp add: titems_for_def)
  qed
  have "titems_for k (rm_closes_at rml p) =
          concat (map (\<lambda>i. titems_for k (if den (u_hi (units ! i)) = p
                                          then rm_close_block rml (units ! i)
                                          else []))
                      [0..<length units])"
    unfolding rm_closes_at_def titems_for_def
    by (simp add: filter_concat_map comp_def if_distrib
             cong: if_cong)
  also have "\<dots> = titems_for k (if den (u_hi (units ! i0)) = p
                                 then rm_close_block rml (units ! i0) else [])"
    by (rule concat_map_upt_single[OF others i0(1)])
  finally show ?thesis
    using titems_rm_close_block2[OF rml the_unit_props(1)[OF k]] i0(2)
    by (simp add: titems_for_def)
qed

text \<open>
  The core's master characterization carries over: a key's occurrences in
  the gated emission are its close entry (iff listed), then its events from
  the high edge on. The core's proof uses the enumeration only through the
  two lemmas above.
\<close>

lemma titems_rm_emission_master2:
  assumes rml: "rml_ok2 s0 rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
  shows "titems_for k (rm_emission_t rml s0) =
           (if k \<in> set (rml (the_unit k))
            then [(den (u_hi (the_unit k)),
                   Event k (merged (the_unit k) k))] else [])
           @ map (\<lambda>p. (Suc p, L ! p))
                 (kposs k (den (u_hi (the_unit k))) (den f))"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units"
    using the_unit_props(1)[OF k] u_def by simp
  have s0_le_hp: "den s0 \<le> hp"
    using s0hi[OF u_in] by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using bracket_hi_f[OF u_in] by (simp add: cle_def hp_def)

  have closes: "\<And>p. titems_for k (rm_closes_at rml p) =
           (if hp = p \<and> k \<in> set (rml u)
            then [(p, Event k (merged u k))] else [])"
    using titems_rm_closes_at2[OF rml k] by (simp add: u_def hp_def)

  have gate_k: "\<And>p. (rm_gate p \<and> ev_key (L ! p) = k)
                       = (ev_key (L ! p) = k \<and> hp \<le> p)"
    using k by (auto simp: rm_gate_def u_def hp_def)

  have item: "\<And>p. titems_for k (rm_closes_at rml p
                     @ (if rm_gate p then [(Suc p, L ! p)] else []))
                 = titems_for k (rm_closes_at rml p)
                     @ (if rm_gate p \<and> ev_key (L ! p) = k
                        then [(Suc p, L ! p)] else [])"
  proof -
    fix p
    show "titems_for k (rm_closes_at rml p
            @ (if rm_gate p then [(Suc p, L ! p)] else []))
          = titems_for k (rm_closes_at rml p)
            @ (if rm_gate p \<and> ev_key (L ! p) = k
               then [(Suc p, L ! p)] else [])"
      by (cases "rm_gate p") (simp_all add: titems_for_def)
  qed

  have expand: "titems_for k (rm_emission_t rml s0) =
        concat (map (\<lambda>p. titems_for k
                           (rm_closes_at rml p
                              @ (if rm_gate p then [(Suc p, L ! p)] else [])))
                    [den s0..<den f])
        @ titems_for k (rm_closes_at rml (den f))"
    unfolding rm_emission_t_def titems_for_def
    by (simp add: filter_concat_map comp_def)

  have maps: "map (\<lambda>p. titems_for k
                         (rm_closes_at rml p
                            @ (if rm_gate p then [(Suc p, L ! p)] else [])))
                  [den s0..<den f]
            = map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                  [den s0..<den f]"
    by (rule map_cong[OF refl]) (rule item)

  have dist: "titems_for k (rm_emission_t rml s0) =
        concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [den s0..<den f])
        @ titems_for k (rm_closes_at rml (den f))"
    by (simp only: expand maps)

  show ?thesis
  proof (cases "hp < den f")
    case False
    then have hp_f: "hp = den f"
      using hp_le_f by simp
    have kposs_e: "kposs k hp (den f) = []"
      using hp_f by (simp add: kposs_def)
    have main_nil: "concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [den s0..<den f]) = []"
    proof (rule concat_map_nil)
      fix p assume "p \<in> set [den s0..<den f]"
      then have p_lt: "p < den f" by simp
      have "titems_for k (rm_closes_at rml p) = []"
        using closes hp_f p_lt by auto
      moreover have "\<not> (rm_gate p \<and> ev_key (L ! p) = k)"
        using gate_k hp_f p_lt by auto
      ultimately show "titems_for k (rm_closes_at rml p)
              @ (if rm_gate p \<and> ev_key (L ! p) = k
                 then [(Suc p, L ! p)] else []) = []"
        by simp
    qed
    have tail_eq: "titems_for k (rm_closes_at rml (den f))
          = (if k \<in> set (rml u) then [(den f, Event k (merged u k))] else [])"
      using closes[of "den f"] hp_f by simp
    show ?thesis
      unfolding dist main_nil tail_eq
      using hp_f kposs_e by (simp add: u_def hp_def)
  next
    case True
    have split: "[den s0..<den f] = [den s0..<hp] @ [hp..<den f]"
      using s0_le_hp hp_le_f by (rule upt_split)
    have head: "[hp..<den f] = hp # [Suc hp..<den f]"
      using True by (simp add: upt_rec)
    have pre: "concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [den s0..<hp]) = []"
    proof (rule concat_map_nil)
      fix p assume "p \<in> set [den s0..<hp]"
      then have p_lt: "p < hp" by simp
      have "titems_for k (rm_closes_at rml p) = []"
        using closes p_lt by auto
      moreover have "\<not> (rm_gate p \<and> ev_key (L ! p) = k)"
        using gate_k p_lt by auto
      ultimately show "titems_for k (rm_closes_at rml p)
              @ (if rm_gate p \<and> ev_key (L ! p) = k
                 then [(Suc p, L ! p)] else []) = []"
        by simp
    qed
    have post: "concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
          = map (\<lambda>p. (Suc p, L ! p)) (kposs k (Suc hp) (den f))"
    proof -
      have "concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
            = concat (map (\<lambda>p. if ev_key (L ! p) = k
                               then [(Suc p, L ! p)] else [])
                      [Suc hp..<den f])"
        using closes gate_k
        by (intro arg_cong[where f = concat] map_cong) auto
      then show ?thesis
        by (simp add: concat_if_map_filter kposs_def)
    qed
    have closes_hp: "titems_for k (rm_closes_at rml hp)
          = (if k \<in> set (rml u) then [(hp, Event k (merged u k))] else [])"
      using closes[of hp] by simp
    have gate_hp: "(rm_gate hp \<and> ev_key (L ! hp) = k)
                     = (ev_key (L ! hp) = k)"
      using gate_k by auto
    have trail: "titems_for k (rm_closes_at rml (den f)) = []"
      using closes True by auto
    have kposs_peel: "kposs k hp (den f)
          = (if ev_key (L ! hp) = k then hp # kposs k (Suc hp) (den f)
             else kposs k (Suc hp) (den f))"
      unfolding kposs_def using head by simp
    have peel: "titems_for k (rm_emission_t rml s0)
            = concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [den s0..<hp])
              @ titems_for k (rm_closes_at rml hp)
              @ (if rm_gate hp \<and> ev_key (L ! hp) = k
                 then [(Suc hp, L ! hp)] else [])
              @ concat (map (\<lambda>p. titems_for k (rm_closes_at rml p)
                          @ (if rm_gate p \<and> ev_key (L ! p) = k
                             then [(Suc p, L ! p)] else []))
                    [Suc hp..<den f])
              @ titems_for k (rm_closes_at rml (den f))"
      unfolding dist by (simp add: split head)
    show ?thesis
      unfolding peel pre post trail closes_hp gate_hp
      by (simp add: kposs_peel flip: u_def hp_def)
  qed
qed

subsection \<open>Safety: any widened enumeration, any initial sink state\<close>

theorem rm_absent_replay_safe:
  assumes rml: "rml_ok2 s0 rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
  shows "state_after D0 (rm_emission rml s0) k = sink_at f k
         \<or> (state_after D0 (rm_emission rml s0) k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> rm_absent (the_unit k)
            \<and> k \<notin> set (rml (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have s0_hi: "s0 \<sqsubseteq> u_hi u" using s0hi[OF u_in] .
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)

  have master: "evs_for k (rm_emission rml s0) =
          (if k \<in> set (rml u) then [Event k (merged u k)] else [])
          @ map ((!) L) (kposs k hp (den f))"
    unfolding rm_emission_def evs_for_map_snd
    using titems_rm_emission_master2[OF rml s0hi k]
    by (simp add: u_def hp_def comp_def if_distrib map_append
             cong: if_cong)

  show ?thesis
  proof (cases "kposs k hp (den f) = []")
    case post_ne: False
    have win_lo_f: "evs_for k (win (u_lo u) f)
                      = map ((!) L) (kposs k (den (u_lo u)) (den f))"
      using evs_for_win_kposs[OF lo_f] by simp
    have kposs_lo_f_split:
        "kposs k (den (u_lo u)) (den f)
           = kposs k (den (u_lo u)) hp @ kposs k hp (den f)"
      using lo_le_hp hp_le_f by (rule kposs_split)
    have lo_f_ne: "kposs k (den (u_lo u)) (den f) \<noteq> []"
      using kposs_lo_f_split post_ne by auto
    have last_lo_f: "last (kposs k (den (u_lo u)) (den f))
                       = last (kposs k hp (den f))"
      using kposs_lo_f_split post_ne by (simp add: last_append)
    have sink: "sink_at f k = ev_img (L ! last (kposs k hp (den f)))"
      using lo_f_ne last_lo_f
      by (simp add: sink_at_def win_lo_f last_map flip: u_def)
    have stream_ne: "evs_for k (rm_emission rml s0) \<noteq> []"
      using master post_ne by auto
    have last_stream: "last (evs_for k (rm_emission rml s0))
                         = (!) L (last (kposs k hp (den f)))"
      using master post_ne by (simp add: last_append last_map)
    have "state_after D0 (rm_emission rml s0) k
            = ev_img (L ! last (kposs k hp (den f)))"
      using state_after_last_event[OF stream_ne] last_stream by simp
    then show ?thesis using sink by simp
  next
    case post_e: True
    have sink: "sink_at f k = merged u k"
      using sink_merged_post_quiet[OF k] post_e
      by (simp add: u_def hp_def)
    show ?thesis
    proof (cases "k \<in> set (rml u)")
      case True
      have "evs_for k (rm_emission rml s0) = [Event k (merged u k)]"
        using master True post_e by simp
      then have "state_after D0 (rm_emission rml s0) k = merged u k"
        by (simp add: state_after_key)
      then show ?thesis using sink by simp
    next
      case not_listed: False
      have no_evs: "evs_for k (rm_emission rml s0) = []"
        using master not_listed post_e by simp
      then have repl: "state_after D0 (rm_emission rml s0) k = D0 k"
        by (simp add: state_after_no_events)
      have not_present: "k \<notin> rm_present u"
        using rml2_present[OF rml u_in] not_listed by blast
      have merged_none: "merged u k = None"
        using not_present k_dom by (simp add: rm_present_def)
      have in_abs: "k \<in> rm_absent u"
        using k_dom merged_none by (simp add: rm_absent_def)
      have not_forced: "k \<notin> forced s0 u"
        using rml2_forced[OF rml u_in] not_listed by blast
      have held_all_e: "evs_for k (win (held_from s0 u) (u_hi u)) = []"
        using not_forced in_abs by (simp add: forced_def)
      have held_e: "evs_for k (win s0 (u_hi u)) = []"
        using evs_for_win_split[OF held_from_le_s0[of s0 u] s0_hi] held_all_e by simp
      have post_win_e: "evs_for k (win (u_hi u) f) = []"
        using evs_for_win_kposs[OF hi_f] post_e by (simp add: hp_def)
      have quiet: "evs_for k (win s0 f) = []"
        using evs_for_win_split[OF s0_hi hi_f] held_e post_win_e by simp
      show ?thesis
        using repl sink merged_none in_abs not_listed quiet
        by (simp add: u_def)
    qed
  qed
qed

corollary rm_absent_replay_empty:
  assumes rml: "rml_ok2 s0 rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
  shows "stream_replay (rm_emission rml s0) k = sink_at f k"
proof -
  have "state_after (\<lambda>_. None) (rm_emission rml s0) k = sink_at f k
        \<or> (state_after (\<lambda>_. None) (rm_emission rml s0) k = (\<lambda>_. None) k
           \<and> sink_at f k = None
           \<and> k \<in> rm_absent (the_unit k)
           \<and> k \<notin> set (rml (the_unit k))
           \<and> evs_for k (win s0 f) = [])"
    by (rule rm_absent_replay_safe[OF rml s0hi k])
  then show ?thesis
    unfolding stream_replay_def by auto
qed

subsection \<open>Convergence under coverage, and its necessity\<close>

theorem rm_self_stabilization:
  assumes rml: "rml_ok2 s0 rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and cov: "rm_covers s0 rml D0"
  shows "\<forall>k \<in> scope. state_after D0 (rm_emission rml s0) k = state_after \<sigma>0 (pfx f) k"
proof
  fix k assume k: "k \<in> scope"
  have u_in: "the_unit k \<in> set units"
    using the_unit_props(1)[OF k] .
  have disj: "state_after D0 (rm_emission rml s0) k = sink_at f k
         \<or> (state_after D0 (rm_emission rml s0) k = D0 k
            \<and> sink_at f k = None
            \<and> k \<in> rm_absent (the_unit k)
            \<and> k \<notin> set (rml (the_unit k))
            \<and> evs_for k (win s0 f) = [])"
    by (rule rm_absent_replay_safe[OF rml s0hi k])
  have "state_after D0 (rm_emission rml s0) k = sink_at f k"
    using disj
  proof
    assume "state_after D0 (rm_emission rml s0) k = sink_at f k"
    then show ?thesis .
  next
    assume orphan: "state_after D0 (rm_emission rml s0) k = D0 k
                    \<and> sink_at f k = None
                    \<and> k \<in> rm_absent (the_unit k)
                    \<and> k \<notin> set (rml (the_unit k))
                    \<and> evs_for k (win s0 f) = []"
    show ?thesis
    proof (cases "D0 k = None")
      case True
      then show ?thesis using orphan by simp
    next
      case False
      have "k \<in> set (rml (the_unit k))"
        using cov u_in orphan False unfolding rm_covers_def by blast
      with orphan show ?thesis by simp
    qed
  qed
  then show "state_after D0 (rm_emission rml s0) k = state_after \<sigma>0 (pfx f) k"
    using contract_cut[OF k] by simp
qed

theorem rm_coverage_necessary:
  assumes rml: "rml_ok2 s0 rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and conv: "\<forall>k \<in> scope. state_after D0 (rm_emission rml s0) k = state_after \<sigma>0 (pfx f) k"
  shows "rm_covers s0 rml D0"
  unfolding rm_covers_def
proof (intro ballI impI)
  fix u k
  assume u: "u \<in> set units" and ka: "k \<in> rm_absent u"
     and held: "D0 k \<noteq> None" and quiet: "evs_for k (win s0 f) = []"
  show "k \<in> set (rml u)"
  proof (rule ccontr)
    assume nl: "k \<notin> set (rml u)"
    have k_dom: "k \<in> u_dom u" and mn: "merged u k = None"
      using ka by (auto simp: rm_absent_def)
    have k_sc: "k \<in> scope" using dom_sub_scope[OF u] k_dom by auto
    have u_eq: "u = the_unit k"
      using covering_unit_unique[OF u k_dom the_unit_props(1)[OF k_sc]
                                    the_unit_props(2)[OF k_sc]] .
    have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u] .
    have s0_hi: "s0 \<sqsubseteq> u_hi u" using s0hi[OF u] .
    have post_win_e: "evs_for k (win (u_hi u) f) = []"
      using evs_for_win_split[OF s0_hi hi_f] quiet by simp
    have post_e: "kposs k (den (u_hi (the_unit k))) (den f) = []"
      using evs_for_win_kposs[OF hi_f] post_win_e u_eq by simp
    have sink: "sink_at f k = None"
      using sink_merged_post_quiet[OF k_sc post_e] mn u_eq by simp
    have "titems_for k (rm_emission_t rml s0) = []"
      using titems_rm_emission_master2[OF rml s0hi k_sc] nl post_e u_eq by simp
    then have "evs_for k (rm_emission rml s0) = []"
      unfolding rm_emission_def evs_for_map_snd by simp
    then have "state_after D0 (rm_emission rml s0) k = D0 k"
      by (simp add: state_after_no_events)
    moreover have "state_after D0 (rm_emission rml s0) k = state_after \<sigma>0 (pfx f) k"
      using conv k_sc by blast
    moreover have "state_after \<sigma>0 (pfx f) k = None"
      using contract_cut[OF k_sc] sink by simp
    ultimately show False using held by simp
  qed
qed

subsection \<open>The forced keys are the keys whose held-back events end in a delete\<close>

lemma forced_char:
  assumes u_in: "u \<in> set units"
  shows "k \<in> forced s0 u \<longleftrightarrow>
           k \<in> u_dom u \<and> evs_for k (win (held_from s0 u) (u_hi u)) \<noteq> [] \<and>
           ev_img (last (evs_for k (win (held_from s0 u) (u_hi u)))) = None"
proof -
  have hf_hi: "held_from s0 u \<sqsubseteq> u_hi u"
    using held_from_le_lo[of s0 u] bracket_lo_hi[OF u_in] by (rule cle_trans)
  have key: "merged u k = ev_img (last (evs_for k (win (held_from s0 u) (u_hi u))))"
    if k_dom: "k \<in> u_dom u" and ne: "evs_for k (win (held_from s0 u) (u_hi u)) \<noteq> []"
  proof -
    have split: "evs_for k (pfx (u_hi u)) =
                   evs_for k (pfx (held_from s0 u)) @ evs_for k (win (held_from s0 u) (u_hi u))"
      by (rule evs_for_pfx_split[OF hf_hi])
    have pne: "evs_for k (pfx (u_hi u)) \<noteq> []"
      using split ne by auto
    have "merged u k = state_after \<sigma>0 (pfx (u_hi u)) k"
      by (rule merged_at_hi[OF u_in k_dom])
    also have "\<dots> = ev_img (last (evs_for k (pfx (u_hi u))))"
      by (rule state_after_last_event[OF pne])
    also have "\<dots> = ev_img (last (evs_for k (win (held_from s0 u) (u_hi u))))"
      using split ne by (simp add: last_append)
    finally show ?thesis .
  qed
  show ?thesis
    using key by (auto simp: forced_def rm_absent_def)
qed

subsection \<open>Existence for a finite sink and finitely many present keys\<close>

lemma forced_finite: "finite (forced s0 u)"
proof -
  have "forced s0 u \<subseteq> ev_key ` set (win (held_from s0 u) (u_hi u))"
    by (auto simp: forced_def evs_for_def filter_empty_conv)
  then show ?thesis by (rule finite_subset) simp
qed

lemma rml2_exists_covering:
  assumes fin_present: "\<And>u. u \<in> set units \<Longrightarrow> finite (rm_present u)"
      and fin_sink: "finite {k. D0 k \<noteq> None}"
  shows "\<exists>rml. rml_ok2 s0 rml \<and> rm_covers s0 rml D0"
proof -
  define S where
    "S = (\<lambda>u. rm_present u \<union> forced s0 u \<union> {k \<in> rm_absent u. D0 k \<noteq> None})"
  have finS: "finite (S u)" if u: "u \<in> set units" for u
  proof -
    have "{k \<in> rm_absent u. D0 k \<noteq> None} \<subseteq> {k. D0 k \<noteq> None}" by auto
    then have "finite {k \<in> rm_absent u. D0 k \<noteq> None}"
      using fin_sink by (rule finite_subset)
    then show ?thesis
      using fin_present[OF u] forced_finite by (simp add: S_def)
  qed
  define rml where "rml = (\<lambda>u. SOME xs. distinct xs \<and> set xs = S u)"
  have rml_u: "distinct (rml u) \<and> set (rml u) = S u" if u: "u \<in> set units" for u
  proof -
    have "\<exists>xs. distinct xs \<and> set xs = S u"
      using finite_distinct_list[OF finS[OF u]] by metis
    then show ?thesis unfolding rml_def by (rule someI_ex)
  qed
  have S_dom: "S u \<subseteq> u_dom u" for u
    by (auto simp: S_def rm_present_def forced_def rm_absent_def)
  have ok: "rml_ok2 s0 rml"
    unfolding rml_ok2_def
  proof
    fix u assume u: "u \<in> set units"
    show "distinct (rml u) \<and> rm_present u \<union> forced s0 u \<subseteq> set (rml u) \<and>
          set (rml u) \<subseteq> u_dom u"
      using rml_u[OF u] S_dom[of u] by (auto simp: S_def)
  qed
  have cov: "rm_covers s0 rml D0"
    unfolding rm_covers_def
  proof (intro ballI impI)
    fix u k
    assume u: "u \<in> set units" and ka: "k \<in> rm_absent u" and held: "D0 k \<noteq> None"
       and "evs_for k (win s0 f) = []"
    show "k \<in> set (rml u)"
      using rml_u[OF u] ka held by (auto simp: S_def)
  qed
  show ?thesis using ok cov by blast
qed

theorem range_merge_record_converges:
  assumes s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and fin_present: "\<And>u. u \<in> set units \<Longrightarrow> finite (rm_present u)"
      and fin_sink: "finite {k. D0 k \<noteq> None}"
  shows "\<exists>rml. rml_ok2 s0 rml \<and>
           (\<forall>k \<in> scope. state_after D0 (rm_emission rml s0) k = state_after \<sigma>0 (pfx f) k)"
proof -
  obtain rml where ok: "rml_ok2 s0 rml" and cov: "rm_covers s0 rml D0"
    using rml2_exists_covering[OF fin_present fin_sink] by blast
  then show ?thesis
    using rm_self_stabilization[OF ok s0hi cov] by blast
qed

subsection \<open>The core's enumeration keeps an unlisted quiet key\<close>

text \<open>
  With the core's enumeration (@{text rml_ok}: exactly the present keys), a
  key that is not listed and has no event from its unit's high edge on keeps
  its initial sink value. The fixtures below use this to show what the forced
  deletes add.
\<close>

lemma rm_unlisted_quiet_kept:
  assumes rml: "rml_ok rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
      and unlisted: "k \<notin> set (rml (the_unit k))"
      and post: "kposs k (den (u_hi (the_unit k))) (den f) = []"
  shows "state_after D0 (rm_emission rml s0) k = D0 k"
proof -
  have "titems_for k (rm_emission_t rml s0) = []"
    using titems_rm_emission_master[OF rml s0hi k] unlisted post by simp
  then have "evs_for k (rm_emission rml s0) = []"
    unfolding rm_emission_def evs_for_map_snd by simp
  then show ?thesis by (simp add: state_after_no_events)
qed

end  (* context capture_contract *)

subsection \<open>Fixtures: a held-back delete before the window and inside it\<close>

text \<open>
  One log with a single delete of key 1, at position 0; the source holds key 1
  with value 5 before it, and so does the sink, which is in sync when the pass
  starts at coordinate 0. In the first fixture the chunk reads key 1 after the
  delete (bracket from 1 to 1), so the delete lies before the window; in the
  second the chunk reads before the delete (bracket from 0 to 1), so the
  window absorbs it. Either way key 1 is absent from the merged image and
  forced. The core's enumeration lists only present keys, so key 1 is not
  listed and the sink keeps the deleted row. Listing the forced key repairs
  it. A rule that re-emits only the deletes the window absorbed lists nothing
  in the first fixture. The second fixture is also run with the stream
  starting at the chunk's close (consumption start 1), after the delete: the
  window merges the delete, the stream never carries it, and key 1 is still
  forced. A rule that re-emits only the deletes the stream carried lists
  nothing there.
\<close>

definition L_f :: "(nat, nat) event list" where
  "L_f = [Event 1 None]"

definition den_f :: "nat \<Rightarrow> nat" where
  "den_f c = min c 1"

definition src_f :: "(nat, nat) state" where
  "src_f = (\<lambda>k. if k = 1 then Some 5 else None)"

interpretation fsc: coordinate_space L_f den_f
  by unfold_locales (simp add: den_f_def L_f_def)

definition pre_unit :: "(nat, nat, nat) cunit" where
  "pre_unit = \<lparr>u_dom = {1}, u_lo = 1, u_hi = 1, u_refresh = (\<lambda>_. None)\<rparr>"

definition inw_unit :: "(nat, nat, nat) cunit" where
  "inw_unit = \<lparr>u_dom = {1}, u_lo = 0, u_hi = 1, u_refresh = src_f\<rparr>"

interpretation pre: capture_contract L_f den_f src_f "[pre_unit]" "{1}" 1
proof (unfold_locales)
  show "(\<Union>u\<in>set [pre_unit]. u_dom u) = {1}"
    by (simp add: pre_unit_def)
next
  fix i j
  assume "i < length [pre_unit]" "j < length [pre_unit]" "i \<noteq> j"
  then show "u_dom ([pre_unit] ! i) \<inter> u_dom ([pre_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [pre_unit]"
  then show "fsc.cle (u_lo u) (u_hi u)"
    by (simp add: pre_unit_def fsc.cle_def den_f_def)
next
  fix u assume "u \<in> set [pre_unit]"
  then show "fsc.cle (u_hi u) 1"
    by (simp add: pre_unit_def fsc.cle_def den_f_def)
next
  fix u k assume "u \<in> set [pre_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. fsc.cle (u_lo u) c \<and> fsc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after src_f (fsc.pfx c) k"
    unfolding fsc.cle_def fsc.pfx_def
    by (intro exI[of _ 1])
       (auto simp add: pre_unit_def den_f_def L_f_def src_f_def state_after_def apply_ev_def)
qed

interpretation inw: capture_contract L_f den_f src_f "[inw_unit]" "{1}" 1
proof (unfold_locales)
  show "(\<Union>u\<in>set [inw_unit]. u_dom u) = {1}"
    by (simp add: inw_unit_def)
next
  fix i j
  assume "i < length [inw_unit]" "j < length [inw_unit]" "i \<noteq> j"
  then show "u_dom ([inw_unit] ! i) \<inter> u_dom ([inw_unit] ! j) = {}" by simp
next
  fix u assume "u \<in> set [inw_unit]"
  then show "fsc.cle (u_lo u) (u_hi u)"
    by (simp add: inw_unit_def fsc.cle_def den_f_def)
next
  fix u assume "u \<in> set [inw_unit]"
  then show "fsc.cle (u_hi u) 1"
    by (simp add: inw_unit_def fsc.cle_def den_f_def)
next
  fix u k assume "u \<in> set [inw_unit]" and "k \<in> u_dom u"
  then show "\<exists>c. fsc.cle (u_lo u) c \<and> fsc.cle c (u_hi u) \<and>
                 u_refresh u k = state_after src_f (fsc.pfx c) k"
    unfolding fsc.cle_def fsc.pfx_def
    by (intro exI[of _ 0])
       (auto simp add: inw_unit_def den_f_def L_f_def src_f_def state_after_def apply_ev_def)
qed

lemma fix_src_at_1: "state_after src_f (fsc.pfx 1) 1 = None"
  unfolding fsc.pfx_def
  by (simp add: den_f_def L_f_def src_f_def state_after_def apply_ev_def)

lemma fix_win_pre: "evs_for 1 (fsc.win 1 1) = []"
  unfolding fsc.win_def by (simp add: den_f_def L_f_def evs_for_def)

lemma fix_win_inw: "evs_for 1 (fsc.win 0 1) = [Event 1 None]"
  unfolding fsc.win_def by (simp add: den_f_def L_f_def evs_for_def)

lemma fix_post_quiet: "fsc.kposs 1 (den_f 1) (den_f 1) = []"
  unfolding fsc.kposs_def by simp

lemma pre_the_unit: "pre.the_unit 1 = pre_unit"
  using pre.the_unit_props[of 1] by simp

lemma inw_the_unit: "inw.the_unit 1 = inw_unit"
  using inw.the_unit_props[of 1] by simp

lemma pre_merged: "pre.merged pre_unit 1 = None"
  using fix_win_pre by (simp add: pre.merged_def pre_unit_def)

lemma inw_merged: "inw.merged inw_unit 1 = None"
  using fix_win_inw by (simp add: inw.merged_def inw_unit_def)

lemma pre_present: "pre.rm_present pre_unit = {}"
  using pre_merged by (auto simp: pre.rm_present_def pre_unit_def)

lemma inw_present: "inw.rm_present inw_unit = {}"
  using inw_merged by (auto simp: inw.rm_present_def inw_unit_def)

lemma pre_forced: "pre.forced 0 pre_unit = {1}"
  using pre_merged fix_win_inw
  by (auto simp: pre.forced_def pre.held_from_def den_f_def pre.rm_absent_def pre_unit_def)

lemma inw_forced: "inw.forced 0 inw_unit = {1}"
  using inw_merged fix_win_inw
  by (auto simp: inw.forced_def inw.held_from_def den_f_def inw.rm_absent_def inw_unit_def)

lemma inw_forced_late: "inw.forced 1 inw_unit = {1}"
  using inw_merged fix_win_inw
  by (auto simp: inw.forced_def inw.held_from_def den_f_def inw.rm_absent_def inw_unit_def)

lemma pre_s0hi: "\<And>u. u \<in> set [pre_unit] \<Longrightarrow> fsc.cle 0 (u_hi u)"
  by (simp add: pre_unit_def fsc.cle_def den_f_def)

lemma inw_s0hi: "\<And>u. u \<in> set [inw_unit] \<Longrightarrow> fsc.cle 0 (u_hi u)"
  by (simp add: inw_unit_def fsc.cle_def den_f_def)

lemma inw_s0hi_late: "\<And>u. u \<in> set [inw_unit] \<Longrightarrow> fsc.cle 1 (u_hi u)"
  by (simp add: inw_unit_def fsc.cle_def den_f_def)

text \<open>The core's enumeration lists no key, and the sink keeps the deleted row.\<close>

lemma pre_rml_ok_core: "pre.rml_ok (\<lambda>_. [])"
  using pre_present by (simp add: pre.rml_ok_def)

lemma inw_rml_ok_core: "inw.rml_ok (\<lambda>_. [])"
  using inw_present by (simp add: inw.rml_ok_def)

lemma wit_pre_core_keeps_row:
  "state_after src_f (pre.rm_emission (\<lambda>_. []) 0) 1 = Some 5"
proof -
  have "state_after src_f (pre.rm_emission (\<lambda>_. []) 0) 1 = src_f 1"
  proof -
    have post: "fsc.kposs 1 (den_f (u_hi (pre.the_unit 1))) (den_f 1) = []"
      unfolding pre_the_unit by (simp add: pre_unit_def fsc.kposs_def)
    show ?thesis
      by (rule pre.rm_unlisted_quiet_kept[OF pre_rml_ok_core pre_s0hi _ _ post]) simp_all
  qed
  then show ?thesis by (simp add: src_f_def)
qed

lemma wit_inw_core_keeps_row:
  "state_after src_f (inw.rm_emission (\<lambda>_. []) 0) 1 = Some 5"
proof -
  have "state_after src_f (inw.rm_emission (\<lambda>_. []) 0) 1 = src_f 1"
  proof -
    have post: "fsc.kposs 1 (den_f (u_hi (inw.the_unit 1))) (den_f 1) = []"
      unfolding inw_the_unit by (simp add: inw_unit_def fsc.kposs_def)
    show ?thesis
      by (rule inw.rm_unlisted_quiet_kept[OF inw_rml_ok_core inw_s0hi _ _ post]) simp_all
  qed
  then show ?thesis by (simp add: src_f_def)
qed

lemma wit_inw_late_core_keeps_row:
  "state_after src_f (inw.rm_emission (\<lambda>_. []) 1) 1 = Some 5"
proof -
  have "state_after src_f (inw.rm_emission (\<lambda>_. []) 1) 1 = src_f 1"
  proof -
    have post: "fsc.kposs 1 (den_f (u_hi (inw.the_unit 1))) (den_f 1) = []"
      unfolding inw_the_unit by (simp add: inw_unit_def fsc.kposs_def)
    show ?thesis
      by (rule inw.rm_unlisted_quiet_kept[OF inw_rml_ok_core inw_s0hi_late _ _ post]) simp_all
  qed
  then show ?thesis by (simp add: src_f_def)
qed

text \<open>
  With the stream starting at the chunk's close, the rule still forces key 1,
  so the core's enumeration does not satisfy it.
\<close>

lemma inw_late_core_not_ok2: "\<not> inw.rml_ok2 1 (\<lambda>_. [])"
  unfolding inw.rml_ok2_def using inw_forced_late by auto

text \<open>Listing the forced key, as the rule requires, repairs the row.\<close>

lemma pre_rml_ok2: "pre.rml_ok2 0 (\<lambda>_. [1])"
  unfolding pre.rml_ok2_def
  using pre_present pre_forced by (simp add: pre_unit_def)

lemma inw_rml_ok2: "inw.rml_ok2 0 (\<lambda>_. [1])"
  unfolding inw.rml_ok2_def
  using inw_present inw_forced by (simp add: inw_unit_def)

lemma pre_covers: "pre.rm_covers 0 (\<lambda>_. [1]) src_f"
  unfolding pre.rm_covers_def by (auto simp: pre.rm_absent_def pre_unit_def)

lemma inw_covers: "inw.rm_covers 0 (\<lambda>_. [1]) src_f"
  unfolding inw.rm_covers_def by (auto simp: inw.rm_absent_def inw_unit_def)

lemma wit_pre_forced_repairs:
  "state_after src_f (pre.rm_emission (\<lambda>_. [1]) 0) 1 = None"
  using pre.rm_self_stabilization[OF pre_rml_ok2 pre_s0hi pre_covers] fix_src_at_1 by simp

lemma wit_inw_forced_repairs:
  "state_after src_f (inw.rm_emission (\<lambda>_. [1]) 0) 1 = None"
  using inw.rm_self_stabilization[OF inw_rml_ok2 inw_s0hi inw_covers] fix_src_at_1 by simp

lemma inw_rml_ok2_late: "inw.rml_ok2 1 (\<lambda>_. [1])"
  unfolding inw.rml_ok2_def
  using inw_present inw_forced_late by (simp add: inw_unit_def)

lemma inw_covers_late: "inw.rm_covers 1 (\<lambda>_. [1]) src_f"
  unfolding inw.rm_covers_def by (auto simp: inw.rm_absent_def inw_unit_def)

lemma wit_inw_late_forced_repairs:
  "state_after src_f (inw.rm_emission (\<lambda>_. [1]) 1) 1 = None"
  using inw.rm_self_stabilization[OF inw_rml_ok2_late inw_s0hi_late inw_covers_late] fix_src_at_1
  by simp

end
