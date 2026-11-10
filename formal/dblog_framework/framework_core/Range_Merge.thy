(*  Title:   Range_Merge.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Range_Merge
  imports Merge_Disciplines
begin

section \<open>The buffered-range-merge discipline\<close>

text \<open>
  The second real merge discipline of the equivalence catalog, and the
  engine of the parallel-chunks instance: read the unit's
  window events and \<^emph>\<open>upsert\<close> them onto the refresh buffer, then emit
  the merged unit ONCE when the window closes. The Flink CDC shape:
  ``Upsert the read binlog records into the buffered chunk records,
  and emit all records in the buffer as final output'' --- all as
  INSERT records, denoting row state as of the chunk's high watermark.

  The equivalence obligation is discharged under two clauses:

    \<^item> \<^bold>\<open>(a) withholding\<close>: the unit's keys are withheld from stream
      emission over \<open>(s\<^sub>0, hi\<^sub>i]\<close> --- the merged unit is their sole
      pre-\<open>hi\<^sub>i\<close> emission. Formalized by the gate @{text rm_gate}: a
      scoped event passes to the stream only at-or-after its covering
      unit's high edge. Without this clause a pre-\<open>lo\<^sub>i\<close> event for a
      later-deleted key replays to the wrong value; the fixture at the
      end of this theory exhibits exactly that failure, so the clause
      is load-bearing, not decorative.
    \<^item> \<^bold>\<open>(b) value-or-absence at the high edge\<close>: the merged unit
      denotes value-or-absence AT \<open>hi\<^sub>i\<close> per key --- the key's LAST
      in-window event decides (@{text merged}), so a
      delete-then-reinsert key is present again and emits normally.
      Keys absent at \<open>hi\<^sub>i\<close> are emitted ZERO times; under the
      empty-map stream-replay convention (@{const stream_replay})
      zero-emission IS the absence result.
      Theorem @{text merged_at_hi} makes clause (b) exact: the merged
      buffer equals the source state at the unit's high edge, key by
      key.

  The discipline's observability premise differs from window-discard's
  in a way worth naming: window-discard consumes a single pass from
  \<open>s\<^sub>0 \<sqsubseteq> lo\<^sub>i\<close>, while range-merge reads each window by a RANGED
  backfill (``read the binlog records that belong to the snapshot
  chunk from LOW offset to HIGH offset'' --- coordinate-addressable
  access, the S-OBS retention requirement), so the
  STREAM only needs \<open>s\<^sub>0 \<sqsubseteq> hi\<^sub>i\<close>: everything below a unit's high
  edge that the stream would contribute is withheld by clause (a)
  anyway, and the window content enters through the buffer. The
  theorems below therefore take the weaker premise
  \<open>s\<^sub>0 \<sqsubseteq> u_hi u\<close> --- the formal content of the handoff condition the
  parallel-chunks instance names as an assumption.

  Same @{text sink} under (a)+(b); DIFFERENT emitted stream: the
  window-discard emission interleaves a unit's in-window events at
  their own positions, the range-merge emission absorbs them into one
  merged block. Both replay to the canonical @{text sink_at} at the
  frontier, which is the point of the equivalence requirement.
\<close>

subsection \<open>List auxiliary\<close>

lemma concat_map_nil:
  "(\<And>x. x \<in> set xs \<Longrightarrow> g x = []) \<Longrightarrow> concat (map g xs) = []"
  by (induction xs) auto

subsection \<open>The merged buffer and the gated emission\<close>

context capture_plan
begin

text \<open>
  The buffer after the backfill upsert: the key's last in-window event
  decides; a window-quiet key keeps its read result. Present keys
  of a unit (@{text rm_present}) are the rows the discipline emits at
  the close; like the window-discard emission, the close takes a
  duplicate-free ENUMERATION @{text rml} of each unit's present set
  (real captures emit rows physically, so one always exists ---
  @{text rml_exists} below).
\<close>

definition merged :: "('k, 'v, 'c) cunit \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "merged u k =
     (if evs_for k (win (u_lo u) (u_hi u)) = []
      then u_refresh u k
      else ev_img (last (evs_for k (win (u_lo u) (u_hi u)))))"

definition rm_present :: "('k, 'v, 'c) cunit \<Rightarrow> 'k set" where
  "rm_present u = {k \<in> u_dom u. merged u k \<noteq> None}"

definition rml_ok :: "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> bool" where
  "rml_ok rml \<longleftrightarrow>
     (\<forall>u \<in> set units. distinct (rml u) \<and> set (rml u) = rm_present u)"

definition rm_close_block ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> ('k, 'v, 'c) cunit
       \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "rm_close_block rml u =
     map (\<lambda>k. (den (u_hi u), Event k (merged u k))) (rml u)"

definition rm_closes_at ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> nat \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "rm_closes_at rml p =
     concat (map (\<lambda>i. if den (u_hi (units ! i)) = p
                      then rm_close_block rml (units ! i) else [])
                 [0..<length units])"

text \<open>
  Clause (a) as a per-position gate: an event whose key is in scope
  passes to the stream only at-or-after its covering unit's high edge;
  out-of-scope events pass unconditionally (they never bear on the
  scoped claim).
\<close>

definition rm_gate :: "nat \<Rightarrow> bool" where
  "rm_gate p \<longleftrightarrow>
     (ev_key (L ! p) \<in> scope \<longrightarrow> den (u_hi (the_unit (ev_key (L ! p)))) \<le> p)"

definition rm_emission_t ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c \<Rightarrow> (nat \<times> ('k, 'v) event) list" where
  "rm_emission_t rml s0 =
     concat (map (\<lambda>p. rm_closes_at rml p
                        @ (if rm_gate p then [(Suc p, L ! p)] else []))
                 [den s0..<den f])
     @ rm_closes_at rml (den f)"

definition rm_emission ::
    "(('k, 'v, 'c) cunit \<Rightarrow> 'k list) \<Rightarrow> 'c \<Rightarrow> ('k, 'v) event list" where
  "rm_emission rml s0 = map snd (rm_emission_t rml s0)"

end  (* context capture_plan *)

subsection \<open>Clause (b): the merged buffer is the state at the high edge\<close>

context capture_contract
begin

lemma rm_present_sub_dom: "rm_present u \<subseteq> u_dom u"
  by (auto simp: rm_present_def)

lemma rml_exists:
  assumes fin: "\<And>u. u \<in> set units \<Longrightarrow> finite (rm_present u)"
  shows "\<exists>rml. rml_ok rml"
proof -
  define rml where
    "rml = (\<lambda>u. SOME xs. distinct xs \<and> set xs = rm_present u)"
  have "distinct (rml u) \<and> set (rml u) = rm_present u"
    if u: "u \<in> set units" for u
  proof -
    have "\<exists>xs. distinct xs \<and> set xs = rm_present u"
      using finite_distinct_list[OF fin[OF u]] by metis
    then show ?thesis
      unfolding rml_def by (rule someI_ex)
  qed
  then have "rml_ok rml"
    by (simp add: rml_ok_def)
  then show ?thesis by blast
qed

theorem merged_at_hi:
  assumes u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
  shows "merged u k = state_after \<sigma>0 (pfx (u_hi u)) k"
proof (cases "evs_for k (win (u_lo u) (u_hi u)) = []")
  case True
  from O2_honest[OF u_in k_dom] obtain c where
    c_lo: "u_lo u \<sqsubseteq> c" and c_hi: "c \<sqsubseteq> u_hi u" and
    honest: "u_refresh u k = state_after \<sigma>0 (pfx c) k"
    by blast
  have "merged u k = u_refresh u k"
    using True by (simp add: merged_def)
  also have "\<dots> = state_after \<sigma>0 (pfx c) k"
    by (rule honest)
  also have "\<dots> = state_after \<sigma>0 (pfx (u_lo u)) k"
    by (rule win_invariant_state[OF c_lo c_hi True])
  also have "\<dots> = state_after \<sigma>0 (pfx (u_hi u)) k"
    by (rule win_invariant_state[OF bracket_lo_hi[OF u_in] cle_refl True,
                                 symmetric])
  finally show ?thesis .
next
  case False
  have split: "evs_for k (pfx (u_hi u)) =
                 evs_for k (pfx (u_lo u)) @ evs_for k (win (u_lo u) (u_hi u))"
    by (rule evs_for_pfx_split[OF bracket_lo_hi[OF u_in]])
  have ne: "evs_for k (pfx (u_hi u)) \<noteq> []"
    using split False by auto
  have "merged u k = ev_img (last (evs_for k (win (u_lo u) (u_hi u))))"
    using False by (simp add: merged_def)
  also have "\<dots> = ev_img (last (evs_for k (pfx (u_hi u))))"
    using split False by (simp add: last_append)
  also have "\<dots> = state_after \<sigma>0 (pfx (u_hi u)) k"
    by (rule state_after_last_event[OF ne, symmetric])
  finally show ?thesis .
qed

subsection \<open>Per-key characterization of the gated emission\<close>

lemma titems_rm_close_block:
  assumes rml: "rml_ok rml" and u_in: "u \<in> set units"
  shows "titems_for k (rm_close_block rml u) =
           (if k \<in> set (rml u)
            then [(den (u_hi u), Event k (merged u k))] else [])"
proof -
  have dis: "distinct (rml u)"
    using rml u_in by (simp add: rml_ok_def)
  have "titems_for k (rm_close_block rml u) =
          map (\<lambda>k'. (den (u_hi u), Event k' (merged u k')))
              (filter (\<lambda>k'. k' = k) (rml u))"
    by (simp add: titems_for_def rm_close_block_def filter_map comp_def)
  then show ?thesis
    using distinct_filter_eq[OF dis] by simp
qed

lemma titems_rm_closes_at:
  assumes rml: "rml_ok rml" and k: "k \<in> scope"
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
      then have "k \<in> rm_present (units ! i)"
        using rml ui_in by (simp add: rml_ok_def)
      then have "k \<in> u_dom (units ! i)"
        using rm_present_sub_dom by auto
      then have eq: "units ! i = the_unit k"
        using covering_unit_unique[OF ui_in _ the_unit_props(1)[OF k]
                                       the_unit_props(2)[OF k]] by blast
      have "i = i0"
        by (rule the_unit_position_unique[OF k i eq i0(1) i0(2)])
      with ne show False ..
    qed
    then show ?thesis
      using titems_rm_close_block[OF rml ui_in]
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
    using titems_rm_close_block[OF rml the_unit_props(1)[OF k]] i0(2)
    by (simp add: titems_for_def)
qed

text \<open>
  The master characterization: a key's occurrences in the gated
  emission are its unit's merged entry at the close position (iff the
  key is present at the high edge), then its post-close events ---
  nothing else. All pre-close stream occurrences are withheld by
  clause (a). The equivalence and the monotonicity claim both read off
  this shape.
\<close>

lemma titems_rm_emission_master:
  assumes rml: "rml_ok rml"
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
    using titems_rm_closes_at[OF rml k] by (simp add: u_def hp_def)

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

subsection \<open>The range-merge equivalence theorem\<close>

text \<open>
  When a key sees no post-close event, the canonical replay value IS
  the merged result --- the bridge between the discipline's buffer
  and the fold.
\<close>

lemma sink_merged_post_quiet:
  assumes k: "k \<in> scope"
      and post: "kposs k (den (u_hi (the_unit k))) (den f) = []"
  shows "sink_at f k = merged (the_unit k) k"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units"
    using the_unit_props(1)[OF k] u_def by simp
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)
  have post': "kposs k hp (den f) = []"
    using post by (simp add: u_def hp_def)
  have win_lo_f: "evs_for k (win (u_lo u) f)
                    = map ((!) L) (kposs k (den (u_lo u)) (den f))"
    using evs_for_win_kposs[OF lo_f] by simp
  have win_lo_hi: "evs_for k (win (u_lo u) (u_hi u))
                     = map ((!) L) (kposs k (den (u_lo u)) hp)"
    using evs_for_win_kposs[OF lo_hi] by (simp add: hp_def)
  have kposs_collapse: "kposs k (den (u_lo u)) (den f)
                          = kposs k (den (u_lo u)) hp"
    using kposs_split[OF lo_le_hp hp_le_f] post' by simp
  show ?thesis
  proof (cases "kposs k (den (u_lo u)) hp = []")
    case True
    have "sink_at f k = u_refresh u k"
      using True kposs_collapse
      by (simp add: sink_at_def win_lo_f flip: u_def)
    moreover have "merged u k = u_refresh u k"
      using True win_lo_hi by (simp add: merged_def)
    ultimately show ?thesis by (simp add: u_def)
  next
    case False
    have "sink_at f k = ev_img (last (evs_for k (win (u_lo u) f)))"
      using False kposs_collapse
      by (simp add: sink_at_def win_lo_f flip: u_def)
    also have "\<dots> = ev_img (L ! last (kposs k (den (u_lo u)) hp))"
      using win_lo_f kposs_collapse False by (simp add: last_map)
    also have "\<dots> = ev_img (last (evs_for k (win (u_lo u) (u_hi u))))"
      using win_lo_hi False by (simp add: last_map)
    also have "\<dots> = merged u k"
      using False win_lo_hi by (simp add: merged_def)
    finally show ?thesis by (simp add: u_def)
  qed
qed

text \<open>
  Buffered-range-merge equivalence: under clauses (a) and (b) the
  gated emission replays to the canonical @{text sink} on the scope.
  Together with @{text contract_cut} this covers the Flink-shaped
  capture: upsert the window onto the buffer, emit the merged unit
  once, stream only above the high edge --- and the replay is exactly
  the source state at the frontier.
\<close>

theorem range_merge_replay:
  assumes rml: "rml_ok rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
  shows "stream_replay (rm_emission rml s0) k = sink_at f k"
proof -
  define u where "u = the_unit k"
  define hp where "hp = den (u_hi u)"
  have u_in: "u \<in> set units" and k_dom: "k \<in> u_dom u"
    using the_unit_props[OF k] u_def by auto
  have lo_hi: "u_lo u \<sqsubseteq> u_hi u" using bracket_lo_hi[OF u_in] .
  have hi_f: "u_hi u \<sqsubseteq> f" using bracket_hi_f[OF u_in] .
  have lo_f: "u_lo u \<sqsubseteq> f" using lo_hi hi_f by (rule cle_trans)
  have lo_le_hp: "den (u_lo u) \<le> hp"
    using lo_hi by (simp add: cle_def hp_def)
  have hp_le_f: "hp \<le> den f"
    using hi_f by (simp add: cle_def hp_def)

  have present_iff: "k \<in> set (rml u) \<longleftrightarrow> merged u k \<noteq> None"
    using rml u_in k_dom by (auto simp: rml_ok_def rm_present_def)

  have master: "evs_for k (rm_emission rml s0) =
          (if k \<in> set (rml u) then [Event k (merged u k)] else [])
          @ map ((!) L) (kposs k hp (den f))"
    unfolding rm_emission_def evs_for_map_snd
    using titems_rm_emission_master[OF rml s0hi k]
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
    have "stream_replay (rm_emission rml s0) k
            = ev_img (L ! last (kposs k hp (den f)))"
      unfolding stream_replay_def
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
      then have "stream_replay (rm_emission rml s0) k = merged u k"
        unfolding stream_replay_def by (simp add: state_after_key)
      then show ?thesis using sink by simp
    next
      case False
      have "evs_for k (rm_emission rml s0) = []"
        using master False post_e by simp
      then have "stream_replay (rm_emission rml s0) k = None"
        unfolding stream_replay_def by (simp add: state_after_no_events)
      moreover have "merged u k = None"
        using present_iff False by simp
      ultimately show ?thesis using sink by simp
    qed
  qed
qed

subsection \<open>Range-merge per-key monotonicity\<close>

text \<open>
  The gated emission is per-key monotone by construction: a key emits
  its merged entry at the close, then its post-close events in commit
  order --- never an older state over a newer one. This is the
  ``all as INSERT records'' emission shape with the during-replay
  monotonicity proved separately for each discipline.
\<close>

theorem range_merge_monotone:
  assumes rml: "rml_ok rml"
      and s0hi: "\<And>u. u \<in> set units \<Longrightarrow> s0 \<sqsubseteq> u_hi u"
      and k: "k \<in> scope"
  shows "sorted (map fst (titems_for k (rm_emission_t rml s0)))"
proof -
  define hp where "hp = den (u_hi (the_unit k))"
  have m: "map fst (titems_for k (rm_emission_t rml s0)) =
        (if k \<in> set (rml (the_unit k)) then [hp] else [])
        @ map Suc (kposs k hp (den f))"
    using titems_rm_emission_master[OF rml s0hi k]
    by (cases "k \<in> set (rml (the_unit k))") (simp_all add: hp_def comp_def)
  have s_post: "sorted (map Suc (kposs k hp (den f)))"
    by (simp add: sorted_map_Suc kposs_sorted)
  have post_ge: "\<And>b. b \<in> set (map Suc (kposs k hp (den f))) \<Longrightarrow> hp \<le> b"
    using kposs_bounds by (auto intro: le_SucI)
  show ?thesis
  proof (cases "k \<in> set (rml (the_unit k))")
    case True
    have "sorted (hp # map Suc (kposs k hp (den f)))"
      using s_post post_ge by auto
    then show ?thesis using m True by simp
  next
    case False
    then show ?thesis using m s_post by simp
  qed
qed

end  (* context capture_contract *)

subsection \<open>Scalar offset coordinates (shared by the offset instances)\<close>

text \<open>
  The parallel-chunks and dump-splice instances both run over scalar
  log offsets (binlog positions, LSN-class coordinates). The shared
  denotation: an offset denotes the prefix of that length, capped at
  the committed history --- on every offset a plan actually uses
  (all at-or-below the frontier, hence in range) the cap is the
  identity, and comparisons agree with the denotational \<open>\<sqsubseteq>\<close>
  (@{text offden_le_iff}); the operational-fidelity requirement is
  discharged per instance from exactly these two facts.
\<close>

definition offden :: "('k, 'v) event list \<Rightarrow> nat \<Rightarrow> nat" where
  "offden L c = min c (length L)"

lemma offden_le_len: "offden L c \<le> length L"
  by (simp add: offden_def)

lemma offden_id: "c \<le> length L \<Longrightarrow> offden L c = c"
  by (simp add: offden_def)

lemma offden_mono: "a \<le> b \<Longrightarrow> offden L a \<le> offden L b"
  by (simp add: offden_def)

lemma offden_le_iff:
  "a \<le> length L \<Longrightarrow> b \<le> length L \<Longrightarrow> (offden L a \<le> offden L b) = (a \<le> b)"
  by (simp add: offden_def)

subsection \<open>Necessity of the withholding clause (a) --- fixture\<close>

text \<open>
  The withholding counterexample: a pre-\<open>lo\<close> event for
  a later-deleted key. The log inserts key 1 and then deletes it
  inside the unit's window; the refresh (read before the delete) is
  valid in-bracket; the merged buffer is empty at the high edge
  (clause (b): the last in-window event is the delete), so the lawful
  gated emission is EMPTY and replays to the correct absence result.
  A variant WITHOUT clause (a) passes the pre-\<open>lo\<close> insert to the
  stream while the in-window delete is still absorbed into the buffer
  --- its stream is @{term "[Event 1 (Some 5)] :: (nat, nat) event list"},
  replaying key 1 to a value the source no longer has. The withholding
  clause is what stands between the discipline and that failure.
\<close>

definition L_a :: "(nat, nat) event list" where
  "L_a = [Event 1 (Some 5), Event 1 None]"

definition den_a :: "nat \<Rightarrow> nat" where
  "den_a c = min c 2"

definition unit_a :: "(nat, nat, nat) cunit" where
  "unit_a = \<lparr>u_dom = {1}, u_lo = 1, u_hi = 2,
             u_refresh = (\<lambda>k. if k = 1 then Some 5 else None)\<rparr>"

interpretation acs: coordinate_space L_a den_a
  by unfold_locales (simp add: den_a_def L_a_def)

interpretation rma: capture_contract L_a den_a "\<lambda>_. None" "[unit_a]" "{1}" 2
proof (unfold_locales)
  show "(\<Union>u\<in>set [unit_a]. u_dom u) = {1}"
    by (simp add: unit_a_def)
next
  fix i j
  assume "i < length [unit_a]" "j < length [unit_a]" "i \<noteq> j"
  then show "u_dom ([unit_a] ! i) \<inter> u_dom ([unit_a] ! j) = {}" by simp
next
  fix u assume "u \<in> set [unit_a]"
  then show "acs.cle (u_lo u) (u_hi u)"
    by (simp add: unit_a_def acs.cle_def den_a_def)
next
  fix u assume "u \<in> set [unit_a]"
  then show "acs.cle (u_hi u) 2"
    by (simp add: unit_a_def acs.cle_def den_a_def)
next
  fix u k assume "u \<in> set [unit_a]" and "k \<in> u_dom u"
  then show "\<exists>c. acs.cle (u_lo u) c \<and> acs.cle c (u_hi u) \<and>
                 u_refresh u k = state_after (\<lambda>_. None) (acs.pfx c) k"
    unfolding acs.cle_def acs.pfx_def
    by (intro exI[of _ 1])
       (simp add: unit_a_def den_a_def L_a_def state_after_def apply_ev_def)
qed

lemma wit_rma_the_unit [simp]: "rma.the_unit 1 = unit_a"
  using rma.the_unit_props[of 1] by simp

lemma wit_rma_merged_absent: "rma.merged unit_a 1 = None"
proof -
  have "evs_for 1 (acs.win (u_lo unit_a) (u_hi unit_a)) = [Event 1 None]"
    unfolding acs.win_def
    by (simp add: unit_a_def den_a_def L_a_def evs_for_def)
  then show ?thesis
    by (simp add: rma.merged_def)
qed

lemma wit_rma_present_empty: "rma.rm_present unit_a = {}"
proof -
  have "\<And>x. x \<in> u_dom unit_a \<Longrightarrow> rma.merged unit_a x = None"
    using wit_rma_merged_absent by (simp add: unit_a_def)
  then show ?thesis
    by (auto simp: rma.rm_present_def)
qed

lemma wit_rma_rml_ok: "rma.rml_ok (\<lambda>_. [])"
  by (simp add: rma.rml_ok_def wit_rma_present_empty)

lemma wit_rma_lawful_replay:
  "stream_replay (rma.rm_emission (\<lambda>_. []) 0) 1 = rma.sink_at 2 1"
proof (rule rma.range_merge_replay[OF wit_rma_rml_ok])
  show "\<And>u. u \<in> set [unit_a] \<Longrightarrow> acs.cle 0 (u_hi u)"
    by (simp add: unit_a_def acs.cle_def den_a_def)
qed simp

lemma wit_rma_lawful_absent: "rma.sink_at 2 1 = None"
proof -
  have win_e: "evs_for 1 (acs.win (u_lo unit_a) 2) = [Event 1 None]"
    unfolding acs.win_def
    by (simp add: unit_a_def den_a_def L_a_def evs_for_def)
  show ?thesis
    unfolding rma.sink_at_def wit_rma_the_unit win_e by simp
qed

lemma fix_no_withholding_wrong:
  "stream_replay [Event 1 (Some 5)] (1 :: nat) = Some (5 :: nat)"
  "state_after (\<lambda>_. None) (take 2 L_a) 1 = None"
  by (simp_all add: stream_replay_def L_a_def state_after_def apply_ev_def)

end
