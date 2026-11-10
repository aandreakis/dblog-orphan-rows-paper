(*  Title:   Layer01_Fixtures_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Fixtures_Inst
  imports Layer01_Fixtures_Model Layer01_Fixtures_Core DBLog_Run_Substrate
begin

section \<open>Constructed interpretations for the Layer 0/1 fixtures\<close>

text \<open>
  Constructs the twelve Layer 1 negative fixtures (each rejected) and the
  empty-scope boundary fixture (accepted) over a single interpretation of
  the Layer 1 locale @{locale dblog_run_substrate} at the concrete model of
  @{text Layer01_Fixtures_Model} (the shared @{type crun}
  record carrier, chunks modeled as @{typ nat}, and the per-fixture
  @{text "crun_\<dots>"} values), establishing every fixture fact with no axioms.

  Structure:

    \<^item> \<^bold>\<open>Constructed interpretation.\<close> We instantiate @{locale dblog_run_substrate}
        once at the @{type crun} carrier: the chunk set is
        @{term "\<lambda>r. set (cr_chunks_list r)"} and the enumeration is
        @{term "\<lambda>r. remdups (cr_chunks_list r)"} (the same
        set-plus-@{const remdups} realization as the concrete @{type run}
        carrier of @{text DBLog_Run}), so the two
        @{text chunks_list} obligations hold definitionally for \<^emph>\<open>every\<close>
        @{type crun} value and the interpretation discharges them with
        @{method simp} --- no axiom. Every fixture's @{text "crun_\<dots>"} value
        sets @{text cr_chunks_list} consistently with @{text cr_chunks}, so the
        interpreted chunk set agrees with the value the fixture pins.

    \<^item> \<^bold>\<open>Constructed rejections / acceptance.\<close> Each negative-fixture theorem
        isolates one wellformedness clause: it extracts that clause from the
        assumed wellformedness, evaluates the fixture's
        @{text "crun_\<dots>"} record value by @{method simp} (chunks appear as
        their @{typ nat} indices), and derives the contradiction; the
        empty-scope boundary theorem instead discharges every clause. The
        carrier-independent fixture data (the base states @{text "b0_\<dots>"},
        source histories @{text "H_\<dots>"}, and the @{const Src} /
        @{const latest_src_event} computation lemmas) lives in
        @{theory DBLog_Virtual_Cuts.Layer01_Fixtures_Core}; the fixture source
        coordinates (@{const caf_c1} / @{const sc_c1} / @{const ec_c1} /
        @{const md_c1} / @{const dm_c1} / @{const do_c1}) are
        @{const coord_of_nat} definitions in
        @{theory Dual_Write_Layer0.Source_Coordinates}, with their order
        lemmas proved there.

  The fixtures fix the key/value
  carrier to concrete @{typ nat}; the @{type crun} carrier fixes
  @{text "'k = nat"}, so the constructed facts live in the global context over
  the interpretation, none resting on a run/chunk axiom.

  Layer 0 source fixture. @{thm [source] fix_h_c0_rejected}
  (in @{theory DBLog_Virtual_Cuts.Layer01_Fixtures_Core})
  rejects @{const H_c0}, a concrete source history over no run carrier;
  it involves no run/chunk interface and so has no counterpart here.
\<close>

subsection \<open>Constructed interpretation at the fixture model carrier\<close>

text \<open>
  Instantiate @{locale dblog_run_substrate} at the @{type crun} carrier of
  @{theory DBLog_Virtual_Cuts.Layer01_Fixtures_Model}, realizing the chunk set
  and enumeration from the single @{const cr_chunks_list} field.
  The two @{text chunks_list} obligations
  reduce to @{term "set (remdups (cr_chunks_list r)) = set (cr_chunks_list r)"}
  and @{term "distinct (remdups (cr_chunks_list r))"}, discharged by
  @{method simp} --- no axiom.
\<close>

global_interpretation cmodel: dblog_run_substrate
  cr_scope
  cr_frontier
  "\<lambda>r. set (cr_chunks_list r)"
  cr_src_history
  cr_rresult
  cr_cdc
  "\<lambda>r. remdups (cr_chunks_list r)"
  cr_dom
  cr_resp
  cr_lwm
  cr_uwm
  cr_rcoord
  by unfold_locales simp_all


subsection \<open>WF1 (b): overlapping chunk domains (@{text fix_overlap})\<close>

theorem fix_overlap_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_ov crun_ov H_ov"
proof
  assume H: "cmodel.wellformed_dblog_run b0_ov crun_ov H_ov"
  hence wf1b:
    "\<forall>ch1 \<in> set (cr_chunks_list crun_ov). \<forall>ch2 \<in> set (cr_chunks_list crun_ov).
        ch1 \<noteq> ch2 \<longrightarrow> cr_dom crun_ov ch1 \<inter> cr_dom crun_ov ch2 = {}"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inA: "(0::nat) \<in> set (cr_chunks_list crun_ov)" by (simp add: crun_ov_def)
  have inB: "(1::nat) \<in> set (cr_chunks_list crun_ov)" by (simp add: crun_ov_def)
  have d01: "(0::nat) \<noteq> 1" by simp
  from wf1b inA inB d01
  have "cr_dom crun_ov 0 \<inter> cr_dom crun_ov 1 = {}" by blast
  thus False by (simp add: crun_ov_def)
qed


subsection \<open>WF1 (c): chunk owns out-of-scope key (@{text fix_miss_cov})\<close>

theorem fix_miss_cov_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_mc crun_mc H_mc"
proof
  assume H: "cmodel.wellformed_dblog_run b0_mc crun_mc H_mc"
  hence wf1c: "cmodel.canonical_chunk_ownership_domain crun_mc = cr_scope crun_mc"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "cmodel.canonical_chunk_ownership_domain crun_mc = {1, 2}"
    unfolding cmodel.canonical_chunk_ownership_domain_def
    by (simp add: crun_mc_def)
  with wf1c have "({1, 2::nat}) = {1}" by (simp add: crun_mc_def)
  thus False by auto
qed


subsection \<open>WF1 (f): infinite chunk domain (@{text fix_inf_dom})\<close>

theorem fix_inf_dom_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_inf crun_inf H_inf"
proof
  assume H: "cmodel.wellformed_dblog_run b0_inf crun_inf H_inf"
  hence wf1f2: "\<forall>ch \<in> set (cr_chunks_list crun_inf). finite (cr_dom crun_inf ch)"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "(0::nat) \<in> set (cr_chunks_list crun_inf)" by (simp add: crun_inf_def)
  with wf1f2 have "finite (cr_dom crun_inf 0)" by blast
  hence "finite (UNIV :: nat set)" by (simp add: crun_inf_def)
  thus False by simp
qed


subsection \<open>WF5: chunk read after frontier (@{text fix_after_f})\<close>

theorem fix_after_f_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_caf crun_caf H_caf"
proof
  assume H: "cmodel.wellformed_dblog_run b0_caf crun_caf H_caf"
  hence wf5: "\<forall>ch \<in> set (cr_chunks_list crun_caf).
                src_le (cr_rcoord crun_caf ch) (cr_frontier crun_caf)"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have "(0::nat) \<in> set (cr_chunks_list crun_caf)" by (simp add: crun_caf_def)
  with wf5 have "src_le (cr_rcoord crun_caf 0) (cr_frontier crun_caf)" by blast
  hence "src_le caf_c1 c0" by (simp add: crun_caf_def)
  with caf_not_src_le_c1_c0 show False by blast
qed


subsection \<open>WF6 main: wrong refresh value (@{text fix_wrong_r})\<close>

theorem fix_wrong_r_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_wr crun_wr H_wr"
proof
  assume H: "cmodel.wellformed_dblog_run b0_wr crun_wr H_wr"
  hence wf6:
    "\<forall>ch \<in> set (cr_chunks_list crun_wr). \<forall>k \<in> cr_dom crun_wr ch. \<forall>m.
        cr_rresult crun_wr ch k = Some m
          \<longrightarrow> m = Src b0_wr H_wr (cr_rcoord crun_wr ch) k"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "(0::nat) \<in> set (cr_chunks_list crun_wr)" by (simp add: crun_wr_def)
  have inK: "(1::nat) \<in> cr_dom crun_wr 0" by (simp add: crun_wr_def)
  have crr: "cr_rresult crun_wr 0 1 = Some (Some 99)" by (simp add: crun_wr_def)
  from wf6 inCh inK crr
  have "Some 99 = Src b0_wr H_wr (cr_rcoord crun_wr 0) (1::nat)" by blast
  moreover have "cr_rcoord crun_wr 0 = c0" by (simp add: crun_wr_def)
  ultimately have "Some 99 = Src b0_wr H_wr c0 (1::nat)" by simp
  with Src_b0_wr_H_wr_c0_1 have "Some 99 = (Some (5::nat))" by simp
  thus False by simp
qed


subsection \<open>WF6 specialized: same-coord read/event ambiguity (@{text fix_same_c})\<close>

theorem fix_same_c_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_sc crun_sc H_sc"
proof
  assume H: "cmodel.wellformed_dblog_run b0_sc crun_sc H_sc"
  hence wf6:
    "\<forall>ch \<in> set (cr_chunks_list crun_sc). \<forall>k \<in> cr_dom crun_sc ch. \<forall>m.
        cr_rresult crun_sc ch k = Some m
          \<longrightarrow> m = Src b0_sc H_sc (cr_rcoord crun_sc ch) k"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "(0::nat) \<in> set (cr_chunks_list crun_sc)" by (simp add: crun_sc_def)
  have inK: "(1::nat) \<in> cr_dom crun_sc 0" by (simp add: crun_sc_def)
  have crr: "cr_rresult crun_sc 0 1 = Some (Some 5)" by (simp add: crun_sc_def)
  from wf6 inCh inK crr
  have "Some 5 = Src b0_sc H_sc (cr_rcoord crun_sc 0) (1::nat)" by blast
  moreover have "cr_rcoord crun_sc 0 = sc_c1" by (simp add: crun_sc_def)
  ultimately have "Some 5 = Src b0_sc H_sc sc_c1 (1::nat)" by simp
  with Src_b0_sc_H_sc_c1_1 have "Some 5 = (Some (7::nat))" by simp
  thus False by simp
qed


subsection \<open>WF2 faithfulness: extra observed CDC (@{text fix_extra_cdc})\<close>

theorem fix_extra_cdc_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_ec crun_ec []"
proof
  assume H: "cmodel.wellformed_dblog_run b0_ec crun_ec []"
  hence wf2f:
    "\<forall>p \<in> set (cr_cdc crun_ec).
        key_of (hist_event p) \<in> cr_scope crun_ec
        \<and> src_le (hist_coord p) (cr_frontier crun_ec)
        \<longrightarrow> p \<in> set (cr_src_history crun_ec)"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have memSet: "(ec_c1, Insert 1 5) \<in> set (cr_cdc crun_ec)"
    by (simp add: crun_ec_def)
  have inScope: "key_of (hist_event ((ec_c1, Insert (1::nat) 5))) \<in> cr_scope crun_ec"
    by (simp add: crun_ec_def)
  have leF: "src_le (hist_coord ((ec_c1, Insert (1::nat) 5))) (cr_frontier crun_ec)"
    using ec_c1_le_c1 by (simp add: crun_ec_def)
  from wf2f memSet inScope leF
  have inSrc: "(ec_c1, Insert (1::nat) 5) \<in> set (cr_src_history crun_ec)" by blast
  thus False by (simp add: crun_ec_def)
qed


subsection \<open>WF2 coverage: missing dominator (@{text fix_miss_dom})\<close>

theorem fix_miss_dom_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_md crun_md H_md"
proof
  assume H: "cmodel.wellformed_dblog_run b0_md crun_md H_md"
  hence wf2c: "\<forall>k \<in> cr_scope crun_md.
                 cmodel.covers_ordinary_cdc crun_md k (cr_frontier crun_md)"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have k1: "(1::nat) \<in> cr_scope crun_md" by (simp add: crun_md_def)
  with wf2c have cov: "cmodel.covers_ordinary_cdc crun_md (1::nat) (cr_frontier crun_md)"
    by blast
  from cov obtain ch where
    ch_resp: "cr_resp crun_md 1 = Some ch" and
    ch_cov:  "\<forall>i. i < length (cr_src_history crun_md)
                  \<longrightarrow> src_lt (cr_rcoord crun_md ch)
                              (hist_coord (cr_src_history crun_md ! i))
                  \<longrightarrow> src_le (hist_coord (cr_src_history crun_md ! i)) (cr_frontier crun_md)
                  \<longrightarrow> key_of (hist_event (cr_src_history crun_md ! i)) = (1::nat)
                  \<longrightarrow> cr_src_history crun_md ! i \<in> set (cr_cdc crun_md)"
    unfolding cmodel.covers_ordinary_cdc_def by blast
  from ch_resp have ch_eq: "ch = 0" by (simp add: crun_md_def)
  have idx_lt: "(0::nat) < length (cr_src_history crun_md)"
    by (simp add: crun_md_def)
  have lt_premise: "src_lt (cr_rcoord crun_md 0)
                           (hist_coord (cr_src_history crun_md ! 0))"
    using md_c0_lt_c1 by (simp add: crun_md_def)
  have le_premise: "src_le (hist_coord (cr_src_history crun_md ! 0))
                           (cr_frontier crun_md)"
    using md_c1_le_c1 by (simp add: crun_md_def)
  have key_premise: "key_of (hist_event (cr_src_history crun_md ! 0)) = (1::nat)"
    by (simp add: crun_md_def)
  from ch_cov ch_eq idx_lt lt_premise le_premise key_premise
  have "cr_src_history crun_md ! 0 \<in> set (cr_cdc crun_md)" by blast
  thus False by (simp add: crun_md_def)
qed


subsection \<open>WF2 multiplicity: duplicate multiset gap (@{text fix_dup_mset})\<close>

theorem fix_dup_mset_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_dm crun_dm H_dm"
proof
  assume H: "cmodel.wellformed_dblog_run b0_dm crun_dm H_dm"
  hence wf2_mset:
    "\<forall>k\<in>cr_scope crun_dm. \<forall>ch c.
        cr_resp crun_dm k = Some ch
        \<and> src_lt (cr_rcoord crun_dm ch) c
        \<and> src_le c (cr_frontier crun_dm)
        \<longrightarrow>
          mset (source_key_coord_slice k c (cr_cdc crun_dm))
          = mset (source_key_coord_slice k c (cr_src_history crun_dm))"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have ms:
    "mset (source_key_coord_slice (1::nat) dm_c1 (cr_cdc crun_dm))
     = mset (source_key_coord_slice (1::nat) dm_c1 (cr_src_history crun_dm))"
  proof -
    have k_scope: "(1::nat) \<in> cr_scope crun_dm"
      by (simp add: crun_dm_def)
    from wf2_mset k_scope
    have inst:
      "\<forall>ch c.
        cr_resp crun_dm (1::nat) = Some ch
        \<and> src_lt (cr_rcoord crun_dm ch) c
        \<and> src_le c (cr_frontier crun_dm)
        \<longrightarrow>
          mset (source_key_coord_slice (1::nat) c (cr_cdc crun_dm))
          = mset (source_key_coord_slice (1::nat) c (cr_src_history crun_dm))"
      by blast
    have prem:
      "cr_resp crun_dm (1::nat) = Some 0
       \<and> src_lt (cr_rcoord crun_dm 0) dm_c1
       \<and> src_le dm_c1 (cr_frontier crun_dm)"
      using dm_c0_lt_c1 dm_c1_le_c1 by (simp add: crun_dm_def)
    show ?thesis using inst prem by blast
  qed
  have bad_mset:
    "mset [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat))]
     = mset [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat)),
             (dm_c1, Update 1 (5::nat))]"
    using ms by (simp add: source_key_coord_slice_def crun_dm_def)
  hence "length [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat))]
       = length [(dm_c1, Update (1::nat) (5::nat)), (dm_c1, Update 1 (6::nat)),
                 (dm_c1, Update 1 (5::nat))]"
    by (rule mset_eq_length)
  thus False by simp
qed


subsection \<open>WF2 order: duplicate order gap (@{text fix_dup_order})\<close>

theorem fix_dup_order_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_do crun_do H_do"
proof
  assume H: "cmodel.wellformed_dblog_run b0_do crun_do H_do"
  hence wf2_order:
    "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
        \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cr_scope crun_do
                                 \<and> src_le (hist_coord p) (cr_frontier crun_do));
               cdc_in_slice  = filter in_slice (cr_cdc crun_do);
               hist_in_slice = filter in_slice (cr_src_history crun_do)
           in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                   \<iota> i < length hist_in_slice
                 \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  then obtain \<iota> :: "nat \<Rightarrow> nat" where
    iota_mono: "strict_mono \<iota>" and
    iota_hits:
      "(let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cr_scope crun_do
                              \<and> src_le (hist_coord p) (cr_frontier crun_do));
            cdc_in_slice  = filter in_slice (cr_cdc crun_do);
            hist_in_slice = filter in_slice (cr_src_history crun_do)
        in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                \<iota> i < length hist_in_slice
              \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
    by blast
  let ?in_slice =
    "\<lambda>p. key_of (hist_event p) \<in> cr_scope crun_do
          \<and> src_le (hist_coord p) (cr_frontier crun_do)"
  have sub:
    "subseq (filter ?in_slice (cr_cdc crun_do))
            (filter ?in_slice (cr_src_history crun_do))"
  proof (rule subseq_from_strict_mono_nth[OF iota_mono])
    fix i
    assume i_lt: "i < length (filter ?in_slice (cr_cdc crun_do))"
    show "\<iota> i < length (filter ?in_slice (cr_src_history crun_do))
          \<and> filter ?in_slice (cr_cdc crun_do) ! i
             = filter ?in_slice (cr_src_history crun_do) ! \<iota> i"
      using iota_hits i_lt by (simp add: Let_def)
  qed
  have impossible:
    "subseq [(do_c1, Update (1::nat) (5::nat)), (do_c1, Update 1 (5::nat)),
             (do_c1, Update 1 (6::nat))]
            [(do_c1, Update (1::nat) (5::nat)), (do_c1, Update 1 (6::nat)),
             (do_c1, Update 1 (5::nat))]"
    using sub do_c1_le_c1 by (simp add: crun_do_def)
  thus False by simp
qed


subsection \<open>WF1 (d): responsible-chunk vs chunk-domain mismatch (@{text fix_resp_dom})\<close>

theorem fix_resp_dom_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_rd crun_rd H_rd"
proof
  assume H: "cmodel.wellformed_dblog_run b0_rd crun_rd H_rd"
  hence wf1d:
    "\<forall>k \<in> cr_scope crun_rd. \<forall>ch.
        cr_resp crun_rd k = Some ch
          \<longleftrightarrow> ch \<in> set (cr_chunks_list crun_rd) \<and> k \<in> cr_dom crun_rd ch"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inScope: "(1::nat) \<in> cr_scope crun_rd" by (simp add: crun_rd_def)
  with wf1d
  have iff_for_rd_ch:
    "cr_resp crun_rd 1 = Some 0
       \<longleftrightarrow> (0::nat) \<in> set (cr_chunks_list crun_rd) \<and> (1::nat) \<in> cr_dom crun_rd 0"
    by blast
  have rhs_holds: "(0::nat) \<in> set (cr_chunks_list crun_rd) \<and> (1::nat) \<in> cr_dom crun_rd 0"
    by (simp add: crun_rd_def)
  with iff_for_rd_ch have "cr_resp crun_rd 1 = Some 0" by simp
  thus False by (simp add: crun_rd_def)
qed


subsection \<open>WF6 row-absence: absence-Refresh without empty source (@{text fix_row_abs})\<close>

text \<open>The determinate clean prefix
  of the row-absence model run, derived from its pinned accessors: a single
  absence @{const Refresh} at the base coordinate.\<close>

lemma cm_ra_clean_prefix:
  "cmodel.clean_prefix_of crun_ra = [Refresh (1::nat) (None::nat option) c0]"
proof -
  have d1: "sorted_list_of_set {Suc 0} = [Suc 0]" by simp
  show ?thesis
    unfolding cmodel.clean_prefix_of_def canonical_clean_prefix_def
              cdc_event_replays_def chunk_read_refreshes_def
    by (simp add: crun_ra_def d1 One_nat_def
                  List.map_filter_simps sort_key_def)
qed

lemma cm_refresh_in_ra_prefix:
  "Refresh (1::nat) (None::nat option) c0 \<in> set (cmodel.clean_prefix_of crun_ra)"
  using cm_ra_clean_prefix by simp

theorem fix_row_abs_rejected_constructed:
  "\<not> cmodel.wellformed_dblog_run b0_ra crun_ra H_ra"
proof
  assume H: "cmodel.wellformed_dblog_run b0_ra crun_ra H_ra"
  hence wf6_ra:
    "\<forall>ch \<in> set (cr_chunks_list crun_ra). \<forall>k \<in> cr_dom crun_ra ch.
        cr_rresult crun_ra ch k = Some None
          \<longrightarrow> cmodel.row_absence_meaningful b0_ra H_ra crun_ra ch k"
    unfolding cmodel.wellformed_dblog_run_def by (elim conjE) (assumption | blast)
  have inCh: "(0::nat) \<in> set (cr_chunks_list crun_ra)" by (simp add: crun_ra_def)
  have inK: "(1::nat) \<in> cr_dom crun_ra 0" by (simp add: crun_ra_def)
  have crr: "cr_rresult crun_ra 0 1 = Some None" by (simp add: crun_ra_def)
  from wf6_ra inCh inK crr
  have ram: "cmodel.row_absence_meaningful b0_ra H_ra crun_ra 0 1" by blast
  have rcoord0: "cr_rcoord crun_ra 0 = c0" by (simp add: crun_ra_def)
  from ram have implication:
    "((1::nat) \<in> cr_dom crun_ra 0
      \<and> Refresh 1 None (cr_rcoord crun_ra 0)
            \<in> set (cmodel.clean_prefix_of crun_ra))
       \<longrightarrow> Src b0_ra H_ra (cr_rcoord crun_ra 0) 1 = None"
    unfolding cmodel.row_absence_meaningful_def by simp
  have antecedent:
    "(1::nat) \<in> cr_dom crun_ra 0
     \<and> Refresh 1 None (cr_rcoord crun_ra 0)
         \<in> set (cmodel.clean_prefix_of crun_ra)"
    using inK cm_refresh_in_ra_prefix rcoord0 by simp
  from implication antecedent
  have "Src b0_ra H_ra (cr_rcoord crun_ra 0) 1 = None" by blast
  with rcoord0 Src_b0_ra_H_ra_c0_1 have "(Some (99::nat)) = None" by simp
  thus False by simp
qed


subsection \<open>Boundary: empty scope, vacuously wellformed (@{text boundary_empty_scope})\<close>

text \<open>The empty-scope model run
  (@{const default_crun}) has no chunks and no observed CDC, so its clean prefix
  is empty.\<close>

lemma cm_es_clean_prefix: "cmodel.clean_prefix_of default_crun = []"
  unfolding cmodel.clean_prefix_of_def canonical_clean_prefix_def cdc_event_replays_def
  by (simp add: default_crun_def List.map_filter_simps)

lemma cm_es_canonical_partition:
  "cmodel.canonical_chunk_ownership_domain default_crun = {}"
  unfolding cmodel.canonical_chunk_ownership_domain_def
  by (simp add: default_crun_def)

theorem boundary_empty_scope_constructed:
  "cmodel.wellformed_dblog_run b0_es default_crun H_es"
  unfolding cmodel.wellformed_dblog_run_def
proof (intro conjI)
  show "cr_src_history default_crun = H_es"
    by (simp add: default_crun_def H_es_def)
next
  show "wellformed_src_history H_es" by (rule wf_h_es)
next
  show "\<forall>k\<in>cr_scope default_crun.
          \<exists>!ch. ch \<in> set (cr_chunks_list default_crun) \<and> k \<in> cr_dom default_crun ch"
    by (simp add: default_crun_def)
next
  show "\<forall>ch1\<in>set (cr_chunks_list default_crun). \<forall>ch2\<in>set (cr_chunks_list default_crun).
          ch1 \<noteq> ch2 \<longrightarrow> cr_dom default_crun ch1 \<inter> cr_dom default_crun ch2 = {}"
    by (simp add: default_crun_def)
next
  show "cmodel.canonical_chunk_ownership_domain default_crun = cr_scope default_crun"
    using cm_es_canonical_partition by (simp add: default_crun_def)
next
  show "\<forall>k\<in>cr_scope default_crun. \<forall>ch.
          cr_resp default_crun k = Some ch
            \<longleftrightarrow> ch \<in> set (cr_chunks_list default_crun) \<and> k \<in> cr_dom default_crun ch"
    by (simp add: default_crun_def)
next
  show "\<forall>k. k \<notin> cr_scope default_crun \<longrightarrow> cr_resp default_crun k = None"
    by (simp add: default_crun_def)
next
  show "finite (cr_scope default_crun)" by (simp add: default_crun_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun). finite (cr_dom default_crun ch)"
    by (simp add: default_crun_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun). cr_dom default_crun ch \<noteq> {}"
    by (simp add: default_crun_def)
next
  show "\<forall>k\<in>cr_scope default_crun.
          cmodel.covers_ordinary_cdc default_crun k (cr_frontier default_crun)"
    by (simp add: default_crun_def)
next
  show "\<forall>p\<in>set (cr_cdc default_crun).
          key_of (hist_event p) \<in> cr_scope default_crun
          \<and> src_le (hist_coord p) (cr_frontier default_crun)
          \<longrightarrow> p \<in> set (cr_src_history default_crun)"
    by (simp add: default_crun_def)
next
  show "\<exists>\<iota> :: nat \<Rightarrow> nat. strict_mono \<iota>
          \<and> (let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cr_scope default_crun
                                   \<and> src_le (hist_coord p) (cr_frontier default_crun));
                 cdc_in_slice  = filter in_slice (cr_cdc default_crun);
                 hist_in_slice = filter in_slice (cr_src_history default_crun)
             in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                    \<iota> i < length hist_in_slice
                  \<and> cdc_in_slice ! i = hist_in_slice ! \<iota> i)"
  proof (intro exI[where x="\<lambda>n :: nat. n"] conjI)
    show "strict_mono (\<lambda>n :: nat. n)" by (simp add: strict_mono_def)
  next
    show "let in_slice = (\<lambda>p. key_of (hist_event p) \<in> cr_scope default_crun
                                \<and> src_le (hist_coord p) (cr_frontier default_crun));
              cdc_in_slice  = filter in_slice (cr_cdc default_crun);
              hist_in_slice = filter in_slice (cr_src_history default_crun)
          in \<forall>i. i < length cdc_in_slice \<longrightarrow>
                 (\<lambda>n :: nat. n) i < length hist_in_slice
               \<and> cdc_in_slice ! i = hist_in_slice ! (\<lambda>n :: nat. n) i"
      by (simp add: default_crun_def Let_def)
  qed
next
  show "\<forall>k\<in>cr_scope default_crun. \<forall>ch c.
          cr_resp default_crun k = Some ch
          \<and> src_lt (cr_rcoord default_crun ch) c
          \<and> src_le c (cr_frontier default_crun)
          \<longrightarrow>
            mset (source_key_coord_slice k c (cr_cdc default_crun))
            = mset (source_key_coord_slice k c (cr_src_history default_crun))"
    by (simp add: default_crun_def source_key_coord_slice_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun).
          src_le (cr_lwm default_crun ch) (cr_rcoord default_crun ch)
        \<and> src_le (cr_rcoord default_crun ch) (cr_uwm default_crun ch)
        \<and> (\<forall>k\<in>cr_dom default_crun ch. \<exists>m. cr_rresult default_crun ch k = Some m)
        \<and> (\<forall>k\<in>cr_dom default_crun ch. \<forall>m.
             cr_rresult default_crun ch k = Some m
               \<longleftrightarrow> Refresh k m (cr_rcoord default_crun ch)
                    \<in> set (cmodel.clean_prefix_of default_crun))"
    by (simp add: default_crun_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun).
          src_le (cr_rcoord default_crun ch) (cr_frontier default_crun)"
    by (simp add: default_crun_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun). \<forall>k\<in>cr_dom default_crun ch. \<forall>m.
          cr_rresult default_crun ch k = Some m
            \<longrightarrow> m = Src b0_es H_es (cr_rcoord default_crun ch) k"
    by (simp add: default_crun_def)
next
  show "\<forall>ch\<in>set (cr_chunks_list default_crun). \<forall>k\<in>cr_dom default_crun ch.
          cr_rresult default_crun ch k = Some None
            \<longrightarrow> cmodel.row_absence_meaningful b0_es H_es default_crun ch k"
    by (simp add: default_crun_def)
next
  show "\<forall>p\<in>set (cr_cdc default_crun).
          key_of (hist_event p) \<in> cr_scope default_crun
          \<and> src_le (hist_coord p) (cr_frontier default_crun)
          \<longrightarrow> Cdc (hist_coord p) (hist_event p)
                \<in> set (cmodel.clean_prefix_of default_crun)"
    by (simp add: default_crun_def)
next
  show "\<forall>e c. Cdc c e \<in> set (cmodel.clean_prefix_of default_crun)
                \<and> key_of e \<in> cr_scope default_crun
                \<and> src_le c (cr_frontier default_crun)
                \<longrightarrow> (c, e) \<in> set (cr_cdc default_crun)"
    using cm_es_clean_prefix by simp
qed


subsection \<open>Constructed existential bundles\<close>

text \<open>
  Reader-facing @{text \<exists>} bundles over the constructed
  @{type crun} carrier, with no run/chunk axiom: rejected runs exist, and a
  wellformed empty-scope run exists. The Layer 0 bundle
  (@{thm [source] layer0_negative_fixture_exists} in
  @{theory DBLog_Virtual_Cuts.Layer01_Fixtures_Core}) is over a
  concrete source history with no run carrier.
\<close>

theorem layer1_negative_fixtures_exist_constructed:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: crun) (H :: (nat, nat) src_history).
        \<not> cmodel.wellformed_dblog_run b0 R H"
proof (intro exI[where x = b0_ov] exI[where x = crun_ov] exI[where x = H_ov])
  show "\<not> cmodel.wellformed_dblog_run b0_ov crun_ov H_ov"
    by (rule fix_overlap_rejected_constructed)
qed

theorem boundary_empty_scope_exists_constructed:
  "\<exists> (b0 :: nat \<rightharpoonup> nat) (R :: crun) (H :: (nat, nat) src_history).
        cmodel.wellformed_dblog_run b0 R H \<and> cr_scope R = {}"
proof (intro exI[where x = b0_es] exI[where x = default_crun] exI[where x = H_es]
             conjI)
  show "cmodel.wellformed_dblog_run b0_es default_crun H_es"
    by (rule boundary_empty_scope_constructed)
next
  show "cr_scope default_crun = {}" by (simp add: default_crun_def)
qed

text \<open>
  A model exists for the @{locale dblog_run_substrate} interface realizing every
  Layer 1 fixture run, so each fixture's rejection (or, for the empty-scope
  boundary, its acceptance) holds by construction --- consistency-by-construction,
  resting on no axiom.
\<close>

end
