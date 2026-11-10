(*  Title:   Layer01_Fixtures_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Fixtures_Core
  imports Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Carrier-independent Layer 0/1 fixture data\<close>

text \<open>
  The carrier-independent data of the Layer 0/1 fixture family, used by the
  constructed fixture interpretation (@{text Layer01_Fixtures_Inst}) together
  with the concrete run models of @{text Layer01_Fixtures_Model}: the
  per-fixture base states @{text "b0_\<dots>"}, source histories @{text "H_\<dots>"},
  and the @{const latest_src_event} / @{const Src} computation lemmas (plus
  @{text wf_h_es}) they depend on. None of this mentions a run or chunk
  carrier, so this theory imports only
  @{theory Dual_Write_Layer0.Source_Coordinates}, where the fixture source
  coordinates and their order lemmas also live.
\<close>

subsection \<open>WF1 (b): overlapping chunk domains (@{text fix_overlap})\<close>

definition b0_ov :: "nat \<rightharpoonup> nat" where
  "b0_ov = (\<lambda>k. None)"

definition H_ov :: "(nat, nat) src_history" where
  "H_ov = []"

subsection \<open>WF1 (c): chunk owns out-of-scope key (@{text fix_miss_cov})\<close>

definition b0_mc :: "nat \<rightharpoonup> nat" where
  "b0_mc = (\<lambda>k. None)"

definition H_mc :: "(nat, nat) src_history" where
  "H_mc = []"

subsection \<open>WF1 (f): infinite chunk domain (@{text fix_inf_dom})\<close>

definition b0_inf :: "nat \<rightharpoonup> nat" where
  "b0_inf = (\<lambda>k. None)"

definition H_inf :: "(nat, nat) src_history" where
  "H_inf = []"

subsection \<open>WF5: chunk read after frontier (@{text fix_after_f})\<close>

definition b0_caf :: "nat \<rightharpoonup> nat" where
  "b0_caf = (\<lambda>k. None)"

definition H_caf :: "(nat, nat) src_history" where
  "H_caf = []"

subsection \<open>WF6 main: wrong refresh value (@{text fix_wrong_r})\<close>

definition b0_wr :: "nat \<rightharpoonup> nat" where
  "b0_wr = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_wr :: "(nat, nat) src_history" where
  "H_wr = []"

lemma latest_src_event_H_wr_c0_1:
  "latest_src_event H_wr c0 (1::nat) = None"
  unfolding latest_src_event_def by (simp add: H_wr_def)

lemma Src_b0_wr_H_wr_c0_1: "Src b0_wr H_wr c0 (1::nat) = Some 5"
  unfolding Src_def using latest_src_event_H_wr_c0_1
  by (simp add: b0_wr_def)

subsection \<open>WF6 specialized: same-coord read/event ambiguity (@{text fix_same_c})\<close>

definition b0_sc :: "nat \<rightharpoonup> nat" where
  "b0_sc = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_sc :: "(nat, nat) src_history" where
  "H_sc = [(sc_c1, Update 1 7)]"

lemma length_H_sc: "length H_sc = 1" by (simp add: H_sc_def)

lemma H_sc_nth_0: "H_sc ! 0 = (sc_c1, Update 1 7)"
  by (simp add: H_sc_def)

lemma latest_src_event_H_sc_c1_1:
  "latest_src_event H_sc sc_c1 (1::nat) = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_sc ! i)) sc_c1
                \<and> key_of (hist_event (H_sc ! i)) = (1::nat)"
  have "filter ?P [0] = [0]"
    using H_sc_nth_0 sc_c1_le_c1 by simp
  thus ?thesis
    unfolding latest_src_event_def
    using length_H_sc by simp
qed

lemma Src_b0_sc_H_sc_c1_1: "Src b0_sc H_sc sc_c1 (1::nat) = Some 7"
  unfolding Src_def
  using latest_src_event_H_sc_c1_1 H_sc_nth_0 by simp

subsection \<open>WF2 faithfulness: extra observed CDC (@{text fix_extra_cdc})\<close>

definition b0_ec :: "nat \<rightharpoonup> nat" where
  "b0_ec = (\<lambda>k. None)"

text \<open>The extra-CDC family carries no named history constant: its true
  history is the empty list (the observed CDC event is the hallucination),
  and the fixture statements pass @{text "[]"} directly.\<close>

subsection \<open>WF2 coverage: missing dominator (@{text fix_miss_dom})\<close>

definition b0_md :: "nat \<rightharpoonup> nat" where
  "b0_md = (\<lambda>k. None)"

definition H_md :: "(nat, nat) src_history" where
  "H_md = [(md_c1, Update 1 7)]"

lemma length_H_md: "length H_md = 1" by (simp add: H_md_def)

lemma H_md_nth_0: "H_md ! 0 = (md_c1, Update 1 7)"
  by (simp add: H_md_def)

subsection \<open>WF2 multiplicity: duplicate multiset gap (@{text fix_dup_mset})\<close>

definition b0_dm :: "nat \<rightharpoonup> nat" where
  "b0_dm = (\<lambda>k. None)"

definition H_dm :: "(nat, nat) src_history" where
  "H_dm =
     [(dm_c1, Update 1 5), (dm_c1, Update 1 6), (dm_c1, Update 1 5)]"

subsection \<open>WF2 order: duplicate order gap (@{text fix_dup_order})\<close>

definition b0_do :: "nat \<rightharpoonup> nat" where
  "b0_do = (\<lambda>k. None)"

definition H_do :: "(nat, nat) src_history" where
  "H_do =
     [(do_c1, Update 1 5), (do_c1, Update 1 6), (do_c1, Update 1 5)]"

subsection \<open>Boundary: empty scope (@{text boundary_empty_scope})\<close>

definition b0_es :: "nat \<rightharpoonup> nat" where
  "b0_es = (\<lambda>k. None)"

definition H_es :: "(nat, nat) src_history" where
  "H_es = []"

lemma wf_h_es: "wellformed_src_history H_es"
  unfolding wellformed_src_history_def by (simp add: H_es_def)

subsection \<open>WF1 (d): responsible-chunk vs chunk-domain mismatch (@{text fix_resp_dom})\<close>

definition b0_rd :: "nat \<rightharpoonup> nat" where
  "b0_rd = (\<lambda>k. None)"

definition H_rd :: "(nat, nat) src_history" where
  "H_rd = []"

subsection \<open>WF6 row-absence: absence-Refresh without empty source (@{text fix_row_abs})\<close>

definition b0_ra :: "nat \<rightharpoonup> nat" where
  "b0_ra = (\<lambda>k. if k = 1 then Some 99 else None)"

definition H_ra :: "(nat, nat) src_history" where
  "H_ra = []"

lemma latest_src_event_H_ra_c0_1:
  "latest_src_event H_ra c0 (1::nat) = None"
  unfolding latest_src_event_def by (simp add: H_ra_def)

lemma Src_b0_ra_H_ra_c0_1: "Src b0_ra H_ra c0 (1::nat) = Some 99"
  unfolding Src_def using latest_src_event_H_ra_c0_1
  by (simp add: b0_ra_def)

section \<open>Layer 0 source-history fixture\<close>

text \<open>The Layer-0 negative fixture (@{text fix_h_c0_rejected}: a source
  history with an event at the base coordinate is rejected) and its
  reader-facing existential. Both are purely over
  @{const wellformed_src_history} --- no run/chunk carrier is involved, so
  there is no constructed @{text Layer01_Fixtures_Inst} counterpart.\<close>

definition H_c0 :: "(nat, nat) src_history" where
  "H_c0 = [(c0, Update 1 7)]"

lemma length_H_c0: "length H_c0 = 1"
  by (simp add: H_c0_def)

lemma H_c0_nth_0: "H_c0 ! 0 = (c0, Update 1 7)"
  by (simp add: H_c0_def)

theorem fix_h_c0_rejected:
  "\<not> wellformed_src_history H_c0"
proof
  assume H: "wellformed_src_history H_c0"
  hence wfh2: "\<forall>i. i < length H_c0 \<longrightarrow> hist_coord (H_c0 ! i) \<noteq> c0"
    unfolding wellformed_src_history_def by blast
  have "(0::nat) < length H_c0" using length_H_c0 by simp
  with wfh2 have "hist_coord (H_c0 ! 0) \<noteq> c0" by blast
  thus False using H_c0_nth_0 by simp
qed

theorem layer0_negative_fixture_exists:
  "\<exists> (H :: (nat, nat) src_history). \<not> wellformed_src_history H"
proof (intro exI[where x = H_c0])
  show "\<not> wellformed_src_history H_c0" by (rule fix_h_c0_rejected)
qed

end
