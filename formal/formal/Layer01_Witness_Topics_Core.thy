(*  Title:   Layer01_Witness_Topics_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witness_Topics_Core
  imports Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Topic 1 and Topic 2 witness data (carrier-independent)\<close>

text \<open>
  Carrier-independent core of the Topic 1 and Topic 2 positive witnesses.

  Holds the witness data shared by the family's constructed
  models (@{text Layer01_Witness_Topics_Model}) and interpretations
  (@{text Layer01_Witness_Topics_Inst}): the per-topic base states and
  source histories (@{text b0_t1} / @{text H_t1}, @{text b0_t2} / @{text H_t2}),
  the @{const Src} / @{const latest_src_event} computation lemmas on that data,
  and the source-history wellformedness lemmas. None of this mentions a run or
  chunk carrier, so the theory imports only
  @{theory Dual_Write_Layer0.Source_Coordinates} (home of the Topic 1
  coordinate @{const ct1} and its order lemmas).
\<close>

section \<open>Topic 1 witness data\<close>

subsection \<open>Topic 1 base state and source history\<close>

definition b0_t1 :: "nat \<rightharpoonup> nat" where
  "b0_t1 = (\<lambda>k. if k = 1 then Some 5 else None)"

definition H_t1 :: "(nat, nat) src_history" where
  "H_t1 = [(ct1, Update 1 7)]"

lemma length_H_t1: "length H_t1 = 1"
  by (simp add: H_t1_def)

lemma H_t1_nth_0: "H_t1 ! 0 = (ct1, Update 1 7)"
  by (simp add: H_t1_def)

lemma set_H_t1: "set H_t1 = {(ct1, Update 1 7)}"
  by (simp add: H_t1_def)

subsection \<open>Source-state computations on the Topic 1 instance\<close>

lemma upt_length_H_t1: "[0..<length H_t1] = [0]"
  by (simp add: length_H_t1)

lemma latest_src_event_H_t1_c0_1:
  "latest_src_event H_t1 c0 (1::nat) = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_t1 ! i)) c0
                \<and> key_of (hist_event (H_t1 ! i)) = (1::nat)"
  have "filter ?P [0] = []"
    using H_t1_nth_0 not_src_le_ct1_c0 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_t1 by simp
qed

lemma latest_src_event_H_t1_ct1_1:
  "latest_src_event H_t1 ct1 (1::nat) = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_t1 ! i)) ct1
                \<and> key_of (hist_event (H_t1 ! i)) = (1::nat)"
  have "filter ?P [0] = [0]"
    using H_t1_nth_0 src_le_ct1_ct1 by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_t1 by simp
qed

lemma Src_b0_t1_H_t1_c0_1: "Src b0_t1 H_t1 c0 (1::nat) = Some 5"
  unfolding Src_def using latest_src_event_H_t1_c0_1
  by (simp add: b0_t1_def)

lemma Src_b0_t1_H_t1_ct1_1: "Src b0_t1 H_t1 ct1 (1::nat) = Some 7"
  unfolding Src_def using latest_src_event_H_t1_ct1_1 H_t1_nth_0
  by simp

subsection \<open>Wellformedness of the Topic 1 source history\<close>

lemma wf_h_t1: "wellformed_src_history H_t1"
  unfolding wellformed_src_history_def
  using length_H_t1 H_t1_nth_0 c0_neq_ct1
  by (auto simp: source_pos_order_def)

section \<open>Topic 2 witness data\<close>

subsection \<open>Topic 2 base state and source history\<close>

definition b0_t2 :: "nat \<rightharpoonup> nat" where
  "b0_t2 = (\<lambda>k. if k = 10 then Some 100
                else if k = 20 then Some 200 else None)"

definition H_t2 :: "(nat, nat) src_history" where
  "H_t2 = []"

lemma length_H_t2: "length H_t2 = 0" by (simp add: H_t2_def)

lemma set_H_t2: "set H_t2 = {}" by (simp add: H_t2_def)

subsection \<open>Source-state computations on the Topic 2 instance\<close>

lemma latest_src_event_H_t2_c0_any:
  "latest_src_event H_t2 c0 (k :: nat) = None"
  unfolding latest_src_event_def by (simp add: H_t2_def)

lemma Src_b0_t2_H_t2_c0_10: "Src b0_t2 H_t2 c0 (10::nat) = Some 100"
  unfolding Src_def using latest_src_event_H_t2_c0_any
  by (simp add: b0_t2_def)

lemma Src_b0_t2_H_t2_c0_20: "Src b0_t2 H_t2 c0 (20::nat) = Some 200"
  unfolding Src_def using latest_src_event_H_t2_c0_any
  by (simp add: b0_t2_def)

subsection \<open>Wellformedness of the Topic 2 source history\<close>

lemma wf_h_t2: "wellformed_src_history H_t2"
  unfolding wellformed_src_history_def by (simp add: H_t2_def)

end
