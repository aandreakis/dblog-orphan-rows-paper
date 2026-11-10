(*  Title:   Layer01_Witnesses_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Witnesses_Core
  imports Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Minimum-viable wellformed-run witness data (carrier-independent)\<close>

text \<open>
  Carrier-independent core of the minimum-viable wellformed-run positive
  witness.

  This theory holds the witness data shared by the family's constructed model
  (@{text Layer01_Witnesses_Model}) and interpretation
  (@{text Layer01_Witnesses_Inst}): the witness base state @{text b0_w}
  and source history @{text H_w}, the source-coordinate ordering facts, the
  @{const Src} / @{const latest_src_event} computation lemmas on the witness
  data, and the source-history wellformedness @{text wf_h_w}. None of this
  mentions a run or chunk carrier, so the theory imports only
  @{theory Dual_Write_Layer0.Source_Coordinates} (home of the witness
  coordinates @{const c1_w} / @{const c2_w} and their order lemmas).
\<close>

subsection \<open>Witness base state and source history\<close>

definition b0_w :: "nat \<rightharpoonup> nat" where
  "b0_w = (\<lambda>k. if k = 7 then Some 100 else None)"

definition H_w :: "(nat, nat) src_history" where
  "H_w = [(c1_w, Insert 0 42), (c2_w, Delete 1)]"

subsection \<open>Helper computation lemmas for the WF discharge\<close>

text \<open>
  Auxiliary facts about source-coordinate ordering and
  @{const Src} / @{const latest_src_event} on the witness data, used by the
  source-history wellformedness proof below and by the wellformed-run
  discharge over the constructed model in @{text Layer01_Witnesses_Inst}.
\<close>

lemma src_le_c0_c2_w: "src_le c0 c2_w"
  using c0_least by simp

lemma src_le_c1_w_c2_w: "src_le c1_w c2_w"
  using c1_w_lt_c2_w by (simp add: src_lt_def)

lemma not_src_le_c1_w_c0: "\<not> src_le c1_w c0"
  using c0_le_c1_w c0_neq_c1_w src_le_antisym by blast

lemma not_src_le_c2_w_c0: "\<not> src_le c2_w c0"
  using src_le_c0_c2_w c0_neq_c2_w src_le_antisym by blast

lemma not_src_lt_c2_w_c1_w: "\<not> src_lt c2_w c1_w"
proof
  assume H: "src_lt c2_w c1_w"
  hence "src_le c2_w c1_w" "c2_w \<noteq> c1_w" by (simp_all add: src_lt_def)
  with src_le_c1_w_c2_w have "c1_w = c2_w"
    using src_le_antisym by blast
  with \<open>c2_w \<noteq> c1_w\<close> show False by simp
qed

lemma not_src_lt_c2_w_c2_w: "\<not> src_lt c2_w c2_w"
  by (simp add: src_lt_def)

lemma length_H_w: "length H_w = 2"
  by (simp add: H_w_def)

lemma H_w_nth_0: "H_w ! 0 = (c1_w, Insert 0 42)"
  by (simp add: H_w_def)

lemma H_w_nth_1: "H_w ! 1 = (c2_w, Delete (1::nat))"
  by (simp add: H_w_def)

lemma set_H_w:
  "set H_w = {(c1_w, Insert 0 42), (c2_w, Delete (1::nat))}"
  by (simp add: H_w_def)

lemma latest_src_event_H_w_c0_0:
  "latest_src_event H_w c0 (0::nat) = None"
  unfolding latest_src_event_def
  using length_H_w H_w_nth_0 H_w_nth_1
        not_src_le_c1_w_c0 not_src_le_c2_w_c0
  by (simp add: numeral_2_eq_2)

lemma latest_src_event_H_w_c2_w_1:
  "latest_src_event H_w c2_w (1::nat) = Some 1"
  unfolding latest_src_event_def
  using length_H_w H_w_nth_0 H_w_nth_1
        src_le_c1_w_c2_w src_le_refl[where c=c2_w]
  by (simp add: numeral_2_eq_2)

lemma Src_b0_w_H_w_c0_0: "Src b0_w H_w c0 (0::nat) = None"
  unfolding Src_def using latest_src_event_H_w_c0_0
  by (simp add: b0_w_def)

lemma Src_b0_w_H_w_c2_w_1: "Src b0_w H_w c2_w (1::nat) = None"
  unfolding Src_def using latest_src_event_H_w_c2_w_1 H_w_nth_1
  by simp

subsection \<open>Wellformedness of the witness source history\<close>

lemma wf_h_w: "wellformed_src_history H_w"
  unfolding wellformed_src_history_def
  using length_H_w H_w_nth_0 H_w_nth_1
        src_le_c1_w_c2_w c0_neq_c1_w c0_neq_c2_w
        c1_w_lt_c2_w not_src_lt_c2_w_c1_w
  by (auto simp: source_pos_order_def numeral_2_eq_2
                 less_Suc_eq nth_Cons')

end
