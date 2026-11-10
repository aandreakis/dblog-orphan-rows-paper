(*  Title:   Layer01_Virtual_Cut_Example_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer01_Virtual_Cut_Example_Core
  imports Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Running-example data (carrier-independent)\<close>

text \<open>
  Carrier-independent core of the running-example virtual cut.

  Holds the example data shared by the family's constructed
  model @{text Layer01_Virtual_Cut_Example_Model} and interpretation
  @{text Layer01_Virtual_Cut_Example_Inst}, and reused throughout the
  Layer 3 / Layer 4 and continuation witness and fixture theories: the
  example base state
  @{text b0_ex} and source history @{text H_ex}, the source-coordinate ordering
  facts, the @{const Src} / @{const latest_src_event} computation lemmas, and
  the source-history wellformedness @{text wf_h_ex}. None of this mentions a
  run or chunk carrier, so the theory imports only
  @{theory Dual_Write_Layer0.Source_Coordinates} (home of the example
  coordinates @{const ec1} @{text \<open>\<dots>\<close>} @{const ec4} and their order lemmas).
\<close>

subsection \<open>Witness source-coordinate ordering facts\<close>

lemma ec1_neq_ec4: "ec1 \<noteq> ec4"
proof -
  have "src_lt ec1 ec4" using ec1_lt_ec2 ec2_le_ec4
    by (metis src_lt_def src_le_antisym src_le_trans ec1_le_ec4)
  thus ?thesis by (simp add: src_lt_def)
qed

lemma ec2_neq_ec4: "ec2 \<noteq> ec4"
proof -
  have "src_lt ec2 ec4" using ec2_lt_ec3 ec3_le_ec4
    by (metis src_lt_def src_le_antisym src_le_trans ec2_le_ec4)
  thus ?thesis by (simp add: src_lt_def)
qed

text \<open>
  Negative orderings used by the WF discharge and by Src
  computations below: @{text "ec_i"} is \<^emph>\<open>not\<close> @{text "src_le"} below
  @{text c0}, and the @{text src_lt} chain rules out backwards
  comparisons.
\<close>

lemma not_src_le_ec1_c0: "\<not> src_le ec1 c0"
  using c0_le_ec1 c0_neq_ec1 src_le_antisym by blast

lemma not_src_le_ec2_c0: "\<not> src_le ec2 c0"
  using c0_le_ec2 c0_neq_ec2 src_le_antisym by blast

lemma not_src_le_ec3_c0: "\<not> src_le ec3 c0"
  using c0_le_ec3 c0_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_c0: "\<not> src_le ec4 c0"
  using c0_le_ec4 c0_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec2_ec1: "\<not> src_le ec2 ec1"
  using ec1_le_ec2 ec1_neq_ec2 src_le_antisym by blast

lemma not_src_le_ec3_ec1: "\<not> src_le ec3 ec1"
  using ec1_le_ec3 ec1_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_ec1: "\<not> src_le ec4 ec1"
  using ec1_le_ec4 ec1_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec3_ec2: "\<not> src_le ec3 ec2"
  using ec2_le_ec3 ec2_neq_ec3 src_le_antisym by blast

lemma not_src_le_ec4_ec2: "\<not> src_le ec4 ec2"
  using ec2_le_ec4 ec2_neq_ec4 src_le_antisym by blast

lemma not_src_le_ec4_ec3: "\<not> src_le ec4 ec3"
  using ec3_le_ec4 ec3_neq_ec4 src_le_antisym by blast

lemma not_src_lt_ec1_ec1: "\<not> src_lt ec1 ec1" by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec1: "\<not> src_lt ec3 ec1"
  using not_src_le_ec3_ec1 by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec2: "\<not> src_lt ec3 ec2"
  using not_src_le_ec3_ec2 by (simp add: src_lt_def)
lemma not_src_lt_ec3_ec3: "\<not> src_lt ec3 ec3" by (simp add: src_lt_def)

subsection \<open>Witness base state and source history\<close>

definition b0_ex :: "nat \<rightharpoonup> nat" where
  "b0_ex = (\<lambda>k. if k = 100 then Some 5000
               else if k = 200 then Some 10000
               else None)"

definition H_ex :: "(nat, nat) src_history" where
  "H_ex = [ (ec1, Update 100 3000),
            (ec2, Insert 300 2500),
            (ec3, Update 200 12000),
            (ec4, Update 300 3500) ]"

lemma length_H_ex: "length H_ex = 4"
  by (simp add: H_ex_def)

lemma H_ex_nth_0: "H_ex ! 0 = (ec1, Update 100 3000)"
  by (simp add: H_ex_def)

lemma H_ex_nth_1: "H_ex ! 1 = (ec2, Insert 300 2500)"
  by (simp add: H_ex_def)

lemma H_ex_nth_2: "H_ex ! 2 = (ec3, Update 200 12000)"
  by (simp add: H_ex_def)

lemma H_ex_nth_3: "H_ex ! 3 = (ec4, Update 300 3500)"
  by (simp add: H_ex_def)

lemma set_H_ex:
  "set H_ex = { (ec1, Update 100 3000),
                (ec2, Insert 300 2500),
                (ec3, Update 200 12000),
                (ec4, Update 300 3500) }"
  by (simp add: H_ex_def)

subsection \<open>Source-state computations on the example\<close>

lemma upt_length_H_ex: "[0..<length H_ex] = [0, 1, 2, 3]"
proof -
  have "length H_ex = 4" by (rule length_H_ex)
  thus ?thesis by (simp add: upt_rec)
qed

lemma latest_src_event_H_ex_ec1_100:
  "latest_src_event H_ex ec1 100 = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = (100::nat)"
  have "filter ?P [0, 1, 2, 3] = [0]"
    using src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec1_200:
  "latest_src_event H_ex ec1 200 = None"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec1
                \<and> key_of (hist_event (H_ex ! i)) = (200::nat)"
  have "filter ?P [0, 1, 2, 3] = []"
    using src_le_refl[where c=ec1] not_src_le_ec2_ec1
          not_src_le_ec3_ec1 not_src_le_ec4_ec1
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec3_300:
  "latest_src_event H_ex ec3 300 = Some 1"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec3
                \<and> key_of (hist_event (H_ex ! i)) = (300::nat)"
  have "filter ?P [0, 1, 2, 3] = [1]"
    using ec2_le_ec3 src_le_refl[where c=ec3] not_src_le_ec4_ec3
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_100:
  "latest_src_event H_ex ec4 100 = Some 0"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (100::nat)"
  have "filter ?P [0, 1, 2, 3] = [0]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_200:
  "latest_src_event H_ex ec4 200 = Some 2"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (200::nat)"
  have "filter ?P [0, 1, 2, 3] = [2]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

lemma latest_src_event_H_ex_ec4_300:
  "latest_src_event H_ex ec4 300 = Some 3"
proof -
  let ?P = "\<lambda>i. src_le (hist_coord (H_ex ! i)) ec4
                \<and> key_of (hist_event (H_ex ! i)) = (300::nat)"
  have "filter ?P [0, 1, 2, 3] = [1, 3]"
    using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
          H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
    by simp
  thus ?thesis
    unfolding latest_src_event_def upt_length_H_ex by simp
qed

text \<open>
  @{const Src} values at the chunk-read coordinates and at the
  frontier. WF6 uses the chunk-read-coordinate values; the final
  virtual-cut equality uses the frontier values.
\<close>

lemma Src_b0_ex_H_ex_ec1_100:
  "Src b0_ex H_ex ec1 100 = Some 3000"
  unfolding Src_def using latest_src_event_H_ex_ec1_100 H_ex_nth_0
  by simp

lemma Src_b0_ex_H_ex_ec1_200:
  "Src b0_ex H_ex ec1 200 = Some 10000"
  unfolding Src_def using latest_src_event_H_ex_ec1_200
  by (simp add: b0_ex_def)

lemma Src_b0_ex_H_ex_ec3_300:
  "Src b0_ex H_ex ec3 300 = Some 2500"
  unfolding Src_def using latest_src_event_H_ex_ec3_300 H_ex_nth_1
  by simp

lemma Src_b0_ex_H_ex_ec4_100:
  "Src b0_ex H_ex ec4 100 = Some 3000"
  unfolding Src_def using latest_src_event_H_ex_ec4_100 H_ex_nth_0
  by simp

lemma Src_b0_ex_H_ex_ec4_200:
  "Src b0_ex H_ex ec4 200 = Some 12000"
  unfolding Src_def using latest_src_event_H_ex_ec4_200 H_ex_nth_2
  by simp

lemma Src_b0_ex_H_ex_ec4_300:
  "Src b0_ex H_ex ec4 300 = Some 3500"
  unfolding Src_def using latest_src_event_H_ex_ec4_300 H_ex_nth_3
  by simp

subsection \<open>Wellformedness of the example source history\<close>

lemma less_4_cases: "(i :: nat) < 4 \<Longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by linarith

lemma wf_h_ex_WFH1:
  "\<forall>i. Suc i < length H_ex
         \<longrightarrow> src_le (hist_coord (H_ex ! i))
                     (hist_coord (H_ex ! Suc i))"
proof (intro allI impI)
  fix i assume "Suc i < length H_ex"
  hence si_lt: "Suc i < 4" by (simp add: length_H_ex)
  hence i_lt: "i < 3" by linarith
  hence i_cases: "i = 0 \<or> i = 1 \<or> i = 2" by linarith
  consider (a) "i = 0" | (b) "i = 1" | (c) "i = 2" using i_cases by blast
  thus "src_le (hist_coord (H_ex ! i)) (hist_coord (H_ex ! Suc i))"
  proof cases
    case a thus ?thesis using ec1_le_ec2 by (simp add: H_ex_def)
  next
    case b thus ?thesis using ec2_le_ec3 by (simp add: H_ex_def)
  next
    case c thus ?thesis using ec3_le_ec4 by (simp add: H_ex_def)
  qed
qed

lemma wf_h_ex_WFH2:
  "\<forall>i. i < length H_ex \<longrightarrow> hist_coord (H_ex ! i) \<noteq> c0"
proof (intro allI impI)
  fix i assume "i < length H_ex"
  hence i_lt: "i < 4" by (simp add: length_H_ex)
  hence i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    by (rule less_4_cases)
  consider (a) "i = 0" | (b) "i = 1" | (c) "i = 2" | (d) "i = 3"
    using i_cases by blast
  thus "hist_coord (H_ex ! i) \<noteq> c0"
  proof cases
    case a thus ?thesis using c0_neq_ec1 by (simp add: H_ex_def)
  next
    case b thus ?thesis using c0_neq_ec2 by (simp add: H_ex_def)
  next
    case c thus ?thesis using c0_neq_ec3 by (simp add: H_ex_def)
  next
    case d thus ?thesis using c0_neq_ec4 by (simp add: H_ex_def)
  qed
qed

lemma wf_h_ex_WFH3:
  "\<forall>i j. i < length H_ex \<and> j < length H_ex \<and> i \<noteq> j
            \<longrightarrow> source_pos_order H_ex i j \<or> source_pos_order H_ex j i"
proof (intro allI impI)
  fix i j
  assume A: "i < length H_ex \<and> j < length H_ex \<and> i \<noteq> j"
  hence i_lt: "i < 4" and j_lt: "j < 4" and ij_ne: "i \<noteq> j"
    by (auto simp: length_H_ex)
  have i_cases: "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
    using i_lt by (rule less_4_cases)
  have j_cases: "j = 0 \<or> j = 1 \<or> j = 2 \<or> j = 3"
    using j_lt by (rule less_4_cases)
  \<comment> \<open>For each (i, j) pair with @{text \<open>i \<noteq> j\<close>} we either have i < j (and the
      coords are @{text src_lt}-related forward) or j < i (the reverse).\<close>
  show "source_pos_order H_ex i j \<or> source_pos_order H_ex j i"
  proof (cases "i < j")
    case True
    \<comment> \<open>i < j: @{text \<open>hist_coord(H_ex ! i)\<close>} @{text src_lt}-precedes
        @{text \<open>hist_coord(H_ex ! j)\<close>}.\<close>
    show ?thesis
    proof (rule disjI1)
      show "source_pos_order H_ex i j"
        unfolding source_pos_order_def
      proof (rule disjI1)
        show "src_lt (hist_coord (H_ex ! i)) (hist_coord (H_ex ! j))"
          using i_cases j_cases True
                H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
                ec1_lt_ec2 ec2_lt_ec3 ec3_lt_ec4
                ec1_le_ec3 ec1_le_ec4 ec2_le_ec4
                ec1_neq_ec3 ec1_neq_ec4 ec2_neq_ec4
                src_lt_def
          by auto
      qed
    qed
  next
    case False
    hence j_lt_i: "j < i" using ij_ne by linarith
    show ?thesis
    proof (rule disjI2)
      show "source_pos_order H_ex j i"
        unfolding source_pos_order_def
      proof (rule disjI1)
        show "src_lt (hist_coord (H_ex ! j)) (hist_coord (H_ex ! i))"
          using i_cases j_cases j_lt_i
                H_ex_nth_0 H_ex_nth_1 H_ex_nth_2 H_ex_nth_3
                ec1_lt_ec2 ec2_lt_ec3 ec3_lt_ec4
                ec1_le_ec3 ec1_le_ec4 ec2_le_ec4
                ec1_neq_ec3 ec1_neq_ec4 ec2_neq_ec4
                src_lt_def
          by auto
      qed
    qed
  qed
qed

lemma wf_h_ex: "wellformed_src_history H_ex"
  unfolding wellformed_src_history_def
  using wf_h_ex_WFH1 wf_h_ex_WFH2 wf_h_ex_WFH3
  by blast

end
