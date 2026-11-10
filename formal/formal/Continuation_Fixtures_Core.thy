(*  Title:   Continuation_Fixtures_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Continuation_Fixtures_Core
  imports Continuation Layer01_Virtual_Cut_Example_Core
begin

section \<open>Carrier-independent continuation fixture data\<close>

text \<open>
  The carrier-independent data and theorems of the continuation fixture
  family, shared with the constructed interpretation
  @{text Continuation_Fixtures_Inst}: the source-coordinate order facts, the
  positive continuation witness segments and their @{const virtual_cut_state}
  lemmas, the shared wellformedness / canonical-segment infrastructure, and
  the negative / boundary @{text "fix_l7_..."} fixtures. The @{text l7_}
  prefix (and its @{text l7f_} / @{text fix_l7_} variants) tags the
  continuation fixture family (historically the seventh fixture layer); it
  does not denote a model layer. None of this mentions
  a run, chunk, or certificate carrier; the theory imports
  @{theory DBLog_Virtual_Cuts.Continuation} (for the continuation lemmas and,
  transitively, the public @{const virtual_cut_state}) and
  @{theory DBLog_Virtual_Cuts.Layer01_Virtual_Cut_Example_Core} (for
  @{const H_ex} and its wellformedness @{text wf_h_ex}).
\<close>

lemma Src_at_base:
  assumes wfH: "wellformed_src_history H"
  shows "Src b0 H c0 = b0"
proof (rule ext)
  fix k
  have no_event_at_c0:
    "\<not> src_le (hist_coord (H ! i)) c0" if i_lt: "i < length H" for i
  proof
    assume "src_le (hist_coord (H ! i)) c0"
    moreover have "src_le c0 (hist_coord (H ! i))" by (rule c0_least)
    ultimately have "hist_coord (H ! i) = c0" by (rule src_le_antisym)
    moreover have "hist_coord (H ! i) \<noteq> c0"
      using wfH i_lt unfolding wellformed_src_history_def by blast
    ultimately show False by simp
  qed
  have "filter (\<lambda>i. src_le (hist_coord (H ! i)) c0
                     \<and> key_of (hist_event (H ! i)) = k) [0..<length H] = []"
    by (auto simp: filter_empty_conv no_event_at_c0)
  hence "latest_src_event H c0 k = None"
    unfolding latest_src_event_def by (simp add: Let_def)
  thus "Src b0 H c0 k = b0 k"
    unfolding Src_def by simp
qed

lemma l7_c0_lt_ec1: "c0 < ec1" using c0_lt_ec1 by (simp add: src_lt_eq_less)

lemma l7_ec1_lt_ec2: "ec1 < ec2" using ec1_lt_ec2 by (simp add: src_lt_eq_less)

lemma l7_ec2_lt_ec3: "ec2 < ec3" using ec2_lt_ec3 by (simp add: src_lt_eq_less)

lemma l7_ec3_lt_ec4: "ec3 < ec4" using ec3_lt_ec4 by (simp add: src_lt_eq_less)

lemma l7_c0_lt_ec2: "c0 < ec2" using l7_c0_lt_ec1 l7_ec1_lt_ec2 by (rule less_trans)

lemma l7_c0_lt_ec3: "c0 < ec3" using l7_c0_lt_ec2 l7_ec2_lt_ec3 by (rule less_trans)

lemma l7_c0_lt_ec4: "c0 < ec4" using l7_c0_lt_ec3 l7_ec3_lt_ec4 by (rule less_trans)

lemma l7_ec2_lt_ec4: "ec2 < ec4" using l7_ec2_lt_ec3 l7_ec3_lt_ec4 by (rule less_trans)

lemma l7_c0_le_ec2: "c0 \<le> ec2" using l7_c0_lt_ec2 by (rule less_imp_le)

lemma l7_ec1_le_ec2: "ec1 \<le> ec2" using l7_ec1_lt_ec2 by (rule less_imp_le)

lemma l7_ec2_le_ec4: "ec2 \<le> ec4" using l7_ec2_lt_ec4 by (rule less_imp_le)

lemma l7_ec3_le_ec4: "ec3 \<le> ec4" using l7_ec3_lt_ec4 by (rule less_imp_le)

lemma l7_not_ec3_le_ec2: "\<not> ec3 \<le> ec2" using l7_ec2_lt_ec3 by (simp add: not_le)

lemma l7_not_ec4_le_ec2: "\<not> ec4 \<le> ec2" using l7_ec2_lt_ec4 by (simp add: not_le)

lemma l7_not_ec2_lt_ec1: "\<not> ec2 < ec1" using l7_ec1_le_ec2 by (simp add: not_less)

abbreviation l7_scope :: "nat set" where
  "l7_scope \<equiv> {100, 200, 300}"

definition l7_seg1 :: "(nat, nat) replay_event list" where
  "l7_seg1 = [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 300 2500)]"

definition l7_seg2 :: "(nat, nat) replay_event list" where
  "l7_seg2 = [Cdc ec3 (Update 200 12000), Cdc ec4 (Update 300 3500)]"

lemma l7_seg1_segment:
  "cdc_segment_between H_ex l7_scope c0 ec2 l7_seg1"
  unfolding cdc_segment_between_def l7_seg1_def H_ex_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_c0_lt_ec3
                l7_c0_lt_ec4 l7_ec1_le_ec2 l7_not_ec3_le_ec2
                l7_not_ec4_le_ec2)

lemma l7_seg2_segment:
  "cdc_segment_between H_ex l7_scope ec2 ec4 l7_seg2"
  unfolding cdc_segment_between_def l7_seg2_def H_ex_def cdc_lift_def
  by (simp add: l7_ec2_le_ec4 l7_ec2_lt_ec3 l7_ec2_lt_ec4 l7_ec3_le_ec4
                l7_not_ec2_lt_ec1)

lemma l7_vc0: "virtual_cut_state (\<lambda>_. None) [] l7_scope c0 H_ex"
  unfolding virtual_cut_state_def
  using Src_at_base[OF wf_h_ex, of "\<lambda>_. None"]
  by (simp add: Apply_def)

lemma l7_vc_ec2: "virtual_cut_state (\<lambda>_. None) l7_seg1 l7_scope ec2 H_ex"
  using virtual_cut_state_continuation[OF wf_h_ex l7_vc0 l7_seg1_segment]
  by simp

theorem continuation_positive_witness:
  "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex"
  by (rule virtual_cut_state_continuation[OF wf_h_ex l7_vc_ec2 l7_seg2_segment])

lemma l7_c0_le_ec1: "c0 \<le> ec1" using l7_c0_lt_ec1 by (rule less_imp_le)

lemma l7_not_ec2_le_ec1: "\<not> ec2 \<le> ec1" using l7_ec1_lt_ec2 by (simp add: not_le)

lemma l7_wf_one:
  fixes ca :: src_coord and ea :: "(nat, nat) source_event"
  assumes "c0 \<noteq> ca"
  shows "wellformed_src_history [(ca, ea)]"
  unfolding wellformed_src_history_def
  using assms by auto

lemma l7_wf_two:
  fixes ca cb :: src_coord
    and ea eb :: "(nat, nat) source_event"
  assumes le:  "src_le ca cb"
      and a0c: "c0 \<noteq> ca"
      and b0c: "c0 \<noteq> cb"
  shows "wellformed_src_history [(ca, ea), (cb, eb)]"
proof -
  let ?H = "[(ca, ea), (cb, eb)]"
  have spo01: "source_pos_order ?H 0 1"
  proof -
    from le have "src_lt ca cb \<or> ca = cb"
      unfolding src_lt_def by blast
    thus ?thesis unfolding source_pos_order_def by auto
  qed
  show ?thesis
    unfolding wellformed_src_history_def
  proof (intro conjI allI impI)
    fix i assume "Suc i < length ?H"
    hence "i = 0" by simp
    thus "src_le (hist_coord (?H ! i)) (hist_coord (?H ! Suc i))"
      using le by simp
  next
    fix i assume "i < length ?H"
    hence "i = 0 \<or> i = 1" by auto
    thus "hist_coord (?H ! i) \<noteq> c0" using a0c b0c by auto
  next
    fix i j assume "i < length ?H \<and> j < length ?H \<and> i \<noteq> j"
    hence "(i = 0 \<and> j = 1) \<or> (i = 1 \<and> j = 0)" by auto
    thus "source_pos_order ?H i j \<or> source_pos_order ?H j i"
      using spo01 by blast
  qed
qed

lemma l7_base_cut:
  assumes "wellformed_src_history H"
  shows "virtual_cut_state (\<lambda>_. None) [] K c0 H"
  unfolding virtual_cut_state_def
  using Src_at_base[OF assms, of "\<lambda>_. None"]
  by (simp add: Apply_def)

lemma l7_canon_continuation:
  assumes wf:  "wellformed_src_history H"
      and seg: "cdc_segment_between H K c0 f' \<delta>"
  shows "virtual_cut_state (\<lambda>_. None) \<delta> K f' H"
proof -
  have "virtual_cut_state (\<lambda>_. None) ([] @ \<delta>) K f' H"
    by (rule virtual_cut_state_continuation[OF wf l7_base_cut[OF wf] seg])
  thus ?thesis by simp
qed

lemma l7_breaks_continuation:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes canon: "virtual_cut_state b0 dc K f' H"
      and kK:    "k \<in> K"
      and diff:  "Apply dx k \<noteq> Apply dc k"
  shows "\<not> virtual_cut_state b0 dx K f' H"
proof
  assume "virtual_cut_state b0 dx K f' H"
  with canon
  have "restrict (Apply dx) K = restrict (Apply dc) K"
    unfolding virtual_cut_state_def by simp
  hence "restrict (Apply dx) K k = restrict (Apply dc) K k" by simp
  with kK have "Apply dx k = Apply dc k"
    unfolding restrict_def by simp
  with diff show False by simp
qed

definition l7_H_cov :: "(nat, nat) src_history" where
  "l7_H_cov = [(ec1, Update 100 3000)]"

lemma l7_wf_cov: "wellformed_src_history l7_H_cov"
  unfolding l7_H_cov_def by (rule l7_wf_one[OF c0_neq_ec1])

lemma l7_cov_canon_seg:
  "cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)

lemma l7_cov_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec1 l7_H_cov"
  by (rule l7_canon_continuation[OF l7_wf_cov l7_cov_canon_seg])

theorem fix_l7_missing_event:
  "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 []
   \<and> \<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov"
proof
  show "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 []"
    unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov"
    by (rule l7_breaks_continuation[OF l7_cov_canon, where k = 100])
       (simp_all add: Apply_def)
qed

theorem fix_l7_event_not_in_history:
  "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 7777)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov"
proof
  show "\<not> cdc_segment_between l7_H_cov {100} c0 ec1 [Cdc ec1 (Update 100 7777)]"
    unfolding cdc_segment_between_def l7_H_cov_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov"
    by (rule l7_breaks_continuation[OF l7_cov_canon, where k = 100])
       (simp_all add: Apply_def)
qed

definition l7_H_future :: "(nat, nat) src_history" where
  "l7_H_future = [(ec1, Update 100 3000), (ec2, Update 100 9000)]"

lemma l7_wf_future: "wellformed_src_history l7_H_future"
  unfolding l7_H_future_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_future_canon_seg:
  "cdc_segment_between l7_H_future {100} c0 ec1 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_future_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_not_ec2_le_ec1)

lemma l7_future_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec1 l7_H_future"
  by (rule l7_canon_continuation[OF l7_wf_future l7_future_canon_seg])

theorem fix_l7_future_event:
  "\<not> cdc_segment_between l7_H_future {100} c0 ec1
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
         {100} ec1 l7_H_future"
proof
  show "\<not> cdc_segment_between l7_H_future {100} c0 ec1
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]"
    unfolding cdc_segment_between_def l7_H_future_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_not_ec2_le_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
           {100} ec1 l7_H_future"
    by (rule l7_breaks_continuation[OF l7_future_canon, where k = 100])
       (simp_all add: Apply_def)
qed

definition l7_H_dup :: "(nat, nat) src_history" where
  "l7_H_dup = [(ec1, Update 100 1), (ec1, Update 100 2)]"

lemma l7_wf_dup: "wellformed_src_history l7_H_dup"
  unfolding l7_H_dup_def
  by (rule l7_wf_two[OF src_le_refl c0_neq_ec1 c0_neq_ec1])

lemma l7_dup_canon_seg:
  "cdc_segment_between l7_H_dup {100} c0 ec1
     [Cdc ec1 (Update 100 1), Cdc ec1 (Update 100 2)]"
  unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
  by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)

lemma l7_dup_canon:
  "virtual_cut_state (\<lambda>_. None)
     [Cdc ec1 (Update 100 1), Cdc ec1 (Update 100 2)] {100} ec1 l7_H_dup"
  by (rule l7_canon_continuation[OF l7_wf_dup l7_dup_canon_seg])

theorem fix_l7_same_coordinate_order:
  "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
        [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
          [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

theorem fix_l7_multiplicity:
  "\<not> cdc_segment_between l7_H_dup {100} c0 ec1 [Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1 [Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

theorem fix_l7_coordinate_sorted_insufficient:
  "sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])
   \<and> \<not> cdc_segment_between l7_H_dup {100} c0 ec1
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
proof (intro conjI)
  show "sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])"
    by simp
next
  show "\<not> cdc_segment_between l7_H_dup {100} c0 ec1
          [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]"
    unfolding cdc_segment_between_def l7_H_dup_def cdc_lift_def
    by (simp add: l7_c0_le_ec1 l7_c0_lt_ec1)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup"
    by (rule l7_breaks_continuation[OF l7_dup_canon, where k = 100])
       (simp_all add: Apply_def)
qed

definition l7_H_back :: "(nat, nat) src_history" where
  "l7_H_back = [(ec2, Update 100 5000)]"

lemma l7_wf_back: "wellformed_src_history l7_H_back"
  unfolding l7_H_back_def by (rule l7_wf_one[OF c0_neq_ec2])

lemma l7_back_canon_seg:
  "cdc_segment_between l7_H_back {100} c0 ec2 [Cdc ec2 (Update 100 5000)]"
  unfolding cdc_segment_between_def l7_H_back_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec2)

lemma l7_back_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back"
  by (rule l7_canon_continuation[OF l7_wf_back l7_back_canon_seg])

lemma l7_back_src_ec1: "Src (\<lambda>_. None) l7_H_back ec1 = (\<lambda>_. None)"
proof (rule ext)
  fix k :: nat
  have seg_empty:
    "filter (\<lambda>(c, e). c0 < c \<and> c \<le> ec1 \<and> key_of e = k) l7_H_back = []"
    unfolding l7_H_back_def using l7_not_ec2_le_ec1 by simp
  have "Src (\<lambda>_. None) l7_H_back ec1 k = Src (\<lambda>_. None) l7_H_back c0 k"
    using Src_interval_decomposition[OF l7_wf_back l7_c0_le_ec1,
            of "\<lambda>_. None" k] seg_empty
    by (simp add: Let_def)
  also have "\<dots> = None"
    using Src_at_base[OF l7_wf_back, of "\<lambda>_. None"] by simp
  finally show "Src (\<lambda>_. None) l7_H_back ec1 k = (\<lambda>_. None) k" by simp
qed

theorem fix_l7_frontier_order:
  "(\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>)
   \<and> virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
proof (intro conjI)
  show "\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>"
    unfolding cdc_segment_between_def using l7_not_ec2_le_ec1 by simp
next
  show "virtual_cut_state (\<lambda>_. None) [Cdc ec2 (Update 100 5000)] {100} ec2 l7_H_back"
    by (rule l7_back_canon)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
  proof
    assume "virtual_cut_state (\<lambda>_. None)
              [Cdc ec2 (Update 100 5000)] {100} ec1 l7_H_back"
    hence "restrict (Apply [Cdc ec2 (Update 100 5000)]) {100} (100::nat)
             = restrict (Src (\<lambda>_. None) l7_H_back ec1) {100} 100"
      unfolding virtual_cut_state_def by simp
    thus False
      by (simp add: restrict_def l7_back_src_ec1 Apply_def)
  qed
qed

definition l7_H_del :: "(nat, nat) src_history" where
  "l7_H_del = [(ec1, Update 100 3000), (ec2, Delete 100)]"

lemma l7_wf_del: "wellformed_src_history l7_H_del"
  unfolding l7_H_del_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_del_canon_seg:
  "cdc_segment_between l7_H_del {100} c0 ec2
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Delete 100)]"
  unfolding cdc_segment_between_def l7_H_del_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

lemma l7_del_canon:
  "virtual_cut_state (\<lambda>_. None)
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Delete 100)] {100} ec2 l7_H_del"
  by (rule l7_canon_continuation[OF l7_wf_del l7_del_canon_seg])

theorem fix_l7_delete_omitted:
  "\<not> cdc_segment_between l7_H_del {100} c0 ec2 [Cdc ec1 (Update 100 3000)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del"
proof
  show "\<not> cdc_segment_between l7_H_del {100} c0 ec2 [Cdc ec1 (Update 100 3000)]"
    unfolding cdc_segment_between_def l7_H_del_def cdc_lift_def
    by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)
next
  show "\<not> virtual_cut_state (\<lambda>_. None)
           [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del"
    by (rule l7_breaks_continuation[OF l7_del_canon, where k = 100])
       (simp_all add: Apply_def)
qed

definition l7_H_oos :: "(nat, nat) src_history" where
  "l7_H_oos = [(ec1, Update 100 3000), (ec2, Insert 999 5)]"

lemma l7_wf_oos: "wellformed_src_history l7_H_oos"
  unfolding l7_H_oos_def
  by (rule l7_wf_two[OF ec1_le_ec2 c0_neq_ec1 c0_neq_ec2])

lemma l7_oos_scoped_seg:
  "cdc_segment_between l7_H_oos {100} c0 ec2 [Cdc ec1 (Update 100 3000)]"
  unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

lemma l7_oos_scoped_canon:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos"
  by (rule l7_canon_continuation[OF l7_wf_oos l7_oos_scoped_seg])

lemma l7_oos_full_seg:
  "cdc_segment_between l7_H_oos UNIV c0 ec2
     [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
  unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
  by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)

lemma l7_oos_src_ec2:
  "Src (\<lambda>_. None) l7_H_oos ec2
     = Apply [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
proof -
  have base: "Apply [] = Src (\<lambda>_. None) l7_H_oos c0"
    using Src_at_base[OF l7_wf_oos, of "\<lambda>_. None"] by (simp add: Apply_def)
  have "Apply ([] @ [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)])
          = Src (\<lambda>_. None) l7_H_oos ec2"
    by (rule whole_table_state_continuation[OF l7_wf_oos base l7_oos_full_seg])
  thus ?thesis by simp
qed

theorem fix_l7_scoped_not_whole_table:
  "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos
   \<and> Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2"
proof
  show "virtual_cut_state (\<lambda>_. None) [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_oos"
    by (rule l7_oos_scoped_canon)
next
  show "Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2"
  proof
    assume eq: "Apply [Cdc ec1 (Update 100 3000)] = Src (\<lambda>_. None) l7_H_oos ec2"
    hence "Apply [Cdc ec1 (Update 100 3000)] (999::nat)
             = Src (\<lambda>_. None) l7_H_oos ec2 999"
      by simp
    thus False by (simp add: l7_oos_src_ec2 Apply_def)
  qed
qed

lemma l7_virtual_cut_source_determined:
  fixes b0 :: "'k \<rightharpoonup> 'v"
  assumes "virtual_cut_state b0 \<sigma>1 K f H"
      and "virtual_cut_state b0 \<sigma>2 K f H"
  shows "restrict (Apply \<sigma>1) K = restrict (Apply \<sigma>2) K"
  using assms unfolding virtual_cut_state_def by simp

theorem fix_l7_rechunk_not_sink_repair:
  "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex
   \<and> (\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
            \<longrightarrow> restrict (Apply \<sigma>') l7_scope
              = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope)"
proof
  show "virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex"
    by (rule continuation_positive_witness)
next
  show "\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
              \<longrightarrow> restrict (Apply \<sigma>') l7_scope
                = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope"
  proof (intro allI impI)
    fix \<sigma>' assume "virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex"
    from l7_virtual_cut_source_determined[OF this continuation_positive_witness]
    show "restrict (Apply \<sigma>') l7_scope
            = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope" .
  qed
qed

section \<open>Positive-witness corollaries and the out-of-scope padding boundary\<close>

text \<open>The positive-witness chaining and non-vacuity facts and the out-of-scope
  padding boundary fixture. All are purely source-side --- no certificate
  carrier is involved, so they have no constructed
  @{text Continuation_Fixtures_Inst} counterpart.\<close>

theorem continuation_witness_chained_segment:
  "cdc_segment_between H_ex l7_scope c0 ec4 (l7_seg1 @ l7_seg2)"
  by (rule cdc_segment_between_concat[OF wf_h_ex l7_seg1_segment l7_seg2_segment])

theorem continuation_witness_nonvacuous:
  "l7_scope \<noteq> {} \<and> l7_seg1 \<noteq> [] \<and> l7_seg2 \<noteq> []"
  by (simp add: l7_seg1_def l7_seg2_def)

theorem fix_l7_out_of_scope_padding_rejected_not_loadbearing:
  "\<not> cdc_segment_between l7_H_oos {100} c0 ec2
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]
   \<and> virtual_cut_state (\<lambda>_. None)
        [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)] {100} ec2 l7_H_oos"
proof
  show "\<not> cdc_segment_between l7_H_oos {100} c0 ec2
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)]"
    unfolding cdc_segment_between_def l7_H_oos_def cdc_lift_def
    by (simp add: l7_c0_le_ec2 l7_c0_lt_ec1 l7_c0_lt_ec2 l7_ec1_le_ec2)
next
  show "virtual_cut_state (\<lambda>_. None)
          [Cdc ec1 (Update 100 3000), Cdc ec2 (Insert 999 5)] {100} ec2 l7_H_oos"
    unfolding virtual_cut_state_def
    by (simp add: l7_oos_src_ec2)
qed

end
