(*  Title:   Layer3_Fixtures_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer3_Fixtures_Core
  imports Layer01_Virtual_Cut_Example_Core Virtual_Cut
begin

section \<open>Carrier-independent Layer 3 fixture data\<close>

text \<open>
  The carrier-independent data of the Layer 3 fixture family, used by the
  constructed interpretation @{text Layer3_Fixtures_Inst}: the wrong-base-state
  and wrong-history values @{text l3_wrong_b0} / @{text l3_wrong_H} (ordinary
  @{command definition}s over @{const b0_ex} / @{const H_ex}, with no
  certificate / evidence / raw-observation carrier) and their mismatch lemmas,
  together with the parametric certificate-coherence facts below. The theory
  imports @{theory DBLog_Virtual_Cuts.Layer01_Virtual_Cut_Example_Core} (for
  @{const b0_ex} / @{const H_ex}) and @{theory DBLog_Virtual_Cuts.Virtual_Cut}
  (for the certificate accessors and @{const virtual_cut} used by those
  parametric facts).
\<close>

definition l3_wrong_b0 :: "nat \<rightharpoonup> nat" where
  "l3_wrong_b0 = (\<lambda>k. if k = 200 then Some (999::nat) else b0_ex k)"

definition l3_wrong_H :: "(nat, nat) src_history" where
  "l3_wrong_H = []"

lemma l3_wrong_b0_neq:
  "l3_wrong_b0 \<noteq> b0_ex"
  unfolding l3_wrong_b0_def b0_ex_def
  by (rule notI, drule fun_cong[where x=200], simp)

lemma l3_wrong_H_neq:
  "l3_wrong_H \<noteq> H_ex"
  unfolding l3_wrong_H_def H_ex_def
  by simp

section \<open>Parametric certificate-coherence facts\<close>

text \<open>Coherence / determinacy / empty-scope facts that are parametric over the
  global certificate/run accessors (hence the
  @{theory DBLog_Virtual_Cuts.Virtual_Cut} import). They quantify over
  arbitrary certificates and runs, so they need no constructed
  @{text Layer3_Fixtures_Inst} counterpart.\<close>

lemma layer3_cert_accessor_determinacy:
  assumes "cert_accessors_agree C R1"
      and "cert_accessors_agree C R2"
  shows "scope_of R1 = scope_of R2
       \<and> frontier_of R1 = frontier_of R2
       \<and> clean_prefix_of R1 = clean_prefix_of R2"
  using assms
  unfolding cert_accessors_agree_def
  by simp

lemma layer3_mismatched_prefix_not_accessor_agree:
  assumes "cert_accessors_agree C R1"
      and "clean_prefix_of R2 \<noteq> clean_prefix_of R1"
  shows "\<not> cert_accessors_agree C R2"
  using assms
  unfolding cert_accessors_agree_def
  by auto

theorem layer3_empty_scope_virtual_cut_boundary:
  assumes "scope C = {}"
  shows "virtual_cut b0 C H"
  using assms
  unfolding virtual_cut_def virtual_cut_state_def restrict_def
  by simp

end
