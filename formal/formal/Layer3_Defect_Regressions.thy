(*  Title:       Layer3_Defect_Regressions.thy
    Author:      Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause

    Permanent kernel-checked regression for a fixture defect found by an
    external review of the released 2.0 artifact and repaired in 2.1.
    The label D15 in the lemma names is that review's defect numbering,
    kept so the regression stays traceable across the development's
    history.

    The defect: the same-evidence negative control (CAcc, EAcc) in
    Layer3_Fixtures_Inst advertised a certificate/run accessor mismatch,
    but its bundle failed to materialize a run, so run coherence already
    failed for that confounding reason and the accessor comparison the
    control advertises was never exercised.  The repair makes
    (CAcc, EAcc) materialize; the lemmas below pin reachability of the
    accessor comparison so the control cannot regress into vacuity.
*)

theory Layer3_Defect_Regressions
  imports Layer3_Fixtures_Inst
begin

section \<open>D15 regression: the accessor fixture reaches comparison\<close>

lemma d15_accessor_mismatch_is_present:
  "\<not> cf.cert_accessors_agree CAcc ()"
  unfolding cf.cert_accessors_agree_def
  by (simp add: cf_clean_prefix_empty)

lemma d15_materializes_then_fails_accessor_agreement:
  "l3f_verify CAcc EAcc = Accept
   \<and> l3f_materializes CAcc EAcc ()
   \<and> \<not> cf.cert_accessors_agree CAcc ()
   \<and> \<not> cf.cert_run_coherent CAcc EAcc ()"
  unfolding cf.cert_run_coherent_def
  using d15_accessor_mismatch_is_present by simp

end
