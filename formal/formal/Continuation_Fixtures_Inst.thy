(*  Title:   Continuation_Fixtures_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Continuation_Fixtures_Inst
  imports
    Continuation_Fixtures_Core
    DBLog_Cert_Substrate
begin

section \<open>Constructed continuation fixtures\<close>

text \<open>
  Constructed continuation fixtures. The negative / boundary continuation rows
  are stated over the plain source histories (@{const l7_H_cov} /
  @{const l7_H_future} / @{const l7_H_dup} /
  @{const l7_H_back} / @{const l7_H_del} / @{const l7_H_oos}) and segments,
  all ordinary @{command definition}s; those rows live in
  @{theory DBLog_Virtual_Cuts.Continuation_Fixtures_Core} and are reused here
  by import. This theory constructs the one row that needs a certificate
  carrier: the ``extended certificate'' fixture, which separates accessor-level
  algebra from verifier acceptance.

  The construction is a certificate-substrate interpretation at its smallest
  (the same shape as the @{text cf} interpretations of
  @{text Layer3_Fixtures_Inst} / @{text Layer4_Fixtures_Inst}): a
  one-constructor certificate datatype
  @{text l7f_cert} whose scope / frontier / clean-prefix
  / verifier functions carry exactly the extended-certificate values (scope
  @{term "{100::nat}"}, frontier @{const ec1}, clean prefix
  @{term "[Cdc ec1 (Update 100 3000)]"}, verdict @{const Reject}), hosted
  by a @{command global_interpretation} @{text cext} of
  @{locale dblog_cert_substrate} at a degenerate @{typ unit} run (the row uses no
  run accessor). The accessor-level virtual cut is then established by
  the canonical-continuation lemmas (@{thm [source] l7_canon_continuation} +
  @{thm [source] l7_cov_canon_seg}), and the verifier rejection by
  @{text simp} --- with no axioms.
\<close>

subsection \<open>Constructed extended certificate\<close>

datatype l7f_cert = CExt

fun l7f_scope :: "l7f_cert \<Rightarrow> nat set" where
  "l7f_scope CExt = {100}"

fun l7f_frontier :: "l7f_cert \<Rightarrow> frontier" where
  "l7f_frontier CExt = ec1"

fun l7f_clean_prefix :: "l7f_cert \<Rightarrow> (nat, nat) replay_event list" where
  "l7f_clean_prefix CExt = [Cdc ec1 (Update 100 3000)]"

fun l7f_verify :: "l7f_cert \<Rightarrow> unit \<Rightarrow> verify_result" where
  "l7f_verify CExt _ = Reject"

text \<open>The run side is a degenerate @{typ unit} run (the extended-certificate row
  uses no run accessor); @{locale dblog_cert_substrate} assumes nothing beyond the
  two inherited @{const chunks_list} obligations (@{term "set [] = {}"},
  @{term "distinct []"}), so the interpretation introduces no axiom. The
  faithfulness / materialization / binding / schema parameters are unused here and
  supplied as trivial constants.\<close>

global_interpretation cext: dblog_cert_substrate
  "\<lambda>_::unit. ({} :: nat set)"                                       \<comment> \<open>@{text scope_of}\<close>
  "\<lambda>_::unit. c0"                                                    \<comment> \<open>@{text frontier_of}\<close>
  "\<lambda>_::unit. ({} :: nat set)"                                       \<comment> \<open>chunks\<close>
  "\<lambda>_::unit. ([] :: (nat, nat) src_history)"                        \<comment> \<open>@{text src_history_of}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. \<lambda>_::nat. (None :: nat option option)"          \<comment> \<open>@{text chunk_read_result}\<close>
  "\<lambda>_::unit. ([] :: (src_coord \<times> (nat, nat) source_event) list)"    \<comment> \<open>@{text cdc_events_of}\<close>
  "\<lambda>_::unit. ([] :: nat list)"                                      \<comment> \<open>@{text chunks_list}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. ({} :: nat set)"                              \<comment> \<open>@{text chunk_domain}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. (None :: nat option)"                         \<comment> \<open>@{text responsible_chunk}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. c0"                                           \<comment> \<open>@{text chunk_lower_watermark}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. c0"                                           \<comment> \<open>@{text chunk_upper_watermark}\<close>
  "\<lambda>_::unit. \<lambda>_::nat. c0"                                           \<comment> \<open>@{text chunk_read_coordinate}\<close>
  l7f_scope l7f_frontier l7f_clean_prefix
  l7f_verify Accept
  "\<lambda>_::unit. \<lambda>_::(nat \<rightharpoonup> nat). \<lambda>_::(nat, nat) src_history. \<lambda>_::unit. False"
                                                                    \<comment> \<open>@{text faithful_source_observation}\<close>
  "\<lambda>_::l7f_cert. \<lambda>_::unit. \<lambda>_::unit. False"                         \<comment> \<open>@{text materializes_run}\<close>
  "\<lambda>_::l7f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text evidence_bound_to_cert}\<close>
  "\<lambda>_::l7f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text source_side_schema_supported}\<close>
  by unfold_locales simp_all


subsection \<open>Accessor equality of an extended certificate is not verifier acceptance (constructed)\<close>

text \<open>Read through its accessors, @{const CExt} satisfies the accessor-level
  @{const cext.virtual_cut} predicate (its clean prefix replays to the source state
  on its scope at its frontier, by the canonical-continuation lemmas); yet
  the verifier rejects it. Accessor-level algebra is strictly weaker than verifier
  acceptance.\<close>

lemma cext_extended_cert_virtual_cut:
  "cext.virtual_cut (\<lambda>_. None) CExt l7_H_cov"
  unfolding cext.virtual_cut_def virtual_cut_state_def
proof (rule l7_canon_continuation[OF l7_wf_cov, unfolded virtual_cut_state_def])
  show "cdc_segment_between l7_H_cov (l7f_scope CExt) c0
          (l7f_frontier CExt) (l7f_clean_prefix CExt)"
    by (simp add: l7_cov_canon_seg)
qed

theorem fix_l7_extended_cert_not_accepted_constructed:
  "cext.virtual_cut (\<lambda>_. None) CExt l7_H_cov
   \<and> l7f_verify CExt () \<noteq> Accept"
  using cext_extended_cert_virtual_cut by simp


subsection \<open>Constructed continuation negative / boundary fixture bundle\<close>

text \<open>The eleven negative / boundary continuation conjuncts in one statement,
  with the two extended-certificate conjuncts over the construction
  (@{const cext.virtual_cut} on @{const CExt} and @{const l7f_verify}); the
  remaining conjuncts are the carrier-independent fixtures of
  @{theory DBLog_Virtual_Cuts.Continuation_Fixtures_Core}, reused by import.
  Of the twelve @{text fix_l7_} facts, the out-of-scope padding boundary fact
  (@{text fix_l7_out_of_scope_padding_rejected_not_loadbearing}, in
  @{theory DBLog_Virtual_Cuts.Continuation_Fixtures_Core}) is deliberately
  not bundled: it exhibits a padded segment that @{text cdc_segment_between}
  rejects while the continuation conclusion still holds, demonstrating a
  non-load-bearing premise rather than a rejection. The whole continuation
  negative-fixture bundle is established with no axioms anywhere.\<close>

theorem continuation_negative_fixture_bundle_constructed:
  "\<not> virtual_cut_state (\<lambda>_. None) [] {100} ec1 l7_H_cov
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 7777)] {100} ec1 l7_H_cov
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000), Cdc ec2 (Update 100 9000)]
         {100} ec1 l7_H_future
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> sorted (map cdc_coord [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)])
   \<and> \<not> cdc_segment_between l7_H_dup {100} c0 ec1
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)]
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 2), Cdc ec1 (Update 100 1)] {100} ec1 l7_H_dup
   \<and> (\<forall>\<delta>. \<not> cdc_segment_between l7_H_back {100} ec2 ec1 \<delta>)
   \<and> \<not> virtual_cut_state (\<lambda>_. None)
         [Cdc ec1 (Update 100 3000)] {100} ec2 l7_H_del
   \<and> Apply [Cdc ec1 (Update 100 3000)] \<noteq> Src (\<lambda>_. None) l7_H_oos ec2
   \<and> cext.virtual_cut (\<lambda>_. None) CExt l7_H_cov
   \<and> l7f_verify CExt () \<noteq> Accept
   \<and> virtual_cut_state (\<lambda>_. None) (l7_seg1 @ l7_seg2) l7_scope ec4 H_ex
   \<and> (\<forall>\<sigma>'. virtual_cut_state (\<lambda>_. None) \<sigma>' l7_scope ec4 H_ex
            \<longrightarrow> restrict (Apply \<sigma>') l7_scope
              = restrict (Apply (l7_seg1 @ l7_seg2)) l7_scope)"
  using fix_l7_missing_event fix_l7_event_not_in_history fix_l7_future_event
        fix_l7_same_coordinate_order fix_l7_multiplicity
        fix_l7_coordinate_sorted_insufficient fix_l7_frontier_order
        fix_l7_delete_omitted fix_l7_scoped_not_whole_table
        fix_l7_extended_cert_not_accepted_constructed fix_l7_rechunk_not_sink_repair
  by blast

end
