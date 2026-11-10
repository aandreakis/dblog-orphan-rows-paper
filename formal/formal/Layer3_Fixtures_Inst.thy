(*  Title:   Layer3_Fixtures_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer3_Fixtures_Inst
  imports
    Layer3_Fixtures_Core
    Layer3_Witnesses_Inst
begin

section \<open>Constructed Layer 3 fixtures\<close>

text \<open>
  Constructed Layer 3 fixtures: the rejection, boundary, and faithfulness facts
  for the certificate / evidence / checker interface, established over explicit
  finite constructions. The constructed carriers (@{text l3f_cert} /
  @{text l3f_ev} / @{text l3f_raw} below) are small datatypes carrying exactly
  the certificate, evidence, and raw-observation values the fixtures exercise;
  the verifier, materialization, faithfulness, binding, and schema functions
  over them are ordinary @{command fun} definitions, so the theory introduces
  no axioms.

  The fixture rows split into three kinds:

    \<^item> \<^bold>\<open>rejecting and boundary rows\<close> (unmapped evidence, cert/evidence binding
        mismatch, an accept-without-materialization pair, a mismatched
        alternative run, faithfulness negatives, an empty-scope certificate, an
        unsupported-verdict evidence). None of these needs a \<^emph>\<open>wellformed\<close>
        materialized run, so they are established here over a single
        @{command global_interpretation} @{text cf} of
        @{locale dblog_cert_substrate} (the Layer 3/4 certificate-substrate
        locale of @{theory DBLog_Virtual_Cuts.DBLog_Cert_Substrate}) whose run
        side is a degenerate @{typ unit} run (no chunks, no observed CDC, hence
        empty clean prefix) and whose certificate / evidence / observation
        carriers are the small finite datatypes. Every fixture fact holds by
        @{text simp} evaluation.

    \<^item> the \<^bold>\<open>non-circular checker-substrate obligation row\<close> exhibits the
        \<^emph>\<open>accepting\<close> certificate satisfying the four primitive checker
        obligations, which requires a wellformed materialized run. It is
        established over the accepting interpretation @{text l3i} of
        @{locale dblog_checker_substrate} from
        @{text Layer3_Witnesses_Inst} (run side
        @{text ex_model}, the constructed running-example run), reusing
        @{thm [source] ex_model_wellformed}.

    \<^item> the \<^bold>\<open>pure coherence / determinacy / empty-scope lemmas\<close> ---
        @{text "layer3_cert_accessor_determinacy"},
        @{text "layer3_mismatched_prefix_not_accessor_agree"}, and
        @{text "layer3_empty_scope_virtual_cut_boundary"} --- reference no
        certificate carrier at all: they range over the global cert-side
        definitions parametrically. They live in
        @{theory DBLog_Virtual_Cuts.Layer3_Fixtures_Core}.

  The definitions @{const l3_wrong_b0} / @{const l3_wrong_H} of
  @{theory DBLog_Virtual_Cuts.Layer3_Fixtures_Core} are ordinary
  @{command definition}s and are reused here, together with their mismatch
  lemmas @{thm [source] l3_wrong_b0_neq} / @{thm [source] l3_wrong_H_neq}, for
  the base-state / history faithfulness negatives.
\<close>


subsection \<open>Constructed certificate / evidence / observation carriers\<close>

text \<open>Small finite carriers holding exactly the certificate, evidence, and
  raw-observation values exercised by the Layer 3 fixtures.\<close>

datatype l3f_cert = CAcc | COther | CEmpty | CNoWit
datatype l3f_ev   = EAcc | EUnmapped | ENoWit | EAlt | EUnknown
datatype l3f_raw  = RawOk | RawBad


subsection \<open>Constructed certificate-side accessor and predicate functions\<close>

text \<open>The accepting certificate @{const CAcc} carries the running example's scope
  and base coordinate; @{const CEmpty} carries the empty scope. The clean prefix
  is a fixed non-empty list, so it differs from the degenerate run's empty clean
  prefix --- the sole discriminator in the coherence-mismatch rows.\<close>

fun l3f_scope :: "l3f_cert \<Rightarrow> nat set" where
  "l3f_scope CEmpty = {}"
| "l3f_scope _ = {100, 200, 300}"

fun l3f_frontier :: "l3f_cert \<Rightarrow> frontier" where
  "l3f_frontier _ = c0"

fun l3f_clean_prefix :: "l3f_cert \<Rightarrow> (nat, nat) replay_event list" where
  "l3f_clean_prefix _ = [Refresh (200::nat) (Some (10000::nat)) c0]"

text \<open>The verifier accepts the bound, schema-supported pairs
  (@{term "(CAcc, EAcc)"} and @{term "(CNoWit, ENoWit)"}), returns
  @{const Unsupported} for the schema-unsupported @{term "(CAcc, EUnknown)"},
  and rejects everything else.\<close>

fun l3f_verify :: "l3f_cert \<Rightarrow> l3f_ev \<Rightarrow> verify_result" where
  "l3f_verify CAcc EAcc = Accept"
| "l3f_verify CNoWit ENoWit = Accept"
| "l3f_verify CAcc EUnknown = Unsupported"
| "l3f_verify _ _ = Reject"

fun l3f_bound :: "l3f_cert \<Rightarrow> l3f_ev \<Rightarrow> bool" where
  "l3f_bound CAcc EAcc = True"
| "l3f_bound CNoWit ENoWit = True"
| "l3f_bound _ _ = False"

fun l3f_schema :: "l3f_cert \<Rightarrow> l3f_ev \<Rightarrow> bool" where
  "l3f_schema CAcc EAcc = True"
| "l3f_schema CNoWit ENoWit = True"
| "l3f_schema _ _ = False"

text \<open>The accepted same-evidence bundle @{term "(CAcc, EAcc)"} and the
  mismatched alternative bundle @{term "(CAcc, EAlt)"} both materialize to
  the degenerate run @{term "()"}.  This makes the former a genuine accessor
  mismatch fixture: materialization succeeds before accessor agreement is
  tested.  The accept-without-witness pair @{term "(CNoWit, ENoWit)"}
  materializes to nothing, modeling a checker whose acceptance is not backed
  by a witness run.\<close>

fun l3f_materializes :: "l3f_cert \<Rightarrow> l3f_ev \<Rightarrow> unit \<Rightarrow> bool" where
  "l3f_materializes CAcc EAcc _ = True"
| "l3f_materializes CAcc EAlt _ = True"
| "l3f_materializes _ _ _ = False"

text \<open>Faithful observation pins the running-example base state, history, and the
  distinguished good raw observation; every other evidence / base-state /
  history / raw combination is unfaithful.\<close>

fun l3f_faithful ::
  "l3f_ev \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> (nat, nat) src_history \<Rightarrow> l3f_raw \<Rightarrow> bool" where
  "l3f_faithful EAcc b0 H Raw = (b0 = b0_ex \<and> H = H_ex \<and> Raw = RawOk)"
| "l3f_faithful _ _ _ _ = False"


subsection \<open>Constructed certificate substrate interpretation (rejecting fixtures)\<close>

text \<open>The run side is a degenerate @{typ unit} run: no chunks, no observed CDC
  events, empty source history. @{locale dblog_cert_substrate} assumes nothing
  beyond the two inherited @{const chunks_list} obligations, which hold
  definitionally (@{term "set [] = {}"}, @{term "distinct []"}), so the
  interpretation introduces no axiom.\<close>

global_interpretation cf: dblog_cert_substrate
  "\<lambda>_::unit. {100::nat, 200, 300}"                                  \<comment> \<open>@{text scope_of}\<close>
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
  l3f_scope l3f_frontier l3f_clean_prefix
  l3f_verify Accept l3f_faithful l3f_materializes l3f_bound l3f_schema
  by unfold_locales simp_all

text \<open>The degenerate run has an empty clean prefix (no chunk reads, no CDC
  replays).\<close>

lemma cf_clean_prefix_empty: "cf.clean_prefix_of () = []"
  unfolding cf.clean_prefix_of_def canonical_clean_prefix_def cdc_event_replays_def
  by (simp add: List.map_filter_simps)

lemma l3f_clean_prefix_nonempty: "l3f_clean_prefix C \<noteq> []"
  by simp


subsection \<open>Certificate/evidence binding failures\<close>

text \<open>Unmapped evidence: rejected, not a valid checker input (not bound), and
  materializes to no run.\<close>

theorem layer3_unmapped_certificate_evidence_rejected_constructed:
  "l3f_verify CAcc EUnmapped \<noteq> Accept
   \<and> \<not> cf.checker_input_ok CAcc EUnmapped
   \<and> (\<forall>R. \<not> l3f_materializes CAcc EUnmapped R)"
  by (simp add: cf.checker_input_ok_def)

text \<open>Certificate/evidence binding mismatch: a different certificate against the
  positive evidence is rejected and not a valid checker input (not bound).\<close>

theorem layer3_cert_evidence_binding_mismatch_rejected_constructed:
  "l3f_verify COther EAcc \<noteq> Accept
   \<and> \<not> cf.checker_input_ok COther EAcc"
  by (simp add: cf.checker_input_ok_def)


subsection \<open>Materialization and non-circular substrate\<close>

text \<open>Accept-without-witness: the pair @{term "(CNoWit, ENoWit)"} is accepted and
  a valid checker input, yet materializes to no run. So it cannot satisfy the
  checker-substrate materialization obligation --- assuming it would yields a
  contradiction.\<close>

lemma l3f_nowit_checker_input_ok: "cf.checker_input_ok CNoWit ENoWit"
  by (simp add: cf.checker_input_ok_def)

theorem layer3_accepted_but_witness_undefined_blocks_substrate_constructed:
  assumes materialization_obligation:
    "\<lbrakk>l3f_verify CNoWit ENoWit = Accept;
      cf.checker_input_ok CNoWit ENoWit\<rbrakk>
      \<Longrightarrow> \<exists>R. l3f_materializes CNoWit ENoWit R"
  shows False
proof -
  have "\<exists>R. l3f_materializes CNoWit ENoWit R"
    using materialization_obligation l3f_nowit_checker_input_ok by simp
  thus False by simp
qed

text \<open>The accepting certificate satisfies the four primitive checker obligations
  over a wellformed materialized run --- the non-circular checker-spec row,
  established over the accepting interpretation @{text l3i} of
  @{text Layer3_Witnesses_Inst} (run side
  @{text ex_model}), so the constructed materialization is the wellformed
  running-example run (@{thm [source] ex_model_wellformed}). The two
  certificate-side predicates are stated component-wise: @{const checker_input_ok}
  as @{text "l3i_ev_bound \<and> l3i_schema"} and @{const cert_accessors_agree} as the
  three accessor equalities --- their @{locale dblog_cert_substrate} definitions
  unfolded, since those definitions live in the parent locale and so carry no
  @{text "l3i."}-qualified name (the @{text cert_loc} interpretation that
  exposes them is local to its defining theory).\<close>

theorem layer3_non_circular_checker_spec_obligations_constructed:
  "l3i_verify () () = Accept
   \<and> (l3i_ev_bound () () \<and> l3i_schema () ())
   \<and> (\<exists>R. l3i_materializes () () R)
   \<and> (\<forall>R. l3i_materializes () () R
        \<longrightarrow> cscope_of () = cscope_of R
          \<and> cfrontier_of () = cfrontier_of R
          \<and> ex_model.clean_prefix_of () = ex_model.clean_prefix_of R)
   \<and> (\<forall>R b0 H Raw.
        l3i_materializes () () R
        \<longrightarrow> l3i_faithful () b0 H Raw
        \<longrightarrow> ex_model.wellformed_dblog_run b0 R H)"
  using ex_model_wellformed
  by (auto simp add: l3i_verify_def l3i_ev_bound_def l3i_schema_def
                     l3i_materializes_def l3i_faithful_def)


subsection \<open>Coherence and determinacy\<close>

text \<open>A mismatched alternative bundle: rejected, yet materializing to the
  degenerate run, whose empty clean prefix differs from the certificate's
  clean prefix --- so the certificate accessors do not agree with the run and
  the pair is not coherent.\<close>

theorem layer3_two_evidence_bundle_determinacy_fixture_constructed:
  "l3f_verify CAcc EAlt \<noteq> Accept
   \<and> l3f_materializes CAcc EAlt ()
   \<and> \<not> cf.cert_run_coherent CAcc EAlt ()"
  unfolding cf.cert_run_coherent_def cf.cert_accessors_agree_def
  by (simp add: cf_clean_prefix_empty)

theorem layer3_cert_run_coherence_mismatch_rejected_constructed:
  "l3f_materializes CAcc EAcc ()
   \<and> \<not> cf.cert_accessors_agree CAcc ()
   \<and> \<not> cf.cert_run_coherent CAcc EAcc ()"
  unfolding cf.cert_run_coherent_def cf.cert_accessors_agree_def
  by (simp add: cf_clean_prefix_empty)

\<comment> \<open>Alias of @{text layer3_cert_run_coherence_mismatch_rejected_constructed},
     mirroring the dual-named Layer 3 fixture-table row.\<close>
theorem layer3_same_evidence_mismatched_run_not_coherent_constructed:
  "\<not> cf.cert_run_coherent CAcc EAcc ()"
  using layer3_cert_run_coherence_mismatch_rejected_constructed by blast


subsection \<open>Faithfulness negatives\<close>

text \<open>The accepting certificate is a valid checker input, but acceptance does not
  certify the raw observation: a wrong raw observation, a wrong base state, or a
  wrong history all fail faithfulness.\<close>

theorem layer3_raw_observation_faithfulness_negative_constructed:
  "l3f_verify CAcc EAcc = Accept
   \<and> cf.checker_input_ok CAcc EAcc
   \<and> \<not> l3f_faithful EAcc b0_ex H_ex RawBad"
  by (simp add: cf.checker_input_ok_def)

theorem layer3_raw_base_state_mismatch_rejected_constructed:
  "\<not> l3f_faithful EAcc l3_wrong_b0 H_ex RawOk"
  using l3_wrong_b0_neq by simp

theorem layer3_wrong_history_mismatch_rejected_constructed:
  "\<not> l3f_faithful EAcc b0_ex l3_wrong_H RawOk"
  using l3_wrong_H_neq by simp


subsection \<open>Empty-scope boundary\<close>

text \<open>An empty-scope certificate vacuously satisfies the cert-side virtual cut,
  yet has empty scope, so it is not a positive witness; the accepting
  certificate's scope is non-empty.\<close>

theorem layer3_empty_scope_boundary_not_positive_witness_constructed:
  "cf.virtual_cut b0_ex CEmpty H_ex
   \<and> l3f_scope CEmpty = {}
   \<and> l3f_scope CAcc \<noteq> {}"
  unfolding cf.virtual_cut_def virtual_cut_state_def restrict_def
  by simp


subsection \<open>Unknown or ignored evidence fields\<close>

text \<open>Evidence outside the source-side schema yields an @{const Unsupported}
  verdict, is not accepted, and is not a valid checker input.\<close>

theorem layer3_unknown_ignored_field_rejected_constructed:
  "l3f_verify CAcc EUnknown = Unsupported
   \<and> l3f_verify CAcc EUnknown \<noteq> Accept
   \<and> \<not> cf.checker_input_ok CAcc EUnknown"
  by (simp add: cf.checker_input_ok_def)


subsection \<open>Fixture bundle\<close>

text \<open>The constructed Layer 3 negative and boundary fixture bundle: the nine
  rejection / boundary facts above in one statement, all established over the
  construction.\<close>

theorem layer3_fixture_bundle_constructed:
  "l3f_verify CAcc EUnmapped \<noteq> Accept
   \<and> (\<forall>R. \<not> l3f_materializes CAcc EUnmapped R)
   \<and> l3f_verify CAcc EAlt \<noteq> Accept
   \<and> \<not> cf.cert_run_coherent CAcc EAcc ()
   \<and> \<not> l3f_faithful EAcc b0_ex H_ex RawBad
   \<and> \<not> l3f_faithful EAcc l3_wrong_b0 H_ex RawOk
   \<and> l3f_scope CEmpty = {}
   \<and> l3f_verify CAcc EUnknown = Unsupported
   \<and> l3f_verify COther EAcc \<noteq> Accept
   \<and> \<not> l3f_faithful EAcc b0_ex l3_wrong_H RawOk"
  using layer3_unmapped_certificate_evidence_rejected_constructed
        layer3_two_evidence_bundle_determinacy_fixture_constructed
        layer3_cert_run_coherence_mismatch_rejected_constructed
        layer3_raw_observation_faithfulness_negative_constructed
        layer3_raw_base_state_mismatch_rejected_constructed
        layer3_empty_scope_boundary_not_positive_witness_constructed
        layer3_unknown_ignored_field_rejected_constructed
        layer3_cert_evidence_binding_mismatch_rejected_constructed
        layer3_wrong_history_mismatch_rejected_constructed
  by blast

text \<open>
  The certificate-dependent Layer 3 fixture rows hold over the construction
  --- the rejecting / boundary / faithfulness rows over the @{text cf}
  interpretation, the non-circular checker-spec row over the @{text l3i}
  interpretation. Together with the carrier-independent pure coherence /
  determinacy / empty-scope lemmas of
  @{theory DBLog_Virtual_Cuts.Layer3_Fixtures_Core}, the whole Layer 3 fixture
  bundle is established with no axioms anywhere.
\<close>

end
