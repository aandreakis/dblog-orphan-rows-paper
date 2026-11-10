(*  Title:   Layer3_Witnesses_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer3_Witnesses_Inst
  imports
    Virtual_Cut
    DBLog_Cert_Substrate
    Layer01_Virtual_Cut_Example_Inst
    Layer4_Witnesses_Core
begin

section \<open>Constructed interpretation for the Layer 3 accepted-certificate and
  Layer 4 whole-table witnesses\<close>

text \<open>
  The accepting-certificate witness. The run-side witnesses (the minimum-viable
  witness, the Topic 1/2 witnesses, and the running example) are constructed
  interpretations of @{locale dblog_run_substrate}, whose only obligations are
  the two inherited @{const chunks_list} facts; the certificate side is the
  structurally distinct one, because the checker substrate carries genuine
  proof obligations.

  This theory constructs the positive certificate/evidence/observation witness
  as a @{command global_interpretation} @{text l3i}
  of @{locale dblog_checker_substrate} (the Layer 3/4
  checker-substrate locale of @{text DBLog_Cert_Substrate}),
  whose run side reuses the running-example interpretation @{text ex_model} of
  @{text Layer01_Virtual_Cut_Example_Inst} (the
  @{typ unit} run carrier, the @{type cchunk} two-element chunk datatype) and
  whose certificate / evidence / observation carriers are the one-point type
  @{typ unit}. Unlike the @{text canonical_cert} interpretation of
  @{locale dblog_cert_substrate} in @{text DBLog_Cert_Substrate_Inst}
  --- which inhabits the certificate interface
  with a rejecting verifier and so discharges only the two @{const chunks_list}
  obligations --- this interpretation is \<^emph>\<open>accepting\<close>: it instantiates the four
  primitive checker obligations of @{locale dblog_checker_substrate} (the trust
  boundary) and discharges them \<^emph>\<open>definitionally\<close>, with no certificate axiom.

  Method. The certificate accessors are one-point functions
  targeted at the @{text ex_model} run
  (whose chunk-covered scope @{term "{100, 200, 300}"}, frontier @{const ec4},
  and clean prefix realize the running example): the verifier always accepts,
  the evidence is bound and schema-supported, the cert accessors agree with the
  one @{text ex_model} run @{term "()"}, and faithful observation pins
  @{const b0_ex} / @{const H_ex}. The four checker obligations then reduce by
  @{method simp} to: acceptance gives @{const checker_input_ok} (both schema
  predicates are @{const True}); a materialization exists (the run @{term "()"});
  the materialized run's accessors agree with the certificate
  (@{const cscope_of} / @{const cfrontier_of} / @{thm [source] ex_model.clean_prefix_of_def});
  and the materialized run is wellformed (@{thm [source] ex_model_wellformed}).
  Every ingredient --- the source coordinates (@{const coord_of_nat}
  definitions with proved order lemmas), the run model, and the certificate
  accessors --- is definitional. On this interpretation the theory establishes
  Layer 3 certificate soundness, the Layer 4 whole-table witness (anchor
  @{const ec1}, certified frontier @{const ec4}, reusing the anchor-domain
  facts of @{text Layer4_Witnesses_Core}), and the
  positive non-vacuity witness.
\<close>

subsection \<open>One-point certificate / evidence / observation accessors\<close>

definition l3i_verify :: "unit \<Rightarrow> unit \<Rightarrow> verify_result" where
  "l3i_verify _ _ = Accept"

definition l3i_ev_bound :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
  "l3i_ev_bound _ _ = True"

definition l3i_schema :: "unit \<Rightarrow> unit \<Rightarrow> bool" where
  "l3i_schema _ _ = True"

definition l3i_materializes :: "unit \<Rightarrow> unit \<Rightarrow> unit \<Rightarrow> bool" where
  "l3i_materializes _ _ R = (R = ())"

definition l3i_faithful ::
  "unit \<Rightarrow> (nat \<rightharpoonup> nat) \<Rightarrow> (nat, nat) src_history \<Rightarrow> unit \<Rightarrow> bool" where
  "l3i_faithful _ b0 H Raw = (b0 = b0_ex \<and> H = H_ex \<and> Raw = ())"

subsection \<open>Constructed accepting interpretation of the checker substrate locale\<close>

text \<open>
  The certificate substrate at the running-example run already holds: its run
  side is the @{text ex_model} interpretation of @{locale dblog_run_substrate}
  and the certificate accessors add no obligation beyond the two inherited
  @{const chunks_list} facts. Establishing it as a (local) interpretation
  @{text cert_loc} makes the certificate-side definitional equations of
  @{locale dblog_cert_substrate} --- @{text checker_input_ok_def} and
  @{text cert_accessors_agree_def} --- available
  \<^emph>\<open>unguarded\<close> at these parameters, which discharges the four checker
  obligations below.
\<close>

interpretation cert_loc: dblog_cert_substrate
  cscope_of cfrontier_of cchunks csrc_history_of cchunk_read_result
  ccdc_events_of cchunks_list cchunk_domain cresponsible_chunk
  cchunk_lower_watermark cchunk_upper_watermark cchunk_read_coordinate
  cscope_of cfrontier_of "ex_model.clean_prefix_of"
  l3i_verify Accept l3i_faithful l3i_materializes l3i_ev_bound l3i_schema
  by unfold_locales (simp_all add: cchunks_def cchunks_list_def)

global_interpretation l3i: dblog_checker_substrate
  cscope_of cfrontier_of cchunks csrc_history_of cchunk_read_result
  ccdc_events_of cchunks_list cchunk_domain cresponsible_chunk
  cchunk_lower_watermark cchunk_upper_watermark cchunk_read_coordinate
  cscope_of cfrontier_of "ex_model.clean_prefix_of"
  l3i_verify Accept l3i_faithful l3i_materializes l3i_ev_bound l3i_schema
  "()" "()"
proof (unfold_locales, goal_cases)
  case 1 \<comment> \<open>@{text accepted_input_ok}: acceptance yields a checker-input-ok pair\<close>
  then show ?case
    by (simp add: cert_loc.checker_input_ok_def l3i_ev_bound_def l3i_schema_def)
next
  case 2 \<comment> \<open>@{text accepted_has_materialization}: the run @{term "()"} materializes\<close>
  then show ?case by (simp add: l3i_materializes_def)
next
  case (3 R) \<comment> \<open>@{text accepted_materialization_agrees}: cert accessors agree with the run\<close>
  then show ?case
    by (simp add: cert_loc.cert_accessors_agree_def)
next
  case (4 R b0 H Raw) \<comment> \<open>@{text faithful_materialization_wellformed}: the run is wellformed\<close>
  then have "b0 = b0_ex" and "H = H_ex"
    by (simp_all add: l3i_faithful_def)
  then show ?case
    using ex_model_wellformed by simp
qed

subsection \<open>Constructed Layer 3 certificate soundness\<close>

text \<open>
  The constructed accepting certificate is sound: its clean prefix replays, on
  its scope, to the source state at its frontier (the paper's bridge
  lemma, certificate side). The conclusion unfolds to exactly @{thm [source] ex_model_virtual_cut_holds},
  but is obtained here through the @{locale dblog_checker_substrate} soundness
  theorem from acceptance and faithful observation --- with no certificate axiom.
\<close>

theorem l3i_accepted_virtual_cut_sound:
  "cert_loc.virtual_cut b0_ex () H_ex"
proof (rule l3i.accepted_virtual_cut_sound)
  show "l3i_verify () () = Accept" by (simp add: l3i_verify_def)
  show "l3i_faithful () b0_ex H_ex ()" by (simp add: l3i_faithful_def)
qed

subsection \<open>Constructed Layer 4 whole-table witness\<close>

text \<open>
  The whole-table side conditions on the constructed certificate, derived
  over the running-example source history and the @{text ex_model} clean prefix
  --- the anchor domain at @{const ec1}, the keys touched up to the frontier
  @{const ec4}, and the replay-key containment --- so the Layer 4 specialization
  upgrades the scoped equality to unrestricted table equality with no
  certificate axiom.
\<close>

lemma l3i_touched_between:
  "touched_between H_ex ec1 ec4 = {200, 300}"
  using touched_H_ex_anchor_ec4[unfolded l4_anchor_def] .

lemma l3i_replay_keys:
  "replay_keys (ex_model.clean_prefix_of ()) = {100, 200, 300}"
  unfolding replay_keys_def exm_clean_prefix by auto

lemma l3i_whole_table_claim_scope:
  "cert_loc.whole_table_claim_scope b0_ex () H_ex ec1"
  unfolding cert_loc.whole_table_claim_scope_def
proof (intro conjI)
  show "ec1 \<le> cfrontier_of ()"
    using ec1_le_ec4 by (simp add: exm_frontier less_eq_src_coord_def)
next
  show "anchor_complete_at_boundary b0_ex H_ex ec1 (cscope_of ())"
    unfolding anchor_complete_at_boundary_def
    using l4_anchor_domain[unfolded l4_anchor_def] by (simp add: exm_scope)
next
  show "all_post_anchor_changes_covered H_ex ec1 (cfrontier_of ()) (cscope_of ())"
    unfolding all_post_anchor_changes_covered_def
    using l3i_touched_between by (simp add: exm_frontier exm_scope)
next
  show "no_unclaimed_replay_keys (ex_model.clean_prefix_of ()) (cscope_of ())"
    unfolding no_unclaimed_replay_keys_def
    using l3i_replay_keys by (simp add: exm_scope)
qed

theorem l3i_accepted_whole_table_equality:
  "Apply (ex_model.clean_prefix_of ()) = Src b0_ex H_ex (cfrontier_of ())"
proof (rule l3i.accepted_whole_table_anchor_domain_specialization)
  show "l3i_verify () () = Accept" by (simp add: l3i_verify_def)
  show "l3i_faithful () b0_ex H_ex ()" by (simp add: l3i_faithful_def)
  show "cert_loc.whole_table_claim_scope b0_ex () H_ex ec1"
    by (rule l3i_whole_table_claim_scope)
qed

subsection \<open>Constructed positive witness (non-vacuity)\<close>

text \<open>
  The accepting certificate is non-vacuous: nonempty scope, non-base frontier,
  a value-changing ordinary CDC event whose value reaches the frontier, sound
  virtual cut, and (via the anchor at @{const ec1}) unrestricted whole-table
  equality --- all over the construction, with no axioms involved.
\<close>

theorem l3i_accepted_certificate_positive_witness:
  "\<exists>(b0 :: nat \<rightharpoonup> nat) H.
      l3i_verify () () = Accept
    \<and> l3i_faithful () b0 H ()
    \<and> cert_loc.virtual_cut b0 () H
    \<and> cscope_of () \<noteq> {}
    \<and> cfrontier_of () \<noteq> c0
    \<and> Cdc ec3 (Update (200::nat) (12000::nat)) \<in> set (ex_model.clean_prefix_of ())
    \<and> b0 200 = Some 10000
    \<and> Apply (ex_model.clean_prefix_of ()) 200 = Some 12000
    \<and> Apply (ex_model.clean_prefix_of ()) = Src b0 H (cfrontier_of ())"
proof (intro exI[where x = b0_ex] exI[where x = H_ex] conjI)
  show "l3i_verify () () = Accept" by (simp add: l3i_verify_def)
  show "l3i_faithful () b0_ex H_ex ()" by (simp add: l3i_faithful_def)
  show "cert_loc.virtual_cut b0_ex () H_ex" by (rule l3i_accepted_virtual_cut_sound)
  show "cscope_of () \<noteq> {}" by (simp add: exm_scope)
  show "cfrontier_of () \<noteq> c0" using c0_neq_ec4 by (simp add: exm_frontier)
  show "Cdc ec3 (Update (200::nat) (12000::nat)) \<in> set (ex_model.clean_prefix_of ())"
    by (simp add: exm_clean_prefix)
  show "b0_ex 200 = Some 10000" by (simp add: b0_ex_def)
  show "Apply (ex_model.clean_prefix_of ()) 200 = Some 12000"
    by (simp add: exm_apply)
  show "Apply (ex_model.clean_prefix_of ()) = Src b0_ex H_ex (cfrontier_of ())"
    by (rule l3i_accepted_whole_table_equality)
qed

end
