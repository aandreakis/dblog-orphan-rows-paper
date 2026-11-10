(*  Title:   DBLog_Cert_Substrate.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory DBLog_Cert_Substrate
  imports DBLog_Run_Substrate_Layer2 Virtual_Cut_Core
begin

section \<open>Layer 3/4 certificate substrate as a locale hierarchy (abstract carriers)\<close>

text \<open>
  The certificate side of the development as
  a locale hierarchy over abstract carrier type variables, abstracting the
  concrete @{text cert} /
  @{text evidence} / @{text raw_observation} datatypes and the
  certificate/evidence/checker definitions of @{text Virtual_Cut}.

    \<^item> @{text dblog_cert_substrate} extends @{locale dblog_run_substrate} with
        the certificate, evidence, and observation accessors fixed over plain
        type variables @{typ 'cert} / @{typ 'evidence} / @{typ 'raw}, and
        states the cert-side definitions (@{text virtual_cut},
        @{text checker_input_ok}, @{text cert_accessors_agree},
        @{text cert_run_coherent}) and the cert-bound Layer 4 whole-table
        claim-scope (@{text whole_table_claim_scope}) with bodies matching
        the global ones. It assumes nothing beyond the two run-substrate
        @{text chunks_list} obligations it inherits.

        The verifier is fixed \<^emph>\<open>polymorphically\<close> in its result type:
        @{text "verify :: 'cert \<Rightarrow> 'evidence \<Rightarrow> 'vres"} with a
        distinguished accepting value @{text "accept_value :: 'vres"}. The
        public @{text Virtual_Cut.verify_result} datatype and its
        @{text Accept} constructor are \<^emph>\<open>not\<close> a dependency of this locale; an
        interpretation may instantiate
        @{text "'vres = verify_result"} and @{text "accept_value = Accept"}
        (the canonical interpretation in @{text DBLog_Cert_Substrate_Inst}
        does exactly that).

    \<^item> @{text dblog_checker_substrate} extends @{text dblog_cert_substrate}
        with a fixed certificate @{text C} and evidence @{text E} and the four
        primitive checker obligations (the trust boundary), stated as
        @{text "verify C E = accept_value"}, and proves the Layer 3 soundness
        theorems --- @{text accepted_certificate_implies_wellformed_run} and the
        headline @{text accepted_virtual_cut_sound} --- together with the Layer 4
        whole-table specialization
        @{text accepted_whole_table_anchor_domain_specialization}, just as
        the global @{text layer3_checker_substrate} does (there via the
        context extension in @{text Layer4_Whole_Table}), but over the
        abstract carriers.

  The carrier-independent ``pure'' core (@{const virtual_cut_state}, the
  Layer 4 anchor / table-scope definitions @{const table_scope_between} /
  @{const anchor_complete_at_boundary} / @{const all_post_anchor_changes_covered} /
  @{const no_unclaimed_replay_keys}, and the outside-scope bridge lemma
  @{thm [source] whole_table_equality_from_scoped_equality}) reference no
  certificate accessor and live in @{text Virtual_Cut_Core}; the locale reuses
  them directly. The Layer 2 run-side soundness theorem
  @{thm [source] dblog_run_substrate.wellformed_run_implies_virtual_cut} is
  inherited from @{locale dblog_run_substrate}.

  The concrete counterparts --- the @{text cert} / @{text evidence} datatypes,
  the global @{text layer3_checker_substrate} locale, and the global Layer 3/4
  theorems --- live in @{text Virtual_Cut} and @{text Layer4_Whole_Table}; the
  canonical concrete interpretation of this hierarchy lives in
  @{text DBLog_Cert_Substrate_Inst}.
\<close>

subsection \<open>Certificate substrate locale\<close>

text \<open>
  The run accessors are re-declared in the @{text "for"} clause so the
  carrier type variables @{typ 'run} / @{typ 'chunk} / @{typ 'k} / @{typ 'v}
  are under this locale's control and are shared by the certificate accessors
  added below; a plain @{text "dblog_run_substrate +"} import would alpha-rename
  the inherited type parameters, leaving the certificate key/value/run types
  disconnected from the run side.
\<close>

locale dblog_cert_substrate =
  dblog_run_substrate
    scope_of frontier_of chunks src_history_of chunk_read_result
    cdc_events_of chunks_list chunk_domain responsible_chunk
    chunk_lower_watermark chunk_upper_watermark chunk_read_coordinate
  for scope_of               :: "'run \<Rightarrow> ('k::linorder) set"
  and frontier_of            :: "'run \<Rightarrow> frontier"
  and chunks                 :: "'run \<Rightarrow> 'chunk set"
  and src_history_of         :: "'run \<Rightarrow> ('k, 'v) src_history"
  and chunk_read_result      :: "'run \<Rightarrow> 'chunk \<Rightarrow> 'k \<Rightarrow> 'v option option"
  and cdc_events_of          :: "'run \<Rightarrow> (src_coord \<times> ('k, 'v) source_event) list"
  and chunks_list            :: "'run \<Rightarrow> 'chunk list"
  and chunk_domain           :: "'run \<Rightarrow> 'chunk \<Rightarrow> 'k set"
  and responsible_chunk      :: "'run \<Rightarrow> 'k \<Rightarrow> 'chunk option"
  and chunk_lower_watermark  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
  and chunk_upper_watermark  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
  and chunk_read_coordinate  :: "'run \<Rightarrow> 'chunk \<Rightarrow> src_coord"
  +
  fixes scope        :: "'cert \<Rightarrow> 'k set"
    and frontier     :: "'cert \<Rightarrow> frontier"
    and clean_prefix :: "'cert \<Rightarrow> ('k, 'v) replay_event list"
    and verify       :: "'cert \<Rightarrow> 'evidence \<Rightarrow> 'vres"
    and accept_value :: "'vres"
    and faithful_source_observation
          :: "'evidence \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) src_history \<Rightarrow> 'raw \<Rightarrow> bool"
    and materializes_run :: "'cert \<Rightarrow> 'evidence \<Rightarrow> 'run \<Rightarrow> bool"
    and evidence_bound_to_cert       :: "'cert \<Rightarrow> 'evidence \<Rightarrow> bool"
    and source_side_schema_supported :: "'cert \<Rightarrow> 'evidence \<Rightarrow> bool"
begin

text \<open>The central object, cert-side: on @{text "scope C"} the replay of
  @{text "clean_prefix C"} equals the source state at @{text "frontier C"}.
  The cert-accessor instance of the core @{const virtual_cut_state}.\<close>

definition virtual_cut
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'cert \<Rightarrow> ('k, 'v) src_history \<Rightarrow> bool"
where
  "virtual_cut b0 C H \<longleftrightarrow>
     virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"

definition checker_input_ok :: "'cert \<Rightarrow> 'evidence \<Rightarrow> bool"
where
  "checker_input_ok C E \<longleftrightarrow>
     evidence_bound_to_cert C E \<and> source_side_schema_supported C E"

definition cert_accessors_agree
where
  "cert_accessors_agree C R \<longleftrightarrow>
     scope C = scope_of R
   \<and> frontier C = frontier_of R
   \<and> clean_prefix C = clean_prefix_of R"

definition cert_run_coherent
where
  "cert_run_coherent C E R \<longleftrightarrow>
     materializes_run C E R \<and> cert_accessors_agree C R"

lemma cert_run_coherence:
  assumes "cert_run_coherent C E R"
  shows   "scope C = scope_of R
         \<and> frontier C = frontier_of R
         \<and> clean_prefix C = clean_prefix_of R"
  using assms
  unfolding cert_run_coherent_def cert_accessors_agree_def
  by blast

lemma cert_run_coherent_virtual_cut_state_subst:
  assumes "cert_accessors_agree C R"
      and "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                             (frontier_of R) H"
  shows   "virtual_cut_state b0 (clean_prefix C) (scope C)
                             (frontier C) H"
  using assms
  unfolding cert_accessors_agree_def
  by simp

text \<open>Layer 4 whole-table claim scope, cert-side (body identical to the global
  @{text Layer4_Whole_Table.whole_table_claim_scope}).\<close>

definition whole_table_claim_scope
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'cert \<Rightarrow> ('k, 'v) src_history \<Rightarrow> frontier \<Rightarrow> bool"
where
  "whole_table_claim_scope b0 C H b \<longleftrightarrow>
     b \<le> frontier C
   \<and> anchor_complete_at_boundary b0 H b (scope C)
   \<and> all_post_anchor_changes_covered H b (frontier C) (scope C)
   \<and> no_unclaimed_replay_keys (clean_prefix C) (scope C)"

lemma whole_table_claim_scope_imp_table_scope_contained:
  assumes "whole_table_claim_scope b0 C H b"
  shows "table_scope_between b0 H b (frontier C) \<subseteq> scope C"
  using assms
  unfolding whole_table_claim_scope_def
            table_scope_between_def
            anchor_complete_at_boundary_def
            all_post_anchor_changes_covered_def
  by blast

lemma whole_table_equality_from_claim_scope:
  assumes vc: "virtual_cut b0 C H"
      and whole: "whole_table_claim_scope b0 C H b"
  shows "Apply (clean_prefix C) = Src b0 H (frontier C)"
proof -
  have scoped:
    "restrict (Apply (clean_prefix C)) (scope C)
       = restrict (Src b0 H (frontier C)) (scope C)"
    using vc unfolding virtual_cut_def virtual_cut_state_def by simp
  have contained:
    "table_scope_between b0 H b (frontier C) \<subseteq> scope C"
    by (rule whole_table_claim_scope_imp_table_scope_contained[OF whole])
  have no_unclaimed:
    "no_unclaimed_replay_keys (clean_prefix C) (scope C)"
    using whole unfolding whole_table_claim_scope_def by blast
  have b_le_frontier: "b \<le> frontier C"
    using whole unfolding whole_table_claim_scope_def by blast
  show ?thesis
    by (rule whole_table_equality_from_scoped_equality
          [OF scoped contained no_unclaimed b_le_frontier])
qed

end


subsection \<open>Layer 3 checker substrate locale\<close>

text \<open>
  The non-circular Layer 3 proof substrate. The locale fixes a certificate
  @{text C} and evidence @{text E} and separates the four primitive checker
  obligations (the trust boundary discharged at deployment, not inside the
  model); the Layer 3 soundness theorems and the Layer 4 specialization are
  then proved inside the locale from those obligations and the inherited Layer 2
  run-side soundness. Acceptance is the abstract @{text "verify C E = accept_value"}.
\<close>

locale dblog_checker_substrate = dblog_cert_substrate +
  fixes C and E
  assumes accepted_input_ok:
    "verify C E = accept_value \<Longrightarrow> checker_input_ok C E"
  and accepted_has_materialization:
    "\<lbrakk>verify C E = accept_value; checker_input_ok C E\<rbrakk>
      \<Longrightarrow> \<exists>R. materializes_run C E R"
  and accepted_materialization_agrees:
    "\<And>R. \<lbrakk>verify C E = accept_value; checker_input_ok C E;
      materializes_run C E R\<rbrakk>
      \<Longrightarrow> cert_accessors_agree C R"
  and faithful_materialization_wellformed:
    "\<And>R b0 H Raw. \<lbrakk>verify C E = accept_value; checker_input_ok C E;
      materializes_run C E R; faithful_source_observation E b0 H Raw\<rbrakk>
      \<Longrightarrow> wellformed_dblog_run b0 R H"
begin

theorem accepted_certificate_implies_wellformed_run:
  assumes accept: "verify C E = accept_value"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "\<exists>R. wellformed_dblog_run b0 R H \<and> cert_run_coherent C E R"
proof -
  have input_ok: "checker_input_ok C E"
    by (rule accepted_input_ok[OF accept])
  then obtain R where mat: "materializes_run C E R"
    using accepted_has_materialization[OF accept input_ok] by blast
  have wf: "wellformed_dblog_run b0 R H"
    by (rule faithful_materialization_wellformed[OF accept input_ok mat faithful])
  have agree: "cert_accessors_agree C R"
    by (rule accepted_materialization_agrees[OF accept input_ok mat])
  have coherent: "cert_run_coherent C E R"
    using mat agree
    unfolding cert_run_coherent_def
    by blast
  show ?thesis
    using wf coherent by blast
qed

theorem accepted_virtual_cut_sound:
  assumes accept: "verify C E = accept_value"
      and faithful: "faithful_source_observation E b0 H Raw"
  shows   "virtual_cut b0 C H"
proof -
  obtain R where wf: "wellformed_dblog_run b0 R H"
      and coherent: "cert_run_coherent C E R"
    using accepted_certificate_implies_wellformed_run[OF accept faithful]
    by blast
  have agree: "cert_accessors_agree C R"
    using coherent unfolding cert_run_coherent_def by blast
  have run_vcs:
    "virtual_cut_state b0 (clean_prefix_of R) (scope_of R)
                       (frontier_of R) H"
    using wellformed_run_implies_virtual_cut[OF wf] .
  have cert_vcs:
    "virtual_cut_state b0 (clean_prefix C) (scope C) (frontier C) H"
    using cert_run_coherent_virtual_cut_state_subst[OF agree run_vcs] .
  show ?thesis
    unfolding virtual_cut_def
    using cert_vcs .
qed

theorem accepted_whole_table_anchor_domain_specialization:
  assumes accept: "verify C E = accept_value"
      and faithful: "faithful_source_observation E b0 H Raw"
      and whole: "whole_table_claim_scope b0 C H b"
  shows "Apply (clean_prefix C) = Src b0 H (frontier C)"
proof -
  have vc: "virtual_cut b0 C H"
    by (rule accepted_virtual_cut_sound[OF accept faithful])
  show ?thesis
    by (rule whole_table_equality_from_claim_scope[OF vc whole])
qed

end

end
