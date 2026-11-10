(*  Title:   Layer4_Fixtures_Inst.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer4_Fixtures_Inst
  imports
    Layer4_Fixtures_Core
    DBLog_Cert_Substrate
    Layer01_Virtual_Cut_Example_Inst
    Layer4_Whole_Table
begin

section \<open>Constructed Layer 4 fixtures\<close>

text \<open>
  Constructed Layer 4 fixtures: the negative, boundary, and run-ambiguity facts
  for the Layer 4 whole-table claim, established over explicit constructions
  with no axioms.

  Each Layer 4 fixture pins exactly the
  three certificate accessors @{const scope} / @{const frontier} /
  @{const clean_prefix} (the run-ambiguity fixture additionally pins
  @{const materializes_run} / @{const chunks} / @{const responsible_chunk} on two
  runs). Everything else --- @{const virtual_cut},
  @{const whole_table_claim_scope}, and the pure Layer 4 predicates
  @{const touched_between} / @{const anchor_domain} / @{const table_scope_between}
  / @{const all_post_anchor_changes_covered} / @{const no_unclaimed_replay_keys}
  / @{const replay_keys} --- is a global definition over those accessor
  \<^emph>\<open>values\<close>, plus the cert-side locale definitions of
  @{locale dblog_cert_substrate}. So a single
  @{command global_interpretation} @{text cf} of
  @{locale dblog_cert_substrate} over a finite certificate datatype whose
  @{const scope} / @{const frontier} / @{const clean_prefix} functions carry
  exactly the fixture values suffices; the run-side ambiguity fixture gets a
  second interpretation @{text amb} over a two-run carrier.

    \<^item> The carrier-independent source-side lemmas of
      @{text Layer4_Fixtures_Core} and the anchor facts of
      @{text Layer4_Witnesses_Core}, which range over the
      plain replay-prefix / source-history @{command definition}s (e.g.
      @{thm [source] l4_missing_insert_scoped_virtual_cut_state},
      @{thm [source] l4_anchor_domain},
      @{thm [source] Src_b0_ex_l4_delete_touch_ec4}), reference no certificate
      accessor and are reused verbatim by import.

    \<^item> The running-example clean prefix --- shared by the post-anchor-delete and
      run-ambiguity fixtures --- is the constructed
      @{term "ex_model.clean_prefix_of ()"} of
      @{text Layer01_Virtual_Cut_Example_Inst}, with
      @{thm [source] exm_apply} / @{thm [source] ex_model_virtual_cut_holds}
      reused.

    \<^item> The @{text H_ex}-based @{const touched_between} fact over the explicit
      frontier @{term ec4} (@{thm [source] touched_H_ex_anchor_ec4}) is reused
      from @{text Layer4_Witnesses_Core}.
\<close>


subsection \<open>Constructed certificate carrier\<close>

text \<open>A finite certificate datatype with one constructor per Layer 4 fixture,
  carrying exactly the scope / frontier / clean-prefix values the fixtures
  exercise.\<close>

datatype l4f_cert =
    CMissingInsert | CDeleteTouch | CEmpty | CClaimRefresh | CAfterFrontier
  | CUpdateRefresh | CUnclaimed | CB0Anchor | CSameBoundary | CAmbig

fun l4f_scope :: "l4f_cert \<Rightarrow> nat set" where
  "l4f_scope CMissingInsert = {100, 200}"
| "l4f_scope CDeleteTouch   = {100, 200, 300}"
| "l4f_scope CEmpty         = {}"
| "l4f_scope CClaimRefresh  = {100, 200, 300}"
| "l4f_scope CAfterFrontier = {}"
| "l4f_scope CUpdateRefresh = {100, 200, 300}"
| "l4f_scope CUnclaimed     = {100, 200, 300}"
| "l4f_scope CB0Anchor      = {700}"
| "l4f_scope CSameBoundary  = {800, 900}"
| "l4f_scope CAmbig         = {100, 200, 300}"

fun l4f_frontier :: "l4f_cert \<Rightarrow> frontier" where
  "l4f_frontier CEmpty         = ec1"
| "l4f_frontier CAfterFrontier = ec1"
| "l4f_frontier _              = ec4"

fun l4f_clean_prefix :: "l4f_cert \<Rightarrow> (nat, nat) replay_event list" where
  "l4f_clean_prefix CMissingInsert = l4_missing_insert_prefix"
| "l4f_clean_prefix CDeleteTouch   = ex_model.clean_prefix_of ()"
| "l4f_clean_prefix CEmpty         = []"
| "l4f_clean_prefix CClaimRefresh  = l4_missing_insert_prefix"
| "l4f_clean_prefix CAfterFrontier = []"
| "l4f_clean_prefix CUpdateRefresh = l4_update_refresh_prefix"
| "l4f_clean_prefix CUnclaimed     = l4_unclaimed_prefix"
| "l4f_clean_prefix CB0Anchor      = l4_b0_anchor_prefix"
| "l4f_clean_prefix CSameBoundary  = l4_same_boundary_prefix"
| "l4f_clean_prefix CAmbig         = ex_model.clean_prefix_of ()"


subsection \<open>Reusable helpers\<close>

text \<open>The running-example clean prefix replay keys and virtual-cut state, over the
  constructed @{term "ex_model.clean_prefix_of ()"}. The @{text H_ex}
  post-anchor touched set @{thm [source] touched_H_ex_anchor_ec4} is imported
  from @{text Layer4_Witnesses_Core}.\<close>

lemma rep_ex_replay_keys:
  "replay_keys (ex_model.clean_prefix_of ()) = {100, 200, 300}"
  unfolding replay_keys_def exm_clean_prefix by auto

lemma rep_ex_virtual_cut_state:
  "virtual_cut_state b0_ex (ex_model.clean_prefix_of ()) {100, 200, 300} ec4 H_ex"
  using ex_model_virtual_cut_holds
  by (simp add: virtual_cut_state_def exm_scope exm_frontier)


subsection \<open>Constructed certificate substrate interpretation (cert-accessor fixtures)\<close>

text \<open>The run side is a degenerate @{typ unit} run (no chunks, no observed CDC,
  empty source history);
  @{locale dblog_cert_substrate} assumes nothing beyond the two inherited
  @{const chunks_list} obligations (@{term "set [] = {}"}, @{term "distinct []"}),
  so the interpretation introduces no axiom. The verifier / materialization /
  faithfulness / binding / schema parameters are not used by the cert-accessor
  fixtures and are supplied as trivial constants.\<close>

global_interpretation cf: dblog_cert_substrate
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
  l4f_scope l4f_frontier l4f_clean_prefix
  "\<lambda>_::l4f_cert. \<lambda>_::unit. Reject"                                  \<comment> \<open>verify\<close>
  Accept                                                            \<comment> \<open>@{text accept_value}\<close>
  "\<lambda>_::unit. \<lambda>_::(nat \<rightharpoonup> nat). \<lambda>_::(nat, nat) src_history. \<lambda>_::unit. False"
                                                                    \<comment> \<open>@{text faithful_source_observation}\<close>
  "\<lambda>_::l4f_cert. \<lambda>_::unit. \<lambda>_::unit. False"                         \<comment> \<open>@{text materializes_run}\<close>
  "\<lambda>_::l4f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text evidence_bound_to_cert}\<close>
  "\<lambda>_::l4f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text source_side_schema_supported}\<close>
  by unfold_locales simp_all


subsection \<open>Post-anchor insert not covered (constructed)\<close>

lemma cf_missing_insert_virtual_cut:
  "cf.virtual_cut b0_ex CMissingInsert H_ex"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using l4_missing_insert_scoped_virtual_cut_state
  by (simp add: virtual_cut_state_def)

lemma cf_missing_insert_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CMissingInsert) (l4f_scope CMissingInsert)"
  unfolding no_unclaimed_replay_keys_def
  using l4_missing_insert_replay_keys by simp

lemma cf_missing_insert_key_touched:
  "(300::nat) \<in> touched_between H_ex l4_anchor (l4f_frontier CMissingInsert)"
  using touched_H_ex_anchor_ec4 by simp

lemma cf_missing_insert_not_covered:
  "\<not> all_post_anchor_changes_covered
        H_ex l4_anchor (l4f_frontier CMissingInsert) (l4f_scope CMissingInsert)"
  using cf_missing_insert_key_touched
  unfolding all_post_anchor_changes_covered_def
  by auto

lemma cf_missing_insert_not_whole_table:
  "\<not> cf.whole_table_claim_scope b0_ex CMissingInsert H_ex l4_anchor"
  using cf_missing_insert_not_covered
  unfolding cf.whole_table_claim_scope_def
  by blast

lemma cf_missing_insert_unrestricted_equality_fails:
  "Apply (l4f_clean_prefix CMissingInsert)
   \<noteq> Src b0_ex H_ex (l4f_frontier CMissingInsert)"
proof
  assume eq:
    "Apply (l4f_clean_prefix CMissingInsert)
     = Src b0_ex H_ex (l4f_frontier CMissingInsert)"
  hence "Apply (l4f_clean_prefix CMissingInsert) (300::nat)
       = Src b0_ex H_ex (l4f_frontier CMissingInsert) 300"
    by simp
  thus False
    using l4_missing_insert_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
qed

theorem layer4_post_anchor_insert_not_covered_fixture_constructed:
  "cf.virtual_cut b0_ex CMissingInsert H_ex
   \<and> no_unclaimed_replay_keys
        (l4f_clean_prefix CMissingInsert) (l4f_scope CMissingInsert)
   \<and> (300::nat) \<in> touched_between H_ex l4_anchor (l4f_frontier CMissingInsert)
   \<and> 300 \<notin> l4f_scope CMissingInsert
   \<and> 300 \<notin> replay_keys (l4f_clean_prefix CMissingInsert)
   \<and> \<not> all_post_anchor_changes_covered
        H_ex l4_anchor (l4f_frontier CMissingInsert) (l4f_scope CMissingInsert)
   \<and> \<not> cf.whole_table_claim_scope b0_ex CMissingInsert H_ex l4_anchor
   \<and> Apply (l4f_clean_prefix CMissingInsert) 300 = None
   \<and> Src b0_ex H_ex (l4f_frontier CMissingInsert) 300 = Some 3500
   \<and> Apply (l4f_clean_prefix CMissingInsert)
      \<noteq> Src b0_ex H_ex (l4f_frontier CMissingInsert)"
  using cf_missing_insert_virtual_cut
        cf_missing_insert_no_unclaimed
        cf_missing_insert_key_touched
        cf_missing_insert_not_covered
        cf_missing_insert_not_whole_table
        cf_missing_insert_unrestricted_equality_fails
        l4_missing_insert_replay_keys
        l4_missing_insert_apply_300
        Src_b0_ex_H_ex_ec4_300
  by simp


subsection \<open>Post-anchor delete as conservative touch coverage (constructed)\<close>

lemma cf_delete_touch_apply_frontier:
  "Apply (l4f_clean_prefix CDeleteTouch) =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 12000
          else if k = 300 then Some 3500
          else None)"
  using exm_apply by simp

lemma cf_delete_touch_unrestricted_equality:
  "Apply (l4f_clean_prefix CDeleteTouch)
   = Src b0_ex l4_delete_touch_H (l4f_frontier CDeleteTouch)"
  using cf_delete_touch_apply_frontier Src_b0_ex_l4_delete_touch_ec4 by simp

lemma cf_delete_touch_virtual_cut:
  "cf.virtual_cut b0_ex CDeleteTouch l4_delete_touch_H"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using cf_delete_touch_unrestricted_equality by simp

lemma cf_delete_touch_replay_keys:
  "replay_keys (l4f_clean_prefix CDeleteTouch) = {100, 200, 300}"
  using rep_ex_replay_keys by simp

lemma cf_delete_touch_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CDeleteTouch) (l4f_scope CDeleteTouch)"
  unfolding no_unclaimed_replay_keys_def
  using cf_delete_touch_replay_keys by simp

lemma cf_delete_touch_anchor_complete:
  "anchor_complete_at_boundary
     b0_ex l4_delete_touch_H l4_anchor (l4f_scope CDeleteTouch)"
  unfolding anchor_complete_at_boundary_def
  using l4_delete_touch_anchor_domain by simp

lemma cf_delete_touch_key_touched:
  "(400::nat) \<in> touched_between
       l4_delete_touch_H l4_anchor (l4f_frontier CDeleteTouch)"
proof -
  have in_H: "(ec2, Delete (400::nat)) \<in> set l4_delete_touch_H"
    by (simp add: l4_delete_touch_H_def)
  have after_anchor: "l4_anchor < ec2"
    using ec1_less_ec2 by (simp add: l4_anchor_def)
  have before_frontier: "ec2 \<le> l4f_frontier CDeleteTouch"
    using ec2_less_eq_ec4 by simp
  show ?thesis
    unfolding touched_between_def
    using in_H after_anchor before_frontier
    by (intro CollectI exI[where x=ec2]
              exI[where x="Delete (400::nat)"]) auto
qed

lemma cf_delete_touch_not_covered:
  "\<not> all_post_anchor_changes_covered
        l4_delete_touch_H l4_anchor (l4f_frontier CDeleteTouch) (l4f_scope CDeleteTouch)"
  using cf_delete_touch_key_touched
  unfolding all_post_anchor_changes_covered_def
  by auto

lemma cf_delete_touch_not_whole_table:
  "\<not> cf.whole_table_claim_scope b0_ex CDeleteTouch l4_delete_touch_H l4_anchor"
  using cf_delete_touch_not_covered
  unfolding cf.whole_table_claim_scope_def
  by blast

theorem layer4_post_anchor_delete_not_covered_fixture_constructed:
  "cf.virtual_cut b0_ex CDeleteTouch l4_delete_touch_H
   \<and> l4_anchor \<le> l4f_frontier CDeleteTouch
   \<and> anchor_complete_at_boundary
        b0_ex l4_delete_touch_H l4_anchor (l4f_scope CDeleteTouch)
   \<and> no_unclaimed_replay_keys
        (l4f_clean_prefix CDeleteTouch) (l4f_scope CDeleteTouch)
   \<and> (400::nat) \<in> touched_between l4_delete_touch_H l4_anchor
        (l4f_frontier CDeleteTouch)
   \<and> 400 \<notin> l4f_scope CDeleteTouch
   \<and> 400 \<notin> replay_keys (l4f_clean_prefix CDeleteTouch)
   \<and> Apply (l4f_clean_prefix CDeleteTouch) 400 = None
   \<and> Src b0_ex l4_delete_touch_H (l4f_frontier CDeleteTouch) 400 = None
   \<and> Apply (l4f_clean_prefix CDeleteTouch)
      = Src b0_ex l4_delete_touch_H (l4f_frontier CDeleteTouch)
   \<and> \<not> all_post_anchor_changes_covered
        l4_delete_touch_H l4_anchor (l4f_frontier CDeleteTouch) (l4f_scope CDeleteTouch)
   \<and> \<not> cf.whole_table_claim_scope b0_ex CDeleteTouch l4_delete_touch_H l4_anchor"
  using cf_delete_touch_virtual_cut
        cf_delete_touch_anchor_complete
        cf_delete_touch_no_unclaimed
        cf_delete_touch_key_touched
        cf_delete_touch_replay_keys
        cf_delete_touch_apply_frontier
        Src_b0_ex_l4_delete_touch_ec4_400
        cf_delete_touch_unrestricted_equality
        cf_delete_touch_not_covered
        cf_delete_touch_not_whole_table
        ec1_le_ec4
  by (simp add: less_eq_src_coord_def l4_anchor_def)


subsection \<open>Empty anchor-domain boundary (constructed)\<close>

lemma cf_empty_apply:
  "Apply (l4f_clean_prefix CEmpty) = (\<lambda>_. None)"
  by (simp add: Apply_def)

lemma cf_empty_source_at_frontier:
  "Src l4_empty_b0 l4_empty_H (l4f_frontier CEmpty) = (\<lambda>_. None)"
  by (simp add: Src_def latest_src_event_def l4_empty_b0_def l4_empty_H_def)

lemma cf_empty_unrestricted_equality:
  "Apply (l4f_clean_prefix CEmpty)
   = Src l4_empty_b0 l4_empty_H (l4f_frontier CEmpty)"
  using cf_empty_apply cf_empty_source_at_frontier by simp

lemma cf_empty_virtual_cut:
  "cf.virtual_cut l4_empty_b0 CEmpty l4_empty_H"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using cf_empty_unrestricted_equality by simp

lemma cf_empty_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CEmpty) (l4f_scope CEmpty)"
  by (simp add: no_unclaimed_replay_keys_def replay_keys_def)

lemma cf_empty_anchor_complete:
  "anchor_complete_at_boundary l4_empty_b0 l4_empty_H l4_anchor (l4f_scope CEmpty)"
  by (simp add: anchor_complete_at_boundary_def l4_empty_anchor_domain)

lemma touched_between_nil: "touched_between [] b f = {}"
  by (simp add: touched_between_def)

lemma cf_empty_touched_between:
  "touched_between l4_empty_H l4_anchor (l4f_frontier CEmpty) = {}"
  by (simp add: l4_empty_H_def touched_between_nil)

lemma cf_empty_table_scope_between:
  "table_scope_between l4_empty_b0 l4_empty_H l4_anchor (l4f_frontier CEmpty) = {}"
  unfolding table_scope_between_def
  using l4_empty_anchor_domain cf_empty_touched_between
  by simp

lemma cf_empty_all_post_anchor_changes_covered:
  "all_post_anchor_changes_covered
     l4_empty_H l4_anchor (l4f_frontier CEmpty) (l4f_scope CEmpty)"
  by (simp add: all_post_anchor_changes_covered_def l4_empty_H_def touched_between_nil)

lemma cf_empty_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CEmpty"
  by (simp add: l4_anchor_def less_eq_src_coord_def src_le_refl)

lemma cf_empty_whole_table_claim_scope:
  "cf.whole_table_claim_scope l4_empty_b0 CEmpty l4_empty_H l4_anchor"
  unfolding cf.whole_table_claim_scope_def
  using cf_empty_anchor_le_frontier
        cf_empty_anchor_complete
        cf_empty_all_post_anchor_changes_covered
        cf_empty_no_unclaimed
  by blast

theorem layer4_empty_anchor_domain_boundary_fixture_constructed:
  "anchor_domain l4_empty_b0 l4_empty_H l4_anchor = {}
   \<and> touched_between l4_empty_H l4_anchor (l4f_frontier CEmpty) = {}
   \<and> table_scope_between l4_empty_b0 l4_empty_H l4_anchor (l4f_frontier CEmpty) = {}
   \<and> l4f_scope CEmpty = {}
   \<and> l4f_clean_prefix CEmpty = []
   \<and> cf.virtual_cut l4_empty_b0 CEmpty l4_empty_H
   \<and> cf.whole_table_claim_scope l4_empty_b0 CEmpty l4_empty_H l4_anchor
   \<and> Apply (l4f_clean_prefix CEmpty)
      = Src l4_empty_b0 l4_empty_H (l4f_frontier CEmpty)"
  using l4_empty_anchor_domain
        cf_empty_touched_between
        cf_empty_table_scope_between
        cf_empty_virtual_cut
        cf_empty_whole_table_claim_scope
        cf_empty_unrestricted_equality
  by simp


subsection \<open>Claim scope broader than materialized replay coverage (constructed)\<close>

lemma cf_claim_refresh_replay_keys:
  "replay_keys (l4f_clean_prefix CClaimRefresh) = {100, 200}"
  using l4_missing_insert_replay_keys by simp

lemma cf_claim_refresh_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CClaimRefresh) (l4f_scope CClaimRefresh)"
  unfolding no_unclaimed_replay_keys_def using cf_claim_refresh_replay_keys by simp

lemma cf_claim_refresh_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CClaimRefresh)"
  unfolding anchor_complete_at_boundary_def using l4_anchor_domain by simp

lemma cf_claim_refresh_all_post:
  "all_post_anchor_changes_covered H_ex l4_anchor
     (l4f_frontier CClaimRefresh) (l4f_scope CClaimRefresh)"
  unfolding all_post_anchor_changes_covered_def using touched_H_ex_anchor_ec4 by simp

lemma cf_claim_refresh_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CClaimRefresh"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma cf_claim_refresh_whole_table:
  "cf.whole_table_claim_scope b0_ex CClaimRefresh H_ex l4_anchor"
  unfolding cf.whole_table_claim_scope_def
  using cf_claim_refresh_anchor_le_frontier cf_claim_refresh_anchor_complete
        cf_claim_refresh_all_post cf_claim_refresh_no_unclaimed
  by blast

lemma cf_claim_refresh_not_virtual_cut:
  "\<not> cf.virtual_cut b0_ex CClaimRefresh H_ex"
proof
  assume vc: "cf.virtual_cut b0_ex CClaimRefresh H_ex"
  hence "restrict (Apply (l4f_clean_prefix CClaimRefresh)) (l4f_scope CClaimRefresh)
       = restrict (Src b0_ex H_ex (l4f_frontier CClaimRefresh)) (l4f_scope CClaimRefresh)"
    unfolding cf.virtual_cut_def virtual_cut_state_def by simp
  hence "restrict (Apply (l4f_clean_prefix CClaimRefresh)) (l4f_scope CClaimRefresh) (300::nat)
       = restrict (Src b0_ex H_ex (l4f_frontier CClaimRefresh)) (l4f_scope CClaimRefresh) 300"
    by simp
  hence "Apply (l4f_clean_prefix CClaimRefresh) (300::nat)
       = Src b0_ex H_ex (l4f_frontier CClaimRefresh) 300"
    by (simp add: restrict_def)
  thus False
    using l4_missing_insert_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
qed

theorem layer4_claim_refresh_scope_mismatch_fixture_constructed:
  "l4f_scope CClaimRefresh = {100, 200, 300}
   \<and> replay_keys (l4f_clean_prefix CClaimRefresh) = {100, 200}
   \<and> (300::nat) \<in> l4f_scope CClaimRefresh
   \<and> 300 \<notin> replay_keys (l4f_clean_prefix CClaimRefresh)
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CClaimRefresh)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (l4f_frontier CClaimRefresh) (l4f_scope CClaimRefresh)
   \<and> no_unclaimed_replay_keys
        (l4f_clean_prefix CClaimRefresh) (l4f_scope CClaimRefresh)
   \<and> cf.whole_table_claim_scope b0_ex CClaimRefresh H_ex l4_anchor
   \<and> \<not> cf.virtual_cut b0_ex CClaimRefresh H_ex
   \<and> Apply (l4f_clean_prefix CClaimRefresh) 300 = None
   \<and> Src b0_ex H_ex (l4f_frontier CClaimRefresh) 300 = Some 3500
   \<and> Apply (l4f_clean_prefix CClaimRefresh)
      \<noteq> Src b0_ex H_ex (l4f_frontier CClaimRefresh)"
  using cf_claim_refresh_replay_keys cf_claim_refresh_anchor_complete
        cf_claim_refresh_all_post cf_claim_refresh_no_unclaimed
        cf_claim_refresh_whole_table cf_claim_refresh_not_virtual_cut
        l4_missing_insert_apply_300 Src_b0_ex_H_ex_ec4_300
        cf_missing_insert_unrestricted_equality_fails
  by simp


subsection \<open>Anchor boundary after certified frontier (constructed)\<close>

lemma cf_after_frontier_source_present_at_frontier:
  "Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier) (500::nat)
     = Some 9000"
  unfolding Src_def
  using latest_src_event_l4_after_frontier_ec1_500
  by (simp add: l4_after_frontier_H_def)

lemma cf_after_frontier_touched_between_empty:
  "touched_between l4_after_frontier_H l4_after_frontier_anchor
     (l4f_frontier CAfterFrontier) = {}"
  unfolding touched_between_def l4_after_frontier_H_def l4_after_frontier_anchor_def
  using not_src_le_ec2_ec1
  by (auto simp: less_src_coord_def src_lt_def less_eq_src_coord_def)

lemma cf_after_frontier_table_scope_between_empty:
  "table_scope_between l4_after_frontier_b0 l4_after_frontier_H
     l4_after_frontier_anchor (l4f_frontier CAfterFrontier) = {}"
  unfolding table_scope_between_def
  using l4_after_frontier_anchor_domain_empty cf_after_frontier_touched_between_empty
  by simp

lemma cf_after_frontier_key_not_in_table_scope:
  "(500::nat) \<notin> table_scope_between l4_after_frontier_b0
     l4_after_frontier_H l4_after_frontier_anchor (l4f_frontier CAfterFrontier)"
  using cf_after_frontier_table_scope_between_empty by simp

lemma cf_after_frontier_anchor_not_le_frontier:
  "\<not> l4_after_frontier_anchor \<le> l4f_frontier CAfterFrontier"
  using not_src_le_ec2_ec1
  by (simp add: l4_after_frontier_anchor_def less_eq_src_coord_def)

lemma cf_after_frontier_anchor_complete:
  "anchor_complete_at_boundary
     l4_after_frontier_b0 l4_after_frontier_H l4_after_frontier_anchor (l4f_scope CAfterFrontier)"
  by (simp add: anchor_complete_at_boundary_def l4_after_frontier_anchor_domain_empty)

lemma cf_after_frontier_all_post:
  "all_post_anchor_changes_covered l4_after_frontier_H
     l4_after_frontier_anchor (l4f_frontier CAfterFrontier) (l4f_scope CAfterFrontier)"
  unfolding all_post_anchor_changes_covered_def
  using cf_after_frontier_touched_between_empty by simp

lemma cf_after_frontier_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CAfterFrontier) (l4f_scope CAfterFrontier)"
  by (simp add: no_unclaimed_replay_keys_def replay_keys_def)

lemma cf_after_frontier_apply:
  "Apply (l4f_clean_prefix CAfterFrontier) = (\<lambda>_. None)"
  by (simp add: Apply_def)

lemma cf_after_frontier_virtual_cut:
  "cf.virtual_cut l4_after_frontier_b0 CAfterFrontier l4_after_frontier_H"
  unfolding cf.virtual_cut_def virtual_cut_state_def restrict_def
  by simp

lemma cf_after_frontier_not_whole_table:
  "\<not> cf.whole_table_claim_scope l4_after_frontier_b0 CAfterFrontier
        l4_after_frontier_H l4_after_frontier_anchor"
  using cf_after_frontier_anchor_not_le_frontier
  unfolding cf.whole_table_claim_scope_def
  by blast

lemma cf_after_frontier_unrestricted_equality_fails:
  "Apply (l4f_clean_prefix CAfterFrontier)
   \<noteq> Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier)"
proof
  assume eq:
    "Apply (l4f_clean_prefix CAfterFrontier)
     = Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier)"
  hence "Apply (l4f_clean_prefix CAfterFrontier) (500::nat)
       = Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier) 500"
    by simp
  thus False
    using cf_after_frontier_apply cf_after_frontier_source_present_at_frontier by simp
qed

theorem layer4_anchor_after_frontier_fixture_constructed:
  "l4f_scope CAfterFrontier = {}
   \<and> l4f_clean_prefix CAfterFrontier = []
   \<and> l4f_frontier CAfterFrontier = ec1
   \<and> l4_after_frontier_anchor = ec2
   \<and> \<not> l4_after_frontier_anchor \<le> l4f_frontier CAfterFrontier
   \<and> anchor_domain l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor = {}
   \<and> touched_between l4_after_frontier_H l4_after_frontier_anchor
        (l4f_frontier CAfterFrontier) = {}
   \<and> table_scope_between l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor (l4f_frontier CAfterFrontier) = {}
   \<and> (500::nat) \<notin> table_scope_between l4_after_frontier_b0
        l4_after_frontier_H l4_after_frontier_anchor (l4f_frontier CAfterFrontier)
   \<and> anchor_complete_at_boundary l4_after_frontier_b0 l4_after_frontier_H
        l4_after_frontier_anchor (l4f_scope CAfterFrontier)
   \<and> all_post_anchor_changes_covered l4_after_frontier_H
        l4_after_frontier_anchor (l4f_frontier CAfterFrontier) (l4f_scope CAfterFrontier)
   \<and> no_unclaimed_replay_keys
        (l4f_clean_prefix CAfterFrontier) (l4f_scope CAfterFrontier)
   \<and> cf.virtual_cut l4_after_frontier_b0 CAfterFrontier l4_after_frontier_H
   \<and> \<not> cf.whole_table_claim_scope l4_after_frontier_b0 CAfterFrontier
        l4_after_frontier_H l4_after_frontier_anchor
   \<and> Apply (l4f_clean_prefix CAfterFrontier) 500 = None
   \<and> Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier) 500 = Some 9000
   \<and> Src l4_after_frontier_b0 l4_after_frontier_H l4_after_frontier_anchor 500 = None
   \<and> Apply (l4f_clean_prefix CAfterFrontier)
      \<noteq> Src l4_after_frontier_b0 l4_after_frontier_H (l4f_frontier CAfterFrontier)"
  using l4_after_frontier_anchor_domain_empty
        cf_after_frontier_touched_between_empty
        cf_after_frontier_table_scope_between_empty
        cf_after_frontier_key_not_in_table_scope
        cf_after_frontier_anchor_not_le_frontier
        cf_after_frontier_anchor_complete
        cf_after_frontier_all_post
        cf_after_frontier_no_unclaimed
        cf_after_frontier_virtual_cut
        cf_after_frontier_not_whole_table
        cf_after_frontier_apply
        cf_after_frontier_source_present_at_frontier
        l4_after_frontier_source_absent_at_anchor_500
        cf_after_frontier_unrestricted_equality_fails
        l4_after_frontier_anchor_def
  by simp


subsection \<open>Post-anchor update materialized by a later refresh (constructed)\<close>

lemma cf_update_refresh_replay_keys:
  "replay_keys (l4f_clean_prefix CUpdateRefresh) = {100, 200, 300}"
  unfolding replay_keys_def by (auto simp: l4_update_refresh_prefix_def)

lemma cf_update_refresh_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CUpdateRefresh) (l4f_scope CUpdateRefresh)"
  unfolding no_unclaimed_replay_keys_def using cf_update_refresh_replay_keys by simp

lemma cf_update_refresh_virtual_cut:
  "cf.virtual_cut b0_ex CUpdateRefresh H_ex"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using l4_update_refresh_scoped_virtual_cut_state by (simp add: virtual_cut_state_def)

lemma cf_update_refresh_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CUpdateRefresh)"
  unfolding anchor_complete_at_boundary_def using l4_anchor_domain by simp

lemma cf_update_refresh_all_post:
  "all_post_anchor_changes_covered H_ex l4_anchor
     (l4f_frontier CUpdateRefresh) (l4f_scope CUpdateRefresh)"
  unfolding all_post_anchor_changes_covered_def using touched_H_ex_anchor_ec4 by simp

lemma cf_update_refresh_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CUpdateRefresh"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma cf_update_refresh_whole_table:
  "cf.whole_table_claim_scope b0_ex CUpdateRefresh H_ex l4_anchor"
  unfolding cf.whole_table_claim_scope_def
  using cf_update_refresh_anchor_le_frontier cf_update_refresh_anchor_complete
        cf_update_refresh_all_post cf_update_refresh_no_unclaimed
  by blast

lemma cf_update_refresh_unrestricted_equality:
  "Apply (l4f_clean_prefix CUpdateRefresh) = Src b0_ex H_ex (l4f_frontier CUpdateRefresh)"
  by (rule cf.whole_table_equality_from_claim_scope
        [OF cf_update_refresh_virtual_cut cf_update_refresh_whole_table])

lemma cf_update_refresh_refresh_for_200:
  "Refresh (200::nat) (Some (12000::nat)) ec4 \<in> set (l4f_clean_prefix CUpdateRefresh)"
  by (simp add: l4_update_refresh_prefix_def)

lemma cf_update_refresh_no_cdc_update_for_200:
  "Cdc ec3 (Update (200::nat) (12000::nat)) \<notin> set (l4f_clean_prefix CUpdateRefresh)"
  by (simp add: l4_update_refresh_prefix_def)

theorem layer4_post_anchor_update_before_read_fixture_constructed:
  "cf.virtual_cut b0_ex CUpdateRefresh H_ex
   \<and> cf.whole_table_claim_scope b0_ex CUpdateRefresh H_ex l4_anchor
   \<and> no_unclaimed_replay_keys
        (l4f_clean_prefix CUpdateRefresh) (l4f_scope CUpdateRefresh)
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CUpdateRefresh)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (l4f_frontier CUpdateRefresh) (l4f_scope CUpdateRefresh)
   \<and> (200::nat) \<in> anchor_domain b0_ex H_ex l4_anchor
   \<and> 200 \<in> touched_between H_ex l4_anchor (l4f_frontier CUpdateRefresh)
   \<and> 200 \<in> l4f_scope CUpdateRefresh
   \<and> Refresh 200 (Some 12000) ec4 \<in> set (l4f_clean_prefix CUpdateRefresh)
   \<and> Cdc ec3 (Update 200 12000) \<notin> set (l4f_clean_prefix CUpdateRefresh)
   \<and> (ec3, Update 200 12000) \<in> set H_ex
   \<and> ec3 < ec4
   \<and> Apply (l4f_clean_prefix CUpdateRefresh) 200 = Some 12000
   \<and> Src b0_ex H_ex (l4f_frontier CUpdateRefresh) 200 = Some 12000
   \<and> Apply (l4f_clean_prefix CUpdateRefresh)
      = Src b0_ex H_ex (l4f_frontier CUpdateRefresh)"
  using cf_update_refresh_virtual_cut cf_update_refresh_whole_table
        cf_update_refresh_no_unclaimed cf_update_refresh_anchor_complete
        cf_update_refresh_all_post l4_anchor_domain touched_H_ex_anchor_ec4
        cf_update_refresh_refresh_for_200 cf_update_refresh_no_cdc_update_for_200
        l4_update_refresh_source_update_before_refresh
        l4_update_refresh_apply_200 Src_b0_ex_H_ex_ec4_200
        cf_update_refresh_unrestricted_equality
  by simp


subsection \<open>No-unclaimed replay-key failure (constructed)\<close>

lemma cf_unclaimed_replay_keys:
  "replay_keys (l4f_clean_prefix CUnclaimed) = {100, 200, 300, 999}"
  unfolding replay_keys_def by (auto simp: l4_unclaimed_prefix_def)

theorem cf_unclaimed_no_unclaimed_fails:
  "\<not> no_unclaimed_replay_keys (l4f_clean_prefix CUnclaimed) (l4f_scope CUnclaimed)"
  unfolding no_unclaimed_replay_keys_def using cf_unclaimed_replay_keys by simp

lemma cf_unclaimed_virtual_cut:
  "cf.virtual_cut b0_ex CUnclaimed H_ex"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using l4_unclaimed_scoped_virtual_cut_state by (simp add: virtual_cut_state_def)

lemma cf_unclaimed_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CUnclaimed)"
  unfolding anchor_complete_at_boundary_def using l4_anchor_domain by simp

lemma cf_unclaimed_all_post:
  "all_post_anchor_changes_covered H_ex l4_anchor
     (l4f_frontier CUnclaimed) (l4f_scope CUnclaimed)"
  unfolding all_post_anchor_changes_covered_def using touched_H_ex_anchor_ec4 by simp

lemma cf_unclaimed_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CUnclaimed"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma cf_unclaimed_table_scope_between:
  "table_scope_between b0_ex H_ex l4_anchor (l4f_frontier CUnclaimed) = l4f_scope CUnclaimed"
  unfolding table_scope_between_def
  using l4_anchor_domain touched_H_ex_anchor_ec4 by auto

theorem cf_unclaimed_not_whole_table:
  "\<not> cf.whole_table_claim_scope b0_ex CUnclaimed H_ex l4_anchor"
  using cf_unclaimed_no_unclaimed_fails
  unfolding cf.whole_table_claim_scope_def by blast

lemma cf_unclaimed_refresh_for_999:
  "Refresh (999::nat) (Some (4242::nat)) ec4 \<in> set (l4f_clean_prefix CUnclaimed)"
  by (simp add: l4_unclaimed_prefix_def)

lemma cf_unclaimed_apply_999:
  "Apply (l4f_clean_prefix CUnclaimed) (999::nat) = Some 4242"
  using l4_unclaimed_apply_999 by simp

lemma cf_unclaimed_source_absent_999:
  "Src b0_ex H_ex (l4f_frontier CUnclaimed) (999::nat) = None"
  unfolding Src_def b0_ex_def
  using latest_src_event_H_ex_ec4_999 by simp

theorem cf_unclaimed_unrestricted_equality_fails:
  "Apply (l4f_clean_prefix CUnclaimed) \<noteq> Src b0_ex H_ex (l4f_frontier CUnclaimed)"
proof
  assume eq: "Apply (l4f_clean_prefix CUnclaimed) = Src b0_ex H_ex (l4f_frontier CUnclaimed)"
  hence "Apply (l4f_clean_prefix CUnclaimed) (999::nat)
       = Src b0_ex H_ex (l4f_frontier CUnclaimed) 999"
    by simp
  thus False using cf_unclaimed_apply_999 cf_unclaimed_source_absent_999 by simp
qed

theorem layer4_no_unclaimed_signature_determinacy_fixture_constructed:
  "cf.virtual_cut b0_ex CUnclaimed H_ex
   \<and> l4_anchor \<le> l4f_frontier CUnclaimed
   \<and> anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CUnclaimed)
   \<and> all_post_anchor_changes_covered H_ex l4_anchor
        (l4f_frontier CUnclaimed) (l4f_scope CUnclaimed)
   \<and> table_scope_between b0_ex H_ex l4_anchor (l4f_frontier CUnclaimed) = l4f_scope CUnclaimed
   \<and> replay_keys (l4f_clean_prefix CUnclaimed) = {100, 200, 300, 999}
   \<and> Refresh 999 (Some 4242) ec4 \<in> set (l4f_clean_prefix CUnclaimed)
   \<and> 999 \<notin> l4f_scope CUnclaimed
   \<and> \<not> no_unclaimed_replay_keys (l4f_clean_prefix CUnclaimed) (l4f_scope CUnclaimed)
   \<and> \<not> cf.whole_table_claim_scope b0_ex CUnclaimed H_ex l4_anchor
   \<and> Apply (l4f_clean_prefix CUnclaimed) 999 = Some 4242
   \<and> Src b0_ex H_ex (l4f_frontier CUnclaimed) 999 = None
   \<and> Apply (l4f_clean_prefix CUnclaimed) \<noteq> Src b0_ex H_ex (l4f_frontier CUnclaimed)"
  using cf_unclaimed_virtual_cut cf_unclaimed_anchor_le_frontier
        cf_unclaimed_anchor_complete cf_unclaimed_all_post
        cf_unclaimed_table_scope_between cf_unclaimed_replay_keys
        cf_unclaimed_refresh_for_999 cf_unclaimed_no_unclaimed_fails
        cf_unclaimed_not_whole_table cf_unclaimed_apply_999
        cf_unclaimed_source_absent_999 cf_unclaimed_unrestricted_equality_fails
  by simp


subsection \<open>b0 base-state contribution to the anchor domain (constructed)\<close>

lemma cf_b0_anchor_apply:
  "Apply (l4f_clean_prefix CB0Anchor) = l4_b0_anchor_b0"
  by (rule ext)
     (simp add: Apply_def l4_b0_anchor_b0_def l4_b0_anchor_prefix_def)

lemma cf_b0_anchor_apply_key:
  "Apply (l4f_clean_prefix CB0Anchor) (700::nat) = Some 7000"
  using cf_b0_anchor_apply l4_b0_anchor_base_key_present by simp

lemma cf_b0_anchor_source_at_frontier:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H (l4f_frontier CB0Anchor) = l4_b0_anchor_b0"
  by (rule ext)
     (simp add: Src_def latest_src_event_def l4_b0_anchor_H_def)

lemma cf_b0_anchor_source_key_at_frontier:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H (l4f_frontier CB0Anchor) (700::nat) = Some 7000"
  using l4_b0_anchor_base_key_present cf_b0_anchor_source_at_frontier by simp

lemma cf_b0_anchor_touched_between:
  "touched_between l4_b0_anchor_H l4_anchor (l4f_frontier CB0Anchor) = {}"
  by (simp add: l4_b0_anchor_H_def touched_between_nil)

lemma cf_b0_anchor_table_scope_between:
  "table_scope_between l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
     (l4f_frontier CB0Anchor) = l4f_scope CB0Anchor"
  unfolding table_scope_between_def
  using l4_b0_anchor_domain cf_b0_anchor_touched_between by simp

lemma cf_b0_anchor_replay_keys:
  "replay_keys (l4f_clean_prefix CB0Anchor) = {700}"
  unfolding replay_keys_def by (simp add: l4_b0_anchor_prefix_def)

lemma cf_b0_anchor_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CB0Anchor) (l4f_scope CB0Anchor)"
  unfolding no_unclaimed_replay_keys_def using cf_b0_anchor_replay_keys by simp

lemma cf_b0_anchor_anchor_complete:
  "anchor_complete_at_boundary l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor (l4f_scope CB0Anchor)"
  unfolding anchor_complete_at_boundary_def using l4_b0_anchor_domain by simp

lemma cf_b0_anchor_all_post:
  "all_post_anchor_changes_covered l4_b0_anchor_H l4_anchor
     (l4f_frontier CB0Anchor) (l4f_scope CB0Anchor)"
  unfolding all_post_anchor_changes_covered_def using cf_b0_anchor_touched_between by simp

lemma cf_b0_anchor_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CB0Anchor"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma cf_b0_anchor_whole_table:
  "cf.whole_table_claim_scope l4_b0_anchor_b0 CB0Anchor l4_b0_anchor_H l4_anchor"
  unfolding cf.whole_table_claim_scope_def
  using cf_b0_anchor_anchor_le_frontier cf_b0_anchor_anchor_complete
        cf_b0_anchor_all_post cf_b0_anchor_no_unclaimed by blast

lemma cf_b0_anchor_unrestricted_equality:
  "Apply (l4f_clean_prefix CB0Anchor)
   = Src l4_b0_anchor_b0 l4_b0_anchor_H (l4f_frontier CB0Anchor)"
  using cf_b0_anchor_apply cf_b0_anchor_source_at_frontier by simp

lemma cf_b0_anchor_virtual_cut:
  "cf.virtual_cut l4_b0_anchor_b0 CB0Anchor l4_b0_anchor_H"
  unfolding cf.virtual_cut_def virtual_cut_state_def
  using cf_b0_anchor_unrestricted_equality by simp

theorem layer4_b0_base_state_anchor_domain_fixture_constructed:
  "l4_b0_anchor_H = []
   \<and> l4_b0_anchor_b0 (700::nat) = Some 7000
   \<and> latest_src_event l4_b0_anchor_H l4_anchor (700::nat) = None
   \<and> Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor 700 = Some 7000
   \<and> Src l4_b0_anchor_b0 l4_b0_anchor_H (l4f_frontier CB0Anchor) 700 = Some 7000
   \<and> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = {700}
   \<and> (700::nat) \<in> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
   \<and> touched_between l4_b0_anchor_H l4_anchor (l4f_frontier CB0Anchor) = {}
   \<and> table_scope_between l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor
        (l4f_frontier CB0Anchor) = l4f_scope CB0Anchor
   \<and> l4f_scope CB0Anchor = {700}
   \<and> replay_keys (l4f_clean_prefix CB0Anchor) = {700}
   \<and> Apply (l4f_clean_prefix CB0Anchor) 700 = Some 7000
   \<and> l4_anchor \<le> l4f_frontier CB0Anchor
   \<and> anchor_complete_at_boundary l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor (l4f_scope CB0Anchor)
   \<and> all_post_anchor_changes_covered l4_b0_anchor_H l4_anchor
        (l4f_frontier CB0Anchor) (l4f_scope CB0Anchor)
   \<and> no_unclaimed_replay_keys (l4f_clean_prefix CB0Anchor) (l4f_scope CB0Anchor)
   \<and> cf.whole_table_claim_scope l4_b0_anchor_b0 CB0Anchor l4_b0_anchor_H l4_anchor
   \<and> cf.virtual_cut l4_b0_anchor_b0 CB0Anchor l4_b0_anchor_H
   \<and> Apply (l4f_clean_prefix CB0Anchor)
      = Src l4_b0_anchor_b0 l4_b0_anchor_H (l4f_frontier CB0Anchor)"
  using l4_b0_anchor_H_def l4_b0_anchor_base_key_present
        l4_b0_anchor_no_source_event_for_key l4_b0_anchor_source_key_at_anchor
        cf_b0_anchor_source_key_at_frontier l4_b0_anchor_domain
        cf_b0_anchor_touched_between cf_b0_anchor_table_scope_between
        cf_b0_anchor_replay_keys cf_b0_anchor_apply_key
        cf_b0_anchor_anchor_le_frontier cf_b0_anchor_anchor_complete
        cf_b0_anchor_all_post cf_b0_anchor_no_unclaimed
        cf_b0_anchor_whole_table cf_b0_anchor_virtual_cut
        cf_b0_anchor_unrestricted_equality
  by simp


subsection \<open>Same-coordinate anchor and frontier boundaries (constructed)\<close>

lemma cf_same_boundary_latest_frontier_800:
  "latest_src_event l4_same_boundary_H (l4f_frontier CSameBoundary) (800::nat) = Some 0"
  unfolding latest_src_event_def l4_same_boundary_H_def
  using ec1_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma cf_same_boundary_latest_frontier_900:
  "latest_src_event l4_same_boundary_H (l4f_frontier CSameBoundary) (900::nat) = Some 1"
  unfolding latest_src_event_def l4_same_boundary_H_def
  using ec1_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma cf_same_boundary_source_frontier_800:
  "Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary) (800::nat)
     = Some 8000"
  unfolding Src_def using cf_same_boundary_latest_frontier_800
  by (simp add: l4_same_boundary_H_def)

lemma cf_same_boundary_source_frontier_900:
  "Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary) (900::nat)
     = Some 9000"
  unfolding Src_def using cf_same_boundary_latest_frontier_900
  by (simp add: l4_same_boundary_H_def)

lemma cf_same_boundary_touched_between:
  "touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary) = {900}"
proof (rule subset_antisym)
  show "touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary) \<subseteq> {900}"
    unfolding touched_between_def l4_same_boundary_H_def l4_anchor_def
    by auto
next
  show "{900} \<subseteq> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)"
  proof
    fix k :: nat
    assume "k \<in> {900}"
    hence k900: "k = 900" by simp
    have in_H: "(ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H"
      by (simp add: l4_same_boundary_H_def)
    have after_anchor: "l4_anchor < ec4"
      using ec1_less_ec4 by (simp add: l4_anchor_def)
    have before_frontier: "ec4 \<le> l4f_frontier CSameBoundary"
      by (simp add: less_eq_src_coord_def src_le_refl)
    show "k \<in> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)"
      unfolding touched_between_def
      using in_H k900 after_anchor before_frontier
      by (intro CollectI exI[where x=ec4]
                exI[where x="Insert (900::nat) (9000::nat)"]) auto
  qed
qed

lemma cf_same_boundary_anchor_key_not_touched:
  "(800::nat) \<notin> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)"
  using cf_same_boundary_touched_between by simp

lemma cf_same_boundary_frontier_key_touched:
  "(900::nat) \<in> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)"
  using cf_same_boundary_touched_between by simp

lemma cf_same_boundary_table_scope_between:
  "table_scope_between l4_same_boundary_b0 l4_same_boundary_H l4_anchor
     (l4f_frontier CSameBoundary) = l4f_scope CSameBoundary"
  unfolding table_scope_between_def
  using l4_same_boundary_anchor_domain cf_same_boundary_touched_between by auto

lemma cf_same_boundary_replay_keys:
  "replay_keys (l4f_clean_prefix CSameBoundary) = {800, 900}"
  unfolding replay_keys_def by (auto simp: l4_same_boundary_prefix_def)

lemma cf_same_boundary_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CSameBoundary) (l4f_scope CSameBoundary)"
  unfolding no_unclaimed_replay_keys_def using cf_same_boundary_replay_keys by simp

lemma cf_same_boundary_anchor_complete:
  "anchor_complete_at_boundary l4_same_boundary_b0 l4_same_boundary_H l4_anchor
     (l4f_scope CSameBoundary)"
  unfolding anchor_complete_at_boundary_def using l4_same_boundary_anchor_domain by simp

lemma cf_same_boundary_all_post:
  "all_post_anchor_changes_covered l4_same_boundary_H l4_anchor
     (l4f_frontier CSameBoundary) (l4f_scope CSameBoundary)"
  unfolding all_post_anchor_changes_covered_def
  using cf_same_boundary_touched_between by simp

lemma cf_same_boundary_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CSameBoundary"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma cf_same_boundary_whole_table:
  "cf.whole_table_claim_scope l4_same_boundary_b0 CSameBoundary l4_same_boundary_H l4_anchor"
  unfolding cf.whole_table_claim_scope_def
  using cf_same_boundary_anchor_le_frontier cf_same_boundary_anchor_complete
        cf_same_boundary_all_post cf_same_boundary_no_unclaimed by blast

lemma cf_same_boundary_apply:
  "Apply (l4f_clean_prefix CSameBoundary) =
     (\<lambda>k. if k = (800::nat) then Some (8000::nat)
          else if k = 900 then Some 9000 else None)"
  by (rule ext)
     (simp add: Apply_def l4_same_boundary_prefix_def)

lemma cf_same_boundary_apply_800:
  "Apply (l4f_clean_prefix CSameBoundary) (800::nat) = Some 8000"
  by (simp add: l4_same_boundary_prefix_def Apply_def)

lemma cf_same_boundary_apply_900:
  "Apply (l4f_clean_prefix CSameBoundary) (900::nat) = Some 9000"
  by (simp add: l4_same_boundary_prefix_def Apply_def)

lemma cf_same_boundary_virtual_cut:
  "cf.virtual_cut l4_same_boundary_b0 CSameBoundary l4_same_boundary_H"
  unfolding cf.virtual_cut_def virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> l4f_scope CSameBoundary
         then Apply (l4f_clean_prefix CSameBoundary) k else None)
      = (if k \<in> l4f_scope CSameBoundary
         then Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary) k
         else None)"
  proof (cases "k = 800")
    case True
    thus ?thesis
      using cf_same_boundary_apply_800 cf_same_boundary_source_frontier_800 by simp
  next
    case not800: False
    show ?thesis
    proof (cases "k = 900")
      case True
      thus ?thesis
        using cf_same_boundary_apply_900 cf_same_boundary_source_frontier_900 by simp
    next
      case False
      with not800 show ?thesis by simp
    qed
  qed
qed

lemma cf_same_boundary_unrestricted_equality:
  "Apply (l4f_clean_prefix CSameBoundary)
   = Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary)"
  by (rule cf.whole_table_equality_from_claim_scope
        [OF cf_same_boundary_virtual_cut cf_same_boundary_whole_table])

theorem layer4_same_coordinate_boundary_fixture_constructed:
  "(ec1, Insert (800::nat) (8000::nat)) \<in> set l4_same_boundary_H
   \<and> (ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H
   \<and> l4f_frontier CSameBoundary = ec4
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor 800 = Some 8000
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor 900 = None
   \<and> Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary) 900 = Some 9000
   \<and> anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor = {800}
   \<and> (800::nat) \<in> anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor
   \<and> (900::nat) \<notin> anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor
   \<and> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary) = {900}
   \<and> 800 \<notin> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)
   \<and> 900 \<in> touched_between l4_same_boundary_H l4_anchor (l4f_frontier CSameBoundary)
   \<and> table_scope_between l4_same_boundary_b0 l4_same_boundary_H l4_anchor
        (l4f_frontier CSameBoundary) = l4f_scope CSameBoundary
   \<and> l4f_scope CSameBoundary = {800, 900}
   \<and> replay_keys (l4f_clean_prefix CSameBoundary) = {800, 900}
   \<and> no_unclaimed_replay_keys (l4f_clean_prefix CSameBoundary) (l4f_scope CSameBoundary)
   \<and> cf.whole_table_claim_scope l4_same_boundary_b0 CSameBoundary l4_same_boundary_H l4_anchor
   \<and> cf.virtual_cut l4_same_boundary_b0 CSameBoundary l4_same_boundary_H
   \<and> Apply (l4f_clean_prefix CSameBoundary)
      = Src l4_same_boundary_b0 l4_same_boundary_H (l4f_frontier CSameBoundary)"
  using l4_same_boundary_anchor_event_in_history l4_same_boundary_frontier_event_in_history
        l4_same_boundary_source_anchor_800 l4_same_boundary_source_anchor_900
        cf_same_boundary_source_frontier_900 l4_same_boundary_anchor_domain
        l4_same_boundary_anchor_key_in_anchor_domain
        l4_same_boundary_frontier_key_not_in_anchor_domain
        cf_same_boundary_touched_between cf_same_boundary_anchor_key_not_touched
        cf_same_boundary_frontier_key_touched cf_same_boundary_table_scope_between
        cf_same_boundary_replay_keys cf_same_boundary_no_unclaimed
        cf_same_boundary_whole_table cf_same_boundary_virtual_cut
        cf_same_boundary_unrestricted_equality
  by simp


subsection \<open>Materialized-run ambiguity is not Layer 4 evidence (constructed)\<close>

text \<open>A run-sensitive boundary fixture. The certificate @{const CAmbig} exposes the
  same Layer 4 surface as the running-example witness (scope, frontier, clean
  prefix), yet @{term materializes_run} is a relation: the same certificate is
  materialized by two distinct runs whose chunk sets, and whose responsible chunk
  for key 100, differ. Layer 4 must therefore not infer responsible-chunk or
  watermark facts from @{const whole_table_claim_scope} or any other set-only
  certificate predicate. The two runs are taken from a @{typ nat} run carrier
  (@{text 0} and @{text 1}); the interpretation @{text amb} differs from @{text cf}
  only in its run side (a two-element carrier rather than the degenerate
  @{typ unit}), so the materialization relation can hold for two distinct runs.
  The fixture is materialization-relational only: it does not assert
  @{const cert_accessors_agree} on the runs (their constructed @{const clean_prefix_of}
  cannot equal the two-coordinate running-example clean prefix); the
  materialization-relational form already discharges the overclaim-control point.\<close>

definition l4f_amb_chunks :: "nat \<Rightarrow> nat set" where
  "l4f_amb_chunks r = (if r = 0 then {0} else if r = 1 then {1} else {})"

definition l4f_amb_chunks_list :: "nat \<Rightarrow> nat list" where
  "l4f_amb_chunks_list r = (if r = 0 then [0] else if r = 1 then [1] else [])"

definition l4f_amb_responsible :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "l4f_amb_responsible r k =
     (if r = 0 then (if k = 100 then Some 0 else None)
      else if r = 1 then (if k = 100 then Some 1 else None) else None)"

definition l4f_amb_materializes :: "l4f_cert \<Rightarrow> unit \<Rightarrow> nat \<Rightarrow> bool" where
  "l4f_amb_materializes C E r \<longleftrightarrow> C = CAmbig \<and> (r = 0 \<or> r = 1)"

text \<open>The ambiguity interpretation: the run side is a @{typ nat} carrier so the
  materialization relation can hold for the two distinct runs @{text 0} and
  @{text 1}; the certificate side reuses @{const l4f_scope} / @{const l4f_frontier}
  / @{const l4f_clean_prefix} (so @{const CAmbig} carries the running-example
  surface). The two inherited @{const chunks_list} obligations hold definitionally
  --- @{term "set (l4f_amb_chunks_list r) = l4f_amb_chunks r"} and
  @{term "distinct (l4f_amb_chunks_list r)"} are parallel if-then-else over
  @{text r} --- so the interpretation introduces no axiom.\<close>

global_interpretation amb: dblog_cert_substrate
  "\<lambda>_::nat. ({} :: nat set)"                                        \<comment> \<open>@{text scope_of}\<close>
  "\<lambda>_::nat. c0"                                                     \<comment> \<open>@{text frontier_of}\<close>
  l4f_amb_chunks                                                     \<comment> \<open>chunks\<close>
  "\<lambda>_::nat. ([] :: (nat, nat) src_history)"                         \<comment> \<open>@{text src_history_of}\<close>
  "\<lambda>_::nat. \<lambda>_::nat. \<lambda>_::nat. (None :: nat option option)"           \<comment> \<open>@{text chunk_read_result}\<close>
  "\<lambda>_::nat. ([] :: (src_coord \<times> (nat, nat) source_event) list)"     \<comment> \<open>@{text cdc_events_of}\<close>
  l4f_amb_chunks_list                                                \<comment> \<open>@{text chunks_list}\<close>
  "\<lambda>_::nat. \<lambda>_::nat. ({} :: nat set)"                               \<comment> \<open>@{text chunk_domain}\<close>
  l4f_amb_responsible                                                \<comment> \<open>@{text responsible_chunk}\<close>
  "\<lambda>_::nat. \<lambda>_::nat. c0"                                            \<comment> \<open>@{text chunk_lower_watermark}\<close>
  "\<lambda>_::nat. \<lambda>_::nat. c0"                                            \<comment> \<open>@{text chunk_upper_watermark}\<close>
  "\<lambda>_::nat. \<lambda>_::nat. c0"                                            \<comment> \<open>@{text chunk_read_coordinate}\<close>
  l4f_scope l4f_frontier l4f_clean_prefix
  "\<lambda>_::l4f_cert. \<lambda>_::unit. Reject"                                  \<comment> \<open>verify\<close>
  Accept                                                            \<comment> \<open>@{text accept_value}\<close>
  "\<lambda>_::unit. \<lambda>_::(nat \<rightharpoonup> nat). \<lambda>_::(nat, nat) src_history. \<lambda>_::unit. False"
                                                                    \<comment> \<open>@{text faithful_source_observation}\<close>
  l4f_amb_materializes                                              \<comment> \<open>@{text materializes_run}\<close>
  "\<lambda>_::l4f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text evidence_bound_to_cert}\<close>
  "\<lambda>_::l4f_cert. \<lambda>_::unit. False"                                   \<comment> \<open>@{text source_side_schema_supported}\<close>
  by unfold_locales (simp_all add: l4f_amb_chunks_def l4f_amb_chunks_list_def)

lemma amb_ambig_virtual_cut:
  "amb.virtual_cut b0_ex CAmbig H_ex"
  unfolding amb.virtual_cut_def virtual_cut_state_def
  using rep_ex_virtual_cut_state by (simp add: virtual_cut_state_def)

lemma amb_ambig_anchor_complete:
  "anchor_complete_at_boundary b0_ex H_ex l4_anchor (l4f_scope CAmbig)"
  unfolding anchor_complete_at_boundary_def using l4_anchor_domain by simp

lemma amb_ambig_all_post:
  "all_post_anchor_changes_covered H_ex l4_anchor (l4f_frontier CAmbig) (l4f_scope CAmbig)"
  unfolding all_post_anchor_changes_covered_def using touched_H_ex_anchor_ec4 by simp

lemma amb_ambig_no_unclaimed:
  "no_unclaimed_replay_keys (l4f_clean_prefix CAmbig) (l4f_scope CAmbig)"
  unfolding no_unclaimed_replay_keys_def using rep_ex_replay_keys by simp

lemma amb_ambig_anchor_le_frontier:
  "l4_anchor \<le> l4f_frontier CAmbig"
  using ec1_le_ec4 by (simp add: l4_anchor_def less_eq_src_coord_def)

lemma amb_ambig_whole_table:
  "amb.whole_table_claim_scope b0_ex CAmbig H_ex l4_anchor"
  unfolding amb.whole_table_claim_scope_def
  using amb_ambig_anchor_le_frontier amb_ambig_anchor_complete
        amb_ambig_all_post amb_ambig_no_unclaimed by blast

lemma amb_ambig_unrestricted_equality:
  "Apply (l4f_clean_prefix CAmbig) = Src b0_ex H_ex (l4f_frontier CAmbig)"
  by (rule amb.whole_table_equality_from_claim_scope
        [OF amb_ambig_virtual_cut amb_ambig_whole_table])

lemma amb_materializes_left: "l4f_amb_materializes CAmbig () 0"
  by (simp add: l4f_amb_materializes_def)

lemma amb_materializes_right: "l4f_amb_materializes CAmbig () 1"
  by (simp add: l4f_amb_materializes_def)

lemma amb_chunks_differ: "l4f_amb_chunks 0 \<noteq> l4f_amb_chunks 1"
  by (simp add: l4f_amb_chunks_def)

lemma amb_responsible_differ:
  "l4f_amb_responsible 0 100 \<noteq> l4f_amb_responsible 1 100"
  by (simp add: l4f_amb_responsible_def)

theorem layer4_materialized_run_ambiguity_fixture_constructed:
  "l4f_amb_materializes CAmbig () 0
   \<and> l4f_amb_materializes CAmbig () 1
   \<and> l4f_scope CAmbig = {100, 200, 300}
   \<and> l4f_frontier CAmbig = ec4
   \<and> l4f_clean_prefix CAmbig = ex_model.clean_prefix_of ()
   \<and> l4f_amb_chunks 0 \<noteq> l4f_amb_chunks 1
   \<and> l4f_amb_responsible 0 100 \<noteq> l4f_amb_responsible 1 100
   \<and> amb.whole_table_claim_scope b0_ex CAmbig H_ex l4_anchor
   \<and> amb.virtual_cut b0_ex CAmbig H_ex
   \<and> Apply (l4f_clean_prefix CAmbig) = Src b0_ex H_ex (l4f_frontier CAmbig)"
  using amb_materializes_left amb_materializes_right
        amb_chunks_differ amb_responsible_differ
        amb_ambig_whole_table amb_ambig_virtual_cut
        amb_ambig_unrestricted_equality
  by simp


subsection \<open>Constructed Layer 4 fixture bundle\<close>

text \<open>The ten Layer 4 negative / boundary / run-ambiguity fixtures hold over
  the construction --- the cert-accessor fixtures over the @{text cf}
  interpretation, the run-ambiguity fixture over the @{text amb} interpretation.
  Together with the reused source-side lemmas of
  @{text Layer4_Fixtures_Core} and the constructed
  running-example facts of
  @{text Layer01_Virtual_Cut_Example_Inst}, the
  whole Layer 4 fixture bundle is established with no axioms anywhere.\<close>

theorem layer4_fixture_bundle_constructed:
  "(\<not> cf.whole_table_claim_scope b0_ex CMissingInsert H_ex l4_anchor)
   \<and> (\<not> cf.whole_table_claim_scope b0_ex CDeleteTouch l4_delete_touch_H l4_anchor)
   \<and> cf.whole_table_claim_scope l4_empty_b0 CEmpty l4_empty_H l4_anchor
   \<and> (cf.whole_table_claim_scope b0_ex CClaimRefresh H_ex l4_anchor
       \<and> \<not> cf.virtual_cut b0_ex CClaimRefresh H_ex)
   \<and> (\<not> cf.whole_table_claim_scope l4_after_frontier_b0 CAfterFrontier
        l4_after_frontier_H l4_after_frontier_anchor)
   \<and> cf.whole_table_claim_scope b0_ex CUpdateRefresh H_ex l4_anchor
   \<and> (\<not> cf.whole_table_claim_scope b0_ex CUnclaimed H_ex l4_anchor)
   \<and> cf.whole_table_claim_scope l4_b0_anchor_b0 CB0Anchor l4_b0_anchor_H l4_anchor
   \<and> cf.whole_table_claim_scope l4_same_boundary_b0 CSameBoundary l4_same_boundary_H l4_anchor
   \<and> (amb.whole_table_claim_scope b0_ex CAmbig H_ex l4_anchor
       \<and> l4f_amb_chunks 0 \<noteq> l4f_amb_chunks 1)"
  using cf_missing_insert_not_whole_table
        cf_delete_touch_not_whole_table
        cf_empty_whole_table_claim_scope
        cf_claim_refresh_whole_table cf_claim_refresh_not_virtual_cut
        cf_after_frontier_not_whole_table
        cf_update_refresh_whole_table
        cf_unclaimed_not_whole_table
        cf_b0_anchor_whole_table
        cf_same_boundary_whole_table
        amb_ambig_whole_table amb_chunks_differ
  by blast

end
