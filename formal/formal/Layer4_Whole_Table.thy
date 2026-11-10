(*  Title:   Layer4_Whole_Table.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer4_Whole_Table
  imports Virtual_Cut Virtual_Cut_Core
begin

section \<open>Layer 4: the whole-table specialization\<close>

text \<open>
  Layer 4 whole-table anchor-domain specialization.

  The reader-facing paper keeps the compact notation
  @{text "whole-table-claim-scope(C,H,b)"}.  The formal surface threads the
  deployment base state @{text b0} explicitly, because @{const Src} and
  faithful source observation are both fixed-base-state objects.
\<close>

text \<open>
  \<^bold>\<open>The pure anchor / table-scope definitions and outside-scope bridge lemmas
  live in @{text Virtual_Cut_Core}\<close>: @{text anchor_domain},
  @{text touched_between}, @{text table_scope_between},
  @{text anchor_complete_at_boundary}, @{text all_post_anchor_changes_covered},
  @{text replay_keys}, @{text no_unclaimed_replay_keys}, and the bridge lemmas
  @{text source_outside_table_scope_absent},
  @{text apply_outside_replay_keys_none},
  @{text unrestricted_equality_from_scoped_equality},
  @{text whole_table_equality_from_scoped_equality}. They reference no
  certificate accessor and are used here via the
  @{text Virtual_Cut_Core} import; the
  @{text DBLog_Cert_Substrate} locale reaches them the same way, without
  importing this theory. The scoped-equality bridge is stated over the raw
  restricted
  equality; the cert-side caller below unfolds @{const virtual_cut_state}
  before applying it.
\<close>

subsection \<open>Whole-table claim scope (cert-side)\<close>

definition whole_table_claim_scope
  :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k, 'v) cert \<Rightarrow> ('k, 'v) src_history
      \<Rightarrow> frontier \<Rightarrow> bool"
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

subsection \<open>Outside-scope bridge to whole-table equality (cert-side)\<close>

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

subsection \<open>Layer 4 theorem surface over accepted certificates\<close>

context layer3_checker_substrate
begin

theorem accepted_whole_table_anchor_domain_specialization:
  fixes b0 :: "'k \<rightharpoonup> 'v"
    and H :: "('k, 'v) src_history"
    and Raw :: raw_observation
    and b :: frontier
  assumes accept: "verify C E = Accept"
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
