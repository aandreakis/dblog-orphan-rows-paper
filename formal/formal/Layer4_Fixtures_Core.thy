(*  Title:   Layer4_Fixtures_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer4_Fixtures_Core
  imports Layer4_Witnesses_Core Virtual_Cut
begin

section \<open>Carrier-independent Layer 4 fixture data\<close>

text \<open>
  The carrier-independent data of the Layer 4 fixture family, used by the
  constructed interpretation @{text Layer4_Fixtures_Inst}: per-fixture base
  states @{text "l4_..._b0"}, histories @{text "l4_..._H"}, replay prefixes
  @{text "l4_..._prefix"}, and their
  @{const Apply} / @{const Src} / @{const latest_src_event} / anchor-domain /
  scoped-virtual-cut-state computation lemmas. None of this mentions a run,
  chunk, or certificate carrier. The theory imports
  @{theory DBLog_Virtual_Cuts.Layer4_Witnesses_Core} (for the anchor boundary
  @{const l4_anchor} and the running-example anchor facts) and
  @{theory DBLog_Virtual_Cuts.Virtual_Cut} (for @{const virtual_cut_state}).
\<close>

definition l4_missing_insert_prefix :: "(nat, nat) replay_event list" where
  "l4_missing_insert_prefix =
     [ Cdc ec1 (Update 100 3000),
       Refresh (100::nat) (Some (3000::nat)) ec1,
       Refresh 200 (Some 10000) ec1,
       Cdc ec3 (Update 200 12000) ]"

lemma l4_missing_insert_apply_100:
  "Apply l4_missing_insert_prefix (100::nat) = Some (3000::nat)"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_apply_200:
  "Apply l4_missing_insert_prefix (200::nat) = Some (12000::nat)"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_apply_300:
  "Apply l4_missing_insert_prefix (300::nat) = None"
  unfolding l4_missing_insert_prefix_def Apply_def by simp

lemma l4_missing_insert_replay_keys:
  "replay_keys l4_missing_insert_prefix = {100, 200}"
  unfolding replay_keys_def l4_missing_insert_prefix_def
  by auto

lemma l4_missing_insert_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_missing_insert_prefix {100, 200} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200} then Apply l4_missing_insert_prefix k else None)
      = (if k \<in> {100, 200} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_missing_insert_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_missing_insert_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case False
      with not100 show ?thesis by simp
    qed
  qed
qed

definition l4_delete_touch_H :: "(nat, nat) src_history" where
  "l4_delete_touch_H =
     [ (ec1, Update 100 3000),
       (ec2, Delete (400::nat)),
       (ec3, Update 200 12000),
       (ec4, Update 300 3500) ]"

lemma latest_src_event_l4_delete_touch_ec4_100:
  "latest_src_event l4_delete_touch_H ec4 (100::nat) = Some 0"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_200:
  "latest_src_event l4_delete_touch_H ec4 (200::nat) = Some 2"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_300:
  "latest_src_event l4_delete_touch_H ec4 (300::nat) = Some 3"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_400:
  "latest_src_event l4_delete_touch_H ec4 (400::nat) = Some 1"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma latest_src_event_l4_delete_touch_ec4_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200" and "k \<noteq> 300" and "k \<noteq> 400"
  shows "latest_src_event l4_delete_touch_H ec4 k = None"
  unfolding latest_src_event_def l4_delete_touch_H_def
  using assms ec1_le_ec4 ec2_le_ec4 ec3_le_ec4 src_le_refl[where c=ec4]
  by simp

lemma Src_b0_ex_l4_delete_touch_ec4_100:
  "Src b0_ex l4_delete_touch_H ec4 (100::nat) = Some 3000"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_100
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_200:
  "Src b0_ex l4_delete_touch_H ec4 (200::nat) = Some 12000"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_200
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_300:
  "Src b0_ex l4_delete_touch_H ec4 (300::nat) = Some 3500"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_300
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_400:
  "Src b0_ex l4_delete_touch_H ec4 (400::nat) = None"
  unfolding Src_def using latest_src_event_l4_delete_touch_ec4_400
  by (simp add: l4_delete_touch_H_def)

lemma Src_b0_ex_l4_delete_touch_ec4_other:
  assumes "k \<noteq> (100::nat)" and "k \<noteq> 200" and "k \<noteq> 300" and "k \<noteq> 400"
  shows "Src b0_ex l4_delete_touch_H ec4 k = None"
  unfolding Src_def b0_ex_def
  using latest_src_event_l4_delete_touch_ec4_other[OF assms] assms
  by simp

lemma Src_b0_ex_l4_delete_touch_ec4:
  "Src b0_ex l4_delete_touch_H ec4 =
     (\<lambda>k. if k = (100::nat) then Some (3000::nat)
          else if k = 200 then Some 12000
          else if k = 300 then Some 3500
          else None)"
proof
  fix k :: nat
  show "Src b0_ex l4_delete_touch_H ec4 k =
        (if k = (100::nat) then Some (3000::nat)
         else if k = 200 then Some 12000
         else if k = 300 then Some 3500
         else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis using Src_b0_ex_l4_delete_touch_ec4_300 by simp
      next
        case not300: False
        show ?thesis
        proof (cases "k = 400")
          case True
          thus ?thesis
            using not100 not200 not300 Src_b0_ex_l4_delete_touch_ec4_400
            by simp
        next
          case False
          with not100 not200 not300 show ?thesis
            using Src_b0_ex_l4_delete_touch_ec4_other by simp
        qed
      qed
    qed
  qed
qed

lemma l4_delete_touch_anchor_domain:
  "anchor_domain b0_ex l4_delete_touch_H l4_anchor = {100, 200}"
  unfolding anchor_domain_def l4_anchor_def Src_def latest_src_event_def
            l4_delete_touch_H_def b0_ex_def
  using src_le_refl[where c=ec1] not_src_le_ec2_ec1
        not_src_le_ec3_ec1 not_src_le_ec4_ec1
  by auto

definition l4_empty_b0 :: "nat \<rightharpoonup> nat" where
  "l4_empty_b0 = (\<lambda>_. None)"

definition l4_empty_H :: "(nat, nat) src_history" where
  "l4_empty_H = []"

lemma l4_empty_anchor_domain:
  "anchor_domain l4_empty_b0 l4_empty_H l4_anchor = {}"
  by (simp add: anchor_domain_def Src_def latest_src_event_def
                l4_empty_b0_def l4_empty_H_def)

definition l4_after_frontier_b0 :: "nat \<rightharpoonup> nat" where
  "l4_after_frontier_b0 = (\<lambda>_. None)"

definition l4_after_frontier_H :: "(nat, nat) src_history" where
  "l4_after_frontier_H =
     [ (ec1, Insert (500::nat) (9000::nat)),
       (ec2, Delete (500::nat)) ]"

definition l4_after_frontier_anchor :: frontier where
  "l4_after_frontier_anchor = ec2"

lemma latest_src_event_l4_after_frontier_ec1_500:
  "latest_src_event l4_after_frontier_H ec1 (500::nat) = Some 0"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using src_le_refl[where c=ec1] not_src_le_ec2_ec1
  by simp

lemma latest_src_event_l4_after_frontier_ec2_500:
  "latest_src_event l4_after_frontier_H ec2 (500::nat) = Some 1"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using ec1_le_ec2 src_le_refl[where c=ec2]
  by simp

lemma latest_src_event_l4_after_frontier_ec2_other:
  assumes "k \<noteq> (500::nat)"
  shows "latest_src_event l4_after_frontier_H ec2 k = None"
  unfolding latest_src_event_def l4_after_frontier_H_def
  using assms
  by simp

lemma l4_after_frontier_source_absent_at_anchor_500:
  "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor (500::nat) = None"
  unfolding Src_def
  using latest_src_event_l4_after_frontier_ec2_500
  by (simp add: l4_after_frontier_H_def l4_after_frontier_anchor_def)

lemma l4_after_frontier_source_absent_at_anchor_other:
  assumes "k \<noteq> (500::nat)"
  shows "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor k = None"
  unfolding Src_def l4_after_frontier_b0_def
  using latest_src_event_l4_after_frontier_ec2_other[OF assms]
  by (simp add: l4_after_frontier_anchor_def)

lemma l4_after_frontier_source_at_anchor_empty:
  "Src l4_after_frontier_b0 l4_after_frontier_H
      l4_after_frontier_anchor = (\<lambda>_. None)"
proof
  fix k :: nat
  show "Src l4_after_frontier_b0 l4_after_frontier_H
          l4_after_frontier_anchor k = None"
  proof (cases "k = 500")
    case True
    thus ?thesis using l4_after_frontier_source_absent_at_anchor_500
      by simp
  next
    case False
    thus ?thesis using l4_after_frontier_source_absent_at_anchor_other
      by simp
  qed
qed

lemma l4_after_frontier_anchor_domain_empty:
  "anchor_domain l4_after_frontier_b0 l4_after_frontier_H
     l4_after_frontier_anchor = {}"
  by (simp add: anchor_domain_def l4_after_frontier_source_at_anchor_empty)

definition l4_update_refresh_prefix :: "(nat, nat) replay_event list" where
  "l4_update_refresh_prefix =
     [ Cdc ec1 (Update (100::nat) (3000::nat)),
       Refresh 100 (Some 3000) ec1,
       Refresh 200 (Some 12000) ec4,
       Cdc ec2 (Insert 300 2500),
       Cdc ec4 (Update 300 3500) ]"

lemma l4_update_refresh_apply_100:
  "Apply l4_update_refresh_prefix (100::nat) = Some 3000"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_apply_200:
  "Apply l4_update_refresh_prefix (200::nat) = Some 12000"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_apply_300:
  "Apply l4_update_refresh_prefix (300::nat) = Some 3500"
  unfolding l4_update_refresh_prefix_def Apply_def by simp

lemma l4_update_refresh_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_update_refresh_prefix {100, 200, 300} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200, 300} then Apply l4_update_refresh_prefix k else None)
      = (if k \<in> {100, 200, 300} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_update_refresh_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_update_refresh_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis
          using l4_update_refresh_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
      next
        case False
        with not100 not200 show ?thesis by simp
      qed
    qed
  qed
qed

lemma l4_update_refresh_source_update_before_refresh:
  "(ec3, Update (200::nat) (12000::nat)) \<in> set H_ex
   \<and> ec3 < ec4"
  using ec3_lt_ec4
  by (simp add: H_ex_def less_src_coord_def)

definition l4_unclaimed_prefix :: "(nat, nat) replay_event list" where
  "l4_unclaimed_prefix =
     [ Cdc ec1 (Update (100::nat) (3000::nat)),
       Refresh 100 (Some 3000) ec1,
       Refresh 200 (Some 10000) ec1,
       Cdc ec2 (Insert 300 2500),
       Cdc ec3 (Update 200 12000),
       Refresh 300 (Some 2500) ec3,
       Cdc ec4 (Update 300 3500),
       Refresh 999 (Some 4242) ec4 ]"

lemma l4_unclaimed_apply_100:
  "Apply l4_unclaimed_prefix (100::nat) = Some 3000"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_200:
  "Apply l4_unclaimed_prefix (200::nat) = Some 12000"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_300:
  "Apply l4_unclaimed_prefix (300::nat) = Some 3500"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_apply_999:
  "Apply l4_unclaimed_prefix (999::nat) = Some 4242"
  unfolding l4_unclaimed_prefix_def Apply_def by simp

lemma l4_unclaimed_scoped_virtual_cut_state:
  "virtual_cut_state b0_ex l4_unclaimed_prefix {100, 200, 300} ec4 H_ex"
  unfolding virtual_cut_state_def restrict_def
proof (rule ext)
  fix k :: nat
  show "(if k \<in> {100, 200, 300} then Apply l4_unclaimed_prefix k else None)
      = (if k \<in> {100, 200, 300} then Src b0_ex H_ex ec4 k else None)"
  proof (cases "k = 100")
    case True
    thus ?thesis
      using l4_unclaimed_apply_100 Src_b0_ex_H_ex_ec4_100 by simp
  next
    case not100: False
    show ?thesis
    proof (cases "k = 200")
      case True
      thus ?thesis
        using l4_unclaimed_apply_200 Src_b0_ex_H_ex_ec4_200 by simp
    next
      case not200: False
      show ?thesis
      proof (cases "k = 300")
        case True
        thus ?thesis
          using l4_unclaimed_apply_300 Src_b0_ex_H_ex_ec4_300 by simp
      next
        case False
        with not100 not200 show ?thesis by simp
      qed
    qed
  qed
qed

definition l4_b0_anchor_b0 :: "nat \<rightharpoonup> nat" where
  "l4_b0_anchor_b0 = (\<lambda>k. if k = (700::nat) then Some (7000::nat) else None)"

definition l4_b0_anchor_H :: "(nat, nat) src_history" where
  "l4_b0_anchor_H = []"

definition l4_b0_anchor_prefix :: "(nat, nat) replay_event list" where
  "l4_b0_anchor_prefix =
     [Refresh (700::nat) (Some (7000::nat)) ec1]"

lemma l4_b0_anchor_base_key_present:
  "l4_b0_anchor_b0 (700::nat) = Some 7000"
  by (simp add: l4_b0_anchor_b0_def)

lemma l4_b0_anchor_no_source_event_for_key:
  "latest_src_event l4_b0_anchor_H l4_anchor (700::nat) = None"
  by (simp add: latest_src_event_def l4_b0_anchor_H_def)

lemma l4_b0_anchor_source_at_anchor:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = l4_b0_anchor_b0"
  by (rule ext) (simp add: Src_def latest_src_event_def
                            l4_b0_anchor_H_def)

lemma l4_b0_anchor_source_key_at_anchor:
  "Src l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor (700::nat)
     = Some 7000"
  using l4_b0_anchor_base_key_present l4_b0_anchor_source_at_anchor
  by simp

lemma l4_b0_anchor_domain:
  "anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor = {700}"
  unfolding anchor_domain_def
  using l4_b0_anchor_source_at_anchor
  by (auto simp: l4_b0_anchor_b0_def)

definition l4_same_boundary_b0 :: "nat \<rightharpoonup> nat" where
  "l4_same_boundary_b0 = (\<lambda>_. None)"

definition l4_same_boundary_H :: "(nat, nat) src_history" where
  "l4_same_boundary_H =
     [ (ec1, Insert (800::nat) (8000::nat)),
       (ec4, Insert (900::nat) (9000::nat)) ]"

definition l4_same_boundary_prefix :: "(nat, nat) replay_event list" where
  "l4_same_boundary_prefix =
     [ Cdc ec1 (Insert (800::nat) (8000::nat)),
       Cdc ec4 (Insert (900::nat) (9000::nat)) ]"

lemma l4_same_boundary_anchor_event_in_history:
  "(ec1, Insert (800::nat) (8000::nat)) \<in> set l4_same_boundary_H"
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_frontier_event_in_history:
  "(ec4, Insert (900::nat) (9000::nat)) \<in> set l4_same_boundary_H"
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_latest_anchor_800:
  "latest_src_event l4_same_boundary_H l4_anchor (800::nat) = Some 0"
  unfolding latest_src_event_def l4_same_boundary_H_def l4_anchor_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by simp

lemma l4_same_boundary_latest_anchor_900:
  "latest_src_event l4_same_boundary_H l4_anchor (900::nat) = None"
  unfolding latest_src_event_def l4_same_boundary_H_def l4_anchor_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by simp

lemma l4_same_boundary_source_anchor_800:
  "Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor (800::nat)
     = Some 8000"
  unfolding Src_def
  using l4_same_boundary_latest_anchor_800
  by (simp add: l4_same_boundary_H_def)

lemma l4_same_boundary_source_anchor_900:
  "Src l4_same_boundary_b0 l4_same_boundary_H l4_anchor (900::nat) = None"
  unfolding Src_def l4_same_boundary_b0_def
  using l4_same_boundary_latest_anchor_900 by simp

lemma l4_same_boundary_anchor_domain:
  "anchor_domain l4_same_boundary_b0 l4_same_boundary_H l4_anchor = {800}"
  unfolding anchor_domain_def l4_same_boundary_b0_def
            l4_same_boundary_H_def l4_anchor_def Src_def latest_src_event_def
  using src_le_refl[where c=ec1] not_src_le_ec4_ec1
  by auto

lemma l4_same_boundary_anchor_key_in_anchor_domain:
  "(800::nat) \<in> anchor_domain l4_same_boundary_b0
     l4_same_boundary_H l4_anchor"
  using l4_same_boundary_anchor_domain by simp

lemma l4_same_boundary_frontier_key_not_in_anchor_domain:
  "(900::nat) \<notin> anchor_domain l4_same_boundary_b0
     l4_same_boundary_H l4_anchor"
  using l4_same_boundary_anchor_domain by simp

section \<open>Further anchor-domain facts\<close>

text \<open>Pure @{const anchor_domain} computation facts on the fixture data above.
  They involve no run, chunk, or certificate carrier and stand on their own,
  with no constructed @{text Layer4_Fixtures_Inst} counterpart.\<close>

lemma l4_claim_refresh_mismatch_anchor_domain:
  "anchor_domain b0_ex H_ex l4_anchor = {100, 200}"
  by (rule l4_anchor_domain)

lemma l4_update_refresh_key_200_anchor_domain:
  "(200::nat) \<in> anchor_domain b0_ex H_ex l4_anchor"
  using l4_anchor_domain by simp

lemma l4_b0_anchor_key_in_anchor_domain:
  "(700::nat) \<in> anchor_domain l4_b0_anchor_b0 l4_b0_anchor_H l4_anchor"
  using l4_b0_anchor_domain by simp

end
