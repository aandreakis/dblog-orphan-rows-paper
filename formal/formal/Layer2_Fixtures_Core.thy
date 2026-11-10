(*  Title:   Layer2_Fixtures_Core.thy
    Author:  Andreas Andreakis
    SPDX-License-Identifier: BSD-3-Clause
*)

theory Layer2_Fixtures_Core
  imports DBLog_Run_Core Dual_Write_Layer0.Source_Coordinates
begin

section \<open>Layer 2 canonical-clean-prefix and frontier fixtures\<close>

text \<open>
  Carrier-independent Layer 2 fixtures: the canonical-clean-prefix structural
  fixtures and the frontier off-by-one subcases. They range only over the pure
  @{const canonical_clean_prefix} / @{const cdc_event_replays} /
  @{const chunk_read_refreshes} constructions of
  @{theory DBLog_Virtual_Cuts.DBLog_Run_Core} and the source coordinates of
  @{theory Dual_Write_Layer0.Source_Coordinates} --- no run/chunk carrier is
  involved, so these fixtures have no constructed
  @{text Layer2_Fixtures_Inst} counterpart.
\<close>

subsection \<open>Canonical-clean-prefix structural fixtures\<close>

definition l2_one_refresh_read :: "(nat, nat) chunk_read_record" where
  "l2_one_refresh_read =
     \<lparr> crr_domain = {1},
       crr_read_coord = c0,
       crr_observation =
         (\<lambda>k. if k = (1::nat) then Some (Some (5::nat)) else None) \<rparr>"

lemma l2_one_refreshes:
  "chunk_read_refreshes l2_one_refresh_read =
     [Refresh (1::nat) (Some (5::nat)) c0]"
  unfolding l2_one_refresh_read_def chunk_read_refreshes_def
            List.map_filter_def
  by simp

theorem fix_layer2_misordered_clean_prefix_rejected:
  "canonical_clean_prefix
     [l2_one_refresh_read]
     [(l2_cp_c1, Update (1::nat) (7::nat))]
     {1} l2_cp_c1
   \<noteq> [Cdc l2_cp_c1 (Update (1::nat) (7::nat)),
       Refresh (1::nat) (Some (5::nat)) c0]"
  using l2_cp_c0_lt_c1 l2_cp_not_le_c0
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by (simp add: l2_one_refreshes less_src_coord_def src_lt_def)

theorem fix_layer2_extra_refresh_in_scope_rejected:
  "canonical_clean_prefix [l2_one_refresh_read] [] {1} c0
   \<noteq> [Refresh (1::nat) (Some (5::nat)) c0,
       Refresh (1::nat) (Some (99::nat)) c0]"
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by (simp add: l2_one_refreshes)

theorem fix_layer2_future_cdc_in_clean_prefix_rejected:
  "Cdc l2_future_c1 (Update (1::nat) (7::nat))
     \<notin> set (canonical_clean_prefix []
          [(l2_future_c1, Update (1::nat) (7::nat))] {1} c0)"
  using l2_future_not_le_c0
  unfolding canonical_clean_prefix_def cdc_event_replays_def
            List.map_filter_def
  by simp

subsection \<open>Frontier off-by-one subcases\<close>

theorem fix_layer2_frontier_off_by_one_before_included:
  "Cdc l2_fo_before (Update (1::nat) (7::nat))
     \<in> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_before, Update (1::nat) (7::nat))])"
  using l2_fo_before_le_frontier
  unfolding cdc_event_replays_def List.map_filter_def
  by simp

theorem fix_layer2_frontier_off_by_one_equal_included:
  "Cdc l2_fo_frontier (Update (1::nat) (7::nat))
     \<in> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_frontier, Update (1::nat) (7::nat))])"
  unfolding cdc_event_replays_def List.map_filter_def
  by (simp add: less_eq_src_coord_def src_le_refl)

theorem fix_layer2_frontier_off_by_one_after_rejected:
  "Cdc l2_fo_after (Update (1::nat) (7::nat))
     \<notin> set (cdc_event_replays {1} l2_fo_frontier
          [(l2_fo_after, Update (1::nat) (7::nat))])"
  using l2_fo_after_not_le_frontier
  unfolding cdc_event_replays_def List.map_filter_def
  by simp

end
