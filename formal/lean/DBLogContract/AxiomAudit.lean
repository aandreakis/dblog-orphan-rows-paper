import DBLogContract.ContractBase
import DBLogContract.CutTheorem
import DBLogContract.ContractWitnesses

/-!
# Axiom audit

This file prints the axiom footprint of every ported theorem. It is
imported by the library root, so every `lake build` elaborates it
and shows the listing. The expected footprint of each theorem is a
subset of `[propext, Classical.choice, Quot.sound]`, the three
standard axioms of the Lean 4 core logic. Any other axiom, and any
`sorry`, would appear in this output.
-/

namespace DBLogContract

-- Contract base: events, states, folds.
#print axioms evs_for_nil
#print axioms evs_for_cons
#print axioms evs_for_append
#print axioms state_after_nil
#print axioms state_after_cons
#print axioms state_after_append
#print axioms state_after_snoc
#print axioms state_after_key
#print axioms state_after_no_events
#print axioms state_after_last_event
#print axioms state_after_append_no_k
#print axioms take_prefix_take

-- Coordinate spaces and windows.
#print axioms CoordinateSpace.cle_refl
#print axioms CoordinateSpace.cle_trans
#print axioms CoordinateSpace.pfx_length
#print axioms CoordinateSpace.cle_iff_prefix
#print axioms CoordinateSpace.den_nested
#print axioms CoordinateSpace.pfx_split
#print axioms CoordinateSpace.win_length
#print axioms CoordinateSpace.win_empty_iff
#print axioms CoordinateSpace.win_split
#print axioms CoordinateSpace.win_nth
#print axioms CoordinateSpace.oracle_set_reading
#print axioms CoordinateSpace.evs_for_pfx_split
#print axioms CoordinateSpace.evs_for_win_split
#print axioms CoordinateSpace.win_invariant_state
#print axioms CoordinateSpace.win_invariant_state2

-- The contract and the cut theorem.
#print axioms getLast_eq_of_eq
#print axioms sink_at_case_events
#print axioms CaptureContract.dom_sub_scope
#print axioms CaptureContract.covering_unit_unique
#print axioms CaptureContract.the_unit_props
#print axioms CaptureContract.the_unit_eq
#print axioms CaptureContract.the_unit_position_unique
#print axioms CaptureContract.contract_cut_at
#print axioms CaptureContract.contract_cut
#print axioms CaptureContract.contract_cut_scope
#print axioms CaptureContract.shared_witness_trajectory_at
#print axioms CaptureContract.shared_witness_trajectory
#print axioms CaptureContract.continuation
#print axioms mixing_union
#print axioms mixing_shared_witness_lift
#print axioms mixing_shared_honesty_lift

-- The torn-read witness.
#print axioms den_w_cases
#print axioms wit_torn_contract
#print axioms fix_torn_no_single_witness
#print axioms wit_torn_the_unit
#print axioms wit_torn_cut

-- The tablesync shape (paper Proposition 2).
#print axioms wit_sync_contract
#print axioms wit_sync_the_unit_2
#print axioms fix_sync_trajectory_breaks
#print axioms fix_sync_no_early_onset
#print axioms sync_memberB_contract
#print axioms wit_sync_memberB_T3

-- The amortized shared bracket.
#print axioms wit_shr_contract
#print axioms wit_shared_bracket_T3

-- The stream substrate and the window-discard discipline.
#print axioms evs_for_map_snd
#print axioms map_fst_zipIdx
#print axioms pairwise_zipIdx_lt
#print axioms nodup_zipIdx
#print axioms flatMap_eq_nil_of_forall
#print axioms flatMap_single
#print axioms nodup_filter_eq
#print axioms map_snd_tagged_seg
#print axioms tagged_seg_split
#print axioms seg_split
#print axioms seg_length
#print axioms flatMap_congr
#print axioms tagged_seg_self
#print axioms titems_append
#print axioms titems_flatMap
#print axioms titems_cons
#print axioms flatMap_titems_single
#print axioms mem_tagged_seg_bounds
#print axioms pairwise_tagged_seg
#print axioms CaptureContract.svl_exists
#print axioms CaptureContract.titems_close_block
#print axioms CaptureContract.titems_closes_at
#print axioms CaptureContract.titems_emission_master
#print axioms CaptureContract.evs_emission_master
#print axioms CaptureContract.window_discard_replay
#print axioms CaptureContract.window_discard_monotone

-- The surviving refresh under window-discard.
#print axioms wit_surv_contract
#print axioms wit_surv_svl_ok
#print axioms wit_surv_the_unit
#print axioms wit_surv_replay_theorem
#print axioms wit_surv_replay_value

end DBLogContract
