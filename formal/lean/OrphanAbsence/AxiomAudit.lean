import OrphanAbsence.Emission
import OrphanAbsence.Replay
import OrphanAbsence.ChunkRecord
import OrphanAbsence.ContractUnits
import OrphanAbsence.Witnesses
import OrphanAbsence.Composition
import OrphanAbsence.CompositionWitnesses
import OrphanAbsence.Redelivery
import OrphanAbsence.RedeliveryWitnesses
import OrphanAbsence.Interleaved
import OrphanAbsence.InterleavedWitnesses
import OrphanAbsence.Tiling
import OrphanAbsence.TilingWitnesses
import OrphanAbsence.TilingBridge
import OrphanAbsence.Restart
import OrphanAbsence.RestartWitnesses

/-!
# Axiom audit

This file prints the axiom footprint of every theorem of the
`OrphanAbsence` port. It is imported by the library root, so every
`lake build` elaborates it and shows the listing, next to the core's
own audit in `DBLogContract/AxiomAudit.lean`. The expected footprint
of each theorem is a subset of `[propext, Classical.choice,
Quot.sound]`, the three standard axioms of the Lean 4 core logic. Any
other axiom, and any `sorry`, would appear in this output.
-/

namespace DBLogContract

-- Replay depends on a key's own events only.
#print axioms replay_per_key

-- Admissible enumerations.
#print axioms survivors_sub_dom
#print axioms absent_untouched_sub_dom
#print axioms CaptureContract.svl_ok_imp_ok2
#print axioms CaptureContract.svl2_distinct
#print axioms CaptureContract.svl2_sub_dom
#print axioms CaptureContract.svl2_untouched
#print axioms CaptureContract.svl2_surv

-- Per-key characterization of the widened emission.
#print axioms CaptureContract.titems_close_block2
#print axioms CaptureContract.titems_closes_at2
#print axioms CaptureContract.titems_emission_master2
#print axioms CaptureContract.evs_emission_master2

-- Safety from an arbitrary initial sink state.
#print axioms CaptureContract.absent_replay_safe

-- Convergence under coverage.
#print axioms CaptureContract.absent_replay
#print axioms CaptureContract.absent_replay_cut
#print axioms CaptureContract.self_stabilization

-- Existence: the sink-expanded enumeration.
#print axioms exists_nodup_listing
#print axioms CaptureContract.svl2_exists_covering
#print axioms CaptureContract.range_record_converges

-- Partial enumerations, unlisted quiet keys, necessity of coverage.
#print axioms CaptureContract.partial_enumeration_safe
#print axioms CaptureContract.unlisted_quiet_key_kept
#print axioms CaptureContract.coverage_necessary
#print axioms CaptureContract.sink_read_covers

-- The chunk record.
#print axioms dom_minus_except
#print axioms CaptureContract.record_enum_ok2
#print axioms CaptureContract.record_enum_covers
#print axioms CaptureContract.chunk_record_converges
#print axioms CaptureContract.except_overapprox_safe

-- A certified absence is a unit, and a unit splits for late absences.
#print axioms absence_assertion_contract
#print axioms O1_disjoint_iff_pairwise
#print axioms late_absence_split

-- The orphan fixture.
#print axioms wit_orph_contract
#print axioms orph_win_4
#print axioms orph_win_3
#print axioms orph_survivors
#print axioms orph_absent_untouched
#print axioms orph_svl_ok2
#print axioms orph_covers
#print axioms orph_s0lo
#print axioms wit_orphan_removed
#print axioms wit_orphan_present_kept
#print axioms orph_svl_ok2_core
#print axioms wit_orphan_kept_by_omission

-- The read-at-high fixture (Flink CDC).
#print axioms wit_rah_contract
#print axioms rah_win_empty
#print axioms rah_survivors
#print axioms rah_absent_untouched
#print axioms rah_svl_ok2
#print axioms rah_covers
#print axioms rah_s0lo
#print axioms wit_read_at_hi_orphan_removed
#print axioms wit_read_at_hi_present_kept

-- Composition: a key outside a contract's scope.
#print axioms CaptureContract.titems_closes_at_out
#print axioms CaptureContract.titems_emission_out
#print axioms CaptureContract.emission_out_of_scope
#print axioms CaptureContract.emission_out_of_scope_replay

-- Composition: a pass followed by a later read.
#print axioms PassThenRead.src_quiet_mid
#print axioms PassThenRead.win_last_src
#print axioms PassThenRead.pass_then_read_safe
#print axioms PassThenRead.pass_then_read_converges
#print axioms PassThenRead.pass_then_request_converges
#print axioms PassThenRead.pass_leaves_wrong_iff
#print axioms PassThenRead.request_after_pass_converges

-- Composition: the request fixture.
#print axioms rq_contract
#print axioms wit_pr_instance
#print axioms rq_win_4
#print axioms rq_survivors
#print axioms rq_absent_untouched
#print axioms rq_svl_ok2
#print axioms wit_request_completes_pass
#print axioms wit_request_after_pass

-- Redelivery: re-applying a suffix or a prefix, repetitions in place.
#print axioms replay_suffix_idempotent
#print axioms replay_block_twice
#print axioms replay_from_prefix
#print axioms repeat_block_noop
#print axioms duplicate_in_place_noop
#print axioms repeat_in_place_noop
#print axioms close_block_reapply_noop

-- Redelivery: a re-emitted absence entry.
#print axioms delete_absent_noop
#print axioms delete_absent_in_stream_noop
#print axioms absence_reemit_noop

-- Redelivery: the delivery class contains the expected streams.
#print axioms reads_from_forward
#print axioms reads_from_drop
#print axioms at_least_once_refl
#print axioms at_least_once_rewind_once
#print axioms at_least_once_restart
#print axioms at_least_once_suffix
#print axioms at_least_once_block_dup
#print axioms at_least_once_dup_in_place
#print axioms redelivered_refl
#print axioms redelivered_hop
#print axioms redelivered_block_dup
#print axioms redelivered_dup_in_place
#print axioms redelivered_suffix

-- Redelivery: every delivery replays to the same state.
#print axioms state_after_Cons
#print axioms settled_start
#print axioms settled_finish
#print axioms settled_advance
#print axioms settled_rewind
#print axioms reads_from_replay
#print axioms at_least_once_replay
#print axioms redelivered_replay

-- Redelivery: transfer of safety and convergence.
#print axioms CaptureContract.absent_replay_safe_at_least_once
#print axioms CaptureContract.self_stabilization_at_least_once

-- Redelivery: per-key delivery, filtering, partitioned topics.
#print axioms evs_for_idem
#print axioms redelivered_key_replay
#print axioms redelivered_per_key_replay
#print axioms length_filter_take_mono
#print axioms reads_from_filter
#print axioms at_least_once_filter
#print axioms redelivered_filter
#print axioms redelivered_evs_for
#print axioms partitioned_delivery_per_key
#print axioms reads_from_empty_end
#print axioms reads_from_ne
#print axioms reads_from_last
#print axioms reads_from_hd
#print axioms reads_from_nonempty
#print axioms redelivered_hd_last
#print axioms CaptureContract.absent_replay_safe_at_least_once_per_key
#print axioms CaptureContract.self_stabilization_at_least_once_per_key

-- Redelivery: the fixtures.
#print axioms wit_redelivered_orphan_removed
#print axioms wit_redelivered_present_kept
#print axioms out_of_order_redelivery_differs
#print axioms out_of_order_not_redelivered
#print axioms wit_partition_reorder_per_key
#print axioms wit_partition_reorder_replay
#print axioms wit_partitioned_delivery
#print axioms wit_rewind_parts
#print axioms wit_rewind_interleave
#print axioms wit_rewind_not_redelivered
#print axioms wit_partitioned_delivery_rewind
#print axioms wit_own_key_only
#print axioms compacted_read_not_per_key_redelivery

-- Interleaved: position-tagged lists.
#print axioms sorted_const_list
#print axioms sorted_map_fst_filter
#print axioms sorted_le_last
#print axioms blocks_sorted_gen
#print axioms blocks_sorted
#print axioms insert_at_split
#print axioms insert_at_sorted
#print axioms insert_at_Nil
#print axioms insert_at_append_le
#print axioms concat_blocks_insert_gen
#print axioms concat_blocks_insert

-- Interleaved: source values at log positions.
#print axioms take_state_quiet
#print axioms event_honest
#print axioms honest_stream_last

-- Interleaved: close entries.
#print axioms closes_at_item
#print axioms closes_at_tag
#print axioms seg_len_den
#print axioms seg_zipIdx_pos
#print axioms emission_t_sorted
#print axioms titems_emission_sorted
#print axioms CaptureContract.listed_entry_honest
#print axioms CaptureContract.unlisted_quiet_absent
#print axioms CaptureContract.contract_with_frontier

-- Interleaved: a pass and a request served inside it.
#print axioms mem_seg_pos
#print axioms mem_seg_zipIdx
#print axioms seg_zipIdx_mem
#print axioms flatMap_perm_split
#print axioms PassWithRequest.inter_t_no_request
#print axioms PassWithRequest.inter_t_mset
#print axioms PassWithRequest.inter_t_sorted
#print axioms PassWithRequest.inter_t_item_cases
#print axioms PassWithRequest.inter_item_honest
#print axioms PassWithRequest.inter_t_tag_bounds
#print axioms PassWithRequest.inter_key_complete
#print axioms PassWithRequest.titems_inter
#print axioms PassWithRequest.inter_key_replay
#print axioms PassWithRequest.pass_with_request_safe
#print axioms PassWithRequest.pass_with_request_converges
#print axioms PassWithRequest.pass_with_listing_request_converges
#print axioms PassWithRequest.pass_leaves_wrong_iff
#print axioms PassWithRequest.request_in_pass_converges

-- Interleaved: the reverse tie order and any tie order.
#print axioms PassWithRequest.inter_t_rev_set
#print axioms PassWithRequest.inter_t_rev_sorted
#print axioms PassWithRequest.inter_rev_key_replay
#print axioms PassWithRequest.inter_rev_same_replay
#print axioms PassWithRequest.s0_le_f1_of_key
#print axioms PassWithRequest.pass_with_request_safe_rev
#print axioms PassWithRequest.pass_with_request_converges_rev
#print axioms PassWithRequest.inter_any_same_replay
#print axioms PassWithRequest.pass_with_request_safe_any
#print axioms PassWithRequest.pass_with_request_converges_any

-- Interleaved: the request fixtures.
#print axioms src_4_none
#print axioms rqb_contract
#print axioms rqo_contract
#print axioms wit_pwb_instance
#print axioms wit_pwa_instance
#print axioms wit_pwo_instance
#print axioms rqb_absent_untouched
#print axioms rqb_svl_ok2
#print axioms rqo_absent_untouched
#print axioms rqo_svl_ok2
#print axioms orph_s0lo_den
#print axioms wit_stream_before_close
#print axioms wit_stream_after_close
#print axioms wit_after_close_is_composition
#print axioms wit_request_before_close
#print axioms wit_request_after_close
#print axioms rqo_overlaps_chunk
#print axioms wit_request_overlapping_chunk

-- Orphan_Absence_Tiling: the model, the scans and the passes (Tiling.lean).
#print axioms Tiling.instNonemptyChunk
#print axioms Tiling.last_eq_getLast
#print axioms Tiling.sorted_list_of_set_eq
#print axioms Tiling.sorted_list_of_set_sorted
#print axioms Tiling.mem_sorted_list_of_set
#print axioms Tiling.mem_sorted_list_of_set_imp
#print axioms Tiling.length_sorted_list_of_set
#print axioms Tiling.sorted_list_of_set_insert
#print axioms Tiling.above_lo_None
#print axioms Tiling.above_lo_Some
#print axioms Tiling.upto_hi_None
#print axioms Tiling.upto_hi_Some
#print axioms Tiling.exact_sound
#print axioms Tiling.exact_absent
#print axioms Tiling.sorted_le_last
#print axioms Tiling.sorted_take_no_skip
#print axioms Tiling.smallest_subset
#print axioms Tiling.smallest_sorted
#print axioms Tiling.smallest_length
#print axioms Tiling.smallest_upto_last
#print axioms Tiling.smallest_short
#print axioms Tiling.smallest_no_skip
#print axioms Tiling.smallest_eqI
#print axioms Tiling.page_sub
#print axioms Tiling.bpage_sub
#print axioms Tiling.exact_closed
#print axioms Tiling.exact_open_above
#print axioms Tiling.exact_bounded_closed
#print axioms Tiling.exact_closed_at_max
#print axioms Tiling.lower_le_None
#print axioms Tiling.lower_le_Some
#print axioms Tiling.above_lower_le
#print axioms Tiling.lower_le_above
#print axioms Tiling.chain_above
#print axioms Tiling.chain_rest_above
#print axioms Tiling.chain_covered
#print axioms Tiling.chain_disjoint
#print axioms Tiling.chain_consecutive
#print axioms Tiling.chain_first
#print axioms Tiling.tail_scan_pos_Nil
#print axioms Tiling.tail_scan_pos_Cons
#print axioms Tiling.page_full_ne
#print axioms Tiling.bpage_full_ne
#print axioms Tiling.page_last_above
#print axioms Tiling.bpage_last_above
#print axioms Tiling.bpage_last_le
#print axioms Tiling.page_length_le
#print axioms Tiling.bpage_length_le
#print axioms Tiling.tail_scan_chain
#print axioms Tiling.tail_scan_rest
#print axioms Tiling.tail_scan_length
#print axioms Tiling.tail_read_bound
#print axioms Tiling.tail_scan_exact
#print axioms Tiling.tail_scan_limit_last
#print axioms Tiling.tail_scan_reads
#print axioms Tiling.tail_scan_rule
#print axioms Tiling.tail_scan_completed
#print axioms Tiling.bounded_scan_chain
#print axioms Tiling.bounded_scan_rest
#print axioms Tiling.bounded_scan_length
#print axioms Tiling.bounded_read_bound
#print axioms Tiling.bounded_scan_exact
#print axioms Tiling.bounded_scan_limit_last
#print axioms Tiling.bounded_scan_no_tail_reads
#print axioms Tiling.bounded_scan_reads
#print axioms Tiling.bounded_scan_rule
#print axioms Tiling.bounded_scan_completed
#print axioms Tiling.pass_chain
#print axioms Tiling.pass_rest
#print axioms Tiling.pass_covered
#print axioms Tiling.pass_read_bound
#print axioms Tiling.pass_exact
#print axioms Tiling.chunks_le_reads
#print axioms Tiling.chunk_is_read
#print axioms Tiling.range_rule
#print axioms Tiling.completed_last_open_above
#print axioms Tiling.empty_table_single_range
#print axioms Tiling.ranges_disjoint
#print axioms Tiling.ranges_first_open_below
#print axioms Tiling.ranges_consecutive
#print axioms Tiling.ranges_no_gap
#print axioms Tiling.union_on_completion
#print axioms Tiling.union_on_limit
#print axioms Tiling.uncovered_on_limit
#print axioms Tiling.limit_frontier_last_returned
#print axioms Tiling.limit_frontier_no_tail_reads
#print axioms Tiling.union_on_limit_last_returned
#print axioms Tiling.uncovered_on_limit_last_returned
#print axioms Tiling.union_in_progress
#print axioms Tiling.range_exact
#print axioms Tiling.range_sound
#print axioms Tiling.range_absent
#print axioms Tiling.tail_scan_unlimited
#print axioms Tiling.classic_is_special_case
#print axioms Tiling.classic_special
#print axioms Tiling.classic_scan_not_limited
#print axioms Tiling.classic_not_limited
#print axioms Tiling.classic_chunks
#print axioms Tiling.classic_read_bound
#print axioms Tiling.classic_ranges_disjoint
#print axioms Tiling.classic_ranges_first_open_below
#print axioms Tiling.classic_ranges_consecutive
#print axioms Tiling.classic_union_on_completion
#print axioms Tiling.classic_union_in_progress
#print axioms Tiling.classic_range_sound
#print axioms Tiling.classic_empty_table_single_range
#print axioms Tiling.take_insort_above
#print axioms Tiling.full_page_hides_higher_keys
#print axioms Tiling.open_above_after_full_page_unsound

-- Orphan_Absence_Tiling: the fixtures (TilingWitnesses.lean).
#print axioms Tiling.terminal_rule_necessary
#print axioms Tiling.terminal_rule_page_without_13
#print axioms Tiling.terminal_rule_page_with_13
#print axioms Tiling.W1_bpage
#print axioms Tiling.W2_bpage
#print axioms Tiling.W2_page
#print axioms Tiling.wit_completed
#print axioms Tiling.wit_completed_covers
#print axioms Tiling.W3_bpage_first
#print axioms Tiling.W3_bpage_second
#print axioms Tiling.W3_page_tail
#print axioms Tiling.wit_limit
#print axioms Tiling.wit_limit_uncovered
#print axioms Tiling.wit_limit_key6

-- Orphan_Absence_Tiling: the bridge to the contract core (TilingBridge.lean).
#print axioms Tiling.pass_contract
#print axioms Tiling.completed_pass_contract
#print axioms Tiling.limited_pass_contract
#print axioms Tiling.W2_bpage_first
#print axioms Tiling.wit_bridge_pass
#print axioms Tiling.wit_bridge_contract

-- Restart: items of a pass's emission.
#print axioms emission_t_item_cases
#print axioms emission_t_tag_le
#print axioms emission_t_tag_ge
#print axioms emission_t_event_in
#print axioms CaptureContract.emission_item_honest
#print axioms CaptureContract.close_entry_in_emission
#print axioms CaptureContract.unlisted_quiet_absent_at
#print axioms evs_for_win_quiet
#print axioms filter_tag_le_sorted

-- Restart: the stream across a restart and its two parts.
#print axioms PassRestart.restart_stream_timed
#print axioms PassRestart.restart_cut_prefix
#print axioms PassRestart.cut_blocks
#print axioms PassRestart.restart_at_frontier_read_after
#print axioms PassRestart.restart_at_frontier
#print axioms PassRestart.cut_item
#print axioms PassRestart.cut_tag_le
#print axioms PassRestart.cut_sorted
#print axioms PassRestart.cut_honest
#print axioms PassRestart.cut_complete
#print axioms PassRestart.resumed_item_cases
#print axioms PassRestart.resumed_tag_ge
#print axioms PassRestart.resumed_tag_le
#print axioms PassRestart.resumed_sorted
#print axioms PassRestart.resumed_honest
#print axioms PassRestart.resumed_complete

-- Restart: safety and convergence.
#print axioms PassRestart.resumed_key_replay
#print axioms PassRestart.cut_key_replay
#print axioms PassRestart.restart_safe
#print axioms PassRestart.restart_converges
#print axioms pass_restart_after_frontier

-- Restart: the fixtures.
#print axioms wit_rx_contract
#print axioms wit_rs_instance
#print axioms rx_svl_ok2
#print axioms wit_restart_stream_orphan
#print axioms wit_restart_orphan_stays_removed
#print axioms wit_rs0_instance
#print axioms wit_restart_stream_before_close
#print axioms wit_restart_before_close_keeps_orphan
#print axioms wit_restart_before_close_second_branch
#print axioms wit_restart_before_close_cover_fails
#print axioms ri_contract
#print axioms wit_rj_contract
#print axioms wit_rt_instance
#print axioms ri_svl_ok2
#print axioms rj_svl_ok2
#print axioms wit_restart_stream_insert
#print axioms wit_restart_live_row_kept
#print axioms wit_tr1_contract
#print axioms wit_tr2_contract
#print axioms wit_rtr_instance
#print axioms tr1_svl_ok2
#print axioms tr2_svl_ok2
#print axioms wit_restart_stream_transient
#print axioms wit_transient_source
#print axioms wit_restart_transient_mid
#print axioms wit_restart_transient_end

end DBLogContract
