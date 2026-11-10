# OrphanAbsence: a Lean 4 port of the main results of Orphan_Absence

This directory contains a second, independent mechanization of the main
results of the paper "Extending DBLog-Based Incremental Snapshots to
Handle Orphan Rows in CDC Pipelines". The primary mechanization is the
Isabelle/HOL session `Orphan_Absence`, which builds on the Generalized
DBLog contract core. This port re-proves the statements of six of the
session's seven theories, `Orphan_Absence.thy`,
`Orphan_Absence_Composition.thy`, `Orphan_Absence_Interleaved.thy`,
`Orphan_Absence_Replay.thy`, `Orphan_Absence_Tiling.thy` and
`Orphan_Absence_Restart.thy`, in Lean 4 with a minimal trust base, so
that two proof systems with different kernels check the same claims.

The port builds on the Lean 4 port of the Generalized DBLog contract core,
in the same way as the Isabelle session builds on the core session. The
directories `DBLogContract.lean` and `DBLogContract/` are an unchanged,
byte-identical copy of that port as it appears in the Generalized DBLog
artifact, version 1.0 (DOI 10.5281/zenodo.22643866). It carries the base
model of events, states, coordinates and windows, the contract, the cut
theorem and the window-discard discipline with its per-key shape lemma.
Its own scope and conventions are described in that artifact.

## Layout

| Path | Content |
| --- | --- |
| `DBLogContract.lean`, `DBLogContract/` | The unchanged copy of the core port, with its own axiom audit |
| `OrphanAbsence.lean` | The library root, which imports every module below |
| `OrphanAbsence/Emission.lean` | Admissible enumerations and the per-key shape of the widened emission |
| `OrphanAbsence/Replay.lean` | Safety, convergence, existence, partial enumerations, necessity of coverage, the sink read |
| `OrphanAbsence/ChunkRecord.lean` | The chunk record with its except set, the union of the paper's selected and changed keys |
| `OrphanAbsence/ContractUnits.lean` | The certified absence as a unit, and the split unit for late absences |
| `OrphanAbsence/Witnesses.lean` | The orphan fixture and the read-at-high fixture |
| `OrphanAbsence/Composition.lean` | A full pass followed by a later bracketed read |
| `OrphanAbsence/CompositionWitnesses.lean` | The fixture in which a request completes a pass |
| `OrphanAbsence/Interleaved.lean` | A key-list request served while the pass is still running, its close blocks inserted into the pass's stream at their own positions |
| `OrphanAbsence/InterleavedWitnesses.lean` | The fixtures in which a request served inside the pass removes the orphan |
| `OrphanAbsence/Redelivery.lean` | Re-applied suffixes and prefixes, repetitions in place, re-emitted absences, and in-order at-least-once delivery with the transfer of safety and convergence |
| `OrphanAbsence/RedeliveryWitnesses.lean` | The delivery fixtures |
| `OrphanAbsence/Tiling.lean` | The chunk ranges of a snapshot pass as a standalone model: bounds, chunks, pages, the scans and passes, and the main tiling and exactness results |
| `OrphanAbsence/TilingWitnesses.lean` | The terminal-rule counterexample and the tiling witnesses |
| `OrphanAbsence/TilingBridge.lean` | The bridge from the chunks of a pass to a capture contract of the core |
| `OrphanAbsence/Restart.lean` | One connector restart during a window-discard pass: the stream a sink sees, its safety and its convergence |
| `OrphanAbsence/RestartWitnesses.lean` | The restart fixtures |
| `OrphanAbsence/AxiomAudit.lean` | `#print axioms` for every theorem of the port |

The modules `Emission` to `Witnesses` port `Orphan_Absence.thy`. The
modules `Composition` and `CompositionWitnesses` port
`Orphan_Absence_Composition.thy`. The modules `Interleaved` and
`InterleavedWitnesses` port `Orphan_Absence_Interleaved.thy`. The modules
`Redelivery` and `RedeliveryWitnesses` port `Orphan_Absence_Replay.thy`. Their name
differs from the theory's because `Replay` already ports the replay
results of `Orphan_Absence.thy`. The modules `Tiling`, `TilingWitnesses`
and `TilingBridge` port `Orphan_Absence_Tiling.thy`, in the namespace
`DBLogContract.Tiling`. The modules `Restart` and `RestartWitnesses`
port `Orphan_Absence_Restart.thy`.

## What the port proves

All statements hold for a contract instance of the core, for a sink that
applies the emitted stream in order, key by key, starting from an
arbitrary initial state. The core enumerates only surviving rows, so its
absence is by omission and its replay starts empty. The session widens
the enumeration to keys read as absent and untouched inside the bracket,
and replays from any initial state.

- Safety (`absent_replay_safe`): for every admissible enumeration and
  every initial state, each scoped key either equals the canonical replay
  at the frontier, or it is an unlisted absent untouched key with no
  consumed event whose sink value stays as it was. No wrong value is
  produced and no live row is deleted.
- Convergence (`self_stabilization`, `coverage_necessary`): the replay
  from the initial state equals the source state at the frontier on the
  whole scope exactly when the enumeration covers every absent untouched
  key that the sink holds and that the stream never mentions.
- Existence (`svl2_exists_covering`, `range_record_converges`): a sink
  with finitely many rows, and finitely many survivors per unit, admits a
  covering enumeration, the chunk info record as the sink applies it.
- The chunk record (`record_enum_covers`, `chunk_record_converges`,
  `except_overapprox_safe`): the range with its except set (the paper's
  selected keys and changed keys together) is a covering admissible
  enumeration, and an except set that over-approximates inside the range
  stays safe.
- The sink read and the key-list read (`sink_read_covers`,
  `absence_assertion_contract`): a complete read of the sink's keys at a
  consumed position provides coverage, and a key set observed empty inside
  a bracket is a one-unit contract on its own.
- Late absences (`late_absence_split`): a contract stays a contract when
  a unit is split into its present keys, closed at the high edge, and its
  absent keys, closed at a later position up to the frontier.
- A pass followed by a later read (`pass_then_read_safe`,
  `pass_then_read_converges`): when the sink applies a full pass and then
  a later bracketed read, such as a key-list request or another pass,
  every key of either read ends at the source state, unless it is an
  orphan that neither read listed and that no change since the pass began
  mentions. Under coverage of exactly those keys the sink converges on
  both scopes.
- A request completes a pass (`pass_leaves_wrong_iff`,
  `pass_then_request_converges`, `request_after_pass_converges`): the
  keys a pass leaves wrong are exactly its unlisted orphans that no change
  during the pass mentions, and a request that lists the keys it finds
  absent and untouched completes the pass when every such key was
  requested.
- Three fixtures: an orphan held in the initial sink state is removed by
  its enumerated absence and kept by survivor-only emission, Flink CDC's
  read at the high watermark is a zero-width bracket of the same
  contract, and a request for the orphan completes the survivor-only
  pass that left it in place.
- A request served inside the pass (`pass_with_request_safe`,
  `pass_with_request_converges`, `request_in_pass_converges` and their
  variants): a key-list request may be served while the pass is still
  running, with its close blocks inserted into the pass's stream at their
  own positions. Every key of either read then ends at the source state
  at the pass's frontier, unless it is an orphan that neither read listed
  and that no change since the pass began mentions. Under coverage of
  exactly those keys the sink converges on both scopes. A request that
  lists every key it reads as absent and untouched completes the pass
  whenever every key the pass leaves wrong was requested. The same holds
  for the reverse order of blocks at equal positions and for any
  position-sorted stream with the same items. The fixtures remove the
  orphan with a request served before the covering chunk closes, at the
  pass's frontier, and with a window overlapping the chunk's.
- Delivery (`at_least_once_replay`, `redelivered_replay`,
  `absent_replay_safe_at_least_once`, `self_stabilization_at_least_once`,
  their per-key forms and `partitioned_delivery_per_key`): a reader with
  a cursor that advances or rewinds to any earlier position and stops
  only at the end of the stream replays to the state of the stream
  itself, and so does a finite chain of such readers. The safety and
  convergence theorems therefore hold for every such delivery of the
  emission. They also hold per key, for a keyed topic with several
  partitions that are each delivered in order at least once. Re-applying
  a suffix, repeating a block or an event in place, and re-emitting an
  absence entry for a key the sink does not hold change nothing. The
  fixtures deliver the orphan fixture twice and show an out-of-order
  delivery and a compacted read outside the class.
- Tiling (`ranges_disjoint`, `ranges_consecutive`, `range_rule`,
  `union_on_completion`, `union_on_limit`, `range_sound`,
  `range_absent`, `range_exact`, `pass_contract` and the related
  results): in a standalone model of pages, tail reads and passes, the
  chunk ranges a pass emits are pairwise disjoint and consecutive, the
  first open below, and each is a full page closed at its last key, a
  short page open above, or a short bounded page closed at the recorded
  maximum. A completed pass covers every key, and a pass stopped by the
  tail-read limit covers exactly the keys up to its last returned key or
  its recorded maximum. On a finite source state, every key of a range
  that the read did not return was absent at that read's cut, which is
  what a chunk info record states. The classic loop is the special case,
  closing a full page open above would certify a present key absent, and
  the chunks of a pass form a capture contract of the core.
- One restart (`restart_safe`, `restart_converges`): a connector that
  crashes during a window-discard pass and restarts from its committed
  offset delivers the pass's emission up to the crash, the log segment
  from the committed offset to the crash a second time, and the emission
  of the re-executed chunks. Every key of either contract then ends at
  the source state at the second frontier, unless it is an orphan that no
  close block before the crash and no re-executed chunk listed, and that
  no change since the pass began mentions. Under coverage of exactly
  those keys the sink converges on both scopes. With the commit and the
  crash at the pass's frontier the stream is the composition of a pass
  and a later read. The fixtures show that an orphan removed before the
  crash stays removed, that a row inserted between that close and the
  crash stays live, that a crash before the close leaves the orphan in
  place, and that the sink can hold an older value for a while as the
  segment is re-delivered.

## Correspondence

The first column paraphrases the statements of the paper's section "What
is formally verified" and the objects they rest on. Lean names in the
`CaptureContract`, `PassThenRead` and `PassWithRequest` namespaces that
take the contract, or the pair of reads, take it as their first argument
`H`, as do those in `PassRestart`, so that `H.absent_replay_safe` is the
safety theorem of the
instance `H`. All Lean names are in the namespace `DBLogContract`, and
those of `Orphan_Absence_Tiling` in `DBLogContract.Tiling`.

| Paper statement | Isabelle name | Lean name |
| --- | --- | --- |
| The sink applies the stream key by key: a replay depends on a key's own events only | `replay_per_key` | `replay_per_key` |
| Keys observed absent by the read and not changed inside the watermark window (the theory's untouched keys) | `absent_untouched` | `absent_untouched` |
| The admissible enumerations: every surviving present row, otherwise only absent untouched keys | `svl_ok2` | `svl_ok2` |
| Facts about admissible enumerations | `svl_ok_imp_ok2`, `absent_untouched_sub_dom`, `svl2_distinct`, `svl2_sub_dom`, `svl2_untouched`, `svl2_surv` | `CaptureContract.svl_ok_imp_ok2`, `absent_untouched_sub_dom`, `CaptureContract.svl2_distinct`, `CaptureContract.svl2_sub_dom`, `CaptureContract.svl2_untouched`, `CaptureContract.svl2_surv` |
| The per-key shape of the widened emission | `titems_close_block2`, `titems_closes_at2`, `titems_emission_master2` | `CaptureContract.titems_close_block2`, `CaptureContract.titems_closes_at2`, `CaptureContract.titems_emission_master2` |
| Safety: no incorrect value, no deleted live row, an unlisted absent key the stream never mentions keeps its value | `absent_replay_safe` | `CaptureContract.absent_replay_safe` |
| Convergence of one key under per-key coverage | `absent_replay`, `absent_replay_cut` | `CaptureContract.absent_replay`, `CaptureContract.absent_replay_cut` |
| Coverage of every absent key held by the sink that the stream never mentions | `covers` | `covers` |
| Convergence, the sufficient direction: a covering pass brings a sink from any prior state into sync | `self_stabilization` | `CaptureContract.self_stabilization` |
| Convergence, the necessary direction: an uncovered orphan fails to converge | `unlisted_quiet_key_kept`, `coverage_necessary` | `CaptureContract.unlisted_quiet_key_kept`, `CaptureContract.coverage_necessary` |
| Candidates from an external or partial list | `partial_enumeration_safe` | `CaptureContract.partial_enumeration_safe` |
| A finite sink state, with finitely many survivors per unit, admits a covering enumeration, the chunk info record as the sink applies it | `svl2_exists_covering`, `range_record_converges` | `CaptureContract.svl2_exists_covering`, `CaptureContract.range_record_converges` |
| The chunk record's range with its selected and changed keys, evaluated per key over the keys the sink holds (the except set is their union) | `except_keys`, `dom_minus_except`, `record_enum`, `record_enum_ok2`, `record_enum_covers`, `chunk_record_converges` | `except_keys`, `dom_minus_except`, `record_enum`, `CaptureContract.record_enum_ok2`, `CaptureContract.record_enum_covers`, `CaptureContract.chunk_record_converges` |
| An except set that over-approximates the exact one stays safe, a robustness result the paper does not rely on | `except_overapprox_safe` | `CaptureContract.except_overapprox_safe` |
| A complete snapshot of the sink's keys at a consumed position suffices for coverage | `sink_read_covers` | `CaptureContract.sink_read_covers` |
| A key set observed empty inside a watermark window is a sound statement of absence on its own | `absence_assertion_contract` | `absence_assertion_contract` |
| Rows at the high watermark, absences at a later position (stated in the session, used by the design) | `late_absence_split` | `late_absence_split` |
| Witness: an orphan in the initial sink state is removed by its enumerated absence and kept by survivor-only emission | `orph_unit`, `D0_o`, interpretation `orph`, `wit_orphan_removed`, `wit_orphan_present_kept`, `wit_orphan_kept_by_omission` | `orph_unit`, `D0_o`, `wit_orph_contract`, `wit_orphan_removed`, `wit_orphan_present_kept`, `wit_orphan_kept_by_omission` |
| Witness: Flink CDC's read at the high watermark as a zero-width window | `rah_unit`, interpretation `rah`, `wit_read_at_hi_orphan_removed`, `wit_read_at_hi_present_kept` | `rah_unit`, `wit_rah_contract`, `wit_read_at_hi_orphan_removed`, `wit_read_at_hi_present_kept` |
| A key outside a read's scope sees only its own log events in that read's stream | `titems_closes_at_out`, `titems_emission_out`, `emission_out_of_scope`, `emission_out_of_scope_replay` | `CaptureContract.titems_closes_at_out`, `CaptureContract.titems_emission_out`, `CaptureContract.emission_out_of_scope`, `CaptureContract.emission_out_of_scope_replay` |
| A full pass composed with a later bracketed read, both applied to the sink in stream order | locale `pass_then_read`, `composed` | structure `PassThenRead`, `composed` |
| Every key of either read ends at the source state, unless it is an orphan that neither read listed and that no change since the pass began mentions | `pass_then_read_safe`, with `src_quiet_mid` and `win_last_src` | `PassThenRead.pass_then_read_safe`, with `PassThenRead.src_quiet_mid` and `PassThenRead.win_last_src` |
| Under coverage of exactly those orphans, the sink converges on both scopes | `pass_then_read_converges` | `PassThenRead.pass_then_read_converges` |
| The keys a pass leaves wrong are its unlisted orphans that no change during the pass mentions | `pass_leaves_wrong_iff` | `PassThenRead.pass_leaves_wrong_iff` |
| A request that lists the keys it finds absent and not changed in its window completes the pass whenever every key the pass left wrong was requested | `pass_then_request_converges`, `request_after_pass_converges` | `PassThenRead.pass_then_request_converges`, `PassThenRead.request_after_pass_converges` |
| Witness: a request completes a pass that left an orphan | `rq_unit`, `rq_contract` with interpretation `rq`, interpretation `pr`, `wit_request_completes_pass`, `wit_request_after_pass` | `rq_unit`, `rq_contract`, `wit_pr_instance`, `wit_request_completes_pass`, `wit_request_after_pass` |

The fixtures' supporting lemmas keep their Isabelle names: `orph_win_3`,
`orph_win_4`, `orph_survivors`, `orph_absent_untouched`, `orph_svl_ok2`,
`orph_covers`, `orph_s0lo`, `orph_svl_ok2_core`, `rah_win_empty`,
`rah_survivors`, `rah_absent_untouched`, `rah_svl_ok2`, `rah_covers`,
`rah_s0lo`, `rq_win_4`, `rq_survivors`, `rq_absent_untouched` and
`rq_svl_ok2`.

### `Orphan_Absence_Interleaved`

The first column paraphrases the deposit README's statement of the
theory. Every declaration keeps its Isabelle name. The locale's
theorems are in the namespace `PassWithRequest`. The locale's lemmas that
use none of its assumptions are there too, stated without the argument
`H`.

| Statement | Isabelle names | Lean names |
| --- | --- | --- |
| Position-tagged lists: sorted tags, blocks, and a block inserted at its own position | `sorted_const_list`, `sorted_map_fst_filter`, `sorted_le_last`, `blocks_sorted`, `insert_at`, `insert_at_split`, `insert_at_sorted`, `insert_at_Nil`, `concat_blocks_insert` | the same names, with the port-local `blocks_sorted_gen`, `insert_at_append_le` and `concat_blocks_insert_gen` |
| Source values at log positions | `take_state_quiet`, `event_honest`, `honest_stream_last` | the same names |
| Close entries: their tags, and the value they carry | `closes_at_item`, `closes_at_tag`, `emission_t_sorted`, `titems_emission_sorted` | the same names |
| Close entries under the contract | `listed_entry_honest`, `unlisted_quiet_absent`, `contract_with_frontier` | the same names in the namespace `CaptureContract` |
| A pass and a request served inside it, over one log, and the stream with the request's close blocks inserted at their own positions | locale `pass_with_request`, `inter_t`, `inter` | structure `PassWithRequest`, `inter_t`, `inter` |
| Facts about the interleaved stream, and the items of one key in it | `inter_t_no_request`, `inter_t_mset`, `inter_t_sorted`, `inter_t_item_cases`, `inter_item_honest`, `inter_t_tag_bounds`, `inter_key_complete`, `titems_inter`, `inter_key_replay` | the same names in the namespace `PassWithRequest`, with the port-local `seg_len_den`, `seg_zipIdx_pos`, `mem_seg_pos`, `mem_seg_zipIdx`, `seg_zipIdx_mem` and `flatMap_perm_split` |
| Safety: every key of either scope ends at the source state at the pass's frontier, or it is an orphan that neither read listed and that no change since the pass began mentions | `pass_with_request_safe` | the same names in the namespace `PassWithRequest` |
| Convergence under coverage, and a request that lists every key it reads as absent and untouched completes the pass whenever every key the pass leaves wrong was requested | `pass_with_request_converges`, `pass_with_listing_request_converges`, `pass_leaves_wrong_iff`, `request_in_pass_converges` | the same names in the namespace `PassWithRequest` |
| The stream with the request's blocks first at equal positions | `inter_t_rev`, `inter_rev` | the same names |
| The same results for that order, and for any position-sorted stream with the same items | `inter_t_rev_set`, `inter_t_rev_sorted`, `inter_rev_key_replay`, `inter_rev_same_replay`, `s0_le_f1_of_key`, `pass_with_request_safe_rev`, `pass_with_request_converges_rev`, `inter_any_same_replay`, `pass_with_request_safe_any`, `pass_with_request_converges_any` | the same names in the namespace `PassWithRequest` |
| Witnesses: the orphan of the fixture pass removed by a request served before the covering chunk closes, at the pass's frontier, and with a window overlapping the chunk's | `rqb_unit`, `rqo_unit`, `src_4_none`, `rqb_contract` with interpretation `rqb`, `rqo_contract` with interpretation `rqo`, interpretations `pwb`, `pwa` and `pwo`, `rqb_absent_untouched`, `rqb_svl_ok2`, `rqo_absent_untouched`, `rqo_svl_ok2`, `orph_s0lo_den`, `wit_stream_before_close`, `wit_stream_after_close`, `wit_after_close_is_composition`, `wit_request_before_close`, `wit_request_after_close`, `rqo_overlaps_chunk`, `wit_request_overlapping_chunk` | `rqb_unit`, `rqo_unit`, `src_4_none`, `rqb_contract`, `rqo_contract`, `wit_pwb_instance`, `wit_pwa_instance`, `wit_pwo_instance`, `rqb_absent_untouched`, `rqb_svl_ok2`, `rqo_absent_untouched`, `rqo_svl_ok2`, `orph_s0lo_den`, `wit_stream_before_close`, `wit_stream_after_close`, `wit_after_close_is_composition`, `wit_request_before_close`, `wit_request_after_close`, `rqo_overlaps_chunk`, `wit_request_overlapping_chunk` |

### `Orphan_Absence_Replay`

The first column paraphrases the deposit README's statement of the
theory. Every declaration keeps its Isabelle name. The four theorems of
the theory's `capture_contract` context are in the namespace
`CaptureContract` and take the contract `H`.

| Statement | Isabelle names | Lean names |
| --- | --- | --- |
| Re-applying any suffix of an applied stream, restarting from any prefix, and repeating a block, an event or a unit's close block in place leave the replayed state unchanged | `replay_suffix_idempotent`, `replay_block_twice`, `replay_from_prefix`, `repeat_block_noop`, `duplicate_in_place_noop`, `repeat_in_place_noop`, `close_block_reapply_noop` | the same names |
| A delete for a key the sink does not hold changes nothing, wherever it lands, so a re-emitted absence entry is a no-op | `delete_absent_noop`, `delete_absent_in_stream_noop`, `absence_reemit_noop` | the same names |
| A reader with a cursor that advances or rewinds and stops only at the end of the stream, and finite chains of such readers | inductive `reads_from`, `at_least_once`, `redelivered` | inductive `reads_from`, `at_least_once`, `redelivered`, with the port-local inductive `rtranclp` |
| The delivery classes contain the expected streams | `reads_from_forward`, `reads_from_drop`, `at_least_once_refl`, `at_least_once_rewind_once`, `at_least_once_restart`, `at_least_once_suffix`, `at_least_once_block_dup`, `at_least_once_dup_in_place`, `redelivered_refl`, `redelivered_hop`, `redelivered_block_dup`, `redelivered_dup_in_place`, `redelivered_suffix` | the same names |
| Every such delivery replays to the state of the stream itself | `settled`, `state_after_Cons`, `settled_start`, `settled_finish`, `settled_advance`, `settled_rewind`, `reads_from_replay`, `at_least_once_replay`, `redelivered_replay` | the same names |
| The safety and convergence theorems hold for every such delivery of the emission | `absent_replay_safe_at_least_once`, `self_stabilization_at_least_once` | `CaptureContract.absent_replay_safe_at_least_once`, `CaptureContract.self_stabilization_at_least_once` |
| Per-key delivery: a stream whose events for a key form such a delivery of the emission's events for that key, and a keyed topic with several partitions | `evs_for_idem`, `redelivered_key_replay`, `redelivered_per_key_replay`, `length_filter_take_mono`, `reads_from_filter`, `at_least_once_filter`, `redelivered_filter`, `redelivered_evs_for`, `partitioned_delivery_per_key`, `reads_from_empty_end`, `reads_from_last`, `reads_from_hd`, `reads_from_nonempty`, `redelivered_hd_last` | the same names, with the port-local `reads_from_ne` |
| The safety and convergence theorems per key | `absent_replay_safe_at_least_once_per_key`, `self_stabilization_at_least_once_per_key` | `CaptureContract.absent_replay_safe_at_least_once_per_key`, `CaptureContract.self_stabilization_at_least_once_per_key` |
| Witnesses: the orphan fixture delivered twice, an out-of-order delivery outside the class, a two-partition reorder with a rewind inside one partition, and a compacted read outside the class | `wit_redelivered_orphan_removed`, `wit_redelivered_present_kept`, `out_of_order_redelivery_differs`, `out_of_order_not_redelivered`, `wit_partition_reorder_per_key`, `wit_partition_reorder_replay`, `wit_partitioned_delivery`, `rw_E`, `rw_part`, `rw_T`, `rw_S`, `wit_rewind_parts`, `wit_rewind_interleave`, `wit_rewind_not_redelivered`, `wit_partitioned_delivery_rewind`, `wit_own_key_only`, `compacted_read_not_per_key_redelivery` | the same names |

### `Orphan_Absence_Tiling`

The first column paraphrases the deposit README's statement of the
theory. Every declaration keeps its Isabelle name, in the namespace
`DBLogContract.Tiling`. The rows follow the theory's subsections.

| Statement | Isabelle names | Lean names |
| --- | --- | --- |
| Bounds, ranges and chunks: open or bounded ends, the keys of a chunk's range, the keys a list of chunks covers, and a chunk exact for a source state | `above_lo`, `upto_hi`, `above_lo_None`, `above_lo_Some`, `upto_hi_None`, `upto_hi_Some`, `chunk_keys`, `covered`, `chunk_exact`, `exact_sound`, `exact_absent` | the same names in the namespace `Tiling` |
| The chunk as the connector records it | record `chunk` | structure `Tiling.Chunk`, with the fields `c_lo`, `c_hi` and `c_rows` |
| Pages: the n smallest keys of a set, for a plain and a bounded chunk query | `smallest`, `page`, `bpage`, `sorted_le_last`, `sorted_take_no_skip`, `smallest_subset`, `smallest_sorted`, `smallest_length`, `smallest_upto_last`, `smallest_short`, `smallest_no_skip`, `smallest_eqI`, `page_sub`, `bpage_sub` | the same names in the namespace `Tiling`, with the port-local `Tiling.sorted_list_of_set`, `Tiling.card`, `Tiling.finite`, `Tiling.last` and `Tiling.last_eq_getLast` |
| Each of the four chunk kinds is exact for its read | `exact_closed`, `exact_open_above`, `exact_bounded_closed`, `exact_closed_at_max` | the same names in the namespace `Tiling` |
| Chains of ranges tile their span: covered, disjoint, consecutive, the first open below | `lower_le`, `lower_le_None`, `lower_le_Some`, `above_lower_le`, `lower_le_above`, `ranges_chain`, `chain_rest`, `chain_above`, `chain_rest_above`, `chain_covered`, `chain_disjoint`, `chain_consecutive`, `chain_first` | the same names in the namespace `Tiling` |
| The pass: the bounded main loop, the tail reads, the classic loop, and what a pass leaves uncovered | `uncovered`, `tail_scan`, `bounded_scan`, `bounded_pass`, `classic_scan`, `classic_pass` | the same names in the namespace `Tiling` |
| How a pass ends | datatype `pass_status` | inductive type `Tiling.PassStatus`, with the constructors `Completed`, `Tail_Limit` and `Running` |
| The tail reads emit an exact chain | `tail_scan_pos_Nil`, `tail_scan_pos_Cons`, `page_full_ne`, `bpage_full_ne`, `page_last_above`, `bpage_last_above`, `bpage_last_le`, `page_length_le`, `bpage_length_le`, `tail_scan_chain`, `tail_scan_rest`, `tail_scan_length`, `tail_scan_exact`, `tail_scan_limit_last`, `tail_scan_reads`, `tail_scan_rule`, `tail_scan_completed` | the same names in the namespace `Tiling`, with the port-local `Tiling.tail_read_bound` |
| The bounded main loop emits an exact chain | `bounded_scan_chain`, `bounded_scan_rest`, `bounded_scan_length`, `bounded_scan_exact`, `bounded_scan_limit_last`, `bounded_scan_no_tail_reads`, `bounded_scan_reads`, `bounded_scan_rule`, `bounded_scan_completed` | the same names in the namespace `Tiling`, with the port-local `Tiling.bounded_read_bound` |
| Pass-level facts | `pass_chain`, `pass_rest`, `pass_covered`, `pass_exact` | the same names in the namespace `Tiling`, with the port-local `Tiling.pass_read_bound` |
| Main results: the ranges are disjoint and consecutive, the first open below, each follows the range rule, a completed pass covers every key, a limited pass covers exactly the keys up to its frontier, and every key of a range that the read did not return was absent at the read's cut | `chunks_le_reads`, `chunk_is_read`, `range_rule`, `completed_last_open_above`, `empty_table_single_range`, `ranges_disjoint`, `ranges_first_open_below`, `ranges_consecutive`, `ranges_no_gap`, `union_on_completion`, `union_on_limit`, `uncovered_on_limit`, `limit_frontier_last_returned`, `limit_frontier_no_tail_reads`, `union_on_limit_last_returned`, `uncovered_on_limit_last_returned`, `union_in_progress`, `range_exact`, `range_sound`, `range_absent` | the same names in the namespace `Tiling` |
| The classic loop as the special case | `tail_scan_unlimited`, `classic_is_special_case`, `classic_special`, `classic_scan_not_limited`, `classic_not_limited`, `classic_chunks`, `classic_ranges_disjoint`, `classic_ranges_first_open_below`, `classic_ranges_consecutive`, `classic_union_on_completion`, `classic_union_in_progress`, `classic_range_sound`, `classic_empty_table_single_range` | the same names in the namespace `Tiling`, with the port-local `Tiling.classic_read_bound` |
| The terminal rule is necessary: closing a full page open above would certify a present key absent | `take_insort_above`, `full_page_hides_higher_keys`, `open_above_after_full_page_unsound`, `terminal_rule_necessary`, `terminal_rule_page_without_13`, `terminal_rule_page_with_13` | the same names in the namespace `Tiling`, with the port-local `Tiling.insort` |
| Witnesses: the general statements are not vacuous | `W1`, `W2`, `wit_reads`, `W1_bpage`, `W2_bpage`, `W2_page`, `wit_completed`, `wit_completed_covers`, `W3`, `wit_reads_limit`, `W3_bpage_first`, `W3_bpage_second`, `W3_page_tail`, `wit_limit`, `wit_limit_uncovered`, `wit_limit_key6` | the same names in the namespace `Tiling` |
| Bridge: the chunks of a pass as the units of a capture contract of the core, whose scope is every key for a completed pass | `pass_units`, `pass_contract`, `completed_pass_contract`, `limited_pass_contract`, `wit_source`, `W2_bpage_first`, `wit_bridge_pass`, `wit_bridge_contract` | the same names in the namespace `Tiling` |
| The ordered key space of the bridge, and its witness | locale `ordered_key_space`, interpretation `wit_space` | the coordinate-space argument and the class `Tiling.Linorder` of the bridge theorems, and the definition `Tiling.wit_space` |

### `Orphan_Absence_Restart`

The first column paraphrases the deposit README's statement of the
theory. Every declaration keeps its Isabelle name. The locale's lemmas
are in the namespace `PassRestart`, those that use none of its
assumptions stated without the argument `H`.

| Statement | Isabelle names | Lean names |
| --- | --- | --- |
| Items of a pass's emission: their cases, tags and positions | `emission_t_item_cases`, `emission_t_tag_le`, `emission_t_tag_ge`, `emission_t_event_in`, `evs_for_win_quiet`, `filter_tag_le_sorted` | the same names |
| The value an emission item carries, and the absence of an unlisted quiet key | `emission_item_honest`, `close_entry_in_emission`, `unlisted_quiet_absent_at` | the same names in the namespace `CaptureContract` |
| A pass interrupted by a crash and its restart, over one log, and the stream a sink sees | locale `pass_restart`, `restart_stream`, `cut_t`, `resumed_t` | structure `PassRestart`, `restart_stream`, `cut_t`, `resumed_t` |
| The parts of the stream: the pass's emission cut at the crash, the re-delivered segment and the second contract's emission, and the composition when the crash is at the frontier | `restart_stream_timed`, `restart_cut_prefix`, `cut_blocks`, `restart_at_frontier_read_after`, `restart_at_frontier`, `cut_item`, `cut_tag_le`, `cut_sorted`, `cut_honest`, `cut_complete`, `resumed_item_cases`, `resumed_tag_ge`, `resumed_tag_le`, `resumed_sorted`, `resumed_honest`, `resumed_complete`, `resumed_key_replay`, `cut_key_replay` | the same names in the namespace `PassRestart` |
| Safety and convergence across one restart | `restart_safe`, `restart_converges` | the same names in the namespace `PassRestart` |
| A crash after the pass's frontier is the same locale with the crash as the frontier | `pass_restart_after_frontier` | the same names |
| Witnesses: an orphan removed by a close block before the crash stays removed, a key inserted between that close and the crash keeps its row, and a crash before the close leaves the orphan in place | `rx_unit`, interpretation `rx`, interpretation `rs`, `rx_svl_ok2`, `wit_restart_stream_orphan`, `wit_restart_orphan_stays_removed`, interpretation `rs0`, `wit_restart_stream_before_close`, `wit_restart_before_close_keeps_orphan`, `wit_restart_before_close_second_branch`, `wit_restart_before_close_cover_fails`, `ri_unit`, `rj_unit`, `D0_r`, `ri_contract` with interpretation `ri`, interpretations `rj` and `rt`, `ri_svl_ok2`, `rj_svl_ok2`, `wit_restart_stream_insert`, `wit_restart_live_row_kept` | `rx_unit`, `wit_rx_contract`, `wit_rs_instance`, `rx_svl_ok2`, `wit_restart_stream_orphan`, `wit_restart_orphan_stays_removed`, `wit_rs0_instance`, `wit_restart_stream_before_close`, `wit_restart_before_close_keeps_orphan`, `wit_restart_before_close_second_branch`, `wit_restart_before_close_cover_fails`, `ri_unit`, `rj_unit`, `D0_r`, `ri_contract`, `wit_rj_contract`, `wit_rt_instance`, `ri_svl_ok2`, `rj_svl_ok2`, `wit_restart_stream_insert`, `wit_restart_live_row_kept` |
| Witness: while the segment is re-delivered the sink can hold an older value for a while, and the guarantees hold at the end of the stream | `L_t`, `den_t`, interpretation `tc`, `tr_unit`, interpretations `tr1`, `tr2` and `rtr`, `tr1_svl_ok2`, `tr2_svl_ok2`, `wit_restart_stream_transient`, `wit_transient_source`, `wit_restart_transient_mid`, `wit_restart_transient_end` | `L_t`, `den_t`, `tc`, `tr_unit`, `wit_tr1_contract`, `wit_tr2_contract`, `wit_rtr_instance`, `tr1_svl_ok2`, `tr2_svl_ok2`, `wit_restart_stream_transient`, `wit_transient_source`, `wit_restart_transient_mid`, `wit_restart_transient_end` |

## Scope

The port covers every definition, lemma, theorem and interpretation of
`Orphan_Absence.thy` except three: `split_index_subset`,
`split_index_ne` and `split_index_bound`. These are list-index lemmas
that the Isabelle proof of `late_absence_split` uses to map family
positions. The Lean proof of the same statement reads the positional
disjointness of the contract as pairwise disjointness along the list
(`O1_disjoint_iff_pairwise`), so the three lemmas have no use here. They
state nothing about the model.

The port covers every declaration of `Orphan_Absence_Composition.thy`.
The locale `pass_then_read` is the structure `PassThenRead`, the
interpretation `pr` is the theorem `wit_pr_instance`, and the lemma
`rq_contract` and the interpretation `rq` built from it are the one
theorem `rq_contract`.

The port covers every declaration of `Orphan_Absence_Interleaved.thy`.
The locale `pass_with_request` is the structure `PassWithRequest`. The
lemmas `rqb_contract` and `rqo_contract`, with the interpretations `rqb`
and `rqo` built from them, are the theorems `rqb_contract` and
`rqo_contract`. The interpretations `pwb`, `pwa` and `pwo` are the
theorems `wit_pwb_instance`, `wit_pwa_instance` and `wit_pwo_instance`.

The port covers every declaration of `Orphan_Absence_Replay.thy`.

The port covers every declaration of `Orphan_Absence_Tiling.thy`. The
record `chunk` is the structure `Tiling.Chunk`, and the datatype
`pass_status` is the inductive type `Tiling.PassStatus`. The locale
`ordered_key_space` adds nothing to a coordinate space but the order on
keys, so it has no declaration of its own: its theorems take the
coordinate space and the class `Tiling.Linorder`. Its interpretation
`wit_space` is the definition `Tiling.wit_space`.

The port covers every declaration of `Orphan_Absence_Restart.thy`. The
locale `pass_restart` is the structure `PassRestart`. The lemma
`ri_contract` and the interpretation `ri` built from it are the one
theorem `ri_contract`. The interpretations `rx`, `rj`, `tr1` and `tr2` of
`capture_contract` are the theorems `wit_rx_contract`, `wit_rj_contract`,
`wit_tr1_contract` and `wit_tr2_contract`, the interpretations `rs`,
`rs0`, `rt` and `rtr` of `pass_restart` are the theorems
`wit_rs_instance`, `wit_rs0_instance`, `wit_rt_instance` and
`wit_rtr_instance`, and the interpretation `tc` of `coordinate_space` is
the definition `tc`.

Port-local helpers that have no Isabelle counterpart are marked as such
in their docstrings: `survivors_sub_dom` (a core lemma of the Isabelle
`Merge_Disciplines.thy` that the Lean core does not carry),
`evs_emission_master2` (the plain-stream reading of the master lemma,
which the Isabelle proofs perform inline), `exists_nodup_listing`,
`O1_disjoint_iff_pairwise`, the inductive `rtranclp` (HOL's reflexive
transitive closure with its two introduction rules, which Lean's core
library does not provide) and `reads_from_ne` (the fact
`reads_from_nonempty`, proved before `reads_from_last` and
`reads_from_hd` so that their statements can use it). The port of
`Orphan_Absence_Interleaved.thy` adds `blocks_sorted_gen`,
`insert_at_append_le` and `concat_blocks_insert_gen` (general forms of
the theory's block lemmas, over any list whose positions form the
range), the segment lemmas `seg_len_den`, `seg_zipIdx_pos`,
`mem_seg_pos`, `mem_seg_zipIdx` and `seg_zipIdx_mem`, which relate the
`zipIdx` traversal of the consumed log segment to the theory's position
ranges, and `flatMap_perm_split`, the multiset split that the Isabelle
proof of `inter_t_mset` states inline. The port of
`Orphan_Absence_Tiling.thy` adds the HOL library notions that Lean's core
library lacks, with HOL's values: the class `Tiling.Linorder`,
`Tiling.finite`, `Tiling.card`, `Tiling.sorted_list_of_set`,
`Tiling.last`, `Tiling.insort`, the instances `Linorder Nat` and
`Nonempty (Chunk K)`, and the facts `Tiling.last_eq_getLast`,
`Tiling.sorted_list_of_set_eq`, `Tiling.sorted_list_of_set_sorted`,
`Tiling.mem_sorted_list_of_set`, `Tiling.mem_sorted_list_of_set_imp`,
`Tiling.length_sorted_list_of_set` and
`Tiling.sorted_list_of_set_insert`. It also adds the bound lemmas
`Tiling.tail_read_bound`, `Tiling.bounded_read_bound`,
`Tiling.pass_read_bound` and `Tiling.classic_read_bound`, which supply
the index bounds behind the Isabelle `Ss ! i`.

`Orphan_Absence_Range_Merge` stays Isabelle-only. It states the results
for Flink CDC's buffered range merge, and it builds on the core's
`Range_Merge.thy`, which the Lean core port does not carry either. The
read-at-high fixture here uses the window-discard model, as the Isabelle
fixture in `Orphan_Absence.thy` does. `VERIFICATION.md` records the exact versions of the
theories this port follows.

## Building

The project depends only on the Lean core toolchain library. It uses no
external packages, so `lake build` performs no downloads once the
toolchain is installed. With elan present, run:

    lake build

The pinned toolchain is `leanprover/lean4:v4.32.2`, recorded in
`lean-toolchain`. The build elaborates the core copy and the port and
prints the axiom footprint of every theorem through two audit modules,
`DBLogContract/AxiomAudit.lean` for the core (87 theorems) and
`OrphanAbsence/AxiomAudit.lean` for the port (388 theorems). Every
theorem depends on at most `propext`, `Classical.choice` and
`Quot.sound`, the three standard axioms of the Lean 4 core logic. The
development contains no `sorry` and declares no axioms of its own.
`VERIFICATION.md` records the build, the audit results, line counts and
file hashes.

## Design notes

The Isabelle development is the source of truth. The port re-proves the
same statements over the same representation and follows the
conventions of the core port.

- Sets of keys are predicates, so membership is function application,
  unions are disjunctions, and set equalities and inclusions are stated
  pointwise.
- The logic is classical, exactly as in Isabelle/HOL. Definitions are
  noncomputable, and the concrete evaluations in the fixtures are proved
  by rewriting rather than by execution.
- HOL's `finite A` holds exactly when `A` is the set of some list, so
  the finiteness assumptions of `svl2_exists_covering` and
  `range_record_converges` are stated as listings `∃ xs, ∀ k, k ∈ xs ↔ A k`.
- The locale parameters of the Isabelle statements are explicit
  arguments. The emission of the Isabelle `emission svl s0` is
  `emission S units f svl s0`, and the canonical replay `sink_at f k`
  is `sink_at S units f f k`.
- The locale `pass_then_read` is the `Prop`-valued structure
  `PassThenRead`, whose fields are the two contracts `P` and `R` and the
  locale's two assumptions, in the way the core port turns the locale
  `capture_contract` into `CaptureContract`.
- A lemma that the Isabelle session states inside a locale but that uses
  none of the locale's assumptions is stated without the locale
  argument. This only drops an unused assumption.
- Lean's core library has no multisets. A multiset equality
  `mset xs = mset ys + mset zs` is the permutation `xs.Perm (ys ++ zs)`,
  which states the same claim.
- A type of sort `linorder` carries `[LE α] [Std.IsLinearOrder α]`, the
  core library's class for a reflexive, transitive, antisymmetric and
  total `≤`, which is all that these statements use. A position range
  `[a..<b]` is `List.range' a (b - a)`, and `concat (map f xs)` is
  `xs.flatMap f`.
- HOL's junk-total `L ! p` is the bounded `S.log[p]`, with the bound
  taken from the statement's own assumptions. Where an assumption
  quantifies over positions, the Lean assumption covers the positions
  inside the log only. This makes `take_state_quiet` and
  `honest_stream_last` stronger than their Isabelle statements.
- The standalone tiling model carries its own class `Tiling.Linorder`,
  with exactly the five axioms of HOL's `linorder` (`order_refl`,
  `order_trans`, `antisym`, `linear` and `less_le_not_le`), since its
  statements use `<` as well as `≤`. HOL's `finite`, `card`,
  `sorted_list_of_set`, `last` and `insort` are port-local definitions
  with HOL's values on every input, `[]` and `0` on an infinite set
  included.
- HOL's `last` is total, and the scans of the tiling model store
  `Some (last [])` when the page size is 0. A Lean definition with the
  same value needs an element of the key type, so the scans and every
  theorem about them take `[Nonempty K]`. Every HOL type is nonempty, so
  these theorems cover exactly the key types the Isabelle ones do. This
  instance is the one assumption of the port that the Isabelle text does
  not show.
- HOL's `suffix` and `prefix` are Lean's `<:+` and `<+:`, which state
  the same existentials. HOL's `rtranclp` is a port-local inductive with
  the same two rules. A filter predicate of type `'a ⇒ bool` is a Lean
  function to `Bool`.
- HOL's total `hd`, `last` and `xs ! 0` are `head`, `getLast` and bounded
  `getElem` with their nonemptiness proofs. Where the Isabelle guards
  them by an assumption, the Lean statement derives the proof from that
  assumption (`reads_from_last`, `reads_from_hd`), or makes the
  nonemptiness the witness of a dependent conjunction
  (`redelivered_hd_last`, `absence_reemit_noop`).
- The Isabelle interpretations `orph`, `rah` and `pr` become the
  theorems `wit_orph_contract`, `wit_rah_contract` and
  `wit_pr_instance`, which state that the fixtures satisfy the contract
  or the pass and read pair.

## License

BSD 3-Clause, the same license as the Isabelle development and the core
port. See `LICENSE`.
