# DBLog Orphan Absence, version 1.0

This artifact accompanies Andreas Andreakis, *Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC Pipelines* (2026). Its Isabelle session is named `Orphan_Absence`, and its Lean 4 port `OrphanAbsence`.

The paper specifies the chunk info record, a record per chunk by which a DBLog-style incremental snapshot states which keys of a key range are absent at the source at a log position, its rendering as per-key absence events for key-partitioned outputs, a request named `verify-keys-absent` served by a bracketed key-list read, and the contract of the drift process that sends such requests. This archive contains the machine-checked session behind the paper's section "What is formally verified", together with the unchanged dependency sessions it builds on.

## Contents

| Directory or file | Purpose |
| --- | --- |
| `orphan_absence/` | The session `Orphan_Absence` (seven theories, `Orphan_Absence.thy`, `Orphan_Absence_Range_Merge.thy`, `Orphan_Absence_Composition.thy`, `Orphan_Absence_Interleaved.thy`, `Orphan_Absence_Replay.thy`, `Orphan_Absence_Tiling.thy` and `Orphan_Absence_Restart.thy`, and its `ROOT`). Additive on the Generalized DBLog contract core. |
| `lean/` | A Lean 4 port of every theory of the session except `Orphan_Absence_Range_Merge`, on an unchanged copy of the Lean port of the contract core, with its own `README.md`, `VERIFICATION.md` and `LICENSE` |
| `tla/` | Three bounded TLA+ models of the connector protocol (a core model and two extensions), checked with the TLC model checker, with their configurations, their own `README.md` and the run record `RUNS.md` |
| `dblog_framework/framework_core/` | The Generalized DBLog contract core, the session `DBLog_Framework_Core`, unchanged from the published artifact of that paper |
| `dual_write_layer0/` | Shared source-history and replay definitions needed by the sessions, unchanged |
| `formal/` | The classic DBLog development, the session `DBLog_Virtual_Cuts`, unchanged |
| `LICENSE` | BSD 3-Clause, with the retained component licenses beside each dependency |
| `SHA256SUMS` | SHA-256 checksums for every other file in the archive |

The three dependency sessions are byte-identical to the corresponding files of the published Generalized DBLog artifact (version 1.0, DOI 10.5281/zenodo.22643866). They are included so that this archive builds on its own. Their proof documents, the TLA+ development and the reproduction runner of that artifact are not repeated here, and neither are the provenance record and the original archive that the description in `dblog_framework/framework_core/ROOT` mentions, which sit at the root of that artifact. The Lean port in `lean/` carries an unchanged copy of that artifact's Lean port of the contract core, which it builds on.

## What the session proves

All statements hold inside the contract locale of the core, for a sink that applies one emitted stream in order, key by key, starting from an arbitrary initial state. The core enumerates only surviving rows, so its absence is by omission and its replay starts empty. This session widens the enumeration to absent keys and replays from any initial state. The main theorems also assume that the emitted stream is consumed from a log position at or before every unit's low watermark (premise `s0lo`), or at or before every unit's high watermark for Flink CDC's range merge (premise `s0hi`), so that the stream carries every change a window must see.

- `absent_replay_safe`: for every admissible enumeration (duplicate-free, containing every survivor, and otherwise listing only keys read as absent with no event inside the window) and every initial state, each scoped key either equals the canonical replay at the frontier or is an unlisted absent untouched key with no consumed event, whose sink value stays as it was while the source value is absent. No wrong value, no deleted live row.
- `absent_replay`, `absent_replay_cut`, `self_stabilization`: under per-key coverage, and under coverage of the whole scope, the replay from the initial state equals the source at the frontier.
- `svl2_exists_covering`, `range_record_converges`: a sink with finitely many rows admits a covering enumeration when every unit has finitely many survivors, the chunk info record as the sink applies it, and with it the replay converges on the whole scope.
- `partial_enumeration_safe`: a key the enumeration lists, or that the sink did not hold, ends equal to the source.
- `coverage_necessary`: convergence on the whole scope implies coverage, so coverage is necessary and sufficient.
- `unlisted_quiet_key_kept`: an unlisted key with no consumed event keeps its initial sink value.
- `replay_per_key`: two streams with the same events for a key replay to the same value at that key from any initial state.
- `sink_read_covers`: a complete read of the sink's keys at any consumed position before the frontier provides coverage.
- `absence_assertion_contract`: a key set observed empty at a coordinate inside a window forms a one-unit capture contract with no refresh, the tail unit.
- `late_absence_split`: a capture contract stays a contract when one unit is split into its present keys closed at the high watermark and its absent keys closed at any later position up to the frontier.
- `except_keys`, `dom_minus_except`, `record_enum`, `record_enum_ok2`, `record_enum_covers`, `chunk_record_converges`, `except_overapprox_safe`: the chunk record stated in its own terms. The paper's chunk info record carries two key lists, the selected keys the query returned and the changed keys touched inside the window, and their union is the theory's except set `except_keys`. The record's enumeration is the survivors plus the keys the sink holds in the range outside that set, that enumeration is admissible and covering, so a sink applying the records of every unit converges on the whole scope from any initial state, and an except set that over-approximates inside the range still gives a safe enumeration, a robustness result the paper does not rely on since its two lists are exact (added 2 November 2026 for the paper, reworded 5 November 2026 when the paper split its list in two).
- `wit_orphan_removed`, `wit_orphan_present_kept`, `wit_orphan_kept_by_omission`: a concrete witness in which an orphan held in the initial state is removed by the enumerated absence and kept by survivor-only emission.
- `wit_read_at_hi_orphan_removed`, `wit_read_at_hi_present_kept`: Flink CDC's read at the high watermark as a window of zero width in the same contract. The model is the window-discard one, whose stream carries every change before the read, while Flink CDC's merge withholds a chunk key's changes until the close. The theory `Orphan_Absence_Range_Merge` below checks the paper's rules for Flink CDC on the core's model of that merge.

- `Orphan_Absence_Range_Merge`, Flink CDC's buffered range merge from any initial state. The core's `Range_Merge` emits each chunk's merged image at its high watermark, holds back every scoped change below it, and proves the replay from an empty sink. This theory widens the enumeration (`rml_ok2`) to keys absent from the merged image, whose close entry is then a statement of absence, and requires every key whose held-back events end in a delete (`forced`, characterized by `forced_char`) to be listed. Those are the deletes the connector re-emits at the close. An event is held back when the gate keeps it off the stream, which starts at the consumption start, or when the window merges it into the buffer, so the held-back events start at the earlier of the two (`held_from`).
  - `rm_absent_replay_safe`: for every widened enumeration and every initial state, each scoped key either equals the canonical replay at the frontier, or is absent at the source, unlisted and without any consumed event, and keeps its initial sink value.
  - `rm_self_stabilization`, `rm_coverage_necessary`: coverage of the absent keys the sink holds and the stream never mentions is sufficient and necessary for convergence on the whole scope.
  - `rml2_exists_covering`, `range_merge_record_converges`: a sink with finitely many rows admits a covering enumeration when every unit's merged image has finitely many present keys, and with it the replay converges.
  - `rm_absent_replay_empty`: from an empty sink the widened enumeration gives the core's result.
  - `wit_pre_core_keeps_row`, `wit_inw_core_keeps_row`, `wit_pre_forced_repairs`, `wit_inw_forced_repairs`: a row in sync when the pass starts and deleted before the chunk's window, or inside it, stays in the sink under the core's enumeration and is removed once the forced key is listed.
  - `wit_inw_late_core_keeps_row`, `inw_late_core_not_ok2`, `wit_inw_late_forced_repairs`: the same holds for the delete inside the window when the stream starts at the chunk's close and never carries it, and the core's enumeration no longer satisfies the rule.
- `Orphan_Absence_Composition`, a full pass followed by a later bracketed read (a key-list request, or another pass), both applied to the sink in stream order from any initial state, inside the locale `pass_then_read` over one log.
  - `emission_out_of_scope`, `emission_out_of_scope_replay`: a key outside a contract's scope sees exactly its own log events in that contract's stream.
  - `pass_then_read_safe`: every key of either scope ends at the source state at the later frontier, or it is absent there, neither read listed it, no log event since the pass started mentions it, and the sink keeps its initial value.
  - `pass_then_read_converges`: under coverage of exactly those keys, the sink ends at the source state on both scopes.
  - `pass_leaves_wrong_iff`: the keys a pass leaves wrong are exactly the unlisted keys of its scope that the sink holds, that are absent at the frontier, and that no log event during the pass mentions.
  - `pass_then_request_converges`, `request_after_pass_converges`: a later read that lists every key it reads as absent and untouched completes the pass when every key the pass leaves wrong is in its scope, and, for a request whose scope holds every requested key that is absent where the request reads it (each batch at its own coordinate), when every key the pass leaves wrong was requested.
  - `wit_request_completes_pass`, `wit_request_after_pass`: the orphan that the survivor-only pass of the fixture leaves is removed by a later request for it, shown once by coverage and once through the request corollary.

- `Orphan_Absence_Interleaved`, a key-list request served while the pass is still running, inside the locale `pass_with_request` (the pass and the request as two contracts over one log, every unit of the request starting at or after the pass's consumption start and closing at or before the pass's frontier, with no assumption relating the request's windows to the chunk windows).
  - `inter_t`, `inter`: the pass's timed emission with the request's close blocks inserted at their own positions, every log event once; `titems_inter` characterizes one key's items.
  - `pass_with_request_safe`: every key of either scope ends at the source state at the pass's frontier, or it is absent there, listed by neither read, has no log event since the pass started, and keeps its initial sink value.
  - `pass_with_request_converges`, `pass_with_listing_request_converges`, `request_in_pass_converges`: under coverage of exactly those keys the sink converges on both scopes, and a request that lists every key it reads as absent and untouched, each batch at its own coordinate inside the pass, completes the pass whenever every key the pass leaves wrong was requested.
  - `pass_with_request_safe_rev`, `pass_with_request_converges_rev`, `inter_any_same_replay`, `pass_with_request_safe_any`, `pass_with_request_converges_any`: the same for the reverse order of blocks at equal positions and for any position-sorted stream with the same items.
  - `wit_request_before_close`, `wit_request_after_close`, `wit_request_overlapping_chunk`: the orphan of the fixture pass removed by a request served before the covering chunk closes, at the pass's frontier, and with a window overlapping the chunk's.
- `Orphan_Absence_Replay`, replay and duplicates, on the plain in-order sink.
  - `replay_suffix_idempotent`, `replay_from_prefix`, `repeat_block_noop`, `duplicate_in_place_noop`, `repeat_in_place_noop`, `close_block_reapply_noop`: re-applying any suffix of an applied stream, restarting from any prefix, and repeating a block, an event or a unit's close block in place leave the replayed state unchanged.
  - `delete_absent_noop`, `delete_absent_in_stream_noop`, `absence_reemit_noop`: a delete for a key the sink does not hold leaves the sink unchanged, wherever it lands, so a re-emitted absence entry is a no-op when the key's last event is a delete or the key was never held.
  - `reads_from`, `at_least_once`, `redelivered`: a reader with a cursor that advances or rewinds to any earlier position and stops only at the end of the stream, and finite chains of such readers (multi-hop delivery); `at_least_once_replay`, `redelivered_replay`: every such delivery replays to the state of the stream itself.
  - `absent_replay_safe_at_least_once`, `self_stabilization_at_least_once`, `absent_replay_safe_at_least_once_per_key`, `self_stabilization_at_least_once_per_key`: the safety and convergence theorems hold verbatim for every such delivery of the emission, and per key for every stream whose events for that key form such a delivery of the emission's events for that key; `partitioned_delivery_per_key`: a keyed topic with several partitions, each delivered in order at least once, yields the per-key form.
  - Fixtures: the orphan fixture delivered twice, an out-of-order delivery of one key's events outside the class, a two-partition reorder with a rewind inside one partition, and a read of a compacted topic outside the class. The stream a sink sees across one connector restart as a whole is stated in `Orphan_Absence_Restart`.
- `Orphan_Absence_Tiling`, the chunk ranges of a snapshot pass, as a standalone model with its own finite source state per read (`page`, `bpage`, `tail_scan`, `bounded_scan`, `bounded_pass`, `classic_pass`).
  - `ranges_disjoint`, `ranges_consecutive`, `ranges_first_open_below`, `range_rule`: the emitted ranges are pairwise disjoint and consecutive, the first open below, and each is a full page closed at its last key, a short page open above, or a short bounded page closed at the recorded maximum.
  - `union_on_completion`, `union_on_limit`, `union_on_limit_last_returned`, `limit_frontier_no_tail_reads`: a completed pass covers every key, a pass stopped by the tail-read limit covers exactly the keys up to the last returned key when at least one tail read is configured, and up to the recorded maximum otherwise, or no key at all when no maximum was recorded (an empty table at the start and no tail read).
  - `range_sound`, `range_absent`, `range_exact`: on a finite source state, every key in a range that the read did not return was absent at that read's cut, which is what a chunk info record states.
  - `classic_is_special_case`, `terminal_rule_necessary`, `open_above_after_full_page_unsound`, `full_page_hides_higher_keys`: the classic loop as the special case, and a counterexample that closing a full page open above certifies a present key absent.
  - `pass_contract`, `completed_pass_contract`, `limited_pass_contract`: inside `ordered_key_space`, the chunks of a pass form a capture contract of the core whose scope is every key for a completed pass, under a read coordinate inside each bracket and the read's key set equal to the source state there.
- `Orphan_Absence_Restart`, one connector restart during a window-discard pass, inside the locale `pass_restart` (the pass and the chunks re-executed after the restart as two contracts over one log, the committed offset at or before the crash, the crash at or before both frontiers, every re-executed chunk opening at or after the crash, and every chunk of the pass that closes after the crash re-read by the second contract).
  - `restart_stream`, `cut_t`, `resumed_t`: the pass's emission up to the crash (its close blocks at the positions from the consumption start to the crash and its log events before the crash), then the log segment from the committed offset to the crash a second time, without close entries, then the second contract's emission from the crash on. `restart_cut_prefix`, `cut_blocks`: the first part is a prefix of the pass's emission. `restart_at_frontier`, `restart_at_frontier_read_after`: with the commit and the crash at the pass's frontier the stream is the sequential composition of `Orphan_Absence_Composition`. `pass_restart_after_frontier`: a crash after the pass's frontier is the same locale with the crash as the frontier.
  - `restart_safe`: with the listing conditions of both contracts, the pass's units starting at or after the consumption start and the committed offset at or after it, every key of either scope ends at the source state at the second contract's frontier, or it is absent there, no close block delivered before the crash lists it, the re-executed chunks do not list it, no log event since the pass started mentions it, and the sink keeps its initial value.
  - `restart_converges`: under coverage of exactly those keys, the sink ends at the source state on both scopes.
  - Fixtures: `wit_restart_orphan_stays_removed` (an orphan removed by a close block delivered before the crash stays removed although the re-executed chunk does not list it), `wit_restart_live_row_kept` (a key inserted between that close and the crash keeps its row), `wit_restart_before_close_keeps_orphan` with `wit_restart_before_close_second_branch` and `wit_restart_before_close_cover_fails` (a crash before the close leaves the orphan in place, the second branch of the safety theorem, and coverage fails for it), and `wit_restart_stream_transient`, `wit_restart_transient_mid`, `wit_transient_source`, `wit_restart_transient_end` (while the re-delivered segment is applied the sink can hold an older value for a while; the guarantees hold at the end of the stream). A commit before the pass started, more than one restart, and a crash inside a close block are not modeled; the text argues the last in prose.

Not covered, and stated as assumptions in the paper: transport (that each key's events reach the sink in order at least once, which `Orphan_Absence_Replay` shows sufficient), the chunk query visibility assumption and the connector's rule that makes the paper's changed keys (the theory's touched keys) include transactions invisible to a read, select and span completeness (the tiling theory assumes a page returns the smallest present keys above its bound), the sink's key order and equality, the range delete at the sink (the chunk record is stated per key over the keys the sink held at the start), other writers at the sink, versions, atomicity and liveness, more than one connector restart, and a commit before the pass started.

## The Lean 4 port

The directory `lean/` proves the results of every theory except `Orphan_Absence_Range_Merge.thy` a second time, in Lean 4, so that two proof systems with different kernels check the same claims. It builds on an unchanged copy of the Lean port of the contract core from the Generalized DBLog artifact. `Orphan_Absence_Range_Merge` stays Isabelle-only, since that copy does not carry the core's range merge. The port of `Orphan_Absence_Tiling` takes a nonempty key type as an instance, which HOL supplies for every type, and no other assumption is added (`lean/VERIFICATION.md`, transport conventions). Every theorem of the port depends on at most `propext`, `Classical.choice` and `Quot.sound`, the standard axioms of Lean 4, and the port contains no `sorry` and declares no axioms. `lean/README.md` maps each Isabelle name to its Lean name and names the three helper lemmas of `Orphan_Absence.thy` the port does not need, and `lean/VERIFICATION.md` records the build, the axiom audit and the file hashes.

## The TLA+ models

The directory `tla/` holds three bounded TLA+ models of the connector protocol, checked with the TLC model checker. They give evidence, not proof. They cover what the theories leave out: the connector's operational steps, a crash at every step, the PostgreSQL visibility gap, the safety cap, the request `verify-keys-absent` with the drift process, and liveness. Every invariant is checked on all behaviors within small bounds, and each mutation of the protocol that the paper rules out produces a counterexample. `tla/README.md` describes the modules, the invariants, the mutations, the bounds and the known limitations, and `tla/RUNS.md` lists every run with its verdict and state counts.

## Requirements and reproduction

Install Isabelle2025-2. Building the dependency sessions with their proof documents also needs a working LaTeX installation. Proof checking alone does not.

From this extracted directory, with `isabelle` on PATH:

```sh
isabelle build -b -j 8 -o quick_and_dirty=false \
  -d dual_write_layer0 -d formal -d dblog_framework/framework_core -d orphan_absence \
  Orphan_Absence
```

To check the proofs without LaTeX or PDF generation:

```sh
isabelle build -b -j 8 -o quick_and_dirty=false -o document=false -o document_variants= \
  -d dual_write_layer0 -d formal -d dblog_framework/framework_core -d orphan_absence \
  Orphan_Absence
```

The expected result ends with `Finished Orphan_Absence`. The theories contain no `sorry`, no `oops` and no axiom declarations. A fresh Isabelle user directory can be forced with `env USER_HOME=<fresh directory>` on the Homebrew distribution, which ignores `ISABELLE_HOME_USER`. The dependency chain takes about four minutes on an Apple Silicon workstation.

The Lean port needs only the toolchain pinned in `lean/lean-toolchain` (`leanprover/lean4:v4.32.2`, installed through elan) and no other package. From `lean/`, `lake build` builds it and prints the axiom footprint of every theorem through its two audit modules. Once the toolchain is installed this takes a few seconds.

The TLA+ models need OpenJDK 21 and TLC 2.19 (`tla2tools.jar` from the TLA+ tools releases). From a module's folder, for example `tla/`, `java -cp tla2tools.jar tlc2.TLC -workers auto -config G7_dense_k3w3c0.cfg AbsenceConnector.tla` checks one configuration in seconds. `tla/README.md` gives the full command and the run times.

## Scope

Kernel checking establishes the formal results under their assumptions, and the TLA+ models add bounded evidence for the connector's operational steps. It does not establish that a running connector decides transaction visibility correctly, that its chunk reads are complete, that the sink evaluates key ranges in the source's order, or that records are delivered in order. The accompanying paper names each of these as an assumption.

## AI assistance

The author used Claude Fable 5.1 and Claude Opus 5.5 to assist with the Isabelle development, its Lean 4 port and the TLA+ models, and with drafting the paper's prose. The author edited all of the prose and takes responsibility for the content and the conclusions.

## License

BSD 3-Clause, as stated in `LICENSE` and the retained component licenses. The software archive does not include or assign a license to the separately submitted paper.
