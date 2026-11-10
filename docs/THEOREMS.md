# Result index

This file maps the guarantees stated in Section 8, "What is formally
verified", of the paper "Extending DBLog-Based Incremental Snapshots to Handle
Orphan Rows in CDC Pipelines" to the Isabelle/HOL theories and theorem names
that prove them.

The paper states its guarantees in prose and does not number them. The tables
below were compiled from [formal/README.md](../formal/README.md), which is part
of the archived artifact and describes every statement listed here. Each
Isabelle name listed here is a declared theorem, lemma or corollary in the
named theory file.

The descriptions below are short labels that omit assumptions. They are not
formal statements. For citation or technical comparison, read Section 8 in
`paper/main.tex` and the Isabelle statements themselves, which are
authoritative.

Theory files are in [formal/orphan_absence/](../formal/orphan_absence/). The
column "Lean" says whether the Lean 4 port in
[formal/lean/](../formal/lean/) also proves the theory's results.
[formal/lean/README.md](../formal/lean/README.md) maps each Isabelle name to
its Lean name.

## Safety: no false deletes or wrong values

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| From any initial sink state, each key in scope ends at the source's state, or it is an unlisted absent key with no consumed event and keeps its sink value | `absent_replay_safe` | `Orphan_Absence.thy` | yes |
| An unlisted key with no consumed event keeps its initial sink value | `unlisted_quiet_key_kept` | `Orphan_Absence.thy` | yes |
| An except set that over-approximates the selected and changed keys inside the range still gives a safe enumeration. The paper does not rely on this result, since its two key lists are exact | `except_overapprox_safe` | `Orphan_Absence.thy` | yes |

## Convergence: exact synchronization

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Under coverage, the replay from the initial state equals the source at the frontier | `absent_replay`, `absent_replay_cut`, `self_stabilization` | `Orphan_Absence.thy` | yes |
| Convergence on the whole scope implies coverage, so coverage is necessary and sufficient | `coverage_necessary` | `Orphan_Absence.thy` | yes |
| A key that the enumeration lists, or that the sink did not hold, ends equal to the source | `partial_enumeration_safe` | `Orphan_Absence.thy` | yes |
| A sink with finitely many rows admits a covering enumeration when every unit has finitely many survivors, and with it the replay converges | `svl2_exists_covering`, `range_record_converges` | `Orphan_Absence.thy` | yes |
| A sink applying the chunk info records of every unit converges on the whole scope | `chunk_record_converges` | `Orphan_Absence.thy` | yes |
| A complete read of the sink's keys during the pass provides coverage | `sink_read_covers` | `Orphan_Absence.thy` | yes |
| A full pass followed by a later bracketed read is safe, and converges under coverage | `pass_then_read_safe`, `pass_then_read_converges` | `Orphan_Absence_Composition.thy` | yes |
| The keys a pass leaves out of sync are exactly the unlisted keys the sink holds that are absent at the source and that no log event during the pass mentions | `pass_leaves_wrong_iff` | `Orphan_Absence_Composition.thy` | yes |
| A later request, or a later pass, that checks the keys a pass left out of sync completes the pass | `pass_then_request_converges`, `request_after_pass_converges` | `Orphan_Absence_Composition.thy` | yes |

## Flink CDC range-merge rule

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety for the buffered range merge from any initial sink state | `rm_absent_replay_safe` | `Orphan_Absence_Range_Merge.thy` | no |
| Coverage is sufficient and necessary for convergence | `rm_self_stabilization`, `rm_coverage_necessary` | `Orphan_Absence_Range_Merge.thy` | no |
| A sink with finitely many rows admits a covering enumeration when every unit's merged image has finitely many present keys, and with it the replay converges | `rml2_exists_covering`, `range_merge_record_converges` | `Orphan_Absence_Range_Merge.thy` | no |
| From an empty sink the widened enumeration gives the result of the Generalized DBLog core | `rm_absent_replay_empty` | `Orphan_Absence_Range_Merge.thy` | no |
| Witnesses: a row deleted before the chunk's window, or inside it, stays in the sink under the core's enumeration and is removed once the key of the held-back delete is listed | `wit_pre_core_keeps_row`, `wit_inw_core_keeps_row`, `wit_pre_forced_repairs`, `wit_inw_forced_repairs` | `Orphan_Absence_Range_Merge.thy` | no |

## Further results

### A repair request served while a pass is running

These results hold when the request's window lies within the pass.

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety with the request's close blocks inserted into the pass's stream | `pass_with_request_safe` | `Orphan_Absence_Interleaved.thy` | yes |
| Convergence under coverage, and for a request that covers the keys the pass leaves out of sync | `pass_with_request_converges`, `pass_with_listing_request_converges`, `request_in_pass_converges` | `Orphan_Absence_Interleaved.thy` | yes |

### One connector restart

These results hold for a window-discard pass with one restart that interrupts
the pass outside a chunk's close, when the connector resumes from an offset
committed during the pass and re-runs every unfinished chunk.

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety at the end of the resumed pass | `restart_safe` | `Orphan_Absence_Restart.thy` | yes |
| Convergence under coverage | `restart_converges` | `Orphan_Absence_Restart.thy` | yes |

### The chunk ranges of a pass

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| The emitted ranges are pairwise disjoint and consecutive, with the first open below | `ranges_disjoint`, `ranges_consecutive`, `ranges_first_open_below` | `Orphan_Absence_Tiling.thy` | yes |
| Each range is a full page closed at its last key, a short page open above, or a short bounded page closed at the recorded maximum | `range_rule` | `Orphan_Absence_Tiling.thy` | yes |
| A completed pass covers every key, and a pass stopped by the tail-read limit covers the keys up to its frontier | `union_on_completion`, `union_on_limit`, `union_on_limit_last_returned` | `Orphan_Absence_Tiling.thy` | yes |
| On a finite source state, every key in a range that the read did not return was absent at that read | `range_sound`, `range_absent`, `range_exact` | `Orphan_Absence_Tiling.thy` | yes |
| Closing a full page open above would certify a present key absent | `terminal_rule_necessary` | `Orphan_Absence_Tiling.thy` | yes |
| The chunks of a pass form a capture contract of the core, given a read coordinate inside each bracket and a read whose key set equals the source state there | `pass_contract`, `completed_pass_contract`, `limited_pass_contract` | `Orphan_Absence_Tiling.thy` | yes |

### In-order at-least-once delivery

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Re-applying a suffix of an applied stream leaves the replayed state unchanged | `replay_suffix_idempotent` | `Orphan_Absence_Replay.thy` | yes |
| A delete for a key the sink does not hold leaves the sink unchanged | `delete_absent_noop` | `Orphan_Absence_Replay.thy` | yes |
| Every in-order at-least-once delivery replays to the state of the stream itself | `at_least_once_replay`, `redelivered_replay` | `Orphan_Absence_Replay.thy` | yes |
| Safety and convergence hold for every such delivery of the emission | `absent_replay_safe_at_least_once`, `self_stabilization_at_least_once` | `Orphan_Absence_Replay.thy` | yes |
| The same two results per key, as in a key-partitioned topic | `absent_replay_safe_at_least_once_per_key`, `self_stabilization_at_least_once_per_key`, `partitioned_delivery_per_key` | `Orphan_Absence_Replay.thy` | yes |

## The three verification layers

- **Isabelle/HOL** proves all of the results above in the session
  `Orphan_Absence`.
- **Lean 4** proves the results of every theory a second time, except those of
  `Orphan_Absence_Range_Merge.thy`.
- **TLA+** model-checks three bounded models of the connector protocol with
  TLC, which gives operational evidence rather than a proof.
  [formal/tla/RUNS.md](../formal/tla/RUNS.md) records the runs.

## What the results do not say

Kernel checking establishes the formal results under their assumptions. It
does not establish that a running connector satisfies them. Section 8 of the
paper names the assumptions that the proofs rely on in a deployment, and what
lies outside the formal model. The section "What the session proves" of
[formal/README.md](../formal/README.md) ends with the corresponding list in
the artifact's terms.

## Citation rule

When citing a result, include:

1. the guarantee as Section 8 of the paper states it, with its conditions,
2. the Isabelle theorem name and its theory,
3. the verification layer you rely on: Isabelle, Lean, or bounded model checking.

Do not cite the one-line label alone.
