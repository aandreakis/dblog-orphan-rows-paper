# Result index

This file maps the guarantees stated in Section 8 of the paper
"Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC
Pipelines" ("What is formally verified") to the Isabelle/HOL theories and
theorem names that carry them.

The paper states its guarantees in prose and does not number them. The tables
below were compiled from [formal/README.md](../formal/README.md), which is part
of the archived artifact and describes every statement. That file is
authoritative. Each Isabelle name listed here was checked to be a declared
theorem or lemma in the named theory file.

The descriptions are labels. They are not formal statements. For citation or
technical comparison, read Section 8 in <code>paper/main.tex</code> and the
Isabelle statement with its assumptions. The Isabelle source is authoritative.

Theory files are in [formal/orphan_absence/](../formal/orphan_absence/). The
column "Lean" says whether the Lean 4 port in
[formal/lean/](../formal/lean/) also proves the theory's results.
[formal/lean/README.md](../formal/lean/README.md) maps each Isabelle name to
its Lean name.

## Safety: no false deletes or wrong values

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| From any initial sink state, each key in scope ends at the source's state, or it is an unlisted absent key with no consumed event and keeps its sink value | <code>absent_replay_safe</code> | <code>Orphan_Absence.thy</code> | yes |
| A key that the enumeration lists, or that the sink did not hold, ends equal to the source | <code>partial_enumeration_safe</code> | <code>Orphan_Absence.thy</code> | yes |
| An unlisted key with no consumed event keeps its initial sink value | <code>unlisted_quiet_key_kept</code> | <code>Orphan_Absence.thy</code> | yes |
| An over-approximated except set inside the range still gives a safe enumeration | <code>except_overapprox_safe</code> | <code>Orphan_Absence.thy</code> | yes |

## Convergence: exact synchronization

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Under coverage, the replay from the initial state equals the source at the frontier | <code>absent_replay</code>, <code>absent_replay_cut</code>, <code>self_stabilization</code> | <code>Orphan_Absence.thy</code> | yes |
| Convergence on the whole scope implies coverage, so coverage is necessary and sufficient | <code>coverage_necessary</code> | <code>Orphan_Absence.thy</code> | yes |
| A sink with finitely many rows admits a covering enumeration, and with it the replay converges | <code>svl2_exists_covering</code>, <code>range_record_converges</code> | <code>Orphan_Absence.thy</code> | yes |
| A sink applying the chunk info records of every unit converges on the whole scope | <code>chunk_record_converges</code> | <code>Orphan_Absence.thy</code> | yes |
| A complete read of the sink's keys during the pass provides coverage | <code>sink_read_covers</code> | <code>Orphan_Absence.thy</code> | yes |
| A full pass followed by a later bracketed read is safe, and converges under coverage | <code>pass_then_read_safe</code>, <code>pass_then_read_converges</code> | <code>Orphan_Absence_Composition.thy</code> | yes |
| The keys a pass leaves wrong, characterized exactly | <code>pass_leaves_wrong_iff</code> | <code>Orphan_Absence_Composition.thy</code> | yes |
| A later request, or a later pass, that checks the keys a pass left wrong completes the pass | <code>pass_then_request_converges</code>, <code>request_after_pass_converges</code> | <code>Orphan_Absence_Composition.thy</code> | yes |

## Flink CDC range-merge rule

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety for the buffered range merge from any initial sink state | <code>rm_absent_replay_safe</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |
| Coverage is sufficient and necessary for convergence | <code>rm_self_stabilization</code>, <code>rm_coverage_necessary</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |
| A covering enumeration exists, and with it the replay converges | <code>rml2_exists_covering</code>, <code>range_merge_record_converges</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |
| From an empty sink the widened enumeration gives the result of the Generalized DBLog core | <code>rm_absent_replay_empty</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |
| A row deleted by a held-back event stays in the sink unless the delete is re-emitted at the chunk's close | <code>wit_pre_core_keeps_row</code>, <code>wit_pre_forced_repairs</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |

## Further results

### A repair request served while a pass is running

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety with the request's close blocks inserted into the pass's stream | <code>pass_with_request_safe</code> | <code>Orphan_Absence_Interleaved.thy</code> | yes |
| Convergence under coverage, and for a request that covers the keys the pass leaves wrong | <code>pass_with_request_converges</code>, <code>pass_with_listing_request_converges</code>, <code>request_in_pass_converges</code> | <code>Orphan_Absence_Interleaved.thy</code> | yes |

### One connector restart

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety at the end of the resumed pass | <code>restart_safe</code> | <code>Orphan_Absence_Restart.thy</code> | yes |
| Convergence under coverage | <code>restart_converges</code> | <code>Orphan_Absence_Restart.thy</code> | yes |

### The chunk ranges of a pass

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| The emitted ranges are pairwise disjoint and consecutive, with the first open below | <code>ranges_disjoint</code>, <code>ranges_consecutive</code>, <code>ranges_first_open_below</code>, <code>range_rule</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |
| A completed pass covers every key, and a pass stopped by the tail-read limit covers the keys up to its frontier | <code>union_on_completion</code>, <code>union_on_limit</code>, <code>union_on_limit_last_returned</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |
| Every key in a range that the read did not return was absent at that read | <code>range_sound</code>, <code>range_absent</code>, <code>range_exact</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |
| Closing a full page open above would certify a present key absent | <code>terminal_rule_necessary</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |
| The chunks of a pass form a capture contract of the core | <code>pass_contract</code>, <code>completed_pass_contract</code>, <code>limited_pass_contract</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |

### In-order at-least-once delivery

| Result | Isabelle names | Theory | Lean |
|---|---|---|---|
| Re-applying a suffix of an applied stream leaves the replayed state unchanged | <code>replay_suffix_idempotent</code> | <code>Orphan_Absence_Replay.thy</code> | yes |
| A delete for a key the sink does not hold leaves the sink unchanged | <code>delete_absent_noop</code> | <code>Orphan_Absence_Replay.thy</code> | yes |
| Every in-order at-least-once delivery replays to the state of the stream itself | <code>at_least_once_replay</code>, <code>redelivered_replay</code> | <code>Orphan_Absence_Replay.thy</code> | yes |
| Safety and convergence hold for every such delivery of the emission | <code>absent_replay_safe_at_least_once</code>, <code>self_stabilization_at_least_once</code> | <code>Orphan_Absence_Replay.thy</code> | yes |
| The same per key, as for a topic partitioned by key | <code>absent_replay_safe_at_least_once_per_key</code>, <code>self_stabilization_at_least_once_per_key</code>, <code>partitioned_delivery_per_key</code> | <code>Orphan_Absence_Replay.thy</code> | yes |

## Not covered

Section 8 of the paper names the assumptions that the proofs rely on in a
deployment, and what lies outside the formal model. The section "What the
session proves" of [formal/README.md](../formal/README.md) ends with the same
list in the artifact's terms.
