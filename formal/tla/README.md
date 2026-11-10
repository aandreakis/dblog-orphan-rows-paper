# TLA+ models of the connector protocol

This folder holds three bounded TLA+ models of the connector protocol of Section 5 of the paper, checked with the
TLC model checker. They are evidence, not proof. The paper's guarantees rest on the Isabelle/HOL theories and their
Lean 4 port in this archive. The models check what the theories leave out: the connector's operational steps, a
crash at every step, the PostgreSQL visibility gap, the safety cap, the request `verify-keys-absent` and the drift
process, and liveness. They can also serve as an oracle for an implementation, since every mutation below is a
scenario a correct connector must not show.

## The three modules

| Folder | Module | What it models | Paper |
|---|---|---|---|
| `.` | `AbsenceConnector.tla` | the log with watermarks, visibility as a second step with both variants of the rule, the bounded loop with the recorded maximum and tail reads, the window with selected and changed keys, the close block (free candidate lists, the record rendered per key, or the atomic chunk info record), the output stream with offset contexts, a crash at any step with the restart from the committed context | 5.1 to 5.3, 5.6 |
| `holds/` | `AbsenceConnectorHolds.tla` | the safety cap: a statement held back, its release as a fresh bracketed read, a hold across a restart under two readings, a sink refusing an unconfirmed record | 5.6 |
| `requests/` | `AbsenceConnectorRequests.tla` | the request `verify-keys-absent` in batches, the drift process, the bounds hand-off, the end-of-pass key-list reads, liveness under weak fairness | 5.3 to 5.6 |

The two extensions EXTEND the core and do not edit it. TLC resolves an EXTENDS from the module's own folder, so
`holds/` and `requests/` each carry a byte-identical copy of `AbsenceConnector.tla`. With their new features switched
off, both extensions reproduce the core's verdicts and its generated and distinct state counts exactly on the core
configurations they re-run (the `R_` and `RH_` configurations of `holds/`, the `X_` configurations of `requests/`).

| Module | sha256 |
|---|---|
| `AbsenceConnector.tla` (and its two copies) | `4cbeac5962889914159a388f736422187cd1af51f75f4384401cbe44ebed9156` |
| `holds/AbsenceConnectorHolds.tla` | `f2bacf8a0fc6619e6a25fa56eb0fa45973a56a1038e00fc1c0170e81b681916f` |
| `requests/AbsenceConnectorRequests.tla` | `480e49a56403d00229d16d12e97fd0a92681707a9c9151fe2fef3c6133ac3504` |

Each module's header maps every operator and invariant to the paper sentence and to the Isabelle statement it
transcribes, and marks every relaxation of the theories as EXTENSION.

## What the invariants check

- **A statement is true at its own position.** `CloseEntryTrue` checks every emitted row and absence entry against
  the source at the entry's own position, including the released entries of a hold and the entries of a request
  (`HoldsSafe`, `RequestSafe`). This is the safety of Section 8 in operational form.
- **Safety at quiescence.** `QuiescentSafe` and its extensions transcribe `absent_replay_safe`, `restart_safe` and
  `pass_with_request_safe` over the contracts' scope, for every key and every initial sink value.
- **Convergence.** `QuiescentConverges` under the cover premise, and `RecordConverges` for the chunk info record
  without one. `DeliveredRecordAbsence` checks that a delivered record's absent keys stay deleted across a crash.
- **The bridge to the theories.** `LocaleAssumptions` checks on every behavior that the emitted stream satisfies the
  assumptions of the Isabelle locales, so that the theorem supplies the conclusion. It is a `pass_restart` instance
  with one crash and a `pass_with_request` instance with one request. With two crashes, or a crash together with a
  release or a request, it checks the per-incarnation contracts only, and the composition is labelled EXTENSION with
  operational evidence.
- **The tiling.** `TilingOK` transcribes the range theorems of the tiling theory, across restarts, with the recorded
  maximum and the tail count persisted.
- **Liveness** (`requests/` only). Under weak fairness of the connector, request service, the hand-off, the end
  reads and the drift process, every requested key is eventually served and the sink eventually converges on every
  covered key. Four control configurations violate the properties when the fairness or the protocol is broken, so
  the properties are not vacuous.

## Mutations, each a scenario a correct connector must not show

| Module | Mutation | What fails | In the paper's terms |
|---|---|---|---|
| core | the visibility rule off, or limited to the window | `CloseEntryTrue` | an insert logged before the low watermark but invisible to the query is certified absent |
| core | the changed keys dropped | `CloseEntryTrue` | a key changed in the window is certified absent |
| core | a full page left open above | `LocaleAssumptions`, `CloseEntryTrue` | a present key above the page is certified absent |
| core | chunk progress persisted with the first close entry | `QuiescentConverges` | a crash loses the rest of the close block, a row is never delivered |
| core | the record rendered per key with a crash | `DeliveredRecordAbsence` | an orphan survives a record the sink would have applied whole |
| core | the offset committed before the record is acknowledged | `RecordConverges` | the record is lost across the restart |
| core | the pending-visibility set lost at a restart, or reset at a chunk close | `CloseEntryTrue` | an invisible transaction is forgotten and its key certified absent |
| core | the tail count reset, or the maximum re-recorded, at a restart | `TilingOK` | a tail read beyond the limit, or an inverted range |
| holds | the stored statement released without a fresh read | `HoldsSafe` | a key inserted between the close and the release is deleted |
| holds | the release's read without the window rule (waiting variant) | `HoldsSafe` | a key changed inside the release window is certified absent |
| holds | the hold lost at a restart | `RecordConvergesH` | the held keys are never released (convergence, not safety) |
| requests | a request ignoring changed keys | `RequestSafe` | a live key is certified absent |
| requests | the bounds published at the tail's highest key | `HandOffCovers` | an orphan between the recorded maximum and new rows is never requested |
| requests | requested keys dropped at a restart | `ReqCovers`, liveness | the orphan stays (convergence, not safety) |
| requests | the drift process deleting directly at the sink | `NoLiveRowDeleted` | the unpositioned delete of Section 6 removes a live row |
| requests | interleaved windows with one shared pending set | `RequestSafe` | the chunk prunes the set, the request certifies a live key absent |
| requests | a batch's completion committed with its first entry | `ReqCovers` | a crash loses the rest of the batch |

Two further results. A sink applying the absence part of an unconfirmed record breaks nothing but the cap's own
guard, since that part is true at its position, so the safety cap guards against deletes an operator did not
expect, not against wrong ones. And overlapping request and chunk windows are safe and converge when each read keeps
its own view of the pending-visibility set, as the Interleaved theory predicts, so the paper's serialization of
windows is what makes one shared set sufficient.

The pre-pass scenario of Section 5.6 is checked too. Under the treat-as-changed variant, a transaction decoded before
the pass and still invisible at the chunk query leaves its key unrepaired by the pass, with no live row deleted.
Under the waiting variant the pass converges.

## Bounds, and runs that did not finish

Keys 1 to 3 (5 in four configurations of `holds/`), values {v1, v2}, up to 4 writes, chunk size 1 or 2, tail limit
1 or 2, up to 2 crashes at 2 keys and 1 crash at 3 keys, a cap of 1, up to 2 requests, liveness at 2 keys.
`RUNS.md` lists every run. Runs stopped by their cap with no violation are named there as such. G12 (28,206,094
states) and G5 (34,568,774 states) of the core were stopped at their 40-minute cap with no violation. G12 completed
with an earlier revision of the core (38,869,092 states), and its Record-mode counterpart G12r completes. The 5-key
configuration Z4 of `holds/` was stopped at 10 minutes (2,805,210 states, depth 31). In `requests/`, H3b was stopped
at its cap. Of the long runs, LQ1 completed with no error (14,329,818 states), LQ4 was stopped with no violation
(46,311,157 states), and LQ2, LQ3 and LQ5 were not run. Six more configurations of `requests/` have no row in
`RUNS.md`, since they were not run against the final module. H3_hoc_k2w2c1, H4_hor_k3w1c0r1n2, L2_live_k2w1c1r1
and R4b_rq2_k3w1c0r2b2 ran only against an earlier revision of it, and I2_rqi_k2w2c0r1b1 and R5b_rqc_k2w2c1r1b1 were
not run.

## The run record

`RUNS.md` was generated from TLC's own output in the logs of the original runs, one row per run, with the spec and
configuration hashes each log recorded. The logs themselves are not part of this archive, since they carry
machine-specific paths. Running a configuration again reproduces its verdict and, for a completed run, its
distinct-state count. The rows of `holds/` marked `review/` come from an independent review of that module, which
named its runs after its probes (`ReviewProbes.tla` and the `Z` configurations). The first two comment lines of the
`Z` configurations were corrected to the true bounds after those runs, so `RUNS.md` shows their configuration hashes
as differing. Their constants are unchanged.

## Notes

- In `holds/`, `CompositionOK` holds by construction and carries no evidence of its own. The composition theory's
  instance it names is still sound, and the stream order comes from `StreamShapeH`. One sentence of its header ("a
  window event before the query is in its result") is false under the visibility gap. Its conclusion holds, because
  such a transaction is in the query's unseen set.
- Mutation runs use one worker, so their counterexamples are shortest and their counts deterministic. Green runs use
  all cores.
- `requests/Mc_dropreqs_safety.cfg` says it runs the mutation's constants but runs one write fewer (both halves of
  the result fit there). The header of `requests/` says the new variables stay constant, which does not hold for the
  request contexts at one crash (a function of the output, so the state counts are unaffected).

## Known limitations

An independent review of the three modules found four places where a model checks less than it claims. None
contradicts an Isabelle theorem or shows a defect of the paper's protocol. They are stated here rather than fixed,
since each fix needs a change of the specification and new runs.

- **End-of-pass candidates after a restart** (`requests/`). The extension argues that a resumed pass that completes
  covers the tail, so the end-of-pass reads need not be retained. A resumed chunk, however, uses the core's free
  choice of absence candidates, not the fixed supplied list, so in the model a known candidate can stay unrepaired
  while every check passes. The paper's protocol does list every supplied candidate at a chunk close, so it is not
  affected. `EndReadCovers` and the liveness coverage do not check this case.
- **The record and its surviving rows** (core, `holds/`). Record mode emits the chunk info record together with the
  chunk's surviving rows as one atomic item. The paper emits the record first and the rows after it, so a crash
  between them is possible. Record mode does not model it. The same crash with a premature progress commit is shown to
  lose a row only in the per-key Dense rendering (mutation M3).
- **The empty-table confirmation** (`holds/`). The model's empty-table test is the record's shape, both bounds open
  and no row. A table emptied after its maximum was recorded gives a bounded first chunk with no row, which the test
  misses, so its absence statements go out without confirmation. Those statements are true, and the cap is an
  operational guard, so safety is unaffected.
- **One witness** (`holds/HW_WitInsertBeforeRelease_k3w3c0.cfg`). It fires on a key that was invisible at the held
  read, not on a key inserted after the close, so it does not witness the stale-release scenario its comment names.
  The stale-release mutation's own counterexample is the genuine one.

## Toolchain and how to run

TLC 2.19 of 08 August 2024 (rev 5a47802), from the TLA+ tools release that ships it
(https://github.com/tlaplus/tlaplus/releases), as `tla2tools.jar` with sha256
`936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88`, and OpenJDK 21. From a module's folder, with
`tla2tools.jar` copied there or its path given to `-cp`:

```sh
java -XX:+UseParallelGC -Xmx8g -cp tla2tools.jar tlc2.TLC -workers auto -cleanup -metadir meta/<run> -config <cfg> <module>.tla
```

Each configuration opens with a comment line stating what it is and the expected verdict. Use `-workers 1` for a
mutation run to get its shortest counterexample. Most runs finish within seconds to a few minutes. The largest
completed runs take about 25 minutes on a 12-core workstation (`RUNS.md` lists each run's time), and the original
runs used `-Xmx24g`.
