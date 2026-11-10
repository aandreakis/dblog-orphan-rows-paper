# AGENTS.md

## Purpose

This repository contains the verification artifact and manuscript sources for the paper
"Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC
Pipelines." It combines:

- the exact arXiv v1 paper source and stamped PDF,
- the complete formal verification artifact archived as version 1.0
  (Isabelle/HOL, Lean 4, TLA+),
- a short result index and provenance notes.

Human readers should start at `README.md`, which is short and points
at the sources and their identifiers. This file is the most detailed guide in
the repository. Use it before answering questions about the results or modifying
the reader guides.

This repository is not a software project. There is no application to run and no
feature work. Your likely task is to read, explain, cite, or check.

**Links.** Paper: [arXiv:2611.10810](https://arxiv.org/abs/2611.10810)
([v1 abstract](https://arxiv.org/abs/2611.10810v1) ·
[v1 PDF](https://arxiv.org/pdf/2611.10810v1) ·
[in-repo PDF](paper/dblog-orphan-rows.pdf) ·
[sources](paper/)). Verification artifact: [formal/](formal/) · archived at Zenodo
[10.5281/zenodo.24035424](https://doi.org/10.5281/zenodo.24035424) (version 1.0)
· [10.5281/zenodo.24035423](https://doi.org/10.5281/zenodo.24035423) (concept
DOI). Reader guides and indexes:
[formal/README.md](formal/README.md) ·
[formal/lean/README.md](formal/lean/README.md) ·
[formal/tla/README.md](formal/tla/README.md) ·
[docs/THEOREMS.md](docs/THEOREMS.md) ·
[docs/PROVENANCE.md](docs/PROVENANCE.md). Earlier work:
[Generalized DBLog](https://arxiv.org/abs/2609.08160) ·
[theory paper for the original algorithm](https://arxiv.org/abs/2605.31475) ·
[2020 DBLog paper](https://arxiv.org/abs/2010.12597). Author: Andreas Andreakis,
[ORCID 0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402).

## Source precedence

When sources differ, use this order:

1. **Isabelle theorem statements and definitions** under
   `formal/orphan_absence/` and its three dependency sessions are
   authoritative for what is proved.
2. **formal/README.md** is the authoritative description of the artifact. It
   names the main proved statements, the assumptions outside the theories, and
   the build instructions. `formal/lean/README.md` maps each Isabelle
   name to its Lean name. `formal/tla/README.md` and
   `formal/tla/RUNS.md` describe the models and their runs.
3. **paper/main.tex** is authoritative for the paper's design, its exposition,
   the guarantees as published in Section 8, and the scope discussion.
4. **README.md** and `docs/` are reader guides and indexes.

The kernel checks the theorem statements under their stated assumptions. It
does not check whether a real deployment satisfies those assumptions.

## Frozen and editable areas

| Path | Role | Edit policy |
|---|---|---|
| `formal/` | Exact Zenodo 1.0 artifact bytes | Do not edit. Publish a new artifact version instead. |
| `paper/` | Exact arXiv v1 source and PDF | Do not edit in place. Refresh only from a new public arXiv version. |
| `README.md`, `docs/`, this file | Reader guides | May be clarified if every claim remains traceable to the frozen sources. |
| `CITATION.cff` | Repository citation metadata | Update only when the public paper or artifact record changes. |

## What the paper studies

A CDC pipeline keeps sinks, such as a search index or a data warehouse, in
sync with a source database. DBLog-based incremental snapshots, as adopted by
Debezium and Flink CDC, read the source tables in chunks interleaved with the
log. After its bootstrap a sink can drift and end up holding orphan rows,
which are still in the sink but no longer at the source. In DBLog's original
design each chunk emits only the rows the table still contains, so it does not
handle orphan rows.

The paper extends the design with three components:

- **The chunk info record.** A chunk read also establishes which keys in its
  range the select did not return. The connector emits a chunk info record
  with each chunk's rows. It carries the chunk's key range, the selected keys
  that the query returned, and the changed keys that have a change event inside
  the watermark window. A sink that accepts the record deletes every key it
  holds in the range that is neither selected nor changed. For key-partitioned
  transports and for sinks that only accept per-key events, the connector can
  instead emit per-key absence events, one for each absent candidate key
  supplied to it. Sinks apply them as deletes.
- **The request `verify-keys-absent`.** An external process submits
  keys it suspects are orphans. The connector reads those keys at the source
  between watermarks and emits an absence event for each key it confirms
  absent. The requesting process never deletes from the sink directly.
- **The drift process.** An external process inspects sinks for suspected
  orphans and submits them through the request.

This gives three modes: the fully integrated mode, the mode with an external
drift process, and the combination of both, which the paper recommends.

## Paper terms and mechanization names

The paper and the mechanization use different names for a few objects.

| Paper | Mechanization |
|---|---|
| the formal development, the Isabelle session | `Orphan_Absence` in `formal/orphan_absence/` |
| the Lean 4 port | `OrphanAbsence` in `formal/lean/` |
| selected keys and changed keys of a chunk info record | their union is the except set `except_keys` |
| changed keys | touched keys |
| the request `verify-keys-absent` | a bracketed key-list read. It is the later read in `Orphan_Absence_Composition.thy` and the interleaved read in `Orphan_Absence_Interleaved.thy` |
| Flink CDC's buffered range merge | `Orphan_Absence_Range_Merge.thy`, on the core's `Range_Merge` |

## Result map

The paper states its guarantees in Section 8 in prose and does not number
them. The table lists the main theorems by theory. All theory files are in
`formal/orphan_absence/`. The full index is
`docs/THEOREMS.md`, and `formal/README.md` describes
each of these statements.

| Section 8 | Main Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety | `absent_replay_safe` | `Orphan_Absence.thy` | yes |
| Convergence | `self_stabilization`, `coverage_necessary`, `chunk_record_converges`, `sink_read_covers` | `Orphan_Absence.thy` | yes |
| Convergence, a pass followed by a request or a later pass | `pass_then_read_safe`, `pass_then_request_converges`, `request_after_pass_converges` | `Orphan_Absence_Composition.thy` | yes |
| Flink CDC range-merge rule | `rm_absent_replay_safe`, `rm_self_stabilization`, `rm_coverage_necessary` | `Orphan_Absence_Range_Merge.thy` | no |
| A request served while a pass is running | `pass_with_request_safe`, `request_in_pass_converges` | `Orphan_Absence_Interleaved.thy` | yes |
| One connector restart | `restart_safe`, `restart_converges` | `Orphan_Absence_Restart.thy` | yes |
| The chunk ranges of a pass | `ranges_disjoint`, `ranges_consecutive`, `union_on_completion`, `range_absent` | `Orphan_Absence_Tiling.thy` | yes |
| In-order at-least-once delivery | `absent_replay_safe_at_least_once`, `self_stabilization_at_least_once`, `partitioned_delivery_per_key` | `Orphan_Absence_Replay.thy` | yes |

## Misreadings to avoid

| Misreading | Correction |
|---|---|
| "The paper verifies Debezium or Flink CDC." | The proofs verify the stream-level algorithm. No running connector is verified. |
| "Every orphan is always removed." | Safety holds from any initial sink state without a coverage condition. Convergence holds if and only if the emitted absence statements cover every orphan held by the sink that the log stream never mentions. An orphan that neither a read nor the log stream mentions remains untouched. |
| "The proofs cover the transport." | In a deployment they rely on the pipeline delivering each key's events in order. In-order at-least-once delivery is proved sufficient. Out-of-order delivery of one key's events is outside the formal model. |
| "The proofs cover the database engine." | They rely on the chunk query visibility rule of Section 5.6, full row images in the log, complete SQL select scans, matching key order and equality between source and sink under a fixed schema, and on transaction atomicity and liveness. |
| "Concurrent writers at the sink are covered." | Concurrent side writers during repair and row-versioned conflict resolution are outside the formal model. |
| "Restart and failover are proved in general." | Safety and convergence are proved for one connector restart that interrupts a pass outside a chunk's close, provided the connector resumes from an offset committed during the pass and re-runs every unfinished chunk. More than one restart is not modeled in the theories. |
| "Lean proves the same theorems as Isabelle." | The Lean port covers every theory except the Flink CDC range merge, which is proved in Isabelle only. |
| "Model checking proves the protocol." | The TLA+ models are bounded and give evidence that does not replace the proofs. Many configurations are mutations or witnesses that are built to produce a counterexample. |

## Artifact facts

- Zenodo version DOI: `10.5281/zenodo.24035424`
- Zenodo concept DOI: `10.5281/zenodo.24035423`
- Version: `1.0`
- Publication date: `2026-11-07`
- Archive: `DBLog_Orphan_Absence_artifact-1.0.zip`
- Archive SHA-256:
  `0d6577a7c097c50778e17e6a145b2d09be0aa811a5d6a876e43945a332922047`
- 285 files: 55 Isabelle theory files in four sessions, 7 of them in the
  session `Orphan_Absence`, 24 Lean files, 3 TLA+ models with 175
  TLC configurations, and the run record of the models.
- Checked with Isabelle2025-2, Lean 4.32.2, and TLC 2.19.
- No `sorry`, no `oops` and no axiom declarations in the
  Isabelle theories.
- The Lean port contains no `sorry` and declares no axioms. Every
  theorem of the port depends on at most `propext`,
  `Classical.choice` and `Quot.sound`, the standard
  axioms of Lean 4.

## Verification commands

### Paper source

~~~bash
cd paper
pdflatex main
pdflatex main
pdflatex main
pdfinfo dblog-orphan-rows.pdf
~~~

Expected public PDF: 15 pages, letter size, four figures, two tables.

### Verification artifact

~~~bash
cd formal
shasum -a 256 -c SHA256SUMS
isabelle build -b -j 8 -o quick_and_dirty=false -o document=false -o document_variants= \
  -d dual_write_layer0 -d formal -d dblog_framework/framework_core -d orphan_absence \
  Orphan_Absence
~~~

~~~bash
cd formal/lean
lake build
~~~

The Isabelle and TLC checks take time and need the tools named in
`formal/README.md`. Do not run them unless the user asked for a
build. Read the sources, `formal/lean/VERIFICATION.md` and
`formal/tla/RUNS.md` instead. `lake build` and TLC write
their output into the tree. That output is ignored by git and is not part of
the artifact.

### Deposit fidelity

Run from the repository root:

~~~bash
curl -sL -o artifact.zip https://zenodo.org/records/24035424/files/DBLog_Orphan_Absence_artifact-1.0.zip
unzip -q artifact.zip
diff -r DBLog_Orphan_Absence_artifact-1.0 formal
~~~

No output from `diff` means byte identity.

## Short summary

A short accurate summary is:

> The paper extends DBLog-based incremental snapshots so that a CDC pipeline
> can also delete orphan rows, which are still in a sink but no longer at the
> source. A chunk read already knows which keys in its range the query did
> not return, and the connector emits that information as a chunk info record,
> or as per-key absence events, which sinks apply as deletes. A repair request
> lets an external drift process submit suspected orphan keys, and the
> connector emits absence events only for keys it confirms absent at the
> source. The core safety and convergence results are machine-checked in
> Isabelle/HOL and Lean 4, and bounded TLA+ models of the connector protocol
> are checked with TLC.

Do not shorten this to "Debezium is verified" or "DBLog removes every orphan
row."
