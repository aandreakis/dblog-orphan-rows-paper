# AGENTS.md

## Purpose

This repository contains the verification artifact and manuscript sources for the paper
"Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC
Pipelines." It combines:

- the exact arXiv v1 paper source and stamped PDF,
- the complete formal verification artifact archived as version 1.0
  (Isabelle/HOL, Lean 4, TLA+),
- a short result index and provenance notes.

Human readers should start at <code>README.md</code>, which is short and points
at the sources and their identifiers. This file is the most detailed guide in
the repository. Use it before answering questions about the results or modifying
derived documentation.

This repository is not a software project. There is no application to run and no
feature work. Your likely task is to read, explain, cite, or check.

**Links.** Paper: [arXiv:2611.10810](https://arxiv.org/abs/2611.10810)
([v1 abstract](https://arxiv.org/abs/2611.10810v1) ·
[v1 PDF](https://arxiv.org/pdf/2611.10810v1) ·
[in-repo PDF](paper/dblog-orphan-rows.pdf) ·
[sources](paper/)). Verification artifact: [formal/](formal/) · archived at Zenodo
[10.5281/zenodo.24035424](https://doi.org/10.5281/zenodo.24035424) (version 1.0)
· [10.5281/zenodo.24035423](https://doi.org/10.5281/zenodo.24035423) (concept
DOI). Indexes and derived reading:
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
   <code>formal/orphan_absence/</code> and its three dependency sessions are
   authoritative for what is proved.
2. **formal/README.md** is the authoritative description of the artifact. It
   names the main proved statements, the assumptions outside the theories, and
   the build instructions. <code>formal/lean/README.md</code> maps each Isabelle
   name to its Lean name. <code>formal/tla/README.md</code> and
   <code>formal/tla/RUNS.md</code> describe the models and their runs.
3. **paper/main.tex** is authoritative for the paper's design, its exposition,
   the guarantees as published in Section 8, and the scope discussion.
4. **README.md** and <code>docs/</code> are derived aids for readers.

The kernel checks the theorem statements under their stated assumptions. It
does not check whether a real deployment satisfies those assumptions.

## Frozen and editable areas

| Path | Role | Edit policy |
|---|---|---|
| <code>formal/</code> | Exact Zenodo 1.0 artifact bytes | Do not edit. Publish a new artifact version instead. |
| <code>paper/</code> | Exact arXiv v1 source and PDF | Do not edit in place. Refresh only from a new public arXiv version. |
| <code>README.md</code>, <code>docs/</code>, this file | Derived guidance | May be clarified if every claim remains traceable to the frozen sources. |
| <code>CITATION.cff</code> | Repository citation metadata | Update only when the public paper or artifact record changes. |

## What the paper studies

A CDC pipeline keeps sinks, such as a search index or a data warehouse, in
sync with a source database. DBLog-based incremental snapshots, as adopted by
Debezium and Flink CDC, read the source tables in chunks interleaved with the
log. After its bootstrap a sink can drift and end up holding orphan rows,
which are still in the sink but no longer at the source. In DBLog's original
design each chunk emits only the rows the table still contains, so it does not
handle orphan rows.

The paper extends the design with three components:

- **The chunk info record.** A chunk read also establishes which keys of its
  key range the select did not return. The connector emits a chunk info record
  with each chunk's rows. It carries the chunk's key range, the selected keys
  that the query returned, and the changed keys that have a change event inside
  the watermark window. A sink that accepts the record deletes every key it
  holds in the range that is neither selected nor changed. For key-partitioned
  transports and for sinks that only accept per-key events, the connector can
  instead emit per-key absence events, one for each absent candidate key
  supplied to it. Sinks apply them as deletes.
- **The request <code>verify-keys-absent</code>.** An external process submits
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
| the formal development, the Isabelle session | <code>Orphan_Absence</code> in <code>formal/orphan_absence/</code> |
| the Lean 4 port | <code>OrphanAbsence</code> in <code>formal/lean/</code> |
| selected keys and changed keys of a chunk info record | their union is the except set <code>except_keys</code> |
| changed keys | touched keys |
| the request <code>verify-keys-absent</code> | a bracketed key-list read. It is the later read in <code>Orphan_Absence_Composition.thy</code> and the interleaved read in <code>Orphan_Absence_Interleaved.thy</code> |
| Flink CDC's buffered range merge | <code>Orphan_Absence_Range_Merge.thy</code>, on the core's <code>Range_Merge</code> |

## Result map

The paper states its guarantees in Section 8 in prose and does not number
them. The table lists the main theorems by theory. All theory files are in
<code>formal/orphan_absence/</code>. The full index is
<code>docs/THEOREMS.md</code>, and <code>formal/README.md</code> describes
each of these statements.

| Section 8 | Main Isabelle names | Theory | Lean |
|---|---|---|---|
| Safety | <code>absent_replay_safe</code> | <code>Orphan_Absence.thy</code> | yes |
| Convergence | <code>self_stabilization</code>, <code>coverage_necessary</code>, <code>chunk_record_converges</code>, <code>sink_read_covers</code> | <code>Orphan_Absence.thy</code> | yes |
| Convergence, a pass followed by a request or a later pass | <code>pass_then_read_safe</code>, <code>pass_then_request_converges</code>, <code>request_after_pass_converges</code> | <code>Orphan_Absence_Composition.thy</code> | yes |
| Flink CDC range-merge rule | <code>rm_absent_replay_safe</code>, <code>rm_self_stabilization</code>, <code>rm_coverage_necessary</code> | <code>Orphan_Absence_Range_Merge.thy</code> | no |
| A request served while a pass is running | <code>pass_with_request_safe</code>, <code>request_in_pass_converges</code> | <code>Orphan_Absence_Interleaved.thy</code> | yes |
| One connector restart | <code>restart_safe</code>, <code>restart_converges</code> | <code>Orphan_Absence_Restart.thy</code> | yes |
| The chunk ranges of a pass | <code>ranges_disjoint</code>, <code>ranges_consecutive</code>, <code>union_on_completion</code>, <code>range_absent</code> | <code>Orphan_Absence_Tiling.thy</code> | yes |
| In-order at-least-once delivery | <code>absent_replay_safe_at_least_once</code>, <code>self_stabilization_at_least_once</code>, <code>partitioned_delivery_per_key</code> | <code>Orphan_Absence_Replay.thy</code> | yes |

## Misreadings to avoid

| Misreading | Correction |
|---|---|
| "The paper verifies Debezium or Flink CDC." | The proofs verify the stream-level algorithm. No running connector is verified. |
| "Every orphan is always removed." | Safety needs no coverage condition. It holds from any initial sink state. Convergence holds if and only if the emitted absence statements cover every orphan held by the sink that the log stream never mentions. An orphan that neither a read nor the log stream mentions remains untouched. |
| "The proofs cover the transport." | In a deployment they rely on the pipeline delivering each key's events in order. In-order at-least-once delivery is proved sufficient. Out-of-order delivery of one key's events is outside the formal model. |
| "The proofs cover the database engine." | They rely on the chunk query visibility rule of Section 5.6, full row images in the log, complete SQL select scans, matching key order and equality between source and sink under a fixed schema, and on transaction atomicity and liveness. |
| "Concurrent writers at the sink are covered." | Concurrent side writers during repair and row-versioned conflict resolution are outside the formal model. |
| "Restart and failover are proved in general." | Safety and convergence are proved for one connector restart that interrupts a pass outside a chunk's close, provided the connector resumes from an offset committed during the pass and re-runs every unfinished chunk. More than one restart is not modeled in the theories. |
| "Lean proves the same theorems as Isabelle." | The Lean port covers every theory except the Flink CDC range merge, which is proved in Isabelle only. |
| "Model checking proves the protocol." | The TLA+ models are bounded and give evidence. They do not replace the proofs. Many configurations are mutations or witnesses that are built to produce a counterexample. |

## Artifact facts

- Zenodo version DOI: <code>10.5281/zenodo.24035424</code>
- Zenodo concept DOI: <code>10.5281/zenodo.24035423</code>
- Version: <code>1.0</code>
- Publication date: <code>2026-11-07</code>
- Archive: <code>DBLog_Orphan_Absence_artifact-1.0.zip</code>
- Archive SHA-256:
  <code>0d6577a7c097c50778e17e6a145b2d09be0aa811a5d6a876e43945a332922047</code>
- 285 files: 55 Isabelle theory files in four sessions, 7 of them in the
  session <code>Orphan_Absence</code>, 24 Lean files, 3 TLA+ models with 175
  TLC configurations, and the run record of the models.
- Checked with Isabelle2025-2, Lean 4.32.2, and TLC 2.19.
- No <code>sorry</code>, no <code>oops</code> and no axiom declarations in the
  Isabelle theories.
- The Lean port contains no <code>sorry</code> and declares no axioms. Every
  theorem of the port depends on at most <code>propext</code>,
  <code>Classical.choice</code> and <code>Quot.sound</code>, the standard
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
<code>formal/README.md</code>. Do not run them unless the user asked for a
build. Read the sources, <code>formal/lean/VERIFICATION.md</code> and
<code>formal/tla/RUNS.md</code> instead. <code>lake build</code> and TLC write
their output into the tree. That output is ignored by git and is not part of
the artifact.

### Deposit fidelity

Run from the repository root:

~~~bash
curl -sL -o artifact.zip https://zenodo.org/records/24035424/files/DBLog_Orphan_Absence_artifact-1.0.zip
unzip -q artifact.zip
diff -r DBLog_Orphan_Absence_artifact-1.0 formal
~~~

No output from <code>diff</code> means byte identity.

## Short summary

A short accurate summary is:

> The paper extends DBLog-based incremental snapshots so that a CDC pipeline
> can also delete orphan rows, which are still in a sink but no longer at the
> source. A chunk read already knows which keys of its range the select did
> not return, and the connector emits this as a new kind of event that sinks
> apply as deletes. A repair request lets an external process hand orphan
> candidates to the connector, which emits these events only for keys it
> confirms absent at the source. The core safety and convergence results are
> machine-checked in Isabelle/HOL and Lean 4, and bounded TLA+ models of the
> connector protocol are checked with TLC.

Do not shorten this to "Debezium is verified" or "DBLog removes every orphan
row."
