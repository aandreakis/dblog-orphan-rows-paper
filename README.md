# Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC Pipelines

[![Paper (arXiv)](https://img.shields.io/badge/paper-arXiv%3A2611.10810-b31b1b)](https://arxiv.org/abs/2611.10810)
[![Artifact 1.0 DOI](https://img.shields.io/badge/artifact-10.5281%2Fzenodo.24035424-1682D4)](https://doi.org/10.5281/zenodo.24035424)

Sources for the paper **"Extending DBLog-Based Incremental Snapshots to Handle
Orphan Rows in CDC Pipelines"** (Andreas Andreakis, 2026) and the formal
verification artifact that accompanies it.

Applications often keep the same data in several datastores. One is the source.
The others are sinks, such as a search index or a data warehouse, and change
data capture (CDC) keeps them up to date. DBLog-based incremental snapshots, as
adopted by Debezium and Flink CDC, bootstrap a sink by reading the source tables
in chunks interleaved with the log, without blocking writes.

After the bootstrap a sink can drift, when it loses change events or receives
unintended writes. Even a repeated bootstrap can leave orphan rows, which exist
in the sink and no longer at the source. In DBLog's original design each chunk
emits only the latest state of the rows the table still contains, so it does
not handle orphan rows.

The paper extends DBLog to delete them. It uses what a chunk read already
knows, namely the keys that the key range select did not return, and emits a
new kind of event that sinks apply as deletes. It also adds a repair request
that an external process can call with orphan candidates. The connector checks
them with its own read and emits these events only for keys confirmed absent at
the source. This enables three modes:

- **Fully integrated.** Every chunk pass removes the orphans it finds, which
  suits both full and periodic proactive repairs.
- **External drift process.** An external process hands suspected orphans at
  the sink to the connector, which deletes only those confirmed absent.
- **Combined.** Both together. This is what the paper recommends.

The core safety and convergence results are machine-checked in Isabelle/HOL and
Lean 4. The proofs verify the stream-level algorithm under assumptions that the
paper names. They do not verify a running connector. Three bounded TLA+ models
of the connector protocol are checked with the TLC model checker. Model
checking gives evidence. It is not a proof.

**Links:** [paper on arXiv](https://arxiv.org/abs/2611.10810) ·
[archived artifact (Zenodo)](https://doi.org/10.5281/zenodo.24035424) ·
[result index](docs/THEOREMS.md) ·
[provenance](docs/PROVENANCE.md) ·
[AGENTS.md](AGENTS.md) for AI tools

## Repository map

| Path | What it is |
|---|---|
| [paper/](paper/) | Exact arXiv v1 manuscript files, the four figures, and arXiv's stamped PDF. |
| [formal/](formal/) | The complete verification artifact, **byte-identical to Zenodo version 1.0**. Do not edit. |
| [formal/README.md](formal/README.md) | The artifact's own README: contents, every proved statement by name, requirements, reproduction, scope. |
| [formal/lean/README.md](formal/lean/README.md) | The Lean 4 port, with the map from each Isabelle name to its Lean name. |
| [formal/tla/README.md](formal/tla/README.md) | The TLA+ models: invariants, mutations, bounds, known limitations. |
| [docs/THEOREMS.md](docs/THEOREMS.md) | Short index from Section 8 of the paper to the Isabelle theories and theorem names. |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Paper and artifact version history, DOIs, hashes. |
| [AGENTS.md](AGENTS.md) | Guide for AI assistants and automated readers. |

## The paper

- **arXiv v1:** [abstract](https://arxiv.org/abs/2611.10810v1) ·
  [PDF](https://arxiv.org/pdf/2611.10810v1). 15 pages, 4 figures, 2 tables,
  cs.DB + cs.DC + cs.LO, CC BY 4.0.
- **In this repository:** [dblog-orphan-rows.pdf](paper/dblog-orphan-rows.pdf), arXiv's own stamped v1 PDF.
- **Build from source.** The bundle carries `main.bbl`, so BibTeX is not
  required for this exact rebuild. The `acmart` class comes from the TeX
  distribution:

~~~bash
cd paper
pdflatex main
pdflatex main
pdflatex main
~~~

## The proofs

The artifact has three layers with different scopes.

| Layer | Location | Scope |
|---|---|---|
| Isabelle/HOL | [formal/orphan_absence/](formal/orphan_absence/) | The session `Orphan_Absence`, seven theories: safety and convergence from any initial sink state, Flink CDC's buffered range merge, a repair request after or during a pass, in-order at-least-once delivery, the chunk ranges of a pass, and one connector restart. |
| Lean 4 | [formal/lean/](formal/lean/) | A port of every theory of the session except the Flink CDC range merge, which is proved in Isabelle only. |
| TLA+ | [formal/tla/](formal/tla/) | Three bounded models of the connector protocol with 175 TLC configurations. They cover the connector's operational steps, crashes, the visibility gap, the safety cap, the repair request and liveness. |

The session builds on the Generalized DBLog contract core. The three dependency
sessions are included unchanged in [formal/dblog_framework/](formal/dblog_framework/),
[formal/dual_write_layer0/](formal/dual_write_layer0/) and
[formal/formal/](formal/formal/), so that the artifact builds on its own.

Requirements: Isabelle2025-2 for the Isabelle session, the Lean toolchain
pinned in `formal/lean/lean-toolchain` (Lean 4.32.2) for the port, and
OpenJDK 21 with TLC 2.19 for the models. The exact TLC binary and its hash are
named in [formal/tla/README.md](formal/tla/README.md).

Verify the file checksums:

~~~bash
cd formal
shasum -a 256 -c SHA256SUMS
~~~

Check the Isabelle proofs without LaTeX or PDF generation:

~~~bash
cd formal
isabelle build -b -j 8 -o quick_and_dirty=false -o document=false -o document_variants= \
  -d dual_write_layer0 -d formal -d dblog_framework/framework_core -d orphan_absence \
  Orphan_Absence
~~~

The expected result ends with `Finished Orphan_Absence`. Build the Lean port,
which also prints the axiom footprint of every theorem:

~~~bash
cd formal/lean
lake build
~~~

Check one TLC configuration:

~~~bash
cd formal/tla
java -cp /absolute/path/to/tla2tools.jar tlc2.TLC -workers auto -config G7_dense_k3w3c0.cfg AbsenceConnector.tla
~~~

[formal/tla/RUNS.md](formal/tla/RUNS.md) lists every recorded run with its
verdict and state counts. Many configurations are mutations or witnesses that
are built to produce a counterexample. For those, a reported violation is the
expected result.

To check this tree against the archived deposit, run from the repository root:

~~~bash
curl -sL -o artifact.zip https://zenodo.org/records/24035424/files/DBLog_Orphan_Absence_artifact-1.0.zip
unzip -q artifact.zip
diff -r DBLog_Orphan_Absence_artifact-1.0 formal
~~~

No output from `diff` means the trees are identical. Run it before building
the Lean port, because `lake build` writes a `.lake` directory into
`formal/lean/`. Zenodo remains the archival identifier. This repository is a
mirror.

## Versions and DOIs

| | Paper | Verification artifact |
|---|---|---|
| Current | [arXiv:2611.10810v1](https://arxiv.org/abs/2611.10810v1), 7 Nov 2026 | `1.0`, [10.5281/zenodo.24035424](https://doi.org/10.5281/zenodo.24035424), 7 Nov 2026 |
| Previous | none | none |
| Always latest | [arXiv:2611.10810](https://arxiv.org/abs/2611.10810) | [10.5281/zenodo.24035423](https://doi.org/10.5281/zenodo.24035423) (concept DOI) |

The arXiv paper cites the Zenodo version DOI `10.5281/zenodo.24035424`, and this
repository's `formal/` tree is byte-identical to that deposit. Full hashes and
the relationship between the public records:
[docs/PROVENANCE.md](docs/PROVENANCE.md).

## Citing

The paper:

~~~bibtex
@misc{andreakis2026dblog_orphan_rows,
  author        = {Andreas Andreakis},
  title         = {Extending {DBLog}-Based Incremental Snapshots to Handle
                   Orphan Rows in {CDC} Pipelines},
  year          = {2026},
  eprint        = {2611.10810},
  archivePrefix = {arXiv},
  primaryClass  = {cs.DB},
  doi           = {10.48550/arXiv.2611.10810}
}
~~~

The verification artifact:

~~~bibtex
@misc{andreakis2026dblog_orphan_rows_formal,
  author    = {Andreas Andreakis},
  title     = {Formal development for "Extending {DBLog}-Based Incremental
               Snapshots to Handle Orphan Rows in {CDC} Pipelines"},
  year      = {2026},
  publisher = {Zenodo},
  version   = {1.0},
  doi       = {10.5281/zenodo.24035424},
  note      = {Software, BSD 3-Clause License.}
}
~~~

GitHub's **Cite this repository** button reads [CITATION.cff](CITATION.cff).

## Background

- **Generalized DBLog: A Verified Contract for Interleaving Copied Rows with a
  Change Log**, Andreakis, 2026.
  [arXiv:2609.08160](https://arxiv.org/abs/2609.08160) ·
  [repository](https://github.com/aandreakis/generalized-dblog-paper).
  The formal model that the present development builds on.
- **A Theoretical Study of DBLog: Certified Virtual Cuts for a
  Snapshot-Equivalent Replay of Live Databases**, Andreakis, 2026.
  [arXiv:2605.31475](https://arxiv.org/abs/2605.31475) ·
  [repository](https://github.com/aandreakis/dblog-theory-virtual-cuts-paper).
  This is the earlier proof for the original algorithm.
- **DBLog: A Watermark Based Change-Data-Capture Framework**, Andreakis &
  Papapanagiotou, 2020. [arXiv:2010.12597](https://arxiv.org/abs/2010.12597).
  This is the original paper on the mechanism.
- **DBLog: A Generic Change-Data-Capture Framework**, Netflix Tech Blog, 2019.
  [Post](https://netflixtechblog.com/dblog-a-generic-change-data-capture-framework-69351fb9099b).

## Licence

- **Paper text and figures** (`paper/main.tex`, `paper/main.bbl`,
  `paper/refs.bib`, `paper/figures/` and reader documentation): Creative
  Commons Attribution 4.0 International, matching the arXiv posting. See
  [LICENSES/CC-BY-4.0.txt](LICENSES/CC-BY-4.0.txt).
- **Verification artifact** (`formal/`): BSD 3-Clause. See [LICENSE](LICENSE),
  copied from the archived artifact. The dependency sessions inside the
  artifact retain their own licence notices.

## Author

**Andreas Andreakis**, independent researcher ·
[ORCID 0009-0003-9025-9402](https://orcid.org/0009-0003-9025-9402)
