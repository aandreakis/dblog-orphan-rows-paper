# Provenance

This repository joins two public records without changing their contents:
the arXiv paper and the Zenodo verification artifact.

## Paper record

**Title:** Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC Pipelines  
**Author:** Andreas Andreakis  
**arXiv:** [2611.10810](https://arxiv.org/abs/2611.10810)  
**arXiv DOI:** [10.48550/arXiv.2611.10810](https://doi.org/10.48550/arXiv.2611.10810)  
**Current version:** v1, 7 November 2026  
**Subjects:** cs.DB, cs.DC, cs.LO  
**License:** CC BY 4.0  
**Extent:** 15 pages, 4 figures, 2 tables

### Version history

| Version | Date | Public record |
|---|---|---|
| v1 | 7 Nov 2026 | [arXiv:2611.10810v1](https://arxiv.org/abs/2611.10810v1) |

### Paper files in this repository

The following files under `paper/` come from the public arXiv v1
source bundle:

- `main.tex`
- `main.bbl`
- `refs.bib`
- four vector PDFs under `figures/`

The public bundle also contains `00README.json`, a file that arXiv
generates. It is not part of the paper and is not copied here.

The repository PDF `paper/dblog-orphan-rows.pdf` is arXiv's v1
build, including its margin stamp.

**Public PDF SHA-256:**
`e5b44c2b40f5fb4c9342df903bb56134485e585fe61e77d2797bd2569aa1dc9a`

The source files were compared with the public arXiv v1 bundle on
10 November 2026. Every file matched byte for byte.

## Verification-artifact record

**Record title:** Formal development for "Extending DBLog-Based Incremental
Snapshots to Handle Orphan Rows in CDC Pipelines"  
**Version:** 1.0  
**Publication date:** 7 November 2026  
**Version DOI:** [10.5281/zenodo.24035424](https://doi.org/10.5281/zenodo.24035424)  
**Concept DOI:** [10.5281/zenodo.24035423](https://doi.org/10.5281/zenodo.24035423)  
**License:** BSD 3-Clause  
**Archive:** `DBLog_Orphan_Absence_artifact-1.0.zip`

**Archive SHA-256:**
`0d6577a7c097c50778e17e6a145b2d09be0aa811a5d6a876e43945a332922047`

**Zenodo MD5:**
`31004408412472501c6968fbacb16c1e`

The extracted archive contains 285 files. They include 55 Isabelle theory
files in four sessions, 7 of them in the session `Orphan_Absence`,
24 Lean files, 3 TLA+ models with 175 TLC configurations, and the run record
of the models. The extracted tree is copied unchanged as
`formal/`.

The MD5 of the local archive was compared with the checksum that the Zenodo
record publishes for its file on 10 November 2026. They matched, and
`formal/` was unpacked directly from that archive. The archive's own
`SHA256SUMS` file verifies all 284 other files of the tree.

## Relationship between the records

The arXiv paper cites the artifact's version DOI
`10.5281/zenodo.24035424` in its reference list and in the
comments of its arXiv record. The Zenodo record declares itself
`isDerivedFrom` the formal development of the Generalized DBLog
paper, `10.5281/zenodo.22643866`. The file
`formal/README.md` documents that dependency: the three dependency
sessions are byte-identical to the corresponding files of that artifact.

This GitHub repository brings the paper and the artifact together in one
place. It is not a separate archival record:

- Use arXiv for the paper of record.
- Use the Zenodo version DOI when you need the exact artifact bytes.
- Use the Zenodo concept DOI when a citation should follow future artifact
  versions.
- Use GitHub for browsing and issue discussion.

## Files written for this repository

The following files were written for this repository and are not part of
either archived record:

- `README.md`
- `AGENTS.md`
- `docs/`
- `paper/README.md`
- `CITATION.cff`
