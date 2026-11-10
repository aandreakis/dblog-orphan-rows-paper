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

### Repository payload

The following files under <code>paper/</code> are the payload members of
the public v1 source:

- <code>main.tex</code>
- <code>main.bbl</code>
- <code>refs.bib</code>
- four vector PDFs under <code>figures/</code>

The public source export also supplies an arXiv-generated
<code>00README.json</code>. It is transport metadata and is not part of the
paper payload mirrored here.

The repository PDF <code>paper/dblog-orphan-rows.pdf</code> is arXiv's v1
build, including its margin stamp.

**Public PDF SHA-256:**
<code>e5b44c2b40f5fb4c9342df903bb56134485e585fe61e77d2797bd2569aa1dc9a</code>

The source payload was compared file by file with the public arXiv v1
export on 10 November 2026. Every payload file was identical.

## Verification-artifact record

**Record title:** Formal development for "Extending DBLog-Based Incremental
Snapshots to Handle Orphan Rows in CDC Pipelines"  
**Version:** 1.0  
**Publication date:** 7 November 2026  
**Version DOI:** [10.5281/zenodo.24035424](https://doi.org/10.5281/zenodo.24035424)  
**Concept DOI:** [10.5281/zenodo.24035423](https://doi.org/10.5281/zenodo.24035423)  
**License:** BSD 3-Clause  
**Archive:** <code>DBLog_Orphan_Absence_artifact-1.0.zip</code>

**Archive SHA-256:**
<code>0d6577a7c097c50778e17e6a145b2d09be0aa811a5d6a876e43945a332922047</code>

**Zenodo MD5:**
<code>31004408412472501c6968fbacb16c1e</code>

The extracted archive contains 285 files. They include 55 Isabelle theory
files in four sessions, 7 of them in the session <code>Orphan_Absence</code>,
24 Lean files, 3 TLA+ models with 175 TLC configurations, and the run record
of the models. The extracted tree is mirrored verbatim as
<code>formal/</code>.

The MD5 of the local archive was compared with the checksum that the Zenodo
record publishes for its file on 10 November 2026. They matched, and the
<code>formal/</code> tree was populated from those bytes. The archive's own
<code>SHA256SUMS</code> file verifies all 284 other files of the tree.

## Relationship between the records

The arXiv paper cites the artifact's version DOI
<code>10.5281/zenodo.24035424</code> in its reference list and in the
comments of its arXiv record. The Zenodo record declares itself
<code>isDerivedFrom</code> the formal development of the Generalized DBLog
paper, <code>10.5281/zenodo.22643866</code>. The file
<code>formal/README.md</code> documents that dependency: the three dependency
sessions are byte-identical to the corresponding files of that artifact.

This GitHub repository is not a third archival authority. It is an
information hub that makes the two records easier to inspect together:

- Use arXiv for the paper of record.
- Use the Zenodo version DOI when you need the exact artifact bytes.
- Use the Zenodo concept DOI when a citation should follow future artifact
  versions.
- Use GitHub for browsing and issue discussion.

## Derived files

The following files are derived and are not part of either archived
payload:

- <code>README.md</code>
- <code>AGENTS.md</code>
- <code>docs/</code>
- <code>paper/README.md</code>
- <code>CITATION.cff</code>
