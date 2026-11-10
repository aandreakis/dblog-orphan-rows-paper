# Paper source

This directory mirrors the public arXiv v1 paper payload for:

> Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC Pipelines  
> Andreas Andreakis  
> arXiv:2611.10810v1

## Contents

- <code>main.tex</code> - manuscript source
- <code>main.bbl</code> - frozen bibliography generated for the public build
- <code>refs.bib</code> - bibliography database
- <code>figures/</code> - four vector-PDF figures
- <code>dblog-orphan-rows.pdf</code> - arXiv's stamped 15-page v1 PDF

ArXiv's generated <code>00README.json</code> transport metadata is not
mirrored. Every paper payload member was compared file by file with the
public source export.

## Build

~~~bash
pdflatex main
pdflatex main
pdflatex main
~~~

The source bundle carries <code>main.bbl</code>, so BibTeX is not required
for the exact public rebuild. The <code>acmart</code> class is not part of the
bundle. It comes from the TeX distribution. arXiv built the paper with
TeX Live 2025.

## Public record

- [Abstract](https://arxiv.org/abs/2611.10810v1)
- [PDF](https://arxiv.org/pdf/2611.10810v1)
- [Source](https://arxiv.org/src/2611.10810v1)
- [DOI](https://doi.org/10.48550/arXiv.2611.10810)

The paper text and figures are licensed CC BY 4.0, matching the arXiv
posting.
