# Paper source

This directory holds the source files of the public arXiv v1 bundle for:

> Extending DBLog-Based Incremental Snapshots to Handle Orphan Rows in CDC Pipelines  
> Andreas Andreakis  
> arXiv:2611.10810v1

## Contents

- `main.tex`: manuscript source
- `main.bbl`: bibliography as generated for the public build
- `refs.bib`: bibliography database
- `figures/`: four vector-PDF figures
- `dblog-orphan-rows.pdf`: arXiv's stamped 15-page v1 PDF

The `00README.json` file that arXiv generates is not copied here.
Every source file matches the public arXiv v1 bundle byte for byte.

## Build

~~~bash
pdflatex main
pdflatex main
pdflatex main
~~~

The source bundle carries `main.bbl`, so BibTeX is not required
for the exact public rebuild. The `acmart` class is not part of the
bundle and comes from the TeX distribution. The arXiv build used TeX Live 2025.

## Public record

- [Abstract](https://arxiv.org/abs/2611.10810v1)
- [PDF](https://arxiv.org/pdf/2611.10810v1)
- [Source](https://arxiv.org/src/2611.10810v1)
- [DOI](https://doi.org/10.48550/arXiv.2611.10810)

The paper text and figures are licensed CC BY 4.0, matching the arXiv
posting.
