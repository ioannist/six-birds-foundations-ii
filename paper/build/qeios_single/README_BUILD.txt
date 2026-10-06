README_BUILD.txt
================
Six Birds Foundations II: Admissibility, Meta-Theory, and the Exact-Six Program
Ioannis Tsiokos <ioannis@automorph.io>

Build instructions for the Qeios source bundle
-----------------------------------------------

OPTION A: Single-file build (recommended, no BibTeX needed)

    pdflatex qeios_single.tex
    pdflatex qeios_single.tex

  Two passes are needed for cross-references. No .bib file is required;
  the bibliography is embedded in the .tex file.

OPTION B: Full modular build

    make paper-build

  This writes the canonical manuscript outputs to:

    paper/build/main.pdf
    paper/build/main_flat.tex

  The modular build requires:
  - `paper/bib/references.bib`
  - all files under `paper/sections/`
  - all files under `paper/figures/` and `paper/tables/`

OPTION C: Generate all Qeios-ready assets

    make paper-qeios

  This produces:

    paper/build/qeios_single/qeios_single.tex
    paper/build/qeios_single/qeios_single.pdf
    paper/build/qeios_single/qeios_source_bundle.zip
    paper/build/qeios_single/Qeios_Submission_Notes.md
    paper/build/qeios_single/README_BUILD.txt

Files in this bundle
--------------------
  qeios_single.tex                         Self-contained single-file TeX
  qeios_single.pdf                        Pre-built PDF from qeios_single.tex
  qeios_source_bundle.zip                 Source bundle for upload / archive
  Qeios_Submission_Notes.md               Copy/paste submission metadata
  main.tex                                Modular main TeX
  macros.tex                              Shared macro definitions
  build/main.bbl                          Pre-built BibTeX output
  bib/references.bib                      BibTeX database
  sections/*.tex                          Section files
  figures/*.tex                           Figure source files
  tables/*.tex                            Table source files

Requirements
------------
  - pdflatex (TeX Live 2022 or later recommended)
  - latexmk recommended for the modular build
  - latexpand or texflatten for the flattened export
  - zip for the source-bundle archive
  - Standard packages used by `paper/main.tex`
  - Optional: orcidlink (fallback provided in `qeios_single.tex`)
