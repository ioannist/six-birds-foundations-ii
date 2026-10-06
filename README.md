# Six Birds Foundations II

Companion repository for the paper:

> **Six Birds Foundations II: Admissibility, Meta-Theory, and the Exact-Six Program**
> Ioannis Tsiokos. Preprint, Version 3, October 2, 2026.
> DOI (v3): [10.5281/zenodo.23096828](https://doi.org/10.5281/zenodo.23096828);
> v2 (Qeios, June 9, 2026): [10.32388/A6LBSO](https://doi.org/10.32388/A6LBSO);
> v1 (April 20, 2026): [10.5281/zenodo.19672278](https://doi.org/10.5281/zenodo.19672278)

This repository contains the LaTeX sources and submission artifacts for the
paper, together with a Lean 4 validation track. The authoritative Lean track is
the integrated full project under `lean/full/`; the recovered Aristotle projects
remain available as provenance and partial supporting artifacts.

## Repository layout

```
paper/        LaTeX sources, bibliography, figures, tables, build outputs
lean/         Full Lean project, manifest, validator inputs, recovered artifacts
scripts/      Build and validation helpers
Makefile      Top-level paper build entry points
Aristotle/    Legacy root placeholder; not part of Lean validation
```

## Building the paper

Requires a TeX distribution providing `pdflatex`, `bibtex`, and a flattener
(`latexpand` or `texflatten`). With `latexmk` available the standard build is:

```bash
make paper-build
```

This produces:

- `paper/build/main.pdf` — the compiled paper.
- `paper/build/main_flat.tex` — a flattened single-file source suitable for
  arXiv submission.

To produce the Qeios single-file bundle (single `.tex`, single PDF, source
zip) under `paper/build/qeios_single/`:

```bash
make paper-qeios
```

To clean build outputs:

```bash
make paper-clean
make paper-qeios-clean
```

## Lean validation

The full integrated Lean project lives under [`lean/full/`](lean/full/). It
exports the `SixBirds` module family and backs all paper-label entries in
[`lean/manifest.toml`](lean/manifest.toml). The manifest currently covers all
16 paper definitions and all 35 theorem/proposition claims with full
`definition` or `theorem` statuses.

Run the full strict validator with:

```bash
./scripts/validate_lean.sh --require-full
```

The explicit full-tier form is also supported:

```bash
./scripts/validate_lean.sh --tier full --require-full
```

For machine-readable output:

```bash
./scripts/validate_lean.sh --tier full --require-full --json /tmp/lean-validation.json
```

Strict validation distinguishes kernel-checked declaration coverage from the
semantically hardened full mechanization. In addition to builds, declaration
probes, declaration-kind checks, theorem axiom audits, and placeholder scans, it
rejects vacuous manifest-backed definitions such as public `:= True` stubs,
all-purpose classifiers, and trivial well-formedness predicates.

The JSON report includes per-entry build, declaration-probe, declaration-kind,
axiom-audit, placeholder-scan, and semantic-audit status, plus aggregate
semantic-audit totals. CI runs both the recovered partial track and the strict
full-mechanization track.

The recovered partial track can still be checked directly:

```bash
./scripts/validate_lean.sh --tier recovered
```

## Citation

```bibtex
@misc{tsiokos2026sixbirds2,
  author = {Tsiokos, Ioannis},
  title  = {Six Birds Foundations II: Admissibility, Meta-Theory, and the Exact-Six Program},
  year   = {2026},
  doi    = {10.5281/zenodo.23096828},
  note   = {Preprint, Version 3}
}
```
