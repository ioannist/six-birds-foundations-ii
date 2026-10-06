# Lean Validation Track

This directory contains the Lean validation assets for the paper. The
authoritative track is the integrated full Lean project in `lean/full/`.
Recovered Aristotle projects remain under `lean/recovered/` as provenance and
partial supporting evidence.

## Layout

```text
lean/
├── full/
├── manifest.toml
├── recovered/
│   ├── substantive/
│   └── skeletons/
└── .validate-logs/
```

- `full/` contains the integrated `SixBirds` Lake project.
- `recovered/substantive/` contains recovered Aristotle-generated Lean projects
  with axiom-free, sorry-free supporting proofs.
- `recovered/skeletons/` contains small axiomatic or partial projects recovered
  from Aristotle result snapshots.
- `manifest.toml` maps every paper definition, theorem, and proposition label
  to a declaration exported by the full project.
- `full/SixBirds/SemanticTests.lean` contains regression checks showing that
  malformed records, generic transitions, generic paths, unresolved residuals,
  and inactive channels do not satisfy the hardened predicates.

## Validation

From the repository root:

```bash
./scripts/validate_lean.sh --require-full
./scripts/validate_lean.sh --tier full --require-full
./scripts/validate_lean.sh --tier full --require-full --json /tmp/lean-validation.json
```

Validation builds the selected Lean projects, checks manifest coverage against
the paper labels, probes each Lean declaration with an import plus `#check`,
checks the Lean declaration kind, scans active Lean sources for proof
placeholders, and audits theorem dependencies against
[`trust_base.txt`](trust_base.txt).

Strict full validation also runs a semantic audit over manifest-backed full
sources. This audit is intentionally separate from Lean kernel checking: it
rejects public vacuity patterns such as `:= True`/`:= False` definition stubs,
`WellFormed... := True`, and all-purpose residual classifiers. The JSON output
records aggregate semantic-audit totals and per-entry `semantic_check` fields.

The recovered track remains available:

```bash
./scripts/validate_lean.sh --tier recovered
```

Strict full-mechanization validation rejects any paper definition or
theorem/proposition claim whose manifest status is `unformalized`, `partial`,
or `axiomatic`. It also fails if the semantic audit reports a finding. The
current manifest has zero non-full entries and strict validation passes with
zero semantic-audit findings.
