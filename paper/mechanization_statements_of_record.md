# Mechanization statements of record — Foundations II companion-form disclosure

**Source of truth for the companion-form footnotes (Phase 3) and the App-D disclosure table.**
Generated in Phase 1 of the paper reshape from an adversarially-verified per-claim Lean fidelity audit
(8 per-module classifiers, each followed by an independent skeptic instructed to *downgrade* every
"verified in Lean" claim and default to the conservative wording when uncertain).

**Revision — 2026-06-02:** incorporates the Phase 1 external review. Two downgrades
(`prop:dependency-stress` schema; `prop:residual-stress` trivial/vacuous) and four footnote
corrections (`prop:probability-closure`, `prop:causality-closure`, `prop:agency-closure`,
`thm:upper-bound-classification` lose "Modeled/models"; `prop:non-uniqueness` discloses the
missing well-formedness condition). The reviewer confirmed: zero faithful derivations, correct
decl mappings, the §6 trivial flags, and notation grounding. No Lean or manifest change required.

## Frozen-Lean invariant

No Lean source and no `lean/manifest.toml` row is modified by the reshape. The mechanization is frozen;
this file records what that frozen mechanization *actually* establishes, so that body footnotes and the
App-D table describe it without over- or under-claiming. The Lean validation track (`scripts/validate_lean.sh`) is unaffected.

## Audit summary

| Fidelity class | Count | Companion-form footnote tier |
| --- | ---: | --- |
| Narrowed / parametric | 9 | "establishes this for <case> under parametric hypotheses …" |
| Schema (projection) | 20 | "tracked in the formalization harness as a conditional schema …" (never "verified"/"proves") |
| Trivial / vacuous  [!] | 6 | footnote openly discloses the triviality (never "verified"/"proves") |
| Definitional mirror | 16 | "Realized in Lean as …" (definitions) |
| **Total** | **51** | |

**Zero claims qualify as faithful derivations.** Every paper claim is narrowed/parametric, a projection
schema, trivial, or (for definitions) a typed mirror. The manifest's uniform `status = "theorem"` / `"Full
integrated Lean track."` does **not** reflect these distinctions and must not be the source for footnote wording.

## Science-risk flags (trivial / vacuous Lean backing)

6 claims carry trivial/vacuous Lean backing and receive the most cautious footnotes. Five are the §6
upper-bound "no seventh role" machinery, whose Lean backing is `True` by construction over a hand-built total
classifier rather than derived from feature content; `prop:residual-stress` (§8) re-asserts that same
classifier-by-construction fact inside the integrated-stress suite.

- **`prop:level-profile`** (Level-profile architecture.) — HasLevelProfile is the full disjunction over all three Level constructors (Admissibility.lean 29-30); hypothesis h is bound and unused, cases level <;> simp (82-87) holds for every record — all-absorbing classifier, vacuous.
- **`prop:probability-closure`** (Closure of probability and uncertainty.) — Proof `intro D; exact True.intro` over the hand-built `rawRecord 0 RawKind.probability`; `classifyResidual` maps it to `composite` (UpperBound.lean:7) and `CoveredResidualClass composite = True` (FATCD.lean:153), so the goal is definitionally `True` and cannot fail; not the paper's universal closure.  [Adjusted in Phase 1 external review, 2026-06-02.]
- **`prop:causality-closure`** (Closure of residual causality.) — Proof `intro D; exact True.intro` over `rawRecord 0 RawKind.causality`; `classifyResidual` -> `composite` (UpperBound.lean:8), `CoveredResidualClass composite = True` (FATCD.lean:153); the P5-inadmissibility caveat in the paper is unmechanized and the goal is vacuous `True`.  [Adjusted in Phase 1 external review, 2026-06-02.]
- **`prop:agency-closure`** (Closure of residual agency.) — Proof `intro D; exact True.intro` over `rawRecord 0 RawKind.agency`; `classifyResidual` -> `empiricalBridgeAnnotation` (UpperBound.lean:9), `CoveredResidualClass empiricalBridgeAnnotation = True` (FATCD.lean:158); single fixed record, vacuous `True`, P1-inadmissibility caveat unmechanized.  [Adjusted in Phase 1 external review, 2026-06-02.]
- **`thm:upper-bound-classification`** (Upper-bound classification.) — Proof `intro D r; exact classifyResidual_covered r` with lemma `cases kind <;> exact True.intro`; all 23 branches of `classifyResidual` (UpperBound.lean:7-29) emit only covered classes and the tokens `unresolvedThreat`/`genuineSeventhRole` never appear in its body, so `CoveredResidualClass` is `True` by construction; 'no seventh role' is tautological, not derived from feature content as the paper's enumeration outline does.  [Adjusted in Phase 1 external review, 2026-06-02.]
- **`prop:residual-stress`** (Upper-bound residual stress.) — `unresolved_and_genuine_seventh_empty` (UpperBound.lean:66-78) uses `classifyResidual_covered` (cases over all 23 RawKinds, UpperBound.lean:34-38) and `CoveredResidualClass _Threat = False` to close by `exact covered : False` — a genuine exhaustive proof, but over a total classifier authored never to emit the two threat classes and with `_D` vacuous, so narrowed_parametric stands (not projection, not vacuous-True).  [Adjusted in Phase 1 external review, 2026-06-02.]

## Per-claim records

### §2 — Primitive role architecture

#### `def:primitive-roles` — Primitive closure roles P1 through P6.
- **Body location:** §2 (definition)
- **Lean decl:** `SixBirds.Role`  (module `Roles`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.Role} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** Role is a bare six-constructor inductive (lines 3-10); the paper's per-role semantics live only as free-form strings in RoleMeaning (lines 17-23), so it is a faithful structural mirror of the six labels, not vacuous and not over-claimed.

#### `def:level-trichotomy` — Behavioral, verification, and structural-categorical levels.
- **Body location:** §2 (definition)
- **Lean decl:** `SixBirds.Level`  (module `Roles`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.Level} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** Level is a three-constructor inductive (lines 25-29); the lossy-forgetting/non-unique-lifting dynamics of the paper Definition (lines 103-106) are absent from the type, so this is a faithful mirror of the three named levels only.

#### `def:selected-lift-atlas` — Selected-lift atlas for the six roles.
- **Body location:** §2 (definition)
- **Lean decl:** `SixBirds.SelectedLiftAtlas`  (module `Roles`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.SelectedLiftAtlas} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** SelectedLiftAtlas (lines 48-51) is a typed structure ranging over all six roles, but the paper's rich per-role lift data (lines 178-193) collapses to a single addedData : String field (line 46); the manifest points at the structure type, so definitional_mirror with schematic role-data is correct, not an over-claim.

#### `prop:boundary-distinctions` — Boundary distinctions under scoped bookkeeping.
- **Body location:** §2 (proposition)
- **Lean decl:** `SixBirds.boundary_distinctions`  (module `Roles`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.boundary_distinctions}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** ForbiddenCollapse r s is DEFINED as r != s (lines 70-71) and the theorem is proven by `intro r s h; exact h` (lines 73-76), returning the hypothesis unchanged; the repaired alignments and FATCD honest-bookkeeping the paper invokes (lines 147-153) appear nowhere, so it restates rather than derives.

### §3 — Admissibility and meta-theory

#### `prop:honest-bookkeeping` — Honest bookkeeping is an admissibility regime.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.honest_bookkeeping_admissibility`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.honest_bookkeeping_admissibility}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** AdmissibleClaim c := HonestBookkeeping c (Admissibility.lean 26-27); proof is intro c h; exact h (72-75), the identity on the same Prop — the rubric's named projection_or_schema example.

#### `prop:typed-non-collapse` — Typed non-collapse.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.typed_non_collapse`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.typed_non_collapse}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** ForbiddenCollapse r s := r ≠ s (Roles.lean 70-71); proof intro r s h; exact h (Admissibility.lean 77-80) repackages the hypothesis as conclusion; no boundary matrix or bookkeeping enters.

#### `prop:level-profile` — Level-profile architecture.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.level_profile`  (module `Admissibility`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean statement \texttt{SixBirds.level_profile} records only that every claim record falls under one of the three levels (a disjunction over the level enumeration); the honest-bookkeeping hypothesis is unused and the translation-record/inadmissibility content of this proposition is not mechanized. The triviality is disclosed in Appendix~\ref{app:mechanization}.
- **Audit evidence:** HasLevelProfile is the full disjunction over all three Level constructors (Admissibility.lean 29-30); hypothesis h is bound and unused, cases level <;> simp (82-87) holds for every record — all-absorbing classifier, vacuous.

#### `prop:forgetting-lifts` — Forgetting and selected-lift architecture.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.forgetting_lifts`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.forgetting_lifts}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Proof returns proof-fields selectedLiftAtlas.selected/nonUnique (Admissibility.lean 89-93) baked into the atlas where selectedLift sets selected:=true, nonUnique:=true (Roles.lean 57-58); pure field projection over a hand-built record.

#### `prop:activation-thresholds` — Activation thresholds.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.activation_thresholds`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.activation_thresholds}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Conclusion is ⟨p.attachment.thresholdIsDeclared, p.attachment.auditRecorded⟩ (Admissibility.lean 95-100), two field accessors of ThresholdAttachment (FATCD.lean 115,122); nothing constructed despite arbitrary D,r,p.

#### `prop:visibility` — Instrument-relative visibility.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.visibility`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.visibility}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** exact ⟨rfl, rfl⟩ over the hand-built standardClaimRecord whose visibilityRecorded:=true and instrument:=some 1 (Admissibility.lean 63,65) were preset to make HasVisibilityRecord hold; hypothesis h unused, single fixed record.

#### `prop:empirical-bridge` — Empirical-bridge admissibility.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.empirical_bridge`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.empirical_bridge}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** exact ⟨⟨rfl, rfl⟩, rfl⟩ over standardClaimRecord and standardNonclaims with preset fields empiricalBridgeRecorded:=true, instrument:=some 1, noEmpiricalRealization:=true (Admissibility.lean 64-70); hypothesis unused.

#### `prop:nonclaim-closure` — Admissibility-regime nonclaim closure.
- **Body location:** §3 (proposition)
- **Lean decl:** `SixBirds.nonclaim_closure`  (module `Admissibility`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.nonclaim_closure}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** exact ⟨rfl, rfl, rfl⟩ (Admissibility.lean 115-119) over standardNonclaims whose three boolean fields are all preset true (67-70); no quantification, no hypothesis — reads back preset flags.

### §4 — The FATCD domain

#### `def:raw-record` — Raw record.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.RawRecord`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.RawRecord} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** RawRecord (lines 31-36) over RawKind (lines 5-29) is a non-vacuous typed structure enumerating Def 4.1 kinds plus five extras; faithful definitional mirror, not trivial.

#### `def:annotations` — Annotation kinds.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.AnnotationKind`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.AnnotationKind} (Appendix~\ref{app:mechanization}); the Lean enumeration additionally carries the audit, claim, promotion, translation, nonclaim, witness, and collapse kinds used by the bookkeeping machinery.
- **Audit evidence:** AnnotationKind (lines 38-52) contains the six Def 4.2 kinds (level/threshold/lift/forget/visibility/bridge) plus seven bookkeeping kinds; faithful superset mirror, not vacuous.

#### `def:finite` — Finite description.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.FiniteDescription`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.FiniteDescription} (Appendix~\ref{app:mechanization}); the Lean condition is carried by a per-record finiteness flag rather than the full clause list of Definition~\ref{def:finite}.
- **Audit evidence:** FiniteDescription (lines 77-79) requires r.finiteFields = true and a.finiteFields = true for all records/annotations; a real (non-True) constraint, narrowed to a flag but not vacuous.

#### `def:closed` — Closed description.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.ClosedDescription`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.ClosedDescription} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** ClosedDescription (lines 81-83) enforces HasRawId resolution of every record ref and every annotation target/ref; a substantive reference-closure predicate, not vacuous.

#### `def:audited` — Audited description.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.AuditedDescription`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.AuditedDescription} (Appendix~\ref{app:mechanization}); the Lean predicate only requires the presence of audit, claim, and nonclaim annotation kinds and does not encode the per-claim bookkeeping discipline of Definition~\ref{def:audited}.
- **Audit evidence:** AuditedDescription (lines 85-88) is the conjunction of three HasAnnotationKind existentials; a weakened but non-vacuous mirror (not defined as True), so definitional_mirror survives, not trivial_or_vacuous.

#### `def:fatcd` — Finite audited typed closure description.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.FATCD`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.FATCD} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** FATCD (lines 90-94) bundles a Description with proofs of FiniteDescription/ClosedDescription/AuditedDescription, faithfully mirroring Def 4.6 and inheriting the component narrowings.

#### `def:threshold-attachment` — Threshold attachment.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.ThresholdAttachment`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.ThresholdAttachment} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** ThresholdAttachment (lines 109-122) carries proof fields for a nonempty cluster drawn from D, a declared threshold targeting a cluster record, a declared witness, plus existential collapse/audit; substantive structure, not vacuous.

#### `def:role-projection` — Derived role projection.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.DerivedRoleProjection`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.DerivedRoleProjection} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** DerivedRoleProjection (lines 127-133) carries a ThresholdAttachment plus AlignedProjection (lines 124-125), a real per-role-kind containment constraint over roleRawKinds (98-104); substantive mirror, not vacuous.

#### `def:residual-scheme` — Residual feature and residual classification scheme.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.ResidualClassificationScheme`  (module `FATCD`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.ResidualClassificationScheme} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** ResidualClassificationScheme (line 149) aliases the eleven-constructor ResidualClass inductive (lines 135-147) matching labels (i)-(xi) of Def 4.10; faithful declarative mirror, and CoveredResidualClass marks (x)/(xi) as False per the deferral.

#### `def:scoped-exact-six-question` — Scoped exact-six question over FATCD.
- **Body location:** §4 (definition)
- **Lean decl:** `SixBirds.ScopedExactSixQuestion`  (module `ScopedExactSix`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.ScopedExactSixQuestion} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** ScopedExactSix.lean:5-9 is a typed Prop (not := True) mirroring the theorem shape (forall D, exists dec, WellFormed and SixChannels and residual-coverage), but narrowed: it drops per-channel lower-bound activation and the active-projection support clauses, and ties exhaustion to the synthetic dec.classify rather than D's raw records; a faithful structural mirror, not vacuous.

#### `prop:non-circularity` — Non-circularity schema for FATCD.
- **Body location:** §4 (proposition)
- **Lean decl:** `SixBirds.non_circularity`  (module `FATCD`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.non_circularity}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** non_circularity (lines 423-427) proof is 'intro D; exact ⟨D.finite, D.closed, D.audited⟩', a pure projection re-extracting the three FATCD record fields; it does not derive the meta-content of Prop 4.11, correctly projection_or_schema.

#### `prop:non-overbreadth` — Non-overbreadth schema for FATCD.
- **Body location:** §4 (proposition)
- **Lean decl:** `SixBirds.non_overbreadth`  (module `FATCD`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.non_overbreadth}); see Appendix~\ref{app:mechanization}. The Lean declaration is identical in statement and proof to \texttt{SixBirds.non_circularity} and re-extracts the admissibility fields of the record rather than establishing the structural-restriction content of the proposition.
- **Audit evidence:** non_overbreadth (lines 429-433) is byte-for-byte identical in statement and proof to non_circularity (same field projection ⟨D.finite, D.closed, D.audited⟩); it captures none of Prop 4.12's restrictiveness content, correctly projection_or_schema and must not be called Lean-verified.

### §5 — Six-role lower bounds

#### `def:common-witness-data` — Common witness data for role Pi.
- **Body location:** §5 (definition)
- **Lean decl:** `SixBirds.CommonWitnessData`  (module `LowerBounds`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.CommonWitnessData} (Appendix~\ref{app:mechanization}); the explicit nonclaim record is mirrored there only as a boolean flag.
- **Audit evidence:** LowerBounds.lean:5-14: structure mirrors the paper tuple with genuine proof-carrying fields (FiniteDescription/ClosedDescription/AuditedDescription/DerivedRoleProjection), but n_i is degraded to nonclaimRecord:Bool and W_i has no typed field (folded into ThresholdAttachment.witness); a faithful-but-weakened mirror, not vacuous.

#### `thm:six-role-lower-bounds` — Six-role lower bounds.
- **Body location:** §5 (theorem)
- **Lean decl:** `SixBirds.six_role_lower_bounds`  (module `LowerBounds`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.six\_role\_lower\_bounds}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** LowerBounds.lean:27-32: existential witness is the prebuilt commonWitnessData role and the Nonempty goal is discharged by the pure field accessor (commonWitnessData role).projection, whose field was set to roleProjection role precisely to make it hold; a projection over a prebuilt record, not a derivation.

#### `prop:p1-witness` — P1 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p1_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P1} under parametric hypotheses (alignment, threshold attachment, and finite/closed/audited verifications of that fixed witness); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p1\_witness}).
- **Audit evidence:** LowerBounds.lean:34-36 exhibits the single hand-built witnessDescription Role.P1 (FATCD.lean:182-183) with roleProjection; the aligned field is the non-vacuous AlignedProjection (FATCD.lean:124-125, refuted by generic_semantics_not_p1 at 414) genuinely proved over the cluster hand-built to contain object/relation/map/comparison, so a real proof of a single concrete surrogate, not the prose's general existence over FATCD.

#### `prop:p2-witness` — P2 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p2_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P2} under parametric hypotheses (alignment, threshold attachment, and finite/closed/audited verifications of that fixed witness); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p2\_witness}).
- **Audit evidence:** LowerBounds.lean:38-40 supplies one fixed witnessDescription Role.P2 (roleRaw P2 = predicate/relation/comparison, FATCD.lean:184-185); roleRaw_aligned (343-351) genuinely discharges the non-vacuous AlignedProjection over the hand-built cluster; genuine proof over a single concrete witness, not full generality.

#### `prop:p3-witness` — P3 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p3_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P3} under parametric hypotheses (alignment, threshold attachment, and finite/closed/audited verifications of that fixed witness); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p3\_witness}).
- **Audit evidence:** LowerBounds.lean:42-44 exhibits one fixed witnessDescription Role.P3 (roleRaw P3 = path/comparison, FATCD.lean:186); AlignedProjection over [path,comparison] genuinely proved and non-vacuous (generic_transition_not_p3, FATCD.lean:396); single concrete surrogate for the prose's general existential.

#### `prop:p4-witness` — P4 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p4_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P4} under parametric hypotheses (alignment, threshold attachment, and finite/closed/audited verifications of that fixed witness; the attached level is fixed to the verification level rather than the structural-categorical level of the prose); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p4\_witness}).
- **Audit evidence:** LowerBounds.lean:46-48 exhibits one fixed witnessDescription Role.P4 (roleRaw P4 = index/transition/refinement, FATCD.lean:187-188); thresholdAttachment fixes level:=Level.verification for all roles (FATCD.lean:372) while the prose assigns P4 the structural-categorical level (05_lower_bounds.tex:190), so an additional narrowing beyond the single concrete witness; genuine proof, narrowed.

#### `prop:p5-witness` — P5 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p5_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P5} under parametric hypotheses (alignment over the same raw-kind cluster used for P1, threshold attachment, and finite/closed/audited verifications of that fixed witness); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p5\_witness}).
- **Audit evidence:** LowerBounds.lean:50-52 exhibits one fixed witnessDescription Role.P5; roleRawKinds P5 = roleRawKinds P1 = object/relation/map/comparison (FATCD.lean:99,103), so the kind-level AlignedProjection does not distinguish the P5 packaging witness from the P1 descent-obstruction witness; the distinguishing packaging content is unchecked, making this a narrowed single-witness proof, not faithful generality.

#### `prop:p6-witness` — P6 lower-bound witness.
- **Body location:** §5 (proposition)
- **Lean decl:** `SixBirds.p6_witness`  (module `LowerBounds`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for one concrete description \texttt{witnessDescription Role.P6} under parametric hypotheses (alignment over event/provenance/replay/check records, threshold attachment, and finite/closed/audited verifications of that fixed witness); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.p6\_witness}).
- **Audit evidence:** LowerBounds.lean:54-56 exhibits one fixed witnessDescription Role.P6 (roleRaw P6 = event/provenance/replay/check, FATCD.lean:191-192); AlignedProjection checks only kind-presence of those four records, so the prose's 'beyond passive logs' nonclaim is only an annotation-presence requirement; a genuine proof over a single concrete surrogate, not the general existential.

### §6 — Upper-bound classification

#### `prop:alignment-rules` — Role-projection alignment.
- **Body location:** §6 (proposition)
- **Lean decl:** `SixBirds.alignment_rules`  (module `UpperBound`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.alignment_rules}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Proof `intro D role p; exact p.aligned` is a pure field projection: the goal `AlignedProjection role p.attachment.cluster` is exactly the type of `DerivedRoleProjection.aligned` (FATCD.lean:129), and `AlignedProjection` (FATCD.lean:124-125) is only a kind-presence check, far weaker than the paper's per-role witness constraints.

#### `prop:probability-closure` — Closure of probability and uncertainty.
- **Body location:** §6 (proposition)
- **Lean decl:** `SixBirds.probability_closure`  (module `UpperBound`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean declaration is a trivial single-record harness check: \texttt{classifyResidual} maps \texttt{RawKind.probability} to \texttt{composite}, whose \texttt{CoveredResidualClass} branch is \texttt{True}; it does not establish the paper's universal probability/uncertainty closure. See Appendix~\ref{app:mechanization} (\texttt{SixBirds.probability\_closure}).
- **Audit evidence:** Proof `intro D; exact True.intro` over the hand-built `rawRecord 0 RawKind.probability`; `classifyResidual` maps it to `composite` (UpperBound.lean:7) and `CoveredResidualClass composite = True` (FATCD.lean:153), so the goal is definitionally `True` and cannot fail; not the paper's universal closure.  [Adjusted in Phase 1 external review, 2026-06-02.]

#### `prop:causality-closure` — Closure of residual causality.
- **Body location:** §6 (proposition)
- **Lean decl:** `SixBirds.causality_closure`  (module `UpperBound`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean declaration is a trivial single-record harness check: \texttt{classifyResidual} maps \texttt{RawKind.causality} to \texttt{composite}, whose \texttt{CoveredResidualClass} branch is \texttt{True}; the \Pfive{}-inadmissibility content of the proposition is absent and no universal residual-causality closure is established. See Appendix~\ref{app:mechanization} (\texttt{SixBirds.causality\_closure}).
- **Audit evidence:** Proof `intro D; exact True.intro` over `rawRecord 0 RawKind.causality`; `classifyResidual` -> `composite` (UpperBound.lean:8), `CoveredResidualClass composite = True` (FATCD.lean:153); the P5-inadmissibility caveat in the paper is unmechanized and the goal is vacuous `True`.  [Adjusted in Phase 1 external review, 2026-06-02.]

#### `prop:agency-closure` — Closure of residual agency.
- **Body location:** §6 (proposition)
- **Lean decl:** `SixBirds.agency_closure`  (module `UpperBound`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean declaration is a trivial single-record harness check: \texttt{classifyResidual} maps \texttt{RawKind.agency} to \texttt{empiricalBridgeAnnotation}, whose \texttt{CoveredResidualClass} branch is \texttt{True}; the \Pone{}-inadmissibility content is absent and no universal residual-agency closure is established. See Appendix~\ref{app:mechanization} (\texttt{SixBirds.agency\_closure}).
- **Audit evidence:** Proof `intro D; exact True.intro` over `rawRecord 0 RawKind.agency`; `classifyResidual` -> `empiricalBridgeAnnotation` (UpperBound.lean:9), `CoveredResidualClass empiricalBridgeAnnotation = True` (FATCD.lean:158); single fixed record, vacuous `True`, P1-inadmissibility caveat unmechanized.  [Adjusted in Phase 1 external review, 2026-06-02.]

#### `thm:upper-bound-classification` — Upper-bound classification.
- **Body location:** §6 (theorem)
- **Lean decl:** `SixBirds.upper_bound_classification`  (module `UpperBound`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean declaration is a classifier-by-construction check: every \texttt{RawKind} branch of \texttt{classifyResidual} lands in a class whose \texttt{CoveredResidualClass} branch is \texttt{True}, and the uncovered constructors \texttt{unresolvedThreat}/\texttt{genuineSeventhRole} are never produced; ``no seventh role'' holds by construction rather than by derivation from feature content. See Appendix~\ref{app:mechanization} (\texttt{SixBirds.upper\_bound\_classification}).
- **Audit evidence:** Proof `intro D r; exact classifyResidual_covered r` with lemma `cases kind <;> exact True.intro`; all 23 branches of `classifyResidual` (UpperBound.lean:7-29) emit only covered classes and the tokens `unresolvedThreat`/`genuineSeventhRole` never appear in its body, so `CoveredResidualClass` is `True` by construction; 'no seventh role' is tautological, not derived from feature content as the paper's enumeration outline does.  [Adjusted in Phase 1 external review, 2026-06-02.]

### §7 — Decomposition and exhaustion

#### `def:channel-status` — Channel status.
- **Body location:** §7 (definition)
- **Lean decl:** `SixBirds.ChannelStatus`  (module `Decomposition`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.ChannelStatus} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** ChannelStatus is a payload-free 5-constructor inductive (Decomposition.lean:5-11) one-to-one with the five paper statuses, made genuinely distinct by deriving DecidableEq; a faithful enum mirror.

#### `def:decomposition-record` — Decomposition/exhaustion record.
- **Body location:** §7 (definition)
- **Lean decl:** `SixBirds.DecompositionRecord`  (module `Decomposition`)
- **Fidelity:** Definitional mirror
- **Footnote (proposed):** Realized in Lean as \texttt{SixBirds.DecompositionRecord} (Appendix~\ref{app:mechanization}).
- **Audit evidence:** DecompositionRecord (Decomposition.lean:13-20) is a typed structure mirroring the paper tuple; activeSound is a non-vacuous proof-field over the substantive predicate RoleKindPresent (FATCD.lean:106-107), with L/V/N attenuated as the paper itself flags them auxiliary.

#### `thm:decomposition-existence` — Decomposition existence.
- **Body location:** §7 (theorem)
- **Lean decl:** `SixBirds.decomposition_existence`  (module `Decomposition`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.decomposition_existence}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Witness is the hand-built defaultDecomposition with every status=absentWithRecord (Decomposition.lean:29-38); well-formedness closes by three rfl, vacuous 'cases h', and the borrowed classifyResidual_covered, whose match (UpperBound.lean:5-29) never emits the two uncovered classes, so no active projection is ever constructed; must not be called 'verified'.

#### `thm:six-channel-exactness` — Six-channel exactness and residual exhaustion.
- **Body location:** §7 (theorem)
- **Lean decl:** `SixBirds.six_channel_exactness`  (module `Decomposition`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.six_channel_exactness}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Proof is exactly two field projections of the hypothesis, ⟨h.left, h.right.right.right.left⟩ (Decomposition.lean:84-90); SixChannels is definitionally the first WellFormedDecomposition conjunct and coverage is verbatim its fourth, so it repackages rather than derives; paper clause (iii) is not even in the statement.

#### `prop:channel-vs-activation` — Channel-versus-activation discipline.
- **Body location:** §7 (proposition)
- **Lean decl:** `SixBirds.channel_vs_activation`  (module `Decomposition`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.channel_vs_activation}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** The statement SixChannels -> (SixActiveProjections -> SixChannels) is a tautology closed by 'exact h' after discarding the antecedent (Decomposition.lean:92-97); it does not establish the paper's actual separation that six channels does not imply six active projections (that content lives in inactive_statuses_are_not_active / non_uniqueness).

#### `prop:non-uniqueness` — Decomposition records are not unique.
- **Body location:** §7 (proposition)
- **Lean decl:** `SixBirds.non_uniqueness`  (module `Decomposition`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development exhibits two concrete decomposition records of a single description that differ only in their \texttt{P1} channel status; the Lean statement does not assert that either record is well-formed, and the further sources of non-uniqueness in the prose (level assignments, witness-schema choice, residual labels, loss/lift placement) are not mechanized. The narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.non\_uniqueness}).
- **Audit evidence:** Genuine existential of two distinct concrete records (activeDecomposition with P1 active backed by the real witness_role_kind_present via roleRaw_aligned, vs all-absent defaultDecomposition) with simp deriving activeProjection != absentWithRecord (Decomposition.lean:116-122); real but narrowed to one description and one field, and the statement does not itself demand well-formedness of either record, so narrowed_parametric stands and does not upgrade.  [Adjusted in Phase 1 external review, 2026-06-02.]

### §8 — Integrated stress

#### `prop:dependency-stress` — Dependency stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.dependency_stress`  (module `IntegratedStress`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.dependency\_stress}); \texttt{DependencyCoherent} is defined as the conjunction of the lower-bound and decomposition-existence schemas and is discharged by bundling them, so it inherits their projection status. See Appendix~\ref{app:mechanization}.
- **Audit evidence:** First conjunct `six_role_lower_bounds` genuinely builds `commonWitnessData` carrying a checked `DerivedRoleProjection` (ThresholdAttachment with cluster_nonempty, AlignedProjection via roleRaw_aligned), but second conjunct `decomposition_existence` is satisfied by `defaultDecomposition` (all channels `absentWithRecord`) whose only nontrivial obligation `activeSound` is discharged vacuously by `cases h`; the prose's ordering content is absent, so genuine-but-narrowed stands.  [Adjusted in Phase 1 external review, 2026-06-02.]

#### `prop:circularity-stress` — Circularity stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.circularity_stress`  (module `IntegratedStress`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.circularity_stress}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** `non_circularity` is `intro D; exact ⟨D.finite, D.closed, D.audited⟩` — a pure projection of the three proof-carrying fields off the `FATCD` record (FATCD.lean:423-427); it derives nothing and models none of the prose's circularity patterns, so projection_or_schema is confirmed.

#### `prop:channel-activation-stress` — Channel-versus-activation stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.channel_activation_stress`  (module `IntegratedStress`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for the five-status `ChannelStatus` enumeration under parametric hypotheses (constructor distinctness of the four inactive statuses from `active_projection`, rather than the full witness-versus-channel discipline); the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.channel_activation_stress}).
- **Audit evidence:** `inactive_statuses_are_not_active` (Decomposition.lean:99-114) proves four constructor-distinctness facts of the `ChannelStatus` inductive via `intro h; cases h` (no-confusion) — genuine and non-vacuous, not projection/rfl-over-record, but only a finite enum-disjointness surrogate for the prose's witness-vs-channel discipline (which lives unimported in `channel_vs_activation`); narrowed_parametric stands.

#### `prop:role-alignment-stress` — Role-alignment stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.role_alignment_stress`  (module `IntegratedStress`)
- **Fidelity:** Narrowed / parametric
- **Footnote (proposed):** The Lean development establishes this for single concrete witness clusters (`[rawRecord 1 RawKind.transition]` not projecting to \Pthree{}, and likewise for \Pfive{}/\Pone{}) under parametric hypotheses (the `AlignedProjection`/`roleRawKinds` required-kind constraints), rather than for arbitrary generic data; the narrowing is recorded in Appendix~\ref{app:mechanization} (\texttt{SixBirds.role_alignment_stress}).
- **Audit evidence:** `generic_*_not_*` (FATCD.lean:396-421) genuinely exercise `AlignedProjection`/`roleRawKinds` — P3 needs a `path` member, the singleton `[transition]` cannot supply it, refuted by `cases hk` — not a projection or rfl; but each prohibition is proved only over one concrete singleton cluster while prose asserts all generic data, so narrowed_parametric is correct.

#### `prop:residual-stress` — Upper-bound residual stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.residual_stress`  (module `IntegratedStress`)
- **Fidelity:** Trivial / vacuous  [!]
- **Footnote (proposed):** The Lean declaration is the same classifier-by-construction fact as the \S6 upper-bound machinery: \texttt{ResidualThreatsClosed} ignores its description argument and is discharged by \texttt{unresolved\_and\_genuine\_seventh\_empty}, which rests on \texttt{classifyResidual\_covered} (a case split closing every branch with \texttt{True.intro}); it does not establish the paper's universal residual-stress closure. See Appendix~\ref{app:mechanization} (\texttt{SixBirds.residual\_stress}).
- **Audit evidence:** `unresolved_and_genuine_seventh_empty` (UpperBound.lean:66-78) uses `classifyResidual_covered` (cases over all 23 RawKinds, UpperBound.lean:34-38) and `CoveredResidualClass _Threat = False` to close by `exact covered : False` — a genuine exhaustive proof, but over a total classifier authored never to emit the two threat classes and with `_D` vacuous, so narrowed_parametric stands (not projection, not vacuous-True).  [Adjusted in Phase 1 external review, 2026-06-02.]

#### `prop:overclaim-stress` — Overclaim stress.
- **Body location:** §8 (proposition)
- **Lean decl:** `SixBirds.overclaim_stress`  (module `IntegratedStress`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.overclaim_stress}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** Three of four conjuncts (the core nonclaim content) are `NoXxxClaim standardNonclaims := n.field = true` proved by `nonclaim_closure := ⟨rfl, rfl, rfl⟩` over `standardNonclaims` whose booleans were set to `true` (Admissibility.lean:67-119) — rfl-over-a-standard-record-built-to-be-true; only `non_uniqueness` is genuine, so the conservative dominant class is schema.

#### `thm:integrated-stress` — Integrated stress.
- **Body location:** §8 (theorem)
- **Lean decl:** `SixBirds.integrated_stress`  (module `IntegratedStress`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.integrated_stress}) bundling the six stress conjuncts; see Appendix~\ref{app:mechanization}.
- **Audit evidence:** `integrated_stress` (IntegratedStress.lean:51-55) only tuples the six stress theorems with `⟨...⟩` and derives nothing new; its fidelity is the meet of its parts, two of which (`circularity_stress`, `overclaim_stress`) are projection/schema, so the conservative class is schema and it must not be called 'verified'.

### §9 — Scoped exact-six

#### `thm:scoped-exact-six` — Scoped exact-six.
- **Body location:** §9 (theorem)
- **Lean decl:** `SixBirds.scoped_exact_six`  (module `ScopedExactSix`)
- **Fidelity:** Schema (projection)
- **Footnote (proposed):** Tracked in the formalization harness as a conditional schema (\texttt{SixBirds.scoped_exact_six}); see Appendix~\ref{app:mechanization}.
- **Audit evidence:** scoped_exact_six (ScopedExactSix.lean:11-15) composes decomposition_existence (Decomposition.lean:79-82, always returns the prebuilt defaultDecomposition with status = const absentWithRecord) and six_channel_exactness (Decomposition.lean:84-90, pure field projection h.left/h.right.right.right.left); WellFormed conjuncts are rfl, the active clause is vacuous (cases h, no active channel), and coverage is True.intro per case because classifyResidual (UpperBound.lean:5-29) is hand-built to never emit the two False classes (FATCD.lean:161-162) -- restatement over a default record, not a derivation, must not be 'verified'.
