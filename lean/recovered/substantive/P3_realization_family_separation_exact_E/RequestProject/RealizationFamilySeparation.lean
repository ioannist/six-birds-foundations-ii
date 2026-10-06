import Mathlib

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Realization-Family Separation — Exactification

Exactifies the refined realization-family separation candidate from the
P3 enriched route language campaign.

## Verdict: `exactified_enriched_P3`

The candidate is exactified as an enriched P3-style phenomenon:
two micro-updates that agree at a coarse stage and disagree at a finer stage,
with both descended maps defined, constituting a coherence/realization mismatch
rather than a descent obstruction (P1).
-/

------------------------------------------------------------------------
-- §1  Core definitions
------------------------------------------------------------------------

/-- A two-stage refinement system with coarse and fine quotients. -/
structure SimpleRS where
  /-- Carrier (process soup). -/
  P : Type
  /-- Quotient object at the coarse stage. -/
  QCoarse : Type
  /-- Quotient object at the fine stage. -/
  QFine : Type
  /-- Packaging map at the coarse stage. -/
  packCoarse : P → QCoarse
  /-- Packaging map at the fine stage. -/
  packFine : P → QFine
  /-- Coarsening map from fine to coarse. -/
  coarsen : QFine → QCoarse
  /-- Packaging commutes with coarsening. -/
  coarsen_pack : ∀ x, coarsen (packFine x) = packCoarse x

/-- Descent at the coarse stage: `f` respects the coarse equivalence relation. -/
def SimpleDescendsCoarse (R : SimpleRS) (f : R.P → R.P) : Prop :=
  ∀ x y, R.packCoarse x = R.packCoarse y → R.packCoarse (f x) = R.packCoarse (f y)

/-- Descent at the fine stage: `f` respects the fine equivalence relation. -/
def SimpleDescendsFine (R : SimpleRS) (f : R.P → R.P) : Prop :=
  ∀ x y, R.packFine x = R.packFine y → R.packFine (f x) = R.packFine (f y)

/-- Descended map specification at the coarse stage: `M ∘ pack = pack ∘ f`. -/
def SimpleIsDescCoarse (R : SimpleRS) (f : R.P → R.P) (M : R.QCoarse → R.QCoarse) : Prop :=
  ∀ x, M (R.packCoarse x) = R.packCoarse (f x)

/-- Descended map specification at the fine stage: `Fsharp ∘ pack = pack ∘ f`. -/
def SimpleIsDescFine (R : SimpleRS) (f : R.P → R.P) (Fsharp : R.QFine → R.QFine) : Prop :=
  ∀ x, Fsharp (R.packFine x) = R.packFine (f x)

/-- Realization family: all micro-updates in `Us` that descend at the coarse stage
    to a given macro map `M`. -/
def RealizationFamily (R : SimpleRS) (M : R.QCoarse → R.QCoarse)
    (Us : Set (R.P → R.P)) : Set (R.P → R.P) :=
  { f ∈ Us | SimpleDescendsCoarse R f ∧ SimpleIsDescCoarse R f M }

/-- Realization-family separation witness: two updates in the same coarse realization
    family that disagree when descended to the fine stage. -/
structure SimpleRFSWitness (R : SimpleRS) where
  /-- First micro-update. -/
  f : R.P → R.P
  /-- Second micro-update. -/
  g : R.P → R.P
  /-- Common coarse descended map. -/
  M : R.QCoarse → R.QCoarse
  /-- Fine descended map of `f`. -/
  Fsharp : R.QFine → R.QFine
  /-- Fine descended map of `g`. -/
  Gsharp : R.QFine → R.QFine
  /-- `f` descends at coarse stage to `M`. -/
  hf_coarse : SimpleIsDescCoarse R f M
  /-- `g` descends at coarse stage to `M`. -/
  hg_coarse : SimpleIsDescCoarse R g M
  /-- `f` descends at fine stage to `Fsharp`. -/
  hf_fine : SimpleIsDescFine R f Fsharp
  /-- `g` descends at fine stage to `Gsharp`. -/
  hg_fine : SimpleIsDescFine R g Gsharp
  /-- Witness point of disagreement. -/
  witness_q : R.QFine
  /-- The fine descended maps disagree. -/
  disagree : Fsharp witness_q ≠ Gsharp witness_q

/-
----------------------------------------------------------------------
§2  Abstract forbidden-square theorem
----------------------------------------------------------------------

The descent/coarsening square commutes whenever both descended maps exist
    and the fine packing is surjective.

    `coarsen ∘ Fsharp = M ∘ coarsen`

    This is why the descent/coarsening square cannot serve as a positive witness
    for realization-family separation — it is a tautology of quotient naturality.
-/
theorem abstract_forbidden_square
    (R : SimpleRS) (f : R.P → R.P)
    (M : R.QCoarse → R.QCoarse) (Fsharp : R.QFine → R.QFine)
    (hcoarse : SimpleIsDescCoarse R f M)
    (hfine : SimpleIsDescFine R f Fsharp)
    (surj : Function.Surjective R.packFine) :
    ∀ q, R.coarsen (Fsharp q) = M (R.coarsen q) := by
  intro q; cases surj q; simp_all +decide [ SimpleIsDescCoarse, SimpleIsDescFine ] ;
  -- By definition of coarsen, we know that coarsen (packFine x) = packCoarse x.
  have h_coarsen_pack : ∀ x, R.coarsen (R.packFine x) = R.packCoarse x := by
    exact R.coarsen_pack;
  grind +revert

------------------------------------------------------------------------
-- §3  Positive finite model
------------------------------------------------------------------------

/-- Four-element carrier. -/
inductive FourElem where | e0 | e1 | e2 | e3
  deriving DecidableEq

/-- Two-element coarse quotient: {e0,e1} and {e2,e3}. -/
inductive TwoClass where | c01 | c23
  deriving DecidableEq

/-- The concrete two-stage refinement system.
  - Coarse: {e0,e1} ↦ c01, {e2,e3} ↦ c23.
  - Fine: singletons (each element is its own class). -/
def modelRS : SimpleRS where
  P := FourElem
  QCoarse := TwoClass
  QFine := FourElem
  packCoarse
    | .e0 | .e1 => .c01
    | .e2 | .e3 => .c23
  packFine := id
  coarsen
    | .e0 | .e1 => .c01
    | .e2 | .e3 => .c23
  coarsen_pack := fun x => by cases x <;> rfl

/-- Update F: swap within each coarse class. 0↔1, 2↔3. -/
def updateF : FourElem → FourElem
  | .e0 => .e1 | .e1 => .e0 | .e2 => .e3 | .e3 => .e2

/-- Update G: swap within first class, fix second. 0↔1, 2↦2, 3↦3. -/
def updateG : FourElem → FourElem
  | .e0 => .e1 | .e1 => .e0 | .e2 => .e2 | .e3 => .e3

/-- The positive witness: `updateF` and `updateG` agree at the coarse stage
    (both descend to `id`) but disagree at the fine stage (at element `e2`). -/
def positiveWitness : SimpleRFSWitness modelRS where
  f := updateF
  g := updateG
  M := id
  Fsharp := updateF
  Gsharp := updateG
  hf_coarse := fun x => by cases x <;> rfl
  hg_coarse := fun x => by cases x <;> rfl
  hf_fine := fun x => by cases x <;> rfl
  hg_fine := fun x => by cases x <;> rfl
  witness_q := .e2
  disagree := by simp [updateF, updateG]

------------------------------------------------------------------------
-- §4  P1 boundary theorem
------------------------------------------------------------------------

/-- Both updates descend at the fine stage, so the witness is not a P1
    (descent obstruction) phenomenon. P1 requires a single update to *fail*
    to descend; here both succeed. -/
theorem witness_not_P1 :
    SimpleDescendsFine modelRS updateF ∧ SimpleDescendsFine modelRS updateG := by
  constructor
  · intro x y h; simp [modelRS] at h; exact congrArg updateF h
  · intro x y h; simp [modelRS] at h; exact congrArg updateG h

------------------------------------------------------------------------
-- §5  Forbidden-square (concrete instances)
------------------------------------------------------------------------

/-- The descent/coarsening square commutes for `updateF`. -/
theorem forbidden_square_F :
    ∀ q : FourElem,
      modelRS.coarsen (updateF q) = id (modelRS.coarsen q) := by
  intro q; cases q <;> rfl

/-- The descent/coarsening square commutes for `updateG`. -/
theorem forbidden_square_G :
    ∀ q : FourElem,
      modelRS.coarsen (updateG q) = id (modelRS.coarsen q) := by
  intro q; cases q <;> rfl

#check @positiveWitness
#check @witness_not_P1
#check @forbidden_square_F
#check @forbidden_square_G