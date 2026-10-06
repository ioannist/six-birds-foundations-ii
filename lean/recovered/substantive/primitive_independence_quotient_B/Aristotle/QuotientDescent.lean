import Mathlib

/-!
# Quotient/Descent Lens — Primitive Independence

This file formalizes the quotient/descent-lens analysis of the six-primitives framework.
It provides:
- The canonical closure package (process soup, refinement tower, designated updates)
- P5 as quotient maps (foundational)
- P4 as strict refinement (tower parameter)
- P6 as cardinality audit (derived from P5+P4)
- P1 as descent obstruction (quotient-native)
- P2 as quotient-derived macro-representability via pro-object / inverse-limit realizability
- P3 as descended-map coherence defect (partial quotient-native P3)
- Separation/collapse theorems and countermodels
-/

namespace QuotientDescent

open Classical

/-! ## Core package: process soup with refinement tower -/

/-- A canonical closure package over a finite type `P` with `n` refinement levels. -/
structure ClosurePackage (P : Type*) (n : ℕ) where
  /-- Equivalence relation at level j -/
  equiv : Fin n → Setoid P
  /-- Refinement: finer level implies coarser level -/
  refines : ∀ (i j : Fin n), i ≤ j →
    ∀ x y : P, (equiv j).r x y → (equiv i).r x y
  /-- Designated admissible updates -/
  updates : Set (P → P)

variable {P : Type*} [Fintype P] [DecidableEq P] {n : ℕ}

/-! ## P5: Packaging — the quotient maps -/

/-- P5: the quotient at level j. This IS the foundational quotient/descent object. -/
noncomputable def P5_quotient (pkg : ClosurePackage P n) (j : Fin n) :=
  Quotient (pkg.equiv j)

/-- P5: the packaging map at level j -/
noncomputable def P5_pack (pkg : ClosurePackage P n) (j : Fin n) : P → Quotient (pkg.equiv j) :=
  Quotient.mk (pkg.equiv j)

/-- P5: packaging is idempotent (the closure cl_j is idempotent) -/
def P5_closure (pkg : ClosurePackage P n) (j : Fin n) (A : Set P) : Set P :=
  { x : P | ∃ a ∈ A, (pkg.equiv j).r x a }

theorem P5_closure_idempotent (pkg : ClosurePackage P n) (j : Fin n) (A : Set P) :
    P5_closure pkg j (P5_closure pkg j A) = P5_closure pkg j A := by
  ext x
  simp only [P5_closure, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨a, ha, hya⟩, hxy⟩
    exact ⟨a, ha, (pkg.equiv j).trans hxy hya⟩
  · intro ⟨a, ha, hxa⟩
    exact ⟨a, ⟨a, ha, (pkg.equiv j).refl a⟩, hxa⟩

/-! ## P4: Staging — strict refinement -/

/-- P4 nontrivial: there exists a level where refinement is strict -/
def P4_nontrivial (pkg : ClosurePackage P n) : Prop :=
  ∃ j : Fin n, ∃ k : Fin n, j < k ∧
    ∃ x y : P, (pkg.equiv j).r x y ∧ ¬(pkg.equiv k).r x y

/-! ## P6: Audit — cardinality of quotient (derived from P5+P4) -/

/-- P6 (cardinality audit): the number of equivalence classes at level j -/
noncomputable def P6_audit (pkg : ClosurePackage P n) (j : Fin n) : ℕ :=
  Fintype.card (Quotient (pkg.equiv j))

/-- P6 is derived from P5: the audit is computable from the quotient structure alone. -/
theorem P6_derived_from_P5 (pkg : ClosurePackage P n) (j : Fin n) :
    P6_audit pkg j = Fintype.card (Quotient (pkg.equiv j)) := by
  rfl

/-! ## P1: Descent obstruction — failure of an update to respect the equivalence -/

/-- An update F descends at level j if it respects ~_j -/
def Descends (pkg : ClosurePackage P n) (F : P → P) (j : Fin n) : Prop :=
  ∀ x y : P, (pkg.equiv j).r x y → (pkg.equiv j).r (F x) (F y)

/-- P1 nontrivial: there exists an admissible update that fails to descend at some level -/
def P1_nontrivial (pkg : ClosurePackage P n) : Prop :=
  ∃ F ∈ pkg.updates, ∃ j : Fin n, ¬Descends pkg F j

/-- The descended macro-map, when descent holds -/
noncomputable def descendedMap (pkg : ClosurePackage P n) (F : P → P) (j : Fin n)
    (hd : Descends pkg F j) : Quotient (pkg.equiv j) → Quotient (pkg.equiv j) :=
  Quotient.map F hd

/-! ## P2: Macro-representability via pro-object / inverse-limit realizability -/

/-- A coherent sequence in the tower: a family of quotient classes compatible under coarsening.
    This is the quotient-native surrogate for a macro-specification space. -/
structure CoherentSeq (pkg : ClosurePackage P n) where
  /-- A choice of quotient class at each level -/
  classes : (j : Fin n) → Quotient (pkg.equiv j)
  /-- Coherence: coarsening from finer to coarser level is respected -/
  coherent : ∀ (i j : Fin n) (hij : i ≤ j),
    Quotient.map id (pkg.refines i j hij) (classes j) = classes i

/-- A coherent sequence is realized if it comes from an actual microstate -/
def CoherentSeq.realized (pkg : ClosurePackage P n) (cs : CoherentSeq pkg) : Prop :=
  ∃ x : P, ∀ j : Fin n, Quotient.mk (pkg.equiv j) x = cs.classes j

/-- P2 nontrivial (quotient-native): there exists an unrealized coherent sequence -/
def P2_nontrivial (pkg : ClosurePackage P n) : Prop :=
  ∃ cs : CoherentSeq pkg, ¬cs.realized pkg

/-! ## Key structural theorem: P2 is always trivially satisfiable for non-empty carriers.

For any non-empty carrier P with a finite tower of n ≥ 1 levels, every coherent sequence
is realized by some microstate. This means P2_nontrivial is always false in the
non-degenerate canonical quotient/descent package. -/

theorem P2_always_realized [Nonempty P] (pkg : ClosurePackage P n) (hn : 0 < n)
    (cs : CoherentSeq pkg) : cs.realized pkg := by
  -- By definition of coherent sequence, there exists an element x in P such that for all levels j, the equivalence class of x at level j is cs.classes j.
  obtain ⟨x, hx⟩ : ∃ x : P, Quotient.mk (pkg.equiv ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩) x = cs.classes ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
    exact Quotient.exists_rep _;
  use x;
  intro j
  have := cs.coherent j ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ (by
  exact Nat.le_pred_of_lt j.is_lt);
  all_goals generalize_proofs at *;
  convert this using 1;
  rw [ ← hx ];
  simp [Quotient.map_mk]

/-! ## P3: Descended-map coherence defect (partial quotient-native P3)

At the quotient/descent lens, the natural route mismatch arises when descended maps
at different levels fail to commute with coarsening. Specifically:
- Route 1: descend F at level j, apply descended map, coarsen result to level i
- Route 2: coarsen to level i first, then apply descended map at level i
These can disagree: the descended map is level-specific. -/

/-- Coarsening map from finer quotient to coarser quotient -/
noncomputable def coarsen (pkg : ClosurePackage P n) (i j : Fin n) (hij : i ≤ j) :
    Quotient (pkg.equiv j) → Quotient (pkg.equiv i) :=
  Quotient.map id (pkg.refines i j hij)

/-- P3 coherence defect: descended maps at different levels disagree under coarsening.
    This is the quotient-native part of route mismatch. -/
def P3_coherenceDefect (pkg : ClosurePackage P n)
    (F : P → P) (i j : Fin n) (hij : i ≤ j)
    (hdi : Descends pkg F i) (hdj : Descends pkg F j) : Prop :=
  ∃ q : Quotient (pkg.equiv j),
    coarsen pkg i j hij (descendedMap pkg F j hdj q) ≠
    descendedMap pkg F i hdi (coarsen pkg i j hij q)

/-- P3 nontrivial: there exists an admissible update with a coherence defect -/
def P3_nontrivial (pkg : ClosurePackage P n) : Prop :=
  ∃ F ∈ pkg.updates, ∃ i j : Fin n, ∃ hij : i ≤ j,
    ∃ hdi : Descends pkg F i, ∃ hdj : Descends pkg F j,
    P3_coherenceDefect pkg F i j hij hdi hdj

/-! ## Key structural theorem: P3 coherence defect is always trivial in this package.

The descended map commutes with coarsening by construction: both are defined via
Quotient.map and the refinement condition ensures compatibility. This is the key
finding: the quotient/descent lens CANNOT support a nontrivial P3 in the canonical
package. Route mismatch requires richer (coherence/categorical) structure. -/

theorem P3_always_trivial (pkg : ClosurePackage P n)
    (F : P → P) (i j : Fin n) (hij : i ≤ j)
    (hdi : Descends pkg F i) (hdj : Descends pkg F j) :
    ¬P3_coherenceDefect pkg F i j hij hdi hdj := by
  rintro ⟨ q, hq ⟩;
  exact hq ( by exact Quotient.inductionOn q fun x => by rfl )

theorem P3_never_nontrivial (pkg : ClosurePackage P n) :
    ¬P3_nontrivial pkg := by
  rintro ⟨F, _, i, j, hij, hdi, hdj, hdef⟩
  exact P3_always_trivial pkg F i j hij hdi hdj hdef

/-! ## Countermodel: P1 nontrivial is achievable -/

/-- Three-element carrier for countermodels -/
inductive Three where | a | b | c
  deriving Fintype, DecidableEq

/-- Setoid on Three identifying a and b but not c -/
def Three.abSetoid : Setoid Three :=
  ⟨fun x y => match x, y with
    | .a, .a => True | .a, .b => True | .b, .a => True | .b, .b => True
    | .c, .c => True | _, _ => False,
   ⟨fun x => by cases x <;> simp,
    fun {x y} h => by cases x <;> cases y <;> simp_all,
    fun {x y z} h1 h2 => by cases x <;> cases y <;> cases z <;> simp_all⟩⟩

/-- Helper: the discrete (equality) setoid on Three -/
def Three.discSetoid : Setoid Three :=
  ⟨fun x y => x = y, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

/-- Countermodel showing P1 can be nontrivial.
    Level 0: a ~ b, c alone. Level 1: discrete.
    Update: swap a and c. This descends at level 1 (discrete: always)
    but fails at level 0: a ~_0 b but F(a)=c, F(b)=b, c ≁_0 b. -/
noncomputable def p1Model : ClosurePackage Three 2 where
  equiv := ![Three.abSetoid, Three.discSetoid]
  refines := by
    intro i j hij x y hj
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
      Three.abSetoid, Three.discSetoid]
    · cases x <;> cases y <;> simp_all [Three.abSetoid]
  updates := { fun x => match x with | .a => .c | .b => .b | .c => .a }

theorem p1Model_P1_nontrivial : P1_nontrivial p1Model := by
  use fun x => match x with | .a => .c | .b => .b | .c => .a;
  constructor;
  · exact Set.mem_singleton _;
  · use ⟨ 0, by decide ⟩;
    intro h;
    exact absurd ( h Three.a Three.b ( by tauto ) ) ( by tauto )

/-! ## P2 independence from P1: existence theorem -/

theorem P2_independent_of_P1 :
    ∃ (P : Type) (_ : Fintype P) (_ : DecidableEq P) (n : ℕ) (pkg : ClosurePackage P n),
      P2_nontrivial pkg ∧ ¬P1_nontrivial pkg := by
  refine' ⟨ _, _, _, _, _ ⟩;
  exact PEmpty;
  all_goals try infer_instance;
  exact 0;
  fconstructor;
  constructor;
  all_goals norm_num [ P2_nontrivial, P1_nontrivial ];
  exact ∅;
  exact fun _ => ⊥;
  refine' ⟨ _, _ ⟩;
  constructor;
  rotate_left;
  exact fun x => Fin.elim0 x;
  all_goals norm_num [ CoherentSeq.realized ]

end QuotientDescent