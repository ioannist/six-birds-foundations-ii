import SixBirds.Semantic.Decomposition

namespace SixBirds.Semantic

def twoIdentity : SemSystem 2 2 2 :=
  { F := id, G := id, q := id, t := id }

def twoMismatch : SemSystem 2 2 2 :=
  { F := fun x => if x = 0 then 1 else 0,
    G := fun _ => 0, q := id, t := fun _ => 0 }

def twoDirected : SemSystem 2 2 2 :=
  { F := fun _ => 1, G := id, q := id, t := fun _ => 0 }

def threeQuotient : SemSystem 3 2 2 :=
  { F := id, G := id, q := fun _ => 0, t := fun _ => 0 }

def twoAudited : SemSystem 2 2 2 :=
  { F := id, G := id, q := id, t := fun _ => 0,
    log := some { start := 0, states := [0] } }

theorem p1_concrete : P1 mergeLensSystem := mergeLens_p1

theorem p2_concrete : P2 twoIdentity := by
  refine ⟨⟨0, 1, by decide⟩, id, ?_⟩
  intro z
  rfl

theorem p3_concrete : P3 twoMismatch := by
  refine ⟨0, ?_⟩
  decide

private theorem directed_walk_one (choices : Fin 2 → Bool) (steps : Nat) :
    walk twoDirected 1 choices steps = 1 := by
  induction steps with
  | zero => rfl
  | succ j ih =>
    by_cases hj : j < 2
    · simp only [walk, hj, dite_true]
      by_cases hc : choices ⟨j, hj⟩ = true
      · simp [hc, twoDirected]
      · simp [hc, twoDirected]
        exact ih
    · simp [walk, hj, twoDirected]
      exact ih

theorem p4_concrete : P4 twoDirected := by
  refine ⟨0, 1, ?_, ?_⟩
  · refine ⟨⟨1, by decide⟩, fun _ => true, ?_⟩
    rfl
  · intro ⟨steps, choices, h⟩
    rw [directed_walk_one] at h
    exact Fin.zero_ne_one h.symm

def quotientRelation (x y : Fin 3) : Bool :=
  decide ((x = 0) ↔ (y = 0))

theorem p5_concrete : P5 threeQuotient := by
  refine ⟨quotientRelation, ?_⟩
  unfold Congruence Equiv
  decide

theorem p6_concrete : P6 twoAudited := by
  simp [P6, twoAudited, Replay]

theorem six_roles_inhabited :
    (∃ n m k, ∃ S : SemSystem n m k, P1 S) ∧
    (∃ n m k, ∃ S : SemSystem n m k, P2 S) ∧
    (∃ n m k, ∃ S : SemSystem n m k, P3 S) ∧
    (∃ n m k, ∃ S : SemSystem n m k, P4 S) ∧
    (∃ n m k, ∃ S : SemSystem n m k, P5 S) ∧
    (∃ n m k, ∃ S : SemSystem n m k, P6 S) := by
  exact ⟨⟨3, 3, 2, mergeLensSystem, p1_concrete⟩,
    ⟨2, 2, 2, twoIdentity, p2_concrete⟩,
    ⟨2, 2, 2, twoMismatch, p3_concrete⟩,
    ⟨2, 2, 2, twoDirected, p4_concrete⟩,
    ⟨3, 2, 2, threeQuotient, p5_concrete⟩,
    ⟨2, 2, 2, twoAudited, p6_concrete⟩⟩

def allRolesSystem : SemSystem 3 3 3 :=
  { F := fun x => if x = 2 then 1 else 0
    G := fun x => if x = 2 then 2 else 0
    q := fun x => if x = 1 then 1 else 0
    t := fun x => if x = 1 then 1 else 0
    log := some { start := 0, states := [0] } }

private theorem all_walk_zero (choices : Fin 3 → Bool) (steps : Nat) :
    walk allRolesSystem 0 choices steps = 0 := by
  induction steps with
  | zero => rfl
  | succ j ih =>
    by_cases hj : j < 3
    · simp only [walk, hj, dite_true]
      by_cases hc : choices ⟨j, hj⟩ = true
      · simp [hc, allRolesSystem] at ih ⊢
        rw [ih]
        decide
      · simp [hc, allRolesSystem] at ih ⊢
        rw [ih]
        decide
    · simp [walk, hj, allRolesSystem] at ih ⊢
      rw [ih]
      decide

def allCongruence (x y : Fin 3) : Bool :=
  decide ((x = 2) ↔ (y = 2))

theorem all_roles_active :
    P1 allRolesSystem ∧ P2 allRolesSystem ∧ P3 allRolesSystem ∧
    P4 allRolesSystem ∧ P5 allRolesSystem ∧ P6 allRolesSystem := by
  constructor
  · refine ⟨0, 2, by decide, by decide⟩
  constructor
  · refine ⟨⟨0, 1, by decide⟩, id, ?_⟩
    intro z
    rfl
  constructor
  · refine ⟨2, by decide⟩
  constructor
  · refine ⟨1, 0, ?_, ?_⟩
    · refine ⟨⟨1, by decide⟩, fun _ => true, ?_⟩
      rfl
    · intro ⟨steps, choices, h⟩
      rw [all_walk_zero] at h
      exact Fin.zero_ne_one h
  constructor
  · refine ⟨allCongruence, ?_⟩
    unfold Congruence Equiv
    decide
  · simp [P6, allRolesSystem, Replay]

def noRolesSystem : SemSystem 1 1 1 :=
  { F := id, G := id, q := id, t := id }

theorem no_roles_active (r : SixBirds.Role) : ¬ Holds noRolesSystem r := by
  cases r with
  | P1 =>
    intro ⟨z, z', _, h⟩
    exact h (congrArg noRolesSystem.q (congrArg noRolesSystem.F (Subsingleton.elim z z')))
  | P2 =>
    intro ⟨⟨z, z', h⟩, _⟩
    exact h (congrArg noRolesSystem.t (Subsingleton.elim z z'))
  | P3 =>
    intro ⟨z, h⟩
    exact h (Subsingleton.elim _ _)
  | P4 =>
    intro ⟨z, z', _, h⟩
    have heq : z' = z := Subsingleton.elim _ _
    cases heq
    exact h ⟨⟨0, by decide⟩, fun _ => false, rfl⟩
  | P5 =>
    intro ⟨R, h⟩
    rcases h.2.1 with ⟨x, y, hxy, _⟩
    exact hxy (Subsingleton.elim x y)
  | P6 =>
    simp [Holds, P6, noRolesSystem]

theorem no_p5_on_two (S : SemSystem 2 m k) : ¬ P5 S := by
  intro ⟨R, h⟩
  rcases h.2.1 with ⟨x, y, hxy, hR⟩
  have hx : x = 0 ∨ x = 1 := by omega
  have hy : y = 0 ∨ y = 1 := by omega
  have h01 : R 0 1 = true := by
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst x <;> subst y
    · exact False.elim (hxy rfl)
    · exact hR
    · simpa [h.1.2.1] using hR
    · exact False.elim (hxy rfl)
  rcases h.2.2.1 with ⟨a, b, hab⟩
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b
  · exact Bool.false_ne_true (hab.symm.trans (h.1.1 0))
  · exact Bool.false_ne_true (hab.symm.trans h01)
  · exact Bool.false_ne_true (hab.symm.trans ((h.1.2.1 0 1).symm.trans h01))
  · exact Bool.false_ne_true (hab.symm.trans (h.1.1 1))

end SixBirds.Semantic
