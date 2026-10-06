import SixBirds.Decomposition

namespace SixBirds.Semantic

structure AuditLog (n : Nat) where
  start : Fin n
  states : List (Fin n)

structure SemSystem (n m k : Nat) where
  F : Fin n → Fin n
  G : Fin n → Fin n
  q : Fin n → Fin m
  t : Fin n → Fin k
  log : Option (AuditLog n) := none

variable {n m k : Nat}

def P1 (S : SemSystem n m k) : Prop :=
  ∃ z z' : Fin n, S.q z = S.q z' ∧ S.q (S.F z) ≠ S.q (S.F z')

def P2 (S : SemSystem n m k) : Prop :=
  (∃ z z' : Fin n, S.t z ≠ S.t z') ∧
  ∃ g : Fin m → Fin k, ∀ z : Fin n, S.t z = g (S.q z)

def P3 (S : SemSystem n m k) : Prop :=
  ∃ z : Fin n, S.F (S.G z) ≠ S.G (S.F z)

def walk (S : SemSystem n m k) (z : Fin n) (choices : Fin n → Bool) : Nat → Fin n
  | 0 => z
  | j + 1 => if h : j < n then
               if choices ⟨j, h⟩ then S.F (walk S z choices j)
               else S.G (walk S z choices j)
             else S.G (walk S z choices j)

def Reach (S : SemSystem n m k) (z z' : Fin n) : Prop :=
  ∃ steps : Fin (n + 1), ∃ choices : Fin n → Bool,
    walk S z choices steps.val = z'

inductive ReachAny (S : SemSystem n m k) (z : Fin n) : Fin n → Prop where
  | refl : ReachAny S z z
  | tail {x y : Fin n} : ReachAny S z x →
      (y = S.F x ∨ y = S.G x) → ReachAny S z y

def P4 (S : SemSystem n m k) : Prop :=
  ∃ z z' : Fin n, Reach S z z' ∧ ¬ Reach S z' z

def Equiv (R : Fin n → Fin n → Bool) : Prop :=
  (∀ x, R x x = true) ∧
  (∀ x y, R x y = R y x) ∧
  (∀ x y z, R x y = true → R y z = true → R x z = true)

def Congruence (S : SemSystem n m k) (R : Fin n → Fin n → Bool) : Prop :=
  Equiv R ∧
  (∃ x y, x ≠ y ∧ R x y = true) ∧
  (∃ x y, R x y = false) ∧
  (∀ x y, R x y = true → R (S.F x) (S.F y) = true) ∧
  (∀ x y, R x y = true → R (S.G x) (S.G y) = true)

def P5 (S : SemSystem n m k) : Prop :=
  ∃ R : Fin n → Fin n → Bool, Congruence S R

def Replay (S : SemSystem n m k) (start : Fin n) : List (Fin n) → Prop
  | [] => True
  | z :: zs => z = S.F start ∧ Replay S z zs

def P6 (S : SemSystem n m k) : Prop :=
  match S.log with
  | none => False
  | some log => log.states ≠ [] ∧ Replay S log.start log.states

def Holds (S : SemSystem n m k) : SixBirds.Role → Prop
  | .P1 => P1 S
  | .P2 => P2 S
  | .P3 => P3 S
  | .P4 => P4 S
  | .P5 => P5 S
  | .P6 => P6 S

instance (S : SemSystem n m k) : Decidable (P1 S) := by
  unfold P1
  infer_instance

noncomputable instance (S : SemSystem n m k) : Decidable (P2 S) := by
  classical
  infer_instance

instance (S : SemSystem n m k) : Decidable (P3 S) := by
  unfold P3
  infer_instance

noncomputable instance (S : SemSystem n m k) : Decidable (P4 S) := by
  classical
  infer_instance

noncomputable instance (S : SemSystem n m k) : Decidable (P5 S) := by
  classical
  infer_instance

noncomputable instance (S : SemSystem n m k) : Decidable (P6 S) := by
  classical
  infer_instance

noncomputable instance (S : SemSystem n m k) (r : SixBirds.Role) : Decidable (Holds S r) := by
  cases r <;> dsimp [Holds] <;> infer_instance

theorem p5_iff_nontrivial_congruence (S : SemSystem n m k) :
    P5 S ↔ ∃ R : Fin n → Fin n → Bool, Congruence S R := Iff.rfl

def MathematicalCongruence (S : SemSystem n m k) : Prop :=
  ∃ R : Fin n → Fin n → Prop,
    (∀ x, R x x) ∧
    (∀ x y, R x y → R y x) ∧
    (∀ x y z, R x y → R y z → R x z) ∧
    (∃ x y, x ≠ y ∧ R x y) ∧
    (∃ x y, ¬ R x y) ∧
    (∀ x y, R x y → R (S.F x) (S.F y)) ∧
    (∀ x y, R x y → R (S.G x) (S.G y))

theorem p5_iff_mathematical_congruence (S : SemSystem n m k) :
    P5 S ↔ MathematicalCongruence S := by
  constructor
  · intro ⟨R, h⟩
    refine ⟨fun x y => R x y = true, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h.1.1
    · intro x y hxy
      rw [← h.1.2.1]
      exact hxy
    · exact h.1.2.2
    · exact h.2.1
    · rcases h.2.2.1 with ⟨x, y, hxy⟩
      exact ⟨x, y, by simp [hxy]⟩
    · exact h.2.2.2.1
    · exact h.2.2.2.2
  · intro ⟨R, hrefl, hsym, htrans, hnontriv, hnototal, hF, hG⟩
    classical
    refine ⟨fun x y => decide (R x y), ?_⟩
    unfold Congruence Equiv
    constructor
    · constructor
      · intro x
        simpa using hrefl x
      constructor
      · intro x y
        by_cases hxy : R x y
        · have hyx := hsym x y hxy
          simp [hxy, hyx]
        · have hyx : ¬ R y x := by
            intro hyx
            exact hxy (hsym y x hyx)
          simp [hxy, hyx]
      · intro x y z hxy hyz
        simpa using htrans x y z (by simpa using hxy) (by simpa using hyz)
    constructor
    · rcases hnontriv with ⟨x, y, hxy, hr⟩
      exact ⟨x, y, hxy, by simpa using hr⟩
    constructor
    · rcases hnototal with ⟨x, y, hr⟩
      exact ⟨x, y, by simp [hr]⟩
    constructor
    · intro x y hr
      simpa using hF x y (by simpa using hr)
    · intro x y hr
      simpa using hG x y (by simpa using hr)

end SixBirds.Semantic
