import SixBirds.Semantic.Core

namespace SixBirds.Semantic

inductive SoundStatus (S : SemSystem n m k) (r : SixBirds.Role) where
  | active : Holds S r → SoundStatus S r
  | absent : ¬ Holds S r → SoundStatus S r

def SoundStatus.isActive {S : SemSystem n m k} {r : SixBirds.Role} :
    SoundStatus S r → Prop
  | .active _ => True
  | .absent _ => False

noncomputable def soundStatus (S : SemSystem n m k) (r : SixBirds.Role) :
    SoundStatus S r :=
  if h : Holds S r then .active h else .absent h

theorem active_iff (S : SemSystem n m k) (r : SixBirds.Role)
    (s : SoundStatus S r) : s.isActive ↔ Holds S r := by
  cases s with
  | active h => simp [SoundStatus.isActive, h]
  | absent h => simp [SoundStatus.isActive, h]

theorem absent_iff (S : SemSystem n m k) (r : SixBirds.Role)
    (s : SoundStatus S r) : ¬ s.isActive ↔ ¬ Holds S r := by
  rw [active_iff]

theorem status_unique (S : SemSystem n m k) (r : SixBirds.Role)
    (a b : SoundStatus S r) : a = b := by
  cases a with
  | active ha =>
    cases b with
    | active hb => rfl
    | absent hb => exact False.elim (hb ha)
  | absent ha =>
    cases b with
    | active hb => exact False.elim (ha hb)
    | absent hb => rfl

def SoundAssignment (S : SemSystem n m k) :=
  ∀ r : SixBirds.Role, SoundStatus S r

theorem semantic_exact_six_unique (S : SemSystem n m k) :
    ∃ assignment : SoundAssignment S, ∀ other : SoundAssignment S,
      assignment = other := by
  refine ⟨soundStatus S, ?_⟩
  intro other
  funext r
  exact status_unique S r (soundStatus S r) (other r)

def splitF : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else 0
def mergeLens : Fin 3 → Fin 3 := fun x => if x = 1 then 0 else x

def identityLensSystem : SemSystem 3 3 2 :=
  { F := splitF, G := id, q := id, t := fun _ => 0 }

def mergeLensSystem : SemSystem 3 3 2 :=
  { F := splitF, G := id, q := mergeLens, t := fun _ => 0 }

theorem identityLens_no_p1 : ¬ P1 identityLensSystem := by
  intro ⟨z, z', hq, hs⟩
  have heq : z = z' := hq
  subst z'
  exact hs rfl

theorem mergeLens_p1 : P1 mergeLensSystem := by
  refine ⟨0, 1, ?_, ?_⟩
  · rfl
  · decide

theorem lens_non_uniqueness :
    ¬ (soundStatus identityLensSystem SixBirds.Role.P1).isActive ∧
    (soundStatus mergeLensSystem SixBirds.Role.P1).isActive := by
  constructor
  · rw [active_iff]
    exact identityLens_no_p1
  · rw [active_iff]
    exact mergeLens_p1

end SixBirds.Semantic
