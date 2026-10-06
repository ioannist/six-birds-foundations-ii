import SixBirds.Semantic.Core

namespace SixBirds.Semantic

def LevelSet {α β : Type} (w : α → β) (x y : α) : Prop :=
  w x = w y

def OneMapCongruence {α : Type} (F : α → α) (R : α → α → Prop) : Prop :=
  Equivalence R ∧ ∀ x y, R x y → R (F x) (F y)

def NontrivialRelation {α : Type} (R : α → α → Prop) : Prop :=
  (∃ x y, x ≠ y ∧ R x y) ∧ (∃ x y, ¬ R x y)

theorem conservation_level_sets {α β : Type} (F : α → α) (w : α → β)
    (h : w ∘ F = w) :
    OneMapCongruence F (LevelSet w) ∧
    ∃ update : β → β,
      (∀ value, update value = value) ∧
      ∀ x, w (F x) = update (w x) := by
  have hw (x : α) : w (F x) = w x := congrFun h x
  constructor
  · constructor
    · constructor
      · intro x
        rfl
      · intro x y hxy
        exact hxy.symm
      · intro x y z hxy hyz
        exact hxy.trans hyz
    · intro x y hxy
      calc
        w (F x) = w x := hw x
        _ = w y := hxy
        _ = w (F y) := (hw y).symm
  · exact ⟨id, fun _ => rfl, hw⟩

theorem nontrivial_level_sets {α β : Type} (w : α → β)
    (hni : ¬ Function.Injective w)
    (hnc : ¬ ∀ x y, w x = w y) :
    NontrivialRelation (LevelSet w) := by
  classical
  have hmerged : ∃ x y, x ≠ y ∧ w x = w y := Classical.byContradiction (by
    intro hnone
    apply hni
    intro x y hxy
    by_cases hne : x = y
    · exact hne
    · exact False.elim (hnone ⟨x, y, hne, hxy⟩))
  have hseparate : ∃ x y, w x ≠ w y := Classical.byContradiction (by
    intro hnone
    apply hnc
    intro x y
    by_cases heq : w x = w y
    · exact heq
    · exact False.elim (hnone ⟨x, y, heq⟩))
  exact ⟨hmerged, hseparate⟩

theorem conservation_proposition {α β : Type} (F : α → α) (w : α → β)
    (h : w ∘ F = w) :
    OneMapCongruence F (LevelSet w) ∧
    (∃ update : β → β, (∀ value, update value = value) ∧
      ∀ x, w (F x) = update (w x)) ∧
    ((¬ Function.Injective w) → (¬ ∀ x y, w x = w y) →
      NontrivialRelation (LevelSet w)) := by
  rcases conservation_level_sets F w h with ⟨hc, hd⟩
  exact ⟨hc, hd, fun hni hnc => nontrivial_level_sets w hni hnc⟩

def fourSwap : Fin 4 → Fin 4 := fun x =>
  if x = 0 then 1 else if x = 1 then 0 else if x = 2 then 3 else 2

def fourWeight : Fin 4 → Fin 2 := fun x =>
  if x.val < 2 then 0 else 1

theorem four_swap_values :
    fourSwap 0 = 1 ∧ fourSwap 1 = 0 ∧
    fourSwap 2 = 3 ∧ fourSwap 3 = 2 := by
  decide

theorem four_level_sets (x y : Fin 4) :
    LevelSet fourWeight x y ↔ (x.val < 2 ↔ y.val < 2) := by
  unfold LevelSet fourWeight
  by_cases hx : x.val < 2 <;> by_cases hy : y.val < 2 <;>
    simp [hx, hy]

theorem four_conservation : fourWeight ∘ fourSwap = fourWeight := by
  funext x
  have h : ∀ x : Fin 4, fourWeight (fourSwap x) = fourWeight x := by decide
  exact h x

theorem four_nontrivial : NontrivialRelation (LevelSet fourWeight) := by
  constructor
  · refine ⟨0, 1, by decide, ?_⟩
    rfl
  · refine ⟨0, 2, ?_⟩
    change fourWeight 0 ≠ fourWeight 2
    decide

theorem four_state_conservation_example :
    (fourWeight ∘ fourSwap = fourWeight) ∧
    OneMapCongruence fourSwap (LevelSet fourWeight) ∧
    NontrivialRelation (LevelSet fourWeight) ∧
    (∃ update : Fin 2 → Fin 2,
      (∀ value, update value = value) ∧
      ∀ x, fourWeight (fourSwap x) = update (fourWeight x)) := by
  rcases conservation_level_sets fourSwap fourWeight four_conservation with ⟨hc, hd⟩
  exact ⟨four_conservation, hc, four_nontrivial, hd⟩

end SixBirds.Semantic
