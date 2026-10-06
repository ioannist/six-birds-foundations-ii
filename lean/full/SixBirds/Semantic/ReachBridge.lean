import SixBirds.Semantic.Core

namespace SixBirds.Semantic

variable {n m k : Nat} (S : SemSystem n m k)

private theorem nodup_length_le_of_subset {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hn : xs.Nodup) (hs : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    have ha : a ∈ ys := hs a (by simp)
    have hna : a ∉ as := (List.nodup_cons.mp hn).1
    have hnas : as.Nodup := (List.nodup_cons.mp hn).2
    have hs' : ∀ x ∈ as, x ∈ ys.erase a := by
      intro x hx
      have hxa : x ≠ a := by
        intro h
        subst x
        exact hna hx
      exact (List.mem_erase_of_ne hxa).2 (hs x (by simp [hx]))
    have hh := ih (ys.erase a) hnas hs'
    have he := List.length_erase_of_mem ha
    have hp : 0 < ys.length := List.length_pos_of_mem ha
    simp only [List.length_cons] at *
    omega

private theorem nodup_fin_length_le (xs : List (Fin n)) (hn : xs.Nodup) :
    xs.length ≤ n := by
  have h := nodup_length_le_of_subset xs (List.finRange n) hn (by
    intro x _
    exact List.mem_finRange x)
  simpa using h

inductive PathFrom (S : SemSystem n m k) (z : Fin n) : List (Fin n) → Prop where
  | start : PathFrom S z [z]
  | step {x y : Fin n} {xs : List (Fin n)} :
      PathFrom S z (x :: xs) →
      (y = S.F x ∨ y = S.G x) →
      PathFrom S z (y :: x :: xs)

private theorem path_truncate {z y : Fin n} {xs : List (Fin n)}
    (h : PathFrom S z xs) (hn : xs.Nodup) (hy : y ∈ xs) :
    ∃ ys, PathFrom S z (y :: ys) ∧ (y :: ys).Nodup := by
  induction h with
  | start =>
    simp at hy
    subst y
    exact ⟨[], PathFrom.start, by simp⟩
  | @step x v rest hp edge ih =>
    by_cases hv : y = v
    · subst y
      exact ⟨x :: rest, PathFrom.step hp edge, hn⟩
    · have hnold : (x :: rest).Nodup := (List.nodup_cons.mp hn).2
      have hyold : y ∈ x :: rest := by simpa [hv] using hy
      exact ih hnold hyold

private theorem simple_path_of_reachAny {z y : Fin n}
    (h : ReachAny S z y) :
    ∃ xs, PathFrom S z (y :: xs) ∧ (y :: xs).Nodup := by
  induction h with
  | refl => exact ⟨[], PathFrom.start, by simp⟩
  | @tail x y hp edge ih =>
    rcases ih with ⟨xs, hpath, hn⟩
    by_cases hy : y ∈ x :: xs
    · exact path_truncate S hpath hn hy
    · exact ⟨x :: xs, PathFrom.step hpath edge,
        (List.nodup_cons.mpr ⟨hy, hn⟩)⟩

private theorem walk_congr_prefix (z : Fin n) (c d : Fin n → Bool)
    (j : Nat) (hj : j ≤ n)
    (hcd : ∀ i : Fin n, i.val < j → c i = d i) :
    walk S z c j = walk S z d j := by
  induction j with
  | zero => rfl
  | succ t ih =>
    have ht : t < n := by omega
    have hpre : ∀ i : Fin n, i.val < t → c i = d i := by
      intro i hi
      exact hcd i (by omega)
    have heq := ih (by omega) hpre
    simp only [walk, ht, dite_true]
    rw [hcd ⟨t, ht⟩ (Nat.lt_succ_self t), heq]

private theorem path_walk_aux {z : Fin n} {path : List (Fin n)}
    (h : PathFrom S z path) :
    ∀ (x : Fin n) (xs : List (Fin n)), path = x :: xs →
      path.length ≤ n →
      ∃ c : Fin n → Bool, walk S z c xs.length = x := by
  induction h with
  | start =>
    intro x xs heq hb
    cases heq
    exact ⟨fun _ => false, rfl⟩
  | @step a b rest hp edge ih =>
    intro x xs heq hb
    cases heq
    have hold : (a :: rest).length ≤ n := by
      simp only [List.length_cons] at hb ⊢
      omega
    rcases ih a rest rfl hold with ⟨c, hc⟩
    let j := rest.length
    have hj : j < n := by
      dsimp [j]
      simp only [List.length_cons] at hb
      omega
    rcases edge with hF | hG
    · let d : Fin n → Bool := fun i => if i.val = j then true else c i
      have hpre : ∀ i : Fin n, i.val < j → c i = d i := by
        intro i hi
        simp [d, Nat.ne_of_lt hi]
      have hwalk := walk_congr_prefix S z c d j (by omega) hpre
      refine ⟨d, ?_⟩
      dsimp [j] at hj hwalk
      have hd : d ⟨rest.length, hj⟩ = true := by simp [d, j]
      simp only [List.length_cons]
      simp only [walk]
      simp [hj, hd]
      rw [← hwalk, hc, ← hF]
    · let d : Fin n → Bool := fun i => if i.val = j then false else c i
      have hpre : ∀ i : Fin n, i.val < j → c i = d i := by
        intro i hi
        simp [d, Nat.ne_of_lt hi]
      have hwalk := walk_congr_prefix S z c d j (by omega) hpre
      refine ⟨d, ?_⟩
      dsimp [j] at hj hwalk
      have hd : d ⟨rest.length, hj⟩ = false := by simp [d, j]
      simp only [List.length_cons]
      simp only [walk]
      simp [hj, hd]
      rw [← hwalk, hc, ← hG]

private theorem walk_reachAny (z : Fin n) (c : Fin n → Bool) (j : Nat) :
    ReachAny S z (walk S z c j) := by
  induction j with
  | zero => exact ReachAny.refl
  | succ t ih =>
    by_cases ht : t < n
    · by_cases hc : c ⟨t, ht⟩ = true
      · simpa [walk, ht, hc] using
          (ReachAny.tail ih (Or.inl rfl) : ReachAny S z (S.F (walk S z c t)))
      · simpa [walk, ht, hc] using
          (ReachAny.tail ih (Or.inr rfl) : ReachAny S z (S.G (walk S z c t)))
    · simpa [walk, ht] using
        (ReachAny.tail ih (Or.inr rfl) : ReachAny S z (S.G (walk S z c t)))

theorem reach_iff_reachAny (z z' : Fin n) :
    Reach S z z' ↔ ReachAny S z z' := by
  constructor
  · intro ⟨steps, choices, h⟩
    rw [← h]
    exact walk_reachAny S z choices steps.val
  · intro h
    rcases simple_path_of_reachAny S h with ⟨xs, hpath, hn⟩
    have hb : (z' :: xs).length ≤ n := nodup_fin_length_le (z' :: xs) hn
    rcases path_walk_aux S hpath z' xs rfl hb with ⟨choices, hw⟩
    exact ⟨⟨xs.length, by simp only [List.length_cons] at hb; omega⟩, choices, hw⟩

theorem p4_iff_reachAny :
    P4 S ↔ ∃ z z' : Fin n, ReachAny S z z' ∧ ¬ ReachAny S z' z := by
  constructor
  · intro ⟨z, z', h, hn⟩
    exact ⟨z, z', (reach_iff_reachAny S z z').mp h,
      fun hr => hn ((reach_iff_reachAny S z' z).mpr hr)⟩
  · intro ⟨z, z', h, hn⟩
    exact ⟨z, z', (reach_iff_reachAny S z z').mpr h,
      fun hr => hn ((reach_iff_reachAny S z' z).mp hr)⟩

end SixBirds.Semantic
