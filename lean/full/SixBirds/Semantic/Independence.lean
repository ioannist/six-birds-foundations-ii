import SixBirds.Semantic.Witnesses

namespace SixBirds.Semantic

theorem no_p1_identity_lens (S : SemSystem n n k) (hq : S.q = id) : ¬ P1 S := by
  intro ⟨z, z', hz, hs⟩
  have heq : z = z' := by simpa [hq] using hz
  subst z'
  exact hs rfl

theorem no_p2_constant_target (S : SemSystem n m k) (a : Fin k)
    (ht : S.t = fun _ => a) : ¬ P2 S := by
  intro ⟨⟨z, z', h⟩, _⟩
  simp [ht] at h

theorem no_p3_equal_maps (S : SemSystem n m k) (h : S.F = S.G) : ¬ P3 S := by
  intro ⟨z, hz⟩
  simp [h] at hz

theorem no_p3_identity_G (S : SemSystem n m k) (h : S.G = id) : ¬ P3 S := by
  intro ⟨z, hz⟩
  simp [h] at hz

theorem no_p6_missing_log (S : SemSystem n m k) (h : S.log = none) : ¬ P6 S := by
  simp [P6, h]

private theorem walk_identity (S : SemSystem n m k)
    (hF : S.F = id) (hG : S.G = id)
    (z : Fin n) (choices : Fin n → Bool) (steps : Nat) :
    walk S z choices steps = z := by
  induction steps with
  | zero => rfl
  | succ j ih =>
    by_cases hj : j < n
    · simp only [walk, hj, dite_true]
      by_cases hc : choices ⟨j, hj⟩ = true
      · simp [hc, hF, ih]
      · simp [hc, hG, ih]
    · simp [walk, hj, hG, ih]

theorem no_p4_identity_maps (S : SemSystem n m k)
    (hF : S.F = id) (hG : S.G = id) : ¬ P4 S := by
  intro ⟨z, z', ⟨steps, choices, hz⟩, hback⟩
  have heq : z = z' := by simpa only [walk_identity S hF hG] using hz
  exact hback ⟨⟨0, by omega⟩, fun _ => false, by simpa [walk] using heq.symm⟩

theorem mismatch_reaches_all (a b : Fin 2) : Reach twoMismatch a b := by
  by_cases h : a = b
  · subst b
    exact ⟨⟨0, by decide⟩, fun _ => false, rfl⟩
  · have hab : twoMismatch.F a = b := by
      have ha : a = 0 ∨ a = 1 := by omega
      have hb : b = 0 ∨ b = 1 := by omega
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        subst a <;> subst b <;> simp [twoMismatch] at h ⊢
    exact ⟨⟨1, by decide⟩, fun _ => true, by simpa [walk] using hab⟩

theorem no_p4_twoMismatch : ¬ P4 twoMismatch := by
  intro ⟨z, z', _, h⟩
  exact h (mismatch_reaches_all z' z)

def cycle3 : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else if x = 1 then 2 else 0

def oneOnlySystem : SemSystem 3 2 2 :=
  { F := cycle3, G := cycle3,
    q := fun x => if x = 2 then 1 else 0,
    t := fun _ => 0 }

theorem oneOnly_p1 : P1 oneOnlySystem := by
  refine ⟨0, 1, by decide, by decide⟩

theorem oneOnly_no_p5 : ¬ P5 oneOnlySystem := by
  intro ⟨R, h⟩
  have step (a b : Fin 3) (hr : R a b = true) :
      R (cycle3 a) (cycle3 b) = true := h.2.2.2.1 a b hr
  have symm (a b : Fin 3) (hr : R a b = true) : R b a = true := by
    rw [← h.1.2.1]
    exact hr
  rcases h.2.1 with ⟨x, y, hxy, hr⟩
  have hx : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  have hy : y = 0 ∨ y = 1 ∨ y = 2 := by omega
  have h01 : R 0 1 = true := by
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;>
      subst x <;> subst y
    · exact False.elim (hxy rfl)
    · exact hr
    · simpa [cycle3] using step 2 0 (symm 0 2 hr)
    · exact symm 1 0 hr
    · exact False.elim (hxy rfl)
    · have h20 : R 2 0 = true := by simpa [cycle3] using step 1 2 hr
      simpa [cycle3] using step 2 0 h20
    · simpa [cycle3] using step 2 0 hr
    · have h12 : R 1 2 = true := symm 2 1 hr
      have h20 : R 2 0 = true := by simpa [cycle3] using step 1 2 h12
      simpa [cycle3] using step 2 0 h20
    · exact False.elim (hxy rfl)
  have h12 : R 1 2 = true := by simpa [cycle3] using step 0 1 h01
  have h20 : R 2 0 = true := by simpa [cycle3] using step 1 2 h12
  have h02 : R 0 2 = true := symm 2 0 h20
  rcases h.2.2.1 with ⟨a, b, hab⟩
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have htotal : R a b = true := by
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      subst a <;> subst b
    · exact h.1.1 0
    · exact h01
    · exact h02
    · exact symm 0 1 h01
    · exact h.1.1 1
    · exact h12
    · exact h20
    · exact symm 1 2 h12
    · exact h.1.1 2
  exact Bool.false_ne_true (hab.symm.trans htotal)

theorem oneOnly_reaches_all (a b : Fin 3) : Reach oneOnlySystem a b := by
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    subst a <;> subst b
  all_goals
    first
    | exact ⟨⟨0, by decide⟩, fun _ => true, by decide⟩
    | exact ⟨⟨1, by decide⟩, fun _ => true, by decide⟩
    | exact ⟨⟨2, by decide⟩, fun _ => true, by decide⟩

theorem oneOnly_no_p4 : ¬ P4 oneOnlySystem := by
  intro ⟨z, z', _, h⟩
  exact h (oneOnly_reaches_all z' z)

def OnlyRole (S : SemSystem n m k) (i : SixBirds.Role) : Prop :=
  Holds S i ∧ ∀ j, j ≠ i → ¬ Holds S j

theorem oneOnly_single : OnlyRole oneOnlySystem .P1 := by
  constructor
  · exact oneOnly_p1
  · intro j hj
    cases j with
    | P1 => exact False.elim (hj rfl)
    | P2 => exact no_p2_constant_target oneOnlySystem 0 rfl
    | P3 => exact no_p3_equal_maps oneOnlySystem rfl
    | P4 => exact oneOnly_no_p4
    | P5 => exact oneOnly_no_p5
    | P6 => exact no_p6_missing_log oneOnlySystem rfl

theorem twoIdentity_single : OnlyRole twoIdentity .P2 := by
  constructor
  · exact p2_concrete
  · intro j hj
    cases j with
    | P1 => exact no_p1_identity_lens twoIdentity rfl
    | P2 => exact False.elim (hj rfl)
    | P3 => exact no_p3_equal_maps twoIdentity rfl
    | P4 => exact no_p4_identity_maps twoIdentity rfl rfl
    | P5 => exact no_p5_on_two twoIdentity
    | P6 => exact no_p6_missing_log twoIdentity rfl

theorem twoMismatch_single : OnlyRole twoMismatch .P3 := by
  constructor
  · exact p3_concrete
  · intro j hj
    cases j with
    | P1 => exact no_p1_identity_lens twoMismatch rfl
    | P2 => exact no_p2_constant_target twoMismatch 0 rfl
    | P3 => exact False.elim (hj rfl)
    | P4 => exact no_p4_twoMismatch
    | P5 => exact no_p5_on_two twoMismatch
    | P6 => exact no_p6_missing_log twoMismatch rfl

theorem twoDirected_single : OnlyRole twoDirected .P4 := by
  constructor
  · exact p4_concrete
  · intro j hj
    cases j with
    | P1 => exact no_p1_identity_lens twoDirected rfl
    | P2 => exact no_p2_constant_target twoDirected 0 rfl
    | P3 => exact no_p3_identity_G twoDirected rfl
    | P4 => exact False.elim (hj rfl)
    | P5 => exact no_p5_on_two twoDirected
    | P6 => exact no_p6_missing_log twoDirected rfl

theorem threeQuotient_single : OnlyRole threeQuotient .P5 := by
  constructor
  · exact p5_concrete
  · intro j hj
    cases j with
    | P1 =>
      intro ⟨z, z', _, hs⟩
      simp [threeQuotient] at hs
    | P2 => exact no_p2_constant_target threeQuotient 0 rfl
    | P3 => exact no_p3_equal_maps threeQuotient rfl
    | P4 => exact no_p4_identity_maps threeQuotient rfl rfl
    | P5 => exact False.elim (hj rfl)
    | P6 => exact no_p6_missing_log threeQuotient rfl

theorem twoAudited_single : OnlyRole twoAudited .P6 := by
  constructor
  · exact p6_concrete
  · intro j hj
    cases j with
    | P1 => exact no_p1_identity_lens twoAudited rfl
    | P2 => exact no_p2_constant_target twoAudited 0 rfl
    | P3 => exact no_p3_equal_maps twoAudited rfl
    | P4 => exact no_p4_identity_maps twoAudited rfl rfl
    | P5 => exact no_p5_on_two twoAudited
    | P6 => exact False.elim (hj rfl)

theorem every_role_has_single_system (i : SixBirds.Role) :
    ∃ n m k, ∃ S : SemSystem n m k, OnlyRole S i := by
  cases i with
  | P1 => exact ⟨3, 2, 2, oneOnlySystem, oneOnly_single⟩
  | P2 => exact ⟨2, 2, 2, twoIdentity, twoIdentity_single⟩
  | P3 => exact ⟨2, 2, 2, twoMismatch, twoMismatch_single⟩
  | P4 => exact ⟨2, 2, 2, twoDirected, twoDirected_single⟩
  | P5 => exact ⟨3, 2, 2, threeQuotient, threeQuotient_single⟩
  | P6 => exact ⟨2, 2, 2, twoAudited, twoAudited_single⟩

theorem ordered_counterexample (i j : SixBirds.Role) (hij : i ≠ j) :
    ∃ n m k, ∃ S : SemSystem n m k, Holds S i ∧ ¬ Holds S j := by
  rcases every_role_has_single_system i with ⟨n, m, k, S, hi, hother⟩
  exact ⟨n, m, k, S, hi, hother j (Ne.symm hij)⟩

theorem semantic_pairwise_non_equivalent (i j : SixBirds.Role) (hij : i ≠ j) :
    ∃ n m k, ∃ S : SemSystem n m k,
      ¬ (Holds S i ↔ Holds S j) := by
  rcases ordered_counterexample i j hij with ⟨n, m, k, S, hi, hj⟩
  exact ⟨n, m, k, S, fun h => hj (h.mp hi)⟩

theorem ordered_implication_matrix (i j : SixBirds.Role) :
    (∀ n m k, ∀ S : SemSystem n m k, Holds S i → Holds S j) ∨
    (∃ n m k, ∃ S : SemSystem n m k, Holds S i ∧ ¬ Holds S j) := by
  by_cases hij : i = j
  · left
    subst j
    intro n m k S h
    exact h
  · right
    exact ordered_counterexample i j hij

end SixBirds.Semantic
