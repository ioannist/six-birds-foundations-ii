import SixBirds.Semantic.Independence

namespace SixBirds.Semantic

noncomputable def activeCount (S : SemSystem n m k) : Nat :=
  (if Holds S .P1 then 1 else 0) +
  (if Holds S .P2 then 1 else 0) +
  (if Holds S .P3 then 1 else 0) +
  (if Holds S .P4 then 1 else 0) +
  (if Holds S .P5 then 1 else 0) +
  (if Holds S .P6 then 1 else 0)

noncomputable def statusActiveCount (S : SemSystem n m k) : Nat := by
  classical
  exact
    (if (soundStatus S .P1).isActive then 1 else 0) +
    (if (soundStatus S .P2).isActive then 1 else 0) +
    (if (soundStatus S .P3).isActive then 1 else 0) +
    (if (soundStatus S .P4).isActive then 1 else 0) +
    (if (soundStatus S .P5).isActive then 1 else 0) +
    (if (soundStatus S .P6).isActive then 1 else 0)

theorem statusActiveCount_eq_activeCount (S : SemSystem n m k) :
    statusActiveCount S = activeCount S := by
  have h1 := active_iff S .P1 (soundStatus S .P1)
  have h2 := active_iff S .P2 (soundStatus S .P2)
  have h3 := active_iff S .P3 (soundStatus S .P3)
  have h4 := active_iff S .P4 (soundStatus S .P4)
  have h5 := active_iff S .P5 (soundStatus S .P5)
  have h6 := active_iff S .P6 (soundStatus S .P6)
  simp only [statusActiveCount, activeCount]
  simp [h1, h2, h3, h4, h5, h6]

theorem activeCount_le_six (S : SemSystem n m k) : activeCount S ≤ 6 := by
  have hb (r : SixBirds.Role) : (if Holds S r then 1 else 0) ≤ 1 := by
    split <;> omega
  have h1 := hb .P1
  have h2 := hb .P2
  have h3 := hb .P3
  have h4 := hb .P4
  have h5 := hb .P5
  have h6 := hb .P6
  unfold activeCount
  omega

theorem walk_same_transitions (S T : SemSystem n m k)
    (hF : S.F = T.F) (hG : S.G = T.G)
    (z : Fin n) (choices : Fin n → Bool) (steps : Nat) :
    walk S z choices steps = walk T z choices steps := by
  induction steps with
  | zero => rfl
  | succ j ih =>
    by_cases hj : j < n
    · by_cases hc : choices ⟨j, hj⟩ = true
      · simp [walk, hj, hc, hF, ih]
      · simp [walk, hj, hc, hG, ih]
    · simp [walk, hj, hG, ih]

theorem p4_same_transitions (S T : SemSystem n m k)
    (hF : S.F = T.F) (hG : S.G = T.G) : P4 S ↔ P4 T := by
  have hr (a b : Fin n) : Reach S a b ↔ Reach T a b := by
    constructor
    · intro ⟨steps, choices, h⟩
      exact ⟨steps, choices, (walk_same_transitions S T hF hG a choices steps.val).symm ▸ h⟩
    · intro ⟨steps, choices, h⟩
      exact ⟨steps, choices, (walk_same_transitions S T hF hG a choices steps.val) ▸ h⟩
  constructor
  · intro ⟨a, b, hab, hba⟩
    exact ⟨a, b, (hr a b).mp hab, fun h => hba ((hr b a).mpr h)⟩
  · intro ⟨a, b, hab, hba⟩
    exact ⟨a, b, (hr a b).mpr hab, fun h => hba ((hr b a).mp h)⟩

def twoActiveSystem : SemSystem 3 2 2 :=
  { threeQuotient with log := some { start := 0, states := [0] } }

def threeActiveSystem : SemSystem 3 3 3 :=
  { allRolesSystem with q := id, t := fun _ => 0, log := none }

def fourActiveSystem : SemSystem 3 3 3 :=
  { allRolesSystem with t := fun _ => 0, log := none }

def fiveActiveSystem : SemSystem 3 3 3 :=
  { allRolesSystem with log := none }

theorem count_zero : activeCount noRolesSystem = 0 := by
  simp [activeCount, no_roles_active]

theorem count_one : activeCount twoIdentity = 1 := by
  have h := twoIdentity_single
  have h1 : ¬ Holds twoIdentity .P1 := h.2 .P1 (by decide)
  have h3 : ¬ Holds twoIdentity .P3 := h.2 .P3 (by decide)
  have h4 : ¬ Holds twoIdentity .P4 := h.2 .P4 (by decide)
  have h5 : ¬ Holds twoIdentity .P5 := h.2 .P5 (by decide)
  have h6 : ¬ Holds twoIdentity .P6 := h.2 .P6 (by decide)
  simp [activeCount, h1, h.1, h3, h4, h5, h6]

theorem count_two : activeCount twoActiveSystem = 2 := by
  have h1 : ¬ P1 twoActiveSystem := by
    intro ⟨z, z', _, h⟩
    simp [twoActiveSystem, threeQuotient] at h
  have h2 : ¬ P2 twoActiveSystem := no_p2_constant_target _ 0 rfl
  have h3 : ¬ P3 twoActiveSystem := no_p3_equal_maps _ rfl
  have h4 : ¬ P4 twoActiveSystem := no_p4_identity_maps _ rfl rfl
  have h5 : P5 twoActiveSystem := p5_concrete
  have h6 : P6 twoActiveSystem := by simp [P6, twoActiveSystem, Replay, threeQuotient]
  simp [activeCount, Holds, h1, h2, h3, h4, h5, h6]

theorem count_three : activeCount threeActiveSystem = 3 := by
  rcases all_roles_active with ⟨_, _, h3, h4, h5, _⟩
  have h1 : ¬ P1 threeActiveSystem := no_p1_identity_lens _ rfl
  have h2 : ¬ P2 threeActiveSystem := no_p2_constant_target _ 0 rfl
  have h6 : ¬ P6 threeActiveSystem := no_p6_missing_log _ rfl
  have h3' : P3 threeActiveSystem := h3
  have h4' : P4 threeActiveSystem :=
    (p4_same_transitions allRolesSystem threeActiveSystem rfl rfl).mp h4
  have h5' : P5 threeActiveSystem := h5
  simp [activeCount, Holds, h1, h2, h3', h4', h5', h6]

theorem count_four : activeCount fourActiveSystem = 4 := by
  rcases all_roles_active with ⟨h1, _, h3, h4, h5, _⟩
  have h2 : ¬ P2 fourActiveSystem := no_p2_constant_target _ 0 rfl
  have h6 : ¬ P6 fourActiveSystem := no_p6_missing_log _ rfl
  have h1' : P1 fourActiveSystem := h1
  have h3' : P3 fourActiveSystem := h3
  have h4' : P4 fourActiveSystem :=
    (p4_same_transitions allRolesSystem fourActiveSystem rfl rfl).mp h4
  have h5' : P5 fourActiveSystem := h5
  simp [activeCount, Holds, h1', h2, h3', h4', h5', h6]

theorem count_five : activeCount fiveActiveSystem = 5 := by
  rcases all_roles_active with ⟨h1, h2, h3, h4, h5, _⟩
  have h6 : ¬ P6 fiveActiveSystem := no_p6_missing_log _ rfl
  have h1' : P1 fiveActiveSystem := h1
  have h2' : P2 fiveActiveSystem := h2
  have h3' : P3 fiveActiveSystem := h3
  have h4' : P4 fiveActiveSystem :=
    (p4_same_transitions allRolesSystem fiveActiveSystem rfl rfl).mp h4
  have h5' : P5 fiveActiveSystem := h5
  simp [activeCount, Holds, h1', h2', h3', h4', h5', h6]

theorem count_six : activeCount allRolesSystem = 6 := by
  rcases all_roles_active with ⟨h1, h2, h3, h4, h5, h6⟩
  simp [activeCount, Holds, h1, h2, h3, h4, h5, h6]

theorem all_active_counts (c : Fin 7) :
    ∃ n m k, ∃ S : SemSystem n m k, activeCount S = c.val := by
  have hc : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨
      c.val = 4 ∨ c.val = 5 ∨ c.val = 6 := by omega
  rcases hc with hc | hc | hc | hc | hc | hc | hc
  · exact ⟨1, 1, 1, noRolesSystem, count_zero.trans hc.symm⟩
  · exact ⟨2, 2, 2, twoIdentity, count_one.trans hc.symm⟩
  · exact ⟨3, 2, 2, twoActiveSystem, count_two.trans hc.symm⟩
  · exact ⟨3, 3, 3, threeActiveSystem, count_three.trans hc.symm⟩
  · exact ⟨3, 3, 3, fourActiveSystem, count_four.trans hc.symm⟩
  · exact ⟨3, 3, 3, fiveActiveSystem, count_five.trans hc.symm⟩
  · exact ⟨3, 3, 3, allRolesSystem, count_six.trans hc.symm⟩

theorem semantic_exact_six :
    (∀ n m k, ∀ S : SemSystem n m k,
      ∃ assignment : SoundAssignment S,
        ∀ other : SoundAssignment S, assignment = other) ∧
    (∀ n m k, ∀ S : SemSystem n m k, activeCount S ≤ 6) ∧
    (∀ c : Fin 7, ∃ n m k, ∃ S : SemSystem n m k,
      activeCount S = c.val) := by
  exact ⟨fun n m k S => semantic_exact_six_unique S,
    fun n m k S => activeCount_le_six S,
    all_active_counts⟩

end SixBirds.Semantic
