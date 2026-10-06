import SixBirds.Semantic.Core

namespace SixBirds

theorem six_channels_fewer_than_six_active :
    ∃ (D : FATCD) (dec : DecompositionRecord D),
      WellFormedDecomposition dec ∧ SixChannels dec ∧
      ¬ SixActiveProjections dec := by
  refine ⟨witnessDescription Role.P1,
    defaultDecomposition (witnessDescription Role.P1),
    defaultDecomposition_wellFormed _, rfl, ?_⟩
  intro h
  have hp := h Role.P1
  simp [defaultDecomposition] at hp

theorem activeDecomposition_wellFormed (role : Role) :
    WellFormedDecomposition (activeDecomposition role) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact classifyResidual_covered
  · exact (activeDecomposition role).activeSound

theorem non_uniqueness_wellFormed :
    ∃ (D : FATCD) (dec₁ dec₂ : DecompositionRecord D),
      WellFormedDecomposition dec₁ ∧ WellFormedDecomposition dec₂ ∧
      dec₁.status Role.P1 ≠ dec₂.status Role.P1 := by
  refine ⟨witnessDescription Role.P1, activeDecomposition Role.P1,
    defaultDecomposition (witnessDescription Role.P1),
    activeDecomposition_wellFormed _, defaultDecomposition_wellFormed _, ?_⟩
  intro h
  simp [activeDecomposition, defaultDecomposition] at h

def minimalAuditedDescription : Description :=
  { raw := [rawRecord 1 RawKind.object]
    annotations := [ann AnnotationKind.audit 1,
      ann AnnotationKind.claim 1, ann AnnotationKind.nonclaim 1] }

def minimalFATCD : FATCD :=
  { desc := minimalAuditedDescription
    finite := by simp [FiniteDescription, minimalAuditedDescription, rawRecord, ann]
    closed := by simp [ClosedDescription, HasRawId, RawIds, minimalAuditedDescription, rawRecord, ann]
    audited := by
      simp [AuditedDescription, HasAnnotationKind, minimalAuditedDescription, ann] }

theorem non_circularity_concrete :
    ∃ D : FATCD, ∀ role : Role, ¬ Nonempty (DerivedRoleProjection D role) := by
  refine ⟨minimalFATCD, ?_⟩
  intro role h
  rcases h with ⟨h⟩
  have hc := h.collapseCasesRecorded
  simp [HasAnnotationKind, minimalFATCD, minimalAuditedDescription, ann] at hc

def rejectedRoleDescription : Description :=
  { raw := [rawRecord 1 RawKind.transition]
    annotations := [ann AnnotationKind.audit 1,
      ann AnnotationKind.claim 1, ann AnnotationKind.nonclaim 1] }

theorem non_overbreadth_concrete :
    ¬ RoleKindPresent rejectedRoleDescription Role.P3 := by
  intro h
  have hp := h RawKind.path (by decide)
  simp [HasRawKind, rejectedRoleDescription, rawRecord] at hp

end SixBirds
