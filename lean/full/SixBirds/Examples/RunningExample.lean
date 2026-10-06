import SixBirds.Semantic.Core

namespace SixBirds
namespace Examples

def exampleF : Fin 4 → Fin 4
  | 0 => 2
  | 1 => 0
  | 2 => 3
  | _ => 1

def exampleQ : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | _ => 1

def exampleSystem : Semantic.SemSystem 4 2 2 :=
  { F := exampleF, G := id, q := exampleQ, t := fun _ => 0,
    log := some ⟨0, [2, 3]⟩ }

theorem example_split : Semantic.P1 exampleSystem := by
  refine ⟨0, 1, ?_, ?_⟩ <;> decide

theorem example_check : exampleF 0 = 2 ∧ exampleF 2 = 3 := by
  decide

theorem example_replay : Semantic.P6 exampleSystem := by
  simp [Semantic.P6, Semantic.Replay, exampleSystem, exampleF]

theorem example_partition_equivalence :
    Equivalence (fun x y : Fin 4 => exampleQ x = exampleQ y) := by
  constructor
  · intro x; rfl
  · intro x y h; exact h.symm
  · intro x y z hxy hyz; exact hxy.trans hyz

theorem example_classes :
    (∀ x : Fin 4, exampleQ x = 0 ↔ x = 0 ∨ x = 1) ∧
    (∀ x : Fin 4, exampleQ x = 1 ↔ x = 2 ∨ x = 3) := by
  decide

theorem example_lens_not_congruence :
    ¬ (∀ x y : Fin 4, exampleQ x = exampleQ y →
      exampleQ (exampleF x) = exampleQ (exampleF y)) := by
  intro h
  have bad := h 0 1 (by decide)
  simp [exampleQ, exampleF] at bad

-- The raw reference list on the map is four (input, output) pairs.
def exampleRaw : List RawRecord :=
  [rawRecord 0 .state, rawRecord 1 .state, rawRecord 2 .state, rawRecord 3 .state,
   rawRecord 10 .object,
   { ident := 11, kind := .map, finiteFields := true, refs := [0, 2, 1, 0, 2, 3, 3, 1] },
   { ident := 12, kind := .relation, finiteFields := true, refs := [0, 1, 2, 3] },
   { ident := 13, kind := .comparison, finiteFields := true, refs := [0, 1, 11, 12] },
   { ident := 14, kind := .trace, finiteFields := true, refs := [0, 2, 3] },
   { ident := 15, kind := .replay, finiteFields := true, refs := [14, 11] },
   { ident := 16, kind := .check, finiteFields := true, refs := [14, 11] },
   { ident := 17, kind := .index, finiteFields := true, refs := [12] },
   { ident := 18, kind := .transition, finiteFields := true, refs := [11] },
   { ident := 19, kind := .event, finiteFields := true, refs := [14] },
   { ident := 20, kind := .provenance, finiteFields := true, refs := [14] }]

def exampleAnnotations : List Annotation :=
  [ann .threshold 11, ann .witness 11, ann .level 11, ann .collapse 11, ann .audit 11,
   ann .threshold 12, ann .witness 12, ann .level 12, ann .collapse 12, ann .audit 12,
   ann .threshold 14, ann .witness 14, ann .level 14, ann .collapse 14, ann .audit 14,
   ann .claim 11, ann .nonclaim 11, ann .promotion 11, ann .lift 11, ann .forget 11]

def exampleDescription : Description :=
  { raw := exampleRaw, annotations := exampleAnnotations }

def runningExample : FATCD :=
  { desc := exampleDescription
    finite := by simp [FiniteDescription, exampleDescription, exampleRaw,
      exampleAnnotations, rawRecord, ann]
    closed := by simp [ClosedDescription, exampleDescription, exampleRaw,
      exampleAnnotations, HasRawId, RawIds, rawRecord, ann]
    audited := by simp [AuditedDescription, HasAnnotationKind, exampleDescription,
      exampleAnnotations, ann] }

theorem transition_without_threshold :
    (∃ r ∈ runningExample.desc.raw, r.kind = .transition ∧ r.refs = [11]) ∧
    (∀ a ∈ runningExample.desc.annotations, a.kind = .threshold → a.target ≠ 18) := by
  constructor
  · refine ⟨{ ident := 18, kind := .transition, finiteFields := true, refs := [11] }, ?_, rfl, rfl⟩
    simp [runningExample, exampleDescription, exampleRaw]
  · intro a ha hkind
    simp [runningExample, exampleDescription, exampleAnnotations, ann] at ha
    rcases ha with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
      <;> subst a <;> simp at hkind ⊢

def exampleP1P5Cluster : List RawRecord :=
  [rawRecord 10 .object,
   { ident := 12, kind := .relation, finiteFields := true, refs := [0, 1, 2, 3] },
   { ident := 11, kind := .map, finiteFields := true, refs := [0, 2, 1, 0, 2, 3, 3, 1] },
   { ident := 13, kind := .comparison, finiteFields := true, refs := [0, 1, 11, 12] }]

def exampleP6Cluster : List RawRecord :=
  [{ ident := 14, kind := .trace, finiteFields := true, refs := [0, 2, 3] },
   { ident := 19, kind := .event, finiteFields := true, refs := [14] },
   { ident := 20, kind := .provenance, finiteFields := true, refs := [14] },
   { ident := 15, kind := .replay, finiteFields := true, refs := [14, 11] },
   { ident := 16, kind := .check, finiteFields := true, refs := [14, 11] }]

private theorem p1p5_cluster_mem :
    ∀ r ∈ exampleP1P5Cluster, r ∈ runningExample.desc.raw := by
  intro r h
  simp [exampleP1P5Cluster] at h
  rcases h with h | h | h | h <;> subst r <;>
    simp [runningExample, exampleDescription, exampleRaw]

private theorem p6_cluster_mem :
    ∀ r ∈ exampleP6Cluster, r ∈ runningExample.desc.raw := by
  intro r h
  simp [exampleP6Cluster] at h
  rcases h with h | h | h | h | h <;> subst r <;>
    simp [runningExample, exampleDescription, exampleRaw]

def p1Attachment : ThresholdAttachment runningExample .P1 :=
  { cluster := exampleP1P5Cluster
    cluster_nonempty := by simp [exampleP1P5Cluster]
    cluster_from_description := p1p5_cluster_mem
    threshold := ann .threshold 11
    threshold_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    thresholdIsDeclared := rfl
    thresholdTargetsCluster := by simp [exampleP1P5Cluster, ann]
    witness := ann .witness 11
    witness_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    witnessIsDeclared := rfl
    level := .verification
    collapseRecorded := ⟨ann .collapse 11, by simp [runningExample, exampleDescription, exampleAnnotations], rfl⟩
    auditRecorded := runningExample.audited.left }

def p5Attachment : ThresholdAttachment runningExample .P5 :=
  { cluster := exampleP1P5Cluster
    cluster_nonempty := by simp [exampleP1P5Cluster]
    cluster_from_description := p1p5_cluster_mem
    threshold := ann .threshold 12
    threshold_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    thresholdIsDeclared := rfl
    thresholdTargetsCluster := by simp [exampleP1P5Cluster, ann]
    witness := ann .witness 12
    witness_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    witnessIsDeclared := rfl
    level := .verification
    collapseRecorded := ⟨ann .collapse 12, by simp [runningExample, exampleDescription, exampleAnnotations], rfl⟩
    auditRecorded := runningExample.audited.left }

def p6Attachment : ThresholdAttachment runningExample .P6 :=
  { cluster := exampleP6Cluster
    cluster_nonempty := by simp [exampleP6Cluster]
    cluster_from_description := p6_cluster_mem
    threshold := ann .threshold 14
    threshold_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    thresholdIsDeclared := rfl
    thresholdTargetsCluster := by simp [exampleP6Cluster, ann]
    witness := ann .witness 14
    witness_in_description := by simp [runningExample, exampleDescription, exampleAnnotations]
    witnessIsDeclared := rfl
    level := .verification
    collapseRecorded := ⟨ann .collapse 14, by simp [runningExample, exampleDescription, exampleAnnotations], rfl⟩
    auditRecorded := runningExample.audited.left }

private theorem example_lift_forget :
    HasAnnotationKind runningExample.desc .lift ∧
    HasAnnotationKind runningExample.desc .forget := by
  constructor
  · exact ⟨ann .lift 11, by simp [runningExample, exampleDescription, exampleAnnotations], rfl⟩
  · exact ⟨ann .forget 11, by simp [runningExample, exampleDescription, exampleAnnotations], rfl⟩

def p1Projection : DerivedRoleProjection runningExample .P1 :=
  { attachment := p1Attachment
    aligned := by simp [AlignedProjection, roleRawKinds, p1Attachment, exampleP1P5Cluster, rawRecord]
    collapseCasesRecorded := p1Attachment.collapseRecorded
    lossesAndLiftsRecorded := example_lift_forget
    nonclaimsPreserved := runningExample.audited.right.right }

def p5Projection : DerivedRoleProjection runningExample .P5 :=
  { attachment := p5Attachment
    aligned := by simp [AlignedProjection, roleRawKinds, p5Attachment, exampleP1P5Cluster, rawRecord]
    collapseCasesRecorded := p5Attachment.collapseRecorded
    lossesAndLiftsRecorded := example_lift_forget
    nonclaimsPreserved := runningExample.audited.right.right }

def p6Projection : DerivedRoleProjection runningExample .P6 :=
  { attachment := p6Attachment
    aligned := by simp [AlignedProjection, roleRawKinds, p6Attachment, exampleP6Cluster]
    collapseCasesRecorded := p6Attachment.collapseRecorded
    lossesAndLiftsRecorded := example_lift_forget
    nonclaimsPreserved := runningExample.audited.right.right }

def runningStatus : Role → ChannelStatus
  | .P1 | .P5 | .P6 => .activeProjection
  | .P4 => .belowThreshold
  | .P2 | .P3 => .absentWithRecord

def runningClassify (r : RawRecord) : ResidualClass :=
  if r.ident = 17 then .presentationVariant else classifyResidual r

def runningDecomposition : DecompositionRecord runningExample :=
  { status := runningStatus
    classify := runningClassify
    classifyCovered := by
      intro r
      by_cases h : r.ident = 17
      · simp [runningClassify, h, CoveredResidualClass]
      · simpa [runningClassify, h] using classifyResidual_covered r
    activeSound := by
      intro role h kind hk
      cases role <;> simp [runningStatus] at h
      all_goals
        simp [roleRawKinds] at hk
        rcases hk with hk | hk | hk | hk <;> subst kind <;>
          simp [HasRawKind, runningExample, exampleDescription, exampleRaw, rawRecord]
    exactChannels := primitiveRoles_length
    auditCarried := runningExample.audited
    nonclaimsCarried := true }

theorem runningDecomposition_wellFormed :
    WellFormedDecomposition runningDecomposition := by
  exact ⟨rfl, rfl, rfl, runningDecomposition.classifyCovered,
    runningDecomposition.activeSound⟩

theorem index_is_presentation_variant :
    ∃ r ∈ runningExample.desc.raw,
      r.kind = .index ∧ runningDecomposition.classify r = .presentationVariant := by
  refine ⟨{ ident := 17, kind := .index, finiteFields := true, refs := [12] }, ?_, rfl, rfl⟩
  simp [runningExample, exampleDescription, exampleRaw]

theorem running_statuses :
    runningDecomposition.status .P1 = .activeProjection ∧
    runningDecomposition.status .P2 = .absentWithRecord ∧
    runningDecomposition.status .P3 = .absentWithRecord ∧
    runningDecomposition.status .P4 = .belowThreshold ∧
    runningDecomposition.status .P5 = .activeProjection ∧
    runningDecomposition.status .P6 = .activeProjection := by
  decide

end Examples
end SixBirds
