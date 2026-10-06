namespace P4StagingExact

axiom J : Type
axiom Le : J -> J -> Prop
axiom Trans : J -> J -> Prop
axiom Refines : J -> J -> Prop

axiom le_reflexive : forall i : J, Le i i
axiom le_transitive : forall {i j k : J}, Le i j -> Le j k -> Le i k

structure NontrivialStageWitness where
  i : J
  j : J
  distinct : i ≠ j
  stage_relation : Le i j \/ Trans i j \/ Refines i j

structure VerificationP4 where
  validity_certificate :
    (forall i : J, Le i i) /\
    (forall {i j k : J}, Le i j -> Le j k -> Le i k)

structure StructuralP4 where
  stage_type : Type
  stage_relation : stage_type -> stage_type -> Prop
  transition_relation : stage_type -> stage_type -> Prop
  refinement_relation : stage_type -> stage_type -> Prop
  compatibility_laws : Prop

axiom bare_label_collapse : Prop
axiom finite_nontrivial_stage_model : Prop
axiom p4_distinct_from_p1 : Prop
axiom p4_distinct_from_p2 : Prop
axiom p4_distinct_from_p3 : Prop
axiom p4_distinct_from_p5 : Prop
axiom p4_distinct_from_p6 : Prop

end P4StagingExact
