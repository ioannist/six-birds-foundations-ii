namespace P2BoundaryStress

axiom Q : Type
axiom S : Type
axiom Real : Q -> S -> Prop

axiom packagingCollapse : Prop

axiom sameCardinalityNotNecessary : Prop
axiom sameCardinalityNotSufficient : Prop
axiom realCriterionIsStructural : Prop

inductive StressClassification where
  | collapses_to_P5
  | collapses_to_P5_up_to_equivalence
  | genuine_P2
  | P4_effect_not_P2_by_itself
  | verification_only
  | scope_gap
  | under_specified

axiom case1 : StressClassification
axiom case2 : StressClassification
axiom case3 : StressClassification
axiom case4 : StressClassification
axiom case5 : StressClassification
axiom case6 : StressClassification
axiom case7 : StressClassification
axiom case8 : StressClassification

end P2BoundaryStress
