namespace P1BoundaryStress

inductive StressCase where
  | packagingOnly
  | stageOnly
  | descentSuccess
  | descentObstruction
  | representabilityFailure
  | routeMismatch
  | routeUndefinedFromFailedDescent
  | invalidQuotient
  | unconditionalMacroMap
  | missingUpdate

inductive Classification where
  | p5OnlyNotP1
  | p4EffectNotP1ByItself
  | p1DescentCaseNotObstruction
  | genuineP1Obstruction
  | p2EffectNotP1ByItself
  | p3EffectNotP1
  | p1ObstructionNotP3Disagreement
  | scopeGapInvalidQuotient
  | scopeGapNotP1DescendedMap
  | p1UnderSpecifiedUntilUpdateSelected
  | underSpecified

axiom classify : StressCase -> Classification
axiom descent_and_obstruction_separated : Prop
axiom obstruction_rejects_unconditional_map : Prop
axiom p1_p5_boundary_survives : Prop
axiom p1_p4_boundary_survives : Prop
axiom p1_p2_boundary_survives : Prop
axiom p1_p3_boundary_survives : Prop

end P1BoundaryStress
