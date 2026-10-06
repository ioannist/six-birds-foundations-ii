namespace P6BoundaryStress

inductive Classification where
  | event_only_not_P6
  | collapses_to_passive_observation
  | certificate_only_not_P6
  | genuine_P6_audit_of_certificate
  | genuine_P6
  | scope_gap_or_passive_log
  | P1_event_not_P6
  | genuine_P6_audit_of_P1
  | P2_event_not_P6
  | genuine_P6_audit_of_P2
  | P3_event_not_P6
  | genuine_P6_audit_of_P3
  | P4_only_not_P6
  | P5_only_not_P6
  | genuine_P6_audit_of_P5
  | partial_audit_scope_gap
  | under_specified

axiom passive_observation_boundary_survives : Prop
axiom certificate_boundary_survives : Prop
axiom P1_P2_P3_boundaries_survive : Prop
axiom P4_P5_boundaries_survive : Prop
axiom partial_audit_records_are_scope_gaps : Prop

end P6BoundaryStress
