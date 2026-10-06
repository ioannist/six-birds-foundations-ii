namespace P6AuditBookkeepingExact

axiom Event : Type
axiom Record : Type
axiom eventOf : Record -> Event
axiom Depends : Record -> Event -> Prop
axiom Checks : Record -> Event -> Prop
axiom forget : Record -> Event

inductive BehavioralP6 where
  | observedEvent (e : Event)
  | recordExists (r : Record)
  | recordRefers (r : Record) (e : Event)

structure VerificationP6 where
  record : Record
  event : Event
  event_ref : eventOf record = event
  checked : Checks record event

structure StructuralP6 where
  provenance : Record -> Event -> Prop
  replay : Record -> Event -> Prop
  validation : Record -> Event -> Prop
  forgetting : Record -> Event

axiom passive_observation_collapse : Prop
axiom certificate_collapse : Prop
axiom finite_nontrivial_audit_model : Prop
axiom boundary_theorems : Prop

end P6AuditBookkeepingExact
