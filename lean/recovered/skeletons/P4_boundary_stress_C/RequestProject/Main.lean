namespace P4BoundaryStress

universe u

axiom J : Type u
axiom Le : J -> J -> Prop
axiom Trans : J -> J -> Prop
axiom Refines : J -> J -> Prop

structure ValidPreorder where
  refl : forall j : J, Le j j
  trans : forall {i j k : J}, Le i j -> Le j k -> Le i k

structure ValidTransition where
  compositional : Prop
  compatible_with_stage : Prop

structure ValidRefinement where
  lawful : Prop
  compatible_with_stage : Prop

structure GenuineP4Witness where
  i : J
  j : J
  distinct : i ≠ j
  by_order : Prop
  by_transition : Prop
  by_refinement : Prop

axiom bare_label_collapse : Prop
axiom arbitrary_relation_scope_gap : Prop
axiom arbitrary_transition_scope_gap : Prop
axiom arbitrary_refinement_scope_gap : Prop
axiom valid_two_stage_preorder_model : Prop
axiom valid_transition_model : Prop
axiom valid_refinement_model : Prop
axiom structural_stage_tower_model : Prop

axiom p4_p1_boundary : Prop
axiom p4_p2_boundary : Prop
axiom p4_p3_boundary : Prop
axiom p4_p5_boundary : Prop
axiom p4_p6_boundary : Prop

end P4BoundaryStress
