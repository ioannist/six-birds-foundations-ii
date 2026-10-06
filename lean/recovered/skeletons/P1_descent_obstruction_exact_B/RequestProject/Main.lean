namespace P1DescentObstructionExact

axiom P : Type
axiom Rel : P -> P -> Prop
axiom Q : Type
axiom Pi : P -> Q
axiom F : P -> P

abbrev Descends : Prop :=
  ∀ ⦃x y : P⦄, Rel x y -> Rel (F x) (F y)

structure ObstructionWitness where
  x : P
  y : P
  related : Rel x y
  separated : ¬ Rel (F x) (F y)

inductive BehavioralP1 where
  | descends
  | obstructed

inductive VerificationP1 where
  | descentProof (h : Descends)
  | obstruction (w : ObstructionWitness)

structure DescendedMapData where
  map : Q -> Q
  respects : Descends

structure ObstructionCase where
  witness : ObstructionWitness
  notWellDefined : Prop

inductive CategoricalP1 where
  | descentCase (data : DescendedMapData)
  | obstructionCase (data : ObstructionCase)

axiom descent_to_map_theorem : Descends -> ∃ g : Q -> Q, True
axiom obstruction_blocks_map_theorem : ObstructionWitness -> Prop
axiom p1_p5_boundary : Prop
axiom p1_p4_boundary : Prop
axiom p1_p2_boundary : Prop
axiom p1_p3_boundary : Prop

end P1DescentObstructionExact
