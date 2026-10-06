namespace P2Representability

inductive Q where
  | q0
  | q1

deriving DecidableEq, Repr

inductive S where
  | alpha
  | beta
  | gamma

deriving DecidableEq, Repr

def Real : Q -> S -> Prop
  | .q0, .alpha => True
  | .q1, .beta => True
  | _, _ => False

def Representable (s : S) : Prop := ∃ q : Q, Real q s

def NonRepresentable (s : S) : Prop := ∀ q : Q, ¬ Real q s

inductive BehavioralStatus where
  | observedRepresentable (s : S)
  | observedNonRepresentable (s : S)

structure RepresentabilityCertificate (s : S) where
  witness : Q
  realizes : Real witness s

structure NonRepresentabilityCertificate (s : S) where
  noWitness : NonRepresentable s

theorem gamma_nonrepresentable : NonRepresentable .gamma := by
  intro q
  cases q <;> simp [Real]

theorem alpha_representable : Representable .alpha := by
  exact ⟨.q0, trivial⟩

theorem packaging_collapse
  (Q' : Type) [DecidableEq Q']
  (RealEq : Q' -> Q' -> Prop)
  (h : ∀ q s, RealEq q s ↔ q = s) :
  ∀ s : Q', ∃ q : Q', RealEq q s := by
  intro s
  exact ⟨s, (h s s).2 rfl⟩

end P2Representability
