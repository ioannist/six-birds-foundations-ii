import Mathlib

/-!
# Route Grammar Candidate A — Exactification with Non-Identity Fine Quotient Witness

This file formalizes Route Grammar Candidate A (typed free-category route grammar),
instantiates the supplied finite non-identity fine quotient witness model, and proves
all required properties for full enriched-P3 promotion.
-/

set_option maxHeartbeats 800000

/-! ## 1. Core Route Grammar Definitions -/

/-- Quotient stage indices. -/
structure Stage where
  idx : ℕ
  deriving DecidableEq, Repr

/-- Route terms in the typed free-category route grammar. -/
inductive RouteTerm : Type 1 where
  | identity (j : Stage) (carrier : Type) : RouteTerm
  | descent (j : Stage) (carrier : Type) (label : String) : RouteTerm
  | projection (k j : Stage) (ck cj : Type) : RouteTerm
  | comp (r s : RouteTerm) : RouteTerm

/-- A route is "generated" if it is built from identity, descent, projection, or composition. -/
def RouteTerm.isGenerated : RouteTerm → Prop
  | .identity _ _ => True
  | .descent _ _ _ => True
  | .projection _ _ _ _ => True
  | .comp r s => r.isGenerated ∧ s.isGenerated

/-- Record bundling a route with its source/target types and evaluation. -/
structure TypedRoute (S T : Type) where
  srcStage : Stage
  tgtStage : Stage
  eval : S → T
  term : RouteTerm

/-- Smart constructor for identity route. -/
def TypedRoute.id (j : Stage) (C : Type) : TypedRoute C C where
  srcStage := j
  tgtStage := j
  eval := _root_.id
  term := RouteTerm.identity j C

/-- Smart constructor for descent route. -/
def TypedRoute.desc (j : Stage) (C : Type) (label : String) (f : C → C) : TypedRoute C C where
  srcStage := j
  tgtStage := j
  eval := f
  term := RouteTerm.descent j C label

/-- Smart constructor for projection route. -/
def TypedRoute.proj (k j : Stage) (Ck Cj : Type) (p : Ck → Cj) : TypedRoute Ck Cj where
  srcStage := k
  tgtStage := j
  eval := p
  term := RouteTerm.projection k j Ck Cj

/-- Composition of typed routes. -/
def TypedRoute.compose (r : TypedRoute A B) (s : TypedRoute B C) : TypedRoute A C where
  srcStage := r.srcStage
  tgtStage := s.tgtStage
  eval := s.eval ∘ r.eval
  term := RouteTerm.comp r.term s.term

/-! ## 2. Finite Witness Model -/

/-- The fine quotient carrier: two equivalence classes. -/
inductive Qk : Type where
  | A : Qk
  | B : Qk
  deriving DecidableEq, Repr, Fintype

/-- The coarse quotient carrier: a single equivalence class. -/
inductive Qj : Type where
  | star : Qj
  deriving DecidableEq, Repr, Fintype

/-- The process soup carrier {1,2,3,4}. -/
inductive Proc : Type where
  | p1 : Proc
  | p2 : Proc
  | p3 : Proc
  | p4 : Proc
  deriving DecidableEq, Repr, Fintype

/-- Fine equivalence packaging map: {1,2} ↦ A, {3,4} ↦ B. -/
def packK : Proc → Qk
  | .p1 => .A
  | .p2 => .A
  | .p3 => .B
  | .p4 => .B

/-- Coarse equivalence packaging map: everything ↦ *. -/
def packJ : Proc → Qj
  | _ => .star

/-- Coarsening map: Q_k → Q_j. -/
def coarsen : Qk → Qj
  | _ => .star

/-- Update F: identity on P. -/
def updateF : Proc → Proc := _root_.id

/-- Update G: swaps fine classes. 1↔3, 2↔4. -/
def updateG : Proc → Proc
  | .p1 => .p3
  | .p2 => .p4
  | .p3 => .p1
  | .p4 => .p2

/-! ### Descent verification -/

/-- F descends at k: packK ∘ F respects the fine equivalence. -/
theorem F_descends_k : ∀ x y : Proc, packK x = packK y →
    packK (updateF x) = packK (updateF y) := by
  intro x y h; simp [updateF]; exact h

/-- G descends at k: packK ∘ G maps each fine class to a fine class. -/
theorem G_descends_k : ∀ x y : Proc, packK x = packK y →
    packK (updateG x) = packK (updateG y) := by
  intro x y h; cases x <;> cases y <;> simp_all [packK, updateG]

/-! ### Descended maps -/

/-- F#_k is the identity on Q_k. -/
def descF_k : Qk → Qk
  | q => q

/-- G#_k swaps A and B. -/
def descG_k : Qk → Qk
  | .A => .B
  | .B => .A

/-- F#_k agrees with the packaging: packK ∘ updateF = descF_k ∘ packK. -/
theorem descF_k_commutes : ∀ p : Proc, packK (updateF p) = descF_k (packK p) := by
  intro p; cases p <;> rfl

/-- G#_k agrees with the packaging: packK ∘ updateG = descG_k ∘ packK. -/
theorem descG_k_commutes : ∀ p : Proc, packK (updateG p) = descG_k (packK p) := by
  intro p; cases p <;> rfl

/-- F#_j and G#_j agree: Q_j is a singleton so all maps agree. -/
theorem coarse_maps_agree : ∀ q : Qj, q = Qj.star := by
  intro q; cases q; rfl

/-! ## 3. Non-Identity Fine Quotient Verification -/

/-- Q_k has exactly 2 elements. -/
theorem Qk_card : Fintype.card Qk = 2 := by decide

/-- Proc has exactly 4 elements. -/
theorem Proc_card : Fintype.card Proc = 4 := by decide

/-- The fine quotient is non-identity: |Q_k| < |P|, so packK is not injective. -/
theorem fine_quotient_nonidentity : Fintype.card Qk < Fintype.card Proc := by decide

/-- The fine quotient is non-trivial: |Q_k| > 1. -/
theorem fine_quotient_nontrivial : Fintype.card Qk > 1 := by decide

/-- packK is surjective (the quotient is well-formed). -/
theorem packK_surjective : Function.Surjective packK := by
  intro q; cases q
  · exact ⟨.p1, rfl⟩
  · exact ⟨.p3, rfl⟩

/-! ## 4. Route Construction and Same-Source Same-Target -/

def stageK : Stage := ⟨1⟩
def stageJ : Stage := ⟨0⟩

/-- Route 1: d(F, k) — descent of F at stage k. -/
def route1 : TypedRoute Qk Qk := TypedRoute.desc stageK Qk "F" descF_k

/-- Route 2: d(G, k) — descent of G at stage k. -/
def route2 : TypedRoute Qk Qk := TypedRoute.desc stageK Qk "G" descG_k

/-- Same source stage. -/
theorem same_source_stage : route1.srcStage = route2.srcStage := rfl

/-- Same target stage. -/
theorem same_target_stage : route1.tgtStage = route2.tgtStage := rfl

/-- Both routes have the same source and target TYPE (Qk),
    enforced by the shared type parameter. -/
theorem same_types : (route1 : TypedRoute Qk Qk).eval = descF_k ∧
    (route2 : TypedRoute Qk Qk).eval = descG_k :=
  ⟨rfl, rfl⟩

/-- Both routes are defined: both updates descend at k (so the descended maps exist). -/
theorem both_defined :
    (∀ x y : Proc, packK x = packK y → packK (updateF x) = packK (updateF y)) ∧
    (∀ x y : Proc, packK x = packK y → packK (updateG x) = packK (updateG y)) :=
  ⟨F_descends_k, G_descends_k⟩

/-! ## 5. Route Evaluation Disagreement -/

/-- The routes disagree on input A. This is genuine evaluation disagreement,
    not undefinedness. -/
theorem routes_disagree : route1.eval Qk.A ≠ route2.eval Qk.A := by decide

/-- Explicit values: route1 maps A↦A. -/
theorem route1_eval_A : route1.eval Qk.A = Qk.A := rfl

/-- Explicit values: route2 maps A↦B. -/
theorem route2_eval_A : route2.eval Qk.A = Qk.B := rfl

/-! ## 6. Generated Route Terms -/

/-- Route 1 is a generated route term (descent generator). -/
theorem route1_generated : route1.term.isGenerated := trivial

/-- Route 2 is a generated route term (descent generator). -/
theorem route2_generated : route2.term.isGenerated := trivial

/-! ## 7. Non-Reducibility Certificate -/

/-- The coarsened maps agree: coarsen ∘ F#_k = coarsen ∘ G#_k. -/
theorem coarsened_maps_agree : ∀ q : Qk, coarsen (descF_k q) = coarsen (descG_k q) := by
  intro q; cases q <;> rfl

/-- The fine maps disagree: F#_k ≠ G#_k as functions. -/
theorem fine_maps_disagree : descF_k ≠ descG_k := by
  intro h
  have : descF_k Qk.A = descG_k Qk.A := congrFun h Qk.A
  simp [descF_k, descG_k] at this

/-- The witness is NOT the forbidden descent/coarsening square.
    The forbidden square compares π(k,j) ∘ d(F,k) with d(F,j) ∘ π(k,j) for a SINGLE update.
    Our witness compares d(F,k) with d(G,k) — two DIFFERENT updates at the SAME stage. -/
theorem not_forbidden_square :
    ¬(∃ (label : String), route1.term = .descent stageK Qk label ∧
      route2.term = .projection stageK stageJ Qk Qj) ∧
    ¬(∃ (label : String), route1.term = .projection stageK stageJ Qk Qj ∧
      route2.term = .descent stageK Qk label) := by
  constructor
  · intro ⟨_, h1, h2⟩; cases h1; exact nomatch h2
  · intro ⟨_, h1, h2⟩; exact nomatch h1

/-- Quotient naturality does not force d(F,k) = d(G,k).
    Naturality constrains: for each update X, coarsen ∘ X#_k = X#_j ∘ coarsen.
    This is a constraint PER UPDATE, not across different updates.
    The model witnesses that F#_k ≠ G#_k is consistent with all naturality squares. -/
theorem naturality_consistent_with_disagreement :
    (∀ q : Qk, coarsen (descF_k q) = coarsen q) ∧
    (∀ q : Qk, coarsen (descG_k q) = coarsen q) ∧
    descF_k ≠ descG_k :=
  ⟨fun q => by cases q <;> rfl,
   fun q => by cases q <;> rfl,
   fine_maps_disagree⟩

/-! ## 8. P1/P3 Boundary Theorem -/

/-- P1 is descent failure: some update fails to descend at some stage.
    In our witness, BOTH F and G descend at k. Therefore this is not P1.
    The phenomenon is route mismatch (P3): two well-defined routes disagree. -/
theorem witness_is_P3_not_P1 :
    -- Both descend (not P1)
    (∀ x y : Proc, packK x = packK y → packK (updateF x) = packK (updateF y)) ∧
    (∀ x y : Proc, packK x = packK y → packK (updateG x) = packK (updateG y)) ∧
    -- Same source, same target, disagree (is P3)
    route1.srcStage = route2.srcStage ∧
    route1.tgtStage = route2.tgtStage ∧
    route1.eval Qk.A ≠ route2.eval Qk.A :=
  ⟨F_descends_k, G_descends_k, rfl, rfl, routes_disagree⟩

/-! ## 9. Composition Requirement -/

/-- Composition is present in the grammar and well-typed.
    We can compose route1 with route2 (both Q_k → Q_k). -/
def composedRoute : TypedRoute Qk Qk := TypedRoute.compose route1 route2

/-- The composed route evaluates correctly. -/
theorem composed_eval : composedRoute.eval = route2.eval ∘ route1.eval := rfl

/-- Naturality squares are expressible via composition. -/
def projRoute : TypedRoute Qk Qj := TypedRoute.proj stageK stageJ Qk Qj coarsen

/-- π ∘ d(F,k) is expressible. -/
def natSquareF_left : TypedRoute Qk Qj := TypedRoute.compose route1 projRoute

/-- The naturality equation holds for F: coarsen ∘ F#_k = coarsen. -/
theorem naturality_F : ∀ q : Qk, coarsen (descF_k q) = coarsen q := by
  intro q; cases q <;> rfl

/-- The naturality equation holds for G: coarsen ∘ G#_k = coarsen. -/
theorem naturality_G : ∀ q : Qk, coarsen (descG_k q) = coarsen q := by
  intro q; cases q <;> rfl
