# Foundations II semantic program report

## Verdict and grade

**Substantive, grade B−.** The added layer proves the six semantic roles are independently realizable, all thirty off-diagonal ordered implications fail, and the active-channel count takes every value from zero through six. It also proves a unique proof-carrying sound assignment for every finite system and the requested small repairs to the old layer. The remaining computational limitation is that decidability of finite function quantifiers uses classical choice rather than an executable enumeration. The old six-slot theorem remains unchanged.

## Mathematical model

A system consists of `Fin n`, endomaps F and G, a lens q to `Fin m`, a macro target t in `Fin k`, and an optional start/list audit log. P1 is a split pair for q and F; P2 is nonconstant factorization of t through q; P3 is failure of F and G to commute; P4 is asymmetric F/G reachability; P5 is a nontrivial congruence for both maps independent of q; P6 is a present, nonempty F-consistent replay log. Carrier equality is decidable.

P4 searches paths of at most n transitions, encoding each step by a Boolean choice. `reach_iff_reachAny` now proves this equivalent to unrestricted reflexive-transitive F/G reachability: repeated states are truncated from a path, and a path with distinct states has at most n vertices. `p4_iff_reachAny` transfers the P4 statement.

P5 quantifies over Boolean equivalence relations. `p5_iff_mathematical_congruence` proves equivalence to a relation-valued mathematical statement with reflexivity, symmetry, transitivity, a merged distinct pair, a separated pair, and preservation by F and G. The reverse direction uses classical decidability of the relation. The six predicate instances are logically decidable, but the P2/P4/P5 function-space searches are not executable finite enumerations. The sound-status constructor and active count consequently depend on `Classical.choice`.

The six single-role systems are: a three-cycle with a splitting lens for P1; a two-state identity system with nonconstant target for P2; a two-state noncommuting pair for P3; a two-state directed system for P4; a three-state identity system with a proper quotient for P5; and a logged two-state identity system for P6. These prove every unordered pair differs. For the full ordered matrix, the six diagonal implications are identities and **all 30 off-diagonal implications have concrete single-role counterexamples**. Thus no role is forced by a different role in this setting. P1 and P5 require at least three states; this size constraint is not a cross-role implication.

The all-role three-state system has F=(0,0,1), G=(0,0,2), q=t=(0,1,0), and log start 0 with list [0]. Its congruence merges states 0 and 1. A one-state identity system without a log has no active role. Modified systems give every intermediate count. `semantic_exact_six` proves unique sound assignment, the upper bound six, and examples for all counts 0,…,6; `statusActiveCount_eq_activeCount` connects that count to the sound statuses. Two lenses on the same updates give different sound P1 statuses.

## Coverage and remaining work

| Target | Result |
|---|---|
| S1 | The requested finite fields and optional replay log are formalized. Bounded and unrestricted reachability are now proved equivalent. |
| S2 | All six definitions and logical decidability are formalized; P5 has a genuine equivalence theorem. First decision attempt used core Lean finite quantifiers, which lack enumeration of function spaces. Second attempt considered coding finite tables; the code/surjectivity proof remains undone. The P4 loop-deletion bridge is complete. |
| S3 | Complete: six single-role systems, all 15 unordered distinctions, and the 6×6 implication matrix. The first search found a joint all-role example; the second, constructive pass proved singleton systems and their exclusions. All six single-role cases exist. |
| S4 | Complete for the formalized predicates: proof-carrying active/absent statuses, soundness both ways, uniqueness, counts 0–6, and lens non-uniqueness. A first pass established uniqueness and endpoints; a second constructed intermediate counts and transfer under unchanged F/G. |
| S5 | Complete under the old `WellFormedDecomposition`: six channels with fewer than six active; two well-formed differing records; concrete FATCD without derived projection; and a rejected role-named description. Old well-formedness still does not enforce semantic absence. |

## Verification and trust

The Round 2 `lake build` passed (19 jobs). The earlier `./scripts/validate_lean.sh --tier full --require-full` run reported **PARTIAL VALIDATION FAIL** because the existing paper manifests have six missing definition entries and twelve stale claim entries. Its build, 51 probes, 51 declaration checks, and 35 axiom audits passed; it found zero placeholders and zero semantic-audit findings. The validator checks the old paper manifest and does not certify the new semantic statements. The new modules contain no `sorry`, `admit`, `axiom`, or `native_decide`; no Mathlib was added and no commit was made.

Every new theorem was inspected with `#print axioms`. In this table `P` is `propext`, `Q` is `Quot.sound`, and `C` is `Classical.choice`.

| Axioms | New theorem names |
|---|---|
| None | `p5_iff_nontrivial_congruence`, `status_unique`, `no_p1_identity_lens` |
| P | `walk_same_transitions`, `p4_same_transitions`, `active_iff`, `absent_iff`, `identityLens_no_p1`, `mergeLens_p1`, `no_p2_constant_target`, `no_p3_equal_maps`, `no_p3_identity_G`, `no_p6_missing_log`, `oneOnly_p1`, `six_channels_fewer_than_six_active`, `p1_concrete`, `p2_concrete`, `p3_concrete`, `p4_concrete`, `p6_concrete`, `no_roles_active` |
| P, Q | `no_p4_identity_maps`, `mismatch_reaches_all`, `no_p4_twoMismatch`, `oneOnly_no_p5`, `oneOnly_reaches_all`, `oneOnly_no_p4`, `oneOnly_single`, `twoIdentity_single`, `twoMismatch_single`, `twoDirected_single`, `threeQuotient_single`, `twoAudited_single`, `every_role_has_single_system`, `ordered_counterexample`, `semantic_pairwise_non_equivalent`, `ordered_implication_matrix`, `activeDecomposition_wellFormed`, `non_uniqueness_wellFormed`, `non_circularity_concrete`, `non_overbreadth_concrete`, `p5_concrete`, `six_roles_inhabited`, `all_roles_active`, `no_p5_on_two` |
| P, C, Q | `p5_iff_mathematical_congruence`, `reach_iff_reachAny`, `p4_iff_reachAny`, `statusActiveCount_eq_activeCount`, `activeCount_le_six`, `count_zero`, `count_one`, `count_two`, `count_three`, `count_four`, `count_five`, `count_six`, `all_active_counts`, `semantic_exact_six`, `semantic_exact_six_unique`, `lens_non_uniqueness` |

The remaining proof work is an executable finite-table decision procedure for P2/P4/P5.
