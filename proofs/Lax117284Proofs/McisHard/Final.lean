import Lax117284Proofs.McisHard.Machine.FinalPoly
import Lax117284Proofs.McisHard.MathFinal
import Lax117284Proofs.Compose
import Lax117284Proofs.BoundedSatProved

/-!
# NP-Hardness of Multicoloured Independent Set in Normal Form, from [2,3]-Bounded 3-Satisfiability

The closing theorem: the reduction `reduceMcis` is polynomial-time computable (`reduceMcis_polyTime`) and
correct (`Proved.reduceMcis_correct`), so the hardness of `BoundedSat` (`BoundedSatProved`) transfers.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard

/--
---
conclusion: Lax117284.MulticolouredIndepSet.normalMulticolouredIndepSet_npHard
---
Multicoloured Independent Set on the instances in normal form is NP-hard, by a many-one reduction from
[2,3]-bounded 3-satisfiability: a formula is sent to the graph `H` that is the union of `p + 10 S` copies
of the port graph of the formula's occurrences (every position with five gadget ports, a matched pair of
ports joining two gadgets and making two positions adjacent), which is regular, has an independent
transversal exactly when the formula is satisfiable, and is written bit by bit by a word RAM program.
-/
theorem normalMulticolouredIndepSet_npHard_proved :
    type_of% @Lax117284.MulticolouredIndepSet.normalMulticolouredIndepSet_npHard :=
  Lax117284Proofs.Compose.npHard_of_manyOne Lax117284Proofs.BoundedSatProved.boundedSat_npHard_proved
    ⟨reduceMcis, Final.reduceMcis_polyTime, Proved.reduceMcis_correct⟩

end Lax117284Proofs.McisHard

example : type_of% @Lax117284.MulticolouredIndepSet.normalMulticolouredIndepSet_npHard :=
  Lax117284Proofs.McisHard.normalMulticolouredIndepSet_npHard_proved
