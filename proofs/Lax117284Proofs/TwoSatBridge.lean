import Lax117284Proofs.Compose
import Lax117284Proofs.TwoSatRename
import Lax117284Proofs.Machine.TsRenFinal
import Lax117284Proofs.TwoSAT.Machine.FinalP
import Lax117284.TwoSatisfiability

/-!
2-satisfiability of the scheduling submission is in polynomial time: its formulas reduce, by a
renaming of their variables, to the 2-SAT of `lax-429075`, which this submission proves to be
in polynomial time, and polynomial time is closed under polynomial-time reductions.
-/

namespace Lax117284Proofs.TwoSatBridge

open Lax434930.PolynomialTime Lax429075.Reductions

/--
---
conclusion: Lax117284.TwoSatisfiability.twoSat_mem_P
---
The formulas of this submission reduce to the 2-SAT of `lax-429075` by renaming: the variable of
every literal is replaced by the position of the first occurrence of that variable, so that the
unary code of `lax-429075` stays polynomial in the binary code of this submission, and renaming
along an injection preserves satisfiability in both directions. A word that is not the code of a
formula is sent to the code of a formula with one empty clause, which is unsatisfiable. The
reduction is a word RAM program on the zeros and ones of its input, in the same way as the
reductions of the theorems, and transfers to a Turing machine; 2-SAT of `lax-429075` is in
polynomial time by the algorithm of this submission, and polynomial time is closed under
polynomial-time reductions.
-/
theorem twoSat_mem_P : Lax117284.TwoSatisfiability.TwoSat ∈ P :=
  Compose.mem_P_of_manyOne
    ⟨TwoSatRename.reduceR, Machine.TsRenFinal.reduceR_polyTime, TwoSatRename.reduceR_correct⟩
    TwoSAT.Machine.FinalP.twoSAT_mem_P

end Lax117284Proofs.TwoSatBridge
