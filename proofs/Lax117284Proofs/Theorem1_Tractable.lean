import Lax117284Proofs.Compose
import Lax117284Proofs.X1Word
import Lax117284Proofs.Machine.X1Final
import Lax117284.Theorem1
import Lax117284.TwoSatisfiability

/-!
The tractable values of the fairness parameter: a reduction to 2-satisfiability, and 2-satisfiability
is solvable in polynomial time.
-/

namespace Lax117284Proofs.Theorem1Tractable

open Lax117284.Problems Lax434930.PolynomialTime Lax429075.Reductions

/--
---
conclusion: Lax117284.Theorem1.uniform_extremes_mem_P
---
The three tractable values of the fairness parameter reduce, as one reduction, to 2-satisfiability.
A word that encodes an instance whose parameter is one below its number of days is sent to the
formula of Theorem 9. One whose parameter equals its number of days is sent to the conflict
clauses of that formula together with a clause asking for every variable to be true: the formula
is satisfiable exactly when no two jobs of a day conflict, which is when every client can be served
on every day. One whose parameter is zero is sent to a formula with no clause, since a client
served on no day is served enough. A word that encodes no instance with one of these parameters is
sent to an unsatisfiable formula. The reduction is a word RAM program on the zeros and ones of its
input, in the same way as the reduction of Theorem 9, and 2-satisfiability is in polynomial time.
-/
theorem uniform_extremes_mem_P :
    Uniform (fun I k => k = 0 ∨ k + 1 = I.days ∨ k = I.days) ∈ P :=
  Compose.mem_P_of_manyOne
    ⟨X1Word.reduceX, Machine.X1Final.reduceX_polyTime, X1Word.reduceX_correct⟩
    Lax117284.TwoSatisfiability.twoSat_mem_P

end Lax117284Proofs.Theorem1Tractable
