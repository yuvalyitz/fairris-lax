import Lax117284Proofs.Compose
import Lax117284Proofs.Machine.X3Final
import Lax117284.Theorem3
import Lax117284.TwoSatisfiability

/-!
Day-independent due dates and processing times: a fair schedule exists exactly when the parameter
times the largest number of jobs of a day that run at the instant one of them starts is at most the
number of days, which a word RAM program computes in quadratic time.
-/

namespace Lax117284Proofs.Theorem3Colouring

open Lax117284.Problems Lax434930.PolynomialTime

/--
---
conclusion: Lax117284.Theorem3.uniform_dayIndepD_dayIndepP_mem_P
---
The language is decided by a reduction to 2-satisfiability, which is in polynomial time, that
carries out the decision itself and writes a formula with no clause for a yes-instance and an
unsatisfiable formula for every other word. A word RAM program reads the instance and the
parameter, checks that every job takes some time and is not due before it starts, checks that every
day repeats the table of the first, counts for every client of the first day the jobs that run at
the instant its job starts — the clique number of the interval graph of the day, which is its
chromatic number — takes the largest of the counts, and compares the parameter times that count
with the number of days. An instance without days is a yes-instance exactly when the parameter is
zero or there is no client. The program runs in time quadratic in the length of the input.
-/
theorem uniform_dayIndepD_dayIndepP_mem_P :
    Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) ∈ P :=
  Compose.mem_P_of_manyOne
    ⟨Machine.X3Sem.reduceD, Machine.X3Final.reduceD_polyTime, Machine.X3Sem.reduceD_correct⟩
    Lax117284.TwoSatisfiability.twoSat_mem_P

end Lax117284Proofs.Theorem3Colouring
