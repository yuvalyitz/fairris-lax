import Lax117284Proofs.Compose
import Lax117284Proofs.Machine.D3ZeroFinal
import Lax117284Proofs.Machine.D3Final
import Lax117284.Theorem3
import Lax117284.TwoSatisfiability

/-!
Day-independent due dates with a fixed number of days: at zero days every schedule is vacuously
fair, decided directly; at a positive number of days a dynamic program over the clients in order
of their due dates decides the problem, carrying for each day the time at which its machine is
next free.
-/

namespace Lax117284Proofs.Theorem3Days

open Lax117284.Problems Lax434930.PolynomialTime

/-- **Theorem 3(i), zero days.** With no days, every schedule is vacuously fair and serves every
client on zero days, so the language is decided directly with no dynamic program. -/
theorem uniform_dayIndepD_days_zero_mem_P :
    Uniform (fun I _ => I.DayIndepD ∧ I.days = 0) ∈ P :=
  Compose.mem_P_of_manyOne
    ⟨Machine.D3Sem.reduceM 0, Machine.D3ZeroFinal.reduceM0_polyTime,
      Machine.D3Sem.reduceM_correct 0⟩
    Lax117284.TwoSatisfiability.twoSat_mem_P

/--
---
conclusion: Lax117284.Theorem3.uniform_dayIndepD_days_mem_P
---
The language is decided by a reduction to 2-satisfiability, which is in polynomial time, that
carries out the decision itself and writes a formula with no clause for a yes-instance and an
unsatisfiable formula for every other word. At zero days every schedule is vacuously fair, so a
word RAM program decides it directly from the day count, the parameter and the client count, with
no dynamic program needed. At a positive number `m` of days, a word RAM program reads the
instance, checks that every job takes some time and is not due before it starts, checks that the
due dates are day-independent, orders the clients by due date, and runs a dynamic program over
them that carries for each of the `m` days the time at which its machine is next free, deciding
whether the parameter is met. The number of days is a constant of the reduction rather than part
of its input, so the algorithm and its running time depend on `m`, with the exponent of the
polynomial growing with `m`.
-/
theorem uniform_dayIndepD_days_mem_P (m : ℕ) :
    Uniform (fun I _ => I.DayIndepD ∧ I.days = m) ∈ P := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact uniform_dayIndepD_days_zero_mem_P
  · exact Compose.mem_P_of_manyOne
      ⟨Machine.D3Sem.reduceM m, Machine.D3Final.reduceM_polyTime m hm,
        Machine.D3Sem.reduceM_correct m⟩
      Lax117284.TwoSatisfiability.twoSat_mem_P

end Lax117284Proofs.Theorem3Days
