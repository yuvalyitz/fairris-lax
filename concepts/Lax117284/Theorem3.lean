import Lax117284.Problems

/-!
---
title: Day-Independent Due Dates
type: theorem
---
**Theorem 3.** The problem
$1 \mid \mathrm{rep},\, d_{i,j} = d_j \mid \min_j \sum_i Z_{i,j}$ is NP-hard. It is
solvable in polynomial time under either of two additional restrictions: (i) the number $m$
of days is a constant; (ii) the processing times are day-independent as well.

Hardness comes from the problem of maximizing the number of just-in-time jobs on unrelated
parallel machines. Under (i) a dynamic program over the clients in order of their due dates
decides the problem, carrying for each day the time at which its machine is next free.
Under (ii) every day has the same conflict graph, and a $k$-fair schedule exists exactly
when $k$ times the chromatic number of that graph is at most $m$.

# Formalization Notes

Restriction (i) is a constant of the slice rather than part of the input, so the claim is
one language per number of days. This is what "$m$ is a constant" means: the algorithm may
depend on $m$, and its running time is polynomial for each fixed $m$ while the exponent may
grow with $m$.
-/

namespace Lax117284.Theorem3

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

/-- **Theorem 3, hardness.** With day-independent due dates the problem remains
NP-hard. -/
axiom uniform_dayIndepD_npHard : NPHard (Uniform fun I _ => I.DayIndepD)

/-- **Theorem 3(i).** With day-independent due dates and a fixed number `m` of days the
problem is solvable in polynomial time. -/
axiom uniform_dayIndepD_days_mem_P (m : ℕ) :
    Uniform (fun I _ => I.DayIndepD ∧ I.days = m) ∈ P

/-- **Theorem 3(ii).** With day-independent due dates and day-independent processing times
the problem is solvable in polynomial time. -/
axiom uniform_dayIndepD_dayIndepP_mem_P :
    Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) ∈ P

end Lax117284.Theorem3
