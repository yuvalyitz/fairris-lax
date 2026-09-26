import Lax117284.Problems

/-!
---
title: Day-independent processing times
type: theorem
---
**Theorem 2.** The problem
$1 \mid \mathrm{rep},\, p_{i,j} = p_j \mid \min_j \sum_i Z_{i,j}$ is NP-hard. It is
solvable in polynomial time if $p_j = 1$ for every client $j$.

Hardness needs no more than three days and $k = 1$, and the instances the reduction
produces have all their processing times equal, which is a special case of
day-independence. With unit processing times two jobs of a day conflict exactly when they
have the same due date, and the problem becomes one of bipartite matching.

# Formalization notes

The hard half is stated for the class of instances whose processing times are
day-independent, and not for the smaller class of instances in which all processing times
are equal, because that is the restriction the source names. That the reduction lands in
the smaller class as well is a statement about the construction.
-/

namespace Lax117284.Theorem2

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

/-- **Theorem 2, hardness.** With day-independent processing times the problem remains
NP-hard. -/
axiom uniform_dayIndepP_npHard : NPHard (Uniform fun I _ => I.DayIndepP)

/-- **Theorem 2, tractability.** With unit processing times the problem is solvable in
polynomial time. -/
axiom uniform_unitP_mem_P : Uniform (fun I _ => I.UnitP) ∈ P

end Lax117284.Theorem2
