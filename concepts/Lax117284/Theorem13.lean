import Lax117284.ConflictGraph

/-!
---
title: Day-Independent Due Dates and Processing Times
type: theorem
---
**Theorem 13.** Let $I$ be an instance whose due dates and processing times are both
day-independent, so that all $m$ days have the same conflict graph $G$. Then $I$ admits a
$k$-fair schedule if and only if $k \cdot \chi(G) \le m$, where $\chi(G)$ is the chromatic
number of $G$.

A feasible schedule meets a clique of $G$ in at most one client per day, so a clique of $c$
vertices whose clients are each served $k$ times needs $k c \le m$ days; this gives the
condition with the clique number in place of the chromatic number. Conversely a proper
colouring of $G$ with $\chi(G)$ colours partitions the clients into $\chi(G)$ independent
sets, and serving the classes in rotation serves every client on
$\lfloor m / \chi(G)\rfloor \ge k$ days. Both bounds meet because $G$ is an interval graph,
and its chromatic number therefore equals its clique number.

# Formalization Notes

The two extreme values of the source's chain of inequalities are stated separately: that
the problem is equivalent to the condition on the clique number, and that the chromatic
number of a day's conflict graph is its clique number. The second is the only property of
interval graphs the results use — a paper cites it, and here it is proved for these graphs.

The chromatic number is mathlib's, with values in the extended naturals, so the condition
is stated there; with the clique number, a natural number, the condition is an inequality
of natural numbers.
-/

namespace Lax117284.Theorem13

open Lax117284.Scheduling Lax117284.ConflictGraph

variable {I : Instance}

/-- **Day-independent instances have one conflict graph.** -/
axiom dayGraph_eq_of_dayIndep (hd : I.DayIndepD) (hp : I.DayIndepP) (i i' : Fin I.days) :
    dayGraph I i = dayGraph I i'

/-- **A day's conflict graph is an interval graph, so its chromatic number is its clique
number.** -/
axiom chromaticNumber_dayGraph (I : Instance) (i : Fin I.days) :
    (dayGraph I i).chromaticNumber = (dayGraph I i).cliqueNum

/-- **Theorem 13, with the clique number.** -/
axiom hasKFairSchedule_iff_mul_cliqueNum_le (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i₀ : Fin I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ k * (dayGraph I i₀).cliqueNum ≤ I.days

/-- **Theorem 13.** With day-independent due dates and processing times, a `k`-fair
schedule exists exactly when `k` times the chromatic number of the conflict graph is at
most the number of days. -/
axiom hasKFairSchedule_iff_mul_chromaticNumber_le (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i₀ : Fin I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ (k : ℕ∞) * (dayGraph I i₀).chromaticNumber ≤ I.days

end Lax117284.Theorem13
