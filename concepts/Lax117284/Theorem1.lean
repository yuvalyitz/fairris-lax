import Lax117284.Problems

/-!
---
title: The Complexity of Fair Repetitive Interval Scheduling in the Fairness Parameter
type: theorem
---
**Theorem 1.** The problem $1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ is solvable in
polynomial time when $k \in \{0,\, m-1,\, m\}$. For every fixed pair $(m,k)$
with $0<k<m-1$, the problem is NP-hard.

The three tractable values are settled separately: $k = 0$ and $k = m$ by inspection of the
instance, and $k = m-1$ by a reduction to 2-satisfiability. Hardness holds already for
every fixed pair $(m, k)$ with $m \ge 3$ and $0 < k < m-1$; it is obtained for $(3,1)$ from
a satisfiability problem of bounded occurrence and lifted to all other pairs by two
constructions adding one day at a time.

# Formalization Notes

The tractable half is one claim about the language of all three cases at once. A word
belongs to that language only if its parameter is one of the three values, so an algorithm
deciding it must first read the parameter and compare it with the number of days; nothing is
gained by splitting the claim.

The hard half is stated for each fixed pair $(m, k)$ separately, which is the stronger
reading: the number of days is a constant of the slice rather than part of the input, so
hardness is not an artifact of letting $m$ grow with the instance.
-/

namespace Lax117284.Theorem1

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime

/-- **The tractable values of the fairness parameter.** The problem restricted to
instances whose fairness parameter is `0`, `m - 1` or `m` is solvable in polynomial
time. -/
axiom uniform_extremes_mem_P :
    Uniform (fun I k => k = 0 ∨ k + 1 = I.days ∨ k = I.days) ∈ P

/-- **Theorem 1.** For every fixed number `m ≥ 3` of days and every fairness parameter `k`
with `0 < k < m - 1`, the problem restricted to that pair is NP-hard. -/
axiom uniform_npHard (m k : ℕ) (hm : 3 ≤ m) (hk : 0 < k) (hk' : k + 1 < m) :
    NPHard (Uniform fun I k' => I.days = m ∧ k' = k)

end Lax117284.Theorem1
