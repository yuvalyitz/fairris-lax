import Lax117284.Scheduling

/-!
---
title: Unit processing times as a bipartite matching problem
type: theorem
---
**Theorem 10.** Let $I$ be an instance all of whose processing times are $1$ and let
$k \le m$. Consider the bipartite graph whose one side holds a vertex $v_{i,j}$ for every
day $i$ and client $j$, and whose other side holds a vertex $u_{i,t}$ for every day $i$ and
time $t$ together with $m - k$ vertices $w_{1,j}, \ldots, w_{m-k,j}$ for every client $j$;
join $v_{i,j}$ to $u_{i,d_{i,j}}$ and to all $m-k$ vertices $w_{\cdot,j}$. Then $I$ admits a
$k$-fair schedule if and only if this graph has a matching saturating every vertex
$v_{i,j}$.

With unit processing times two jobs of a day conflict exactly when their due dates agree,
so a day's machine may execute at most one job per due date; matching $v_{i,j}$ to
$u_{i,d_{i,j}}$ records that client $j$ is served on day $i$, and matching it to one of the
$m-k$ vertices $w_{\cdot,j}$ records that it is not. A matching saturating the job side
thus assigns every job either a slot of its day or one of the $m-k$ rejections client $j$ is
allowed.

# Formalization notes

A matching saturating the $n m$ vertices of the job side is an injective map from that side
whose values are neighbours of their arguments; stating it this way needs no cardinality
argument to see that the matching has $nm$ edges.

The far side is presented as a sum of the two families of vertices, and its time vertices
are indexed by a natural number, of which only the due dates occurring in the instance are
ever matched.
-/

namespace Lax117284.Theorem10

open Lax117284.Scheduling

variable (I : Instance)

/-- The far side of the bipartite graph: a slot vertex `u_{i,t}` for a day and a time, and
a rejection vertex `w_{l,j}` for a client. -/
def Target : Type := (Fin I.days × ℕ) ⊕ (ℕ × Fin I.clients)

/-- The edges of the bipartite graph: the job vertex `v_{i,j}` is joined to the slot vertex
of its own day and due date, and to the `m - k` rejection vertices of its own client. -/
def Matchable (k : ℕ) (v : Fin I.days × Fin I.clients) (t : Target I) : Prop :=
  t = Sum.inl (v.1, I.d v.1 v.2) ∨ ∃ l < I.days - k, t = Sum.inr (l, v.2)

/-- The bipartite graph has a matching saturating every job vertex. -/
def HasFullMatching (k : ℕ) : Prop :=
  ∃ f : Fin I.days × Fin I.clients → Target I,
    Function.Injective f ∧ ∀ v, Matchable I k v (f v)

/-- **With unit processing times, two jobs of a day conflict exactly when their due dates
agree.** -/
axiom conflict_iff_d_eq_of_unitP {I : Instance} (h : I.UnitP) (i : Fin I.days)
    (j j' : Fin I.clients) : I.Conflict i j j' ↔ I.d i j = I.d i j'

/-- **Theorem 10.** With unit processing times and `k ≤ m`, a `k`-fair schedule exists
exactly when the bipartite graph has a matching saturating every job vertex. -/
axiom hasKFairSchedule_iff_hasFullMatching {I : Instance} (h : I.UnitP) {k : ℕ}
    (hk : k ≤ I.days) : I.HasKFairSchedule k ↔ HasFullMatching I k

end Lax117284.Theorem10
