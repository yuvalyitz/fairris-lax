import Lax117284.TwoSatCNF
import Mathlib.Logic.Relation

/-!
---
title: The implication graph of a 2-CNF formula
type: definition
---
The implication graph of a 2-CNF formula is the directed graph on the literals in which a
clause $(a \lor b)$ contributes the two edges $\lnot a \to b$ and $\lnot b \to a$, and a unit
clause $(a)$ the edge $\lnot a \to a$. An edge $u \to v$ says that any assignment making $u$ true
must make $v$ true, and so does a path. A variable $x$ is *contradictory* when $x$ reaches
$\lnot x$ and $\lnot x$ reaches $x$.

# Formalization notes

The graph is a relation on all literals, with no vertex set: a literal that no clause mentions
has no edges, and reachability is the reflexive-transitive closure of the edge relation. The
algorithm restricts its attention to the literals whose index is below a bound; that is its
business, and the criterion is stated for the graph as a whole.

The edge relation is written by the shape of the clause. A clause of one literal $b$ gives
$\lnot b \to b$; a clause $[a', b]$ gives $\lnot a' \to b$ and, read from the other end,
$\lnot b \to a'$. A clause with two copies of the same literal gives one edge twice, and a
clause with more than two literals gives no edge at all, since the graph is only meant for
formulas in 2-CNF.
-/

namespace Lax117284.TwoSatImplicationGraph

open Lax429075.CNF

/-- The negation of a literal: the same variable, the opposite sign. -/
def negate (l : Literal) : Literal := ⟨l.index, !l.positive⟩

/-- The positive literal of the variable `x`. -/
def pos (x : ℕ) : Literal := ⟨x, true⟩

/-- The negative literal of the variable `x`. -/
def neg (x : ℕ) : Literal := ⟨x, false⟩

/-- **The edges of the implication graph**: `a → b` when some clause is `[b]` with `a = ¬b`, or
some clause is `[¬a, b]` or `[b, ¬a]`. -/
def Implies (F : Formula) (a b : Literal) : Prop :=
  ∃ C ∈ F, (C = [b] ∧ a = negate b) ∨ C = [negate a, b] ∨ C = [b, negate a]

/-- **Reachability** in the implication graph, by a path of any length including zero. -/
def Reaches (F : Formula) : Literal → Literal → Prop := Relation.ReflTransGen (Implies F)

/-- **A contradictory variable**: it reaches its negation, and its negation reaches it. -/
def Contradictory (F : Formula) (x : ℕ) : Prop :=
  Reaches F (pos x) (neg x) ∧ Reaches F (neg x) (pos x)

end Lax117284.TwoSatImplicationGraph
