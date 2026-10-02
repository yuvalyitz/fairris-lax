import Lax117284.TwoSatImplicationGraph
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Iterate

/-!
---
title: The Algorithm: Reachability in the Implication Graph, One Variable at a Time
type: definition
---
The algorithm decides a formula in three steps. It rejects if some clause is empty or has more
than two literals. It builds the implication graph on the literals whose variable index is below
one more than the largest index that occurs. Then, for each variable $x$ that occurs, it
computes the set of literals reachable from $x$ by a breadth-first search and, if $\lnot x$ is
among them, the set reachable from $\lnot x$; it rejects if $x$ is among those. If no variable is
rejected the formula is accepted.

# Formalization Notes

The breadth-first search is written as what it computes: starting from the singleton of the
source, add the successors of every literal in the current set, and repeat as many times as
there are literals in the graph. Every literal at distance $d$ from the source is in the set
after $d$ rounds, and no round adds anything not reachable, so the final set is exactly the set
of reachable literals. The machine program computes the same set with a queue, visiting every
literal at most once, which is what makes a search cost linear in the size of the graph.

The nodes of the graph are the literals with index below `indexBound`, and the successors of a
literal are its out-neighbours among them. Reachability from a literal that occurs never
leaves the nodes, since every edge joins two literals of one clause, so the restriction loses
nothing; it is there so that the sets are finite and the search terminates.

The decision is a Boolean, computed by Boolean operations over lists and finite sets, so
`decide F` is a definition that Lean can evaluate; it is the specification the machine program
is proved to implement. The result is stated as a function of the formula; on the machine it is
a function of the word, through the decoder of `lax-429075`.
-/

namespace Lax117284.TwoSatAlgorithm

open Lax429075.CNF Lax117284.TwoSatCNF Lax117284.TwoSatImplicationGraph

/-- One more than the largest variable index occurring in `F`, and `0` for no literal. -/
def indexBound (F : Formula) : ℕ := (literals F).foldr (fun l n => max (l.index + 1) n) 0

/-- The nodes of the graph the algorithm searches: the literals with index below the bound. -/
def nodes (F : Formula) : Finset Literal :=
  (Finset.range (indexBound F) ×ˢ (Finset.univ : Finset Bool)).image fun p => ⟨p.1, p.2⟩

instance (F : Formula) : DecidableRel (Implies F) := by
  unfold Implies; infer_instance

/-- The successors of a literal among the nodes. -/
def successors (F : Formula) (a : Literal) : Finset Literal :=
  (nodes F).filter fun b => Implies F a b

/-- One round of the search: add the successors of every literal in the set. -/
def expand (F : Formula) (S : Finset Literal) : Finset Literal := S ∪ S.biUnion (successors F)

/-- **The literals reachable from `s`**: the set the breadth-first search from `s` marks, here
as the result of as many rounds of expansion as there are nodes. -/
def reachable (F : Formula) (s : Literal) : Finset Literal := (expand F)^[(nodes F).card] {s}

/-- Every clause has one or two literals. -/
def widthOk (F : Formula) : Bool := F.all fun C => 1 ≤ C.length && C.length ≤ 2

/-- The variable `x` is found contradictory: its negation is reachable from it, and it from its
negation. -/
def contradictory (F : Formula) (x : ℕ) : Bool :=
  neg x ∈ reachable F (pos x) && pos x ∈ reachable F (neg x)

/-- **The algorithm.** Reject unless every clause has one or two literals; then reject exactly
when some occurring variable is contradictory. -/
def decide (F : Formula) : Bool :=
  widthOk F && ((literals F).map Literal.index).dedup.all fun x => !contradictory F x

end Lax117284.TwoSatAlgorithm
