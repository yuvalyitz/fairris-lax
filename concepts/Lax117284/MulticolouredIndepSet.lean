import Lax117284.Problems
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
---
title: Multicoloured Independent Set
type: definition
---
An instance consists of $\ell$ colour classes of $n$ vertices each and a graph on those
$\ell n$ vertices whose edges join vertices of different classes. It is a yes-instance if
one vertex can be chosen from every class so that no two chosen vertices are adjacent — a
*multicoloured independent set*, necessarily of size $\ell$.

The problem is NP-hard, and remains NP-hard on the instances the reduction of the last
section consumes: those in which every vertex has the same number $r \ge 1$ of neighbours,
every class holds at least four vertices, and the number of edges is even.

# Formalization Notes

A vertex is a pair, its class and its index inside the class, so that the colouring is part
of the vertex set rather than a function to be constrained, and a solution is a choice of
one index per class rather than a set whose size and multicolouredness must be argued.

Vertices are also numbered, the vertex of class $i$ and index $a$ being $in + a$, and the
graph is read off those numbers by `adjAt`. A construction reading an instance works with
the numbers, and the numbering has the property the source's convention needs: an edge runs
from the smaller number to the larger exactly when it runs from the smaller class to the
larger. The neighbours of a vertex are listed in increasing order, which is the arbitrary
order the source fixes on them, and the edges are listed likewise.

Whether two vertices of a finite graph are adjacent is decided by inspection. The
definitions below nevertheless appeal to classical decidability, so that they do not carry
a decision procedure as an argument; no statement about them needs one.

The three side conditions of the hard slice are the normal form the source assumes of its
input. Regularity and the parity of the edge count let the construction distribute the
edges evenly between two clients; four vertices per class make the number of edges large
enough against the number of classes. All three are reached from an arbitrary instance by
padding, which is part of what the hardness of the slice asserts.
-/

namespace Lax117284.MulticolouredIndepSet

open Lax434930.PolynomialTime

/-- An instance of Multicoloured Independent Set: a graph on `colours` classes of `size`
vertices whose edges join vertices of different classes. -/
structure Instance where
  /-- The number `ℓ` of colour classes. -/
  colours : ℕ
  /-- The number `n` of vertices in each class. -/
  size : ℕ
  /-- The graph, on the vertices `(class, index)`. -/
  graph : SimpleGraph (Fin colours × Fin size)
  /-- Adjacent vertices lie in different classes. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → u.1 ≠ v.1

namespace Instance

variable (G : Instance)

/-- **The question of Multicoloured Independent Set**: is there one vertex of every class
such that no two of them are adjacent? -/
def HasIndepSet : Prop :=
  ∃ f : Fin G.colours → Fin G.size, ∀ i i', ¬ G.graph.Adj (i, f i) (i', f i')

/-- The number `ℓn` of vertices. -/
def vertices : ℕ := G.colours * G.size

/-- The class of the vertex numbered `w`. -/
def classOf (w : ℕ) : ℕ := w / G.size

/-- The index inside its class of the vertex numbered `w`. -/
def indexOf (w : ℕ) : ℕ := w % G.size

open Classical in
/-- Whether the vertices numbered `w` and `w'` are adjacent, and `false` for numbers that
name no vertex. -/
noncomputable def adjAt (w w' : ℕ) : Bool :=
  if h : w < G.vertices ∧ w' < G.vertices then
    have hs : 0 < G.size := by
      by_contra h0
      have hz : G.size = 0 := by omega
      rw [vertices, hz, Nat.mul_zero] at h
      omega
    decide (G.graph.Adj
      (⟨w / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.1⟩, ⟨w % G.size, Nat.mod_lt _ hs⟩)
      (⟨w' / G.size, (Nat.div_lt_iff_lt_mul hs).2 h.2⟩, ⟨w' % G.size, Nat.mod_lt _ hs⟩))
  else false

/-- The neighbours of the vertex numbered `w`, in increasing order. -/
noncomputable def nbrs (w : ℕ) : List ℕ :=
  (List.range G.vertices).filter fun w' => G.adjAt w w'

/-- The number of neighbours the vertex `0` has; on a regular graph, the degree `r`. -/
noncomputable def degree : ℕ := (G.nbrs 0).length

/-- The edges, each listed as the pair of its endpoints from the smaller number to the
larger — which, since adjacent vertices lie in different classes, is from the smaller class
to the larger. -/
noncomputable def edgeList : List (ℕ × ℕ) :=
  (List.range G.vertices).flatMap fun w => ((G.nbrs w).filter fun w' => w < w').map (w, ·)

/-- The number `|E|` of edges. -/
noncomputable def edgeCount : ℕ := G.edgeList.length

/-- Every vertex of `G` has exactly `r` neighbours. -/
def Regular (r : ℕ) : Prop := ∀ w < G.vertices, (G.nbrs w).length = r

/-- The normal form the reduction into fair repetitive interval scheduling consumes: the
graph is regular of some positive degree, every class holds at least four vertices, and the
number of edges is even. -/
def Normal : Prop := (∃ r, 0 < r ∧ G.Regular r) ∧ 4 ≤ G.size ∧ 2 ∣ G.edgeCount

end Instance

/-- An instance as a binary word: the number of classes, the number of vertices per class,
and then the adjacency matrix, one bit per ordered pair of vertices. -/
noncomputable def encodeInstance (G : Instance) : Word :=
  Problems.encodeNat G.colours ++ Problems.encodeNat G.size ++
    (List.range G.vertices).flatMap fun w =>
      (List.range G.vertices).map fun w' => G.adjAt w w'

/-- **Multicoloured Independent Set on the instances in normal form**, as a language. -/
def NormalMulticolouredIndepSet : Language :=
  {w | ∃ G : Instance, encodeInstance G = w ∧ G.Normal ∧ G.HasIndepSet}

/-- **Multicoloured Independent Set is NP-hard on the instances in normal form.** -/
axiom normalMulticolouredIndepSet_npHard :
    Problems.NPHard NormalMulticolouredIndepSet

end Lax117284.MulticolouredIndepSet
