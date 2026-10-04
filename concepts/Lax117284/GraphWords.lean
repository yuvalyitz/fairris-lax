import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Lax228581.Treewidth

/-!
---
title: Graphs and Nice Tree Decompositions as Words
type: definition
---
A *tree decomposition* of a graph is a tree whose nodes carry bags of vertices such that every
vertex and every edge lies in a bag and the nodes whose bags contain a fixed vertex form a
connected subtree; its width is the largest bag size minus one, and the *treewidth* of the
graph is the least width of a decomposition (the archive's `Lax228581.Treewidth`). A tree
decomposition is *nice* if its root and its leaves have empty bags and every other node is
either an *introduce* node, whose bag is the bag of its single child plus one vertex, a
*forget* node, whose bag is the bag of its single child minus one vertex, or a *join* node,
with two children whose bags equal its own. This is the form dynamic programs over tree
decompositions consume; it is due to Kloks.

# Formalization Notes

The word RAM of the archive reads and writes lists of natural numbers, so this module fixes
how a graph and a nice tree decomposition are written as one.

A graph on the vertices `0 … n - 1` is written as `n` followed by its adjacency matrix row by
row, each entry `1` for adjacent and `0` for not: `1 + n * n` numbers. The matrix rather
than an edge list, so that a program which fills a table indexed by pairs of vertices reads an
entry in one instruction; the length of the word is then quadratic in the number of vertices,
and the running times below are polynomial in it, not linear.

A nice tree decomposition is a word `N` followed by `N` records of three numbers, one for each
node, in an order in which every node comes after its children: the kind of the node (`0`
leaf, `1` introduce, `2` forget, `3` join), a vertex (for an introduce or a forget node) and a
node (the second child of a join node). The first child of a node that is not a leaf is the node
just before it, and the last node is the root. Bags are not written: they are determined from
the leaves upward, a leaf having the empty bag. Listed in this order, the nodes describe a rooted tree in which each
node has at most two children.
`NiceDecomposition G w D` says that `D` describes a tree, that the bags it determines cover the
vertices and the edges of `G`, that they are connected as required, and that they have at most
`w + 1` vertices. It is the archive's tree decomposition written out for words.

The root is *not* required to have an empty bag: every consumer of a nice decomposition only
uses that each vertex is introduced once along each path and forgotten after its last edge,
and the root's bag can be emptied by forget nodes at the cost of a linear number of further
nodes. A word with a nonempty root bag is still a nice tree decomposition here.
-/

namespace Lax117284.GraphWords

open Lax228581.Treewidth

-- The word of a decomposition.

/-- The number of nodes of the decomposition word `D`: its first entry. -/
def nodeCount (D : List ℕ) : ℕ := D.getD 0 0

/-- The kind of node `i`: `0` leaf, `1` introduce, `2` forget, `3` join. -/
def kind (D : List ℕ) (i : ℕ) : ℕ := D.getD (1 + 3 * i) 0

/-- The vertex of node `i`, for an introduce or a forget node. -/
def vertex (D : List ℕ) (i : ℕ) : ℕ := D.getD (2 + 3 * i) 0

/-- The second child of node `i`, for a join node. -/
def other (D : List ℕ) (i : ℕ) : ℕ := D.getD (3 + 3 * i) 0

/-- The bag of node `i` among the vertices `0 … n - 1`, from the leaves up: the empty bag at a
leaf, the child's bag plus the vertex at an introduce node, minus it at a forget node, and the
child's bag at a join node. The first child of node `i + 1` is node `i`. -/
def bagAt (n : ℕ) (D : List ℕ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | i + 1 =>
      if kind D (i + 1) = 1 then
        if h : vertex D (i + 1) < n then insert ⟨vertex D (i + 1), h⟩ (bagAt n D i)
        else bagAt n D i
      else if kind D (i + 1) = 2 then
        if h : vertex D (i + 1) < n then (bagAt n D i).erase ⟨vertex D (i + 1), h⟩
        else bagAt n D i
      else if kind D (i + 1) = 3 then bagAt n D i
      else ∅

/-- Node `c` is a child of node `p`. -/
def IsChild (D : List ℕ) (c p : ℕ) : Prop :=
  p < nodeCount D ∧
    ((kind D p = 1 ∨ kind D p = 2) ∧ c + 1 = p ∨ kind D p = 3 ∧ (c + 1 = p ∨ c = other D p))

/-- The graph on the nodes `0 … N - 1` whose edges join a node to its children. -/
def treeGraph (D : List ℕ) : SimpleGraph (Fin (nodeCount D)) where
  Adj a b := a ≠ b ∧ (IsChild D a.val b.val ∨ IsChild D b.val a.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **`D` is the word of a nice tree decomposition of `G` of width at most `w`.** -/
structure NiceDecomposition {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) (D : List ℕ) : Prop where
  /-- The word is `N` followed by three numbers for each of the `N` nodes. -/
  length_eq : D.length = 1 + 3 * nodeCount D
  /-- There is a node. -/
  nonempty : 0 < nodeCount D
  /-- Every node is a leaf, or an introduce node over the node before it whose vertex is not in
  that node's bag, or a forget node over the node before it whose vertex is in that node's bag,
  or a join node whose two children, the node before it and an earlier node, have its bag. -/
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt n D (other D i) = bagAt n D (i - 1))
  /-- Every node other than the last has exactly one parent. -/
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p
  /-- The nodes form a tree. -/
  isTree : (treeGraph D).IsTree
  /-- Every vertex is in a bag. -/
  covers : ∀ v : Fin n, ∃ i, i < nodeCount D ∧ v ∈ bagAt n D i
  /-- Every two adjacent vertices are in a bag together. -/
  edges : ∀ u v : Fin n, G.Adj u v →
    ∃ i, i < nodeCount D ∧ u ∈ bagAt n D i ∧ v ∈ bagAt n D i
  /-- The nodes whose bags contain a fixed vertex form a connected subtree. -/
  connected : ∀ v : Fin n,
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt n D i}).Connected
  /-- Every bag has at most `w + 1` vertices. -/
  width : ∀ i, i < nodeCount D → (bagAt n D i).card ≤ w + 1

open Classical in
/-- **`g` is the word of the graph `G`**: the number of vertices, then the adjacency matrix row
by row. -/
structure EncodesGraph {n : ℕ} (g : List ℕ) (G : SimpleGraph (Fin n)) : Prop where
  /-- The word is the count followed by the matrix. -/
  length_eq : g.length = 1 + n * n
  /-- The first entry is the number of vertices. -/
  head_eq : g.getD 0 0 = n
  /-- The entry of the row `u` and column `v` is `1` when the two vertices are adjacent and `0`
  otherwise. -/
  adj_eq : ∀ u v : Fin n, g.getD (1 + u.val * n + v.val) 0 = if G.Adj u v then 1 else 0

end Lax117284.GraphWords
