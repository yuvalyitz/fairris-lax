import Lax808846.Ram
import Lax117284.InstanceEncoding
import Lax117284.ConflictGraph

/-!
---
title: Nice Tree Decompositions of Small Width Are Found in Fixed-Parameter Time
type: definition
---
A *tree decomposition* of a graph is a tree whose nodes carry bags of vertices such that every
vertex and every edge lies in a bag and the nodes whose bags contain a fixed vertex form a
connected subtree; its width is the largest bag size minus one. It is *nice* if its nodes are of
four kinds: a leaf, an *introduce* node whose bag is the bag of its single child plus one
vertex, a *forget* node whose bag is the bag of its single child minus one vertex, and a *join*
node with two children whose bags equal its own.

**Bodlaender's theorem.** For every constant `w` one can decide in linear time whether a graph
has treewidth at most `w`, and if so construct a tree decomposition of width at most `w`; the
dependence on `w` is `2^{O(w^3)}`. Kloks' construction turns any tree decomposition of width `w`
into a nice one of the same width in time linear in the size of the decomposition, so the same
holds for nice decompositions.

Bodlaender, *"A linear-time algorithm for finding tree-decompositions of small treewidth"*,
SIAM Journal on Computing 25 (1996) 1305–1317; Kloks, *"Treewidth: Computations and
Approximations"*, Lecture Notes in Computer Science 842, Springer 1994. Cited by
Heeger–Hermelin–Itzhaki–Molter–Shabtay for Theorem 4's second bullet.

# Formalization Notes

The cited theorem is stated for the graphs this development runs it on: the overall conflict
graph of an instance. A word presents that graph as its adjacency matrix: the number `n` of
clients, then the `n * n` entries of the matrix row by row, each `1` for adjacent and `0` for not,
and the bound `w` on the width is appended as a last entry. Reading the graph off an instance
takes time polynomial in the instance, so it is a step of the algorithm that uses the theorem
and not of the theorem itself; the running time of the theorem is measured in the length of the
graph's word, polynomially, and is `2^{c w^3}` in the bound, which is what the linear-time
algorithm takes once the graph is in this form.

The output is either `[0]`, which is admissible only when the graph has no tree decomposition
of width at most `w` (in the archive's sense), or `1` followed by the word of a nice tree
decomposition of width at most `w`. A nice decomposition is a word `N` followed by `N` records
of three numbers, one for each node in an order in which every node comes after its children: the
kind of the node (`0` leaf, `1` introduce, `2` forget, `3` join), a vertex (for introduce and
forget nodes) and a node (the second child of a join node). The first child of a non-leaf is the
node just before it. Bags are not written: they are determined from the leaves upward, a leaf
having the empty bag. `NiceDecomposition` says that this describes a tree, that its bags
cover the vertices and the edges, that they are connected as required, and that the bags have at
most `w + 1` vertices. It is the archive's tree decomposition written out for words.

The output is a relation and not a function, since a graph has many decompositions: the program
may produce any one of them.

The guard on the word length is what makes the statement true. The program's tables have size
`2^{c w^3}` times a polynomial in the length of the word, so a machine of too small a word length
cannot hold them; the hypothesis is an explicit inequality against `2 ^ W`, checkable from the
input alone, and it ranges over the entries of the word so that every entry, and every number the
output contains (node numbers are bounded by the running time), is a word. Nothing is claimed
for word lengths that violate it.

The program and the constant are quantified before the word length, the graph and the
bound, so one program serves them all.
-/

namespace Lax117284.Bodlaender

open Lax808846.Ram Lax117284.Scheduling Lax117284.ConflictGraph

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

/-- **`D` is the word of a nice tree decomposition of the overall conflict graph of `I` of width
at most `w`.** -/
structure NiceDecomposition (I : Instance) (w : ℕ) (D : List ℕ) : Prop where
  /-- The word is `N` followed by three numbers for each of the `N` nodes. -/
  length_eq : D.length = 1 + 3 * nodeCount D
  /-- There is a node. -/
  nonempty : 0 < nodeCount D
  /-- Every node is a leaf, or an introduce node over the node before it whose vertex is not in
  that node's bag, or a forget node over the node before it whose vertex is in that node's bag,
  or a join node whose two children, the node before it and an earlier node, have its bag. -/
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < I.clients ∧
      ∀ h : vertex D i < I.clients, (⟨vertex D i, h⟩ : Fin I.clients) ∉ bagAt I.clients D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < I.clients ∧
      ∀ h : vertex D i < I.clients, (⟨vertex D i, h⟩ : Fin I.clients) ∈ bagAt I.clients D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt I.clients D (other D i) = bagAt I.clients D (i - 1))
  /-- Every node other than the last has exactly one parent. -/
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p
  /-- The nodes form a tree. -/
  isTree : (treeGraph D).IsTree
  /-- Every client is in a bag. -/
  covers : ∀ v : Fin I.clients, ∃ i, i < nodeCount D ∧ v ∈ bagAt I.clients D i
  /-- Every two clients whose jobs conflict on some day are in a bag together. -/
  edges : ∀ u v : Fin I.clients, (overallGraph I).Adj u v →
    ∃ i, i < nodeCount D ∧ u ∈ bagAt I.clients D i ∧ v ∈ bagAt I.clients D i
  /-- The nodes whose bags contain a fixed client form a connected subtree. -/
  connected : ∀ v : Fin I.clients,
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt I.clients D i}).Connected
  /-- Every bag has at most `w + 1` clients. -/
  width : ∀ i, i < nodeCount D → (bagAt I.clients D i).card ≤ w + 1

open Classical in
/-- **`g` is the word of the overall conflict graph of `I`**: the number of clients, then the
adjacency matrix row by row. -/
structure EncodesGraph (g : List ℕ) (I : Instance) : Prop where
  /-- The word is the count followed by the matrix. -/
  length_eq : g.length = 1 + I.clients * I.clients
  /-- The first entry is the number of clients. -/
  head_eq : g.getD 0 0 = I.clients
  /-- The entry of the row `u` and column `v` is `1` when the two clients are adjacent and `0`
  otherwise. -/
  adj_eq : ∀ u v : Fin I.clients,
    g.getD (1 + u.val * I.clients + v.val) 0 = if (overallGraph I).Adj u v then 1 else 0

/-- **Bodlaender's theorem with Kloks' niceness, for the overall conflict graph of an instance
given as a word.** One program and one constant serve every word length `W`, every graph and every
bound `w`, provided the word — the graph followed by `w` — fits with room for
`c * 2 ^ (c * w ^ 3)` times a polynomial in its length. On such a word the program halts within
`c * 2 ^ (c * w ^ 3) * (|g| + 2) ^ c` instructions, writing `[0]` if the graph has no tree
decomposition of width at most `w`, and `1` followed by the word of a nice tree decomposition of
width at most `w` otherwise. -/
axiom niceDecomposition_computable :
    ∃ (prog : Program) (c : ℕ), ∀ (W w : ℕ) (g : List ℕ) (I : Instance),
      EncodesGraph g I →
      (∀ v ∈ g ++ [w], c * 2 ^ (c * w ^ 3) * ((g ++ [w]).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * w ^ 3) * (g.length + 2) ^ c ∧
        RunsTo W prog (g ++ [w]) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) w ∨
          ∃ D, out = 1 :: D ∧ NiceDecomposition I w D)

end Lax117284.Bodlaender
