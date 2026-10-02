import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Lax228581.Treewidth
import Lax117284.GraphWords

/-!
# Decompositions as inductive rooted trees, nice trees (definitions; the two bridges live in `Trees/Bridge1`, `Trees/Bridge2`)

**Representation decision (PLAN §a).**  All the algorithmic mathematics lives on *inductive rooted trees with
`Finset ℕ` bags* (`RT`), and on *nice trees* (`NT`).  Validity is a recursive predicate (no `SimpleGraph` tree
structure, no node types).  There are exactly two bridges, both proved once and used only at the two ends:

* `RT ↔ Lax228581.Treewidth.TreeDecomposition`   (`hasTreewidthAtMost_iff_rt`)  — the *statement* of the
  concept (`¬ HasTreewidthAtMost` for the negative answer);
* `NT ↔ GraphWords.NiceDecomposition`            (`niceDecomposition_encode`, `niceDecomposition_parse`) — the
  *word format* of input and output.

Every vertex is a natural number; a graph on `Fin n` is lifted along `Fin.val`.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax228581.Treewidth

/-! ## rooted decomposition trees -/

set_option genInjectivity false in
/-- A rooted tree of bags (arbitrary arity). -/
inductive RT where
  | node (bag : Finset ℕ) (kids : List RT)

namespace RT

def rootBag : RT → Finset ℕ
  | node b _ => b

mutual
/-- All vertices occurring in the tree. -/
def verts : RT → Finset ℕ
  | node b ks => b ∪ vertsL ks
def vertsL : List RT → Finset ℕ
  | [] => ∅
  | k :: ks => verts k ∪ vertsL ks
end

mutual
/-- The bags of all nodes. -/
def bags : RT → List (Finset ℕ)
  | node b ks => b :: bagsL ks
def bagsL : List RT → List (Finset ℕ)
  | [] => []
  | k :: ks => bags k ++ bagsL ks
end

mutual
/-- Number of nodes. -/
def size : RT → ℕ
  | node _ ks => 1 + sizeL ks
def sizeL : List RT → ℕ
  | [] => 0
  | k :: ks => size k + sizeL ks
end

mutual
/-- *Connectedness of the occurrence sets*, recursively: a vertex of a bag that occurs below a child occurs in the
child's root bag; a vertex not in the bag occurs below at most one child. -/
def Conn : RT → Prop
  | node b ks => ConnL ks ∧ (∀ k ∈ ks, ∀ v ∈ b, v ∈ verts k → v ∈ rootBag k) ∧
      ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ b)
def ConnL : List RT → Prop
  | [] => True
  | k :: ks => Conn k ∧ ConnL ks
end

/-- `t` is a tree decomposition of the subgraph of `G` induced on `U`. -/
structure IsTD (G : SimpleGraph ℕ) (U : Finset ℕ) (t : RT) : Prop where
  verts_eq : t.verts = U
  edges : ∀ u v, G.Adj u v → u ∈ U → v ∈ U → ∃ X ∈ t.bags, u ∈ X ∧ v ∈ X
  conn : t.Conn

/-- All bags have at most `w + 1` elements. -/
def Width (t : RT) (w : ℕ) : Prop := ∀ X ∈ t.bags, X.card ≤ w + 1

end RT

/-- The graph on `Fin n` seen as a graph on `ℕ` (with vertex set `range n`). -/
def liftGraph {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph ℕ :=
  G.map Fin.valEmbedding


/-- Induced subgraphs on initial segments (used by the wrapper). -/
def prefixGraph {n : ℕ} (G : SimpleGraph (Fin n)) (i : ℕ) (h : i ≤ n) : SimpleGraph (Fin i) :=
  G.comap (Fin.castLEEmb h)


/-! ## nice trees -/

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Nice decompositions: leaf, introduce, forget, join.  (Bags are *computed*, as in the word format.) -/
inductive NT where
  | leaf
  | intro (v : ℕ) (c : NT)
  | forget (v : ℕ) (c : NT)
  | join (a b : NT)

namespace NT

/-- The bag of the root. -/
def bag : NT → Finset ℕ
  | leaf => ∅
  | intro v c => insert v (bag c)
  | forget v c => (bag c).erase v
  | join a _ => bag a

/-- Shape conditions: the introduced vertex is new, the forgotten one is present, joins have equal bags. -/
def Wf : NT → Prop
  | leaf => True
  | intro v c => v ∉ bag c ∧ Wf c
  | forget v c => v ∈ bag c ∧ Wf c
  | join a b => bag a = bag b ∧ Wf a ∧ Wf b

/-- The underlying decomposition tree. -/
def toRT : NT → RT
  | leaf => .node ∅ []
  | intro v c => .node (bag (intro v c)) [toRT c]
  | forget v c => .node (bag (forget v c)) [toRT c]
  | join a b => .node (bag a) [toRT a, toRT b]

/-- `t` is a nice decomposition of `G[U]` of width `≤ w`. -/
def IsNiceTD (G : SimpleGraph ℕ) (U : Finset ℕ) (t : NT) (w : ℕ) : Prop :=
  t.Wf ∧ t.toRT.IsTD G U ∧ t.toRT.Width w

/-- Number of nodes. -/
def size : NT → ℕ
  | leaf => 1
  | intro _ c => size c + 1
  | forget _ c => size c + 1
  | join a b => size a + size b + 1

/-- Insert the vertex `v` into every bag: an introduce node above every leaf (this is *the* word
transformation of the wrapper, PLAN §e). -/
def addEverywhere (v : ℕ) : NT → NT
  | leaf => intro v leaf
  | intro u c => intro u (addEverywhere v c)
  | forget u c => forget u (addEverywhere v c)
  | join a b => join (addEverywhere v a) (addEverywhere v b)



/-! ### The word format (`GraphWords`) -/

/-- One record `(kind, vertex, other)` per node, children before parents; the first child of a node is the node just
before it, the second child of a join is `other`.  `recs b t` numbers the nodes from `b`. -/
def recs : ℕ → NT → List (ℕ × ℕ × ℕ)
  | _, leaf => [(0, 0, 0)]
  | b, intro v c => recs b c ++ [(1, v, 0)]
  | b, forget v c => recs b c ++ [(2, v, 0)]
  | b, join x y =>
      let ry := recs b y
      let rx := recs (b + ry.length) x
      ry ++ rx ++ [(3, 0, b + ry.length - 1)]

/-- The word `N` followed by `N` records. -/
def encode (t : NT) : List ℕ :=
  let rs := recs 0 t
  rs.length :: rs.flatMap (fun r => [r.1, r.2.1, r.2.2])

end NT

end Lax117284Proofs.Treewidth.Trees
