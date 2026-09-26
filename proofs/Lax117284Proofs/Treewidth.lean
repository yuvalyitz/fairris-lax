import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Nice tree decompositions (Definition 17)

> **Definition 6.** A *tree-decomposition* of a graph `G = (V, E)` is a tree
> `T = (𝒳, F)` with a node set `𝒳 ⊆ {X | X ⊆ V}` and `F ⊆ 𝒳 × 𝒳` that upholds the
> following:
> * `V = ⋃_{X ∈ 𝒳} X`.
> * For every edge `{u, v} ∈ E` there exists `X ∈ 𝒳` such that `u, v ∈ X`.
> * The set of nodes `𝒳_v = {X | X ∈ 𝒳 ∧ v ∈ X}` containing any vertex `v ∈ V` is a
>   connected subgraph in `T`.

This file supplies the *nice* tree decompositions (Definition 17) that Theorem 19's dynamic
program runs on, as a rooted tree by construction: a tree decomposition is a **rooted** tree of
bags rather than an abstract graph with an acyclicity proof, so recursing on one (as
Theorem 19 does) needs no well-founded relation.

Definition 6's third clause — *`𝒳_v` is connected* — becomes, for a rooted tree, the
**coherence** conditions of `NiceTree.Coherent`: a vertex of a node's bag that occurs anywhere
in a child's subtree is already in that child's bag, and two different children's subtrees
share only vertices the node's bag already holds.

## What the dynamic program needs, and where it comes from

Theorem 19's four cases each need a *separation* property — at an introduce node the new
client has no neighbour deeper in the subtree outside the child's bag, and at a join node
the two subtrees' private parts are non-adjacent. These are **proved** here
(`adj_mem_bag_of_intro`, `not_adj_of_join`) from Definition 6's conditions, not assumed:
the ingredient that makes it work is `EdgesCovered`, the observation that the edge-covering
clause, stated at the root, *propagates to every subtree* (`EdgesCovered.intro_child` and
friends). Without that step one would have to assume the separation properties outright.
-/


namespace Lax117284Proofs.Model

/-! ## Nice tree decompositions (Definition 17)

> **Definition 17.** A *nice tree decomposition* is a tree decomposition `T = (𝒳, F)` where
> the following conditions additionally hold:
> 1. Every node `X ∈ 𝒳` has at most two children.
> 2. If node `X` has two children `X'` and `X''` then `X = X' = X''`, and `X` is called a
>    *join node*.
> 3. If node `X` has a single child `X'` then either of the two following holds:
>    (a) `X = X' \ {j}` for some client `j ∈ X'`. In this case, we call `X` a *forget node*.
>    (b) `X = X' ∪ {j}` for some client `j ∈ {1,…,n} \ X'`. In this case, we say that `X` is
>        an *introduce node*.

Four shapes, so four constructors. -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A **nice tree decomposition** (Definition 17), as an inductive shape. -/
inductive NiceTree (V : Type) where
  /-- A leaf, with its bag. -/
  | leaf (bag : Finset V) : NiceTree V
  /-- An introduce node: `j` joins the child's bag. -/
  | intro (j : V) (child : NiceTree V) : NiceTree V
  /-- A forget node: `j` leaves the child's bag. -/
  | forget (j : V) (child : NiceTree V) : NiceTree V
  /-- A join node: two children with the same bag. -/
  | join (l r : NiceTree V) : NiceTree V

namespace NiceTree

variable {V : Type} [DecidableEq V]

/-- The bag at the root. -/
def bag : NiceTree V → Finset V
  | leaf b => b
  | intro j c => insert j c.bag
  | forget j c => c.bag.erase j
  | join l _ => l.bag

/-- Every vertex occurring anywhere in the subtree. -/
def verts : NiceTree V → Finset V
  | leaf b => b
  | intro j c => insert j c.verts
  | forget _ c => c.verts
  | join l r => l.verts ∪ r.verts

/-- `s` is one of the bags. -/
def HasBag : NiceTree V → Finset V → Prop
  | leaf b, s => s = b
  | intro j c, s => s = insert j c.bag ∨ HasBag c s
  | forget j c, s => s = c.bag.erase j ∨ HasBag c s
  | join l r, s => s = l.bag ∨ HasBag l s ∨ HasBag r s

/-- Definition 6's connectivity clause, for the four nice shapes. -/
def Coherent : NiceTree V → Prop
  | leaf _ => True
  | intro j c => j ∉ c.verts ∧ Coherent c
  | forget j c => j ∈ c.bag ∧ Coherent c
  | join l r => l.bag = r.bag ∧ (l.verts ∩ r.verts ⊆ l.bag) ∧ Coherent l ∧ Coherent r

/-! The clauses of `HasBag` and `Coherent`, one per shape, as rewrite rules. -/

lemma hasBag_leaf_iff (b s : Finset V) : (leaf b).HasBag s ↔ s = b := Iff.intro id id

lemma hasBag_intro_iff (j : V) (c : NiceTree V) (s : Finset V) :
    (intro j c).HasBag s ↔ s = insert j c.bag ∨ c.HasBag s := by
  rw [HasBag.eq_def]

lemma hasBag_forget_iff (j : V) (c : NiceTree V) (s : Finset V) :
    (forget j c).HasBag s ↔ s = c.bag.erase j ∨ c.HasBag s := Iff.intro id id

lemma hasBag_join_iff (l r : NiceTree V) (s : Finset V) :
    (join l r).HasBag s ↔ s = l.bag ∨ l.HasBag s ∨ r.HasBag s := Iff.intro id id

lemma coherent_leaf_iff (b : Finset V) : (leaf b).Coherent ↔ True := Iff.intro id id

lemma coherent_intro_iff (j : V) (c : NiceTree V) :
    (intro j c).Coherent ↔ j ∉ c.verts ∧ c.Coherent := Iff.intro id id

lemma coherent_forget_iff (j : V) (c : NiceTree V) :
    (forget j c).Coherent ↔ j ∈ c.bag ∧ c.Coherent := Iff.intro id id

lemma coherent_join_iff (l r : NiceTree V) :
    (join l r).Coherent ↔
      l.bag = r.bag ∧ (l.verts ∩ r.verts ⊆ l.bag) ∧ l.Coherent ∧ r.Coherent := Iff.intro id id

@[simp] lemma bag_leaf (b : Finset V) : (leaf b).bag = b := Eq.trans rfl rfl
@[simp] lemma bag_intro (j : V) (c : NiceTree V) : (intro j c).bag = insert j c.bag := Eq.trans rfl rfl
@[simp] lemma bag_forget (j : V) (c : NiceTree V) : (forget j c).bag = c.bag.erase j := Eq.trans rfl rfl
@[simp] lemma bag_join (l r : NiceTree V) : (join l r).bag = l.bag := rfl

@[simp] lemma verts_leaf (b : Finset V) : (leaf b).verts = b := Eq.trans rfl rfl
@[simp] lemma verts_intro (j : V) (c : NiceTree V) : (intro j c).verts = insert j c.verts := Eq.trans rfl rfl
@[simp] lemma verts_forget (j : V) (c : NiceTree V) : (forget j c).verts = c.verts := Eq.trans rfl rfl
@[simp] lemma verts_join (l r : NiceTree V) : (join l r).verts = l.verts ∪ r.verts := Eq.trans rfl rfl

/-- Every bag sits inside the subtree's vertex set. -/
lemma bag_subset_verts : ∀ T : NiceTree V, T.bag ⊆ T.verts
  | leaf _ => le_rfl
  | intro j c => by
      simp only [bag_intro, verts_intro]
      exact Finset.insert_subset_insert _ (bag_subset_verts c)
  | forget j c => by
      simp only [bag_forget, verts_forget]
      exact (Finset.erase_subset _ _).trans (bag_subset_verts c)
  | join l r => by
      simp only [bag_join, verts_join]
      exact (bag_subset_verts l).trans Finset.subset_union_left

/-- Every bag of the subtree sits inside the subtree's vertex set. -/
lemma hasBag_subset_verts {T : NiceTree V} {s : Finset V} (h : T.HasBag s) :
    s ⊆ T.verts := by
  induction T generalizing s with
  | leaf b => subst h; exact le_rfl
  | intro j c ih =>
      rcases h with rfl | h
      · exact bag_subset_verts (intro j c)
      · exact (ih h).trans (by simp [Finset.subset_insert])
  | forget j c ih =>
      rcases h with rfl | h
      · exact bag_subset_verts (forget j c)
      · exact ih h
  | join l r ihl ihr =>
      rcases h with rfl | h | h
      · exact bag_subset_verts (join l r)
      · exact (ihl h).trans Finset.subset_union_left
      · exact (ihr h).trans Finset.subset_union_right

/-- The root's own bag is a bag. -/
lemma hasBag_self : ∀ T : NiceTree V, T.HasBag T.bag
  | leaf _ => rfl
  | intro _ _ => Or.inl rfl
  | forget _ _ => Or.inl rfl
  | join _ _ => Or.inl rfl

/-- `T` is a nice tree decomposition of `G`. -/
structure IsNice {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : NiceTree V) : Prop where
  /-- Every vertex occurs in some bag. -/
  covers : ∀ v : V, v ∈ T.verts
  /-- Every edge is inside some bag. -/
  edges : ∀ u v, G.Adj u v → ∃ s, T.HasBag s ∧ u ∈ s ∧ v ∈ s
  /-- The bags containing a fixed vertex form a connected subtree. -/
  coherent : T.Coherent

/-! ### Edge covering propagates down the tree

This is the step that lets the dynamic program reason locally. -/

variable (G : SimpleGraph V) in
/-- Every edge *inside this subtree* is inside one of this subtree's bags. -/
def EdgesCovered (T : NiceTree V) : Prop :=
  ∀ u ∈ T.verts, ∀ v ∈ T.verts, G.Adj u v → ∃ s, T.HasBag s ∧ u ∈ s ∧ v ∈ s

lemma EdgesCovered.of_isNice {G : SimpleGraph V} {T : NiceTree V} (h : IsNice G T) :
    EdgesCovered G T := fun u _ v _ huv => h.edges u v huv

lemma EdgesCovered.intro_child {G : SimpleGraph V} {j : V} {c : NiceTree V}
    (hj : j ∉ c.verts) (h : EdgesCovered G (intro j c)) : EdgesCovered G c := by
  intro u hu v hv huv
  obtain ⟨s, hs, hus, hvs⟩ := h u (by simp [hu]) v (by simp [hv]) huv
  rcases hs with rfl | hs
  · refine ⟨c.bag, hasBag_self c, ?_, ?_⟩
    · rcases Finset.mem_insert.1 hus with rfl | h'
      · exact absurd hu hj
      · exact h'
    · rcases Finset.mem_insert.1 hvs with rfl | h'
      · exact absurd hv hj
      · exact h'
  · exact ⟨s, hs, hus, hvs⟩

lemma EdgesCovered.forget_child {G : SimpleGraph V} {j : V} {c : NiceTree V}
    (h : EdgesCovered G (forget j c)) : EdgesCovered G c := by
  intro u hu v hv huv
  obtain ⟨s, hs, hus, hvs⟩ := h u hu v hv huv
  rcases hs with rfl | hs
  · exact ⟨c.bag, hasBag_self c, Finset.mem_of_mem_erase hus, Finset.mem_of_mem_erase hvs⟩
  · exact ⟨s, hs, hus, hvs⟩

lemma EdgesCovered.join_left {G : SimpleGraph V} {l r : NiceTree V}
    (hco : l.verts ∩ r.verts ⊆ l.bag) (h : EdgesCovered G (join l r)) : EdgesCovered G l := by
  intro u hu v hv huv
  obtain ⟨s, hs, hus, hvs⟩ := h u (by simp [hu]) v (by simp [hv]) huv
  rcases hs with rfl | hs | hs
  · exact ⟨l.bag, hasBag_self l, hus, hvs⟩
  · exact ⟨s, hs, hus, hvs⟩
  · refine ⟨l.bag, hasBag_self l, ?_, ?_⟩
    · exact hco (Finset.mem_inter.2 ⟨hu, hasBag_subset_verts hs hus⟩)
    · exact hco (Finset.mem_inter.2 ⟨hv, hasBag_subset_verts hs hvs⟩)

lemma EdgesCovered.join_right {G : SimpleGraph V} {l r : NiceTree V} (hbag : l.bag = r.bag)
    (hco : l.verts ∩ r.verts ⊆ l.bag) (h : EdgesCovered G (join l r)) : EdgesCovered G r := by
  intro u hu v hv huv
  obtain ⟨s, hs, hus, hvs⟩ := h u (by simp [hu]) v (by simp [hv]) huv
  rcases hs with rfl | hs | hs
  · exact ⟨r.bag, hasBag_self r, hbag ▸ hus, hbag ▸ hvs⟩
  · refine ⟨r.bag, hasBag_self r, ?_, ?_⟩
    · exact hbag ▸ hco (Finset.mem_inter.2 ⟨hasBag_subset_verts hs hus, hu⟩)
    · exact hbag ▸ hco (Finset.mem_inter.2 ⟨hasBag_subset_verts hs hvs, hv⟩)
  · exact ⟨s, hs, hus, hvs⟩

/-! ### The two separation properties the dynamic program runs on -/

/-- **Introduce nodes separate.** The client introduced at an introduce node has no
neighbour in the child's subtree outside the child's bag. -/
theorem adj_mem_bag_of_intro {G : SimpleGraph V} {j : V} {c : NiceTree V}
    (hj : j ∉ c.verts) (h : EdgesCovered G (intro j c)) {u : V} (hu : u ∈ c.verts)
    (huv : G.Adj j u) : u ∈ c.bag := by
  obtain ⟨s, hs, hjs, hus⟩ := h j (by simp) u (by simp [hu]) huv
  rcases hs with rfl | hs
  · rcases Finset.mem_insert.1 hus with rfl | h'
    · exact absurd hu hj
    · exact h'
  · exact absurd (hasBag_subset_verts hs hjs) hj

/-- **Join nodes separate.** The parts of the two subtrees outside the shared bag are
non-adjacent. -/
theorem not_adj_of_join {G : SimpleGraph V} {l r : NiceTree V}
    (hco : l.verts ∩ r.verts ⊆ l.bag) (h : EdgesCovered G (join l r))
    {u v : V} (hu : u ∈ l.verts) (hu' : u ∉ l.bag) (hv : v ∈ r.verts) (hv' : v ∉ l.bag) :
    ¬ G.Adj u v := by
  intro huv
  obtain ⟨s, hs, hus, hvs⟩ := h u (by simp [hu]) v (by simp [hv]) huv
  rcases hs with rfl | hs | hs
  · exact hu' hus
  · exact hv' (hco (Finset.mem_inter.2 ⟨hasBag_subset_verts hs hvs, hv⟩))
  · exact hu' (hco (Finset.mem_inter.2 ⟨hu, hasBag_subset_verts hs hus⟩))

end NiceTree

end Lax117284Proofs.Model
