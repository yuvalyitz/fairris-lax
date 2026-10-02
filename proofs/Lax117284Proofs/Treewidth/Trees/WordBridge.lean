import Lax117284Proofs.Treewidth.Trees.WordGraph

/-!
# `NiceDecomposition` of a word in arbitrary layout ↔ `IsNiceTD` of the tree it reads (T2)

For a word with `Lay n D` (this is the layout half of `NiceDecomposition`), the remaining fields of
`NiceDecomposition G w D` hold iff `ofWord D (N - 1)` is a nice tree decomposition of `G` of width `≤ w`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

/-- Vertices of the tree are the vertices of the bags. -/
lemma Lay.mem_vs_iff (L : Lay n D) (u : ℕ) :
    u ∈ (ofWord D (nodeCount D - 1)).vs ↔ ∃ j, j < nodeCount D ∧ u ∈ bagN n D j := by
  have hN := L.nonempty
  rw [L.mem_vs_ofWord _ (by omega), L.desc_full]
  simp only [Finset.mem_range]

/-- The bags of the tree are the bags `bagN` of the nodes. -/
lemma Lay.mem_bs_iff (L : Lay n D) (X : Finset ℕ) :
    X ∈ (ofWord D (nodeCount D - 1)).bs ↔ ∃ j, j < nodeCount D ∧ X = bagN n D j := by
  have hN := L.nonempty
  rw [L.mem_bs_ofWord _ (by omega), L.desc_full]
  simp only [Finset.mem_range]

lemma card_bagN (n : ℕ) (D : List ℕ) (i : ℕ) : (bagN n D i).card = (bagAt n D i).card := by
  simp [bagN]

/-- **A word with the layout conditions whose tree is a nice tree decomposition is a `NiceDecomposition`.** -/
theorem Lay.niceDecomposition_of_isNiceTD (L : Lay n D) {G : SimpleGraph (Fin n)} {w : ℕ}
    (h : (ofWord D (nodeCount D - 1)).IsNiceTD (liftGraph G) (Finset.range n) w) :
    NiceDecomposition G w D := by
  have hN := L.nonempty
  obtain ⟨hwf, hTD, hwd⟩ := h
  have hverts : (ofWord D (nodeCount D - 1)).vs = Finset.range n := hTD.verts_eq
  have hcov : ∀ v : Fin n, ∃ i, i < nodeCount D ∧ v ∈ bagAt n D i := by
    intro v
    have : v.val ∈ (ofWord D (nodeCount D - 1)).vs := by rw [hverts]; exact Finset.mem_range.2 v.2
    obtain ⟨j, hj, hv⟩ := (L.mem_vs_iff _).1 this
    exact ⟨j, hj, (mem_bagN_fin v).1 hv⟩
  have hloc : ∀ j, j < nodeCount D → Loc n D j := by
    have hn := (NT.conn_toRT_iff hwf).1 hTD.conn
    rw [L.nconn_ofWord _ (by omega), L.desc_full] at hn
    exact fun j hj => hn j (Finset.mem_range.2 hj)
  refine ⟨L.length_eq, L.nonempty, L.shape, L.parent, L.isTree, hcov, ?_, ?_, ?_⟩
  · intro u v huv
    have hadj : (liftGraph (n := n) G).Adj u.val v.val :=
      ⟨fun h => G.ne_of_adj huv (Fin.ext h), u, v, huv, rfl, rfl⟩
    obtain ⟨X, hX, hu, hv⟩ := hTD.edges u.val v.val hadj (Finset.mem_range.2 u.2) (Finset.mem_range.2 v.2)
    obtain ⟨j, hj, rfl⟩ := (L.mem_bs_iff X).1 hX
    exact ⟨j, hj, (mem_bagN_fin u).1 hu, (mem_bagN_fin v).1 hv⟩
  · intro v
    obtain ⟨j, hj, hvj⟩ := hcov v
    exact (L.connected_bagAt_iff v).2
      (L.connOn_of_loc hloc ⟨j, hj, (mem_bagN_fin v).2 hvj⟩)
  · intro i hi
    have := hwd (bagN n D i) ((L.mem_bs_iff _).2 ⟨i, hi, rfl⟩)
    rwa [card_bagN] at this

end Word

end Lax117284Proofs.Treewidth.Trees
