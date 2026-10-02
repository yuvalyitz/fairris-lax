import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Trees.AddEverywhere
import Lax117284Proofs.Treewidth.Trees.Bridge1
import Lax117284Proofs.Treewidth.Trees.Bridge2
import Lax117284Proofs.Treewidth.Wrap.Nice

/-!
# The vertex-by-vertex wrapper (C8a)

* `hasTW_mono`  : `HasTW` is monotone under induced subgraphs;
* `Adj.SymmOn`  : the symmetry hypothesis on adjacency that the tables need (see `Wrap/NOTES.md`);
* `ImproveSpec adj W` : the conclusion of `improve_correct` for all vertex sets `U ⊆ W` (an explicit hypothesis, so
  that the wrapper is proved independently of the tables);
* `decompose_correct`, `decompose_words` : the wrapper's specification on `Adj` / on graphs on `Fin n`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

/-- The adjacency function is symmetric on the vertex set `W`. -/
def Adj.SymmOn (adj : Adj) (W : Finset ℕ) : Prop := ∀ u ∈ W, ∀ v ∈ W, adj u v = adj v u

theorem hasTW_mono {adj : Adj} {U U' : Finset ℕ} {k : ℕ} (h : U' ⊆ U) : HasTW adj U k → HasTW adj U' k := by
  rintro ⟨t, htd, hw⟩
  refine ⟨t.restrict U', ?_, hw.restrict U'⟩
  have := htd.restrict U'
  rwa [Finset.inter_eq_right.2 h] at this

theorem hasTW_of_isNiceTD {adj : Adj} {U : Finset ℕ} {nt : NT} {k : ℕ} (h : nt.IsNiceTD adj.graph U k) :
    HasTW adj U k := ⟨nt.toRT, h.2.1, h.2.2⟩

theorem hasTW_empty (adj : Adj) (k : ℕ) : HasTW adj ∅ k :=
  hasTW_of_isNiceTD (nt := .leaf) (k := k)
    ⟨trivial, ⟨rfl, fun u v _ hu _ => absurd hu (by simp), by simp [NT.toRT, RT.Conn, RT.ConnL]⟩,
      by intro X hX; simp [NT.toRT, RT.bags, RT.bagsL] at hX; simp [hX]⟩

/-- The conclusion of `improve_correct`, for all vertex sets inside `W`: an explicit hypothesis of the wrapper. -/
def ImproveSpec (adj : Adj) (W : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (nt : NT) (l k : ℕ), U ⊆ W → nt.IsNiceTD adj.graph U l →
    (improve adj k nt = none ↔ ¬ HasTW adj U k) ∧ (∀ t', improve adj k nt = some t' → t'.IsNiceTD adj.graph U k)

/-- The graph `adj.graph` restricted to `range n` is the graph of `G` when `adj` encodes `G`. -/
theorem isTD_congr {G G' : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v ↔ G'.Adj u v) :
    t.IsTD G U ↔ t.IsTD G' U :=
  ⟨fun ht => ⟨ht.verts_eq, fun u v huv hu hv => ht.edges u v ((h u hu v hv).2 huv) hu hv, ht.conn⟩,
   fun ht => ⟨ht.verts_eq, fun u v huv hu hv => ht.edges u v ((h u hu v hv).1 huv) hu hv, ht.conn⟩⟩

theorem graph_adj_of_encodes {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) {u v : ℕ} (hu : u < n) (hv : v < n) :
    adj.graph.Adj u v ↔ (liftGraph G).Adj u v := by
  rw [Adj.graph, SimpleGraph.fromRel_adj, liftGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases (hadj ⟨u, hu⟩ ⟨v, hv⟩).1 h with h' | h'
      · exact ⟨_, _, h', rfl, rfl⟩
      · exact ⟨_, _, h'.symm, rfl, rfl⟩
    · rcases (hadj ⟨v, hv⟩ ⟨u, hu⟩).1 h with h' | h'
      · exact ⟨_, _, h'.symm, rfl, rfl⟩
      · exact ⟨_, _, h', rfl, rfl⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨fun e => hab.ne (Fin.ext e), Or.inl ((hadj a b).2 (Or.inl hab))⟩

/-- **The adjacency function obtained from the word of a graph is symmetric on `range n`.** -/
theorem symmOn_of_encodes {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) : adj.SymmOn (Finset.range n) := by
  intro u hu v hv
  have hu' := Finset.mem_range.1 hu
  have hv' := Finset.mem_range.1 hv
  have := hadj ⟨u, hu'⟩ ⟨v, hv'⟩
  have := hadj ⟨v, hv'⟩ ⟨u, hu'⟩
  rw [Bool.eq_iff_iff]
  simp only at *
  rw [hadj ⟨u, hu'⟩ ⟨v, hv'⟩, hadj ⟨v, hv'⟩ ⟨u, hu'⟩]
  exact or_comm

theorem hasTW_iff_hasTreewidthAtMost {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) (k : ℕ) :
    HasTW adj (Finset.range n) k ↔ Lax228581.Treewidth.HasTreewidthAtMost G k := by
  rw [hasTreewidthAtMost_iff_rt]
  have hcong : ∀ u ∈ Finset.range n, ∀ v ∈ Finset.range n, adj.graph.Adj u v ↔ (liftGraph G).Adj u v :=
    fun u hu v hv => graph_adj_of_encodes hadj (Finset.mem_range.1 hu) (Finset.mem_range.1 hv)
  constructor
  · rintro ⟨t, ht, hw⟩; exact ⟨t, (isTD_congr hcong).1 ht, hw⟩
  · rintro ⟨t, ht, hw⟩; exact ⟨t, (isTD_congr hcong).2 ht, hw⟩

end Lax117284Proofs.Treewidth.Chars
