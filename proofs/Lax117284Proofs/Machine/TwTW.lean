import Mathlib.Tactic
import Lax228581.Treewidth

/-!
Two facts about the archive's treewidth: a graph on at most `w + 1` vertices has treewidth at most
`w` (a single bag), and a width at which there is no decomposition lies below the treewidth.
-/

namespace Lax117284Proofs.Machine.TwTW

open Lax228581.Treewidth

/-- The decomposition with one node and one bag holding every vertex. -/
def oneBag {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : TreeDecomposition G where
  Node := Unit
  tree := ⊥
  isTree := ⟨⟨fun u v => by cases u; cases v; exact SimpleGraph.Reachable.refl _⟩,
    SimpleGraph.isAcyclic_bot⟩
  bag _ := Finset.univ
  vertex_mem_bag v := ⟨(), Finset.mem_univ v⟩
  edge_mem_bag u v _ := ⟨(), Finset.mem_univ u, Finset.mem_univ v⟩
  bag_indices_connected v := by
    have : Nonempty {i : Unit | v ∈ (Finset.univ : Finset V)} := ⟨⟨(), Finset.mem_univ v⟩⟩
    refine ⟨fun a b => ?_⟩
    have : a = b := Subsingleton.elim _ _
    rw [this]

theorem hasTW_of_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {w : ℕ}
    (h : Fintype.card V ≤ w + 1) : HasTreewidthAtMost G w :=
  ⟨oneBag G, fun _ => by simpa [oneBag] using h⟩

theorem hasTW_mono {V : Type} {G : SimpleGraph V} {w w' : ℕ} (h : HasTreewidthAtMost G w)
    (hw : w ≤ w') : HasTreewidthAtMost G w' := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun i => (hD i).trans (by omega)⟩

/-- **A width without a decomposition lies below the treewidth.** -/
theorem lt_treewidth_of_not {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : ℕ}
    (h : ¬ HasTreewidthAtMost G w) : w < treewidth G := by
  have hne : {w | HasTreewidthAtMost G w}.Nonempty := ⟨Fintype.card V, hasTW_of_card G (by omega)⟩
  have hmem : treewidth G ∈ {w | HasTreewidthAtMost G w} := Nat.sInf_mem hne
  by_contra hc
  exact h (hasTW_mono hmem (by omega))

end Lax117284Proofs.Machine.TwTW
