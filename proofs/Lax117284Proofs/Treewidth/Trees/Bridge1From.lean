import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Root
import Lax117284Proofs.Treewidth.Trees.Bridge1Paths

/-!
# Bridge 1, direction (←): an `RT` decomposition is a `TreeDecomposition`

The abstract tree lives on the nodes-as-paths of the `RT` (`RT.paths`); the parent of a path drops its last step.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Trees.RootedTree Lax228581.Treewidth

theorem hasTreewidthAtMost_of_rt {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {t : RT}
    (htd : t.IsTD (liftGraph G) (Finset.range n)) (hw : t.Width w) : HasTreewidthAtMost G w := by
  classical
  let N := {p : List ℕ // p ∈ t.paths}
  let r : N := ⟨[], RT.nil_mem_paths t⟩
  let par : N → N := fun p => ⟨p.1.dropLast, RT.dropLast_mem_paths t _ p.2⟩
  let dd : N → ℕ := fun p => p.1.length
  have hR : Rooted r par dd := by
    refine ⟨rfl, ?_⟩
    intro x hx
    have : x.1 ≠ [] := fun e => hx (Subtype.ext e)
    show x.1.dropLast.length + 1 = x.1.length
    rw [List.length_dropLast]
    have := List.length_pos_iff.2 this
    omega
  let bag : N → Finset (Fin n) := fun q => Finset.univ.filter (fun y => y.1 ∈ t.bagAt q.1)
  have hbag : ∀ q y, y ∈ bag q ↔ y.1 ∈ t.bagAt q.1 := by intro q y; simp [bag]
  have hocc : ∀ y : Fin n, ∃ p ∈ t.paths, y.1 ∈ t.bagAt p := by
    intro y
    have : y.1 ∈ t.verts := by rw [htd.verts_eq]; exact Finset.mem_range.2 y.2
    obtain ⟨X, hX, hyX⟩ := (RT.mem_verts_iff _ _).1 this
    obtain ⟨p, hp, rfl⟩ := RT.exists_path_of_mem_bags t X hX
    exact ⟨p, hp, hyX⟩
  refine ⟨{ Node := N, tree := rgraph par, isTree := hR.isTree, bag := bag,
            vertex_mem_bag := ?_, edge_mem_bag := ?_, bag_indices_connected := ?_ }, ?_⟩
  · intro y
    obtain ⟨p, hp, h⟩ := hocc y
    exact ⟨⟨p, hp⟩, (hbag _ _).2 h⟩
  · intro u v huv
    have hadj : (liftGraph G).Adj u.1 v.1 := (SimpleGraph.map_adj _ _ _ _).2 ⟨u, v, huv, rfl, rfl⟩
    obtain ⟨X, hX, hu, hv⟩ := htd.edges u.1 v.1 hadj (Finset.mem_range.2 u.2) (Finset.mem_range.2 v.2)
    obtain ⟨p, hp, rfl⟩ := RT.exists_path_of_mem_bags t X hX
    exact ⟨⟨p, hp⟩, (hbag _ _).2 hu, (hbag _ _).2 hv⟩
  · intro y
    obtain ⟨p, hp, h⟩ := hocc y
    obtain ⟨p₀, hp₀, hyp₀, htop⟩ := RT.top_exists t htd.conn y.1 ⟨p, hp, h⟩
    have ht₀ : (⟨p₀, hp₀⟩ : N) ∈ {i : N | y ∈ bag i} := (hbag _ _).2 hyp₀
    have htop' : ∀ s ∈ {i : N | y ∈ bag i}, s ≠ ⟨p₀, hp₀⟩ → s ≠ r ∧ par s ∈ {i : N | y ∈ bag i} := by
      intro s hs hne
      have hq : s.1 ≠ p₀ := fun e => hne (Subtype.ext e)
      obtain ⟨h1, h2⟩ := htop s.1 s.2 ((hbag _ _).1 hs) hq
      exact ⟨fun e => h1 (congrArg Subtype.val e), (hbag _ _).2 h2⟩
    have : Nonempty ↥{i : N | y ∈ bag i} := ⟨⟨_, ht₀⟩⟩
    exact ⟨fun a b => (reachable_of_top hR ht₀ htop' a.1 a.2).trans
      (reachable_of_top hR ht₀ htop' b.1 b.2).symm⟩
  · intro q
    refine le_trans ?_ (hw _ (RT.bagAt_mem_bags t q.1 q.2))
    apply Finset.card_le_card_of_injOn Fin.val
    · intro y hy
      exact (hbag _ _).1 hy
    · intro a _ b _ e
      exact Fin.ext e

end Lax117284Proofs.Treewidth.Trees
