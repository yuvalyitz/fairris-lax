import Lax117284Proofs.Treewidth.Wrap.Nice

/-!
# The size of `niceOf t` (C8a)

* `niceOf_size_le_uncond` : `(niceOf t).size ≤ 2 * (|V| + 1) * size t` for every rooted tree `t`.
* `niceOf_size_le` : the bound `(|V| + 2) * (size t + 1)` of `proofs-todo/Statements.lean`, which is FALSE without
  the connectedness hypothesis (a root with empty bag and four leaf children with bag `{1,2,3,4}` gives
  `39 > 36`), under `t.Conn`.
-/

namespace Lax117284Proofs.Treewidth.Trees.RT

mutual
/-- The number of leaves of a rooted tree. -/
def nleaves : RT → ℕ
  | node _ ks => if ks = [] then 1 else nleavesL ks
def nleavesL : List RT → ℕ
  | [] => 0
  | k :: ks => nleaves k + nleavesL ks
end

theorem sizeL_eq : ∀ ks : List RT, sizeL ks = (ks.map size).sum
  | [] => rfl
  | k :: ks => by simp [sizeL, sizeL_eq ks]

theorem nleavesL_eq : ∀ ks : List RT, nleavesL ks = (ks.map nleaves).sum
  | [] => rfl
  | k :: ks => by simp [nleavesL, nleavesL_eq ks]

theorem size_node (X : Finset ℕ) (ks : List RT) : size (.node X ks) = 1 + (ks.map size).sum := by
  simp [size, sizeL_eq]

theorem nleaves_node_nil (X : Finset ℕ) : nleaves (.node X []) = 1 := by simp [nleaves]

theorem nleaves_node_cons (X : Finset ℕ) (k : RT) (ks : List RT) :
    nleaves (.node X (k :: ks)) = ((k :: ks).map nleaves).sum := by
  simp [nleaves, nleavesL_eq]

theorem size_pos (t : RT) : 0 < t.size := by
  cases t; simp [size_node]

theorem nleaves_le_size : ∀ t : RT, t.nleaves ≤ t.size := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rcases ks with _ | ⟨k, ks'⟩
    · simp [nleaves_node_nil, size_node]
    · rw [nleaves_node_cons, size_node]
      have : ((k :: ks').map nleaves).sum ≤ ((k :: ks').map size).sum :=
        List.sum_le_sum (fun i hi => ih i hi)
      omega

theorem sub_verts {X : Finset ℕ} {ks : List RT} {k : RT} (hk : k ∈ ks) : k.verts ⊆ (RT.node X ks).verts := by
  intro u hu
  rw [RT.verts_node]
  exact Or.inr ⟨k, hk, hu⟩

theorem rootBag_sub_verts (t : RT) : t.rootBag ⊆ t.verts := by
  intro u hu
  rw [mem_verts_iff]
  exact ⟨_, root_mem_bags t, hu⟩

end Lax117284Proofs.Treewidth.Trees.RT

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

/-- the number of nodes of `niceOf` of a tree with kids -/
theorem niceOf_size_cons (X : Finset ℕ) (k : RT) (ks : List RT) :
    (niceOf (.node X (k :: ks))).size + 1 =
      ((k :: ks).map (fun k' => (conv X (niceOf k')).size + 1)).sum := by
  rw [niceOf_node]
  simp only [List.map_cons]
  have hf : ∀ k' ∈ k :: ks, ((conv X (niceOf k')).Wf ∧ (conv X (niceOf k')).bag = X) := by
    intro k' hk'
    obtain ⟨c1, c2, -⟩ := conv_spec X (niceOf k') (niceOf_facts k').1
    exact ⟨c1, c2⟩
  obtain ⟨-, -, -, -, h5⟩ := fold_spec (ks.map (fun k' => conv X (niceOf k'))) (conv X (niceOf k))
    (hf k (by simp)).1 (by
      intro s hs
      obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hs
      exact ⟨(hf k' (List.mem_cons_of_mem _ hk')).1, by
        rw [(hf k' (List.mem_cons_of_mem _ hk')).2, (hf k (by simp)).2]⟩)
  rw [h5]
  simp only [List.map_map, Function.comp_def]
  have : ∀ l : List RT, (l.map (fun k' => (conv X (niceOf k')).size + 1)).sum =
      (l.map (fun k' => (conv X (niceOf k')).size)).sum + l.length := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [ih]; ring
  simp only [List.length_map, List.sum_cons, this]
  omega

theorem niceOf_size_nil (X : Finset ℕ) : (niceOf (.node X [])).size = 1 + X.card := by
  rw [niceOf_node]
  simp only [List.map_nil]
  obtain ⟨-, -, -, -, -, -, i7⟩ := introMany_spec (X.sort (· ≤ ·)) .leaf (Finset.sort_nodup _ _)
    (fun x _ => by simp) trivial
  rw [i7, Finset.length_sort]; simp [NT.size]

/-- the size of the converted kid -/
theorem conv_size_kid (X : Finset ℕ) (k : RT) :
    (conv X (niceOf k)).size = (niceOf k).size + (k.rootBag \ X).card + (X \ k.rootBag).card := by
  obtain ⟨a1, a2, -⟩ := niceOf_facts k
  obtain ⟨-, -, -, -, -, -, c7⟩ := conv_spec X (niceOf k) a1
  rw [c7, a2]

end Lax117284Proofs.Treewidth.Chars
