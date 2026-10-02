import Lax117284Proofs.Treewidth.Fun.E3Util
import Lax117284Proofs.Treewidth.Size.Plans

/-!
# WP E3: facts about `winPlans` / `kidChoices` used by the cost analysis

* every vertex set in the output is contained in `verts` of the input (so its cardinality is `≤ sz`);
* `card_verts_le_sz`;
* every combination has one entry per kid, and `kidChoices` is never empty;
* the `whole` part of `winPlans` is at least as long as `kidChoices`.
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars CT

theorem card_vertsL_le_sz : ∀ (ks : List CT), (∀ k ∈ ks, (verts k).card ≤ sz k) → (vertsL ks).card ≤ sz ks
  | [], _ => by simp [vertsL, sz_nil]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := card_vertsL_le_sz ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    have := Finset.card_union_le (verts k) (vertsL ks)
    rw [sz_cons]; simp only [vertsL]; omega

theorem card_verts_le_sz (t : CT) : (verts t).card ≤ sz t := by
  induction t using CT.ind with
  | h S y ks ih =>
    have h1 := card_vertsL_le_sz ks ih
    have h2 := Finset.card_union_le S (vertsL ks)
    rw [sz_ct_node, sz_finset, verts_node]
    have := sz_pos y
    omega

theorem foldl_union_sub (V : Finset ℕ) :
    ∀ (combo : List (Option WPlan × CT × Finset ℕ)) (S : Finset ℕ), S ⊆ V → (∀ c ∈ combo, c.2.2 ⊆ V) →
      combo.foldl (fun a c => a ∪ c.2.2) S ⊆ V
  | [], S, hS, _ => by simpa using hS
  | c :: combo, S, hS, h => by
    simp only [List.foldl_cons]
    exact foldl_union_sub V combo _ (Finset.union_subset hS (h c (by simp)))
      (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

mutual
theorem winPlans_sub (v : ℕ) : ∀ (lo : ℕ) (t : CT), ∀ x ∈ winPlans v lo t, x.2.2 ⊆ t.verts
  | lo, node S y ks, x, hx => by
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    have hS : S ⊆ (node S y ks).verts := subset_verts (node S y ks)
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · exact hS
    · exact hS
    · have := kidChoices_sub v ks combo hcombo
      refine foldl_union_sub _ combo S hS (fun c hc => ?_)
      exact fun w hw => mem_verts_node.2 (Or.inr (by
        have := (mem_vertsL.1 (this c hc hw)); exact this))
theorem kidChoices_sub (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks, ∀ c ∈ combo, c.2.2 ⊆ vertsL ks
  | [], combo, h, c, hc => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp at hc
  | k :: ks, combo, h, c, hc => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have ih := kidChoices_sub v ks combo' hcombo'
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases List.mem_cons.1 ho with rfl | ho
      · intro w hw; simp at hw
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        have := winPlans_sub v 0 k p hp
        intro w hw
        simp only [vertsL, Finset.mem_union]
        exact Or.inl (this hw)
    · intro w hw
      simp only [vertsL, Finset.mem_union]
      exact Or.inr (ih c hc hw)
end

theorem kidChoices_combo_length (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks, combo.length = ks.length
  | [], combo, h => by simp only [kidChoices, List.mem_singleton] at h; subst h; simp
  | k :: ks, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    simp [kidChoices_combo_length v ks combo' hcombo']

theorem kidChoices_length_pos (v : ℕ) : ∀ (ks : List CT), 1 ≤ (kidChoices v ks).length
  | [] => by simp [kidChoices]
  | k :: ks => by
    have := kidChoices_length_pos v ks
    simp only [kidChoices, List.length_flatMap]
    have h1 : (kidChoices v ks).length ≤ (List.map (fun o => (List.map (fun x => o :: x) (kidChoices v ks)).length) ((none, k, (∅ : Finset ℕ)) :: List.map (fun p => (some p.1, p.2.1, p.2.2)) (winPlans v 0 k))).sum := by
      simp only [List.map_cons, List.sum_cons, List.length_map]; omega
    omega

theorem kidChoices_le_winPlans (v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    (kidChoices v ks).length ≤ (winPlans v lo (node S y ks)).length := by
  simp only [winPlans, List.length_append, List.length_map]; omega

end Lax117284Proofs.Treewidth.Fun
