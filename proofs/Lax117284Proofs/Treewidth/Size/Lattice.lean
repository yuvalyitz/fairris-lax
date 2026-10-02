import Lax117284Proofs.Treewidth.Size.Join
import Lax117284Proofs.Treewidth.Chars.Lattice

/-!
# Size bounds (WP P1), part 5: the lattice dynamic programme of `joinC`

Every cell of the lattice DP (`Cell a b i j C`) holds at most `4^(L+1)` states, where `L` bounds the entries of the ring
sums (`L = L₁ + L₂` for entries `≤ L₁`, `≤ L₂`): the states of a cell have pairwise distinct `τ`-components, and these are
non-empty typical sequences over `{0..L}` (`card_typicalSeqs_le`).  Consequently `latticeStates`, `ringTypList` and the
list `ys` of `joinC` are at most `4^(L+1)` long (`L = 2 kmax` for `Good` inputs with `maxEntry ≤ kmax`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem getD_le_of_all {a : List ℕ} {L : ℕ} (h : ∀ x ∈ a, x ≤ L) (i : ℕ) : a.getD i 0 ≤ L := by
  by_cases hi : i < a.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem pathSum_le {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂)
    (P : List (ℕ × ℕ)) : ∀ x ∈ pathSum a b P, x ≤ L₁ + L₂ := by
  intro x hx
  unfold pathSum at hx
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  exact Nat.add_le_add (getD_le_of_all ha _) (getD_le_of_all hb _)

theorem card_typicalSeqs_le' (L : ℕ) : (typicalSeqs L).card ≤ 4 ^ (L + 1) := by
  have := card_typicalSeqs_le L
  rw [pow_succ]
  omega

/-- A duplicate-free (by first component) list of states, all typical over `{0..L}`, is short. -/
theorem states_length_le {C : List LState} {L : ℕ} (hnd : (C.map Prod.fst).Nodup)
    (h : ∀ s ∈ C, s.1 ∈ typicalSeqs L) : C.length ≤ 4 ^ (L + 1) := by
  have h1 : C.length = (C.map Prod.fst).length := (List.length_map _).symm
  have h2 : (C.map Prod.fst).length = (C.map Prod.fst).toFinset.card :=
    (List.toFinset_card_of_nodup hnd).symm
  have h3 : (C.map Prod.fst).toFinset ⊆ typicalSeqs L := by
    intro l hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hl)
    exact h s hs
  rw [h1, h2]
  exact le_trans (Finset.card_le_card h3) (card_typicalSeqs_le' L)

theorem cell_length_le {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) {i j : ℕ}
    {C : List LState} (hC : Cell a b i j C) : C.length ≤ 4 ^ (L₁ + L₂ + 1) := by
  refine states_length_le hC.2.2 ?_
  intro s hs
  obtain ⟨hp, he⟩ := hC.1 s hs
  rw [mem_typicalSeqs_iff_exists]
  refine ⟨pathSum a b s.2.reverse, ?_, pathSum_le ha hb _, he.symm⟩
  obtain ⟨h1, -, -⟩ := hp
  intro hnil
  have : s.2.reverse = [] := by
    unfold pathSum at hnil
    exact List.map_eq_nil_iff.1 hnil
  rw [this] at h1
  simp at h1

theorem latticeStates_length_le {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) :
    (latticeStates a b).length ≤ 4 ^ (L₁ + L₂ + 1) := by
  by_cases ha' : a = []
  · subst ha'; simp
  by_cases hb' : b = []
  · subst hb'; simp
  exact cell_length_le ha hb (latticeStates_cell ha' hb')

theorem ringTypList_length_le {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) :
    (ringTypList a b).length ≤ 4 ^ (L₁ + L₂ + 1) := by
  unfold ringTypList
  rw [List.length_map]
  exact latticeStates_length_le ha hb

/-- The list `ys` of `joinC` (deduplicated, shifted, filtered ring sums). -/
theorem joinYs_length_le {a b : List ℕ} {c kmax L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) :
    ((((ringTypList a b).map (fun d => d.map (· - c))).dedup).filter (fun d => d.all (· ≤ kmax))).length ≤
      4 ^ (L₁ + L₂ + 1) := by
  refine le_trans (List.length_filter_le _ _) (le_trans (List.dedup_sublist _).length_le ?_)
  rw [List.length_map]
  exact ringTypList_length_le ha hb

end Lax117284Proofs.Treewidth.Chars
