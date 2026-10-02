import Lax117284Proofs.Treewidth.Fun.E2Base

/-!
# WP E2 (2): sizes never grow under `norm`, `relabel (erase ·)`, `filter`, `sort`, `typical`

`sz_norm_le : sz (norm c) ≤ sz c` and the same for `forgetC`.  These make the cost of `norm` and `forgetC` bounds in terms of
the *input* size only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lax117284Proofs.Treewidth.Seq

theorem sz_filter_le {α : Type} [ToVal α] (p : α → Bool) : ∀ l : List α, sz (l.filter p) ≤ sz l
  | [] => by simp
  | a :: l => by
    have ih := sz_filter_le p l
    rw [List.filter_cons]
    split_ifs
    · rw [sz_cons, sz_cons]; omega
    · rw [sz_cons]; omega

theorem sz_map_le {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_perm {α : Type} [ToVal α] {l l' : List α} (h : l.Perm l') : sz l = sz l' := by
  rw [sz_list, sz_list, h.length_eq, (h.map sz).sum_eq]

theorem sz_take_le {α : Type} [ToVal α] (n : ℕ) : ∀ l : List α, sz (l.take n) ≤ sz l
  | [] => by simp
  | a :: l => by
    cases n with
    | zero => simp; have := sz_pos (a :: l); omega
    | succ n =>
      have ih := sz_take_le n l
      rw [List.take_succ_cons, sz_cons, sz_cons]; omega

theorem typical_length_le_length_aux (t : List ℕ) : ∀ (a : List ℕ),
    (a.foldl push t).length ≤ t.length + a.length
  | [] => by simp
  | y :: a => by
    have h := typical_length_le_length_aux (push t y) a
    have h2 : (push t y).length ≤ t.length + 1 := by
      simp only [push, List.length_append, List.length_singleton]
      have := E1A.length_cut_le t y; omega
    simp only [List.foldl_cons, List.length_cons]; omega

theorem typical_length_le_length (a : List ℕ) : (typical a).length ≤ a.length := by
  have := typical_length_le_length_aux [] a
  simpa [typical] using this

theorem sz_typical_le (a : List ℕ) : sz (typical a) ≤ sz a := by
  rw [sz_list_nat, sz_list_nat]
  have := typical_length_le_length a
  omega

theorem sz_mem_add_two {α : Type} [ToVal α] {a : α} {l : List α} (h : a ∈ l) : sz a + 2 ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have := sz_pos l; omega
    · have := ih h; have := sz_pos b; omega

theorem sz_norm_le : ∀ c : CT, sz (norm c) ≤ sz c := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    have hmap : sz (ks.map norm) ≤ sz ks := sz_map_le norm ks ih
    rw [norm_node']
    have hFsz := sz_filter_le (keep S) (ks.map norm)
    have hFmem : ∀ k ∈ (ks.map norm).filter (keep S), sz k + 2 ≤ sz ks := by
      intro k hk
      have hk' := (List.mem_filter.1 hk).1
      obtain ⟨k', hk'', rfl⟩ := List.mem_map.1 hk'
      have := sz_mem_add_two hk''
      have := ih k' hk''
      omega
    generalize (ks.map norm).filter (keep S) = F at hFsz hFmem
    have hy := sz_take_le 1 y
    have hp1 := sz_pos ks
    rw [sz_ct_node' S y ks]
    cases F with
    | nil =>
      rw [normF_nil, sz_ct_node']
      have : sz ([] : List CT) = 1 := rfl
      omega
    | cons k F' =>
      cases F' with
      | nil =>
        have hk := hFmem k (by simp)
        rw [normF_single]
        split_ifs with hS
        · obtain ⟨kS, ky, kks⟩ := k
          simp only [CT.S, CT.y, CT.kids]
          rw [sz_ct_node']
          have h1 := sz_typical_le (y ++ ky)
          have h2 := sz_append y ky
          rw [sz_ct_node'] at hk
          omega
        · rw [sz_ct_node']
          have : sz [k] = sz k + 2 := by rw [sz_cons]; rfl
          omega
      | cons k2 F'' =>
        rw [normF_ge2, sz_ct_node', sz_perm (sortKids_perm S _)]
        omega

end E2
end Lax117284Proofs.Treewidth.Fun
