import Lax117284Proofs.Treewidth.Fun.E1
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize

/-!
# WP E5 (0): generic arithmetic and size lemmas used by the E5 layers

* sums of per-element costs (`sum_map_le_mul`, `sum_map_const`);
* `sz` of `take / drop / filter / map / append / perm` of lists;
* powers `t ^ d` of `t = s + 1` as atoms (`pw_le`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5

open ToVal

/-! ## sums -/

theorem sum_map_const {α : Type} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-! ## powers of `t = s + 1` -/

theorem le_pw {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : 1 ≤ d) : t ≤ t ^ d := by
  calc t = t ^ 1 := (pow_one t).symm
    _ ≤ t ^ d := Nat.pow_le_pow_right ht hd

theorem one_le_pw {t : ℕ} (ht : 1 ≤ t) (d : ℕ) : 1 ≤ t ^ d := Nat.one_le_pow _ _ ht

/-! ## sizes of list operations -/

theorem sz_filter_le' {α : Type} [ToVal α] (p : α → Bool) : ∀ l : List α, sz (l.filter p) ≤ sz l
  | [] => by simp
  | a :: l => by
    have ih := sz_filter_le' p l
    rw [List.filter_cons]
    split_ifs
    · rw [sz_cons, sz_cons]; omega
    · rw [sz_cons]; omega

theorem sz_map_le' {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le' f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_append_le {α : Type} [ToVal α] (l₁ l₂ : List α) : sz (l₁ ++ l₂) ≤ sz l₁ + sz l₂ := by
  have := sz_append l₁ l₂; omega

theorem sz_perm' {α : Type} [ToVal α] {l l' : List α} (h : l.Perm l') : sz l = sz l' := by
  rw [sz_list, sz_list, h.length_eq, (h.map sz).sum_eq]

theorem sz_mem_lt {α : Type} [ToVal α] {a : α} {l : List α} (h : a ∈ l) : sz a + 2 ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.mp h with rfl | h
    · have := sz_pos l; omega
    · have := ih h; have := sz_pos b; omega

theorem sz_getD_le {α : Type} [ToVal α] (l : List α) (i : ℕ) (d : α) : sz (l.getD i d) ≤ sz l + sz d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp [sz_cons]; omega
    | succ i => have := ih i; simp only [List.getD_cons_succ, sz_cons]; omega

theorem sz_finset_le_of_subset {S T : Finset ℕ} (h : S ⊆ T) : sz S ≤ sz T := by
  rw [sz_finset, sz_finset]; have := Finset.card_le_card h; omega

theorem sz_inter_le (S T : Finset ℕ) : sz (S ∩ T) ≤ sz S :=
  sz_finset_le_of_subset Finset.inter_subset_left

theorem sz_insert_le (a : ℕ) (S : Finset ℕ) : sz (insert a S) ≤ sz S + 2 := by
  rw [sz_finset, sz_finset]
  have := Finset.card_insert_le a S
  omega

theorem sz_union_le (S T : Finset ℕ) : sz (S ∪ T) ≤ sz S + sz T := by
  rw [sz_finset, sz_finset, sz_finset]
  have := Finset.card_union_le S T
  omega

theorem card_le_sz (S : Finset ℕ) : S.card ≤ sz S := by rw [sz_finset]; omega

/-! ## `typical` does not lengthen -/

theorem typical_length_le_aux (t : List ℕ) : ∀ (a : List ℕ),
    (a.foldl Lax117284Proofs.Treewidth.Seq.push t).length ≤ t.length + a.length
  | [] => by simp
  | y :: a => by
    have h := typical_length_le_aux (Lax117284Proofs.Treewidth.Seq.push t y) a
    have h2 : (Lax117284Proofs.Treewidth.Seq.push t y).length ≤ t.length + 1 := by
      simp only [Lax117284Proofs.Treewidth.Seq.push, List.length_append, List.length_singleton]
      have := E1A.length_cut_le t y; omega
    simp only [List.foldl_cons, List.length_cons]; omega

theorem typical_length_le (a : List ℕ) : (Lax117284Proofs.Treewidth.Seq.typical a).length ≤ a.length := by
  have := typical_length_le_aux [] a
  simpa [Lax117284Proofs.Treewidth.Seq.typical] using this

/-! ## reaching the library / E1 from an extension of `e1Δ` -/

section plumbing
variable {Δ : ℕ → Option Tm}

theorem lib_of (hE : E1.e1Δ ⊑ Δ) : Lib.Δ ⊑ Δ := Ext.trans E1.extLib hE
theorem l1 (hE : E1.e1Δ ⊑ Δ) : Lib1.Δ ⊑ Δ := Ext.trans Lib.ext1 (lib_of hE)
theorem l2 (hE : E1.e1Δ ⊑ Δ) : Lib2.Δ ⊑ Δ := Ext.trans Lib.ext2 (lib_of hE)
theorem l3 (hE : E1.e1Δ ⊑ Δ) : Lib3.Δ ⊑ Δ := Ext.trans Lib.ext3 (lib_of hE)
theorem l4 (hE : E1.e1Δ ⊑ Δ) : Lib4.Δ ⊑ Δ := Ext.trans Lib.ext4 (lib_of hE)
theorem eA (hE : E1.e1Δ ⊑ Δ) : E1A.Δ ⊑ Δ := Ext.trans E1.extA hE
theorem eB (hE : E1.e1Δ ⊑ Δ) : E1B.Δ ⊑ Δ := Ext.trans E1.extB hE
theorem eD (hE : E1.e1Δ ⊑ Δ) : E1D.Δ ⊑ Δ := Ext.trans E1.ext hE
end plumbing

/-- every id of `e1Δ` is `< 158` -/
theorem e1Δ_lt {f : ℕ} {b : Tm} (h : E1.e1Δ f = some b) : f < 158 := by
  unfold E1.e1Δ Lib.extend layerΔ at h
  by_cases h1 : 128 ≤ f
  · simp only [h1, if_true] at h; exact E1.e1Tbl_lt h
  · have := h1
    omega

theorem lt_of_bnd {B s N : ℕ} (hB : 3000 + 400 * (s + 1) < B) (hN : N ≤ 3000) : N < B := by omega

end E5
end Lax117284Proofs.Treewidth.Fun
