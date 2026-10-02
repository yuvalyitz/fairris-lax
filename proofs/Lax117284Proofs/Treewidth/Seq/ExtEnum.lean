import Lax117284Proofs.Treewidth.Seq.Ext
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card

/-!
# Enumerating extensions of a fixed length (Lemma 3.16)
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- All extensions of `a` of length exactly `k` (computable). -/
def extLen : List ℕ → ℕ → Finset (List ℕ)
  | [], 0 => {[]}
  | [], _ + 1 => ∅
  | _ :: _, 0 => ∅
  | x :: a, k + 1 => ((extLen (x :: a) k) ∪ (extLen a k)).image (List.cons x)

theorem mem_extLen {a w : List ℕ} {k : ℕ} : w ∈ extLen a k ↔ Ext a w ∧ w.length = k := by
  induction k generalizing a w with
  | zero =>
    cases a with
    | nil =>
      simp only [extLen, Finset.mem_singleton, List.length_eq_zero_iff, ext_nil_iff, and_self]
    | cons x a =>
      simp only [extLen, Finset.notMem_empty, false_iff, not_and]
      intro h; rw [List.length_eq_zero_iff] at *; intro hw; subst hw; exact absurd h (by simp)
  | succ k ih =>
    cases a with
    | nil =>
      simp only [extLen, Finset.notMem_empty, false_iff, not_and]
      intro h; rw [ext_nil_iff] at h; subst h; simp
    | cons x a =>
      simp only [extLen, Finset.mem_image, Finset.mem_union, ih]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨ext_cons_cons.mpr ⟨rfl, Or.inl h1⟩, by simp [h2]⟩
        · exact ⟨ext_cons_cons.mpr ⟨rfl, Or.inr h1⟩, by simp [h2]⟩
      · rintro ⟨h1, h2⟩
        cases w with
        | nil => simp at h2
        | cons y w =>
          obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h1
          · exact ⟨w, Or.inl ⟨h, by simpa using h2⟩, rfl⟩
          · exact ⟨w, Or.inr ⟨h, by simpa using h2⟩, rfl⟩

theorem card_extLen_cons (x k : ℕ) (a : List ℕ) :
    (extLen (x :: a) (k + 1)).card ≤ (extLen (x :: a) k).card + (extLen a k).card := by
  rw [extLen]; exact Finset.card_image_le.trans (Finset.card_union_le _ _)

theorem card_extLen_succ_le : ∀ (k : ℕ) (a : List ℕ), (extLen a (k + 1)).card ≤ 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro a
    cases a with
    | nil => simp [extLen]
    | cons x a =>
      have := card_extLen_cons x 0 a
      cases a with
      | nil => simp [extLen] at this ⊢
      | cons y a => simp [extLen] at this ⊢
  | succ k ih =>
    intro a
    cases a with
    | nil => simp [extLen]
    | cons x a =>
      have h1 := card_extLen_cons x (k + 1) a
      have h2 := ih (x :: a)
      have h3 := ih a
      rw [pow_succ]; omega

/-- **Lemma 3.16**: at most `2^(k-1)` extensions of `a` have length `k` (`k ≥ 1`). -/
theorem card_extLen_le (a : List ℕ) {k : ℕ} (hk : 1 ≤ k) : (extLen a k).card ≤ 2 ^ (k - 1) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simpa using card_extLen_succ_le k' a

theorem extLen_length {a w : List ℕ} {k : ℕ} (h : w ∈ extLen a k) : w.length = k :=
  (mem_extLen.mp h).2

end Lax117284Proofs.Treewidth.Seq
