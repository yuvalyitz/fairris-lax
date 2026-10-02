import Lax117284Proofs.Treewidth.Seq.Ext

/-!
# `Ext` is the paper's Def. 3.6

The paper writes `E(a) = {a* | ∃ 1 = t₁ < t₂ < … < t_{n+1} ∀ i ∀ t_i ≤ k < t_{i+1} [a*(k) = a(i)]}`
(with `t_{n+1} = l(a*) + 1`).  In `0`-based form this is `ExtIdx`; `ext_iff_extIdx` shows that it
coincides with the recursive `Ext`.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- The paper's definition of `a' ∈ E(a)`, `0`-indexed: breakpoints `t 0 = 0 < t 1 < … < t n =
l(a')` such that `a'` is constantly `a_i` on `[t i, t (i+1))`. -/
def ExtIdx (a w : List ℕ) : Prop :=
  ∃ t : ℕ → ℕ, t 0 = 0 ∧ (∀ i, i < a.length → t i < t (i + 1)) ∧ t a.length = w.length ∧
    ∀ i, i < a.length → ∀ k, t i ≤ k → k < t (i + 1) → ent w k = ent a i

theorem extIdx_of_ext : ∀ {a w : List ℕ}, Ext a w → ExtIdx a w := by
  intro a
  induction a with
  | nil =>
    intro w h
    rw [ext_nil_iff] at h; subst h
    exact ⟨fun _ => 0, rfl, fun i hi => by simp at hi, rfl, fun i hi => by simp at hi⟩
  | cons x a ih =>
    intro w h
    obtain ⟨p, w0, rfl, hw0⟩ := ext_cons_iff.mp h
    obtain ⟨t0, h0, h1, h2, h3⟩ := ih hw0
    refine ⟨fun i => if i = 0 then 0 else (p + 1) + t0 (i - 1), by simp, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => simp
      | succ j =>
        have := h1 j (by simpa using hi)
        simp; omega
    · simp [h2]
    · intro i hi k hk1 hk2
      cases i with
      | zero =>
        simp at hk1 hk2
        rw [ent_append_left _ (by simp; omega)]
        simp
        rw [ent_eq_getElem (by simp; omega)]; simp
      | succ j =>
        simp at hk1 hk2
        rw [ent_append_right _ (by simp; omega)]
        simp only [List.length_replicate, ent_cons_succ]
        exact h3 j (by simpa using hi) _ (by omega) (by omega)

theorem t_mono {t : ℕ → ℕ} {n : ℕ} (h : ∀ i, i < n → t i < t (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → t i ≤ t j := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
    exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (h j (by omega)))

theorem ext_of_extIdx : ∀ {a w : List ℕ}, ExtIdx a w → Ext a w := by
  intro a
  induction a with
  | nil =>
    intro w ⟨t, h0, h1, h2, h3⟩
    simp at h2
    rw [h0] at h2
    have : w = [] := List.length_eq_zero_iff.mp h2.symm
    subst this; exact ext_nil_nil
  | cons x a ih =>
    intro w ⟨t, h0, h1, h2, h3⟩
    have hm := t_mono h1
    have ht1 : 0 < t 1 := by have := h1 0 (by simp); rwa [h0] at this
    have ht1w : t 1 ≤ w.length := by
      rw [← h2]; exact hm 1 (a.length + 1) (by simp) le_rfl
    have hblock : w.take (t 1) = List.replicate (t 1) x := by
      apply List.ext_getElem
      · simp; omega
      · intro k hk1 hk2
        have hk : k < t 1 := by simpa [List.length_take] using hk2
        have := h3 0 (by simp) k (by omega) (by omega)
        rw [ent_eq_getElem (by omega)] at this
        simpa using this
    refine ext_cons_iff.mpr ⟨t 1 - 1, w.drop (t 1), ?_, ?_⟩
    · have : t 1 - 1 + 1 = t 1 := by omega
      rw [this, ← hblock, List.take_append_drop]
    · apply ih
      refine ⟨fun i => t (i + 1) - t 1, by simp, ?_, ?_, ?_⟩
      · intro i hi
        have e1 := h1 (i + 1) (by simp; omega)
        have e2 := hm 1 (i + 1) (by omega) (by simp; omega)
        show t (i + 1) - t 1 < t (i + 1 + 1) - t 1
        omega
      · have e1 := hm 1 (a.length + 1) (by simp) le_rfl
        show t (a.length + 1) - t 1 = (w.drop (t 1)).length
        rw [List.length_drop, ← h2]
        simp
      · intro i hi k hk1 hk2
        have e2 := hm 1 (i + 1) (by omega) (by simp; omega)
        have e3 := hm 1 (i + 1 + 1) (by omega) (by simp; omega)
        have e4 := h1 (i + 1) (by simp; omega)
        simp only at hk1 hk2
        have : ent (w.drop (t 1)) k = ent w (t 1 + k) := by
          unfold ent
          simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
        rw [this]
        have := h3 (i + 1) (by simp; omega) (t 1 + k) (by omega) (by omega)
        rwa [ent_cons_succ] at this

/-- `Ext` is the paper's Def. 3.6. -/
theorem ext_iff_extIdx {a w : List ℕ} : Ext a w ↔ ExtIdx a w :=
  ⟨extIdx_of_ext, ext_of_extIdx⟩

end Lax117284Proofs.Treewidth.Seq
