import Lax117284Proofs.ClientsILPRaw

/-!
The integer program with its variables regrouped by (type, subset): the columns below `nV n` are
the pairs `(r, s)` at `r * nZ n + s`, and the slack variables follow.
-/

namespace Lax117284Proofs.ClientsILP

open Finset

theorem sum_range_mul' (F : ℕ → ℕ) (a b : ℕ) :
    ∑ c ∈ range (a * b), F c = ∑ i ∈ range a, ∑ j ∈ range b, F (i * b + j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The regrouped problem: weights `w r s` of the pairs, slacks `sl j`, the type rows and the
client rows. -/
def Feas' (n m k : ℕ) (cnt : ℕ → ℕ) : Prop :=
  ∃ (w : ℕ → ℕ → ℕ) (sl : ℕ → ℕ),
    (∀ r < nT n, ∑ s ∈ range (nZ n), (if indepB n r s then w r s else 0) = cnt r) ∧
    (∀ j < n, ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n),
        (if indepB n r s = true ∧ s.testBit j = false then w r s else 0) + sl j = m - k)

/-- A column below `nV n`, written as a pair. -/
theorem col_div (n r s : ℕ) (hs : s < nZ n) : (r * nZ n + s) / nZ n = r ∧ (r * nZ n + s) % nZ n = s := by
  have := nZ_pos n
  rw [Nat.mul_comm r, Nat.mul_add_div this, Nat.div_eq_of_lt hs, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hs]
  simp

theorem coef_col (n r r' s : ℕ) (hr' : r' < nT n) (hs : s < nZ n) :
    coefRaw n r (r' * nZ n + s) =
      if indepB n r' s = true then
        (if r < nT n then (if r' = r then 1 else 0)
         else (if s.testBit (r - nT n) = false then 1 else 0))
      else 0 := by
  have hlt : r' * nZ n + s < nV n := by
    have : (r' + 1) * nZ n ≤ nT n * nZ n := Nat.mul_le_mul_right _ hr'
    simp only [nV]; nlinarith
  obtain ⟨h1, h2⟩ := col_div n r' s hs
  simp only [coefRaw, if_pos hlt, h1, h2]

theorem coef_slack (n r s' : ℕ) :
    coefRaw n r (nV n + s') = if nT n ≤ r ∧ s' = r - nT n then 1 else 0 := by
  simp only [coefRaw, if_neg (by omega : ¬ nV n + s' < nV n)]
  congr 1
  simp

theorem row_split (n r : ℕ) (y : ℕ → ℕ) :
    ∑ c ∈ range (nN n), coefRaw n r c * y c =
      ∑ r' ∈ range (nT n), ∑ s ∈ range (nZ n), coefRaw n r (r' * nZ n + s) * y (r' * nZ n + s) +
        ∑ s' ∈ range n, coefRaw n r (nV n + s') * y (nV n + s') := by
  have : nN n = nT n * nZ n + n := rfl
  rw [this, Finset.sum_range_add,
    sum_range_mul' (fun c => coefRaw n r c * y c) (nT n) (nZ n)]
  rfl

theorem row_type (n r : ℕ) (y : ℕ → ℕ) (hr : r < nT n) :
    ∑ c ∈ range (nN n), coefRaw n r c * y c =
      ∑ s ∈ range (nZ n), (if indepB n r s then y (r * nZ n + s) else 0) := by
  rw [row_split]
  have h0 : ∑ s' ∈ range n, coefRaw n r (nV n + s') * y (nV n + s') = 0 := by
    refine Finset.sum_eq_zero fun s' _ => ?_
    rw [coef_slack, if_neg (by omega)]; simp
  rw [h0, add_zero]
  rw [Finset.sum_eq_single r]
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [coef_col n r r s hr (Finset.mem_range.mp hs)]
    by_cases h : indepB n r s = true
    · simp [h, hr]
    · simp [h]
  · intro r' hr' hne
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [coef_col n r r' s (Finset.mem_range.mp hr') (Finset.mem_range.mp hs)]
    by_cases h : indepB n r' s = true <;> simp [h, hr, hne]
  · intro h; exact absurd (Finset.mem_range.mpr hr) h

theorem row_client (n j : ℕ) (y : ℕ → ℕ) (hj : j < n) :
    ∑ c ∈ range (nN n), coefRaw n (nT n + j) c * y c =
      ∑ r ∈ range (nT n), ∑ s ∈ range (nZ n),
        (if indepB n r s = true ∧ s.testBit j = false then y (r * nZ n + s) else 0) +
        y (nV n + j) := by
  rw [row_split]
  congr 1
  · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => ?_
    rw [coef_col n (nT n + j) r s (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)]
    have : ¬ nT n + j < nT n := by omega
    by_cases h : indepB n r s = true
    · by_cases h2 : s.testBit j = false <;> simp [h, this, h2]
    · simp [h]
  · rw [Finset.sum_eq_single j]
    · rw [coef_slack]; simp
    · intro s' _ hne
      rw [coef_slack, if_neg (by omega)]; simp
    · intro h; exact absurd (Finset.mem_range.mpr hj) h

theorem ilpNat_iff (n m k : ℕ) (cnt : ℕ → ℕ) :
    (∃ y : ℕ → ℕ, ∀ r < nM n, ∑ c ∈ range (nN n), coefRaw n r c * y c = rhsRaw n m k cnt r) ↔
      Feas' n m k cnt := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun r s => y (r * nZ n + s), fun j => y (nV n + j), fun r hr => ?_, fun j hj => ?_⟩
    · have := hy r (by simp only [nM]; omega)
      rw [row_type n r y hr, rhsRaw, if_pos hr] at this
      exact this
    · have := hy (nT n + j) (by simp only [nM]; omega)
      rw [row_client n j y hj, rhsRaw, if_neg (by omega)] at this
      simpa using this
  · rintro ⟨w, sl, h1, h2⟩
    refine ⟨fun c => if c < nV n then w (c / nZ n) (c % nZ n) else sl (c - nV n), fun r hr => ?_⟩
    have hz := nZ_pos n
    have hcol : ∀ r' s, r' < nT n → s < nZ n →
        (if r' * nZ n + s < nV n then w ((r' * nZ n + s) / nZ n) ((r' * nZ n + s) % nZ n)
          else sl (r' * nZ n + s - nV n)) = w r' s := by
      intro r' s hr' hs
      have hlt : r' * nZ n + s < nV n := by
        have : (r' + 1) * nZ n ≤ nT n * nZ n := Nat.mul_le_mul_right _ hr'
        simp only [nV]; nlinarith
      obtain ⟨e1, e2⟩ := col_div n r' s hs
      rw [if_pos hlt, e1, e2]
    by_cases hrT : r < nT n
    · rw [row_type n r _ hrT, rhsRaw, if_pos hrT, ← h1 r hrT]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hcol r s hrT (Finset.mem_range.mp hs)]
    · obtain ⟨j, rfl⟩ : ∃ j, r = nT n + j := ⟨r - nT n, by omega⟩
      have hj : j < n := by simp only [nM] at hr; omega
      rw [row_client n j _ hj, rhsRaw, if_neg hrT, ← h2 j hj]
      congr 1
      · refine Finset.sum_congr rfl fun r' hr' => Finset.sum_congr rfl fun s hs => ?_
        rw [hcol r' s (Finset.mem_range.mp hr') (Finset.mem_range.mp hs)]
      · simp

end Lax117284Proofs.ClientsILP
