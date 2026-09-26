import Lax117284Proofs.ClientsILPRaw

/-!
Sizes of the integer program: everything is at most `Q n + 2`, where `Q n = 2 ^ (2 n² + n + 3)`.
-/

namespace Lax117284Proofs.ClientsILP

/-- When the word is at least this long, the program's word is shorter than it. -/
def Q (n : ℕ) : ℕ := 2 ^ (2 * (n * n) + n + 3)

theorem n_le_nZ (n : ℕ) : n < nZ n := Nat.lt_two_pow_self

theorem n_le_nT (n : ℕ) : n ≤ nT n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact le_trans (Nat.lt_two_pow_self (n := n)).le
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self n))

theorem nT_le_nV (n : ℕ) : nT n ≤ nV n := by
  have := nZ_pos n; simp only [nV]; nlinarith [nT_pos n]

theorem nZ_le_nV (n : ℕ) : nZ n ≤ nV n := by
  have := nT_pos n; simp only [nV]; nlinarith [nZ_pos n]

theorem nV_eq (n : ℕ) : nV n = 2 ^ (n * n + n) := by
  simp only [nV, nT, nZ, ← pow_add]

theorem zLen_le (n : ℕ) : zLen n ≤ Q n + 2 := by
  have h1 : nM n ≤ 2 * nT n := by have := n_le_nT n; simp only [nM]; omega
  have h2 : nN n ≤ 2 * nV n := by
    have := n_le_nZ n; have := nZ_le_nV n; simp only [nN]; omega
  have h3 : nM n * nN n ≤ 4 * (nT n * nV n) := by
    calc nM n * nN n ≤ (2 * nT n) * (2 * nV n) := Nat.mul_le_mul h1 h2
      _ = 4 * (nT n * nV n) := by ring
  have h4 : nT n * nV n = 2 ^ (2 * (n * n) + n) := by
    rw [nV_eq, nT, ← pow_add]; congr 1; ring
  have h5 : 4 * 2 ^ (2 * (n * n) + n) = 2 ^ (2 * (n * n) + n + 2) := by
    rw [pow_add _ _ 2]; ring
  have h6 : 2 * nT n ≤ 2 ^ (2 * (n * n) + n + 2) := by
    have : 2 * nT n = 2 ^ (n * n + 1) := by rw [nT, pow_succ]; ring
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.zero_le n])
  have h7 : Q n = 2 * 2 ^ (2 * (n * n) + n + 2) := by
    rw [Q, show 2 * (n * n) + n + 3 = (2 * (n * n) + n + 2) + 1 by ring, pow_succ]; ring
  simp only [zLen]
  omega

theorem sizes_le_zLen (n : ℕ) : nT n ≤ zLen n ∧ nZ n ≤ zLen n ∧ nV n ≤ zLen n ∧ nN n ≤ zLen n ∧
    nM n ≤ zLen n ∧ n * n < nT n ∧ n < nZ n ∧ 2 ≤ zLen n := by
  have hT := nT_pos n
  have hN : nN n ≤ nM n * nN n := by
    have : 1 ≤ nM n := by simp only [nM]; omega
    nlinarith [nN_pos n]
  have h1 := nT_le_nV n
  have h2 := nZ_le_nV n
  have h3 : n * n < nT n := by
    rw [nT]; exact Nat.lt_two_pow_self
  refine ⟨?_, ?_, ?_, ?_, ?_, h3, n_le_nZ n, ?_⟩ <;> simp only [zLen, nN, nM, nV] at * <;> omega

end Lax117284Proofs.ClientsILP
