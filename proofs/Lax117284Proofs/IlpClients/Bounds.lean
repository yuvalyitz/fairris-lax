import Lax117284Proofs.IlpClients.Final

/-!
# Numeric Bounds: Alg F Runs with Word-Sized Numbers

Let `Bd n cnt B = (n+1) · n! · (N K + ∑_{t<T} cnt t + B + 1)` (`N = nN n`, `K = Kn n`).  For a
certificate in the box every intermediate number of `decode` is at most `Bd` (the digits, `sigma`,
`cp`, `Sj`, `P_i`, `Q_i`, the values of the extras and, once the guards hold, of the bases; a
running sum of at most `n` extras is at most `n · Bd`), and `Bd n cnt B ≤ (zLen n + v + 1)^4` when
`B` and all `cnt t` (`t < T`) are at most `v`.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

/-- The bound on every intermediate number. -/
def Bd (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : ℕ :=
  (n + 1) * n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1)

section Numbers

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {ω : Cert}


theorem sigma_le (d : ℕ → ℕ) (t : ℕ) : sigma n d t ≤ nN n * Kn n := by
  unfold sigma
  calc ∑ c ∈ range (nN n), (if tyOf n c = some t ∧ d c < Kn n then d c else 0)
      ≤ ∑ _c ∈ range (nN n), Kn n := by
        refine Finset.sum_le_sum fun c _ => ?_
        split_ifs with h
        · exact h.2.le
        · exact Nat.zero_le _
    _ = nN n * Kn n := by simp















/-- The rank of an extra is below the number of extras. -/
theorem rk_lt_card {d : ℕ → ℕ} {c : ℕ} (hc : c ∈ Ext n d) : rk n d c < (Ext n d).card := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨c, hc, ?_⟩
    simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hxN : x < nN n := hx.1.trans (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxN, hx.2⟩



end Numbers

section Sizes

/-- `n + 1 ≤ 2 ^ n`. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self


theorem nT_le_nN (n : ℕ) : nT n ≤ nN n := by
  unfold nN nV
  have := Nat.mul_le_mul_left (nT n) (Nat.one_le_two_pow (n := n))
  simp only [nZ]; nlinarith [Nat.one_le_two_pow (n := n)]

theorem nN_le_zLen (n : ℕ) : nN n + 1 ≤ zLen n := by
  unfold zLen nM
  have h1 : 1 ≤ nT n + n := by have := nT_pos n; omega
  have : nN n * 1 ≤ (nT n + n) * nN n := by nlinarith
  omega

theorem n_succ_le_zLen (n : ℕ) : n + 1 ≤ zLen n := by
  have h1 := nN_le_zLen n
  unfold nN at h1
  omega

theorem Kn_le_zLen (n : ℕ) : Kn n ≤ zLen n := by
  have h1 : (n + 1) ^ (n + 1) ≤ nV n := by
    calc (n + 1) ^ (n + 1) ≤ (2 ^ n) ^ (n + 1) := Nat.pow_le_pow_left (succ_le_two_pow n) _
      _ = nV n := by unfold nV nT nZ; rw [← pow_mul, ← pow_add]; congr 1
  have h2 := nN_le_zLen n
  unfold Kn nN at *
  omega


end Sizes

end

end Lax117284Proofs.IlpClients
