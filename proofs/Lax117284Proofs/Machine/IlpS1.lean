import Lax117284Proofs.Machine.IlpAddRow

/-!
The first pass over `Sj`: the small digits.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

/-- The small-digit part of `Sj`, over the columns below `k`. -/
def s1P (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) : ℕ :=
  ∑ c ∈ range k, if d c < Kn n then d c * coef n (nT n + j) c else 0

theorem s1P_succ (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) :
    s1P n d j (k + 1) =
      s1P n d j k + (if d k < Kn n then d k else 0) * coef n (nT n + j) k := by
  unfold s1P
  rw [Finset.sum_range_succ]
  by_cases h : d k < Kn n <;> simp [h]

theorem s1P_le (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) : s1P n d j k ≤ k * Kn n := by
  induction k with
  | zero => simp [s1P]
  | succ k ih =>
    rw [s1P_succ]
    have h1 : (if d k < Kn n then d k else 0) * coef n (nT n + j) k ≤ Kn n := by
      have := coef_le_one n (nT n + j) k
      have h2 : (if d k < Kn n then d k else 0) ≤ Kn n := by split_ifs with h <;> omega
      calc _ ≤ (if d k < Kn n then d k else 0) * 1 := Nat.mul_le_mul_left _ this
        _ ≤ Kn n := by omega
    nlinarith

theorem s1P_N (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j : ℕ) :
    s1P n d j (nN n) = ∑ c ∈ range (nN n), if d c < Kn n then d c * coef n (nT n + j) c else 0 := rfl

/-- The multiplier of the pass. -/
theorem mvAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n)
      (asg "mv" (.mul (.get "dg" (V "i")) (ltF (.get "dg" (V "i")) (V "K"))))
      (fun σ σ' => σ' = σ.setVar "mv" (v (σ.vars "i") * if v (σ.vars "i") < Kn n then 1 else 0))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    obtain ⟨hdgv, hldg, -⟩ := colFacts hv hC hi
    have hdg' : (σ.arrs "dg").getD (σ.vars "i") 0 = v (σ.vars "i") := by
      rw [hC.2, getD_arrOf_lt (by have : nN n ≤ Dn n := by unfold Dn; omega
                                  omega)]
    have hK := hC.1.hK
    have hBK := hb.NK_lt
    have hBN := hb.nN_lt
    have hBKn := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hprod := mul_le_of_le_one' ((σ.arrs "dg").getD (σ.vars "i") 0)
      (1 - (1 - (σ.vars "K" - (σ.arrs "dg").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hdg', hK]
    by_cases h : v (σ.vars "i") < Kn n
    · have e : 1 - (1 - (Kn n - v (σ.vars "i"))) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (Kn n - v (σ.vars "i"))) = 0 := by omega
      rw [e, if_neg h]

theorem s1_mult (n : ℕ) (v : ℕ → ℕ) (k : ℕ) (hk : k < nN n) :
    v k * (if v k < Kn n then 1 else 0) = if dd n v k < Kn n then dd n v k else 0 := by
  rw [dd_lt hk]; split_ifs <;> simp

/-- **The first pass over `Sj`.** -/
theorem s1Com_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "S" = arrOf n (fun _ => 0))
      s1Com (fun _ σ' => CE n cnt bb v σ' ∧
        σ'.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n)))
      ((30 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + ((30 + 4) * n + 6) + 4) s1Body
    (CE n cnt bb v)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j k))
    (CE.stable (by decide) (by decide) (by decide)) hb.nN_lt (fun σ h => h.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hS⟩
      refine ⟨hC.setVar (by decide) _, ?_⟩
      simpa [s1P] using hS
    · rintro σ σ' - ⟨hC, hS, -⟩
      exact ⟨hC, hS⟩
  · intro k hk σ ⟨hC, hik, hS⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    obtain ⟨σ1, r1, e1⟩ := mvAssign_vals hb v hv σ ⟨hC, by omega⟩
    have hm1 : σ1.vars "mv" = if dd n v k < Kn n then dd n v k else 0 := by
      rw [e1]; simp [Env.setVar, hik, s1_mult n v k hk]
    have hMK : (if dd n v k < Kn n then dd n v k else 0) ≤ Kn n := by
      rw [dd_lt hk]; split_ifs with h <;> omega
    have hC1 : CE n cnt bb v σ1 := by rw [e1]; exact hC.setVar (by decide) _
    have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
    have hS1 : σ1.arrs "S" = arrOf n (fun j => s1P n (dd n v) j k) := by rw [e1]; simpa using hS
    have hBK := hb.NK_lt
    obtain ⟨σ2, r2, hC2, hi2, hm2, hS2⟩ := addRow_spec hb v k _ hk
      (fun j => s1P n (dd n v) j k)
      (fun j _ => by
        have := s1P_le n (dd n v) j k
        have : k * Kn n ≤ nN n * Kn n := Nat.mul_le_mul_right _ hk.le
        rw [hm1]; omega) σ1 ⟨hC1, hi1, rfl, hS1⟩
    have hBN := hb.nN_lt
    obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by show σ2.vars "i" + 1 < B; rw [hi2]; omega)
    refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
    · rw [e3]; simp [Env.setVar, hi2]
    · rw [e3]
      show σ2.arrs "S" = _
      rw [hS2, hm1]
      refine arrOf_congr fun j _ => ?_
      rw [s1P_succ]

end Lax117284Proofs.Machine.Ilp
