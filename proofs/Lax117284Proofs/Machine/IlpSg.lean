import Lax117284Proofs.Machine.IlpRk

/-!
The pass computing `sigma`: for every type, the sum of the small digits of its live columns.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

/-- The sum defining `sigma`, over the columns below `k`. -/
def sgP (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) : ℕ :=
  ∑ c ∈ range k, if tyOf n c = some t ∧ d c < Kn n then d c else 0

theorem sgP_N (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sgP n d t (nN n) = sigma n d t := rfl

theorem sgP_succ (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) :
    sgP n d t (k + 1) = sgP n d t k + if tyOf n k = some t ∧ d k < Kn n then d k else 0 := by
  unfold sgP; rw [Finset.sum_range_succ]

theorem sgP_ge_V (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) (hk : nV n ≤ k) :
    sgP n d t k = sgP n d t (nV n) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [sgP_succ, ih, if_neg, add_zero]
    rintro ⟨h, -⟩
    rw [tyOf_of_ge_V hk] at h; simp at h

theorem sigma_eq_sgP_V (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sigma n d t = sgP n d t (nV n) := by
  rw [← sgP_N]; exact sgP_ge_V n d t _ (by unfold nN; omega)

theorem sgP_step {n : ℕ} {d : ℕ → ℕ} {t k : ℕ} (hk : k < nV n) :
    sgP n d t (k + 1) = sgP n d t k + if (kindOf n d k = 3 ∧ k / nZ n = t) then d k else 0 := by
  rw [sgP_succ]
  congr 1
  have : (tyOf n k = some t ∧ d k < Kn n) ↔ (kindOf n d k = 3 ∧ k / nZ n = t) := by
    rw [kindOf_eq_three, tyOf_eq_some_iff, isLive_iff_of_lt_V hk]
    constructor
    · rintro ⟨⟨hl, ht⟩, hd⟩; exact ⟨⟨hl, hd⟩, ht.symm⟩
    · rintro ⟨⟨hl, hd⟩, ht⟩; exact ⟨⟨hl, ht.symm⟩, hd⟩
  simp only [this]

theorem sgP_le (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) : sgP n d t k ≤ k * Kn n := by
  induction k with
  | zero => simp [sgP]
  | succ k ih =>
    rw [sgP_succ]
    have : (if tyOf n k = some t ∧ d k < Kn n then d k else 0) ≤ Kn n := by
      split_ifs with h
      · exact h.2.le
      · omega
    nlinarith

/-- What one turn of the pass does to `sg`. -/
theorem sgBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nV n ∧ (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n)
      sgBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "sg" = if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then
          (σ.arrs "sg").set (σ.vars "i" / σ.vars "Z")
            ((σ.arrs "sg").getD (σ.vars "i" / σ.vars "Z") 0 + (σ.arrs "dg").getD (σ.vars "i") 0)
          else σ.arrs "sg") 40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nV n := ‹σ.vars "i" < nV n›
    have hsgb : ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n :=
      ‹∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n›
    have hVN := nV_le_nN'' n
    obtain ⟨hdgv, hldg, hq⟩ := colFacts hv hC (by omega)
    have hq' := hq hi
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hlkd : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hVv : σ.vars "V" = nV n := hC.1.hV
    have hZv : σ.vars "Z" = nZ n := hC.1.hZ
    have hNv : σ.vars "N" = nN n := hC.1.hN
    have hBN := hb.nN_lt
    have hB5 := hb.five_lt_B
    have hBV := hb.nV_lt
    have hBZ := hb.nZ_lt
    have hBK := hb.NK_lt
    have hBT := hb.nT_lt
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 :=
      ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hsg1 := hsgb (σ.vars "i" / σ.vars "Z")
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; simp_all))

theorem kindOf_le_three (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : kindOf n d c ≤ 3 := by
  unfold kindOf; split_ifs <;> omega

theorem arrOf_getD_le {T : ℕ} {f : ℕ → ℕ} {b : ℕ} (h : ∀ t < T, f t ≤ b) (t : ℕ) :
    (arrOf T f).getD t 0 ≤ b := by
  by_cases ht : t < T
  · rw [getD_arrOf_lt ht]; exact h t ht
  · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

/-- **The pass computing `sigma`.** -/
theorem sgCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "sg" = arrOf (nT n) (fun _ => 0))
      sgCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "sg" = arrOf (nT n) (sigma n (dd n v)))
      ((40 + 4) * nV n + 6) := by
  have hs := scan_spec (B := B) "i" "V" (nV n) 40 sgBody
    (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
    (fun k σ => σ.arrs "sg" = arrOf (nT n) (fun t => sgP n (dd n v) t k))
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) (by decide)))
    hb.nV_lt (fun σ h => h.1.1.hV) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hkd, hsg⟩
      refine ⟨⟨hC.setVar (by decide) _, by simpa using hkd⟩, ?_⟩
      simpa [sgP] using hsg
    · rintro σ σ' - ⟨⟨hC, -⟩, hsg, -⟩
      refine ⟨hC, ?_⟩
      rw [hsg]
      exact arrOf_congr fun t _ => (sigma_eq_sgP_V n _ t).symm
  · intro k hk σ ⟨⟨hC, hkd⟩, hik, hsg⟩
    have hkN : k < nN n := lt_of_lt_of_le hk (nV_le_nN'' n)
    have hkd' : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd, hik]; exact getD_arrOf_lt hkN
    have hsgb : ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n := by
      intro t
      rw [hsg]
      refine arrOf_getD_le (fun t _ => ?_) t
      calc sgP n (dd n v) t k ≤ k * Kn n := sgP_le _ _ _ _
        _ ≤ nN n * Kn n := Nat.mul_le_mul_right _ hkN.le
    obtain ⟨σ', hr, h1, h2⟩ := sgBody_vals hb v hv σ
      ⟨hC, by omega, by rw [hkd']; exact kindOf_le_three _ _ _, hsgb⟩
    refine ⟨σ', hr, by omega, ?_⟩
    have hZ := hC.1.hZ
    have hlt : k / nZ n < nT n := by
      apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact hk
    have hDk : k < Dn n := lt_of_lt_of_le hkN (by unfold Dn; omega)
    have hdgk : (σ.arrs "dg").getD (σ.vars "i") 0 = dd n v k := by
      rw [hC.2, hik, getD_arrOf_lt hDk, dd_lt hkN]
    rw [h2, hkd', hdgk, hik, hZ, hsg, getD_arrOf_lt hlt]
    by_cases h3 : kindOf n (dd n v) k = 3
    · rw [if_pos h3, set_arrOf]
      refine arrOf_congr fun t _ => ?_
      rw [sgP_step hk]
      by_cases ht : t = k / nZ n
      · subst ht; simp [h3]
      · have : ¬ (kindOf n (dd n v) k = 3 ∧ k / nZ n = t) := fun h => ht h.2.symm
        simp [ht, this]
    · rw [if_neg h3]
      refine arrOf_congr fun t _ => ?_
      rw [sgP_step hk, if_neg (fun h => h3 h.1)]; simp

end Lax117284Proofs.Machine.Ilp
