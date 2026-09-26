import Lax117284Proofs.Machine.IlpPq

/-!
The values of the extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem rAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n)
      (asg "r" (.mul (.get "rkA" (V "i")) (ltF (.get "rkA" (V "i")) (V "n"))))
      (fun σ σ' => σ' = σ.setVar "r" ((σ.arrs "rkA").getD (σ.vars "i") 0 *
        if (σ.arrs "rkA").getD (σ.vars "i") 0 < n then 1 else 0)) 30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hrk : (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n := ‹(σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n›
    have hlr : (σ.arrs "rkA").length = nN n := hC.1.lrk
    have hnv := hC.1.hn
    have hBN := hb.nN_lt
    have hBn := hb.n_lt
    have hB5 := hb.five_lt_B
    have hprod := mul_le_of_le_one' ((σ.arrs "rkA").getD (σ.vars "i") 0)
      (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hnv]
    by_cases h : (σ.arrs "rkA").getD (σ.vars "i") 0 < n
    · have e : 1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0)) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0)) = 0 := by omega
      rw [e, if_neg h]

theorem wvStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n ∧ σ.vars "P" ≤ Pbd n vb ∧ σ.vars "Q" ≤ Pbd n vb ∧
        σ.vars "dl" ≤ Kn n)
      (.store "wv" (V "i")
        (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (.get "rkA" (V "i")) (V "n")))
          (.div (.sub (V "P") (V "Q")) (V "dl"))))
      (fun σ σ' => σ' = σ.setArr "wv" (σ.vars "i")
        (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 ∧ (σ.arrs "rkA").getD (σ.vars "i") 0 < n then
          (σ.vars "P" - σ.vars "Q") / σ.vars "dl" else 0)) 40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hrk : (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n := ‹(σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n›
    have hPb : σ.vars "P" ≤ Pbd n vb := ‹σ.vars "P" ≤ Pbd n vb›
    have hQb : σ.vars "Q" ≤ Pbd n vb := ‹σ.vars "Q" ≤ Pbd n vb›
    have hdl : σ.vars "dl" ≤ Kn n := ‹σ.vars "dl" ≤ Kn n›
    have hBK := hb.Kn_lt
    have hlr : (σ.arrs "rkA").length = nN n := hC.1.lrk
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hnv := hC.1.hn
    have hBN := hb.nN_lt
    have hBn := hb.n_lt
    have hBP := hb.Pbd_lt
    have hB5 := hb.five_lt_B
    have hdiv : (σ.vars "P" - σ.vars "Q") / σ.vars "dl" ≤ σ.vars "P" - σ.vars "Q" := Nat.div_le_self _ _
    have hprod := mul_le_of_le_one_left'
      ((1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) *
        (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))))
      ((σ.vars "P" - σ.vars "Q") / σ.vars "dl") (by
        have h1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
        have h2 : (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) ≤ 1 := by omega
        calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
          _ = 1 := rfl)
    have hprod2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hnv]
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0))) =
        if (σ.arrs "rkA").getD (σ.vars "i") 0 < n then 1 else 0 := by split_ifs <;> omega
    rw [f1, f2]
    by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2 <;>
      by_cases h2 : (σ.arrs "rkA").getD (σ.vars "i") 0 < n <;>
      simp only [h1, h2, if_true, if_false, one_mul, mul_one, zero_mul, mul_zero, and_self, and_true,
        true_and, and_false, false_and]

theorem dlAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ)
      (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn")))))
      (fun σ σ' => σ' = σ.setVar "dl" (v (dlIdx n))) 20 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hN := hC.1.hN
    have hnn := hC.1.hnn
    have hDl := hC.1.ldg
    have hlt : dlIdx n < Dn n := dlIdx_lt n
    have hd : (σ.arrs "dg").getD (dlIdx n) 0 = v (dlIdx n) := by
      rw [hC.2]; exact getD_arrOf_lt hlt
    have hdv := hv _ hlt
    have hBK := hb.Kn_lt
    have hBD := hb.Dn_lt
    have hB5 := hb.five_lt_B
    have hidx : σ.vars "N" + 2 * σ.vars "nn" = dlIdx n := by unfold dlIdx; omega
    clear_runs
  all_goals (first | omega | (rw [hidx, hd]; done) | (rw [hidx, hd]; omega))

/-- The static context of the pass of the values. -/
def C3 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
    σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ σ.vars "dl" = v (dlIdx n)

theorem C3.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hr : "rkA" ∉ c.warrs) (hs : "S" ∉ c.warrs) (hdl : "dl" ∉ c.wvars) :
    Stable c (C3 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (Stable.and (stable_arr "rkA" (fun l => l = arrOf (nN n) (rk n (dd n v))) hr)
        (Stable.and (stable_arr "S" (fun l => l = arrOf n (fun j => Sj n cnt (dd n v) j)) hs)
          (stable_var "dl" (fun x => x = v (dlIdx n)) hdl))))

theorem Sj_le_Sb {n : ℕ} {cnt : ℕ → ℕ} {vb : ℕ} (hcnt : ∀ t < nT n, cnt t ≤ vb) (d : ℕ → ℕ) (j : ℕ) :
    Sj n cnt d j ≤ nN n * (Kn n + vb) := by
  rw [Sj_eq_s]
  have h1 := s1P_le n d j (nN n)
  have h2 := s2P_le hcnt d j (nN n) (cnt := cnt) (n := n)
  have h4 : nN n * (Kn n + vb) = nN n * Kn n + nN n * vb := by ring
  omega

theorem rk_le_self (n : ℕ) (d : ℕ → ℕ) (k : ℕ) : rk n d k ≤ k := by
  unfold rk
  calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := Finset.card_range k

theorem wvF_step {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {k : ℕ} :
    (if kindOf n (dd n v) k = 2 ∧ rk n (dd n v) k < n then
      (Pi n cnt bb (certVec n v) (rk n (dd n v) k * if rk n (dd n v) k < n then 1 else 0) -
        Qi n cnt bb (certVec n v) (rk n (dd n v) k * if rk n (dd n v) k < n then 1 else 0)) / v (dlIdx n)
     else 0) = wvF n cnt bb (certVec n v) k := by
  unfold wvF
  by_cases h : kindOf n (dd n v) k = 2 ∧ rk n (dd n v) k < n
  · have h' : isExtra n (certVec n v).d k ∧ rk n (certVec n v).d k < n :=
      ⟨kindOf_eq_two.mp h.1, h.2⟩
    rw [if_pos h, if_pos h', if_pos h.2, mul_one]
    unfold wcol
    rfl
  · have h' : ¬ (isExtra n (certVec n v).d k ∧ rk n (certVec n v).d k < n) :=
      fun h2 => h ⟨kindOf_eq_two.mpr h2.1, h2.2⟩
    rw [if_neg h, if_neg h']

end

end Lax117284Proofs.Machine.Ilp
