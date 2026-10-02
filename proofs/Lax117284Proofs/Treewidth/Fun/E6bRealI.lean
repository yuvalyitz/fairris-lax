import Lax117284Proofs.Treewidth.Fun.E6bNum

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (7): `realIntro` on the trees built by `extract`

`realIntro_at`: the F-function `E5R.fRealIntro` computes `realIntro (k+1) v N Bs t0 target` within `Zc^pRI` steps, where
`t0` is a real decomposition returned by the extraction of the child (`PTD adj c k t0`), `Bs = c.bag`.

What is used from the math layer: `PTD adj c k t0` (so `t0.char Bs` is a well-formed characteristic, `char_wf`),
`tables_wf` (the target is well formed), the P1 bounds (`Wf.vsz_le`, `introPlans_length_le`, `introPlans_vsz_le`), the
plan-size and entry bounds of `E6bMath2`, and `ir_aux` (goodness of the un-normalised results, hence of their `norm`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5R

/-- `10 U + 600` and the polynomial part of `cIP` are bounded by `2 · introCCost` -/
theorem cIP_le (Bs : Finset ℕ) (kmax U c : ℕ) (hb : Bs.card ≤ U) (hk : kmax + 1 ≤ U + 1) (hc : c ≤ U) :
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1)) * (3 * c - 1) + (10 * U + 600) ≤
    2 * E3C.introCCost (U + 1) (Bs.card + kmax + 2) := by
  have hX1 : 1 ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hW1 : 1 ≤ U + 1 := by omega
  have hGX := E3C.Gp_le Bs.card kmax
  have hΩX : 2 ^ Bs.card + 1 ≤ 2 * 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := by
    have h1 : 2 ^ Bs.card ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) (by
      have : Bs.card ≤ (Bs.card + kmax + 2) ^ 3 := by
        have : Bs.card ≤ Bs.card + kmax + 2 := by omega
        calc Bs.card ≤ Bs.card + kmax + 2 := this
          _ = (Bs.card + kmax + 2) ^ 1 := (pow_one _).symm
          _ ≤ (Bs.card + kmax + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega)
    omega
  obtain ⟨hMW, hSnW⟩ := E3C.Sn_le Bs.card kmax (U + 1) (by omega) (by omega)
  have hcost := E3C.final_arith (U + 1) (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) (runBound Bs.card) (E3C.Gp Bs.card kmax)
    (2 ^ Bs.card + 1) ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) c
    hW1 hX1 hGX hΩX hMW hSnW (by omega)
  have e : E3C.introCCost (U + 1) (Bs.card + kmax + 2) =
      10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
    unfold E3C.introCCost
    rw [← pow_mul, show 64 * (Bs.card + kmax + 2) ^ 3 * 2 = 128 * (Bs.card + kmax + 2) ^ 3 by ring]
  have h10 : 10 * U + 600 ≤ E3C.introCCost (U + 1) (Bs.card + kmax + 2) := by
    rw [e]
    have h1 : 1 ≤ (U + 1) ^ 15 := Nat.one_le_pow _ _ hW1
    have h2 : U + 1 ≤ (U + 1) ^ 15 := by
      calc U + 1 = (U + 1) ^ 1 := (pow_one _).symm
        _ ≤ (U + 1) ^ 15 := Nat.pow_le_pow_right hW1 (by norm_num)
    have h3 : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
    have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
        10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
    rw [h5]; omega
  rw [e] at h10 ⊢
  omega

/-! ### numerical facts about `k` -/

theorem sq_le_Yk (k : ℕ) : (k + 2) ^ 2 ≤ Yk k := by
  unfold Yk
  exact Nat.pow_le_pow_right (by omega) (by norm_num)

theorem wf_sz_le {Bs : Finset ℕ} {k : ℕ} {t : CT} (hb : Bs.card ≤ k + 2) (h : t.Wf Bs (k + 1)) :
    sz t ≤ 128 * (k + 2) ^ 3 := by
  have h1 := Lax117284Proofs.Treewidth.Fun.CT.Wf.sz_le h
  refine le_trans h1 (le_trans ?_ (runBound_mul_le k))
  have h2 : runBound Bs.card ≤ runBound (k + 2) := by
    unfold runBound; exact Nat.mul_le_mul (by omega) (by omega)
  exact Nat.mul_le_mul h2 (by omega)

theorem plan_sz_num (M k b : ℕ) (hb : b ≤ k + 2) :
    2 * runBound b + planSzBound (runBound b) b +
      (2 * runBound b + b + 4) * (2 * b + 4 * (k + 1) + 10) + 2 ≤ sI M k := by
  unfold sI Yk planSzBound runBound
  have h1 : (2 * b + 2) * (2 * b + 2) ≤ (2 * k + 6) * (2 * k + 6) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (b + 1) * (2 * b + 2) ≤ (k + 3) * (2 * k + 6) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (2 * (2 * b + 2) * (2 * b + 2) + b + 4) * (2 * b + 4 * (k + 1) + 10) ≤
      (2 * (2 * k + 6) * (2 * k + 6) + (k + 2) + 4) * (2 * (k + 2) + 4 * (k + 1) + 10) := by
    apply Nat.mul_le_mul <;> nlinarith
  have hM : 1 ≤ M + 1 := by omega
  have h4 : 16000 * (k + 2) ^ 3 ≤ 16000 * (k + 2) ^ 3 * (M + 1) := Nat.le_mul_of_pos_right _ hM
  have h5 : (2 * (2 * b + 2) * (2 * b + 2) + b + 4) * (2 * b + 4 * (k + 1) + 10) =
      (2 * ((2 * b + 2) * (2 * b + 2)) + b + 4) * (2 * b + 4 * (k + 1) + 10) := by ring
  nlinarith [Nat.zero_le k, sq_nonneg k, pow_pos (show 0 < k + 2 by omega) 3]

theorem t0_sz_num (M k cs : ℕ) (hc : cs ≤ M) : (2 * k + 8) * (2 * k + 6) * cs ≤ sI M k := by
  unfold sI Yk
  have h1 : (2 * k + 8) * (2 * k + 6) * cs ≤ (2 * k + 8) * (2 * k + 6) * (M + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (2 * k + 8) * (2 * k + 6) ≤ 16000 * (k + 2) ^ 3 := by
    nlinarith [Nat.zero_le k, sq_nonneg k, pow_pos (show 0 < k + 2 by omega) 3]
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

theorem tg_sz_num (M k : ℕ) : 128 * (k + 2) ^ 3 ≤ sI M k := by
  unfold sI Yk
  have : 1 ≤ M + 1 := by omega
  nlinarith [pow_pos (show 0 < k + 2 by omega) 3]

theorem bag_sz_num (M k : ℕ) : 2 * (k + 2) + 1 ≤ sI M k := by
  unfold sI Yk
  have : 1 ≤ M + 1 := by omega
  nlinarith [pow_pos (show 0 < k + 2 by omega) 3, sq_nonneg k]

theorem introCCost_mono {W s s' : ℕ} (h : s ≤ s') : E3C.introCCost W s ≤ E3C.introCCost W s' := by
  unfold E3C.introCCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)))

theorem intro_len_num (k b : ℕ) (hb : b ≤ k + 2) : 64 * (b + (k + 1) + 2) ^ 3 ≤ 1728 * Yk k := by
  unfold Yk
  have h1 : b + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (b + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 64 * (b + (k + 1) + 2) ^ 3 ≤ 64 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 1728 * (k + 2) ^ 3 := by ring

/-! ### the `ExtIP` instance -/

/-- the instance of `E5.ExtIP` for characteristics over `Bs` with entries `≤ kmax` and naturals `≤ U` -/
def ipInst {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U : ℕ) : E5.ExtIP Δ' :=
  E5Inst.extIP_e3 U (1000 * (U + 1) * (U + 1)) (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card))
    (E3C.Gp Bs.card kmax) (2 ^ Bs.card + 1) (1000 * ((U + 1) * (2 ^ Bs.card + 1)))
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1))
    Bs kmax (runBound Bs.card) le_rfl le_rfl le_rfl le_rfl
    (fun v N ν hg hm hc => E3C.hG_of_good Bs kmax v N ν (runBound Bs.card) rfl hg hm hc)
    (fun N ν hg => E3C.hΩ_of_good Bs N ν hg) hΔ

theorem ipInst_ip {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U : ℕ) :
    (ipInst hΔ Bs kmax U).ip = E3C.fIntroPlans := rfl

theorem ipInst_PIP {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U v : ℕ) (N : Finset ℕ) (t : CT) :
    (ipInst hΔ Bs kmax U).PIP v N t ↔ (v ≤ U ∧ N.card ≤ U ∧ sz t ≤ U ∧ mx t ≤ U ∧ Good Bs t ∧ maxEntry t ≤ kmax ∧
      count t ≤ runBound Bs.card) := Iff.rfl

theorem ipInst_cIP {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') (Bs : Finset ℕ) (kmax U v : ℕ) (N : Finset ℕ) (t : CT) :
    (ipInst hΔ Bs kmax U).cIP v N t =
      (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * E3C.Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * E3C.Gp Bs.card kmax) +
      500 * ((U + 1) * E3C.Gp Bs.card kmax) + 1000 * (U + 1)) * (3 * count t - 1) + (10 * U + 600) := rfl

/-! ### the main statement -/

theorem realIntro_at {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ) {adj : Adj} {k M v : ℕ} {c : NT}
    (hg : (NT.intro v c).Good adj) (hw : (NT.intro v c).toRT.Width (k + 1))
    {t0 : RT} (hpt : PTD adj c k t0) {target : CT} (htg : target ∈ tables adj k (NT.intro v c))
    (hsz : sz t0 ≤ (2 * k + 8) * (2 * k + 6) * c.size) (hcM : c.size ≤ M) (hvM : v ≤ M)
    (hbagM : ∀ u ∈ c.bag, u ≤ M) (hB : (Zc M k ^ pRI + 2) ^ 2 < B) :
    Runs Δ' B E5R.fRealIntro [Val.nat E3C.fIntroPlans, toVal (k + 1), toVal v, toVal (nbrs adj v c.bag),
      toVal c.bag, toVal t0, toVal target]
      (toVal (realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 target)) (Zc M k ^ pRI) := by
  have hg0 := hg
  obtain ⟨hvB, -, -, hgc⟩ := hg
  have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
  have hb : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
  have hcov : c.bag ⊆ t0.verts := by
    rw [hpt.1.verts_eq]; intro x hx; exact NT.bag_subset_under c hx
  have hwf : (t0.char c.bag).Wf c.bag (k + 1) := char_wf hpt.1.conn hcov hpt.2
  have hwt : target.Wf (insert v c.bag) (k + 1) := tables_wf hg0 target htg
  have hU1 : ∀ u ∈ c.bag, u ≤ UI M k := fun u hu => le_trans (hbagM u hu) (by unfold UI; omega)
  have hNcard : (nbrs adj v c.bag).card ≤ k + 2 :=
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hb
  have hsz' : sz (t0.char c.bag) ≤ 128 * (k + 2) ^ 3 := wf_sz_le hb hwf
  have hcnt : count (t0.char c.bag) ≤ runBound c.bag.card := hwf.count_le
  have hY := Yk_ge k
  have hUY : 128 * (k + 2) ^ 3 ≤ UI M k := by unfold UI Yk; omega
  have hmx : mx (t0.char c.bag) ≤ UI M k := mx_ct_le_of_wf hwf hU1 (by unfold UI; omega)
  have hΔ3 : E3C.Δ ⊑ Δ' := hΔ.e4.e3
  have hPIP : (ipInst hΔ3 c.bag (k + 1) (UI M k)).PIP v (nbrs adj v c.bag) (t0.char c.bag) := by
    rw [ipInst_PIP]
    refine ⟨by unfold UI; omega, by unfold UI; omega, le_trans hsz' hUY, hmx, hwf.good, hwf.bounded, hcnt⟩
  have hcip : (ipInst hΔ3 c.bag (k + 1) (UI M k)).cIP v (nbrs adj v c.bag) (t0.char c.bag) ≤
      2 * E3C.introCCost (UI M k + 1) (3 * (k + 2)) := by
    rw [ipInst_cIP]
    refine le_trans (cIP_le c.bag (k + 1) (UI M k) (count (t0.char c.bag)) ?_ ?_ ?_)
      (Nat.mul_le_mul_left _ (introCCost_mono ?_))
    · unfold UI; omega
    · unfold UI; omega
    · exact le_trans (count_le_sz _) (le_trans hsz' hUY)
    · omega
  have hLen : (introPlans v (nbrs adj v c.bag) (t0.char c.bag)).length ≤ LenI k := by
    refine le_trans (introPlans_length_le hwf) (Nat.pow_le_pow_right (by norm_num) ?_)
    exact intro_len_num k _ hb
  have hplans : ∀ r ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag), sz r ≤ sI M k := by
    intro r hr
    have hct : ∀ x ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag),
        sz x.2.2 ≤ (2 * runBound c.bag.card + c.bag.card + 4) * (2 * c.bag.card + 4 * (k + 1) + 10) := by
      intro x hx
      rw [sz_ct_eq]
      exact introPlans_vsz_le v _ hwf x hx
    have := introPlans_sz_le v (nbrs adj v c.bag) (b := c.bag.card) (t0.char c.bag) (LB.of_good hwf.good) hcnt hct r hr
    exact le_trans this (plan_sz_num M k _ hb)
  have hcardI : (insert v c.bag).card ≤ k + 3 := le_trans (Finset.card_insert_le _ _) (by omega)
  have hsI := bag_sz_num M k
  have hPD : ∀ r ∈ introPlans v (nbrs adj v c.bag) (t0.char c.bag),
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).PD (sI M k) (CT.norm r.2.2) target := by
    intro r hr
    obtain ⟨path, plan, r2⟩ := r
    have hIR := introPlans_toIR v (nbrs adj v c.bag) (t0.char c.bag) r2 ⟨path, plan, hr⟩
    obtain ⟨lr, cr, -, -, -⟩ := ir_aux v c.bag hvB (nbrs adj v c.bag) hIR (loc_of_good _ hwf.good) hwf.conn
      (by rw [hwf.verts_eq]; exact hvB)
    have hgood : Good (insert v c.bag) (CT.norm r2) := good_norm r2 lr cr
    have hme : maxEntry r2 ≤ k + 3 :=
      introPlans_me v (nbrs adj v c.bag) (b := c.bag.card) (K := k + 3) (by omega) (t0.char c.bag)
        (LB.of_good hwf.good) (by have := hwf.bounded; omega) (path, plan, r2) hr
    have hme' : maxEntry (CT.norm r2) ≤ k + 3 := le_trans (maxEntry_norm_le r2) hme
    refine ⟨?_, ?_⟩
    · exact (RB.of_good hgood hme').mono (by omega) (by unfold LrI; omega)
    · exact (RB.of_good hwt.good hwt.bounded).mono (by omega) (by unfold LrI; omega)
  have hBsum := numRI_B M k _ hcip
  have hBd : sz c.bag ≤ sI M k := by rw [sz_finset]; omega
  have ht : sz t0 ≤ sI M k := le_trans hsz (t0_sz_num M k _ hcM)
  have htg' : sz target ≤ sI M k := le_trans (tables_sz_le hg0 hw target htg) (tg_sz_num M k)
  have hB2 : 20000 + 20000 * (sI M k + 1) + (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cKey (6 * sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cNorm (5 * sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cNorm (sI M k) +
      (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1).cDom (sI M k) +
      (ipInst hΔ3 c.bag (k + 1) (UI M k)).cIP v (nbrs adj v c.bag) (t0.char c.bag) < B := by
    have : Zc M k ^ pRI < B := by nlinarith [Nat.zero_le (Zc M k ^ pRI)]
    exact lt_of_le_of_lt hBsum this
  have h := E5R.realIntro_runs (Ext.trans E5W.extR hΔ.e5) B (E5Inst.ext5_e2 (LrI k) hΔ.e4.e2 hΔ.e4.e1)
    (ipInst hΔ3 c.bag (k + 1) (UI M k)) (k + 1) v (nbrs adj v c.bag) c.bag t0 target (sI M k) (LenI k)
    hBd ht htg' hPIP hLen hplans hPD hB2
  rw [ipInst_ip] at h
  exact h.mono (numRI_cost M k _ hcip)

end E6b
end Lax117284Proofs.Treewidth.Fun
