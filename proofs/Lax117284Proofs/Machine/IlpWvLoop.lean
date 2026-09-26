import Lax117284Proofs.Machine.IlpWv

/-!
The pass of the values of the extras: the loop.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- **One turn of the pass of the values.** -/
theorem wvBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C3 n cnt bb v σ)
    (hik : σ.vars "i" = k) :
    ∃ σ', Run B wvBody σ σ' (30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "wv" = (σ.arrs "wv").set k (wvF n cnt bb (certVec n v) k) := by
  obtain ⟨hCE, hkd, hrk, hS, hdl⟩ := hC
  have hBN := hb.nN_lt
  have hrkk : (σ.arrs "rkA").getD (σ.vars "i") 0 = rk n (dd n v) k := by
    rw [hrk, hik]; exact getD_arrOf_lt hk
  have hkdk : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd, hik]; exact getD_arrOf_lt hk
  have hrkle : rk n (dd n v) k ≤ nN n := (rk_le_self n _ k).trans hk.le
  obtain ⟨σ1, r1, e1⟩ := rAssign_vals hb v σ ⟨hCE, by omega, by rw [hrkk]; exact hrkle⟩
  obtain ⟨r', hr'⟩ : ∃ r', r' = rk n (dd n v) k * (if rk n (dd n v) k < n then 1 else 0) := ⟨_, rfl⟩
  have hr'n : r' < n := by
    rw [hr']
    by_cases h : rk n (dd n v) k < n
    · rw [if_pos h, mul_one]; exact h
    · rw [if_neg h, mul_zero]; exact hb.n1
  have hσ1r : σ1.vars "r" = r' := by
    rw [e1, hr', hrkk]; simp [Env.setVar]
  have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
  have hS1 : σ1.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) := by rw [e1]; simpa using hS
  have hSf : ∀ j < n, Sj n cnt (dd n v) j ≤ nN n * (Kn n + vb) := fun j _ =>
    Sj_le_Sb hb.hcnt _ j
  obtain ⟨σ2, r2, ⟨hCE2, hr2, hS2, hP2, hQ2⟩, hfv, hfa, -, -⟩ :=
    (pqCom_spec hb v hv (fun j => Sj n cnt (dd n v) j) hSf r' hr'n).frame σ1 ⟨hCE1, hσ1r, hS1⟩
  have hi2 : σ2.vars "i" = k := by rw [hfv "i" (by decide), ← hik, e1]; simp [Env.setVar]
  have hdl2 : σ2.vars "dl" = v (dlIdx n) := by rw [hfv "dl" (by decide), e1]; simpa [Env.setVar] using hdl
  have hkd2 : σ2.arrs "kd" = σ.arrs "kd" := by rw [hfa "kd" (by decide), e1]; rfl
  have hrk2 : σ2.arrs "rkA" = σ.arrs "rkA" := by rw [hfa "rkA" (by decide), e1]; rfl
  have hhb : bb ≤ vb := hb.hbb
  have hPQ := pSum_le hhb v hv (fun j => Sj n cnt (dd n v) j) hSf r' hr'n n le_rfl
  have hPbd : n * Pterm n vb = Pbd n vb := rfl
  have hdlK : v (dlIdx n) ≤ Kn n := hv _ (dlIdx_lt n)
  have hkd3 : (σ2.arrs "kd").getD k 0 = kindOf n (dd n v) k := by
    rw [hkd2, hkd]; exact getD_arrOf_lt hk
  have hrk3 : (σ2.arrs "rkA").getD k 0 = rk n (dd n v) k := by
    rw [hrk2, hrk]; exact getD_arrOf_lt hk
  obtain ⟨σ3, r3, e3⟩ := wvStore_vals hb v σ2
    ⟨hCE2, by omega, by rw [hi2, hkd3]; exact kindOf_le_three _ _ _, by rw [hi2, hrk3]; exact hrkle,
      by rw [hP2]; have := hPQ.1; omega, by rw [hQ2]; have := hPQ.2; omega,
      by rw [hdl2]; exact hdlK⟩
  have hi3 : σ3.vars "i" = k := by rw [e3]; simpa [Env.setArr] using hi2
  obtain ⟨σ4, r4, e4⟩ := bump_spec (B := B) "i" hb.one_lt_B σ3 (by
    show σ3.vars "i" + 1 < B; rw [hi3]; omega)
  have hwv2 : σ2.arrs "wv" = σ.arrs "wv" := by rw [hfa "wv" (by decide), e1]; rfl
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, ?_⟩
  · rw [e4]; simp [Env.setVar, hi3]
  · rw [e4]
    show σ3.arrs "wv" = _
    rw [e3]
    simp only [Env.setArr, if_true]
    rw [hi2, hwv2, hkd3, hrk3, hP2, hQ2, hdl2, pSum_eq_Pi n cnt bb v r' hr'n, qSum_eq_Qi n cnt bb v r' hr'n, hr']
    rw [wvF_step]

/-- **The pass of the values of the extras.** -/
theorem wvCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ ∃ f, σ.arrs "wv" = arrOf (nN n) f)
      wvCom
      (fun _ σ' => C3 n cnt bb v σ' ∧ σ'.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v)))
      (20 + (((30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) + 4) * nN n + 6)) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) wvBody
    (C3 n cnt bb v)
    (fun k σ => ∃ f, σ.arrs "wv" = arrOf (nN n) f ∧ ∀ c < k, f c = wvF n cnt bb (certVec n v) c)
    (C3.stable (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ ∃ f, σ.arrs "wv" = arrOf (nN n) f)
        (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn")))))
        (fun σ σ' => σ' = σ.setVar "dl" (v (dlIdx n))) 20 :=
      Spec.pre (dlAssign_vals hb v hv) (fun σ h => h.1)
    refine Spec.mono (Spec.seq hA hs ?_ ?_) le_rfl
    · intro σ σ1 hσ e
      rw [e]
      obtain ⟨hC, hkd, hrk, hS, f, hf⟩ := hσ
      refine ⟨⟨(hC.setVar (by decide) _).setVar (by decide) _, by simpa using hkd, by simpa using hrk,
        by simpa using hS, by simp⟩, ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩⟩
    · intro σ σ1 σ2 hσ e hpost
      obtain ⟨hC, ⟨f, hf, hfk⟩, -⟩ := hpost
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, f, hf, hfk⟩
    obtain ⟨σ', hr, h1, h2⟩ := wvBody_step hb v hv k hk σ hC hik
    refine ⟨σ', hr, h1, ⟨fun j => if j = k then wvF n cnt bb (certVec n v) k else f j, ?_, ?_⟩⟩
    · rw [h2, hf, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)

end

end Lax117284Proofs.Machine.Ilp
