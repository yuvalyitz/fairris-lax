import Lax117284Proofs.Machine.IlpKd

/-!
The classification pass: the loop.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

/-- The static context of the decoding of the digits `v`. -/
def CE (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) v

theorem CE.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs) :
    Stable c (CE n cnt bb v) :=
  Stable.and (Ctx.stable hv hz) (stable_arr "dg" (fun l => l = arrOf (Dn n) v) hd)

theorem CE.setVar {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {σ : Env} (h : CE n cnt bb v σ)
    {y : String} (hy : y ∉ ctxVars) (x : ℕ) : CE n cnt bb v (σ.setVar y x) :=
  ⟨h.1.setVar hy x, h.2⟩

/-- The digits of the columns, as a function. -/
abbrev dd (n : ℕ) (v : ℕ → ℕ) : ℕ → ℕ := (certVec n v).d

theorem dd_lt {n : ℕ} {v : ℕ → ℕ} {c : ℕ} (hc : c < nN n) : dd n v c = v c := by
  simp [dd, certVec, hc]

theorem getD_arrOf_lt {n : ℕ} {f : ℕ → ℕ} {i : ℕ} (h : i < n) : (arrOf n f).getD i 0 = f i :=
  getD_arrOf f h

/-- **One turn of the classification computes the kind and the flags.** -/
theorem kdStep {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {σ : Env} {k : ℕ}
    (hctx : Ctx n cnt bb σ) (hdg : σ.arrs "dg" = arrOf (Dn n) v) (hk : k < nN n)
    (hi : σ.vars "i" = k) (hv : v k ≤ Kn n)
    (hl : σ.arrs "hl" = arrOf (nT n) (fun t => hlF n (dd n v) t k)) :
    kdVal σ = kindOf n (dd n v) k ∧
      hlNew σ = arrOf (nT n) (fun t => hlF n (dd n v) t (k + 1)) := by
  have hDk : k < Dn n := lt_of_lt_of_le hk (by unfold Dn; omega)
  have hddk : dd n v k = v k := dd_lt hk
  have hdgk : (σ.arrs "dg").getD k 0 = v k := by rw [hdg]; exact getD_arrOf_lt hDk
  have hN := hctx.hN
  have hV := hctx.hV
  have hZ := hctx.hZ
  have hK := hctx.hK
  have hlt : k < nV n → k / nZ n < nT n := by
    intro h
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact h
  have hzk : k < nV n → (σ.arrs "z").getD (2 + k / nZ n * nN n + k) 0 = coef n (k / nZ n) k := by
    intro h
    rw [hctx.hz]
    exact ilpWord_coef n cnt bb (by have := hlt h; unfold nM; omega) hk
  have hhl : k < nV n → (σ.arrs "hl").getD (k / nZ n) 0 = hlF n (dd n v) (k / nZ n) k := by
    intro h
    rw [hl]; exact getD_arrOf_lt (hlt h)
  have hkd := kindOf_step (n := n) (d := dd n v) hk (by rw [hddk]; exact hv)
  have hhs := fun t => hlF_step (n := n) (d := dd n v) (t := t) hk (by rw [hddk]; exact hv)
  rw [hddk] at hkd
  simp only [hddk] at hhs
  constructor
  · unfold kdVal
    rw [hkd, hi, hN, hV, hZ, hK]
    by_cases h1 : k < nV n
    · rw [if_pos h1, if_pos h1, hzk h1, hdgk, hhl h1]
    · rw [if_neg h1, if_neg h1, hdgk]
  · unfold hlNew
    rw [hi, hN, hV, hZ, hK]
    have hiff : (k < nV n ∧ (σ.arrs "z").getD (2 + k / nZ n * nN n + k) 0 = 1 ∧
        ¬ (σ.arrs "dg").getD k 0 < Kn n ∧ (σ.arrs "hl").getD (k / nZ n) 0 = 0) ↔
        (k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ hlF n (dd n v) (k / nZ n) k = 0) := by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, by rw [← hzk h1]; exact h2, by rw [← hdgk]; exact h3,
          by rw [← hhl h1]; exact h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, by rw [hzk h1]; exact h2, by rw [hdgk]; exact h3, by rw [hhl h1]; exact h4⟩
    by_cases hc : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧
        hlF n (dd n v) (k / nZ n) k = 0
    · rw [if_pos (hiff.mpr hc)]
      obtain ⟨h1, h2, h3, h4⟩ := hc
      rw [hl, set_arrOf]
      refine arrOf_congr fun t _ => ?_
      rw [hhs t]
      by_cases ht : t = k / nZ n
      · have hcond : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n :=
          ⟨h1, h2, h3, ht⟩
        rw [if_pos hcond, if_pos ht]
      · have hcond : ¬ (k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n) :=
          fun h => ht h.2.2.2
        rw [if_neg hcond, if_neg ht]
    · rw [if_neg (fun h => hc (hiff.mp h)), hl]
      refine arrOf_congr fun t _ => ?_
      rw [hhs t]
      by_cases hcc : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n
      · rw [if_pos hcc]
        obtain ⟨h1, h2, h3, h4⟩ := hcc
        have h5 : ¬ hlF n (dd n v) (k / nZ n) k = 0 := fun h => hc ⟨h1, h2, h3, h⟩
        have h6 := hlF_le_one (n := n) (d := dd n v) (k / nZ n) k
        rw [h4]; omega
      · rw [if_neg hcc]

theorem hlF_flags (n : ℕ) (d : ℕ → ℕ) (k : ℕ) (T : ℕ) :
    ∀ t, (arrOf T (fun t => hlF n d t k)).getD t 0 ≤ 1 := by
  intro t
  by_cases h : t < T
  · rw [getD_arrOf_lt h]; exact hlF_le_one _ _
  · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

/-- **The classification pass**: `kd` holds the kind of every column. -/
theorem kdCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ (∃ f, σ.arrs "kd" = arrOf (nN n) f) ∧
        σ.arrs "hl" = arrOf (nT n) (fun _ => 0))
      kdCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
      ((100 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) 100 kdBody (CE n cnt bb v)
    (fun k σ => (∃ f, σ.arrs "kd" = arrOf (nN n) f ∧ ∀ c < k, f c = kindOf n (dd n v) c) ∧
      σ.arrs "hl" = arrOf (nT n) (fun t => hlF n (dd n v) t k))
    (CE.stable (by decide) (by decide) (by decide)) hb.nN_lt (fun σ h => h.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, ⟨f, hf⟩, hh⟩
      refine ⟨hC.setVar (by decide) 0, ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩, ?_⟩
      simpa [hlF_zero] using hh
    · rintro σ σ' - ⟨hC, ⟨⟨f, hf, hfk⟩, -⟩, -⟩
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, ⟨f, hf, hfk⟩, hhl⟩
    have hflags : ∀ t, (σ.arrs "hl").getD t 0 ≤ 1 := by rw [hhl]; exact hlF_flags _ _ _ _
    obtain ⟨σ', hr, h1, h2, h3⟩ := kdBody_vals hb v hv σ ⟨hC.1, hC.2, by rw [hik]; exact hk, hflags⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    obtain ⟨e1, e2⟩ := kdStep hC.1 hC.2 hk hik hvk hhl
    refine ⟨σ', hr, by omega, ⟨fun j => if j = k then kindOf n (dd n v) k else f j, ?_, ?_⟩, ?_⟩
    · rw [h2, hf, hik, e1, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)
    · rw [h3, e2]

/-- Facts about the current column `i < N` of a state of a pass. -/
theorem colFacts {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} (hv : ∀ q < Dn n, v q ≤ Kn n)
    {σ : Env} (hC : CE n cnt bb v σ) (hi : σ.vars "i" < nN n) :
    (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧ (σ.arrs "dg").length = Dn n ∧
    (σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n) := by
  have hZv : σ.vars "Z" = nZ n := hC.1.hZ
  have hDN : nN n ≤ Dn n := by unfold Dn; omega
  refine ⟨?_, hC.1.ldg, ?_⟩
  · rw [hC.2, getD_arrOf_lt (by omega)]
    exact hv _ (by omega)
  · intro h
    rw [hZv]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h

end Lax117284Proofs.Machine.Ilp
