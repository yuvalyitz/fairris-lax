import Lax117284Proofs.Machine.IlpEs

/-!
The candidate solution.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem xvStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧ (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧
        (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb ∧
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb ∧
        (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n ∧
        (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb)
      (.store "xv" (V "i")
        (.add
          (.add (.mul (eqF (.get "kd" (V "i")) (lit 3)) (.get "dg" (V "i")))
            (.mul (eqF (.get "kd" (V "i")) (lit 2)) (.get "wv" (V "i"))))
          (.mul (eqF (.get "kd" (V "i")) (lit 1))
            (.sub (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))
              (.get "es" (V "t"))))))
      (fun σ σ' => σ' = σ.setArr "xv" (σ.vars "i")
        ((if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then (σ.arrs "dg").getD (σ.vars "i") 0 else 0) +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then (σ.arrs "wv").getD (σ.vars "i") 0 else 0) +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then
            (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 -
              (σ.arrs "es").getD (σ.vars "t") 0 else 0))) 80 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hdgv : (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n := ‹(σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n›
    have hwv : (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb := ‹(σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb›
    have hzv : (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb :=
      ‹(σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb›
    have hsgv : (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n := ‹(σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n›
    have hes : (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb :=
      ‹(σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb›
    have hrb := hC.1.hrb
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hles : (σ.arrs "es").length = nT n := hC.1.les
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hldg : (σ.arrs "dg").length = Dn n := hC.1.ldg
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hlx : (σ.arrs "xv").length = nN n := hC.1.lxv
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBrb := hb.rb_lt
    have hBE := hb.Ebd_lt
    have hBK := hb.NK_lt
    have hBX := hb.XB_lt
    have hBP := hb.Pbd_lt
    have hidx : σ.vars "rb" + σ.vars "t" < zLen n := by
      have : nT n ≤ nM n := by unfold nM; omega
      unfold zLen; omega
    have g3 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have g2 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have g1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have p3 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "dg").getD (σ.vars "i") 0) g3
    have p2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "wv").getD (σ.vars "i") 0) g2
    have p1 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 -
        (σ.arrs "es").getD (σ.vars "t") 0) g1
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    have f3 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then 1 else 0 := by split_ifs <;> omega
    rw [f3, f2, f1]
    by_cases h3 : (σ.arrs "kd").getD (σ.vars "i") 0 = 3
    · have h2 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 2 := by omega
      have h1 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 1 := by omega
      simp [h3, h2, h1]
    · by_cases h2 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2
      · have h1 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 1 := by omega
        simp [h3, h2, h1]
      · by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 1
        · simp [h3, h2, h1]
        · simp [h3, h2, h1]

/-- The static context of the pass of the candidate. -/
def C5 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v)) ∧
    σ.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) ∧
    σ.arrs "es" = arrOf (nT n) (esF n cnt bb (certVec n v))

theorem C5.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hw : "wv" ∉ c.warrs) (hs : "sg" ∉ c.warrs) (he : "es" ∉ c.warrs) :
    Stable c (C5 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (Stable.and (stable_arr "wv" (fun l => l = arrOf (nN n) (wvF n cnt bb (certVec n v))) hw)
        (Stable.and (stable_arr "sg" (fun l => l = arrOf (nT n) (sigma n (dd n v))) hs)
          (stable_arr "es" (fun l => l = arrOf (nT n) (esF n cnt bb (certVec n v))) he))))

/-- **One turn of the pass of the candidate.** -/
theorem xvBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C5 n cnt bb v σ)
    (hik : σ.vars "i" = k) :
    ∃ σ', Run B xvBody σ σ' (30 + 80 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "xv" = (σ.arrs "xv").set k (xF n cnt bb (certVec n v) k) := by
  obtain ⟨hCE, hkd, hwv, hsg, hes⟩ := hC
  have hBN := hb.nN_lt
  obtain ⟨σ1, r1, e1⟩ := tAssign_vals hb v hv σ ⟨hCE, by omega⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = k / nZ n * (if k < nV n then 1 else 0) := ⟨_, rfl⟩
  have ht'T : t' < nT n := by
    rw [ht']
    by_cases h : k < nV n
    · rw [if_pos h, mul_one]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h
    · rw [if_neg h, mul_zero]; exact nT_pos n
  have hσ1t : σ1.vars "t" = t' := by rw [e1, ht']; simp only [Env.setVar, if_true, hik]
  have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
  have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
  have hkd1 : σ1.arrs "kd" = σ.arrs "kd" := by rw [e1]; rfl
  have hwv1 : σ1.arrs "wv" = σ.arrs "wv" := by rw [e1]; rfl
  have hsg1 : σ1.arrs "sg" = σ.arrs "sg" := by rw [e1]; rfl
  have hes1 : σ1.arrs "es" = σ.arrs "es" := by rw [e1]; rfl
  have hxv1 : σ1.arrs "xv" = σ.arrs "xv" := by rw [e1]; rfl
  have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd1, hkd, hi1]; exact getD_arrOf_lt hk
  have hDk : k < Dn n := lt_of_lt_of_le hk (by unfold Dn; omega)
  have hdgk : (σ1.arrs "dg").getD (σ1.vars "i") 0 = v k := by
    rw [hCE1.2, hi1, getD_arrOf_lt hDk]
  have hwvk : (σ1.arrs "wv").getD (σ1.vars "i") 0 = wvF n cnt bb (certVec n v) k := by
    rw [hwv1, hwv, hi1]; exact getD_arrOf_lt hk
  have hzt : (σ1.arrs "z").getD (σ1.vars "rb" + σ1.vars "t") 0 = cnt t' := by
    rw [hCE1.1.hz, hCE1.1.hrb, hσ1t, ilpWord_rhs n cnt bb (by unfold nM; omega)]
    unfold rhs; rw [if_pos ht'T]
  have hsgt : (σ1.arrs "sg").getD (σ1.vars "t") 0 = sigma n (dd n v) t' := by
    rw [hsg1, hsg, hσ1t]; exact getD_arrOf_lt ht'T
  have hest : (σ1.arrs "es").getD (σ1.vars "t") 0 = esF n cnt bb (certVec n v) t' := by
    rw [hes1, hes, hσ1t]; exact getD_arrOf_lt ht'T
  have hesle : esF n cnt bb (certVec n v) t' ≤ nN n * Pbd n vb := by
    rw [esF_eq_esP]; exact esP_le hb v hv t' (nN n)
  have hvk : v k ≤ Kn n := hv k hDk
  obtain ⟨σ2, r2, e2⟩ := xvStore_vals hb v σ1
    ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _, by rw [hdgk]; exact hvk,
      by rw [hwvk]; exact wvF_le hb v hv k, by rw [hzt]; exact hb.hcnt _ ht'T,
      by rw [hsgt]; exact sigma_le' _ _ _, by rw [hest]; exact hesle⟩
  obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by
    show σ2.vars "i" + 1 < B
    rw [e2]; simp [Env.setArr, hi1]; omega)
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
  · rw [e3, e2]; simp [Env.setVar, Env.setArr, hi1]
  · rw [e3]
    show σ2.arrs "xv" = _
    rw [e2]
    simp only [Env.setArr, if_true]
    rw [hkdk, hdgk, hwvk, hzt, hsgt, hest, hxv1, hi1]
    congr 1
    unfold xF
    have hkc := kindOf_le_three n (dd n v) k
    by_cases h3 : kindOf n (dd n v) k = 3
    · rw [if_pos h3]; simp [h3, dd_lt hk, dd]
    · by_cases h2 : kindOf n (dd n v) k = 2
      · rw [if_neg h3, if_pos h2]; simp [h3, h2]
      · by_cases h1 : kindOf n (dd n v) k = 1
        · rw [if_neg h3, if_neg h2, if_pos h1]
          have hbase := kindOf_eq_one.mp h1
          obtain ⟨e1', e2'⟩ := isBase_tyIdx hbase
          have hV := isBase_lt_V hbase
          have ht'' : t' = k / nZ n := by rw [ht', if_pos hV, mul_one]
          rw [e1', ← ht'']
          simp [h1, cp]
        · have h0 : kindOf n (dd n v) k = 0 := by omega
          rw [if_neg h3, if_neg h2, if_neg h1]
          simp [h3, h2, h1]

/-- **The pass of the candidate.** -/
theorem xvCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C5 n cnt bb v σ ∧ ∃ f, σ.arrs "xv" = arrOf (nN n) f)
      xvCom (fun _ σ' => C5 n cnt bb v σ' ∧ σ'.arrs "xv" = arrOf (nN n) (xF n cnt bb (certVec n v)))
      ((30 + 80 + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 80 + 4) xvBody (C5 n cnt bb v)
    (fun k σ => ∃ f, σ.arrs "xv" = arrOf (nN n) f ∧ ∀ c < k, f c = xF n cnt bb (certVec n v) c)
    (C5.stable (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, f, hf⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2.1,
        by simpa using hC.2.2.2.1, by simpa using hC.2.2.2.2⟩,
        ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩⟩
    · rintro σ σ' - ⟨hC, ⟨f, hf, hfk⟩, -⟩
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, f, hf, hfk⟩
    obtain ⟨σ', hr, h1, h2⟩ := xvBody_step hb v hv k hk σ hC hik
    refine ⟨σ', hr, h1, ⟨fun j => if j = k then xF n cnt bb (certVec n v) k else f j, ?_, ?_⟩⟩
    · rw [h2, hf, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)

end

end Lax117284Proofs.Machine.Ilp
