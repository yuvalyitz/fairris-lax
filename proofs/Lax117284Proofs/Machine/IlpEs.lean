import Lax117284Proofs.Machine.IlpWvLoop

/-!
The pass computing `extraSum`: for every type, the sum of the values of its extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The sum defining `esF`, over the columns below `k`. -/
def esP (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t k : ℕ) : ℕ :=
  ∑ c ∈ range k, if isExtra n ω.d c ∧ tyOf n c = some t then wvF n cnt bb ω c else 0

theorem esF_eq_esP (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t : ℕ) :
    esF n cnt bb ω t = esP n cnt bb ω t (nN n) := rfl

theorem esP_succ (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t k : ℕ) :
    esP n cnt bb ω t (k + 1) = esP n cnt bb ω t k +
      if isExtra n ω.d k ∧ tyOf n k = some t then wvF n cnt bb ω k else 0 := by
  unfold esP; rw [Finset.sum_range_succ]


theorem esP_step {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {ω : Cert} {t k : ℕ} :
    esP n cnt bb ω t (k + 1) = esP n cnt bb ω t k +
      if (isExtra n ω.d k ∧ k < nV n ∧ k / nZ n = t) then wvF n cnt bb ω k else 0 := by
  rw [esP_succ]
  congr 1
  have : (isExtra n ω.d k ∧ tyOf n k = some t) ↔ (isExtra n ω.d k ∧ k < nV n ∧ k / nZ n = t) := by
    constructor
    · rintro ⟨he, ht⟩
      obtain ⟨hl, ht'⟩ := tyOf_eq_some_iff.mp ht
      exact ⟨he, hl.1, ht'.symm⟩
    · rintro ⟨he, hV, ht⟩
      have hlive := ((mem_Lset_iff n ω.d k).mp he.1).1
      have hlv : liveP n k := (isLive_iff_of_lt_V hV).mp hlive
      exact ⟨he, tyOf_eq_some_iff.mpr ⟨hlv, ht.symm⟩⟩
  simp only [this]

/-- A value of an extra is at most `Pbd`. -/
theorem wvF_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (c : ℕ) : wvF n cnt bb (certVec n v) c ≤ Pbd n vb := by
  unfold wvF
  split_ifs with h
  · have hr := h.2
    have hSf : ∀ j < n, Sj n cnt (dd n v) j ≤ nN n * (Kn n + vb) := fun j _ =>
      Sj_le_Sb hb.hcnt _ j
    have hPQ := pSum_le (hb.hbb : bb ≤ vb) v hv (fun j => Sj n cnt (dd n v) j) hSf _ hr n le_rfl
    have := pSum_eq_Pi n cnt bb v (rk n (certVec n v).d c) hr
    unfold wcol
    calc _ ≤ _ := Nat.div_le_self _ _
      _ ≤ Pi n cnt bb (certVec n v) (rk n (certVec n v).d c) := Nat.sub_le _ _
      _ ≤ Pbd n vb := by rw [← this]; exact hPQ.1
  · exact Nat.zero_le _

theorem esP_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (t k : ℕ) :
    esP n cnt bb (certVec n v) t k ≤ k * Pbd n vb := by
  induction k with
  | zero => simp [esP]
  | succ k ih =>
    rw [esP_succ]
    have : (if isExtra n (certVec n v).d k ∧ tyOf n k = some t then wvF n cnt bb (certVec n v) k else 0)
        ≤ Pbd n vb := by
      split_ifs
      · exact wvF_le hb v hv k
      · omega
    nlinarith

theorem esStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧ (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb ∧
        (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb)
      (.store "es" (V "t")
        (.add (.get "es" (V "t"))
          (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (V "i") (V "V")))
            (.get "wv" (V "i")))))
      (fun σ σ' => σ' = σ.setArr "es" (σ.vars "t")
        ((σ.arrs "es").getD (σ.vars "t") 0 +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 ∧ σ.vars "i" < nV n then
            (σ.arrs "wv").getD (σ.vars "i") 0 else 0))) 50 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hwv : (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb := ‹(σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb›
    have hes : (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb :=
      ‹(σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb›
    have hles : (σ.arrs "es").length = nT n := hC.1.les
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hVv := hC.1.hV
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBV := hb.nV_lt
    have hBE := hb.Ebd_lt
    have hB5 := hb.five_lt_B
    have hprod1 := mul_le_of_le_one_left'
      ((1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) *
        (1 - (1 - (σ.vars "V" - σ.vars "i"))))
      ((σ.arrs "wv").getD (σ.vars "i") 0) (by
        have h1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
        have h2 : (1 - (1 - (σ.vars "V" - σ.vars "i"))) ≤ 1 := by omega
        calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
          _ = 1 := rfl)
    have hprod2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      (1 - (1 - (σ.vars "V" - σ.vars "i"))) (by omega)
    have hNP : nN n * Pbd n vb ≤ nN n * Pbd n vb := le_rfl
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hVv]
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - (1 - (nV n - σ.vars "i"))) = if σ.vars "i" < nV n then 1 else 0 := by
      split_ifs <;> omega
    rw [f1, f2]
    by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2 <;>
      by_cases h2 : σ.vars "i" < nV n <;>
      simp only [h1, h2, if_true, if_false, one_mul, mul_one, zero_mul, mul_zero, and_self, and_true,
        true_and, and_false, false_and]

/-- The static context of the pass of the sums of the extras. -/
def C4 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v))

theorem C4.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hw : "wv" ∉ c.warrs) : Stable c (C4 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (stable_arr "wv" (fun l => l = arrOf (nN n) (wvF n cnt bb (certVec n v))) hw))

/-- **One turn of the pass of the sums of the extras.** -/
theorem esBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C4 n cnt bb v σ)
    (hik : σ.vars "i" = k)
    (hes : σ.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t k)) :
    ∃ σ', Run B esBody σ σ' (30 + 50 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t (k + 1)) := by
  obtain ⟨hCE, hkd, hwv⟩ := hC
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
  have hes1 : σ1.arrs "es" = σ.arrs "es" := by rw [e1]; rfl
  have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd1, hkd, hi1]; exact getD_arrOf_lt hk
  have hwvk : (σ1.arrs "wv").getD (σ1.vars "i") 0 = wvF n cnt bb (certVec n v) k := by
    rw [hwv1, hwv, hi1]; exact getD_arrOf_lt hk
  have hesk : (σ1.arrs "es").getD (σ1.vars "t") 0 = esP n cnt bb (certVec n v) t' k := by
    rw [hes1, hes, hσ1t]; exact getD_arrOf_lt ht'T
  have hle := esP_le hb v hv t' k
  have hkN : k * Pbd n vb ≤ nN n * Pbd n vb := Nat.mul_le_mul_right _ hk.le
  obtain ⟨σ2, r2, e2⟩ := esStore_vals hb v σ1
    ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _,
      by rw [hwvk]; exact wvF_le hb v hv k, by rw [hesk]; omega⟩
  obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by
    show σ2.vars "i" + 1 < B
    rw [e2]; simp [Env.setArr, hi1]; omega)
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
  · rw [e3, e2]; simp [Env.setVar, Env.setArr, hi1]
  · rw [e3]
    show σ2.arrs "es" = _
    rw [e2]
    simp only [Env.setArr, if_true]
    rw [hesk, hkdk, hwvk, hes1, hes, hσ1t, hi1, set_arrOf]
    refine arrOf_congr fun t _ => ?_
    rw [esP_step]
    by_cases htt : t = t'
    · subst htt
      rw [if_pos rfl]
      congr 1
      refine if_congr ?_ rfl rfl
      rw [show (kindOf n (dd n v) k = 2) ↔ isExtra n (certVec n v).d k from kindOf_eq_two]
      constructor
      · rintro ⟨he, hV⟩
        refine ⟨he, hV, ?_⟩
        rw [ht', if_pos hV, mul_one]
      · rintro ⟨he, hV, -⟩
        exact ⟨he, hV⟩
    · rw [if_neg htt]
      have : ¬ (isExtra n (certVec n v).d k ∧ k < nV n ∧ k / nZ n = t) := by
        rintro ⟨-, hV, ht⟩
        apply htt
        rw [ht', if_pos hV, mul_one, ht]
      rw [if_neg this, add_zero]

/-- **The pass of the sums of the extras.** -/
theorem esCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C4 n cnt bb v σ ∧ σ.arrs "es" = arrOf (nT n) (fun _ => 0))
      esCom (fun _ σ' => C4 n cnt bb v σ' ∧ σ'.arrs "es" = arrOf (nT n) (esF n cnt bb (certVec n v)))
      ((30 + 50 + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 50 + 4) esBody (C4 n cnt bb v)
    (fun k σ => σ.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t k))
    (C4.stable (by decide) (by decide) (by decide) (by decide) (by decide)) hb.nN_lt
    (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hes⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2⟩, ?_⟩
      simpa [esP] using hes
    · rintro σ σ' - ⟨hC, hes, -⟩
      exact ⟨hC, hes⟩
  · intro k hk σ ⟨hC, hik, hes⟩
    obtain ⟨σ', hr, h1, h2⟩ := esBody_step hb v hv k hk σ hC hik hes
    exact ⟨σ', hr, h1, h2⟩

end

end Lax117284Proofs.Machine.Ilp
