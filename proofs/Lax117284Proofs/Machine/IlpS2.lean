import Lax117284Proofs.Machine.IlpS1

/-!
The second pass over `Sj`: what is left of the demand of the type of each base.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The base part of `Sj`, over the columns below `k`. -/
def s2P (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j k : ℕ) : ℕ :=
  ∑ c ∈ range k, if isBase n d c then cp n cnt d (tyIdx n c) * coef n (nT n + j) c else 0

theorem s2P_succ (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j k : ℕ) :
    s2P n cnt d j (k + 1) = s2P n cnt d j k +
      (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * coef n (nT n + j) k := by
  unfold s2P
  rw [Finset.sum_range_succ]
  by_cases h : isBase n d k <;> simp [h]

theorem Sj_eq_s (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j : ℕ) :
    Sj n cnt d j = s1P n d j (nN n) + s2P n cnt d j (nN n) := rfl

theorem isBase_lt_V {n : ℕ} {d : ℕ → ℕ} {c : ℕ} (h : isBase n d c) : c < nV n := by
  obtain ⟨-, hτ, -⟩ := h
  by_contra hc
  exact hτ (tyOf_of_ge_V (by omega))

theorem isBase_tyIdx {n : ℕ} {d : ℕ → ℕ} {c : ℕ} (h : isBase n d c) :
    tyIdx n c = c / nZ n ∧ c / nZ n < nT n := by
  have hV := isBase_lt_V h
  have hτ := h.2.1
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hτ
  have := tyOf_eq_some_iff.mp ht
  have hlt : c / nZ n < nT n := by
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact hV
  refine ⟨?_, hlt⟩
  unfold tyIdx; rw [ht]; simp [this.2]

theorem s2P_le {n : ℕ} {cnt : ℕ → ℕ} {vb : ℕ} (hcnt : ∀ t < nT n, cnt t ≤ vb) (d : ℕ → ℕ)
    (j k : ℕ) : s2P n cnt d j k ≤ k * vb := by
  induction k with
  | zero => simp [s2P]
  | succ k ih =>
    rw [s2P_succ]
    have h1 : (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * coef n (nT n + j) k ≤ vb := by
      have hc := coef_le_one n (nT n + j) k
      have h2 : (if isBase n d k then cp n cnt d (tyIdx n k) else 0) ≤ vb := by
        split_ifs with h
        · obtain ⟨h3, h4⟩ := isBase_tyIdx h
          rw [h3]
          unfold cp
          exact (Nat.sub_le _ _).trans (hcnt _ h4)
        · omega
      calc _ ≤ (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * 1 := Nat.mul_le_mul_left _ hc
        _ ≤ vb := by omega
    nlinarith

theorem mul_le_of_le_one_left' (c a : ℕ) (h : c ≤ 1) : c * a ≤ a := by
  rw [mul_comm]; exact mul_le_of_le_one' a c h

theorem tAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n)
      (asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))))
      (fun σ σ' => σ' = σ.setVar "t" (σ.vars "i" / nZ n * if σ.vars "i" < nV n then 1 else 0))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hZ := hC.1.hZ
    have hV := hC.1.hV
    have hBN := hb.nN_lt
    have hBV := hb.nV_lt
    have hBZ := hb.nZ_lt
    have hB5 := hb.five_lt_B
    have hdiv : σ.vars "i" / σ.vars "Z" ≤ σ.vars "i" := Nat.div_le_self _ _
    have hprod := mul_le_of_le_one' (σ.vars "i" / σ.vars "Z")
      (1 - (1 - (σ.vars "V" - σ.vars "i"))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hZ, hV]
    by_cases h : σ.vars "i" < nV n
    · have e : 1 - (1 - (nV n - σ.vars "i")) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (nV n - σ.vars "i")) = 0 := by omega
      rw [e, if_neg h]

theorem mvAssign2_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb ∧
        (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n)
      (asg "mv" (.mul (eqF (.get "kd" (V "i")) (lit 1))
        (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))))
      (fun σ σ' => σ' = σ.setVar "mv" (if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 else 0))
      40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hzv : (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb :=
      ‹(σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb›
    have hsgv : (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n :=
      ‹(σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n›
    have hrb := hC.1.hrb
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hlkd : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBrb := hb.rb_lt
    have hBS := hb.SB_lt
    have hBK := hb.NK_lt
    have hidx : σ.vars "rb" + σ.vars "t" < zLen n := by
      have : nT n ≤ nM n := by unfold nM; omega
      unfold zLen; omega
    have hprod := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0)
      (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    by_cases h : (σ.arrs "kd").getD (σ.vars "i") 0 = 1
    · have e : 1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)) = 1 := by omega
      rw [e, if_pos h, one_mul]
    · have e : 1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)) = 0 := by omega
      rw [e, if_neg h, zero_mul]

/-- The static context of the second pass. -/
def C2 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "sg" = arrOf (nT n) (sigma n (dd n v))

theorem C2.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hs : "sg" ∉ c.warrs) : Stable c (C2 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (stable_arr "sg" (fun l => l = arrOf (nT n) (sigma n (dd n v))) hs))

theorem sigma_le' (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sigma n d t ≤ nN n * Kn n := sigma_le d t

/-- **The second pass over `Sj`.** -/
theorem s2Com_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C2 n cnt bb v σ ∧ σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n)))
      s2Com (fun _ σ' => C2 n cnt bb v σ' ∧
        σ'.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j))
      ((30 + 40 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 40 + ((30 + 4) * n + 6) + 4) s2Body
    (C2 n cnt bb v)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k))
    (C2.stable (by decide) (by decide) (by decide) (by decide) (by decide)) hb.nN_lt
    (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hS⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2⟩, ?_⟩
      simpa [s2P] using hS
    · rintro σ σ' - ⟨hC, hS, -⟩
      exact ⟨hC, by rw [hS]; exact arrOf_congr fun j _ => (Sj_eq_s n cnt _ j).symm⟩
  · intro k hk σ ⟨⟨hCE, hkd, hsg⟩, hik, hS⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    have hBN := hb.nN_lt
    obtain ⟨σ1, r1, e1⟩ := tAssign_vals hb v hv σ ⟨hCE, by omega⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = k / nZ n * (if k < nV n then 1 else 0) := ⟨_, rfl⟩
    have ht'T : t' < nT n := by
      rw [ht']
      by_cases h : k < nV n
      · rw [if_pos h, mul_one]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h
      · rw [if_neg h, mul_zero]; exact nT_pos n
    have hσ1t : σ1.vars "t" = t' := by
      rw [e1, ht']; simp only [Env.setVar, if_true, hik]
    have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
    have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
    have hkd1 : σ1.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) := by rw [e1]; simpa using hkd
    have hsg1 : σ1.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) := by rw [e1]; simpa using hsg
    have hS1 : σ1.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k) := by
      rw [e1]; simpa using hS
    have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd1, hi1]; exact getD_arrOf_lt hk
    have hzt : (σ1.arrs "z").getD (σ1.vars "rb" + σ1.vars "t") 0 = cnt t' := by
      rw [hCE1.1.hz, hCE1.1.hrb, hσ1t, ilpWord_rhs n cnt bb (by unfold nM; omega)]
      unfold rhs; rw [if_pos ht'T]
    have hsgt : (σ1.arrs "sg").getD (σ1.vars "t") 0 = sigma n (dd n v) t' := by
      rw [hsg1, hσ1t]; exact getD_arrOf_lt ht'T
    obtain ⟨σ2, r2, e2⟩ := mvAssign2_vals hb v σ1
      ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _,
        by rw [hzt]; exact hb.hcnt _ ht'T, by rw [hsgt]; exact sigma_le' _ _ _⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (if kindOf n (dd n v) k = 1 then cnt t' - sigma n (dd n v) t' else 0) := ⟨_, rfl⟩
    have hσ2m : σ2.vars "mv" = m := by
      rw [e2, hm]; simp only [Env.setVar, if_true, hkdk, hzt, hsgt]
    have hCE2 : CE n cnt bb v σ2 := by rw [e2]; exact hCE1.setVar (by decide) _
    have hi2 : σ2.vars "i" = k := by rw [e2]; simpa using hi1
    have hS2 : σ2.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k) := by
      rw [e2]; simpa using hS1
    have hmb : m ≤ vb := by
      rw [hm]; split_ifs
      · exact (Nat.sub_le _ _).trans (hb.hcnt _ ht'T)
      · omega
    have hSB := hb.SB_lt
    obtain ⟨σ3, r3, hC3, hi3, hm3, hS3⟩ := addRow_spec hb v k m hk
      (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k)
      (fun j _ => by
        have h1 := s1P_le n (dd n v) j (nN n)
        have h2 := s2P_le hb.hcnt (dd n v) j k (cnt := cnt) (n := n)
        have h3 : k * vb ≤ nN n * vb := Nat.mul_le_mul_right _ hk.le
        have h4 : nN n * (Kn n + vb) = nN n * Kn n + nN n * vb := by ring
        omega) σ2 ⟨hCE2, hi2, hσ2m, hS2⟩
    obtain ⟨σ4, r4, e4⟩ := bump_spec (B := B) "i" hb.one_lt_B σ3 (by
      show σ3.vars "i" + 1 < B; rw [hi3]; omega)
    have hmeq : m = if isBase n (dd n v) k then cp n cnt (dd n v) (tyIdx n k) else 0 := by
      by_cases hb1 : isBase n (dd n v) k
      · obtain ⟨h3, h4⟩ := isBase_tyIdx hb1
        have hV := isBase_lt_V hb1
        have ht'' : t' = k / nZ n := by rw [ht', if_pos hV, mul_one]
        rw [hm, if_pos (kindOf_eq_one.mpr hb1), if_pos hb1, h3, ht'']
        rfl
      · rw [hm, if_neg (fun h => hb1 (kindOf_eq_one.mp h)), if_neg hb1]
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, ?_⟩
    · rw [e4]; simp [Env.setVar, hi3]
    · rw [e4]
      show σ3.arrs "S" = _
      rw [hS3]
      refine arrOf_congr fun j _ => ?_
      rw [s2P_succ, ← hmeq]
      ring

end

end Lax117284Proofs.Machine.Ilp
