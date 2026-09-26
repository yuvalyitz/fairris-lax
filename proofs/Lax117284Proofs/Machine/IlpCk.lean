import Lax117284Proofs.Machine.IlpXv

/-!
The check: the candidate solves the program stored in `z`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- A value of the candidate is at most `Xbd`. -/
theorem xF_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (c : ℕ) : xF n cnt bb (certVec n v) c ≤ Xbd n vb := by
  unfold xF Xbd
  have hw := wvF_le hb v hv c
  split_ifs with h3 h2 h1
  · show (certVec n v).d c ≤ _
    simp only [certVec]
    split_ifs with hc
    · have := hv c (by unfold Dn; omega); omega
    · omega
  · omega
  · have hbase := kindOf_eq_one.mp h1
    obtain ⟨e1, e2⟩ := isBase_tyIdx (d := (certVec n v).d) hbase
    unfold cp
    have := hb.hcnt (tyIdx n c) (by rw [e1]; exact e2)
    omega
  · omega

theorem z_row_coef {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (hC : Ctx n cnt bb σ) {r c : ℕ}
    (hr : r < nM n) (hc : c < nN n) (hrow : σ.vars "rowb" = 2 + r * nN n) :
    (σ.arrs "z").getD (σ.vars "rowb" + c) 0 = coef n r c := by
  rw [hC.hz, hrow]
  exact ilpWord_coef n cnt bb hr hc

theorem ckInner_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (r : ℕ) (hr : r < nM n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "c" < nN n ∧ σ.vars "rowb" = 2 + r * nN n ∧
        (σ.arrs "xv").getD (σ.vars "c") 0 ≤ Xbd n vb ∧
        σ.vars "acc" + Xbd n vb ≤ nN n * Xbd n vb)
      ckInner
      (fun σ σ' => σ'.vars "c" = σ.vars "c" + 1 ∧
        σ'.vars "acc" = σ.vars "acc" + (σ.arrs "z").getD (σ.vars "rowb" + σ.vars "c") 0 *
          (σ.arrs "xv").getD (σ.vars "c") 0) 30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hc : σ.vars "c" < nN n := ‹σ.vars "c" < nN n›
    have hrow : σ.vars "rowb" = 2 + r * nN n := ‹σ.vars "rowb" = 2 + r * nN n›
    have hxv : (σ.arrs "xv").getD (σ.vars "c") 0 ≤ Xbd n vb := ‹(σ.arrs "xv").getD (σ.vars "c") 0 ≤ Xbd n vb›
    have hacc : σ.vars "acc" + Xbd n vb ≤ nN n * Xbd n vb := ‹σ.vars "acc" + Xbd n vb ≤ nN n * Xbd n vb›
    have hzc := z_row_coef hC.1 hr hc hrow
    have hcf := coef_le_one n r (σ.vars "c")
    have hidx : σ.vars "rowb" + σ.vars "c" < 2 + nM n * nN n := by
      rw [hrow]
      have := idx_lt_zLen hr hc
      omega
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlx : (σ.arrs "xv").length = nN n := hC.1.lxv
    have hprod := mul_le_of_le_one_left' ((σ.arrs "z").getD (σ.vars "rowb" + σ.vars "c") 0)
      ((σ.arrs "xv").getD (σ.vars "c") 0) (by rw [hzc]; exact hcf)
    have hBN := hb.nN_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBC := hb.CB_lt
    have hrb := rb_le_zLen n
    have hBrb := hb.rb_lt
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | exact ⟨trivial, trivial⟩)

/-- The row sum of the candidate, over the columns below `k`. -/
def rowSum (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (x : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ c ∈ range k, coef n r c * x c

theorem rowSum_le {n : ℕ} {x : ℕ → ℕ} {X : ℕ} (hx : ∀ c, x c ≤ X) (cnt : ℕ → ℕ) (bb r k : ℕ) :
    rowSum n cnt bb x r k ≤ k * X := by
  induction k with
  | zero => simp [rowSum]
  | succ k ih =>
    unfold rowSum at *
    rw [Finset.sum_range_succ]
    have h1 : coef n r k * x k ≤ X := by
      have := coef_le_one n r k
      calc coef n r k * x k ≤ 1 * x k := Nat.mul_le_mul_right _ this
        _ ≤ X := by simpa using hx k
    nlinarith

/-- The static context of the check. -/
def C6 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "xv" = arrOf (nN n) (xF n cnt bb (certVec n v))

theorem C6.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hx : "xv" ∉ c.warrs) : Stable c (C6 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (stable_arr "xv" (fun l => l = arrOf (nN n) (xF n cnt bb (certVec n v))) hx)

/-- **The row loop of the check.** -/
theorem ckInnerLoop_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (r : ℕ) (hr : r < nM n) :
    Spec B (fun σ => C6 n cnt bb v σ ∧ σ.vars "rowb" = 2 + r * nN n ∧ σ.vars "acc" = 0)
      (forZ "c" "N" ckInner)
      (fun _ σ' => C6 n cnt bb v σ' ∧ σ'.vars "rowb" = 2 + r * nN n ∧
        σ'.vars "acc" = rowSum n cnt bb (xF n cnt bb (certVec n v)) r (nN n))
      ((30 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "c" "N" (nN n) 30 ckInner
    (fun σ => C6 n cnt bb v σ ∧ σ.vars "rowb" = 2 + r * nN n)
    (fun k σ => σ.vars "acc" = rowSum n cnt bb (xF n cnt bb (certVec n v)) r k)
    (Stable.and (C6.stable (by decide) (by decide) (by decide) (by decide))
      (stable_var "rowb" (fun x => x = 2 + r * nN n) (by decide)))
    hb.nN_lt (fun σ h => h.1.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hrow, hacc⟩
      refine ⟨⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2⟩, by simpa using hrow⟩, ?_⟩
      simp [rowSum, hacc]
    · rintro σ σ' - ⟨⟨hC, hrow⟩, hacc, -⟩
      exact ⟨hC, hrow, hacc⟩
  · intro k hk σ ⟨⟨hC, hrow⟩, hck, hacc⟩
    have hxk : (σ.arrs "xv").getD (σ.vars "c") 0 = xF n cnt bb (certVec n v) k := by
      rw [hC.2, hck]; exact getD_arrOf_lt hk
    have hle := rowSum_le (n := n) (x := xF n cnt bb (certVec n v)) (X := Xbd n vb) (xF_le hb v hv) cnt bb r k
    have hXk : (k + 1) * Xbd n vb ≤ nN n * Xbd n vb := Nat.mul_le_mul_right _ hk
    obtain ⟨σ', hrun, h1, h2⟩ := ckInner_vals hb v r hr σ
      ⟨hC.1, by omega, hrow, by rw [hxk]; exact xF_le hb v hv k, by rw [hacc]; nlinarith⟩
    refine ⟨σ', hrun, by omega, ?_⟩
    rw [h2, hacc, hxk, hck, z_row_coef hC.1.1 hr (by omega) hrow]
    unfold rowSum
    rw [Finset.sum_range_succ]

theorem rowbAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" < nM n)
      (asg "rowb" (.add (lit 2) (.mul (V "r") (V "N"))))
      (fun σ σ' => σ' = σ.setVar "rowb" (2 + σ.vars "r" * nN n)) 20 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hr : σ.vars "r" < nM n := ‹σ.vars "r" < nM n›
    have hN := hC.1.hN
    have hlt : σ.vars "r" * nN n < nM n * nN n := by
      apply Nat.mul_lt_mul_of_pos_right hr (nN_pos n)
    have hlt' : σ.vars "r" * σ.vars "N" < nM n * nN n := by rw [hN]; exact hlt
    have hBrb := hb.rb_lt
    have hBM := hb.nM_lt
    have hBN := hb.nN_lt
    have hB5 := hb.five_lt_B
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (congr 1; rw [hN]))

theorem okAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" < nM n ∧ σ.vars "ok" ≤ 1 ∧
        σ.vars "acc" ≤ nN n * Xbd n vb ∧ (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 ≤ vb)
      (asg "ok" (.mul (V "ok") (eqF (V "acc") (.get "z" (.add (V "rb") (V "r"))))))
      (fun σ σ' => σ' = σ.setVar "ok" (σ.vars "ok" *
        if σ.vars "acc" = (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 then 1 else 0)) 30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hr : σ.vars "r" < nM n := ‹σ.vars "r" < nM n›
    have hok : σ.vars "ok" ≤ 1 := ‹σ.vars "ok" ≤ 1›
    have hacc : σ.vars "acc" ≤ nN n * Xbd n vb := ‹σ.vars "acc" ≤ nN n * Xbd n vb›
    have hzv : (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 ≤ vb := ‹(σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 ≤ vb›
    have hrb := hC.1.hrb
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hidx : σ.vars "rb" + σ.vars "r" < zLen n := by
      unfold zLen nM at *; omega
    have hBz := hb.zLen_lt
    have hBC := hb.CB_lt
    have hBrb := hb.rb_lt
    have hB5 := hb.five_lt_B
    have hBv : vb < B := hb.lt_U (by unfold Ub; omega)
    have hprod := mul_le_of_le_one' (σ.vars "ok")
      (1 - (σ.vars "acc" - (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 +
        ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 - σ.vars "acc"))) (by omega)
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | skip)
  all_goals
    congr 1
    have f1 : (1 - (σ.vars "acc" - (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 +
        ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 - σ.vars "acc"))) =
        if σ.vars "acc" = (σ.arrs "z").getD (σ.vars "rb" + σ.vars "r") 0 then 1 else 0 := by
      split_ifs <;> omega
    rw [f1]

theorem rowSum_N_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (r : ℕ) :
    rowSum n cnt bb (xF n cnt bb (certVec n v)) r (nN n) ≤ nN n * Xbd n vb :=
  rowSum_le (xF_le hb v hv) cnt bb r (nN n)

/-- **One row of the check.** -/
theorem ckBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nM n) (σ : Env) (hC : C6 n cnt bb v σ)
    (hrk : σ.vars "r" = k) (hok : σ.vars "ok" ≤ 1) :
    ∃ σ', Run B ckBody σ σ' (20 + 2 + ((30 + 4) * nN n + 6) + 30 + 4) ∧ σ'.vars "r" = k + 1 ∧
      σ'.vars "ok" = σ.vars "ok" *
        (if rowSum n cnt bb (xF n cnt bb (certVec n v)) k (nN n) = rhs n cnt bb k then 1 else 0) := by
  have hBM := hb.nM_lt
  obtain ⟨σ1, r1, e1⟩ := rowbAssign_vals hb v σ ⟨hC.1, by omega⟩
  obtain ⟨σ2, r2, e2⟩ := (Spec.pre (assign_lit_spec (B := B) "acc" 0 (by have := hb.five_lt_B; omega))
    (fun _ _ => trivial) : Spec B (fun σ => True) (asg "acc" (lit 0)) _ 2) σ1 trivial
  have hC2 : C6 n cnt bb v σ2 := by
    rw [e2, e1]; exact ⟨(hC.1.setVar (by decide) _).setVar (by decide) _, by simpa using hC.2⟩
  have hrow2 : σ2.vars "rowb" = 2 + k * nN n := by rw [e2, e1]; simp [Env.setVar, hrk]
  have hacc2 : σ2.vars "acc" = 0 := by rw [e2]; simp [Env.setVar]
  obtain ⟨σ3, r3, ⟨hC3, hrow3, hacc3⟩, hfv, -, -, -⟩ :=
    (ckInnerLoop_spec hb v hv k hk).frame σ2 ⟨hC2, hrow2, hacc2⟩
  have hr3 : σ3.vars "r" = k := by rw [hfv "r" (by decide), e2, e1]; simpa [Env.setVar] using hrk
  have hok3 : σ3.vars "ok" = σ.vars "ok" := by rw [hfv "ok" (by decide), e2, e1]; simp [Env.setVar]
  have hrb3 : σ3.vars "rb" = 2 + nM n * nN n := hC3.1.1.hrb
  have hzr : (σ3.arrs "z").getD (σ3.vars "rb" + σ3.vars "r") 0 = rhs n cnt bb k := by
    rw [hC3.1.1.hz, hrb3, hr3]; exact ilpWord_rhs n cnt bb hk
  have hzle : rhs n cnt bb k ≤ vb := by
    unfold rhs
    split_ifs with h
    · exact hb.hcnt _ h
    · exact hb.hbb
  obtain ⟨σ4, r4, e4⟩ := okAssign_vals hb v σ3
    ⟨hC3.1, by rw [hr3]; exact hk, by rw [hok3]; exact hok,
      by rw [hacc3]; exact rowSum_N_le hb v hv k, by rw [hzr]; exact hzle⟩
  obtain ⟨σ5, r5, e5⟩ := bump_spec (B := B) "r" hb.one_lt_B σ4 (by
    show σ4.vars "r" + 1 < B; rw [e4]; simp [Env.setVar, hr3]; omega)
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_, ?_⟩
  · rw [e5, e4]; simp [Env.setVar, hr3]
  · rw [e5, e4]
    simp only [Env.setVar, if_true, if_false, String.reduceEq]
    rw [hok3, hacc3, hzr]

theorem ok_step (P : ℕ → Prop) (k : ℕ) :
    (if (∀ r < k, P r) then 1 else 0) * (if P k then 1 else 0) =
      if (∀ r < k + 1, P r) then 1 else 0 := by
  by_cases hA : ∀ r < k, P r
  · by_cases hB : P k
    · have : ∀ r < k + 1, P r := by
        intro r hr
        by_cases h : r < k
        · exact hA r h
        · have : r = k := by omega
          subst this; exact hB
      rw [if_pos hA, if_pos hB, if_pos this]
    · have : ¬ ∀ r < k + 1, P r := fun h => hB (h k (by omega))
      rw [if_pos hA, if_neg hB, if_neg this]
  · have : ¬ ∀ r < k + 1, P r := fun h => hA fun r hr => h r (by omega)
    rw [if_neg hA, if_neg this, zero_mul]

/-- **The check.** -/
theorem ckCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C6 n cnt bb v σ)
      ckCom (fun _ σ' => C6 n cnt bb v σ' ∧
        σ'.vars "ok" = if Checks n cnt bb (xF n cnt bb (certVec n v)) then 1 else 0)
      (2 + (((20 + 2 + ((30 + 4) * nN n + 6) + 30 + 4) + 4) * nM n + 6)) := by
  have hs := scan_spec (B := B) "r" "M" (nM n) (20 + 2 + ((30 + 4) * nN n + 6) + 30 + 4) ckBody
    (C6 n cnt bb v)
    (fun k σ => σ.vars "ok" =
      if (∀ r < k, rowSum n cnt bb (xF n cnt bb (certVec n v)) r (nN n) = rhs n cnt bb r) then 1 else 0)
    (C6.stable (by decide) (by decide) (by decide) (by decide)) hb.nM_lt
    (fun σ h => h.1.1.hM) ?_
  · have hA : Spec B (fun σ => C6 n cnt bb v σ) (asg "ok" (lit 1))
        (fun σ σ' => σ' = σ.setVar "ok" 1) 2 :=
      Spec.pre (Spec.mono (Spec.assign (fun _ _ => evalB_lit (by have := hb.five_lt_B; omega)))
        (by simp)) (fun _ _ => trivial)
    have hs' : Spec B (fun σ => C6 n cnt bb v σ ∧ σ.vars "ok" = 1) (forZ "r" "M" ckBody)
        (fun _ σ' => C6 n cnt bb v σ' ∧
          σ'.vars "ok" = if Checks n cnt bb (xF n cnt bb (certVec n v)) then 1 else 0)
        ((20 + 2 + ((30 + 4) * nN n + 6) + 30 + 4 + 4) * nM n + 6) := by
      refine (Spec.pre hs ?_).post ?_
      · rintro σ ⟨hC, hok⟩
        refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2⟩, ?_⟩
        simp [hok]
      · rintro σ σ' - ⟨hC, hok, -⟩
        refine ⟨hC, ?_⟩
        rw [hok]
        have hiff : Checks n cnt bb (xF n cnt bb (certVec n v)) ↔
            (∀ r < nM n, rowSum n cnt bb (xF n cnt bb (certVec n v)) r (nN n) = rhs n cnt bb r) :=
          Iff.rfl
        exact if_congr hiff.symm rfl rfl
    unfold ckCom
    refine Spec.mono (Spec.seq hA hs' ?_ ?_) le_rfl
    · intro σ σ1 hσ e
      rw [e]
      exact ⟨⟨hσ.1.setVar (by decide) _, by simpa using hσ.2⟩, by simp⟩
    · intro σ σ1 σ2 hσ e hpost
      exact hpost
  · intro k hk σ ⟨hC, hrk, hok⟩
    have hok1 : σ.vars "ok" ≤ 1 := by rw [hok]; split_ifs <;> omega
    obtain ⟨σ', hr, h1, h2⟩ := ckBody_step hb v hv k hk σ hC hrk hok1
    refine ⟨σ', hr, h1, ?_⟩
    rw [h2, hok]
    convert ok_step (fun r => rowSum n cnt bb (xF n cnt bb (certVec n v)) r (nN n) = rhs n cnt bb r) k

end

end Lax117284Proofs.Machine.Ilp
