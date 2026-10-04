import Lax117284Proofs.Machine.IlpXv
import Lax117284Proofs.Machine.ClMainOk
import Lax117284Proofs.IlpClientsBridge
import Lax808846Proofs.Transfer

/-! ### `Lax117284Proofs.Machine.IlpCk` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.IlpEval` -/

section
/-!
One certificate: `evalCom` computes whether the digits in `dg` are accepted.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The cost of `evalCom`. -/
def Keval (n : ℕ) : ℕ :=
  ((7 + 4) * nT n + 6) + ((7 + 4) * nT n + 6) + ((7 + 4) * n + 6) + ((7 + 4) * nT n + 6) +
  ((100 + 4) * nN n + 6) +
  (2 + ((40 + 4) * nN n + 6)) +
  ((40 + 4) * nV n + 6) +
  ((30 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) +
  ((30 + 40 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) +
  (20 + (((30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) + 4) * nN n + 6)) +
  ((30 + 50 + 4 + 4) * nN n + 6) +
  ((30 + 80 + 4 + 4) * nN n + 6) +
  (2 + (((20 + 2 + ((30 + 4) * nN n + 6) + 30 + 4) + 4) * nM n + 6)) + 40

theorem finalGuard_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "E" ≤ nN n)
      (.ite (.lt (V "E") (.add (V "n") (lit 1))) .skip (asg "ok" (lit 0)))
      (fun σ σ' => σ'.vars "ok" = if σ.vars "E" ≤ n then σ.vars "ok" else 0) 40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hE : σ.vars "E" ≤ nN n := ‹σ.vars "E" ≤ nN n›
    have hnv := hC.1.hn
    have hBN := hb.nN_lt
    have hBn := hb.n_lt
    have hBn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
    have hB5 := hb.five_lt_B
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (split_ifs <;> omega))

/-- Zeroing a working array keeps the context. -/
theorem fillCE_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (a len : String) (L : ℕ) (hz : a ≠ "z") (hd : a ≠ "dg") (hne : len ≠ "fi")
    (hlen : ∀ σ, CE n cnt bb v σ → σ.vars len = L) (hLB : L < B) :
    Spec B (fun σ => CE n cnt bb v σ ∧ (σ.arrs a).length = L) (fillCom a len)
      (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs a = arrOf L (fun _ => 0)) ((7 + 4) * L + 6) := by
  refine fill_spec (B := B) a len L (CE n cnt bb v) ?_ (fun σ h => h.setVar (by decide) _) hlen hLB
    hb.one_lt_B hne
  exact CE.stable (by simp [Com.wvars, ctxVars, bump, asg]) (by simp [Com.warrs, bump, Ne.symm hz])
    (by simp [Com.warrs, bump, Ne.symm hd])

/-- **One certificate.** -/
theorem evalCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ) evalCom
      (fun _ σ' => CE n cnt bb v σ' ∧
        σ'.vars "ok" = if AccSpec n cnt bb (certVec n v) then 1 else 0) (Keval n) := by
  intro σ0 hCE0
  have hl := hCE0.1
  -- the fills
  obtain ⟨σ1, r1, ⟨hC1, hhl1⟩, hv1, ha1, -, -⟩ :=
    (fillCE_spec hb v "hl" "T" (nT n) (by decide) (by decide) (by decide) (fun σ h => h.1.hT)
      hb.nT_lt).frame σ0 ⟨hCE0, hl.lhl⟩
  obtain ⟨σ2, r2, ⟨hC2, hsg2⟩, hv2, ha2, -, -⟩ :=
    (fillCE_spec hb v "sg" "T" (nT n) (by decide) (by decide) (by decide) (fun σ h => h.1.hT)
      hb.nT_lt).frame σ1 ⟨hC1, by rw [ha1 "sg" (by decide)]; exact hl.lsg⟩
  obtain ⟨σ3, r3, ⟨hC3, hS3⟩, hv3, ha3, -, -⟩ :=
    (fillCE_spec hb v "S" "n" n (by decide) (by decide) (by decide) (fun σ h => h.1.hn)
      hb.n_lt).frame σ2 ⟨hC2, by rw [ha2 "S" (by decide), ha1 "S" (by decide)]; exact hl.lS⟩
  obtain ⟨σ4, r4, ⟨hC4, hes4⟩, hv4, ha4, -, -⟩ :=
    (fillCE_spec hb v "es" "T" (nT n) (by decide) (by decide) (by decide) (fun σ h => h.1.hT)
      hb.nT_lt).frame σ3 ⟨hC3, by rw [ha3 "es" (by decide), ha2 "es" (by decide), ha1 "es" (by decide)]; exact hl.les⟩
  have hhl4 : σ4.arrs "hl" = arrOf (nT n) (fun _ => 0) := by
    rw [ha4 "hl" (by decide), ha3 "hl" (by decide), ha2 "hl" (by decide)]; exact hhl1
  have hsg4 : σ4.arrs "sg" = arrOf (nT n) (fun _ => 0) := by
    rw [ha4 "sg" (by decide), ha3 "sg" (by decide)]; exact hsg2
  have hS4 : σ4.arrs "S" = arrOf n (fun _ => 0) := by
    rw [ha4 "S" (by decide)]; exact hS3
  -- the kinds
  obtain ⟨σ5, r5, ⟨hC5, hkd5⟩, hv5, ha5, -, -⟩ :=
    (kdCom_spec hb v hv).frame σ4 ⟨hC4, ⟨_, eq_arrOf_of_length hC4.1.lkd⟩, hhl4⟩
  -- the ranks
  obtain ⟨σ6, r6, ⟨hC6, hrk6, hE6⟩, hv6, ha6, -, -⟩ :=
    (rkCom_spec hb v).frame σ5 ⟨hC5, hkd5, ⟨_, eq_arrOf_of_length hC5.1.lrk⟩⟩
  have hkd6 : σ6.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) := by
    rw [ha6 "kd" (by decide)]; exact hkd5
  have hsg6 : σ6.arrs "sg" = arrOf (nT n) (fun _ => 0) := by
    rw [ha6 "sg" (by decide), ha5 "sg" (by decide)]; exact hsg4
  have hS6 : σ6.arrs "S" = arrOf n (fun _ => 0) := by
    rw [ha6 "S" (by decide), ha5 "S" (by decide)]; exact hS4
  -- sigma
  obtain ⟨σ7, r7, ⟨hC7, hsg7⟩, hv7, ha7, -, -⟩ :=
    (sgCom_spec hb v hv).frame σ6 ⟨hC6, hkd6, hsg6⟩
  have hkd7 : σ7.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) := by
    rw [ha7 "kd" (by decide)]; exact hkd6
  have hrk7 : σ7.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) := by
    rw [ha7 "rkA" (by decide)]; exact hrk6
  have hS7 : σ7.arrs "S" = arrOf n (fun _ => 0) := by
    rw [ha7 "S" (by decide)]; exact hS6
  have hE7 : σ7.vars "E" = (Ext n (dd n v)).card := by
    rw [hv7 "E" (by decide)]; exact hE6
  -- the first pass over Sj
  obtain ⟨σ8, r8, ⟨hC8, hS8⟩, hv8, ha8, -, -⟩ :=
    (s1Com_spec hb v hv).frame σ7 ⟨hC7, hS7⟩
  have hkd8 : σ8.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) := by
    rw [ha8 "kd" (by decide)]; exact hkd7
  have hsg8 : σ8.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) := by
    rw [ha8 "sg" (by decide)]; exact hsg7
  have hrk8 : σ8.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) := by
    rw [ha8 "rkA" (by decide)]; exact hrk7
  have hE8 : σ8.vars "E" = (Ext n (dd n v)).card := by
    rw [hv8 "E" (by decide)]; exact hE7
  -- the second pass over Sj
  obtain ⟨σ9, r9, ⟨⟨hC9, hkd9, hsg9⟩, hS9⟩, hv9, ha9, -, -⟩ :=
    (s2Com_spec hb v hv).frame σ8 ⟨⟨hC8, hkd8, hsg8⟩, hS8⟩
  have hrk9 : σ9.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) := by
    rw [ha9 "rkA" (by decide)]; exact hrk8
  have hE9 : σ9.vars "E" = (Ext n (dd n v)).card := by
    rw [hv9 "E" (by decide)]; exact hE8
  have hes9 : σ9.arrs "es" = arrOf (nT n) (fun _ => 0) := by
    rw [ha9 "es" (by decide), ha8 "es" (by decide), ha7 "es" (by decide), ha6 "es" (by decide),
      ha5 "es" (by decide)]; exact hes4
  -- the values
  obtain ⟨σ10, r10, ⟨⟨hC10, hkd10, hrk10, hS10, hdl10⟩, hwv10⟩, hv10, ha10, -, -⟩ :=
    (wvCom_spec hb v hv).frame σ9 ⟨hC9, hkd9, hrk9, hS9, ⟨_, eq_arrOf_of_length hC9.1.lwv⟩⟩
  have hsg10 : σ10.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) := by
    rw [ha10 "sg" (by decide)]; exact hsg9
  have hE10 : σ10.vars "E" = (Ext n (dd n v)).card := by
    rw [hv10 "E" (by decide)]; exact hE9
  have hes10 : σ10.arrs "es" = arrOf (nT n) (fun _ => 0) := by
    rw [ha10 "es" (by decide)]; exact hes9
  -- the sums of the extras
  obtain ⟨σ11, r11, ⟨⟨hC11, hkd11, hwv11⟩, hes11⟩, hv11, ha11, -, -⟩ :=
    (esCom_spec hb v hv).frame σ10 ⟨⟨hC10, hkd10, hwv10⟩, hes10⟩
  have hsg11 : σ11.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) := by
    rw [ha11 "sg" (by decide)]; exact hsg10
  have hE11 : σ11.vars "E" = (Ext n (dd n v)).card := by
    rw [hv11 "E" (by decide)]; exact hE10
  -- the candidate
  obtain ⟨σ12, r12, ⟨⟨hC12, hkd12, hwv12, hsg12, hes12⟩, hxv12⟩, hv12, ha12, -, -⟩ :=
    (xvCom_spec hb v hv).frame σ11
      ⟨⟨hC11, hkd11, hwv11, hsg11, hes11⟩, ⟨_, eq_arrOf_of_length hC11.1.lxv⟩⟩
  have hE12 : σ12.vars "E" = (Ext n (dd n v)).card := by
    rw [hv12 "E" (by decide)]; exact hE11
  -- the check
  obtain ⟨σ13, r13, ⟨⟨hC13, hxv13⟩, hok13⟩, hv13, ha13, -, -⟩ :=
    (ckCom_spec hb v hv).frame σ12 ⟨hC12, hxv12⟩
  have hE13 : σ13.vars "E" = (Ext n (dd n v)).card := by
    rw [hv13 "E" (by decide)]; exact hE12
  have hEle : (Ext n (dd n v)).card ≤ nN n := by
    rw [card_Ext_eq_rk]; exact (rk_le_self n _ _)
  -- the guard
  obtain ⟨σ14, r14, hok14, hkeeps⟩ :=
    spec_keeps (finalGuard_spec hb v) σ13 ⟨hC13, by rw [hE13]; exact hEle⟩
  have hC14 : CE n cnt bb v σ14 :=
    (CE.stable (c := .ite (.lt (V "E") (.add (V "n") (lit 1))) .skip (asg "ok" (lit 0)))
      (by decide) (by decide) (by decide)) σ13 σ14 hC13 hkeeps
  refine ⟨σ14, ?_, hC14, ?_⟩
  · refine Run.mono (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq (r11.seq (r12.seq (r13.seq r14))))))))))))) ?_
    unfold Keval; omega
  · rw [hok14, hok13, hE13]
    by_cases hg : (Ext n (dd n v)).card ≤ n
    · by_cases hc : Checks n cnt bb (xF n cnt bb (certVec n v))
      · have : AccSpec n cnt bb (certVec n v) := ⟨hg, hc⟩
        rw [if_pos hg, if_pos hc, if_pos this]
      · have : ¬ AccSpec n cnt bb (certVec n v) := fun h => hc h.2
        rw [if_pos hg, if_neg hc, if_neg this]
    · have : ¬ AccSpec n cnt bb (certVec n v) := fun h => hg h.1
      rw [if_neg hg, if_neg this]

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpOdo` -/

section
/-!
The odometer: add one to the number whose base-`R` digits are in `dg`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem odoBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.vars "q" < Dn n ∧ σ.vars "cy" ≤ 1 ∧
        (σ.arrs "dg").getD (σ.vars "q") 0 < Rd n)
      odoBody
      (fun σ σ' => σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.vars "cy" = ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / Rd n ∧
        σ'.arrs "dg" = (σ.arrs "dg").set (σ.vars "q")
          (((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") -
            ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / Rd n * Rd n)) 40 := by
  run_vcg
  all_goals
    have hC : Ctx n cnt bb σ := ‹Ctx n cnt bb σ›
    have hq : σ.vars "q" < Dn n := ‹σ.vars "q" < Dn n›
    have hcy : σ.vars "cy" ≤ 1 := ‹σ.vars "cy" ≤ 1›
    have hd : (σ.arrs "dg").getD (σ.vars "q") 0 < Rd n := ‹(σ.arrs "dg").getD (σ.vars "q") 0 < Rd n›
    have hR := hC.hR
    have hldg := hC.ldg
    have hBR := hb.Rd_lt
    have hBD := hb.Dn_lt
    have hB5 := hb.five_lt_B
    have hdiv : ((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / σ.vars "R" ≤ 1 := by
      apply Nat.div_le_of_le_mul
      omega
    have hprod := mul_le_of_le_one_left'
      (((σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy") / σ.vars "R") (σ.vars "R") hdiv
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; rw [hR]; exact ⟨rfl, rfl⟩))

theorem encR_top (R : ℕ) (f : ℕ → ℕ) (k : ℕ) : encR R f (k + 1) = encR R f k + f k * R ^ k := by
  unfold encR; rw [Finset.sum_range_succ]

theorem encR_congr' (R : ℕ) {f g : ℕ → ℕ} {k : ℕ} (h : ∀ q < k, f q = g q) :
    encR R f k = encR R g k := by
  unfold encR
  exact Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.mp hq)]

theorem odo_arith (S F c fk X R cy' v : ℕ) (hS : S + c * X = F + 1) (hv : v = fk + c)
    (hcy : cy' * R ≤ v) : S + (v - cy' * R) * X + cy' * (X * R) = F + fk * X + 1 := by
  have h1 : (v - cy' * R) * X + cy' * R * X = v * X := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hcy]
  have h2 : cy' * (X * R) = cy' * R * X := by ring
  rw [h2]
  have h3 : v * X = fk * X + c * X := by rw [hv]; ring
  omega

theorem encR_digitsOf {R : ℕ} (hR : 0 < R) :
    ∀ (D t : ℕ), t < R ^ D → encR R (digitsOf R t) D = t := by
  intro D
  induction D with
  | zero => intro t ht; simp at ht; simp [encR, ht]
  | succ D ih =>
    intro t ht
    rw [encR_succ']
    have h1 : t / R < R ^ D := by
      rw [pow_succ'] at ht
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; simpa [mul_comm] using ht)
    have h2 : encR R (fun q => digitsOf R t (q + 1)) D = encR R (digitsOf R (t / R)) D := by
      refine encR_congr' R fun q _ => ?_
      unfold digitsOf
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
    rw [h2, ih _ h1]
    unfold digitsOf
    simp only [pow_zero, Nat.div_one]
    exact Nat.mod_add_div t R

/-- **The odometer**: the digits of `t` become the digits of `t + 1`, the carry is `1` exactly when
`t + 1` is the number of vectors. -/
theorem odoCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (t : ℕ)
    (ht : t < Rd n ^ Dn n) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t))
      odoCom
      (fun _ σ' => Ctx n cnt bb σ' ∧ σ'.vars "cy" = (if t + 1 = Rd n ^ Dn n then 1 else 0) ∧
        σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) ((t + 1) % Rd n ^ Dn n)))
      (2 + ((40 + 4) * Dn n + 6)) := by
  have hR : 0 < Rd n := by unfold Rd; omega
  set f := digitsOf (Rd n) t with hf
  have hfR : ∀ q, f q < Rd n := fun q => digitsOf_lt hR t q
  have hEf : encR (Rd n) f (Dn n) = t := encR_digitsOf hR (Dn n) t ht
  have hs := scan_spec (B := B) "q" "D" (Dn n) 40 odoBody (Ctx n cnt bb)
    (fun k σ => ∃ g, σ.arrs "dg" = arrOf (Dn n) g ∧ σ.vars "cy" ≤ 1 ∧ (∀ r, k ≤ r → g r = f r) ∧
      (∀ r < Dn n, g r < Rd n) ∧
      encR (Rd n) g k + σ.vars "cy" * Rd n ^ k = encR (Rd n) f k + 1)
    (Ctx.stable (by decide) (by decide)) hb.Dn_lt (fun σ h => h.hD) ?_
  · have hA : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) f) (asg "cy" (lit 1))
        (fun σ σ' => σ' = σ.setVar "cy" 1) 2 :=
      Spec.pre (assign_lit_spec (B := B) "cy" 1 hb.one_lt_B) (fun _ _ => trivial)
    have hs' : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) f ∧ σ.vars "cy" = 1)
        (forZ "q" "D" odoBody)
        (fun _ σ' => Ctx n cnt bb σ' ∧ σ'.vars "cy" = (if t + 1 = Rd n ^ Dn n then 1 else 0) ∧
          σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) ((t + 1) % Rd n ^ Dn n)))
        ((40 + 4) * Dn n + 6) := by
      refine (Spec.pre hs ?_).post ?_
      · rintro σ ⟨hC, hdg, hcy⟩
        refine ⟨hC.setVar (by decide) _, ⟨f, by simpa using hdg, by simp [hcy], fun r _ => rfl,
          fun r _ => hfR r, by simp [hcy, encR]⟩⟩
      · rintro σ σ' - ⟨hC, ⟨g, hg, hcy, hgf, hgR, henc⟩, hq⟩
        refine ⟨hC, ?_⟩
        rw [hEf] at henc
        obtain ⟨hlt, hdig⟩ := digits_encR hR (Dn n) g (fun q hq => hgR q hq)
        have hcyc : σ'.vars "cy" = 0 ∨ σ'.vars "cy" = 1 := by omega
        rcases hcyc with h0 | h1
        · rw [h0] at henc
          have hnc : encR (Rd n) g (Dn n) = t + 1 := by omega
          have hlt' : t + 1 < Rd n ^ Dn n := by rw [← hnc]; exact hlt
          rw [if_neg (by omega), Nat.mod_eq_of_lt hlt', h0]
          refine ⟨rfl, ?_⟩
          rw [hg]
          refine arrOf_congr fun q hq => ?_
          rw [← hnc]; exact (hdig q hq).symm
        · rw [h1] at henc
          have hnc : encR (Rd n) g (Dn n) = 0 := by
            have : Rd n ^ Dn n ≥ t + 1 := ht
            have hh : t + 1 ≤ Rd n ^ Dn n := ht
            omega
          have heq : t + 1 = Rd n ^ Dn n := by
            have := hlt; omega
          rw [if_pos heq, heq, Nat.mod_self, h1]
          refine ⟨rfl, ?_⟩
          rw [hg]
          refine arrOf_congr fun q hq => ?_
          rw [← hdig q hq, hnc]
    unfold odoCom
    refine Spec.mono (Spec.seq hA hs' ?_ ?_) le_rfl
    · intro σ σ1 hσ e
      rw [e]
      exact ⟨hσ.1.setVar (by decide) _, by simpa using hσ.2, by simp⟩
    · intro σ σ1 σ2 hσ e hpost
      exact hpost
  · intro k hk σ ⟨hC, hqk, g, hg, hcy, hgf, hgR, henc⟩
    have hgk : g k = f k := hgf k le_rfl
    have hDl := hC.ldg
    have hd : (σ.arrs "dg").getD (σ.vars "q") 0 = f k := by
      rw [hg, hqk, getD_arrOf_lt hk, hgk]
    obtain ⟨σ', hr, h1, h2, h3⟩ := odoBody_vals hb σ
      ⟨hC, by omega, hcy, by rw [hd]; exact hfR k⟩
    have hv : (σ.arrs "dg").getD (σ.vars "q") 0 + σ.vars "cy" = f k + σ.vars "cy" := by rw [hd]
    have hcy' : σ'.vars "cy" = (f k + σ.vars "cy") / Rd n := by rw [h2, hv]
    have hcy1 : σ'.vars "cy" ≤ 1 := by
      rw [hcy']
      apply Nat.div_le_of_le_mul
      have := hfR k; omega
    have hdm : (σ'.vars "cy") * Rd n ≤ f k + σ.vars "cy" := by
      rw [hcy']; exact Nat.div_mul_le_self _ _
    refine ⟨σ', hr, by omega, ⟨fun r => if r = k then (f k + σ.vars "cy") - σ'.vars "cy" * Rd n else g r,
      ?_, hcy1, ?_, ?_, ?_⟩⟩
    · rw [h3, hd, hqk, hg, set_arrOf, hcy']
    · intro r hr
      have : r ≠ k := by omega
      simp only [this, if_false]; exact hgf r (by omega)
    · intro r hr
      by_cases h : r = k
      · subst h; simp only [if_true]
        have hh := Nat.div_add_mod' (f r + σ.vars "cy") (Rd n)
        have hm := Nat.mod_lt (f r + σ.vars "cy") hR
        rw [hcy']
        have : f r + σ.vars "cy" - (f r + σ.vars "cy") / Rd n * Rd n = (f r + σ.vars "cy") % Rd n := by
          omega
        rw [this]; exact hm
      · simp only [h, if_false]; exact hgR r hr
    · have hc1 : encR (Rd n) (fun r => if r = k then (f k + σ.vars "cy") - σ'.vars "cy" * Rd n else g r) k = encR (Rd n) g k :=
        encR_congr' (Rd n) fun q hq => by simp [Nat.ne_of_lt hq]
      rw [encR_top, encR_top, hc1]
      simp only [if_true]
      have := odo_arith (encR (Rd n) g k) (encR (Rd n) f k) (σ.vars "cy") (f k) (Rd n ^ k) (Rd n)
        (σ'.vars "cy") (f k + σ.vars "cy") henc rfl hdm
      rw [pow_succ]
      exact this

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpSearch` -/

section
/-!
The search: every number below `R ^ D` is decoded and tested.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem foundUpd_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "ok" ≤ 1)
      (.ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip)
      (fun σ σ' => σ'.vars "found" = if σ.vars "ok" = 1 then 1 else σ.vars "found") 20 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hok : σ.vars "ok" ≤ 1 := ‹σ.vars "ok" ≤ 1›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (split_ifs <;> omega))

theorem doneAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "cy" ≤ 1) (asg "done" (V "cy"))
      (fun σ σ' => σ' = σ.setVar "done" (σ.vars "cy")) 20 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hcy : σ.vars "cy" ≤ 1 := ‹σ.vars "cy" ≤ 1›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | rfl)

theorem found_step (P : ℕ → Prop) (t : ℕ) :
    (if P t then 1 else if ∃ t' < t, P t' then 1 else 0) = if ∃ t' < t + 1, P t' then 1 else 0 := by
  by_cases h : P t
  · rw [if_pos h, if_pos]
    exact ⟨t, by omega, h⟩
  · rw [if_neg h]
    by_cases h2 : ∃ t' < t, P t'
    · rw [if_pos h2, if_pos]
      obtain ⟨t', ht', hp⟩ := h2
      exact ⟨t', by omega, hp⟩
    · rw [if_neg h2, if_neg]
      rintro ⟨t', ht', hp⟩
      by_cases hh : t' = t
      · subst hh; exact h hp
      · exact h2 ⟨t', by omega, hp⟩

/-- The cost of a turn of the search. -/
def Kturn (n : ℕ) : ℕ := Keval n + 20 + (2 + ((40 + 4) * Dn n + 6)) + 20

theorem digitsOf_le_K (n t q : ℕ) : digitsOf (Rd n) t q ≤ Kn n := by
  have h := digitsOf_lt (R := Rd n) (by unfold Rd; omega) t q
  have e : Rd n = Kn n + 1 := rfl
  omega

/-- **One turn of the search.** -/
theorem searchBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (t : ℕ)
    (ht : t < Rd n ^ Dn n) (σ : Env) (hC : Ctx n cnt bb σ)
    (hdg : σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t))
    (hfound : σ.vars "found" = if ∃ t' < t, AccT n cnt bb t' then 1 else 0) :
    ∃ σ', Run B searchBody σ σ' (Kturn n) ∧ Ctx n cnt bb σ' ∧
      ((t + 1 < Rd n ^ Dn n ∧ σ'.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) (t + 1)) ∧
          σ'.vars "done" = 0 ∧ σ'.vars "found" = if ∃ t' < t + 1, AccT n cnt bb t' then 1 else 0) ∨
        (t + 1 = Rd n ^ Dn n ∧ σ'.vars "done" = 1 ∧
          σ'.vars "found" = if ∃ t' < Rd n ^ Dn n, AccT n cnt bb t' then 1 else 0)) := by
  have hv := fun q (_ : q < Dn n) => digitsOf_le_K n t q
  obtain ⟨σ1, r1, ⟨hC1, hok1⟩, hv1, ha1, -, -⟩ :=
    (evalCom_spec hb (digitsOf (Rd n) t) hv).frame σ ⟨hC, hdg⟩
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) := hC1.2
  have hC1' : Ctx n cnt bb σ1 := hC1.1
  have hfound1 : σ1.vars "found" = σ.vars "found" := hv1 "found" (by decide)
  have hok1' : σ1.vars "ok" ≤ 1 := by rw [hok1]; split_ifs <;> omega
  obtain ⟨σ2, r2, hfnd2⟩ := foundUpd_vals hb σ1 hok1'
  obtain ⟨σ2, r2, hfnd2, hk2⟩ := spec_keeps (foundUpd_vals hb) σ1 hok1'
  have hC2 : Ctx n cnt bb σ2 :=
    (Ctx.stable (c := .ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip)
      (by decide) (by decide)) σ1 σ2 hC1' hk2
  have hdg2 : σ2.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) := by
    rw [hk2.2.1 "dg" (by decide)]; exact hdg1
  have hfound2 : σ2.vars "found" =
      if AccT n cnt bb t then 1 else (if ∃ t' < t, AccT n cnt bb t' then 1 else 0) := by
    rw [hfnd2, hfound1, hfound, hok1]
    by_cases h : AccSpec n cnt bb (certVec n (digitsOf (Rd n) t))
    · have h' : AccT n cnt bb t := h
      simp [h, h']
    · have h' : ¬ AccT n cnt bb t := h
      simp [h, h']
  obtain ⟨σ3, r3, ⟨hC3, hcy3, hdg3⟩, hv3, ha3, -, -⟩ :=
    (odoCom_spec hb t ht).frame σ2 ⟨hC2, hdg2⟩
  have hfound3 : σ3.vars "found" = σ2.vars "found" := hv3 "found" (by decide)
  have hcy3' : σ3.vars "cy" ≤ 1 := by rw [hcy3]; split_ifs <;> omega
  obtain ⟨σ4, r4, e4⟩ := doneAssign_vals hb σ3 hcy3'
  have hC4 : Ctx n cnt bb σ4 := by rw [e4]; exact hC3.setVar (by decide) _
  have hfound4 : σ4.vars "found" = σ3.vars "found" := by rw [e4]; simp [Env.setVar]
  have hdone4 : σ4.vars "done" = σ3.vars "cy" := by rw [e4]; simp [Env.setVar]
  have hdg4 : σ4.arrs "dg" = σ3.arrs "dg" := by rw [e4]; rfl
  refine ⟨σ4, ?_, hC4, ?_⟩
  · refine Run.mono (show Run B searchBody σ σ4 _ from r1.seq (r2.seq (r3.seq r4))) ?_
    unfold Kturn; omega
  · by_cases hlast : t + 1 = Rd n ^ Dn n
    · right
      refine ⟨hlast, ?_, ?_⟩
      · rw [hdone4, hcy3, if_pos hlast]
      · rw [hfound4, hfound3, hfound2, found_step, ← hlast]
    · left
      have hlt : t + 1 < Rd n ^ Dn n := by omega
      refine ⟨hlt, ?_, ?_, ?_⟩
      · rw [hdg4, hdg3, Nat.mod_eq_of_lt hlt]
      · rw [hdone4, hcy3, if_neg hlast]
      · rw [hfound4, hfound3, hfound2, found_step]

/-- The number whose digits are in `dg`. -/
def tOf (n : ℕ) (σ : Env) : ℕ := encR (Rd n) (fun q => (σ.arrs "dg").getD q 0) (Dn n)

theorem tOf_digits (n t : ℕ) (σ : Env) (ht : t < Rd n ^ Dn n)
    (hdg : σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t)) : tOf n σ = t := by
  have hR : 0 < Rd n := by unfold Rd; omega
  unfold tOf
  rw [encR_congr' (Rd n) (g := digitsOf (Rd n) t) (fun q hq => by rw [hdg]; exact getD_arrOf_lt hq)]
  exact encR_digitsOf hR (Dn n) t ht

/-- The invariant of the search. -/
def SInv (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop :=
  Ctx n cnt bb σ ∧
    ((∃ t, t < Rd n ^ Dn n ∧ σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) t) ∧
        σ.vars "done" = 0 ∧ σ.vars "found" = if ∃ t' < t, AccT n cnt bb t' then 1 else 0) ∨
      (σ.vars "done" = 1 ∧
        σ.vars "found" = if ∃ t' < Rd n ^ Dn n, AccT n cnt bb t' then 1 else 0))

/-- The potential of the search. -/
def SPot (n : ℕ) (σ : Env) : ℕ :=
  if σ.vars "done" = 0 then (Rd n ^ Dn n - tOf n σ) * (Kturn n + 4) else 0

/-- The cost of the search. -/
def Ksearch (n : ℕ) : ℕ := 2 + 2 + (Rd n ^ Dn n * (Kturn n + 4) + 4)

theorem done_eq_zero_of_true {B : ℕ} {σ : Env}
    (h : (Cond.eq (V "done") (lit 0)).evalB B σ = some true) : σ.vars "done" = 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨m, n', ⟨hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hm; subst hn
  simpa using hr.symm

theorem done_ne_zero_of_false {B : ℕ} {σ : Env}
    (h : (Cond.eq (V "done") (lit 0)).evalB B σ = some false) : σ.vars "done" ≠ 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨m, n', ⟨hm, -⟩, ⟨hn, -⟩, hr⟩ := h
  subst hm; subst hn
  intro h0
  rw [h0] at hr
  simp at hr

theorem SInv.done_le {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (h : SInv n cnt bb σ) :
    σ.vars "done" ≤ 1 := by
  rcases h.2 with ⟨t, -, -, hd, -⟩ | ⟨hd, -⟩ <;> omega

/-- **The search.** -/
theorem searchCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      searchCom
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (Ksearch n) := by
  have hR : 0 < Rd n := by unfold Rd; omega
  have hRD : 0 < Rd n ^ Dn n := pow_pos hR _
  have hloop : Spec B (fun σ => SInv n cnt bb σ ∧ σ.vars "done" = 0 ∧ tOf n σ = 0)
      (.while (.eq (V "done") (lit 0)) searchBody)
      (fun _ σ' => SInv n cnt bb σ' ∧ (Cond.eq (V "done") (lit 0)).evalB B σ' = some false)
      (Rd n ^ Dn n * (Kturn n + 4) + 4) := by
    refine Spec.while_potential (B := B) (b := .eq (V "done") (lit 0)) (c := searchBody)
      (SInv n cnt bb) (SPot n) ?_ ?_ (fun σ h => h.1) ?_
    · intro σ hI
      have hd := hI.done_le
      have h1 := hb.five_lt_B
      exact (evalB_condEq_isSome (evalB_var (by omega)) (evalB_lit (by omega))).elim
        fun v hv => ⟨v, hv.1⟩
    · intro σ hI hcond
      have hdone := done_eq_zero_of_true hcond
      obtain ⟨hC, hd⟩ := hI
      rcases hd with ⟨t, ht, hdg, hdn, hfound⟩ | ⟨hd1, -⟩
      · obtain ⟨σ', hr, hC', hcases⟩ := searchBody_step hb t ht σ hC hdg hfound
        have htσ : tOf n σ = t := tOf_digits n t σ ht hdg
        refine ⟨σ', Kturn n, hr, ⟨hC', ?_⟩, ?_⟩
        · rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
          · exact Or.inl ⟨t + 1, h1, h2, h3, h4⟩
          · exact Or.inr ⟨h2, h3⟩
        · unfold SPot
          rw [if_pos hdn, htσ]
          have hcs : (Cond.eq (V "done") (lit 0)).size = 3 := by simp
          rw [hcs]
          rcases hcases with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
          · rw [if_pos h3, tOf_digits n (t + 1) σ' h1 h2]
            have : Rd n ^ Dn n - t = (Rd n ^ Dn n - (t + 1)) + 1 := by omega
            rw [this]; nlinarith
          · rw [if_neg (by omega)]
            have : Rd n ^ Dn n - t = 1 := by omega
            rw [this]; omega
      · omega
    · intro σ hP
      obtain ⟨hI, hdone, ht0⟩ := hP
      unfold SPot
      rw [if_pos hdone, ht0]
      have hcs : (Cond.eq (V "done") (lit 0)).size = 3 := by simp
      rw [hcs, Nat.sub_zero]
  have hz0 : ∀ σ : Env, σ.arrs "dg" = arrOf (Dn n) (fun _ => 0) →
      σ.arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) 0) := by
    intro σ h
    rw [h]; exact arrOf_congr fun q _ => by simp [digitsOf]
  have hA : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      (asg "found" (lit 0)) (fun σ σ' => σ' = σ.setVar "found" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "found" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  have hA' : Spec B (fun σ => (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
        σ.vars "found" = 0)
      (asg "done" (lit 0)) (fun σ σ' => σ' = σ.setVar "done" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "done" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  have hfin : Spec B (fun σ => SInv n cnt bb σ ∧ σ.vars "done" = 0 ∧ tOf n σ = 0)
      (.while (.eq (V "done") (lit 0)) searchBody)
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (Rd n ^ Dn n * (Kturn n + 4) + 4) := by
    refine Spec.post hloop ?_
    rintro σ σ' - ⟨⟨hC, hd⟩, hfalse⟩
    have hne := done_ne_zero_of_false hfalse
    rcases hd with ⟨t, -, -, hd0, -⟩ | ⟨-, hf⟩
    · exact absurd hd0 hne
    · exact ⟨hC, hf⟩
  have h2 : Spec B (fun σ => (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
        σ.vars "found" = 0)
      (.seq (asg "done" (lit 0)) (.while (.eq (V "done") (lit 0)) searchBody))
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (2 + (Rd n ^ Dn n * (Kturn n + 4) + 4)) := by
    have hmid : ∀ σ σ1 : Env, ((Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧
          σ.vars "found" = 0) → σ1 = σ.setVar "done" 0 →
        (SInv n cnt bb σ1 ∧ σ1.vars "done" = 0 ∧ tOf n σ1 = 0) := by
      rintro σ σ1 ⟨⟨hC, hdg⟩, hf⟩ e
      rw [e]
      have hC1 : Ctx n cnt bb (σ.setVar "done" 0) := hC.setVar (by decide) _
      have hdg1 : (σ.setVar "done" 0).arrs "dg" = arrOf (Dn n) (digitsOf (Rd n) 0) := by
        simpa using hz0 σ hdg
      refine ⟨⟨hC1, Or.inl ⟨0, hRD, hdg1, by simp, by simp [hf]⟩⟩, by simp, ?_⟩
      exact tOf_digits n 0 _ hRD hdg1
    exact Spec.mono (Spec.seq hA' hfin hmid (fun σ σ1 σ2 _ _ hp => hp)) le_rfl
  have h1 : Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      (.seq (asg "found" (lit 0)) (.seq (asg "done" (lit 0)) (.while (.eq (V "done") (lit 0)) searchBody)))
      (fun _ σ' => Ctx n cnt bb σ' ∧
        σ'.vars "found" = if ∃ t < Rd n ^ Dn n, AccT n cnt bb t then 1 else 0)
      (2 + (2 + (Rd n ^ Dn n * (Kturn n + 4) + 4))) := by
    have hmid : ∀ σ σ1 : Env, (Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0)) →
        σ1 = σ.setVar "found" 0 →
        ((Ctx n cnt bb σ1 ∧ σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0)) ∧ σ1.vars "found" = 0) := by
      rintro σ σ1 ⟨hC, hdg⟩ e
      rw [e]
      exact ⟨⟨hC.setVar (by decide) _, by simpa using hdg⟩, by simp⟩
    exact Spec.mono (Spec.seq hA h2 hmid (fun σ σ1 σ2 _ _ hp => hp)) le_rfl
  unfold searchCom
  refine Spec.mono h1 ?_
  unfold Ksearch; omega

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpRead` -/

section
/-!
Reading the word into `z`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem readBody_vals {B : ℕ} :
    Spec B (fun σ => σ.inp ≠ [] ∧ σ.inp.headD 0 < B ∧ σ.vars "q" + 2 < (σ.arrs "z").length ∧
        σ.vars "q" + 2 < B)
      readBody
      (fun σ σ' => σ'.inp = σ.inp.tail ∧ σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "q" + 2) (σ.inp.headD 0)) 10 := by
  run_vcg
  all_goals
    have hq : σ.vars "q" + 2 < (σ.arrs "z").length := ‹σ.vars "q" + 2 < (σ.arrs "z").length›
    have hqB : σ.vars "q" + 2 < B := ‹σ.vars "q" + 2 < B›
    have hh : σ.inp.headD 0 < B := ‹σ.inp.headD 0 < B›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | exact ⟨trivial, trivial, trivial⟩ | exact hh)

theorem tail_ne_nil' {l : List ℕ} (h : 2 ≤ l.length) : l.tail ≠ [] := by
  intro h0
  have : l.tail.length = l.length - 1 := List.length_tail
  rw [h0] at this
  simp at this
  omega

theorem ne_nil' {l : List ℕ} (h : 2 ≤ l.length) : l ≠ [] := by
  intro h0; rw [h0] at h; simp at h

theorem readHead_vals {B : ℕ} :
    Spec B (fun σ => 1 < B ∧ σ.inp.length ≥ 2 ∧ σ.inp.headD 0 < B ∧ σ.inp.tail.headD 0 < B ∧
        2 ≤ (σ.arrs "z").length ∧
        σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B)
      readHead
      (fun σ σ' => σ'.vars "N" = σ.inp.headD 0 ∧ σ'.vars "M" = σ.inp.tail.headD 0 ∧
        σ'.vars "tl" = σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 ∧
        σ'.arrs "z" = ((σ.arrs "z").set 0 (σ.inp.headD 0)).set 1 (σ.inp.tail.headD 0) ∧
        σ'.inp = σ.inp.tail.tail) 30 := by
  unfold readHead
  run_vcg
  all_goals
    have hB1 : 1 < B := ‹1 < B›
    have hlen : σ.inp.length ≥ 2 := ‹σ.inp.length ≥ 2›
    have hh : σ.inp.headD 0 < B := ‹σ.inp.headD 0 < B›
    have hh2 : σ.inp.tail.headD 0 < B := ‹σ.inp.tail.headD 0 < B›
    have hz : 2 ≤ (σ.arrs "z").length := ‹2 ≤ (σ.arrs "z").length›
    have hp : σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B :=
      ‹σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | exact ⟨trivial, trivial, trivial, trivial, trivial⟩ | assumption |
    exact ne_nil' hlen | exact tail_ne_nil' hlen |
    skip)

theorem list_eq_arrOf {x : List ℕ} {f : ℕ → ℕ} (h : ∀ c < x.length, f c = x.getD c 0) :
    arrOf x.length f = x := by
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [arrOf, List.getElem_map, List.getElem_range]
  rw [h k (by simpa using h1), List.getElem_eq_getD 0]

theorem headD_drop' (l : List ℕ) (m : ℕ) : (l.drop m).headD 0 = l.getD m 0 := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih => cases m <;> simp [ih]


/-- **The word is read into `z`.** -/
theorem readCom_spec {B : ℕ} (x : List ℕ) (hx : x.length = 2 + x.getD 1 0 * x.getD 0 0 + x.getD 1 0)
    (hxB : ∀ v ∈ x, v < B) (hlB : x.length + 1 < B) (h2 : 2 ≤ x.length) :
    Spec B (fun σ => σ.inp = x ∧ (σ.arrs "z").length = x.length)
      readCom
      (fun _ σ' => σ'.vars "N" = x.getD 0 0 ∧ σ'.vars "M" = x.getD 1 0 ∧ σ'.arrs "z" = x ∧
        σ'.inp = []) (30 + ((10 + 4) * (x.length - 2) + 6)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, x = a :: b :: rest := by
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    · exact ⟨a, b, rest, rfl⟩
  have hB1 : 1 < B := by simp at hlB; omega
  have hTL : (a :: b :: rest).length - 2 = b * a + b := by
    have := hx; simp at this ⊢; omega
  have hs := scan_spec (B := B) "q" "tl" ((a :: b :: rest).length - 2) 10 readBody
    (fun σ => σ.vars "tl" = (a :: b :: rest).length - 2 ∧
      (σ.arrs "z").length = (a :: b :: rest).length)
    (fun k σ => σ.inp = (a :: b :: rest).drop (k + 2) ∧ ∃ f, σ.arrs "z" = arrOf (a :: b :: rest).length f ∧
      ∀ c < k + 2, f c = (a :: b :: rest).getD c 0)
    (Stable.and (stable_var "tl" (fun v => v = (a :: b :: rest).length - 2) (by decide))
      (stable_len "z" (fun l => l = (a :: b :: rest).length))) (by omega) (fun σ h => h.1) ?_
  · have hH := readHead_vals (B := B)
    unfold readCom
    have hH' : Spec B (fun σ => σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length)
        readHead
        (fun σ σ' => σ'.vars "N" = a ∧ σ'.vars "M" = b ∧
          σ'.vars "tl" = (a :: b :: rest).length - 2 ∧
          σ'.arrs "z" = (((σ.arrs "z").set 0 a).set 1 b) ∧
          σ'.inp = rest) 30 := by
      refine Spec.post (Spec.pre hH ?_) ?_
      · rintro σ ⟨hin, hz⟩
        rw [hin]
        refine ⟨hB1, by simp, hxB a (by simp), hxB b (by simp), by simp at hz ⊢; omega, ?_⟩
        simp only [List.headD_cons, List.tail_cons]
        omega
      · rintro σ σ' ⟨hin, hz⟩ ⟨h1, h2, h3, h4, h5⟩
        rw [hin] at h1 h2 h3 h4 h5
        simp only [List.headD_cons, List.tail_cons] at h1 h2 h3 h4 h5
        exact ⟨h1, h2, by rw [h3, hTL], h4, h5⟩
    have hL : Spec B (fun σ => σ.vars "tl" = (a :: b :: rest).length - 2 ∧ σ.inp = rest ∧
        (∃ f, σ.arrs "z" = arrOf (a :: b :: rest).length f ∧ ∀ c < 2, f c = (a :: b :: rest).getD c 0))
        (forZ "q" "tl" readBody)
        (fun _ σ' => σ'.inp = [] ∧ σ'.arrs "z" = a :: b :: rest) ((10 + 4) * ((a :: b :: rest).length - 2) + 6) := by
      refine Spec.mono (Spec.post (Spec.pre hs ?_) ?_) (by omega)
      · rintro σ ⟨htl, hin, f, hz, hf⟩
        refine ⟨⟨by simpa using htl, by simp [hz]⟩, by simpa using hin, f, by simpa using hz, hf⟩
      · rintro σ σ' - ⟨-, ⟨hin, f, hz, hf⟩, -⟩
        refine ⟨?_, ?_⟩
        · rw [hin]; simp
        · rw [hz]; exact list_eq_arrOf fun c hc => hf c (by omega)
    have hmid : ∀ σ σ1 : Env, (σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length) →
        (σ1.vars "N" = a ∧ σ1.vars "M" = b ∧ σ1.vars "tl" = (a :: b :: rest).length - 2 ∧
          σ1.arrs "z" = (((σ.arrs "z").set 0 a).set 1 b) ∧ σ1.inp = rest) →
        (σ1.vars "tl" = (a :: b :: rest).length - 2 ∧ σ1.inp = rest ∧
          (∃ f, σ1.arrs "z" = arrOf (a :: b :: rest).length f ∧
            ∀ c < 2, f c = (a :: b :: rest).getD c 0)) := by
      rintro σ σ1 ⟨hin, hz⟩ ⟨g1, g2, g3, g4, g5⟩
      have hlen2 : 2 ≤ (σ.arrs "z").length := by rw [hz]; exact h2
      refine ⟨g3, g5, fun c => (((σ.arrs "z").set 0 a).set 1 b).getD c 0, ?_, ?_⟩
      · rw [g4]; exact eq_arrOf_of_length (by simp [hz])
      · intro c hc
        interval_cases c
        · simp [List.getD_eq_getElem?_getD, List.getElem?_set, show 0 < (σ.arrs "z").length by omega]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_set, show 1 < (σ.arrs "z").length by omega]
    have hL' := Spec.frame hL
    have hfull : Spec B (fun σ => σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length)
        (.seq readHead (forZ "q" "tl" readBody))
        (fun _ σ' => σ'.inp = [] ∧ σ'.arrs "z" = a :: b :: rest ∧ σ'.vars "N" = a ∧ σ'.vars "M" = b)
        (30 + ((10 + 4) * ((a :: b :: rest).length - 2) + 6)) := by
      refine Spec.seq hH' hL' hmid ?_
      rintro σ σ1 σ2 - ⟨h1, h2', -, -, -⟩ ⟨⟨hin, hz⟩, hv, -, -, -⟩
      exact ⟨hin, hz, by rw [hv "N" (by decide), h1], by rw [hv "M" (by decide), h2']⟩
    refine Spec.post hfull ?_
    rintro σ σ' - ⟨hin, hz, hN, hM⟩
    exact ⟨hN, hM, hz, hin⟩
  · intro k hk σ ⟨⟨htl, hzl⟩, hqk, hin, f, hz, hf⟩
    have hk' : k + 2 < (a :: b :: rest).length := by omega
    have hget : (a :: b :: rest).getD (k + 2) 0 ∈ (a :: b :: rest) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      exact List.getElem_mem hk'
    have hhead : ((a :: b :: rest).drop (k + 2)).headD 0 = (a :: b :: rest).getD (k + 2) 0 :=
      headD_drop' _ _
    obtain ⟨σ', hr, h1, h2', h3⟩ := readBody_vals (B := B) σ
      ⟨by rw [hin]; intro h; have : ((a :: b :: rest).drop (k + 2)).length = (a :: b :: rest).length - (k + 2) := List.length_drop; rw [h] at this; simp at this hk'; omega,
       by rw [hin, hhead]; exact hxB _ hget, by rw [hzl, hqk]; exact hk', by rw [hqk]; omega⟩
    refine ⟨σ', hr, by omega, ?_, ?_⟩
    · rw [h1, hin, List.tail_drop]
    · refine ⟨fun c => if c = k + 2 then (a :: b :: rest).getD (k + 2) 0 else f c, ?_, ?_⟩
      · rw [h3, hz, hqk, hin, hhead, set_arrOf]
      · intro c hc
        by_cases h : c = k + 2
        · simp [h]
        · simp only [h, if_false]; exact hf c (by omega)

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpHdr` -/

section
/-!
The header: from the counts `N` and `M` of the word, the number `n` of clients and the constants.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem nM_lt_nM {a b : ℕ} (h : a < b) : nM a < nM b := by
  unfold nM nT
  have : 2 ^ (a * a) < 2 ^ (b * b) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  omega

theorem nM_eq (n : ℕ) : nM n = 2 ^ (n * n) + n := rfl

/-- The test of the loop that finds `n`, evaluated. -/
theorem nCond_eval {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (σ : Env)
    (hM : σ.vars "M" = nM n) (hk : σ.vars "n" ≤ n) :
    ∃ v, (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).evalB B σ = some v ∧
      (v = true ↔ σ.vars "n" < n) := by
  have hkk : σ.vars "n" * σ.vars "n" ≤ n * n := Nat.mul_le_mul hk hk
  have hpow : 2 ^ (σ.vars "n" * σ.vars "n") ≤ 2 ^ (n * n) :=
    Nat.pow_le_pow_right (by norm_num) hkk
  have hBnn := hb.nn_lt
  have hBn := hb.n_lt
  have hBM := hb.nM_lt
  have hBT := hb.nT_lt
  have hB1 := hb.one_lt_B
  have hTn : nT n = 2 ^ (n * n) := rfl
  have hsum : 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" ≤ nM n := by
    rw [nM_eq]; omega
  have e1 : (Expr.mul (V "n") (V "n")).evalB B σ = some (σ.vars "n" * σ.vars "n") :=
    evalB_bin (evalB_var (by omega)) (evalB_var (by omega)) (by
      show σ.vars "n" * σ.vars "n" < B; omega)
  have e2 : (Expr.shiftl (lit 1) (.mul (V "n") (V "n"))).evalB B σ =
      some (1 * 2 ^ (σ.vars "n" * σ.vars "n")) :=
    evalB_bin (evalB_lit hB1) e1 (by
      show 1 * 2 ^ (σ.vars "n" * σ.vars "n") < B; omega)
  have e3 : (Expr.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")).evalB B σ =
      some (1 * 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n") :=
    evalB_bin e2 (evalB_var (by omega)) (by
      show 1 * 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" < B; omega)
  refine ⟨_, evalB_condLt e3 (evalB_var (by omega)), ?_⟩
  simp only [decide_eq_true_eq]
  rw [hM, one_mul]
  constructor
  · intro h
    by_contra hnk
    have : σ.vars "n" = n := by omega
    rw [this] at h
    rw [nM_eq] at h
    omega
  · intro h
    have := nM_lt_nM h
    have hk2 : nM (σ.vars "n") = 2 ^ (σ.vars "n" * σ.vars "n") + σ.vars "n" := rfl
    omega

/-- **The number of clients is found.** -/
theorem nCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "M" = nM n) nCom (fun _ σ' => σ'.vars "n" = n) (2 + (14 * n + 10)) := by
  have hloop : Spec B (fun σ => σ.vars "M" = nM n ∧ σ.vars "n" = 0)
      (.while (.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (bump "n"))
      (fun _ σ' => σ'.vars "n" = n) (14 * n + 10) := by
    refine Spec.post (Spec.while_potential (B := B)
      (b := .lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (c := bump "n")
      (fun σ => σ.vars "M" = nM n ∧ σ.vars "n" ≤ n) (fun σ => 14 * (n - σ.vars "n")) ?_ ?_
      (fun σ h => ⟨h.1, by omega⟩) ?_) ?_
    · intro σ hI
      obtain ⟨v, hv, -⟩ := nCond_eval hb σ hI.1 hI.2
      exact ⟨v, hv⟩
    · intro σ hI hcond
      obtain ⟨v, hv, hiff⟩ := nCond_eval hb σ hI.1 hI.2
      rw [hv] at hcond
      have hlt : σ.vars "n" < n := hiff.mp (Option.some.inj hcond)
      have hBn := hb.n_lt
      obtain ⟨σ', hr, e⟩ := bump_spec (B := B) "n" hb.one_lt_B σ (by omega)
      refine ⟨σ', 4, hr, ⟨by rw [e]; simpa [Env.setVar] using hI.1, by rw [e]; simp [Env.setVar]; omega⟩, ?_⟩
      rw [e]
      simp only [Env.setVar, if_true]
      have : (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).size = 9 := by
        simp
      rw [this]
      omega
    · intro σ h
      simp only [h.2, Nat.sub_zero]
      have : (Cond.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")).size = 9 := by
        simp
      rw [this]
    · rintro σ σ' - ⟨⟨hM, hk⟩, hfalse⟩
      obtain ⟨v, hv, hiff⟩ := nCond_eval hb σ' hM hk
      rw [hv] at hfalse
      have : v = false := Option.some.inj hfalse
      have : ¬ σ'.vars "n" < n := fun h => by
        have := hiff.mpr h; rw [‹v = false›] at this; simp at this
      omega
  have hA : Spec B (fun σ => σ.vars "M" = nM n) (asg "n" (lit 0)) (fun σ σ' => σ' = σ.setVar "n" 0) 2 :=
    Spec.pre (assign_lit_spec (B := B) "n" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
  unfold nCom
  exact Spec.mono (Spec.seq hA hloop (fun σ σ1 hM e => by rw [e]; exact ⟨by simpa using hM, by simp⟩)
    (fun σ σ1 σ2 _ _ hp => hp)) le_rfl

theorem h2Com_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "M" = nM n) h2Com
      (fun _ σ' => σ'.vars "nn" = n * n ∧ σ'.vars "T" = nT n ∧ σ'.vars "Z" = nZ n ∧
        σ'.vars "V" = nV n ∧ σ'.vars "np" = n + 1 ∧ σ'.vars "pw" = 1) 60 := by
  unfold h2Com
  run_vcg
  all_goals
    have hnv : σ.vars "n" = n := ‹σ.vars "n" = n›
    have hMv : σ.vars "M" = nM n := ‹σ.vars "M" = nM n›
    have hBnn := hb.nn_lt
    have hBn := hb.n_lt
    have hBM := hb.nM_lt
    have hBT := hb.nT_lt
    have hBZ := hb.nZ_lt
    have hBV := hb.nV_lt
    have hB5 := hb.five_lt_B
    have hBn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
    have hTv : nM n - n = nT n := by unfold nM; omega
    have e2 : nZ n = 2 ^ n := rfl
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hnv, hMv])
  all_goals (first | omega | (rw [hTv, one_mul, ← e2]; exact hBV) |
    exact ⟨trivial, hTv, by rw [one_mul, e2], by rw [hTv, one_mul, ← e2]; rfl, trivial, trivial⟩)

theorem pwBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "np" = n + 1 ∧ σ.vars "pw" = (n + 1) ^ σ.vars "i" ∧ σ.vars "i" < n + 1)
      (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))
      (fun σ σ' => σ'.vars "pw" = σ.vars "pw" * σ.vars "np" ∧ σ'.vars "i" = σ.vars "i" + 1) 20 := by
  run_vcg
  all_goals
    have hnp : σ.vars "np" = n + 1 := ‹σ.vars "np" = n + 1›
    have hpw : σ.vars "pw" = (n + 1) ^ σ.vars "i" := ‹σ.vars "pw" = (n + 1) ^ σ.vars "i"›
    have hi : σ.vars "i" < n + 1 := ‹σ.vars "i" < n + 1›
    have hKB := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
    have hle : (n + 1) ^ σ.vars "i" * (n + 1) ≤ (n + 1) ^ (n + 1) := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) hi
    have hK : Kn n = (n + 1) ^ (n + 1) + 1 := rfl
    have h1 : σ.vars "pw" * (n + 1) ≤ (n + 1) ^ (n + 1) := by rw [hpw]; exact hle
    have h2 : σ.vars "pw" ≤ (n + 1) ^ (n + 1) := le_trans (Nat.le_mul_of_pos_right _ (by omega)) h1
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hnp])
  all_goals (first | omega | exact ⟨trivial, trivial⟩)

theorem pwCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "np" = n + 1 ∧ σ.vars "pw" = 1) pwCom
      (fun _ σ' => σ'.vars "pw" = (n + 1) ^ (n + 1)) ((20 + 4) * (n + 1) + 6) := by
  have hn1 : n + 1 < B := hb.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
  have hs := scan_spec (B := B) "i" "np" (n + 1) 20 (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))
    (fun σ => σ.vars "np" = n + 1) (fun k σ => σ.vars "pw" = (n + 1) ^ k)
    (stable_var "np" (fun v => v = n + 1) (by decide)) hn1 (fun σ h => h) ?_
  · unfold pwCom
    refine Spec.pre (Spec.post hs ?_) ?_
    · rintro σ σ' - ⟨-, hpw, -⟩
      exact hpw
    · rintro σ ⟨hnp, hpw⟩
      exact ⟨by simpa using hnp, by simpa using hpw⟩
  · intro k hk σ ⟨hnp, hik, hpw⟩
    obtain ⟨σ', hr, h1, h2⟩ := pwBody_vals hb σ ⟨hnp, by rw [hpw, hik], by omega⟩
    refine ⟨σ', hr, by omega, ?_⟩
    rw [h1, hpw, hnp, pow_succ]

theorem h4Com_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.vars "pw" = (n + 1) ^ (n + 1) ∧ σ.vars "N" = nN n ∧ σ.vars "M" = nM n ∧
        σ.vars "nn" = n * n ∧ σ.vars "T" = nT n ∧ σ.arrs "z" = ilpWord n cnt bb) h4Com
      (fun _ σ' => σ'.vars "K" = Kn n ∧ σ'.vars "R" = Rd n ∧ σ'.vars "D" = Dn n ∧
        σ'.vars "rb" = 2 + nM n * nN n ∧ σ'.vars "tn" = 2 + nT n * nN n ∧ σ'.vars "bb" = bb) 80 := by
  unfold h4Com
  run_vcg
  all_goals
    have hpw : σ.vars "pw" = (n + 1) ^ (n + 1) := ‹σ.vars "pw" = (n + 1) ^ (n + 1)›
    have hN : σ.vars "N" = nN n := ‹σ.vars "N" = nN n›
    have hM : σ.vars "M" = nM n := ‹σ.vars "M" = nM n›
    have hnn : σ.vars "nn" = n * n := ‹σ.vars "nn" = n * n›
    have hT : σ.vars "T" = nT n := ‹σ.vars "T" = nT n›
    have hz : σ.arrs "z" = ilpWord n cnt bb := ‹σ.arrs "z" = ilpWord n cnt bb›
    have hK : Kn n = (n + 1) ^ (n + 1) + 1 := rfl
    have hBK := hb.Kn_lt
    have hBR := hb.Rd_lt
    have hBD := hb.Dn_lt
    have hBrb := hb.rb_lt
    have hBtn := hb.tn_lt
    have hBN := hb.nN_lt
    have hBM := hb.nM_lt
    have hBnn := hb.nn_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBv : bb < B := hb.lt_U (by have := hb.hbb; unfold Ub; omega)
    have hlz : (σ.arrs "z").length = zLen n := by rw [hz, ilpWord_length]
    have hTM : nT n < nM n := by unfold nM; have := hb.n1; omega
    have hzv : (σ.arrs "z").getD (2 + nM n * nN n + nT n) 0 = bb := by
      rw [hz, ilpWord_rhs n cnt bb hTM]; unfold rhs; rw [if_neg (lt_irrefl _)]
    have hidx : 2 + nM n * nN n + nT n < zLen n := by unfold zLen; omega
    have hRd : Rd n = Kn n + 1 := rfl
    have hDn : Dn n = nN n + 2 * (n * n) + 1 := rfl
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hpw, hN, hM, hnn, hT] at *)
  all_goals (first | omega | exact ⟨hK.symm, by omega, hDn.symm, trivial, trivial, hzv⟩)

/-- What the machine holds after reading the word: the counts, the word and the arrays. -/
structure Read0 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop where
  hN : σ.vars "N" = nN n
  hM : σ.vars "M" = nM n
  hz : σ.arrs "z" = ilpWord n cnt bb
  ldg : (σ.arrs "dg").length = Dn n
  lhl : (σ.arrs "hl").length = nT n
  lkd : (σ.arrs "kd").length = nN n
  lrk : (σ.arrs "rkA").length = nN n
  lsg : (σ.arrs "sg").length = nT n
  lS : (σ.arrs "S").length = n
  lwv : (σ.arrs "wv").length = nN n
  les : (σ.arrs "es").length = nT n
  lxv : (σ.arrs "xv").length = nN n

/-- **The header.** -/
theorem hdrCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Read0 n cnt bb σ) hdrCom (fun _ σ' => Ctx n cnt bb σ')
      ((2 + (14 * n + 10)) + (60 + (((20 + 4) * (n + 1) + 6) + 80))) := by
  intro σ0 h0
  obtain ⟨σ1, r1, hn1, hv1, ha1, -, -⟩ := (nCom_spec hb).frame σ0 h0.hM
  have hM1 : σ1.vars "M" = nM n := by rw [hv1 "M" (by decide)]; exact h0.hM
  obtain ⟨σ2, r2, ⟨hnn2, hT2, hZ2, hV2, hnp2, hpw2⟩, hv2, ha2, -, -⟩ :=
    (h2Com_vals hb).frame σ1 ⟨hn1, hM1⟩
  obtain ⟨σ3, r3, hpw3, hv3, ha3, -, -⟩ := (pwCom_spec hb).frame σ2 ⟨hnp2, hpw2⟩
  have hz3 : σ3.arrs "z" = ilpWord n cnt bb := by
    rw [ha3 "z" (by decide), ha2 "z" (by decide), ha1 "z" (by decide)]; exact h0.hz
  have hN3 : σ3.vars "N" = nN n := by
    rw [hv3 "N" (by decide), hv2 "N" (by decide), hv1 "N" (by decide)]; exact h0.hN
  have hM3 : σ3.vars "M" = nM n := by
    rw [hv3 "M" (by decide), hv2 "M" (by decide), hM1]
  have hnn3 : σ3.vars "nn" = n * n := by rw [hv3 "nn" (by decide)]; exact hnn2
  have hT3 : σ3.vars "T" = nT n := by rw [hv3 "T" (by decide)]; exact hT2
  obtain ⟨σ4, r4, ⟨hK4, hR4, hD4, hrb4, htn4, hbb4⟩, hv4, ha4, -, -⟩ :=
    (h4Com_vals hb).frame σ3 ⟨hpw3, hN3, hM3, hnn3, hT3, hz3⟩
  refine ⟨σ4, ?_, ?_⟩
  · exact Run.mono (r1.seq (r2.seq (r3.seq r4))) (by omega)
  · have hlen : ∀ a, (σ4.arrs a).length = (σ0.arrs a).length := fun a => by
      rw [run_len_arrs r4 a, run_len_arrs r3 a, run_len_arrs r2 a, run_len_arrs r1 a]
    refine
      { hN := ?_, hM := ?_, hn := ?_, hT := ?_, hZ := ?_, hV := ?_, hK := hK4, hR := hR4, hD := hD4,
        hrb := hrb4, htn := htn4, hnn := ?_, hbb := hbb4, hz := ?_, ldg := ?_, lhl := ?_, lkd := ?_,
        lrk := ?_, lsg := ?_, lS := ?_, lwv := ?_, les := ?_, lxv := ?_ }
    · rw [hv4 "N" (by decide)]; exact hN3
    · rw [hv4 "M" (by decide)]; exact hM3
    · rw [hv4 "n" (by decide), hv3 "n" (by decide), hv2 "n" (by decide)]; exact hn1
    · rw [hv4 "T" (by decide)]; exact hT3
    · rw [hv4 "Z" (by decide), hv3 "Z" (by decide)]; exact hZ2
    · rw [hv4 "V" (by decide), hv3 "V" (by decide)]; exact hV2
    · rw [hv4 "nn" (by decide)]; exact hnn3
    · rw [ha4 "z" (by decide)]; exact hz3
    · rw [hlen]; exact h0.ldg
    · rw [hlen]; exact h0.lhl
    · rw [hlen]; exact h0.lkd
    · rw [hlen]; exact h0.lrk
    · rw [hlen]; exact h0.lsg
    · rw [hlen]; exact h0.lS
    · rw [hlen]; exact h0.lwv
    · rw [hlen]; exact h0.les
    · rw [hlen]; exact h0.lxv

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpMain` -/

section
/-!
The whole solver: read the word, then either solve the program `a x = b` or search.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The cost of the big branch. -/
def Kbig (n : ℕ) : ℕ :=
  ((2 + (14 * n + 10)) + (60 + (((20 + 4) * (n + 1) + 6) + 80))) + Ksearch n + 3

theorem writeFound_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.out = [] ∧ σ.vars "found" ≤ 1) (.write (V "found"))
      (fun σ σ' => σ'.out = [σ.vars "found"]) 3 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hf : σ.vars "found" ≤ 1 := ‹σ.vars "found" ≤ 1›
    have ho : σ.out = [] := ‹σ.out = []›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (rw [ho]; rfl))

/-- **The big branch.** -/
theorem bigCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Read0 n cnt bb σ ∧ σ.out = [] ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      bigCom
      (fun _ σ' => σ'.out = [if (decodeILP (ilpWord n cnt bb)).Feasible then 1 else 0])
      (Kbig n) := by
  intro σ0 ⟨h0, hout0, hdg0⟩
  obtain ⟨σ1, r1, hC1, hv1, ha1, -, hout1⟩ := (hdrCom_spec hb).frame σ0 h0
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0) := by rw [ha1 "dg" (by decide)]; exact hdg0
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; exact hout0
  obtain ⟨σ2, r2, ⟨hC2, hfound2⟩, hv2, ha2, -, hout2⟩ := (searchCom_spec hb).frame σ1 ⟨hC1, hdg1⟩
  have hout2' : σ2.out = [] := by rw [hout2 (by decide)]; exact hout1'
  have hf2 : σ2.vars "found" ≤ 1 := by rw [hfound2]; split_ifs <;> omega
  obtain ⟨σ3, r3, hout3⟩ := writeFound_vals hb σ2 ⟨hout2', hf2⟩
  refine ⟨σ3, Run.mono (r1.seq (r2.seq r3)) ?_, ?_⟩
  · unfold Kbig; omega
  · show σ3.out = _
    rw [hout3, hfound2]
    have hiff := feasible_iff_accT n cnt bb
    congr 1
    by_cases hF : (decodeILP (ilpWord n cnt bb)).Feasible
    · rw [if_pos (hiff.mp hF), if_pos hF]
    · rw [if_neg (fun h => hF (hiff.mpr h)), if_neg hF]

theorem dvd_iff_sub' (a b : ℕ) : b - b / a * a = 0 ↔ (0 < a → a ∣ b) ∧ (a = 0 → b = 0) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have h1 := Nat.div_add_mod' b a
    have h2 : a ∣ b ↔ b % a = 0 := Nat.dvd_iff_mod_eq_zero
    constructor
    · intro h
      refine ⟨fun _ => h2.mpr (by omega), fun h0 => absurd h0 ha⟩
    · rintro ⟨h, -⟩
      have := h2.mp (h (Nat.pos_of_ne_zero ha))
      omega

theorem smallP_iff (a b : ℕ) :
    ((a = 0 → b = 0) ∧ (0 < a → a ∣ b)) ↔ (if a = 0 then b = 0 else b - b / a * a = 0) := by
  by_cases ha : a = 0
  · subst ha; simp
  · rw [if_neg ha]
    have := dvd_iff_sub' a b
    constructor
    · intro h; exact this.mpr ⟨h.2, h.1⟩
    · intro h; exact ⟨(this.mp h).2, (this.mp h).1⟩

/-- **The small branch**: the program `a x = b`. -/
theorem smallCom_spec {B : ℕ} (a0 b0 : ℕ) (ha : a0 < B) (hb : b0 < B) (hB : 5 < B) :
    Spec B (fun σ => σ.arrs "z" = [1, 1, a0, b0] ∧ σ.out = []) smallCom
      (fun _ σ' => σ'.out = [if (a0 = 0 → b0 = 0) ∧ (0 < a0 → a0 ∣ b0) then 1 else 0]) 30 := by
  unfold smallCom
  run_vcg
  all_goals
    have hz : σ.arrs "z" = [1, 1, a0, b0] := ‹σ.arrs "z" = [1, 1, a0, b0]›
    have ho : σ.out = [] := ‹σ.out = []›
    have g2 : [1, 1, a0, b0].getD 2 0 = a0 := rfl
    have g3 : [1, 1, a0, b0].getD 3 0 = b0 := rfl
    have hl : [1, 1, a0, b0].length = 4 := rfl
    have hdiv : b0 / a0 * a0 ≤ b0 := Nat.div_mul_le_self _ _
    have hdiv2 : b0 / a0 ≤ b0 := Nat.div_le_self _ _
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hz, ho] at *)
  all_goals (try simp only [g2, g3, hl] at *)
  all_goals (try simp only [List.nil_append])
  all_goals (first | omega | (refine congrArg (fun x => [x]) ?_; split_ifs with hP <;>
    first | rfl | (exfalso; have := (smallP_iff a0 b0).mp hP; simp_all) |
      (exfalso; apply hP; rw [smallP_iff]; simp_all)))

/-- The lengths of the arrays. -/
def extI (n len : ℕ) (a : String) : ℕ :=
  if a = "z" then len else if a = "dg" then Dn n else if a = "S" then n else
  if a = "hl" ∨ a = "sg" ∨ a = "es" then nT n else
  if a = "kd" ∨ a = "rkA" ∨ a = "wv" ∨ a = "xv" then nN n else 0

theorem ilpWord_zero (cnt : ℕ → ℕ) (bb : ℕ) : ilpWord 0 cnt bb = [1, 1, 1, cnt 0] := by
  rfl


theorem two_le_nN {n : ℕ} (hn : 1 ≤ n) : 2 ≤ nN n := by
  have h1 := nT_le_nN n
  have h2 : 2 ≤ nT n := by
    unfold nT
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

/-- The cost of the whole solver on a word of the family with `n ≥ 1` clients. -/
def Kfam (n : ℕ) : ℕ := (30 + ((10 + 4) * (zLen n - 2) + 6)) + (4 + Kbig n)

theorem readInit {x : List ℕ} {ext : String → ℕ} (hz : ext "z" = x.length) :
    (initEnv ext x).inp = x ∧ ((initEnv ext x).arrs "z").length = x.length := by
  refine ⟨rfl, ?_⟩
  simp [initEnv, hz]

/-- **The solver on a word of the family with `n ≥ 1` clients.** -/
theorem ilpFamily_run {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B)
    (hxle : ∀ v ∈ ilpWord n cnt bb, v ≤ vb) :
    ∃ σ', Run B ilpCom (initEnv (extI n (zLen n)) (ilpWord n cnt bb)) σ' (Kfam n) ∧
      σ'.out = [if (decodeILP (ilpWord n cnt bb)).Feasible then 1 else 0] := by
  set x := ilpWord n cnt bb with hxdef
  have hlen : x.length = zLen n := ilpWord_length n cnt bb
  have h0 : x.getD 0 0 = nN n := by
    rw [hxdef, ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
  have h1 : x.getD 1 0 = nM n := by
    rw [hxdef, ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
  have hx : x.length = 2 + x.getD 1 0 * x.getD 0 0 + x.getD 1 0 := by
    rw [h0, h1, hlen]; unfold zLen; ring
  have hxB : ∀ v ∈ x, v < B := fun v hv => hb.lt_U (by
    have := hxle v hv; unfold Ub; omega)
  have hlB : x.length + 1 < B := hb.lt_U (by rw [hlen]; unfold Ub; omega)
  have h2 : 2 ≤ x.length := by rw [hlen]; have := zLen_ge n; omega
  obtain ⟨σ1, r1, ⟨hN1, hM1, hz1, hin1⟩, hv1, ha1, -, hout1⟩ :=
    (readCom_spec x hx hxB hlB h2).frame (initEnv (extI n (zLen n)) x)
      (readInit (by simp [extI, hlen]))
  have hN1' : σ1.vars "N" = nN n := by rw [hN1, h0]
  have hM1' : σ1.vars "M" = nM n := by rw [hM1, h1]
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; rfl
  have hlens : ∀ a, (σ1.arrs a).length = ((initEnv (extI n (zLen n)) x).arrs a).length := by
    intro a; exact run_len_arrs r1 a
  have hread : Read0 n cnt bb σ1 :=
    { hN := hN1', hM := hM1', hz := by rw [hz1],
      ldg := by rw [hlens]; simp [initEnv, extI],
      lhl := by rw [hlens]; simp [initEnv, extI],
      lkd := by rw [hlens]; simp [initEnv, extI],
      lrk := by rw [hlens]; simp [initEnv, extI],
      lsg := by rw [hlens]; simp [initEnv, extI],
      lS := by rw [hlens]; simp [initEnv, extI],
      lwv := by rw [hlens]; simp [initEnv, extI],
      les := by rw [hlens]; simp [initEnv, extI],
      lxv := by rw [hlens]; simp [initEnv, extI] }
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0) := by
    rw [ha1 "dg" (by decide)]
    simp only [initEnv, extI]
    simpa using replicate_eq_arrOf (Dn n) 0
  obtain ⟨σ2, r2, hout2⟩ := bigCom_spec hb σ1 ⟨hread, hout1', hdg1⟩
  have hn2 : 2 ≤ nN n := two_le_nN hb.n1
  have hBN := hb.nN_lt
  have hB1 := hb.one_lt_B
  have hcond : (Cond.eq (V "N") (lit 1)).evalB B σ1 = some false := by
    have := evalB_condEq (evalB_var (B := B) (σ := σ1) (x := "N") (by rw [hN1']; exact hBN))
      (evalB_lit (B := B) (n := 1) (σ := σ1) hB1)
    rw [this, hN1']
    simp
    omega
  refine ⟨σ2, ?_, hout2⟩
  refine Run.mono (show Run B (.seq readCom (.ite (Cond.eq (V "N") (lit 1)) smallCom bigCom)) _ σ2 _ from
    r1.seq (Run.ite_false hcond r2)) ?_
  unfold Kfam
  simp
  omega

/-- **The solver on a word `[1, 1, a, b]`.** -/
theorem ilpSmall_run {B : ℕ} (a0 b0 : ℕ) (ha : a0 < B) (hb : b0 < B) (hB : 5 < B) :
    ∃ σ', Run B ilpCom (initEnv (extI 0 4) [1, 1, a0, b0]) σ' 100 ∧
      σ'.out = [if (a0 = 0 → b0 = 0) ∧ (0 < a0 → a0 ∣ b0) then 1 else 0] := by
  have hx : ([1, 1, a0, b0] : List ℕ).length = 2 +
      ([1, 1, a0, b0] : List ℕ).getD 1 0 * ([1, 1, a0, b0] : List ℕ).getD 0 0 +
      ([1, 1, a0, b0] : List ℕ).getD 1 0 := rfl
  have hxB : ∀ v ∈ ([1, 1, a0, b0] : List ℕ), v < B := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> first | omega | assumption
  have hlB : ([1, 1, a0, b0] : List ℕ).length + 1 < B := by
    simp; omega
  obtain ⟨σ1, r1, ⟨hN1, hM1, hz1, hin1⟩, hv1, ha1, -, hout1⟩ :=
    (readCom_spec [1, 1, a0, b0] hx hxB hlB (by simp)).frame (initEnv (extI 0 4) [1, 1, a0, b0])
      (readInit (by simp [extI]))
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; rfl
  obtain ⟨σ2, r2, hout2⟩ := smallCom_spec (B := B) a0 b0 ha hb hB σ1 ⟨hz1, hout1'⟩
  have hcond : (Cond.eq (V "N") (lit 1)).evalB B σ1 = some true := by
    have := evalB_condEq (evalB_var (B := B) (σ := σ1) (x := "N") (by rw [hN1]; simp; omega))
      (evalB_lit (B := B) (n := 1) (σ := σ1) (by omega))
    rw [this, hN1]
    simp
  refine ⟨σ2, ?_, hout2⟩
  refine Run.mono (show Run B (.seq readCom (.ite (Cond.eq (V "N") (lit 1)) smallCom bigCom)) _ σ2 _ from
    r1.seq (Run.ite_true hcond r2)) ?_
  simp

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpLayout` -/

section
/-!
The layout of the solver.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax117284Proofs.Machine.ClMain (cS cA cD com_ok)

/-- The arrays of the solver. -/
def ilpArrs : List String := ["z", "dg", "hl", "kd", "rkA", "sg", "S", "wv", "es", "xv"]

/-- The layout of the solver: the scalars it mentions, its ten arrays, twelve temporaries. -/
def layoutI : Layout := ⟨(cS ilpCom).dedup, ilpArrs, 12⟩

theorem ilp_arrays : ∀ a ∈ cA ilpCom, a ∈ ilpArrs := by decide +kernel

theorem ilp_depth : cD ilpCom ≤ 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem layoutI_ok : Com.Ok layoutI ilpCom :=
  com_ok layoutI ilpCom (fun y h => List.mem_dedup.mpr h) ilp_arrays ilp_depth

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpFinal` -/

section
/-!
The solver solves the integer programs of the family within the word RAM cost model.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The largest entry of a word. -/
def mxl (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mxl {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mxl x := by
  induction x with
  | nil => simp at h
  | cons a l ih =>
    simp only [mxl, List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

theorem mxl_mem {x : List ℕ} (h : x ≠ []) : mxl x ∈ x := by
  induction x with
  | nil => exact absurd rfl h
  | cons a l ih =>
    simp only [mxl, List.foldr_cons]
    by_cases hl : l = []
    · subst hl; simp
    · have := ih hl
      rcases le_total a (l.foldr max 0) with h1 | h1
      · rw [max_eq_right h1]; exact List.mem_cons_of_mem _ this
      · rw [max_eq_left h1]; exact List.mem_cons_self

/-- The bound of the machine. -/
def Bx (x : List ℕ) : ℕ := (x.length + mxl x + 1) ^ 17 + 1

/-- The cost of the solver on a word with `N` variables. -/
def Kx' (N : ℕ) : ℕ := 100 + ∑ m ∈ range (N + 1), Kfam m

/-- The cost of the solver. -/
def Kx (x : List ℕ) : ℕ := Kx' (x.getD 0 0)

/-- What the solver answers. -/
def fAns (x : List ℕ) : List ℕ :=
  if (Lax117284.IlpClients.decodeILP x).Feasible then [1] else [0]

theorem lt_Bx {x : List ℕ} {v : ℕ} (h : v ∈ x) : v < Bx x := by
  have h1 := le_mxl h
  have h2 : 1 ≤ x.length + mxl x + 1 := by omega
  have h3 : x.length + mxl x + 1 ≤ (x.length + mxl x + 1) ^ 17 := by
    calc x.length + mxl x + 1 = (x.length + mxl x + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h2 (by omega)
  unfold Bx; omega

theorem five_lt_Bx {x : List ℕ} (h : 5 ≤ x.length + 1) : 5 < Bx x := by
  have h2 : 1 ≤ x.length + mxl x + 1 := by omega
  have h3 : x.length + mxl x + 1 ≤ (x.length + mxl x + 1) ^ 17 := by
    calc x.length + mxl x + 1 = (x.length + mxl x + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right h2 (by omega)
  unfold Bx; omega

theorem getD_mem' (l : List ℕ) (i : ℕ) (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem hyp_of_family (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (hn : 1 ≤ n) :
    Hyp n cnt bb (mxl (ilpWord n cnt bb)) (Bx (ilpWord n cnt bb)) := by
  have hlen := ilpWord_length n cnt bb
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro t ht
    have hM : t < nM n := by unfold nM; omega
    have := ilpWord_rhs n cnt bb hM
    have hi : 2 + nM n * nN n + t < (ilpWord n cnt bb).length := by rw [hlen]; unfold zLen; omega
    have hm := le_mxl (getD_mem' _ _ hi)
    rw [this] at hm
    unfold rhs at hm
    rwa [if_pos ht] at hm
  · have hT : nT n < nM n := by unfold nM; omega
    have := ilpWord_rhs n cnt bb hT
    have hi : 2 + nM n * nN n + nT n < (ilpWord n cnt bb).length := by rw [hlen]; unfold zLen; omega
    have hm := le_mxl (getD_mem' _ _ hi)
    rw [this] at hm
    unfold rhs at hm
    rwa [if_neg (lt_irrefl _)] at hm
  · unfold Ub Bx
    rw [hlen]; omega

theorem n_le_nN (n : ℕ) : n ≤ nN n := by unfold nN; omega

theorem Kfam_le_Kx' (n N : ℕ) (h : n ≤ N) : Kfam n ≤ Kx' N := by
  unfold Kx'
  have : Kfam n ≤ ∑ m ∈ range (N + 1), Kfam m :=
    Finset.single_le_sum (f := Kfam) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  omega

theorem fAns_of_iff (x : List ℕ) (P : Prop) [Decidable P]
    (h : (Lax117284.IlpClients.decodeILP x).Feasible ↔ P) : [if P then 1 else 0] = fAns x := by
  unfold fAns
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.mpr hP)]
  · rw [if_neg hP, if_neg (fun hf => hP (h.mp hf))]

theorem feasible_small (a b : ℕ) :
    (Lax117284.IlpClients.decodeILP [1, 1, a, b]).Feasible ↔ (a = 0 → b = 0) ∧ (0 < a → a ∣ b) :=
  feasible_one_by_one a b

/-- **The solver runs on every word of the domain.** -/
theorem ilp_run {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (Bx x) ilpCom (initEnv ext x) σ' (Kx x) ∧
      σ'.out = fAns x := by
  rcases hx with ⟨n, cnt, bb, hxe⟩ | hxe
  · have hxe' : x = ilpWord n cnt bb := by
      rw [hxe]; exact (IlpClientsBridge.ilpWord_eq n cnt bb)
    subst hxe'
    by_cases hn : n = 0
    · subst hn
      rw [ilpWord_zero]
      have hmem : ∀ v ∈ ([1, 1, 1, cnt 0] : List ℕ), v < Bx [1, 1, 1, cnt 0] := fun v hv => lt_Bx hv
      have h5 : 5 < Bx [1, 1, 1, cnt 0] := five_lt_Bx (by simp)
      obtain ⟨σ', hr, hout⟩ := ilpSmall_run (B := Bx [1, 1, 1, cnt 0]) 1 (cnt 0) (hmem 1 (by simp))
        (hmem (cnt 0) (by simp)) h5
      refine ⟨extI 0 4, σ', hr.mono (by unfold Kx Kx'; simp), ?_⟩
      rw [hout]
      exact fAns_of_iff _ _ (feasible_small 1 (cnt 0))
    · have hn1 : 1 ≤ n := by omega
      have hb := hyp_of_family n cnt bb hn1
      have hxle : ∀ v ∈ ilpWord n cnt bb, v ≤ mxl (ilpWord n cnt bb) := fun v hv => le_mxl hv
      obtain ⟨σ', hr, hout⟩ := ilpFamily_run hb hxle
      have hlen := ilpWord_length n cnt bb
      have h0 : (ilpWord n cnt bb).getD 0 0 = nN n := by
        rw [ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
      refine ⟨extI n (zLen n), σ', hr.mono ?_, ?_⟩
      · unfold Kx
        rw [h0]
        exact Kfam_le_Kx' n (nN n) (n_le_nN n)
      · rw [hout]
        exact fAns_of_iff _ _ (IlpClientsBridge.feasible_iff _)
  · subst hxe
    have hmem : ∀ v ∈ ([1, 1, 0, 1] : List ℕ), v < Bx [1, 1, 0, 1] := fun v hv => lt_Bx hv
    have h5 : 5 < Bx [1, 1, 0, 1] := five_lt_Bx (by simp)
    obtain ⟨σ', hr, hout⟩ := ilpSmall_run (B := Bx [1, 1, 0, 1]) 0 1 (hmem 0 (by simp))
      (hmem 1 (by simp)) h5
    refine ⟨extI 0 4, σ', hr.mono (by unfold Kx Kx'; simp), ?_⟩
    rw [hout]
    exact fAns_of_iff _ _ (feasible_small 0 1)

theorem ilp_solves : Solves layoutI ilpCom Lax117284.IlpClients.ilpClients.Domain fAns Bx Kx where
  ok := layoutI_ok
  inp := fun x _ v hv => lt_Bx hv
  run := fun x hx => ilp_run hx

/-- The scalars of the layout. -/
def SI : ℕ := layoutI.scalars.length

/-- The constant of the solver. -/
def cI : ℕ := 30 + SI

/-- The function of the parameter. -/
def gI (N : ℕ) : ℕ := 10 * Kx' N + 1

theorem domain_len_ge {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) : 4 ≤ x.length := by
  rcases hx with ⟨n, cnt, bb, hxe⟩ | hxe
  · have h' : x = ilpWord n cnt bb := by rw [hxe]; exact (IlpClientsBridge.ilpWord_eq n cnt bb)
    rw [h', ilpWord_length]; exact zLen_ge n
  · rw [hxe]; simp

theorem domain_ne_nil {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) : x ≠ [] := by
  intro h
  have := domain_len_ge hx
  rw [h] at this; simp at this

set_option maxRecDepth 100000 in
theorem fits_layout {x : List ℕ} {w : ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain)
    (hf : Lax117284.ParameterizedComplexity.Fits cI w x) : layoutI.FitsWords (Bx x) w := by
  have hne := domain_ne_nil hx
  have h4 := domain_len_ge hx
  have h1 := hf _ (mxl_mem hne)
  have hspan : layoutI.span (Bx x) = 12 + 2 + SI + 10 * Bx x := by
    have ha : layoutI.arrays.length = 10 := rfl
    have ht : layoutI.temps = 12 := rfl
    unfold Layout.span
    rw [ha, ht]
    rfl
  have hB : Bx x = (x.length + mxl x + 1) ^ 17 + 1 := rfl
  obtain ⟨U, hU⟩ : ∃ U, U = x.length + mxl x + 1 := ⟨_, rfl⟩
  rw [← hU] at h1 hB
  have hU5 : 5 ≤ U := by omega
  have hpow : U ^ 17 ≤ U ^ cI := Nat.pow_le_pow_right (by omega) (by unfold cI; omega)
  obtain ⟨P, hP⟩ : ∃ P, P = U ^ 17 := ⟨_, rfl⟩
  have hP5 : 5 ≤ P := by
    rw [hP]
    calc 5 ≤ U := hU5
      _ = U ^ 1 := (pow_one _).symm
      _ ≤ U ^ 17 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [← hP] at hB hpow
  have h2 : cI * P ≤ cI * U ^ cI := Nat.mul_le_mul_left _ hpow
  have h3 : 24 + SI + 10 * P ≤ cI * P := by
    unfold cI
    nlinarith
  refine fitsWords_of_max_le (by rw [hB]; omega) ?_
  rw [max_le_iff]
  constructor
  · rw [hB]; omega
  · rw [hspan, hB]; omega

theorem time_bound {x : List ℕ} (hx : x ∈ Lax117284.IlpClients.ilpClients.Domain) :
    (10 : ℕ) * Kx x + 1 ≤ cI * gI (x.getD 0 0) * (x.length + 1) ^ cI := by
  have h1 : 1 ≤ (x.length + 1) ^ cI := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ cI := by unfold cI; omega
  have : gI (x.getD 0 0) = 10 * Kx x + 1 := rfl
  rw [← this]
  calc gI (x.getD 0 0) ≤ cI * gI (x.getD 0 0) := Nat.le_mul_of_pos_left _ h2
    _ ≤ cI * gI (x.getD 0 0) * (x.length + 1) ^ cI := Nat.le_mul_of_pos_right _ h1

/--
---
conclusion: Lax117284.IlpClients.ilpClients_fpt
---
The integer programs of the family are solved by a word RAM program that reads the word, with `N`
variables and `M` constraints, and decides at once whether it is the program `a x = b` of one variable
(the fixed word `[1, 1, 0, 1]` and the program of no client), which it solves by a division. Otherwise
it finds the number `n` of clients from `M`, and enumerates all the numbers below `(K + 1) ^ D`, where
`K = (n + 1) ^ (n + 1) + 1` and `D = N + 2 n² + 1`, by an odometer whose digits are the entries of a
certificate: a digit for every variable, the two matrices of an integer left inverse of the
difference vectors of the large variables, and a common denominator. For every certificate it
decodes a candidate solution (sums of the small digits per type, the base of each type, the values of
the extras by the integer left inverse, the values of the bases by what is left of the demand of the
type) and tests it against the program stored in the word, row by row. The program is feasible if and
only if some certificate is accepted, by the completeness of the certificates (the shifting lemma,
the kernel bound of the family by Siegel's lemma, the bound `n` on the number of extras) and the
soundness of the test. Every number is at most a fixed power of the length of the word plus its largest
entry, so the running time is a function of the number of variables alone times a constant.
-/
theorem ilpClients_fpt_proved : Lax117284.ParameterizedComplexity.FPT Lax117284.IlpClients.ilpClients := by
  refine ⟨compileProgram layoutI ilpCom, cI, gI, fun w => ?_⟩
  have hs : Solves layoutI ilpCom
      {x | x ∈ Lax117284.IlpClients.ilpClients.Domain ∧ Lax117284.ParameterizedComplexity.Fits cI w x}
      fAns Bx Kx :=
    ⟨ilp_solves.ok, fun x hx => ilp_solves.inp x hx.1, fun x hx => ilp_solves.run x hx.1⟩
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hx, hf⟩
    exact fits_layout hx hf
  · rintro x ⟨hx, hf⟩
    exact time_bound hx

end

end Lax117284Proofs.Machine.Ilp

example : type_of% @Lax117284.IlpClients.ilpClients_fpt := Lax117284Proofs.Machine.Ilp.ilpClients_fpt_proved

end
