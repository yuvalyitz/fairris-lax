import Lax117284Proofs.Machine.IlpCk

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
