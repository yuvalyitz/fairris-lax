import Lax117284Proofs.Machine.TwMain1

/-!
The main program, phase by phase: the reading and the preparation.
-/

namespace Lax117284Proofs.Machine.TwMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding

variable {B : ℕ}

/-- **What is known of an environment**: the arrays outside `T` are the zeros the machine started
with, and the scalars outside `V0` are zero. -/
structure W (ext : String → ℕ) (T V0 : List String) (σ : Env) : Prop where
  arrs : ∀ a, a ∉ T → σ.arrs a = List.replicate (ext a) 0
  vars : ∀ v, v ∉ V0 → σ.vars v = 0

/-- The scalars the reading writes. -/
def VR : List String := ["n", "m", "L", "rt", "k", "rv"]

theorem phaseR {x : List ℕ} {I : Instance} {k : ℕ} (hdec : EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) (ext : String → ℕ) (hext : ext "X" = x.length)
    (σ0 : Env) (hin : σ0.inp = x) (hout : σ0.out = []) (hW : W ext [] [] σ0) :
    ∃ σ1, Run B ClMain.readCom σ0 σ1 (24 * x.length + 60) ∧ ClBuild.Ctx0 I x k σ1 ∧
      σ1.vars "L" = x.length ∧ σ1.inp = [] ∧ σ1.out = [] ∧ W ext ["X"] VR σ1 := by
  obtain ⟨σ1, r, hC, hLv, hi, ho, hA, hV⟩ := ClMain.readCom_spec hdec hL hX σ0
    ⟨hin, hout, by rw [hW.arrs "X" (by simp), hext]; simp⟩
  refine ⟨σ1, r, hC, hLv, hi, ho, ⟨fun a ha => ?_, fun v hv => ?_⟩⟩
  · have : a ≠ "X" := by simpa using ha
    rw [hA a this, hW.arrs a (by simp)]
  · have hv' : v ∉ ["n", "m", "L", "rt", "k", "rv"] := hv
    rw [hV v hv', hW.vars v (by simp)]

/-- What the preparation costs. -/
def Kprep (L lg : ℕ) : ℕ :=
  40 + ((20 + 10 + 4) * L + 6) + 20 + ((40 + 10 + 4) * (lg + 1) + 6) + 100

theorem phaseP (cc plit : ℕ) (hcc : 1 ≤ cc) {x : List ℕ} {I : Instance} {k : ℕ}
    (σ1 : Env) (hn : σ1.vars "n" = I.clients) (hm : σ1.vars "m" = I.days)
    (hLv : σ1.vars "L" = x.length) (hL0 : 0 < x.length)
    (hmn : I.days * I.clients + 8 < B) (hnB : I.clients + 8 < B) (hmB : I.days + 8 < B)
    (hLB : x.length + 8 < B)
    (hge : TwPrep.geE cc I.days (Nat.log 2 x.length) + 8 < B) (hccB : 2 * cc + 8 < B)
    (hplB : plit + 8 < B)
    (hwp : (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit + 8 < B)
    (hP : 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) + 8 < B) :
    ∃ σ2, Run B (TwPrep.prepCom cc plit) σ1 σ2 (Kprep x.length (Nat.log 2 x.length)) ∧
      σ2.vars "mn" = I.days * I.clients ∧ σ2.vars "lg" = Nat.log 2 x.length ∧
      σ2.vars "wc" = TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧
      σ2.vars "ok" = (if 0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days
        then 1 else 0) ∧
      σ2.vars "w" = TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1 ∧
      σ2.vars "wp" = (2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit ∧
      σ2.vars "P" = 2 ^ ((2 * cc + 1) * Nat.log 2 x.length + 4 * cc + plit) ∧
      (∀ v, v ∉ TwPrep.SPrep → σ2.vars v = σ1.vars v) ∧ σ2.arrs = σ1.arrs ∧
      σ2.out = σ1.out := by
  have hlgL : Nat.log 2 x.length ≤ x.length := Nat.log_le_self 2 _
  obtain ⟨hw1, hw2, hw3⟩ := TwPrep.wcnt_spec hcc I.days (Nat.log 2 x.length)
  obtain ⟨σa, ra, ea⟩ := TwPrep.prepPre_run (B := B) σ1 I.clients I.days hn hm (by omega) (by omega)
    (by omega)
  have hva : ∀ v, v ≠ "mn" → v ≠ "lg" → σa.vars v = σ1.vars v := by
    intro v h1 h2; rw [ea]; simp [Env.setVar, h1, h2]
  have hLa : σa.vars "L" = x.length := by rw [hva "L" (by decide) (by decide), hLv]
  have hlga : σa.vars "lg" = 0 := by rw [ea]; simp [Env.setVar]
  obtain ⟨σb, rb, hlgb, Ab, ob⟩ := TwPrep.lgLoop_run (B := B) σa x.length hL0 hLa (by omega) hlga
  have hvb : ∀ v, v ∉ ["j", "lg"] → σb.vars v = σa.vars v := Ab.2
  obtain ⟨σc, rc, ec⟩ := TwPrep.prepMid_run (B := B) σb (Nat.log 2 x.length) hlgb (by omega)
  have hvc : ∀ v, v ≠ "lg1" → v ≠ "wc" → σc.vars v = σb.vars v := by
    intro v h1 h2; rw [ec]; simp [Env.setVar, h1, h2]
  have hmc : σc.vars "m" = I.days := by
    rw [hvc "m" (by decide) (by decide), hvb "m" (by decide), hva "m" (by decide) (by decide), hm]
  have hlg1c : σc.vars "lg1" = Nat.log 2 x.length + 1 := by rw [ec]; simp [Env.setVar]
  have hwcc : σc.vars "wc" = 0 := by rw [ec]; simp [Env.setVar]
  obtain ⟨σd, rd, hwcd, Ad, od⟩ := TwPrep.wcLoop_run (B := B) cc σc I.days (Nat.log 2 x.length) hcc
    (by omega) hmc hlg1c hwcc (by omega) (by omega)
  have hvd : ∀ v, v ∉ ["j", "wc"] → σd.vars v = σc.vars v := Ad.2
  have hme : σd.vars "m" = I.days := by rw [hvd "m" (by decide), hmc]
  have hlgd : σd.vars "lg" = Nat.log 2 x.length := by
    rw [hvd "lg" (by decide), hvc "lg" (by decide) (by decide), hlgb]
  obtain ⟨σe, re, hok, hw, hwp', hP', Ae, oe⟩ := TwPrep.prepPost_run (B := B) cc plit σd
    (TwPrep.wcnt cc I.days (Nat.log 2 x.length)) I.days (Nat.log 2 x.length) hwcd hme hlgd
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨σe, ?_, ?_, ?_, ?_, hok, hw, hwp', hP', ?_, ?_, ?_⟩
  · have := ra.seq (rb.seq (rc.seq (rd.seq re)))
    exact this.mono (by unfold Kprep; omega)
  · rw [Ae.2 "mn" (by simp), hvd "mn" (by decide), hvc "mn" (by decide) (by decide),
      hvb "mn" (by decide), ea]; simp [Env.setVar]
  · rw [Ae.2 "lg" (by simp), hlgd]
  · rw [Ae.2 "wc" (by simp), hwcd]
  · intro v hv
    have h1 : v ∉ ["ok", "w", "wp", "P"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h2 : v ∉ ["j", "wc"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h3 : v ∉ ["j", "lg"] := fun h => hv (by
      simp only [TwPrep.SPrep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have h4 : v ≠ "lg1" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h5 : v ≠ "wc" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h6 : v ≠ "mn" := fun h => hv (by simp [TwPrep.SPrep, h])
    have h7 : v ≠ "lg" := fun h => hv (by simp [TwPrep.SPrep, h])
    rw [Ae.2 v h1, hvd v h2, hvc v h4 h5, hvb v h3, hva v h6 h7]
  · rw [Ae.1, Ad.1, show σc.arrs = σb.arrs by rw [ec]; simp [Env.setVar], Ab.1,
      show σa.arrs = σ1.arrs by rw [ea]; simp [Env.setVar]]
  · rw [oe, od, show σc.out = σb.out by rw [ec]; simp [Env.setVar], ob,
      show σa.out = σ1.out by rw [ea]; simp [Env.setVar]]

end Lax117284Proofs.Machine.TwMain
