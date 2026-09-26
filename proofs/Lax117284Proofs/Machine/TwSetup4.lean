import Lax117284Proofs.Machine.TwSetup3

/-!
The interpreter phase: load the code, set the constants, run the loop.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Cst InitEnv loopCom interp_run Small)

variable {B : ℕ}

/-- The constants the interpreter reads and the run flag. -/
def initCom (plen : ℕ) : Com := seqs
  [ .assign "run" (Expr.lit 1),
    .assign "ylen" (add (mul (V "n") (V "n")) (Expr.lit 2)),
    .assign "plen" (Expr.lit plen) ]

/-- **The interpreter phase.** -/
def interpCom (prog : Program) : Com :=
  .seq (loadFrom 0 prog) (.seq (initCom prog.length) loopCom)

/-- The scalars the interpreter writes. -/
def SI : List String :=
  ["pc", "cur", "ol", "run", "op", "ia", "ib", "ic", "t1", "t2", "ta", "ylen", "plen"]

theorem initCom_run (plen : ℕ) (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hpl : plen + 3 < B) :
    ∃ σ1, Run B (initCom plen) σ σ1 30 ∧ σ1 = ((σ.setVar "run" 1).setVar "ylen"
      (n * n + 2)).setVar "plen" plen := by
  unfold initCom seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem interpCom_run (prog : Program) (y z : List ℕ) (n Pn Wp OL t : ℕ) (σ : Env)
    (hY : σ.arrs "Y" = y) (hn : σ.vars "n" = n) (hyl : y.length = n * n + 2)
    (hOP : σ.arrs "OP" = List.replicate prog.length 0)
    (hXA : σ.arrs "XA" = List.replicate prog.length 0)
    (hXB : σ.arrs "XB" = List.replicate prog.length 0)
    (hXC : σ.arrs "XC" = List.replicate prog.length 0)
    (hM : σ.arrs "M" = List.replicate Pn 0) (hO : σ.arrs "O" = List.replicate OL 0)
    (hpc : σ.vars "pc" = 0) (hcur : σ.vars "cur" = 0) (hol : σ.vars "ol" = 0)
    (hP : σ.vars "P" = Pn) (hwp : σ.vars "wp" = Wp) (hPn : Pn = 2 ^ Wp)
    (hsm : Small Wp prog) (hyP : ∀ v ∈ y, v < Pn) (hyPn : y.length < Pn)
    (bPP : Pn * Pn < B) (b2 : Pn + Pn < B) (bnd : prog.length + OL + y.length + Pn + 24 < B)
    (hOL : 0 < OL) (hOLt : t < OL)
    (hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B)
    (hRuns : RunsTo Wp prog y z t) :
    ∃ σ', Run B (interpCom prog) σ σ' (13 * prog.length + 1 + 30 + 250 * (t + 1)) ∧
      z = (σ'.arrs "O").take (σ'.vars "ol") ∧ (σ'.arrs "O").length = OL ∧
      (∀ v, v ∉ SI → σ'.vars v = σ.vars v) ∧
      (∀ a, a ∉ ["OP", "XA", "XB", "XC", "M", "O"] → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out := by
  have hcnt : ∀ (f : Instr → ℕ) (l : List ℕ), l = List.replicate prog.length 0 →
      setFrom l 0 (prog.map f) = prog.map f := by
    intro f l hl
    have hl' : (prog.map f).length = prog.length := List.length_map _
    rw [hl, ← hl']
    exact setFrom_replicate (prog.map f)
  obtain ⟨σ1, r1, hOP1, hXA1, hXB1, hXC1, hoth1, hvar1, hout1⟩ := loadFrom_run (B := B) prog 0 σ
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [hOP, hXA, hXB, hXC])
    (by omega) hlit
  obtain ⟨σ2, r2, e2⟩ := initCom_run (B := B) prog.length σ1 n (by rw [hvar1]; exact hn)
    (by nlinarith) (by omega) (by omega)
  have hInit : InitEnv Wp Pn prog y OL σ2 := by
    have hs : ∀ v, v ∉ ["run", "ylen", "plen"] → σ2.vars v = σ.vars v := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      rw [e2]; simp [Env.setVar, hvar1, hv.1, hv.2.1, hv.2.2]
    have ha : σ2.arrs = σ1.arrs := by rw [e2]; simp [Env.setVar]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs "P" (by simp), hP]
    · rw [hs "wp" (by simp), hwp]
    · rw [e2]; simp [Env.setVar, hyl]
    · rw [e2]; simp [Env.setVar]
    · rw [ha, hoth1 "Y" (by simp), hY]
    · rw [ha, hOP1, hcnt opcode _ hOP]
    · rw [ha, hXA1, hcnt fa _ hXA]
    · rw [ha, hXB1, hcnt fb _ hXB]
    · rw [ha, hXC1, hcnt fc _ hXC]
    · rw [ha, hoth1 "M" (by simp), hM]; simp
    · rw [ha, hoth1 "O" (by simp), hO]; simp
    · rw [hs "pc" (by simp), hpc]
    · rw [hs "cur" (by simp), hcur]
    · rw [hs "ol" (by simp), hol]
    · rw [e2]; simp [Env.setVar]
    · rw [ha, hoth1 "M" (by simp), hM]
  have hS := hInit.sctx (B := B) hPn bPP b2 bnd hyP hyPn hsm hOL
  obtain ⟨σ3, r3, hC3, -, hz⟩ := interp_run hS hRuns hOLt
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), hz, hC3.Olen, ?_, ?_, ?_⟩
  · intro v hv
    have h3 : σ3.vars v = σ2.vars v := r3.frame_var v (fun h => hv (by
      have := loopCom_frame_vars h
      simp only [SI, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      tauto))
    rw [h3, e2]
    have hv' : v ≠ "run" ∧ v ≠ "ylen" ∧ v ≠ "plen" := ⟨fun h => hv (by simp [SI, h]), fun h => hv (by simp [SI, h]), fun h => hv (by simp [SI, h])⟩
    simp [Env.setVar, hvar1, hv'.1, hv'.2.1, hv'.2.2]
  · intro a ha
    have h3 : σ3.arrs a = σ2.arrs a := r3.frame_arr a (fun h => ha (by
      have := loopCom_frame_arrs h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      tauto))
    rw [h3, show σ2.arrs = σ1.arrs by rw [e2]; simp [Env.setVar], hoth1 a (fun h => ha (by simp at h ⊢; tauto))]
  · rw [r3.out_eq loopCom_frame_write, e2]; simp [Env.setVar, hout1]

end Lax117284Proofs.Machine.TwSetup
