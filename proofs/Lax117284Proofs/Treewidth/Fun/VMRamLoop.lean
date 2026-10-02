import Lax117284Proofs.Treewidth.Fun.VMRamOps3

/-!
# WP V2 (5): the dispatch loop

`refines_blkOp` collects the sixteen instruction lemmas; `turn_step` is one turn of `vmLoop` (fetch,
dispatch, execute) and `loop_run` runs the loop along a `StepsB` run, at cost `≤ 120 (n + 1) + 4`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

theorem opc_le (i : Instr) : opc i ≤ 16 := by cases i <;> simp [opc]

/-- Every instruction is refined by the block of its opcode (`halt` vacuously: it never steps). -/
theorem refines_blkOp (i : Instr) : Refines (blkOp (opc i)) 40 i := by
  cases i with
  | halt =>
    intro P W Bi s s' σ hA hC hB hB' hc hs hf
    simp [Prog.step, hc] at hs
  | lit n => exact (core_lit n).refines (by decide)
  | var i => exact (core_var i).refines (by decide)
  | add => exact core_add.refines (by decide)
  | sub => exact core_sub.refines (by decide)
  | mul => exact core_mul.refines (by decide)
  | lt => exact core_lt.refines (by decide)
  | eq => exact core_eq.refines (by decide)
  | cons => exact core_cons.refines (by decide)
  | fst => exact core_fst.refines (by decide)
  | snd => exact core_snd.refines (by decide)
  | isNat => exact core_isNat.refines (by decide)
  | jz k => exact (core_jz k).refines (by decide)
  | jmp k => exact (core_jmp k).refines (by decide)
  | slide => exact core_slide.refines (by decide)
  | call n => exact (core_call n).refines (by decide)
  | ret => exact core_ret.refines (by decide)

/-! ## The dispatch chain -/

theorem dispatchFrom_run {Bi K : ℕ} :
    ∀ (f k : ℕ) (σ σ' : Env), k ≤ σ.vars "op" → σ.vars "op" ≤ k + f → k + f < Bi →
      Run Bi (blkOp (σ.vars "op")) σ σ' K → Run Bi (dispatchFrom k f) σ σ' (4 * f + K) := by
  intro f
  induction f with
  | zero =>
    intro k σ σ' h1 h2 h3 h
    have e : σ.vars "op" = k := by omega
    rw [e] at h
    simpa [dispatchFrom] using h
  | succ f ih =>
    intro k σ σ' h1 h2 h3 h
    have hop : σ.vars "op" < Bi := by omega
    have hk : k < Bi := by omega
    have hev : (Expr.var "op").evalB Bi σ = some (σ.vars "op") := RunStep.eval_var Bi σ "op" hop
    have hel : (Expr.lit k).evalB Bi σ = some k := RunStep.eval_lit Bi k σ hk
    by_cases hc : σ.vars "op" = k
    · have hb := RunStep.cond_eq_true Bi σ (V "op") (L k) _ _ hev hel hc
      rw [hc] at h
      have := Run.ite_true (d := dispatchFrom (k + 1) f) hb h
      simp only [dispatchFrom]
      exact this.mono (by (try simp) <;> omega)
    · have hb := RunStep.cond_eq_false Bi σ (V "op") (L k) _ _ hev hel hc
      have := Run.ite_false (c := blkOp k) hb (ih (k + 1) σ σ' (by omega) (by omega) (by omega) h)
      simp only [dispatchFrom]
      exact this.mono (by (try simp) <;> omega)

theorem dispatch_run {Bi K : ℕ} (hBi : 17 < Bi) {σ σ' : Env} (hop : σ.vars "op" ≤ 16)
    (h : Run Bi (blkOp (σ.vars "op")) σ σ' K) : Run Bi bDispatch σ σ' (4 * 16 + K) :=
  dispatchFrom_run 16 0 σ σ' (by omega) (by omega) (by omega) h

/-! ## Fetch -/

theorem fetch_run {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) :
    ∃ σ', Run Bi bFetch σ σ' 6 ∧
      σ' = (σ.setVar "op" (opc (P.code s.pc))).setVar "oa" (opa (P.code s.pc)) := by
  have hpc : σ.vars "pc" = s.pc := hA.pc
  have hpcW : s.pc ≤ W := hB.pc
  have g1 : (σ.arrs "OP").getD (σ.vars "pc") 0 = opc (P.code s.pc) := by
    rw [hpc, List.getD_eq_getElem?_getD, hC.op _ hpcW]; rfl
  have g2 : (σ.arrs "OA").getD (σ.vars "pc") 0 = opa (P.code s.pc) := by
    rw [hpc, List.getD_eq_getElem?_getD, hC.oa _ hpcW]; rfl
  have hl1 : (σ.arrs "OP").length = W + 1 := hC.len "OP" (by simp [arrNames])
  have hl2 : (σ.arrs "OA").length = W + 1 := hC.len "OA" (by simp [arrNames])
  have ho : opc (P.code s.pc) ≤ 16 := opc_le _
  have ha : opa (P.code s.pc) < Bi := hC.opa_lt _ hpcW
  have hB18 := hC.bi
  unfold bFetch
  run_vcg
  all_goals try (nrm; omega)
  nrm
  rw [g1, g2]

theorem abs_op_oa {s : St} {σ : Env} (hA : Abs s σ) (a b : ℕ) :
    Abs s ((σ.setVar "op" a).setVar "oa" b) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; exact hA.pc
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## One turn of the loop -/

theorem turn_step {P : Prog} {W Bi : ℕ} {s s' : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) (hB' : s'.Bd W) (hs : P.step s = some s') (hrun : σ.vars "run" = 1) :
    ∃ σ', Run Bi bBody σ σ' 110 ∧ Abs s' σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 1 := by
  obtain ⟨σ1, hr1, e1⟩ := fetch_run hA hC hB
  obtain ⟨i, hi⟩ : ∃ i, P.code s.pc = i := ⟨_, rfl⟩
  rw [hi] at e1
  have hA1 : Abs s σ1 := by rw [e1]; exact abs_op_oa hA _ _
  have hC1 : Cst P W Bi σ1 := hC.of_run hr1 (by decide) (by decide) (by decide) (by decide)
  have hop : σ1.vars "op" = opc i := by rw [e1]; nrm
  have hF : Fetched σ1 i := ⟨hop, by rw [e1]; nrm⟩
  have hrun1 : σ1.vars "run" = 1 := by rw [hr1.frame_var _ (by decide)]; exact hrun
  obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := refines_blkOp i P W Bi s s' σ1 hA1 hC1 hB hB' hi hs hF
  have hd := dispatch_run (Bi := Bi) (K := 40) (by have := hC.bi; omega) (σ := σ1) (σ' := σ2)
    (by rw [hop]; exact opc_le i) (by rw [hop]; exact hr2)
  exact ⟨σ2, (hr1.seq hd).mono (by omega), hA2, hC2, by rw [hrun2, hrun1]⟩

theorem turn_halt {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) (hhalt : P.code s.pc = .halt) :
    ∃ σ', Run Bi bBody σ σ' 110 ∧ Abs s σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  obtain ⟨σ1, hr1, e1⟩ := fetch_run hA hC hB
  rw [hhalt] at e1
  have hA1 : Abs s σ1 := by rw [e1]; exact abs_op_oa hA _ _
  have hC1 : Cst P W Bi σ1 := hC.of_run hr1 (by decide) (by decide) (by decide) (by decide)
  have hop : σ1.vars "op" = 0 := by rw [e1]; simp [opc]
  obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := halt_run hA1 hC1
  have hd := dispatch_run (Bi := Bi) (K := 4) (by have := hC.bi; omega) (σ := σ1) (σ' := σ2)
    (by rw [hop]; omega) (by rw [hop]; exact hr2)
  exact ⟨σ2, (hr1.seq hd).mono (by omega), hA2, hC2, hrun2⟩

/-! ## The loop -/

theorem run_while_step {B : ℕ} {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb hbs1 hbs2⟩

theorem run_cond_true {Bi : ℕ} {σ : Env} (hB : 1 < Bi) (h : σ.vars "run" = 1) (hr : σ.vars "run" < Bi) :
    (Cond.eq (V "run") (L 1)).evalB Bi σ = some true :=
  RunStep.cond_eq_true Bi σ (V "run") (L 1) _ _ (RunStep.eval_var Bi σ "run" hr)
    (RunStep.eval_lit Bi 1 σ hB) h

theorem run_cond_false {Bi : ℕ} {σ : Env} (hB : 1 < Bi) (h : σ.vars "run" = 0) :
    (Cond.eq (V "run") (L 1)).evalB Bi σ = some false :=
  RunStep.cond_eq_false Bi σ (V "run") (L 1) _ _ (RunStep.eval_var Bi σ "run" (by omega))
    (RunStep.eval_lit Bi 1 σ hB) (by omega)

/-- **The loop.**  Along a bounded run `s → … → s'` ending at a `halt`, `vmLoop` started on a representation
of `s` (with `run = 1`) runs to a representation of `s'` with `run = 0`, at cost `≤ 120 (n + 1) + 4`. -/
theorem loop_run {P : Prog} {W Bi n : ℕ} {s s' : St} (h : StepsB P W n s s')
    (hhalt : P.code s'.pc = .halt) :
    ∀ σ, Abs s σ → Cst P W Bi σ → σ.vars "run" = 1 →
      ∃ σ', Run Bi vmLoop σ σ' (120 * (n + 1) + 4) ∧ Abs s' σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  induction h with
  | refl hb =>
    intro σ hA hC hrun
    have hB1 : 1 < Bi := by have := hC.bi; omega
    obtain ⟨σ1, hr, hA1, hC1, hrun1⟩ := turn_halt hA hC hb hhalt
    have hw := run_while_step (run_cond_true hB1 hrun (by omega)) hr
      (Run.while_false (c := bBody) (run_cond_false hB1 hrun1))
    exact ⟨σ1, by simpa [vmLoop] using hw.mono (by simp), hA1, hC1, hrun1⟩
  | @step s0 s1 s2 m hb hs hrest ih =>
    intro σ hA hC hrun
    have hB1 : 1 < Bi := by have := hC.bi; omega
    obtain ⟨σ1, hr, hA1, hC1, hrun1⟩ := turn_step hA hC hb hrest.bd_start hs hrun
    obtain ⟨σ2, hr2, hA2, hC2, hrun2⟩ := ih hhalt σ1 hA1 hC1 hrun1
    have hw := run_while_step (run_cond_true hB1 hrun (by omega)) hr hr2
    exact ⟨σ2, by simpa [vmLoop] using hw.mono (by simp; omega), hA2, hC2, hrun2⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram
