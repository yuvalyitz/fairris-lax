import Lax117284Proofs.Machine.TwRamStep

/-!
The loop of the interpreter: it runs the machine to its halt, at a cost of a constant per step.
-/

namespace Lax117284Proofs.Machine.TwRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

variable {B : ℕ}

/-- A step appends at most one number to the output. -/
lemma step_out_le {Wp : ℕ} {P : Program} {s s' : State} (h : step Wp P s = some s') :
    s'.out.length ≤ s.out.length + 1 := by
  unfold step at h
  cases hi : P[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    cases i <;> simp only [Instr.effect, Option.some.injEq] at h <;>
      first
      | (subst h; simp)
      | (cases hh : s.inp.head? <;> simp_all [Option.map] <;> (subst h; simp))
      | skip


/-- A step is taken only inside the code, and lands on the next instruction or on a label. -/
lemma step_pc {Wp Pn : ℕ} {P : Program} (hsm : Small Wp P) (hPn : Pn = 2 ^ Wp) {s s' : State}
    (h : step Wp P s = some s') :
    s.pc < P.length ∧ (s'.pc = s.pc + 1 ∨ s'.pc < Pn) := by
  unfold step at h
  cases hi : P[s.pc]? with
  | none => rw [hi] at h; simp at h
  | some i =>
    rw [hi] at h
    simp only [Option.bind_some] at h
    have hlt : s.pc < P.length := (List.getElem?_eq_some_iff.1 hi).1
    have hmem : i ∈ P := List.mem_of_getElem? hi
    obtain ⟨h1, h2, h3⟩ := hsm i hmem
    refine ⟨hlt, ?_⟩
    rw [← hPn] at h1 h2 h3
    cases i <;> simp only [Instr.effect, Option.some.injEq, fa, fb, fc] at h h1 h2 h3 <;>
      first
      | (subst h; dsimp only; split_ifs <;> first | (left; rfl) | (right; omega))
      | (subst h; dsimp only; first | (left; rfl) | (right; omega))
      | (subst h; simp; done)
      | (cases hh : s.inp.head? <;> simp_all [Option.map] <;> (subst h; simp))


theorem Run.while_step {B : ℕ} {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb hbs1 hbs2⟩

/-- The interpreter's loop: step while the machine runs. -/
def loopCom : Com := .while (.eq (V "run") (L 1)) stepCom

theorem loop_aux {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} :
    ∀ (n : ℕ) (s : State) (σ : Env) (send : State), SCtx B Wp Pn P y OL s σ →
      s.out.length + n < OL → run Wp P n s = some send → step Wp P send = none →
      ∃ σ', Run B loopCom σ σ' (250 * (n + 1)) ∧ Cst Wp Pn P y OL σ' ∧ Rel Pn y send σ' ∧
        σ'.vars "run" = 0 := by
  intro n
  induction n with
  | zero =>
    intro s σ send hS hbud hrun hstep
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    have hb := hS.bnd
    have hcond : (Cond.eq (V "run") (L 1)).evalB B σ = some true :=
      RunStep.cond_eq_true B σ (V "run") (L 1) _ _ (evalB_var (by rw [hS.run]; omega))
        (evalB_lit (by omega)) hS.run
    obtain ⟨σ1, r1, hC1, hO1⟩ := step_run hS
    rw [hstep] at hO1
    obtain ⟨hR1, hrun1⟩ := hO1
    have hcond' : (Cond.eq (V "run") (L 1)).evalB B σ1 = some false :=
      RunStep.cond_eq_false B σ1 (V "run") (L 1) _ _ (evalB_var (by rw [hrun1]; omega))
        (evalB_lit (by omega)) (by rw [hrun1]; omega)
    refine ⟨σ1, ?_, hC1, hR1, hrun1⟩
    have := Run.while_step (c := stepCom) hcond r1 (Run.while_false hcond')
    exact this.mono (by simp)
  | succ n ih =>
    intro s σ send hS hbud hrun hstep
    have hb := hS.bnd
    simp only [run] at hrun
    cases hs : step Wp P s with
    | none => rw [hs] at hrun; simp at hrun
    | some s' =>
      rw [hs] at hrun
      simp only [Option.bind_some] at hrun
      have hcond : (Cond.eq (V "run") (L 1)).evalB B σ = some true :=
        RunStep.cond_eq_true B σ (V "run") (L 1) _ _ (evalB_var (by rw [hS.run]; omega))
          (evalB_lit (by omega)) hS.run
      obtain ⟨σ1, r1, hC1, hO1⟩ := step_run hS
      rw [hs] at hO1
      obtain ⟨hR1, hrun1⟩ := hO1
      have hout := step_out_le hs
      obtain ⟨-, hpc'⟩ := step_pc hS.hsm hS.hPn hs
      have hS1 : SCtx B Wp Pn P y OL s' σ1 :=
        ⟨hR1, hC1, hS.hPn, hS.bPP, hS.b2, hS.bnd, by
          rw [hR1.pc]
          rcases hpc' with h | h
          · left; have := (step_pc hS.hsm hS.hPn hs).1; omega
          · right; exact h, hS.hyP, hS.hyl, hS.hsm, by omega, hrun1⟩
      obtain ⟨σ', r2, hC', hR', hrun'⟩ := ih s' σ1 send hS1 (by omega) hrun hstep
      refine ⟨σ', ?_, hC', hR', hrun'⟩
      have := Run.while_step (c := stepCom) hcond r1 r2
      exact this.mono (by simp; omega)


/-- The initial environment corresponds to the initial state. -/
structure InitEnv (Wp Pn : ℕ) (P : Program) (y : List ℕ) (OL : ℕ) (σ : Env) : Prop where
  cst : Cst Wp Pn P y OL σ
  pc : σ.vars "pc" = 0
  cur : σ.vars "cur" = 0
  ol : σ.vars "ol" = 0
  run : σ.vars "run" = 1
  M : σ.arrs "M" = List.replicate Pn 0

theorem InitEnv.sctx {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env}
    (h : InitEnv Wp Pn P y OL σ) (hPn : Pn = 2 ^ Wp) (bPP : Pn * Pn < B) (b2 : Pn + Pn < B)
    (bnd : P.length + OL + y.length + Pn + 24 < B) (hyP : ∀ v ∈ y, v < Pn) (hyl : y.length < Pn)
    (hsm : Small Wp P) (hOL : 0 < OL) : SCtx B Wp Pn P y OL (initState y) σ := by
  have hpos : 0 < Pn := by rw [hPn]; exact Nat.two_pow_pos _
  refine ⟨⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, h.cst, hPn, bPP, b2, bnd, Or.inl (by rw [h.pc]; omega),
    hyP, hyl, hsm, ?_, h.run⟩
  · simpa [initState] using h.pc
  · simp [initState, h.cur]
  · simp [h.cur]
  · simp [initState, h.ol]
  · rw [h.ol]; omega
  · intro a ha; rw [h.M]; simp [initState, List.getD_eq_getElem?_getD, List.getElem?_replicate, ha]
  · intro a; simpa [initState] using hpos
  · simpa [initState] using hOL

/-- **The interpreter.** Started on the initial environment, the loop runs to the end of the run
and leaves the output of the machine in the array `O`. -/
theorem interp_run {B Wp Pn : ℕ} {P : Program} {y : List ℕ} {OL : ℕ} {σ : Env} {z : List ℕ} {t : ℕ}
    (hS : SCtx B Wp Pn P y OL (initState y) σ) (hRuns : RunsTo Wp P y z t) (hOL : t < OL) :
    ∃ σ', Run B loopCom σ σ' (250 * (t + 1)) ∧ Cst Wp Pn P y OL σ' ∧ σ'.vars "run" = 0 ∧
      z = (σ'.arrs "O").take (σ'.vars "ol") := by
  obtain ⟨k, sk, hrun, hstep, hout, ht⟩ := hRuns
  have hk : k ≤ t := by rw [ht]; omega
  obtain ⟨σ', r, hC, hR, hrun'⟩ := loop_aux k (initState y) σ sk hS (by simp [initState]; omega) hrun hstep
  refine ⟨σ', r.mono (Nat.mul_le_mul_left _ (by omega)), hC, hrun', ?_⟩
  rw [← hout]; exact hR.ol

end Lax117284Proofs.Machine.TwRam
