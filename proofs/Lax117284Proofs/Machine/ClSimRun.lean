import Lax117284Proofs.Machine.ClSimBody

/-!
The interpreter loop runs the machine to its halt: induction on the number of transitions.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {P : Program} {z : List ℕ}

/-- The assumptions on the world that do not depend on the state. -/
structure HypS (B wp : ℕ) (P : Program) (z : List ℕ) : Prop where
  hB : Bnd B wp
  hzB : z.length < B
  hzE : ∀ i, z.getD i 0 < B
  hzE' : ∀ i (h : i < z.length), z[i] < B
  hpl : P.length < B
  hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B

/-- The relation at the end of the run: everything but the counter, which is at or past the end
of the program. -/
def Fin' (P : Program) (z : List ℕ) (wp v : ℕ) (σ : Env) (s : State) : Prop :=
  DRel z wp v σ { s with pc := σ.vars "spc" } ∧ P.length ≤ σ.vars "spc"

theorem run_while_step {b : Cond} {c : Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}
    (hb : b.evalB B σ = some true) (h1 : Run B c σ σ1 K1) (h2 : Run B (.while b c) σ1 σ2 K2) :
    Run B (.while b c) σ σ2 (1 + b.size + K1 + K2) := by
  obtain ⟨k1, hk1, b1⟩ := h1
  obtain ⟨k2, hk2, b2⟩ := h2
  exact ⟨1 + b.size + k1 + k2, by omega, .while_true hb b1 b2⟩

theorem loopCond_eval (σ : Env) (h1 : σ.vars "spc" < B) (h2 : σ.vars "plen" < B) :
    (Cond.lt (V "spc") (V "plen")).evalB B σ = some (decide (σ.vars "spc" < σ.vars "plen")) :=
  evalB_condLt (evalB_var h1) (evalB_var h2)

theorem run_out_prefix {w : ℕ} {p : Program} : ∀ (n : ℕ) (s s' : State),
    run w p n s = some s' → s.out <+: s'.out := by
  intro n
  induction n with
  | zero => intro s s' h; simp only [run, Option.some.injEq] at h; subst h; exact List.prefix_refl _
  | succ n ih =>
    intro s s' h
    simp only [run] at h
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    refine (?_ : s.out <+: s1.out).trans (ih s1 s' h2)
    unfold step at h1
    rcases hp : p[s.pc]? with _ | i
    · simp [hp] at h1
    · rw [hp] at h1
      simp only [Option.bind_some] at h1
      cases i <;> simp only [Instr.effect] at h1
      case halt => cases h1
      case read a =>
        obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.mp h1
        exact List.prefix_refl _
      case write a =>
        obtain rfl := Option.some.inj h1
        exact List.prefix_append _ _
      all_goals (obtain rfl := Option.some.inj h1; exact List.prefix_refl _)

theorem hyp_of {σ : Env} {s : State} (HS : HypS B wp P z) (hD : DRel z wp v σ s)
    (hpc : σ.vars "spc" < P.length) : Hyp B wp s P z :=
  ⟨HS.hB, hD.word, HS.hzB, HS.hzE, HS.hzE', HS.hpl, by rw [← hD.spc]; exact hpc⟩

theorem fin_of_ge {σ : Env} {s : State} (hD : DRel z wp v σ s) (hK : KRel P z wp σ)
    (hge : ¬ σ.vars "spc" < P.length) : Fin' P z wp v σ s := by
  refine ⟨?_, by omega⟩
  have : ({ s with pc := σ.vars "spc" } : State) = s := by rw [hD.spc]
  rw [this]; exact hD

theorem loop_run (HS : HypS B wp P z) (sf : State) (hfin : sf.out = [v])
    (hhalt : step wp P sf = none) :
    ∀ (n : ℕ) (s : State) (σ : Env), KRel P z wp σ → DRel z wp v σ s → σ.vars "spc" < B →
      run wp P n s = some sf →
      ∃ σ', Run B interpLoop σ σ' ((n + 1) * 604 + 4) ∧ KRel P z wp σ' ∧ Fin' P z wp v σ' sf := by
  intro n
  induction n with
  | zero =>
    intro s σ hK hD hsB hrun
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    have hplB : σ.vars "plen" < B := by rw [hK.plen]; exact HS.hpl
    by_cases hpc : σ.vars "spc" < P.length
    · have hs := hyp_of HS hD hpc
      obtain ⟨i, hi⟩ : ∃ i, P[s.pc]? = some i :=
        ⟨P[s.pc]'(by rw [← hD.spc]; exact hpc), List.getElem?_eq_getElem _⟩
      have hbody := body_spec (v := v) hs i hi (HS.hLits i (List.mem_of_getElem? hi))
        (fun s' h => by rw [hhalt] at h; cases h)
      obtain ⟨σ1, hr1, hK1, hB1, hpost⟩ := hbody σ ⟨hK, hD⟩
      rw [hhalt] at hpost
      dsimp only at hpost
      have hsp : σ1.vars "spc" = P.length := hpost.spc
      have hct : (Cond.lt (V "spc") (V "plen")).evalB B σ = some true := by
        rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
      have hcf : (Cond.lt (V "spc") (V "plen")).evalB B σ1 = some false := by
        rw [loopCond_eval σ1 hB1 (by rw [hK1.plen]; exact HS.hpl)]
        simp [hK1.plen, hsp]
      refine ⟨σ1, ((run_while_step hct hr1 (Run.while_false hcf)).mono (by simp [Cond.size])),
        hK1, ?_, by rw [hsp]⟩
      have : ({ s with pc := σ1.vars "spc" } : State) = halted P s := by
        rw [hsp]; rfl
      rw [this]; exact hpost
    · have hcf : (Cond.lt (V "spc") (V "plen")).evalB B σ = some false := by
        rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
      exact ⟨σ, (Run.while_false hcf).mono (by simp [Cond.size]), hK, fin_of_ge hD hK hpc⟩
  | succ n ih =>
    intro s σ hK hD hsB hrun
    have hplB : σ.vars "plen" < B := by rw [hK.plen]; exact HS.hpl
    simp only [run] at hrun
    obtain ⟨s1, hs1, hrun1⟩ := Option.bind_eq_some_iff.mp hrun
    have hpc : σ.vars "spc" < P.length := by
      by_contra hcon
      have := Lax808846Proofs.Machine.step_none_of_length_le (w := wp) (p := P) (s := s) (by rw [← hD.spc]; omega)
      rw [this] at hs1; cases hs1
    have hs := hyp_of HS hD hpc
    obtain ⟨i, hi⟩ : ∃ i, P[s.pc]? = some i :=
      ⟨P[s.pc]'(by rw [← hD.spc]; exact hpc), List.getElem?_eq_getElem _⟩
    have hpref : ∀ s', step wp P s = some s' → s'.out <+: [v] := by
      intro s' h
      rw [hs1] at h
      cases h
      have := run_out_prefix n s1 sf hrun1
      rw [hfin] at this
      exact this
    have hbody := body_spec (v := v) hs i hi (HS.hLits i (List.mem_of_getElem? hi)) hpref
    obtain ⟨σ1, hr1, hK1, hB1, hpost⟩ := hbody σ ⟨hK, hD⟩
    rw [hs1] at hpost
    obtain ⟨σ', hr2, hK2, hF⟩ := ih s1 σ1 hK1 hpost hB1 hrun1
    have hct : (Cond.lt (V "spc") (V "plen")).evalB B σ = some true := by
      rw [loopCond_eval σ hsB hplB]; simp [hK.plen, hpc]
    refine ⟨σ', (run_while_step hct hr1 hr2).mono (by simp [Cond.size]; nlinarith), hK2, hF⟩

end Lax117284Proofs.Machine.ClSim
