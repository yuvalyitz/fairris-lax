import Lax117284Proofs.Machine.ClSimStep

/-!
One iteration of the interpreter agrees with one step of the machine.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

/-- The postcondition of an iteration: the machine's next state, or the stop. -/
def StepPost (B : ℕ) (P : Program) (z : List ℕ) (wp v : ℕ) (s : State) (σ' : Env) : Prop :=
  KRel P z wp σ' ∧ σ'.vars "spc" < B ∧ match step wp P s with
    | some s' => DRel z wp v σ' s'
    | none => DRel z wp v σ' (halted P s)

theorem commit_pre {σ : Env} {o : Option State} (H : Hyp B wp s P z) (hK : KRel P z wp σ)
    (hD : DRel z wp v σ s) (hR : Res B wp P.length s o σ) :
    σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
      (σ.vars "wf" = 1 → σ.vars "wa" < (σ.arrs "om").length ∧ σ.vars "wa" < B ∧ σ.vars "wv" < B) ∧
      (σ.vars "wo" = 1 → σ.vars "wov" < B) ∧ σ.vars "npc" < B ∧
      σ.vars "rd" + σ.vars "rdi" < B ∧ 1 < B := by
  have hB := H.hB
  have hw := H.hw
  have hzB := H.hzB
  have hzE := H.hzE
  have hzE' := H.hzE'
  have hpl := H.hpl
  have hpc := H.hpc
  clear H
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have homlen := hD.omlen
  have hrd := hD.rd
  have hzl := hK.zl
  cases o with
  | none =>
    simp only [Res] at hR
    obtain ⟨hnpc, hwf, hwo, hrdi⟩ := hR
    refine ⟨by omega, by omega, fun h => by omega, fun h => by omega, by omega, by omega, by omega⟩
  | some s' =>
    simp only [Res] at hR
    obtain ⟨-, hwa, hrd2, hwf1, hwo1, hwov, hnpc⟩ := hR
    refine ⟨hwf1, hwo1, fun h => ?_, fun h => ?_, hnpc, by omega, by omega⟩
    · have := hwa h; refine ⟨by omega, by omega, by omega⟩
    · have := hwov h; omega

theorem dispatch_frame_ok : (∀ y ∈ dispatch.wvars, y ∈ FV) ∧ dispatch.warrs = [] ∧ ¬ dispatch.reads ∧
    dispatch.NoWrite := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem agree_of_frame {c : Com} (hv : ∀ y ∈ c.wvars, y ∈ FV) (ha : c.warrs = []) (hr : ¬ c.reads)
    (hw : c.NoWrite) {σ σ' : Env} (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y)
    (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) (h3 : ¬ c.reads → σ'.inp = σ.inp)
    (h4 : c.NoWrite → σ'.out = σ.out) : AgreeOff FV σ σ' :=
  ⟨funext fun a => h2 a (by simp [ha]), h3 hr, h4 hw,
    fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem body_spec (H : Hyp B wp s P z) (i : Instr) (hi : P[s.pc]? = some i)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B)
    (hpref : ∀ s', step wp P s = some s' → s'.out <+: [v]) :
    Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s) bodyCom (fun _ σ' => StepPost B P z wp v s σ')
      600 := by
  have hf := Spec.pre (P' := fun σ => KRel P z wp σ ∧ DRel z wp v σ s) (fetch_spec (v := v) i H hL)
    (fun σ h => ⟨h.1, h.2, hi⟩)
  have hd := (dispatch_spec (v := v) i H hL).frame
  have hstep : step wp P s = i.effect wp s := by simp [step, hi]
  obtain ⟨hv, ha, hr, hw⟩ := dispatch_frame_ok
  have hd' : Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
      dispatch (fun σ σ' => Res B wp P.length s (i.effect wp s) σ' ∧ AgreeOff FV σ σ') 300 :=
    hd.post fun σ σ' _ ⟨hR, h1, h2, h3, h4⟩ =>
      ⟨hR, agree_of_frame hv ha hr hw h1 h2 h3 h4⟩
  have hc' : Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s ∧
      Res B wp P.length s (i.effect wp s) σ) commitCom (fun _ σ' => StepPost B P z wp v s σ') 100 := by
    refine (commit_run (B := B) trivial).conseq
      (fun σ ⟨hK, hD, hR⟩ => commit_pre H hK hD hR) ?_ le_rfl
    intro σ σ' ⟨hK, hD, hR⟩ hσ'
    subst hσ'
    refine ⟨commit_krel hK, ?_, ?_⟩
    · rw [commitEnv_vars]; simp only [String.reduceEq, if_false, if_true, and_false, ite_false]
      have := H.hpl
      cases hE : i.effect wp s with
      | none => rw [hE] at hR; simp only [Res] at hR; omega
      | some s' => rw [hE] at hR; simp only [Res] at hR; omega
    · rw [hstep]
      cases hE : i.effect wp s with
      | none => rw [hE] at hR; exact commit_drel_none hD hK.zl hR
      | some s' =>
        rw [hE] at hR
        exact commit_drel_some hD hK.zl hR (hpref s' (by rw [hstep, hE]))
  have h23 : Spec B (Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
      (.seq dispatch commitCom) (fun _ σ' => StepPost B P z wp v s σ') 400 := by
    refine Spec.seq hd' hc' ?_ ?_
    · rintro σ σ' ⟨hF, hK, hD⟩ ⟨hR, hA⟩
      exact ⟨hK.agree hA, hD.agree hA, hR⟩
    · intro σ σ' σ'' _ _ h
      exact h
  refine Spec.seq (P' := Pre P z wp v s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2)
    hf h23 ?_ ?_
  · rintro σ σ' ⟨hK, hD⟩ ⟨hF, hA⟩
    exact ⟨hF, hK.agree hA, hD.agree hA⟩
  · intro σ σ' σ'' _ _ h
    exact h

end Lax117284Proofs.Machine.ClSim
