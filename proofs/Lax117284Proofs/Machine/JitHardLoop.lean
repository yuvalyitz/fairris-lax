import Lax117284Proofs.Machine.Emit

/-!
Loops of output steps with a counter of their own, so that they can be nested: the counter is
a parameter of the loop, and the body leaves everything but its own scratch scalars alone.
-/

namespace Lax117284Proofs.Machine.JitHardLoop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit

variable {B : ℕ}

/-- A loop over `ctr` from `0` to the value of `mv`. -/
def cLoop (ctr mv : String) (c : Com) : Com :=
  .seq (.assign ctr (.lit 0))
    (.while (.lt (.var ctr) (.var mv)) (.seq c (.assign ctr (.bin .add (V ctr) (.lit 1)))))

/-- **A loop whose body reads everything but its counter and its scratch scalars from the state
the loop started in.** The counter must be among the listed scalars; the body leaves it alone,
and its own output depends on the counter alone. -/
theorem cLoop_spec (ctr mv : String) (c : Com) (S : List String) (g : ℕ → List ℕ) (K N : ℕ)
    (σ0 : Env) (hi : ctr ∈ S) (hmv : mv ∉ S) (hN : σ0.vars mv = N) (hNB : N + 1 < B)
    (hc : ∀ σ, Agr S σ0 σ → σ.vars ctr < N →
      ∃ σ', Run B c σ σ' K ∧ σ'.out = σ.out ++ g (σ.vars ctr) ∧ Agr S σ0 σ' ∧
        σ'.vars ctr = σ.vars ctr) :
    ∃ σ', Run B (cLoop ctr mv c) σ0 σ' ((K + 10 + 4) * N + 6) ∧
      σ'.out = σ0.out ++ (List.range N).flatMap g ∧ Agr S σ0 σ' := by
  let I : Env → Prop := fun σ => Agr S σ0 σ ∧ σ.vars ctr ≤ N ∧
    σ.out = σ0.out ++ (List.range (σ.vars ctr)).flatMap g
  have hbody : Spec B (fun σ => I σ ∧ σ.vars ctr < N)
      (.seq c (.assign ctr (.bin .add (V ctr) (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars ctr = σ.vars ctr + 1) (K + 10) := by
    intro σ ⟨⟨hA, hle, hout⟩, hlt⟩
    obtain ⟨σ1, r1, o1, hA1, hi1⟩ := hc σ hA hlt
    have r2 : Run B (.assign ctr (.bin .add (V ctr) (.lit 1))) σ1
        (σ1.setVar ctr (σ1.vars ctr + 1)) (1 + (Expr.bin .add (V ctr) (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by rw [hi1]; omega)) (evalB_lit (by omega))
        (by simp [hi1]; omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size] <;> omega), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [Env.setVar]; exact hA1.1
    · intro y hy
      have hyi : y ≠ ctr := fun h => hy (h ▸ hi)
      simp only [Env.setVar, if_neg hyi]
      exact hA1.2 y hy
    · simp [Env.setVar, hi1]; omega
    · simp only [Env.setVar, if_true, hi1]
      rw [o1, hout, List.range_succ, List.flatMap_append]
      simp
    · simp [Env.setVar, hi1]
  obtain ⟨σ', r, hI', hi'⟩ := (Spec.forRangeZero (B := B) (c := .seq c (.assign ctr
      (.bin .add (V ctr) (.lit 1)))) ctr mv I N (K + 10) (by omega) (fun _ h => h.2.1)
    (fun σ h => (h.1.2 mv hmv).trans hN) hbody) σ0
    ⟨⟨by simp [Env.setVar], fun y hy => by
        have hyi : y ≠ ctr := fun h => hy (h ▸ hi)
        simp [Env.setVar, hyi]⟩, by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, ?_, hI'.1⟩
  rw [hI'.2.2, hi']

end Lax117284Proofs.Machine.JitHardLoop
