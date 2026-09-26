import Lax117284Proofs.Machine.Out

/-!
Loops whose body is straight-line code over any number of scalars, not only the counter and one
base: the body may read whatever the loop left alone and may use as scratch whatever it lists.
-/

namespace Lax117284Proofs.Machine.Emit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out

variable {B : ℕ}

/-- Write the entry of the token array at `2 + 2 v + o`, `v` being a scalar. -/
def emitCell (v : String) (o : ℕ) : Com :=
  emitTK (add (add (.lit 2) (mul (.lit 2) (V v))) (.lit o))

theorem emitCell_run (v : String) (o Sz : ℕ) (σ : Env)
    (h1 : 2 + 2 * σ.vars v + o < (σ.arrs "TK").length) (h2 : 2 + 2 * σ.vars v + o < B)
    (h3 : (σ.arrs "TK").getD (2 + 2 * σ.vars v + o) 0 + 4 < B)
    (h4 : ((σ.arrs "TK").getD (2 + 2 * σ.vars v + o) 0).size ≤ Sz) :
    ∃ σ', Run B (emitCell v o) σ σ' (1 + 9 + (48 * Sz + 50)) ∧
      σ'.out = σ.out ++ bitsNat ((σ.arrs "TK").getD (2 + 2 * σ.vars v + o) 0) ∧ Same σ σ' := by
  have hev : (add (add (.lit 2) (mul (.lit 2) (V v))) (.lit o)).evalB B σ
      = some (2 + 2 * σ.vars v + o) :=
    evalB_bin (evalB_bin (evalB_lit (by omega)) (evalB_bin (evalB_lit (by omega))
      (evalB_var (by omega)) (by simp; omega)) (by simp; omega)) (evalB_lit (by omega))
      (by simp; omega)
  have r1 : Run B (.assign "ix" (add (add (.lit 2) (mul (.lit 2) (V v))) (.lit o))) σ
      (σ.setVar "ix" (2 + 2 * σ.vars v + o))
      (1 + (add (add (.lit 2) (mul (.lit 2) (V v))) (.lit o)).size) := Run.assign hev
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "TK" "ix" Sz (by decide)
    (σ.setVar "ix" (2 + 2 * σ.vars v + o))
    ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2,
      by simpa [Env.setVar] using h3, by simpa [Env.setVar] using h4⟩
  refine ⟨σ2, (r1.seq r2).mono (by simp [Expr.size]), by simpa [Env.setVar] using o2,
    fun y hy => ?_, by rw [a2]; simp [Env.setVar]⟩
  have hix : y ≠ "ix" := fun h => hy (by simp [SCR, h])
  rw [v2 y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto)]
  simp [Env.setVar, hix]

/-- Nothing changed but the listed scalars. -/
def Agr (S : List String) (σ0 σ : Env) : Prop := σ.arrs = σ0.arrs ∧ ∀ y ∉ S, σ.vars y = σ0.vars y

lemma Agr.refl (S : List String) (σ : Env) : Agr S σ σ := ⟨rfl, fun _ _ => rfl⟩

/-- **A loop whose body reads everything but the counter and its scratch scalars from the
state the loop started in.** The counter must be among the listed scalars; the body leaves it
alone, and its own output depends on the counter alone. -/
theorem eLoop (mv : String) (c : Com) (S : List String) (g : ℕ → List ℕ) (K N : ℕ) (σ0 : Env)
    (hi : "i" ∈ S) (hmv : mv ∉ S) (hN : σ0.vars mv = N) (hNB : N + 1 < B)
    (hc : ∀ σ, Agr S σ0 σ → σ.vars "i" < N →
      ∃ σ', Run B c σ σ' K ∧ σ'.out = σ.out ++ g (σ.vars "i") ∧ Agr S σ0 σ' ∧
        σ'.vars "i" = σ.vars "i") :
    ∃ σ', Run B (outLoop mv c) σ0 σ' ((K + 10 + 4) * N + 6) ∧
      σ'.out = σ0.out ++ (List.range N).flatMap g ∧ Agr S σ0 σ' := by
  let I : Env → Prop := fun σ => Agr S σ0 σ ∧ σ.vars "i" ≤ N ∧
    σ.out = σ0.out ++ (List.range (σ.vars "i")).flatMap g
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "i" < N)
      (.seq c (.assign "i" (.bin .add (V "i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (K + 10) := by
    intro σ ⟨⟨hA, hle, hout⟩, hlt⟩
    obtain ⟨σ1, r1, o1, hA1, hi1⟩ := hc σ hA hlt
    have r2 : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ1
        (σ1.setVar "i" (σ1.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
      Run.assign (evalB_bin (evalB_var (by rw [hi1]; omega)) (evalB_lit (by omega))
        (by simp [hi1]; omega))
    refine ⟨_, (r1.seq r2).mono (by simp [Expr.size] <;> omega), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simp only [Env.setVar]; exact hA1.1
    · intro y hy
      have hyi : y ≠ "i" := fun h => hy (h ▸ hi)
      simp only [Env.setVar, if_neg hyi]
      exact hA1.2 y hy
    · simp [Env.setVar, hi1]; omega
    · simp only [Env.setVar, if_true, hi1]
      rw [o1, hout, List.range_succ, List.flatMap_append]
      simp
    · simp [Env.setVar, hi1]
  obtain ⟨σ', r, hI', hi'⟩ := (Spec.forRangeZero (B := B) (c := .seq c (.assign "i"
      (.bin .add (V "i") (.lit 1)))) "i" mv I N (K + 10) (by omega) (fun _ h => h.2.1)
    (fun σ h => (h.1.2 mv hmv).trans hN) hbody) σ0
    ⟨⟨by simp [Env.setVar], fun y hy => by
        have hyi : y ≠ "i" := fun h => hy (h ▸ hi)
        simp [Env.setVar, hyi]⟩, by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, ?_, hI'.1⟩
  rw [hI'.2.2, hi']

end Lax117284Proofs.Machine.Emit
