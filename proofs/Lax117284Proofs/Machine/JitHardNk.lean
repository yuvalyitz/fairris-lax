import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.JitHardFormat
import Lax117284Proofs.Machine.MisNk

/-!
What the format of an instance of interval scheduling with eligible machine sets expects next, as
a command: a number for each of the two counts and each of the `3 n` entries of the three
tables, and then a bit for each entry of the matrix.
-/

namespace Lax117284Proofs.Machine.JitHardNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.JitHardFormat
open Lax117284Proofs.Machine.MisNk (sub mul)

/-- What the format expects, the counts being `TK[0]` and `TK[1]`. -/
def nkH : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.lit 3) (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n3")) (set "kind" 0)
          (.seq (.assign "nm" (mul (.get "TK" (.lit 0)) (.get "TK" (.lit 1))))
            (.ite (.lt (sub (V "j") (V "n3")) (V "nm")) (set "kind" 1) (set "kind" 2))))))

/-- The code of what is expected after `Tn` tokens, the counts being `a` and `b`. -/
def kindCodeH (Tn a b : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindH a b (Tn - 2))

variable {B : ℕ}

theorem nkH_flat (Tn a b : ℕ) (hB : 3 * a + a * b + Tn + a + b + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = a ∧
        (σ.arrs "TK").getD 1 0 = b ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkH
      (fun σ σ' => σ'.vars "kind" = kindCodeH Tn a b ∧
        (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 100 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = a›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = b›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y y1 y2 y3 y4 => by simp [y1, y2, y3, y4]⟩
    unfold kindCodeH kindH
    split_ifs <;> first | rfl | omega)

theorem setKind_spec (v : ℕ) (hv : v < B) :
    Spec B (fun _ => True) (set "kind" v)
      (fun σ σ' => σ'.vars "kind" = v ∧ (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkH_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt EH cap nkH 100 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · have hE : EH toks = .num := by unfold EH; rw [if_pos h2]
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind_spec (B := B) 0 (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have h3 : 2 ≤ toks.length := by omega
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have hg : ∀ k, k < 2 → (σ.arrs "TK").getD k 0 = Tok.val (toks.getD k (.num 0)) := fun k hk => by
      have h1 : (σ.arrs "TK").getD k 0 = ((σ.arrs "TK").take toks.length).getD k 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega)]
      rw [h1, hTK, Lax117284Proofs.Machine.MisFormat.getD_map_val]
    have hb : ∀ k, k < 2 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 0 (by omega)
    have hb1 := hb 1 (by omega)
    have hab : Tok.val (toks.getD 0 (.num 0)) * Tok.val (toks.getD 1 (.num 0)) ≤ Bt * Bt :=
      Nat.mul_le_mul ha.le hb1.le
    have hbig : 3 * Tok.val (toks.getD 0 (.num 0)) + Tok.val (toks.getD 0 (.num 0)) *
        Tok.val (toks.getD 1 (.num 0)) + toks.length + Tok.val (toks.getD 0 (.num 0)) +
        Tok.val (toks.getD 1 (.num 0)) + 16 < B := by nlinarith
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkH_flat (B := B) toks.length
      (Tok.val (toks.getD 0 (.num 0))) (Tok.val (toks.getD 1 (.num 0))) hbig σ
      ⟨hT, hg 0 (by omega), hg 1 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeH EH
    rw [if_neg h2, if_neg h2]
