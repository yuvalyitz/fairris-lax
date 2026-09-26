import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.SatSem

/-!
What the format of a formula expects next, as a command: a number for each of the three counts,
and then a number and a bit alternately until every position has been read.
-/

namespace Lax117284Proofs.Machine.SatNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.SatFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f
abbrev add (e f : Expr) : Expr := .bin .add e f

/-- What the format expects, the counts being `TK[1]` and `TK[2]`. -/
def nkF : Com :=
  .ite (.lt (V "T") (.lit 3)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 3)))
      (.seq (.assign "n3" (add (mul (.lit 4) (.get "TK" (.lit 1)))
          (mul (.lit 6) (.get "TK" (.lit 2)))))
        (.ite (.lt (V "j") (V "n3"))
          (.assign "kind" (sub (V "j") (mul (div (V "j") (.lit 2)) (.lit 2))))
          (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the counts being `a` and `b`. -/
def kindCodeF (Tn a b : ℕ) : ℕ := if Tn < 3 then 0 else kcode (kindF a b (Tn - 3))

variable {B : ℕ}

theorem nkF_flat (Tn a b : ℕ) (hB : 4 * a + 6 * b + Tn + a + b + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 1 0 = a ∧
        (σ.arrs "TK").getD 2 0 = b ∧ (3 ≤ Tn → 3 ≤ (σ.arrs "TK").length)) nkF
      (fun σ σ' => σ'.vars "kind" = kindCodeF Tn a b ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 80 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = a›
  all_goals have h2 := ‹(σ.arrs "TK").getD 2 0 = b›
  all_goals have hl := ‹3 ≤ Tn → 3 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h1, h2, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k1 : kcode .bit = 1 := rfl
    have k2 : kcode .done = 2 := rfl
    unfold kindCodeF kindF
    split_ifs <;> simp_all [k0, k1, k2] <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkF_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt EF cap nkF 80 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 3
  · have hE : EF toks = .num := by unfold EF; rw [if_pos h2]
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 3)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have h3 : 3 ≤ toks.length := by omega
    have hlen : 3 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have hg : ∀ k, k < 3 → (σ.arrs "TK").getD k 0 = Tok.val (toks.getD k (.num 0)) := fun k hk => by
      have h1 : (σ.arrs "TK").getD k 0 = ((σ.arrs "TK").take toks.length).getD k 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega)]
      rw [h1, hTK, SatFormat.getD_map_val]
    have hb : ∀ k, k < 3 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 1 (by omega)
    have hb2 := hb 2 (by omega)
    have hBt : 12 * Bt ≤ 2 * (Bt * Bt) + 2 * Bt + 12 := by
      rcases Nat.lt_or_ge Bt 5 with h | h
      · interval_cases Bt <;> omega
      · nlinarith
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkF_flat (B := B) toks.length
      (Tok.val (toks.getD 1 (.num 0))) (Tok.val (toks.getD 2 (.num 0))) (by omega) σ
      ⟨hT, hg 1 (by omega), hg 2 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeF EF
    rw [if_neg h2, if_neg h2]

end Lax117284Proofs.Machine.SatNk
