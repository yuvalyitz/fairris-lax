import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.TsRenFormat

/-!
What the format of a 2-CNF formula expects next, as a command: a number for each of the two
counts, and then a number and a bit alternately until every position has been read.
-/

namespace Lax117284Proofs.Machine.TsRenNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TsRenFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- What the format expects, the number of clauses being `TK[1]`. -/
def nkR : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.lit 4) (.get "TK" (.lit 1))))
        (.ite (.lt (V "j") (V "n3"))
          (.assign "kind" (sub (V "j") (mul (div (V "j") (.lit 2)) (.lit 2))))
          (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the number of clauses being `C`. -/
def kindCodeR (Tn C : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindR C (Tn - 2))

variable {B : ℕ}

theorem nkR_flat (Tn C : ℕ) (hB : 4 * C + Tn + C + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 1 0 = C ∧
        (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkR
      (fun σ σ' => σ'.vars "kind" = kindCodeR Tn C ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 80 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = C›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k1 : kcode .bit = 1 := rfl
    have k2 : kcode .done = 2 := rfl
    unfold kindCodeR kindR
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

/-- **The command meets the contract of the tokenizer.** -/
theorem nkR_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt ER cap nkR 80 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · have hE : ER toks = .num := by unfold ER; rw [if_pos h2]
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
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
      rw [h1, hTK, TsRenFormat.getD_map_val]
    have hb : ∀ k, k < 2 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 1 (by omega)
    have hBt : 10 * Bt ≤ 2 * (Bt * Bt) + 2 * Bt + 12 := by
      rcases Nat.lt_or_ge Bt 5 with h | h
      · interval_cases Bt <;> omega
      · nlinarith
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkR_flat (B := B) toks.length
      (Tok.val (toks.getD 1 (.num 0))) (by omega) σ
      ⟨hT, hg 1 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeR ER
    rw [if_neg h2, if_neg h2]

end Lax117284Proofs.Machine.TsRenNk
