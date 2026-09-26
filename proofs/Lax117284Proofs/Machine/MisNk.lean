import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.MisFormat

/-!
What the format of an instance of Multicoloured Independent Set expects next, as a command: a
number for each of the two counts, and then a bit for each entry of the matrix.
-/

namespace Lax117284Proofs.Machine.MisNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.MisFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- What the format expects, the counts being `TK[0]` and `TK[1]`: with `V` their product, a bit
as long as the number of bits read is below `V * V`, which is `j / V < V`. -/
def nkM : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.get "TK" (.lit 0)) (.get "TK" (.lit 1))))
        (.ite (.lt (div (V "j") (V "n3")) (V "n3")) (set "kind" 1) (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the counts being `a` and `b`. -/
def kindCodeM (Tn a b : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindM a b (Tn - 2))

variable {B : ℕ}

lemma lt_mul_iff (j V : ℕ) : j / V < V ↔ j < V * V := by
  rcases Nat.eq_zero_or_pos V with h | h
  · subst h; simp
  · exact Nat.div_lt_iff_lt_mul h

theorem nkM_flat (Tn a b : ℕ) (hB : a * b + Tn + a + b + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = a ∧
        (σ.arrs "TK").getD 1 0 = b ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkM
      (fun σ σ' => σ'.vars "kind" = kindCodeM Tn a b ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 80 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = a›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = b›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals try (have := Nat.div_le_self (Tn - 2) (a * b); omega)
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    unfold kindCodeM kindM
    first
    | (rw [if_pos (by omega)])
    | (rw [if_neg (by omega), if_pos ((lt_mul_iff _ _).1 ‹(Tn - 2) / (a * b) < a * b›)]; rfl)
    | (rw [if_neg (by omega), if_neg (fun h => absurd ((lt_mul_iff _ _).2 h)
        (Nat.not_lt.mpr ‹a * b ≤ (Tn - 2) / (a * b)›))]; rfl))

theorem setKind_spec (v : ℕ) (hv : v < B) :
    Spec B (fun _ => True) (set "kind" v)
      (fun σ σ' => σ'.vars "kind" = v ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkM_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt EM cap nkM 80 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · have hE : EM toks = .num := by unfold EM; rw [if_pos h2]
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
      rw [h1, hTK, MisFormat.getD_map_val]
    have hb : ∀ k, k < 2 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 0 (by omega)
    have hb1 := hb 1 (by omega)
    have hab : Tok.val (toks.getD 0 (.num 0)) * Tok.val (toks.getD 1 (.num 0)) ≤ Bt * Bt :=
      Nat.mul_le_mul ha.le hb1.le
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkM_flat (B := B) toks.length
      (Tok.val (toks.getD 0 (.num 0))) (Tok.val (toks.getD 1 (.num 0))) (by omega) σ
      ⟨hT, hg 0 (by omega), hg 1 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeM EM
    rw [if_neg h2, if_neg h2]

end Lax117284Proofs.Machine.MisNk
