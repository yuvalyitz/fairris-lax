import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.InstSem

/-!
What the format of an instance with a fairness parameter expects next, as a command.
-/

namespace Lax117284Proofs.Machine.UNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.InstSem

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev add (e f : Expr) : Expr := .bin .add e f

/-- What the format expects, the counts and the parameter being `n`, `m`: a number as long as the
table has not been read, and the end after it. -/
def nkU : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (add (mul (.lit 2) (mul (.get "TK" (.lit 1)) (.get "TK" (.lit 0))))
          (.lit 1)))
        (.ite (.lt (V "j") (V "n3")) (set "kind" 0) (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the counts being `n` and `m`. -/
def kindCode (Tn n m : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindI eU n m (Tn - 2))

variable {B : ℕ}

theorem nkU_flat (Tn n m : ℕ) (hB : 2 * (m * n) + Tn + 8 < B) (hm : m + 8 < B) (hn : n + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (σ.arrs "TK").getD 1 0 = m ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkU
      (fun σ σ' => σ'.vars "kind" = kindCode Tn n m ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 60 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = m›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k2 : kcode .done = 2 := rfl
    have hE1 : eU n m = 1 := rfl
    unfold kindCode kindI
    split_ifs <;> omega)

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
theorem nkU_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt (EI eU) cap nkU 60 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · -- fewer than two tokens: a count is expected
    have hE : EI eU toks = .num := by
      rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · cases a <;> rfl
      · simp at h2
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · -- the counts are known
    rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    have ha : a.kind = .num := by simpa [EI] using hfol 0 (by simp)
    have hb : b.kind = .num := by
      have := hfol 1 (by simp)
      simpa [EI] using this
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := by cases a <;> simp_all [Tok.kind]
    obtain ⟨m, rfl⟩ : ∃ m, b = .num m := by cases b <;> simp_all [Tok.kind]
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hm : m < Bt := hsm (.num m) (by simp)
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    have g1 : (σ.arrs "TK").getD 1 0 = m := by
      have := congrArg (fun l => l.getD 1 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    have hmn : m * n ≤ Bt * Bt := Nat.mul_le_mul hm.le hn.le
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkU_flat (B := B) (rest.length + 2) n m (by omega)
      (by omega) (by omega) σ ⟨by rw [hT], g0, g1, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, EI_cons]
    simp [kindCode]

end Lax117284Proofs.Machine.UNk
