import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.JitSem
import Lax117284Proofs.Machine.Flag

/-!
The pass over the table of processing times that checks that every job takes some time and is not
due before it starts.
-/

namespace Lax117284Proofs.Machine.JitCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.JitSem

variable {B : ℕ}

/-- An assignment of an operation on a literal and a scalar. -/
theorem asg_binl (op : Bop) (c : ℕ) (y z : String) (σ : Env) (b : ℕ) (hy : σ.vars y = b)
    (hB : op.apply c b < B) (hc : c < B) (hb : b < B) :
    Run B (.assign z (.bin op (.lit c) (V y))) σ (σ.setVar z (op.apply c b)) 4 := by
  have h := evalB_bin (B := B) (op := op) (evalB_lit (B := B) (σ := σ) (n := c) hc)
    (evalB_var (B := B) (x := y) (σ := σ) (by omega)) (by simpa [hy] using hB)
  have h' : (Expr.bin op (.lit c) (V y)).evalB B σ = some (op.apply c b) := by
    simpa [hy] using h
  exact (Run.assign h').mono (by simp [Expr.size])

/-- An assignment of the entry of the token array at the position in a scalar. -/
theorem asg_tkv (x z : String) (σ : Env) (arr : List ℕ) (a : ℕ) (hA : σ.arrs "TK" = arr)
    (hx : σ.vars x = a) (h1 : a < arr.length) (h2 : a < B) (h3 : arr.getD a 0 < B) :
    Run B (.assign z (.get "TK" (V x))) σ (σ.setVar z (arr.getD a 0)) 3 := by
  have hev : (Expr.get "TK" (V x)).evalB B σ = some (arr.getD a 0) := by
    have hix : (V x).evalB B σ = some a := by
      have := evalB_var (B := B) (x := x) (σ := σ) (by omega)
      rwa [hx] at this
    have := RunStep.eval_get B σ "TK" (V x) a hix
      (by rw [hA]; exact h1) (by rw [hA]; exact h3)
    rwa [hA] at this
  exact (Run.assign hev).mono (by simp [Expr.size])

/-- The cell of the table of processing times: its position and the position of the due date. -/
def cellIdx : Com :=
  .seq (.assign "q" (.bin .div (V "i") (V "n")))
  (.seq (.assign "tt" (mul (V "q") (V "n")))
  (.seq (.assign "jj" (sub (V "i") (V "tt")))
  (.seq (.assign "ip" (add (V "o") (V "i")))
    (.assign "ij" (.bin .add (.lit 2) (V "jj"))))))

/-- The scalars `cellIdx` assigns. -/
def AI : List String := ["q", "tt", "jj", "ip", "ij"]

/-- **The positions of a cell.** -/
theorem cellIdx_run (n o c : ℕ) (σ : Env) (hi : σ.vars "i" = c) (hn : σ.vars "n" = n)
    (ho : σ.vars "o" = 2 + n) (hc : c < B) (hnB : n < B) (hn0 : 0 < n)
    (hoB : 2 + n + c < B) :
    ∃ σ', Run B cellIdx σ σ' 30 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.vars "ip" = 2 + n + c ∧ σ'.vars "ij" = 2 + (c - c / n * n) ∧
      ∀ y, y ∉ AI → σ'.vars y = σ.vars y := by
  have hdm : n * (c / n) + c % n = c := Nat.div_add_mod c n
  have hq : c / n * n ≤ c := Nat.div_mul_le_self c n
  have hqc : c / n ≤ c := Nat.div_le_self c n
  have s1 : Run B (.assign "q" (.bin .div (V "i") (V "n"))) σ (σ.setVar "q" (c / n)) 4 := by
    have := asg_bin (B := B) .div "i" "n" "q" σ c n hi hn (by
      show c / n < B; omega) (by omega) (by omega)
    simpa only [Bop.apply_div] using this
  set σ1 := σ.setVar "q" (c / n) with hσ1
  have s1q : σ1.vars "q" = c / n := by simp [hσ1, Env.setVar]
  have s1n : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have s1i : σ1.vars "i" = c := by simp [hσ1, Env.setVar, hi]
  have s2 : Run B (.assign "tt" (mul (V "q") (V "n"))) σ1 (σ1.setVar "tt" (c / n * n)) 4 := by
    have := asg_bin (B := B) .mul "q" "n" "tt" σ1 (c / n) n s1q s1n (by
      show c / n * n < B; omega) (by omega) (by omega)
    simpa only [Bop.apply_mul] using this
  set σ2 := σ1.setVar "tt" (c / n * n) with hσ2
  have s2tt : σ2.vars "tt" = c / n * n := by simp [hσ2, Env.setVar]
  have s2i : σ2.vars "i" = c := by simp [hσ2, Env.setVar, s1i]
  have s3 : Run B (.assign "jj" (sub (V "i") (V "tt"))) σ2 (σ2.setVar "jj" (c - c / n * n)) 4 := by
    have := asg_bin (B := B) .sub "i" "tt" "jj" σ2 c (c / n * n) s2i s2tt (by
      show c - c / n * n < B; omega) (by omega) (by omega)
    simpa only [Bop.apply_sub] using this
  set σ3 := σ2.setVar "jj" (c - c / n * n) with hσ3
  have s3jj : σ3.vars "jj" = c - c / n * n := by simp [hσ3, Env.setVar]
  have s3o : σ3.vars "o" = 2 + n := by simp [hσ3, hσ2, hσ1, Env.setVar, ho]
  have s3i : σ3.vars "i" = c := by simp [hσ3, Env.setVar, s2i]
  have s4 : Run B (.assign "ip" (add (V "o") (V "i"))) σ3 (σ3.setVar "ip" (2 + n + c)) 4 :=
    asg_bin (B := B) .add "o" "i" "ip" σ3 (2 + n) c s3o s3i (by
      show 2 + n + c < B; omega) (by omega) (by omega)
  set σ4 := σ3.setVar "ip" (2 + n + c) with hσ4
  have s4jj : σ4.vars "jj" = c - c / n * n := by simp [hσ4, Env.setVar, s3jj]
  have s5 : Run B (.assign "ij" (.bin .add (.lit 2) (V "jj"))) σ4
      (σ4.setVar "ij" (2 + (c - c / n * n))) 4 :=
    asg_binl (B := B) .add 2 "jj" "ij" σ4 (c - c / n * n) s4jj (by
      show 2 + (c - c / n * n) < B; omega) (by omega) (by omega)
  refine ⟨σ4.setVar "ij" (2 + (c - c / n * n)), (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono
    (by omega), ?_⟩
  refine ⟨by simp [hσ1, hσ2, hσ3, hσ4, Env.setVar], by simp [hσ1, hσ2, hσ3, hσ4, Env.setVar],
    by simp [hσ1, hσ2, hσ3, hσ4, Env.setVar], by simp [hσ1, hσ2, hσ3, hσ4, Env.setVar], ?_⟩
  intro y hy
  simp only [AI, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  simp [hσ1, hσ2, hσ3, hσ4, Env.setVar, h1, h2, h3, h4, h5]

end Lax117284Proofs.Machine.JitCheck
