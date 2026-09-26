import Lax117284Proofs.Machine.SatOps

/-!
Arithmetic expressions without array reads evaluate to their denotation whenever every intermediate
value is a word, and so an assignment of such an expression is a single step.
-/

namespace Lax117284Proofs.Machine.MisBlk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out

variable {B : ℕ}

/-- The value of an expression without array reads. -/
def den (σ : Env) : Expr → ℕ
  | .lit n => n
  | .var x => σ.vars x
  | .get _ _ => 0
  | .bin op e f => op.apply (den σ e) (den σ f)

/-- Every intermediate value of the expression is a word. -/
def small (B : ℕ) (σ : Env) : Expr → Prop
  | .lit n => n < B
  | .var x => σ.vars x < B
  | .get _ _ => False
  | .bin op e f => small B σ e ∧ small B σ f ∧ op.apply (den σ e) (den σ f) < B

theorem evalB_den {σ : Env} : ∀ {e : Expr}, small B σ e → e.evalB B σ = some (den σ e)
  | .lit n, h => evalB_lit h
  | .var x, h => evalB_var h
  | .get _ _, h => absurd h (by simp [small])
  | .bin op e f, h => evalB_bin (evalB_den h.1) (evalB_den h.2.1) h.2.2

/-- **An assignment of an expression without array reads.** -/
theorem asgE (z : String) (e : Expr) (σ : Env) (h : small B σ e) :
    Run B (.assign z e) σ (σ.setVar z (den σ e)) (1 + e.size) :=
  Run.assign (evalB_den h)

/-- The test of two expressions for equality. -/
theorem condEq_den (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f) :
    (Cond.eq e f).evalB B σ = some (decide (den σ e = den σ f)) := by
  have := evalB_condEq (B := B) (σ := σ) (evalB_den he) (evalB_den hf)
  rw [this]
  exact congrArg some (beq_eq_decide _ _)

/-- The test of two expressions for order. -/
theorem condLt_den (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f) :
    (Cond.lt e f).evalB B σ = some (decide (den σ e < den σ f)) :=
  evalB_condLt (evalB_den he) (evalB_den hf)

theorem condEq_true (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f)
    (h : den σ e = den σ f) : (Cond.eq e f).evalB B σ = some true := by
  rw [condEq_den e f σ he hf]; exact congrArg some (decide_eq_true h)

theorem condEq_false (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f)
    (h : den σ e ≠ den σ f) : (Cond.eq e f).evalB B σ = some false := by
  rw [condEq_den e f σ he hf]; exact congrArg some (decide_eq_false h)

theorem condLt_true (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f)
    (h : den σ e < den σ f) : (Cond.lt e f).evalB B σ = some true := by
  rw [condLt_den e f σ he hf]; exact congrArg some (decide_eq_true h)

theorem condLt_false (e f : Expr) (σ : Env) (he : small B σ e) (hf : small B σ f)
    (h : ¬ den σ e < den σ f) : (Cond.lt e f).evalB B σ = some false := by
  rw [condLt_den e f σ he hf]; exact congrArg some (decide_eq_false h)

@[simp] lemma den_lit (σ : Env) (n : ℕ) : den σ (.lit n) = n := Eq.trans rfl rfl
@[simp] lemma den_var (σ : Env) (x : String) : den σ (.var x) = σ.vars x := Eq.trans rfl rfl
@[simp] lemma den_bin (σ : Env) (op : Bop) (e f : Expr) :
    den σ (.bin op e f) = op.apply (den σ e) (den σ f) := Eq.trans rfl rfl
@[simp] lemma small_lit (σ : Env) (n : ℕ) : small B σ (.lit n) ↔ n < B := Iff.rfl
@[simp] lemma small_var (σ : Env) (x : String) : small B σ (.var x) ↔ σ.vars x < B := Iff.rfl
@[simp] lemma small_bin (σ : Env) (op : Bop) (e f : Expr) :
    small B σ (.bin op e f) ↔
      small B σ e ∧ small B σ f ∧ op.apply (den σ e) (den σ f) < B := Iff.rfl

end Lax117284Proofs.Machine.MisBlk
