import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.JitCheck
import Lax117284Proofs.Machine.SatSem

/-!
Small runs the straight-line bodies of the reduction of Theorem 7 are made of: an assignment of an
entry of the token array whose position is `c + d x`, of a literal, of a sum, and a comparison.
-/

namespace Lax117284Proofs.Machine.SatOps

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops

variable {B : ℕ}

/-- The position `c + d x`, evaluated. -/
theorem ev_idx (c d : ℕ) (x : String) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (hc : c < B)
    (hd : d < B) (ha : a < B) (h1 : d * a < B) (h2 : c + d * a < B) :
    (add (.lit c) (mul (.lit d) (V x))).evalB B σ = some (c + d * a) := by
  have h := evalB_bin (B := B) (op := .add) (evalB_lit (B := B) (σ := σ) (n := c) hc)
    (evalB_bin (B := B) (op := .mul) (evalB_lit (B := B) (σ := σ) (n := d) hd)
      (evalB_var (B := B) (x := x) (σ := σ) (by omega)) (by simp [hx]; omega))
    (by simp [hx]; omega)
  simpa [hx] using h

/-- An assignment of the entry of the token array at the position `c + d x`. -/
theorem asg_idx (z : String) (c d : ℕ) (x : String) (σ : Env) (arr : List ℕ) (a : ℕ)
    (hA : σ.arrs "TK" = arr) (hx : σ.vars x = a) (hc : c < B) (hd : d < B) (ha : a < B)
    (h1 : d * a < B) (h2 : c + d * a < B) (h3 : c + d * a < arr.length)
    (h4 : arr.getD (c + d * a) 0 < B) :
    Run B (.assign z (.get "TK" (add (.lit c) (mul (.lit d) (V x))))) σ
      (σ.setVar z (arr.getD (c + d * a) 0)) 12 := by
  have hev := ev_idx (B := B) c d x σ a hx hc hd ha h1 h2
  have := RunStep.eval_get B σ "TK" _ (c + d * a) hev (by rw [hA]; exact h3) (by rw [hA]; exact h4)
  rw [hA] at this
  exact (Run.assign this).mono (by simp [Expr.size])

/-- An assignment of a scalar plus a literal. -/
theorem asg_addl (z x : String) (c : ℕ) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B)
    (hc : c < B) (hs : a + c < B) :
    Run B (.assign z (add (V x) (.lit c))) σ (σ.setVar z (a + c)) 5 := by
  have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_lit (B := B) (σ := σ) (n := c) hc) (by simp [hx]; omega)
  have h' : (add (V x) (.lit c)).evalB B σ = some (a + c) := by simpa [hx] using h
  exact (Run.assign h').mono (by simp [Expr.size])

/-- An assignment of a literal. -/
theorem asg_lit (z : String) (c : ℕ) (σ : Env) (hc : c < B) :
    Run B (.assign z (.lit c)) σ (σ.setVar z c) 2 :=
  (Run.assign (evalB_lit hc)).mono (by simp [Expr.size])

/-- The comparison of two scalars for equality. -/
theorem cond_eqv (x y : String) (σ : Env) (a b : ℕ) (hx : σ.vars x = a) (hy : σ.vars y = b)
    (ha : a < B) (hb : b < B) :
    (Cond.eq (V x) (V y)).evalB B σ = some (a == b) := by
  have := evalB_condEq (B := B) (σ := σ) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_var (B := B) (x := y) (σ := σ) (by omega))
  simpa [hx, hy] using this

/-- The comparison of two scalars for order. -/
theorem cond_ltv (x y : String) (σ : Env) (a b : ℕ) (hx : σ.vars x = a) (hy : σ.vars y = b)
    (ha : a < B) (hb : b < B) :
    (Cond.lt (V x) (V y)).evalB B σ = some (decide (a < b)) := by
  have := evalB_condLt (B := B) (σ := σ) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_var (B := B) (x := y) (σ := σ) (by omega))
  simpa [hx, hy] using this

/-- An assignment of an operation on a scalar and a literal. -/
theorem asg_binr (op : Bop) (x : String) (c : ℕ) (z : String) (σ : Env) (a : ℕ)
    (hx : σ.vars x = a) (hB : op.apply a c < B) (ha : a < B) (hc : c < B) :
    Run B (.assign z (.bin op (V x) (.lit c))) σ (σ.setVar z (op.apply a c)) 4 := by
  have h := evalB_bin (B := B) (op := op) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_lit (B := B) (σ := σ) (n := c) hc) (by simpa [hx] using hB)
  have h' : (Expr.bin op (V x) (.lit c)).evalB B σ = some (op.apply a c) := by
    simpa [hx] using h
  exact (Run.assign h').mono (by simp [Expr.size])

/-- The value of `X + d y`. -/
theorem ev_lin (X : Expr) (xv d : ℕ) (y : String) (σ : Env) (a : ℕ)
    (hX : X.evalB B σ = some xv) (hy : σ.vars y = a) (hd : d < B) (ha : a < B)
    (h1 : d * a < B) (h2 : xv + d * a < B) :
    (add X (mul (.lit d) (V y))).evalB B σ = some (xv + d * a) := by
  have h := evalB_bin (B := B) (op := .add) hX
    (evalB_bin (B := B) (op := .mul) (evalB_lit (B := B) (σ := σ) (n := d) hd)
      (evalB_var (B := B) (x := y) (σ := σ) (by omega)) (by simp [hy]; omega))
    (by simp [hy]; omega)
  simpa [hy] using h

/-- An assignment of `c + d y`. -/
theorem asg_linl (z : String) (c d : ℕ) (y : String) (σ : Env) (a : ℕ) (hy : σ.vars y = a)
    (hc : c < B) (hd : d < B) (ha : a < B) (h1 : d * a < B) (h2 : c + d * a < B) :
    Run B (.assign z (add (.lit c) (mul (.lit d) (V y)))) σ (σ.setVar z (c + d * a)) 12 :=
  (Run.assign (ev_lin (.lit c) c d y σ a (evalB_lit hc) hy hd ha h1 h2)).mono
    (by simp [Expr.size])

/-- An assignment of `x + d y`. -/
theorem asg_linv (z x : String) (d : ℕ) (y : String) (σ : Env) (b a : ℕ) (hx : σ.vars x = b)
    (hy : σ.vars y = a) (hb : b < B) (hd : d < B) (ha : a < B) (h1 : d * a < B)
    (h2 : b + d * a < B) :
    Run B (.assign z (add (V x) (mul (.lit d) (V y)))) σ (σ.setVar z (b + d * a)) 12 :=
  (Run.assign (ev_lin (V x) b d y σ a (by
    have := evalB_var (B := B) (x := x) (σ := σ) (by omega); rwa [hx] at this) hy hd ha h1 h2)).mono
    (by simp [Expr.size])

/-- An assignment of a literal is a step of the same shape as the others. -/
theorem cond_eql (x : String) (c : ℕ) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B)
    (hc : c < B) : (Cond.eq (V x) (.lit c)).evalB B σ = some (a == c) := by
  have := evalB_condEq (B := B) (σ := σ) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_lit (B := B) (σ := σ) (n := c) hc)
  simpa [hx] using this

/-- The comparison of a scalar with a literal. -/
theorem cond_ltl (x : String) (c : ℕ) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B)
    (hc : c < B) : (Cond.lt (V x) (.lit c)).evalB B σ = some (decide (a < c)) := by
  have := evalB_condLt (B := B) (σ := σ) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_lit (B := B) (σ := σ) (n := c) hc)
  simpa [hx] using this

/-- The comparison of a literal with a scalar. -/
theorem cond_lll (c : ℕ) (x : String) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (ha : a < B)
    (hc : c < B) : (Cond.lt (.lit c) (V x)).evalB B σ = some (decide (c < a)) := by
  have := evalB_condLt (B := B) (σ := σ) (evalB_lit (B := B) (σ := σ) (n := c) hc)
    (evalB_var (B := B) (x := x) (σ := σ) (by omega))
  simpa [hx] using this

/-- An assignment of the entry of the token array at a literal position. -/
theorem asg_tkl (z : String) (k : ℕ) (σ : Env) (arr : List ℕ) (hA : σ.arrs "TK" = arr)
    (hk : k < B) (h1 : k < arr.length) (h3 : arr.getD k 0 < B) :
    Run B (.assign z (.get "TK" (.lit k))) σ (σ.setVar z (arr.getD k 0)) 4 := by
  have hev := evalB_lit (B := B) (σ := σ) (n := k) hk
  have := RunStep.eval_get B σ "TK" (.lit k) k hev (by rw [hA]; exact h1) (by rw [hA]; exact h3)
  rw [hA] at this
  exact (Run.assign this).mono (by simp [Expr.size])

end Lax117284Proofs.Machine.SatOps
