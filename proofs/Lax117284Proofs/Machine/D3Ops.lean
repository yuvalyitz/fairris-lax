import Lax117284Proofs.Machine.ILoop
import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.MisBlk
import Lax117284Proofs.Machine.SatRank
import Lax117284Proofs.Machine.SatOps

/-!
Reads and writes of the working array `R`, the table of the dynamic program.
-/

namespace Lax117284Proofs.Machine.D3Ops

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out

variable {B : ℕ}

/-- An assignment of the entry of `R` at the position a scalar holds. -/
theorem asg_R (z x : String) (σ : Env) (a : ℕ) (hx : σ.vars x = a) (hlen : a < (σ.arrs "R").length)
    (hv : (σ.arrs "R").getD a 0 < B) (hB : a < B) :
    Run B (.assign z (.get "R" (V x))) σ (σ.setVar z ((σ.arrs "R").getD a 0)) 3 := by
  have hev : (V x : Expr).evalB B σ = some a := by
    have := evalB_var (B := B) (x := x) (σ := σ) (by omega)
    rwa [hx] at this
  have := RunStep.eval_get B σ "R" (V x) a hev hlen hv
  exact (Run.assign this).mono (by simp [Expr.size])

/-- An assignment of the entry of `R` at the sum of two scalars. -/
theorem asg_R2 (z x y : String) (σ : Env) (a b : ℕ) (hx : σ.vars x = a) (hy : σ.vars y = b)
    (hlen : a + b < (σ.arrs "R").length) (hv : (σ.arrs "R").getD (a + b) 0 < B)
    (hB : a + b < B) (ha : a < B) (hb : b < B) :
    Run B (.assign z (.get "R" (add (V x) (V y)))) σ
      (σ.setVar z ((σ.arrs "R").getD (a + b) 0)) 5 := by
  have hev : (add (V x) (V y)).evalB B σ = some (a + b) := by
    have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
      (evalB_var (B := B) (x := y) (σ := σ) (by omega)) (by simp [hx, hy]; omega)
    simpa [hx, hy] using h
  have := RunStep.eval_get B σ "R" _ (a + b) hev hlen hv
  exact (Run.assign this).mono (by simp [Expr.size])

/-- A store into `R` at a position held in a scalar. -/
theorem store_R (x v : String) (σ : Env) (a w : ℕ) (hx : σ.vars x = a) (hv : σ.vars v = w)
    (hlen : a < (σ.arrs "R").length) (hB : a < B) (hwB : w < B) :
    Run B (.store "R" (V x) (V v)) σ (σ.setArr "R" a w) 3 := by
  have hi : (V x : Expr).evalB B σ = some a := by
    have := evalB_var (B := B) (x := x) (σ := σ) (by omega)
    rwa [hx] at this
  have he : (V v : Expr).evalB B σ = some w := by
    have := evalB_var (B := B) (x := v) (σ := σ) (by omega)
    rwa [hv] at this
  exact (Run.store hi he hlen).mono (by simp [Expr.size])

/-- A store of a constant into `R` at a position held in a scalar. -/
theorem store_R_lit (x : String) (σ : Env) (a w : ℕ) (hx : σ.vars x = a)
    (hlen : a < (σ.arrs "R").length) (hB : a < B) (hwB : w < B) :
    Run B (.store "R" (V x) (.lit w)) σ (σ.setArr "R" a w) 3 := by
  have hi : (V x : Expr).evalB B σ = some a := by
    have := evalB_var (B := B) (x := x) (σ := σ) (by omega)
    rwa [hx] at this
  have he : (Expr.lit w).evalB B σ = some w := evalB_lit hwB
  exact (Run.store hi he hlen).mono (by simp [Expr.size])

/-- A store into `R` at the sum of two scalars. -/
theorem store_R2 (x y v : String) (σ : Env) (a b w : ℕ) (hx : σ.vars x = a) (hy : σ.vars y = b)
    (hv : σ.vars v = w) (hlen : a + b < (σ.arrs "R").length) (hB : a + b < B) (ha : a < B)
    (hb : b < B) (hwB : w < B) :
    Run B (.store "R" (add (V x) (V y)) (V v)) σ (σ.setArr "R" (a + b) w) 5 := by
  have hi : (add (V x) (V y)).evalB B σ = some (a + b) := by
    have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
      (evalB_var (B := B) (x := y) (σ := σ) (by omega)) (by simp [hx, hy]; omega)
    simpa [hx, hy] using h
  have he : (V v : Expr).evalB B σ = some w := by
    have := evalB_var (B := B) (x := v) (σ := σ) (by omega)
    rwa [hv] at this
  exact (Run.store hi he hlen).mono (by simp [Expr.size])

@[simp] lemma setArr_vars (σ : Env) (a : String) (i v : ℕ) (y : String) :
    (σ.setArr a i v).vars y = σ.vars y := Eq.trans rfl rfl

@[simp] lemma setArr_arrs_R (σ : Env) (i v : ℕ) :
    (σ.setArr "R" i v).arrs "R" = (σ.arrs "R").set i v := by simp [Env.setArr]

@[simp] lemma setArr_arrs_ne (σ : Env) (a b : String) (i v : ℕ) (h : b ≠ a) :
    (σ.setArr a i v).arrs b = σ.arrs b := by simp [Env.setArr, h]

end Lax117284Proofs.Machine.D3Ops
