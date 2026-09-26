import Lax117284Proofs.Machine.Emit

/-!
Small runs the straight-line bodies are made of: an assignment of an operation on two scalars, of
an entry of the token array, a written bit, and a clause written as two variables with their signs.
-/

namespace Lax117284Proofs.Machine.T9Ops

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit

variable {B : ℕ}

/-- An assignment of an operation on two scalars. -/
theorem asg_bin (op : Bop) (x y z : String) (σ : Env) (a b : ℕ) (hx : σ.vars x = a)
    (hy : σ.vars y = b) (hB : op.apply a b < B) (ha : a < B) (hb : b < B) :
    Run B (.assign z (.bin op (V x) (V y))) σ (σ.setVar z (op.apply a b)) 4 := by
  have h := evalB_bin (B := B) (op := op) (evalB_var (B := B) (x := x) (σ := σ) (by omega))
    (evalB_var (B := B) (x := y) (σ := σ) (by omega)) (by simpa [hx, hy] using hB)
  have h' : (Expr.bin op (V x) (V y)).evalB B σ = some (op.apply a b) := by
    simpa [hx, hy] using h
  exact (Run.assign h').mono (by simp [Expr.size])

/-- The entry of the token array at `2 + 2 x + o`. -/
theorem ev_tk (x : String) (o : ℕ) (σ : Env) (arr : List ℕ) (a : ℕ) (hA : σ.arrs "TK" = arr)
    (hx : σ.vars x = a) (h1 : 2 + 2 * a + o < arr.length) (h2 : 2 + 2 * a + o < B)
    (h3 : arr.getD (2 + 2 * a + o) 0 < B) :
    (Expr.get "TK" (add (add (.lit 2) (mul (.lit 2) (V x))) (.lit o))).evalB B σ
      = some (arr.getD (2 + 2 * a + o) 0) := by
  have hev : (add (add (.lit 2) (mul (.lit 2) (V x))) (.lit o)).evalB B σ = some (2 + 2 * a + o) := by
    have h := evalB_bin (B := B) (op := .add)
      (evalB_bin (B := B) (op := .add) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
        (evalB_bin (B := B) (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
          (evalB_var (B := B) (x := x) (σ := σ) (by omega)) (by simp [hx]; omega))
        (by simp [hx]; omega))
      (evalB_lit (B := B) (σ := σ) (n := o) (by omega)) (by simp [hx]; omega)
    simpa [hx] using h
  have := RunStep.eval_get B σ "TK" _ (2 + 2 * a + o) hev (by rw [hA]; exact h1) (by rw [hA]; exact h3)
  rwa [hA] at this

/-- An assignment of the entry of the token array at `2 + 2 x + o`. -/
theorem asg_tk (x z : String) (o : ℕ) (σ : Env) (arr : List ℕ) (a : ℕ) (hA : σ.arrs "TK" = arr)
    (hx : σ.vars x = a) (h1 : 2 + 2 * a + o < arr.length) (h2 : 2 + 2 * a + o < B)
    (h3 : arr.getD (2 + 2 * a + o) 0 < B) :
    Run B (.assign z (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V x))) (.lit o)))) σ
      (σ.setVar z (arr.getD (2 + 2 * a + o) 0)) 10 :=
  (Run.assign (ev_tk x o σ arr a hA hx h1 h2 h3)).mono (by simp [Expr.size])

/-- A written bit. -/
theorem write_bit (b : ℕ) (hb : b < B) (σ : Env) :
    Run B (.write (.lit b)) σ { σ with out := σ.out ++ [b] } 2 :=
  (Run.write (evalB_lit hb)).mono (by simp [Expr.size])

/-- A clause: the variable, the sign, the variable, the sign. -/
def emitClause (u v : String) (s t : ℕ) : Com :=
  .seq (emitVar u) (.seq (.write (.lit s)) (.seq (emitVar v) (.write (.lit t))))

theorem emitClause_run (Sz : ℕ) (u v : String) (s t : ℕ) (σ : Env)
    (hs : ∀ w, w + 4 < B → w.size ≤ Sz) (hu : u ∉ ["v", "s", "u", "i2"])
    (hv : v ∉ ["v", "s", "u", "i2"]) (huB : σ.vars u + 4 < B) (hvB : σ.vars v + 4 < B)
    (hsB : s < B) (htB : t < B) :
    ∃ σ', Run B (emitClause u v s t) σ σ' (2 * (48 * Sz + 50) + 4) ∧
      σ'.out = σ.out ++ (bitsNat (σ.vars u) ++ [s] ++ bitsNat (σ.vars v) ++ [t]) ∧
      (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) u Sz σ ⟨huB, hs _ huB⟩
  have r2 := write_bit (B := B) s hsB σ1
  set σ2 : Env := { σ1 with out := σ1.out ++ [s] } with hσ2
  have hv2 : σ2.vars v = σ.vars v := by simp [hσ2]; exact v1 v hv
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitVar_spec (B := B) v Sz σ2
    ⟨by rw [hv2]; exact hvB, by rw [hv2]; exact hs _ hvB⟩
  have r4 := write_bit (B := B) t htB σ3
  refine ⟨{ σ3 with out := σ3.out ++ [t] }, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_,
    fun y hy => ?_, ?_⟩
  · have hv1 : σ1.vars v = σ.vars v := v1 v hv
    simp only [o3, hσ2, o1, hv2, hv1, List.append_assoc]
  · simp only
    rw [v3 y hy]
    simp only [hσ2]
    exact v1 y hy
  · simp only
    rw [a3]; simp [hσ2, a1]

end Lax117284Proofs.Machine.T9Ops
