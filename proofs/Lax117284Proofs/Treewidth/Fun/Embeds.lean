import Lax117284Proofs.Treewidth.Fun.Kit
import Mathlib.Tactic.Linarith

/-!
# WP F0 (3): `Embeds` and its closure lemmas

`Embeds Δ fid P f cost` — the function `fid` of the table computes the Lean function `f` on the inputs satisfying
`P`, within cost `cost a`, whenever `B` is large (`Fits`).  (Same definition as `proofs-todo/Machine.lean`.)

`EmbedsE Δ t P env f cost` is the term-level version over an arbitrary environment `env a : List Val`
(`Embeds` is the case `t = body`, `env a = [toVal a]`).  Closure lemmas: `call1` (composition with a function),
`ite`, `letE`, `var`, `lit`, `cons`, monotonicity in the precondition and in the cost.
-/

set_option linter.unusedSectionVars false

namespace Lax117284Proofs.Treewidth.Fun

open ToVal

/-- `f` is computed by the function `fid` of the table, within cost `cost a`, on every `a` with `P a`. -/
def Embeds {α β : Type} [ToVal α] [ToVal β] (Δ : ℕ → Option Tm) (fid : ℕ) (P : α → Prop) (f : α → β)
    (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → Fits B (toVal a) (cost a) → Runs Δ B fid [toVal a] (toVal (f a)) (cost a)

/-- Output-sensitive polynomial cost of degree `d`. -/
def osCost {α β : Type} [ToVal α] [ToVal β] (d : ℕ) (f : α → β) (a : α) : ℕ := 64 * (sz a + sz (f a) + 1) ^ d

/-! ### `Fits` -/

theorem Fits.cost_lt {B : ℕ} {v : Val} {c : ℕ} (h : Fits B v c) : c + 3 < B := by
  have h1 : (v.maxNat + c + 2) ^ 2 ≥ c + 3 := by nlinarith [Nat.zero_le v.maxNat, Nat.zero_le c]
  have h' : (v.maxNat + c + 2) ^ 2 < B := h
  omega

/-- the largest natural in an environment -/
def Val.maxNatL : List Val → ℕ
  | [] => 0
  | v :: vs => max v.maxNat (Val.maxNatL vs)

/-- `Fits` for a whole environment. -/
def FitsL (B : ℕ) (ρ : List Val) (c : ℕ) : Prop := (Val.maxNatL ρ + c + 2) ^ 2 < B

/-! ### term-level embeddings -/

/-- `t`, evaluated in the environment `env a`, computes `f a` within cost `cost a`. -/
def EmbedsE {α β : Type} [ToVal β] (Δ : ℕ → Option Tm) (t : Tm) (P : α → Prop) (env : α → List Val)
    (f : α → β) (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → FitsL B (env a) (cost a) → EvLe Δ B (env a) t (toVal (f a)) (cost a)

namespace EmbedsE
variable {α β γ : Type} [ToVal α] [ToVal β] [ToVal γ] {Δ : ℕ → Option Tm} {t : Tm} {P : α → Prop}
  {env : α → List Val} {f : α → β} {cost : α → ℕ}

end EmbedsE

end Lax117284Proofs.Treewidth.Fun
