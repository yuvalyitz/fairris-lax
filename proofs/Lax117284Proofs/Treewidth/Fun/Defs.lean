import Mathlib.Data.List.Basic

/-!
# The functional fragment F (WP F0): values, terms, big-step semantics with cost

Definitions copied from `proofs-todo/Machine.lean` (see `PLAN-machine.md` §2).  The compiler of `Ev` to IMP+ lives elsewhere;
this file has only the syntax and semantics.  Owners of WP F0/F1/V1 extend this package; do not change these definitions without
telling the other owners (change = coordinate through the coordinator).
-/

namespace Lax117284Proofs.Treewidth.Fun

/-- Values: naturals and pairs (lists are `cons a (cons b … (nat 0))`). -/
inductive Val where
  | nat (n : ℕ)
  | cons (a b : Val)

def Val.size : Val → ℕ
  | .nat _ => 1
  | .cons a b => a.size + b.size + 1

def Val.maxNat : Val → ℕ
  | .nat n => n
  | .cons a b => max a.maxNat b.maxNat

/-- Terms: first-order, call by value, de Bruijn variables into the environment list; recursion through
the function table; `callv` calls a function whose id is a run-time natural (defunctionalised higher order). -/
inductive Tm where
  | lit (n : ℕ) | var (i : ℕ)
  | add (a b : Tm) | sub (a b : Tm) | mul (a b : Tm) | lt (a b : Tm) | eq (a b : Tm)
  | cons (a b : Tm) | fst (a : Tm) | snd (a : Tm) | isNat (a : Tm)
  | ite (c t e : Tm) | letE (a b : Tm)
  | call (f : ℕ) (args : List Tm)
  | callv (f : Tm) (args : List Tm)

mutual
/-- Big-step evaluation with cost (= number of constructs evaluated); every natural produced is `< B`. -/
inductive Ev (Δ : ℕ → Option Tm) (B : ℕ) : List Val → Tm → Val → ℕ → Prop
  | lit {ρ : List Val} {n : ℕ} : n < B → Ev Δ B ρ (.lit n) (.nat n) 1
  | var {ρ : List Val} {i : ℕ} {v : Val} : ρ[i]? = some v → Ev Δ B ρ (.var i) v 1
  | add {ρ a b m n c₁ c₂} : Ev Δ B ρ a (.nat m) c₁ → Ev Δ B ρ b (.nat n) c₂ → m + n < B →
      Ev Δ B ρ (.add a b) (.nat (m + n)) (c₁ + c₂ + 1)
  | sub {ρ a b m n c₁ c₂} : Ev Δ B ρ a (.nat m) c₁ → Ev Δ B ρ b (.nat n) c₂ →
      Ev Δ B ρ (.sub a b) (.nat (m - n)) (c₁ + c₂ + 1)
  | mul {ρ a b m n c₁ c₂} : Ev Δ B ρ a (.nat m) c₁ → Ev Δ B ρ b (.nat n) c₂ → m * n < B →
      Ev Δ B ρ (.mul a b) (.nat (m * n)) (c₁ + c₂ + 1)
  | lt {ρ a b m n c₁ c₂} : Ev Δ B ρ a (.nat m) c₁ → Ev Δ B ρ b (.nat n) c₂ →
      Ev Δ B ρ (.lt a b) (.nat (if m < n then 1 else 0)) (c₁ + c₂ + 1)
  | eq {ρ a b m n c₁ c₂} : Ev Δ B ρ a (.nat m) c₁ → Ev Δ B ρ b (.nat n) c₂ →
      Ev Δ B ρ (.eq a b) (.nat (if m = n then 1 else 0)) (c₁ + c₂ + 1)
  | cons {ρ a b u v c₁ c₂} : Ev Δ B ρ a u c₁ → Ev Δ B ρ b v c₂ → Ev Δ B ρ (.cons a b) (.cons u v) (c₁ + c₂ + 1)
  | fst {ρ a u v c} : Ev Δ B ρ a (.cons u v) c → Ev Δ B ρ (.fst a) u (c + 1)
  | snd {ρ a u v c} : Ev Δ B ρ a (.cons u v) c → Ev Δ B ρ (.snd a) v (c + 1)
  | isNatT {ρ a n c} : Ev Δ B ρ a (.nat n) c → Ev Δ B ρ (.isNat a) (.nat 1) (c + 1)
  | isNatF {ρ a u v c} : Ev Δ B ρ a (.cons u v) c → Ev Δ B ρ (.isNat a) (.nat 0) (c + 1)
  | iteT {ρ cnd t e n v c₁ c₂} : Ev Δ B ρ cnd (.nat n) c₁ → n ≠ 0 → Ev Δ B ρ t v c₂ →
      Ev Δ B ρ (.ite cnd t e) v (c₁ + c₂ + 1)
  | iteF {ρ cnd t e v c₁ c₂} : Ev Δ B ρ cnd (.nat 0) c₁ → Ev Δ B ρ e v c₂ →
      Ev Δ B ρ (.ite cnd t e) v (c₁ + c₂ + 1)
  | letE {ρ a b u v c₁ c₂} : Ev Δ B ρ a u c₁ → Ev Δ B (u :: ρ) b v c₂ → Ev Δ B ρ (.letE a b) v (c₁ + c₂ + 1)
  | call {ρ f args body vs v c₁ c₂} : EvL Δ B ρ args vs c₁ → Δ f = some body → Ev Δ B vs body v c₂ →
      Ev Δ B ρ (.call f args) v (c₁ + c₂ + 1)
  | callv {ρ ft f args body vs v c₀ c₁ c₂} : Ev Δ B ρ ft (.nat f) c₀ → EvL Δ B ρ args vs c₁ →
      Δ f = some body → Ev Δ B vs body v c₂ → Ev Δ B ρ (.callv ft args) v (c₀ + c₁ + c₂ + 1)
inductive EvL (Δ : ℕ → Option Tm) (B : ℕ) : List Val → List Tm → List Val → ℕ → Prop
  | nil {ρ : List Val} : EvL Δ B ρ [] [] 0
  | cons {ρ t ts v vs c₁ c₂} : Ev Δ B ρ t v c₁ → EvL Δ B ρ ts vs c₂ → EvL Δ B ρ (t :: ts) (v :: vs) (c₁ + c₂)
end

/-- The function `f` of the table, applied to argument values, evaluates to `y` within `c` steps. -/
def Runs (Δ : ℕ → Option Tm) (B f : ℕ) (xs : List Val) (y : Val) (c : ℕ) : Prop :=
  ∃ body, Δ f = some body ∧ ∃ c' ≤ c, Ev Δ B xs body y c'


/-- Every natural a run produces is at most `(largest input natural + cost + 2)^2`. -/
def Fits (B : ℕ) (v : Val) (c : ℕ) : Prop := (v.maxNat + c + 2) ^ 2 < B

end Lax117284Proofs.Treewidth.Fun
