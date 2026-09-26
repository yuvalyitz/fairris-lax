import Lax117284.TwoSatCNF
import Mathlib.Logic.Relation

/-!
The pure mathematics of the 2-SAT algorithm, on data as the word RAM holds it.

A formula is given by the number `m` of its clauses and two functions on the *occurrences*
`0, …, 2m-1`: the literal `2c + α` is the `α`-th literal of clause `c`; it has the variable
`xs (2c+α)` and the sign `ss (2c+α)`, which is `1` for the variable and `0` for its negation.
The word RAM stores exactly this in an array.
-/

namespace Lax117284Proofs.TwoSAT.Math



/-- The `i`-th literal is true under the assignment `a`. -/
def Holds (a : ℕ → Bool) (xs ss : ℕ → ℕ) (i : ℕ) : Prop := a (xs i) = decide (ss i = 1)

/-- The assignment `a` satisfies the clauses `0, …, m-1`. -/
def SatBy (a : ℕ → Bool) (m : ℕ) (xs ss : ℕ → ℕ) : Prop :=
  ∀ c < m, Holds a xs ss (2 * c) ∨ Holds a xs ss (2 * c + 1)

/-- The clauses `0, …, m-1` are satisfiable. -/
def Sat2 (m : ℕ) (xs ss : ℕ → ℕ) : Prop := ∃ a : ℕ → Bool, SatBy a m xs ss

/-- The node of the implication graph of the literal with variable `x` and sign `s`
(`1` for the variable, `0` for its negation): `2x + s`. -/
def node (x s : ℕ) : ℕ := 2 * x + s

/-- The implication graph of the clauses `0, …, m-1`, with variables `ys` and signs `ss`.
The clause `(l ∨ l')` gives the edges `¬l → l'` and `¬l' → l`. -/
def Edge (m : ℕ) (ys ss : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∃ c < m,
    (a = node (ys (2 * c)) (1 - ss (2 * c)) ∧ b = node (ys (2 * c + 1)) (ss (2 * c + 1))) ∨
    (a = node (ys (2 * c + 1)) (1 - ss (2 * c + 1)) ∧ b = node (ys (2 * c)) (ss (2 * c)))

/-- Reachability by a path of at least one edge. -/
abbrev Reach (m : ℕ) (ys ss : ℕ → ℕ) : ℕ → ℕ → Prop := Relation.TransGen (Edge m ys ss)

/-- **The variable `x` is contradictory**: it implies its negation and is implied by it. -/
def Contra (m : ℕ) (ys ss : ℕ → ℕ) (x : ℕ) : Prop :=
  Reach m ys ss (node x 1) (node x 0) ∧ Reach m ys ss (node x 0) (node x 1)

/-- One step of Warshall's algorithm: allow the node `k` as an intermediate. -/
def wstep (k : ℕ) (M : ℕ → ℕ → Bool) : ℕ → ℕ → Bool :=
  fun a b => M a b || (M a k && M k b)

/-- Warshall's algorithm: the matrix after allowing the intermediate nodes `0, …, k-1`. -/
def wshall (M : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0 => M
  | k + 1 => wstep k (wshall M k)

end Lax117284Proofs.TwoSAT.Math
