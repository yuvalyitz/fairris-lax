import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bitwise
import Lax117284.ParameterizedComplexity

/-!
---
title: The Integer Programs of the Clients' Reduction Are Fixed-Parameter Tractable
type: definition
---
An *integer program* here is a system of `M` linear equality constraints over `N`
non-negative integer variables, with non-negative integer coefficients and right-hand
sides: find `x : Fin N → ℕ` with `∑ᵢ a j i * x i = b j` for every constraint `j`. It is
*feasible* if such an `x` exists.

The integer programs that the paper solves with Lenstra's algorithm (Heeger–Hermelin–Itzhaki–Molter–Shabtay,
proof of Theorem 4's third bullet, via the integer program of `Theorem4ILP.lean`'s `HasILPSolution`) form
one explicit family, one constraint matrix `A_n` for each number `n` of clients: `2 ^ (n * n)` *types* of day
(a type is a conflict relation on the clients), `2 ^ n` subsets of clients, one variable for every
pair of a type and a subset and one slack variable for every client, and one constraint for each
type and one for each client. This module states, for exactly this family, that feasibility is
fixed-parameter tractable in the number of variables: `ilpClients_fpt`. The matrix is fixed by `n`;
only the right-hand side (the number `cnt t` of days of each type `t` and the number `B` of days a
client may go unserved) is free. The reduction of the problem of the clients to this problem is
`Theorem4.byClients_fptReduces_ilp`, and `ilpClients_fpt` is proved in the proofs package, by a
certificate-enumeration algorithm specific to these matrices. The search space depends
only on the number of clients; each certificate is decoded using the right-hand sides,
and the resulting assignment is checked.

# Formalization Notes

The family is written out here, the coefficient formula included, because this module cannot import the
proofs; the proofs identify it, definition by definition, with the construction of the reduction. Column
`t * 2^n + s` (`t` a type, `s` a subset of clients, both as numbers) has the coefficient `1` in the row of type
`t` and in the row of client `j` for every client `j` not in `s`, when `s` contains no two clients that `t` makes
conflict (`indepB`), and is the zero column otherwise; the column `2 ^ (n * n) * 2 ^ n + j` is the slack of client `j` and
has a single `1`, in the row of client `j`. The right-hand side is `cnt t` in the row of type `t` and `B` in
every client row.

The domain is the words of this family, which are the words of the integer programs that the reduction
outputs, and, in addition, the fixed word `[1, 1, 0, 1]` of the infeasible program `0 · x = 1`. It is
needed: for `n ≤ 1` every member of the family is feasible, whatever the right-hand side, so for a fairness
parameter above the number of days the reduction has no infeasible word of the family to output. The
word of an integer program is its two counts, then the `M * N` coefficients of the constraint matrix row
by row, then the `M` right-hand sides (the layout convention of `InstSem.lean`'s `instToks`); reading it back
is total, missing entries being read as `0`.

The bound of `FPT` is, as everywhere in this development, `c * g k * (|x| + 1) ^ c` with `g` an arbitrary
function of the parameter. The `g` of the proof is astronomically large (of the order of
`(n^n)^(2^(n²))` in the number `n` of clients, more than the paper's algorithm needs); it is a
function of the parameter alone, which is all fixed-parameter tractability asks. Unlike a general
integer-programming algorithm this one needs no factor polynomial in the word length: all its numbers stay
below a fixed power of the length of the word plus its largest entry.
-/

namespace Lax117284.IlpClients

open Lax117284.ParameterizedComplexity

/-- **An integer program**: `M` linear equality constraints over `N` non-negative integer
variables, with non-negative integer coefficients `a` and right-hand sides `b`. -/
structure ILP where
  /-- The number of variables. -/
  N : ℕ
  /-- The number of constraints. -/
  M : ℕ
  /-- The coefficient of variable `i` in constraint `j`. -/
  a : Fin M → Fin N → ℕ
  /-- The right-hand side of constraint `j`. -/
  b : Fin M → ℕ

/-- **`E` is feasible**: some assignment of its variables satisfies every constraint. -/
def ILP.Feasible (E : ILP) : Prop := ∃ x : Fin E.N → ℕ, ∀ j, ∑ i, E.a j i * x i = E.b j

/-- The numbers of an integer program: the two counts, then the coefficients row by row,
then the right-hand sides. Total and well-defined on every list, reading absent entries as
`0`, exactly like `Instance.pAt`/`Instance.dAt`. -/
def decodeILP (w : List ℕ) : ILP where
  N := w.getD 0 0
  M := w.getD 1 0
  a := fun j i => w.getD (2 + j.val * w.getD 0 0 + i.val) 0
  b := fun j => w.getD (2 + w.getD 1 0 * w.getD 0 0 + j.val) 0

/-- The number of types of day for `n` clients: `2 ^ (n * n)` (bit `a * n + b` of a type says
that clients `a` and `b` conflict on the days of that type). -/
def nT (n : ℕ) : ℕ := 2 ^ (n * n)

/-- The number of subsets of the `n` clients, `2 ^ n` (bit `j` of a subset says that client `j` is served). -/
def nZ (n : ℕ) : ℕ := 2 ^ n

/-- The number of pairs of a type and a subset, `2 ^ (n * n) * 2 ^ n`. -/
def nV (n : ℕ) : ℕ := nT n * nZ n

/-- The number of variables, `2 ^ (n * n) * 2 ^ n + n`: one for every pair of a type and a
subset, and one slack for every client. -/
def nN (n : ℕ) : ℕ := nV n + n

/-- The number of constraints, `2 ^ (n * n) + n`: one for every type and one for every client. -/
def nM (n : ℕ) : ℕ := nT n + n

/-- The subset `S` (a number) is independent for the type `t` (a number): it contains no two distinct
clients `a`, `b` that the type makes conflict (bit `a * n + b` of `t`). -/
def indepB (n t S : ℕ) : Bool :=
  decide (∀ a < n, ∀ b < n, a ≠ b → S.testBit a = true → S.testBit b = true →
    t.testBit (a * n + b) = false)

/-- The coefficient of variable `c` in constraint `r`: the variable `c < nV n` is the pair
of the type `c / 2 ^ n` and the subset `c % 2 ^ n`, whose column has a `1` in the row of its type and in the row
of every client outside the subset, unless the subset is not independent for the type, when the column is
zero; the other variables are the slacks, `1` in the row of their client. -/
def coef (n r c : ℕ) : ℕ :=
  if c < nV n then
    (if indepB n (c / nZ n) (c % nZ n) then
      (if r < nT n then (if c / nZ n = r then 1 else 0)
       else (if (c % nZ n).testBit (r - nT n) = false then 1 else 0))
     else 0)
  else (if nT n ≤ r ∧ c - nV n = r - nT n then 1 else 0)

/-- **The word of the integer program** of `n` clients with `cnt t` days of type `t` and `B` days that a
client may go unserved: the two counts, the coefficients row by row, and the right-hand sides, `cnt r` in the row
of type `r` and `B` in each client row. -/
def ilpWord (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : List ℕ :=
  [nN n, nM n] ++ (List.range (nM n * nN n)).map (fun i => coef n (i / nN n) (i % nN n))
    ++ (List.range (nM n)).map (fun r => if r < nT n then cnt r else B)

/-- **The integer programs of the clients' reduction, as a parameterized problem**: the domain is the words
`ilpWord n cnt B` of the family and the fixed word `[1, 1, 0, 1]` of the program `0 · x = 1`; a yes-instance
is a word whose integer program is feasible; the parameter is the number of variables. -/
def ilpClients : Problem where
  Domain := {z | (∃ n cnt B, z = ilpWord n cnt B) ∨ z = [1, 1, 0, 1]}
  Yes z := (decodeILP z).Feasible
  param z := (decodeILP z).N

/-- **Integer programs of the clients' family are fixed-parameter tractable** in the number of variables. -/
axiom ilpClients_fpt : FPT ilpClients

end Lax117284.IlpClients
