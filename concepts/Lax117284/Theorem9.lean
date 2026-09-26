import Lax117284.Problems
import Lax117284.TwoSatisfiability

/-!
---
title: The fairness parameter one below the number of days
type: theorem
---
**Theorem 9.** The problem $1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ is solvable in
polynomial time when $k = m - 1$.

Associate with every day $i$ and client $j$ a variable $x_{i,j}$, read as "client $j$'s job
is executed on day $i$". Two families of clauses express the two requirements. For every day
$i$ and every two distinct clients $j_1, j_2$ whose jobs conflict on that day, the
*conflict clause* $(\lnot x_{i,j_1} \lor \lnot x_{i,j_2})$ forbids executing both. For every
client $j$ and every two distinct days $i_1, i_2$, the *validation clause*
$(x_{i_1,j} \lor x_{i_2,j})$ forbids rejecting the client on both. A schedule satisfies the
first family exactly when it is feasible and the second exactly when no client is rejected
twice, which at $k = m-1$ is fairness. The formula is a 2-CNF formula of $mn$ variables and
$mn^2 + nm^2$ clauses, and 2-satisfiability is decidable in linear time.

The parameter $k = m-1$ is exactly the value at which two literals suffice: "$j$ is served
on at least $m-1$ days" says "of any two days, $j$ is served on one of them", a binary
constraint.

# Formalization notes

Clauses are numbered rather than enumerated: a slot is allocated for every day and ordered
pair of clients, and for every client and ordered pair of days, and a slot whose pair is
inadmissible — two equal clients, two non-conflicting jobs, two equal days — carries the
tautology $(x \lor \lnot x)$ on the variable it names. A closed formula for the index of a
clause is what an algorithm can compute; enumerating only the admissible pairs would require
a search. Ordered pairs make each constraint appear twice, which is harmless.

The variables are numbered $i n + j$, with one further variable that no meaningful clause
names, so that the numbering is a total function of two numbers and needs no proof that its
arguments are in range.
-/

namespace Lax117284.Theorem9

open Lax117284.Scheduling Lax117284.Problems Lax117284.TwoSatisfiability
open Lax434930.PolynomialTime Lax429075.Reductions

/-- The variable "client `j`'s job is executed on day `i`", numbered `i·n + j`. The one
further variable, which no meaningful clause names, is the value on indices out of
range. -/
def varIdx (I : Instance) (i j : ℕ) : Fin (I.days * I.clients + 1) :=
  ⟨min (i * I.clients + j) (I.days * I.clients), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The `α`-th literal of clause `c`: the conflict clauses come first, one slot for every
day and ordered pair of clients, then the validation clauses, one slot for every client and
ordered pair of days. An inadmissible slot carries a tautology. -/
def clauseLit (I : Instance) (c : ℕ) (α : Fin 2) : Fin (I.days * I.clients + 1) × Bool :=
  if c < I.days * I.clients * I.clients then
    let i := c / (I.clients * I.clients)
    let r := c % (I.clients * I.clients)
    let j₁ := r / I.clients
    let j₂ := r % I.clients
    if j₁ ≠ j₂ ∧ I.ConflictAt i j₁ j₂ then
      (varIdx I i (if α = 0 then j₁ else j₂), false)
    else (varIdx I i j₁, α = 0)
  else
    let c' := c - I.days * I.clients * I.clients
    let j := c' / (I.days * I.days)
    let r := c' % (I.days * I.days)
    let i₁ := r / I.days
    let i₂ := r % I.days
    if i₁ ≠ i₂ then (varIdx I (if α = 0 then i₁ else i₂) j, true)
    else (varIdx I i₁ j, α = 0)

/-- **The 2-CNF formula of Theorem 9.** -/
def formula (I : Instance) : Formula where
  vars := I.days * I.clients + 1
  clauses := I.days * I.clients * I.clients + I.clients * I.days * I.days
  lit c α := clauseLit I c α

/-- **The construction is correct**: at the fairness parameter `m - 1` an instance is a
yes-instance exactly when its formula is satisfiable. -/
axiom correct (I : Instance) (k : ℕ) (hk : k + 1 = I.days) :
    I.HasKFairSchedule k ↔ (formula I).Satisfiable

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance with the fairness
parameter one below its number of days is sent to the encoding of its formula, and every
other word to the encoding of an unsatisfiable formula. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ k + 1 = I.days then
    encodeFormula (formula h.choose)
  else encodeFormula unsatisfiable

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ Uniform (fun I k => k + 1 = I.days) ↔ reduce w ∈ TwoSat

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

/-- **Theorem 9.** The problem at the fairness parameter one below the number of days
reduces in polynomial time to 2-SAT. -/
axiom manyOne_twoSat : ManyOne (Uniform fun I k => k + 1 = I.days) TwoSat

end Lax117284.Theorem9
