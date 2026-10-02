import Lax117284.BoundedSat
import Lax117284.Problems

/-!
---
title: Three Days and the Fairness Parameter One
type: theorem
---
**Theorem 7.** The problem
$1 \mid \mathrm{rep},\, p_{i,j} = p \mid \min_j \sum_i Z_{i,j}$ is NP-hard for $k = 1$ and
$m = 3$.

Let $\varphi$ be a [2,3]-bounded 3-SAT formula with $n$ variables, $\ell$ clauses of two
literals and $q$ clauses of three literals. Build an instance with three days and the
clients: three *dummies*; two clients $x_v^1, x_v^0$ per variable $v$; and one client per
occurrence of a literal in a clause. Every processing time is $2$, so two jobs of a day
conflict exactly when their due dates differ by at most one, and the whole construction is a
matter of placing due dates on a line, three times.

On the first day the due dates are $2$ for the three dummies, $2v+5$ for both clients of
variable $v$, $2n+2j+7$ for both clients of the $j$-th clause of two literals, and
$2n+2\ell+2j+9$ for all three clients of the $j$-th clause of three literals. Clients
sharing a due date conflict and nothing else does, so the first day admits one client out of
each group: one dummy, one of $x_v^1 / x_v^0$ — this is the truth assignment — and one
client of every clause. On the second day the dummies, the variable clients and the clients
of the clauses of two literals all have the due date $2$, so they are pairwise conflicting,
while the clients of the $j$-th clause of three literals sit alone at $3j+6$; since a dummy
runs on every day, the second day is a dead end for everything but one client of each clause
of three literals. On the third day $x_v^1$ sits at $10v+6$ and $x_v^0$ at $10v+11$, while
an occurrence of the literal $v$ sits at $10v+5$ or $10v+7$ and an occurrence of $\lnot v$
at $10v+10$ or $10v+12$, according to which of its at most two occurrences it is. So on the
third day a client of an occurrence conflicts with exactly the variable client that
*falsifies* its literal, and with nothing else.

The three dummies conflict with each other on all three days, so a $1$-fair schedule runs
exactly one of them on each day. This is what forces the selection on the first day and
makes the second day a dead end, and a client of an occurrence can then be served only on
the third day — which is possible exactly when the assignment selected on the first day
makes its literal true.

# Formalization Notes

Clients are numbered: the dummies $0, 1, 2$; then the pair $x_v^1, x_v^0$ of variable $v$;
then one client per occurrence slot, those of the clauses of two literals first. Which of
the at most two occurrences of a literal a slot is, which the third day's layout needs, is
computed from the formula as the number of earlier slots carrying the same literal; it is
the occurrence bound that makes this $0$ or $1$.

The due dates are the source's with every index shifted, since the source numbers variables
and clauses from $1$ and these are numbered from $0$.

All processing times are equal, so the instance lies in the class of instances with
day-independent processing times, which is the restriction Theorem 2 concerns.
-/

namespace Lax117284.Theorem7

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax429075.Reductions

/-- The number of clients of the construction: three dummies, two per variable, and one per
occurrence slot. -/
def clients (φ : BoundedSat.Formula) : ℕ := 3 + 2 * φ.vars + BoundedSat.slots φ

/-- The due date of client `c` on day `i` of the construction. -/
def due (φ : BoundedSat.Formula) (i c : ℕ) : ℕ :=
  if c < 3 then 2
  else if c < 3 + 2 * φ.vars then
    let v := (c - 3) / 2
    if i = 0 then 2 * v + 5
    else if i = 1 then 2
    else if (c - 3) % 2 = 0 then 10 * v + 6 else 10 * v + 11
  else
    let o := c - 3 - 2 * φ.vars
    let l := BoundedSat.litOfSlot φ o
    if i = 2 then
      (if l.2 then 10 * l.1 + 5 + 2 * BoundedSat.slotRank φ o
        else 10 * l.1 + 10 + 2 * BoundedSat.slotRank φ o)
    else if o < 2 * φ.twoClauses then
      (if i = 0 then 2 * φ.vars + 2 * (o / 2) + 7 else 2)
    else
      (if i = 0 then
        2 * φ.vars + 2 * φ.twoClauses + 2 * ((o - 2 * φ.twoClauses) / 3) + 9
      else 3 * ((o - 2 * φ.twoClauses) / 3) + 6)

theorem two_le_due (φ : BoundedSat.Formula) (i c : ℕ) : 2 ≤ due φ i c := by
  unfold due
  simp only []
  split_ifs <;> omega

/-- **The instance of Theorem 7**: three days, all processing times `2`, and the fairness
parameter `1`. -/
def inst (φ : BoundedSat.Formula) : Instance where
  clients := clients φ
  days := 3
  p _ _ := 2
  d i c := due φ i c
  p_pos _ _ := by omega
  p_le_d i c := two_le_due φ i c

/-- **The constructed instance has three days.** -/
axiom inst_days (φ : BoundedSat.Formula) : (inst φ).days = 3

/-- **All processing times of the constructed instance are equal**, so in particular they
are day-independent. -/
axiom inst_p_eq (φ : BoundedSat.Formula) (i i' : Fin (inst φ).days)
    (j j' : Fin (inst φ).clients) : (inst φ).p i j = (inst φ).p i' j'

/-- **The construction is correct**: the formula is satisfiable exactly when the instance
admits a schedule serving every client on at least one of the three days. -/
axiom correct (φ : BoundedSat.Formula) :
    φ.Satisfiable ↔ (inst φ).HasKFairSchedule 1

open Classical in
/-- **The reduction**, as a map on words: a word encoding a formula with no more variables
than positions is sent to the encoding of the constructed instance with the fairness
parameter `1`, and every other word to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ φ : BoundedSat.Formula,
      BoundedSat.encodeFormula φ = w ∧ φ.vars ≤ BoundedSat.slots φ then
    encodeUniform (inst h.choose) 1
  else rejected

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ BoundedSat.BoundedSat ↔
      reduce w ∈ Uniform fun I k => I.days = 3 ∧ k = 1 ∧ I.DayIndepP

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

/-- **Theorem 7.** The problem with three days, the fairness parameter `1` and
day-independent processing times is NP-hard. -/
axiom uniform_three_one_npHard :
    NPHard (Uniform fun I k => I.days = 3 ∧ k = 1 ∧ I.DayIndepP)

end Lax117284.Theorem7
