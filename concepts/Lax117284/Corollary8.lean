import Lax117284.Problems

/-!
---
title: Raising the number of days and the fairness parameter
type: corollary
---
**Corollary 8.** The problem
$1 \mid \mathrm{rep},\, p_{i,j} = p_j \mid \min_j \sum_i Z_{i,j}$ is NP-hard whenever
$m \ge 3$ and $0 < k < m-1$.

Two constructions lift hardness from one pair $(m, k)$ to the next. Adding a single day on
which no two jobs conflict raises the attainable fairness by exactly one, so hardness for
$(m, k)$ gives hardness for $(m+1, k+1)$: every client is served on the new day, and on the
old days nothing has changed. Adding one day together with one new client raises the number
of days at $k = 1$: the new client's job blocks every job on each of the old days, and on the
new day all jobs coincide, so a $1$-fair schedule must serve the new client on the new day
and is otherwise a $1$-fair schedule of the old instance. Together with the base case
$(m, k) = (3, 1)$ these two steps reach every pair with $m \ge 3$ and $0 < k < m-1$.

Both constructions give the new day the processing times of the first day, so an instance
with day-independent processing times is sent to one with day-independent processing times,
which is what makes the corollary a statement about that restriction.

# Formalization notes

The conflict-free day is laid out explicitly: client $j$ receives the interval ending at
$(j+1)Q$, where $Q$ is at least every processing time of the first day. Consecutive clients
are then separated by at least $Q$, so no two of their jobs meet. The source does not say
how to lay such a day out.

On the blocking day every job ends at the same time, one later than every due date of the
instance, so all of them pairwise conflict; the new client receives that same job on every
day, which is why it blocks every old job as well.

The new client is numbered $n$ and the new day $m$.

An instance without clients is a yes-instance, and its table is empty, so its code does not
reflect its number of days. Adding a blocking client to it would add one cell per day, which is
exponentially many cells in the length of the code, so the map does not add one: it sends such
an instance to the instance without clients and one more day, which is again a yes-instance of
the same fairness parameter. Everything else is as in the source.
-/

namespace Lax117284.Corollary8

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax429075.Reductions

/-- A time later than every due date of `I`. -/
def bound (I : Instance) : ℕ :=
  (Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j) + 1

/-- A length at least every processing time of the first day of `I`. -/
def gap (I : Instance) : ℕ := Finset.univ.sup fun j : Fin I.clients => I.pAt 0 j

/-- **The instance with one conflict-free day added**: on the new day client `j`'s job has
the processing time it has on the first day and ends at `(j+1)` times a length at least
every such processing time, so no two jobs of the new day meet. -/
def addFreeDay (I : Instance) : Instance where
  clients := I.clients
  days := I.days + 1
  p i j := if (i : ℕ) < I.days then I.pAt i j else I.pAt 0 j
  d i j := if (i : ℕ) < I.days then I.dAt i j else ((j : ℕ) + 1) * gap I
  p_pos i j := by
    have h0 := I.pAt_pos (i : ℕ) (j : ℕ)
    have h1 := I.pAt_pos 0 (j : ℕ)
    split_ifs <;> omega
  p_le_d i j := by
    have h1 := I.pAt_le_dAt (i : ℕ) (j : ℕ)
    have h2 : I.pAt 0 (j : ℕ) ≤ gap I := by
      have := Finset.le_sup (f := fun j' : Fin I.clients => I.pAt 0 (j' : ℕ))
        (Finset.mem_univ j)
      simp only [gap]
      omega
    have h3 : 1 * gap I ≤ ((j : ℕ) + 1) * gap I := Nat.mul_le_mul_right _ (by omega)
    split_ifs <;> omega

/-- **The instance with one blocking client and one blocking day added**: the new client's
job ends later than every due date of `I` and starts at time `0`, so on an old day it
conflicts with every job, and on the new day every job ends at that same time, so all jobs
of the new day pairwise conflict. -/
def addBlockingDay (I : Instance) : Instance where
  clients := I.clients + 1
  days := I.days + 1
  p i j :=
    if (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.pAt i j else I.pAt 0 j)
    else bound I
  d i j := if (j : ℕ) < I.clients ∧ (i : ℕ) < I.days then I.dAt i j else bound I
  p_pos i j := by
    have h0 := I.pAt_pos (i : ℕ) (j : ℕ)
    have h1 := I.pAt_pos 0 (j : ℕ)
    have h2 : 0 < bound I := by simp [bound]
    split_ifs <;> omega
  p_le_d i j := by
    have h1 := I.pAt_le_dAt (i : ℕ) (j : ℕ)
    have h2 : I.dAt (i : ℕ) (j : ℕ) ≤ bound I := by
      unfold Instance.dAt bound
      split_ifs with h h'
      · have h3 : I.d ⟨(i : ℕ), h⟩ ⟨(j : ℕ), h'⟩ ≤
            Finset.univ.sup fun j' => I.d ⟨(i : ℕ), h⟩ j' :=
          Finset.le_sup (Finset.mem_univ _)
        have h4 : (Finset.univ.sup fun j' => I.d ⟨(i : ℕ), h⟩ j') ≤
            Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
          Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ _)
        omega
      · omega
      · omega
    have h5 : I.pAt 0 (j : ℕ) ≤ I.dAt 0 (j : ℕ) := I.pAt_le_dAt 0 (j : ℕ)
    have h6 : I.dAt 0 (j : ℕ) ≤ bound I := by
      unfold Instance.dAt bound
      split_ifs with h h'
      · have h3 : I.d ⟨0, h⟩ ⟨(j : ℕ), h'⟩ ≤ Finset.univ.sup fun j' => I.d ⟨0, h⟩ j' :=
          Finset.le_sup (Finset.mem_univ _)
        have h4 : (Finset.univ.sup fun j' => I.d ⟨0, h⟩ j') ≤
            Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
          Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ _)
        omega
      · omega
      · omega
    split_ifs <;> omega

/-- **The instance without clients and with `m` days.** -/
def noClients (m : ℕ) : Instance where
  clients := 0
  days := m
  p _ j := j.elim0
  d _ j := j.elim0
  p_pos _ j := j.elim0
  p_le_d _ j := j.elim0

/-- **Adding a conflict-free day raises the attainable fairness by exactly one.** -/
axiom addFreeDay_correct (I : Instance) (hm : 0 < I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ (addFreeDay I).HasKFairSchedule (k + 1)

/-- **Adding a blocking client and a blocking day preserves one-fairness.** -/
axiom addBlockingDay_correct (I : Instance) (hm : 0 < I.days) :
    I.HasKFairSchedule 1 ↔ (addBlockingDay I).HasKFairSchedule 1

/-- **The conflict-free day keeps the processing times day-independent.** -/
axiom addFreeDay_dayIndepP {I : Instance} (h : I.DayIndepP) : (addFreeDay I).DayIndepP

/-- **The blocking day keeps the processing times day-independent.** -/
axiom addBlockingDay_dayIndepP {I : Instance} (h : I.DayIndepP) :
    (addBlockingDay I).DayIndepP

open Classical in
/-- **The first reduction**, as a map on words: a word encoding an instance with `m` days
and the fairness parameter `k` is sent to the encoding of the instance with one
conflict-free day added and the parameter `k + 1`. -/
noncomputable def reduceFreeDay (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days then
    encodeUniform (addFreeDay h.choose) (h.choose_spec.choose + 1)
  else rejected

open Classical in
/-- **The second reduction**, as a map on words: a word encoding an instance with `m` days
and the fairness parameter `1` is sent to the encoding of the instance with one blocking
client and one blocking day added, with the parameter `1`; an instance without clients is
sent to the instance without clients and one more day. -/
noncomputable def reduceBlockingDay (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ 0 < I.days ∧ k = 1 then
    if h.choose.clients = 0 then encodeUniform (noClients (h.choose.days + 1)) 1
    else encodeUniform (addBlockingDay h.choose) 1
  else rejected

/-- **The first reduction is correct.** -/
axiom reduceFreeDay_correct (m k : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP) ↔
      reduceFreeDay w ∈ Uniform fun I k' => I.days = m + 1 ∧ k' = k + 1 ∧ I.DayIndepP

/-- **The second reduction is correct.** -/
axiom reduceBlockingDay_correct (m : ℕ) (hm : 0 < m) (w : Word) :
    w ∈ Uniform (fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP) ↔
      reduceBlockingDay w ∈ Uniform fun I k' => I.days = m + 1 ∧ k' = 1 ∧ I.DayIndepP

/-- **The first reduction runs in polynomial time.** -/
axiom reduceFreeDay_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id reduceFreeDay)

/-- **The second reduction runs in polynomial time.** -/
axiom reduceBlockingDay_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id reduceBlockingDay)

/-- **The first step of Corollary 8**: hardness for `(m, k)` gives hardness for
`(m+1, k+1)`. -/
axiom manyOne_freeDay (m k : ℕ) (hm : 0 < m) :
    ManyOne (Uniform fun I k' => I.days = m ∧ k' = k ∧ I.DayIndepP)
      (Uniform fun I k' => I.days = m + 1 ∧ k' = k + 1 ∧ I.DayIndepP)

/-- **The second step of Corollary 8**: hardness for `(m, 1)` gives hardness for
`(m+1, 1)`. -/
axiom manyOne_blockingDay (m : ℕ) (hm : 0 < m) :
    ManyOne (Uniform fun I k' => I.days = m ∧ k' = 1 ∧ I.DayIndepP)
      (Uniform fun I k' => I.days = m + 1 ∧ k' = 1 ∧ I.DayIndepP)

end Lax117284.Corollary8
