import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Set.Basic

/-!
---
title: Fair repetitive interval scheduling
type: definition
---
An instance consists of $n$ clients and $m$ days. Every client submits one job on every
day: client $j$'s job on day $i$ has a processing time $p_{i,j} \ge 1$ and a due date
$d_{i,j} \ge p_{i,j}$. The schedule is just-in-time, so that job occupies exactly the
interval $(d_{i,j} - p_{i,j},\, d_{i,j}]$, and two jobs of the same day *conflict* if their
intervals intersect. One machine is available on each day, so a *schedule* selects, for
every day, a set of clients whose day's jobs are pairwise non-conflicting; the jobs of the
clients left out are rejected that day.

Write $Z_{i,j}$ for the indicator that client $j$'s job is executed on day $i$. The
objective is the fairness of the schedule, $\min_j \sum_i Z_{i,j}$: the decision problem
$1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ asks, given a fairness parameter $k$,
whether some schedule serves every client on at least $k$ of the $m$ days. In the
generalization $1 \mid k_j, \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ every client $j$
carries its own parameter $k_j$ and must be served on at least $k_j$ days.

Three restrictions of the instance recur. The processing times are *day-independent* if
$p_{i,j} = p_j$ for all $i$, the due dates are *day-independent* if $d_{i,j} = d_j$ for all
$i$, and the processing times are *unit* if $p_{i,j} = 1$ throughout.

# Formalization notes

Clients and days are numbered rather than abstract finite types: an instance is something
an algorithm is handed as a word, and a word presents its clients and days in an order.
Nothing in the results depends on days carrying an order.

A job is the set of time points it occupies, and conflict is the intersection of two such
sets being nonempty. Because processing times are positive, this agrees with the
arithmetic condition that each job starts before the other one is due.

Fairness is stated for per-client parameters from the start and the uniform problem is the
constant case, so that the two problems are one definition rather than two. Both are
stated as the existence of a schedule and not as an optimization, which is the form in
which the source's complexity results are proved.
-/

namespace Lax117284.Scheduling

/-- An instance of fair repetitive interval scheduling: `clients` clients each submitting
one job on each of `days` days, where client `j`'s job on day `i` has processing time
`p i j` and due date `d i j`. A job takes some time and does not start before time `0`. -/
structure Instance where
  /-- The number `n` of clients. -/
  clients : ℕ
  /-- The number `m` of days. -/
  days : ℕ
  /-- The processing time `p i j` of client `j`'s job on day `i`. -/
  p : Fin days → Fin clients → ℕ
  /-- The due date `d i j` of client `j`'s job on day `i`. -/
  d : Fin days → Fin clients → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d i j

namespace Instance

variable (I : Instance)

/-- The interval `(d i j - p i j, d i j]` occupied by client `j`'s job on day `i`: the job
is completed exactly at its due date. -/
def job (i : Fin I.days) (j : Fin I.clients) : Set ℕ :=
  Set.Ioc (I.d i j - I.p i j) (I.d i j)

/-- Clients `j` and `j'` **conflict on day `i`**: their day-`i` jobs share a time point, so
the machine of that day can execute at most one of them. -/
def Conflict (i : Fin I.days) (j j' : Fin I.clients) : Prop :=
  (I.job i j ∩ I.job i j').Nonempty

/-- A **schedule** names, for each day, the clients whose job is executed that day. -/
abbrev Schedule := Fin I.days → Finset (Fin I.clients)

variable {I}

/-- A schedule is **feasible** if the jobs it executes on any one day are pairwise
non-conflicting. -/
def Feasible (σ : I.Schedule) : Prop :=
  ∀ i, (σ i : Set (Fin I.clients)).Pairwise fun j j' => ¬ I.Conflict i j j'

/-- `∑_i Z_{i,j}`, the number of days on which client `j`'s job is executed. -/
def served (σ : I.Schedule) (j : Fin I.clients) : ℕ :=
  (Finset.univ.filter fun i => j ∈ σ i).card

/-- A schedule is **fair** for the parameters `k` if every client `j` is served on at least
`k j` days. -/
def Fair (k : Fin I.clients → ℕ) (σ : I.Schedule) : Prop := ∀ j, k j ≤ served σ j

variable (I)

/-- **The question of `1 | k_j, rep | min_j ∑_i Z_{i,j}`**: is there a feasible schedule
serving every client `j` on at least `k j` days? -/
def HasFairSchedule (k : Fin I.clients → ℕ) : Prop :=
  ∃ σ : I.Schedule, Feasible σ ∧ Fair k σ

/-- **The question of `1 | rep | min_j ∑_i Z_{i,j}`**: the uniform case, in which every
client carries the same fairness parameter `k`. -/
def HasKFairSchedule (k : ℕ) : Prop := I.HasFairSchedule fun _ => k

/-- `p_{i,j} = p_j`: the processing times are **day-independent**. -/
def DayIndepP : Prop := ∀ i i' j, I.p i j = I.p i' j

/-- `d_{i,j} = d_j`: the due dates are **day-independent**. -/
def DayIndepD : Prop := ∀ i i' j, I.d i j = I.d i' j

/-- The processing time of client `j`'s job on day `i`, read off unnumbered indices and
`1` outside the instance, so that a construction reading another instance need not carry
the proofs that its indices are in range. -/
def pAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.p ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

/-- The due date of client `j`'s job on day `i`, and `1` outside the instance. -/
def dAt (i j : ℕ) : ℕ :=
  if h : i < I.days then if h' : j < I.clients then I.d ⟨i, h⟩ ⟨j, h'⟩ else 1 else 1

theorem pAt_pos (i j : ℕ) : 0 < I.pAt i j := by
  unfold pAt
  split
  · split
    · exact I.p_pos _ _
    · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one

theorem pAt_le_dAt (i j : ℕ) : I.pAt i j ≤ I.dAt i j := by
  unfold pAt dAt
  split
  · split
    · exact I.p_le_d _ _
    · exact Nat.le_refl 1
  · exact Nat.le_refl 1

@[simp] theorem pAt_coe (i : Fin I.days) (j : Fin I.clients) : I.pAt i j = I.p i j := by
  simp [pAt, i.isLt, j.isLt]

@[simp] theorem dAt_coe (i : Fin I.days) (j : Fin I.clients) : I.dAt i j = I.d i j := by
  simp [dAt, i.isLt, j.isLt]

/-- Whether clients `j` and `j'` conflict on day `i`, read off unnumbered indices and in
the arithmetic form: each of the two jobs starts before the other one is due. It is this
form of the condition that a construction can decide. -/
def ConflictAt (i j j' : ℕ) : Prop :=
  I.dAt i j - I.pAt i j < I.dAt i j' ∧ I.dAt i j' - I.pAt i j' < I.dAt i j

instance (i j j' : ℕ) : Decidable (I.ConflictAt i j j') := by
  unfold ConflictAt; infer_instance

/-- **The arithmetic and the geometric form of conflict agree.** -/
theorem conflictAt_iff (i : Fin I.days) (j j' : Fin I.clients) :
    I.ConflictAt i j j' ↔ I.Conflict i j j' := by
  have h1 := I.p_pos i j
  have h2 := I.p_le_d i j
  have h3 := I.p_pos i j'
  have h4 := I.p_le_d i j'
  simp only [ConflictAt, Conflict, job, pAt_coe, dAt_coe, Set.Nonempty, Set.mem_inter_iff,
    Set.mem_Ioc]
  constructor
  · intro h
    exact ⟨min (I.d i j) (I.d i j'), by omega, by omega⟩
  · rintro ⟨t, ⟨h5, h6⟩, h7, h8⟩
    omega

/-- `p_{i,j} = 1`: the processing times are **unit**. -/
def UnitP : Prop := ∀ i j, I.p i j = 1

/-- No two jobs of a day conflict, so every client can be served on every day. -/
def ConflictFree : Prop := ∀ i, ∀ j j', j ≠ j' → ¬ I.Conflict i j j'

end Instance

end Lax117284.Scheduling
