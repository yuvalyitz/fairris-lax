import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-!
# Fair Repetitive Interval Scheduling

The problem of Heeger, Hermelin, Itzhaki, Molter and Shabtay, *"Fair Repetitive Interval
Scheduling"*, Algorithmica (2025), Section 1.2.

`n` clients each submit one job on each of `m` days. Client `j`'s job on day `i` has a
processing time `p i j` and a due date `d i j`, and — because the schedule is
Just-In-Time — occupies *exactly* the interval `(d i j - p i j, d i j]`. A single machine
runs the jobs of one day, so a daily schedule is a set of clients whose intervals are
pairwise disjoint; jobs left out are rejected. `Z i j` is `1` when client `j`'s job runs
on day `i`, and the objective `min_j ∑_i Z i j` asks that *every* client be served on at
least `k` of the `m` days.

Clients and days are abstract `Fintype`s rather than `Fin n` and `Fin m`, so that a gadget
construction can name them structurally — as sums and subtypes of the objects they come
from — instead of through an ad-hoc enumeration. Nothing in the paper's arguments depends
on days carrying an order.

## Fairness, per Client

Section 5.1 needs the generalization `1 | k_j, rep | min_j ∑_i Z_{i,j}` in which each
client `j` carries its own fairness parameter `k j`, and Lemma 15 reduces that back to the
uniform problem. So `Fair` is stated against a function `Client → ℕ` from the start, and
`HasKFairSchedule k` is the constant case — one definition, not two.
-/


namespace Lax117284Proofs.Model

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An instance of *Fair Repetitive Interval Scheduling* (Section 1.2).

Client `j`'s job on day `i` has processing time `p i j` and due date `d i j`, and occupies
exactly the interval `(d i j - p i j, d i j]`. `p_pos` and `p_le_d` are the paper's
standing conventions: a job takes some time, and it does not start before time `0`. -/
structure Instance where
  /-- The clients, `{1, …, n}` in the paper. -/
  Client : Type
  /-- The days, `{1, …, m}` in the paper. -/
  Day : Type
  clientFintype : Fintype Client
  clientDecEq : DecidableEq Client
  dayFintype : Fintype Day
  dayDecEq : DecidableEq Day
  /-- `p i j`, the processing time of client `j`'s job on day `i`. -/
  p : Day → Client → ℕ
  /-- `d i j`, the due date of client `j`'s job on day `i`. -/
  d : Day → Client → ℕ
  p_pos : ∀ i j, 0 < p i j
  p_le_d : ∀ i j, p i j ≤ d i j

attribute [instance] Instance.clientFintype Instance.clientDecEq
attribute [instance] Instance.dayFintype Instance.dayDecEq

namespace Instance

variable (I : Instance)

/-- The number `n` of clients. -/
def numClients : ℕ := Fintype.card I.Client

/-- The number `m` of days. -/
def numDays : ℕ := Fintype.card I.Day

/-- The start of client `j`'s job on day `i`: the left end of `(d i j - p i j, d i j]`. -/
def start (i : I.Day) (j : I.Client) : ℕ := I.d i j - I.p i j

variable {I}

lemma start_lt_d (i : I.Day) (j : I.Client) : I.start i j < I.d i j := by
  have := I.p_pos i j
  have := I.p_le_d i j
  simp only [start]; omega

variable (I)

/-! ## 1. Conflicts

Two jobs of the same day *conflict* when their time intervals intersect; the machine can
then run at most one of them. This is the daily conflict relation of Definition 5, before
it is packaged as a graph (see `ConflictGraph.lean`). -/

/-- Clients `j` and `j'` **conflict on day `i`**: their day-`i` intervals intersect. -/
def Conflict (i : I.Day) (j j' : I.Client) : Prop :=
  I.start i j < I.d i j' ∧ I.start i j' < I.d i j

variable {I}

lemma conflict_symm {i : I.Day} {j j' : I.Client} (h : I.Conflict i j j') :
    I.Conflict i j' j := ⟨h.2, h.1⟩

@[simp] lemma conflict_self (i : I.Day) (j : I.Client) : I.Conflict i j j :=
  ⟨start_lt_d i j, start_lt_d i j⟩

/-- Jobs laid out one after the other on the time line do not conflict. -/
lemma not_conflict_of_le {i : I.Day} {j j' : I.Client} (h : I.d i j ≤ I.start i j') :
    ¬ I.Conflict i j j' := fun hc => absurd hc.2 (Nat.not_lt.mpr h)

lemma not_conflict_of_le' {i : I.Day} {j j' : I.Client} (h : I.d i j' ≤ I.start i j) :
    ¬ I.Conflict i j j' := fun hc => not_conflict_of_le h (conflict_symm hc)

/-- Two jobs with the same interval conflict — the workhorse of every gadget that makes a
set of clients mutually exclusive by giving them identical jobs. -/
lemma conflict_of_eq {i : I.Day} {j j' : I.Client}
    (hp : I.p i j = I.p i j') (hd : I.d i j = I.d i j') : I.Conflict i j j' := by
  have h := start_lt_d (I := I) i j
  refine ⟨by simpa [hd] using h, ?_⟩
  simpa [start, hp, hd] using h

/-- Conflict is decidable, so daily schedules can be checked by `decide`. -/
instance (i : I.Day) (j j' : I.Client) : Decidable (I.Conflict i j j') := by
  unfold Conflict; infer_instance

/-! ## 2. Schedules, feasibility and fairness -/

variable (I)

/-- A **solution**: for each day, the set of clients whose job runs that day. The paper's
tuple `(σ₁, …, σ_m)`. -/
abbrev Schedule := I.Day → Finset I.Client

variable {I}

/-- A schedule is **feasible** when no day runs two conflicting jobs. -/
def Feasible (σ : I.Schedule) : Prop :=
  ∀ i, ∀ j ∈ σ i, ∀ j' ∈ σ i, j ≠ j' → ¬ I.Conflict i j j'

/-- `∑ᵢ Z_{i,j}`: the number of days on which client `j`'s job is executed. -/
def served (σ : I.Schedule) (j : I.Client) : ℕ :=
  (Finset.univ.filter fun i => j ∈ σ i).card

/-- A schedule is **fair** for the per-client thresholds `k` when every client `j` is
served on at least `k j` days. The paper's `∑ᵢ Z_{i,j} ≥ k_j`. -/
def Fair (k : I.Client → ℕ) (σ : I.Schedule) : Prop := ∀ j, k j ≤ served σ j

variable (I)

/-- **The question of `1 | k_j, rep | min_j ∑_i Z_{i,j}`** (Section 5.1): is there a
feasible schedule serving every client `j` on at least `k j` days? -/
def HasFairSchedule (k : I.Client → ℕ) : Prop :=
  ∃ σ : I.Schedule, Feasible σ ∧ Fair k σ

/-- **The question of `1 | rep | min_j ∑_i Z_{i,j}`** (Section 1.2): the uniform case, in
which every client carries the same fairness parameter `k`. -/
def HasKFairSchedule (k : ℕ) : Prop := I.HasFairSchedule fun _ => k

variable {I}

/-! ## 3. Basic facts -/

/-- `served` as a sum of indicators — the form that splits along a sum type of days. -/
lemma served_eq_sum (σ : I.Schedule) (j : I.Client) :
    served σ j = ∑ i : I.Day, (if j ∈ σ i then 1 else 0) := by
  rw [served, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Two schedules that agree on where `j` runs serve `j` equally often. -/
lemma served_congr {σ τ : I.Schedule} {j : I.Client} (h : ∀ i, j ∈ σ i ↔ j ∈ τ i) :
    served σ j = served τ j := by
  rw [served, served]
  congr 1
  ext i
  simp [h i]

/-- Scheduling more can only serve more. -/
lemma served_mono {σ τ : I.Schedule} (h : ∀ i, σ i ⊆ τ i) (j : I.Client) :
    served σ j ≤ served τ j := by
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-- A client scheduled on exactly one day is served once. -/
lemma served_eq_one_of_unique {σ : I.Schedule} {j : I.Client} {i₀ : I.Day}
    (h : ∀ i, j ∈ σ i ↔ i = i₀) : served σ j = 1 := by
  have hfil : (Finset.univ.filter fun i => j ∈ σ i) = {i₀} := by
    ext i
    simp [h i]
  rw [served, hfil, Finset.card_singleton]

/-- A client on every day is served on every day. -/
lemma served_eq_numDays_of_mem {σ : I.Schedule} {j : I.Client} (h : ∀ i, j ∈ σ i) :
    served σ j = I.numDays := by
  rw [served, Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ]
  rfl

/-- A client scheduled somewhere is served at least once. -/
lemma one_le_served_of_mem {σ : I.Schedule} {j : I.Client} {i : I.Day} (h : j ∈ σ i) :
    1 ≤ served σ j :=
  Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩⟩

/-- A client that is served at all is served on some particular day. -/
lemma exists_mem_of_served_pos {σ : I.Schedule} {j : I.Client} (h : 0 < served σ j) :
    ∃ i, j ∈ σ i := by
  obtain ⟨i, hi⟩ := Finset.card_pos.1 h
  exact ⟨i, (Finset.mem_filter.1 hi).2⟩

lemma served_le_numDays (σ : I.Schedule) (j : I.Client) : served σ j ≤ I.numDays :=
  le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)

/-- Serving fewer clients on fewer days keeps a schedule feasible. -/
lemma Feasible.mono {σ τ : I.Schedule} (h : Feasible σ) (hsub : ∀ i, τ i ⊆ σ i) :
    Feasible τ := fun i j hj j' hj' hne => h i j (hsub i hj) j' (hsub i hj') hne

/-- The empty schedule is feasible. -/
lemma feasible_empty : Feasible (fun _ : I.Day => (∅ : Finset I.Client)) := by
  intro i j hj; simp at hj

@[simp] lemma served_empty (j : I.Client) :
    served (fun _ : I.Day => (∅ : Finset I.Client)) j = 0 := by
  simp [served]

/-! ## 4. Day-independence

The two restrictions of Sections 4 and 5: processing times, or due dates, that depend only
on the client and not on the day. -/

variable (I)

/-- `p_{i,j} = p_j`: processing times are **day-independent**. -/
def DayIndepP : Prop := ∀ i i' j, I.p i j = I.p i' j

/-- `d_{i,j} = d_j`: due dates are **day-independent**. -/
def DayIndepD : Prop := ∀ i i' j, I.d i j = I.d i' j

/-- `p_{i,j} = 1`: unit processing times, the "slots of fixed duration" special case. -/
def UnitP : Prop := ∀ i j, I.p i j = 1

variable {I}

end Instance

end Lax117284Proofs.Model
