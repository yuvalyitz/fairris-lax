import Lax117284.Problems

/-!
---
title: Just-in-time scheduling on unrelated parallel machines
type: definition
---
An instance of $R \parallel \sum_j Z_j$ consists of $n$ jobs and $m$ unrelated parallel
machines. Job $j$ has a due date $d_j$ and a processing time $p_{i,j}$ on machine $i$. A job
is *just in time* if it is executed on some machine and completes exactly at its due date,
so that, when assigned to machine $i$, it occupies the interval
$(d_j - p_{i,j},\, d_j]$ of that machine; two jobs assigned to the same machine may not
overlap. The objective $\sum_j Z_j$ counts the jobs that are just in time, and the decision
problem asks whether all $n$ jobs can be just in time at once. It is NP-hard.

# Formalization notes

The problem is stated at the maximum value of the objective, which is the form the
reduction into fair repetitive interval scheduling uses and the form in which it is hard: a
schedule is an assignment of every job to a machine such that no two jobs on a machine
overlap.

Due dates do not depend on the machine, and processing times do, which is what makes the
machines unrelated.
-/

namespace Lax117284.JustInTime

open Lax434930.PolynomialTime

/-- An instance of `R || ∑_j Z_j`: `jobs` jobs and `machines` unrelated machines, where job
`j` has due date `d j` and processing time `p i j` on machine `i`. -/
structure Instance where
  /-- The number `n` of jobs. -/
  jobs : ℕ
  /-- The number `m` of machines. -/
  machines : ℕ
  /-- The processing time `p i j` of job `j` on machine `i`. -/
  p : Fin machines → Fin jobs → ℕ
  /-- The due date `d j` of job `j`, the same on every machine. -/
  d : Fin jobs → ℕ
  /-- Every job takes some time. -/
  p_pos : ∀ i j, 0 < p i j
  /-- No job starts before time `0`. -/
  p_le_d : ∀ i j, p i j ≤ d j

namespace Instance

variable (R : Instance)

/-- The interval `(d j - p i j, d j]` occupied by job `j` when it is executed just in time
on machine `i`. -/
def job (i : Fin R.machines) (j : Fin R.jobs) : Set ℕ :=
  Set.Ioc (R.d j - R.p i j) (R.d j)

/-- Jobs `j` and `j'` **overlap on machine `i`**: executing both just in time on that
machine would have them share a time point. -/
def Overlap (i : Fin R.machines) (j j' : Fin R.jobs) : Prop :=
  (R.job i j ∩ R.job i j').Nonempty

/-- **The question of `R || ∑_j Z_j` at its maximum value**: can every job be executed just
in time, that is, is there an assignment of the jobs to machines under which no two jobs of
a machine overlap? -/
def AllJustInTime : Prop :=
  ∃ f : Fin R.jobs → Fin R.machines,
    ∀ j j', j ≠ j' → f j = f j' → ¬ R.Overlap (f j) j j'

end Instance

/-- An instance as a binary word: the number of jobs, the number of machines, the due
dates, and then the processing times machine by machine. -/
def encodeInstance (R : Instance) : Word :=
  Problems.encodeNat R.jobs ++ Problems.encodeNat R.machines ++
    ((List.finRange R.jobs).flatMap fun j => Problems.encodeNat (R.d j)) ++
    (List.finRange R.machines).flatMap fun i =>
      (List.finRange R.jobs).flatMap fun j => Problems.encodeNat (R.p i j)

/-- **`R || ∑_j Z_j`**, as a language. -/
def AllJIT : Language :=
  {w | ∃ R : Instance, encodeInstance R = w ∧ R.AllJustInTime}

/-- **`R || ∑_j Z_j` is NP-hard.** -/
axiom allJIT_npHard : Problems.NPHard AllJIT

end Lax117284.JustInTime
