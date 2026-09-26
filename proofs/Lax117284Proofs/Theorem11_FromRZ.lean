import Lax117284Proofs.Defs

/-!
# Theorem 11: day-independent due dates are NP-hard

> **Theorem 11.** The `1 | rep, d_{i,j} = d_j | min_j ∑_i Z_{i,j}` problem is NP-hard.
>
> *Proof.* We give a reduction from `R || ∑_j Z_j` to `1 | rep, d_{i,j} = d_j |
> min_j ∑_i Z_{i,j}` with `k = 1`. Given an instance of `R || ∑_j Z_j` we create an instance
> of `1 | rep, d_{i,j} = d_j | min_j ∑_i Z_{i,j}` as follows: For every job `j` we create a
> client `c_j`, and for every machine `i` create a day `i`. The due dates are
> day-independent. Accordingly, `d_j` is the common due-date of all jobs belonging to client
> `c_j`. The processing time of client `c_j`'s job on day `i` is `p_{i,j}` (that is, the
> processing time of job `j` on machine `i`). We then ask if there exists a `1`-fair schedule
> for the constructed instance.

`R || ∑_j Z_j`: `n` jobs with due dates `d_j`, `m` unrelated machines, job `j` taking
`p_{i,j}` on machine `i`, and the question of whether **all** jobs can run just-in-time.

The reduction is an identity in disguise. A `1`-fair schedule of the constructed instance
must serve every client on at least one day, and *serving client `j` on day `i`* is exactly
*running job `j` on machine `i`*; conversely an assignment of jobs to machines is a schedule
that serves every client at least once. The only thing to check is that the two feasibility
notions agree, and they do, because the constructed instance's day-`i` conflict relation is
the machine-`i` conflict relation by construction (`conflict_iff`).

Both directions are `hasOneFairSchedule_iff_allJIT`. The NP-hardness of `R || ∑_j Z_j`
itself is Sung and Vlach's [20], cited in `Assumptions.lean`; nothing about it is proved
here.
-/


namespace Lax117284Proofs.Model

namespace Theorem11

open Instance

/-! ## 1. `R || ∑_j Z_j` -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An instance of **`R || ∑_j Z_j`**: unrelated parallel machines, one due date per job,
and the question of running every job just-in-time. -/
structure RZ where
  /-- The jobs. -/
  Job : Type
  /-- The machines. -/
  Machine : Type
  jobFintype : Fintype Job
  jobDecEq : DecidableEq Job
  machineFintype : Fintype Machine
  machineDecEq : DecidableEq Machine
  /-- `p i j`, the processing time of job `j` on machine `i`. -/
  p : Machine → Job → ℕ
  /-- `d j`, the due date of job `j` — the same on every machine. -/
  d : Job → ℕ
  p_pos : ∀ i j, 0 < p i j
  p_le_d : ∀ i j, p i j ≤ d j

attribute [instance] RZ.jobFintype RZ.jobDecEq RZ.machineFintype RZ.machineDecEq

namespace RZ

variable (R : RZ)

/-- Jobs `j` and `j'` conflict on machine `i`: their machine-`i` intervals intersect. -/
def Conflict (i : R.Machine) (j j' : R.Job) : Prop :=
  R.d j - R.p i j < R.d j' ∧ R.d j' - R.p i j' < R.d j

/-- **The question of `R || ∑_j Z_j` with all `n` jobs just-in-time**: an assignment of jobs
to machines under which no machine runs two conflicting jobs. -/
def AllJIT : Prop :=
  ∃ f : R.Job → R.Machine, ∀ j j', j ≠ j' → f j = f j' → ¬ R.Conflict (f j) j j'

/-! ## 2. The constructed instance -/

/-- **The instance of Theorem 11**: clients are jobs, days are machines, the due date is
the job's and so day-independent, and the processing time on day `i` is the job's on
machine `i`. -/
@[reducible] def inst : Instance where
  Client := R.Job
  Day := R.Machine
  clientFintype := R.jobFintype
  clientDecEq := R.jobDecEq
  dayFintype := R.machineFintype
  dayDecEq := R.machineDecEq
  p i j := R.p i j
  d _ j := R.d j
  p_pos := R.p_pos
  p_le_d i j := R.p_le_d i j

/-! ## 3. Correctness -/

variable {R}

/-- **Theorem 11's correctness.** The constructed instance admits a feasible `1`-fair
schedule exactly when every job of `R || ∑_j Z_j` can run just-in-time. -/
theorem hasOneFairSchedule_iff_allJIT :
    R.AllJIT ↔ (inst R).HasKFairSchedule 1 := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨fun i => Finset.univ.filter fun j => f j = i, ?_, fun j => ?_⟩
    · intro i j hj j' hj' hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
      subst hj
      exact hf j j' hne hj'.symm
    · show 1 ≤ _
      refine Nat.one_le_iff_ne_zero.2 fun hzero => ?_
      have : (f j) ∈ Finset.univ.filter fun i => j ∈ Finset.univ.filter fun j' => f j' = i := by
        simp
      rw [served] at hzero
      exact absurd hzero (Finset.card_ne_zero_of_mem this)
  · rintro ⟨σ, hfeas, hfair⟩
    choose f hf using fun j : R.Job =>
      exists_mem_of_served_pos (lt_of_lt_of_le Nat.zero_lt_one (hfair j))
    exact ⟨f, fun j j' hne hEq => hfeas (f j) j (hf j) j' (hEq ▸ hf j') hne⟩

end RZ

end Theorem11

end Lax117284Proofs.Model
