import Lax117284.JustInTime
import Lax888481.Scheduling

/-!
The reduction from interval scheduling with eligible machine sets (schedule every job) to
just-in-time scheduling on unrelated machines.

Every machine of the interval scheduling instance is a machine of the just-in-time instance.
Each job `j` becomes a job with due date `d j + 1`; on an eligible machine it takes `p j`,
so that it occupies `(d j + 1 - p j, d j + 1]`, which lies to the right of the point `1`;
on a machine that is not eligible it takes `d j + 1`, so that it occupies `(0, d j + 1]`, which
contains the point `1`. One more job per machine, a *wall*, is due at `1` and takes `1` on every
machine: it occupies the point `1` alone. The walls overlap one another, so they sit on pairwise
distinct machines, hence on all of them, and a job on an ineligible machine would overlap
the wall of that machine.

If there is no job, the instance is already schedulable, and it gets no wall: the walls
would be exponentially many in the size of the input.
-/

namespace Lax117284Proofs.JitHard

open Lax888481.Scheduling

/-- An instance of interval scheduling with eligible machine sets. -/
abbrev SchedI := Lax888481.Scheduling.Instance

/-- An instance of just-in-time scheduling. -/
abbrev JitI := Lax117284.JustInTime.Instance

/-- The number of walls: one per machine, unless there is no job. -/
def walls (I : SchedI) : ℕ := if I.jobs = 0 then 0 else I.machines

/-- The due date of a job of the image: the real jobs come first, the walls after them. -/
def dOf (I : SchedI) (k : Fin (I.jobs + walls I)) : ℕ :=
  Fin.addCases (motive := fun _ => ℕ) (fun j => I.d j + 1) (fun _ => 1) k

/-- The processing time of a job of the image on a machine. -/
def pOf (I : SchedI) (i : Fin I.machines) (k : Fin (I.jobs + walls I)) : ℕ :=
  Fin.addCases (motive := fun _ => ℕ)
    (fun j => if i ∈ I.eligible j then I.p j else I.d j + 1) (fun _ => 1) k

/-- **The image of an instance.** -/
@[reducible] def toJIT (I : SchedI) : JitI where
  jobs := I.jobs + walls I
  machines := I.machines
  p := pOf I
  d := dOf I
  p_pos := fun i k => by
    refine Fin.addCases (fun j => ?_) (fun w => ?_) k
    · simp only [pOf, Fin.addCases_left]
      split
      · exact I.p_pos j
      · omega
    · simp [pOf]
  p_le_d := fun i k => by
    refine Fin.addCases (fun j => ?_) (fun w => ?_) k
    · simp only [pOf, dOf, Fin.addCases_left]
      have := I.p_le_d j
      split <;> omega
    · simp [pOf, dOf]

theorem toJIT_jobs (I : SchedI) : (toJIT I).jobs = I.jobs + walls I := rfl

theorem ioc_inter {a b c d : ℕ} :
    (Set.Ioc a b ∩ Set.Ioc c d).Nonempty ↔ a < b ∧ c < d ∧ a < d ∧ c < b := by
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨max a c + 1, ?_, ?_⟩ <;> simp only [Set.mem_Ioc] <;> omega

theorem job_left (I : SchedI) (i : Fin I.machines) (j : Fin I.jobs) :
    (toJIT I).job i (Fin.castAdd _ j) =
      if i ∈ I.eligible j then Set.Ioc (I.start j + 1) (I.d j + 1) else Set.Ioc 0 (I.d j + 1) := by
  have hp := I.p_le_d j
  have hs : I.start j = I.d j - I.p j := rfl
  simp only [Lax117284.JustInTime.Instance.job, pOf, dOf, Fin.addCases_left]
  split
  · congr 1
    omega
  · congr 1
    omega

theorem job_right (I : SchedI) (i : Fin I.machines) (w : Fin (walls I)) :
    (toJIT I).job i (Fin.natAdd _ w) = Set.Ioc 0 1 := by
  simp [Lax117284.JustInTime.Instance.job, pOf, dOf]

theorem start_lt (I : SchedI) (j : Fin I.jobs) : I.start j < I.d j := by
  have := I.p_pos j
  have := I.p_le_d j
  unfold Instance.start
  omega

/-- Two real jobs on a machine that is eligible for both overlap exactly when they overlap
in the source. -/
theorem overlap_left_left (I : SchedI) (i : Fin I.machines) (j j' : Fin I.jobs)
    (h : i ∈ I.eligible j) (h' : i ∈ I.eligible j') :
    (toJIT I).Overlap i (Fin.castAdd _ j) (Fin.castAdd _ j') ↔ I.Overlap j j' := by
  unfold Lax117284.JustInTime.Instance.Overlap
  rw [job_left, job_left, if_pos h, if_pos h', ioc_inter]
  have := start_lt I j
  have := start_lt I j'
  unfold Instance.Overlap
  omega

/-- A wall and a real job on an eligible machine do not overlap. -/
theorem not_overlap_wall_elig (I : SchedI) (i : Fin I.machines) (j : Fin I.jobs)
    (w : Fin (walls I)) (h : i ∈ I.eligible j) :
    ¬ (toJIT I).Overlap i (Fin.natAdd _ w) (Fin.castAdd _ j) := by
  unfold Lax117284.JustInTime.Instance.Overlap
  rw [job_right, job_left, if_pos h, ioc_inter]
  omega

/-- A wall and a real job on an ineligible machine overlap. -/
theorem overlap_wall_inelig (I : SchedI) (i : Fin I.machines) (j : Fin I.jobs)
    (w : Fin (walls I)) (h : i ∉ I.eligible j) :
    (toJIT I).Overlap i (Fin.castAdd _ j) (Fin.natAdd _ w) := by
  unfold Lax117284.JustInTime.Instance.Overlap
  rw [job_right, job_left, if_neg h, ioc_inter]
  omega

/-- Two walls overlap. -/
theorem overlap_wall_wall (I : SchedI) (i : Fin I.machines) (w w' : Fin (walls I)) :
    (toJIT I).Overlap i (Fin.natAdd _ w) (Fin.natAdd _ w') := by
  unfold Lax117284.JustInTime.Instance.Overlap
  rw [job_right, job_right, ioc_inter]
  omega

theorem walls_eq_of_pos (I : SchedI) (h : 0 < I.jobs) : walls I = I.machines := by
  unfold walls
  rw [if_neg (by omega)]

theorem walls_eq_zero (I : SchedI) (h : I.jobs = 0) : walls I = 0 := by
  unfold walls
  rw [if_pos h]

theorem overlap_comm (R : JitI) (i : Fin R.machines) (j j' : Fin R.jobs) :
    R.Overlap i j j' ↔ R.Overlap i j' j := by
  unfold Lax117284.JustInTime.Instance.Overlap
  rw [Set.inter_comm]

/-- With no job, the instance is schedulable, and so is its image. -/
theorem iff_of_jobs_zero (I : SchedI) (h : I.jobs = 0) :
    I.AllSchedulable ↔ (toJIT I).AllJustInTime := by
  have key : (toJIT I).jobs = 0 := by rw [toJIT_jobs, walls_eq_zero I h, h]
  have hj : ∀ k : Fin (toJIT I).jobs, False := fun k => by
    have := k.2
    omega
  constructor
  · intro _
    exact ⟨fun k => (hj k).elim, fun k => (hj k).elim⟩
  · intro _
    refine ⟨fun j => absurd j.2 (by simp [h]), ⟨fun j => absurd j.2 (by simp [h]), ?_⟩,
      fun j => absurd j.2 (by simp [h])⟩
    intro j
    exact absurd j.2 (by simp [h])

theorem castAdd_ne_natAdd {n m : ℕ} (j : Fin n) (w : Fin m) : Fin.castAdd m j ≠ Fin.natAdd n w := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := j.2
  omega

/-- A schedule of the source gives a placement of the image. -/
theorem jit_of_sched (I : SchedI) (h : 0 < I.jobs) (hs : I.AllSchedulable) :
    (toJIT I).AllJustInTime := by
  obtain ⟨σ, ⟨hel, hfe⟩, hc⟩ := hs
  have hw : walls I = I.machines := walls_eq_of_pos I h
  have hsome : ∀ j, (σ j).isSome = true := fun j => Option.isSome_iff_ne_none.mpr (hc j)
  refine ⟨fun k => Fin.addCases (motive := fun _ => Fin I.machines)
    (fun j => (σ j).get (hsome j)) (fun w => Fin.cast hw w) k, ?_⟩
  intro k k'
  refine Fin.addCases (fun j => ?_) (fun w => ?_) k <;>
  refine Fin.addCases (fun j' => ?_) (fun w' => ?_) k'
  · intro hne heq hov
    simp only [Fin.addCases_left] at heq hov
    have hji : σ j = some ((σ j).get (hsome j)) := (Option.some_get (hsome j)).symm
    have hji' : σ j' = some ((σ j').get (hsome j')) := (Option.some_get (hsome j')).symm
    generalize (σ j).get (hsome j) = i at heq hov hji
    generalize (σ j').get (hsome j') = i' at heq hov hji'
    subst heq
    have hne' : j ≠ j' := fun e => hne (by rw [e])
    rw [overlap_left_left I i j j' (hel j i hji) (hel j' i hji')] at hov
    exact hfe j j' i hne' hov hji hji'
  · intro _ heq hov
    simp only [Fin.addCases_left, Fin.addCases_right] at heq hov
    have hji : σ j = some ((σ j).get (hsome j)) := (Option.some_get (hsome j)).symm
    generalize (σ j).get (hsome j) = i at heq hov hji
    subst heq
    rw [overlap_comm] at hov
    exact not_overlap_wall_elig I _ j w' (hel j _ hji) hov
  · intro _ heq hov
    simp only [Fin.addCases_left, Fin.addCases_right] at heq hov
    have hji : σ j' = some ((σ j').get (hsome j')) := (Option.some_get (hsome j')).symm
    generalize (σ j').get (hsome j') = i at heq hov hji
    subst heq
    exact not_overlap_wall_elig I _ j' w (hel j' _ hji) hov
  · intro hne heq _
    simp only [Fin.addCases_right] at heq
    exact hne (by rw [Fin.cast_injective hw heq])

theorem sched_of_jit (I : SchedI) (h : 0 < I.jobs) (hj : (toJIT I).AllJustInTime) :
    I.AllSchedulable := by
  obtain ⟨f, hf⟩ := hj
  have hw : walls I = I.machines := walls_eq_of_pos I h
  -- the machines of the walls
  let g : Fin I.machines → Fin I.machines := fun w => f (Fin.natAdd I.jobs (Fin.cast hw.symm w))
  have ginj : Function.Injective g := by
    intro w w' hww
    by_contra hne
    have hne' : Fin.natAdd I.jobs (Fin.cast hw.symm w) ≠ Fin.natAdd I.jobs (Fin.cast hw.symm w') := by
      intro e
      exact hne (Fin.cast_injective hw.symm (Fin.natAdd_injective _ _ e))
    exact hf _ _ hne' hww (overlap_wall_wall I _ _ _)
  have gsurj : Function.Surjective g := Finite.injective_iff_surjective.mp ginj
  have hel : ∀ j : Fin I.jobs, f (Fin.castAdd _ j) ∈ I.eligible j := by
    intro j
    by_contra hn
    obtain ⟨w, hw'⟩ := gsurj (f (Fin.castAdd _ j))
    exact hf (Fin.castAdd _ j) (Fin.natAdd I.jobs (Fin.cast hw.symm w))
      (castAdd_ne_natAdd _ _) hw'.symm (overlap_wall_inelig I _ j _ hn)
  refine ⟨fun j => some (f (Fin.castAdd _ j)), ⟨?_, ?_⟩, fun j => by simp⟩
  · intro j i hji
    have := Option.some.inj hji
    rw [← this]
    exact hel j
  · intro j j' i hne hov hji hj'i
    have e1 := Option.some.inj hji
    have e2 := Option.some.inj hj'i
    have hne' : Fin.castAdd _ j ≠ Fin.castAdd (walls I) j' := fun e => hne (Fin.castAdd_injective _ _ e)
    refine hf _ _ hne' (e1.trans e2.symm) ?_
    rw [e1]
    exact (overlap_left_left I i j j' (e1 ▸ hel j) (e2 ▸ hel j')).mpr hov

/-- **The reduction is correct.** -/
theorem allSchedulable_iff (I : SchedI) : I.AllSchedulable ↔ (toJIT I).AllJustInTime := by
  rcases Nat.eq_zero_or_pos I.jobs with h | h
  · exact iff_of_jobs_zero I h
  · exact ⟨jit_of_sched I h, sched_of_jit I h⟩

end Lax117284Proofs.JitHard
