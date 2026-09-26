import Lax117284Proofs.Theorem11_FromRZ
import Lax117284Proofs.Transport
import Lax117284.Theorem11

/-!
Just-in-time scheduling on unrelated parallel machines, read as fair repetitive interval
scheduling with day-independent due dates. The construction is a renaming, so the numbering
it needs is the identity on both sides.
-/

namespace Lax117284Proofs.Theorem11

open Lax117284.JustInTime

/-- The instance of the development belonging to an instance of `R || ∑_j Z_j`. -/
def rz (R : Instance) : Model.Theorem11.RZ where
  Job := Fin R.jobs
  Machine := Fin R.machines
  jobFintype := inferInstance
  jobDecEq := inferInstance
  machineFintype := inferInstance
  machineDecEq := inferInstance
  p := R.p
  d := R.d
  p_pos := R.p_pos
  p_le_d := R.p_le_d

/-- The two notions of two jobs overlapping on a machine agree. -/
theorem overlap_iff (R : Instance) (i : Fin R.machines) (j j' : Fin R.jobs) :
    R.Overlap i j j' ↔ (rz R).Conflict i j j' := by
  have h1 := R.p_pos i j
  have h2 := R.p_le_d i j
  have h3 := R.p_pos i j'
  have h4 := R.p_le_d i j'
  simp only [Instance.Overlap, Instance.job, Model.Theorem11.RZ.Conflict, rz,
    Set.Nonempty, Set.mem_inter_iff, Set.mem_Ioc]
  constructor
  · rintro ⟨t, ⟨h5, h6⟩, h7, h8⟩
    omega
  · intro h
    exact ⟨min (R.d j) (R.d j'), by omega, by omega⟩

/-- The two questions agree. -/
theorem allJustInTime_iff (R : Instance) : R.AllJustInTime ↔ (rz R).AllJIT := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun j j' hne he hc => hf j j' hne he ((overlap_iff R _ j j').2 hc)⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, fun j j' hne he hc => hf j j' hne he ((overlap_iff R _ j j').1 hc)⟩

/-- The constructed instance of the development is the numbered one, with both bijections
the identity. -/
def numbering (R : Instance) :
    Transport.Numbering (Model.Theorem11.RZ.inst (rz R)) (Lax117284.Theorem11.inst R) :=
  Transport.Numbering.ofJobs (Equiv.refl _) (Equiv.refl _) (fun _ _ => rfl) (fun _ _ => rfl)

/--
---
conclusion: Lax117284.Theorem11.inst_dayIndepD
---
The due date of a client is the due date of its job, which does not depend on the machine.
-/
theorem inst_dayIndepD (R : Instance) : (Lax117284.Theorem11.inst R).DayIndepD :=
  fun _ _ _ => rfl

/--
---
conclusion: Lax117284.Theorem11.correct
---
An assignment of the jobs to machines with no two jobs of a machine overlapping is a
schedule serving every client once, and conversely.
-/
theorem correct (R : Instance) :
    R.AllJustInTime ↔ (Lax117284.Theorem11.inst R).HasKFairSchedule 1 := by
  rw [allJustInTime_iff, Model.Theorem11.RZ.hasOneFairSchedule_iff_allJIT]
  exact (numbering R).hasKFairSchedule_iff 1

end Lax117284Proofs.Theorem11
