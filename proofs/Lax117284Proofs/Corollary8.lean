import Lax117284Proofs.Corollary8_Induction
import Lax117284Proofs.Transport
import Lax117284.Corollary8

/-!
The two steps that lift hardness from one pair of a number of days and a fairness parameter
to the next. Both constructions of the concepts give the added day the processing times of
the first day, and the added day's layout of the development is the one of the concepts once
its arbitrary enumeration of the clients is the numbering they already carry.
-/

namespace Lax117284Proofs.Corollary8

open Lax117284.Scheduling Lax117284.Corollary8

/-- The processing times the added day carries: those of the first day. -/
def q (J : Instance) : Fin J.clients → ℕ := fun j => J.pAt 0 j

theorem q_pos (J : Instance) : ∀ j, 0 < q J j := fun j => J.pAt_pos 0 j

/-- The processing times of the first day do not exceed the time at which the blocking job
ends. -/
theorem q_le_bound (J : Instance) : ∀ j, q J j ≤ bound J := by
  intro j
  have h1 := J.pAt_le_dAt 0 (j : ℕ)
  have h2 : J.dAt 0 (j : ℕ) ≤ bound J := by
    unfold Instance.dAt bound
    split_ifs with h h'
    · have h3 : J.d ⟨0, h⟩ ⟨(j : ℕ), h'⟩ ≤ Finset.univ.sup fun j' => J.d ⟨0, h⟩ j' :=
        Finset.le_sup (Finset.mem_univ _)
      have h4 : (Finset.univ.sup fun j' => J.d ⟨0, h⟩ j') ≤
          Finset.univ.sup fun i' => Finset.univ.sup fun j' => J.d i' j' :=
        Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => J.d i' j') (Finset.mem_univ _)
      omega
    · omega
    · omega
  simpa [q] using h1.trans h2

/-- With day-independent processing times, the processing time of a job is the one it has on
the first day. -/
theorem pAt_eq_of_dayIndepP {J : Instance} (h : J.DayIndepP) {a : ℕ} (ha : a < J.days)
    (j : Fin J.clients) : J.pAt a j = J.pAt 0 j := by
  have h0 : 0 < J.days := by omega
  have e1 : J.pAt a (j : ℕ) = J.p ⟨a, ha⟩ j := by simp [Instance.pAt, ha, j.isLt]
  have e2 : J.pAt 0 (j : ℕ) = J.p ⟨0, h0⟩ j := by simp [Instance.pAt, h0, j.isLt]
  rw [e1, e2]
  exact h _ _ _

theorem free_p_castSucc (J : Instance) (i : Fin J.days) (j : Fin J.clients) :
    (addFreeDay J).p i.castSucc j = J.p i j := by
  simp [addFreeDay, Fin.coe_castSucc, i.isLt]

theorem free_p_last (J : Instance) (j : Fin J.clients) :
    (addFreeDay J).p (Fin.last J.days) j = J.pAt 0 j := by
  simp [addFreeDay]

theorem free_d_castSucc (J : Instance) (i : Fin J.days) (j : Fin J.clients) :
    (addFreeDay J).d i.castSucc j = J.d i j := by
  simp [addFreeDay, Fin.coe_castSucc, i.isLt]

theorem free_d_last (J : Instance) (j : Fin J.clients) :
    (addFreeDay J).d (Fin.last J.days) j = ((j : ℕ) + 1) * gap J := by
  simp [addFreeDay]

theorem block_p_castSucc_castSucc (J : Instance) (i : Fin J.days) (j : Fin J.clients) :
    (addBlockingDay J).p i.castSucc j.castSucc = J.p i j := by
  simp [addBlockingDay, Fin.coe_castSucc, i.isLt, j.isLt]

theorem block_p_castSucc_last (J : Instance) (i : Fin J.days) :
    (addBlockingDay J).p i.castSucc (Fin.last J.clients) = bound J := by
  simp [addBlockingDay]

theorem block_p_last_castSucc (J : Instance) (j : Fin J.clients) :
    (addBlockingDay J).p (Fin.last J.days) j.castSucc = J.pAt 0 j := by
  simp [addBlockingDay, Fin.coe_castSucc, j.isLt]

theorem block_p_last_last (J : Instance) :
    (addBlockingDay J).p (Fin.last J.days) (Fin.last J.clients) = bound J := by
  simp [addBlockingDay]

theorem block_d_castSucc_castSucc (J : Instance) (i : Fin J.days) (j : Fin J.clients) :
    (addBlockingDay J).d i.castSucc j.castSucc = J.d i j := by
  simp [addBlockingDay, Fin.coe_castSucc, i.isLt, j.isLt]

theorem block_d_castSucc_last (J : Instance) (i : Fin J.days) :
    (addBlockingDay J).d i.castSucc (Fin.last J.clients) = bound J := by
  simp [addBlockingDay]

theorem block_d_last_castSucc (J : Instance) (j : Fin J.clients) :
    (addBlockingDay J).d (Fin.last J.days) j.castSucc = bound J := by
  simp [addBlockingDay, Fin.coe_castSucc, j.isLt]

theorem block_d_last_last (J : Instance) :
    (addBlockingDay J).d (Fin.last J.days) (Fin.last J.clients) = bound J := by
  simp [addBlockingDay]

/-- The instance of the development with a conflict-free day added is the numbered one. -/
noncomputable def freeNumbering (J : Instance) :
    Transport.Numbering
      (Model.AddFreeDay.inst (Bridge.model J) (q J) (fun j : Fin J.clients => j.val)
        (q_pos J))
      (addFreeDay J) :=
  Transport.Numbering.ofJobs (Equiv.refl _) (Transport.dayEquivSucc J.days)
    (by
      rintro (i | u) j
      · exact (free_p_castSucc J i j).symm
      · exact (free_p_last J j).symm)
    (by
      rintro (i | u) j
      · exact (free_d_castSucc J i j).symm
      · exact (free_d_last J j).symm)

/-- The instance of the development with a blocking client and a blocking day added is the
numbered one. -/
noncomputable def blockingNumbering (J : Instance) :
    Transport.Numbering
      (Model.AddBlockingDay.inst (Bridge.model J) (q J) (q_pos J) (q_le_bound J))
      (addBlockingDay J) :=
  Transport.Numbering.ofJobs (Transport.dayEquivSucc J.clients)
    (Transport.dayEquivSucc J.days)
    (by
      rintro (i | u) (j | v)
      · exact (block_p_castSucc_castSucc J i j).symm
      · exact (block_p_castSucc_last J i).symm
      · exact (block_p_last_castSucc J j).symm
      · exact (block_p_last_last J).symm)
    (by
      rintro (i | u) (j | v)
      · exact (block_d_castSucc_castSucc J i j).symm
      · exact (block_d_castSucc_last J i).symm
      · exact (block_d_last_castSucc J j).symm
      · exact (block_d_last_last J).symm)

/--
---
conclusion: Lax117284.Corollary8.addFreeDay_correct
---
On the added day every client is served, and on the old days nothing has changed.
-/
theorem addFreeDay_correct (J : Instance) (hm : 0 < J.days) (k : ℕ) :
    J.HasKFairSchedule k ↔ (addFreeDay J).HasKFairSchedule (k + 1) := by
  rw [Bridge.hasKFairSchedule_iff,
    Model.AddFreeDay.hasKFairSchedule_addFreeDay (idx := fun j : Fin J.clients => j.val)
      (hq := q_pos J) Fin.val_injective k]
  exact (freeNumbering J).hasKFairSchedule_iff (k + 1)

/--
---
conclusion: Lax117284.Corollary8.addBlockingDay_correct
---
The blocking client must be served on the added day, on which all jobs coincide, and is
blocked everywhere else; the rest of the schedule is a schedule of the old instance.
-/
theorem addBlockingDay_correct (J : Instance) (hm : 0 < J.days) :
    J.HasKFairSchedule 1 ↔ (addBlockingDay J).HasKFairSchedule 1 := by
  rw [Bridge.hasKFairSchedule_iff,
    Model.AddBlockingDay.hasOneFairSchedule_addBlockingDay (hq := q_pos J)
      (hqP := q_le_bound J)]
  exact (blockingNumbering J).hasKFairSchedule_iff 1

/--
---
conclusion: Lax117284.Corollary8.addFreeDay_dayIndepP
---
Every day of the instance, old or new, gives a client the processing time it has on the
first day.
-/
theorem addFreeDay_dayIndepP {J : Instance} (h : J.DayIndepP) :
    (addFreeDay J).DayIndepP := by
  have key : ∀ (a : Fin (J.days + 1)) (j : Fin J.clients),
      (addFreeDay J).p a j = J.pAt 0 j := by
    intro a j
    show (if (a : ℕ) < J.days then J.pAt a j else J.pAt 0 j) = J.pAt 0 j
    split_ifs with ha
    · exact pAt_eq_of_dayIndepP h ha j
    · rfl
  intro i i' j
  rw [key i j, key i' j]

/--
---
conclusion: Lax117284.Corollary8.addBlockingDay_dayIndepP
---
The added client has the same job on every day, and every other client has the processing
time it has on the first day.
-/
theorem addBlockingDay_dayIndepP {J : Instance} (h : J.DayIndepP) :
    (addBlockingDay J).DayIndepP := by
  have key : ∀ (a : Fin (J.days + 1)) (j : Fin (J.clients + 1)),
      (addBlockingDay J).p a j =
        if hj : (j : ℕ) < J.clients then J.pAt 0 j else bound J := by
    intro a j
    show (if (j : ℕ) < J.clients then
        (if (a : ℕ) < J.days then J.pAt a j else J.pAt 0 j)
      else bound J) = _
    split_ifs with hj ha
    · exact pAt_eq_of_dayIndepP h ha ⟨j, hj⟩
    · rfl
    · rfl
  intro i i' j
  rw [key i j, key i' j]

end Lax117284Proofs.Corollary8
