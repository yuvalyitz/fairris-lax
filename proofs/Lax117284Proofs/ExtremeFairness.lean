import Lax117284Proofs.Bridge
import Lax117284.ExtremeFairness

/-!
The conflict graph observation and the three values of the fairness parameter that are
settled by inspection.
-/

namespace Lax117284Proofs.ExtremeFairness

open Lax117284.Scheduling

/--
---
conclusion: Lax117284.ConflictGraph.feasible_iff_isIndepSet
---
Feasibility forbids exactly the conflicting pairs of a day, which are exactly the edges of
that day's conflict graph.
-/
theorem feasible_iff_isIndepSet {I : Instance} (σ : I.Schedule) :
    Instance.Feasible σ ↔
      ∀ i, (Lax117284.ConflictGraph.dayGraph I i).IsIndepSet (σ i : Set (Fin I.clients)) := by
  simp only [Bridge.feasible_iff, Bridge.dayGraph_eq]
  exact Model.Instance.feasible_iff_isIndepSet

/--
---
conclusion: Lax117284.ExtremeFairness.hasKFairSchedule_zero
---
The empty schedule is feasible and serves every client on no day, which is enough.
-/
theorem hasKFairSchedule_zero (I : Instance) : I.HasKFairSchedule 0 :=
  (Bridge.hasKFairSchedule_iff I 0).2 Model.Instance.hasKFairSchedule_zero

/--
---
conclusion: Lax117284.ExtremeFairness.hasKFairSchedule_days_iff
---
A client served on as many days as there are is served on every one of them, so the whole
of every day must be free of conflicts; conversely, on a conflict-free instance every
client can be served every day.
-/
theorem hasKFairSchedule_days_iff (I : Instance) :
    I.HasKFairSchedule I.days ↔ I.ConflictFree := by
  rw [Bridge.hasKFairSchedule_iff, Bridge.conflictFree_iff, ← Bridge.model_numDays]
  exact Model.Instance.hasKFairSchedule_numDays_iff

/--
---
conclusion: Lax117284.ExtremeFairness.not_hasKFairSchedule_of_days_lt
---
No client is served on more days than there are days.
-/
theorem not_hasKFairSchedule_of_days_lt {I : Instance} {k : ℕ} (hk : I.days < k)
    (hn : 0 < I.clients) : ¬ I.HasKFairSchedule k := by
  rw [Bridge.hasKFairSchedule_iff]
  exact Model.Instance.not_hasKFairSchedule_of_gt (by rwa [Bridge.model_numDays])
    ⟨0, hn⟩

end Lax117284Proofs.ExtremeFairness
