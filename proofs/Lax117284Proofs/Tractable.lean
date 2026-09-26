import Lax117284Proofs.Bridge
import Lax117284Proofs.Theorem10_Matching
import Lax117284Proofs.Theorem12_DP
import Lax117284Proofs.Theorem13_Coloring
import Lax117284.Theorem10
import Lax117284.Theorem12
import Lax117284.Theorem13

/-!
The three restrictions of the problem that are solved rather than reduced: unit processing
times as a matching problem, day-independent due dates by a dynamic program, and
day-independent due dates and processing times by a colouring.
-/

namespace Lax117284Proofs.Tractable

open Lax117284.Scheduling

/-- The dynamic program of the concept is the one of the development: both are the same
recursion on the list of clients. -/
theorem program_iff {I : Instance} (dd : Fin I.clients → ℕ) (k : ℕ) :
    ∀ (l : List (Fin I.clients)) (free : Fin I.days → ℕ),
      Lax117284.Theorem12.Program dd k l free ↔
        Model.Instance.Dp (I := Bridge.model I) dd k l free := by
  intro l
  induction l with
  | nil => intro _; exact Iff.rfl
  | cons j rest ih =>
    intro free
    simp only [Lax117284.Theorem12.Program, Model.Instance.Dp]
    exact exists_congr fun S => and_congr Iff.rfl (and_congr Iff.rfl (ih _))

/-- The bipartite graph of the concept is the one of the development. -/
theorem hasFullMatching_iff (I : Instance) (k : ℕ) :
    Lax117284.Theorem10.HasFullMatching I k ↔
      Model.Instance.HasFullMatching (Bridge.model I) k := by
  simp only [Lax117284.Theorem10.HasFullMatching, Lax117284.Theorem10.Matchable,
    Lax117284.Theorem10.Target, Model.Instance.HasFullMatching, Model.Instance.Matchable,
    Model.Instance.MatchTarget, Bridge.model_numDays]
  exact Iff.rfl

/--
---
conclusion: Lax117284.Theorem10.conflict_iff_d_eq_of_unitP
---
With unit processing times a job occupies the single time unit ending at its due date.
-/
theorem conflict_iff_d_eq_of_unitP {I : Instance} (h : I.UnitP) (i : Fin I.days)
    (j j' : Fin I.clients) : I.Conflict i j j' ↔ I.d i j = I.d i j' := by
  rw [Bridge.conflict_iff]
  exact Model.Instance.conflict_iff_d_eq_of_unitP (I := Bridge.model I) h i j j'

/--
---
conclusion: Lax117284.Theorem10.hasKFairSchedule_iff_hasFullMatching
---
A scheduled job is matched to the slot of its day and due date, a rejected one to one of
the `m - k` rejections its client is allowed.
-/
theorem hasKFairSchedule_iff_hasFullMatching {I : Instance} (h : I.UnitP) {k : ℕ}
    (hk : k ≤ I.days) :
    I.HasKFairSchedule k ↔ Lax117284.Theorem10.HasFullMatching I k := by
  rw [Bridge.hasKFairSchedule_iff, hasFullMatching_iff]
  exact Model.Instance.hasKFairSchedule_iff_hasFullMatching (I := Bridge.model I) h
    (by rwa [Bridge.model_numDays])

/--
---
conclusion: Lax117284.Theorem12.hasKFairSchedule_iff_program
---
Processing the clients in due-date order makes the time at which each machine becomes free
a sufficient state.
-/
theorem hasKFairSchedule_iff_program {I : Instance} (hd : I.DayIndepD) (i₀ : Fin I.days)
    (k : ℕ) {l : List (Fin I.clients)} (hnd : l.Nodup) (hall : ∀ j, j ∈ l)
    (hsorted : l.Pairwise fun a b => I.d i₀ a ≤ I.d i₀ b) :
    I.HasKFairSchedule k ↔ Lax117284.Theorem12.Program (I.d i₀) k l fun _ => 0 := by
  rw [Bridge.hasKFairSchedule_iff, program_iff]
  exact Model.Instance.hasKFairSchedule_iff_dp (I := Bridge.model I) hd i₀ k hnd hall hsorted

/--
---
conclusion: Lax117284.Theorem13.dayGraph_eq_of_dayIndep
---
With both data day-independent, every day presents the same jobs.
-/
theorem dayGraph_eq_of_dayIndep {I : Instance} (hd : I.DayIndepD) (hp : I.DayIndepP)
    (i i' : Fin I.days) :
    Lax117284.ConflictGraph.dayGraph I i = Lax117284.ConflictGraph.dayGraph I i' := by
  rw [Bridge.dayGraph_eq, Bridge.dayGraph_eq]
  exact Model.Instance.dayGraph_eq_of_dayIndep (I := Bridge.model I) hd hp i i'

/--
---
conclusion: Lax117284.Theorem13.chromaticNumber_dayGraph
---
Colour the clients greedily in the order in which their jobs start: when a job is coloured,
the jobs already coloured that it meets are all running at the instant it starts, so they
and it form a clique, and a colour below the clique number is free.
-/
theorem chromaticNumber_dayGraph (I : Instance) (i : Fin I.days) :
    (Lax117284.ConflictGraph.dayGraph I i).chromaticNumber =
      (Lax117284.ConflictGraph.dayGraph I i).cliqueNum := by
  rw [Bridge.dayGraph_eq]
  exact Model.Instance.chromaticNumber_dayGraph (Bridge.model I) i

/--
---
conclusion: Lax117284.Theorem13.hasKFairSchedule_iff_mul_cliqueNum_le
---
A feasible schedule meets a clique in at most one client per day, and a proper colouring
serves its classes in rotation.
-/
theorem hasKFairSchedule_iff_mul_cliqueNum_le {I : Instance} (hd : I.DayIndepD)
    (hp : I.DayIndepP) (i₀ : Fin I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔ k * (Lax117284.ConflictGraph.dayGraph I i₀).cliqueNum ≤ I.days := by
  rw [Bridge.hasKFairSchedule_iff, Bridge.dayGraph_eq, ← Bridge.model_numDays]
  exact Model.Instance.hasKFairSchedule_iff_mul_cliqueNum_le (I := Bridge.model I) hd hp i₀ k

/--
---
conclusion: Lax117284.Theorem13.hasKFairSchedule_iff_mul_chromaticNumber_le
---
The clique number of a day's conflict graph is its chromatic number, the graph being an
interval graph.
-/
theorem hasKFairSchedule_iff_mul_chromaticNumber_le {I : Instance} (hd : I.DayIndepD)
    (hp : I.DayIndepP) (i₀ : Fin I.days) (k : ℕ) :
    I.HasKFairSchedule k ↔
      (k : ℕ∞) * (Lax117284.ConflictGraph.dayGraph I i₀).chromaticNumber ≤ I.days := by
  rw [Bridge.hasKFairSchedule_iff, Bridge.dayGraph_eq, ← Bridge.model_numDays]
  exact Model.Instance.hasKFairSchedule_iff_mul_chromaticNumber_le (I := Bridge.model I) hd hp i₀ k

end Lax117284Proofs.Tractable
