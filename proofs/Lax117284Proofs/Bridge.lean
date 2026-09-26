import Lax117284Proofs.ConflictGraph
import Lax117284Proofs.Trivial
import Lax117284.ConflictGraph

/-!
The instances of the concepts are the instances of the ported development whose clients and
days are numbered. This file carries that identification: `model I` is the instance of the
development belonging to the numbered instance `I`, and the lemmas below say that the two
speak about the same jobs, the same feasible schedules and the same fair schedules.

The development's conflict relation is the arithmetic one, "each job starts before the other
is due"; the concept's is the geometric one, "the two jobs share a time point". They agree
because processing times are positive.
-/

namespace Lax117284Proofs.Bridge

open Lax117284.Scheduling

/-- The instance of the development belonging to a numbered instance. -/
def model (I : Instance) : Model.Instance where
  Client := Fin I.clients
  Day := Fin I.days
  clientFintype := inferInstance
  clientDecEq := inferInstance
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p := I.p
  d := I.d
  p_pos := I.p_pos
  p_le_d := I.p_le_d

@[simp] theorem model_numDays (I : Instance) : (model I).numDays = I.days :=
  Fintype.card_fin I.days

/-- The two conflict relations agree. -/
theorem conflict_iff (I : Instance) (i : Fin I.days) (j j' : Fin I.clients) :
    I.Conflict i j j' ↔ (model I).Conflict i j j' := by
  have h1 := I.p_pos i j
  have h2 := I.p_le_d i j
  have h3 := I.p_pos i j'
  have h4 := I.p_le_d i j'
  simp only [Instance.Conflict, Instance.job, Set.Ioc_inter_Ioc, Set.nonempty_Ioc,
    max_lt_iff, lt_min_iff, Model.Instance.Conflict, Model.Instance.start, model]
  omega

/-- The two notions of feasibility agree. -/
theorem feasible_iff {I : Instance} (σ : I.Schedule) :
    Instance.Feasible σ ↔ Model.Instance.Feasible (I := model I) σ := by
  constructor
  · intro h i j hj j' hj' hne hc
    exact h i (Finset.mem_coe.2 hj) (Finset.mem_coe.2 hj') hne ((conflict_iff I i j j').2 hc)
  · intro h i j hj j' hj' hne hc
    exact h i j (Finset.mem_coe.1 hj) j' (Finset.mem_coe.1 hj') hne
      ((conflict_iff I i j j').1 hc)

/-- The two notions of "how often a client is served" agree. -/
theorem served_eq {I : Instance} (σ : I.Schedule) (j : Fin I.clients) :
    Instance.served σ j = Model.Instance.served (I := model I) σ j := rfl

/-- The two questions agree, for per-client fairness parameters. -/
theorem hasFairSchedule_iff (I : Instance) (k : Fin I.clients → ℕ) :
    I.HasFairSchedule k ↔ (model I).HasFairSchedule k := by
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    exact ⟨σ, (feasible_iff σ).1 hfeas, fun j => (hfair j).trans (le_of_eq (served_eq σ j))⟩
  · rintro ⟨σ, hfeas, hfair⟩
    exact ⟨σ, (feasible_iff σ).2 hfeas,
      fun j => (hfair j).trans (le_of_eq (served_eq σ j).symm)⟩

/-- The two questions agree, for a uniform fairness parameter. -/
theorem hasKFairSchedule_iff (I : Instance) (k : ℕ) :
    I.HasKFairSchedule k ↔ (model I).HasKFairSchedule k :=
  hasFairSchedule_iff I _

/-- The two notions of a conflict-free instance agree. -/
theorem conflictFree_iff (I : Instance) :
    I.ConflictFree ↔ (model I).ConflictFree :=
  ⟨fun h i j j' hne hc => h i j j' hne ((conflict_iff I i j j').2 hc),
    fun h i j j' hne hc => h i j j' hne ((conflict_iff I i j j').1 hc)⟩

/-- The two notions of unit processing times agree. -/
theorem unitP_iff (I : Instance) : I.UnitP ↔ (model I).UnitP := Iff.rfl

/-- The two day conflict graphs agree. -/
theorem dayGraph_eq (I : Instance) (i : Fin I.days) :
    Lax117284.ConflictGraph.dayGraph I i = (model I).dayGraph i := by
  ext j j'
  simp only [Lax117284.ConflictGraph.dayGraph, Model.Instance.dayGraph_adj]
  exact and_congr_right fun _ => conflict_iff I i j j'

/-- The two overall conflict graphs agree. -/
theorem overallGraph_eq (I : Instance) :
    Lax117284.ConflictGraph.overallGraph I = (model I).overallGraph := by
  ext j j'
  simp only [Lax117284.ConflictGraph.overallGraph]
  exact and_congr_right fun _ => exists_congr fun i => conflict_iff I i j j'

end Lax117284Proofs.Bridge
