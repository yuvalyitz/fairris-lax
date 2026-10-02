import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Lax117284Proofs.Defs

/-!
# Conflict Graphs (Definition 5)

> **Definition 5.** Given an instance `I` of `1 | rep | min_j ∑_i Z_{i,j}` with `n` clients
> and `m` days, the *day `i` conflict graph* associated with `I` is the graph
> `G_i = ({1,…,n}, E_i)` where each vertex `j` is associated with a client `j` of `I`. Two
> vertices `j₁, j₂` are adjacent in `G_i` if their corresponding clients have a pair of
> conflicting jobs on day `i`. The *overall conflict graph* associated with `I` is the
> graph `G = ({1,…,n}, E₁ ∪ ⋯ ∪ E_m)`.

The one fact that makes the whole paper a graph-theory paper: *a feasible schedule on day
`i` is exactly an independent set of `G_i`* (`feasible_iff_isIndepSet`). Sections 4 and 5
then read off consequences — a daily schedule of an instance with day-independent due
dates and processing times is an independent set of a *single* graph (Theorem 13), and the
overall conflict graph's treewidth is a parameter worth bounding (Section 5).

`G_i` is an *interval graph*, the intersection graph of the `n` day-`i` intervals. This
file does not define "interval graph" abstractly: `dayGraph` is one by construction, and
`IntervalColoring.lean` proves the only property of interval graphs the paper uses — that
they are colorable with as many colors as their largest clique has vertices.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. The two graphs -/

variable (I) in
/-- **The day `i` conflict graph `G_i`** (Definition 5): clients are adjacent when their
day-`i` jobs conflict. -/
def dayGraph (i : I.Day) : SimpleGraph I.Client where
  Adj j j' := j ≠ j' ∧ I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, conflict_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable (I) in
/-- **The overall conflict graph `G`** (Definition 5): the union of the `m` daily conflict
graphs. -/
def overallGraph : SimpleGraph I.Client where
  Adj j j' := j ≠ j' ∧ ∃ i, I.Conflict i j j'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.imp fun _ => conflict_symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[simp] lemma dayGraph_adj {i : I.Day} {j j' : I.Client} :
    (I.dayGraph i).Adj j j' ↔ j ≠ j' ∧ I.Conflict i j j' := Iff.rfl

instance (i : I.Day) : DecidableRel (I.dayGraph i).Adj := fun _ _ => by
  unfold dayGraph; infer_instance

instance : DecidableRel I.overallGraph.Adj := fun _ _ => by
  unfold overallGraph; infer_instance

/-! ## 2. Feasible days are independent sets

> *"a feasible schedule on day `i` corresponds to an independent set in `G_i`."* -/

/-- **A schedule is feasible exactly when each day's set of clients is independent in that
day's conflict graph.** -/
theorem feasible_iff_isIndepSet {σ : I.Schedule} :
    Feasible σ ↔ ∀ i, (I.dayGraph i).IsIndepSet (σ i : Set I.Client) := by
  constructor
  · intro h i j hj j' hj' hne hadj
    exact h i j hj j' hj' hne hadj.2
  · intro h i j hj j' hj' hne hc
    exact h i hj hj' hne ⟨hne, hc⟩

/-! ## 3. Cliques of a day must be spread over distinct days

The counting fact behind Theorem 13's negative half and behind every "these clients block
each other" argument: on any one day a feasible schedule contains at most one member of a
clique, so a clique of size `c` all of whose members need `k` days needs `k · c ≤ m`. -/

/-- On a fixed day, a feasible schedule meets a clique of that day's conflict graph in at
most one client. -/
lemma card_inter_clique_le_one {σ : I.Schedule} (hσ : Feasible σ) (i : I.Day)
    {K : Finset I.Client} (hK : (I.dayGraph i).IsClique (K : Set I.Client)) :
    (σ i ∩ K).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_inter] at ha hb
  by_contra hne
  exact hσ i a ha.1 b hb.1 hne (hK ha.2 hb.2 hne).2

/-- **The blocking bound.** If `K` is a clique in *every* day's conflict graph — the case
of a clique of the overall graph all of whose edges come from every day, and in
particular the case of day-independent instances — then a feasible schedule serves the
members of `K` on pairwise different days, so `∑_{j ∈ K} served σ j ≤ m`. -/
lemma sum_served_le_numDays {σ : I.Schedule} (hσ : Feasible σ) {K : Finset I.Client}
    (hK : ∀ i, (I.dayGraph i).IsClique (K : Set I.Client)) :
    ∑ j ∈ K, served σ j ≤ I.numDays := by
  classical
  have hone : ∀ j, served σ j = ∑ i : I.Day, (if j ∈ σ i then 1 else 0) := fun j => by
    simp [served, Finset.card_filter]
  have hrw : ∑ j ∈ K, served σ j = ∑ i : I.Day, (σ i ∩ K).card := by
    calc ∑ j ∈ K, served σ j
        = ∑ j ∈ K, ∑ i : I.Day, (if j ∈ σ i then 1 else 0) := by simp_rw [hone]
      _ = ∑ i : I.Day, ∑ j ∈ K, (if j ∈ σ i then 1 else 0) := Finset.sum_comm
      _ = ∑ i : I.Day, (σ i ∩ K).card := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [hrw]
  calc ∑ i : I.Day, (σ i ∩ K).card ≤ ∑ _i : I.Day, 1 :=
        Finset.sum_le_sum fun i _ => card_inter_clique_le_one hσ i (hK i)
    _ = I.numDays := by simp [numDays]

end Instance

end Lax117284Proofs.Model
