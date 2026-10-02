import Mathlib.Data.Fintype.EquivFin
import Lax117284Proofs.ConflictGraph

/-!
# Theorem 10: Unit Processing Times, by Bipartite Matching

> **Theorem 10.** The `1 | rep, p_{i,j} = 1 | min_j ∑_i Z_{i,j}` problem is solvable in
> `O(n^{1.5} · m^{2.5})` time.
>
> *Proof.* […] Informally, we create a bipartite graph with a set of *job vertices* on one
> side and the set of *due dates vertices* on the other, to the latter we add a set of
> *rejection vertices*, `m − k` per client. A matching in this graph where all job vertices
> are matched corresponds to a schedule in which every job is either completed at the due
> date to which it was matched or is rejected. The schedule is fair if *all* job vertices
> are matched since the number of rejection vertices of every client is bounded by `m − k`.

Unit processing times collapse the geometry: every job occupies the single slot
`(d_{i,j} − 1, d_{i,j}]`, so *two jobs conflict on a day exactly when they share a due
date* (`conflict_iff_d_eq_of_unitP`). A feasible day is then a set of clients with pairwise
distinct due dates, and the whole problem becomes an assignment problem.

## What "a Matching of Size `nm`" Is, Here

The job side of the paper's bipartite graph has exactly `n · m` vertices — one per pair
`(i, j)` — so a matching saturating it is precisely an *injective* map sending each job
vertex to one of its neighbours, and that is what `HasFullMatching` says. Writing it this
way rather than through `SimpleGraph.Subgraph.IsMatching` keeps the statement at the level
the proof actually uses (injectivity plus the edge condition) and loses nothing: on a
bipartite graph the two formulations are the same object. `Matchable` is the edge relation
of the paper's `G`: job vertex `v_{i,j}` is joined to the due-date vertex `u_{i,d_{i,j}}`
and to the `m − k` rejection vertices `w_{1,j}, …, w_{m−k,j}`.

The `O(n^{1.5} m^{2.5})` running time — Hopcroft–Karp [31] on a graph with `O(nm)` vertices
and `O(m²n)` edges — is a resource claim and lives in `FairRIS.lean`.
-/


namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. With unit processing times, conflict means "same due date" -/

/-- **Unit processing times turn conflict into equality of due dates.** -/
theorem conflict_iff_d_eq_of_unitP (h : I.UnitP) (i : I.Day) (j j' : I.Client) :
    I.Conflict i j j' ↔ I.d i j = I.d i j' := by
  have h1 : 1 ≤ I.d i j := by have := I.p_le_d i j; rw [h i j] at this; omega
  have h2 : 1 ≤ I.d i j' := by have := I.p_le_d i j'; rw [h i j'] at this; omega
  simp only [Conflict, start, h i j, h i j']
  omega

/-! ## 2. The bipartite graph, and matchings saturating the job side -/

variable (I) in
/-- The vertices on the far side of the paper's bipartite graph: a due-date vertex
`u_{i,d}` on the left, a rejection vertex `w_{ℓ,j}` on the right. -/
def MatchTarget : Type := (I.Day × ℕ) ⊕ (ℕ × I.Client)

/-- The edge relation of the paper's graph `G`: the job vertex `v_{i,j}` is adjacent to the
due-date vertex `u_{i,d_{i,j}}` and to each of the `m − k` rejection vertices of client
`j`. -/
def Matchable (k : ℕ) (v : I.Day × I.Client) (t : MatchTarget I) : Prop :=
  t = Sum.inl (v.1, I.d v.1 v.2) ∨ ∃ ℓ < I.numDays - k, t = Sum.inr (ℓ, v.2)

variable (I) in
/-- `G` has a matching saturating the `n · m` job vertices. -/
def HasFullMatching (k : ℕ) : Prop :=
  ∃ f : I.Day × I.Client → MatchTarget I, Function.Injective f ∧ ∀ v, Matchable k v (f v)

/-! ## 3. Correctness -/

/-- The count of days *before* `i` (in an arbitrary but fixed order on days) on which
client `j`'s job is rejected — the index `ℓ` of the rejection vertex the paper matches
`v_{i,j}` to. -/
private def rejRank (e : I.Day ≃ Fin I.numDays) (σ : I.Schedule) (j : I.Client)
    (i : I.Day) : ℕ :=
  (Finset.univ.filter fun i' => (e i').val < (e i).val ∧ j ∉ σ i').card

/-- `rejRank` is strictly increasing along the days on which `j` is rejected, which is what
makes the rejection half of the matching injective. -/
private lemma rejRank_lt {e : I.Day ≃ Fin I.numDays} {σ : I.Schedule} {j : I.Client}
    {a b : I.Day} (hab : (e a).val < (e b).val) (ha : j ∉ σ a) :
    rejRank e σ j a < rejRank e σ j b := by
  classical
  refine Finset.card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨lt_trans hx.1 hab, hx.2⟩
  · have hmem : a ∈ Finset.univ.filter fun i' => (e i').val < (e b).val ∧ j ∉ σ i' := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hab, ha⟩
    have := hsub hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    omega

/-- The matching the forward direction builds: a scheduled job goes to its due-date vertex,
a rejected one to the rejection vertex indexed by how many earlier days rejected it. -/
private def matchMap (e : I.Day ≃ Fin I.numDays) (σ : I.Schedule) :
    I.Day × I.Client → MatchTarget I :=
  fun v => if v.2 ∈ σ v.1 then Sum.inl (v.1, I.d v.1 v.2)
    else Sum.inr (rejRank e σ v.2 v.1, v.2)

private lemma matchMap_apply (e : I.Day ≃ Fin I.numDays) (σ : I.Schedule)
    (i : I.Day) (j : I.Client) :
    matchMap e σ (i, j) =
      if j ∈ σ i then Sum.inl (i, I.d i j) else Sum.inr (rejRank e σ j i, j) := rfl

/-- **Theorem 10's correctness.** With unit processing times and `k ≤ m`, a feasible
`k`-fair schedule exists exactly when the bipartite graph has a matching saturating every
job vertex. -/
theorem hasKFairSchedule_iff_hasFullMatching (h : I.UnitP) {k : ℕ} (hk : k ≤ I.numDays) :
    I.HasKFairSchedule k ↔ I.HasFullMatching k := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    obtain ⟨e⟩ : Nonempty (I.Day ≃ Fin I.numDays) := ⟨Fintype.equivFin I.Day⟩
    refine ⟨matchMap e σ, ?_, ?_⟩
    · -- injectivity
      rintro ⟨i, j⟩ ⟨i', j'⟩ hEq
      rw [matchMap_apply, matchMap_apply] at hEq
      by_cases hj : j ∈ σ i <;> by_cases hj' : j' ∈ σ i'
      · -- both scheduled: same day and same due date, so feasibility forces `j = j'`
        rw [if_pos hj, if_pos hj'] at hEq
        have hp : ((i, I.d i j) : I.Day × ℕ) = (i', I.d i' j') := Sum.inl_injective hEq
        have hi : i = i' := congrArg Prod.fst hp
        have hd : I.d i j = I.d i' j' := congrArg Prod.snd hp
        subst hi
        by_cases hjj : j = j'
        · subst hjj; rfl
        · exact absurd ((conflict_iff_d_eq_of_unitP h i j j').2 hd) (hfeas i j hj j' hj' hjj)
      · rw [if_pos hj, if_neg hj'] at hEq; exact absurd hEq (by simp)
      · rw [if_neg hj, if_pos hj'] at hEq; exact absurd hEq (by simp)
      · -- both rejected: `rejRank` is strictly monotone along the rejected days
        rw [if_neg hj, if_neg hj'] at hEq
        have hp : ((rejRank e σ j i, j) : ℕ × I.Client) = (rejRank e σ j' i', j') :=
          Sum.inr_injective hEq
        have hr : rejRank e σ j i = rejRank e σ j' i' := congrArg Prod.fst hp
        have hjj : j = j' := congrArg Prod.snd hp
        subst hjj
        by_cases hii : i = i'
        · subst hii; rfl
        · exfalso
          have hne : (e i).val ≠ (e i').val := fun hE => hii (e.injective (Fin.ext hE))
          rcases Nat.lt_or_ge (e i).val (e i').val with hlt | hge
          · exact absurd hr (Nat.ne_of_lt (rejRank_lt hlt hj))
          · exact absurd hr.symm (Nat.ne_of_lt (rejRank_lt (by omega) hj'))
    · -- every job vertex is matched to a neighbour
      rintro ⟨i, j⟩
      rw [Matchable, matchMap_apply]
      by_cases hj : j ∈ σ i
      · exact Or.inl (by rw [if_pos hj])
      · refine Or.inr ⟨rejRank e σ j i, ?_, by rw [if_neg hj]⟩
        -- `ℓ + 1` rejected days up to and including `i`, and at most `m − k` in total
        have hins : insert i (Finset.univ.filter fun i' => (e i').val < (e i).val ∧ j ∉ σ i')
            ⊆ Finset.univ.filter fun i' : I.Day => ¬ j ∈ σ i' := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simpa using hj
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact hx.2
        have hnotmem : i ∉ Finset.univ.filter fun i' => (e i').val < (e i).val ∧ j ∉ σ i' := by
          simp
        have hcard := Finset.card_le_card hins
        rw [Finset.card_insert_of_notMem hnotmem] at hcard
        have hsplit : (Finset.univ.filter fun i' => j ∈ σ i').card
            + (Finset.univ.filter fun i' : I.Day => ¬ j ∈ σ i').card = I.numDays := by
          simpa [numDays] using
            Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I.Day))
              (p := fun i' => j ∈ σ i')
        have hf : k ≤ served σ j := hfair j
        simp only [served] at hf
        simp only [rejRank]
        omega
  · rintro ⟨f, hinj, hmatch⟩
    refine ⟨fun i => Finset.univ.filter fun j => f (i, j) = Sum.inl (i, I.d i j), ?_, ?_⟩
    · -- feasibility: two clients of a day with equal due dates would share a target
      intro i j hj j' hj' hne hc
      simp only [Finset.mem_filter] at hj hj'
      have hd : I.d i j = I.d i j' := (conflict_iff_d_eq_of_unitP h i j j').1 hc
      have hpair : ((i, j) : I.Day × I.Client) = (i, j') :=
        hinj (by rw [hj.2, hj'.2, hd])
      exact hne (congrArg Prod.snd hpair)
    · -- fairness: the rejected days of `j` inject into its `m − k` rejection vertices
      intro j
      show k ≤ served _ j
      -- read the rejection index off the target, so the counting happens in `ℕ`
      set g : I.Day → ℕ := fun i => ((f (i, j)).getRight?).elim 0 Prod.fst with hg
      have hgspec : ∀ i, ¬ f (i, j) = Sum.inl (i, I.d i j) →
          g i < I.numDays - k ∧ f (i, j) = Sum.inr (g i, j) := by
        intro i hi
        rcases hmatch (i, j) with hl | ⟨ℓ, hℓ, hfi⟩
        · exact absurd hl hi
        · have hgi : g i = ℓ := by simp [hg, hfi]
          exact ⟨hgi ▸ hℓ, by rw [hgi, hfi]⟩
      have hRcard : (Finset.univ.filter fun i : I.Day =>
          ¬ f (i, j) = Sum.inl (i, I.d i j)).card ≤ I.numDays - k := by
        have hmapsto : ∀ i ∈ Finset.univ.filter fun i : I.Day =>
            ¬ f (i, j) = Sum.inl (i, I.d i j), g i ∈ Finset.range (I.numDays - k) :=
          fun i hi => Finset.mem_range.2 (hgspec i (Finset.mem_filter.1 hi).2).1
        have hinj' : ∀ a ∈ Finset.univ.filter fun i : I.Day =>
            ¬ f (i, j) = Sum.inl (i, I.d i j), ∀ b ∈ Finset.univ.filter fun i : I.Day =>
            ¬ f (i, j) = Sum.inl (i, I.d i j), g a = g b → a = b := by
          intro a ha b hb hab
          have e₁ := (hgspec a (Finset.mem_filter.1 ha).2).2
          have e₂ := (hgspec b (Finset.mem_filter.1 hb).2).2
          have hfe : f (a, j) = f (b, j) := e₁.trans (by rw [hab]; exact e₂.symm)
          exact congrArg Prod.fst (hinj hfe)
        simpa using Finset.card_le_card_of_injOn g hmapsto hinj'
      have hsplit : (Finset.univ.filter fun i => f (i, j) = Sum.inl (i, I.d i j)).card
          + (Finset.univ.filter fun i : I.Day => ¬ f (i, j) = Sum.inl (i, I.d i j)).card
            = I.numDays := by
        simpa [numDays] using
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I.Day))
            (p := fun i => f (i, j) = Sum.inl (i, I.d i j))
      have hserved : served (fun i => Finset.univ.filter fun j' =>
          f (i, j') = Sum.inl (i, I.d i j')) j
          = (Finset.univ.filter fun i => f (i, j) = Sum.inl (i, I.d i j)).card := by
        simp only [served]
        congr 1
        ext i
        simp
      rw [hserved]
      omega

end Instance

end Lax117284Proofs.Model
