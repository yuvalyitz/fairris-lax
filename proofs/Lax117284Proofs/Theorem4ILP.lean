import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lax117284Proofs.Defs

/-!
# Theorem 4, third bullet: fixed-parameter tractability for the number of clients

> **Theorem 4 / Theorem 21.** The `1 | rep | min_j ∑_i Z_{i,j}` problem is solvable in
> `2^{2^{O(n log n)}} · m^{O(1)}` time.
>
> *Proof.* We prove this by providing an ILP formulation of the problem. […] Recall that
> every daily conflict graph `G_i` is an interval graph with `n` vertices. […] For every such
> graph type `G^t` and every subset of vertices `I ⊆ {1,…,n}` that *is an independent set* in
> `G^t` we create an integer variable `x_I^{G^t}`, whose value indicates how many times we
> schedule the set `I` on days of type `G^t`.
>
> `∀ G^t, I : x_I^{G^t} ≥ 0`  (1)
> `∀ G^t : ∑_I x_I^{G^t} = |{G_i | i ∈ {1,…,m} ∧ G_i = G^t}|`  (2)
> `∀ j ∈ {1,…,n} : ∑_{I : j ∈ I} ∑_{G^t} x_I^{G^t} ≥ k`  (3)

Days with the same conflict relation are interchangeable, so a schedule is determined, up to
which day is which, by *how many days of each type run each independent set*. That count is
the ILP, and `hasKFairSchedule_iff_hasILPSolution` is the paper's two-directional argument.

The `⇐` direction is the paper's *"we can therefore define an arbitrary order `π` over the
subsets of `V` and iterate over the days"*, here as a single induction on the set of days
still to be filled (`exists_schedule_of_counts`): give the next day any set whose variable is
still positive, decrement it, and recurse.

## Variables are bounded in `n` alone

That is what makes the formulation an FPT algorithm via Lenstra's theorem: the number of
variables and constraints depends only on `n`. `card_variables_le` gives the crude bound
`2^{n²} · 2^n`, counting day types as arbitrary conflict relations. The paper's sharper
`2^{O(n log n)}` counts *interval* graphs and cites the enumeration results [38, 39]; the two
give the same conclusion — a bound in `n` alone — and only the crude one is needed for that,
so only the crude one is proved here.

Ported from the pre-Lax `FairRIS/Proofs-FairRIS/Theorem21_ILP.lean`, whose `Instance` has the
same fields as `Lax117284Proofs.Model.Instance` verbatim.
-/

namespace Lax117284Proofs.Model

namespace Instance

variable {I : Instance}

/-! ## 1. Day types and independent sets -/

/-- The **type of a day**: its conflict relation. Two days of the same type are
interchangeable. -/
def dayType (I : Instance) (i : I.Day) : I.Client → I.Client → Bool :=
  fun a b => decide (I.Conflict i a b)

/-- `S` is an independent set for the day type `t`. -/
def IndepFor (t : I.Client → I.Client → Bool) (S : Finset I.Client) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → t a b = false

instance (t : I.Client → I.Client → Bool) (S : Finset I.Client) : Decidable (IndepFor t S) := by
  unfold IndepFor; infer_instance

/-- Feasibility, restated: each day runs a set independent for that day's type. -/
lemma feasible_iff_indepFor {σ : I.Schedule} :
    Feasible σ ↔ ∀ i, IndepFor (dayType I i) (σ i) := by
  constructor
  · intro h i a ha b hb hab
    simpa [dayType] using h i a ha b hb hab
  · intro h i a ha b hb hab hc
    have := h i a ha b hb hab
    simp only [dayType, decide_eq_false_iff_not] at this
    exact this hc

/-! ## 2. The integer program -/

variable (I) in
/-- **The ILP of Theorem 4's third bullet.** `x t S` is the paper's `x_S^{G^t}`: the number
of days of type `t` on which exactly the clients of `S` run. Constraint (1) is
`ℕ`-valuedness. -/
def HasILPSolution (k : ℕ) : Prop :=
  ∃ x : (I.Client → I.Client → Bool) → Finset I.Client → ℕ,
    (∀ t S, ¬ IndepFor t S → x t S = 0) ∧
    (∀ t, ∑ S : Finset I.Client, x t S
        = (Finset.univ.filter fun i => dayType I i = t).card) ∧
    (∀ j : I.Client, k ≤ ∑ t : I.Client → I.Client → Bool,
        ∑ S ∈ Finset.univ.filter (fun S : Finset I.Client => j ∈ S), x t S)

/-! ## 3. Counting, twice

Both directions are the same double count: a day is classified by its type and by the set
it runs, and the two classifications are independent. -/

/-- The days of one type are partitioned by the set they run. -/
private lemma sum_card_eq (σ : I.Schedule) (t : I.Client → I.Client → Bool) :
    ∑ S : Finset I.Client, (Finset.univ.filter fun i => dayType I i = t ∧ σ i = S).card
      = (Finset.univ.filter fun i => dayType I i = t).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := σ)
    (t := (Finset.univ : Finset (Finset I.Client))) (fun i _ => Finset.mem_univ _)]
  exact Finset.sum_congr rfl fun S _ => by rw [Finset.filter_filter]

/-- A client's served days are partitioned by day type and by the set run. -/
private lemma served_eq_double_sum (σ : I.Schedule) (j : I.Client) :
    served σ j = ∑ t : I.Client → I.Client → Bool,
      ∑ S ∈ Finset.univ.filter (fun S : Finset I.Client => j ∈ S),
        (Finset.univ.filter fun i => dayType I i = t ∧ σ i = S).card := by
  classical
  rw [served, Finset.card_eq_sum_card_fiberwise (f := fun i => dayType I i)
    (t := (Finset.univ : Finset (I.Client → I.Client → Bool))) (fun i _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := σ)
    (t := Finset.univ.filter fun S : Finset I.Client => j ∈ S)
    (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2⟩)]
  refine Finset.sum_congr rfl fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, hit⟩, his⟩
    exact ⟨hit, his⟩
  · rintro ⟨hit, his⟩
    exact ⟨⟨his ▸ hS, hit⟩, his⟩

/-! ## 4. Filling the days from the counts

The `⇐` direction's construction: fill the days one at a time, decrementing the variable
used. Stated for an arbitrary set `D` of days still to be filled so that the induction has
something to shrink. -/

private lemma exists_schedule_of_counts (I : Instance) :
    ∀ (D : Finset I.Day) (x : (I.Client → I.Client → Bool) → Finset I.Client → ℕ),
      (∀ t, ∑ S : Finset I.Client, x t S = (D.filter fun i => dayType I i = t).card) →
      ∃ σ : I.Schedule, ∀ t S,
        (D.filter fun i => dayType I i = t ∧ σ i = S).card = x t S := by
  classical
  intro D
  induction D using Finset.strongInduction with
  | _ D ih =>
    intro x hcount
    rcases D.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · refine ⟨fun _ => ∅, fun t S => ?_⟩
      have h0 : ∑ S' : Finset I.Client, x t S' = 0 := by simpa using hcount t
      have hz : x t S = 0 :=
        Nat.eq_zero_of_le_zero (h0 ▸ Finset.single_le_sum
          (f := fun S' => x t S') (fun _ _ => Nat.zero_le _) (Finset.mem_univ S))
      simp [hz]
    · -- the type of the day about to be filled has a positive variable
      have hpos : ∑ S : Finset I.Client, x (dayType I i₀) S ≠ 0 := by
        rw [hcount (dayType I i₀)]
        refine Finset.card_ne_zero_of_mem (a := i₀) ?_
        simp [hi₀]
      obtain ⟨S₀, -, hS₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
      -- decrement it and recurse on the remaining days
      set x' : (I.Client → I.Client → Bool) → Finset I.Client → ℕ :=
        fun t S => if t = dayType I i₀ ∧ S = S₀ then x t S - 1 else x t S with hx'def
      have hx'_at : x' (dayType I i₀) S₀ = x (dayType I i₀) S₀ - 1 := by
        simp [hx'def]
      have hx'_ne : ∀ t S, ¬ (t = dayType I i₀ ∧ S = S₀) → x' t S = x t S := by
        intro t S h; simp only [hx'def]; rw [if_neg h]
      have hsum' : ∀ t, ∑ S : Finset I.Client, x' t S
          = ((D.erase i₀).filter fun i => dayType I i = t).card := by
        intro t
        by_cases ht : t = dayType I i₀
        · have hstep : ∑ S : Finset I.Client, x' t S = (∑ S : Finset I.Client, x t S) - 1 := by
            have e1 : ∑ S : Finset I.Client, x' t S
                = (∑ S ∈ Finset.univ.erase S₀, x' t S) + x' t S₀ :=
              (Finset.sum_erase_add Finset.univ (fun S => x' t S) (Finset.mem_univ S₀)).symm
            have e2 : ∑ S : Finset I.Client, x t S
                = (∑ S ∈ Finset.univ.erase S₀, x t S) + x t S₀ :=
              (Finset.sum_erase_add Finset.univ (fun S => x t S) (Finset.mem_univ S₀)).symm
            have e3 : ∑ S ∈ Finset.univ.erase S₀, x' t S = ∑ S ∈ Finset.univ.erase S₀, x t S :=
              Finset.sum_congr rfl fun S hS =>
                hx'_ne t S fun hc => Finset.ne_of_mem_erase hS hc.2
            have e4 : x' t S₀ = x t S₀ - 1 := by rw [ht]; exact hx'_at
            have h1 : x t S₀ ≠ 0 := by rw [ht]; exact hS₀
            omega
          have hins : (D.filter fun i => dayType I i = t) =
              insert i₀ ((D.erase i₀).filter fun i => dayType I i = t) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hiD, hit⟩
              by_cases h : i = i₀
              · exact Or.inl h
              · exact Or.inr ⟨⟨h, hiD⟩, hit⟩
            · rintro (rfl | ⟨⟨-, hiD⟩, hit⟩)
              · exact ⟨hi₀, ht.symm⟩
              · exact ⟨hiD, hit⟩
          rw [hstep, hcount t, hins, Finset.card_insert_of_notMem (by simp)]
          omega
        · rw [Finset.sum_congr rfl (fun S _ => hx'_ne t S (fun hc => ht hc.1)), hcount t]
          congr 1
          ext i
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hiD, hit⟩
            exact ⟨⟨fun h => ht (by rw [← hit, h]), hiD⟩, hit⟩
          · rintro ⟨⟨-, hiD⟩, hit⟩
            exact ⟨hiD, hit⟩
      obtain ⟨σ', hσ'⟩ := ih (D.erase i₀) (Finset.erase_ssubset hi₀) x' hsum'
      refine ⟨Function.update σ' i₀ S₀, fun t S => ?_⟩
      by_cases hcase : t = dayType I i₀ ∧ S = S₀
      · obtain ⟨ht, hS⟩ := hcase
        have hsplit : (D.filter fun i => dayType I i = t ∧ Function.update σ' i₀ S₀ i = S)
            = insert i₀ ((D.erase i₀).filter fun i => dayType I i = t ∧ σ' i = S) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨hiD, hit, his⟩
            by_cases h : i = i₀
            · exact Or.inl h
            · rw [Function.update_of_ne h] at his
              exact Or.inr ⟨⟨h, hiD⟩, hit, his⟩
          · rintro (rfl | ⟨⟨hne, hiD⟩, hit, his⟩)
            · exact ⟨hi₀, ht.symm, by rw [Function.update_self]; exact hS.symm⟩
            · exact ⟨hiD, hit, by rwa [Function.update_of_ne hne]⟩
        rw [hsplit, Finset.card_insert_of_notMem (by simp), hσ']
        have e4 : x' t S = x t S - 1 := by
          simp only [hx'def]; rw [if_pos ⟨ht, hS⟩]
        have h1 : x t S ≠ 0 := by rw [ht, hS]; exact hS₀
        omega
      · have hfil : (D.filter fun i => dayType I i = t ∧ Function.update σ' i₀ S₀ i = S)
            = ((D.erase i₀).filter fun i => dayType I i = t ∧ σ' i = S) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_erase]
          constructor
          · rintro ⟨hiD, hit, his⟩
            by_cases h : i = i₀
            · subst h
              rw [Function.update_self] at his
              exact absurd ⟨hit.symm, his.symm⟩ hcase
            · rw [Function.update_of_ne h] at his
              exact ⟨⟨h, hiD⟩, hit, his⟩
          · rintro ⟨⟨h1, hiD⟩, hit, his⟩
            exact ⟨hiD, hit, by rwa [Function.update_of_ne h1]⟩
        rw [hfil, hσ', hx'_ne t S hcase]

/-! ## 5. Theorem 4's third bullet, correctness -/

/-- **Correctness.** A feasible `k`-fair schedule exists exactly when the integer program has
a solution. -/
theorem hasKFairSchedule_iff_hasILPSolution (k : ℕ) :
    I.HasKFairSchedule k ↔ I.HasILPSolution k := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    refine ⟨fun t S => (Finset.univ.filter fun i => dayType I i = t ∧ σ i = S).card,
      ?_, sum_card_eq σ, fun j => ?_⟩
    · -- a non-independent set is never used
      intro t S hS
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      obtain ⟨-, hit, his⟩ := Finset.mem_filter.1 hi
      exact hS (hit ▸ his ▸ feasible_iff_indepFor.1 hfeas i)
    · rw [← served_eq_double_sum]
      exact hfair j
  · rintro ⟨x, hindep, hcount, hfair⟩
    obtain ⟨σ, hσ⟩ := exists_schedule_of_counts I Finset.univ x (by simpa using hcount)
    refine ⟨σ, ?_, fun j => ?_⟩
    · -- every day runs a set whose variable is positive, hence an independent set
      refine feasible_iff_indepFor.2 fun i => ?_
      by_contra hbad
      have hzero := hindep (dayType I i) (σ i) hbad
      have hmem : i ∈ Finset.univ.filter fun i' =>
          dayType I i' = dayType I i ∧ σ i' = σ i := by simp
      have hcard := hσ (dayType I i) (σ i)
      rw [hzero] at hcard
      exact absurd hcard (Finset.card_ne_zero_of_mem hmem)
    · rw [served_eq_double_sum]
      refine le_trans (hfair j) (le_of_eq (Finset.sum_congr rfl fun t _ =>
        Finset.sum_congr rfl fun S _ => (hσ t S).symm))

end Instance

end Lax117284Proofs.Model
