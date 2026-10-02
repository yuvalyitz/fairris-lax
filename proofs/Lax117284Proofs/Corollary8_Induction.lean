import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Lax117284Proofs.Defs

/-!
# Corollary 8: from `(m, k) = (3, 1)` to Every `0 < k < m − 1`

> We next use the NP-hardness proof for the case of `(m, k) = (3, 1)` of Theorem 7 as a base
> case to inductively show NP-hardness for every `(m, k) ∈ ℕ²` where `0 < k < m − 1` and
> `m ≥ 3`. Observe that an NP-hardness result for any pair `(m, k)` implies an NP-hardness
> for the pair `(m + 1, k + 1)`, as we can add a single day with no conflicts to any instance
> `I` […]: Clearly `I` is `k`-fair if and only if it is `(k + 1)`-fair. Moreover, observe
> that NP-hardness for any pair `(m, 1)` implies NP-hardness for `(m + 1, 1)`, as can be seen
> by adding an additional client and an additional day to an instance `I` such that the new
> client conflicts with every other client on each of first `m` days, and on the new day the
> jobs of all clients are mutually conflicting.
>
> **Corollary 8.** The `1 | rep, p_{i,j} = p_j | min_j ∑_i Z_{i,j}` problem is NP-hard when
> `0 < k < m − 1` and `m ≥ 3`.

Two instance-level constructions, each with its own equivalence:

* `addFreeDay` — one extra day on which nothing conflicts, so every client picks up exactly
  one more served day. `hasKFairSchedule_addFreeDay` : `k`-fair `↔` `(k+1)`-fair.
* `addBlockingDay` — one extra client that blocks every old day, and one extra day on which
  everything blocks everything. `hasOneFairSchedule_addBlockingDay` : `1`-fair `↔` `1`-fair.

Both are stated for an arbitrary vector `q` of processing times on the new day, precisely so
that Corollary 8's *"observe that this can be also done with day-independent processing
times"* is a corollary and not a second construction: taking `q j = p_{i₀,j}` keeps
`DayIndepP`, and that is `addFreeDay_dayIndepP` / `addBlockingDay_dayIndepP`. With the
general `q` the same two lemmas serve Theorem 1.

## The Conflict-Free Day

The paper does not say how to lay out a conflict-free day; here client `j` (in an arbitrary
enumeration `idx`) gets the interval ending at `(idx j + 1) · Q`, where `Q` bounds every
`q j`. Consecutive clients are then separated by at least `Q ≥ q`, so no two intervals meet.
-/


namespace Lax117284Proofs.Model

open Instance

/-! ## 1. A conflict-free extra day -/

namespace AddFreeDay

variable (I : Instance) (q : I.Client → ℕ)

-- An injective numbering of the clients, used only to spread the new day's jobs out. Any
-- one will do; the construction of the concepts takes the numbering the clients already
-- carry.
variable (idx : I.Client → ℕ)

/-- A bound on all the new day's processing times. -/
def Q : ℕ := Finset.univ.sup q

lemma le_Q (j : I.Client) : q j ≤ Q I q := Finset.le_sup (Finset.mem_univ j)

variable (hq : ∀ j, 0 < q j)

/-- **The instance with one conflict-free day added.**

Marked `@[reducible]` so that `(inst I q idx hq).Client` and `.Day` unfold during unification and
instance search: without it every `Finset (inst I q idx hq).Client` needs its `DecidableEq`
re-derived by hand, and `rw` refuses to see through the projection. -/
@[reducible] noncomputable def inst : Instance where
  Client := I.Client
  Day := I.Day ⊕ Unit
  clientFintype := I.clientFintype
  clientDecEq := I.clientDecEq
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p i j := i.elim (fun i' => I.p i' j) fun _ => q j
  d i j := i.elim (fun i' => I.d i' j) fun _ => (idx j + 1) * Q I q
  p_pos i j := by cases i with
    | inl i' => exact I.p_pos i' j
    | inr _ => exact hq j
  p_le_d i j := by
    cases i with
    | inl i' => exact I.p_le_d i' j
    | inr _ =>
      show q j ≤ (idx j + 1) * Q I q
      have h1 : q j ≤ Q I q := le_Q I q j
      have h2 : 1 * Q I q ≤ (idx j + 1) * Q I q :=
        Nat.mul_le_mul (by omega) (le_refl _)
      omega

variable {I q}

/-- On the extra day, distinct clients never conflict: their intervals sit in disjoint
blocks of length `Q`. -/
lemma not_conflict_new (hinj : Function.Injective idx) {j j' : I.Client} (hne : j ≠ j') :
    ¬ (inst I q idx hq).Conflict (Sum.inr ()) j j' := by
  have hQ : ∀ x, q x ≤ Q I q := le_Q I q
  have hidx : idx j ≠ idx j' := fun h => hne (hinj h)
  have step : ∀ a b : ℕ, a < b → (a + 1) * Q I q + Q I q ≤ (b + 1) * Q I q := by
    intro a b hab
    have hmul : (a + 1 + 1) * Q I q ≤ (b + 1) * Q I q :=
      Nat.mul_le_mul (by omega) (le_refl _)
    have heq : (a + 1) * Q I q + Q I q = (a + 1 + 1) * Q I q := by ring
    omega
  rcases Nat.lt_or_ge (idx j) (idx j') with h | h
  · refine not_conflict_of_le ?_
    show (idx j + 1) * Q I q ≤ (idx j' + 1) * Q I q - q j'
    have h1 := step _ _ h
    have := hQ j'
    omega
  · have hlt : idx j' < idx j := by omega
    refine not_conflict_of_le' ?_
    show (idx j' + 1) * Q I q ≤ (idx j + 1) * Q I q - q j
    have h1 := step _ _ hlt
    have := hQ j
    omega

/-- A schedule of `I`, extended to the new day by running everything (the new day has no
conflicts, so that is feasible). -/
noncomputable def extend (σ : I.Schedule) : (inst I q idx hq).Schedule := fun i =>
  match i with
  | Sum.inl i' => σ i'
  | Sum.inr _ => Finset.univ

/-- A schedule of the extended instance, restricted back to the old days. -/
noncomputable def restrict (τ : (inst I q idx hq).Schedule) : I.Schedule := fun i => τ (Sum.inl i)

lemma served_extend (σ : I.Schedule) (x : (inst I q idx hq).Client) :
    served (extend idx hq σ) x = served (I := I) σ x + 1 := by
  have h1 : served (extend idx hq σ) x
      = ∑ i : I.Day ⊕ Unit, (if x ∈ extend idx hq σ i then 1 else 0) := served_eq_sum _ _
  have h2 : (∑ i : I.Day ⊕ Unit, (if x ∈ extend idx hq σ i then 1 else 0))
      = (∑ i : I.Day, (if x ∈ extend idx hq σ (Sum.inl i) then 1 else 0))
        + ∑ u : Unit, (if x ∈ extend idx hq σ (Sum.inr u) then 1 else 0) :=
    Fintype.sum_sum_type _
  have h3 : (∑ i : I.Day, (if x ∈ extend idx hq σ (Sum.inl i) then 1 else 0))
      = served (I := I) σ x := (served_eq_sum σ x).symm
  have h4 : (∑ u : Unit, (if x ∈ extend idx hq σ (Sum.inr u) then 1 else 0)) = 1 := by
    simp [extend]
  omega

lemma served_restrict_le (τ : (inst I q idx hq).Schedule) (x : (inst I q idx hq).Client) :
    served τ x ≤ served (restrict idx hq τ) x + 1 := by
  have h1 : served τ x = ∑ i : I.Day ⊕ Unit, (if x ∈ τ i then 1 else 0) := served_eq_sum _ _
  have h2 : (∑ i : I.Day ⊕ Unit, (if x ∈ τ i then 1 else 0))
      = (∑ i : I.Day, (if x ∈ τ (Sum.inl i) then 1 else 0))
        + ∑ u : Unit, (if x ∈ τ (Sum.inr u) then 1 else 0) :=
    Fintype.sum_sum_type _
  have h3 : (∑ i : I.Day, (if x ∈ τ (Sum.inl i) then 1 else 0))
      = served (restrict idx hq τ) x := (served_eq_sum (restrict idx hq τ) x).symm
  have h4 : (∑ u : Unit, (if x ∈ τ (Sum.inr u) then 1 else 0)) ≤ 1 := by
    have : (if x ∈ τ (Sum.inr ()) then 1 else 0) ≤ 1 := by split <;> omega
    simpa using this
  omega

/-- **The first reduction of Corollary 8.** Adding one conflict-free day raises the
attainable fairness by exactly one. -/
theorem hasKFairSchedule_addFreeDay (hinj : Function.Injective idx) (k : ℕ) :
    I.HasKFairSchedule k ↔ (inst I q idx hq).HasKFairSchedule (k + 1) := by
  classical
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    refine ⟨extend idx hq σ, ?_, fun j => ?_⟩
    · rintro (i | u) x hx y hy hne
      · exact hfeas i x hx y hy hne
      · exact not_conflict_new idx hq hinj hne
    · show k + 1 ≤ _
      rw [served_extend]
      have := hfair j
      simp only at this
      omega
  · rintro ⟨τ, hfeas, hfair⟩
    refine ⟨restrict idx hq τ, fun i x hx y hy hne => hfeas (Sum.inl i) x hx y hy hne,
      fun j => ?_⟩
    have hj := hfair j
    simp only at hj
    have hle := served_restrict_le idx hq τ j
    show k ≤ _
    omega

end AddFreeDay

/-! ## 2. A blocking client and a blocking day -/

namespace AddBlockingDay

variable (I : Instance) (q : I.Client → ℕ)

/-- A time later than every due date of `I`: the new client's job fills `[0, P)` on each old
day, so it conflicts with everything there. -/
def P : ℕ := (Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j) + 1

lemma d_lt_P (i : I.Day) (j : I.Client) : I.d i j < P I := by
  have h1 : I.d i j ≤ Finset.univ.sup fun j' => I.d i j' := Finset.le_sup (Finset.mem_univ j)
  have h2 : (Finset.univ.sup fun j' => I.d i j') ≤
      Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
    Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ i)
  simp only [P]
  omega

lemma P_pos : 0 < P I := by simp [P]

variable (hq : ∀ j, 0 < q j) (hqP : ∀ j, q j ≤ P I)

/-- **The instance with a blocking client and a blocking day added.** `@[reducible]` for the
same reason as `AddFreeDay.inst`. On each old day the
new client `inr ()` occupies `[0, P)` and so conflicts with every old job; on the new day
every job ends at `P`, so all jobs are mutually conflicting and at most one runs. -/
@[reducible] def inst : Instance where
  Client := I.Client ⊕ Unit
  Day := I.Day ⊕ Unit
  clientFintype := inferInstance
  clientDecEq := inferInstance
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p i j := i.elim (fun i' => j.elim (fun j' => I.p i' j') fun _ => P I)
    fun _ => j.elim (fun j' => q j') fun _ => P I
  d i j := i.elim (fun i' => j.elim (fun j' => I.d i' j') fun _ => P I) fun _ => P I
  p_pos i j := by
    cases i with
    | inl i' => cases j with
      | inl j' => exact I.p_pos i' j'
      | inr _ => exact P_pos I
    | inr _ => cases j with
      | inl j' => exact hq j'
      | inr _ => exact P_pos I
  p_le_d i j := by
    cases i with
    | inl i' => cases j with
      | inl j' => exact I.p_le_d i' j'
      | inr _ => exact le_rfl
    | inr _ => cases j with
      | inl j' => exact hqP j'
      | inr _ => exact le_rfl

variable {I q}

/-- The new client blocks every old client on every old day. -/
lemma conflict_new_client (i : I.Day) (j : I.Client) :
    (inst I q hq hqP).Conflict (Sum.inl i) (Sum.inr ()) (Sum.inl j) := by
  have h1 : I.d i j < P I := d_lt_P I i j
  have h2 := I.p_pos i j
  have h3 := I.p_le_d i j
  refine ⟨?_, ?_⟩ <;> simp only [Instance.start, Sum.elim_inl, Sum.elim_inr] <;> omega

/-- On the new day every pair of jobs conflicts: all of them end at `P`. -/
lemma conflict_new_day (j j' : (inst I q hq hqP).Client) :
    (inst I q hq hqP).Conflict (Sum.inr ()) j j' := by
  have hd : ∀ x : (inst I q hq hqP).Client,
      (inst I q hq hqP).d (Sum.inr ()) x = P I := by rintro (x | u) <;> rfl
  have h1 := start_lt_d (I := inst I q hq hqP) (Sum.inr ()) j
  have h2 := start_lt_d (I := inst I q hq hqP) (Sum.inr ()) j'
  rw [hd j] at h1
  rw [hd j'] at h2
  exact ⟨by rw [hd j']; exact h1, by rw [hd j]; exact h2⟩

/-- On the new day a feasible schedule runs at most one job. -/
lemma card_new_day_le_one {τ : (inst I q hq hqP).Schedule}
    (hfeas : Feasible τ) : (τ (Sum.inr ())).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  exact hfeas (Sum.inr ()) a ha b hb hne (conflict_new_day hq hqP a b)

/-- A schedule of `I`, lifted to the extended instance: the old clients keep their days,
and the new client takes the new day (where it must run alone anyway). -/
noncomputable def lift (σ : I.Schedule) : (inst I q hq hqP).Schedule := fun i =>
  match i with
  | Sum.inl i' => (σ i').image Sum.inl
  | Sum.inr _ => {Sum.inr ()}

@[simp] lemma lift_inl (σ : I.Schedule) (i : I.Day) :
    lift hq hqP σ (Sum.inl i) = (σ i).image Sum.inl := Eq.trans rfl rfl

@[simp] lemma lift_inr (σ : I.Schedule) (u : Unit) :
    lift hq hqP σ (Sum.inr u) = {Sum.inr ()} := Eq.trans rfl rfl

lemma served_lift_old (σ : I.Schedule) (x : I.Client) :
    served (lift hq hqP σ) (Sum.inl x) = served (I := I) σ x := by
  have h1 : served (lift hq hqP σ) (Sum.inl x)
      = ∑ i : I.Day ⊕ Unit, (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ i then 1 else 0) :=
    served_eq_sum _ _
  have h2 : (∑ i : I.Day ⊕ Unit,
        (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ i then 1 else 0))
      = (∑ i : I.Day, (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inl i)
            then 1 else 0))
        + ∑ u : Unit, (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inr u)
            then 1 else 0) :=
    Fintype.sum_sum_type _
  have h3 : (∑ i : I.Day, (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inl i)
      then 1 else 0)) = served (I := I) σ x := by
    rw [served_eq_sum (I := I)]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ σ i <;> simp [hx]
  have h4 : (∑ u : Unit, (if (Sum.inl x : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inr u)
      then 1 else 0)) = 0 := by simp
  omega

lemma served_lift_new (σ : I.Schedule) :
    served (lift hq hqP σ) (Sum.inr ()) = 1 := by
  have h1 : served (lift hq hqP σ) (Sum.inr ())
      = ∑ i : I.Day ⊕ Unit,
          (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ i then 1 else 0) :=
    served_eq_sum _ _
  have h2 : (∑ i : I.Day ⊕ Unit,
        (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ i then 1 else 0))
      = (∑ i : I.Day, (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inl i)
            then 1 else 0))
        + ∑ u : Unit, (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inr u)
            then 1 else 0) :=
    Fintype.sum_sum_type _
  have h3 : (∑ i : I.Day, (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inl i)
      then 1 else 0)) = 0 := by simp
  have h4 : (∑ u : Unit, (if (Sum.inr () : I.Client ⊕ Unit) ∈ lift hq hqP σ (Sum.inr u)
      then 1 else 0)) = 1 := by simp
  omega

/-- The old-client part of a schedule of the extended instance, on the old days. -/
def oldPart (τ : (inst I q hq hqP).Schedule) : I.Schedule := fun i =>
  Finset.univ.filter fun j => (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inl i)

@[simp] lemma mem_oldPart {τ : (inst I q hq hqP).Schedule} {i : I.Day} {j : I.Client} :
    j ∈ oldPart hq hqP τ i ↔ (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inl i) := by
  simp [oldPart]

/-- The swap of the paper's *"we can assume by a swapping argument"*: the one old client
that the new day was carrying is moved onto the day `i₁` that the new client vacates. -/
def repair (τ : (inst I q hq hqP).Schedule) (i₁ : I.Day) : I.Schedule := fun i =>
  if i = i₁ then Finset.univ.filter (fun j : I.Client =>
      (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inr ())) else oldPart hq hqP τ i

@[simp] lemma mem_repair_self {τ : (inst I q hq hqP).Schedule} {i₁ : I.Day} {j : I.Client} :
    j ∈ repair hq hqP τ i₁ i₁ ↔ (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inr ()) := by
  simp [repair]

@[simp] lemma mem_repair_of_ne {τ : (inst I q hq hqP).Schedule} {i i₁ : I.Day}
    (h : i ≠ i₁) {j : I.Client} :
    j ∈ repair hq hqP τ i₁ i ↔ (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inl i) := by
  simp [repair, h]

/-- **The second reduction of Corollary 8.** Adding a blocking client together with a
blocking day preserves `1`-fairness in both directions. -/
theorem hasOneFairSchedule_addBlockingDay :
    I.HasKFairSchedule 1 ↔ (inst I q hq hqP).HasKFairSchedule 1 := by
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    refine ⟨lift hq hqP σ, ?_, ?_⟩
    · rintro (i | u) x hx y hy hne
      · simp only [lift_inl, Finset.mem_image] at hx hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact hfeas i a ha b hb fun h => hne (by rw [h])
      · simp only [lift_inr, Finset.mem_singleton] at hx hy
        exact absurd (hx.trans hy.symm) hne
    · rintro (j | u)
      · show 1 ≤ _
        rw [served_lift_old]
        have := hfair j
        simp only at this
        omega
      · show 1 ≤ _
        cases u
        rw [served_lift_new]
  · rintro ⟨τ, hfeas, hfair⟩
    have holdfeas : Feasible (oldPart hq hqP τ) := by
      intro i x hx y hy hne
      simp only [mem_oldPart] at hx hy
      exact hfeas (Sum.inl i) _ hx _ hy (fun h => hne (Sum.inl_injective h))
    have hcard := card_new_day_le_one hq hqP hfeas
    -- the new client is served somewhere
    obtain ⟨i₁, hi₁⟩ : ∃ i, (Sum.inr () : I.Client ⊕ Unit) ∈ τ i := by
      have h : 1 ≤ served τ (Sum.inr ()) := hfair (Sum.inr ())
      simp only [served] at h
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one h)
      exact ⟨i, (Finset.mem_filter.1 hi).2⟩
    -- an old client not served on any old day must live on the new day
    have hnew : ∀ j : I.Client, (∀ i, (Sum.inl j : I.Client ⊕ Unit) ∉ τ (Sum.inl i)) →
        (Sum.inl j : I.Client ⊕ Unit) ∈ τ (Sum.inr ()) := by
      intro j hj
      have h : 1 ≤ served τ (Sum.inl j) := hfair (Sum.inl j)
      simp only [served] at h
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one h)
      have hmem := (Finset.mem_filter.1 hi).2
      cases i with
      | inl i' => exact absurd hmem (hj i')
      | inr u => cases u; exact hmem
    cases i₁ with
    | inr u =>
      -- the new client uses the new day, so every old client is served on an old day
      cases u
      refine ⟨oldPart hq hqP τ, holdfeas, fun j => ?_⟩
      show 1 ≤ _
      by_cases hj : ∀ i, (Sum.inl j : I.Client ⊕ Unit) ∉ τ (Sum.inl i)
      · exact absurd (Finset.card_le_one.1 hcard _ (hnew j hj) _ hi₁) (by simp)
      · push Not at hj
        obtain ⟨i, hi⟩ := hj
        simp only [served]
        exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i,
          (mem_oldPart hq hqP).2 hi⟩⟩
    | inl i₁' =>
      -- the new client uses an old day, which it therefore occupies alone
      have hempty : ∀ x : I.Client, x ∉ oldPart hq hqP τ i₁' := by
        intro x hx
        simp only [mem_oldPart] at hx
        exact hfeas (Sum.inl i₁') _ hi₁ _ hx (by simp) (conflict_new_client hq hqP i₁' x)
      refine ⟨repair hq hqP τ i₁', ?_, fun j => ?_⟩
      · intro i x hx y hy hne
        by_cases hi : i = i₁'
        · subst hi
          rw [mem_repair_self] at hx hy
          exact absurd (Finset.card_le_one.1 hcard _ hx _ hy)
            (fun h => hne (Sum.inl_injective h))
        · rw [mem_repair_of_ne hq hqP hi] at hx hy
          exact holdfeas i x ((mem_oldPart hq hqP).2 hx) y ((mem_oldPart hq hqP).2 hy) hne
      · show 1 ≤ _
        simp only [served]
        by_cases hj : ∀ i, (Sum.inl j : I.Client ⊕ Unit) ∉ τ (Sum.inl i)
        · -- `j` lives on the new day; move it to the day the new client vacated
          refine Finset.card_pos.2 ⟨i₁', Finset.mem_filter.2 ⟨Finset.mem_univ i₁', ?_⟩⟩
          exact (mem_repair_self hq hqP).2 (hnew j hj)
        · push Not at hj
          obtain ⟨i, hi⟩ := hj
          have hii : i ≠ i₁' := by
            rintro rfl
            exact hempty j ((mem_oldPart hq hqP).2 hi)
          refine Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, ?_⟩⟩
          exact (mem_repair_of_ne hq hqP hii).2 hi

end AddBlockingDay

end Lax117284Proofs.Model
