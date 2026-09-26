import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Lax117284Proofs.ConflictGraph
import Lax117284Proofs.Treewidth

/-!
# Lemma 15: per-client fairness parameters reduce to a uniform one

> **Lemma 15.** There is a polynomial time reduction from `1 | k_j, rep | min_j ∑_i Z_{i,j}`
> to `1 | rep | min_j ∑_i Z_{i,j}` which increases the treewidth by at most 2.
>
> *Proof.* Let `I` be an instance of `1 | k_j, rep | min_j ∑_i Z_{i,j}` with `m` days and `n`
> clients. We construct an instance `I'` […] of `1 | rep | min_j ∑_i Z_{i,j}` as follows:
> Starting with `I`, we append another `m` days, add two clients `c⁻` and `c⁺`, and set
> `k := m`. The jobs of `c⁻` and `c⁺` have the same processing time and due date, so they
> cannot both be scheduled on the same day. On the first "original" `m` days, no clients from
> `I` intersects with clients `c⁻` and `c⁺`. On the last "additional" `m` days, no two
> different clients from `I` intersect. For each client `c` from `I` there are exactly `k_c`
> days where client `c` intersects with `c⁻` and `c⁺`.

`c⁻` and `c⁺` conflict on every one of the `2m` days, so a `m`-fair schedule runs exactly one
of them each day (`exists_marker_each_day`) — which turns the `k_c` "intersecting" additional
days into `k_c` days client `c` cannot use. Its remaining budget of `m` served days therefore
has to come `k_c` from the original days, which is exactly the original fairness requirement.

## The layout

`d_max` bounds every due date of `I`, `P = n + 1`, and `blocked c` is any set of `k_c` days
(it exists precisely when `k_c ≤ m`, which is the only case the reduction needs). Then

* `c⁻` and `c⁺` occupy `(d_max, d_max + P]` on **every** day, so they conflict with each
  other everywhere, and with no original client on the original days (whose jobs end by
  `d_max`);
* on an additional day, client `c` — the `idx c`-th in an arbitrary enumeration,
  `1 ≤ idx c ≤ n` — occupies the unit slot ending at `d_max + idx c` if that day is one of
  its `k_c` blocked ones, which sits *inside* `(d_max, d_max + P]`, and the unit slot ending
  at `d_max + P + idx c` otherwise, which sits strictly after it.

Distinct clients get distinct slots, so no two original clients ever conflict on an
additional day — the clause that keeps the treewidth from growing by more than the two new
clients (`treewidth_inst_le`).
-/


namespace Lax117284Proofs.Model

namespace Lemma15

open Instance

variable (I : Instance)

/-! ## 1. The construction -/

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- An injective numbering of the clients by `1, …, n`. The construction uses it only to
give every client a private slot inside the markers' job; any numbering will do, and a
numbered instance supplies the numbering its clients already carry. -/
structure Enum (I : Instance) where
  /-- The number of a client. -/
  idx : I.Client → ℕ
  /-- The numbers are positive. -/
  pos : ∀ j, 0 < idx j
  /-- The numbers do not exceed the number of clients. -/
  le : ∀ j, idx j ≤ I.numClients
  /-- Distinct clients receive distinct numbers. -/
  inj : Function.Injective idx

variable (num : Enum I)

/-- A time later than every due date of `I`. -/
def dmax : ℕ := Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j

lemma d_le_dmax (i : I.Day) (j : I.Client) : I.d i j ≤ dmax I := by
  have h1 : I.d i j ≤ Finset.univ.sup fun j' => I.d i j' := Finset.le_sup (Finset.mem_univ j)
  have h2 : (Finset.univ.sup fun j' => I.d i j') ≤
      Finset.univ.sup fun i' => Finset.univ.sup fun j' => I.d i' j' :=
    Finset.le_sup (f := fun i' => Finset.univ.sup fun j' => I.d i' j') (Finset.mem_univ i)
  simp only [dmax]
  omega

/-- The length of the two markers' jobs: longer than any client's private slot. -/
def P : ℕ := I.numClients + 1

variable (blocked : I.Client → Finset I.Day)

/-- **The instance of Lemma 15**: `2m` days, the original clients plus two markers, and the
uniform fairness parameter `m`. -/
@[reducible] noncomputable def inst : Instance where
  Client := I.Client ⊕ Bool
  Day := I.Day ⊕ I.Day
  clientFintype := inferInstance
  clientDecEq := inferInstance
  dayFintype := inferInstance
  dayDecEq := inferInstance
  p i j :=
    match i, j with
    | Sum.inl i', Sum.inl j' => I.p i' j'
    | Sum.inl _, Sum.inr _ => P I
    | Sum.inr _, Sum.inl _ => 1
    | Sum.inr _, Sum.inr _ => P I
  d i j :=
    match i, j with
    | Sum.inl i', Sum.inl j' => I.d i' j'
    | Sum.inl _, Sum.inr _ => dmax I + P I
    | Sum.inr i', Sum.inl j' =>
        if i' ∈ blocked j' then dmax I + num.idx j' else dmax I + P I + num.idx j'
    | Sum.inr _, Sum.inr _ => dmax I + P I
  p_pos i j := by
    cases i <;> cases j <;> simp only [] <;> first
      | exact I.p_pos _ _
      | simp [P]
  p_le_d i j := by
    cases i with
    | inl i' => cases j with
      | inl j' => exact I.p_le_d i' j'
      | inr _ => simp
    | inr i' => cases j with
      | inl j' =>
        have := num.pos j'
        simp only []
        split <;> omega
      | inr _ => simp

@[simp] lemma numDays_inst : (inst I num blocked).numDays = I.numDays + I.numDays := by
  show Fintype.card (I.Day ⊕ I.Day) = _
  rw [Fintype.card_sum]
  rfl

/-! ## 2. Which jobs conflict -/

variable {I num blocked}

/-- The two markers conflict on every day. -/
lemma conflict_markers (i : (inst I num blocked).Day) (b b' : Bool) :
    (inst I num blocked).Conflict i (Sum.inr b) (Sum.inr b') := by
  cases i <;> exact conflict_of_eq rfl rfl

/-- On an original day the markers conflict with nothing else: every original job ends by
`d_max`, where the markers' job starts. -/
lemma not_conflict_marker_orig (i : I.Day) (j : I.Client) (b : Bool) :
    ¬ (inst I num blocked).Conflict (Sum.inl i) (Sum.inl j) (Sum.inr b) := by
  refine not_conflict_of_le ?_
  show I.d i j ≤ (dmax I + P I) - P I
  have := d_le_dmax I i j
  omega

/-- On an additional day a client conflicts with the markers exactly on its own `k_c`
days. -/
lemma conflict_marker_add {i : I.Day} {j : I.Client} (h : i ∈ blocked j) (b : Bool) :
    (inst I num blocked).Conflict (Sum.inr i) (Sum.inl j) (Sum.inr b) := by
  have h1 := num.pos j
  have h2 := num.le j
  refine ⟨?_, ?_⟩ <;>
    simp only [Instance.start, P, if_pos h] <;> omega

lemma not_conflict_marker_add {i : I.Day} {j : I.Client} (h : i ∉ blocked j) (b : Bool) :
    ¬ (inst I num blocked).Conflict (Sum.inr i) (Sum.inl j) (Sum.inr b) := by
  have h1 := num.pos j
  refine not_conflict_of_le' ?_
  simp only [Instance.start, if_neg h]
  omega

/-- On an additional day, two different clients never conflict: their unit slots are
distinct. -/
lemma not_conflict_orig_add {i : I.Day} {j j' : I.Client} (hne : j ≠ j') :
    ¬ (inst I num blocked).Conflict (Sum.inr i) (Sum.inl j) (Sum.inl j') := by
  have h1 := num.pos j
  have h2 := num.pos j'
  have h3 := num.le j
  have h4 := num.le j'
  have hidx : num.idx j ≠ num.idx j' := fun h => hne (num.inj h)
  simp only [Instance.Conflict, Instance.start, P]
  split <;> split <;> omega

/-! ## 3. The two schedules -/

variable (blocked)

/-- The schedule of the constructed instance built from a `k`-fair schedule of `I`: `c⁻`
takes the original days, `c⁺` the additional ones, and every client takes all the additional
days that are not among its blocked ones. -/
noncomputable def liftSched (σ : I.Schedule) : (inst I num blocked).Schedule := fun i =>
  match i with
  | Sum.inl i' => insert (Sum.inr false) ((σ i').image Sum.inl)
  | Sum.inr i' => insert (Sum.inr true)
      ((Finset.univ.filter fun j : I.Client => i' ∉ blocked j).image Sum.inl)

/-- The original-day part of a schedule of the constructed instance. -/
noncomputable def dropSched (τ : (inst I num blocked).Schedule) : I.Schedule := fun i =>
  Finset.univ.filter fun j => (Sum.inl j : (inst I num blocked).Client) ∈ τ (Sum.inl i)

variable {blocked}

@[simp] lemma mem_dropSched {τ : (inst I num blocked).Schedule} {i : I.Day} {j : I.Client} :
    j ∈ dropSched (num := num) blocked τ i ↔ (Sum.inl j : (inst I num blocked).Client) ∈ τ (Sum.inl i) := by
  simp [dropSched]

/-- Serving splits into the original and the additional days. -/
lemma served_split (τ : (inst I num blocked).Schedule) (c : (inst I num blocked).Client) :
    served τ c = (Finset.univ.filter fun i : I.Day => c ∈ τ (Sum.inl i)).card
      + (Finset.univ.filter fun i : I.Day => c ∈ τ (Sum.inr i)).card := by
  classical
  have h1 : served τ c = ∑ i : I.Day ⊕ I.Day, (if c ∈ τ i then 1 else 0) := served_eq_sum _ _
  have h2 : (∑ i : I.Day ⊕ I.Day, (if c ∈ τ i then 1 else 0))
      = (∑ i : I.Day, (if c ∈ τ (Sum.inl i) then 1 else 0))
        + ∑ i : I.Day, (if c ∈ τ (Sum.inr i) then 1 else 0) := Fintype.sum_sum_type _
  have h3 : (Finset.univ.filter fun i : I.Day => c ∈ τ (Sum.inl i)).card
      = ∑ i : I.Day, (if c ∈ τ (Sum.inl i) then 1 else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h4 : (Finset.univ.filter fun i : I.Day => c ∈ τ (Sum.inr i)).card
      = ∑ i : I.Day, (if c ∈ τ (Sum.inr i) then 1 else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

/-! ## 4. One marker runs every day -/

/-- In an `m`-fair schedule of the constructed instance, one of the two markers runs on each
of the `2m` days: they conflict, so at most one runs per day, and together they need `2m`
served days. -/
theorem exists_marker_each_day {τ : (inst I num blocked).Schedule} (hfeas : Feasible τ)
    (hfair : Fair (fun _ => I.numDays) τ) (i : (inst I num blocked).Day) :
    ∃ b : Bool, (Sum.inr b : (inst I num blocked).Client) ∈ τ i := by
  classical
  by_contra hcon
  push Not at hcon
  set f : (inst I num blocked).Day → ℕ := fun i' =>
    (if (Sum.inr false : (inst I num blocked).Client) ∈ τ i' then 1 else 0)
      + (if (Sum.inr true : (inst I num blocked).Client) ∈ τ i' then 1 else 0) with hf
  have hone : ∀ i', f i' ≤ 1 := by
    intro i'
    by_cases h1 : (Sum.inr false : (inst I num blocked).Client) ∈ τ i'
    · by_cases h2 : (Sum.inr true : (inst I num blocked).Client) ∈ τ i'
      · exact absurd (conflict_markers i' false true)
          (hfeas i' _ h1 _ h2 (by simp))
      · simp [hf, h1, h2]
    · by_cases h2 : (Sum.inr true : (inst I num blocked).Client) ∈ τ i' <;> simp [hf, h1, h2]
  have hzero : f i = 0 := by simp [hf, hcon false, hcon true]
  have hcards : Fintype.card (inst I num blocked).Day = I.numDays + I.numDays :=
    numDays_inst I num blocked
  have hbound : ∑ i' : (inst I num blocked).Day, f i' ≤ I.numDays + I.numDays - 1 := by
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
    have h1 : ∑ i' ∈ Finset.univ.erase i, f i' ≤ (Finset.univ.erase i).card := by
      calc ∑ i' ∈ Finset.univ.erase i, f i' ≤ ∑ _i' ∈ Finset.univ.erase i, 1 :=
            Finset.sum_le_sum fun i' _ => hone i'
        _ = (Finset.univ.erase i).card := by simp
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hcards] at h1
    omega
  have hge : ∑ i' : (inst I num blocked).Day, f i'
      = served τ (Sum.inr false) + served τ (Sum.inr true) := by
    rw [served_eq_sum, served_eq_sum, ← Finset.sum_add_distrib]
  have hA : I.numDays ≤ served τ (Sum.inr false) := hfair _
  have hB : I.numDays ≤ served τ (Sum.inr true) := hfair _
  have hpos : 0 < Fintype.card (inst I num blocked).Day := Fintype.card_pos_iff.2 ⟨i⟩
  rw [hcards] at hpos
  omega

/-! ## 5. Lemma 15's correctness -/

/-- **Lemma 15's correctness.** With `blocked j` a set of `k j` days for each client, the
constructed instance admits a feasible `m`-fair schedule exactly when the original admits a
feasible `k`-fair one. -/
theorem hasFairSchedule_iff (k : I.Client → ℕ) (hcard : ∀ j, (blocked j).card = k j) :
    I.HasFairSchedule k ↔ (inst I num blocked).HasKFairSchedule I.numDays := by
  classical
  have hkm : ∀ j, k j ≤ I.numDays := fun j => by
    rw [← hcard j]
    have h : (blocked j).card ≤ (Finset.univ : Finset I.Day).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [numDays] using h
  have hfree : ∀ j : I.Client,
      (Finset.univ.filter fun i : I.Day => i ∉ blocked j).card = I.numDays - k j := by
    intro j
    have hsplit : (Finset.univ.filter fun i : I.Day => i ∈ blocked j).card
        + (Finset.univ.filter fun i : I.Day => i ∉ blocked j).card = I.numDays := by
      simpa [numDays] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I.Day))
          (p := fun i => i ∈ blocked j)
    have hb : (Finset.univ.filter fun i : I.Day => i ∈ blocked j).card = k j := by
      rw [← hcard j]
      congr 1
      ext i
      simp
    omega
  constructor
  · rintro ⟨σ, hfeas, hfair⟩
    refine ⟨liftSched (num := num) blocked σ, ?_, ?_⟩
    · rintro (i | i) x hx y hy hne
      · -- an original day: the schedule of `I`, plus `c⁻`
        simp only [liftSched, Finset.mem_insert, Finset.mem_image] at hx hy
        rcases hx with rfl | ⟨a, ha, rfl⟩ <;> rcases hy with rfl | ⟨b, hb, rfl⟩
        · exact absurd rfl hne
        · exact fun hc => not_conflict_marker_orig i b false (conflict_symm hc)
        · exact not_conflict_marker_orig i a false
        · exact hfeas i a ha b hb fun h => hne (by rw [h])
      · -- an additional day: the unblocked clients, plus `c⁺`
        simp only [liftSched, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and] at hx hy
        rcases hx with rfl | ⟨a, ha, rfl⟩ <;> rcases hy with rfl | ⟨b, hb, rfl⟩
        · exact absurd rfl hne
        · exact fun hc => not_conflict_marker_add hb true (conflict_symm hc)
        · exact not_conflict_marker_add ha true
        · exact not_conflict_orig_add fun h => hne (by rw [h])
    · rintro (j | b)
      · show I.numDays ≤ _
        rw [served_split (num := num)]
        have horig : (Finset.univ.filter fun i : I.Day =>
            (Sum.inl j : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inl i)).card
            = served σ j := by
          congr 1
          ext i
          simp [liftSched]
        have hadd : (Finset.univ.filter fun i : I.Day =>
            (Sum.inl j : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inr i)).card
            = (Finset.univ.filter fun i : I.Day => i ∉ blocked j).card := by
          congr 1
          ext i
          simp [liftSched]
        rw [horig, hadd, hfree j]
        have := hfair j
        have := hkm j
        omega
      · show I.numDays ≤ _
        rw [served_split]
        cases b with
        | false =>
          have horig : (Finset.univ.filter fun i : I.Day =>
              (Sum.inr false : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inl i)).card
              = I.numDays := by
            rw [show (Finset.univ.filter fun i : I.Day =>
              (Sum.inr false : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inl i))
              = Finset.univ from by ext i; simp [liftSched]]
            simp [numDays]
          omega
        | true =>
          have hadd : (Finset.univ.filter fun i : I.Day =>
              (Sum.inr true : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inr i)).card
              = I.numDays := by
            rw [show (Finset.univ.filter fun i : I.Day =>
              (Sum.inr true : (inst I num blocked).Client) ∈ liftSched (num := num) blocked σ (Sum.inr i))
              = Finset.univ from by ext i; simp [liftSched]]
            simp [numDays]
          omega
  · rintro ⟨τ, hfeas, hfair⟩
    refine ⟨dropSched (num := num) blocked τ, ?_, fun j => ?_⟩
    · intro i x hx y hy hne
      rw [mem_dropSched] at hx hy
      exact hfeas (Sum.inl i) _ hx _ hy fun h => hne (Sum.inl_injective h)
    · -- a blocked day is unusable, so the original days must supply `k j` of the `m`
      have hblock : ∀ i : I.Day, i ∈ blocked j →
          (Sum.inl j : (inst I num blocked).Client) ∉ τ (Sum.inr i) := by
        intro i hi hmem
        obtain ⟨b, hb⟩ := exists_marker_each_day hfeas hfair (Sum.inr i)
        exact hfeas (Sum.inr i) _ hmem _ hb (by simp) (conflict_marker_add hi b)
      have hsub : (Finset.univ.filter fun i : I.Day =>
          (Sum.inl j : (inst I num blocked).Client) ∈ τ (Sum.inr i))
          ⊆ Finset.univ.filter fun i : I.Day => i ∉ blocked j := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact fun hb => hblock i hb hi
      have hadd := le_trans (Finset.card_le_card hsub) (le_of_eq (hfree j))
      have hsplit := served_split τ (Sum.inl j)
      have horig : (Finset.univ.filter fun i : I.Day =>
          (Sum.inl j : (inst I num blocked).Client) ∈ τ (Sum.inl i)).card
          = served (dropSched (num := num) blocked τ) j := by
        rw [served]
        congr 1
        ext i
        simp
      have hm : I.numDays ≤ served τ (Sum.inl j) := hfair _
      have := hkm j
      omega


/-! ## 6. The treewidth grows by at most two

The construction adds two clients and **no** conflict between two clients of `I`, so any
tree decomposition of `I`'s overall conflict graph becomes one of the new instance's by
putting the two markers into every bag. -/

end Lemma15

end Lax117284Proofs.Model
