import Lax117284Proofs.IlpClients.Siegel

/-!
# The block system: type rows and client rows

An abstract version of the constraint system of the reduction.  Columns `c` of a linear order `κ`
carry an optional *type* `τ c` and a `0/1` vector `u c` of length `n`.  A vector `v` (supported on
a finite set `S` of columns) is in the kernel, `BKer τ u S v`, when for every type `t` the entries
of the columns of type `t` add up to `0` (the type rows), and `∑ v c • u c = 0` (the client rows).

The *base* of a type inside `S` is its least column in `S`.  The *difference matrix* `Dm` has, for
a typed column, the difference `u c - u (base c)`, and for an untyped column `u c`.  Kernel vectors
supported on `S` correspond to vectors of the kernel of `Dm` that vanish at the bases
(`proj_ker`, `lift_ker`): the base entry is minus the sum of the other entries of its type.
-/

namespace Lax117284Proofs.IlpClients

open Finset

noncomputable section Block

variable {κ : Type*} [LinearOrder κ] {n : ℕ} (τ : κ → Option ℕ) (u : κ → Fin n → ℤ)

/-- The kernel conditions of the block system on the columns of `S`. -/
def BKer (S : Finset κ) (v : κ → ℤ) : Prop :=
  (∀ t : ℕ, ∑ c ∈ S.filter (fun c => τ c = some t), v c = 0) ∧
    ∀ j : Fin n, ∑ c ∈ S, v c * u c j = 0

/-- The base column of the type of `c` inside `S`: the least column of `S` of that type. -/
def bs (S : Finset κ) (c : κ) : κ :=
  if h : (S.filter (fun c' => τ c' = τ c)).Nonempty then
    (S.filter (fun c' => τ c' = τ c)).min' h else c

theorem bs_congr (S : Finset κ) {c c' : κ} (hc : c ∈ S) (h : τ c = τ c') :
    bs τ S c = bs τ S c' := by
  have hne : (S.filter (fun x => τ x = τ c)).Nonempty := ⟨c, by simp [hc]⟩
  unfold bs
  simp only [← h]
  rw [dif_pos hne, dif_pos hne]

theorem bs_spec (S : Finset κ) {c : κ} (hc : c ∈ S) :
    bs τ S c ∈ S ∧ τ (bs τ S c) = τ c ∧ ∀ c' ∈ S, τ c' = τ c → bs τ S c ≤ c' := by
  have hne : (S.filter (fun c' => τ c' = τ c)).Nonempty := ⟨c, by simp [hc]⟩
  have h1 : bs τ S c = (S.filter (fun c' => τ c' = τ c)).min' hne := by
    unfold bs; rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  rw [← h1] at hmem
  simp only [mem_filter] at hmem
  refine ⟨hmem.1, hmem.2, fun c' hc' hτ => ?_⟩
  rw [h1]
  exact Finset.min'_le _ _ (by simp [hc', hτ])

theorem bs_bs (S : Finset κ) {c : κ} (hc : c ∈ S) : bs τ S (bs τ S c) = bs τ S c :=
  bs_congr τ S (bs_spec τ S hc).1 (bs_spec τ S hc).2.1

/-- `b` is a base column of `S`: typed, and the least column of its type in `S`. -/
def IsB (S : Finset κ) (b : κ) : Prop := τ b ≠ none ∧ bs τ S b = b

instance (S : Finset κ) : DecidablePred (IsB τ S) := fun b => by unfold IsB; infer_instance

/-- The difference matrix. -/
def Dm (S : Finset κ) (j : Fin n) (c : κ) : ℤ :=
  if τ c = none then u c j else u c j - u (bs τ S c) j

theorem Dm_abs_le (hu : ∀ c j, 0 ≤ u c j ∧ u c j ≤ 1) (S : Finset κ) (j : Fin n) (c : κ) :
    |Dm τ u S j c| ≤ ((1 : ℕ) : ℤ) := by
  unfold Dm
  have h1 := hu c j
  have h2 := hu (bs τ S c) j
  split_ifs
  · rw [abs_le]; constructor <;> push_cast <;> linarith
  · rw [abs_le]; constructor <;> push_cast <;> linarith

/-- Base columns have a vanishing difference vector. -/
theorem Dm_base (S : Finset κ) {c : κ} (hτ : τ c ≠ none) (hc : bs τ S c = c) (j : Fin n) :
    Dm τ u S j c = 0 := by
  unfold Dm; rw [if_neg hτ, hc]; ring

theorem sum_swap (Sc S₁ : Finset κ) (a G : κ → ℤ) (g : κ → κ) :
    ∑ c ∈ Sc, (∑ c' ∈ S₁, if g c' = c then a c' else 0) * G c =
      ∑ c' ∈ S₁, if g c' ∈ Sc then a c' * G (g c') else 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  have : ∀ c, (if g c' = c then a c' else 0) * G c = if g c' = c then a c' * G c else 0 := by
    intro c; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_eq]

/-- `∑ Dm * α`, split into the two obvious sums. -/
theorem sum_Dm (S : Finset κ) (α : κ → ℤ) (j : Fin n) :
    ∑ c ∈ S, Dm τ u S j c * α c =
      ∑ c ∈ S, α c * u c j - ∑ c ∈ S.filter (fun c => τ c ≠ none), α c * u (bs τ S c) j := by
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold Dm
  by_cases h : τ c = none <;> simp [h] <;> ring

/-- The correction: the sum of the entries of `α` at the columns whose base is `c`. -/
def corr (S : Finset κ) (α : κ → ℤ) (c : κ) : ℤ :=
  ∑ c' ∈ S.filter (fun c' => τ c' ≠ none), if bs τ S c' = c then α c' else 0

/-- The kernel vector of the block system attached to a vector `α` of the kernel of `Dm`. -/
def lift (S : Finset κ) (α : κ → ℤ) (c : κ) : ℤ :=
  if c ∈ S then α c - corr τ S α c else 0

/-- **Lifting**: a kernel vector of the difference matrix gives a kernel vector of the block
system. -/
theorem lift_ker (S : Finset κ) (α : κ → ℤ) (hα : ∀ j, ∑ c ∈ S, Dm τ u S j c * α c = 0) :
    BKer τ u S (lift τ S α) := by
  constructor
  · intro t
    set Sc := S.filter (fun c => τ c = some t) with hSc
    have h1 : ∑ c ∈ Sc, lift τ S α c = ∑ c ∈ Sc, α c - ∑ c ∈ Sc, corr τ S α c := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      have : c ∈ S := (Finset.mem_filter.mp hc).1
      simp [lift, this]
    have h2 : ∑ c ∈ Sc, corr τ S α c = ∑ c ∈ Sc, α c := by
      have := sum_swap (Sc := Sc) (S.filter (fun c' => τ c' ≠ none)) α (fun _ => 1) (bs τ S)
      simp only [mul_one] at this
      unfold corr
      rw [this]
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      by_cases hτ : τ c' = none
      · simp [hτ]
      · have hb := bs_spec τ S hc'
        by_cases h4 : τ c' = some t
        · simp [hSc, hτ, h4, hb.1, hb.2.1]
        · simp [hSc, hτ, h4, hb.1, hb.2.1]
    rw [h1, h2, sub_self]
  · intro j
    have h1 : ∑ c ∈ S, lift τ S α c * u c j =
        ∑ c ∈ S, α c * u c j - ∑ c ∈ S, corr τ S α c * u c j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      simp [lift, hc]; ring
    have h2 : ∑ c ∈ S, corr τ S α c * u c j =
        ∑ c' ∈ S.filter (fun c' => τ c' ≠ none), α c' * u (bs τ S c') j := by
      have := sum_swap (Sc := S) (S.filter (fun c' => τ c' ≠ none)) α (fun c => u c j) (bs τ S)
      have h3 : ∀ c ∈ S, corr τ S α c * u c j = (∑ c' ∈ S.filter (fun c' => τ c' ≠ none),
          if bs τ S c' = c then α c' else 0) * u c j := fun c _ => by simp [corr]
      rw [Finset.sum_congr rfl h3, this]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      have := (bs_spec τ S (Finset.mem_filter.mp hc').1).1
      simp [this]
    have h3 := hα j
    rw [sum_Dm] at h3
    rw [h1, h2]
    exact h3

/-- Grouping by type: the entries of the columns of one type add up to `0`, so any function of the
base of the type is annihilated. -/
theorem sum_bs_fiber (S : Finset κ) (v w : κ → ℤ)
    (hv : ∀ t, ∑ c ∈ S.filter (fun c => τ c = some t), v c = 0) :
    ∑ c ∈ S.filter (fun c => τ c ≠ none), v c * w (bs τ S c) = 0 := by
  classical
  let g : κ → ℕ := fun c => (τ c).getD 0
  have hmaps : ∀ c ∈ S.filter (fun c => τ c ≠ none),
      g c ∈ (S.filter (fun c => τ c ≠ none)).image g :=
    fun c hc => Finset.mem_image_of_mem g hc
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨c0, hc0, hg0⟩ := Finset.mem_image.mp ht
  have hc0S : c0 ∈ S := (Finset.mem_filter.mp hc0).1
  have hτ0 : τ c0 = some t := by
    have hne := (Finset.mem_filter.mp hc0).2
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [g, hx, Option.getD_some] at hg0
    rw [hx, hg0]
  have hfib : (S.filter (fun c => τ c ≠ none)).filter (fun c => g c = t) =
      S.filter (fun c => τ c = some t) := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hS, hne⟩, hg⟩
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
      simp only [g, hx, Option.getD_some] at hg
      exact ⟨hS, by rw [hx, hg]⟩
    · rintro ⟨hS, hτ⟩
      exact ⟨⟨hS, by simp [hτ]⟩, by simp [g, hτ]⟩
  have hbs : ∀ c ∈ S.filter (fun c => τ c = some t), bs τ S c = bs τ S c0 := by
    intro c hc
    have := Finset.mem_filter.mp hc
    exact bs_congr τ S this.1 (this.2.trans hτ0.symm)
  rw [hfib]
  rw [Finset.sum_congr rfl (fun c hc => by rw [hbs c hc])]
  rw [← Finset.sum_mul, hv t, zero_mul]

/-- The vector of the difference kernel attached to `v`: `v` with the bases zeroed. -/
def alpha0 (S : Finset κ) (v : κ → ℤ) (c : κ) : ℤ :=
  if τ c ≠ none ∧ bs τ S c = c then 0 else v c

theorem Dm_alpha0 (S : Finset κ) (v : κ → ℤ) (j : Fin n) (c : κ) :
    Dm τ u S j c * alpha0 τ S v c = Dm τ u S j c * v c := by
  unfold alpha0
  split_ifs with h
  · rw [Dm_base τ u S h.1 h.2 j]; ring
  · rfl

/-- **Projection**: a kernel vector of the block system gives a kernel vector of the difference
matrix. -/
theorem proj_ker (S : Finset κ) (v : κ → ℤ) (hv : BKer τ u S v) (j : Fin n) :
    ∑ c ∈ S, Dm τ u S j c * alpha0 τ S v c = 0 := by
  rw [Finset.sum_congr rfl (fun c _ => Dm_alpha0 τ u S v j c), sum_Dm]
  have h1 := hv.2 j
  have h2 := sum_bs_fiber τ S v (fun c => u c j) hv.1
  simp only [mul_comm (v _)] at h1 h2 ⊢
  rw [h1, h2]; ring

theorem alpha0_ne (S : Finset κ) (v : κ → ℤ) (hS : ∀ c, c ∈ S ↔ v c ≠ 0) (hne : S.Nonempty)
    (hv : ∀ t, ∑ c ∈ S.filter (fun c => τ c = some t), v c = 0) :
    ∃ c ∈ S, alpha0 τ S v c ≠ 0 := by
  obtain ⟨c, hc⟩ := hne
  have hvc : v c ≠ 0 := (hS c).mp hc
  by_cases hb : τ c ≠ none ∧ bs τ S c = c
  · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hb.1
    have hsum := hv t
    have hcSc : c ∈ S.filter (fun c => τ c = some t) := by simp [hc, ht]
    -- another column of the same type with a nonzero entry
    obtain ⟨c', hc'Sc, hc'ne, hc'v⟩ : ∃ c' ∈ S.filter (fun c => τ c = some t), c' ≠ c ∧ v c' ≠ 0 := by
      by_contra hcon
      have hz : ∀ c' ∈ S.filter (fun c => τ c = some t), c' ≠ c → v c' = 0 := by
        intro c' h1 h2
        by_contra h3
        exact hcon ⟨c', h1, h2, h3⟩
      rw [Finset.sum_eq_single_of_mem c hcSc hz] at hsum
      exact hvc hsum
    have hc'S := (Finset.mem_filter.mp hc'Sc).1
    have hτ' : τ c' = some t := (Finset.mem_filter.mp hc'Sc).2
    refine ⟨c', hc'S, ?_⟩
    unfold alpha0
    have hbs : bs τ S c' = c := by
      rw [bs_congr τ S hc'S (hτ'.trans ht.symm)]; exact hb.2
    rw [if_neg]
    · exact hc'v
    · rintro ⟨-, h⟩
      exact hc'ne (h.symm.trans hbs)
  · exact ⟨c, hc, by unfold alpha0; rw [if_neg hb]; exact hvc⟩

/-- A column that is not a base is the base of no column. -/
theorem corr_eq_zero (S : Finset κ) (α : κ → ℤ) {c : κ} (hc : c ∈ S)
    (hnb : ¬ (τ c ≠ none ∧ bs τ S c = c)) : corr τ S α c = 0 := by
  unfold corr
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hc'S := Finset.mem_filter.mp hc'
  rw [if_neg]
  intro hb
  apply hnb
  have h1 := bs_spec τ S hc'S.1
  have h2 : τ c = τ c' := by rw [← hb]; exact h1.2.1
  refine ⟨by rw [h2]; exact hc'S.2, ?_⟩
  rw [← hb, bs_bs τ S hc'S.1]

theorem corr_abs_le (S : Finset κ) (α : κ → ℤ) (B : ℤ) (m : ℕ) (hB : 0 ≤ B)
    (hα : ∀ c, |α c| ≤ B) (hm : (S.filter (fun c => α c ≠ 0)).card ≤ m) (c : κ) :
    |corr τ S α c| ≤ m * B := by
  unfold corr
  calc |∑ c' ∈ S.filter (fun c' => τ c' ≠ none), if bs τ S c' = c then α c' else 0|
      ≤ ∑ c' ∈ S.filter (fun c' => τ c' ≠ none), |if bs τ S c' = c then α c' else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c' ∈ S.filter (fun c' => τ c' ≠ none), (if α c' ≠ 0 then B else 0) := by
        refine Finset.sum_le_sum fun c' _ => ?_
        by_cases h : α c' = 0
        · by_cases h2 : bs τ S c' = c <;> simp [h, h2]
        · by_cases h2 : bs τ S c' = c
          · simp [h, h2, hα c']
          · simp [h, h2, hB]
    _ ≤ ∑ c' ∈ S, (if α c' ≠ 0 then B else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun c' _ _ => by split_ifs <;> simp [hB])
    _ = (S.filter (fun c => α c ≠ 0)).card * B := by
        rw [← Finset.sum_filter]; simp
    _ ≤ m * B := by
        have : ((S.filter (fun c => α c ≠ 0)).card : ℤ) ≤ m := by exact_mod_cast hm
        exact mul_le_mul_of_nonneg_right this hB

/-- **Small kernel vectors of the block system** (the family's Lemma F3). -/
theorem block_small (hu : ∀ c j, 0 ≤ u c j ∧ u c j ≤ 1) (S : Finset κ) (v : κ → ℤ)
    (hS : ∀ c, c ∈ S ↔ v c ≠ 0) (hne : S.Nonempty) (hv : BKer τ u S v) :
    ∃ v' : κ → ℤ, (∃ c ∈ S, v' c ≠ 0) ∧ (∀ c, v' c ≠ 0 → c ∈ S) ∧ BKer τ u S v' ∧
      (∀ c, |v' c| ≤ (((n + 1) ^ (n + 1) : ℕ) : ℤ)) ∧
      (S.filter (fun c => v' c ≠ 0 ∧ ¬ IsB τ S c)).card ≤ n + 1 := by
  classical
  obtain ⟨α, hα0, hαS, hαk, hαv, hαb, hαc⟩ := small_kernel_on S (Dm τ u S) 1 le_rfl
    (fun j c => Dm_abs_le τ u hu S j c) (alpha0 τ S v)
    (alpha0_ne τ S v hS hne hv.1) (proj_ker τ u S v hv)
  simp only [Fintype.card_fin] at hαb hαc
  have hαnb : ∀ c, α c ≠ 0 → ¬ (τ c ≠ none ∧ bs τ S c = c) := by
    intro c hc hb
    have := hαv c hc
    unfold alpha0 at this
    rw [if_pos hb] at this
    exact this rfl
  refine ⟨lift τ S α, ?_, ?_, lift_ker τ u S α hαk, ?_, ?_⟩
  · obtain ⟨c, hcS, hc⟩ := hα0
    refine ⟨c, hcS, ?_⟩
    simp only [lift, if_pos hcS, corr_eq_zero τ S α hcS (hαnb c hc), sub_zero]
    exact hc
  · intro c hc
    by_contra h
    exact hc (by simp [lift, h])
  · intro c
    set B₁ : ℤ := (((n + 1) * 1 : ℕ) : ℤ) ^ n with hB₁
    have hB : (0 : ℤ) ≤ B₁ := by positivity
    have hn1 : (1 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos n
    have hfin : (((n + 1) ^ (n + 1) : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) * B₁ := by
      rw [hB₁]; push_cast; ring
    rw [hfin]
    by_cases hcS : c ∈ S
    · unfold lift
      rw [if_pos hcS]
      by_cases hc : α c = 0
      · rw [hc, zero_sub, abs_neg]
        exact corr_abs_le τ S α B₁ (n + 1) hB hαb hαc c
      · rw [corr_eq_zero τ S α hcS (hαnb c hc), sub_zero]
        exact (hαb c).trans (le_mul_of_one_le_left hB hn1)
    · have : lift τ S α c = 0 := by simp [lift, hcS]
      rw [this, abs_zero]
      positivity
  · refine le_trans (Finset.card_le_card ?_) hαc
    intro c hc
    have hc' := Finset.mem_filter.mp hc
    have hcS : c ∈ S := hc'.1
    have hnb : ¬ (τ c ≠ none ∧ bs τ S c = c) := hc'.2.2
    have h1 : lift τ S α c = α c := by
      simp only [lift, if_pos hcS, corr_eq_zero τ S α hcS hnb, sub_zero]
    refine Finset.mem_filter.mpr ⟨hcS, ?_⟩
    rw [← h1]; exact hc'.2.1

/-- **Lifting is nonzero**: a kernel vector of the difference matrix that vanishes at the bases and
is nonzero at some column of `S` lifts to a nonzero kernel vector of the block system, supported
in `S`, agreeing with `α` at that column. -/
theorem lift_nonzero (S : Finset κ) (α : κ → ℤ) (hαk : ∀ j, ∑ c ∈ S, Dm τ u S j c * α c = 0)
    (hαnb : ∀ c, α c ≠ 0 → ¬ (τ c ≠ none ∧ bs τ S c = c)) {c : κ} (hcS : c ∈ S) (hc : α c ≠ 0) :
    BKer τ u S (lift τ S α) ∧ lift τ S α c ≠ 0 := by
  refine ⟨lift_ker τ u S α hαk, ?_⟩
  simp only [lift, if_pos hcS, corr_eq_zero τ S α hcS (hαnb c hc), sub_zero]
  exact hc

/-- The base of a typed column of `S` is a base column of `S`. -/
theorem bs_isB (S : Finset κ) {c : κ} (hc : c ∈ S) (hτ : τ c ≠ none) :
    bs τ S c ∈ S ∧ IsB τ S (bs τ S c) := by
  have h := bs_spec τ S hc
  exact ⟨h.1, by rw [h.2.1]; exact hτ, bs_bs τ S hc⟩

/-- A base column is the base of exactly the columns of its type. -/
theorem bs_eq_iff (S : Finset κ) {b c : κ} (hb : b ∈ S) (hbb : IsB τ S b) (hc : c ∈ S)
    (hτ : τ c ≠ none) : bs τ S c = b ↔ τ c = τ b := by
  constructor
  · intro h
    rw [← h]; exact (bs_spec τ S hc).2.1.symm
  · intro h
    rw [bs_congr τ S hc h]; exact hbb.2

/-- A base column is the least column of its type. -/
theorem isB_iff (S : Finset κ) {c : κ} (hc : c ∈ S) :
    IsB τ S c ↔ τ c ≠ none ∧ ∀ c' ∈ S, τ c' = τ c → c ≤ c' := by
  constructor
  · rintro ⟨hτ, hbs⟩
    exact ⟨hτ, fun c' hc' h => hbs ▸ (bs_spec τ S hc).2.2 c' hc' h⟩
  · rintro ⟨hτ, hmin⟩
    refine ⟨hτ, le_antisymm ?_ ?_⟩
    · exact (bs_spec τ S hc).2.2 c hc rfl
    · have h := bs_spec τ S hc
      exact hmin _ h.1 h.2.1

/-- Two base columns of the same type coincide. -/
theorem IsB_unique (S : Finset κ) {b b' : κ} (hb : b ∈ S) (hbb : IsB τ S b) (hbb' : IsB τ S b')
    (h : τ b = τ b') : b = b' := by
  rw [← hbb.2, ← hbb'.2]
  exact bs_congr τ S hb h

/-- **Regrouping by base.** -/
theorem sum_regroup (S : Finset κ) (f G : κ → ℤ) :
    ∑ b ∈ S.filter (IsB τ S), (∑ c ∈ S.filter (fun c => τ c ≠ none),
      if bs τ S c = b then f c else 0) * G b =
      ∑ c ∈ S.filter (fun c => τ c ≠ none), f c * G (bs τ S c) := by
  classical
  rw [sum_swap (Sc := S.filter (IsB τ S)) (S.filter (fun c => τ c ≠ none)) f G (bs τ S)]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' := Finset.mem_filter.mp hc
  have := bs_isB τ S hc'.1 hc'.2
  rw [if_pos (Finset.mem_filter.mpr this)]

/-- The columns of `S` with base `b`, for a base column `b`, are the columns of `S` of its type. -/
theorem filter_bs_eq (S : Finset κ) {b : κ} (hb : b ∈ S) (hbb : IsB τ S b) :
    S.filter (fun c => τ c ≠ none ∧ bs τ S c = b) = S.filter (fun c => τ c = τ b) := by
  ext c
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hc, hτ, h⟩
    exact ⟨hc, ((bs_eq_iff τ S hb hbb hc hτ).mp h)⟩
  · rintro ⟨hc, h⟩
    have hτ : τ c ≠ none := by rw [h]; exact hbb.1
    exact ⟨hc, hτ, (bs_eq_iff τ S hb hbb hc hτ).mpr h⟩

/-- The columns of the type of a base column `b`: `b` and the non-base ones. -/
theorem sum_type_eq (S : Finset κ) {b : κ} (hb : b ∈ S) (hbb : IsB τ S b) (f : κ → ℤ) :
    ∑ c ∈ S.filter (fun c => τ c = τ b), f c =
      f b + ∑ c ∈ S.filter (fun c => τ c = τ b ∧ ¬ IsB τ S c), f c := by
  have hbmem : b ∈ S.filter (fun c => τ c = τ b) := by simp [hb]
  rw [← Finset.add_sum_erase _ _ hbmem]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext c
  simp only [Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨hcb, hc, hτ⟩
    refine ⟨hc, hτ, fun hB => hcb ?_⟩
    have h1 := (bs_eq_iff τ S hb hbb hc (by rw [hτ]; exact hbb.1)).mpr hτ
    rw [← h1, hB.2]
  · rintro ⟨hc, hτ, hnB⟩
    refine ⟨fun h => hnB (h ▸ hbb), hc, hτ⟩

/-- Base columns have a vanishing entry in the difference matrix. -/
theorem sum_filter_nonbase (S : Finset κ) (F : κ → ℤ) (hF : ∀ c, IsB τ S c → F c = 0) :
    ∑ c ∈ S.filter (fun c => ¬ IsB τ S c), F c = ∑ c ∈ S, F c := by
  apply Finset.sum_filter_of_ne
  intro c _ hc hB
  exact hc (hF c hB)

end Block

end Lax117284Proofs.IlpClients
