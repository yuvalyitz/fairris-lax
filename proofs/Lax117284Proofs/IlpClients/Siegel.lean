import Lax117284Proofs.IlpClients.Basic
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Matrix.Normed

/-!
# Small Kernel Vectors (Siegel's Lemma)

`small_kernel`: if an integer matrix `D` (entries of absolute value `≤ Δ`, `Δ ≥ 1`, with `M` rows)
has a nonzero integer kernel vector `v`, it has a nonzero integer kernel vector `α`, supported in the
support of `v`, with at most `M + 1` nonzero entries, each of absolute value at most
`((M + 1) Δ)^M`.  Consequently `((M+1)Δ)^M + 1` is a kernel bound of every `M × N` matrix with
entries `≤ Δ` (`kernelBound_of_entries`).
-/

attribute [local instance] Matrix.seminormedAddCommGroup

set_option linter.unusedSectionVars false

namespace Lax117284Proofs.IlpClients

open Finset

variable {ι κ : Type*}

section Rational

variable [Fintype ι] [Fintype κ] [DecidableEq κ] (D : ι → κ → ℤ)

/-- The column set `C` carries a nonzero rational kernel vector. -/
def QDep (C : Finset κ) : Prop :=
  ∃ w : κ → ℚ, w ≠ 0 ∧ (∀ j, j ∉ C → w j = 0) ∧ ∀ i, ∑ j, (D i j : ℚ) * w j = 0


/-- A minimal (for inclusion) dependent subset of a dependent set. -/
theorem exists_minimal_qdep (S : Finset κ) (hS : QDep D S) :
    ∃ C ⊆ S, QDep D C ∧ ∀ C' ⊂ C, ¬ QDep D C' := by
  classical
  obtain ⟨C, hC, hmin⟩ := exists_minimal_of_wellFoundedLT (fun C : Finset κ => C ⊆ S ∧ QDep D C)
    ⟨S, Finset.Subset.refl S, hS⟩
  refine ⟨C, hC.1, hC.2, fun C' hC' hd => ?_⟩
  have := hmin ⟨hC'.subset.trans hC.1, hd⟩ hC'.subset
  exact hC'.not_ge this

/-- A minimal dependent set has at most `M + 1` elements. -/
theorem card_le_of_minimal (C : Finset κ) (hC : QDep D C) (hmin : ∀ C' ⊂ C, ¬ QDep D C') :
    C.card ≤ Fintype.card ι + 1 := by
  classical
  obtain ⟨w, hw0, hwC, hw⟩ := hC
  obtain ⟨j0, hj0⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    exact hw0 (funext fun j => by by_contra h; exact hcon ⟨j, h⟩)
  have hj0C : j0 ∈ C := by
    by_contra h; exact hj0 (hwC j0 h)
  let col : ↥(C.erase j0) → (ι → ℚ) := fun j i => (D i j : ℚ)
  have hli : LinearIndependent ℚ col := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hcon
    obtain ⟨j1, hj1⟩ := not_forall.mp hcon
    refine hmin (C.erase j0) (Finset.erase_ssubset hj0C) ⟨fun j => if h : j ∈ C.erase j0 then g ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
    · intro h0
      have := congrFun h0 j1
      simp [j1.2] at this
      exact hj1 this
    · intro j hj; simp [hj]
    · intro i
      have := congrFun hg i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, col] at this
      rw [← Finset.sum_subset (Finset.subset_univ (C.erase j0)) (fun j _ hj => by simp [hj])]
      rw [← Finset.sum_coe_sort (C.erase j0)]
      simp only [dif_pos (Finset.coe_mem _), Subtype.coe_eta]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => by ring
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.card_erase_of_mem hj0C] at hcard
  have : 0 < C.card := Finset.card_pos.mpr ⟨j0, hj0C⟩
  omega


theorem sum_restrict {M : Type*} [AddCommMonoid M] (C : Finset κ) (f : κ → M)
    (hf : ∀ j, j ∉ C → f j = 0) : ∑ j, f j = ∑ c : ↥C, f c := by
  rw [Finset.sum_coe_sort C f]
  exact (Finset.sum_subset (Finset.subset_univ C) fun j _ hj => hf j hj).symm

/-- The Siegel step: a dependent set `C` carries a nonzero integer kernel vector of size at most
`(|C| Δ)^(|C| - 1)`. -/
theorem int_relation (Δ : ℕ) (hΔ : 1 ≤ Δ) (hD : ∀ i j, |D i j| ≤ Δ)
    (C : Finset κ) (hC : QDep D C) :
    ∃ α : κ → ℤ, α ≠ 0 ∧ (∀ j, j ∉ C → α j = 0) ∧ (∀ i, ∑ j, D i j * α j = 0) ∧
      ∀ j, |α j| ≤ ((C.card * Δ : ℕ) : ℤ) ^ (C.card - 1) := by
  classical
  obtain ⟨w, hw0, hwC, hw⟩ := hC
  obtain ⟨j0, hj0⟩ : ∃ j, w j ≠ 0 := by
    by_contra hcon
    exact hw0 (funext fun j => by by_contra h; exact hcon ⟨j, h⟩)
  have hj0C : j0 ∈ C := by
    by_contra h; exact hj0 (hwC j0 h)
  have hCpos : 1 ≤ C.card := Finset.card_pos.mpr ⟨j0, hj0C⟩
  let rowC : ι → (↥C → ℚ) := fun i c => (D i c : ℚ)
  obtain ⟨κ', a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ rowC
  have : Finite κ' := Finite.of_injective a ha
  have : Fintype κ' := Fintype.ofFinite κ'
  let Dr : Matrix κ' ↥C ℚ := fun k c => rowC (a k) c
  have hrank : Dr.rank = Fintype.card κ' := LinearIndependent.rank_matrix hli
  -- the kernel of `Dr` is nonzero
  let w' : ↥C → ℚ := fun c => w c
  have hw'0 : w' ≠ 0 := by
    intro h
    exact hj0 (by simpa [w'] using congrFun h ⟨j0, hj0C⟩)
  have hw'ker : Dr.mulVec w' = 0 := by
    funext k
    have := hw (a k)
    have h2 : ∑ j, (D (a k) j : ℚ) * w j = ∑ c : ↥C, (D (a k) c : ℚ) * w c :=
      sum_restrict C (fun j => (D (a k) j : ℚ) * w j) fun j hj => by simp [hwC j hj]
    simp only [Matrix.mulVec, dotProduct, Dr, rowC, w', Pi.zero_apply]
    rw [← h2]; exact this
  have hlt : Fintype.card κ' < Fintype.card ↥C := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Dr.mulVecLin
    have h2 : 0 < Module.finrank ℚ (LinearMap.ker Dr.mulVecLin) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      refine ⟨⟨w', ?_⟩, ?_⟩
      · simpa using hw'ker
      · intro h; exact hw'0 (congrArg Subtype.val h)
    rw [Module.finrank_fintype_fun_eq_card] at h1
    have h3 : Module.finrank ℚ (LinearMap.range Dr.mulVecLin) = Fintype.card κ' := hrank
    omega
  have hlt' := hlt
  rw [Fintype.card_coe] at hlt
  by_cases hr : Fintype.card κ' = 0
  · -- all rows vanish on `C`
    have : IsEmpty κ' := Fintype.card_eq_zero_iff.mp hr
    have hrows : ∀ i, ∀ c : ↥C, D i c = 0 := by
      intro i c
      have hmem : rowC i ∈ Submodule.span ℚ (Set.range rowC) := Submodule.subset_span ⟨i, rfl⟩
      rw [← hspan] at hmem
      have : Set.range (rowC ∘ a) = ∅ := Set.range_eq_empty _
      rw [this, Submodule.span_empty] at hmem
      have := congrFun (Submodule.mem_bot ℚ |>.mp hmem) c
      simpa [rowC] using this
    refine ⟨Pi.single j0 1, ?_, ?_, ?_, ?_⟩
    · intro h; have := congrFun h j0; simp at this
    · intro j hj
      have : j ≠ j0 := fun e => hj (e ▸ hj0C)
      simp [this]
    · intro i
      rw [Finset.sum_eq_single j0]
      · simp [hrows i ⟨j0, hj0C⟩]
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ j0) h
    · intro j
      by_cases hj : j = j0
      · subst hj
        simp only [Pi.single_eq_same, abs_one]
        exact one_le_pow₀ (by exact_mod_cast Nat.mul_pos hCpos hΔ)
      · simp [Pi.single_eq_of_ne hj]
        positivity
  · -- Siegel
    have hpos : 0 < Fintype.card κ' := Nat.pos_of_ne_zero hr
    let Ar : Matrix κ' ↥C ℤ := fun k c => D (a k) c
    obtain ⟨t, ht0, htker, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le Ar hlt' hpos
    have hAr : ‖Ar‖ ≤ (Δ : ℝ) := by
      rw [Matrix.norm_le_iff (by positivity)]
      intro k c
      have h1 : (|D (a k) c| : ℤ) ≤ Δ := hD (a k) c
      have h2 : ((|D (a k) c| : ℤ) : ℝ) ≤ Δ := by exact_mod_cast h1
      simpa [Ar, Int.norm_eq_abs] using h2
    have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    have hℓr : (1 : ℝ) ≤ C.card := by exact_mod_cast hCpos
    have hX1 : (1 : ℝ) ≤ (C.card : ℝ) * Δ := by nlinarith
    rw [Fintype.card_coe] at htn
    have hbase : (C.card : ℝ) * max 1 ‖Ar‖ ≤ (C.card : ℝ) * Δ :=
      mul_le_mul_of_nonneg_left (max_le hΔr hAr) (by positivity)
    have hrl : (Fintype.card κ' : ℝ) + 1 ≤ C.card := by exact_mod_cast hlt
    have hexp : (Fintype.card κ' : ℝ) / ((C.card : ℝ) - Fintype.card κ') ≤ ((C.card - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ (C.card : ℝ) - Fintype.card κ' := by linarith
      have h2 : (Fintype.card κ' : ℝ) / ((C.card : ℝ) - Fintype.card κ') ≤ Fintype.card κ' :=
        div_le_self (by positivity) h1
      have h3 : ((C.card - 1 : ℕ) : ℝ) = (C.card : ℝ) - 1 := by
        rw [Nat.cast_sub hCpos]; simp
      rw [h3]; linarith
    have hbound : ‖t‖ ≤ ((C.card : ℝ) * Δ) ^ (C.card - 1) := by
      refine htn.trans ?_
      calc ((C.card : ℝ) * max 1 ‖Ar‖) ^ ((Fintype.card κ' : ℝ) / ((C.card : ℝ) - Fintype.card κ'))
          ≤ ((C.card : ℝ) * Δ) ^ ((Fintype.card κ' : ℝ) / ((C.card : ℝ) - Fintype.card κ')) :=
            Real.rpow_le_rpow (by positivity) hbase (by
              apply div_nonneg (by positivity); linarith)
        _ ≤ ((C.card : ℝ) * Δ) ^ (((C.card - 1 : ℕ)) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1 hexp
        _ = ((C.card : ℝ) * Δ) ^ (C.card - 1) := Real.rpow_natCast _ _
    -- the extension by zero
    let α : κ → ℤ := fun j => if h : j ∈ C then t ⟨j, h⟩ else 0
    have hαC : ∀ j, j ∉ C → α j = 0 := fun j hj => by simp [α, hj]
    have hαc : ∀ c : ↥C, α c = t c := fun c => by simp [α, c.2]
    refine ⟨α, ?_, hαC, ?_, ?_⟩
    · intro h
      apply ht0
      funext c
      have := congrFun h c
      rw [hαc] at this
      simpa using this
    · intro i
      -- express the row of `D` through the selected rows
      have hmem : rowC i ∈ Submodule.span ℚ (Set.range (rowC ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
      have h1 : ∑ j, D i j * α j = ∑ c : ↥C, D i c * α c :=
        sum_restrict C (fun j => D i j * α j) fun j hj => by simp [hαC j hj]
      rw [h1]
      apply Int.cast_injective (α := ℚ)
      push_cast
      have h2 : ∀ c : ↥C, (D i c : ℚ) = ∑ k, q k * (D (a k) c : ℚ) := by
        intro c
        have := congrFun hq c
        simpa [rowC, Finset.sum_apply, mul_comm] using this.symm
      have h3 : ∀ k, ∑ c : ↥C, (D (a k) c : ℚ) * (t c : ℚ) = 0 := by
        intro k
        have := congrFun htker k
        have h4 : ∑ c : ↥C, D (a k) c * t c = 0 := by simpa [Matrix.mulVec, dotProduct, Ar] using this
        have h5 := congrArg (Int.cast (R := ℚ)) h4
        push_cast at h5
        exact h5
      calc ∑ c : ↥C, (D i c : ℚ) * (α c : ℚ)
          = ∑ c : ↥C, (∑ k, q k * (D (a k) c : ℚ)) * (t c : ℚ) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [h2 c, hαc]
        _ = ∑ k, q k * ∑ c : ↥C, (D (a k) c : ℚ) * (t c : ℚ) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => by ring
        _ = 0 := Finset.sum_eq_zero fun k _ => by rw [h3 k, mul_zero]
    · intro j
      by_cases hj : j ∈ C
      · have h1 : (|α j| : ℝ) ≤ ((C.card : ℝ) * Δ) ^ (C.card - 1) := by
          have := norm_le_pi_norm t ⟨j, hj⟩
          have h2 : α j = t ⟨j, hj⟩ := hαc ⟨j, hj⟩
          rw [h2]
          simpa [Int.norm_eq_abs] using this.trans hbound
        have h2 : ((|α j| : ℤ) : ℝ) ≤ (((C.card * Δ : ℕ) : ℤ) : ℝ) ^ (C.card - 1) := by
          push_cast; push_cast at h1; exact h1
        exact_mod_cast h2
      · rw [hαC j hj]; simp only [abs_zero]; positivity

/-- **Small kernel vectors.**  A nonzero integer kernel vector `v` of a matrix with `M` rows and
entries of absolute value `≤ Δ` yields one, `α`, supported in the support of `v`, with at most
`M + 1` nonzero entries, each of absolute value `≤ ((M+1) Δ)^M`. -/
theorem small_kernel (Δ : ℕ) (hΔ : 1 ≤ Δ) (hD : ∀ i j, |D i j| ≤ Δ)
    (v : κ → ℤ) (hv0 : v ≠ 0) (hv : ∀ i, ∑ j, D i j * v j = 0) :
    ∃ α : κ → ℤ, α ≠ 0 ∧ (∀ i, ∑ j, D i j * α j = 0) ∧ (∀ j, α j ≠ 0 → v j ≠ 0) ∧
      (∀ j, |α j| ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) ^ Fintype.card ι) ∧
      (Finset.univ.filter (fun j => α j ≠ 0)).card ≤ Fintype.card ι + 1 := by
  classical
  let S : Finset κ := Finset.univ.filter (fun j => v j ≠ 0)
  have hS : QDep D S := by
    refine ⟨fun j => (v j : ℚ), ?_, ?_, ?_⟩
    · intro h
      apply hv0
      funext j
      have := congrFun h j
      simpa using this
    · intro j hj
      have : v j = 0 := by simpa [S] using hj
      simp [this]
    · intro i
      have := congrArg (Int.cast (R := ℚ)) (hv i)
      push_cast at this
      exact this
  obtain ⟨C, hCS, hCd, hmin⟩ := exists_minimal_qdep D S hS
  have hcard := card_le_of_minimal D C hCd hmin
  obtain ⟨α, hα0, hαC, hαker, hαb⟩ := int_relation D Δ hΔ hD C hCd
  have hCpos : 1 ≤ C.card := by
    obtain ⟨w, hw0, hwC, -⟩ := hCd
    obtain ⟨j0, hj0⟩ : ∃ j, w j ≠ 0 := by
      by_contra hcon
      exact hw0 (funext fun j => by by_contra h; exact hcon ⟨j, h⟩)
    exact Finset.card_pos.mpr ⟨j0, by by_contra h; exact hj0 (hwC j0 h)⟩
  refine ⟨α, hα0, hαker, ?_, ?_, ?_⟩
  · intro j hj
    have hjC : j ∈ C := by by_contra h; exact hj (hαC j h)
    have := hCS hjC
    simpa [S] using this
  · intro j
    refine (hαb j).trans ?_
    have h1 : ((C.card * Δ : ℕ) : ℤ) ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_right Δ hcard
    have h2 : (1 : ℤ) ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos (Nat.succ_pos _) hΔ
    calc ((C.card * Δ : ℕ) : ℤ) ^ (C.card - 1)
        ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) ^ (C.card - 1) := pow_le_pow_left₀ (by positivity) h1 _
      _ ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) ^ Fintype.card ι :=
          pow_le_pow_right₀ h2 (by omega)
  · refine (Finset.card_le_card ?_).trans hcard
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_contra h; exact hj (hαC j h)

end Rational

section Generic

variable [Fintype ι] [Fintype κ]


end Generic

section OnFinset

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- `small_kernel` for a system whose sums run over a finite set `S` of columns of an arbitrary
column type. -/
theorem small_kernel_on (S : Finset κ) (D : ι → κ → ℤ) (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hD : ∀ i j, |D i j| ≤ Δ) (v : κ → ℤ) (hv0 : ∃ c ∈ S, v c ≠ 0)
    (hv : ∀ i, ∑ j ∈ S, D i j * v j = 0) :
    ∃ α : κ → ℤ, (∃ c ∈ S, α c ≠ 0) ∧ (∀ c, c ∉ S → α c = 0) ∧
      (∀ i, ∑ j ∈ S, D i j * α j = 0) ∧ (∀ j, α j ≠ 0 → v j ≠ 0) ∧
      (∀ j, |α j| ≤ (((Fintype.card ι + 1) * Δ : ℕ) : ℤ) ^ Fintype.card ι) ∧
      (S.filter (fun j => α j ≠ 0)).card ≤ Fintype.card ι + 1 := by
  classical
  obtain ⟨α', hα0, hαk, hαv, hαb, hαc⟩ := small_kernel (fun i (c : ↥S) => D i c) Δ hΔ
    (fun i c => hD i c) (fun c => v c)
    (by
      intro h
      obtain ⟨c, hc, hvc⟩ := hv0
      exact hvc (by simpa using congrFun h ⟨c, hc⟩))
    (fun i => by rw [Finset.sum_coe_sort S (fun j => D i j * v j)]; exact hv i)
  let α : κ → ℤ := fun j => if h : j ∈ S then α' ⟨j, h⟩ else 0
  have hαS : ∀ c, c ∉ S → α c = 0 := fun c hc => by simp [α, hc]
  have hαs : ∀ c : ↥S, α c = α' c := fun c => by simp [α, c.2]
  refine ⟨α, ?_, hαS, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    apply hα0
    funext c
    have h1 : ¬ α c ≠ 0 := fun h => hcon ⟨c, c.2, h⟩
    rw [hαs] at h1
    simpa using h1
  · intro i
    rw [← Finset.sum_coe_sort S (fun j => D i j * α j)]
    simpa [hαs] using hαk i
  · intro j hj
    by_cases hjS : j ∈ S
    · have : α' ⟨j, hjS⟩ ≠ 0 := by
        have := hαs ⟨j, hjS⟩
        simp only at this
        rw [this] at hj; exact hj
      exact hαv ⟨j, hjS⟩ this
    · exact absurd (hαS j hjS) hj
  · intro j
    by_cases hjS : j ∈ S
    · have := hαb ⟨j, hjS⟩
      rw [← hαs ⟨j, hjS⟩] at this
      exact this
    · rw [hαS j hjS]; simp only [abs_zero]; positivity
  · refine le_trans ?_ hαc
    have : S.filter (fun j => α j ≠ 0) ⊆ (Finset.univ.filter (fun c : ↥S => α' c ≠ 0)).image Subtype.val := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
      have := hαs ⟨j, hj.1⟩
      simp only at this
      rw [← this]; exact hj.2
    exact (Finset.card_le_card this).trans Finset.card_image_le

end OnFinset

end Lax117284Proofs.IlpClients
