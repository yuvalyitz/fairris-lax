import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An integer left inverse with small entries

If the columns of a `0/±1` matrix `D` with `n` rows and columns indexed by `E` have no nonzero
integer relation, then `|E| ≤ n` and there are an integer matrix `H : E × n` and `δ ∈ [1, n!]`
with `H D = δ I` and all entries of `H` bounded by `n!` (it is `± adj` of a nonsingular `E × E`
row-submatrix of `D`, extended by zero columns).
-/

namespace Lax117284Proofs.IlpClients

open Finset
open scoped Nat

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Clearing denominators: a common integer multiple of a rational vector. -/
theorem exists_int_multiple (β : E → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, ∃ z : ℤ, β i * d = z := by
  refine ⟨∏ i, (β i).den, Finset.prod_pos fun i _ => (β i).den_pos, fun i => ?_⟩
  refine ⟨(β i).num * ∏ i' ∈ univ.erase i, ((β i').den : ℤ), ?_⟩
  push_cast
  rw [← Finset.mul_prod_erase univ (fun i' => ((β i').den : ℚ)) (Finset.mem_univ i)]
  rw [← mul_assoc, Rat.mul_den_eq_num]

/-- Rational independence from integer independence. -/
theorem indep_rat {n : ℕ} (D : Fin n → E → ℤ)
    (hind : ∀ α : E → ℤ, (∀ j, ∑ i, D j i * α i = 0) → α = 0)
    (β : E → ℚ) (hβ : ∀ j, ∑ i, (D j i : ℚ) * β i = 0) : β = 0 := by
  obtain ⟨d, hd, hz⟩ := exists_int_multiple β
  choose z hz using hz
  have hzero : z = 0 := by
    apply hind
    intro j
    apply Int.cast_injective (α := ℚ)
    push_cast
    have : ∑ i, (D j i : ℚ) * (z i : ℚ) = (d : ℚ) * ∑ i, (D j i : ℚ) * β i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hz i]; ring
    rw [this, hβ j, mul_zero]
  funext i
  have h1 := hz i
  rw [hzero] at h1
  simp only [Pi.zero_apply, Int.cast_zero] at h1
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa [hd'] using h1

/-- Selecting `|E|` rows of `D` with a nonsingular square submatrix. -/
theorem exists_rows {n : ℕ} (D : Fin n → E → ℤ)
    (hind : ∀ α : E → ℤ, (∀ j, ∑ i, D j i * α i = 0) → α = 0) :
    ∃ ρ : E → Fin n, Function.Injective ρ ∧
      (Matrix.of fun k i : E => D (ρ k) i).det ≠ 0 := by
  classical
  let Dq : Matrix (Fin n) E ℚ := fun j i => (D j i : ℚ)
  have hinj : Function.Injective Dq.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro β hβ
    exact indep_rat D hind β (fun j => by
      have := congrFun hβ j
      rw [Matrix.mulVecLin_apply] at this
      simpa [Matrix.mulVec, dotProduct, Dq] using this)
  have hrank : Dq.rank = Fintype.card E := by
    unfold Matrix.rank
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ', a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ Dq.row
  have : Finite κ' := Finite.of_injective a ha
  have : Fintype κ' := Fintype.ofFinite κ'
  have hcard : Fintype.card κ' = Fintype.card E := by
    rw [← hrank, Matrix.rank_eq_finrank_span_row, ← hspan]
    exact (finrank_span_eq_card hli).symm
  let e : E ≃ κ' := (Fintype.equivOfCardEq hcard.symm)
  let ρ : E → Fin n := a ∘ e
  refine ⟨ρ, ha.comp e.injective, ?_⟩
  have hli' : LinearIndependent ℚ (Matrix.of fun k i : E => (D (ρ k) i : ℚ)).row := by
    have := hli.comp e e.injective
    exact this
  have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  have hdet := hunit.ne_zero
  intro h0
  apply hdet
  have := (Int.castRingHom ℚ).map_det (Matrix.of fun k i : E => D (ρ k) i)
  rw [h0] at this
  exact this.symm

theorem det_abs_le {F : Type*} [Fintype F] [DecidableEq F] (A : Matrix F F ℤ)
    (hA : ∀ i j, |A i j| ≤ 1) : |A.det| ≤ (Fintype.card F)! := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) (x := (1 : ℤ)) (A := A) hA
  simpa using this

theorem adj_abs_le {F : Type*} [Fintype F] [DecidableEq F] (A : Matrix F F ℤ)
    (hA : ∀ i j, |A i j| ≤ 1) (i j : F) : |A.adjugate i j| ≤ (Fintype.card F)! := by
  rw [Matrix.adjugate_apply]
  apply det_abs_le
  intro i' j'
  by_cases h : i' = j
  · subst h
    simp only [Matrix.updateRow_self, Pi.single_apply]
    split_ifs <;> simp
  · rw [Matrix.updateRow_ne h]; exact hA i' j'

/-- **The integer left inverse.** -/
theorem exists_left_inverse {n : ℕ} (D : Fin n → E → ℤ) (hD : ∀ j i, |D j i| ≤ 1)
    (hind : ∀ α : E → ℤ, (∀ j, ∑ i, D j i * α i = 0) → α = 0) :
    Fintype.card E ≤ n ∧ ∃ (H : E → Fin n → ℤ) (δ : ℕ), 1 ≤ δ ∧ δ ≤ n ! ∧
      (∀ i j, |H i j| ≤ n !) ∧
      ∀ i i', ∑ j, H i j * D j i' = if i = i' then (δ : ℤ) else 0 := by
  classical
  obtain ⟨ρ, hρ, hdet⟩ := exists_rows D hind
  have hcard : Fintype.card E ≤ n := by
    simpa using Fintype.card_le_of_injective ρ hρ
  refine ⟨hcard, ?_⟩
  set Dρ : Matrix E E ℤ := Matrix.of fun k i : E => D (ρ k) i with hDρ
  set s : ℤ := if 0 ≤ Dρ.det then 1 else -1 with hs
  have hs1 : |s| = 1 := by rw [hs]; split_ifs <;> simp
  have hsdet : s * Dρ.det = |Dρ.det| := by
    rw [hs]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  refine ⟨fun i j => s * ∑ k, Dρ.adjugate i k * (if ρ k = j then 1 else 0),
    Dρ.det.natAbs, ?_, ?_, ?_, ?_⟩
  · exact Int.natAbs_pos.mpr hdet
  · have h1 := det_abs_le Dρ (fun i j => hD _ _)
    have h2 : ((Dρ.det.natAbs : ℕ) : ℤ) ≤ ((Fintype.card E)! : ℕ) := by
      rw [Int.natCast_natAbs]; exact h1
    exact (by exact_mod_cast h2 : Dρ.det.natAbs ≤ (Fintype.card E)!).trans
      (Nat.factorial_le hcard)
  · intro i j
    rw [abs_mul, hs1, one_mul]
    by_cases hj : ∃ k0, ρ k0 = j
    · obtain ⟨k0, hk0⟩ := hj
      rw [Finset.sum_eq_single k0]
      · simp only [hk0, if_true, mul_one]
        exact (adj_abs_le Dρ (fun i j => hD _ _) i k0).trans (by exact_mod_cast Nat.factorial_le hcard)
      · intro k _ hk
        have : ρ k ≠ j := fun h => hk (hρ (h.trans hk0.symm))
        simp [this]
      · intro h; exact absurd (Finset.mem_univ k0) h
    · have hj' : ∀ k, ρ k ≠ j := fun k h => hj ⟨k, h⟩
      simp [hj']
  · intro i i'
    have hmul : Dρ.adjugate * Dρ = Dρ.det • (1 : Matrix E E ℤ) := Matrix.adjugate_mul Dρ
    have hentry := congrFun (congrFun hmul i) i'
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at hentry
    calc ∑ j, (s * ∑ k, Dρ.adjugate i k * (if ρ k = j then 1 else 0)) * D j i'
        = s * ∑ k, Dρ.adjugate i k * ∑ j, (if ρ k = j then 1 else 0) * D j i' := by
          have e1 : ∀ j, (s * ∑ k, Dρ.adjugate i k * (if ρ k = j then (1:ℤ) else 0)) * D j i' =
              s * ∑ k, Dρ.adjugate i k * ((if ρ k = j then (1:ℤ) else 0) * D j i') := by
            intro j
            rw [mul_assoc, Finset.sum_mul]
            congr 1
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [Finset.sum_congr rfl (fun j _ => e1 j), ← Finset.mul_sum, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
      _ = s * ∑ k, Dρ.adjugate i k * Dρ k i' := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          simp [hDρ]
      _ = if i = i' then ((Dρ.det.natAbs : ℕ) : ℤ) else 0 := by
          rw [hentry]
          by_cases h : i = i'
          · simp only [h, if_true, mul_one]
            rw [hsdet, Int.natCast_natAbs]
          · simp [h]

end Lax117284Proofs.IlpClients
