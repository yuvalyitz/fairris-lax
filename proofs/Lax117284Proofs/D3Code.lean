import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The code of a state: the digits of a number in the base one more than the number of clients.
-/

namespace Lax117284Proofs.D3Code

/-- The code of a vector of digits. -/
def enc (b : ℕ) {m : ℕ} (v : Fin m → ℕ) : ℕ := ∑ i : Fin m, v i * b ^ (i : ℕ)

/-- The digit at a position of a number. -/
def dig (b s i : ℕ) : ℕ := s / b ^ i % b

variable {b : ℕ}

lemma enc_succ {m : ℕ} (v : Fin (m + 1) → ℕ) :
    enc b v = v 0 + b * enc b (fun i : Fin m => v i.succ) := by
  unfold enc
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma enc_lt (hb : 0 < b) : ∀ {m : ℕ} (v : Fin m → ℕ), (∀ i, v i < b) → enc b v < b ^ m
  | 0, v, _ => by simp [enc]
  | m + 1, v, h => by
    rw [enc_succ]
    have ih := enc_lt hb (fun i : Fin m => v i.succ) (fun i => h i.succ)
    have h0 := h 0
    rw [pow_succ]
    nlinarith

lemma dig_enc (hb : 1 < b) : ∀ {m : ℕ} (v : Fin m → ℕ), (∀ i, v i < b) →
    ∀ i : Fin m, dig b (enc b v) i = v i
  | 0, v, _, i => i.elim0
  | m + 1, v, h, i => by
    rw [enc_succ]
    have h0 := h 0
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp [dig, Nat.mod_eq_of_lt h0]
    · have ih := dig_enc hb (fun i : Fin m => v i.succ) (fun i => h i.succ) j
      have e1 : (v 0 + b * enc b (fun i : Fin m => v i.succ)) / b =
          enc b (fun i : Fin m => v i.succ) := by
        rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h0, Nat.zero_add]
      unfold dig at ih ⊢
      rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, e1]
      exact ih

/-- **Changing a digit changes the code by its weight.** -/
lemma enc_update {m : ℕ} (v : Fin m → ℕ) (i : Fin m) (a : ℕ) :
    enc b (Function.update v i a) + v i * b ^ (i : ℕ) = enc b v + a * b ^ (i : ℕ) := by
  unfold enc
  rw [← Finset.add_sum_erase Finset.univ (fun j : Fin m => Function.update v i a j * b ^ (j : ℕ))
      (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j : Fin m => v j * b ^ (j : ℕ)) (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, Function.update v i a j * b ^ (j : ℕ) =
      ∑ j ∈ Finset.univ.erase i, v j * b ^ (j : ℕ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [this]
  simp only [Function.update_self]
  ring

end Lax117284Proofs.D3Code
