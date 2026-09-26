import Mathlib

/-!
# Sets of days as numbers

The days on which a client is served form a set of days, written as a number whose bit `d` says
whether day `d` is in the set. The dynamic program's digits are these numbers.
-/

namespace Lax117284Proofs.TwMask

/-- The number whose bit `d`, for `d < k`, is `f d`. -/
def bitsOf (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitsOf f k + if f k then 2 ^ k else 0

lemma bitsOf_lt (f : ℕ → Bool) : ∀ k, bitsOf f k < 2 ^ k
  | 0 => by simp [bitsOf]
  | k + 1 => by
    have : bitsOf f k < 2 ^ k := bitsOf_lt f k
    simp only [bitsOf, pow_succ]
    split_ifs <;> omega

lemma testBit_bitsOf (f : ℕ → Bool) : ∀ (k d : ℕ),
    (bitsOf f k).testBit d = (decide (d < k) && f d)
  | 0, d => by simp [bitsOf]
  | k + 1, d => by
    have ih := testBit_bitsOf f k d
    have hlt := bitsOf_lt f k
    have hk : (bitsOf f k).testBit k = false := Nat.testBit_lt_two_pow hlt
    simp only [bitsOf]
    by_cases hf : f k = true
    · simp only [hf, if_true]
      rw [Nat.add_comm]
      rcases lt_trichotomy d k with h | h | h
      · rw [Nat.testBit_two_pow_add_gt h, ih]; simp [h, show d < k + 1 by omega]
      · subst h; rw [Nat.testBit_two_pow_add_eq, hk]; simp [hf]
      · have : (2 ^ k + bitsOf f k).testBit d = false := by
          apply Nat.testBit_eq_false_of_lt
          calc 2 ^ k + bitsOf f k < 2 ^ k + 2 ^ k := by omega
            _ = 2 ^ (k + 1) := by ring
            _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [this]; simp; omega
    · have hf' : f k = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, if_false, Nat.add_zero, ih]
      rcases lt_trichotomy d k with h | h | h
      · simp [h, show d < k + 1 by omega]
      · subst h; simp [hf']
      · have h1 : ¬ d < k := by omega
        have h2 : ¬ d < k + 1 := by omega
        simp [h1, h2]

/-- Two numbers below `2 ^ k` with the same bits below `k` are equal. -/
lemma eq_of_bits {x y k : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ d < k, x.testBit d = y.testBit d) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro d
  by_cases hd : d < k
  · exact h d hd
  · have hp : 2 ^ k ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy hp)]

/-- The number of bits below `m` that are set. -/
def popc (m x : ℕ) : ℕ := ∑ d ∈ Finset.range m, if x.testBit d then 1 else 0

end Lax117284Proofs.TwMask
