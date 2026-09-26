import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
Numbers with prescribed bits, and the two encodings of Theorem 4's integer program: a subset of `n`
clients as a number below `2 ^ n`, a day type (a conflict relation on `n` clients) as a number below
`2 ^ (n * n)`.
-/

namespace Lax117284Proofs.ClientsILP

/-- The number whose bit `q` is `f q` for `q < P`. -/
def bitsNum (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | P + 1 => bitsNum f P + if f P then 2 ^ P else 0

theorem bitsNum_lt (f : ℕ → Bool) : ∀ P, bitsNum f P < 2 ^ P
  | 0 => by simp [bitsNum]
  | P + 1 => by
    have := bitsNum_lt f P
    simp only [bitsNum, pow_succ]
    split <;> omega

theorem testBit_bitsNum (f : ℕ → Bool) :
    ∀ (P q : ℕ), (bitsNum f P).testBit q = if q < P then f q else false
  | 0, q => by simp [bitsNum]
  | P + 1, q => by
    have ih := testBit_bitsNum f P q
    have hlt := bitsNum_lt f P
    have hlt' := bitsNum_lt f (P + 1)
    simp only [bitsNum]
    rcases lt_trichotomy q P with hq | hq | hq
    · have h1 : q < P + 1 := by omega
      rw [if_pos h1]
      rw [if_pos hq] at ih
      by_cases hf : f P = true
      · rw [if_pos hf, add_comm, Nat.testBit_two_pow_add_gt hq]; exact ih
      · rw [if_neg hf, add_zero]; exact ih
    · subst hq
      have h1 : q < q + 1 := by omega
      rw [if_pos h1]
      have hb := Nat.testBit_lt_two_pow hlt
      by_cases hf : f q = true
      · rw [if_pos hf, add_comm, Nat.testBit_two_pow_add_eq, hb]; simp [hf]
      · rw [if_neg hf, add_zero, hb]; simpa using hf
    · have h1 : ¬ q < P + 1 := by omega
      rw [if_neg h1]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- A number below `2 ^ P` is determined by its bits. -/
theorem eq_bitsNum {x P : ℕ} (hx : x < 2 ^ P) : x = bitsNum (fun q => x.testBit q) P := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_bitsNum]
  split_ifs with h
  · rfl
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem bitsNum_congr {f g : ℕ → Bool} {P : ℕ} (h : ∀ q < P, f q = g q) : bitsNum f P = bitsNum g P := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_bitsNum, testBit_bitsNum]
  split_ifs with hq
  · exact h q hq
  · rfl

end Lax117284Proofs.ClientsILP
