import Lax759944.RamPolytime
import Lax808846Proofs.Transfer
import Mathlib.Data.Nat.Size

/-!
The bit size of a word (`lax-759944`'s `bitSize`) bounds its length and its entries, and a
program whose values fit into `d · bitSize x + K` bits and whose running time is a polynomial in
`bitSize x` is a polynomial-time word RAM computation in the sense of `lax-759944`
(`ramPolytime_of_wordlen`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

theorem bitSize_cons (a : ℕ) (x : List ℕ) :
    bitSize (a :: x) = (Nat.bits a).length + 1 + bitSize x := by
  simp [bitSize, encode, encodeNat, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_le_bitSize (x : List ℕ) : x.length ≤ bitSize x := by
  induction x with
  | nil => simp [bitSize, encode]
  | cons a x ih =>
      rw [bitSize_cons]
      simp only [List.length_cons]
      omega

theorem bits_length_add_one_le_bitSize_of_mem {a : ℕ} {x : List ℕ}
    (ha : a ∈ x) : a.bits.length + 1 ≤ bitSize x := by
  induction x with
  | nil => simp at ha
  | cons b x ih =>
      rw [bitSize_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · have := ih ha
        omega

theorem mem_lt_two_pow_bitSize_add_one {a : ℕ} {x : List ℕ} (ha : a ∈ x) :
    a < 2 ^ (bitSize x + 1) := by
  have haSize : a < 2 ^ a.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size_self a
  exact haSize.trans_le (Nat.pow_le_pow_right (by omega)
    (by have := bits_length_add_one_le_bitSize_of_mem ha; omega))

theorem length_lt_two_pow_bitSize_add_one (x : List ℕ) :
    x.length < 2 ^ (bitSize x + 1) := by
  have hlen := length_le_bitSize x
  have hpow := Nat.lt_two_pow_self (n := bitSize x)
  exact hlen.trans_lt (hpow.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))

/-- **The bridge to `RamPolytime`**: values below `2 ^ (d · bitSize x + K)`, a run at every
word length from `d · bitSize x + K + 1` on, within a polynomial in the bit size. -/
theorem ramPolytime_of_wordlen {f : List ℕ → List ℕ} {prog : Program} {d K : ℕ}
    (time : Polynomial ℕ) (hd : 1 ≤ d)
    (hout : ∀ x, ∀ v ∈ f x, v < 2 ^ (d * bitSize x + K))
    (hrun : ∀ (w : ℕ) (x : List ℕ), d * bitSize x + (K + 1) ≤ w →
        ∃ t ≤ time.eval (bitSize x), RunsTo w prog (x.length :: x) (f x) t) :
    RamPolytime f := by
  refine ⟨prog, Polynomial.C d * Polynomial.X + Polynomial.C (K + 1), time,
    fun x => ⟨?_, ?_⟩⟩
  · intro a ha
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rcases List.mem_append.mp ha with hin | hin
    · have hlt : a < 2 ^ (bitSize x + 1) := by
        rcases List.mem_cons.mp hin with rfl | hin'
        · exact length_lt_two_pow_bitSize_add_one x
        · exact mem_lt_two_pow_bitSize_add_one hin'
      calc a < 2 ^ (bitSize x + 1) := hlt
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by
            have : bitSize x ≤ d * bitSize x := Nat.le_mul_of_pos_left _ hd
            omega)
    · calc a < 2 ^ (d * bitSize x + K) := hout x a hin
        _ ≤ 2 ^ (d * bitSize x + (K + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  · intro w hw
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C] at hw
    exact hrun w x hw

end Lax117284Proofs.Bipartite.Ram2
