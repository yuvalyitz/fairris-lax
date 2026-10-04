import Lax808846.RamComputes
import Lax759944.RamPolytime
import Lax759944Proofs.Encoding

/-! ### `Lax117284Proofs.Machine.RamBridge` -/

section
/-!
From a running-time statement in the archive's word RAM style to the polynomial-time
predicate of the RAM/Turing equivalence.

The two say the same thing in different currencies. `Lax808846` measures the input by
its length as a list of numbers and states an explicit bound at every word length that
admits the input; `Lax759944` measures it by its bit size, prefixes the physical input
with its length, and asks for a polynomial. This file converts one into the other once,
so that a program written and costed in the first style can be cited in the second.
-/

namespace Lax117284Proofs.Machine.RamBridge

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax759944Proofs.Encoding

end Lax117284Proofs.Machine.RamBridge

end

/-! ### `Lax117284Proofs.Machine.RamBridge2` -/

section
/-!
The bridge to `RamPolytime`, in the form a program with exponentially large values needs:
the run hypothesis is handed the word length itself.
-/

namespace Lax117284Proofs.Machine.RamBridge2

open Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax759944Proofs.Encoding

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

end Lax117284Proofs.Machine.RamBridge2

end
