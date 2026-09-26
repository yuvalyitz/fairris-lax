import Lax391470Proofs.RamToTuring
import Lax117284Proofs.TwoSAT.Machine.Language

/-!
From a polynomial-time word RAM computation of the decision, on the zeros and ones of the
word, to membership of 2-SAT in the class P: the RAM/Turing equivalence of `lax-759944` and the
two fixed translations of `lax-391470` give a polynomial-time Turing machine on the binary word
itself, and a machine writing the one bit of the answer is a machine for the class.
-/

namespace Lax117284Proofs.TwoSAT.Machine.ToP

open Lax434930.PolynomialTime Lax117284.TwoSatCNF Lax759944.RamPolytime
open Lax391470Proofs.Bits
open scoped Classical

/-- The decision, as a map of binary words. -/
noncomputable def dec (w : Word) : Word := [decide (w ∈ TwoSAT)]

/-- The decision on the zeros and ones of a word: what the machine computes. -/
noncomputable def decBits (y : List ℕ) : List ℕ := natBits (dec (bitsOf y))

theorem decBits_natBits (w : Word) : decBits (natBits w) = natBits (dec w) := by
  unfold decBits; rw [bitsOf_natBits]

theorem decBits_eq (y : List ℕ) : decBits y = if bitsOf y ∈ TwoSAT then [1] else [0] := by
  unfold decBits dec natBits
  split <;> simp_all

/-- **2-SAT is in P once the decision is a polynomial-time RAM computation on bits.** -/
theorem mem_P_of_ram (h : RamPolytime decBits) : TwoSAT ∈ P := by
  obtain ⟨c⟩ := Lax391470Proofs.RamToTuring.polyTime_of_ram h decBits_natBits
  refine ⟨fun w => decide (w ∈ TwoSAT), fun w => by simp, ⟨?_⟩⟩
  exact
    { tm := c.tm
      inputAlphabet := c.inputAlphabet
      outputAlphabet := c.outputAlphabet
      time := c.time
      outputsFun := fun w => c.outputsFun w }

end Lax117284Proofs.TwoSAT.Machine.ToP
