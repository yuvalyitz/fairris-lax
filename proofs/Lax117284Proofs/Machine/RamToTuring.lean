import Lax117284Proofs.Machine.TMCompose
import Lax117284Proofs.Machine.TMToNats
import Lax117284Proofs.Machine.TMToBits

/-!
A map on binary words that a word RAM computes in polynomial time, on the zeros and ones
of its input, is polynomial-time computable on a Turing machine.
-/

namespace Lax117284Proofs.Machine.RamToTuring

open Turing Lax434930.PolynomialTime Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax117284Proofs.Machine.Bits

theorem polyTime_of_ram {f : Word → Word} {g : List ℕ → List ℕ} (hg : RamPolytime g)
    (h : ∀ w, g (natBits w) = natBits (f w)) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨t1⟩ := Lax117284Proofs.Machine.TMToNats.toNats
  obtain ⟨t2⟩ :=
    (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g).mp hg
  obtain ⟨t3⟩ := Lax117284Proofs.Machine.TMToBits.toBits
  obtain ⟨c12⟩ := Lax117284Proofs.Machine.TMCompose.comp t1 t2
  obtain ⟨c⟩ := Lax117284Proofs.Machine.TMCompose.comp c12 t3
  refine ⟨{ tm := c.tm, inputAlphabet := c.inputAlphabet, outputAlphabet := c.outputAlphabet,
            time := c.time, outputsFun := fun w => ?_ }⟩
  have hc := c.outputsFun w
  simp only [Function.comp_apply, h, bitsOf_natBits] at hc
  exact hc

end Lax117284Proofs.Machine.RamToTuring
