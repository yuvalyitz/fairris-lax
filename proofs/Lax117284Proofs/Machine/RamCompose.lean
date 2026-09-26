import Lax117284Proofs.Machine.RamToTuring

/-!
Three word RAM computations, one after the other, decide a language of binary words in
polynomial time: the first maps the zeros and ones of the input to a list of numbers, the second
maps that list to another, and the third maps it to the one-number answer.
-/

namespace Lax117284Proofs.Machine.RamCompose

open Turing Lax434930.PolynomialTime Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax117284Proofs.Machine.Bits

theorem polyTime_of_ram3 {g1 g2 g3 : List ℕ → List ℕ} (h1 : RamPolytime g1)
    (h2 : RamPolytime g2) (h3 : RamPolytime g3) {f : Word → Word}
    (h : ∀ w, bitsOf (g3 (g2 (g1 (natBits w)))) = f w) :
    Nonempty (TM2ComputableInPolyTime id id f) := by
  obtain ⟨t0⟩ := Lax117284Proofs.Machine.TMToNats.toNats
  obtain ⟨t1⟩ := (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g1).mp h1
  obtain ⟨t2⟩ := (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g2).mp h2
  obtain ⟨t3⟩ := (Lax759944Proofs.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime g3).mp h3
  obtain ⟨t4⟩ := Lax117284Proofs.Machine.TMToBits.toBits
  obtain ⟨c01⟩ := Lax117284Proofs.Machine.TMCompose.comp t0 t1
  obtain ⟨c012⟩ := Lax117284Proofs.Machine.TMCompose.comp c01 t2
  obtain ⟨c0123⟩ := Lax117284Proofs.Machine.TMCompose.comp c012 t3
  obtain ⟨c⟩ := Lax117284Proofs.Machine.TMCompose.comp c0123 t4
  refine ⟨{ tm := c.tm, inputAlphabet := c.inputAlphabet, outputAlphabet := c.outputAlphabet,
            time := c.time, outputsFun := fun w => ?_ }⟩
  have hc := c.outputsFun w
  simp only [Function.comp_apply, h] at hc
  exact hc

/-- A language decided by three word RAM computations in a row belongs to `P`. -/
theorem mem_P_of_ram3 {V : Language} (f : Word → Bool) (hf : ∀ w, f w = true ↔ w ∈ V)
    {g1 g2 g3 : List ℕ → List ℕ} (h1 : RamPolytime g1) (h2 : RamPolytime g2)
    (h3 : RamPolytime g3)
    (h : ∀ w, g3 (g2 (g1 (natBits w))) = [if f w then 1 else 0]) : V ∈ P := by
  obtain ⟨c⟩ := polyTime_of_ram3 h1 h2 h3 (f := fun w => [f w]) (fun w => by
    rw [h w]; cases f w <;> rfl)
  refine ⟨f, hf, ⟨?_⟩⟩
  exact
    { tm := c.tm
      inputAlphabet := c.inputAlphabet
      outputAlphabet := c.outputAlphabet
      time := c.time
      outputsFun := fun w => c.outputsFun w }

end Lax117284Proofs.Machine.RamCompose
