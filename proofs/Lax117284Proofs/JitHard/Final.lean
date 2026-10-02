import Lax117284Proofs.Machine.JitHardFinal
import Lax117284Proofs.Machine.JitHardTM
import Lax117284Proofs.JitHard.Code
import Lax117284Proofs.SourceInjectivity
import Lax117284Proofs.JitHard.Sat34Wired

/-!
Just-in-time scheduling on unrelated machines is NP-hard, by a reduction from interval scheduling
with eligible machine sets, whose NP-hardness is the second theorem of `lax-888481`, imported here
as the proof `Sat34Wired.npHard_allSchedulable_wired` rather than cited as an axiom, so that this
submission discharges it too.
-/

namespace Lax117284Proofs.JitHard

open Turing Lax434930.PolynomialTime Lax429075.Reductions Lax117284.Problems
open Lax117284Proofs.Machine.Bits

/-- **The program computes the image of an instance on the code of the instance.** -/
theorem redBits_encode (I : SchedI) :
    Lax117284Proofs.Machine.JitHardFinal.W.redBits (natBits (Lax888481.BinaryEncoding.encodeInstance I)) =
      natBits (Lax117284.JustInTime.encodeInstance (toJIT I)) := by
  unfold Lax117284Proofs.Machine.WrapT.WrapT.redBits
  rw [bitsOf_natBits]
  show natBits (Lax117284Proofs.Machine.JitHardFinal.redH _) = _
  rw [Code.encode_eq I, Lax117284Proofs.Machine.JitHardFinal.redH_code _
    (Lax117284Proofs.Machine.JitHardFormat.conforms_of_shape (Code.shape I)),
    Lax117284Proofs.Machine.JitHardFormat.vals_toksH (Code.shape I), Code.outH_code I]

/-- **The reduction is polynomial-time computable on the codes of the instances.** -/
theorem polyTime_toJIT :
    Nonempty (TM2ComputableInPolyTime Lax888481.BinaryEncoding.encodeInstance id
      (fun I : SchedI => Lax117284.JustInTime.encodeInstance (toJIT I))) :=
  Lax117284Proofs.Machine.JitHardTM.polyTime_of_ram_dom
    Lax117284Proofs.Machine.JitHardFinal.ramPolytime redBits_encode

/--
---
conclusion: Lax117284.JustInTime.allJIT_npHard
---
Deciding whether every job of an instance of `R || ∑_j Z_j` can be just in time is NP-hard.
Every language in NP reduces to interval scheduling with eligible machine sets, by the second
theorem of `lax-470956`, and that problem reduces to this one: every job is given the due date
`d_j + 1` and the processing time it has, and on a machine it may not use, the processing time
`d_j + 1`, so that it covers the time point `1`, which one extra job per machine, due at `1` and
of length `1` on every machine, occupies. Those extra jobs overlap one another and so sit on
distinct machines, hence on all of them, and a job that sits on a machine it may not use would
overlap the extra job of that machine. The map is computed by a word RAM program, which is
polynomial in the length of the code, since the extra jobs are only added when there is a job,
and then there are as many machines as the matrix of the input has columns.
-/
theorem allJIT_npHard : Lax117284.Problems.NPHard Lax117284.JustInTime.AllJIT := by
  intro A hA
  obtain ⟨f, ⟨hf⟩, hfc⟩ := npHard_allSchedulable_wired A hA
  obtain ⟨t⟩ := polyTime_toJIT
  obtain ⟨c⟩ := Lax434930Proofs.PolynomialComposition.comp hf t
  refine ⟨_, ⟨c⟩, fun x => ?_⟩
  rw [hfc x, allSchedulable_iff]
  constructor
  · intro h
    exact ⟨toJIT (f x), rfl, h⟩
  · rintro ⟨R, hR, hall⟩
    have := Lax117284Proofs.SourceInjectivity.jit_encode_inj hR
    subst this
    exact hall

example : type_of% @Lax117284.JustInTime.allJIT_npHard := allJIT_npHard

end Lax117284Proofs.JitHard
