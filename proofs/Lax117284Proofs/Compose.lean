import Lax429075.Reductions
import Lax434930Proofs.PolynomialComposition
import Lax117284.Problems

/-!
Polynomial-time many-one reductions compose, and hardness passes along them.
-/

namespace Lax117284Proofs.Compose

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime Lax429075.Reductions

theorem manyOne_trans {A B C : Language} (hAB : ManyOne A B) (hBC : ManyOne B C) :
    ManyOne A C := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hAB
  obtain ⟨g, ⟨hg⟩, hgc⟩ := hBC
  refine ⟨g ∘ f, Lax434930Proofs.PolynomialComposition.comp hf hg, fun x => ?_⟩
  rw [hfc x, hgc (f x)]
  rfl

/-- A language that reduces to a language in `P` in polynomial time is in `P`. -/
theorem mem_P_of_manyOne {A B : Language} (hAB : ManyOne A B) (hB : B ∈ P) : A ∈ P := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hAB
  obtain ⟨g, hg, ⟨hgm⟩⟩ := hB
  refine ⟨g ∘ f, fun w => ?_, Lax434930Proofs.PolynomialComposition.comp hf hgm⟩
  show g (f w) = true ↔ w ∈ A
  rw [hg (f w), hfc w]

theorem npHard_of_manyOne {A B : Language} (hA : Lax117284.Problems.NPHard A)
    (hAB : ManyOne A B) : Lax117284.Problems.NPHard B :=
  fun L hL => manyOne_trans (hA L hL) hAB

end Lax117284Proofs.Compose
