import Lax888481Proofs.Theorem2Assembly
import Lax888481Proofs.Theorem2
import Lax888481Proofs.Sat34
import Lax345332Proofs.Reduction
import Lax345332Proofs.Final

/-!
Three citations of an axiom stand between `lax-888481`'s `Theorem2Assembly.npHard` and the
proof each axiom already has, elsewhere in an already-published proofs package:

* `Theorem2Assembly.npHard` cites the concept axiom `Lax888481.SatVariant.sat34_npHard`,
  although `lax-888481` discharges it itself, from `lax-345332`, in
  `Lax888481Proofs.Sat34.sat34_npHard` — `Theorem2Assembly.lean` simply never imports
  `Sat34.lean`.
* `Sat34.sat34_npHard` in turn cites the concept axiom `Lax345332.ThreeFourSat.npHard`,
  although `lax-345332` discharges that one too, in `Lax345332Proofs.Reduction.npHard`
  (which this submission already requires, for its own `BoundedSat` discharge).
* `Reduction.npHard` in turn cites the concept axiom `Lax345332.Construction.reduce_polyTime`,
  although `lax-345332` discharges that one too, in `Lax345332Proofs.Final.reduce_polyTime` —
  `Reduction.lean` simply never imports `Final.lean` (which imports `Reduction.lean`, so the
  dependency cannot run the other way).

Rather than cite any of the three axioms here, this file recomposes all three arguments
verbatim with their one citation each swapped, using only pieces their own packages already
prove and export. The first two gaps have also been fixed directly, upstream, in a local
checkout of `lax-888481`'s `Theorem2Assembly.lean` and `Sat34.lean`, pending that
submission's next push. The third gap, inside `lax-345332` itself, is not: `Reduction.lean`
cannot import `Final.lean` without a cycle (`Final.lean` already imports `Reduction.lean`
transitively through `Main.lean`), so fixing it upstream needs a small restructuring rather
than an added import, left for whoever next touches that submission; the workaround here
needs nothing from `lax-345332` beyond what it already exports.
-/

namespace Lax117284Proofs.JitHard

open Lax888481.NPHardness Lax888481.Scheduling
open Lax888481Proofs.Theorem2Assembly

/-- **Tovey's theorem, with the running time of its reduction taken from its proof.**
Composed exactly as `Lax345332Proofs.Reduction.npHard` is, citing
`Lax345332Proofs.Final.reduce_polyTime` in place of the concept axiom
`Lax345332.Construction.reduce_polyTime`. -/
theorem threeFourSat_npHard_wired :
    ∀ A, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
      Lax429075.Reductions.ManyOne A Lax345332.ThreeFourSat.SAT34 :=
  fun A hA => Lax345332Proofs.Reduction.manyOne_trans (Lax429075.SATHard.hardness A hA)
    ⟨Lax345332.Construction.reduce, Lax345332Proofs.Final.reduce_polyTime,
      Lax345332Proofs.Reduction.reduce_correct⟩

/-- **Tovey's hardness of `lax-888481`'s `(3,4)`-SAT, with the hardness of `lax-345332`'s
taken from its proof.** Composed exactly as `Sat34.sat34_npHard` is, citing
`threeFourSat_npHard_wired` in place of the concept axiom `Lax345332.ThreeFourSat.npHard`. -/
theorem sat34_npHard_wired :
    ∀ A, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
      Lax429075.Reductions.ManyOne A Lax888481.SatVariant.SAT34 := by
  intro A hA
  rw [Lax888481Proofs.Sat34.sat34_eq]
  exact threeFourSat_npHard_wired A hA

/-- **`lax-888481`'s Theorem 2, with Tovey's hardness taken from its proof.** Composed exactly
as `Theorem2Assembly.npHard` is, citing `sat34_npHard_wired` in place of the concept axiom
`SatVariant.sat34_npHard`. -/
theorem npHard_allSchedulable_wired : NPHard Instance.AllSchedulable := by
  intro A hA
  obtain ⟨g, ⟨tg⟩, hg⟩ := sat34_npHard_wired A hA
  obtain ⟨t⟩ := instOf_polytime Lax888481Proofs.Theorem2.parts
  obtain ⟨c⟩ := Lax434930Proofs.PolynomialComposition.comp tg t
  exact ⟨instOf Lax888481Proofs.Theorem2.parts ∘ g, ⟨c⟩, fun x =>
    (hg x).trans (instOf_correct Lax888481Proofs.Theorem2.parts (g x))⟩

end Lax117284Proofs.JitHard
