import Lax117284.BipartiteKuhnCorrect
import Lax117284Proofs.Bipartite.Maximum

/-!
The three relation-level statements of the concept `Lax117284.BipartiteKuhnCorrect`, read off the
maximality argument of `Maximum.lean`: Kuhn's algorithm (`Lax117284.BipartiteKuhn.kuhn`) returns a
matching, no matching is larger, and it saturates the left side exactly when some matching does.
-/

namespace Lax117284Proofs.Bipartite.KuhnCorrect

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching

variable {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (adj : L → R → Prop) [DecidableRel adj]

omit [DecidableEq L] in
/--
---
conclusion: Lax117284.BipartiteKuhnCorrect.kuhn_isMatching
---
The invariant of the run (`Maximum.kuhn_spec`): the matching the algorithm keeps always respects
the graph and is injective.
-/
theorem kuhn_isMatching : Respects adj (kuhn adj) ∧ InjOnSupport (kuhn adj) := by
  classical
  exact (Lax117284Proofs.Bipartite.Maximum.kuhn_maximum adj).1

omit [DecidableEq L] in
/--
---
conclusion: Lax117284.BipartiteKuhnCorrect.kuhn_maximum
---
At the end every left vertex is matched or failed, and a matching with that property is maximum
by counting (`Maximum.size_le_of_saturating`), without Berge's lemma.
-/
theorem kuhn_maximum (μ : R → Option L) (hres : Respects adj μ) (hinj : InjOnSupport μ) :
    size μ ≤ size (kuhn adj) := by
  classical
  exact (Lax117284Proofs.Bipartite.Maximum.kuhn_maximum adj).2 μ ⟨hres, hinj⟩

omit [DecidableEq L] in
/--
---
conclusion: Lax117284.BipartiteKuhnCorrect.kuhn_saturates_iff
---
A saturating result gives the injection `l ↦ its right vertex`; conversely a left vertex the
algorithm leaves unmatched has failed, and the right vertices reachable from a failed vertex are
fewer than the left ones, which no injection respecting the graph allows.
-/
theorem kuhn_saturates_iff :
    (∀ l, Matched (kuhn adj) l) ↔ ∃ f : L → R, Function.Injective f ∧ ∀ l, adj l (f l) := by
  classical
  exact Lax117284Proofs.Bipartite.Maximum.kuhn_full_iff adj

end Lax117284Proofs.Bipartite.KuhnCorrect
