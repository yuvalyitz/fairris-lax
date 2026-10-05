import Lax117284.Bodlaender
import Lax689794.Bodlaender

/-!
Bodlaender's theorem with Kloks' niceness for the overall conflict graph of an instance, from the
theorem for an arbitrary graph on `Fin n`, `Lax689794.Bodlaender.niceDecomposition_computable` of the registered
submission lax-689794 (proved there).

The two statements differ only in that the concept `Bodlaender` fixes the graph to be the
overall conflict graph of an instance `I` (on `Fin I.clients`) and carries its own copies of the
word definitions. The copies are the same functions: the bag of a node is equal to that of
`Lax689794.GraphWords` (by induction), and the child relation and the tree of the nodes agree by
unfolding, so a word which encodes the overall conflict graph, and a nice decomposition of it, in
one reading are so in the other.
-/

namespace Lax117284Proofs.BodlaenderProved

open Lax117284.Scheduling Lax117284.ConflictGraph

/-- The bag of a node is the same in the two copies of the definition. -/
theorem bagAt_eq (n : ℕ) (D : List ℕ) (i : ℕ) :
    Lax117284.Bodlaender.bagAt n D i = Lax689794.GraphWords.bagAt n D i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Lax117284.Bodlaender.bagAt, Lax689794.GraphWords.bagAt, ih]
    rfl

/-- A word of the overall conflict graph in the sense of `Bodlaender` is one in the sense of `GraphWords`. -/
theorem encodes {g : List ℕ} {I : Instance} (h : Lax117284.Bodlaender.EncodesGraph g I) :
    Lax689794.GraphWords.EncodesGraph g (overallGraph I) :=
  ⟨h.length_eq, h.head_eq, h.adj_eq⟩

/-- A nice decomposition of the overall conflict graph in the sense of `GraphWords` is one in the
sense of `Bodlaender`. -/
theorem niceDecomposition {I : Instance} {w : ℕ} {D : List ℕ}
    (h : Lax689794.GraphWords.NiceDecomposition (overallGraph I) w D) :
    Lax117284.Bodlaender.NiceDecomposition I w D := by
  have hb : Lax117284.Bodlaender.bagAt = Lax689794.GraphWords.bagAt := by
    funext n D i
    exact bagAt_eq n D i
  refine ⟨h.length_eq, h.nonempty, ?_, h.parent, h.isTree, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hb]
    exact h.shape i hi
  · intro v
    rw [hb]
    exact h.covers v
  · intro u v huv
    rw [hb]
    exact h.edges u v huv
  · intro v
    rw [hb]
    exact h.connected v
  · intro i hi
    rw [hb]
    exact h.width i hi

/--
---
conclusion: Lax117284.Bodlaender.niceDecomposition_computable
---
Bodlaender's theorem with Kloks' niceness for the overall conflict graph of an instance, on a word
RAM: the case of `Lax689794.Bodlaender.niceDecomposition_computable` of lax-689794, which runs the exact
Bodlaender–Kloks algorithm on a verified virtual machine, for the graph `overallGraph I` on the
`I.clients` vertices.
-/
theorem niceDecomposition_computable_proved :
    type_of% @Lax117284.Bodlaender.niceDecomposition_computable := by
  obtain ⟨prog, c, h⟩ := Lax689794.Bodlaender.niceDecomposition_computable
  refine ⟨prog, c, fun W w g I hg hguard => ?_⟩
  obtain ⟨out, t, ht, hrun, hout⟩ := h W w I.clients (overallGraph I) g (encodes hg) hguard
  refine ⟨out, t, ht, hrun, ?_⟩
  rcases hout with hout | ⟨D, hD, hND⟩
  · exact Or.inl hout
  · exact Or.inr ⟨D, hD, niceDecomposition hND⟩

end Lax117284Proofs.BodlaenderProved

example : type_of% @Lax117284.Bodlaender.niceDecomposition_computable :=
  Lax117284Proofs.BodlaenderProved.niceDecomposition_computable_proved
