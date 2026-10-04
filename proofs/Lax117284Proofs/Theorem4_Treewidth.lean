import Lax117284.Bodlaender
import Lax117284.Theorem4
import Lax117284Proofs.Machine.TwFinal
import Lax117284Proofs.BodlaenderProved

/-!
Theorem 4, second bullet: the problem is fixed-parameter tractable with respect to the number of
days plus the treewidth of the overall conflict graph.

The algorithm, on the word of an instance and its fairness parameter: read the word and test, from
its length, the largest width `w` for which a nice tree decomposition of that width can be
afforded (the guard). If there is one, build the adjacency matrix of the overall conflict graph,
run the cited program of Bodlaender and Kloks on it (an arbitrary word RAM program, so an
interpreter for word RAM programs written in IMP+ runs it), and if it returns a nice tree
decomposition, run the dynamic program over it, whose tables are indexed by the sets of days of the
clients of a bag and whose size is at most the length of the word. Otherwise, and when the guard
admits no width, enumerate the schedules: this is only done on a word whose length is bounded by a
function of the number of days and the treewidth. An instance with no day is answered in constant
time.
-/

namespace Lax117284Proofs.TreewidthReal

open Lax117284.ParameterizedComplexity Lax117284Proofs.Machine

/--
---
conclusion: Lax117284.Theorem4.fpt_byDaysAndTreewidth
---
The problem of the number of days plus the treewidth is fixed-parameter tractable. A word RAM
program computes the answer within `c * g k * (|x| + 1) ^ c` instructions, where `k` is the number
of days plus the treewidth of the overall conflict graph, for a function `g` of `k` alone. The
program is compiled from an IMP+ program whose correctness and cost are proved in
`Machine/Tw*.lean`; the theorem of Bodlaender and Kloks that finds a nice tree decomposition of
small width in time `2^{O(w^3)}` times a polynomial
(`Lax117284.Bodlaender.niceDecomposition_computable`) is proved, in `BodlaenderProved.lean`, from
its proof in lax-689794.
-/
theorem fpt_byDaysAndTreewidth : FptDecision Lax117284.Theorem4.byDaysAndTreewidth := by
  obtain ⟨prog, c, h⟩ := Lax117284Proofs.BodlaenderProved.niceDecomposition_computable_proved
  exact TwFinal.fpt_real ⟨prog, c, h⟩


end Lax117284Proofs.TreewidthReal
