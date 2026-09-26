import Lax117284Proofs.Machine.UFinal
import Lax117284Proofs.Machine.MatchRam
import Lax117284Proofs.Machine.MatchWord
import Lax117284Proofs.Machine.RamCompose
import Lax117284.Theorem2

/-!
Theorem 2, tractability: with unit processing times the problem is solvable in polynomial time.
The instance is reduced, by a word RAM program on the zeros and ones of its word, to the bipartite
graph of `UnitPGraph` as a table; a second word RAM program converts the table to the bipartite
word of `lax-817977`; and the cited decider of `lax-817977` decides whether the graph has a
matching saturating its left side.
-/

namespace Lax117284Proofs.Theorem2UnitP

open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine Lax117284Proofs.Machine.USem Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.MatchGuard
open Lax117284Proofs.UnitPGraph (Yes)
open scoped Classical

/--
---
conclusion: Lax117284.Theorem2.uniform_unitP_mem_P
---
With unit processing times, a fair schedule exists exactly when a bipartite graph has a matching
that saturates its left side. The left vertices of the graph are the jobs, one for every day and
client. The right vertices are the pairs of a day and a client, of which the first client of a day
with a given due date stands for that due date, and, for every client, the `k` days that the client
must be served on being taken out of the `m` days, `m - k` rejection vertices. The graph is written
as a flat table of zeros and ones by a word RAM program on the zeros and ones of the word of the
instance, in time polynomial in the size of the word; a second word RAM program converts the table
into the compressed sparse row word of the graph, in time polynomial in the size of the table; and
the cited decider of `lax-817977` (`ramPolytime_saturating`) decides whether the graph has such a
matching in time polynomial in the size of that word. A word that encodes no instance with unit
processing times is sent to a graph with one left vertex and no right vertex.
-/
theorem uniform_unitP_mem_P : Uniform (fun I _ => I.UnitP) ∈ P :=
  RamCompose.mem_P_of_ram3 (f := fun w => decide (Yes (redU w)))
    (fun w => by rw [decide_eq_true_iff]; exact (redU_correct w).symm)
    UFinal.redU_ramPolytime MatchRam.conv_ramPolytime
    Lax117284.BipartiteDecision.ramPolytime_saturating (fun w => by
      have h1 : UFinal.W.redBits (natBits w) = redU w := by
        show redU (bitsOf (natBits w)) = _
        rw [bitsOf_natBits]
      rw [h1, MatchWord.saturatingAnswer_conv, gfun_redU]
      simp)

end Lax117284Proofs.Theorem2UnitP
