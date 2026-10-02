import Lax117284.InstanceEncoding
import Lax117284.IlpClients
import Lax117284.ParameterizedComplexity
import Lax117284.Problems

/-!
---
title: Structural Parameters of the Conflict Graph
type: theorem
---
**Theorem 4.** The problem $1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$

* is NP-hard for a constant treewidth $\tau$ of the overall conflict graph,
* is fixed-parameter tractable with respect to $m + \tau$,
* and is fixed-parameter tractable with respect to the number $n$ of clients.

Hardness at constant treewidth holds already at $\tau = 6$, and therefore at every larger
constant: it is obtained from Multicoloured Independent Set through the per-client problem,
whose instances the construction produces with treewidth at most $4$, and a reduction back
to the uniform problem that raises the treewidth by at most $2$. Tractability for
$m + \tau$ is a dynamic program over a nice tree decomposition of the overall conflict
graph, whose table holds, for every bag, the restrictions to that bag of the schedules of
the subtree; a bag of $\tau + 1$ clients admits $2^{O(\tau m)}$ of them. Tractability for
$n$ is a formulation as an integer program whose number of variables depends on $n$ alone,
which the source solves by Lenstra's algorithm; here it is solved by an algorithm for these
particular integer programs.

The third bullet is stated in two halves: the problem parameterized by $n$ *fpt-reduces* to the
feasibility of the integer programs of the reduction, parameterized by the number of variables
(`byClients_fptReduces_ilp`, proved: the integer program of the source, written by a word RAM
program), and the feasibility of these integer programs is fixed-parameter tractable
(`IlpClients.ilpClients_fpt`, proved by a guess-and-verify algorithm for the constraint matrices
of the family, which are fixed by $n$; the source cites Lenstra's algorithm for it, which is not
needed for this family). Fixed-parameter tractability in $n$ (`fpt_byClients`) is their
combination.

# Formalization Notes

The combination of the two halves is not a general closure theorem. An fpt-reduction is only
required to run where its image fits in the word length, and the image here has a
parameter-sized table, so on a word much shorter than that table the decision program cannot run
the algorithm for the integer programs on the image; the proof of `fpt_byClients` handles those words, whose number
of schedules is bounded by a function of $n$ alone, by enumeration. On every other word it writes
the integer program and runs the algorithm for the integer programs on it at a word length chosen for that program.

Hardness is stated at treewidth at most $6$ rather than for each $\tau \ge 6$ separately.
The class of instances of treewidth at most $6$ is contained in that of treewidth at most
$\tau$ for every larger $\tau$, so the statement at $6$ gives every other one; the source's
construction forcing the treewidth to be exactly $\tau$ serves the version of the claim in
which the parameter is pinned rather than bounded.

The two tractability claims are claims about one program each, on the word encoding of an
instance, with the parameter a function of the word: the number of days plus the treewidth
of the overall conflict graph of the decoded instance, and the number of clients. The
number of days and the number of clients are entries of the word; the treewidth is a
structural property of what the word encodes, which is a function of the word because a word
encodes at most one instance.

A word of the domain is an instance block followed by the single entry of the fairness
parameter, so the instance is decoded from the word without its last entry (`x.dropLast`); the
parameter itself is the last entry. Decoding the whole word would read no instance at all, since
the block has even length, and would make both problems trivial.
-/

namespace Lax117284.Theorem4

open Lax117284.Scheduling Lax117284.Problems Lax117284.InstanceEncoding
open Lax117284.ParameterizedComplexity

/-- The problem parameterized by the number of days plus the treewidth of the overall
conflict graph. -/
noncomputable def byDaysAndTreewidth : ParameterizedComplexity.Problem where
  Domain := UniformInstances
  Yes x := (decode x.dropLast).HasKFairSchedule (parameter x)
  param x := (decode x.dropLast).days + ConflictGraph.treewidth (decode x.dropLast)

/-- The problem parameterized by the number of clients. -/
noncomputable def byClients : ParameterizedComplexity.Problem where
  Domain := UniformInstances
  Yes x := (decode x.dropLast).HasKFairSchedule (parameter x)
  param x := (decode x.dropLast).clients

/-- **Theorem 4, first bullet.** The problem is NP-hard on the instances whose overall
conflict graph has treewidth at most `6`, hence for a constant treewidth. -/
axiom uniform_treewidth_npHard :
    NPHard (Uniform fun I _ => ConflictGraph.treewidth I ≤ 6)

/-- **Theorem 4, second bullet.** The problem is fixed-parameter tractable with respect to
the number of days plus the treewidth of the overall conflict graph. -/
axiom fpt_byDaysAndTreewidth : FPT byDaysAndTreewidth

/-- **Theorem 4, third bullet, the reduction.** The problem parameterized by the number of
clients fpt-reduces to the feasibility of the integer programs of the family `IlpClients.ilpClients`,
parameterized by the number of variables: the integer program of Theorem 21 of the source, with one
variable per type of day and set of clients and one slack per client, `2 ^ (n² + n) + n` variables in
all, computed by a word RAM program. -/
axiom byClients_fptReduces_ilp : byClients ≤fpt IlpClients.ilpClients

/-- **Theorem 4, third bullet.** The problem is fixed-parameter tractable with respect to
the number of clients: by the reduction `byClients_fptReduces_ilp` and the algorithm for the
integer programs of the family, `IlpClients.ilpClients_fpt`. -/
axiom fpt_byClients : FPT byClients

end Lax117284.Theorem4
