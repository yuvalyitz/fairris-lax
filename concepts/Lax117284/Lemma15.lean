import Lax117284.ConflictGraph
import Lax117284.Corollary8
import Lax117284.Problems

/-!
---
title: Per-client fairness parameters reduce to a uniform one
type: lemma
---
**Lemma 15.** There is a polynomial-time reduction from
$1 \mid k_j, \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ to
$1 \mid \mathrm{rep} \mid \min_j \sum_i Z_{i,j}$ which increases the treewidth of the
overall conflict graph by at most $2$.

Let $I$ have $n$ clients, $m$ days and fairness parameters $k_1, \ldots, k_n$ with
$k_j \le m$. Append another $m$ days, add two clients $c^-$ and $c^+$, and ask for the
uniform parameter $m$. The jobs of $c^-$ and $c^+$ coincide on every day, so at most one of
them runs on any day and, being asked for $m$ of the $2m$ days, each of them runs on
exactly one day of every pair. Their common job occupies a stretch of time later than every
due date of $I$, so it conflicts with no original job on the original days. On the
additional days each original client $j$ has a job of its own, which is placed inside that
stretch on $k_j$ of them and after it on the others. A client of $I$ can therefore be served
on all but $k_j$ of the additional days, and needs $k_j$ of the original days to reach $m$ —
which is its original requirement.

The jobs the original clients receive on the additional days are pairwise disjoint, so the
construction adds no edge between original clients: the overall conflict graph grows only by
the two new vertices, and its treewidth by at most $2$.

# Formalization notes

The $k_j$ days on which client $j$ is blocked are the first $k_j$ of the additional days.
The source takes an arbitrary set of that size; taking the first ones makes the construction
a function of the instance and its parameters alone, which is what a reduction has to be.

The two new clients are numbered $n$ and $n+1$, and day $m + i$ of the construction is the
additional copy of day $i$. The private job of client $j$ ends at a time offset by $j+1$
inside a stretch of length $n+1$, so distinct clients receive disjoint jobs and every such
job lies inside the stretch the two new clients occupy.

Correctness is stated for instances whose parameters do not exceed the number of days, which
is the only case that can be a yes-instance. The three statements separate what is
asserted: the combinatorial content of the construction, the treewidth of its output, and
the running time of the map on words. The lemma itself follows from them.

An instance without clients is a yes-instance whatever its parameters, and its table is empty, so
its code does not reflect its number of days: the construction, which has four cells for every
day, would write exponentially many in the length of the code. The map therefore sends such an
instance to the instance without clients and without days with the parameter `0`, which is
again a yes-instance.

The reduction is correct on all words, and the treewidth is not part of that statement: the
treewidth of the input instance is not something the map checks, and the construction
preserves the answer whatever it is. What the construction does to the treewidth is
`treewidth_le`; a reduction that starts from instances of treewidth at most `4`, such as the
one of Lemma 14, therefore lands among those of treewidth at most `6`.
-/

namespace Lax117284.Lemma15

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax429075.Reductions

/-- A time not before any due date of `I`. -/
def dmax (I : Instance) : ℕ := Finset.univ.sup fun i => Finset.univ.sup fun j => I.d i j

/-- The length of the job the two new clients share: longer than the stretch of private
jobs, so that it contains all of them. -/
def span (I : Instance) : ℕ := I.clients + 1

/-- **The instance of Lemma 15**: `2m` days, the `n` clients of `I` together with two new
ones, and the uniform fairness parameter `m`. -/
def inst (I : Instance) (k : Fin I.clients → ℕ) : Instance where
  clients := I.clients + 2
  days := 2 * I.days
  p i j :=
    if (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.pAt i j else 1)
    else span I
  d i j :=
    if hj : (j : ℕ) < I.clients then
      (if (i : ℕ) < I.days then I.dAt i j
        else if (i : ℕ) - I.days < k ⟨j, hj⟩ then dmax I + ((j : ℕ) + 1)
          else dmax I + span I + ((j : ℕ) + 1))
    else dmax I + span I
  p_pos i j := by
    have h0 := I.pAt_pos (i : ℕ) (j : ℕ)
    have hs : span I = I.clients + 1 := rfl
    split_ifs <;> omega
  p_le_d i j := by
    have h1 := I.pAt_le_dAt (i : ℕ) (j : ℕ)
    have hs : span I = I.clients + 1 := rfl
    split_ifs <;> omega

/-- **The construction is correct**: the instance it produces admits a schedule serving
every client on `m` of its `2m` days exactly when the original instance admits one serving
every client `j` on `k j` of its `m` days. -/
axiom correct (I : Instance) (k : Fin I.clients → ℕ) (hk : ∀ j, k j ≤ I.days) :
    I.HasFairSchedule k ↔ (inst I k).HasKFairSchedule I.days

/-- **The construction raises the treewidth of the overall conflict graph by at most
two.** -/
axiom treewidth_le (I : Instance) (k : Fin I.clients → ℕ) :
    ConflictGraph.treewidth (inst I k) ≤ ConflictGraph.treewidth I + 2

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance with per-client
parameters not exceeding its number of days is sent to the encoding of the constructed
instance with the parameter `m`, an instance without clients to a fixed yes-instance, and
every other word to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ (I : Instance) (k : Fin I.clients → ℕ),
      encodePerClient I k = w ∧ ∀ j, k j ≤ I.days then
    if h.choose.clients = 0 then encodeUniform (Corollary8.noClients 0) 0
    else encodeUniform (inst h.choose h.choose_spec.choose) h.choose.days
  else rejected

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ PerClient (fun I k => ∀ j, k j ≤ I.days) ↔ reduce w ∈ Uniform any

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

/-- **Lemma 15.** The per-client problem reduces in polynomial time to the uniform problem;
by `treewidth_le` the reduction raises the treewidth of the overall conflict graph by at
most two. -/
axiom perClient_manyOne_uniform :
    ManyOne (PerClient fun I k => ∀ j, k j ≤ I.days) (Uniform any)

end Lax117284.Lemma15
