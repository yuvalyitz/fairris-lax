import Lax117284.JustInTime
import Lax117284.Problems

/-!
---
title: Just-in-Time Scheduling on Unrelated Machines as Day-Independent Due Dates
type: theorem
---
**Theorem 11.** The problem
$1 \mid \mathrm{rep},\, d_{i,j} = d_j \mid \min_j \sum_i Z_{i,j}$ is NP-hard.

An instance of $R \parallel \sum_j Z_j$ is read as an instance of fair repetitive interval
scheduling by taking its jobs as clients and its machines as days: client $j$'s job on day
$i$ has the processing time of job $j$ on machine $i$ and the due date of job $j$, which
does not depend on the day. Executing every job just in time on some machine is then the
same thing as serving every client on at least one day, so the constructed instance is a
yes-instance at $k = 1$ exactly when the given one admits an all-just-in-time schedule.
Since $R \parallel \sum_j Z_j$ is NP-hard, so is the problem with day-independent due dates.

# Formalization Notes

The two models are already the same up to naming, the whole content of the reduction being
that both ask for a partition of intervals ending at fixed times. The construction is
therefore a renaming, and what has to be checked is that it is one.
-/

namespace Lax117284.Theorem11

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax429075.Reductions

/-- **The instance of Theorem 11**: clients are jobs, days are machines, the due date of a
client is that of its job and so does not depend on the day. -/
def inst (R : JustInTime.Instance) : Instance where
  clients := R.jobs
  days := R.machines
  p i j := R.p i j
  d _ j := R.d j
  p_pos := R.p_pos
  p_le_d := R.p_le_d

/-- **The constructed instance has day-independent due dates.** -/
axiom inst_dayIndepD (R : JustInTime.Instance) : (inst R).DayIndepD

/-- **The construction is correct**: every job can be executed just in time exactly when
every client can be served on at least one day. -/
axiom correct (R : JustInTime.Instance) :
    R.AllJustInTime ↔ (inst R).HasKFairSchedule 1

open Classical in
/-- **The reduction**, as a map on words: a word encoding an instance of
`R || ∑_j Z_j` is sent to the encoding of the constructed instance with the fairness
parameter `1`, and every other word to the rejected word. -/
noncomputable def reduce (w : Word) : Word :=
  if h : ∃ R : JustInTime.Instance, JustInTime.encodeInstance R = w then
    encodeUniform (inst h.choose) 1
  else rejected

/-- **The reduction is correct.** -/
axiom reduce_correct (w : Word) :
    w ∈ JustInTime.AllJIT ↔ reduce w ∈ Uniform fun I _ => I.DayIndepD

/-- **The reduction runs in polynomial time.** -/
axiom reduce_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduce)

/-- **Theorem 11.** `R || ∑_j Z_j` reduces in polynomial time to the problem on the
instances with day-independent due dates. -/
axiom allJIT_manyOne_dayIndepD :
    ManyOne JustInTime.AllJIT (Uniform fun I _ => I.DayIndepD)

end Lax117284.Theorem11
