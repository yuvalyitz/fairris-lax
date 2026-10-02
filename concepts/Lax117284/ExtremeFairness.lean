import Lax117284.Scheduling

/-!
---
title: The Extreme Values of the Fairness Parameter
type: lemma
---
Three values of the fairness parameter are settled by inspection. For $k = 0$ nothing is
required of a schedule, so every instance is a yes-instance. For $k = m$ every client must
be served on every day, which is possible exactly when no two jobs of a day conflict. For
$k > m$ no client can be served often enough, so an instance with at least one client is a
no-instance.

# Formalization Notes

The case $k > m$ needs an instance with a client: an instance with none has nothing to
require and admits the empty schedule for every parameter.
-/

namespace Lax117284.ExtremeFairness

open Lax117284.Scheduling

/-- **A fairness parameter of `0` requires nothing.** -/
axiom hasKFairSchedule_zero (I : Instance) : I.HasKFairSchedule 0

/-- **Serving every client on every day is possible exactly for conflict-free
instances.** -/
axiom hasKFairSchedule_days_iff (I : Instance) :
    I.HasKFairSchedule I.days ↔ I.ConflictFree

/-- **A fairness parameter above the number of days is unattainable**, as soon as there is
a client of whom it is demanded. -/
axiom not_hasKFairSchedule_of_days_lt {I : Instance} {k : ℕ} (hk : I.days < k)
    (hn : 0 < I.clients) : ¬ I.HasKFairSchedule k

end Lax117284.ExtremeFairness
