import Lax117284.Scheduling

/-!
---
title: The Dynamic Program for Day-Independent Due Dates
type: theorem
---
**Theorem 12.** Let $I$ be an instance whose due dates are day-independent, so that client
$j$ has one due date $d_j$ on every day. Order the clients by due date and process them in
that order, carrying as state, for every day, the time at which that day's machine becomes
free. Serving a client on a set of days requires that on each of those days the machine be
free early enough for its job to be completed at its due date, and leaves the machine of
each of those days free from that due date onwards. The instance admits a $k$-fair schedule
if and only if the program, started with every machine free from time $0$ and applied to
the clients in due-date order, can serve every client on $k$ days.

Processing the clients in due-date order is what makes the state sufficient: a client
considered later has a due date at least as large, so the only thing a decision about the
earlier clients can leave behind that matters is how late each machine is occupied. For a
constant number $m$ of days the number of reachable states is polynomial, and the program
decides the problem in polynomial time.

# Formalization Notes

The program is a predicate: it holds of a list of clients and a state when the clients of
the list can each be served on $k$ days from that state onwards. It is recursive in the
list, and the recursion is the transition of the dynamic program rather than a table, which
is the form in which its correctness is stated and proved. A table filled in the order of
the list has the same reachable states.

The list is required to contain every client exactly once and to be sorted by due date,
which is the precondition of the program rather than a property of the instance, so a
statement about it says what the algorithm must be given.
-/

namespace Lax117284.Theorem12

open Lax117284.Scheduling

variable {I : Instance}

/-- The dynamic program of Theorem 12: given the due dates `dd`, the fairness parameter
`k`, the clients still to be served, and for each day the time at which its machine is
free, can every remaining client be served on `k` days? -/
def Program (dd : Fin I.clients → ℕ) (k : ℕ) :
    List (Fin I.clients) → (Fin I.days → ℕ) → Prop
  | [], _ => True
  | j :: rest, free => ∃ S : Finset (Fin I.days), S.card = k ∧
      (∀ i ∈ S, I.p i j + free i ≤ dd j) ∧
      Program dd k rest fun i => if i ∈ S then dd j else free i

/-- **Theorem 12.** With day-independent due dates, an instance admits a `k`-fair schedule
exactly when the dynamic program, applied to the clients in due-date order with every
machine free from time `0`, can serve every client on `k` days. -/
axiom hasKFairSchedule_iff_program (hd : I.DayIndepD) (i₀ : Fin I.days) (k : ℕ)
    {l : List (Fin I.clients)} (hnd : l.Nodup) (hall : ∀ j, j ∈ l)
    (hsorted : l.Pairwise fun a b => I.d i₀ a ≤ I.d i₀ b) :
    I.HasKFairSchedule k ↔ Program (I.d i₀) k l fun _ => 0

end Lax117284.Theorem12
