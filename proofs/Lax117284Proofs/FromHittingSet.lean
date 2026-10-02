import Lax117284.JustInTime
import Lax496464.HittingSet
import Mathlib.Tactic

/-!
# From Hitting Set to Just-in-Time Scheduling on Unrelated Machines

An instance of Hitting Set with universe `n`, `m` sets and required size `k ≤ n` becomes an
instance of `R || ∑ Z_j` with `n` machines, one per element, and three kinds of jobs.

* `n` *guards*, due at `1` with processing time `1` on every machine: two guards overlap on
  a machine, so every machine holds exactly one guard, occupying `(0, 1]`.
* One *set job* per set `s`, due at `2 + s`; its processing time is `1` on the machines of
  the set, where it occupies `(1 + s, 2 + s]`, and `2 + s` elsewhere, where it would occupy
  `(0, 2 + s]` and collide with the guard.
* `n - k` *fillers*, due at `m + 2` with processing time `m + 1`, occupying `(1, m + 2]`:
  fillers collide with each other and with every set job, so they block `n - k` machines
  and the set jobs live on at most `k` machines, which hit every set.
-/

namespace Lax117284Proofs.FromHittingSet

open Lax117284.JustInTime Lax496464.HittingSet

variable (P : Lax496464.HittingSet.Instance) (k : ℕ)

/-- The number of jobs: `n` guards, `m` set jobs, `n - k` fillers. -/
def jobs : ℕ := P.n + P.m + (P.n - k)

/-- Machine `i` is eligible for set `s`. -/
def Elig (i s : ℕ) : Prop := ∃ (hi : i < P.n) (hs : s < P.m), (⟨i, hi⟩ : Fin P.n) ∈ P.F ⟨s, hs⟩

instance (i s : ℕ) : Decidable (Elig P i s) := by unfold Elig; infer_instance

/-- The due date of job `j`. -/
def due (j : ℕ) : ℕ :=
  if j < P.n then 1 else if j < P.n + P.m then 2 + (j - P.n) else P.m + 2

/-- The processing time of job `j` on machine `i`. -/
def proc (i j : ℕ) : ℕ :=
  if j < P.n then 1
  else if j < P.n + P.m then (if Elig P i (j - P.n) then 1 else 2 + (j - P.n))
  else P.m + 1

/-- The instance of `R || ∑ Z_j`. -/
def R : Lax117284.JustInTime.Instance where
  jobs := jobs P k
  machines := P.n
  p := fun i j => proc P i j
  d := fun j => due P j
  p_pos := fun _ j => by unfold proc; split_ifs <;> omega
  p_le_d := fun _ j => by unfold proc due; split_ifs <;> omega

/-! ### The three kinds of jobs -/

def guardIdx (a : Fin P.n) : Fin (jobs P k) := ⟨a, by unfold jobs; omega⟩
def setIdx (s : Fin P.m) : Fin (jobs P k) := ⟨P.n + s, by unfold jobs; omega⟩
def fillIdx (t : Fin (P.n - k)) : Fin (jobs P k) := ⟨P.n + P.m + t, by unfold jobs; omega⟩



/-! ### Which pairs overlap -/



/-! ### From a hitting set to a schedule -/










section Forward

variable {P k} (H : Finset (Fin P.n)) (ch : Fin P.m → Fin P.n)
  (hch : ∀ s, ch s ∈ H ∧ ch s ∈ P.F s)
  (e : Fin (P.n - k) → Fin P.n) (he : Function.Injective e) (heH : ∀ t, e t ∉ H)

/-- The assignment: guards to their own machine, set jobs to the chosen element `ch s` of
their set in `H`, fillers along `e`. -/
def assign : Fin (jobs P k) → Fin P.n := fun j =>
  if hg : (j : ℕ) < P.n then ⟨j, hg⟩
  else if hs : (j : ℕ) < P.n + P.m then ch ⟨j - P.n, by omega⟩
  else e ⟨j - (P.n + P.m), by have := j.isLt; unfold jobs at this; omega⟩




end Forward

/-! ### From a schedule to a hitting set -/

section Backward

variable {P k} (f : Fin (jobs P k) → Fin P.n)
  (hf : ∀ j j', j ≠ j' → f j = f j' → ¬ (R P k).Overlap (f j) j j')

end Backward


end Lax117284Proofs.FromHittingSet
