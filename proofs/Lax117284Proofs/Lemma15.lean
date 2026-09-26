import Lax117284Proofs.Lemma15_KjToK
import Lax117284Proofs.Transport
import Lax117284.Lemma15
import Mathlib.Data.Finset.Fin

/-!
Per-client fairness parameters reduce to a uniform one. The development's construction takes
an arbitrary injective numbering of the clients and an arbitrary set of `k j` days for each
client `j`; the construction of the concepts takes the numbering the clients already carry
and the first `k j` of the additional days, so it is that construction at those choices.
-/

namespace Lax117284Proofs.Lemma15

open Lax117284.Scheduling Lax117284.Lemma15

/-- The numbering of the clients the construction of the concepts uses: the number a client
already carries, counted from one. -/
def enum (J : Instance) : Model.Lemma15.Enum (Bridge.model J) where
  idx := fun j : Fin J.clients => (j : ℕ) + 1
  pos _ := Nat.succ_pos _
  le j := by
    have h : (Bridge.model J).numClients = J.clients := Fintype.card_fin J.clients
    have := j.isLt
    omega
  inj a b h := Fin.ext (Nat.succ_injective h)

/-- The days on which a client is blocked: the first `k j` of the additional days. -/
def blocked (J : Instance) (k : Fin J.clients → ℕ) :
    Fin J.clients → Finset (Fin J.days) :=
  fun j => Finset.univ.filter fun i => (i : ℕ) < k j

theorem blocked_card (J : Instance) (k : Fin J.clients → ℕ) (hk : ∀ j, k j ≤ J.days)
    (j : Fin J.clients) : (blocked J k j).card = k j := by
  classical
  have h : blocked J k j
      = (Finset.range (k j)).attachFin fun m hm =>
          lt_of_lt_of_le (Finset.mem_range.1 hm) (hk j) := by
    ext i
    simp [blocked, Finset.mem_attachFin]
  rw [h, Finset.card_attachFin, Finset.card_range]

/-- The end of the gadget is the same time in both descriptions. -/
theorem dmax_eq (J : Instance) : Model.Lemma15.dmax (Bridge.model J) = dmax J := Eq.trans rfl rfl

/-- The markers' job of the development has the length the concepts give it. -/
theorem P_eq (J : Instance) : Model.Lemma15.P (Bridge.model J) = span J := by
  have h : (Bridge.model J).numClients = J.clients := Fintype.card_fin J.clients
  simp [Model.Lemma15.P, span, h]

/-- On an original day an original client keeps its job. -/
theorem p_inl_inl (J : Instance) (k : Fin J.clients → ℕ) (i : Fin J.days)
    (j : Fin J.clients) :
    J.p i j = (inst J k).p (Transport.dayEquivDouble J.days (Sum.inl i))
      (Transport.clientEquivAdd2 J.clients (Sum.inl j)) := by
  simp [inst, i.isLt, j.isLt]

/-- A marker's job has the length of the markers' stretch. -/
theorem p_marker (J : Instance) (k : Fin J.clients → ℕ)
    (a : Fin J.days ⊕ Fin J.days) (b : Bool) :
    Model.Lemma15.P (Bridge.model J) =
      (inst J k).p (Transport.dayEquivDouble J.days a)
        (Transport.clientEquivAdd2 J.clients (Sum.inr b)) := by
  have hb := Nat.not_lt.2 (Transport.clientEquivAdd2_inr_val J.clients b)
  simp [inst, P_eq J, dmax_eq J, hb]

/-- On an additional day an original client has a unit job. -/
theorem p_inr_inl (J : Instance) (k : Fin J.clients → ℕ) (i : Fin J.days)
    (j : Fin J.clients) :
    (1 : ℕ) = (inst J k).p (Transport.dayEquivDouble J.days (Sum.inr i))
      (Transport.clientEquivAdd2 J.clients (Sum.inl j)) := by
  have hi := Nat.not_lt.2 (Nat.le_add_right J.days (i : ℕ))
  simp [inst, j.isLt, hi]

/-- On an original day an original client keeps its due date. -/
theorem d_inl_inl (J : Instance) (k : Fin J.clients → ℕ) (i : Fin J.days)
    (j : Fin J.clients) :
    J.d i j = (inst J k).d (Transport.dayEquivDouble J.days (Sum.inl i))
      (Transport.clientEquivAdd2 J.clients (Sum.inl j)) := by
  simp [inst, i.isLt, j.isLt]

/-- A marker's job ends at the end of the markers' stretch. -/
theorem d_marker (J : Instance) (k : Fin J.clients → ℕ)
    (a : Fin J.days ⊕ Fin J.days) (b : Bool) :
    Model.Lemma15.dmax (Bridge.model J) + Model.Lemma15.P (Bridge.model J) =
      (inst J k).d (Transport.dayEquivDouble J.days a)
        (Transport.clientEquivAdd2 J.clients (Sum.inr b)) := by
  have hb := Nat.not_lt.2 (Transport.clientEquivAdd2_inr_val J.clients b)
  simp [inst, P_eq J, dmax_eq J, hb]

/-- On an additional day an original client's unit job sits inside the markers' job exactly
on the days it is blocked on. -/
theorem d_inr_inl (J : Instance) (k : Fin J.clients → ℕ) (i : Fin J.days)
    (j : Fin J.clients) :
    (if i ∈ blocked J k j then
        Model.Lemma15.dmax (Bridge.model J) + (enum J).idx j
      else Model.Lemma15.dmax (Bridge.model J) + Model.Lemma15.P (Bridge.model J)
        + (enum J).idx j) =
      (inst J k).d (Transport.dayEquivDouble J.days (Sum.inr i))
        (Transport.clientEquivAdd2 J.clients (Sum.inl j)) := by
  have hi := Nat.not_lt.2 (Nat.le_add_right J.days (i : ℕ))
  by_cases hb : (i : ℕ) < k j
  · have hmem : i ∈ blocked J k j := by simp [blocked, hb]
    simp [inst, P_eq J, dmax_eq J, enum, hmem, hb, j.isLt, hi]
  · have hmem : i ∉ blocked J k j := by simp [blocked, hb]
    simp [inst, P_eq J, dmax_eq J, enum, hmem, hb, j.isLt, hi]

/-- The instance of the development is the numbered one. -/
noncomputable def numbering (J : Instance) (k : Fin J.clients → ℕ) :
    Transport.Numbering
      (Model.Lemma15.inst (Bridge.model J) (enum J) (blocked J k)) (inst J k) :=
  Transport.Numbering.ofJobs (Transport.clientEquivAdd2 J.clients)
    (Transport.dayEquivDouble J.days)
    (by
      rintro (i | i) (j | b)
      · exact p_inl_inl J k i j
      · exact p_marker J k (Sum.inl i) b
      · exact p_inr_inl J k i j
      · exact p_marker J k (Sum.inr i) b)
    (by
      rintro (i | i) (j | b)
      · exact d_inl_inl J k i j
      · exact d_marker J k (Sum.inl i) b
      · exact d_inr_inl J k i j
      · exact d_marker J k (Sum.inr i) b)

/--
---
conclusion: Lax117284.Lemma15.correct
---
The two markers can never run on the same day, so each of them runs on exactly one day of
every pair; a client of the original instance is blocked on exactly the `k j` additional
days whose private slot lies inside the markers' job, and needs `k j` of the original days
to reach `m`.
-/
theorem correct (J : Instance) (k : Fin J.clients → ℕ) (hk : ∀ j, k j ≤ J.days) :
    J.HasFairSchedule k ↔ (inst J k).HasKFairSchedule J.days := by
  rw [Bridge.hasFairSchedule_iff,
    Model.Lemma15.hasFairSchedule_iff (num := enum J) (blocked := blocked J k) k
      (blocked_card J k hk),
    Bridge.model_numDays]
  exact (numbering J k).hasKFairSchedule_iff J.days

end Lax117284Proofs.Lemma15
