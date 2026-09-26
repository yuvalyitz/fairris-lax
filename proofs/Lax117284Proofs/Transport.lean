import Lax117284Proofs.Bridge
import Mathlib.Logic.Equiv.Fin.Basic

/-!
The gadget constructions of the development name their clients and days structurally, as
sums and subtypes of the objects they are built from, while the constructions of the
concepts number them. This file carries the identification between the two: a `Numbering`
of an instance of the development by a numbered instance, and the transport of feasibility,
of how often a client is served, and of the two questions along it.

Nothing here is specific to a construction; every gadget supplies its own two bijections
and the agreement of the processing times and due dates, and reads off the equivalence of
the questions.
-/

namespace Lax117284Proofs.Transport

open Lax117284.Scheduling

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- A numbering of an instance of the development by a numbered instance: bijections of the
clients and of the days under which the two instances have the same conflicts. Feasibility
and fairness depend on an instance only through its conflicts, so this is all a transport of
the question needs — the two instances may lay their jobs out differently. -/
structure Numbering (K : Model.Instance) (J : Instance) where
  /-- The numbering of the clients. -/
  client : K.Client ≃ Fin J.clients
  /-- The numbering of the days. -/
  day : K.Day ≃ Fin J.days
  /-- The conflicts agree. -/
  conflict_iff : ∀ i j j', K.Conflict i j j' ↔ J.Conflict (day i) (client j) (client j')

/-- A numbering under which the two instances present the very same jobs. -/
def Numbering.ofJobs {K : Model.Instance} {J : Instance} (client : K.Client ≃ Fin J.clients)
    (day : K.Day ≃ Fin J.days) (p_eq : ∀ i j, K.p i j = J.p (day i) (client j))
    (d_eq : ∀ i j, K.d i j = J.d (day i) (client j)) : Numbering K J where
  client := client
  day := day
  conflict_iff := by
    intro i j j'
    rw [← Instance.conflictAt_iff]
    simp only [Model.Instance.Conflict, Model.Instance.start, Instance.ConflictAt,
      Instance.pAt_coe, Instance.dAt_coe, p_eq, d_eq]

namespace Numbering

variable {K : Model.Instance} {J : Instance} (N : Numbering K J)

/-- The schedule of the numbered instance belonging to a schedule of the other. -/
def push (σ : K.Schedule) : J.Schedule :=
  fun i => (σ (N.day.symm i)).map N.client.toEmbedding

/-- The schedule of the development's instance belonging to a schedule of the numbered
one. -/
def pull (τ : J.Schedule) : K.Schedule :=
  fun i => (τ (N.day i)).map N.client.symm.toEmbedding

theorem mem_push (σ : K.Schedule) (i : Fin J.days) (a : Fin J.clients) :
    a ∈ N.push σ i ↔ N.client.symm a ∈ σ (N.day.symm i) := by
  simp [push, Finset.mem_map_equiv]

theorem mem_pull (τ : J.Schedule) (i : K.Day) (j : K.Client) :
    j ∈ N.pull τ i ↔ N.client j ∈ τ (N.day i) := by
  simp [pull, Finset.mem_map_equiv]

theorem feasible_push {σ : K.Schedule} (h : Model.Instance.Feasible σ) :
    Instance.Feasible (N.push σ) := by
  intro i a ha b hb hne hc
  have ha' : N.client.symm a ∈ σ (N.day.symm i) := (N.mem_push σ i a).1 (Finset.mem_coe.1 ha)
  have hb' : N.client.symm b ∈ σ (N.day.symm i) := (N.mem_push σ i b).1 (Finset.mem_coe.1 hb)
  have hne' : N.client.symm a ≠ N.client.symm b := fun he => hne (N.client.symm.injective he)
  refine h (N.day.symm i) _ ha' _ hb' hne' ?_
  rw [N.conflict_iff]
  simpa using hc

theorem feasible_pull {τ : J.Schedule} (h : Instance.Feasible τ) :
    Model.Instance.Feasible (N.pull τ) := by
  intro i j hj j' hj' hne hc
  have hj2 : N.client j ∈ τ (N.day i) := (N.mem_pull τ i j).1 hj
  have hj2' : N.client j' ∈ τ (N.day i) := (N.mem_pull τ i j').1 hj'
  have hne' : N.client j ≠ N.client j' := fun he => hne (N.client.injective he)
  exact h (N.day i) (Finset.mem_coe.2 hj2) (Finset.mem_coe.2 hj2') hne'
    ((N.conflict_iff i j j').1 hc)

theorem served_push (σ : K.Schedule) (j : K.Client) :
    Model.Instance.served σ j = Instance.served (N.push σ) (N.client j) := by
  refine Finset.card_equiv N.day fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, N.mem_push,
    Equiv.symm_apply_apply]

theorem served_pull (τ : J.Schedule) (j : K.Client) :
    Model.Instance.served (N.pull τ) j = Instance.served τ (N.client j) := by
  refine Finset.card_equiv N.day fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, N.mem_pull]

/-- **The two instances ask the same question**, once the fairness parameters are carried
along the numbering of the clients. -/
theorem hasFairSchedule_iff (k : Fin J.clients → ℕ) :
    K.HasFairSchedule (fun j => k (N.client j)) ↔ J.HasFairSchedule k := by
  constructor
  · rintro ⟨σ, hf, hfair⟩
    refine ⟨N.push σ, N.feasible_push hf, fun a => ?_⟩
    have h := hfair (N.client.symm a)
    rw [N.served_push] at h
    simpa using h
  · rintro ⟨τ, hf, hfair⟩
    exact ⟨N.pull τ, N.feasible_pull hf, fun j => by
      rw [N.served_pull]; exact hfair (N.client j)⟩

/-- The uniform case of the same equivalence. -/
theorem hasKFairSchedule_iff (M : Numbering K J) (k : ℕ) :
    K.HasKFairSchedule k ↔ J.HasKFairSchedule k :=
  M.hasFairSchedule_iff fun _ => k

end Numbering

/-- Numbering the days of an instance with one day appended: the old days keep their
numbers and the new one is the last. -/
def dayEquivSucc (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) where
  toFun := Sum.elim Fin.castSucc fun _ => Fin.last n
  invFun := Fin.lastCases (Sum.inr ()) fun i => Sum.inl i
  left_inv := by rintro (i | u) <;> simp
  right_inv := by refine Fin.lastCases ?_ ?_ <;> simp

/-- Numbering the clients of an instance with two clients appended. -/
def clientEquivAdd2 (n : ℕ) : Fin n ⊕ Bool ≃ Fin (n + 2) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finSumFinEquiv

/-- Numbering the days of an instance whose days are doubled. -/
def dayEquivDouble (n : ℕ) : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
  finSumFinEquiv.trans (finCongr (two_mul n).symm)

@[simp] theorem clientEquivAdd2_inl_val (n : ℕ) (i : Fin n) :
    ((clientEquivAdd2 n (Sum.inl i) : Fin (n + 2)) : ℕ) = (i : ℕ) := Eq.trans rfl rfl

@[simp] theorem clientEquivAdd2_inr_val (n : ℕ) (b : Bool) :
    n ≤ ((clientEquivAdd2 n (Sum.inr b) : Fin (n + 2)) : ℕ) := Nat.le_add_right _ _

@[simp] theorem dayEquivDouble_inl_val (n : ℕ) (i : Fin n) :
    ((dayEquivDouble n (Sum.inl i) : Fin (2 * n)) : ℕ) = (i : ℕ) := Eq.trans rfl rfl

@[simp] theorem dayEquivDouble_inr_val (n : ℕ) (i : Fin n) :
    ((dayEquivDouble n (Sum.inr i) : Fin (2 * n)) : ℕ) = n + (i : ℕ) := Eq.trans rfl rfl

end Lax117284Proofs.Transport
