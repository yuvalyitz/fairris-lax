import Mathlib.Tactic
import Lax117284.InstanceEncoding
import Lax117284Proofs.Injectivity

/-!
The word of a uniform instance, read entry by entry: the counts, the processing times and due dates
of the jobs, the fairness parameter.
-/

namespace Lax117284Proofs.ClientsWord

open Lax117284.Scheduling Lax117284.InstanceEncoding

variable {x y : List ℕ} {I : Instance} {k : ℕ}

theorem len_eq (h : EncodesUniform x I k) : x.length = 3 + 2 * (I.days * I.clients) := by
  obtain ⟨y, rfl, hy⟩ := h
  simp [hy.length_eq]; ring

theorem x0 (h : EncodesUniform x I k) : x.getD 0 0 = I.clients := by
  obtain ⟨y, rfl, hy⟩ := h
  have := hy.length_eq
  rw [List.getD_append _ _ _ _ (by omega)]
  exact hy.clientCount_eq

theorem x1 (h : EncodesUniform x I k) : x.getD 1 0 = I.days := by
  obtain ⟨y, rfl, hy⟩ := h
  have := hy.length_eq
  rw [List.getD_append _ _ _ _ (by omega)]
  exact hy.dayCount_eq

theorem xk (h : EncodesUniform x I k) : x.getD (2 + 2 * (I.days * I.clients)) 0 = k := by
  obtain ⟨y, rfl, hy⟩ := h
  have := hy.length_eq
  have e : 2 + 2 * (I.days * I.clients) = y.length := by rw [this]; ring
  rw [e, List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem proc_eq (h : EncodesUniform x I k) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    x.getD (2 + i * I.clients + a) 0 = I.pAt i a := by
  obtain ⟨y, rfl, hy⟩ := h
  have hl := hy.length_eq
  have h1 : 2 + i * I.clients + a < y.length := by
    have : (i + 1) * I.clients ≤ I.days * I.clients := Nat.mul_le_mul_right _ hi
    nlinarith
  rw [List.getD_append _ _ _ _ h1]
  have := hy.proc_eq ⟨i, hi⟩ ⟨a, ha⟩
  simp only [proc, hy.clientCount_eq] at this
  rw [this]
  exact (Instance.pAt_coe I ⟨i, hi⟩ ⟨a, ha⟩).symm

theorem due_eq (h : EncodesUniform x I k) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    x.getD (2 + I.days * I.clients + i * I.clients + a) 0 = I.dAt i a := by
  obtain ⟨y, rfl, hy⟩ := h
  have hl := hy.length_eq
  have h1 : 2 + I.days * I.clients + i * I.clients + a < y.length := by
    have : (i + 1) * I.clients ≤ I.days * I.clients := Nat.mul_le_mul_right _ hi
    nlinarith
  rw [List.getD_append _ _ _ _ h1]
  have := hy.due_eq ⟨i, hi⟩ ⟨a, ha⟩
  simp only [due, hy.clientCount_eq, hy.dayCount_eq] at this
  rw [this]
  exact (Instance.dAt_coe I ⟨i, hi⟩ ⟨a, ha⟩).symm

end Lax117284Proofs.ClientsWord
