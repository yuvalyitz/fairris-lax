import Lax117284.IlpClients
import Lax117284Proofs.IlpClients.Box
import Lax117284Proofs.ClientsILPRaw

/-!
The family of integer programs of the concepts (`Lax117284.IlpClients`), the restatement of it in the
math layer (`Lax117284Proofs.IlpClients`) and the construction of the reduction
(`Lax117284Proofs.ClientsILP.zList`) are one and the same: the words agree.
-/

namespace Lax117284Proofs.IlpClientsBridge

open Lax117284Proofs



/-- The word of the concepts is the word of the math layer. -/
theorem ilpWord_eq (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    Lax117284.IlpClients.ilpWord n cnt B = IlpClients.ilpWord n cnt B :=
  (IlpClients.ilpWord_eq_append n cnt B).symm

/-- The word of the construction of the reduction is the word of the concepts. -/
theorem zList_eq (n m k : ℕ) (cnt : ℕ → ℕ) :
    ClientsILP.zList n m k cnt = Lax117284.IlpClients.ilpWord n cnt (m - k) := by
  rw [ilpWord_eq]
  exact IlpClients.zList_eq_ilpWord n m k cnt

theorem feasible_iff (z : List ℕ) :
    (Lax117284.IlpClients.decodeILP z).Feasible ↔ (IlpClients.decodeILP z).Feasible := Iff.rfl


theorem zList_mem_domain (n m k : ℕ) (cnt : ℕ → ℕ) :
    ClientsILP.zList n m k cnt ∈ Lax117284.IlpClients.ilpClients.Domain :=
  Or.inl ⟨n, cnt, m - k, zList_eq n m k cnt⟩

theorem fixed_mem_domain : [1, 1, 0, 1] ∈ Lax117284.IlpClients.ilpClients.Domain := Or.inr rfl



end Lax117284Proofs.IlpClientsBridge
