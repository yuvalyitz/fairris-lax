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

theorem nT_eq (n : ℕ) : Lax117284.IlpClients.nT n = IlpClients.nT n := rfl
theorem nZ_eq (n : ℕ) : Lax117284.IlpClients.nZ n = IlpClients.nZ n := rfl
theorem nV_eq (n : ℕ) : Lax117284.IlpClients.nV n = IlpClients.nV n := rfl
theorem nN_eq (n : ℕ) : Lax117284.IlpClients.nN n = IlpClients.nN n := rfl
theorem nM_eq (n : ℕ) : Lax117284.IlpClients.nM n = IlpClients.nM n := rfl

theorem coef_eq (n r c : ℕ) : Lax117284.IlpClients.coef n r c = IlpClients.coef n r c := rfl

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

theorem domain_iff (z : List ℕ) :
    z ∈ Lax117284.IlpClients.ilpClients.Domain ↔ IlpClients.IlpDomain z := by
  show ((∃ n cnt B, z = Lax117284.IlpClients.ilpWord n cnt B) ∨ z = [1, 1, 0, 1]) ↔ _
  simp only [ilpWord_eq]
  rfl

theorem zList_mem_domain (n m k : ℕ) (cnt : ℕ → ℕ) :
    ClientsILP.zList n m k cnt ∈ Lax117284.IlpClients.ilpClients.Domain :=
  Or.inl ⟨n, cnt, m - k, zList_eq n m k cnt⟩

theorem fixed_mem_domain : [1, 1, 0, 1] ∈ Lax117284.IlpClients.ilpClients.Domain := Or.inr rfl

theorem param_eq (z : List ℕ) :
    Lax117284.IlpClients.ilpClients.param z = (IlpClients.decodeILP z).N := rfl

theorem yes_iff (z : List ℕ) :
    Lax117284.IlpClients.ilpClients.Yes z ↔ (IlpClients.decodeILP z).Feasible := Iff.rfl

end Lax117284Proofs.IlpClientsBridge
