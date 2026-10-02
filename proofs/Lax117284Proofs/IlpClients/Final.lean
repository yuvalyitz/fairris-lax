import Lax117284Proofs.IlpClients.Assemble

/-!
# Alg F Decides the Family

* `cert_complete`: a feasible program of the family has a certificate in the search space that
  decodes to a solution;
* `decode_sound`: conversely (`Decode.lean`);
* `feasible_iff_algF`: the decision theorem.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section




/-- The program of a `1 × 1` word `[1, 1, a, b]`, that is `a x = b`. -/
theorem feasible_one_by_one (a b : ℕ) :
    (decodeILP [1, 1, a, b]).Feasible ↔ (a = 0 → b = 0) ∧ (0 < a → a ∣ b) := by
  have hN : (decodeILP [1, 1, a, b]).N = 1 := rfl
  have hM : (decodeILP [1, 1, a, b]).M = 1 := rfl
  have hU : Unique (Fin (decodeILP [1, 1, a, b]).N) := inferInstanceAs (Unique (Fin 1))
  have ha' : ∀ (j : Fin (decodeILP [1, 1, a, b]).M) (i : Fin (decodeILP [1, 1, a, b]).N),
      (decodeILP [1, 1, a, b]).a j i = a := by
    intro j i
    have hj : j.val = 0 := by have : j.val < 1 := j.isLt; omega
    have hi : i.val = 0 := by have : i.val < 1 := i.isLt; omega
    simp [decodeILP, hj, hi]
  have hb' : ∀ j : Fin (decodeILP [1, 1, a, b]).M, (decodeILP [1, 1, a, b]).b j = b := by
    intro j
    have hj : j.val = 0 := by have : j.val < 1 := j.isLt; omega
    simp [decodeILP, hj]
  have hj0 : 0 < (decodeILP [1, 1, a, b]).M := by rw [hM]; omega
  constructor
  · rintro ⟨x, hx⟩
    have h := hx ⟨0, hj0⟩
    rw [hb', Fintype.sum_unique] at h
    simp only [ha'] at h
    constructor
    · intro ha; subst ha; simpa using h.symm
    · intro _; exact ⟨_, h.symm⟩
  · rintro ⟨h1, h2⟩
    by_cases ha : a = 0
    · refine ⟨fun _ => 0, fun j => ?_⟩
      rw [hb', Fintype.sum_unique]
      simp [ha', ha, h1 ha]
    · obtain ⟨y, hy⟩ := h2 (Nat.pos_of_ne_zero ha)
      refine ⟨fun _ => y, fun j => ?_⟩
      rw [hb', Fintype.sum_unique]
      simp [ha', hy]


/-- The words the reduction outputs: the programs of the family and the fixed word. -/
def IlpDomain (z : List ℕ) : Prop := (∃ n cnt B, z = ilpWord n cnt B) ∨ z = [1, 1, 0, 1]

/-- **Alg F accepts** a word: it is `ilpWord n cnt B` and a certificate decodes to a solution. -/
def AlgFAccepts (z : List ℕ) : Prop :=
  ∃ n cnt B, z = ilpWord n cnt B ∧
    ∃ ω : Cert, InBox n ω ∧ ∃ x, decode n cnt B ω = some x ∧ Checks n cnt B x



end

end Lax117284Proofs.IlpClients
