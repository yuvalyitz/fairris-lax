import Lax117284Proofs.IlpClients.Assemble

/-!
# Alg F decides the family

* `cert_complete`: a feasible program of the family has a certificate in the search space that
  decodes to a solution;
* `decode_sound`: conversely (`Decode.lean`);
* `feasible_iff_algF`: the decision theorem.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

/-- **Completeness for a normalised solution.** -/
theorem cert_complete_of_sol {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ} (hY : Sol n cnt B Y) :
    ∃ ω : Cert, InBox n ω ∧ ∃ x, decode n cnt B ω = some x ∧ Checks n cnt B x := by
  obtain ⟨hcard, H, δ, hδ1, hδn, hHb, hHD⟩ :=
    exists_left_inverse (Dmat n Y) (fun j c => Dmat_abs_le j c) (Dmat_indep hY)
  have hcard' : (Ext n (dY n Y)).card ≤ n := by simpa using hcard
  refine ⟨certOf n Y H δ, inBox_certOf hδ1 hδn hHb, xval n cnt B (certOf n Y H δ), ?_, ?_⟩
  · unfold decode
    rw [if_pos (guards_hold hY hcard' hHD hδ1)]
  · intro r hr
    rw [← hY.row r hr]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [xval_eq hY hHD hδ1 c]

/-- **Completeness of Alg F.** -/
theorem cert_complete {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ}
    (h : (decodeILP (ilpWord n cnt B)).Feasible) :
    ∃ ω : Cert, InBox n ω ∧ ∃ x, decode n cnt B ω = some x ∧ Checks n cnt B x := by
  obtain ⟨Y, hY⟩ := sol_of_feasible ((feasible_iff_nat n cnt B).mp h)
  exact cert_complete_of_sol hY

/-- **The decision theorem for the family**: the program of the word `ilpWord n cnt B` is feasible
if and only if some certificate of the search space decodes to a solution of it. -/
theorem feasible_iff_algF (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    (decodeILP (ilpWord n cnt B)).Feasible ↔
      ∃ ω : Cert, InBox n ω ∧ ∃ x, decode n cnt B ω = some x ∧ Checks n cnt B x :=
  ⟨cert_complete, fun ⟨_, _, _, hd, hx⟩ => decode_sound hd hx⟩

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

/-- **The fixed word is infeasible**: `0 · x = 1`. -/
theorem not_feasible_fixed : ¬ (decodeILP [1, 1, 0, 1]).Feasible := by
  rw [feasible_one_by_one]
  intro h
  exact absurd (h.1 rfl) (by decide)

/-- The words the reduction outputs: the programs of the family and the fixed word. -/
def IlpDomain (z : List ℕ) : Prop := (∃ n cnt B, z = ilpWord n cnt B) ∨ z = [1, 1, 0, 1]

/-- **Alg F accepts** a word: it is `ilpWord n cnt B` and a certificate decodes to a solution. -/
def AlgFAccepts (z : List ℕ) : Prop :=
  ∃ n cnt B, z = ilpWord n cnt B ∧
    ∃ ω : Cert, InBox n ω ∧ ∃ x, decode n cnt B ω = some x ∧ Checks n cnt B x

/-- **Alg F decides the family** (and the fixed word `[1,1,0,1]`, which it rejects). -/
theorem feasible_iff_algF_domain (z : List ℕ) (hz : IlpDomain z) :
    (decodeILP z).Feasible ↔ AlgFAccepts z := by
  -- soundness holds for every decomposition of the word
  have hsound : AlgFAccepts z → (decodeILP z).Feasible := by
    rintro ⟨n', cnt', B', h, ω, -, x, hd, hx⟩
    have hf := decode_sound hd hx
    rw [← h] at hf
    exact hf
  constructor
  · intro hf
    rcases hz with ⟨n, cnt, B, rfl⟩ | rfl
    · obtain ⟨ω, hω, hrest⟩ := (feasible_iff_algF n cnt B).mp hf
      exact ⟨n, cnt, B, rfl, ω, hω, hrest⟩
    · exact absurd hf not_feasible_fixed
  · exact hsound

/-- Feasibility of the program of the family, as membership in the monoid of the columns of
`Amat n` (matching the generic `monoid_iff`). -/
theorem feasible_iff_monoid (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    (decodeILP (ilpWord n cnt B)).Feasible ↔
      ∃ z : Fin (nN n) → ℕ, ∀ r : Fin (nM n), ∑ c, Amat n r c * z c = rhs n cnt B r := by
  rw [feasible_iff_nat]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun c => y c.val, fun r => ?_⟩
    rw [← hy r.val r.isLt, ← Fin.sum_univ_eq_sum_range (fun c => coef n r.val c * y c)]
    rfl
  · rintro ⟨z, hz⟩
    refine ⟨fun c => if h : c < nN n then z ⟨c, h⟩ else 0, fun r hr => ?_⟩
    rw [← hz ⟨r, hr⟩, ← Fin.sum_univ_eq_sum_range (fun c => coef n r c *
      (if h : c < nN n then z ⟨c, h⟩ else 0))]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Amat]

end

end Lax117284Proofs.IlpClients
