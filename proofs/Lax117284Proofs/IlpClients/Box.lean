import Lax117284Proofs.IlpClients.Bounds

/-!
# The search space of Alg F as a finite type

`BCert n` is the finite set of certificates: a digit in `[0, K]` for each of the `nN n` columns, two
`n × n` matrices with entries in `[0, n!]`, and `δ ∈ [1, n!]`.  Its cardinality is
`(K+1)^N (n!+1)^(2 n²) n!` (`card_bcert`), and Alg F is complete on it (`cert_complete_box`).
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

/-- The certificates of the search space, as a finite type: `δ - 1` is stored. -/
def BCert (n : ℕ) : Type :=
  (Fin (nN n) → Fin (Kn n + 1)) × (Fin n → Fin n → Fin (n.factorial + 1)) ×
    (Fin n → Fin n → Fin (n.factorial + 1)) × Fin n.factorial

instance (n : ℕ) : Fintype (BCert n) := by unfold BCert; infer_instance

/-- **The size of the search space.** -/
theorem card_bcert (n : ℕ) :
    Fintype.card (BCert n) = (Kn n + 1) ^ nN n * (n.factorial + 1) ^ (2 * n ^ 2) * n.factorial := by
  unfold BCert
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- The certificate of a finite-type certificate. -/
def BCert.toCert {n : ℕ} (b : BCert n) : Cert where
  d c := if h : c < nN n then ((b.1 ⟨c, h⟩ : Fin (Kn n + 1)) : ℕ) else 0
  Hp i j := if h : i < n ∧ j < n then ((b.2.1 ⟨i, h.1⟩ ⟨j, h.2⟩ : Fin (n.factorial + 1)) : ℕ) else 0
  Hn i j := if h : i < n ∧ j < n then ((b.2.2.1 ⟨i, h.1⟩ ⟨j, h.2⟩ : Fin (n.factorial + 1)) : ℕ) else 0
  δ := ((b.2.2.2 : Fin n.factorial) : ℕ) + 1

theorem BCert.inBox {n : ℕ} (b : BCert n) : InBox n b.toCert := by
  refine ⟨fun c hc => ?_, fun i hi j hj => ?_, ?_, ?_⟩
  · simp only [BCert.toCert, dif_pos hc]
    exact Nat.lt_succ_iff.mp (b.1 ⟨c, hc⟩).isLt
  · simp only [BCert.toCert, dif_pos (And.intro hi hj)]
    exact ⟨Nat.lt_succ_iff.mp (b.2.1 ⟨i, hi⟩ ⟨j, hj⟩).isLt,
      Nat.lt_succ_iff.mp (b.2.2.1 ⟨i, hi⟩ ⟨j, hj⟩).isLt⟩
  · show 1 ≤ (b.2.2.2 : ℕ) + 1; omega
  · show (b.2.2.2 : ℕ) + 1 ≤ n.factorial
    exact b.2.2.2.isLt

/-- A certificate of the box, as a finite-type certificate. -/
def BCert.ofCert {n : ℕ} (ω : Cert) (hω : InBox n ω) : BCert n :=
  (fun c => ⟨ω.d c, Nat.lt_succ_of_le (hω.1 c c.isLt)⟩,
   fun i j => ⟨ω.Hp i j, Nat.lt_succ_of_le (hω.2.1 i i.isLt j j.isLt).1⟩,
   fun i j => ⟨ω.Hn i j, Nat.lt_succ_of_le (hω.2.1 i i.isLt j j.isLt).2⟩,
   ⟨ω.δ - 1, by have := hω.2.2.1; have := hω.2.2.2; omega⟩)

theorem BCert.toCert_ofCert {n : ℕ} (ω : Cert) (hω : InBox n ω)
    (hd : ∀ c, nN n ≤ c → ω.d c = 0)
    (hH : ∀ i j, (n ≤ i ∨ n ≤ j) → ω.Hp i j = 0 ∧ ω.Hn i j = 0) :
    (BCert.ofCert ω hω).toCert = ω := by
  have hδ := hω.2.2.1
  obtain ⟨d, Hp, Hn, δ⟩ := ω
  simp only at hd hH hδ
  simp only [BCert.toCert, BCert.ofCert, Cert.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext c
    by_cases h : c < nN n
    · simp [h]
    · simp [h, hd c (not_lt.mp h)]
  · funext i j
    by_cases h : i < n ∧ j < n
    · simp [h]
    · simp only [h, dif_neg, not_false_eq_true]
      have : n ≤ i ∨ n ≤ j := by omega
      exact ((hH i j this).1).symm
  · funext i j
    by_cases h : i < n ∧ j < n
    · simp [h]
    · simp only [h, dif_neg, not_false_eq_true]
      have : n ≤ i ∨ n ≤ j := by omega
      exact ((hH i j this).2).symm
  · omega

section Complete

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {Y : ℕ → ℕ}

/-- **Completeness on the finite search space** (for a normalised solution). -/
theorem cert_complete_box_of_sol (hY : Sol n cnt B Y) :
    ∃ b : BCert n, ∃ x, decode n cnt B b.toCert = some x ∧ Checks n cnt B x := by
  obtain ⟨hcard, H, δ, hδ1, hδn, hHb, hHD⟩ :=
    exists_left_inverse (Dmat n Y) (fun j c => Dmat_abs_le j c) (Dmat_indep hY)
  have hcard' : (Ext n (dY n Y)).card ≤ n := by simpa using hcard
  have hbox := inBox_certOf (Y := Y) (H := H) hδ1 hδn hHb
  refine ⟨BCert.ofCert (certOf n Y H δ) hbox, xval n cnt B (certOf n Y H δ), ?_, ?_⟩
  · rw [BCert.toCert_ofCert (certOf n Y H δ) hbox]
    · unfold decode
      rw [if_pos (guards_hold hY hcard' hHD hδ1)]
    · intro c hc
      show min (Y c) (Kn n) = 0
      have : Y c = 0 := hY.dead c (fun h => by have := h.1; omega)
      simp [this]
    · intro i j hij
      constructor
      · show HpOf n Y H i j = 0
        unfold HpOf
        split_ifs with h
        · have hspec := Classical.choose_spec h
          have hcl := (rk_lt_card hspec.1).trans_le hcard'
          have hj : n ≤ j := by
            rcases hij with h1 | h1
            · exfalso; rw [hspec.2] at hcl; omega
            · exact h1
          have : HcOf n Y H (Classical.choose h) j = 0 := by
            unfold HcOf; split_ifs <;> first | rfl | omega
          rw [this]; rfl
        · rfl
      · show HnOf n Y H i j = 0
        unfold HnOf
        split_ifs with h
        · have hspec := Classical.choose_spec h
          have hcl := (rk_lt_card hspec.1).trans_le hcard'
          have hj : n ≤ j := by
            rcases hij with h1 | h1
            · exfalso; rw [hspec.2] at hcl; omega
            · exact h1
          have : HcOf n Y H (Classical.choose h) j = 0 := by
            unfold HcOf; split_ifs <;> first | rfl | omega
          rw [this]; rfl
        · rfl
  · intro r hr
    rw [← hY.row r hr]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [xval_eq hY hHD hδ1 c]

end Complete

/-- **Completeness of Alg F on the finite search space.** -/
theorem cert_complete_box {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ}
    (h : (decodeILP (ilpWord n cnt B)).Feasible) :
    ∃ b : BCert n, ∃ x, decode n cnt B b.toCert = some x ∧ Checks n cnt B x := by
  obtain ⟨Y, hY⟩ := sol_of_feasible ((feasible_iff_nat n cnt B).mp h)
  exact cert_complete_box_of_sol hY

/-- **The decision theorem on the finite search space**: the program of `ilpWord n cnt B` is
feasible if and only if one of the `(K+1)^N (n!+1)^(2 n²) n!` certificates decodes to a solution. -/
theorem feasible_iff_algF_box (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    (decodeILP (ilpWord n cnt B)).Feasible ↔
      ∃ b : BCert n, ∃ x, decode n cnt B b.toCert = some x ∧ Checks n cnt B x :=
  ⟨cert_complete_box, fun ⟨_, _, hd, hx⟩ => decode_sound hd hx⟩

end

end Lax117284Proofs.IlpClients
