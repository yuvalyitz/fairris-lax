import Lax117284Proofs.Machine.ClMainFinal

/-!
The arithmetic of the last step: the values fit into a word of the length the fitting condition
gives, and the cost is within `c * g n * (|x| + 1) ^ c`.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284.ParameterizedComplexity Lax808846Proofs.Transfer

variable {P : Program} {c' c1 : ℕ} {g' : ℕ → ℕ} {x : List ℕ}

/-- The fitting condition, in terms of the largest entry. -/
theorem fits_Mx {c w : ℕ} (hx : x ∈ UniformInstances) (hf : Fits c w x) :
    c * (x.length + Mx x + 1) ^ c ≤ 2 ^ w := by
  obtain ⟨I, k, hdec⟩ := hx
  have hl := ClientsWord.len_eq hdec
  have h0 : 0 < x.length := by omega
  rcases Mx_mem_or_zero x with hm | hm
  · exact hf _ hm
  · have := hf (x.getD 0 0) (by rw [List.getD_eq_getElem _ _ h0]; exact List.getElem_mem h0)
    rw [hm]
    have : c * (x.length + 0 + 1) ^ c ≤ c * (x.length + x.getD 0 0 + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega

/-- The constant of the fitting condition. -/
def C0 (P : Program) (c1 : ℕ) : ℕ := 16 * c1 * 2 ^ (c1 - 1) + 101 + P.length + PB P

theorem Bx_le {c : ℕ} (hc1 : 1 ≤ c1) (hcE : c1 - 1 ≤ c) (hc : 1 ≤ c) (hl : 3 ≤ x.length) :
    Bx P c1 x ≤ C0 P c1 * (x.length + Mx x + 1) ^ c := by
  unfold Bx C0
  set a := x.length + Mx x + 1 with ha
  have ha4 : 4 ≤ a := by omega
  have h1 : (2 * x.length + Mx x + 1) ^ (c1 - 1) ≤ 2 ^ (c1 - 1) * a ^ c := by
    calc (2 * x.length + Mx x + 1) ^ (c1 - 1) ≤ (2 * a) ^ (c1 - 1) :=
          Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (c1 - 1) * a ^ (c1 - 1) := mul_pow _ _ _
      _ ≤ 2 ^ (c1 - 1) * a ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcE)
  have h2 : a ≤ a ^ c := Nat.le_self_pow (by omega) a
  have h3 : 1 ≤ a ^ c := Nat.one_le_pow _ _ (by omega)
  have h4 : c1 * (2 * x.length + Mx x + 1) ^ (c1 - 1) ≤ c1 * (2 ^ (c1 - 1) * a ^ c) :=
    Nat.mul_le_mul_left _ h1
  have h5 : P.length + PB P ≤ (P.length + PB P) * a ^ c := Nat.le_mul_of_pos_right _ h3
  have h6 : 65 ≤ 65 * a ^ c := Nat.le_mul_of_pos_right _ h3
  nlinarith

theorem fitsWords_of (hc1 : 1 ≤ c1) {c w : ℕ} (hx : x ∈ UniformInstances) (hf : Fits c w x)
    (hcE : c1 - 1 ≤ c) (hc0 : 1 ≤ c)
    (hc : 10 * C0 P c1 + (layoutF P c1).scalars.length + 14 ≤ c) :
    (layoutF P c1).FitsWords (Bx P c1 x) w := by
  have hfM := fits_Mx hx hf
  obtain ⟨I, k, hdec⟩ := hx
  have hl := ClientsWord.len_eq hdec
  have hB := Bx_le (P := P) hc1 hcE hc0 (by omega : 3 ≤ x.length)
  have ha : 4 ≤ x.length + Mx x + 1 := by omega
  set a := (x.length + Mx x + 1) ^ c with ha'
  have ha1 : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  set S := (layoutF P c1).scalars.length with hS
  have hspan : (layoutF P c1).span (Bx P c1 x) = 12 + 2 + S + 10 * Bx P c1 x := by
    show 12 + 2 + S + arrs10.length * Bx P c1 x = _
    rw [show arrs10.length = 10 from rfl]
  have h1 : 10 * (C0 P c1 * a) + (S + 14) * a ≤ c * a := by nlinarith
  have h2 : (14 + S) ≤ (S + 14) * a := by nlinarith
  have h3 : 1 < Bx P c1 x := by unfold Bx; omega
  refine fitsWords_of_max_le h3 ?_
  rw [max_le_iff]
  constructor
  · have : C0 P c1 * a ≤ c * a := by nlinarith [Nat.zero_le (C0 P c1 * a)]
    omega
  · rw [hspan]; nlinarith

/-- The function of the parameter that bounds the cost. -/
def Gt (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 n : ℕ) : ℕ :=
  (10 * (1000 + 20 * P.length + 10 * c' + 792 + 508) + 1) + 6040 * c' * g' (nN n) * Mc c' c1 + 440 * c1 * 3 ^ c' +
    (10 * Gb n + 1)

theorem time_le {c : ℕ} (hc1 : c1 = c' + 1) (hx : x ∈ UniformInstances) (hc2 : 2 ≤ c) (hcc : c' ≤ c) (hcD : c' + c' * c' ≤ c) :
    10 * Kx P c' g' c1 x + 1 ≤ c * Gt P c' g' c1 (x.getD 0 0) * (x.length + 1) ^ c := by
  obtain ⟨I, k, hdec⟩ := hx
  have hl := ClientsWord.len_eq hdec
  have hn : x.getD 0 0 = I.clients := ClientsWord.x0 hdec
  have hm : x.getD 1 0 = I.days := ClientsWord.x1 hdec
  have ha1 : 1 ≤ x.length + 1 := by omega
  have hpc : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have hp2 : (x.length + 1) ^ 2 ≤ (x.length + 1) ^ c := Nat.pow_le_pow_right (by omega) hc2
  have hpc' : (x.length + 1) ^ c' ≤ (x.length + 1) ^ c := Nat.pow_le_pow_right (by omega) hcc
  have hpD : (x.length + 1) ^ (c' + c' * c') ≤ (x.length + 1) ^ c := Nat.pow_le_pow_right (by omega) hcD
  by_cases hc : Q (x.getD 0 0) + 2 ≤ x.length
  · rw [hn] at hc
    have hn1 : 1 ≤ I.clients := by
      by_contra h0
      have : I.clients = 0 := by omega
      rw [this] at hc hl
      simp [Q] at hc hl
      omega
    have hz := zLen_le I.clients
    obtain ⟨-, -, hV, -, -, hnn, -, -⟩ := sizes_le_zLen I.clients
    have hT := (sizes_le_zLen I.clients).1
    have hmn : I.days ≤ I.days * I.clients := Nat.le_mul_of_pos_right _ hn1
    have hK := Kx_fit_le P c' g' c1 hc1 (x := x) (by rw [hn]; exact hc) (by rw [hn]; omega)
      (by rw [hm]; omega) (by rw [hn]; omega) (by rw [hn]; omega)
    rw [hn] at hK
    unfold Gt
    set a := (x.length + 1) with ha
    set G := g' (nN I.clients)
    rw [hn]
    have e1 : (1000 + 20 * P.length + 10 * c' + 792 + 508) * a ^ 2 ≤
        (1000 + 20 * P.length + 10 * c' + 792 + 508) * a ^ c := Nat.mul_le_mul_left _ hp2
    have e2 : (604 * c' * G * Mc c' c1) * a ^ (c' + c' * c') ≤ (604 * c' * G * Mc c' c1) * a ^ c :=
      Nat.mul_le_mul_left _ hpD
    have e2' : (44 * c1 * 3 ^ c') * a ^ c' ≤ (44 * c1 * 3 ^ c') * a ^ c := Nat.mul_le_mul_left _ hpc'
    have e3 : 10 * (1000 + 20 * P.length + 10 * c' + 792 + 508) + 1 + 6040 * c' * G * Mc c' c1 +
        440 * c1 * 3 ^ c' ≤ Gt P c' g' c1 I.clients := by unfold Gt; exact Nat.le_add_right _ _
    have step : 10 * Kx P c' g' c1 x + 1 ≤
        (10 * (1000 + 20 * P.length + 10 * c' + 792 + 508) + 1 + 6040 * c' * G * Mc c' c1 +
          440 * c1 * 3 ^ c') * a ^ c := by
      nlinarith [e1, e2, e2', hpc, hK]
    have step2 : (10 * (1000 + 20 * P.length + 10 * c' + 792 + 508) + 1 + 6040 * c' * G * Mc c' c1 +
        440 * c1 * 3 ^ c') * a ^ c ≤ Gt P c' g' c1 I.clients * a ^ c := Nat.mul_le_mul_right _ e3
    have step3 : Gt P c' g' c1 I.clients * a ^ c ≤ c * Gt P c' g' c1 I.clients * a ^ c := by
      apply Nat.mul_le_mul_right
      nlinarith [Nat.zero_le (Gt P c' g' c1 I.clients)]
    exact step.trans (step2.trans step3)
  · have hb := Kx_brute_le P c' g' c1 hc (by rw [hn, hm]; exact hl)
    rw [hn] at hb ⊢
    have e3 : 10 * Gb I.clients + 1 ≤ Gt P c' g' c1 I.clients := by
      unfold Gt; exact Nat.le_add_left _ _
    generalize Gt P c' g' c1 I.clients = Gv at *
    have h5 : Gv * 1 ≤ Gv * (x.length + 1) ^ c := Nat.mul_le_mul_left _ hpc
    have h6 : Gv * (x.length + 1) ^ c ≤ c * Gv * (x.length + 1) ^ c := by
      rw [mul_comm c Gv]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (by omega))
    have : 10 * Kx P c' g' c1 x + 1 ≤ Gv * 1 := by omega
    exact this.trans (h5.trans h6)

end Lax117284Proofs.Machine.ClMain
