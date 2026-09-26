import Lax117284Proofs.Machine.ClMainBound

/-!
The cost of the main program, as a function of the word, and its bound.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

/-- The cost of the builder, as a function of the numbers of clients and days. -/
def bcNM (n m : ℕ) : ℕ :=
  100 + ((((204 * (n * n) + 40) + 4) * m + 6) +
    ((((200 + 4) * (n * n) + 6) + 2 + 60 + 4) * nV n + 6) +
    ((((10 + 10 + 10 + (100 + 10) + 100 + 10) + 20) + 4) * zLen n + 6))

/-- The cost of the branch that builds. -/
def KfitNM (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 n m : ℕ) : ℕ :=
  bcNM n m + (44 * (c1 * (2 * zLen n + m + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) +
    (20 * P.length + 101 + ((c' * g' (nN n) * (zLen n + 1) ^ c' *
      (Nat.clog 2 (c1 * (2 * zLen n + m + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 + 4)) + 3

/-- The cost of the main program on the word `x`. -/
def Kx (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + ((90 * x.length + 300) +
    (4 + (if Q (x.getD 0 0) + 2 ≤ x.length then KfitNM P c' g' c1 (x.getD 0 0) (x.getD 1 0) + 30
      else ClBrute.bruteCost (x.getD 1 0) (x.getD 0 0) + 3)))

theorem bcNM_le {n m N : ℕ} (hnn : n * n ≤ N) (hm : m ≤ N) (hV : nV n ≤ N) (hz : zLen n ≤ N) :
    bcNM n m ≤ 1000 * (N + 1) ^ 2 := by
  unfold bcNM
  have h1 : n * n * m ≤ N * N := Nat.mul_le_mul hnn hm
  have h2 : n * n * nV n ≤ N * N := Nat.mul_le_mul hnn hV
  nlinarith

/-- The constant that bounds the `w + 1` factor of the oracle. -/
def Mc (c' c1 : ℕ) : ℕ := (2 * c1 * 3 ^ c') ^ c'

theorem KfitNM_le (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1) {n m N : ℕ}
    (hnn : n * n ≤ N) (hm : m ≤ N) (hV : nV n ≤ N) (hz : zLen n ≤ N) :
    KfitNM P c' g' c1 n m ≤ (1000 + 20 * P.length + 10 * c' + 792) * (N + 1) ^ 2 +
      (604 * c' * g' (nN n) * Mc c' c1) * (N + 1) ^ (c' + c' * c') + (44 * c1 * 3 ^ c') * (N + 1) ^ c' := by
  have hb := bcNM_le hnn hm hV hz
  have hE : c1 - 1 = c' := by omega
  have hp : (zLen n + 1) ^ c' ≤ (N + 1) ^ c' := Nat.pow_le_pow_left (by omega) _
  have h1 : (2 * zLen n + m + 1) ^ c' ≤ 3 ^ c' * (N + 1) ^ c' := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have h1' : c1 * (2 * zLen n + m + 1) ^ c' ≤ c1 * (3 ^ c' * (N + 1) ^ c') := Nat.mul_le_mul_left _ h1
  have hpos : 1 ≤ c1 * (2 * zLen n + m + 1) ^ c' :=
    Nat.mul_pos (by omega) (Nat.one_le_pow _ _ (by omega))
  have hw : Nat.clog 2 (c1 * (2 * zLen n + m + 1) ^ c') + 1 ≤ 2 * (c1 * (2 * zLen n + m + 1) ^ c') := by
    have := pow_clog_le hpos
    have := @Nat.lt_two_pow_self (Nat.clog 2 (c1 * (2 * zLen n + m + 1) ^ c'))
    omega
  have hw2 : (Nat.clog 2 (c1 * (2 * zLen n + m + 1) ^ c') + 1) ^ c' ≤ Mc c' c1 * (N + 1) ^ (c' * c') := by
    calc _ ≤ (2 * (c1 * (3 ^ c' * (N + 1) ^ c'))) ^ c' :=
          Nat.pow_le_pow_left (by omega) _
      _ = (2 * c1 * 3 ^ c') ^ c' * ((N + 1) ^ c') ^ c' := by
          have e : 2 * (c1 * (3 ^ c' * (N + 1) ^ c')) = 2 * c1 * 3 ^ c' * (N + 1) ^ c' := by ring
          rw [e, mul_pow]
      _ = Mc c' c1 * (N + 1) ^ (c' * c') := by rw [← pow_mul]; rfl
  have hT : c' * g' (nN n) * (zLen n + 1) ^ c' *
      (Nat.clog 2 (c1 * (2 * zLen n + m + 1) ^ c') + 1) ^ c' ≤
      c' * g' (nN n) * (N + 1) ^ c' * (Mc c' c1 * (N + 1) ^ (c' * c')) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hw2
  have hT' : c' * g' (nN n) * (N + 1) ^ c' * (Mc c' c1 * (N + 1) ^ (c' * c')) =
      c' * g' (nN n) * Mc c' c1 * (N + 1) ^ (c' + c' * c') := by ring
  have h2 : (N + 1) ≤ (N + 1) ^ 2 := by nlinarith
  have h3 : 1 ≤ (N + 1) ^ 2 := by nlinarith
  have h4 : c1 * (2 * zLen n + m + 1) ^ c' ≤ 44 * 0 + c1 * (3 ^ c' * (N + 1) ^ c') := by omega
  unfold KfitNM
  rw [hE]
  nlinarith

theorem Kx_fit_le (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1) {x : List ℕ}
    (hc : Q (x.getD 0 0) + 2 ≤ x.length) (hnn : x.getD 0 0 * x.getD 0 0 ≤ x.length)
    (hm : x.getD 1 0 ≤ x.length) (hV : nV (x.getD 0 0) ≤ x.length) (hz : zLen (x.getD 0 0) ≤ x.length) :
    Kx P c' g' c1 x ≤ (1000 + 20 * P.length + 10 * c' + 792 + 508) * (x.length + 1) ^ 2 +
      (604 * c' * g' (nN (x.getD 0 0)) * Mc c' c1) * (x.length + 1) ^ (c' + c' * c') +
      (44 * c1 * 3 ^ c') * (x.length + 1) ^ c' := by
  have := KfitNM_le P c' g' c1 hc1 hnn hm hV hz
  have h2 : (x.length + 1) ≤ (x.length + 1) ^ 2 := by nlinarith
  have h3 : 1 ≤ (x.length + 1) ^ 2 := by nlinarith
  unfold Kx
  rw [if_pos hc]
  nlinarith

/-- The bound on the cost when the word is too short to build in: a function of `n` alone. -/
def Gb (n : ℕ) : ℕ := 114 * (Q n + 2) + 367 + 5000 * 2 ^ (Q n + 2) * ((Q n + 2) + n + 2) ^ 2

theorem Kx_brute_le (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) {x : List ℕ}
    (hc : ¬ Q (x.getD 0 0) + 2 ≤ x.length) (hl : x.length = 3 + 2 * (x.getD 1 0 * x.getD 0 0)) :
    Kx P c' g' c1 x ≤ Gb (x.getD 0 0) := by
  unfold Kx Gb
  rw [if_neg hc]
  have hb := ClBrute.bruteCost_le (x.getD 1 0) (x.getD 0 0)
  generalize x.getD 0 0 = n at *
  generalize x.getD 1 0 = m at *
  have hR : m * n ≤ Q n + 2 := by omega
  have h1 : 2 ^ (m * n) ≤ 2 ^ (Q n + 2) := Nat.pow_le_pow_right (by norm_num) hR
  have h2 : (m * n + n + 2) ^ 2 ≤ ((Q n + 2) + n + 2) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have h3 : 5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2 ≤ 5000 * 2 ^ (Q n + 2) * ((Q n + 2) + n + 2) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  omega

end Lax117284Proofs.Machine.ClMain
