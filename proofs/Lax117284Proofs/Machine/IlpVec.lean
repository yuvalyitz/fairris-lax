import Lax117284Proofs.IlpClients.Box
import Mathlib.Algebra.BigOperators.Intervals

/-!
The search space of Alg F as vectors of digits, for the machine.

The machine enumerates *all* vectors `v : Fin D → [0, R)` with `R = Kn n + 1` and
`D = nN n + 2 n² + 1`, in the order of the numbers `t < R ^ D` whose base-`R` digits they are.
The digits `0 … nN n - 1` are the digits of the columns, the next `n²` and the next `n²` the entries
of `Hp` and `Hn`, and the last the denominator `δ`.  Every certificate of the finite box `BCert n`
of the math layer is among them (`exists_digits_of_bcert`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

noncomputable section

/-- The radix of the digits. -/
def Rd (n : ℕ) : ℕ := Kn n + 1

/-- The number of digits of a certificate. -/
def Dn (n : ℕ) : ℕ := nN n + 2 * (n * n) + 1

/-- The digit of `Hp i j`. -/
def hpIdx (n i j : ℕ) : ℕ := nN n + i * n + j

/-- The digit of `Hn i j`. -/
def hnIdx (n i j : ℕ) : ℕ := nN n + n * n + i * n + j

/-- The digit of `δ`. -/
def dlIdx (n : ℕ) : ℕ := nN n + 2 * (n * n)

/-- The certificate whose digits are `v`. -/
def certVec (n : ℕ) (v : ℕ → ℕ) : Cert where
  d c := if c < nN n then v c else 0
  Hp i j := if i < n ∧ j < n then v (hpIdx n i j) else 0
  Hn i j := if i < n ∧ j < n then v (hnIdx n i j) else 0
  δ := v (dlIdx n)

/-- The digit `q` of the number `t` in base `R`. -/
def digitsOf (R t q : ℕ) : ℕ := t / R ^ q % R

/-- The number whose digits are `v`. -/
def encR (R : ℕ) (v : ℕ → ℕ) (D : ℕ) : ℕ := ∑ q ∈ range D, v q * R ^ q

theorem hpIdx_lt {n i j : ℕ} (hi : i < n) (hj : j < n) : hpIdx n i j < nN n + n * n := by
  unfold hpIdx
  have : i * n + j < n * n := by nlinarith
  omega

theorem hnIdx_lt {n i j : ℕ} (hi : i < n) (hj : j < n) : hnIdx n i j < nN n + 2 * (n * n) := by
  unfold hnIdx
  have : i * n + j < n * n := by nlinarith
  omega

theorem dlIdx_lt (n : ℕ) : dlIdx n < Dn n := by unfold dlIdx Dn; omega

/-- A certificate depends on the digits below `Dn n` only. -/
theorem certVec_congr {n : ℕ} {v v' : ℕ → ℕ} (h : ∀ q < Dn n, v q = v' q) :
    certVec n v = certVec n v' := by
  have h1 : ∀ c, c < nN n → v c = v' c := fun c hc => h c (by unfold Dn; omega)
  have h2 : ∀ i j, i < n → j < n → v (hpIdx n i j) = v' (hpIdx n i j) := fun i j hi hj =>
    h _ (by have := hpIdx_lt hi hj; unfold Dn; omega)
  have h3 : ∀ i j, i < n → j < n → v (hnIdx n i j) = v' (hnIdx n i j) := fun i j hi hj =>
    h _ (by have := hnIdx_lt hi hj; unfold Dn; omega)
  have h4 : v (dlIdx n) = v' (dlIdx n) := h _ (dlIdx_lt n)
  unfold certVec
  congr 1
  · funext c; by_cases hc : c < nN n <;> simp [hc, h1]
  · funext i j
    by_cases hij : i < n ∧ j < n
    · simp [hij, h2 _ _ hij.1 hij.2]
    · simp [hij]
  · funext i j
    by_cases hij : i < n ∧ j < n
    · simp [hij, h3 _ _ hij.1 hij.2]
    · simp [hij]

theorem factorial_le_Kn (n : ℕ) : n.factorial ≤ Kn n := by
  have h1 : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
  have h2 : n ^ n ≤ (n + 1) ^ (n + 1) := by
    calc n ^ n ≤ (n + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ n) n
      _ ≤ (n + 1) ^ (n + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ n)
  unfold Kn
  omega

/-- The digits of a certificate of the finite box. -/
def vecOfBcert {n : ℕ} (b : BCert n) : ℕ → ℕ := fun q =>
  if h : q < nN n then ((b.1 ⟨q, h⟩ : Fin (Kn n + 1)) : ℕ)
  else if q < nN n + n * n then
    (if h : (q - nN n) / n < n ∧ (q - nN n) % n < n then
      ((b.2.1 ⟨(q - nN n) / n, h.1⟩ ⟨(q - nN n) % n, h.2⟩ : Fin (n.factorial + 1)) : ℕ) else 0)
  else if q < nN n + 2 * (n * n) then
    (if h : (q - nN n - n * n) / n < n ∧ (q - nN n - n * n) % n < n then
      ((b.2.2.1 ⟨(q - nN n - n * n) / n, h.1⟩ ⟨(q - nN n - n * n) % n, h.2⟩ :
        Fin (n.factorial + 1)) : ℕ) else 0)
  else ((b.2.2.2 : Fin n.factorial) : ℕ) + 1

theorem vecOfBcert_lt {n : ℕ} (b : BCert n) {q : ℕ} (hq : q < Dn n) : vecOfBcert b q < Rd n := by
  have hf := factorial_le_Kn n
  unfold vecOfBcert Rd
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact lt_of_lt_of_le (b.1 ⟨q, h1⟩).isLt le_rfl
  · have := (b.2.1 ⟨(q - nN n) / n, h3.1⟩ ⟨(q - nN n) % n, h3.2⟩).isLt; omega
  · omega
  · have := (b.2.2.1 ⟨(q - nN n - n * n) / n, h5.1⟩ ⟨(q - nN n - n * n) % n, h5.2⟩).isLt; omega
  · omega
  · have := b.2.2.2.isLt; omega

theorem certVec_vecOfBcert {n : ℕ} (b : BCert n) : certVec n (vecOfBcert b) = b.toCert := by
  unfold certVec BCert.toCert
  congr 1
  · funext c
    by_cases hc : c < nN n
    · simp [hc, vecOfBcert]
    · simp [hc]
  · funext i j
    by_cases hij : i < n ∧ j < n
    · have hn : 0 < n := by omega
      have hlt := hpIdx_lt hij.1 hij.2
      have e1 : (hpIdx n i j - nN n) / n = i := by
        unfold hpIdx
        rw [show nN n + i * n + j - nN n = i * n + j by omega, Nat.mul_comm i n,
          Nat.mul_add_div hn, Nat.div_eq_of_lt hij.2]; simp
      have e2 : (hpIdx n i j - nN n) % n = j := by
        unfold hpIdx
        rw [show nN n + i * n + j - nN n = i * n + j by omega, Nat.mul_comm i n,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hij.2]
      have hnl : ¬ hpIdx n i j < nN n := by unfold hpIdx; omega
      simp only [hij, and_self, dite_true]
      unfold vecOfBcert
      rw [dif_neg hnl, if_pos hlt]
      simp only [e1, e2]
      simp [hij]
    · simp [hij]
  · funext i j
    by_cases hij : i < n ∧ j < n
    · have hn : 0 < n := by omega
      have hlt := hnIdx_lt hij.1 hij.2
      have e1 : (hnIdx n i j - nN n - n * n) / n = i := by
        unfold hnIdx
        rw [show nN n + n * n + i * n + j - nN n - n * n = i * n + j by omega, Nat.mul_comm i n,
          Nat.mul_add_div hn, Nat.div_eq_of_lt hij.2]; simp
      have e2 : (hnIdx n i j - nN n - n * n) % n = j := by
        unfold hnIdx
        rw [show nN n + n * n + i * n + j - nN n - n * n = i * n + j by omega, Nat.mul_comm i n,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hij.2]
      have hnl : ¬ hnIdx n i j < nN n := by unfold hnIdx; omega
      have hnl2 : ¬ hnIdx n i j < nN n + n * n := by unfold hnIdx; omega
      simp only [hij, and_self, dite_true]
      unfold vecOfBcert
      rw [dif_neg hnl, if_neg hnl2, if_pos hlt]
      simp only [e1, e2]
      simp [hij]
    · simp [hij]
  · have hnl : ¬ dlIdx n < nN n := by unfold dlIdx; omega
    have hnl2 : ¬ dlIdx n < nN n + n * n := by unfold dlIdx; omega
    have hnl3 : ¬ dlIdx n < nN n + 2 * (n * n) := by unfold dlIdx; omega
    show vecOfBcert b (dlIdx n) = _
    unfold vecOfBcert
    rw [dif_neg hnl, if_neg hnl2, if_neg hnl3]

/-! ### Digits of numbers -/

theorem encR_succ' (R : ℕ) (v : ℕ → ℕ) (D : ℕ) :
    encR R v (D + 1) = v 0 + R * encR R (fun q => v (q + 1)) D := by
  unfold encR
  rw [Finset.sum_range_succ' _ D]
  simp only [pow_succ, pow_zero, mul_one, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The number whose digits are `v` is below `R ^ D` and has the digits `v`. -/
theorem digits_encR {R : ℕ} (hR : 0 < R) :
    ∀ (D : ℕ) (v : ℕ → ℕ), (∀ q < D, v q < R) →
      encR R v D < R ^ D ∧ ∀ q < D, digitsOf R (encR R v D) q = v q := by
  intro D
  induction D with
  | zero => intro v _; simp [encR]
  | succ D ih =>
    intro v hv
    obtain ⟨h1, h2⟩ := ih (fun q => v (q + 1)) (fun q hq => hv (q + 1) (by omega))
    rw [encR_succ']
    have hv0 := hv 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [pow_succ']
      have : v 0 + R * encR R (fun q => v (q + 1)) D < R * (encR R (fun q => v (q + 1)) D + 1) := by
        nlinarith
      exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ h1)
    · intro q hq
      unfold digitsOf
      rcases q with _ | q
      · simp only [pow_zero, Nat.div_one]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv0]
      · have hdiv : (v 0 + R * encR R (fun q => v (q + 1)) D) / R = encR R (fun q => v (q + 1)) D := by
          rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt hv0]; simp
        rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        exact h2 q (by omega)

/-- **Every vector of digits below `R` is the vector of digits of a number below `R ^ D`.** -/
theorem exists_number_of_digits {R : ℕ} (hR : 0 < R) (D : ℕ) (v : ℕ → ℕ) (hv : ∀ q < D, v q < R) :
    ∃ t < R ^ D, ∀ q < D, digitsOf R t q = v q :=
  ⟨encR R v D, (digits_encR hR D v hv).1, (digits_encR hR D v hv).2⟩

/-- **Every certificate of the finite box is the certificate of the digits of a number below
`Rd n ^ Dn n`.** -/
theorem exists_digits_of_bcert {n : ℕ} (b : BCert n) :
    ∃ t < Rd n ^ Dn n, certVec n (digitsOf (Rd n) t) = b.toCert := by
  obtain ⟨t, ht, hd⟩ := exists_number_of_digits (R := Rd n) (by unfold Rd; omega) (Dn n)
    (vecOfBcert b) (fun q hq => vecOfBcert_lt b hq)
  refine ⟨t, ht, ?_⟩
  rw [← certVec_vecOfBcert b]
  exact certVec_congr fun q hq => hd q hq

/-- The digits of a number below `R ^ D` are below `R`. -/
theorem digitsOf_lt {R : ℕ} (hR : 0 < R) (t q : ℕ) : digitsOf R t q < R := Nat.mod_lt _ hR

end

end Lax117284Proofs.Machine.Ilp
