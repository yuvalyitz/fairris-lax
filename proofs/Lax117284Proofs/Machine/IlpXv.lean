import Lax117284Proofs.IlpClients.Box
import Mathlib.Algebra.BigOperators.Intervals
import Lax117284Proofs.IlpClients.Extras
import Lax808846Proofs.Tactic
import Lax808846Proofs.Transfer

/-! ### `Lax117284Proofs.Machine.IlpVec` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.IlpNum` -/

section
/-!
The numbers of the machine: every quantity the machine holds is at most a fixed power of
`U = zLen n + v + 1`, where `v` bounds the entries of the right-hand side, and the bound `B` of
the machine is a larger power of `U`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

/-- The base of the bounds. -/
def Ub (n v : ℕ) : ℕ := zLen n + v + 1

/-- The numeric hypotheses of a run: `n ≥ 1`, the entries of the right-hand side are at most `v`,
and the bound `B` of the machine is above `U ^ 17`. -/
structure Hyp (n : ℕ) (cnt : ℕ → ℕ) (bb v B : ℕ) : Prop where
  n1 : 1 ≤ n
  hcnt : ∀ t < nT n, cnt t ≤ v
  hbb : bb ≤ v
  hB : Ub n v ^ 17 < B

theorem nV_le_nN'' (n : ℕ) : nV n ≤ nN n := by unfold nN; omega

theorem nZ_le_nV (n : ℕ) : nZ n ≤ nV n := by
  unfold nV
  have := nT_pos n
  exact Nat.le_mul_of_pos_left _ this

theorem nM_le_zLen (n : ℕ) : nM n ≤ zLen n := by unfold zLen; omega

theorem zLen_ge (n : ℕ) : 4 ≤ zLen n := by
  unfold zLen
  have h1 : 1 ≤ nM n := by unfold nM; have := nT_pos n; omega
  have h2 : 1 ≤ nN n := nN_pos n
  have : 1 ≤ nM n * nN n := Nat.mul_pos h1 h2
  omega

theorem nn_le_nT (n : ℕ) : n * n ≤ nT n := by
  unfold nT
  exact (Nat.lt_two_pow_self (n := n * n)).le

theorem rb_le_zLen (n : ℕ) : 2 + nM n * nN n ≤ zLen n := by unfold zLen; omega

theorem tn_le_zLen (n : ℕ) : 2 + nT n * nN n ≤ zLen n := by
  have : nT n * nN n ≤ nM n * nN n := Nat.mul_le_mul_right _ (by unfold nM; omega)
  have := rb_le_zLen n
  omega

theorem Dn_le_zLen (n : ℕ) : Dn n ≤ 3 * zLen n := by
  unfold Dn
  have h1 := nn_le_nT n
  have h2 := nT_le_nN n
  have h3 := nN_le_zLen n
  omega

/-- The index of a coefficient in the word. -/
theorem idx_lt_zLen {n t i : ℕ} (ht : t < nM n) (hi : i < nN n) : 2 + t * nN n + i < 2 + nM n * nN n := by
  have : (t + 1) * nN n ≤ nM n * nN n := Nat.mul_le_mul_right _ ht
  nlinarith

theorem ilpWord_length (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) : (ilpWord n cnt bb).length = zLen n := by
  simp [ilpWord, zLen]

/-- **A coefficient of the word.** -/
theorem ilpWord_coef (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) {r c : ℕ} (hr : r < nM n) (hc : c < nN n) :
    (ilpWord n cnt bb).getD (2 + r * nN n + c) 0 = coef n r c := by
  have hN' := nN_pos n
  have h1 : 2 + r * nN n + c < 2 + nM n * nN n := idx_lt_zLen hr hc
  rw [ilpWord_getD, if_pos (by unfold zLen; omega)]
  simp only [wordFun]
  rw [if_neg (by omega), if_neg (by omega), if_pos h1]
  have e : 2 + r * nN n + c - 2 = c + nN n * r := by rw [Nat.mul_comm r]; omega
  rw [e, Nat.add_mul_div_left _ _ hN', Nat.div_eq_of_lt hc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hc]
  simp

/-- **A right-hand side of the word.** -/
theorem ilpWord_rhs (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) {r : ℕ} (hr : r < nM n) :
    (ilpWord n cnt bb).getD (2 + nM n * nN n + r) 0 = rhs n cnt bb r := by
  rw [ilpWord_getD, if_pos (by unfold zLen; omega)]
  simp only [wordFun]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega


section
variable {n : ℕ} {cnt : ℕ → ℕ} {bb v B : ℕ}

theorem Hyp.U_pos (_ : Hyp n cnt bb v B) : 1 ≤ Ub n v := by unfold Ub; omega

theorem Hyp.U_ge (_ : Hyp n cnt bb v B) : 5 ≤ Ub n v := by
  unfold Ub; have := zLen_ge n; omega

/-- Anything at most a power `U ^ k`, `k ≤ 17`, is below `B`. -/
theorem Hyp.lt_B (h : Hyp n cnt bb v B) {x k : ℕ} (hx : x ≤ Ub n v ^ k) (hk : k ≤ 17) : x < B :=
  lt_of_le_of_lt (hx.trans (Nat.pow_le_pow_right h.U_pos hk)) h.hB

theorem Hyp.lt_U (h : Hyp n cnt bb v B) {x : ℕ} (hx : x ≤ Ub n v) : x < B :=
  h.lt_B (k := 1) (by simpa using hx) (by omega)

theorem Hyp.one_lt_B (h : Hyp n cnt bb v B) : 1 < B := h.lt_U (x := 1) h.U_pos

theorem Hyp.five_lt_B (h : Hyp n cnt bb v B) : 5 < B :=
  h.lt_U (x := 5) h.U_ge

theorem Hyp.NK_lt (h : Hyp n cnt bb v B) : nN n * Kn n + Kn n < B := by
  have h1 := nN_le_zLen n
  have h2 := Kn_le_zLen n
  have h5 := h.U_ge
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have : nN n * Kn n ≤ Ub n v * Ub n v := Nat.mul_le_mul (by omega) (by omega)
  refine h.lt_B (k := 3) ?_ (by omega)
  have hK : Kn n ≤ Ub n v := by omega
  have h3 : Ub n v * Ub n v * 2 ≤ Ub n v ^ 3 := by
    have : 2 ≤ Ub n v := by omega
    calc Ub n v * Ub n v * 2 ≤ Ub n v * Ub n v * Ub n v := Nat.mul_le_mul_left _ this
      _ = Ub n v ^ 3 := by ring
  nlinarith

theorem Hyp.SB_lt (h : Hyp n cnt bb v B) : nN n * (Kn n + v) + v < B := by
  have h1 := nN_le_zLen n
  have h2 := Kn_le_zLen n
  have h5 := h.U_ge
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have hv : v ≤ Ub n v := by unfold Ub; omega
  have : nN n * (Kn n + v) ≤ Ub n v * (Ub n v + Ub n v) := Nat.mul_le_mul (by omega) (by omega)
  refine h.lt_B (k := 3) ?_ (by omega)
  have h3 : Ub n v * (Ub n v + Ub n v) + Ub n v ≤ Ub n v ^ 3 := by
    have : 3 ≤ Ub n v := by omega
    nlinarith [Nat.mul_le_mul this this]
  omega

/-- The bound of a term of `P` and `Q`. -/
def Pterm (n vb : ℕ) : ℕ := Kn n * vb + Kn n * (nN n * (Kn n + vb))

/-- The bound of `P` and `Q`. -/
def Pbd (n vb : ℕ) : ℕ := n * Pterm n vb

theorem Ub_ge (n v : ℕ) : 5 ≤ Ub n v := by unfold Ub; have := zLen_ge n; omega

theorem Pbd_le_pow (n v : ℕ) : Pbd n v ≤ Ub n v ^ 5 := by
  have h1 := nN_le_zLen n
  have h2 := Kn_le_zLen n
  have h3 := n_succ_le_zLen n
  have h5 := Ub_ge n v
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have hv : v ≤ Ub n v := by unfold Ub; omega
  have hK : Kn n ≤ Ub n v := by omega
  have hN : nN n ≤ Ub n v := by omega
  have hn : n ≤ Ub n v := by omega
  have a1 : Kn n * v ≤ Ub n v * Ub n v := Nat.mul_le_mul hK hv
  have a2 : Kn n + v ≤ Ub n v + Ub n v := by omega
  have a3 : nN n * (Kn n + v) ≤ Ub n v * (Ub n v + Ub n v) := Nat.mul_le_mul hN a2
  have a4 : Kn n * (nN n * (Kn n + v)) ≤ Ub n v * (Ub n v * (Ub n v + Ub n v)) :=
    Nat.mul_le_mul hK a3
  have a5 : Pterm n v ≤ Ub n v * Ub n v + Ub n v * (Ub n v * (Ub n v + Ub n v)) := by
    unfold Pterm; omega
  have a6 : Pbd n v ≤ Ub n v * (Ub n v * Ub n v + Ub n v * (Ub n v * (Ub n v + Ub n v))) := by
    unfold Pbd; exact Nat.mul_le_mul hn a5
  have : 3 ≤ Ub n v := by omega
  have e : Ub n v * (Ub n v * Ub n v + Ub n v * (Ub n v * (Ub n v + Ub n v))) =
      Ub n v ^ 3 + 2 * Ub n v ^ 4 := by ring
  have e4 : Ub n v ^ 3 ≤ Ub n v ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have e5 : 3 * Ub n v ^ 4 ≤ Ub n v ^ 5 := by
    calc 3 * Ub n v ^ 4 ≤ Ub n v * Ub n v ^ 4 := Nat.mul_le_mul_right _ this
      _ = Ub n v ^ 5 := by ring
  omega

theorem Hyp.Pbd_lt (h : Hyp n cnt bb v B) : Pbd n v < B :=
  h.lt_B (Pbd_le_pow n v) (by omega)

theorem Hyp.Ebd_lt (h : Hyp n cnt bb v B) : nN n * Pbd n v + Pbd n v < B := by
  have h1 := nN_le_zLen n
  have h5 := h.U_ge
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have hN : nN n ≤ Ub n v := by omega
  have hP := Pbd_le_pow n v
  have a1 : nN n * Pbd n v ≤ Ub n v * Ub n v ^ 5 := Nat.mul_le_mul hN hP
  have e : Ub n v * Ub n v ^ 5 = Ub n v ^ 6 := by ring
  have e2 : Ub n v ^ 5 ≤ Ub n v ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 2 * Ub n v ^ 6 ≤ Ub n v ^ 7 := by
    calc 2 * Ub n v ^ 6 ≤ Ub n v * Ub n v ^ 6 := Nat.mul_le_mul_right _ (by omega)
      _ = Ub n v ^ 7 := by ring
  exact h.lt_B (k := 7) (by omega) (by omega)

theorem Hyp.XB_lt (h : Hyp n cnt bb v B) : Kn n + Pbd n v + v < B := by
  have h2 := Kn_le_zLen n
  have h5 := h.U_ge
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have hv : v ≤ Ub n v := by unfold Ub; omega
  have hP := Pbd_le_pow n v
  have e2 : Ub n v ≤ Ub n v ^ 5 := by
    calc Ub n v = Ub n v ^ 1 := (pow_one _).symm
      _ ≤ Ub n v ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have e3 : 3 * Ub n v ^ 5 ≤ Ub n v ^ 6 := by
    calc 3 * Ub n v ^ 5 ≤ Ub n v * Ub n v ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = Ub n v ^ 6 := by ring
  exact h.lt_B (k := 6) (by omega) (by omega)

/-- The bound of a value of the candidate. -/
def Xbd (n vb : ℕ) : ℕ := Kn n + Pbd n vb + vb

theorem Hyp.CB_lt (h : Hyp n cnt bb v B) : nN n * Xbd n v + Xbd n v < B := by
  have h1 := nN_le_zLen n
  have h5 := h.U_ge
  have hU : zLen n < Ub n v := by unfold Ub; omega
  have hN : nN n ≤ Ub n v := by omega
  have h2 := Kn_le_zLen n
  have hv : v ≤ Ub n v := by unfold Ub; omega
  have hP := Pbd_le_pow n v
  have e2 : Ub n v ≤ Ub n v ^ 5 := by
    calc Ub n v = Ub n v ^ 1 := (pow_one _).symm
      _ ≤ Ub n v ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : Xbd n v ≤ 3 * Ub n v ^ 5 := by unfold Xbd; omega
  have a1 : nN n * Xbd n v ≤ Ub n v * (3 * Ub n v ^ 5) := Nat.mul_le_mul hN hX
  have e : Ub n v * (3 * Ub n v ^ 5) = 3 * Ub n v ^ 6 := by ring
  rw [e] at a1
  have e3 : 3 * Ub n v ^ 5 ≤ 3 * Ub n v ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have e4 : 6 * Ub n v ^ 6 ≤ Ub n v ^ 8 := by
    have : 6 ≤ Ub n v * Ub n v := by nlinarith
    calc 6 * Ub n v ^ 6 ≤ (Ub n v * Ub n v) * Ub n v ^ 6 := Nat.mul_le_mul_right _ this
      _ = Ub n v ^ 8 := by ring
  have hsum : nN n * Xbd n v + Xbd n v ≤ 6 * Ub n v ^ 6 := by omega
  exact h.lt_B (k := 8) (le_trans hsum e4) (by omega)

theorem Hyp.zLen_lt (h : Hyp n cnt bb v B) : zLen n < B := h.lt_U (by unfold Ub; omega)
theorem Hyp.nN_lt (h : Hyp n cnt bb v B) : nN n < B :=
  h.lt_U (by have := nN_le_zLen n; unfold Ub; omega)
theorem Hyp.nM_lt (h : Hyp n cnt bb v B) : nM n < B :=
  h.lt_U (by have := nM_le_zLen n; unfold Ub; omega)
theorem Hyp.nT_lt (h : Hyp n cnt bb v B) : nT n < B :=
  h.lt_U (by have := nT_le_nN n; have := nN_le_zLen n; unfold Ub; omega)
theorem Hyp.nV_lt (h : Hyp n cnt bb v B) : nV n < B :=
  h.lt_U (by have := nV_le_nN'' n; have := nN_le_zLen n; unfold Ub; omega)
theorem Hyp.Kn_lt (h : Hyp n cnt bb v B) : Kn n < B :=
  h.lt_U (by have := Kn_le_zLen n; unfold Ub; omega)
theorem Hyp.Rd_lt (h : Hyp n cnt bb v B) : Rd n < B :=
  h.lt_U (by have := Kn_le_zLen n; unfold Ub Rd; omega)
theorem Hyp.n_lt (h : Hyp n cnt bb v B) : n < B :=
  h.lt_U (by have := n_succ_le_zLen n; unfold Ub; omega)
theorem Hyp.nn_lt (h : Hyp n cnt bb v B) : n * n < B :=
  h.lt_U (by have := nn_le_nT n; have := nT_le_nN n; have := nN_le_zLen n; unfold Ub; omega)
theorem Hyp.nZ_lt (h : Hyp n cnt bb v B) : nZ n < B :=
  h.lt_U (by have := nZ_le_nV n; have := nV_le_nN'' n; have := nN_le_zLen n; unfold Ub; omega)
theorem Hyp.rb_lt (h : Hyp n cnt bb v B) : 2 + nM n * nN n < B :=
  h.lt_U (by have := rb_le_zLen n; unfold Ub; omega)
theorem Hyp.tn_lt (h : Hyp n cnt bb v B) : 2 + nT n * nN n < B :=
  h.lt_U (by have := tn_le_zLen n; unfold Ub; omega)
theorem Hyp.Dn_lt (h : Hyp n cnt bb v B) : Dn n < B :=
  h.lt_B (k := 2) (by
    have := Dn_le_zLen n
    have h5 := h.U_ge
    have : zLen n < Ub n v := by unfold Ub; omega
    nlinarith) (by omega)

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpSpec` -/

section
/-!
What the machine computes for one certificate, as functions of the certificate.

The passes of the machine compute, from the digits `d` of a certificate `ω`:
* `kindOf n d c`: `3` for a live column with a small digit, `1` for a base, `2` for an extra, `0`
  for the rest (the zero columns and the large digit of nothing);
* `sigma`, `Sj` (as in the math layer);
* `wvF`: the value of the extras of rank below `n`, `0` for the others;
* `esF`: the sum of `wvF` over the extras of a type;
* `xF`: the candidate solution.
All of them are defined for every certificate, and agree with `xval` of the math layer once the
guard `(Ext n d).card ≤ n` holds (`xF_eq_xval`).  The machine accepts a certificate exactly when the
guard holds and `xF` solves the program (`AccSpec`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

open Classical

noncomputable section

/-- The kind of a column, as the machine computes it. -/
def kindOf (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : ℕ :=
  if isLive n c ∧ d c < Kn n then 3
  else if isBase n d c then 1 else if isExtra n d c then 2 else 0

/-- The value of an extra of rank below `n`; `0` for every other column. -/
def wvF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  if isExtra n ω.d c ∧ rk n ω.d c < n then wcol n cnt bb ω c else 0

/-- The sum of the values of the extras of type `t`. -/
def esF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t : ℕ) : ℕ :=
  ∑ c ∈ range (nN n), if isExtra n ω.d c ∧ tyOf n c = some t then wvF n cnt bb ω c else 0

/-- The candidate solution, as the machine computes it. -/
def xF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  if kindOf n ω.d c = 3 then ω.d c
  else if kindOf n ω.d c = 2 then wvF n cnt bb ω c
  else if kindOf n ω.d c = 1 then
    cp n cnt ω.d (tyIdx n c) - esF n cnt bb ω (tyIdx n c)
  else 0

/-- The certificate is accepted: at most `n` extras, and the candidate solves the program. -/
def AccSpec (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) : Prop :=
  (Ext n ω.d).card ≤ n ∧ Checks n cnt bb (xF n cnt bb ω)

/-- The number `t` is accepted: the certificate of its digits is. -/
def AccT (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (t : ℕ) : Prop :=
  AccSpec n cnt bb (certVec n (digitsOf (Rd n) t))

section
variable {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {ω : Cert}

theorem isExtra_mem_Ext {c : ℕ} (h : isExtra n ω.d c) : c ∈ Ext n ω.d := by
  unfold Ext
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  have := h.1
  unfold Lset at this
  exact (Finset.mem_filter.mp this).1

theorem wvF_eq_wcol (hE : (Ext n ω.d).card ≤ n) {c : ℕ} (h : isExtra n ω.d c) :
    wvF n cnt bb ω c = wcol n cnt bb ω c := by
  unfold wvF
  rw [if_pos ⟨h, (rk_lt_card (isExtra_mem_Ext h)).trans_le hE⟩]

theorem esF_eq_extraSum (hE : (Ext n ω.d).card ≤ n) (t : ℕ) :
    esF n cnt bb ω t = extraSum n cnt bb ω t := by
  unfold esF extraSum
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : isExtra n ω.d c ∧ tyOf n c = some t
  · rw [if_pos h, if_pos h, wvF_eq_wcol hE h.1]
  · rw [if_neg h, if_neg h]

theorem kindOf_eq_three {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 3 ↔ isLive n c ∧ d c < Kn n := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    split_ifs at h <;> omega
  · intro h; rw [if_pos h]

theorem kindOf_eq_one {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 1 ↔ isBase n d c := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    split_ifs at h <;> omega
  · intro h
    have hK : ¬ (isLive n c ∧ d c < Kn n) := by
      rintro ⟨-, hlt⟩
      have := ((mem_Lset_iff n d c).mp h.1).2
      omega
    rw [if_neg hK, if_pos h]

theorem kindOf_eq_two {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 2 ↔ isExtra n d c := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    split_ifs at h <;> omega
  · intro h
    have hK : ¬ (isLive n c ∧ d c < Kn n) := by
      rintro ⟨-, hlt⟩
      have := ((mem_Lset_iff n d c).mp h.1).2
      omega
    have hb : ¬ isBase n d c := h.2
    rw [if_neg hK, if_neg hb, if_pos h]

/-- **The candidate of the machine is the candidate of the math layer** once the guard holds. -/
theorem xF_eq_xval (hE : (Ext n ω.d).card ≤ n) (c : ℕ) : xF n cnt bb ω c = xval n cnt bb ω c := by
  unfold xF xval
  by_cases h3 : isLive n c ∧ ω.d c < Kn n
  · rw [if_pos (kindOf_eq_three.mpr h3), if_pos h3]
  · have h3' : ¬ kindOf n ω.d c = 3 := fun h => h3 (kindOf_eq_three.mp h)
    rw [if_neg h3', if_neg h3]
    by_cases h2 : isExtra n ω.d c
    · rw [if_pos (kindOf_eq_two.mpr h2), if_pos h2, wvF_eq_wcol hE h2]
    · have h2' : ¬ kindOf n ω.d c = 2 := fun h => h2 (kindOf_eq_two.mp h)
      rw [if_neg h2', if_neg h2]
      by_cases h1 : isBase n ω.d c
      · rw [if_pos (kindOf_eq_one.mpr h1), if_pos h1, esF_eq_extraSum hE]
      · have h1' : ¬ kindOf n ω.d c = 1 := fun h => h1 (kindOf_eq_one.mp h)
        rw [if_neg h1', if_neg h1]

theorem AccSpec_iff : AccSpec n cnt bb ω ↔
    (Ext n ω.d).card ≤ n ∧ Checks n cnt bb (xval n cnt bb ω) := by
  unfold AccSpec
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨hE, fun r hr => ?_⟩
    rw [← hc r hr]
    exact Finset.sum_congr rfl fun c _ => by rw [xF_eq_xval hE]
  · rintro ⟨hE, hc⟩
    refine ⟨hE, fun r hr => ?_⟩
    rw [← hc r hr]
    exact Finset.sum_congr rfl fun c _ => by rw [xF_eq_xval hE]

end

/-- **The search of the machine decides feasibility**: the program of `ilpWord n cnt bb` is feasible
if and only if one of the numbers below `Rd n ^ Dn n` is accepted. -/
theorem feasible_iff_accT (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) :
    (decodeILP (ilpWord n cnt bb)).Feasible ↔ ∃ t < Rd n ^ Dn n, AccT n cnt bb t := by
  constructor
  · intro h
    obtain ⟨b, x, hd, hx⟩ := cert_complete_box h
    obtain ⟨t, ht, hcert⟩ := exists_digits_of_bcert b
    refine ⟨t, ht, ?_⟩
    unfold AccT
    rw [hcert]
    rw [AccSpec_iff]
    unfold decode at hd
    split_ifs at hd with hG
    · have hx' : x = xval n cnt bb b.toCert := (Option.some.inj hd).symm
      refine ⟨hG.2.1, ?_⟩
      rw [← hx']
      exact hx
  · rintro ⟨t, -, hacc⟩
    have := (AccSpec_iff).mp hacc
    exact (feasible_iff_nat n cnt bb).mpr ⟨_, this.2⟩

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpProg` -/

section
/-!
Alg F as an IMP+ command.

The word of the integer program is read into the array `z`.  For the words of the family with
`n ≥ 1` clients the command counts through *all* vectors of `D = nN n + 2 n² + 1` digits below
`R = Kn n + 1` (the array `dg`, an odometer), and for each of them decodes a candidate solution
`xv` and checks it against the program stored in `z`.  Names:

* constants (set once): `N M zl n T Z V K R D rb bb tn nn`;
* arrays: `z` the word, `dg` the digits, `hl` (per type: has a large column so far), `kd` (the kind
  of each column), `rkA` (the rank of each column among the extras), `sg` (`sigma` per type),
  `S` (`Sj` per client), `wv` (values of the extras), `es` (`extraSum` per type), `xv` (the
  candidate).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp

abbrev V (s : String) : Expr := .var s
abbrev lit (n : ℕ) : Expr := .lit n
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- Right-nested sequence. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `x := 0; while x < m do c`. -/
abbrev forZ (x m : String) (c : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) c)

/-- `x := x + 1`. -/
abbrev bump (x : String) : Com := asg x (.add (V x) (lit 1))

/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltF (e f : Expr) : Expr := .sub (lit 1) (.sub (lit 1) (.sub f e))

/-- `1` when `e = f`, `0` otherwise. -/
abbrev eqF (e f : Expr) : Expr := .sub (lit 1) (.add (.sub e f) (.sub f e))

/-! ### Zeroing -/

/-- Set the first `len` cells of the array `a` to `0`. -/
def fillCom (a len : String) : Com :=
  forZ "fi" len (.seq (.store a (V "fi") (lit 0)) (bump "fi"))

/-! ### The kinds of the columns -/

/-- The kind of column `i`, and the flag of its type. -/
def kdBody : Com := seqs [
  asg "dv" (.get "dg" (V "i")),
  .ite (.lt (V "i") (V "V"))
    (seqs [
      asg "t" (.div (V "i") (V "Z")),
      asg "cf" (.get "z" (.add (.add (lit 2) (.mul (V "t") (V "N"))) (V "i"))),
      .ite (.eq (V "cf") (lit 1))
        (.ite (.lt (V "dv") (V "K"))
          (.store "kd" (V "i") (lit 3))
          (seqs [
            asg "hv" (.get "hl" (V "t")),
            .ite (.eq (V "hv") (lit 0))
              (.seq (.store "hl" (V "t") (lit 1)) (.store "kd" (V "i") (lit 1)))
              (.store "kd" (V "i") (lit 2))]))
        (.store "kd" (V "i") (lit 0))])
    (.ite (.lt (V "dv") (V "K"))
      (.store "kd" (V "i") (lit 3))
      (.store "kd" (V "i") (lit 2))),
  bump "i"]

def kdCom : Com := forZ "i" "N" kdBody

/-- The ranks of the columns among the extras; `E` ends the number of extras. -/
def rkBody : Com := seqs [
  .store "rkA" (V "i") (V "E"),
  .ite (.eq (.get "kd" (V "i")) (lit 2)) (asg "E" (.add (V "E") (lit 1))) .skip,
  bump "i"]

def rkCom : Com := .seq (asg "E" (lit 0)) (forZ "i" "N" rkBody)

/-! ### `sigma` -/

def sgBody : Com := seqs [
  .ite (.eq (.get "kd" (V "i")) (lit 3))
    (seqs [
      asg "t" (.div (V "i") (V "Z")),
      .store "sg" (V "t") (.add (.get "sg" (V "t")) (.get "dg" (V "i")))])
    .skip,
  bump "i"]

def sgCom : Com := forZ "i" "V" sgBody

/-! ### `Sj` -/

/-- Add `mv` times the coefficient of client `j` in column `i` to `S[j]`, for every client. -/
def addRowBody : Com := seqs [
  .store "S" (V "j")
    (.add (.get "S" (V "j"))
      (.mul (V "mv")
        (.get "z" (.add (.add (V "tn") (.mul (V "j") (V "N"))) (V "i"))))),
  bump "j"]

def addRow : Com := forZ "j" "n" addRowBody

def s1Body : Com := seqs [
  asg "mv" (.mul (.get "dg" (V "i")) (ltF (.get "dg" (V "i")) (V "K"))),
  addRow,
  bump "i"]

def s1Com : Com := forZ "i" "N" s1Body

/-- Add the rest of the demand of the type of the base `i` times its coefficients. -/
def s2Body : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  asg "mv" (.mul (eqF (.get "kd" (V "i")) (lit 1))
    (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))),
  addRow,
  bump "i"]

def s2Com : Com := forZ "i" "N" s2Body

/-! ### The values of the extras -/

/-- `P` and `Q` of row `r` of `H`. -/
def pqInner : Com := seqs [
  asg "hp" (.get "dg" (.add (.add (V "N") (.mul (V "r") (V "n"))) (V "j"))),
  asg "hn" (.get "dg" (.add (.add (.add (V "N") (V "nn")) (.mul (V "r") (V "n"))) (V "j"))),
  asg "sj" (.get "S" (V "j")),
  asg "P" (.add (V "P") (.add (.mul (V "hp") (V "bb")) (.mul (V "hn") (V "sj")))),
  asg "Q" (.add (V "Q") (.add (.mul (V "hp") (V "sj")) (.mul (V "hn") (V "bb")))),
  bump "j"]

def pqCom : Com := seqs [asg "P" (lit 0), asg "Q" (lit 0), forZ "j" "n" pqInner]

def wvBody : Com := seqs [
  asg "r" (.mul (.get "rkA" (V "i")) (ltF (.get "rkA" (V "i")) (V "n"))),
  pqCom,
  .store "wv" (V "i")
    (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (.get "rkA" (V "i")) (V "n")))
      (.div (.sub (V "P") (V "Q")) (V "dl"))),
  bump "i"]

def wvCom : Com := .seq (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn"))))) (forZ "i" "N" wvBody)

/-- The sums of the values of the extras of a type. -/
def esBody : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  .store "es" (V "t")
    (.add (.get "es" (V "t"))
      (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (V "i") (V "V"))) (.get "wv" (V "i")))),
  bump "i"]

def esCom : Com := forZ "i" "N" esBody

/-! ### The candidate -/

def xvBody : Com := seqs [
  asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))),
  .store "xv" (V "i")
    (.add
      (.add (.mul (eqF (.get "kd" (V "i")) (lit 3)) (.get "dg" (V "i")))
        (.mul (eqF (.get "kd" (V "i")) (lit 2)) (.get "wv" (V "i"))))
      (.mul (eqF (.get "kd" (V "i")) (lit 1))
        (.sub (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))
          (.get "es" (V "t"))))),
  bump "i"]

def xvCom : Com := forZ "i" "N" xvBody

/-! ### The check -/

def ckInner : Com := seqs [
  asg "acc" (.add (V "acc")
    (.mul (.get "z" (.add (V "rowb") (V "c"))) (.get "xv" (V "c")))),
  bump "c"]

def ckBody : Com := seqs [
  asg "rowb" (.add (lit 2) (.mul (V "r") (V "N"))),
  asg "acc" (lit 0),
  forZ "c" "N" ckInner,
  asg "ok" (.mul (V "ok") (eqF (V "acc") (.get "z" (.add (V "rb") (V "r"))))),
  bump "r"]

/-- `ok` ends `1` exactly when `xv` solves the program of `z`. -/
def ckCom : Com := .seq (asg "ok" (lit 1)) (forZ "r" "M" ckBody)

/-! ### One certificate -/

/-- Decode the candidate of the digits and test it: `ok` ends `1` exactly when it is accepted. -/
def evalCom : Com := seqs [
  fillCom "hl" "T", fillCom "sg" "T", fillCom "S" "n", fillCom "es" "T",
  kdCom, rkCom, sgCom, s1Com, s2Com, wvCom, esCom, xvCom, ckCom,
  .ite (.lt (V "E") (.add (V "n") (lit 1))) .skip (asg "ok" (lit 0))]

/-! ### The odometer -/

def odoBody : Com := seqs [
  asg "ov" (.add (.get "dg" (V "q")) (V "cy")),
  asg "cy" (.div (V "ov") (V "R")),
  .store "dg" (V "q") (.sub (V "ov") (.mul (V "cy") (V "R"))),
  bump "q"]

/-- Add one to the number whose digits are in `dg`; the carry `cy` ends `1` exactly when the
number was the largest one. -/
def odoCom : Com := .seq (asg "cy" (lit 1)) (forZ "q" "D" odoBody)

/-! ### The search -/

def searchBody : Com := seqs [
  evalCom,
  .ite (.eq (V "ok") (lit 1)) (asg "found" (lit 1)) .skip,
  odoCom,
  asg "done" (V "cy")]

def searchCom : Com := seqs [
  asg "found" (lit 0), asg "done" (lit 0),
  .while (.eq (V "done") (lit 0)) searchBody]

/-! ### Reading the word and the header -/

/-- Read the word into `z`: its two counts, then the other `M * N + M` entries. -/
def readBody : Com := seqs [.read "rv", .store "z" (.add (V "q") (lit 2)) (V "rv"), bump "q"]

def readHead : Com := seqs [
  .read "N", .read "M",
  .store "z" (lit 0) (V "N"), .store "z" (lit 1) (V "M"),
  asg "tl" (.add (.mul (V "M") (V "N")) (V "M"))]

def readCom : Com := .seq readHead (forZ "q" "tl" readBody)

/-- The number `n` of clients: the least `n` with `2 ^ (n * n) + n ≥ M`; then `nT n`, `nZ n`,
`nV n`, `Kn n`, `Rd n` and the other constants. -/
def nCom : Com := .seq (asg "n" (lit 0))
  (.while (.lt (.add (.shiftl (lit 1) (.mul (V "n") (V "n"))) (V "n")) (V "M")) (bump "n"))

def h2Com : Com := seqs [
  asg "nn" (.mul (V "n") (V "n")),
  asg "T" (.sub (V "M") (V "n")),
  asg "Z" (.shiftl (lit 1) (V "n")),
  asg "V" (.mul (V "T") (V "Z")),
  asg "np" (.add (V "n") (lit 1)),
  asg "pw" (lit 1)]

def pwCom : Com := forZ "i" "np" (.seq (asg "pw" (.mul (V "pw") (V "np"))) (bump "i"))

def h4Com : Com := seqs [
  asg "K" (.add (V "pw") (lit 1)),
  asg "R" (.add (V "K") (lit 1)),
  asg "D" (.add (.add (V "N") (.mul (lit 2) (V "nn"))) (lit 1)),
  asg "rb" (.add (lit 2) (.mul (V "M") (V "N"))),
  asg "tn" (.add (lit 2) (.mul (V "T") (V "N"))),
  asg "bb" (.get "z" (.add (V "rb") (V "T")))]

def hdrCom : Com := .seq nCom (.seq h2Com (.seq pwCom h4Com))

/-- The program `a x = b`. -/
def smallCom : Com := seqs [
  asg "a" (.get "z" (lit 2)), asg "b" (.get "z" (lit 3)),
  .ite (.eq (V "a") (lit 0))
    (.ite (.eq (V "b") (lit 0)) (.write (lit 1)) (.write (lit 0)))
    (.ite (.eq (.sub (V "b") (.mul (.div (V "b") (V "a")) (V "a"))) (lit 0))
      (.write (lit 1)) (.write (lit 0)))]

/-- The program of the family with `n ≥ 1` clients. -/
def bigCom : Com := seqs [hdrCom, searchCom, .write (V "found")]

/-- **The solver.** -/
def ilpCom : Com := seqs [readCom, .ite (.eq (V "N") (lit 1)) smallCom bigCom]

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpCtx` -/

section
/-!
The context of the machine: what never changes while certificates are decoded, and how a phase is
shown to preserve it.

`Ctx n cnt bb σ` says that the constants of the header (`N M n T Z V K R D rb tn nn bb`) hold their
values, that `z` is the word of the integer program and that every working array has its length.
Every phase leaves the lengths of all arrays alone (`Run.len_arrs`), so the context is preserved as
soon as the phase does not assign to the constants nor store into `z` (`Ctx.stable`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-! ### Frames -/

theorem bigStep_len_arrs {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStep c σ σ' k) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_len_arrs {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hbs⟩ := h.bigStep; exact bigStep_len_arrs hbs a

/-- What a run of `c` leaves alone. -/
def Keeps (c : Com) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) ∧ (∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a) ∧
    (∀ a, (σ'.arrs a).length = (σ.arrs a).length)

theorem run_keeps {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) : Keeps c σ σ' :=
  ⟨fun y hy => h.frame_var y hy, fun a ha => h.frame_arr a ha, fun a => run_len_arrs h a⟩

/-- Every specification also says what the command leaves alone (`Spec.frame` and the lengths). -/
theorem spec_keeps {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) : Spec B P c (fun σ σ' => Q σ σ' ∧ Keeps c σ σ') K := by
  intro σ hσ
  obtain ⟨σ', hr, hq⟩ := h σ hσ
  exact ⟨σ', hr, hq, run_keeps hr⟩

/-- A property of the environment that is preserved by every run of `c` that leaves alone the
names it depends on. -/
def Stable (c : Com) (C : Env → Prop) : Prop := ∀ σ σ', C σ → Keeps c σ σ' → C σ'

theorem Stable.and {c : Com} {C D : Env → Prop} (h1 : Stable c C) (h2 : Stable c D) :
    Stable c (fun σ => C σ ∧ D σ) :=
  fun σ σ' h hk => ⟨h1 σ σ' h.1 hk, h2 σ σ' h.2 hk⟩


theorem stable_var {c : Com} (y : String) (P : ℕ → Prop) (h : y ∉ c.wvars) :
    Stable c (fun σ => P (σ.vars y)) :=
  fun σ σ' hσ hk => by show P (σ'.vars y); rw [hk.1 y h]; exact hσ

theorem stable_arr {c : Com} (a : String) (P : List ℕ → Prop) (h : a ∉ c.warrs) :
    Stable c (fun σ => P (σ.arrs a)) :=
  fun σ σ' hσ hk => by show P (σ'.arrs a); rw [hk.2.1 a h]; exact hσ

theorem stable_len {c : Com} (a : String) (P : ℕ → Prop) :
    Stable c (fun σ => P (σ.arrs a).length) :=
  fun σ σ' hσ hk => by show P (σ'.arrs a).length; rw [hk.2.2 a]; exact hσ

/-! ### The context -/

/-- The constants of the header, the word, and the lengths of the working arrays. -/
structure Ctx (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (σ : Env) : Prop where
  hN : σ.vars "N" = nN n
  hM : σ.vars "M" = nM n
  hn : σ.vars "n" = n
  hT : σ.vars "T" = nT n
  hZ : σ.vars "Z" = nZ n
  hV : σ.vars "V" = nV n
  hK : σ.vars "K" = Kn n
  hR : σ.vars "R" = Rd n
  hD : σ.vars "D" = Dn n
  hrb : σ.vars "rb" = 2 + nM n * nN n
  htn : σ.vars "tn" = 2 + nT n * nN n
  hnn : σ.vars "nn" = n * n
  hbb : σ.vars "bb" = bb
  hz : σ.arrs "z" = ilpWord n cnt bb
  ldg : (σ.arrs "dg").length = Dn n
  lhl : (σ.arrs "hl").length = nT n
  lkd : (σ.arrs "kd").length = nN n
  lrk : (σ.arrs "rkA").length = nN n
  lsg : (σ.arrs "sg").length = nT n
  lS : (σ.arrs "S").length = n
  lwv : (σ.arrs "wv").length = nN n
  les : (σ.arrs "es").length = nT n
  lxv : (σ.arrs "xv").length = nN n

/-- The names the context depends on. -/
def ctxVars : List String :=
  ["N", "M", "n", "T", "Z", "V", "K", "R", "D", "rb", "tn", "nn", "bb"]

theorem Ctx.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} (hv : ∀ y ∈ ctxVars, y ∉ c.wvars)
    (hz : "z" ∉ c.warrs) : Stable c (Ctx n cnt bb) := by
  intro σ σ' h hk
  have hV : ∀ y, y ∈ ctxVars → σ'.vars y = σ.vars y := fun y hy => hk.1 y (hv y hy)
  exact
    { hN := by rw [hV "N" (by simp [ctxVars])]; exact h.hN
      hM := by rw [hV "M" (by simp [ctxVars])]; exact h.hM
      hn := by rw [hV "n" (by simp [ctxVars])]; exact h.hn
      hT := by rw [hV "T" (by simp [ctxVars])]; exact h.hT
      hZ := by rw [hV "Z" (by simp [ctxVars])]; exact h.hZ
      hV := by rw [hV "V" (by simp [ctxVars])]; exact h.hV
      hK := by rw [hV "K" (by simp [ctxVars])]; exact h.hK
      hR := by rw [hV "R" (by simp [ctxVars])]; exact h.hR
      hD := by rw [hV "D" (by simp [ctxVars])]; exact h.hD
      hrb := by rw [hV "rb" (by simp [ctxVars])]; exact h.hrb
      htn := by rw [hV "tn" (by simp [ctxVars])]; exact h.htn
      hnn := by rw [hV "nn" (by simp [ctxVars])]; exact h.hnn
      hbb := by rw [hV "bb" (by simp [ctxVars])]; exact h.hbb
      hz := by rw [hk.2.1 "z" hz]; exact h.hz
      ldg := by rw [hk.2.2 "dg"]; exact h.ldg
      lhl := by rw [hk.2.2 "hl"]; exact h.lhl
      lkd := by rw [hk.2.2 "kd"]; exact h.lkd
      lrk := by rw [hk.2.2 "rkA"]; exact h.lrk
      lsg := by rw [hk.2.2 "sg"]; exact h.lsg
      lS := by rw [hk.2.2 "S"]; exact h.lS
      lwv := by rw [hk.2.2 "wv"]; exact h.lwv
      les := by rw [hk.2.2 "es"]; exact h.les
      lxv := by rw [hk.2.2 "xv"]; exact h.lxv }

/-- Setting a scalar that is not a constant keeps the context. -/
theorem Ctx.setVar {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (h : Ctx n cnt bb σ) {y : String}
    (hy : y ∉ ctxVars) (v : ℕ) : Ctx n cnt bb (σ.setVar y v) := by
  have hne : ∀ x ∈ ctxVars, x ≠ y := fun x hx hxy => hy (hxy ▸ hx)
  have e : ∀ x ∈ ctxVars, (σ.setVar y v).vars x = σ.vars x := fun x hx => by
    simp [Env.setVar, hne x hx]
  exact
    { hN := by rw [e "N" (by simp [ctxVars])]; exact h.hN
      hM := by rw [e "M" (by simp [ctxVars])]; exact h.hM
      hn := by rw [e "n" (by simp [ctxVars])]; exact h.hn
      hT := by rw [e "T" (by simp [ctxVars])]; exact h.hT
      hZ := by rw [e "Z" (by simp [ctxVars])]; exact h.hZ
      hV := by rw [e "V" (by simp [ctxVars])]; exact h.hV
      hK := by rw [e "K" (by simp [ctxVars])]; exact h.hK
      hR := by rw [e "R" (by simp [ctxVars])]; exact h.hR
      hD := by rw [e "D" (by simp [ctxVars])]; exact h.hD
      hrb := by rw [e "rb" (by simp [ctxVars])]; exact h.hrb
      htn := by rw [e "tn" (by simp [ctxVars])]; exact h.htn
      hnn := by rw [e "nn" (by simp [ctxVars])]; exact h.hnn
      hbb := by rw [e "bb" (by simp [ctxVars])]; exact h.hbb
      hz := h.hz, ldg := h.ldg, lhl := h.lhl, lkd := h.lkd, lrk := h.lrk, lsg := h.lsg,
      lS := h.lS, lwv := h.lwv, les := h.les, lxv := h.lxv }

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpScan` -/

section
/-!
The counted scan, with a static context, and the zeroing of an array.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-- **A counted scan** `i := 0; while i < len do body`, whose invariant `Inv k` at the counter value
`k` is separated from a static context `C` (preserved by every run of the body that leaves alone
what the body cannot touch). -/
theorem scan_spec {B : ℕ} (i len : String) (N Kb : ℕ) (body : Com) (C : Env → Prop)
    (Inv : ℕ → Env → Prop) (hC : Stable body C) (hNB : N < B) (hlen : ∀ σ, C σ → σ.vars len = N)
    (hbody : ∀ k < N, Spec B (fun σ => C σ ∧ σ.vars i = k ∧ Inv k σ) body
      (fun σ σ' => σ'.vars i = k + 1 ∧ Inv (k + 1) σ') Kb) :
    Spec B (fun σ => C (σ.setVar i 0) ∧ Inv 0 (σ.setVar i 0)) (forZ i len body)
      (fun _ σ' => C σ' ∧ Inv N σ' ∧ σ'.vars i = N) ((Kb + 4) * N + 6) := by
  have hI := Spec.forRangeZero (B := B) (c := body) i len
    (fun σ => C σ ∧ σ.vars i ≤ N ∧ Inv (σ.vars i) σ) N Kb hNB (fun σ h => h.2.1)
    (fun σ h => hlen σ h.1) ?_
  · refine (Spec.pre hI ?_).post ?_
    · intro σ ⟨h1, h2⟩
      exact ⟨h1, by simp, by simpa using h2⟩
    · intro σ σ' _ ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, by rw [h4] at h3; exact h3, h4⟩
  · intro σ ⟨⟨hCσ, hle, hinv⟩, hlt⟩
    obtain ⟨σ', hr, ⟨hi', hinv'⟩, hkp⟩ := spec_keeps (hbody (σ.vars i) hlt) σ ⟨hCσ, rfl, hinv⟩
    refine ⟨σ', hr, ⟨hC σ σ' hCσ hkp, by omega, by rw [hi']; exact hinv'⟩, hi'⟩

/-! ### Zeroing an array -/

theorem fillBody_vals {B : ℕ} (a len : String) (L : ℕ) (hB : 1 < B) :
    Spec B (fun σ => (σ.arrs a).length = L ∧ σ.vars "fi" < L ∧ L < B)
      (.seq (.store a (V "fi") (lit 0)) (bump "fi"))
      (fun σ σ' => σ'.vars "fi" = σ.vars "fi" + 1 ∧
        σ'.arrs a = (σ.arrs a).set (σ.vars "fi") 0) 7 := by
  run_vcg
  simp

theorem eq_arrOf_of_length {l : List ℕ} {L : ℕ} (h : l.length = L) :
    l = arrOf L (fun c => l.getD c 0) := by
  subst h
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_eq_getD 0]
  simp [arrOf]

/-- **Zeroing**: the first `L` cells of `a` become `0`. -/
theorem fill_spec {B : ℕ} (a len : String) (L : ℕ) (C : Env → Prop)
    (hC : Stable (.seq (.store a (V "fi") (lit 0)) (bump "fi")) C)
    (hCi : ∀ σ, C σ → C (σ.setVar "fi" 0)) (hlen : ∀ σ, C σ → σ.vars len = L)
    (hLB : L < B) (hB : 1 < B) (hne : len ≠ "fi") :
    Spec B (fun σ => C σ ∧ (σ.arrs a).length = L) (fillCom a len)
      (fun _ σ' => C σ' ∧ σ'.arrs a = arrOf L (fun _ => 0)) ((7 + 4) * L + 6) := by
  unfold fillCom
  have hs := scan_spec (B := B) "fi" len L 7 (.seq (.store a (V "fi") (lit 0)) (bump "fi")) C
    (fun k σ => ∃ g, σ.arrs a = arrOf L g ∧ ∀ c < k, g c = 0) hC hLB hlen ?_
  · refine (Spec.pre hs ?_).post ?_
    · intro σ ⟨h1, h2⟩
      exact ⟨hCi σ h1, fun c => (σ.arrs a).getD c 0, eq_arrOf_of_length h2, fun c hc => absurd hc (by omega)⟩
    · intro σ σ' _ ⟨h1, ⟨g, hg, hc⟩, h3⟩
      exact ⟨h1, by rw [hg]; exact arrOf_congr hc⟩
  · intro k hk σ ⟨hCσ, hk', g, hg, hgk⟩
    obtain ⟨σ', hr, h1, h2⟩ := (fillBody_vals (B := B) a len L hB) σ ⟨by rw [hg]; simp, by omega, hLB⟩
    refine ⟨σ', hr, by omega, fun j => if j = σ.vars "fi" then 0 else g j, ?_, ?_⟩
    · rw [h2, hg, set_arrOf]
    · intro c hc
      by_cases h : c = σ.vars "fi"
      · simp [h]
      · simp only [h, if_false]; exact hgk c (by omega)

/-- `x := x + 1`. -/
theorem bump_spec {B : ℕ} (x : String) (hB : 1 < B) :
    Spec B (fun σ => σ.vars x + 1 < B) (bump x) (fun σ σ' => σ' = σ.setVar x (σ.vars x + 1)) 4 := by
  run_vcg
  rfl

/-- `x := c`. -/
theorem assign_lit_spec {B : ℕ} (x : String) (c : ℕ) (hc : c < B) :
    Spec B (fun _ => True) (asg x (lit c)) (fun σ σ' => σ' = σ.setVar x c) 2 :=
  Spec.mono (Spec.assign (fun _ _ => evalB_lit hc)) (by simp)

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpKind` -/

section
/-!
The kinds of the columns, column by column: the facts about `kindOf` that the classification pass
of the machine uses (`kindOf_step`, `hlF_succ`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

open Classical

noncomputable section

section
variable {n : ℕ} {d : ℕ → ℕ}

theorem nV_le_nN' (n : ℕ) : nV n ≤ nN n := by unfold nN; omega

theorem coef_div_eq_one_iff {c : ℕ} (hc : c < nV n) : coef n (c / nZ n) c = 1 ↔ liveP n c := by
  have hlt : c / nZ n < nT n := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact hc
  rw [coef_type_row n _ c hlt]
  unfold tyOf
  by_cases hl : liveP n c
  · simp [hl]
  · simp [hl]

theorem tyOf_eq_some_iff {c t : ℕ} : tyOf n c = some t ↔ liveP n c ∧ t = c / nZ n := by
  unfold tyOf
  by_cases hl : liveP n c
  · simp only [hl, if_true, Option.some.injEq, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp [hl]

theorem tyOf_of_ge_V {c : ℕ} (h : nV n ≤ c) : tyOf n c = none := by
  unfold tyOf
  have : ¬ liveP n c := fun hl => by have := hl.1; omega
  simp [this]

theorem isLive_iff_of_lt_V {c : ℕ} (hc : c < nV n) : isLive n c ↔ liveP n c := by
  unfold isLive
  constructor
  · rintro ⟨-, h | h⟩
    · omega
    · exact h
  · intro h
    exact ⟨by have := nV_le_nN' n; omega, Or.inr h⟩

theorem isLive_of_ge_V {c : ℕ} (h1 : nV n ≤ c) (h2 : c < nN n) : isLive n c :=
  ⟨h2, Or.inl h1⟩

/-- Whether an earlier large column has type `t`. -/
def hlF (n : ℕ) (d : ℕ → ℕ) (t i : ℕ) : ℕ :=
  if ∃ c < i, c ∈ Lset n d ∧ tyOf n c = some t then 1 else 0

theorem hlF_zero (t : ℕ) : hlF n d t 0 = 0 := by
  unfold hlF
  rw [if_neg]
  rintro ⟨c, hc, -⟩
  omega

theorem hlF_succ (t c : ℕ) :
    hlF n d t (c + 1) = if (c ∈ Lset n d ∧ tyOf n c = some t) then 1 else hlF n d t c := by
  unfold hlF
  by_cases h : c ∈ Lset n d ∧ tyOf n c = some t
  · rw [if_pos h, if_pos ⟨c, by omega, h⟩]
  · rw [if_neg h]
    by_cases h' : ∃ c' < c, c' ∈ Lset n d ∧ tyOf n c' = some t
    · rw [if_pos h', if_pos]
      obtain ⟨c', hc', hh⟩ := h'
      exact ⟨c', by omega, hh⟩
    · rw [if_neg h', if_neg]
      rintro ⟨c', hc', hh⟩
      by_cases hcc : c' = c
      · subst hcc; exact h hh
      · exact h' ⟨c', by omega, hh⟩

theorem hlF_le_one (t i : ℕ) : hlF n d t i ≤ 1 := by
  unfold hlF; split_ifs <;> omega

/-- A large typed column: the flag of its type. -/
theorem mem_Lset_and_tyOf {c t : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    (c ∈ Lset n d ∧ tyOf n c = some t) ↔
      c < nV n ∧ coef n (c / nZ n) c = 1 ∧ d c = Kn n ∧ t = c / nZ n := by
  rw [mem_Lset_iff, tyOf_eq_some_iff]
  constructor
  · rintro ⟨⟨hl, hd⟩, hlv, ht⟩
    refine ⟨hlv.1, (coef_div_eq_one_iff hlv.1).mpr hlv, hd, ht⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hlv : liveP n c := (coef_div_eq_one_iff h1).mp h2
    exact ⟨⟨(isLive_iff_of_lt_V h1).mpr hlv, h3⟩, hlv, h4⟩

/-- **The kind of column `c`, from the tests of the machine.** -/
theorem kindOf_step {c : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    kindOf n d c =
      if c < nV n then
        (if coef n (c / nZ n) c = 1 then
          (if d c < Kn n then 3 else if hlF n d (c / nZ n) c = 0 then 1 else 2)
         else 0)
      else (if d c < Kn n then 3 else 2) := by
  by_cases hV : c < nV n
  · rw [if_pos hV]
    by_cases hcf : coef n (c / nZ n) c = 1
    · rw [if_pos hcf]
      have hlv : liveP n c := (coef_div_eq_one_iff hV).mp hcf
      have hlive : isLive n c := (isLive_iff_of_lt_V hV).mpr hlv
      by_cases hdk : d c < Kn n
      · rw [if_pos hdk]
        exact kindOf_eq_three.mpr ⟨hlive, hdk⟩
      · rw [if_neg hdk]
        have hdeq : d c = Kn n := by omega
        have hL : c ∈ Lset n d := (mem_Lset_iff n d c).mpr ⟨hlive, hdeq⟩
        have hty : tyOf n c = some (c / nZ n) := tyOf_eq_some_iff.mpr ⟨hlv, rfl⟩
        have hbase : isBase n d c ↔ hlF n d (c / nZ n) c = 0 := by
          rw [isBase_iff]
          unfold hlF
          constructor
          · rintro ⟨-, -, h⟩
            rw [if_neg]
            rintro ⟨c', hc', hL', hty'⟩
            exact h c' hc' hL' (by rw [hty, hty'])
          · intro h
            refine ⟨hL, by rw [hty]; simp, fun c' hc' hL' hne => ?_⟩
            have : ∃ c' < c, c' ∈ Lset n d ∧ tyOf n c' = some (c / nZ n) :=
              ⟨c', hc', hL', by rw [hne, hty]⟩
            rw [if_pos this] at h
            omega
        by_cases hb : isBase n d c
        · have h0 : hlF n d (c / nZ n) c = 0 := hbase.mp hb
          rw [if_pos h0]
          exact kindOf_eq_one.mpr hb
        · have h0 : ¬ hlF n d (c / nZ n) c = 0 := fun h => hb (hbase.mpr h)
          rw [if_neg h0]
          exact kindOf_eq_two.mpr ⟨hL, hb⟩
    · rw [if_neg hcf]
      have hlv : ¬ liveP n c := fun h => hcf ((coef_div_eq_one_iff hV).mpr h)
      have hlive : ¬ isLive n c := fun h => hlv ((isLive_iff_of_lt_V hV).mp h)
      unfold kindOf
      have h1 : ¬ (isLive n c ∧ d c < Kn n) := fun h => hlive h.1
      have h2 : ¬ isBase n d c := fun h => hlive ((mem_Lset_iff n d c).mp h.1).1
      have h3 : ¬ isExtra n d c := fun h => hlive ((mem_Lset_iff n d c).mp h.1).1
      rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [if_neg hV]
    have hV' : nV n ≤ c := by omega
    have hlive : isLive n c := isLive_of_ge_V hV' hc
    by_cases hdk : d c < Kn n
    · rw [if_pos hdk]
      exact kindOf_eq_three.mpr ⟨hlive, hdk⟩
    · rw [if_neg hdk]
      have hdeq : d c = Kn n := by omega
      have hL : c ∈ Lset n d := (mem_Lset_iff n d c).mpr ⟨hlive, hdeq⟩
      have hb : ¬ isBase n d c := fun h => h.2.1 (tyOf_of_ge_V hV')
      exact kindOf_eq_two.mpr ⟨hL, hb⟩

/-- The flag of the type after column `c`, from the tests of the machine. -/
theorem hlF_step {c t : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    hlF n d t (c + 1) =
      if (c < nV n ∧ coef n (c / nZ n) c = 1 ∧ ¬ d c < Kn n ∧ t = c / nZ n) then 1
      else hlF n d t c := by
  rw [hlF_succ]
  have := mem_Lset_and_tyOf (n := n) (d := d) (t := t) hc hdc
  by_cases h : c ∈ Lset n d ∧ tyOf n c = some t
  · have h' := this.mp h
    rw [if_pos h, if_pos ⟨h'.1, h'.2.1, by omega, h'.2.2.2⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3, h4⟩
    exact h (this.mpr ⟨h1, h2, by omega, h4⟩)

end

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpTac` -/

section
/-!
Small tactics for the proofs of the machine layer.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lean Elab Tactic Meta in
/-- Clear every hypothesis that is a `Run` (the derivations that `run_vcg` leaves behind). -/
elab "clear_runs" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    let ids := (← getLCtx).foldl (init := ([] : List FVarId)) fun acc d =>
      if d.isImplementationDetail then acc else
      if d.type.isAppOf ``Lax808846Proofs.Reasoning.Run then d.fvarId :: acc else acc
    for id in ids do
      try g ← g.clear id catch _ => pure ()
    replaceMainGoal [g]

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpKd` -/

section
/-!
The classification pass: the kind of every column, and the flags of the types.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-- What one turn of the classification stores in `kd`. -/
def kdVal (σ : Env) : ℕ :=
  if σ.vars "i" < σ.vars "V" then
    (if (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 = 1 then
      (if (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" then 3
       else if (σ.arrs "hl").getD (σ.vars "i" / σ.vars "Z") 0 = 0 then 1 else 2)
     else 0)
  else (if (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" then 3 else 2)

/-- What one turn of the classification does to `hl`. -/
def hlNew (σ : Env) : List ℕ :=
  if σ.vars "i" < σ.vars "V" ∧
      (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 = 1 ∧
      ¬ (σ.arrs "dg").getD (σ.vars "i") 0 < σ.vars "K" ∧
      (σ.arrs "hl").getD (σ.vars "i" / σ.vars "Z") 0 = 0
  then (σ.arrs "hl").set (σ.vars "i" / σ.vars "Z") 1 else σ.arrs "hl"

theorem Dn_ge_nN (n : ℕ) : nN n ≤ Dn n := by unfold Dn; omega

/-- The numeric facts about a state of the classification pass. -/
theorem kdFacts {n : ℕ} {cnt : ℕ → ℕ} {bb v B : ℕ} (hb : Hyp n cnt bb v B) (d : ℕ → ℕ)
    (hd : ∀ q < Dn n, d q ≤ Kn n) {σ : Env} (hctx : Ctx n cnt bb σ)
    (hdg : σ.arrs "dg" = arrOf (Dn n) d) (hi : σ.vars "i" < nN n) :
    σ.vars "N" = nN n ∧ σ.vars "V" = nV n ∧ σ.vars "Z" = nZ n ∧ σ.vars "K" = Kn n ∧
    (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧
    (σ.arrs "hl").length = nT n ∧ (σ.arrs "kd").length = nN n ∧ (σ.arrs "z").length = zLen n ∧
    (σ.arrs "dg").length = Dn n ∧
    (σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n) ∧
    (σ.vars "i" < nV n → 2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i" < zLen n) ∧
    (σ.vars "i" < nV n →
      (σ.arrs "z").getD (2 + σ.vars "i" / σ.vars "Z" * σ.vars "N" + σ.vars "i") 0 ≤ 1) := by
  have hNv : σ.vars "N" = nN n := hctx.hN
  have hZv : σ.vars "Z" = nZ n := hctx.hZ
  have hq : σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n := by
    intro h
    rw [hZv]
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact h
  refine ⟨hNv, hctx.hV, hZv, hctx.hK, ?_, hctx.lhl, hctx.lkd, ?_, hctx.ldg, hq, ?_, ?_⟩
  · rw [hdg, getD_arrOf _ (by have := Dn_ge_nN n; omega)]
    exact hd _ (by have := Dn_ge_nN n; omega)
  · rw [hctx.hz]; simp [ilpWord, zLen]
  · intro h
    have h1 := hq h
    rw [hNv]
    have h2 : 2 + σ.vars "i" / σ.vars "Z" * nN n + σ.vars "i" < 2 + nM n * nN n :=
      idx_lt_zLen (by have := h1; unfold nM; omega) hi
    have := rb_le_zLen n
    omega
  · intro h
    have h1 := hq h
    rw [hctx.hz, hNv, hZv] at *
    have h1' : σ.vars "i" / nZ n < nM n := by have := h1; unfold nM; omega
    rw [ilpWord_coef n cnt bb h1' hi]
    exact coef_le_one n _ _

theorem kdBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb v B : ℕ} (hb : Hyp n cnt bb v B) (d : ℕ → ℕ)
    (hd : ∀ q < Dn n, d q ≤ Kn n) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) d ∧ σ.vars "i" < nN n ∧
        ∀ t, (σ.arrs "hl").getD t 0 ≤ 1)
      kdBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "kd" = (σ.arrs "kd").set (σ.vars "i") (kdVal σ) ∧ σ'.arrs "hl" = hlNew σ) 100 := by
  run_vcg
  all_goals
    obtain ⟨hNv, hVv, hZv, hKv, hdgv, hlhl, hlkd, hlz, hldg, hq, hzi, hzv⟩ :=
      kdFacts hb d hd ‹Ctx n cnt bb σ› ‹σ.arrs "dg" = arrOf (Dn n) d› ‹σ.vars "i" < nN n›
    have hlb : ∀ t, (σ.arrs "hl").getD t 0 ≤ 1 := ‹∀ t, (σ.arrs "hl").getD t 0 ≤ 1›
    have hBN := hb.nN_lt
    have hBV := hb.nV_lt
    have hBK := hb.Kn_lt
    have hBz := hb.zLen_lt
    have hBT := hb.nT_lt
    have hBZ := hb.nZ_lt
    have hB5 := hb.five_lt_B
    have hDN := Dn_ge_nN n
    have hlb' := hlb (σ.vars "i" / σ.vars "Z")
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (unfold kdVal hlNew; split_ifs <;> first | omega | simp) | omega)

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpKdLoop` -/

section
/-!
The classification pass: the loop.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

/-- The static context of the decoding of the digits `v`. -/
def CE (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  Ctx n cnt bb σ ∧ σ.arrs "dg" = arrOf (Dn n) v

theorem CE.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs) :
    Stable c (CE n cnt bb v) :=
  Stable.and (Ctx.stable hv hz) (stable_arr "dg" (fun l => l = arrOf (Dn n) v) hd)

theorem CE.setVar {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {σ : Env} (h : CE n cnt bb v σ)
    {y : String} (hy : y ∉ ctxVars) (x : ℕ) : CE n cnt bb v (σ.setVar y x) :=
  ⟨h.1.setVar hy x, h.2⟩

/-- The digits of the columns, as a function. -/
abbrev dd (n : ℕ) (v : ℕ → ℕ) : ℕ → ℕ := (certVec n v).d

theorem dd_lt {n : ℕ} {v : ℕ → ℕ} {c : ℕ} (hc : c < nN n) : dd n v c = v c := by
  simp [dd, certVec, hc]

theorem getD_arrOf_lt {n : ℕ} {f : ℕ → ℕ} {i : ℕ} (h : i < n) : (arrOf n f).getD i 0 = f i :=
  getD_arrOf f h

/-- **One turn of the classification computes the kind and the flags.** -/
theorem kdStep {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {σ : Env} {k : ℕ}
    (hctx : Ctx n cnt bb σ) (hdg : σ.arrs "dg" = arrOf (Dn n) v) (hk : k < nN n)
    (hi : σ.vars "i" = k) (hv : v k ≤ Kn n)
    (hl : σ.arrs "hl" = arrOf (nT n) (fun t => hlF n (dd n v) t k)) :
    kdVal σ = kindOf n (dd n v) k ∧
      hlNew σ = arrOf (nT n) (fun t => hlF n (dd n v) t (k + 1)) := by
  have hDk : k < Dn n := lt_of_lt_of_le hk (by unfold Dn; omega)
  have hddk : dd n v k = v k := dd_lt hk
  have hdgk : (σ.arrs "dg").getD k 0 = v k := by rw [hdg]; exact getD_arrOf_lt hDk
  have hN := hctx.hN
  have hV := hctx.hV
  have hZ := hctx.hZ
  have hK := hctx.hK
  have hlt : k < nV n → k / nZ n < nT n := by
    intro h
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact h
  have hzk : k < nV n → (σ.arrs "z").getD (2 + k / nZ n * nN n + k) 0 = coef n (k / nZ n) k := by
    intro h
    rw [hctx.hz]
    exact ilpWord_coef n cnt bb (by have := hlt h; unfold nM; omega) hk
  have hhl : k < nV n → (σ.arrs "hl").getD (k / nZ n) 0 = hlF n (dd n v) (k / nZ n) k := by
    intro h
    rw [hl]; exact getD_arrOf_lt (hlt h)
  have hkd := kindOf_step (n := n) (d := dd n v) hk (by rw [hddk]; exact hv)
  have hhs := fun t => hlF_step (n := n) (d := dd n v) (t := t) hk (by rw [hddk]; exact hv)
  rw [hddk] at hkd
  simp only [hddk] at hhs
  constructor
  · unfold kdVal
    rw [hkd, hi, hN, hV, hZ, hK]
    by_cases h1 : k < nV n
    · rw [if_pos h1, if_pos h1, hzk h1, hdgk, hhl h1]
    · rw [if_neg h1, if_neg h1, hdgk]
  · unfold hlNew
    rw [hi, hN, hV, hZ, hK]
    have hiff : (k < nV n ∧ (σ.arrs "z").getD (2 + k / nZ n * nN n + k) 0 = 1 ∧
        ¬ (σ.arrs "dg").getD k 0 < Kn n ∧ (σ.arrs "hl").getD (k / nZ n) 0 = 0) ↔
        (k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ hlF n (dd n v) (k / nZ n) k = 0) := by
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, by rw [← hzk h1]; exact h2, by rw [← hdgk]; exact h3,
          by rw [← hhl h1]; exact h4⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, by rw [hzk h1]; exact h2, by rw [hdgk]; exact h3, by rw [hhl h1]; exact h4⟩
    by_cases hc : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧
        hlF n (dd n v) (k / nZ n) k = 0
    · rw [if_pos (hiff.mpr hc)]
      obtain ⟨h1, h2, h3, h4⟩ := hc
      rw [hl, set_arrOf]
      refine arrOf_congr fun t _ => ?_
      rw [hhs t]
      by_cases ht : t = k / nZ n
      · have hcond : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n :=
          ⟨h1, h2, h3, ht⟩
        rw [if_pos hcond, if_pos ht]
      · have hcond : ¬ (k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n) :=
          fun h => ht h.2.2.2
        rw [if_neg hcond, if_neg ht]
    · rw [if_neg (fun h => hc (hiff.mp h)), hl]
      refine arrOf_congr fun t _ => ?_
      rw [hhs t]
      by_cases hcc : k < nV n ∧ coef n (k / nZ n) k = 1 ∧ ¬ v k < Kn n ∧ t = k / nZ n
      · rw [if_pos hcc]
        obtain ⟨h1, h2, h3, h4⟩ := hcc
        have h5 : ¬ hlF n (dd n v) (k / nZ n) k = 0 := fun h => hc ⟨h1, h2, h3, h⟩
        have h6 := hlF_le_one (n := n) (d := dd n v) (k / nZ n) k
        rw [h4]; omega
      · rw [if_neg hcc]

theorem hlF_flags (n : ℕ) (d : ℕ → ℕ) (k : ℕ) (T : ℕ) :
    ∀ t, (arrOf T (fun t => hlF n d t k)).getD t 0 ≤ 1 := by
  intro t
  by_cases h : t < T
  · rw [getD_arrOf_lt h]; exact hlF_le_one _ _
  · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

/-- **The classification pass**: `kd` holds the kind of every column. -/
theorem kdCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ (∃ f, σ.arrs "kd" = arrOf (nN n) f) ∧
        σ.arrs "hl" = arrOf (nT n) (fun _ => 0))
      kdCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
      ((100 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) 100 kdBody (CE n cnt bb v)
    (fun k σ => (∃ f, σ.arrs "kd" = arrOf (nN n) f ∧ ∀ c < k, f c = kindOf n (dd n v) c) ∧
      σ.arrs "hl" = arrOf (nT n) (fun t => hlF n (dd n v) t k))
    (CE.stable (by decide) (by decide) (by decide)) hb.nN_lt (fun σ h => h.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, ⟨f, hf⟩, hh⟩
      refine ⟨hC.setVar (by decide) 0, ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩, ?_⟩
      simpa [hlF_zero] using hh
    · rintro σ σ' - ⟨hC, ⟨⟨f, hf, hfk⟩, -⟩, -⟩
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, ⟨f, hf, hfk⟩, hhl⟩
    have hflags : ∀ t, (σ.arrs "hl").getD t 0 ≤ 1 := by rw [hhl]; exact hlF_flags _ _ _ _
    obtain ⟨σ', hr, h1, h2, h3⟩ := kdBody_vals hb v hv σ ⟨hC.1, hC.2, by rw [hik]; exact hk, hflags⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    obtain ⟨e1, e2⟩ := kdStep hC.1 hC.2 hk hik hvk hhl
    refine ⟨σ', hr, by omega, ⟨fun j => if j = k then kindOf n (dd n v) k else f j, ?_, ?_⟩, ?_⟩
    · rw [h2, hf, hik, e1, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)
    · rw [h3, e2]

/-- Facts about the current column `i < N` of a state of a pass. -/
theorem colFacts {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} (hv : ∀ q < Dn n, v q ≤ Kn n)
    {σ : Env} (hC : CE n cnt bb v σ) (hi : σ.vars "i" < nN n) :
    (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧ (σ.arrs "dg").length = Dn n ∧
    (σ.vars "i" < nV n → σ.vars "i" / σ.vars "Z" < nT n) := by
  have hZv : σ.vars "Z" = nZ n := hC.1.hZ
  have hDN : nN n ≤ Dn n := by unfold Dn; omega
  refine ⟨?_, hC.1.ldg, ?_⟩
  · rw [hC.2, getD_arrOf_lt (by omega)]
    exact hv _ (by omega)
  · intro h
    rw [hZv]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpRk` -/

section
/-!
The rank pass: the rank of every column among the extras, and the number of extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

theorem rk_succ' (n : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    rk n d (k + 1) = rk n d k + if isExtra n d k then 1 else 0 := by
  unfold rk
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : isExtra n d k
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h]; simp

theorem card_Ext_eq_rk (n : ℕ) (d : ℕ → ℕ) : (Ext n d).card = rk n d (nN n) := rfl

/-- What one turn of the rank pass stores. -/
theorem rkBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Ctx n cnt bb σ ∧ σ.vars "i" < nN n ∧ σ.vars "E" < nN n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3)
      rkBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "rkA" = (σ.arrs "rkA").set (σ.vars "i") (σ.vars "E") ∧
        σ'.vars "E" = σ.vars "E" + (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0)) 40 := by
  run_vcg
  all_goals
    have hctx : Ctx n cnt bb σ := ‹Ctx n cnt bb σ›
    have hlk : (σ.arrs "kd").length = nN n := hctx.lkd
    have hlr : (σ.arrs "rkA").length = nN n := hctx.lrk
    have hBN := hb.nN_lt
    have hB5 := hb.five_lt_B
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | simp_all)

/-- **The rank pass.** -/
theorem rkCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        ∃ f, σ.arrs "rkA" = arrOf (nN n) f)
      rkCom
      (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ'.vars "E" = (Ext n (dd n v)).card) (2 + ((40 + 4) * nN n + 6)) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) 40 rkBody
    (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
    (fun k σ => (∃ f, σ.arrs "rkA" = arrOf (nN n) f ∧ ∀ c < k, f c = rk n (dd n v) c) ∧
      σ.vars "E" = rk n (dd n v) k)
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) (by decide)))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        ∃ f, σ.arrs "rkA" = arrOf (nN n) f) (asg "E" (lit 0)) (fun σ σ' => σ' = σ.setVar "E" 0) 2 :=
      Spec.mono (Spec.assign (fun σ _ => evalB_lit (by have := hb.five_lt_B; omega))) (by simp)
    refine (Spec.seq hA hs ?_ ?_).mono le_rfl
    · rintro σ σ' ⟨hC, hkd, f, hf⟩ rfl
      refine ⟨⟨hC.setVar (by decide) _ |>.setVar (by decide) _, by simpa using hkd⟩,
        ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩, by simp [rk]⟩
    · rintro σ σ' σ'' ⟨hC, hkd, f, hf⟩ rfl ⟨⟨hC', hkd'⟩, ⟨⟨f', hf', hfk⟩, hE⟩, -⟩
      refine ⟨hC', by rw [hf']; exact arrOf_congr hfk, ?_⟩
      rw [hE, card_Ext_eq_rk]
  · intro k hk σ ⟨⟨hC, hkd⟩, hik, ⟨f, hf, hfk⟩, hE⟩
    have hEle : rk n (dd n v) k ≤ k := by
      unfold rk
      calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
        _ = k := Finset.card_range k
    have hkd' : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd, hik]; exact getD_arrOf_lt hk
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := by
      rw [hkd']
      unfold kindOf; split_ifs <;> omega
    obtain ⟨σ', hr, h1, h2, h3⟩ := rkBody_vals hb σ ⟨hC.1, by omega, by omega, hkd3⟩
    refine ⟨σ', hr, by omega, ⟨fun j => if j = k then rk n (dd n v) k else f j, ?_, ?_⟩, ?_⟩
    · rw [h2, hf, hik, hE, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)
    · rw [h3, hE, rk_succ', hkd']
      simp only [kindOf_eq_two]

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpSg` -/

section
/-!
The pass computing `sigma`: for every type, the sum of the small digits of its live columns.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

/-- The sum defining `sigma`, over the columns below `k`. -/
def sgP (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) : ℕ :=
  ∑ c ∈ range k, if tyOf n c = some t ∧ d c < Kn n then d c else 0

theorem sgP_N (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sgP n d t (nN n) = sigma n d t := rfl

theorem sgP_succ (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) :
    sgP n d t (k + 1) = sgP n d t k + if tyOf n k = some t ∧ d k < Kn n then d k else 0 := by
  unfold sgP; rw [Finset.sum_range_succ]

theorem sgP_ge_V (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) (hk : nV n ≤ k) :
    sgP n d t k = sgP n d t (nV n) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [sgP_succ, ih, if_neg, add_zero]
    rintro ⟨h, -⟩
    rw [tyOf_of_ge_V hk] at h; simp at h

theorem sigma_eq_sgP_V (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sigma n d t = sgP n d t (nV n) := by
  rw [← sgP_N]; exact sgP_ge_V n d t _ (by unfold nN; omega)

theorem sgP_step {n : ℕ} {d : ℕ → ℕ} {t k : ℕ} (hk : k < nV n) :
    sgP n d t (k + 1) = sgP n d t k + if (kindOf n d k = 3 ∧ k / nZ n = t) then d k else 0 := by
  rw [sgP_succ]
  congr 1
  have : (tyOf n k = some t ∧ d k < Kn n) ↔ (kindOf n d k = 3 ∧ k / nZ n = t) := by
    rw [kindOf_eq_three, tyOf_eq_some_iff, isLive_iff_of_lt_V hk]
    constructor
    · rintro ⟨⟨hl, ht⟩, hd⟩; exact ⟨⟨hl, hd⟩, ht.symm⟩
    · rintro ⟨⟨hl, hd⟩, ht⟩; exact ⟨⟨hl, ht.symm⟩, hd⟩
  simp only [this]

theorem sgP_le (n : ℕ) (d : ℕ → ℕ) (t k : ℕ) : sgP n d t k ≤ k * Kn n := by
  induction k with
  | zero => simp [sgP]
  | succ k ih =>
    rw [sgP_succ]
    have : (if tyOf n k = some t ∧ d k < Kn n then d k else 0) ≤ Kn n := by
      split_ifs with h
      · exact h.2.le
      · omega
    nlinarith

/-- What one turn of the pass does to `sg`. -/
theorem sgBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nV n ∧ (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n)
      sgBody
      (fun σ σ' => σ'.vars "i" = σ.vars "i" + 1 ∧
        σ'.arrs "sg" = if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then
          (σ.arrs "sg").set (σ.vars "i" / σ.vars "Z")
            ((σ.arrs "sg").getD (σ.vars "i" / σ.vars "Z") 0 + (σ.arrs "dg").getD (σ.vars "i") 0)
          else σ.arrs "sg") 40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nV n := ‹σ.vars "i" < nV n›
    have hsgb : ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n :=
      ‹∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n›
    have hVN := nV_le_nN'' n
    obtain ⟨hdgv, hldg, hq⟩ := colFacts hv hC (by omega)
    have hq' := hq hi
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hlkd : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hVv : σ.vars "V" = nV n := hC.1.hV
    have hZv : σ.vars "Z" = nZ n := hC.1.hZ
    have hNv : σ.vars "N" = nN n := hC.1.hN
    have hBN := hb.nN_lt
    have hB5 := hb.five_lt_B
    have hBV := hb.nV_lt
    have hBZ := hb.nZ_lt
    have hBK := hb.NK_lt
    have hBT := hb.nT_lt
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 :=
      ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hsg1 := hsgb (σ.vars "i" / σ.vars "Z")
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; simp_all))

theorem kindOf_le_three (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : kindOf n d c ≤ 3 := by
  unfold kindOf; split_ifs <;> omega

theorem arrOf_getD_le {T : ℕ} {f : ℕ → ℕ} {b : ℕ} (h : ∀ t < T, f t ≤ b) (t : ℕ) :
    (arrOf T f).getD t 0 ≤ b := by
  by_cases ht : t < T
  · rw [getD_arrOf_lt ht]; exact h t ht
  · rw [List.getD_eq_default _ _ (by simp; omega)]; omega

/-- **The pass computing `sigma`.** -/
theorem sgCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "sg" = arrOf (nT n) (fun _ => 0))
      sgCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.arrs "sg" = arrOf (nT n) (sigma n (dd n v)))
      ((40 + 4) * nV n + 6) := by
  have hs := scan_spec (B := B) "i" "V" (nV n) 40 sgBody
    (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)))
    (fun k σ => σ.arrs "sg" = arrOf (nT n) (fun t => sgP n (dd n v) t k))
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) (by decide)))
    hb.nV_lt (fun σ h => h.1.1.hV) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hkd, hsg⟩
      refine ⟨⟨hC.setVar (by decide) _, by simpa using hkd⟩, ?_⟩
      simpa [sgP] using hsg
    · rintro σ σ' - ⟨⟨hC, -⟩, hsg, -⟩
      refine ⟨hC, ?_⟩
      rw [hsg]
      exact arrOf_congr fun t _ => (sigma_eq_sgP_V n _ t).symm
  · intro k hk σ ⟨⟨hC, hkd⟩, hik, hsg⟩
    have hkN : k < nN n := lt_of_lt_of_le hk (nV_le_nN'' n)
    have hkd' : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd, hik]; exact getD_arrOf_lt hkN
    have hsgb : ∀ t, (σ.arrs "sg").getD t 0 ≤ nN n * Kn n := by
      intro t
      rw [hsg]
      refine arrOf_getD_le (fun t _ => ?_) t
      calc sgP n (dd n v) t k ≤ k * Kn n := sgP_le _ _ _ _
        _ ≤ nN n * Kn n := Nat.mul_le_mul_right _ hkN.le
    obtain ⟨σ', hr, h1, h2⟩ := sgBody_vals hb v hv σ
      ⟨hC, by omega, by rw [hkd']; exact kindOf_le_three _ _ _, hsgb⟩
    refine ⟨σ', hr, by omega, ?_⟩
    have hZ := hC.1.hZ
    have hlt : k / nZ n < nT n := by
      apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact hk
    have hDk : k < Dn n := lt_of_lt_of_le hkN (by unfold Dn; omega)
    have hdgk : (σ.arrs "dg").getD (σ.vars "i") 0 = dd n v k := by
      rw [hC.2, hik, getD_arrOf_lt hDk, dd_lt hkN]
    rw [h2, hkd', hdgk, hik, hZ, hsg, getD_arrOf_lt hlt]
    by_cases h3 : kindOf n (dd n v) k = 3
    · rw [if_pos h3, set_arrOf]
      refine arrOf_congr fun t _ => ?_
      rw [sgP_step hk]
      by_cases ht : t = k / nZ n
      · subst ht; simp [h3]
      · have : ¬ (kindOf n (dd n v) k = 3 ∧ k / nZ n = t) := fun h => ht h.2.symm
        simp [ht, this]
    · rw [if_neg h3]
      refine arrOf_congr fun t _ => ?_
      rw [sgP_step hk, if_neg (fun h => h3 h.1)]; simp

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpAddRow` -/

section
/-!
Adding a multiple of a column of the client rows to the vector `S`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical

theorem mul_le_of_le_one' (a c : ℕ) (h : c ≤ 1) : a * c ≤ a := by
  calc a * c ≤ a * 1 := Nat.mul_le_mul_left a h
    _ = a := mul_one a

/-- The coefficient of client `j` of the column `i`, as the machine reads it. -/
theorem z_client_coef {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {σ : Env} (hC : Ctx n cnt bb σ) {j c : ℕ}
    (hj : j < n) (hc : c < nN n) :
    (σ.arrs "z").getD (σ.vars "tn" + j * σ.vars "N" + c) 0 = coef n (nT n + j) c := by
  rw [hC.hz, hC.htn, hC.hN]
  have : 2 + nT n * nN n + j * nN n + c = 2 + (nT n + j) * nN n + c := by ring
  rw [this]
  exact ilpWord_coef n cnt bb (by unfold nM; omega) hc

theorem addRowBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "j" < n ∧
        σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B)
      addRowBody
      (fun σ σ' => σ'.vars "j" = σ.vars "j" + 1 ∧
        σ'.arrs "S" = (σ.arrs "S").set (σ.vars "j")
          ((σ.arrs "S").getD (σ.vars "j") 0 + σ.vars "mv" * coef n (nT n + σ.vars "j") (σ.vars "i")))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hj : σ.vars "j" < n := ‹σ.vars "j" < n›
    have hmS : σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B :=
      ‹σ.vars "mv" + (σ.arrs "S").getD (σ.vars "j") 0 < B›
    have hzc := z_client_coef hC.1 hj hi
    have hcf := coef_le_one n (nT n + σ.vars "j") (σ.vars "i")
    have hprod := mul_le_of_le_one' (σ.vars "mv") ((σ.arrs "z").getD
      (σ.vars "tn" + σ.vars "j" * σ.vars "N" + σ.vars "i") 0) (by rw [hzc]; exact hcf)
    have hidx : σ.vars "tn" + σ.vars "j" * σ.vars "N" + σ.vars "i" < zLen n := by
      rw [hC.1.htn, hC.1.hN]
      have h1 : 2 + (nT n + σ.vars "j") * nN n + σ.vars "i" < 2 + nM n * nN n :=
        idx_lt_zLen (by unfold nM; omega) hi
      have h2 : 2 + nT n * nN n + σ.vars "j" * nN n + σ.vars "i" =
          2 + (nT n + σ.vars "j") * nN n + σ.vars "i" := by ring
      have := rb_le_zLen n
      omega
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlS : (σ.arrs "S").length = n := hC.1.lS
    have htnv := hC.1.htn
    have hNv := hC.1.hN
    have hBn := hb.n_lt
    have hB5 := hb.five_lt_B
    have hBN := hb.nN_lt
    have hBz := hb.zLen_lt
    have hBtn := hb.tn_lt
    have hjN : σ.vars "j" * σ.vars "N" < B := by
      rw [hC.1.hN]
      have : σ.vars "j" * nN n ≤ (n - 1) * nN n := Nat.mul_le_mul_right _ (by omega)
      have h3 : (n - 1) * nN n ≤ nT n * nN n := Nat.mul_le_mul_right _ (by
        have := nn_le_nT n; have : n ≤ n * n := Nat.le_mul_self n; omega)
      have := hb.tn_lt
      omega
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_⟩; rw [hzc]))

/-- **The row loop**: `S[j] += m * coef (T + j) c` for every client `j`. -/
theorem addRow_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (c m : ℕ) (hc : c < nN n) (S0 : ℕ → ℕ) (hS0 : ∀ j < n, m + S0 j < B) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" = c ∧ σ.vars "mv" = m ∧
        σ.arrs "S" = arrOf n S0)
      addRow
      (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "i" = c ∧ σ'.vars "mv" = m ∧
        σ'.arrs "S" = arrOf n (fun j => S0 j + m * coef n (nT n + j) c))
      ((30 + 4) * n + 6) := by
  have hs := scan_spec (B := B) "j" "n" n 30 addRowBody
    (fun σ => CE n cnt bb v σ ∧ σ.vars "i" = c ∧ σ.vars "mv" = m)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => S0 j + if j < k then m * coef n (nT n + j) c else 0))
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (Stable.and (stable_var "i" (fun x => x = c) (by decide))
        (stable_var "mv" (fun x => x = m) (by decide))))
    hb.n_lt (fun σ h => h.1.1.hn) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hi, hm, hS⟩
      refine ⟨⟨hC.setVar (by decide) _, by simpa using hi, by simpa using hm⟩, ?_⟩
      simpa using hS
    · rintro σ σ' - ⟨⟨hC, hi, hm⟩, hS, -⟩
      refine ⟨hC, hi, hm, ?_⟩
      rw [hS]
      exact arrOf_congr fun j hj => by simp [hj]
  · intro k hk σ ⟨⟨hC, hi, hm⟩, hjk, hS⟩
    have hSk : (σ.arrs "S").getD (σ.vars "j") 0 = S0 k := by
      rw [hS, hjk, getD_arrOf_lt hk]; simp
    obtain ⟨σ', hr, h1, h2⟩ := addRowBody_vals hb v σ
      ⟨hC, by omega, by omega, by rw [hSk, hm]; exact hS0 k hk⟩
    refine ⟨σ', hr, by omega, ?_⟩
    rw [h2, hSk, hS, hi, hm, hjk, set_arrOf]
    refine arrOf_congr fun j _ => ?_
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h]
      have : (j < k + 1) ↔ (j < k) := by omega
      simp only [this]

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpS1` -/

section
/-!
The first pass over `Sj`: the small digits.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

/-- The small-digit part of `Sj`, over the columns below `k`. -/
def s1P (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) : ℕ :=
  ∑ c ∈ range k, if d c < Kn n then d c * coef n (nT n + j) c else 0

theorem s1P_succ (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) :
    s1P n d j (k + 1) =
      s1P n d j k + (if d k < Kn n then d k else 0) * coef n (nT n + j) k := by
  unfold s1P
  rw [Finset.sum_range_succ]
  by_cases h : d k < Kn n <;> simp [h]

theorem s1P_le (n : ℕ) (d : ℕ → ℕ) (j k : ℕ) : s1P n d j k ≤ k * Kn n := by
  induction k with
  | zero => simp [s1P]
  | succ k ih =>
    rw [s1P_succ]
    have h1 : (if d k < Kn n then d k else 0) * coef n (nT n + j) k ≤ Kn n := by
      have := coef_le_one n (nT n + j) k
      have h2 : (if d k < Kn n then d k else 0) ≤ Kn n := by split_ifs with h <;> omega
      calc _ ≤ (if d k < Kn n then d k else 0) * 1 := Nat.mul_le_mul_left _ this
        _ ≤ Kn n := by omega
    nlinarith


/-- The multiplier of the pass. -/
theorem mvAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n)
      (asg "mv" (.mul (.get "dg" (V "i")) (ltF (.get "dg" (V "i")) (V "K"))))
      (fun σ σ' => σ' = σ.setVar "mv" (v (σ.vars "i") * if v (σ.vars "i") < Kn n then 1 else 0))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    obtain ⟨hdgv, hldg, -⟩ := colFacts hv hC hi
    have hdg' : (σ.arrs "dg").getD (σ.vars "i") 0 = v (σ.vars "i") := by
      rw [hC.2, getD_arrOf_lt (by have : nN n ≤ Dn n := by unfold Dn; omega
                                  omega)]
    have hK := hC.1.hK
    have hBK := hb.NK_lt
    have hBN := hb.nN_lt
    have hBKn := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hprod := mul_le_of_le_one' ((σ.arrs "dg").getD (σ.vars "i") 0)
      (1 - (1 - (σ.vars "K" - (σ.arrs "dg").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hdg', hK]
    by_cases h : v (σ.vars "i") < Kn n
    · have e : 1 - (1 - (Kn n - v (σ.vars "i"))) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (Kn n - v (σ.vars "i"))) = 0 := by omega
      rw [e, if_neg h]

theorem s1_mult (n : ℕ) (v : ℕ → ℕ) (k : ℕ) (hk : k < nN n) :
    v k * (if v k < Kn n then 1 else 0) = if dd n v k < Kn n then dd n v k else 0 := by
  rw [dd_lt hk]; split_ifs <;> simp

/-- **The first pass over `Sj`.** -/
theorem s1Com_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "S" = arrOf n (fun _ => 0))
      s1Com (fun _ σ' => CE n cnt bb v σ' ∧
        σ'.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n)))
      ((30 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + ((30 + 4) * n + 6) + 4) s1Body
    (CE n cnt bb v)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j k))
    (CE.stable (by decide) (by decide) (by decide)) hb.nN_lt (fun σ h => h.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hS⟩
      refine ⟨hC.setVar (by decide) _, ?_⟩
      simpa [s1P] using hS
    · rintro σ σ' - ⟨hC, hS, -⟩
      exact ⟨hC, hS⟩
  · intro k hk σ ⟨hC, hik, hS⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    obtain ⟨σ1, r1, e1⟩ := mvAssign_vals hb v hv σ ⟨hC, by omega⟩
    have hm1 : σ1.vars "mv" = if dd n v k < Kn n then dd n v k else 0 := by
      rw [e1]; simp [Env.setVar, hik, s1_mult n v k hk]
    have hMK : (if dd n v k < Kn n then dd n v k else 0) ≤ Kn n := by
      rw [dd_lt hk]; split_ifs with h <;> omega
    have hC1 : CE n cnt bb v σ1 := by rw [e1]; exact hC.setVar (by decide) _
    have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
    have hS1 : σ1.arrs "S" = arrOf n (fun j => s1P n (dd n v) j k) := by rw [e1]; simpa using hS
    have hBK := hb.NK_lt
    obtain ⟨σ2, r2, hC2, hi2, hm2, hS2⟩ := addRow_spec hb v k _ hk
      (fun j => s1P n (dd n v) j k)
      (fun j _ => by
        have := s1P_le n (dd n v) j k
        have : k * Kn n ≤ nN n * Kn n := Nat.mul_le_mul_right _ hk.le
        rw [hm1]; omega) σ1 ⟨hC1, hi1, rfl, hS1⟩
    have hBN := hb.nN_lt
    obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by show σ2.vars "i" + 1 < B; rw [hi2]; omega)
    refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
    · rw [e3]; simp [Env.setVar, hi2]
    · rw [e3]
      show σ2.arrs "S" = _
      rw [hS2, hm1]
      refine arrOf_congr fun j _ => ?_
      rw [s1P_succ]

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpS2` -/

section
/-!
The second pass over `Sj`: what is left of the demand of the type of each base.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The base part of `Sj`, over the columns below `k`. -/
def s2P (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j k : ℕ) : ℕ :=
  ∑ c ∈ range k, if isBase n d c then cp n cnt d (tyIdx n c) * coef n (nT n + j) c else 0

theorem s2P_succ (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j k : ℕ) :
    s2P n cnt d j (k + 1) = s2P n cnt d j k +
      (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * coef n (nT n + j) k := by
  unfold s2P
  rw [Finset.sum_range_succ]
  by_cases h : isBase n d k <;> simp [h]

theorem Sj_eq_s (n : ℕ) (cnt : ℕ → ℕ) (d : ℕ → ℕ) (j : ℕ) :
    Sj n cnt d j = s1P n d j (nN n) + s2P n cnt d j (nN n) := rfl

theorem isBase_lt_V {n : ℕ} {d : ℕ → ℕ} {c : ℕ} (h : isBase n d c) : c < nV n := by
  obtain ⟨-, hτ, -⟩ := h
  by_contra hc
  exact hτ (tyOf_of_ge_V (by omega))

theorem isBase_tyIdx {n : ℕ} {d : ℕ → ℕ} {c : ℕ} (h : isBase n d c) :
    tyIdx n c = c / nZ n ∧ c / nZ n < nT n := by
  have hV := isBase_lt_V h
  have hτ := h.2.1
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hτ
  have := tyOf_eq_some_iff.mp ht
  have hlt : c / nZ n < nT n := by
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact hV
  refine ⟨?_, hlt⟩
  unfold tyIdx; rw [ht]; simp [this.2]

theorem s2P_le {n : ℕ} {cnt : ℕ → ℕ} {vb : ℕ} (hcnt : ∀ t < nT n, cnt t ≤ vb) (d : ℕ → ℕ)
    (j k : ℕ) : s2P n cnt d j k ≤ k * vb := by
  induction k with
  | zero => simp [s2P]
  | succ k ih =>
    rw [s2P_succ]
    have h1 : (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * coef n (nT n + j) k ≤ vb := by
      have hc := coef_le_one n (nT n + j) k
      have h2 : (if isBase n d k then cp n cnt d (tyIdx n k) else 0) ≤ vb := by
        split_ifs with h
        · obtain ⟨h3, h4⟩ := isBase_tyIdx h
          rw [h3]
          unfold cp
          exact (Nat.sub_le _ _).trans (hcnt _ h4)
        · omega
      calc _ ≤ (if isBase n d k then cp n cnt d (tyIdx n k) else 0) * 1 := Nat.mul_le_mul_left _ hc
        _ ≤ vb := by omega
    nlinarith

theorem mul_le_of_le_one_left' (c a : ℕ) (h : c ≤ 1) : c * a ≤ a := by
  rw [mul_comm]; exact mul_le_of_le_one' a c h

theorem tAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n)
      (asg "t" (.mul (.div (V "i") (V "Z")) (ltF (V "i") (V "V"))))
      (fun σ σ' => σ' = σ.setVar "t" (σ.vars "i" / nZ n * if σ.vars "i" < nV n then 1 else 0))
      30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hZ := hC.1.hZ
    have hV := hC.1.hV
    have hBN := hb.nN_lt
    have hBV := hb.nV_lt
    have hBZ := hb.nZ_lt
    have hB5 := hb.five_lt_B
    have hdiv : σ.vars "i" / σ.vars "Z" ≤ σ.vars "i" := Nat.div_le_self _ _
    have hprod := mul_le_of_le_one' (σ.vars "i" / σ.vars "Z")
      (1 - (1 - (σ.vars "V" - σ.vars "i"))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hZ, hV]
    by_cases h : σ.vars "i" < nV n
    · have e : 1 - (1 - (nV n - σ.vars "i")) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (nV n - σ.vars "i")) = 0 := by omega
      rw [e, if_neg h]

theorem mvAssign2_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb ∧
        (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n)
      (asg "mv" (.mul (eqF (.get "kd" (V "i")) (lit 1))
        (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))))
      (fun σ σ' => σ' = σ.setVar "mv" (if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 else 0))
      40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hzv : (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb :=
      ‹(σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb›
    have hsgv : (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n :=
      ‹(σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n›
    have hrb := hC.1.hrb
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hlkd : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBrb := hb.rb_lt
    have hBS := hb.SB_lt
    have hBK := hb.NK_lt
    have hidx : σ.vars "rb" + σ.vars "t" < zLen n := by
      have : nT n ≤ nM n := by unfold nM; omega
      unfold zLen; omega
    have hprod := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0)
      (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    by_cases h : (σ.arrs "kd").getD (σ.vars "i") 0 = 1
    · have e : 1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)) = 1 := by omega
      rw [e, if_pos h, one_mul]
    · have e : 1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)) = 0 := by omega
      rw [e, if_neg h, zero_mul]

/-- The static context of the second pass. -/
def C2 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "sg" = arrOf (nT n) (sigma n (dd n v))

theorem C2.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hs : "sg" ∉ c.warrs) : Stable c (C2 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (stable_arr "sg" (fun l => l = arrOf (nT n) (sigma n (dd n v))) hs))

theorem sigma_le' (n : ℕ) (d : ℕ → ℕ) (t : ℕ) : sigma n d t ≤ nN n * Kn n := sigma_le d t

/-- **The second pass over `Sj`.** -/
theorem s2Com_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C2 n cnt bb v σ ∧ σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n)))
      s2Com (fun _ σ' => C2 n cnt bb v σ' ∧
        σ'.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j))
      ((30 + 40 + ((30 + 4) * n + 6) + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 40 + ((30 + 4) * n + 6) + 4) s2Body
    (C2 n cnt bb v)
    (fun k σ => σ.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k))
    (C2.stable (by decide) (by decide) (by decide) (by decide) (by decide)) hb.nN_lt
    (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hS⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2⟩, ?_⟩
      simpa [s2P] using hS
    · rintro σ σ' - ⟨hC, hS, -⟩
      exact ⟨hC, by rw [hS]; exact arrOf_congr fun j _ => (Sj_eq_s n cnt _ j).symm⟩
  · intro k hk σ ⟨⟨hCE, hkd, hsg⟩, hik, hS⟩
    have hvk : v k ≤ Kn n := hv k (lt_of_lt_of_le hk (by unfold Dn; omega))
    have hBN := hb.nN_lt
    obtain ⟨σ1, r1, e1⟩ := tAssign_vals hb v hv σ ⟨hCE, by omega⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = k / nZ n * (if k < nV n then 1 else 0) := ⟨_, rfl⟩
    have ht'T : t' < nT n := by
      rw [ht']
      by_cases h : k < nV n
      · rw [if_pos h, mul_one]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h
      · rw [if_neg h, mul_zero]; exact nT_pos n
    have hσ1t : σ1.vars "t" = t' := by
      rw [e1, ht']; simp only [Env.setVar, if_true, hik]
    have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
    have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
    have hkd1 : σ1.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) := by rw [e1]; simpa using hkd
    have hsg1 : σ1.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) := by rw [e1]; simpa using hsg
    have hS1 : σ1.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k) := by
      rw [e1]; simpa using hS
    have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
      rw [hkd1, hi1]; exact getD_arrOf_lt hk
    have hzt : (σ1.arrs "z").getD (σ1.vars "rb" + σ1.vars "t") 0 = cnt t' := by
      rw [hCE1.1.hz, hCE1.1.hrb, hσ1t, ilpWord_rhs n cnt bb (by unfold nM; omega)]
      unfold rhs; rw [if_pos ht'T]
    have hsgt : (σ1.arrs "sg").getD (σ1.vars "t") 0 = sigma n (dd n v) t' := by
      rw [hsg1, hσ1t]; exact getD_arrOf_lt ht'T
    obtain ⟨σ2, r2, e2⟩ := mvAssign2_vals hb v σ1
      ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _,
        by rw [hzt]; exact hb.hcnt _ ht'T, by rw [hsgt]; exact sigma_le' _ _ _⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (if kindOf n (dd n v) k = 1 then cnt t' - sigma n (dd n v) t' else 0) := ⟨_, rfl⟩
    have hσ2m : σ2.vars "mv" = m := by
      rw [e2, hm]; simp only [Env.setVar, if_true, hkdk, hzt, hsgt]
    have hCE2 : CE n cnt bb v σ2 := by rw [e2]; exact hCE1.setVar (by decide) _
    have hi2 : σ2.vars "i" = k := by rw [e2]; simpa using hi1
    have hS2 : σ2.arrs "S" = arrOf n (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k) := by
      rw [e2]; simpa using hS1
    have hmb : m ≤ vb := by
      rw [hm]; split_ifs
      · exact (Nat.sub_le _ _).trans (hb.hcnt _ ht'T)
      · omega
    have hSB := hb.SB_lt
    obtain ⟨σ3, r3, hC3, hi3, hm3, hS3⟩ := addRow_spec hb v k m hk
      (fun j => s1P n (dd n v) j (nN n) + s2P n cnt (dd n v) j k)
      (fun j _ => by
        have h1 := s1P_le n (dd n v) j (nN n)
        have h2 := s2P_le hb.hcnt (dd n v) j k (cnt := cnt) (n := n)
        have h3 : k * vb ≤ nN n * vb := Nat.mul_le_mul_right _ hk.le
        have h4 : nN n * (Kn n + vb) = nN n * Kn n + nN n * vb := by ring
        omega) σ2 ⟨hCE2, hi2, hσ2m, hS2⟩
    obtain ⟨σ4, r4, e4⟩ := bump_spec (B := B) "i" hb.one_lt_B σ3 (by
      show σ3.vars "i" + 1 < B; rw [hi3]; omega)
    have hmeq : m = if isBase n (dd n v) k then cp n cnt (dd n v) (tyIdx n k) else 0 := by
      by_cases hb1 : isBase n (dd n v) k
      · obtain ⟨h3, h4⟩ := isBase_tyIdx hb1
        have hV := isBase_lt_V hb1
        have ht'' : t' = k / nZ n := by rw [ht', if_pos hV, mul_one]
        rw [hm, if_pos (kindOf_eq_one.mpr hb1), if_pos hb1, h3, ht'']
        rfl
      · rw [hm, if_neg (fun h => hb1 (kindOf_eq_one.mp h)), if_neg hb1]
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, ?_⟩
    · rw [e4]; simp [Env.setVar, hi3]
    · rw [e4]
      show σ3.arrs "S" = _
      rw [hS3]
      refine arrOf_congr fun j _ => ?_
      rw [s2P_succ, ← hmeq]
      ring

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpPq` -/

section
/-!
The sums `P` and `Q` of a row of `H`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section


/-- Facts about the current entry of `H` and the current row. -/
theorem pqFacts {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) {σ : Env} (hC : CE n cnt bb v σ) (hr : σ.vars "r" < n)
    (hj : σ.vars "j" < n) :
    σ.vars "N" + σ.vars "r" * σ.vars "n" + σ.vars "j" = hpIdx n (σ.vars "r") (σ.vars "j") ∧
    σ.vars "N" + σ.vars "nn" + σ.vars "r" * σ.vars "n" + σ.vars "j" =
      hnIdx n (σ.vars "r") (σ.vars "j") ∧
    (σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 ≤ Kn n ∧
    (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 ≤ Kn n ∧
    hpIdx n (σ.vars "r") (σ.vars "j") < (σ.arrs "dg").length ∧
    hnIdx n (σ.vars "r") (σ.vars "j") < (σ.arrs "dg").length ∧
    σ.vars "r" * σ.vars "n" < B := by
  have hNv := hC.1.hN
  have hnv := hC.1.hn
  have hnnv := hC.1.hnn
  have hp := hpIdx_lt hr hj
  have hh := hnIdx_lt hr hj
  have hD : nN n + 2 * (n * n) < Dn n := by unfold Dn; omega
  have hDl := hC.1.ldg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hNv, hnv]; unfold hpIdx; ring
  · rw [hNv, hnv, hnnv]; unfold hnIdx; ring
  · rw [hC.2, getD_arrOf_lt (by omega)]; exact hv _ (by omega)
  · rw [hC.2, getD_arrOf_lt (by omega)]; exact hv _ (by omega)
  · omega
  · omega
  · rw [hnv]
    have : σ.vars "r" * n ≤ n * n := Nat.mul_le_mul_right _ hr.le
    have := hb.nn_lt
    omega

theorem pqBody_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" < n ∧ σ.vars "j" < n ∧
        (σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb) ∧
        σ.vars "P" + Pterm n vb ≤ Pbd n vb ∧ σ.vars "Q" + Pterm n vb ≤ Pbd n vb)
      pqInner
      (fun σ σ' => σ'.vars "j" = σ.vars "j" + 1 ∧
        σ'.vars "P" = σ.vars "P" +
          ((σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 * bb +
            (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 * (σ.arrs "S").getD (σ.vars "j") 0) ∧
        σ'.vars "Q" = σ.vars "Q" +
          ((σ.arrs "dg").getD (hpIdx n (σ.vars "r") (σ.vars "j")) 0 * (σ.arrs "S").getD (σ.vars "j") 0 +
            (σ.arrs "dg").getD (hnIdx n (σ.vars "r") (σ.vars "j")) 0 * bb)) 80 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hr : σ.vars "r" < n := ‹σ.vars "r" < n›
    have hj : σ.vars "j" < n := ‹σ.vars "j" < n›
    have hSj : (σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb) :=
      ‹(σ.arrs "S").getD (σ.vars "j") 0 ≤ nN n * (Kn n + vb)›
    have hPb : σ.vars "P" + Pterm n vb ≤ Pbd n vb := ‹σ.vars "P" + Pterm n vb ≤ Pbd n vb›
    have hQb : σ.vars "Q" + Pterm n vb ≤ Pbd n vb := ‹σ.vars "Q" + Pterm n vb ≤ Pbd n vb›
    obtain ⟨e1, e2, hpv, hnv, hlp, hln, hrn⟩ := pqFacts hb v hv hC hr hj
    have hbbv := hC.1.hbb
    have hpv' : (σ.arrs "dg").getD (σ.vars "N" + σ.vars "r" * σ.vars "n" + σ.vars "j") 0 ≤ Kn n := by
      rw [e1]; exact hpv
    have hnv' : (σ.arrs "dg").getD (σ.vars "N" + σ.vars "nn" + σ.vars "r" * σ.vars "n" + σ.vars "j") 0 ≤ Kn n := by
      rw [e2]; exact hnv
    have hbb' : σ.vars "bb" ≤ vb := by have := hb.hbb; omega
    have hprod1 := Nat.mul_le_mul hpv' hbb'
    have hprod2 := Nat.mul_le_mul hnv' hSj
    have hprod3 := Nat.mul_le_mul hpv' hSj
    have hprod4 := Nat.mul_le_mul hnv' hbb'
    have hPT : Pterm n vb ≤ Pbd n vb := by
      unfold Pbd; exact Nat.le_mul_of_pos_left _ hb.n1
    have hPterm : Kn n * vb + Kn n * (nN n * (Kn n + vb)) = Pterm n vb := rfl
    have hlS : (σ.arrs "S").length = n := hC.1.lS
    have hBP := hb.Pbd_lt
    have hBD := hb.Dn_lt
    have hBS := hb.SB_lt
    have hDl := hC.1.ldg
    have hBtn := hb.tn_lt
    have hBn := hb.n_lt
    have hBN := hb.nN_lt
    have hBnn := hb.nn_lt
    have hBK := hb.Kn_lt
    have hB5 := hb.five_lt_B
    have hNv := hC.1.hN
    have hnnv := hC.1.hnn
    have hD : nN n + 2 * (n * n) < Dn n := by unfold Dn; omega
    have hnv' := hC.1.hn
    have hbbB : bb < B := hb.lt_U (by have := hb.hbb; unfold Ub; omega)
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (refine ⟨trivial, ?_, ?_⟩ <;> rw [hbbv, ← e1, ← e2]))

/-- The sum `P` of a row. -/
def pSum (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ j ∈ range k, (v (hpIdx n r j) * bb + v (hnIdx n r j) * Sf j)

/-- The sum `Q` of a row. -/
def qSum (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ j ∈ range k, (v (hpIdx n r j) * Sf j + v (hnIdx n r j) * bb)

theorem pSum_succ (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) :
    pSum n v bb Sf r (k + 1) = pSum n v bb Sf r k + (v (hpIdx n r k) * bb + v (hnIdx n r k) * Sf k) := by
  unfold pSum; rw [Finset.sum_range_succ]

theorem qSum_succ (n : ℕ) (v : ℕ → ℕ) (bb : ℕ) (Sf : ℕ → ℕ) (r k : ℕ) :
    qSum n v bb Sf r (k + 1) = qSum n v bb Sf r k + (v (hpIdx n r k) * Sf k + v (hnIdx n r k) * bb) := by
  unfold qSum; rw [Finset.sum_range_succ]

theorem pq_term_le {n vb : ℕ} {bb : ℕ} (hbb : bb ≤ vb) (v : ℕ → ℕ) (hv : ∀ q < Dn n, v q ≤ Kn n)
    (Sf : ℕ → ℕ) (j : ℕ) (hS : Sf j ≤ nN n * (Kn n + vb)) (r : ℕ) (hr : r < n) (hj : j < n) :
    v (hpIdx n r j) * bb + v (hnIdx n r j) * Sf j ≤ Pterm n vb ∧
    v (hpIdx n r j) * Sf j + v (hnIdx n r j) * bb ≤ Pterm n vb := by
  have hp := hpIdx_lt hr hj
  have hh := hnIdx_lt hr hj
  have hp' : v (hpIdx n r j) ≤ Kn n := hv _ (by unfold Dn; omega)
  have hn' : v (hnIdx n r j) ≤ Kn n := hv _ (by unfold Dn; omega)
  have h1 := Nat.mul_le_mul hp' hbb
  have h2 := Nat.mul_le_mul hn' hS
  have h3 := Nat.mul_le_mul hp' hS
  have h4 := Nat.mul_le_mul hn' hbb
  unfold Pterm
  constructor <;> omega

theorem pSum_le {n vb : ℕ} {bb : ℕ} (hbb : bb ≤ vb) (v : ℕ → ℕ) (hv : ∀ q < Dn n, v q ≤ Kn n)
    (Sf : ℕ → ℕ) (hS : ∀ j < n, Sf j ≤ nN n * (Kn n + vb)) (r : ℕ) (hr : r < n) (k : ℕ) (hk : k ≤ n) :
    pSum n v bb Sf r k ≤ k * Pterm n vb ∧ qSum n v bb Sf r k ≤ k * Pterm n vb := by
  induction k with
  | zero => simp [pSum, qSum]
  | succ k ih =>
    rw [pSum_succ, qSum_succ]
    have := pq_term_le hbb v hv Sf k (hS k (by omega)) r hr (by omega)
    have ih' := ih (by omega)
    constructor <;> nlinarith [ih'.1, ih'.2]

/-- **The sums `P` and `Q` of a row.** -/
theorem pqCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (Sf : ℕ → ℕ) (hSf : ∀ j < n, Sf j ≤ nN n * (Kn n + vb))
    (r : ℕ) (hr : r < n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
      pqCom (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
        σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
      (2 + 2 + ((80 + 4) * n + 6)) := by
  have hs := scan_spec (B := B) "j" "n" n 80 pqInner
    (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
    (fun k σ => σ.vars "P" = pSum n v bb Sf r k ∧ σ.vars "Q" = qSum n v bb Sf r k)
    (Stable.and (CE.stable (by decide) (by decide) (by decide))
      (Stable.and (stable_var "r" (fun x => x = r) (by decide))
        (stable_arr "S" (fun l => l = arrOf n Sf) (by decide))))
    hb.n_lt (fun σ h => h.1.1.hn) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
        (asg "P" (lit 0)) (fun σ σ' => σ' = σ.setVar "P" 0) 2 :=
      Spec.pre (assign_lit_spec (B := B) "P" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
    have hA' : Spec B (fun σ => (CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf) ∧
        σ.vars "P" = 0)
        (asg "Q" (lit 0)) (fun σ σ' => σ' = σ.setVar "Q" 0) 2 :=
      Spec.pre (assign_lit_spec (B := B) "Q" 0 (by have := hb.five_lt_B; omega)) (fun _ _ => trivial)
    have h2 : Spec B (fun σ => (CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf) ∧
        σ.vars "P" = 0)
        (.seq (asg "Q" (lit 0)) (forZ "j" "n" pqInner))
        (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
          σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
        (2 + ((80 + 4) * n + 6)) := by
      refine Spec.seq hA' hs ?_ ?_
      · intro σ σ1 hσ e
        rw [e]
        obtain ⟨⟨hC, hr', hS⟩, hP0⟩ := hσ
        refine ⟨⟨(hC.setVar (by decide) _).setVar (by decide) _, by simpa using hr',
          by simpa using hS⟩, ?_⟩
        simp [pSum, qSum, hP0]
      · intro σ σ1 σ2 hσ e hpost
        exact ⟨hpost.1.1, hpost.1.2.1, hpost.1.2.2, hpost.2.1.1, hpost.2.1.2⟩
    have h1 : Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "r" = r ∧ σ.arrs "S" = arrOf n Sf)
        (.seq (asg "P" (lit 0)) (.seq (asg "Q" (lit 0)) (forZ "j" "n" pqInner)))
        (fun _ σ' => CE n cnt bb v σ' ∧ σ'.vars "r" = r ∧ σ'.arrs "S" = arrOf n Sf ∧
          σ'.vars "P" = pSum n v bb Sf r n ∧ σ'.vars "Q" = qSum n v bb Sf r n)
        (2 + (2 + ((80 + 4) * n + 6))) := by
      refine Spec.seq hA h2 ?_ ?_
      · intro σ σ1 hσ e
        rw [e]
        obtain ⟨hC, hr', hS⟩ := hσ
        exact ⟨⟨hC.setVar (by decide) _, by simpa using hr', by simpa using hS⟩, by simp⟩
      · intro σ σ1 σ2 hσ e hpost
        exact hpost
    unfold pqCom
    exact Spec.mono h1 (by omega)
  · intro k hk σ ⟨⟨hC, hr', hS⟩, hjk, hP, hQ⟩
    have hkn : k < n := hk
    have hcnt : ((σ.arrs "S").getD (σ.vars "j") 0) = Sf k := by
      rw [hS, hjk, getD_arrOf_lt hk]
    have hPQ := pSum_le (hb.hbb : bb ≤ vb) v hv Sf hSf r hr k hk.le
    have hPT : (k + 1) * Pterm n vb ≤ Pbd n vb := by unfold Pbd; exact Nat.mul_le_mul_right _ hk
    obtain ⟨σ', hrun, h1, h2, h3⟩ := pqBody_vals hb v hv σ
      ⟨hC, by rw [hr']; exact hr, by omega, by rw [hcnt]; exact hSf k hk, by
        rw [hP]; nlinarith [hPQ.1], by rw [hQ]; nlinarith [hPQ.2]⟩
    refine ⟨σ', hrun, by omega, ?_, ?_⟩
    · rw [h2, hP, pSum_succ, hcnt, hr', hjk, hC.2, getD_arrOf_lt (by have := hpIdx_lt hr hk; unfold Dn; omega),
        getD_arrOf_lt (by have := hnIdx_lt hr hk; unfold Dn; omega)]
    · rw [h3, hQ, qSum_succ, hcnt, hr', hjk, hC.2, getD_arrOf_lt (by have := hpIdx_lt hr hk; unfold Dn; omega),
        getD_arrOf_lt (by have := hnIdx_lt hr hk; unfold Dn; omega)]

theorem certVec_Hp {n : ℕ} (v : ℕ → ℕ) {r j : ℕ} (hr : r < n) (hj : j < n) :
    (certVec n v).Hp r j = v (hpIdx n r j) := by simp [certVec, hr, hj]

theorem certVec_Hn {n : ℕ} (v : ℕ → ℕ) {r j : ℕ} (hr : r < n) (hj : j < n) :
    (certVec n v).Hn r j = v (hnIdx n r j) := by simp [certVec, hr, hj]

theorem pSum_eq_Pi (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (r : ℕ) (hr : r < n) :
    pSum n v bb (fun j => Sj n cnt (dd n v) j) r n = Pi n cnt bb (certVec n v) r := by
  unfold pSum Pi
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [certVec_Hp v hr hj', certVec_Hn v hr hj']

theorem qSum_eq_Qi (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (r : ℕ) (hr : r < n) :
    qSum n v bb (fun j => Sj n cnt (dd n v) j) r n = Qi n cnt bb (certVec n v) r := by
  unfold qSum Qi
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [certVec_Hp v hr hj', certVec_Hn v hr hj']

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpWv` -/

section
/-!
The values of the extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem rAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n)
      (asg "r" (.mul (.get "rkA" (V "i")) (ltF (.get "rkA" (V "i")) (V "n"))))
      (fun σ σ' => σ' = σ.setVar "r" ((σ.arrs "rkA").getD (σ.vars "i") 0 *
        if (σ.arrs "rkA").getD (σ.vars "i") 0 < n then 1 else 0)) 30 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hrk : (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n := ‹(σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n›
    have hlr : (σ.arrs "rkA").length = nN n := hC.1.lrk
    have hnv := hC.1.hn
    have hBN := hb.nN_lt
    have hBn := hb.n_lt
    have hB5 := hb.five_lt_B
    have hprod := mul_le_of_le_one' ((σ.arrs "rkA").getD (σ.vars "i") 0)
      (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hnv]
    by_cases h : (σ.arrs "rkA").getD (σ.vars "i") 0 < n
    · have e : 1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0)) = 1 := by omega
      rw [e, if_pos h]
    · have e : 1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0)) = 0 := by omega
      rw [e, if_neg h]

theorem wvStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧
        (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n ∧ σ.vars "P" ≤ Pbd n vb ∧ σ.vars "Q" ≤ Pbd n vb ∧
        σ.vars "dl" ≤ Kn n)
      (.store "wv" (V "i")
        (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (.get "rkA" (V "i")) (V "n")))
          (.div (.sub (V "P") (V "Q")) (V "dl"))))
      (fun σ σ' => σ' = σ.setArr "wv" (σ.vars "i")
        (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 ∧ (σ.arrs "rkA").getD (σ.vars "i") 0 < n then
          (σ.vars "P" - σ.vars "Q") / σ.vars "dl" else 0)) 40 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hrk : (σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n := ‹(σ.arrs "rkA").getD (σ.vars "i") 0 ≤ nN n›
    have hPb : σ.vars "P" ≤ Pbd n vb := ‹σ.vars "P" ≤ Pbd n vb›
    have hQb : σ.vars "Q" ≤ Pbd n vb := ‹σ.vars "Q" ≤ Pbd n vb›
    have hdl : σ.vars "dl" ≤ Kn n := ‹σ.vars "dl" ≤ Kn n›
    have hBK := hb.Kn_lt
    have hlr : (σ.arrs "rkA").length = nN n := hC.1.lrk
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hnv := hC.1.hn
    have hBN := hb.nN_lt
    have hBn := hb.n_lt
    have hBP := hb.Pbd_lt
    have hB5 := hb.five_lt_B
    have hdiv : (σ.vars "P" - σ.vars "Q") / σ.vars "dl" ≤ σ.vars "P" - σ.vars "Q" := Nat.div_le_self _ _
    have hprod := mul_le_of_le_one_left'
      ((1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) *
        (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))))
      ((σ.vars "P" - σ.vars "Q") / σ.vars "dl") (by
        have h1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
        have h2 : (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) ≤ 1 := by omega
        calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
          _ = 1 := rfl)
    have hprod2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      (1 - (1 - (σ.vars "n" - (σ.arrs "rkA").getD (σ.vars "i") 0))) (by omega)
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hnv]
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - (1 - (n - (σ.arrs "rkA").getD (σ.vars "i") 0))) =
        if (σ.arrs "rkA").getD (σ.vars "i") 0 < n then 1 else 0 := by split_ifs <;> omega
    rw [f1, f2]
    by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2 <;>
      by_cases h2 : (σ.arrs "rkA").getD (σ.vars "i") 0 < n <;>
      simp only [h1, h2, if_true, if_false, one_mul, mul_one, zero_mul, mul_zero, and_self, and_true,
        true_and, and_false, false_and]

theorem dlAssign_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ)
      (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn")))))
      (fun σ σ' => σ' = σ.setVar "dl" (v (dlIdx n))) 20 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hN := hC.1.hN
    have hnn := hC.1.hnn
    have hDl := hC.1.ldg
    have hlt : dlIdx n < Dn n := dlIdx_lt n
    have hd : (σ.arrs "dg").getD (dlIdx n) 0 = v (dlIdx n) := by
      rw [hC.2]; exact getD_arrOf_lt hlt
    have hdv := hv _ hlt
    have hBK := hb.Kn_lt
    have hBD := hb.Dn_lt
    have hB5 := hb.five_lt_B
    have hidx : σ.vars "N" + 2 * σ.vars "nn" = dlIdx n := by unfold dlIdx; omega
    clear_runs
  all_goals (first | omega | (rw [hidx, hd]; done) | (rw [hidx, hd]; omega))

/-- The static context of the pass of the values. -/
def C3 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
    σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ σ.vars "dl" = v (dlIdx n)

theorem C3.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hr : "rkA" ∉ c.warrs) (hs : "S" ∉ c.warrs) (hdl : "dl" ∉ c.wvars) :
    Stable c (C3 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (Stable.and (stable_arr "rkA" (fun l => l = arrOf (nN n) (rk n (dd n v))) hr)
        (Stable.and (stable_arr "S" (fun l => l = arrOf n (fun j => Sj n cnt (dd n v) j)) hs)
          (stable_var "dl" (fun x => x = v (dlIdx n)) hdl))))

theorem Sj_le_Sb {n : ℕ} {cnt : ℕ → ℕ} {vb : ℕ} (hcnt : ∀ t < nT n, cnt t ≤ vb) (d : ℕ → ℕ) (j : ℕ) :
    Sj n cnt d j ≤ nN n * (Kn n + vb) := by
  rw [Sj_eq_s]
  have h1 := s1P_le n d j (nN n)
  have h2 := s2P_le hcnt d j (nN n) (cnt := cnt) (n := n)
  have h4 : nN n * (Kn n + vb) = nN n * Kn n + nN n * vb := by ring
  omega

theorem rk_le_self (n : ℕ) (d : ℕ → ℕ) (k : ℕ) : rk n d k ≤ k := by
  unfold rk
  calc _ ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := Finset.card_range k

theorem wvF_step {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ} {k : ℕ} :
    (if kindOf n (dd n v) k = 2 ∧ rk n (dd n v) k < n then
      (Pi n cnt bb (certVec n v) (rk n (dd n v) k * if rk n (dd n v) k < n then 1 else 0) -
        Qi n cnt bb (certVec n v) (rk n (dd n v) k * if rk n (dd n v) k < n then 1 else 0)) / v (dlIdx n)
     else 0) = wvF n cnt bb (certVec n v) k := by
  unfold wvF
  by_cases h : kindOf n (dd n v) k = 2 ∧ rk n (dd n v) k < n
  · have h' : isExtra n (certVec n v).d k ∧ rk n (certVec n v).d k < n :=
      ⟨kindOf_eq_two.mp h.1, h.2⟩
    rw [if_pos h, if_pos h', if_pos h.2, mul_one]
    unfold wcol
    rfl
  · have h' : ¬ (isExtra n (certVec n v).d k ∧ rk n (certVec n v).d k < n) :=
      fun h2 => h ⟨kindOf_eq_two.mpr h2.1, h2.2⟩
    rw [if_neg h, if_neg h']

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpWvLoop` -/

section
/-!
The pass of the values of the extras: the loop.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- **One turn of the pass of the values.** -/
theorem wvBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C3 n cnt bb v σ)
    (hik : σ.vars "i" = k) :
    ∃ σ', Run B wvBody σ σ' (30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "wv" = (σ.arrs "wv").set k (wvF n cnt bb (certVec n v) k) := by
  obtain ⟨hCE, hkd, hrk, hS, hdl⟩ := hC
  have hBN := hb.nN_lt
  have hrkk : (σ.arrs "rkA").getD (σ.vars "i") 0 = rk n (dd n v) k := by
    rw [hrk, hik]; exact getD_arrOf_lt hk
  have hkdk : (σ.arrs "kd").getD (σ.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd, hik]; exact getD_arrOf_lt hk
  have hrkle : rk n (dd n v) k ≤ nN n := (rk_le_self n _ k).trans hk.le
  obtain ⟨σ1, r1, e1⟩ := rAssign_vals hb v σ ⟨hCE, by omega, by rw [hrkk]; exact hrkle⟩
  obtain ⟨r', hr'⟩ : ∃ r', r' = rk n (dd n v) k * (if rk n (dd n v) k < n then 1 else 0) := ⟨_, rfl⟩
  have hr'n : r' < n := by
    rw [hr']
    by_cases h : rk n (dd n v) k < n
    · rw [if_pos h, mul_one]; exact h
    · rw [if_neg h, mul_zero]; exact hb.n1
  have hσ1r : σ1.vars "r" = r' := by
    rw [e1, hr', hrkk]; simp [Env.setVar]
  have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
  have hS1 : σ1.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) := by rw [e1]; simpa using hS
  have hSf : ∀ j < n, Sj n cnt (dd n v) j ≤ nN n * (Kn n + vb) := fun j _ =>
    Sj_le_Sb hb.hcnt _ j
  obtain ⟨σ2, r2, ⟨hCE2, hr2, hS2, hP2, hQ2⟩, hfv, hfa, -, -⟩ :=
    (pqCom_spec hb v hv (fun j => Sj n cnt (dd n v) j) hSf r' hr'n).frame σ1 ⟨hCE1, hσ1r, hS1⟩
  have hi2 : σ2.vars "i" = k := by rw [hfv "i" (by decide), ← hik, e1]; simp [Env.setVar]
  have hdl2 : σ2.vars "dl" = v (dlIdx n) := by rw [hfv "dl" (by decide), e1]; simpa [Env.setVar] using hdl
  have hkd2 : σ2.arrs "kd" = σ.arrs "kd" := by rw [hfa "kd" (by decide), e1]; rfl
  have hrk2 : σ2.arrs "rkA" = σ.arrs "rkA" := by rw [hfa "rkA" (by decide), e1]; rfl
  have hhb : bb ≤ vb := hb.hbb
  have hPQ := pSum_le hhb v hv (fun j => Sj n cnt (dd n v) j) hSf r' hr'n n le_rfl
  have hPbd : n * Pterm n vb = Pbd n vb := rfl
  have hdlK : v (dlIdx n) ≤ Kn n := hv _ (dlIdx_lt n)
  have hkd3 : (σ2.arrs "kd").getD k 0 = kindOf n (dd n v) k := by
    rw [hkd2, hkd]; exact getD_arrOf_lt hk
  have hrk3 : (σ2.arrs "rkA").getD k 0 = rk n (dd n v) k := by
    rw [hrk2, hrk]; exact getD_arrOf_lt hk
  obtain ⟨σ3, r3, e3⟩ := wvStore_vals hb v σ2
    ⟨hCE2, by omega, by rw [hi2, hkd3]; exact kindOf_le_three _ _ _, by rw [hi2, hrk3]; exact hrkle,
      by rw [hP2]; have := hPQ.1; omega, by rw [hQ2]; have := hPQ.2; omega,
      by rw [hdl2]; exact hdlK⟩
  have hi3 : σ3.vars "i" = k := by rw [e3]; simpa [Env.setArr] using hi2
  obtain ⟨σ4, r4, e4⟩ := bump_spec (B := B) "i" hb.one_lt_B σ3 (by
    show σ3.vars "i" + 1 < B; rw [hi3]; omega)
  have hwv2 : σ2.arrs "wv" = σ.arrs "wv" := by rw [hfa "wv" (by decide), e1]; rfl
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_, ?_⟩
  · rw [e4]; simp [Env.setVar, hi3]
  · rw [e4]
    show σ3.arrs "wv" = _
    rw [e3]
    simp only [Env.setArr, if_true]
    rw [hi2, hwv2, hkd3, hrk3, hP2, hQ2, hdl2, pSum_eq_Pi n cnt bb v r' hr'n, qSum_eq_Qi n cnt bb v r' hr'n, hr']
    rw [wvF_step]

/-- **The pass of the values of the extras.** -/
theorem wvCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ ∃ f, σ.arrs "wv" = arrOf (nN n) f)
      wvCom
      (fun _ σ' => C3 n cnt bb v σ' ∧ σ'.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v)))
      (20 + (((30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) + 4) * nN n + 6)) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + (2 + 2 + ((80 + 4) * n + 6)) + 40 + 4) wvBody
    (C3 n cnt bb v)
    (fun k σ => ∃ f, σ.arrs "wv" = arrOf (nN n) f ∧ ∀ c < k, f c = wvF n cnt bb (certVec n v) c)
    (C3.stable (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · have hA : Spec B (fun σ => CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
        σ.arrs "rkA" = arrOf (nN n) (rk n (dd n v)) ∧
        σ.arrs "S" = arrOf n (fun j => Sj n cnt (dd n v) j) ∧ ∃ f, σ.arrs "wv" = arrOf (nN n) f)
        (asg "dl" (.get "dg" (.add (V "N") (.mul (lit 2) (V "nn")))))
        (fun σ σ' => σ' = σ.setVar "dl" (v (dlIdx n))) 20 :=
      Spec.pre (dlAssign_vals hb v hv) (fun σ h => h.1)
    refine Spec.mono (Spec.seq hA hs ?_ ?_) le_rfl
    · intro σ σ1 hσ e
      rw [e]
      obtain ⟨hC, hkd, hrk, hS, f, hf⟩ := hσ
      refine ⟨⟨(hC.setVar (by decide) _).setVar (by decide) _, by simpa using hkd, by simpa using hrk,
        by simpa using hS, by simp⟩, ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩⟩
    · intro σ σ1 σ2 hσ e hpost
      obtain ⟨hC, ⟨f, hf, hfk⟩, -⟩ := hpost
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, f, hf, hfk⟩
    obtain ⟨σ', hr, h1, h2⟩ := wvBody_step hb v hv k hk σ hC hik
    refine ⟨σ', hr, h1, ⟨fun j => if j = k then wvF n cnt bb (certVec n v) k else f j, ?_, ?_⟩⟩
    · rw [h2, hf, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpEs` -/

section
/-!
The pass computing `extraSum`: for every type, the sum of the values of its extras.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The sum defining `esF`, over the columns below `k`. -/
def esP (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t k : ℕ) : ℕ :=
  ∑ c ∈ range k, if isExtra n ω.d c ∧ tyOf n c = some t then wvF n cnt bb ω c else 0

theorem esF_eq_esP (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t : ℕ) :
    esF n cnt bb ω t = esP n cnt bb ω t (nN n) := rfl

theorem esP_succ (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t k : ℕ) :
    esP n cnt bb ω t (k + 1) = esP n cnt bb ω t k +
      if isExtra n ω.d k ∧ tyOf n k = some t then wvF n cnt bb ω k else 0 := by
  unfold esP; rw [Finset.sum_range_succ]


theorem esP_step {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {ω : Cert} {t k : ℕ} :
    esP n cnt bb ω t (k + 1) = esP n cnt bb ω t k +
      if (isExtra n ω.d k ∧ k < nV n ∧ k / nZ n = t) then wvF n cnt bb ω k else 0 := by
  rw [esP_succ]
  congr 1
  have : (isExtra n ω.d k ∧ tyOf n k = some t) ↔ (isExtra n ω.d k ∧ k < nV n ∧ k / nZ n = t) := by
    constructor
    · rintro ⟨he, ht⟩
      obtain ⟨hl, ht'⟩ := tyOf_eq_some_iff.mp ht
      exact ⟨he, hl.1, ht'.symm⟩
    · rintro ⟨he, hV, ht⟩
      have hlive := ((mem_Lset_iff n ω.d k).mp he.1).1
      have hlv : liveP n k := (isLive_iff_of_lt_V hV).mp hlive
      exact ⟨he, tyOf_eq_some_iff.mpr ⟨hlv, ht.symm⟩⟩
  simp only [this]

/-- A value of an extra is at most `Pbd`. -/
theorem wvF_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (c : ℕ) : wvF n cnt bb (certVec n v) c ≤ Pbd n vb := by
  unfold wvF
  split_ifs with h
  · have hr := h.2
    have hSf : ∀ j < n, Sj n cnt (dd n v) j ≤ nN n * (Kn n + vb) := fun j _ =>
      Sj_le_Sb hb.hcnt _ j
    have hPQ := pSum_le (hb.hbb : bb ≤ vb) v hv (fun j => Sj n cnt (dd n v) j) hSf _ hr n le_rfl
    have := pSum_eq_Pi n cnt bb v (rk n (certVec n v).d c) hr
    unfold wcol
    calc _ ≤ _ := Nat.div_le_self _ _
      _ ≤ Pi n cnt bb (certVec n v) (rk n (certVec n v).d c) := Nat.sub_le _ _
      _ ≤ Pbd n vb := by rw [← this]; exact hPQ.1
  · exact Nat.zero_le _

theorem esP_le {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (t k : ℕ) :
    esP n cnt bb (certVec n v) t k ≤ k * Pbd n vb := by
  induction k with
  | zero => simp [esP]
  | succ k ih =>
    rw [esP_succ]
    have : (if isExtra n (certVec n v).d k ∧ tyOf n k = some t then wvF n cnt bb (certVec n v) k else 0)
        ≤ Pbd n vb := by
      split_ifs
      · exact wvF_le hb v hv k
      · omega
    nlinarith

theorem esStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧ (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb ∧
        (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb)
      (.store "es" (V "t")
        (.add (.get "es" (V "t"))
          (.mul (.mul (eqF (.get "kd" (V "i")) (lit 2)) (ltF (V "i") (V "V")))
            (.get "wv" (V "i")))))
      (fun σ σ' => σ' = σ.setArr "es" (σ.vars "t")
        ((σ.arrs "es").getD (σ.vars "t") 0 +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 ∧ σ.vars "i" < nV n then
            (σ.arrs "wv").getD (σ.vars "i") 0 else 0))) 50 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hwv : (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb := ‹(σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb›
    have hes : (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb :=
      ‹(σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb›
    have hles : (σ.arrs "es").length = nT n := hC.1.les
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hVv := hC.1.hV
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBV := hb.nV_lt
    have hBE := hb.Ebd_lt
    have hB5 := hb.five_lt_B
    have hprod1 := mul_le_of_le_one_left'
      ((1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) *
        (1 - (1 - (σ.vars "V" - σ.vars "i"))))
      ((σ.arrs "wv").getD (σ.vars "i") 0) (by
        have h1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
        have h2 : (1 - (1 - (σ.vars "V" - σ.vars "i"))) ≤ 1 := by omega
        calc _ ≤ 1 * 1 := Nat.mul_le_mul h1 h2
          _ = 1 := rfl)
    have hprod2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      (1 - (1 - (σ.vars "V" - σ.vars "i"))) (by omega)
    have hNP : nN n * Pbd n vb ≤ nN n * Pbd n vb := le_rfl
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    rw [hVv]
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - (1 - (nV n - σ.vars "i"))) = if σ.vars "i" < nV n then 1 else 0 := by
      split_ifs <;> omega
    rw [f1, f2]
    by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2 <;>
      by_cases h2 : σ.vars "i" < nV n <;>
      simp only [h1, h2, if_true, if_false, one_mul, mul_one, zero_mul, mul_zero, and_self, and_true,
        true_and, and_false, false_and]

/-- The static context of the pass of the sums of the extras. -/
def C4 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v))

theorem C4.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hw : "wv" ∉ c.warrs) : Stable c (C4 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (stable_arr "wv" (fun l => l = arrOf (nN n) (wvF n cnt bb (certVec n v))) hw))

/-- **One turn of the pass of the sums of the extras.** -/
theorem esBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C4 n cnt bb v σ)
    (hik : σ.vars "i" = k)
    (hes : σ.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t k)) :
    ∃ σ', Run B esBody σ σ' (30 + 50 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t (k + 1)) := by
  obtain ⟨hCE, hkd, hwv⟩ := hC
  have hBN := hb.nN_lt
  obtain ⟨σ1, r1, e1⟩ := tAssign_vals hb v hv σ ⟨hCE, by omega⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = k / nZ n * (if k < nV n then 1 else 0) := ⟨_, rfl⟩
  have ht'T : t' < nT n := by
    rw [ht']
    by_cases h : k < nV n
    · rw [if_pos h, mul_one]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h
    · rw [if_neg h, mul_zero]; exact nT_pos n
  have hσ1t : σ1.vars "t" = t' := by rw [e1, ht']; simp only [Env.setVar, if_true, hik]
  have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
  have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
  have hkd1 : σ1.arrs "kd" = σ.arrs "kd" := by rw [e1]; rfl
  have hwv1 : σ1.arrs "wv" = σ.arrs "wv" := by rw [e1]; rfl
  have hes1 : σ1.arrs "es" = σ.arrs "es" := by rw [e1]; rfl
  have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd1, hkd, hi1]; exact getD_arrOf_lt hk
  have hwvk : (σ1.arrs "wv").getD (σ1.vars "i") 0 = wvF n cnt bb (certVec n v) k := by
    rw [hwv1, hwv, hi1]; exact getD_arrOf_lt hk
  have hesk : (σ1.arrs "es").getD (σ1.vars "t") 0 = esP n cnt bb (certVec n v) t' k := by
    rw [hes1, hes, hσ1t]; exact getD_arrOf_lt ht'T
  have hle := esP_le hb v hv t' k
  have hkN : k * Pbd n vb ≤ nN n * Pbd n vb := Nat.mul_le_mul_right _ hk.le
  obtain ⟨σ2, r2, e2⟩ := esStore_vals hb v σ1
    ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _,
      by rw [hwvk]; exact wvF_le hb v hv k, by rw [hesk]; omega⟩
  obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by
    show σ2.vars "i" + 1 < B
    rw [e2]; simp [Env.setArr, hi1]; omega)
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
  · rw [e3, e2]; simp [Env.setVar, Env.setArr, hi1]
  · rw [e3]
    show σ2.arrs "es" = _
    rw [e2]
    simp only [Env.setArr, if_true]
    rw [hesk, hkdk, hwvk, hes1, hes, hσ1t, hi1, set_arrOf]
    refine arrOf_congr fun t _ => ?_
    rw [esP_step]
    by_cases htt : t = t'
    · subst htt
      rw [if_pos rfl]
      congr 1
      refine if_congr ?_ rfl rfl
      rw [show (kindOf n (dd n v) k = 2) ↔ isExtra n (certVec n v).d k from kindOf_eq_two]
      constructor
      · rintro ⟨he, hV⟩
        refine ⟨he, hV, ?_⟩
        rw [ht', if_pos hV, mul_one]
      · rintro ⟨he, hV, -⟩
        exact ⟨he, hV⟩
    · rw [if_neg htt]
      have : ¬ (isExtra n (certVec n v).d k ∧ k < nV n ∧ k / nZ n = t) := by
        rintro ⟨-, hV, ht⟩
        apply htt
        rw [ht', if_pos hV, mul_one, ht]
      rw [if_neg this, add_zero]

/-- **The pass of the sums of the extras.** -/
theorem esCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C4 n cnt bb v σ ∧ σ.arrs "es" = arrOf (nT n) (fun _ => 0))
      esCom (fun _ σ' => C4 n cnt bb v σ' ∧ σ'.arrs "es" = arrOf (nT n) (esF n cnt bb (certVec n v)))
      ((30 + 50 + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 50 + 4) esBody (C4 n cnt bb v)
    (fun k σ => σ.arrs "es" = arrOf (nT n) (fun t => esP n cnt bb (certVec n v) t k))
    (C4.stable (by decide) (by decide) (by decide) (by decide) (by decide)) hb.nN_lt
    (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, hes⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2⟩, ?_⟩
      simpa [esP] using hes
    · rintro σ σ' - ⟨hC, hes, -⟩
      exact ⟨hC, hes⟩
  · intro k hk σ ⟨hC, hik, hes⟩
    obtain ⟨σ', hr, h1, h2⟩ := esBody_step hb v hv k hk σ hC hik hes
    exact ⟨σ', hr, h1, h2⟩

end

end Lax117284Proofs.Machine.Ilp

end

/-! ### `Lax117284Proofs.Machine.IlpXv` -/

section
/-!
The candidate solution.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem xvStore_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ) :
    Spec B (fun σ => CE n cnt bb v σ ∧ σ.vars "i" < nN n ∧ σ.vars "t" < nT n ∧
        (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 ∧ (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n ∧
        (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb ∧
        (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb ∧
        (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n ∧
        (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb)
      (.store "xv" (V "i")
        (.add
          (.add (.mul (eqF (.get "kd" (V "i")) (lit 3)) (.get "dg" (V "i")))
            (.mul (eqF (.get "kd" (V "i")) (lit 2)) (.get "wv" (V "i"))))
          (.mul (eqF (.get "kd" (V "i")) (lit 1))
            (.sub (.sub (.get "z" (.add (V "rb") (V "t"))) (.get "sg" (V "t")))
              (.get "es" (V "t"))))))
      (fun σ σ' => σ' = σ.setArr "xv" (σ.vars "i")
        ((if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then (σ.arrs "dg").getD (σ.vars "i") 0 else 0) +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then (σ.arrs "wv").getD (σ.vars "i") 0 else 0) +
          (if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then
            (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 -
              (σ.arrs "es").getD (σ.vars "t") 0 else 0))) 80 := by
  run_vcg
  all_goals
    have hC : CE n cnt bb v σ := ‹CE n cnt bb v σ›
    have hi : σ.vars "i" < nN n := ‹σ.vars "i" < nN n›
    have ht : σ.vars "t" < nT n := ‹σ.vars "t" < nT n›
    have hkd3 : (σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3 := ‹(σ.arrs "kd").getD (σ.vars "i") 0 ≤ 3›
    have hdgv : (σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n := ‹(σ.arrs "dg").getD (σ.vars "i") 0 ≤ Kn n›
    have hwv : (σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb := ‹(σ.arrs "wv").getD (σ.vars "i") 0 ≤ Pbd n vb›
    have hzv : (σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb :=
      ‹(σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 ≤ vb›
    have hsgv : (σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n := ‹(σ.arrs "sg").getD (σ.vars "t") 0 ≤ nN n * Kn n›
    have hes : (σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb :=
      ‹(σ.arrs "es").getD (σ.vars "t") 0 ≤ nN n * Pbd n vb›
    have hrb := hC.1.hrb
    have hlz : (σ.arrs "z").length = zLen n := by rw [hC.1.hz, ilpWord_length]
    have hlsg : (σ.arrs "sg").length = nT n := hC.1.lsg
    have hles : (σ.arrs "es").length = nT n := hC.1.les
    have hlk : (σ.arrs "kd").length = nN n := hC.1.lkd
    have hlw : (σ.arrs "wv").length = nN n := hC.1.lwv
    have hldg : (σ.arrs "dg").length = Dn n := hC.1.ldg
    have hDN : nN n ≤ Dn n := by unfold Dn; omega
    have hlx : (σ.arrs "xv").length = nN n := hC.1.lxv
    have hBN := hb.nN_lt
    have hBT := hb.nT_lt
    have hBz := hb.zLen_lt
    have hB5 := hb.five_lt_B
    have hBrb := hb.rb_lt
    have hBE := hb.Ebd_lt
    have hBK := hb.NK_lt
    have hBX := hb.XB_lt
    have hBP := hb.Pbd_lt
    have hidx : σ.vars "rb" + σ.vars "t" < zLen n := by
      have : nT n ≤ nM n := by unfold nM; omega
      unfold zLen; omega
    have g3 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have g2 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have g1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0))) ≤ 1 := by omega
    have p3 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "dg").getD (σ.vars "i") 0) g3
    have p2 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "wv").getD (σ.vars "i") 0) g2
    have p1 := mul_le_of_le_one_left'
      (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0)))
      ((σ.arrs "z").getD (σ.vars "rb" + σ.vars "t") 0 - (σ.arrs "sg").getD (σ.vars "t") 0 -
        (σ.arrs "es").getD (σ.vars "t") 0) g1
    clear_runs
  all_goals (first | omega | skip)
  all_goals
    congr 1
    have f3 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 3 + (3 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 3 then 1 else 0 := by split_ifs <;> omega
    have f2 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 2 + (2 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 2 then 1 else 0 := by split_ifs <;> omega
    have f1 : (1 - ((σ.arrs "kd").getD (σ.vars "i") 0 - 1 + (1 - (σ.arrs "kd").getD (σ.vars "i") 0))) =
        if (σ.arrs "kd").getD (σ.vars "i") 0 = 1 then 1 else 0 := by split_ifs <;> omega
    rw [f3, f2, f1]
    by_cases h3 : (σ.arrs "kd").getD (σ.vars "i") 0 = 3
    · have h2 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 2 := by omega
      have h1 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 1 := by omega
      simp [h3, h2, h1]
    · by_cases h2 : (σ.arrs "kd").getD (σ.vars "i") 0 = 2
      · have h1 : ¬ (σ.arrs "kd").getD (σ.vars "i") 0 = 1 := by omega
        simp [h3, h2, h1]
      · by_cases h1 : (σ.arrs "kd").getD (σ.vars "i") 0 = 1
        · simp [h3, h2, h1]
        · simp [h3, h2, h1]

/-- The static context of the pass of the candidate. -/
def C5 (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (v : ℕ → ℕ) (σ : Env) : Prop :=
  CE n cnt bb v σ ∧ σ.arrs "kd" = arrOf (nN n) (kindOf n (dd n v)) ∧
    σ.arrs "wv" = arrOf (nN n) (wvF n cnt bb (certVec n v)) ∧
    σ.arrs "sg" = arrOf (nT n) (sigma n (dd n v)) ∧
    σ.arrs "es" = arrOf (nT n) (esF n cnt bb (certVec n v))

theorem C5.stable {c : Com} {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {v : ℕ → ℕ}
    (hv : ∀ y ∈ ctxVars, y ∉ c.wvars) (hz : "z" ∉ c.warrs) (hd : "dg" ∉ c.warrs)
    (hk : "kd" ∉ c.warrs) (hw : "wv" ∉ c.warrs) (hs : "sg" ∉ c.warrs) (he : "es" ∉ c.warrs) :
    Stable c (C5 n cnt bb v) :=
  Stable.and (CE.stable hv hz hd)
    (Stable.and (stable_arr "kd" (fun l => l = arrOf (nN n) (kindOf n (dd n v))) hk)
      (Stable.and (stable_arr "wv" (fun l => l = arrOf (nN n) (wvF n cnt bb (certVec n v))) hw)
        (Stable.and (stable_arr "sg" (fun l => l = arrOf (nT n) (sigma n (dd n v))) hs)
          (stable_arr "es" (fun l => l = arrOf (nT n) (esF n cnt bb (certVec n v))) he))))

/-- **One turn of the pass of the candidate.** -/
theorem xvBody_step {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) (k : ℕ) (hk : k < nN n) (σ : Env) (hC : C5 n cnt bb v σ)
    (hik : σ.vars "i" = k) :
    ∃ σ', Run B xvBody σ σ' (30 + 80 + 4) ∧ σ'.vars "i" = k + 1 ∧
      σ'.arrs "xv" = (σ.arrs "xv").set k (xF n cnt bb (certVec n v) k) := by
  obtain ⟨hCE, hkd, hwv, hsg, hes⟩ := hC
  have hBN := hb.nN_lt
  obtain ⟨σ1, r1, e1⟩ := tAssign_vals hb v hv σ ⟨hCE, by omega⟩
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t' = k / nZ n * (if k < nV n then 1 else 0) := ⟨_, rfl⟩
  have ht'T : t' < nT n := by
    rw [ht']
    by_cases h : k < nV n
    · rw [if_pos h, mul_one]; apply Nat.div_lt_of_lt_mul; rw [mul_comm]; exact h
    · rw [if_neg h, mul_zero]; exact nT_pos n
  have hσ1t : σ1.vars "t" = t' := by rw [e1, ht']; simp only [Env.setVar, if_true, hik]
  have hCE1 : CE n cnt bb v σ1 := by rw [e1]; exact hCE.setVar (by decide) _
  have hi1 : σ1.vars "i" = k := by rw [e1]; simpa using hik
  have hkd1 : σ1.arrs "kd" = σ.arrs "kd" := by rw [e1]; rfl
  have hwv1 : σ1.arrs "wv" = σ.arrs "wv" := by rw [e1]; rfl
  have hsg1 : σ1.arrs "sg" = σ.arrs "sg" := by rw [e1]; rfl
  have hes1 : σ1.arrs "es" = σ.arrs "es" := by rw [e1]; rfl
  have hxv1 : σ1.arrs "xv" = σ.arrs "xv" := by rw [e1]; rfl
  have hkdk : (σ1.arrs "kd").getD (σ1.vars "i") 0 = kindOf n (dd n v) k := by
    rw [hkd1, hkd, hi1]; exact getD_arrOf_lt hk
  have hDk : k < Dn n := lt_of_lt_of_le hk (by unfold Dn; omega)
  have hdgk : (σ1.arrs "dg").getD (σ1.vars "i") 0 = v k := by
    rw [hCE1.2, hi1, getD_arrOf_lt hDk]
  have hwvk : (σ1.arrs "wv").getD (σ1.vars "i") 0 = wvF n cnt bb (certVec n v) k := by
    rw [hwv1, hwv, hi1]; exact getD_arrOf_lt hk
  have hzt : (σ1.arrs "z").getD (σ1.vars "rb" + σ1.vars "t") 0 = cnt t' := by
    rw [hCE1.1.hz, hCE1.1.hrb, hσ1t, ilpWord_rhs n cnt bb (by unfold nM; omega)]
    unfold rhs; rw [if_pos ht'T]
  have hsgt : (σ1.arrs "sg").getD (σ1.vars "t") 0 = sigma n (dd n v) t' := by
    rw [hsg1, hsg, hσ1t]; exact getD_arrOf_lt ht'T
  have hest : (σ1.arrs "es").getD (σ1.vars "t") 0 = esF n cnt bb (certVec n v) t' := by
    rw [hes1, hes, hσ1t]; exact getD_arrOf_lt ht'T
  have hesle : esF n cnt bb (certVec n v) t' ≤ nN n * Pbd n vb := by
    rw [esF_eq_esP]; exact esP_le hb v hv t' (nN n)
  have hvk : v k ≤ Kn n := hv k hDk
  obtain ⟨σ2, r2, e2⟩ := xvStore_vals hb v σ1
    ⟨hCE1, by omega, by omega, by rw [hkdk]; exact kindOf_le_three _ _ _, by rw [hdgk]; exact hvk,
      by rw [hwvk]; exact wvF_le hb v hv k, by rw [hzt]; exact hb.hcnt _ ht'T,
      by rw [hsgt]; exact sigma_le' _ _ _, by rw [hest]; exact hesle⟩
  obtain ⟨σ3, r3, e3⟩ := bump_spec (B := B) "i" hb.one_lt_B σ2 (by
    show σ2.vars "i" + 1 < B
    rw [e2]; simp [Env.setArr, hi1]; omega)
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_, ?_⟩
  · rw [e3, e2]; simp [Env.setVar, Env.setArr, hi1]
  · rw [e3]
    show σ2.arrs "xv" = _
    rw [e2]
    simp only [Env.setArr, if_true]
    rw [hkdk, hdgk, hwvk, hzt, hsgt, hest, hxv1, hi1]
    congr 1
    unfold xF
    have hkc := kindOf_le_three n (dd n v) k
    by_cases h3 : kindOf n (dd n v) k = 3
    · rw [if_pos h3]; simp [h3, dd_lt hk, dd]
    · by_cases h2 : kindOf n (dd n v) k = 2
      · rw [if_neg h3, if_pos h2]; simp [h3, h2]
      · by_cases h1 : kindOf n (dd n v) k = 1
        · rw [if_neg h3, if_neg h2, if_pos h1]
          have hbase := kindOf_eq_one.mp h1
          obtain ⟨e1', e2'⟩ := isBase_tyIdx hbase
          have hV := isBase_lt_V hbase
          have ht'' : t' = k / nZ n := by rw [ht', if_pos hV, mul_one]
          rw [e1', ← ht'']
          simp [h1, cp]
        · have h0 : kindOf n (dd n v) k = 0 := by omega
          rw [if_neg h3, if_neg h2, if_neg h1]
          simp [h3, h2, h1]

/-- **The pass of the candidate.** -/
theorem xvCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) (v : ℕ → ℕ)
    (hv : ∀ q < Dn n, v q ≤ Kn n) :
    Spec B (fun σ => C5 n cnt bb v σ ∧ ∃ f, σ.arrs "xv" = arrOf (nN n) f)
      xvCom (fun _ σ' => C5 n cnt bb v σ' ∧ σ'.arrs "xv" = arrOf (nN n) (xF n cnt bb (certVec n v)))
      ((30 + 80 + 4 + 4) * nN n + 6) := by
  have hs := scan_spec (B := B) "i" "N" (nN n) (30 + 80 + 4) xvBody (C5 n cnt bb v)
    (fun k σ => ∃ f, σ.arrs "xv" = arrOf (nN n) f ∧ ∀ c < k, f c = xF n cnt bb (certVec n v) c)
    (C5.stable (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.nN_lt (fun σ h => h.1.1.hN) ?_
  · refine (Spec.pre hs ?_).post ?_
    · rintro σ ⟨hC, f, hf⟩
      refine ⟨⟨hC.1.setVar (by decide) _, by simpa using hC.2.1, by simpa using hC.2.2.1,
        by simpa using hC.2.2.2.1, by simpa using hC.2.2.2.2⟩,
        ⟨f, by simpa using hf, fun c hc => absurd hc (by omega)⟩⟩
    · rintro σ σ' - ⟨hC, ⟨f, hf, hfk⟩, -⟩
      exact ⟨hC, by rw [hf]; exact arrOf_congr hfk⟩
  · intro k hk σ ⟨hC, hik, f, hf, hfk⟩
    obtain ⟨σ', hr, h1, h2⟩ := xvBody_step hb v hv k hk σ hC hik
    refine ⟨σ', hr, h1, ⟨fun j => if j = k then xF n cnt bb (certVec n v) k else f j, ?_, ?_⟩⟩
    · rw [h2, hf, set_arrOf]
    · intro c hc
      by_cases h : c = k
      · simp [h]
      · simp only [h, if_false]; exact hfk c (by omega)

end

end Lax117284Proofs.Machine.Ilp

end
