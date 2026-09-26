import Lax117284Proofs.Machine.IlpVec

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

theorem coef_le_one'' (n r c : ℕ) : coef n r c ≤ 1 := coef_le_one n r c

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
