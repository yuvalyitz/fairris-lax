import Mathlib.Tactic
import Lax117284Proofs.Machine.TwPrep

/-!
The arithmetic of the guard: when the guard of the main program holds for a width `w`, the tables
of the dynamic program, the running time of the decomposition step and the word length it needs are
all at most polynomial in the length `L` of the word.
-/

namespace Lax117284Proofs.Machine.TwNum

open TwPrep

/-- **What the guard says**: `L` has binary length `lg + 1`, and the width `w` is admitted for `m`
days at that length. -/
structure Gd (ca cc L lg m w : ℕ) : Prop where
  hca : 1 ≤ ca
  hcc : ca + 1 ≤ cc
  hL : 3 ≤ L
  hlg1 : 2 ^ lg ≤ L
  hlg2 : L < 2 ^ (lg + 1)
  hw : geE cc m w ≤ lg

variable {ca cc L lg m w : ℕ}

theorem Gd.cw (h : Gd ca cc L lg m w) : cc * ((w + 1) * (w + 1) * (w + 1)) ≤ lg := by
  have := h.hw; unfold geE at this; omega

theorem Gd.mw (h : Gd ca cc L lg m w) : m * (w + 1) ≤ lg := by
  have := h.hw; unfold geE at this; omega

theorem Gd.wlg (h : Gd ca cc L lg m w) : w + 1 ≤ lg := by
  have h1 := h.cw
  have h2 : w + 1 ≤ (w + 1) * (w + 1) * (w + 1) := by
    calc w + 1 = (w + 1) * 1 * 1 := by ring
      _ ≤ (w + 1) * (w + 1) * (w + 1) := by gcongr <;> omega
  have h3 : (w + 1) * (w + 1) * (w + 1) ≤ cc * ((w + 1) * (w + 1) * (w + 1)) :=
    Nat.le_mul_of_pos_left _ (by have := h.hcc; omega)
  omega

theorem Gd.mlg (h : Gd ca cc L lg m w) : m ≤ lg := by
  have := h.mw
  have : m ≤ m * (w + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem Gd.lgL (h : Gd ca cc L lg m w) : lg < L :=
  lt_of_lt_of_le (Nat.lt_two_pow_self) h.hlg1

theorem Gd.pm (h : Gd ca cc L lg m w) : 2 ^ m ≤ L :=
  le_trans (Nat.pow_le_pow_right (by norm_num) h.mlg) h.hlg1

theorem Gd.tabs (h : Gd ca cc L lg m w) : (2 ^ m) ^ (w + 1) ≤ L := by
  rw [← pow_mul]
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h.mw) h.hlg1

theorem Gd.pw (h : Gd ca cc L lg m w) : 2 ^ (ca * w ^ 3) ≤ L := by
  have h1 : ca * w ^ 3 ≤ lg := by
    have := h.cw
    have e1 : w ^ 3 ≤ (w + 1) * (w + 1) * (w + 1) := by
      calc w ^ 3 = w * w * w := by ring
        _ ≤ (w + 1) * (w + 1) * (w + 1) := by gcongr <;> omega
    have e2 : ca * w ^ 3 ≤ cc * ((w + 1) * (w + 1) * (w + 1)) :=
      Nat.mul_le_mul (by have := h.hcc; omega) e1
    omega
  exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) h.hlg1

/-- **The word length of the decomposition step is enough**: the hypothesis of the cited theorem,
for a word of `n * n + 2` entries each at most `L`, on `Wp = (2 * cc + 1) * lg + 4 * cc + plit`
bits. -/
theorem Gd.ax (h : Gd ca cc L lg m w) {n v plit : ℕ} (hn : n ≤ L) (hv : v ≤ L) (hpl : ca ≤ plit) :
    ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca ≤
      2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) := by
  have hL := h.hL
  have hcc := h.hcc
  have hca := h.hca
  have h1 : n * n + 2 + v + 1 ≤ 2 * (L * L) := by
    have : n * n ≤ L * L := Nat.mul_le_mul hn hn
    nlinarith
  have h2 : (n * n + 2 + v + 1) ^ ca ≤ 2 ^ ca * L ^ (2 * ca) := by
    calc (n * n + 2 + v + 1) ^ ca ≤ (2 * (L * L)) ^ ca := Nat.pow_le_pow_left h1 _
      _ = 2 ^ ca * L ^ (2 * ca) := by rw [mul_pow, ← pow_two, ← pow_mul, mul_comm 2 ca]
  have h3 : ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca ≤ ca * L * (2 ^ ca * L ^ (2 * ca)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h.pw) h2
  have h4 : ca * L * (2 ^ ca * L ^ (2 * ca)) = ca * 2 ^ ca * L ^ (2 * ca + 1) := by ring
  have h5 : L ^ (2 * ca + 1) ≤ L ^ (2 * cc + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : L ^ (2 * cc + 1) ≤ (2 * 2 ^ lg) ^ (2 * cc + 1) :=
    Nat.pow_le_pow_left (by have := h.hlg2; rw [pow_succ] at this; omega) _
  have h7 : (2 * 2 ^ lg) ^ (2 * cc + 1) = 2 ^ (2 * cc + 1) * 2 ^ ((2 * cc + 1) * lg) := by
    rw [mul_pow, ← pow_mul, mul_comm lg]
  have h8 : ca ≤ 2 ^ plit := le_trans hpl (le_of_lt Nat.lt_two_pow_self)
  have h9 : 2 ^ ca * 2 ^ (2 * cc + 1) ≤ 2 ^ (4 * cc) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hE : 2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) =
      2 ^ ((2 * cc + 1) * lg) * 2 ^ (4 * cc) * 2 ^ plit := by
    rw [pow_add, pow_add]
  rw [hE]
  calc ca * 2 ^ (ca * w ^ 3) * (n * n + 2 + v + 1) ^ ca
      ≤ ca * 2 ^ ca * L ^ (2 * ca + 1) := by rw [← h4]; exact h3
    _ ≤ ca * 2 ^ ca * (2 ^ (2 * cc + 1) * 2 ^ ((2 * cc + 1) * lg)) := by
        rw [← h7]; exact Nat.mul_le_mul_left _ (h5.trans h6)
    _ = ca * (2 ^ ca * 2 ^ (2 * cc + 1)) * 2 ^ ((2 * cc + 1) * lg) := by ring
    _ ≤ 2 ^ plit * 2 ^ (4 * cc) * 2 ^ ((2 * cc + 1) * lg) := by
        gcongr
    _ = 2 ^ ((2 * cc + 1) * lg) * 2 ^ (4 * cc) * 2 ^ plit := by ring

end Lax117284Proofs.Machine.TwNum
