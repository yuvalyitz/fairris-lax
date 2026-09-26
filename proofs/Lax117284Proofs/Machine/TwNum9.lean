import Lax117284Proofs.Machine.TwNum8

/-!
The enumeration is only paid for on a word whose length is bounded by a function of the number of
days and the treewidth.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph

/-- The largest length of a word on which the enumeration is run, for the parameter `p`. -/
def Fm (cc p : ℕ) : ℕ := 2 ^ TwPrep.geE cc p p

/-- The function of the parameter that bounds the cost of the enumeration. -/
def HB (cc p : ℕ) : ℕ := 5000 * 2 ^ Fm cc p * (2 * Fm cc p + 2) ^ 2 + 3

theorem geE_mono2 (cc : ℕ) {m m' w w' : ℕ} (hm : m ≤ m') (hw : w ≤ w') :
    TwPrep.geE cc m w ≤ TwPrep.geE cc m' w' := by
  unfold TwPrep.geE; gcongr

theorem brute_le_HB {cc p L m n : ℕ} (hL : L < Fm cc p) (hl : L = 3 + 2 * (m * n)) (hm : 0 < m) :
    Lax117284Proofs.Machine.ClBrute.bruteCost m n + 3 ≤ HB cc p := by
  have h1 := Lax117284Proofs.Machine.ClBrute.bruteCost_le m n
  have hn : n ≤ m * n := Nat.le_mul_of_pos_left _ hm
  have h2 : m * n + n + 2 ≤ 2 * Fm cc p + 2 := by omega
  have h3 : 2 ^ (m * n) ≤ 2 ^ Fm cc p := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2 ≤ 5000 * 2 ^ Fm cc p * (2 * Fm cc p + 2) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) (Nat.pow_le_pow_left h2 _)
  unfold HB
  omega

variable {cc : ℕ} {x : List ℕ}

/-- **The length of a word is below `Fm`** when the guard admits no width beyond `w'`. -/
theorem len_lt_Fm (hcc : 1 ≤ cc) (hx : Dm x) {p w' : ℕ} (hm : mx x ≤ p) (hw' : wcx cc x ≤ w')
    (hwp : w' ≤ p) : x.length < Fm cc p := by
  have hL0 := hx.three
  have h1 := (TwPrep.wcnt_spec hcc (mx x) (lgx x)).2.2
  have h2 : lgx x + 1 ≤ TwPrep.geE cc p p :=
    le_trans h1 (geE_mono2 cc hm (le_trans hw' hwp))
  have h3 : x.length < 2 ^ (lgx x + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  exact lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) h2)

/-- **The enumeration costs at most a function of the parameter.** -/
theorem KB_le (hcc : 1 ≤ cc) (hx : Dm x) :
    KB cc x ≤ HB cc ((Ix x).days + treewidth (Ix x)) := by
  classical
  obtain ⟨I, k, hdec, hl, hn, hm⟩ := hx.len
  have hI : Ix x = I := Ix_eq hdec
  have hl' : x.length = 3 + 2 * (mx x * nx x) := by rw [hl, hm, hn]
  rw [hI]
  unfold KB
  rw [hI]
  by_cases hg : gdx cc x
  · simp only [if_pos hg]
    by_cases ht : Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)
    · simp only [if_pos ht]; exact Nat.zero_le _
    · simp only [if_neg ht]
      have hlt : wx cc x < treewidth I := Lax117284Proofs.Machine.TwTW.lt_treewidth_of_not ht
      have hwc : wcx cc x ≤ treewidth I := by have := hg.1; unfold wx at hlt; omega
      exact brute_le_HB (len_lt_Fm hcc hx (p := I.days + treewidth I) (w' := treewidth I)
        (by omega) hwc (by omega)) hl' hg.2
  · simp only [if_neg hg]
    by_cases hm0 : 0 < mx x
    · simp only [if_pos hm0]
      have hwc : wcx cc x = 0 := by
        by_contra h; exact hg ⟨by omega, hm0⟩
      exact brute_le_HB (len_lt_Fm hcc hx (p := I.days + treewidth I) (w' := 0) (by omega)
        (by omega) (by omega)) hl' hm0
    · simp only [if_neg hm0]; exact Nat.zero_le _

end Lax117284Proofs.Machine.TwNum
