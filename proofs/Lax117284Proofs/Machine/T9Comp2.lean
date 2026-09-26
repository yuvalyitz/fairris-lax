import Lax117284Proofs.Machine.T9Comp1

/-!
The numbers of a validation clause, computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Comp2

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1

variable {B : ℕ}

/-- The computation of the numbers of a validation clause. -/
def comp2 : Com :=
  .seq (.assign "cj" (.bin .div (V "i") (V "mm")))
  (.seq (.assign "tt" (mul (V "cj") (V "mm")))
  (.seq (.assign "r2" (sub (V "i") (V "tt")))
  (.seq (.assign "i1" (.bin .div (V "r2") (V "m")))
  (.seq (.assign "tt" (mul (V "i1") (V "m")))
  (.seq (.assign "i2" (sub (V "r2") (V "tt")))
  (.seq (.assign "tt" (mul (V "i1") (V "n")))
  (.seq (.assign "x1" (add (V "tt") (V "cj")))
  (.seq (.assign "tt" (mul (V "i2") (V "n")))
    (.assign "x2" (add (V "tt") (V "cj")))))))))))

/-- The scalars `comp2` assigns. -/
def A2 : List String := ["cj", "tt", "r2", "i1", "i2", "x1", "x2"]

set_option maxHeartbeats 8000000 in
/-- **The numbers of a validation clause.** -/
theorem comp2_run (n m c : ℕ) (σ : Env)
    (hi : σ.vars "i" = c) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hmm : σ.vars "mm" = m * m) (hc : c < n * m * m) (hcB : c + 8 < B) (hmB : m + 8 < B)
    (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B) :
    ∃ σ', Run B comp2 σ σ' 200 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.vars "i1" = c % (m * m) / m ∧ σ'.vars "i2" = c % (m * m) % m ∧
      σ'.vars "x1" = c % (m * m) / m * n + c / (m * m) ∧
      σ'.vars "x2" = c % (m * m) % m * n + c / (m * m) ∧
      ∀ y, y ∉ A2 → σ'.vars y = σ.vars y := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hmm0 : 0 < m * m := Nat.mul_pos hm0 hm0
  obtain ⟨a, ha⟩ : ∃ a, a = c / (m * m) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = c % (m * m) := ⟨_, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ j, j = r / m := ⟨_, rfl⟩
  obtain ⟨j2, hj2⟩ : ∃ j, j = r % m := ⟨_, rfl⟩
  have hdm1 : m * m * a + r = c := by rw [ha, hr]; exact Nat.div_add_mod c (m * m)
  have hdm2 : m * j1 + j2 = r := by rw [hj1, hj2]; exact Nat.div_add_mod r m
  have han : a < n := by
    rw [ha, Nat.div_lt_iff_lt_mul hmm0]
    have : n * m * m = n * (m * m) := Nat.mul_assoc _ _ _
    omega
  have hrl : r < m * m := by rw [hr]; exact Nat.mod_lt _ hmm0
  have hj1l : j1 < m := by rw [hj1, Nat.div_lt_iff_lt_mul hm0]; exact hrl
  have hj2l : j2 < m := by rw [hj2]; exact Nat.mod_lt _ hm0
  have hx1 : j1 * n + a < m * n := cell_lt hj1l han
  have hx2 : j2 * n + a < m * n := cell_lt hj2l han
  have e1 : a * (m * m) = m * m * a := Nat.mul_comm _ _
  have e2 : j1 * m = m * j1 := Nat.mul_comm _ _
  have hale : a ≤ c := by rw [ha]; exact Nat.div_le_self _ _
  have hrle : r ≤ c := by rw [hr]; exact Nat.mod_le _ _
  have hj1le : j1 ≤ r := by rw [hj1]; exact Nat.div_le_self _ _
  have hj2le : j2 ≤ r := by rw [hj2]; exact Nat.mod_le _ _
  have hnB : n + 8 < B := by
    have : n ≤ m * n := Nat.le_mul_of_pos_left n hm0
    omega
  have s1 : Run B (.assign "cj" (.bin .div (V "i") (V "mm"))) σ (σ.setVar "cj" a) 4 := by
    have := asg_bin (B := B) .div "i" "mm" "cj" σ c (m * m) hi hmm (by
      show c / (m * m) < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div] at this; rw [← ha] at this; exact this
  set σ1 := σ.setVar "cj" a with hσ1
  have s1i : σ1.vars "i" = c := by simp [hσ1, Env.setVar, hi]
  have s1mm : σ1.vars "mm" = m * m := by simp [hσ1, Env.setVar, hmm]
  have s1m : σ1.vars "m" = m := by simp [hσ1, Env.setVar, hm]
  have s1n : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have s1cj : σ1.vars "cj" = a := by simp [hσ1, Env.setVar]
  have s2 : Run B (.assign "tt" (mul (V "cj") (V "mm"))) σ1 (σ1.setVar "tt" (m * m * a)) 4 := by
    have := asg_bin (B := B) .mul "cj" "mm" "tt" σ1 a (m * m) s1cj s1mm (by
      show a * (m * m) < B; omega) (by omega) (by omega)
    simp only [Bop.apply_mul] at this; rw [e1] at this; exact this
  set σ2 := σ1.setVar "tt" (m * m * a) with hσ2
  have s2i : σ2.vars "i" = c := by simp [hσ2, Env.setVar, s1i]
  have s2tt : σ2.vars "tt" = m * m * a := by simp [hσ2, Env.setVar]
  have s2m : σ2.vars "m" = m := by simp [hσ2, Env.setVar, s1m]
  have s2n : σ2.vars "n" = n := by simp [hσ2, Env.setVar, s1n]
  have s2cj : σ2.vars "cj" = a := by simp [hσ2, Env.setVar, s1cj]
  have s3 : Run B (.assign "r2" (sub (V "i") (V "tt"))) σ2 (σ2.setVar "r2" r) 4 := by
    have := asg_bin (B := B) .sub "i" "tt" "r2" σ2 c (m * m * a) s2i s2tt (by
      show c - m * m * a < B; omega) (by omega) (by omega)
    have e : c - m * m * a = r := by omega
    simp only [Bop.apply_sub] at this; rw [e] at this; exact this
  set σ3 := σ2.setVar "r2" r with hσ3
  have s3r2 : σ3.vars "r2" = r := by simp [hσ3, Env.setVar]
  have s3m : σ3.vars "m" = m := by simp [hσ3, Env.setVar, s2m]
  have s3n : σ3.vars "n" = n := by simp [hσ3, Env.setVar, s2n]
  have s3cj : σ3.vars "cj" = a := by simp [hσ3, Env.setVar, s2cj]
  have s4 : Run B (.assign "i1" (.bin .div (V "r2") (V "m"))) σ3 (σ3.setVar "i1" j1) 4 := by
    have := asg_bin (B := B) .div "r2" "m" "i1" σ3 r m s3r2 s3m (by
      show r / m < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div] at this; rw [← hj1] at this; exact this
  set σ4 := σ3.setVar "i1" j1 with hσ4
  have s4i1 : σ4.vars "i1" = j1 := by simp [hσ4, Env.setVar]
  have s4m : σ4.vars "m" = m := by simp [hσ4, Env.setVar, s3m]
  have s4n : σ4.vars "n" = n := by simp [hσ4, Env.setVar, s3n]
  have s4r2 : σ4.vars "r2" = r := by simp [hσ4, Env.setVar, s3r2]
  have s4cj : σ4.vars "cj" = a := by simp [hσ4, Env.setVar, s3cj]
  have s5 : Run B (.assign "tt" (mul (V "i1") (V "m"))) σ4 (σ4.setVar "tt" (m * j1)) 4 := by
    have := asg_bin (B := B) .mul "i1" "m" "tt" σ4 j1 m s4i1 s4m (by
      show j1 * m < B; omega) (by omega) (by omega)
    simp only [Bop.apply_mul] at this; rw [e2] at this; exact this
  set σ5 := σ4.setVar "tt" (m * j1) with hσ5
  have s5tt : σ5.vars "tt" = m * j1 := by simp [hσ5, Env.setVar]
  have s5r2 : σ5.vars "r2" = r := by simp [hσ5, Env.setVar, s4r2]
  have s5i1 : σ5.vars "i1" = j1 := by simp [hσ5, Env.setVar, s4i1]
  have s5n : σ5.vars "n" = n := by simp [hσ5, Env.setVar, s4n]
  have s5cj : σ5.vars "cj" = a := by simp [hσ5, Env.setVar, s4cj]
  have s6 : Run B (.assign "i2" (sub (V "r2") (V "tt"))) σ5 (σ5.setVar "i2" j2) 4 := by
    have := asg_bin (B := B) .sub "r2" "tt" "i2" σ5 r (m * j1) s5r2 s5tt (by
      show r - m * j1 < B; omega) (by omega) (by omega)
    have e : r - m * j1 = j2 := by omega
    simp only [Bop.apply_sub] at this; rw [e] at this; exact this
  set σ6 := σ5.setVar "i2" j2 with hσ6
  have s6i2 : σ6.vars "i2" = j2 := by simp [hσ6, Env.setVar]
  have s6i1 : σ6.vars "i1" = j1 := by simp [hσ6, Env.setVar, s5i1]
  have s6n : σ6.vars "n" = n := by simp [hσ6, Env.setVar, s5n]
  have s6cj : σ6.vars "cj" = a := by simp [hσ6, Env.setVar, s5cj]
  have s7 : Run B (.assign "tt" (mul (V "i1") (V "n"))) σ6 (σ6.setVar "tt" (j1 * n)) 4 := by
    have := asg_bin (B := B) .mul "i1" "n" "tt" σ6 j1 n s6i1 s6n (by
      show j1 * n < B; omega) (by omega) (by omega)
    simp only [Bop.apply_mul] at this; exact this
  set σ7 := σ6.setVar "tt" (j1 * n) with hσ7
  have s7tt : σ7.vars "tt" = j1 * n := by simp [hσ7, Env.setVar]
  have s7cj : σ7.vars "cj" = a := by simp [hσ7, Env.setVar, s6cj]
  have s7i2 : σ7.vars "i2" = j2 := by simp [hσ7, Env.setVar, s6i2]
  have s7n : σ7.vars "n" = n := by simp [hσ7, Env.setVar, s6n]
  have s8 : Run B (.assign "x1" (add (V "tt") (V "cj"))) σ7 (σ7.setVar "x1" (j1 * n + a)) 4 :=
    asg_bin (B := B) .add "tt" "cj" "x1" σ7 (j1 * n) a s7tt s7cj (by
      show j1 * n + a < B; omega) (by omega) (by omega)
  set σ8 := σ7.setVar "x1" (j1 * n + a) with hσ8
  have s8x1 : σ8.vars "x1" = j1 * n + a := by simp [hσ8, Env.setVar]
  have s8cj : σ8.vars "cj" = a := by simp [hσ8, Env.setVar, s7cj]
  have s8i2 : σ8.vars "i2" = j2 := by simp [hσ8, Env.setVar, s7i2]
  have s8n : σ8.vars "n" = n := by simp [hσ8, Env.setVar, s7n]
  have s9 : Run B (.assign "tt" (mul (V "i2") (V "n"))) σ8 (σ8.setVar "tt" (j2 * n)) 4 := by
    have := asg_bin (B := B) .mul "i2" "n" "tt" σ8 j2 n s8i2 s8n (by
      show j2 * n < B; omega) (by omega) (by omega)
    simp only [Bop.apply_mul] at this; exact this
  set σ9 := σ8.setVar "tt" (j2 * n) with hσ9
  have s9tt : σ9.vars "tt" = j2 * n := by simp [hσ9, Env.setVar]
  have s9cj : σ9.vars "cj" = a := by simp [hσ9, Env.setVar, s8cj]
  have s10 : Run B (.assign "x2" (add (V "tt") (V "cj"))) σ9 (σ9.setVar "x2" (j2 * n + a)) 4 :=
    asg_bin (B := B) .add "tt" "cj" "x2" σ9 (j2 * n) a s9tt s9cj (by
      show j2 * n + a < B; omega) (by omega) (by omega)
  set σ10 := σ9.setVar "x2" (j2 * n + a) with hσ10
  have hfr : ∀ y, y ∉ A2 → σ10.vars y = σ.vars y := by
    intro y hy
    simp only [A2, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hy
    simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar,
      h1, h2, h3, h4, h5, h6, h7]
  refine ⟨σ10, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
    s10))))))))).mono (by omega), ?_⟩
  subst ha hj1 hj2 hr
  refine ⟨by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar],
    by simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar],
    ?_, ?_, ?_, ?_, hfr⟩ <;>
  simp [hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]

end Lax117284Proofs.Machine.T9Comp2
