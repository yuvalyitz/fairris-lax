import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.T9Sem

/-!
The program that writes the clauses of Theorem 9: one loop over the conflict clauses and one over
the validation clauses, each clause computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Comp1

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime

variable {B : ℕ}

/-- The sign of a literal, as a bit. -/
def sb (b : Bool) : ℕ := if b then 1 else 0

/-- The bits of the word of clause `c`. -/
def clB (arr : List ℕ) (n m c : ℕ) : List ℕ :=
  bitsNat (clauseG arr n m c).1 ++ [sb (clauseG arr n m c).2.1] ++
    bitsNat (clauseG arr n m c).2.2.1 ++ [sb (clauseG arr n m c).2.2.2]

lemma natBits_app (a b : Word) : natBits (a ++ b) = natBits a ++ natBits b := by
  simp [natBits]

lemma natBits_clW (arr : List ℕ) (n m c : ℕ) : natBits (clW arr n m c) = clB arr n m c := by
  unfold clW clB
  simp only [natBits_app, natBits_encodeNat, sb]
  cases hh : (clauseG arr n m c).2.1 <;> cases hh2 : (clauseG arr n m c).2.2.2 <;>
    simp [natBits]

/-- Scratch scalars of a clause. -/
def S9 : List String :=
  SCR ++ ["ci", "cr", "j1", "j2", "tt", "x1", "x2", "pa", "da", "pb", "db", "cj", "r2", "i1", "i2"]

lemma nscr_of_s9 {y : String} (hy : y ∉ S9) : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
  simp only [S9, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  tauto)

/-- The computation of the numbers of a conflict clause. -/
def comp1 : Com :=
  .seq (.assign "ci" (.bin .div (V "i") (V "nn")))
  (.seq (.assign "tt" (mul (V "ci") (V "nn")))
  (.seq (.assign "cr" (sub (V "i") (V "tt")))
  (.seq (.assign "j1" (.bin .div (V "cr") (V "n")))
  (.seq (.assign "tt" (mul (V "j1") (V "n")))
  (.seq (.assign "j2" (sub (V "cr") (V "tt")))
  (.seq (.assign "tt" (mul (V "ci") (V "n")))
  (.seq (.assign "x1" (add (V "tt") (V "j1")))
  (.seq (.assign "x2" (add (V "tt") (V "j2")))
  (.seq (.assign "pa" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "x1"))) (.lit 0))))
  (.seq (.assign "da" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "x1"))) (.lit 1))))
  (.seq (.assign "pb" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "x2"))) (.lit 0))))
    (.assign "db" (.get "TK" (add (add (.lit 2) (mul (.lit 2) (V "x2"))) (.lit 1)))))))))))))))

/-- The scalars `comp1` assigns. -/
def A1 : List String := ["ci", "tt", "cr", "j1", "j2", "x1", "x2", "pa", "da", "pb", "db"]

set_option maxHeartbeats 8000000 in
/-- **The numbers of a conflict clause.** -/
theorem comp1_run (arr : List ℕ) (n m c : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = c) (hn : σ.vars "n" = n)
    (hnn : σ.vars "nn" = n * n) (hc : c < m * n * n) (hcB : c + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B comp1 σ σ' 200 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.vars "j1" = c % (n * n) / n ∧ σ'.vars "j2" = c % (n * n) % n ∧
      σ'.vars "x1" = c / (n * n) * n + c % (n * n) / n ∧
      σ'.vars "x2" = c / (n * n) * n + c % (n * n) % n ∧
      σ'.vars "pa" = arr.getD (2 + 2 * (c / (n * n) * n + c % (n * n) / n)) 0 ∧
      σ'.vars "da" = arr.getD (2 + 2 * (c / (n * n) * n + c % (n * n) / n) + 1) 0 ∧
      σ'.vars "pb" = arr.getD (2 + 2 * (c / (n * n) * n + c % (n * n) % n)) 0 ∧
      σ'.vars "db" = arr.getD (2 + 2 * (c / (n * n) * n + c % (n * n) % n) + 1) 0 ∧
      ∀ y, y ∉ A1 → σ'.vars y = σ.vars y := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hnn0 : 0 < n * n := Nat.mul_pos hn0 hn0
  obtain ⟨a, ha⟩ : ∃ a, a = c / (n * n) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = c % (n * n) := ⟨_, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ j, j = r / n := ⟨_, rfl⟩
  obtain ⟨j2, hj2⟩ : ∃ j, j = r % n := ⟨_, rfl⟩
  have hdm1 : n * n * a + r = c := by rw [ha, hr]; exact Nat.div_add_mod c (n * n)
  have hdm2 : n * j1 + j2 = r := by rw [hj1, hj2]; exact Nat.div_add_mod r n
  have ham : a < m := by rw [ha, Nat.div_lt_iff_lt_mul hnn0, ← Nat.mul_assoc]; exact hc
  have hrl : r < n * n := by rw [hr]; exact Nat.mod_lt _ hnn0
  have hj1l : j1 < n := by rw [hj1, Nat.div_lt_iff_lt_mul hn0]; exact hrl
  have hj2l : j2 < n := by rw [hj2]; exact Nat.mod_lt _ hn0
  have hx1 : a * n + j1 < m * n := cell_lt ham hj1l
  have hx2 : a * n + j2 < m * n := cell_lt ham hj2l
  have e1 : a * (n * n) = n * n * a := Nat.mul_comm _ _
  have e2 : j1 * n = n * j1 := Nat.mul_comm _ _
  have hale : a ≤ c := by rw [ha]; exact Nat.div_le_self _ _
  have hrle : r ≤ c := by rw [hr]; exact Nat.mod_le _ _
  have hj1le : j1 ≤ r := by rw [hj1]; exact Nat.div_le_self _ _
  have hj2le : j2 ≤ r := by rw [hj2]; exact Nat.mod_le _ _
  -- ci := i / nn
  have s1 : Run B (.assign "ci" (.bin .div (V "i") (V "nn"))) σ (σ.setVar "ci" a) 4 := by
    have := asg_bin (B := B) .div "i" "nn" "ci" σ c (n * n) hi hnn (by
      show c / (n * n) < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [← ha] at this; exact this
  set σ1 := σ.setVar "ci" a with hσ1
  have s1i : σ1.vars "i" = c := by simp [hσ1, Env.setVar, hi]
  have s1nn : σ1.vars "nn" = n * n := by simp [hσ1, Env.setVar, hnn]
  have s1n : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have s1ci : σ1.vars "ci" = a := by simp [hσ1, Env.setVar]
  -- tt := ci * nn
  have s2 : Run B (.assign "tt" (mul (V "ci") (V "nn"))) σ1 (σ1.setVar "tt" (n * n * a)) 4 := by
    have := asg_bin (B := B) .mul "ci" "nn" "tt" σ1 a (n * n) s1ci s1nn (by
      show a * (n * n) < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [e1] at this; exact this
  set σ2 := σ1.setVar "tt" (n * n * a) with hσ2
  have s2i : σ2.vars "i" = c := by simp [hσ2, Env.setVar, s1i]
  have s2tt : σ2.vars "tt" = n * n * a := by simp [hσ2, Env.setVar]
  have s2n : σ2.vars "n" = n := by simp [hσ2, Env.setVar, s1n]
  have s2ci : σ2.vars "ci" = a := by simp [hσ2, Env.setVar, s1ci]
  have s2nn : σ2.vars "nn" = n * n := by simp [hσ2, Env.setVar, s1nn]
  -- cr := i - tt
  have s3 : Run B (.assign "cr" (sub (V "i") (V "tt"))) σ2 (σ2.setVar "cr" r) 4 := by
    have := asg_bin (B := B) .sub "i" "tt" "cr" σ2 c (n * n * a) s2i s2tt (by
      show c - n * n * a < B; omega) (by omega) (by omega)
    have e : c - n * n * a = r := by omega
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [e] at this; exact this
  set σ3 := σ2.setVar "cr" r with hσ3
  have s3cr : σ3.vars "cr" = r := by simp [hσ3, Env.setVar]
  have s3n : σ3.vars "n" = n := by simp [hσ3, Env.setVar, s2n]
  have s3ci : σ3.vars "ci" = a := by simp [hσ3, Env.setVar, s2ci]
  have s3i : σ3.vars "i" = c := by simp [hσ3, Env.setVar, s2i]
  have s3nn : σ3.vars "nn" = n * n := by simp [hσ3, Env.setVar, s2nn]
  -- j1 := cr / n
  have s4 : Run B (.assign "j1" (.bin .div (V "cr") (V "n"))) σ3 (σ3.setVar "j1" j1) 4 := by
    have := asg_bin (B := B) .div "cr" "n" "j1" σ3 r n s3cr s3n (by
      show r / n < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [← hj1] at this; exact this
  set σ4 := σ3.setVar "j1" j1 with hσ4
  have s4j1 : σ4.vars "j1" = j1 := by simp [hσ4, Env.setVar]
  have s4n : σ4.vars "n" = n := by simp [hσ4, Env.setVar, s3n]
  have s4cr : σ4.vars "cr" = r := by simp [hσ4, Env.setVar, s3cr]
  have s4ci : σ4.vars "ci" = a := by simp [hσ4, Env.setVar, s3ci]
  -- tt := j1 * n
  have s5 : Run B (.assign "tt" (mul (V "j1") (V "n"))) σ4 (σ4.setVar "tt" (n * j1)) 4 := by
    have := asg_bin (B := B) .mul "j1" "n" "tt" σ4 j1 n s4j1 s4n (by
      show j1 * n < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [e2] at this; exact this
  set σ5 := σ4.setVar "tt" (n * j1) with hσ5
  have s5tt : σ5.vars "tt" = n * j1 := by simp [hσ5, Env.setVar]
  have s5cr : σ5.vars "cr" = r := by simp [hσ5, Env.setVar, s4cr]
  have s5j1 : σ5.vars "j1" = j1 := by simp [hσ5, Env.setVar, s4j1]
  have s5n : σ5.vars "n" = n := by simp [hσ5, Env.setVar, s4n]
  have s5ci : σ5.vars "ci" = a := by simp [hσ5, Env.setVar, s4ci]
  -- j2 := cr - tt
  have s6 : Run B (.assign "j2" (sub (V "cr") (V "tt"))) σ5 (σ5.setVar "j2" j2) 4 := by
    have := asg_bin (B := B) .sub "cr" "tt" "j2" σ5 r (n * j1) s5cr s5tt (by
      show r - n * j1 < B; omega) (by omega) (by omega)
    have e : r - n * j1 = j2 := by omega
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [e] at this; exact this
  set σ6 := σ5.setVar "j2" j2 with hσ6
  have s6j2 : σ6.vars "j2" = j2 := by simp [hσ6, Env.setVar]
  have s6j1 : σ6.vars "j1" = j1 := by simp [hσ6, Env.setVar, s5j1]
  have s6n : σ6.vars "n" = n := by simp [hσ6, Env.setVar, s5n]
  have s6ci : σ6.vars "ci" = a := by simp [hσ6, Env.setVar, s5ci]
  -- tt := ci * n
  have s7 : Run B (.assign "tt" (mul (V "ci") (V "n"))) σ6 (σ6.setVar "tt" (a * n)) 4 := by
    have := asg_bin (B := B) .mul "ci" "n" "tt" σ6 a n s6ci s6n (by
      show a * n < B; omega) (by omega) (by omega)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this
    exact this
  set σ7 := σ6.setVar "tt" (a * n) with hσ7
  have s7tt : σ7.vars "tt" = a * n := by simp [hσ7, Env.setVar]
  have s7j1 : σ7.vars "j1" = j1 := by simp [hσ7, Env.setVar, s6j1]
  have s7j2 : σ7.vars "j2" = j2 := by simp [hσ7, Env.setVar, s6j2]
  -- x1 := tt + j1
  have s8 : Run B (.assign "x1" (add (V "tt") (V "j1"))) σ7 (σ7.setVar "x1" (a * n + j1)) 4 :=
    asg_bin (B := B) .add "tt" "j1" "x1" σ7 (a * n) j1 s7tt s7j1 (by
      show a * n + j1 < B; omega) (by omega) (by omega)
  set σ8 := σ7.setVar "x1" (a * n + j1) with hσ8
  have s8x1 : σ8.vars "x1" = a * n + j1 := by simp [hσ8, Env.setVar]
  have s8tt : σ8.vars "tt" = a * n := by simp [hσ8, Env.setVar, s7tt]
  have s8j2 : σ8.vars "j2" = j2 := by simp [hσ8, Env.setVar, s7j2]
  -- x2 := tt + j2
  have s9 : Run B (.assign "x2" (add (V "tt") (V "j2"))) σ8 (σ8.setVar "x2" (a * n + j2)) 4 :=
    asg_bin (B := B) .add "tt" "j2" "x2" σ8 (a * n) j2 s8tt s8j2 (by
      show a * n + j2 < B; omega) (by omega) (by omega)
  set σ9 := σ8.setVar "x2" (a * n + j2) with hσ9
  have s9x2 : σ9.vars "x2" = a * n + j2 := by simp [hσ9, Env.setVar]
  have s9x1 : σ9.vars "x1" = a * n + j1 := by simp [hσ9, Env.setVar, s8x1]
  have hA9 : σ9.arrs "TK" = arr := by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
    Env.setVar, hA]
  -- the four reads
  have s10 := asg_tk (B := B) "x1" "pa" 0 σ9 arr (a * n + j1) hA9 s9x1 (by omega) (by omega)
    (by have := hE (2 + 2 * (a * n + j1) + 0) (by omega); omega)
  set σ10 := σ9.setVar "pa" (arr.getD (2 + 2 * (a * n + j1) + 0) 0) with hσ10
  have hA10 : σ10.arrs "TK" = arr := by simp [hσ10, Env.setVar, hA9]
  have s10x1 : σ10.vars "x1" = a * n + j1 := by simp [hσ10, Env.setVar, s9x1]
  have s10x2 : σ10.vars "x2" = a * n + j2 := by simp [hσ10, Env.setVar, s9x2]
  have s11 := asg_tk (B := B) "x1" "da" 1 σ10 arr (a * n + j1) hA10 s10x1 (by omega) (by omega)
    (by have := hE (2 + 2 * (a * n + j1) + 1) (by omega); omega)
  set σ11 := σ10.setVar "da" (arr.getD (2 + 2 * (a * n + j1) + 1) 0) with hσ11
  have hA11 : σ11.arrs "TK" = arr := by simp [hσ11, Env.setVar, hA10]
  have s11x2 : σ11.vars "x2" = a * n + j2 := by simp [hσ11, Env.setVar, s10x2]
  have s12 := asg_tk (B := B) "x2" "pb" 0 σ11 arr (a * n + j2) hA11 s11x2 (by omega) (by omega)
    (by have := hE (2 + 2 * (a * n + j2) + 0) (by omega); omega)
  set σ12 := σ11.setVar "pb" (arr.getD (2 + 2 * (a * n + j2) + 0) 0) with hσ12
  have hA12 : σ12.arrs "TK" = arr := by simp [hσ12, Env.setVar, hA11]
  have s12x2 : σ12.vars "x2" = a * n + j2 := by simp [hσ12, Env.setVar, s11x2]
  have s13 := asg_tk (B := B) "x2" "db" 1 σ12 arr (a * n + j2) hA12 s12x2 (by omega) (by omega)
    (by have := hE (2 + 2 * (a * n + j2) + 1) (by omega); omega)
  set σ13 := σ12.setVar "db" (arr.getD (2 + 2 * (a * n + j2) + 1) 0) with hσ13
  refine ⟨σ13, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
    (s10.seq (s11.seq (s12.seq s13)))))))))))).mono (by omega), ?_⟩
  have hfr : ∀ y, y ∉ A1 → σ13.vars y = σ.vars y := by
    intro y hy
    simp only [A1, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hy
    simp [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  subst ha hj1 hj2 hr
  refine ⟨by simp [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar],
    by simp [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfr⟩ <;>
  simp [hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]

end Lax117284Proofs.Machine.T9Comp1
