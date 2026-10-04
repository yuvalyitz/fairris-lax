import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.T9Sem
import Lax117284Proofs.OmegaFresh

/-! ### `Lax117284Proofs.Machine.T9Comp1` -/

section
/-!
The program that writes the clauses of Theorem 9: one loop over the conflict clauses and one over
the validation clauses, each clause computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Comp1

open Lax117284Proofs
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
      show c / (n * n) < B; omega_fresh) (by omega_fresh) (by omega_fresh)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [← ha] at this; exact this
  set σ1 := σ.setVar "ci" a with hσ1
  have s1i : σ1.vars "i" = c := by simp [hσ1, Env.setVar, hi]
  have s1nn : σ1.vars "nn" = n * n := by simp [hσ1, Env.setVar, hnn]
  have s1n : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have s1ci : σ1.vars "ci" = a := by simp [hσ1, Env.setVar]
  -- tt := ci * nn
  have s2 : Run B (.assign "tt" (mul (V "ci") (V "nn"))) σ1 (σ1.setVar "tt" (n * n * a)) 4 := by
    have := asg_bin (B := B) .mul "ci" "nn" "tt" σ1 a (n * n) s1ci s1nn (by
      show a * (n * n) < B; omega_fresh) (by omega_fresh) (by omega_fresh)
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
      show c - n * n * a < B; omega_fresh) (by omega_fresh) (by omega_fresh)
    have e : c - n * n * a = r := by omega_fresh
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
      show r / n < B; omega_fresh) (by omega_fresh) (by omega_fresh)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [← hj1] at this; exact this
  set σ4 := σ3.setVar "j1" j1 with hσ4
  have s4j1 : σ4.vars "j1" = j1 := by simp [hσ4, Env.setVar]
  have s4n : σ4.vars "n" = n := by simp [hσ4, Env.setVar, s3n]
  have s4cr : σ4.vars "cr" = r := by simp [hσ4, Env.setVar, s3cr]
  have s4ci : σ4.vars "ci" = a := by simp [hσ4, Env.setVar, s3ci]
  -- tt := j1 * n
  have s5 : Run B (.assign "tt" (mul (V "j1") (V "n"))) σ4 (σ4.setVar "tt" (n * j1)) 4 := by
    have := asg_bin (B := B) .mul "j1" "n" "tt" σ4 j1 n s4j1 s4n (by
      show j1 * n < B; omega_fresh) (by omega_fresh) (by omega_fresh)
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
      show r - n * j1 < B; omega_fresh) (by omega_fresh) (by omega_fresh)
    have e : r - n * j1 = j2 := by omega_fresh
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this; rw [e] at this; exact this
  set σ6 := σ5.setVar "j2" j2 with hσ6
  have s6j2 : σ6.vars "j2" = j2 := by simp [hσ6, Env.setVar]
  have s6j1 : σ6.vars "j1" = j1 := by simp [hσ6, Env.setVar, s5j1]
  have s6n : σ6.vars "n" = n := by simp [hσ6, Env.setVar, s5n]
  have s6ci : σ6.vars "ci" = a := by simp [hσ6, Env.setVar, s5ci]
  -- tt := ci * n
  have s7 : Run B (.assign "tt" (mul (V "ci") (V "n"))) σ6 (σ6.setVar "tt" (a * n)) 4 := by
    have := asg_bin (B := B) .mul "ci" "n" "tt" σ6 a n s6ci s6n (by
      show a * n < B; omega_fresh) (by omega_fresh) (by omega_fresh)
    simp only [Bop.apply_div, Bop.apply_mul, Bop.apply_sub, Bop.apply_add] at this
    exact this
  set σ7 := σ6.setVar "tt" (a * n) with hσ7
  have s7tt : σ7.vars "tt" = a * n := by simp [hσ7, Env.setVar]
  have s7j1 : σ7.vars "j1" = j1 := by simp [hσ7, Env.setVar, s6j1]
  have s7j2 : σ7.vars "j2" = j2 := by simp [hσ7, Env.setVar, s6j2]
  -- x1 := tt + j1
  have s8 : Run B (.assign "x1" (add (V "tt") (V "j1"))) σ7 (σ7.setVar "x1" (a * n + j1)) 4 :=
    asg_bin (B := B) .add "tt" "j1" "x1" σ7 (a * n) j1 s7tt s7j1 (by
      show a * n + j1 < B; omega_fresh) (by omega_fresh) (by omega_fresh)
  set σ8 := σ7.setVar "x1" (a * n + j1) with hσ8
  have s8x1 : σ8.vars "x1" = a * n + j1 := by simp [hσ8, Env.setVar]
  have s8tt : σ8.vars "tt" = a * n := by simp [hσ8, Env.setVar, s7tt]
  have s8j2 : σ8.vars "j2" = j2 := by simp [hσ8, Env.setVar, s7j2]
  -- x2 := tt + j2
  have s9 : Run B (.assign "x2" (add (V "tt") (V "j2"))) σ8 (σ8.setVar "x2" (a * n + j2)) 4 :=
    asg_bin (B := B) .add "tt" "j2" "x2" σ8 (a * n) j2 s8tt s8j2 (by
      show a * n + j2 < B; omega_fresh) (by omega_fresh) (by omega_fresh)
  set σ9 := σ8.setVar "x2" (a * n + j2) with hσ9
  have s9x2 : σ9.vars "x2" = a * n + j2 := by simp [hσ9, Env.setVar]
  have s9x1 : σ9.vars "x1" = a * n + j1 := by simp [hσ9, Env.setVar, s8x1]
  have hA9 : σ9.arrs "TK" = arr := by simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
    Env.setVar, hA]
  -- the four reads
  have s10 := asg_tk (B := B) "x1" "pa" 0 σ9 arr (a * n + j1) hA9 s9x1 (by omega_fresh) (by omega_fresh)
    (by have := hE (2 + 2 * (a * n + j1) + 0) (by omega_fresh); omega_fresh)
  set σ10 := σ9.setVar "pa" (arr.getD (2 + 2 * (a * n + j1) + 0) 0) with hσ10
  have hA10 : σ10.arrs "TK" = arr := by simp [hσ10, Env.setVar, hA9]
  have s10x1 : σ10.vars "x1" = a * n + j1 := by simp [hσ10, Env.setVar, s9x1]
  have s10x2 : σ10.vars "x2" = a * n + j2 := by simp [hσ10, Env.setVar, s9x2]
  have s11 := asg_tk (B := B) "x1" "da" 1 σ10 arr (a * n + j1) hA10 s10x1 (by omega_fresh) (by omega_fresh)
    (by have := hE (2 + 2 * (a * n + j1) + 1) (by omega_fresh); omega_fresh)
  set σ11 := σ10.setVar "da" (arr.getD (2 + 2 * (a * n + j1) + 1) 0) with hσ11
  have hA11 : σ11.arrs "TK" = arr := by simp [hσ11, Env.setVar, hA10]
  have s11x2 : σ11.vars "x2" = a * n + j2 := by simp [hσ11, Env.setVar, s10x2]
  have s12 := asg_tk (B := B) "x2" "pb" 0 σ11 arr (a * n + j2) hA11 s11x2 (by omega_fresh) (by omega_fresh)
    (by have := hE (2 + 2 * (a * n + j2) + 0) (by omega_fresh); omega_fresh)
  set σ12 := σ11.setVar "pb" (arr.getD (2 + 2 * (a * n + j2) + 0) 0) with hσ12
  have hA12 : σ12.arrs "TK" = arr := by simp [hσ12, Env.setVar, hA11]
  have s12x2 : σ12.vars "x2" = a * n + j2 := by simp [hσ12, Env.setVar, s11x2]
  have s13 := asg_tk (B := B) "x2" "db" 1 σ12 arr (a * n + j2) hA12 s12x2 (by omega_fresh) (by omega_fresh)
    (by have := hE (2 + 2 * (a * n + j2) + 1) (by omega_fresh); omega_fresh)
  set σ13 := σ12.setVar "db" (arr.getD (2 + 2 * (a * n + j2) + 1) 0) with hσ13
  refine ⟨σ13, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
    (s10.seq (s11.seq (s12.seq s13)))))))))))).mono (by omega_fresh), ?_⟩
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

end

/-! ### `Lax117284Proofs.Machine.T9Comp2` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.T9Prog` -/

section
/-!
The program that writes the clauses of Theorem 9: one loop over the conflict clauses and one over
the validation clauses, each clause computed from its index.
-/

namespace Lax117284Proofs.Machine.T9Prog

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Comp2

variable {B : ℕ}

lemma clB_conf (arr : List ℕ) (n m c : ℕ) (hc : c < m * n * n)
    (h : c % (n * n) / n ≠ c % (n * n) % n ∧
      confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n)) :
    clB arr n m c = bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [0] ++
      bitsNat (c / (n * n) * n + c % (n * n) % n) ++ [0] := by
  unfold clB clauseG
  rw [if_pos hc, if_pos h]
  simp [sb]

lemma clB_non (arr : List ℕ) (n m c : ℕ) (hc : c < m * n * n)
    (h : ¬ (c % (n * n) / n ≠ c % (n * n) % n ∧
      confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n))) :
    clB arr n m c = bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [1] ++
      bitsNat (c / (n * n) * n + c % (n * n) / n) ++ [0] := by
  unfold clB clauseG
  rw [if_pos hc, if_neg h]
  simp [sb]

/-- The branching of a conflict clause. -/
def br1 : Com :=
  .ite (.eq (V "j1") (V "j2")) (emitClause "x1" "x1" 1 0)
    (.ite (.lt (sub (V "da") (V "pa")) (V "db"))
      (.ite (.lt (sub (V "db") (V "pb")) (V "da")) (emitClause "x1" "x2" 0 0)
        (emitClause "x1" "x1" 1 0))
      (emitClause "x1" "x1" 1 0))

/-- Write a conflict clause. -/
def body1 : Com := .seq comp1 br1

/-- The cost of a conflict clause. -/
def K1 (Sz : ℕ) : ℕ := 320 + 2 * (48 * Sz + 50)

/-- **A conflict clause.** -/
theorem body1_run (Sz : ℕ) (arr : List ℕ) (n m c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = c) (hn : σ.vars "n" = n)
    (hnn : σ.vars "nn" = n * n) (hc : c < m * n * n) (hcB : c + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B body1 σ σ' (K1 Sz) ∧ σ'.out = σ.out ++ clB arr n m c ∧
      (∀ y ∉ S9, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, a1, o1, hj1, hj2, hx1, hx2, hpa, hda, hpb, hdb, hfr⟩ :=
    comp1_run (B := B) arr n m c σ hA hi hn hnn hc hcB hnB hnnB hmnB hE hL hlen
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hnn0 : 0 < n * n := Nat.mul_pos hn0 hn0
  have hai : c / (n * n) < m := by
    rw [Nat.div_lt_iff_lt_mul hnn0, ← Nat.mul_assoc]; exact hc
  have hrl : c % (n * n) < n * n := Nat.mod_lt _ hnn0
  have hj1l : c % (n * n) / n < n := by rw [Nat.div_lt_iff_lt_mul hn0]; exact hrl
  have hj2l : c % (n * n) % n < n := Nat.mod_lt _ hn0
  have hx1l := cell_lt hai hj1l
  have hx2l := cell_lt hai hj2l
  have hbase : ∀ σ'' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ''.vars y = σ1.vars y) →
      σ''.arrs = σ1.arrs → (∀ y ∉ S9, σ''.vars y = σ.vars y) ∧ σ''.arrs = σ.arrs := by
    intro σ'' hv ha
    refine ⟨fun y hy => ?_, by rw [ha, a1]⟩
    have hyA : y ∉ A1 := fun h => hy (by
      simp only [A1, S9, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h ⊢
      tauto)
    rw [hv y (nscr_of_s9 hy), hfr y hyA]
  have hx1B : σ1.vars "x1" + 4 < B := by rw [hx1]; omega
  have hx2B : σ1.vars "x2" + 4 < B := by rw [hx2]; omega
  have hcondj : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some (c % (n * n) / n ==
      c % (n * n) % n) := by
    have h := evalB_condEq (B := B) (σ := σ1)
      (evalB_var (B := B) (x := "j1") (σ := σ1) (by rw [hj1]; omega))
      (evalB_var (B := B) (x := "j2") (σ := σ1) (by rw [hj2]; omega))
    rw [hj1, hj2] at h
    exact h
  by_cases hj : c % (n * n) / n = c % (n * n) % n
  · have hT : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some true := by rw [hcondj, beq_iff_eq.2 hj]
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
      (by decide) hx1B hx1B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_true hT r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h.1 hj)]
  · have hF : (Cond.eq (V "j1") (V "j2")).evalB B σ1 = some false := by rw [hcondj, beq_eq_false_iff_ne.2 hj]
    have kA : 2 + 2 * (c / (n * n) * n + c % (n * n) / n) + 1 < 3 + 2 * (m * n) := by omega
    have kB : 2 + 2 * (c / (n * n) * n + c % (n * n) / n) < 3 + 2 * (m * n) := by omega
    have kC : 2 + 2 * (c / (n * n) * n + c % (n * n) % n) + 1 < 3 + 2 * (m * n) := by omega
    have kD : 2 + 2 * (c / (n * n) * n + c % (n * n) % n) < 3 + 2 * (m * n) := by omega
    have hda' : σ1.vars "da" < B := by
      rw [hda]; have := hE _ kA; omega
    have hpa' : σ1.vars "pa" < B := by
      rw [hpa]; have := hE _ kB; omega
    have hdb' : σ1.vars "db" < B := by
      rw [hdb]; have := hE _ kC; omega
    have hpb' : σ1.vars "pb" < B := by
      rw [hpb]; have := hE _ kD; omega
    have hc2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some (decide
        (σ1.vars "da" - σ1.vars "pa" < σ1.vars "db")) := by
      have h := evalB_condLt (B := B) (σ := σ1)
        (evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "da") (σ := σ1) hda')
          (evalB_var (B := B) (x := "pa") (σ := σ1) hpa') (by simp; omega))
        (evalB_var (B := B) (x := "db") (σ := σ1) hdb')
      simp only [Bop.apply_sub] at h
      exact h
    have hc3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some (decide
        (σ1.vars "db" - σ1.vars "pb" < σ1.vars "da")) := by
      have h := evalB_condLt (B := B) (σ := σ1)
        (evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "db") (σ := σ1) hdb')
          (evalB_var (B := B) (x := "pb") (σ := σ1) hpb') (by simp; omega))
        (evalB_var (B := B) (x := "da") (σ := σ1) hda')
      simp only [Bop.apply_sub] at h
      exact h
    have hconf : confG arr n (c / (n * n)) (c % (n * n) / n) (c % (n * n) % n) ↔
        (σ1.vars "da" - σ1.vars "pa" < σ1.vars "db" ∧ σ1.vars "db" - σ1.vars "pb" < σ1.vars "da") := by
      rw [hda, hpa, hdb, hpb]
      unfold confG
      simp
    by_cases h2 : σ1.vars "da" - σ1.vars "pa" < σ1.vars "db"
    · have hT2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some true := by
        rw [hc2]; simp [h2]
      by_cases h3 : σ1.vars "db" - σ1.vars "pb" < σ1.vars "da"
      · have hT3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some true := by
          rw [hc3]; simp [h3]
        obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x2" 0 0 σ1 hs (by decide)
          (by decide) hx1B hx2B (by omega) (by omega)
        obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
        refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_true hT3 r2)))).mono ?_,
          ?_, hv, ha⟩
        · simp [Cond.size, Expr.size, K1] <;> omega
        · rw [o2, o1, hx1, hx2, clB_conf arr n m c hc ⟨hj, hconf.2 ⟨h2, h3⟩⟩]
      · have hF3 : (Cond.lt (sub (V "db") (V "pb")) (V "da")).evalB B σ1 = some false := by
          rw [hc3]; simp [h3]
        obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
          (by decide) hx1B hx1B (by omega) (by omega)
        obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
        refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_false hF3 r2)))).mono ?_,
          ?_, hv, ha⟩
        · simp [Cond.size, Expr.size, K1] <;> omega
        · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h3 (hconf.1 h.2).2)]
    · have hF2 : (Cond.lt (sub (V "da") (V "pa")) (V "db")).evalB B σ1 = some false := by
        rw [hc2]; simp [h2]
      obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
        (by decide) hx1B hx1B (by omega) (by omega)
      obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
      refine ⟨σ2, (r1.seq (Run.ite_false hF (Run.ite_false hF2 r2))).mono ?_, ?_, hv, ha⟩
      · simp [Cond.size, Expr.size, K1] <;> omega
      · rw [o2, o1, hx1, clB_non arr n m c hc (fun h => h2 (hconf.1 h.2).1)]


lemma clB_v_ne (arr : List ℕ) (n m c : ℕ)
    (h : c % (m * m) / m ≠ c % (m * m) % m) :
    clB arr n m (m * n * n + c) = bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [1] ++
      bitsNat (c % (m * m) % m * n + c / (m * m)) ++ [1] := by
  unfold clB clauseG
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]
  simp [sb]

lemma clB_v_eq (arr : List ℕ) (n m c : ℕ)
    (h : ¬ c % (m * m) / m ≠ c % (m * m) % m) :
    clB arr n m (m * n * n + c) = bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [1] ++
      bitsNat (c % (m * m) / m * n + c / (m * m)) ++ [0] := by
  unfold clB clauseG
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_neg h]
  simp [sb]

/-- The branching of a validation clause. -/
def br2 : Com :=
  .ite (.eq (V "i1") (V "i2")) (emitClause "x1" "x1" 1 0) (emitClause "x1" "x2" 1 1)

/-- Write a validation clause. -/
def body2 : Com := .seq comp2 br2

/-- **A validation clause.** -/
theorem body2_run (Sz : ℕ) (arr : List ℕ) (n m c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hi : σ.vars "i" = c) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hmm : σ.vars "mm" = m * m) (hc : c < n * m * m) (hcB : c + 8 < B) (hmB : m + 8 < B)
    (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B) :
    ∃ σ', Run B body2 σ σ' (K1 Sz) ∧ σ'.out = σ.out ++ clB arr n m (m * n * n + c) ∧
      (∀ y ∉ S9, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, a1, o1, hi1, hi2, hx1, hx2, hfr⟩ :=
    comp2_run (B := B) n m c σ hi hn hm hmm hc hcB hmB hmmB hmnB
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hmm0 : 0 < m * m := Nat.mul_pos hm0 hm0
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hc; simp at hc
    · exact h
  have hj : c / (m * m) < n := by
    rw [Nat.div_lt_iff_lt_mul hmm0]
    have : n * m * m = n * (m * m) := Nat.mul_assoc _ _ _
    omega
  have hrl : c % (m * m) < m * m := Nat.mod_lt _ hmm0
  have hi1l : c % (m * m) / m < m := by rw [Nat.div_lt_iff_lt_mul hm0]; exact hrl
  have hi2l : c % (m * m) % m < m := Nat.mod_lt _ hm0
  have hx1l := cell_lt hi1l hj
  have hx2l := cell_lt hi2l hj
  have hbase : ∀ σ'' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ''.vars y = σ1.vars y) →
      σ''.arrs = σ1.arrs → (∀ y ∉ S9, σ''.vars y = σ.vars y) ∧ σ''.arrs = σ.arrs := by
    intro σ'' hv ha
    refine ⟨fun y hy => ?_, by rw [ha, a1]⟩
    have hyA : y ∉ A2 := fun h => hy (by
      simp only [A2, S9, List.mem_cons, List.not_mem_nil, or_false, List.mem_append] at h ⊢
      tauto)
    rw [hv y (nscr_of_s9 hy), hfr y hyA]
  have hx1B : σ1.vars "x1" + 4 < B := by rw [hx1]; omega
  have hx2B : σ1.vars "x2" + 4 < B := by rw [hx2]; omega
  have hcondj : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some (c % (m * m) / m ==
      c % (m * m) % m) := by
    have h := evalB_condEq (B := B) (σ := σ1)
      (evalB_var (B := B) (x := "i1") (σ := σ1) (by rw [hi1]; omega))
      (evalB_var (B := B) (x := "i2") (σ := σ1) (by rw [hi2]; omega))
    rw [hi1, hi2] at h
    exact h
  by_cases hj' : c % (m * m) / m = c % (m * m) % m
  · have hT : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some true := by
      rw [hcondj, beq_iff_eq.2 hj']
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x1" 1 0 σ1 hs (by decide)
      (by decide) hx1B hx1B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_true hT r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, clB_v_eq arr n m c (fun h => h hj')]
  · have hF : (Cond.eq (V "i1") (V "i2")).evalB B σ1 = some false := by
      rw [hcondj, beq_eq_false_iff_ne.2 hj']
    obtain ⟨σ2, r2, o2, v2, a2⟩ := emitClause_run (B := B) Sz "x1" "x2" 1 1 σ1 hs (by decide)
      (by decide) hx1B hx2B (by omega) (by omega)
    obtain ⟨hv, ha⟩ := hbase σ2 v2 a2
    refine ⟨σ2, (r1.seq (Run.ite_false hF r2)).mono ?_, ?_, hv, ha⟩
    · simp [Cond.size, Expr.size, K1] <;> omega
    · rw [o2, o1, hx1, hx2, clB_v_ne arr n m c hj']

end Lax117284Proofs.Machine.T9Prog

end

/-! ### `Lax117284Proofs.Machine.T9Print` -/

section
/-!
Writing the whole formula of Theorem 9: the two counts, then the loop over the conflict clauses and
the loop over the validation clauses.
-/

namespace Lax117284Proofs.Machine.T9Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.InstSem Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Comp2 Lax117284Proofs.Machine.T9Prog

variable {B : ℕ}

/-- **The loop over the conflict clauses.** -/
theorem cl1Loop_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ0.arrs "TK" = arr) (hn : σ0.vars "n" = n) (hnn : σ0.vars "nn" = n * n)
    (hC : σ0.vars "C1" = m * n * n) (hCB : m * n * n + 8 < B) (hnB : n + 8 < B)
    (hnnB : n * n + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B (outLoop "C1" body1) σ0 σ' ((K1 Sz + 10 + 4) * (m * n * n) + 6) ∧
      σ'.out = σ0.out ++ (List.range (m * n * n)).flatMap (clB arr n m) ∧
      (∀ y ∉ "i" :: S9, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C1" body1 ("i" :: S9) (clB arr n m) (K1 Sz)
    (m * n * n) σ0 (by simp) (by decide) hC (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hnn' : σ.vars "nn" = n * n := by rw [hAg.2 "nn" (by decide)]; exact hnn
      obtain ⟨σ1, r1, o1, v1, a1⟩ := body1_run (B := B) Sz arr n m (σ.vars "i") σ hs hA' rfl hn'
        hnn' hlt (by omega) hnB hnnB hmnB hE hL hlen
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ S9 := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  exact ⟨σ', r, o, hAg.2, hAg.1⟩

/-- **The loop over the validation clauses.** -/
theorem cl2Loop_run (Sz : ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m) (hmm : σ0.vars "mm" = m * m)
    (hC : σ0.vars "C2" = n * m * m) (hCB : n * m * m + 8 < B) (hmB : m + 8 < B)
    (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B) (arr : List ℕ) :
    ∃ σ', Run B (outLoop "C2" body2) σ0 σ' ((K1 Sz + 10 + 4) * (n * m * m) + 6) ∧
      σ'.out = σ0.out ++ (List.range (n * m * m)).flatMap (fun c => clB arr n m (m * n * n + c)) ∧
      (∀ y ∉ "i" :: S9, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C2" body2 ("i" :: S9)
    (fun c => clB arr n m (m * n * n + c)) (K1 Sz) (n * m * m) σ0 (by simp) (by decide) hC
    (by omega) (by
      intro σ hAg hlt
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hm' : σ.vars "m" = m := by rw [hAg.2 "m" (by decide)]; exact hm
      have hmm' : σ.vars "mm" = m * m := by rw [hAg.2 "mm" (by decide)]; exact hmm
      obtain ⟨σ1, r1, o1, v1, a1⟩ := body2_run (B := B) Sz arr n m (σ.vars "i") σ hs rfl hn' hm'
        hmm' hlt (by omega) hmB hmmB hmnB
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ S9 := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  exact ⟨σ', r, o, hAg.2, hAg.1⟩

/-- Write the whole formula. -/
def printT9 : Com :=
  .seq (emitVar "V1") (.seq (emitVar "CC")
    (.seq (outLoop "C1" body1) (outLoop "C2" body2)))

/-- The cost of writing the formula. -/
def KprintT (Sz C1 C2 : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + ((K1 Sz + 10 + 4) * C1 + 6) + ((K1 Sz + 10 + 4) * C2 + 6)

/-- **Writing the formula.** -/
theorem printT9_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hnn : σ.vars "nn" = n * n) (hmm : σ.vars "mm" = m * m)
    (hV : σ.vars "V1" = m * n + 1) (hCC : σ.vars "CC" = m * n * n + n * m * m)
    (hC1 : σ.vars "C1" = m * n * n) (hC2 : σ.vars "C2" = n * m * m)
    (hCCB : m * n * n + n * m * m + 8 < B) (hnB : n + 8 < B) (hmB : m + 8 < B)
    (hnnB : n * n + 8 < B) (hmmB : m * m + 8 < B) (hmnB : m * n + 8 < B)
    (hE : ∀ k < 3 + 2 * (m * n), arr.getD k 0 + 8 < B) (hL : 3 + 2 * (m * n) + 8 < B)
    (hlen : 3 + 2 * (m * n) ≤ arr.length) :
    ∃ σ', Run B printT9 σ σ' (KprintT Sz (m * n * n) (n * m * m)) ∧
      σ'.out = σ.out ++ natBits (outT9 arr n m) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "V1" Sz σ
    ⟨by rw [hV]; omega, by rw [hV]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "CC" Sz σ1
    ⟨by rw [v1 "CC" (by decide), hCC]; omega,
      by rw [v1 "CC" (by decide), hCC]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  have hC1B : m * n * n + 8 < B := by omega
  have hC2B : n * m * m + 8 < B := by omega
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cl1Loop_run (B := B) Sz arr n m σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "nn" (by decide)]; exact hnn)
    (by rw [z2 "C1" (by decide)]; exact hC1) hC1B hnB hnnB hmnB hE hL hlen
  have z3 : ∀ y, y ∉ "i" :: S9 → σ3.vars y = σ.vars y := fun y hy => by
    rw [v3 y hy]; exact z2 y (fun h => hy (List.mem_cons_of_mem _ (by
      simp only [S9, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)))
  obtain ⟨σ4, r4, o4, v4, a4⟩ := cl2Loop_run (B := B) Sz n m σ3 hs
    (by rw [z3 "n" (by decide)]; exact hn) (by rw [z3 "m" (by decide)]; exact hm)
    (by rw [z3 "mm" (by decide)]; exact hmm) (by rw [z3 "C2" (by decide)]; exact hC2) hC2B hmB
    hmmB hmnB arr
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintT; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "CC" (by decide), hCC, hV]
  unfold outT9
  have hrange : List.range (m * n * n + n * m * m) = List.range (m * n * n) ++
      (List.range (n * m * m)).map (fun c => m * n * n + c) := List.range_add ..
  have e1 : natBits ((List.range (m * n * n)).flatMap (clW arr n m)) =
      (List.range (m * n * n)).flatMap (clB arr n m) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun c _ => natBits_clW arr n m c
  have e2 : natBits ((List.range (n * m * m)).flatMap (fun c => clW arr n m (m * n * n + c))) =
      (List.range (n * m * m)).flatMap (fun c => clB arr n m (m * n * n + c)) := by
    simp only [natBits, List.map_flatMap]
    exact List.flatMap_congr fun c _ => natBits_clW arr n m (m * n * n + c)
  rw [hrange, List.flatMap_append, List.flatMap_map]
  simp only [natBits_app, natBits_encodeNat, List.append_assoc, Function.comp_def]
  rw [e1, e2]

end Lax117284Proofs.Machine.T9Print

end
