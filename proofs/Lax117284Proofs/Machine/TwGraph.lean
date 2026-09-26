import Lax117284Proofs.Machine.TwFill
import Lax117284Proofs.Machine.TwCf

/-!
The adjacency matrix of the overall conflict graph, built by the fill loop: the cell `fc` is the
pair of clients `fc / n` and `fc % n`, and it is `1` when they are distinct and conflict on some day.
The count of the conflicting days is the loop over the days that the violation counter already has,
run with the digit that holds every day.
-/

namespace Lax117284Proofs.Machine.TwGraph

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

macro "nrmB" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar, vars_setArr, arrs_setArr, ↓reduceIte, String.reduceEq, eq_self])

/-- The scalars a cell writes. -/
def SG : List String := ["val", "du", "dv", "dt", "dq"] ++ SD

/-- The two clients of a cell, and the digit that holds every day. -/
def adjPre : Com := seqs
  [ .assign "du" (.bin .div (V "fc") (V "n")),
    .assign "dv" (sub (V "fc") (mul (V "du") (V "n"))),
    .assign "dt" (V "mask"),
    .assign "dq" (V "mask"),
    .assign "vi" (L 0) ]

/-- The bit: distinct clients that conflict on some day. -/
def adjFin : Com :=
  .ite (.eq (V "du") (V "dv")) (.assign "val" (L 0))
    (.ite (.lt (L 0) (V "vi")) (.assign "val" (L 1)) (.assign "val" (L 0)))

/-- The cell of the matrix. -/
def adjCell : Com := .seq adjPre (.seq dLoop adjFin)

/-- The bit of the matrix: the two clients are distinct and conflict on a day. -/
def adjBit (X : List ℕ) (n m fc : ℕ) : ℕ :=
  if fc / n ≠ fc % n ∧ ∃ d < m, cfN X n m d (fc / n) (fc % n) then 1 else 0

lemma testBit_mask (m d : ℕ) (hd : d < m) : (2 ^ m - 1).testBit d = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hd

lemma cfDayN_mask_pos (X : List ℕ) (n m u v : ℕ) :
    0 < cfDayN X n m u v (2 ^ m - 1) (2 ^ m - 1) ↔ ∃ d < m, cfN X n m d u v := by
  unfold cfDayN
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨d, hd, hpos⟩
    have hd' := Finset.mem_range.1 hd
    refine ⟨d, hd', ?_⟩
    by_contra hn
    simp [hn] at hpos
  · rintro ⟨d, hd, hc⟩
    refine ⟨d, Finset.mem_range.2 hd, ?_⟩
    simp [testBit_mask m d hd, hc]

lemma mod_eq_sub (a n : ℕ) : a % n = a - a / n * n := by
  rw [Nat.mod_def, Nat.mul_comm]

theorem adjPre_run (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hmask : σ.vars "mask" < B)
    (hfc : σ.vars "fc" < B) (h0 : 0 < B) :
    ∃ σ1, Run B adjPre σ σ1 60 ∧ σ1 = ((((σ.setVar "du" (σ.vars "fc" / n)).setVar "dv"
      (σ.vars "fc" - σ.vars "fc" / n * n)).setVar "dt" (σ.vars "mask")).setVar "dq"
      (σ.vars "mask")).setVar "vi" 0 := by
  have hd : σ.vars "fc" / n < B := lt_of_le_of_lt (Nat.div_le_self _ _) hfc
  have hm : σ.vars "fc" / n * n < B := lt_of_le_of_lt (Nat.div_mul_le_self _ _) hfc
  unfold adjPre seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hn]; omega) | exact hd | (simp only [hn]; exact hm))
  all_goals (try simp only [hn])

/-- **The cell of the matrix.** -/
theorem adjCell_run (X : List ℕ) (n m : ℕ) (σ : Env) (hX : σ.arrs "X" = X)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (hmn : σ.vars "mn" = m * n)
    (hmask : σ.vars "mask" = 2 ^ m - 1) (hfc : σ.vars "fc" < n * n)
    (hlen : 2 + 2 * (m * n) + 1 ≤ X.length) (hXB : ∀ v ∈ X, v < B) (hB : X.length + 8 < B)
    (hmB : m + 3 < B) (hnB : n < B) (hmk : 2 ^ m < B) (hnn : n * n < B) :
    ∃ σ', Run B adjCell σ σ' (214 * m + 90) ∧
      σ'.vars "val" = adjBit X n m (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ∉ SG → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hnpos : 0 < n := by
    by_contra h; have : n = 0 := by omega
    subst this; omega
  have hfcB : σ.vars "fc" < B := by omega
  have hmaskB : σ.vars "mask" < B := by rw [hmask]; omega
  obtain ⟨σ1, r1, e1⟩ := adjPre_run (B := B) σ n hn hnB hmaskB hfcB (by omega)
  have hdu1 : σ1.vars "du" = σ.vars "fc" / n := by rw [e1]; simp [Env.setVar]
  have hdv1 : σ1.vars "dv" = σ.vars "fc" % n := by
    rw [e1]; simp [Env.setVar, mod_eq_sub]
  have hdt1 : σ1.vars "dt" = σ.vars "mask" := by rw [e1]; simp [Env.setVar]
  have hdq1 : σ1.vars "dq" = σ.vars "mask" := by rw [e1]; simp [Env.setVar]
  have hvi1 : σ1.vars "vi" = 0 := by rw [e1]; simp [Env.setVar]
  have hfr1 : ∀ y, y ∉ ["du", "dv", "dt", "dq", "vi"] → σ1.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e1]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [Env.setVar]
  have ho1 : σ1.out = σ.out := by rw [e1]; simp [Env.setVar]
  have hdult : σ1.vars "du" < n := by
    rw [hdu1]; exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hfc)
  have hdvlt : σ1.vars "dv" < n := by rw [hdv1]; exact Nat.mod_lt _ hnpos
  obtain ⟨σ2, r2, hv2, hA2, ho2⟩ := dLoop_run (B := B) X n m σ1 (by rw [har1]; exact hX)
    (by rw [hfr1 "n" (by simp)]; exact hn) (by rw [hfr1 "m" (by simp)]; exact hm)
    (by rw [hfr1 "mn" (by simp)]; exact hmn) hdult hdvlt hlen hXB hB
    (by rw [hdt1, hmask]; omega) (by rw [hdq1, hmask]; omega) (by omega) hnB
    (by rw [hvi1]; omega)
  have hdu2 : σ2.vars "du" = σ.vars "fc" / n := by rw [hA2.2 "du" (by simp [SD]), hdu1]
  have hdv2 : σ2.vars "dv" = σ.vars "fc" % n := by rw [hA2.2 "dv" (by simp [SD]), hdv1]
  have hcnt : σ2.vars "vi" = cfDayN X n m (σ.vars "fc" / n) (σ.vars "fc" % n) (2 ^ m - 1) (2 ^ m - 1) := by
    rw [hv2, hvi1, hdu1, hdv1, hdt1, hdq1, hmask]; simp
  have hvi2B : σ2.vars "vi" ≤ m := by rw [hcnt]; exact cfDayN_le _ _ _ _ _ _ _
  have hiff := cfDayN_mask_pos X n m (σ.vars "fc" / n) (σ.vars "fc" % n)
  have hAdj : (if σ.vars "fc" / n ≠ σ.vars "fc" % n then
      (if 0 < σ2.vars "vi" then 1 else 0) else 0) = adjBit X n m (σ.vars "fc") := by
    unfold adjBit
    rw [hcnt]
    by_cases h1 : σ.vars "fc" / n ≠ σ.vars "fc" % n <;>
      by_cases h2 : ∃ d < m, cfN X n m d (σ.vars "fc" / n) (σ.vars "fc" % n) <;>
      simp [h1, h2, hiff]
  obtain ⟨σ3, r3, e3, ha3, ho3, hf3⟩ : ∃ σ3, Run B adjFin σ2 σ3 20 ∧
      σ3.vars "val" = (if σ.vars "fc" / n ≠ σ.vars "fc" % n then
        (if 0 < σ2.vars "vi" then 1 else 0) else 0) ∧ σ3.arrs = σ2.arrs ∧ σ3.out = σ2.out ∧
      (∀ y, y ≠ "val" → σ3.vars y = σ2.vars y) := by
    unfold adjFin
    run_vcg
    all_goals first
      | (refine ⟨?_, rfl, rfl, fun y hy => by simp [Env.setVar, hy]⟩
         nrmB
         first
           | rw [if_neg (by omega)]
           | rw [if_pos (by omega), if_pos (by omega)]
           | rw [if_pos (by omega), if_neg (by omega)])
      | omega
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), by rw [e3, hAdj], by rw [ha3, hA2.1, har1], ?_, by rw [ho3, ho2, ho1]⟩
  intro y hy
  have hy' : y ∉ ["du", "dv", "dt", "dq", "vi"] ∧ y ∉ SD ∧ y ≠ "val" := by
    refine ⟨?_, fun h => hy (by simp [SG, h]), fun h => hy (by simp [SG, h])⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> exact hy (by simp [SG, SD, h])
  rw [hf3 y hy'.2.2, hA2.2 y hy'.2.1, hfr1 y hy'.1]

end Lax117284Proofs.Machine.TwGraph
