import Lax117284Proofs.Machine.ClBuildTab
import Lax117284Proofs.ClientsILPIndep

/-!
The table of independent pairs: `okt[c] = 1` exactly when the pair (type `c / Z`, subset `c % Z`)
is independent.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One position `q = a * n + b` of the pair `(ct, cs)`: the flag drops to zero on a violation. -/
def okStep : Com := seqs [
  asg "qa" (dv (V "q") (V "n")), asg "qb" (sub (V "q") (mul (V "qa") (V "n"))),
  asg "bd" (mul (mul (add (ltFl (V "qa") (V "qb")) (ltFl (V "qb") (V "qa")))
    (mul (bitE (V "cs") (V "qa")) (bitE (V "cs") (V "qb")))) (bitE (V "ct") (V "q"))),
  asg "fg" (sub (V "fg") (mul (V "fg") (V "bd"))),
  asg "q" (add (V "q") (lit 1))]

/-- The flag of one pair, in `fg`. -/
def okInner : Com := seqs [asg "fg" (lit 1), asg "q" (lit 0), .while (.lt (V "q") (V "nn")) okStep]

/-- The store into the table and the increment. -/
def okBump : Com := seqs [.store "okt" (V "cc") (V "fg"), asg "cc" (add (V "cc") (lit 1))]

/-- One column: split it into type and subset, compute the flag, store it. -/
def okBody : Com := .seq (.seq (asg "ct" (dv (V "cc") (V "Z")))
  (asg "cs" (sub (V "cc") (mul (V "ct") (V "Z"))))) (.seq okInner okBump)

/-- The whole table. -/
def okCom : Com := seqs [asg "cc" (lit 0), .while (.lt (V "cc") (V "Vv")) okBody]

theorem bitE_eq (x p : ℕ) : x / 2 ^ p % 2 = if x.testBit p = true then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : x / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h : x / 2 ^ p % 2 = 1
  · simp [h]
  · have : x / 2 ^ p % 2 = 0 := by omega
    simp [this]

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The invariant of the position loop for the column `c`. -/
def OInv (I : Instance) (x : List ℕ) (k c : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.vars "ct" = c / nZ I.clients ∧ σ.vars "cs" = c % nZ I.clients ∧
    σ.vars "q" ≤ I.clients * I.clients ∧
    σ.vars "fg" = if (∀ q' < σ.vars "q", ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) q')
      then 1 else 0

theorem bd_eq (n ct cs q : ℕ) :
    ((q % n - q / n - (q % n - q / n - 1)) + (q / n - q % n - (q / n - q % n - 1))) *
      (cs / 2 ^ (q / n) % 2 * (cs / 2 ^ (q % n) % 2)) * (ct / 2 ^ q % 2) =
      if badQ n ct cs q then 1 else 0 := by
  rw [bitE_eq, bitE_eq, bitE_eq]
  unfold badQ
  by_cases h1 : q / n = q % n
  · simp [h1]
  · have : (q % n - q / n - (q % n - q / n - 1)) + (q / n - q % n - (q / n - q % n - 1)) = 1 := by
      omega
    rw [this]
    by_cases h2 : cs.testBit (q / n) = true <;> by_cases h3 : cs.testBit (q % n) = true <;>
      by_cases h4 : ct.testBit q = true <;> simp [h1, h2, h3, h4]

theorem mod2_mul_le (a b : ℕ) : a % 2 * (b % 2) ≤ 1 := by
  have := Nat.mod_lt a (by norm_num : 0 < 2); have := Nat.mod_lt b (by norm_num : 0 < 2)
  interval_cases (a % 2) <;> interval_cases (b % 2) <;> simp

theorem sub1_sum (a b : ℕ) : (a - (a - 1)) + (b - (b - 1)) ≤ 2 := by omega

set_option maxHeartbeats 6400000 in
theorem okStep_spec (h : Bh I x k B) (c : ℕ) (hc : c < nV I.clients) :
    Spec B (fun σ => OInv I x k c σ ∧ σ.vars "q" < I.clients * I.clients) okStep
      (fun σ σ' => OInv I x k c σ' ∧ σ'.vars "q" = σ.vars "q" + 1) 200 := by
  have hnB := h.n_lt
  have hnnB := h.nn_lt
  have hnT := h.nT_lt
  rcases Nat.eq_zero_or_pos I.clients with h0 | hn
  · intro σ ⟨_, hq⟩
    rw [h0] at hq; simp at hq
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hz := h.hzB
  have hL := h.hL
  have hctT : c / nZ I.clients < nT I.clients := by
    rw [Nat.div_lt_iff_lt_mul (nZ_pos _)]; exact hc
  have hcsZ : c % nZ I.clients < nZ I.clients := Nat.mod_lt _ (nZ_pos _)
  have hmod : ∀ q n : ℕ, q - q / n * n = q % n := fun q n => by
    rw [Nat.mul_comm]; exact (Nat.mod_def q n).symm
  have hlt : ∀ q' : ℕ, (∀ p ≤ q', ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) p) ↔
      ((∀ p < q', ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) p) ∧
        ¬ badQ I.clients (c / nZ I.clients) (c % nZ I.clients) q') := by
    intro q'
    constructor
    · intro hh; exact ⟨fun p hp => hh p (by omega), hh q' le_rfl⟩
    · rintro ⟨h1, h2⟩ p hp
      rcases Nat.lt_or_ge p q' with h3 | h3
      · exact h1 p h3
      · have : p = q' := by omega
        rw [this]; exact h2
  run_vcg
  all_goals
    obtain ⟨hC, hS, hct, hcs, hqle, hfg⟩ := ‹OInv I x k c _›
    have hq : σ.vars "q" < I.clients * I.clients := ‹_›
    have hd1 : σ.vars "q" / I.clients ≤ σ.vars "q" := Nat.div_le_self _ _
    have hd2 : σ.vars "q" / I.clients * I.clients ≤ σ.vars "q" := Nat.div_mul_le_self _ _
    have hd3 : σ.vars "q" % I.clients ≤ σ.vars "q" := Nat.mod_le _ _
    have hd4 : σ.vars "q" / I.clients < I.clients := Nat.div_lt_of_lt_mul hq
    have hd5 : σ.vars "q" % I.clients < I.clients := Nat.mod_lt _ hn
    have hd6 : σ.vars "q" % I.clients - σ.vars "q" / I.clients ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd3
    have hd7 : σ.vars "q" % I.clients - σ.vars "q" / I.clients - 1 ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd6
    have hd8 : σ.vars "q" / I.clients - σ.vars "q" % I.clients ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd1
    have hd9 : σ.vars "q" / I.clients - σ.vars "q" % I.clients - 1 ≤ σ.vars "q" :=
      le_trans (Nat.sub_le _ _) hd8
    have he1 : c % nZ I.clients / 2 ^ (σ.vars "q" / I.clients) ≤ c % nZ I.clients := Nat.div_le_self _ _
    have he2 : c % nZ I.clients / 2 ^ (σ.vars "q" % I.clients) ≤ c % nZ I.clients := Nat.div_le_self _ _
    have he3 : c / nZ I.clients / 2 ^ σ.vars "q" ≤ c / nZ I.clients := Nat.div_le_self _ _
    have hm2 : ∀ a : ℕ, a % 2 < 2 := fun a => Nat.mod_lt _ (by norm_num)
  all_goals try
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp [Env.setVar, hC.X, hC.n, hC.m, hC.k, hS.nn, hS.T, hS.Z, hS.Vv, hS.N, hS.M,
    hS.zl, hct, hcs, hmod, bd_eq, hlt]
  all_goals try (rw [hfg]; split_ifs <;> simp_all)
  all_goals try omega
  all_goals try (rw [bd_eq]; split_ifs <;> omega)
  all_goals try (split_ifs <;> omega)
  all_goals try
    (have ha := hm2 (c % nZ I.clients / 2 ^ (σ.vars "q" / I.clients))
     have hb := hm2 (c % nZ I.clients / 2 ^ (σ.vars "q" % I.clients))
     have hB3 : 2 < B := by omega
     first
       | exact lt_of_le_of_lt (mod2_mul_le _ _) (by omega)
       | exact lt_of_le_of_lt (Nat.mul_le_mul (sub1_sum _ _) (mod2_mul_le _ _)) (by omega))

end Lax117284Proofs.Machine.ClBuild
