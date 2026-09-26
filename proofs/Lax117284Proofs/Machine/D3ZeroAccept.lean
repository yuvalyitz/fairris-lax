import Lax117284Proofs.Machine.D3ZeroSem
import Lax117284Proofs.Machine.BlockFinal

/-!
The accepting phase at zero days: read the day count, and when it is zero, read the parameter and
the client count and write the satisfiable formula exactly when the parameter is zero or there is
no client; write the unsatisfiable formula otherwise. No dynamic program is needed, since
`decideOk_zero_iff` reduces the class to a comparison of three numbers against zero.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.MisBlk
open Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.BlockFinal (getD_eq_of_take)

open scoped Classical

variable {B : ℕ}

/-- The whole of the reduction at zero days, after the tokenizer has accepted. -/
def acceptM0 : Com :=
  .seq (.assign "m1" (.get "TK" (.lit 1)))
  (.ite (.eq (V "m1") (.lit 0))
    (.seq (.assign "n0" (.get "TK" (.lit 0)))
    (.seq (.assign "pr" (.get "TK" (.lit 2)))
      (.ite (.eq (V "pr") (.lit 0)) X1Accept.printZ
        (.ite (.eq (V "n0") (.lit 0)) X1Accept.printZ T9Accept.rejT9))))
    T9Accept.rejT9)

/-- The cost of the accepting phase at zero days: a constant, since no loop over the table is
needed. -/
def KaccM0 (Sz _l : ℕ) : ℕ := 25 + Krej9 Sz

lemma KaccM0_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM0 Sz a ≤ KaccM0 Sz b := le_refl _

/-- **The satisfiable formula, as numbers.** -/
lemma sat_encode :
    Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF =
      encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, Lax117284Proofs.X1Word.satF]

/-- **The satisfiable formula, as bits.** -/
lemma sat_bits :
    natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF) =
      bitsNat 1 ++ bitsNat 0 := by
  rw [sat_encode, Lax117284Proofs.Machine.T9Comp1.natBits_app, natBits_encodeNat, natBits_encodeNat]

/-- **Writing the satisfiable formula.** -/
theorem printZ_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B X1Accept.printZ σ σ' (2 * (48 * Sz + 50)) ∧
      σ'.out = σ.out ++
        natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF) := by
  obtain ⟨σ1, r1, o1, -, -⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, -, -⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ1 trivial
  refine ⟨σ2, (r1.seq r2).mono (by omega), ?_⟩
  rw [o2, o1, sat_bits, List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The accepting phase at zero days.** -/
theorem acceptM0_run (Sz L : ℕ) (ns arr : List ℕ) (σ : Env)
    (hsh : Shape eU ns) (harr : arr.take ns.length = ns) (hA : σ.arrs "TK" = arr)
    (hlenL : ns.length ≤ L) (hvals : ∀ v ∈ ns, v < 2 ^ (L + 1))
    (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    ∃ σ', Run B acceptM0 σ σ' (KaccM0 Sz ns.length) ∧
      σ'.out = σ.out ++
        (if decideOk ns 0 then
          natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF)
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  have hg := getD_eq_of_take harr
  obtain ⟨h2, hl⟩ := hsh
  simp only [eU] at hl
  have hlenA : ns.length ≤ arr.length := by
    have := congrArg List.length harr
    rw [List.length_take] at this; omega
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
  have hPP : (2 : ℕ) ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
  have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
  have hlen3 : 3 ≤ ns.length := by omega
  have hE : ∀ k < 3, arr.getD k 0 + 8 < B := fun k hk => by
    rw [hg k (by omega)]
    have := hval k (by omega)
    omega
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  have hB6 : 6 < B := by have := hE 0 (by omega); omega
  have hidx1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by have := hE 1 (by omega); omega)
  have hev1 := RunStep.eval_get B σ "TK" (.lit 1) 1 hidx1 (by rw [hA]; omega)
    (by rw [hA]; have := hE 1 (by omega); omega)
  rw [hA] at hev1
  have s1 : Run B (.assign "m1" (.get "TK" (.lit 1))) σ (σ.setVar "m1" (arr.getD 1 0)) 3 :=
    (Run.assign hev1).mono (by simp [Expr.size])
  set σ1 := σ.setVar "m1" (arr.getD 1 0) with hσ1
  have m1v : σ1.vars "m1" = arr.getD 1 0 := by simp [hσ1, Env.setVar]
  have a1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have o1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have m1B : σ1.vars "m1" < B := by rw [m1v]; have := hE 1 (by omega); omega
  by_cases hm1 : arr.getD 1 0 = 0
  · have hcondT : (Cond.eq (V "m1") (.lit 0)).evalB B σ1 = some true :=
      condEq_true _ _ σ1 m1B (by simp [MisBlk.small]; omega) (by show σ1.vars "m1" = 0; rw [m1v]; exact hm1)
    have hm1' : ns.getD 1 0 = 0 := by rw [← h1]; exact hm1
    have hidxeq : 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) = 2 := by rw [hm1']; ring
    have hpar : paramOf ns = arr.getD 2 0 := by
      unfold paramOf
      rw [hidxeq, ← hg 2 (by omega)]
    have hidx0 : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
    have hev0 := RunStep.eval_get B σ1 "TK" (.lit 0) 0 hidx0 (by rw [a1, hA]; omega)
      (by rw [a1, hA]; have := hE 0 (by omega); omega)
    rw [a1, hA] at hev0
    have s2 : Run B (.assign "n0" (.get "TK" (.lit 0))) σ1 (σ1.setVar "n0" (arr.getD 0 0)) 3 :=
      (Run.assign hev0).mono (by simp [Expr.size])
    set σ2 := σ1.setVar "n0" (arr.getD 0 0) with hσ2
    have n0v : σ2.vars "n0" = arr.getD 0 0 := by simp [hσ2, Env.setVar]
    have a2 : σ2.arrs = σ1.arrs := by simp [hσ2, Env.setVar]
    have o2 : σ2.out = σ1.out := by simp [hσ2, Env.setVar]
    have hidx2 : (Expr.lit 2).evalB B σ2 = some 2 := evalB_lit (by have := hE 2 (by omega); omega)
    have hev2 := RunStep.eval_get B σ2 "TK" (.lit 2) 2 hidx2 (by rw [a2, a1, hA]; omega)
      (by rw [a2, a1, hA]; have := hE 2 (by omega); omega)
    rw [a2, a1, hA] at hev2
    have s3 : Run B (.assign "pr" (.get "TK" (.lit 2))) σ2 (σ2.setVar "pr" (arr.getD 2 0)) 3 :=
      (Run.assign hev2).mono (by simp [Expr.size])
    set σ3 := σ2.setVar "pr" (arr.getD 2 0) with hσ3
    have prv : σ3.vars "pr" = arr.getD 2 0 := by simp [hσ3, Env.setVar]
    have a3 : σ3.arrs = σ2.arrs := by simp [hσ3, Env.setVar]
    have o3 : σ3.out = σ2.out := by simp [hσ3, Env.setVar]
    have prB : σ3.vars "pr" < B := by rw [prv]; have := hE 2 (by omega); omega
    have n0v3 : σ3.vars "n0" = arr.getD 0 0 := by simp [hσ3, Env.setVar, n0v]
    have n0B3 : σ3.vars "n0" < B := by rw [n0v3]; have := hE 0 (by omega); omega
    by_cases hpr : arr.getD 2 0 = 0
    · have hcondT2 : (Cond.eq (V "pr") (.lit 0)).evalB B σ3 = some true :=
        condEq_true _ _ σ3 prB (by simp [MisBlk.small]; omega) (by show σ3.vars "pr" = 0; rw [prv]; exact hpr)
      obtain ⟨σ4, r4, o4⟩ := printZ_run (B := B) Sz σ3 hs (by omega)
      refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq
        (Run.ite_true hcondT2 r4))))).mono
        (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o4, o3, o2, o1]
      have hcond : decideOk ns 0 := by
        rw [decideOk_zero_iff]
        exact ⟨hm1', Or.inl (by rw [hpar]; exact hpr)⟩
      rw [if_pos hcond]
    · have hcondF2 : (Cond.eq (V "pr") (.lit 0)).evalB B σ3 = some false :=
        condEq_false _ _ σ3 prB (by simp [MisBlk.small]; omega) (by show σ3.vars "pr" ≠ 0; rw [prv]; exact hpr)
      by_cases hn0 : arr.getD 0 0 = 0
      · have hcondT3 : (Cond.eq (V "n0") (.lit 0)).evalB B σ3 = some true :=
          condEq_true _ _ σ3 n0B3 (by simp [MisBlk.small]; omega) (by show σ3.vars "n0" = 0; rw [n0v3]; exact hn0)
        obtain ⟨σ4, r4, o4⟩ := printZ_run (B := B) Sz σ3 hs (by omega)
        refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq (Run.ite_false hcondF2
          (Run.ite_true hcondT3 r4)))))).mono
          (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [o4, o3, o2, o1]
        have hcond : decideOk ns 0 := by
          rw [decideOk_zero_iff]
          exact ⟨hm1', Or.inr (by rw [← h0]; exact hn0)⟩
        rw [if_pos hcond]
      · have hcondF3 : (Cond.eq (V "n0") (.lit 0)).evalB B σ3 = some false :=
          condEq_false _ _ σ3 n0B3 (by simp [MisBlk.small]; omega) (by show σ3.vars "n0" ≠ 0; rw [n0v3]; exact hn0)
        obtain ⟨σ4, r4, o4⟩ := rejT9_run (B := B) Sz σ3 hs (by omega)
        refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq (Run.ite_false hcondF2
          (Run.ite_false hcondF3 r4)))))).mono
          (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [o4, o3, o2, o1]
        have hcond : ¬ decideOk ns 0 := by
          rw [decideOk_zero_iff]
          rintro ⟨-, hp | hc⟩
          · exact hpr (hpar.symm.trans hp)
          · exact hn0 (h0.trans hc)
        rw [if_neg hcond]
  · have hcondF : (Cond.eq (V "m1") (.lit 0)).evalB B σ1 = some false :=
      condEq_false _ _ σ1 m1B (by simp [MisBlk.small]; omega) (by show σ1.vars "m1" ≠ 0; rw [m1v]; exact hm1)
    have hm1'' : ns.getD 1 0 ≠ 0 := by rw [← h1]; exact hm1
    obtain ⟨σ2, r2, o2⟩ := rejT9_run (B := B) Sz σ1 hs (by omega)
    refine ⟨σ2, (s1.seq (Run.ite_false hcondF r2)).mono
      (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [o2, o1]
    have hcond : ¬ decideOk ns 0 := by
      rw [decideOk_zero_iff]
      rintro ⟨hm0, -⟩
      exact hm1'' hm0
    rw [if_neg hcond]

end Lax117284Proofs.Machine.D3Accept
