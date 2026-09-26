import Lax117284Proofs.Machine.SatPrint
import Lax117284Proofs.Machine.FreeAccept

/-!
The whole of the reduction of Theorem 7 after the tokenizer has accepted: read the counts off the
array, check the positions, and write either the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.SatAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank
open Lax117284Proofs.Machine.SatCheck Lax117284Proofs.Machine.SatDue Lax117284Proofs.Machine.SatPrint
open Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.SatFormat (SlotsN)

variable {B : ℕ}

/-- Read the counts off the array and derive the scalars the rest reads. -/
def prepSat : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "na" (.get "TK" (.lit 1)))
  (.seq (.assign "nb" (.get "TK" (.lit 2)))
  (.seq (.assign "A2" (.bin .mul (V "na") (.lit 2)))
  (.seq (.assign "t3" (.bin .mul (V "nb") (.lit 3)))
  (.seq (.assign "N" (.bin .add (V "A2") (V "t3")))
  (.seq (.assign "V3" (add (.lit 3) (mul (.lit 2) (V "n"))))
  (.seq (.assign "C" (.bin .add (V "V3") (V "N")))
  (.seq (.assign "K7" (add (.lit 7) (mul (.lit 2) (V "n"))))
  (.seq (.assign "K9" (add (.lit 9) (mul (.lit 2) (V "n"))))
  (.seq (.assign "K9" (.bin .add (V "K9") (V "A2")))
    (.ite (.lt (V "N") (V "n")) (.assign "ok" (.lit 0)) (.assign "ok" (.lit 1)))))))))))))

/-- The scalars the preparation assigns. -/
def AP : List String := ["n", "na", "nb", "A2", "t3", "N", "V3", "C", "K7", "K9", "ok"]

set_option maxHeartbeats 6400000 in
theorem prepSat_run (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr) (h3 : 3 ≤ arr.length)
    (hE : ∀ k < 3, arr.getD k 0 + 8 < B)
    (hb : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B) :
    ∃ σ', Run B prepSat σ σ' 120 ∧ σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "N" = SlotsN arr ∧
      σ'.vars "V3" = 3 + 2 * arr.getD 0 0 ∧ σ'.vars "A2" = 2 * arr.getD 1 0 ∧
      σ'.vars "K7" = 7 + 2 * arr.getD 0 0 ∧
      σ'.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0 ∧
      σ'.vars "C" = 3 + 2 * arr.getD 0 0 + SlotsN arr ∧
      σ'.vars "ok" = (if SlotsN arr < arr.getD 0 0 then 0 else 1) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ AP → σ'.vars y = σ.vars y := by
  have e0 := hE 0 (by omega)
  have e1 := hE 1 (by omega)
  have e2 := hE 2 (by omega)
  have s0 := asg_tkl (B := B) "n" 0 σ arr hA (by omega) (by omega) (by omega)
  set σ0 := σ.setVar "n" (arr.getD 0 0) with h0
  have A0 : σ0.arrs "TK" = arr := by simp [h0, Env.setVar, hA]
  have s1 := asg_tkl (B := B) "na" 1 σ0 arr A0 (by omega) (by omega) (by omega)
  set σ1 := σ0.setVar "na" (arr.getD 1 0) with h1
  have A1 : σ1.arrs "TK" = arr := by simp [h1, h0, Env.setVar, hA]
  have s2 := asg_tkl (B := B) "nb" 2 σ1 arr A1 (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "nb" (arr.getD 2 0) with h2
  have vna : σ2.vars "na" = arr.getD 1 0 := by simp [h2, h1, Env.setVar]
  have vnb : σ2.vars "nb" = arr.getD 2 0 := by simp [h2, Env.setVar]
  have vn2 : σ2.vars "n" = arr.getD 0 0 := by simp [h2, h1, h0, Env.setVar]
  have s3 := asg_binr (B := B) .mul "na" 2 "A2" σ2 (arr.getD 1 0) vna
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s3
  set σ3 := σ2.setVar "A2" (arr.getD 1 0 * 2) with h3'
  have vnb3 : σ3.vars "nb" = arr.getD 2 0 := by simp [h3', Env.setVar, vnb]
  have s4 := asg_binr (B := B) .mul "nb" 3 "t3" σ3 (arr.getD 2 0) vnb3
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s4
  set σ4 := σ3.setVar "t3" (arr.getD 2 0 * 3) with h4
  have vA24 : σ4.vars "A2" = arr.getD 1 0 * 2 := by simp [h4, h3', Env.setVar]
  have vt4 : σ4.vars "t3" = arr.getD 2 0 * 3 := by simp [h4, Env.setVar]
  have s5 := asg_bin (B := B) .add "A2" "t3" "N" σ4 (arr.getD 1 0 * 2) (arr.getD 2 0 * 3) vA24 vt4
    (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
  simp only [Bop.apply_add] at s5
  set σ5 := σ4.setVar "N" (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) with h5
  have vn5 : σ5.vars "n" = arr.getD 0 0 := by simp [h5, h4, h3', Env.setVar, vn2]
  have s6 := asg_linl (B := B) "V3" 3 2 "n" σ5 (arr.getD 0 0) vn5 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ6 := σ5.setVar "V3" (3 + 2 * arr.getD 0 0) with h6
  have vV6 : σ6.vars "V3" = 3 + 2 * arr.getD 0 0 := by simp [h6, Env.setVar]
  have vN6 : σ6.vars "N" = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by
    simp [h6, h5, Env.setVar]
  have s7 := asg_bin (B := B) .add "V3" "N" "C" σ6 (3 + 2 * arr.getD 0 0)
    (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) vV6 vN6 (by simp only [Bop.apply_add]; omega)
    (by omega) (by omega)
  simp only [Bop.apply_add] at s7
  set σ7 := σ6.setVar "C" (3 + 2 * arr.getD 0 0 + (arr.getD 1 0 * 2 + arr.getD 2 0 * 3)) with h7
  have vn7 : σ7.vars "n" = arr.getD 0 0 := by simp [h7, h6, h5, h4, h3', Env.setVar, vn2]
  have s8 := asg_linl (B := B) "K7" 7 2 "n" σ7 (arr.getD 0 0) vn7 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ8 := σ7.setVar "K7" (7 + 2 * arr.getD 0 0) with h8
  have vn8 : σ8.vars "n" = arr.getD 0 0 := by simp [h8, h7, h6, h5, h4, h3', Env.setVar, vn2]
  have s9 := asg_linl (B := B) "K9" 9 2 "n" σ8 (arr.getD 0 0) vn8 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ9 := σ8.setVar "K9" (9 + 2 * arr.getD 0 0) with h9
  have vK9 : σ9.vars "K9" = 9 + 2 * arr.getD 0 0 := by simp [h9, Env.setVar]
  have vA29 : σ9.vars "A2" = arr.getD 1 0 * 2 := by
    simp [h9, h8, h7, h6, h5, h4, h3', Env.setVar]
  have s10 := asg_bin (B := B) .add "K9" "A2" "K9" σ9 (9 + 2 * arr.getD 0 0) (arr.getD 1 0 * 2)
    vK9 vA29 (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
  simp only [Bop.apply_add] at s10
  set σ10 := σ9.setVar "K9" (9 + 2 * arr.getD 0 0 + arr.getD 1 0 * 2) with h10
  have vN10 : σ10.vars "N" = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by
    simp [h10, h9, h8, h7, h6, h5, Env.setVar]
  have vn10 : σ10.vars "n" = arr.getD 0 0 := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3', Env.setVar, vn2]
  have c := cond_ltv (B := B) "N" "n" σ10 _ _ vN10 vn10 (by omega) (by omega)
  have hA10 : σ10.arrs = σ.arrs := by simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar]
  have hO10 : σ10.out = σ.out := by simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar]
  have hSN : SlotsN arr = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by unfold SlotsN; omega
  have hfr : ∀ y, y ∉ AP → ∀ z ∈ AP, y ≠ z := fun y hy z hz h => hy (h ▸ hz)
  have hframe10 : ∀ y, y ∉ AP → σ10.vars y = σ.vars y := by
    intro y hy
    have g : ∀ z, z ∈ AP → y ≠ z := hfr y hy
    simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar, g "n" (by simp [AP]),
      g "na" (by simp [AP]), g "nb" (by simp [AP]), g "A2" (by simp [AP]), g "t3" (by simp [AP]),
      g "N" (by simp [AP]), g "V3" (by simp [AP]), g "C" (by simp [AP]), g "K7" (by simp [AP]),
      g "K9" (by simp [AP])]
  have fV3 : σ10.vars "V3" = 3 + 2 * arr.getD 0 0 := by
    simp [h10, h9, h8, h7, h6, Env.setVar]
  have fA2 : σ10.vars "A2" = arr.getD 1 0 * 2 := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3', Env.setVar]
  have fK7 : σ10.vars "K7" = 7 + 2 * arr.getD 0 0 := by simp [h10, h9, h8, Env.setVar]
  have fK9 : σ10.vars "K9" = 9 + 2 * arr.getD 0 0 + arr.getD 1 0 * 2 := by
    simp [h10, Env.setVar]
  have fC : σ10.vars "C" = 3 + 2 * arr.getD 0 0 + (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) := by
    simp [h10, h9, h8, h7, Env.setVar]
  have hfin : ∀ (v : ℕ), (σ10.setVar "ok" v).vars "n" = arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "N" = SlotsN arr ∧
      (σ10.setVar "ok" v).vars "V3" = 3 + 2 * arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "A2" = 2 * arr.getD 1 0 ∧
      (σ10.setVar "ok" v).vars "K7" = 7 + 2 * arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0 ∧
      (σ10.setVar "ok" v).vars "C" = 3 + 2 * arr.getD 0 0 + SlotsN arr ∧
      (σ10.setVar "ok" v).arrs = σ.arrs ∧ (σ10.setVar "ok" v).out = σ.out ∧
      ∀ y, y ∉ AP → (σ10.setVar "ok" v).vars y = σ.vars y := by
    intro v
    refine ⟨by simp [Env.setVar, vn10], by simp [Env.setVar, vN10, hSN],
      by simp [Env.setVar, fV3], by simp [Env.setVar, fA2]; omega, by simp [Env.setVar, fK7],
      by simp [Env.setVar, fK9]; omega, by simp [Env.setVar, fC, hSN], by simp [Env.setVar, hA10],
      by simp [Env.setVar, hO10], fun y hy => ?_⟩
    have hyo : y ≠ "ok" := fun h => hy (by simp [AP, h])
    simp only [Env.setVar, if_neg hyo]
    exact hframe10 y hy
  by_cases hlt : arr.getD 1 0 * 2 + arr.getD 2 0 * 3 < arr.getD 0 0
  · have hT : (Cond.lt (V "N") (V "n")).evalB B σ10 = some true := by
      rw [c]; exact congrArg some (decide_eq_true hlt)
    have l := asg_lit (B := B) "ok" 0 σ10 (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hfin 0
    exact ⟨_, (s0.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
      (s10.seq (Run.ite_true hT l)))))))))))).mono (by simp [Cond.size, Expr.size]),
      g1, g2, g3, g4, g5, g6, g7, by simp only [Env.setVar, if_true]; rw [hSN, if_pos hlt], g8, g9, g10⟩
  · have hF : (Cond.lt (V "N") (V "n")).evalB B σ10 = some false := by
      rw [c]; exact congrArg some (decide_eq_false hlt)
    have l := asg_lit (B := B) "ok" 1 σ10 (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hfin 1
    exact ⟨_, (s0.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
      (s10.seq (Run.ite_false hF l)))))))))))).mono (by simp [Cond.size, Expr.size]),
      g1, g2, g3, g4, g5, g6, g7, by simp only [Env.setVar, if_true]; rw [hSN, if_neg hlt], g8, g9, g10⟩

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptSat : Com :=
  .seq prepSat (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printSat rejectPrint))

/-- The cost of the accepting phase, on an input of `l` tokens. -/
def KaccS (Sz l : ℕ) : ℕ :=
  200 + ((120 + 64 * l + 4) * l + 6) + KprintS Sz l (3 + 3 * l) + 3 * (48 * Sz + 50)

lemma KprintS_mono (Sz a b N N' : ℕ) (h : a ≤ b) (h' : N ≤ N') :
    KprintS Sz a N ≤ KprintS Sz b N' := by
  unfold KprintS Kcell
  have h1 : (110 + 64 * a + 2 * (48 * Sz + 50) + 10 + 10 + 4) * N ≤
      (110 + 64 * b + 2 * (48 * Sz + 50) + 10 + 10 + 4) * N' :=
    Nat.mul_le_mul (by omega) h'
  omega

lemma KaccS_mono (Sz a b : ℕ) (h : a ≤ b) : KaccS Sz a ≤ KaccS Sz b := by
  unfold KaccS
  have h1 : (120 + 64 * a + 4) * a ≤ (120 + 64 * b + 4) * b := Nat.mul_le_mul (by omega) h
  have h2 := KprintS_mono Sz a b (3 + 3 * a) (3 + 3 * b) h (by omega)
  omega

open Classical in
set_option maxHeartbeats 3200000 in
theorem acceptSat_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hlen : 3 + 2 * SlotsN arr ≤ arr.length)
    (hE : ∀ k < 3 + 2 * SlotsN arr, arr.getD k 0 + 8 < B) (hl : SlotsN arr ≤ l)
    (hB : 60 * (SlotsN arr + 4) < B)
    (hb : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B) :
    ∃ σ', Run B acceptSat σ σ' (KaccS Sz l) ∧
      σ'.out = σ.out ++ (if CondN arr then numBits (outNums arr) else numBits [1, 0, 1]) := by
  obtain ⟨S, hSdef⟩ : ∃ S, SlotsN arr = S := ⟨_, rfl⟩
  rw [hSdef] at hlen hE hl hB
  have hB2 : 6 < B := by omega
  obtain ⟨σ1, r1, e1n, e1N, e1V3, e1A2, e1K7, e1K9, e1C, e1ok, e1a, e1o, e1f⟩ :=
    prepSat_run (B := B) arr σ hA (by omega) (fun k hk => hE k (by omega)) hb
  rw [hSdef] at e1N e1C e1ok
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hok0 : (if S < arr.getD 0 0 then 0 else 1) ≤ 1 := by split <;> omega
  have hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B := fun k hk => hE _ (by omega)
  have hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B := fun k hk => hE _ (by omega)
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_spec (B := B) arr S (arr.getD 0 0)
    (if S < arr.getD 0 0 then 0 else 1) σ1 rfl hEv hEs hlen (by omega)
    (hE 0 (by omega)) hok0 A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hcond : σ2.vars "ok" = 1 ↔ CondN arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondN
    rw [hSdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h
      have : S < arr.getD 0 0 := by omega
      rw [if_pos this] at h1
      exact absurd h1 (by decide)
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_neg (by omega)], h2⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassS arr) (if S < arr.getD 0 0 then 0 else 1) S; omega
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨hn, hpass⟩ : arr.getD 0 0 ≤ S ∧ ∀ k < S, PassS arr k := by
      have := hc; unfold CondN at this; rw [hSdef] at this; exact this
    have hctx : PCtx arr S σ2 :=
      ⟨A2, by rw [e2f "V3" (by decide)]; exact e1V3, by rw [e2f "A2" (by decide)]; exact e1A2,
        by rw [e2f "K7" (by decide)]; exact e1K7, by rw [e2f "K9" (by decide)]; exact e1K9,
        by rw [e2f "C" (by decide)]; exact e1C⟩
    obtain ⟨σ3, r3, o3⟩ := printSat_run (B := B) Sz arr S σ2 hs hctx hSdef (by omega) hn
      (by have := hSdef; unfold SlotsN at this; omega) hpass hlen hEv hEs hB
    have hK := KprintS_mono Sz S l (3 + 2 * arr.getD 0 0 + S) (3 + 3 * l) hl (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccS
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_pos hc]
  · have hno : ¬ CondN arr := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccS
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [e3o, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.SatAccept
