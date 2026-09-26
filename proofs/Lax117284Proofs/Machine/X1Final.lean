import Lax117284Proofs.Machine.X1Accept
import Lax117284Proofs.Machine.T9Final

/-!
The reduction of the tractable parameters to 2-satisfiability is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.X1Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Accept
open Lax117284Proofs.Machine.T9Final Lax117284Proofs.Machine.X1Sem Lax117284Proofs.Machine.X1Print
open Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.X1Word

open scoped Classical

theorem outX_congr (arr ns : List ℕ)
    (h : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0) :
    outX arr = outX ns := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [h0, h1]
    exact h _ (by omega)
  unfold outX
  rw [hpar, h0, h1]
  by_cases a : paramOf ns + 1 = ns.getD 1 0
  · rw [if_pos a, if_pos a]
    exact outT9_congr arr ns _ _ (fun k hk => h k (by omega))
  · by_cases b : paramOf ns = ns.getD 1 0
    · rw [if_neg a, if_neg a, if_pos b, if_pos b]
      unfold outU
      have : (List.range (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0)).flatMap
          (clW arr (ns.getD 0 0) (ns.getD 1 0)) =
          (List.range (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0)).flatMap
          (clW ns (ns.getD 0 0) (ns.getD 1 0)) :=
        List.flatMap_congr fun c _ => by
          unfold clW
          rw [clauseG_congr arr ns _ _ c (fun k hk => h k (by omega))]
      rw [this]
    · rw [if_neg a, if_neg a, if_neg b, if_neg b]

theorem cond_iffX (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns) :
    ((∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
      (paramOf arr = 0 ∨ paramOf arr + 1 = arr.getD 1 0 ∨ paramOf arr = arr.getD 1 0)) ↔
      condX ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [h0, h1]
    exact hg _ (by omega)
  unfold condX
  rw [hpar, h0, h1]
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨fun t ht => ?_, hq⟩
    have := hp t ht
    unfold Pass at this
    rw [hg _ (by omega), hg _ (by omega)] at this
    exact this
  · rintro ⟨hv, hq⟩
    refine ⟨fun t ht => ?_, hq⟩
    have := hv t ht
    unfold Pass
    rw [hg _ (by omega), hg _ (by omega)]
    exact this

lemma KmonoX (Sz a b : ℕ) (h : a ≤ b) : KaccX Sz a ≤ KaccX Sz b := KaccX_mono Sz a b h

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceX
  cond := condX
  outW := outX
  sem_acc := fun ns hs hc => tX_eq ns hc.1 hs hc.2
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w h => tX_rej w h
  rej := rejT9
  Krej := Krej9
  rejRun := fun B Sz σ hs hB => rejT9_run (B := B) Sz σ hs hB
  acc := acceptX
  Kacc := KaccX
  Kmono := KmonoX
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    simp only [eU] at hl
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hLt : L < 2 ^ L := Nat.lt_two_pow_self
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hn : arr.getD 0 0 < 2 ^ (L + 1) := by rw [h0]; exact hval 0 (by omega)
    have hm : arr.getD 1 0 < 2 ^ (L + 1) := by rw [h1]; exact hval 1 (by omega)
    have hl' : ns.length = 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) := by rw [h0, h1]; omega
    have hmnL : arr.getD 1 0 * arr.getD 0 0 < 2 ^ L := by omega
    have hnn : arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hn.le hn.le
    have hmm : arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hm.le hm.le
    have hpp2 : 2 ^ (L + 1) * 2 ^ (L + 1) = 4 * (2 ^ L * 2 ^ L) := by ring
    have hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ L * 2 ^ (L + 1) :=
      Nat.mul_le_mul hmnL.le hn.le
    have hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ L * 2 ^ (L + 1) := by
      rw [Nat.mul_comm (arr.getD 0 0) (arr.getD 1 0)]
      exact Nat.mul_le_mul hmnL.le hm.le
    have hpp3 : 2 ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
    have htq : arr.getD 0 0 * arr.getD 1 0 ≤ 2 ^ L := by
      rw [Nat.mul_comm]; omega
    -- the cost bounds
    have hlm : arr.getD 1 0 * arr.getD 0 0 ≤ ns.length := by omega
    have hl1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ ns.length * ns.length := by
      rcases Nat.eq_zero_or_pos (arr.getD 1 0) with hm0 | hm0
      · rw [hm0]; simp
      · have : arr.getD 0 0 ≤ arr.getD 1 0 * arr.getD 0 0 := Nat.le_mul_of_pos_left _ hm0
        exact Nat.mul_le_mul hlm (by omega)
    have hl2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ ns.length * ns.length := by
      rcases Nat.eq_zero_or_pos (arr.getD 0 0) with hn0 | hn0
      · rw [hn0]; simp
      · have : arr.getD 1 0 ≤ arr.getD 1 0 * arr.getD 0 0 := Nat.le_mul_of_pos_right _ hn0
        rw [Nat.mul_comm (arr.getD 0 0) (arr.getD 1 0)]
        exact Nat.mul_le_mul hlm (by omega)
    obtain ⟨σ', r, o⟩ := acceptX_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hl1 hl2 hlm hA
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : condX ns
    · rw [if_pos hc, if_pos ((cond_iffX arr ns harr ⟨h2, hl⟩).2 hc)]
      congr 1
      rw [outX_congr arr ns (fun k hk => hg k (by omega))]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffX arr ns harr ⟨h2, hl⟩).1 h))]

def layoutX : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "k1", "nn", "mm", "V1", "C1", "C2", "CC", "tq", "ci", "cr", "j1", "j2", "tt", "x1", "x2", "pa",
    "da", "pb", "db", "cj", "r2", "i1", "CU"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutX W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptX, fixOk, printZ, prepT, rejT9, T9Print.printT9, printU, bodyU, body1, body2, comp1,
    T9Comp2.comp2, br1, br2, T9Ops.emitClause,
    FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, layoutX, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 30000 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccX Sz l ≤ _
  unfold KaccX KaccT T9Print.KprintT K1 Krej9
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/-- **The reduction of the tractable parameters to 2-satisfiability is polynomial-time
computable.** -/
theorem reduceX_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceX) :=
  WrapFinal.polyTimeE W layoutX com_ok rfl (by simp [layoutX]) 30000 2 (by omega) Kpoly
    (fun Sz => by
      show 6 * (48 * Sz + 50) + 20 ≤ 30000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.X1Final
