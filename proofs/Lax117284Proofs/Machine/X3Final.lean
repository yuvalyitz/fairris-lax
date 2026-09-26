import Lax117284Proofs.Machine.X3Accept
import Lax117284Proofs.Machine.X1Final

/-!
The reduction to 2-satisfiability that decides day-independent due dates and processing times is
polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.X3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Accept
open Lax117284Proofs.Machine.T9Final Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.X3Sem Lax117284Proofs.Machine.X3Loop Lax117284Proofs.Machine.X3Accept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.X3Word

open scoped Classical

/-- **The check reads only the table and the parameter.** -/
theorem cond_iffD (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns) :
    ((∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧ DI arr ∧
        paramOf arr * omegaS arr ≤ arr.getD 1 0) ↔ goodD ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [h0, h1]
    exact hg _ (by omega)
  have hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0 :=
    fun k hk => hg k (by omega)
  have hdi : DI arr ↔ DI ns := by
    unfold DI
    rw [h0, h1]
    constructor
    · intro hd t ht
      have := hd t ht
      have hn : 0 < ns.getD 0 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 0 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hm : 0 < ns.getD 1 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 1 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm
      have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
      rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)] at this
      exact this
    · intro hd t ht
      have := hd t ht
      have hn : 0 < ns.getD 0 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 0 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hm : 0 < ns.getD 1 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 1 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm
      have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
      rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)]
      exact this
  have hom : omegaS arr = omegaS ns := by
    unfold omegaS
    rw [h0, h1]
    by_cases hm : ns.getD 1 0 = 0
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm]
      have hm' : 0 < ns.getD 1 0 := Nat.pos_of_ne_zero hm
      unfold omegaN
      rw [h0]
      refine foldl_max_congr _ _ (fun j hj => ?_)
      have hj' := List.mem_range.1 hj
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm'
      unfold cntN
      rw [h0]
      refine List.countP_congr (fun j' hj'' => ?_)
      have hj3 := List.mem_range.1 hj''
      unfold sRow
      rw [hag (3 + 2 * j) (by omega), hag (2 + 2 * j) (by omega), hag (3 + 2 * j') (by omega),
        hag (2 + 2 * j') (by omega)]
  unfold goodD Valid
  rw [hpar, h0, h1, hom, hdi]
  constructor
  · rintro ⟨hp, hd, hk⟩
    refine ⟨fun t ht => ?_, hd, hk⟩
    have := hp t ht
    unfold Pass at this
    rw [hg _ (by omega), hg _ (by omega)] at this
    exact this
  · rintro ⟨hv, hd, hk⟩
    refine ⟨fun t ht => ?_, hd, hk⟩
    have := hv t ht
    unfold Pass
    rw [hg _ (by omega), hg _ (by omega)]
    exact this

lemma KmonoD (Sz a b : ℕ) (h : a ≤ b) : KaccD Sz a ≤ KaccD Sz b := KaccD_mono Sz a b h

lemma encode_sat : Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF =
    encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, Lax117284Proofs.X1Word.satF]

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceD
  cond := goodD
  outW := fun _ => encodeNat 1 ++ encodeNat 0
  sem_acc := fun ns hs hc => by
    have hmem : numCode ns ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) :=
      (uniform_iff_good _).2 ⟨ns, rfl, hs, hc⟩
    unfold reduceD
    rw [if_pos hmem, encode_sat]
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w h => by
    have hnot : w ∉ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) := fun hm => by
      obtain ⟨ns, hw, hs, hg⟩ := (uniform_iff_good w).1 hm
      exact h ⟨ns, hw, hs, hg⟩
    unfold reduceD
    rw [if_neg hnot]
  rej := rejT9
  Krej := Krej9
  rejRun := fun B Sz σ hs hB => rejT9_run (B := B) Sz σ hs hB
  acc := acceptD
  Kacc := KaccD
  Kmono := KmonoD
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
    have hkp : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 < 2 ^ (L + 1) := by
      rw [hg _ (by omega)]; exact hval _ (by omega)
    have hkn : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 * arr.getD 0 0 ≤
        2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hkp.le hn.le
    have hlm : arr.getD 1 0 * arr.getD 0 0 ≤ ns.length := by omega
    obtain ⟨σ', r, o⟩ := acceptD_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hlm hA
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : goodD ns
    · rw [if_pos hc, if_pos ((cond_iffD arr ns harr ⟨h2, hl⟩).2 hc)]
      simp only [T9Comp1.natBits_app, natBits_encodeNat]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffD arr ns harr ⟨h2, hl⟩).1 h))]

theorem com_ok : Com.Ok X1Final.layoutX W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptD, fixOk, printZ, prepT, rejT9, decCom, omegaCom, maxCom, outerBody, cntCom, innerBody,
    diCom, diBody, FoldLoop.fLoop, SatRank.bumpS,
    FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, X1Final.layoutX, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 2000 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccD Sz l ≤ _
  unfold KaccD Kmax Krej9
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/-- **The reduction is polynomial-time computable.** -/
theorem reduceD_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceD) :=
  WrapFinal.polyTimeE W X1Final.layoutX com_ok rfl (by simp [X1Final.layoutX]) 2000 2 (by omega)
    Kpoly (fun Sz => by
      show 6 * (48 * Sz + 50) + 20 ≤ 2000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.X3Final
