import Lax117284Proofs.Machine.JitAccept
import Lax117284Proofs.Machine.JNk
import Lax117284Proofs.Machine.WrapFinal
import Lax117284Proofs.Machine.BlockFinal

/-!
The reduction of Theorem 11 from just-in-time scheduling on unrelated machines to the problem with
day-independent due dates is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.JitFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitPass Lax117284Proofs.Machine.JitAccept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.Machine.TokModel

open scoped Classical

lemma sub_div_mul (t n : ℕ) : t - t / n * n = t % n := by
  have := Nat.mod_def t n
  rw [Nat.mul_comm]; omega

theorem outJG_eq (arr ns : List ℕ) (hs : ShapeJ ns) (h : arr.take ns.length = ns) :
    outJG arr (arr.getD 0 0) (arr.getD 1 0) = outJ ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold outJG outJ
  rw [h0, h1]
  congr 2
  refine List.flatMap_congr fun t ht => ?_
  have ht' := List.mem_range.mp ht
  have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht'; simp at ht')
  have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
  have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
    Nat.pos_of_ne_zero (fun h => by rw [h] at ht'; simp at ht'))
  rw [sub_div_mul, hg (2 + ns.getD 0 0 + t) (by omega), hg (2 + t % ns.getD 0 0) (by omega)]

theorem cond_iffJ (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : ShapeJ ns) :
    (∀ t < arr.getD 1 0 * arr.getD 0 0, PassJ arr (arr.getD 0 0) t) ↔ ValidJ ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold ValidJ
  rw [h0, h1]
  constructor
  · intro hp t ht
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht)
    have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
      Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht))
    have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have := hp t ht
    unfold PassJ at this
    rw [sub_div_mul, hg _ (by omega), hg _ (by omega)] at this
    exact this
  · intro hv t ht
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht)
    have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
      Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht))
    have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have := hv t ht
    unfold PassJ
    rw [sub_div_mul, hg _ (by omega), hg _ (by omega)]
    exact this

lemma KmonoJ (Sz a b : ℕ) (h : a ≤ b) : KaccJ Sz a ≤ KaccJ Sz b := KaccJ_mono Sz a b h

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EJ
  Sh := ShapeJ
  nk := JNk.nkJ
  Knk := 60
  hnk := fun B Bt cap hB => JNk.nkJ_spec (B := B) Bt cap hB
  hconf := fun ns hs => conformsJ_of_shape hs
  hshape := fun ts h => shapeJ_of_conforms h
  red := Lax117284.Theorem11.reduce
  cond := ValidJ
  outW := fun ns => numCode (outJ ns)
  sem_acc := fun ns hs hc => t11_eq ns hc hs
  rejW := rejected
  sem_rej := fun w h => t11_rej w (by
    rintro ⟨ns, hw, hs, hv⟩
    exact h ⟨ns, hw, hs, hv⟩)
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptJ
  Kacc := KaccJ
  Kmono := KmonoJ
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hl' : ns.length = 2 + (arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0) := by
      rw [h0, h1]; exact hl
    have hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B :=
      fun k hk => by
        rw [hg k (by omega)]
        have := hval k (by omega)
        omega
    obtain ⟨σ', r, o⟩ := acceptJ_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) hA
    have hK : KaccJ Sz ns.length ≤ KaccJ Sz ns.length := le_rfl
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : ValidJ ns
    · rw [if_pos hc, if_pos ((cond_iffJ arr ns harr ⟨h2, hl⟩).2 hc)]
      show numBits (outJG arr (arr.getD 0 0) (arr.getD 1 0)) = natBits (numCode (outJ ns))
      rw [natBits_numCode, outJG_eq arr ns ⟨h2, hl⟩ harr]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffJ arr ns harr ⟨h2, hl⟩).1 h)),
        FreeMain.natBits_rejected]

def layoutJ : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "o", "q", "tt", "jj", "ip", "ij", "pv", "dv"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutJ W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, JNk.nkJ,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptJ, prepJ, printJ, JitPrint.cellPrint, JitCheck.cellIdx, jokLoop, jokBody, jokChk,
    FreeAccept.rejectPrint, Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutJ, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 1000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show KaccJ Sz l ≤ _
  unfold KaccJ KprintJ JitPrint.KcellJ
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l)]

/--
---
conclusion: Lax117284.Theorem11.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the numbers of the instance — the counts, the due dates and the processing times machine by
machine —, a pass over the table of processing times checks that every job takes some time and is
not due before it starts, and the numbers of the image are written cell by cell, each cell being
the processing time of its job on its machine and the due date of that job, found from the cell's
index by division. The counts are the same, and the parameter is `1`. A word that is not the code
of an instance is answered with the rejected word. The numbers may be exponential in the length
of the input, which the word length of a polynomial-time word RAM accommodates, and polynomial
time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Theorem11.reduce) :=
  WrapFinal.polyTime W layoutJ com_ok rfl (by simp [layoutJ]) 1000 Kpoly (fun Sz => by
    show 3 * (48 * Sz + 50) ≤ 1000 * (Sz + 1)
    omega)

end Lax117284Proofs.Machine.JitFinal
