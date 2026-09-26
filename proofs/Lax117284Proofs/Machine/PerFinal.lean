import Lax117284Proofs.Machine.PerAccept
import Lax117284Proofs.Machine.BlockFinal

/-!
The reduction of Lemma 15 from per-client parameters to a uniform one is polynomial-time
computable.
-/

namespace Lax117284Proofs.Machine.PerFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.BlockCheck Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.PerCheck
open Lax117284Proofs.Machine.PerProg Lax117284Proofs.Machine.PerAccept Lax117284Proofs.Machine.Wrap
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.PNk Lax117284Proofs.Machine.BlockFinal

open scoped Classical

/-- The streams that are mapped to an image. -/
def condP (ns : List ℕ) : Prop := Valid ns ∧ ∀ j < ns.getD 0 0, paramAt ns j ≤ ns.getD 1 0

lemma cellLG_congr (arr ns : List ℕ) (n m dm t : ℕ)
    (h : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 = ns.getD k 0) :
    cellLG arr n m dm t = cellLG ns n m dm t := by
  unfold cellLG
  by_cases hb : t % (n + 2) < n
  · by_cases ha : t / (n + 2) < m
    · have hab := cell_lt ha hb
      rw [if_pos hb, if_pos ha, if_pos hb, if_pos ha, h _ (by omega), h _ (by omega)]
    · rw [if_pos hb, if_neg ha, if_pos hb, if_neg ha, h _ (by omega)]
  · rw [if_neg hb, if_neg hb]

theorem outPG_eq (arr ns : List ℕ) (hs : Shape eP ns) (h : arr.take ns.length = ns) :
    outPG arr = outLAll ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eP] at hl
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold outPG outLAll
  rw [h0, h1]
  by_cases hn : ns.getD 0 0 = 0
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    unfold outL outLG
    have hk : ∀ k < 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + ns.getD 0 0, arr.getD k 0 = ns.getD k 0 :=
      fun k hk => hg k (by omega)
    have hmax : runMaxD arr (ns.getD 1 0 * ns.getD 0 0) = dmaxOf ns := by
      unfold dmaxOf
      exact runMaxD_congr arr ns _ (fun j hj => hg _ (by
        have : ns.getD 0 0 ≥ 1 := by omega
        have h3 : j < ns.getD 1 0 * ns.getD 0 0 := hj
        omega))
    rw [hmax]
    have hcells : (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap
        (cellLG arr (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns))
        = (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap
          (cellLG ns (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns)) :=
      List.flatMap_congr fun t _ => cellLG_congr arr ns _ _ _ t hk
    rw [hcells]

theorem cond_iffP (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eP ns) :
    ((∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
      (∀ j < arr.getD 0 0, PassK arr (arr.getD 1 0) (2 * (arr.getD 1 0 * arr.getD 0 0)) j)) ↔
      condP ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eP] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  unfold condP
  rw [h0, h1]
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨fun t ht => ?_, fun j hj => ?_⟩
    · have := hp t ht
      unfold Pass at this
      rw [hg _ (by omega), hg _ (by omega)] at this
      exact this
    · have := hq j hj
      unfold PassK at this
      rw [hg _ (by omega)] at this
      exact this
  · rintro ⟨hv, hq⟩
    refine ⟨fun t ht => ?_, fun j hj => ?_⟩
    · have := hv t ht
      unfold Pass
      rw [hg _ (by omega), hg _ (by omega)]
      exact this
    · have := hq j hj
      unfold PassK
      rw [hg _ (by omega)]
      exact this

lemma KmonoP (Sz a b : ℕ) (h : a ≤ b) : KaccP Sz a ≤ KaccP Sz b := KaccP_mono Sz a b h

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eP
  Sh := Shape eP
  nk := PNk.nkP
  Knk := 60
  hnk := fun B Bt cap hB => PNk.nkP_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eP hs
  hshape := fun ts h => shape_of_conforms eP h
  red := Lax117284.Lemma15.reduce
  cond := condP
  outW := fun ns => numCode (outLAll ns)
  sem_acc := fun ns hs hc => per_eq ns hc.1 hs hc.2
  sem_rej := fun w h => per_rej w (by
    rintro ⟨ns, hw, hs, hv, hp⟩
    exact h ⟨ns, hw, hs, hv, hp⟩)
  rejW := rejected
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptP
  Kacc := KaccP
  Kmono := KmonoP
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    simp only [eP] at hl
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0,
        arr.getD k 0 + 16 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hmn : arr.getD 0 0 < 2 ^ (L + 1) := by rw [h0]; exact hval 0 (by omega)
    have hmm : arr.getD 1 0 < 2 ^ (L + 1) := by rw [h1]; exact hval 1 (by omega)
    have hl' : ns.length = 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 := by
      rw [h0, h1]; exact hl
    have hprod : (2 * arr.getD 1 0) * (arr.getD 0 0 + 2) ≤ (2 * 2 ^ (L + 1)) * (2 ^ (L + 1) + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hpp2 : (2 * 2 ^ (L + 1)) * (2 ^ (L + 1) + 2) = 8 * (2 ^ L * 2 ^ L) + 8 * 2 ^ L := by
      rw [hpow1]; ring
    have hrm : runMaxD arr (arr.getD 1 0 * arr.getD 0 0) ≤ 2 ^ (L + 1) := by
      refine foldl_max_le (fun j => arr.getD (2 + 2 * j + 1) 0) (2 ^ (L + 1)) _ 0 (Nat.zero_le _)
        (fun j hj => ?_)
      have hj' : j < arr.getD 1 0 * arr.getD 0 0 := hj
      have := hval (2 + 2 * j + 1) (by omega)
      rw [hg _ (by omega)]
      omega
    obtain ⟨σ', r, o⟩ := acceptP_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hA
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : condP ns
    · rw [if_pos hc, if_pos ((cond_iffP arr ns harr ⟨h2, hl⟩).2 hc), outPG_eq arr ns ⟨h2, hl⟩ harr,
        natBits_numCode]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffP arr ns harr ⟨h2, hl⟩).1 h)),
        FreeMain.natBits_rejected]


def layoutP : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "n1", "n2", "m2", "M2", "ca", "cb", "cs", "kj", "cr"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutP W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, PNk.nkP,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptP, prepP, print0L, printL, cellBodyL, newCell, Emit.emitCell,
    FreeAccept.rejectPrint, FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    parLoop, parBody, parChk, dmaxLoop, dmaxBody, dmaxChk,
    Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutP, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 5000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show KaccP Sz l ≤ _
  unfold KaccP KprintL KcellP
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l)]

/--
---
conclusion: Lax117284.Lemma15.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the numbers of the instance and its parameters, a first pass over the table checks that every job
takes some time and is not due before it starts, a second pass checks that no parameter exceeds
the number of days, a third finds the largest due date, and the numbers of the image are written
cell by cell, the closed form of every cell being computed from its row and column: the original
jobs on the original days, the private unit job of each client on each additional day, placed in
the stretch of the two new clients or after it according to its parameter, and the common job of
the two new clients. An instance without clients is answered with a fixed yes-instance, and a
word that is not the code of an admissible instance with the rejected word. The numbers may be
exponential in the length of the input, which the word length of a polynomial-time word RAM
accommodates, and polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Lemma15.reduce) :=
  WrapFinal.polyTime W layoutP com_ok rfl (by simp [layoutP]) 5000 Kpoly (fun Sz => by
    show 3 * (48 * Sz + 50) ≤ 5000 * (Sz + 1)
    omega)

end Lax117284Proofs.Machine.PerFinal
