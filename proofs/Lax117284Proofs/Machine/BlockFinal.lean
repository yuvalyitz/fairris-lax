import Lax117284Proofs.Machine.BlockAccept
import Lax117284Proofs.Machine.WrapFinal
import Lax117284Proofs.Machine.UNk

/-!
The reduction that adds a blocking client and a blocking day is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.BlockFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.BlockCheck Lax117284Proofs.Machine.BlockProg
open Lax117284Proofs.Machine.BlockAccept Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits

open scoped Classical

/-- The streams that are mapped to an image. -/
def condB (ns : List ℕ) : Prop := Valid ns ∧ 0 < ns.getD 1 0 ∧ paramOf ns = 1

lemma getD_eq_of_take {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

lemma runMaxD_congr (arr ns : List ℕ) (N : ℕ)
    (h : ∀ j < N, arr.getD (2 + 2 * j + 1) 0 = ns.getD (2 + 2 * j + 1) 0) :
    runMaxD arr N = runMaxD ns N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [runMaxD_succ, runMaxD_succ, ih (fun j hj => h j (by omega)), h N (by omega)]

lemma cellG_congr (arr ns : List ℕ) (n m bd t : ℕ) (hm : 0 < m)
    (h : ∀ k < 3 + 2 * (m * n), arr.getD k 0 = ns.getD k 0) :
    cellG arr n m bd t = cellG ns n m bd t := by
  unfold cellG
  by_cases hb : t % (n + 1) < n
  · have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n hm
    by_cases ha : t / (n + 1) < m
    · have hab := cell_lt ha hb
      rw [if_pos hb, if_pos ha, if_pos hb, if_pos ha, h _ (by omega), h _ (by omega)]
    · rw [if_pos hb, if_neg ha, if_pos hb, if_neg ha, h _ (by omega)]
  · rw [if_neg hb, if_neg hb]

theorem outBlockG_eq (arr ns : List ℕ) (hs : Shape eU ns) (h : arr.take ns.length = ns)
    (hm : 0 < ns.getD 1 0) : outBlockG arr = outBlockAll ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold outBlockG outBlockAll
  rw [h0, h1]
  by_cases hn : ns.getD 0 0 = 0
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    unfold outG outBlock
    have hk : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0 :=
      fun k hk => hg k (by omega)
    have hmax : runMaxD arr (ns.getD 1 0 * ns.getD 0 0) = dmaxOf ns := by
      unfold dmaxOf
      exact runMaxD_congr arr ns _ (fun j hj => hg _ (by omega))
    rw [hmax]
    have hcells : (List.range ((ns.getD 1 0 + 1) * (ns.getD 0 0 + 1))).flatMap
        (cellG arr (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns + 1))
        = (List.range ((ns.getD 1 0 + 1) * (ns.getD 0 0 + 1))).flatMap (cellB ns) :=
      List.flatMap_congr fun t _ => by
        rw [cellB_eq]
        exact cellG_congr arr ns _ _ _ t hm hk
    rw [hcells]

theorem cond_iff (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns) :
    (0 < arr.getD 1 0 ∧ paramOf arr = 1 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ↔
      condB ns := by
  have hg := getD_eq_of_take h
  have h1 := FreeMain.cond_iff arr ns h hs
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [hg 0 (by omega), hg 1 (by omega)]
    exact hg _ (by omega)
  unfold condB
  rw [hpar]
  constructor
  · rintro ⟨hm, hp, hall⟩
    obtain ⟨hm', hv⟩ := h1.1 ⟨hm, hall⟩
    exact ⟨hv, hm', hp⟩
  · rintro ⟨hv, hm, hp⟩
    obtain ⟨hm', hall⟩ := h1.2 ⟨hm, hv⟩
    exact ⟨hm', hp, hall⟩

lemma Kmono' (Sz a b : ℕ) (h : a ≤ b) : Kacc Sz a ≤ Kacc Sz b := by
  unfold Kacc
  have := Kprint_mono Sz (4 * a) (4 * b) (by omega)
  omega

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := Lax117284.Corollary8.reduceBlockingDay
  cond := condB
  outW := fun ns => numCode (outBlockAll ns)
  sem_acc := fun ns hs hc => block_eq ns hc.1 hs hc.2.1 hc.2.2
  sem_rej := fun w h => block_rej w (by
    rintro ⟨ns, hw, hs, hv, hm, hp⟩
    exact h ⟨ns, hw, hs, hv, hm, hp⟩)
  rejW := rejected
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptBlock
  Kacc := Kacc
  Kmono := Kmono'
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
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 16 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hmn : ns.getD 0 0 < 2 ^ (L + 1) := hval 0 (by omega)
    have hmm : ns.getD 1 0 < 2 ^ (L + 1) := hval 1 (by omega)
    have hprod : (ns.getD 1 0 + 1) * (ns.getD 0 0 + 1) ≤ 2 ^ (L + 1) * 2 ^ (L + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hpp2 : 2 ^ (L + 1) * 2 ^ (L + 1) = 4 * (2 ^ L * 2 ^ L) := by ring
    obtain ⟨σ', r, o⟩ := acceptBlock_run (B := B) Sz arr σ hs hE
      (by rw [h0, h1]; omega) (by rw [h0, h1]; omega)
      (by rw [h0, h1]; omega) (by rw [h0, h1]; omega) hA
    have hK : Kacc Sz (arr.getD 1 0 * arr.getD 0 0) ≤ Kacc Sz ns.length := Kmono' _ _ _ (by
      rw [h0, h1]; omega)
    refine ⟨σ', r.mono hK, ?_⟩
    rw [o]
    congr 1
    by_cases hc : condB ns
    · rw [if_pos hc, if_pos ((cond_iff arr ns harr ⟨h2, hl⟩).2 hc),
        outBlockG_eq arr ns ⟨h2, hl⟩ harr hc.2.1, natBits_numCode]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iff arr ns harr ⟨h2, hl⟩).1 h)),
        FreeMain.natBits_rejected]


def layoutB : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "n1", "M1", "bd", "ca", "cb", "cs"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutB W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptBlock, prepB, print0, printBlock, cellBody, Emit.emitCell,
    FreeAccept.rejectPrint, FreeCheck.okLoop,
    FreeCheck.okBody, FreeCheck.okChk, dmaxLoop, dmaxBody, dmaxChk,
    Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutB, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 2000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show Kacc Sz l ≤ _
  unfold Kacc Kprint Kcell
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l)]

/--
---
conclusion: Lax117284.Corollary8.reduceBlockingDay_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer
reads the numbers of the instance, a first pass over the table checks that every job takes
some time and is not due before it starts, and that the parameter is one, a second pass finds
the largest due date, and the numbers of the output are written cell by cell, the closed form of
every cell of the new table being computed from its row and column. An instance without clients
is answered with the instance without clients and one more day, and a word that is not the code
of such an instance is answered with the rejected word. The numbers may be exponential in the
length of the input, which the word length of a polynomial-time word RAM accommodates, and
polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduceBlockingDay_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Corollary8.reduceBlockingDay) :=
  WrapFinal.polyTime W layoutB com_ok rfl (by simp [layoutB]) 2000 Kpoly (fun Sz => by
    show 3 * (48 * Sz + 50) ≤ 2000 * (Sz + 1)
    omega)

end Lax117284Proofs.Machine.BlockFinal
