import Lax117284Proofs.Machine.SatAccept
import Lax117284Proofs.Machine.SatNk
import Lax117284Proofs.Machine.SatCong
import Lax117284Proofs.Machine.WrapTFinal
import Lax117284Proofs.Machine.BlockFinal

/-!
The reduction of Theorem 7 from [2,3]-bounded 3-satisfiability to the problem with three days and
the fairness parameter one is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.SatFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatCong
open Lax117284Proofs.Machine.SatAccept Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.BlockFinal Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)

open scoped Classical

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EF
  nk := SatNk.nkF
  Knk := 80
  hnk := fun B Bt cap hB => SatNk.nkF_spec (B := B) Bt cap hB
  red := Lax117284.Theorem7.reduce
  cond := fun ts => CondN (ts.map Tok.val)
  outW := fun ts => numCode (outNums (ts.map Tok.val))
  sem_acc := fun ts hc hcond => t7_eq ts hc hcond
  rejW := rejected
  sem_rej := fun w h => t7_rej w h
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptSat
  Kacc := KaccS
  Kmono := KaccS_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    obtain ⟨h3, hl, hsg⟩ := hshape
    have hlenns : (ts.map Tok.val).length = ts.length := by simp
    have harr' : arr.take (ts.map Tok.val).length = ts.map Tok.val := by rw [hlenns]; exact harr
    have hg := getD_eq_of_take harr'
    obtain ⟨S, hS⟩ : ∃ S, SlotsN (ts.map Tok.val) = S := ⟨_, rfl⟩
    rw [hS] at hl hsg
    have hAg : Agree arr (ts.map Tok.val) S := fun k hk => hg k (by omega)
    have hlenA : 3 + 2 * S ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hval : ∀ k < (ts.map Tok.val).length, (ts.map Tok.val).getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk)
      rw [← e]
      exact hvals t ht
    have hL3 : 3 ≤ L := by omega
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hP8 : 8 ≤ 2 ^ L := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL3
    have hPL : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    have hPP : 8 * 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ hP8
    have hE : ∀ k < 3 + 2 * S, arr.getD k 0 + 8 < B := by
      intro k hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hSl : SlotsN arr = S := by rw [hAg.slots]; exact hS
    have hn0 := hval 0 (by omega)
    have hSN : 2 * (ts.map Tok.val).getD 1 0 + 3 * (ts.map Tok.val).getD 2 0 = S := hS
    obtain ⟨σ', r, o⟩ := acceptSat_run (B := B) Sz ts.length arr σ hs hA (by rw [hSl]; exact hlenA)
      (by rw [hSl]; exact hE) (by rw [hSl]; omega) (by rw [hSl]; omega) (by
        rw [hAg.n, hAg.na, hAg.nb]; omega)
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    show _ = if CondN (ts.map Tok.val) then natBits (numCode (outNums (ts.map Tok.val)))
      else natBits rejected
    by_cases hc : CondN (ts.map Tok.val)
    · rw [if_pos hc, if_pos ((hAg.cond hS).2 hc), hAg.out hS, natBits_numCode]
    · rw [if_neg hc, if_neg (fun h => hc ((hAg.cond hS).1 h)), FreeMain.natBits_rejected]

/-- The scalars of the program. -/
def layoutS : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv",
    "n", "na", "nb", "A2", "t3", "N", "V3", "C", "K7", "K9", "ok", "o", "vo", "so", "cnt", "vj",
    "sj", "dy", "dv", "q1", "r1", "w", "h", "q2", "w5", "v", "s", "u", "i2", "ix", "aa", "M"],
    ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutS W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, SatNk.nkF,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptSat, prepSat, SatCheck.chkLoop, SatCheck.chkBody, SatRank.rankCom, SatRank.rankLoop,
    SatRank.rankBody, SatRank.bumpS, SatPrint.printSat, SatPrint.dayC, SatPrint.cellBody,
    SatDue.dueCom, SatDue.varCom, SatDue.slotCom,
    FreeAccept.rejectPrint, Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar,
    Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
    EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, layoutS, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 4000 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccS Sz l ≤ _
  unfold KaccS SatPrint.KprintS SatPrint.Kcell
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/--
---
conclusion: Lax117284.Theorem7.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the formula — the number of variables, the numbers of clauses of two and of three literals, and a
variable and a sign for every position —, a first pass checks, for every position, that its
variable is one of the formula's and that its literal has not occurred twice before it, which is a
loop over the earlier positions that counts, and a second pass writes the image, the due date of
every client on each of the three days being a case analysis on the number of the client that
counts, on the third day, the earlier positions with the same literal. The number of variables is
required not to exceed the number of positions, which keeps the image polynomial in the input. A
word that is not the code of such a formula is answered with the rejected word. The numbers may be
exponential in the length of the input, which the word length of a polynomial-time word RAM
accommodates, and polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Theorem7.reduce) :=
  WrapTFinal.polyTimeE W layoutS com_ok rfl (by simp [layoutS]) 4000 2 (by omega) Kpoly
    (fun Sz => by
      show 3 * (48 * Sz + 50) ≤ 4000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.SatFinal
