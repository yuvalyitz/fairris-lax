import Lax117284Proofs.McisHard.Machine.FinalStruct

/-!
# The Layout of the Reduction to `H` (WP9, Part 2)

The 90 scalars of the program and the two arrays; `Com.Ok`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.SatAccept
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc Lax117284Proofs.McisHard.Print
open Lax117284Proofs.McisHard.Bit

/-- The scalars of the program and its arrays. -/
def layoutM : Layout :=
  ⟨["L", "rt", "rv", "Ln", "ph", "val", "pw", "i", "T", "kind", "j", "n3", "p", "c", "tv", "n", "na",
    "nb", "A2", "t3", "N", "V3", "C", "K7", "K9", "ok", "o", "vo", "so", "cnt", "vj", "sj", "pK", "pM",
    "pV", "v", "s", "u", "i2", "w", "w2", "bTi", "bTu", "bTj", "bTv", "bt", "bTn", "bTo", "bTr",
    "bTo2", "bTr2", "ba", "bb", "bpe", "bk1", "bk2", "bv1", "bs1", "bv2", "bs2", "bc", "bTx", "bTq",
    "bTt", "bj", "bu", "bs", "bq1", "bx", "by", "bz", "bm", "bd0", "bTqa", "bTta", "bg", "bg2", "bE1",
    "bE2", "bE", "bcd", "bd", "bTg", "bjp", "bF1", "bF2", "bF", "bl", "br1", "bTl"],
    ["a", "TK"], 12⟩

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 100000 in
theorem com_ok : Com.Ok layoutM W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, SatNk.nkF,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    accMcis, prepSat, SatCheck.chkLoop, SatCheck.chkBody, SatRank.rankCom, SatRank.rankLoop,
    SatRank.rankBody, SatRank.bumpS, printCom, hdrCom, matCom, rowCom, rowBody,
    FoldLoop.fLoop, bitCom, treeCom, compCom, cidCom, clauseCom, gadCom, peCom, linkCom, coCntCom,
    unmatchedCom, gadTest, gadChain, unmLeaf, slotDecode, posSlot, gadBlock, linkBlock, slotDec, slotSlot,
    Out.emitVar, EmitNat.emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
    EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, layoutM, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

end Lax117284Proofs.McisHard.Final
