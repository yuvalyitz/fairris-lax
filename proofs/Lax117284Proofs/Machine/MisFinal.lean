import Lax117284Proofs.Machine.MisBound
import Lax117284Proofs.Machine.MisCong
import Lax117284Proofs.Machine.MisNk
import Lax117284Proofs.Machine.WrapTFinal

/-!
The reduction of Lemma 14 from the multicoloured independent set problem to the problem with the
fairness parameter of every client given is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.MisFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.MisFormat Lax117284Proofs.Machine.MisSem Lax117284Proofs.Machine.MisCong
open Lax117284Proofs.Machine.MisRun Lax117284Proofs.Machine.MisBound Lax117284Proofs.Machine.MisAccept
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)

open scoped Classical

lemma getD_eq_of_take' {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- The cost of the accepting phase. -/
def KaccM (Sz l : ℕ) : ℕ := 30000 * (Sz + 1) * (l + 1) ^ 3

lemma KaccM_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM Sz a ≤ KaccM Sz b := by
  unfold KaccM
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EM
  nk := MisNk.nkM
  Knk := 80
  hnk := fun B Bt cap hB => MisNk.nkM_spec (B := B) Bt cap hB
  red := Lax117284.Lemma14.reduce
  cond := fun ts => CondM (ts.map Tok.val)
  outW := fun ts => numCode (outM (ts.map Tok.val))
  sem_acc := fun ts hc hcond => t14_eq ts hc hcond
  rejW := rejectedPerClient
  sem_rej := fun w h => t14_rej w h
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, rejectedPerClient_eq, FreeMain.natBits_rejected]⟩
  acc := acceptM
  Kacc := KaccM
  Kmono := KaccM_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    obtain ⟨ns, hns⟩ : ∃ ns, ts.map Tok.val = ns := ⟨_, rfl⟩
    rw [hns] at hshape
    have hlenns : ns.length = ts.length := by rw [← hns]; simp
    have harr' : arr.take ns.length = ns := by rw [hlenns, ← hns]; exact harr
    have hg := getD_eq_of_take' harr'
    obtain ⟨h2, hl, hsg⟩ := hshape
    have hshape' : ShapeM ns := ⟨h2, hl, hsg⟩
    have hAg : AgrM arr ns := fun k hk => hg k (by omega)
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      have hk' : k < (ts.map Tok.val).length := by rw [hns]; exact hk
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk')
      have : (ts.map Tok.val)[k] = ns[k] := by simp [hns]
      rw [← this, ← e]
      exact hvals t ht
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := accept_bounds ns B L hshape' (by omega) hval hB
    have hVM := VM_cong hAg
    have hlN := lN_cong hAg
    have hnN := nN_cong hAg
    have hcond := CondM_cong hAg
    have hE : ∀ k < VM arr * VM arr, arr.getD (2 + k) 0 + 8 < B := by
      intro k hk
      rw [hVM] at hk
      rw [hAg (2 + k) (by omega)]
      exact b1 k hk
    obtain ⟨σ', r, o⟩ := acceptM_run (B := B) Sz arr σ hs hA (by rw [hVM]; omega) hE
      (by rw [hlN]; exact b2) (by rw [hnN]; exact b3)
      (by rw [hVM, hnN]; exact b4) (by rw [hVM, hlN]; exact b5)
      (fun hc => by
        have := b6 (hcond.1 hc)
        rw [Mag_cong hAg]; exact this)
      (fun hc => by
        have := b7 (hcond.1 hc)
        rw [daysN_cong hAg, clN_cong hAg]; exact this)
    refine ⟨σ', r.mono ?_, ?_⟩
    · show Kreal Sz (VM arr) (VM arr * VM arr) (if CondM arr then daysN arr * clN arr else 0)
          (if CondM arr then clN arr else 0) ≤ KaccM Sz ts.length
      unfold KaccM
      rw [← hlenns, hVM]
      have h1 := VM_le_len hshape'
      have h3 := VV_le_len hshape'
      by_cases hc : CondM arr
      · simp only [if_pos hc]
        rw [daysN_cong hAg, clN_cong hAg]
        have h4 : 4 ≤ nN ns := ((hcond.1 hc).1)
        have hd := daysN_le hshape' h4
        have hcl := clN_le hshape' h4
        exact Kreal_le Sz ns.length (VM ns) (VM ns * VM ns) _ _ h1 rfl h3
          (le_trans (Nat.mul_le_mul hd hcl) (by nlinarith)) (by omega)
      · simp only [if_neg hc]
        exact Kreal_le Sz ns.length (VM ns) (VM ns * VM ns) 0 0 h1 rfl h3 (by omega) (by omega)
    · rw [o]
      congr 1
      show _ = if CondM (ts.map Tok.val) then natBits (numCode (outM (ts.map Tok.val)))
        else natBits rejectedPerClient
      rw [hns]
      by_cases hc : CondM ns
      · rw [if_pos (hcond.2 hc), if_pos hc, outM_cong hAg, natBits_numCode]
      · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc, rejectedPerClient_eq,
          FreeMain.natBits_rejected]

/-- The scalars of the program. -/
def layoutM : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "v", "s", "u", "i2", "ix", "aa", "M", "B3", "B4", "CC", "DC", "DD", "E2", "EE", "LB", "S2", "V", "VV", "bd", "bs", "ca", "cb", "cc", "cnt", "dg", "di", "dm", "dn", "dv", "e", "eh", "em", "ee", "fm", "fq", "fr", "fw", "fw2", "k1", "k2", "lc", "ma", "nn", "nn1", "ok", "pv", "qa", "ra", "rb", "rr", "ta", "tb", "va", "vb", "xa", "xf", "xj", "ya"],
    ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutM W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, MisNk.nkM,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptM, prepM, postM, dgM, postTail, MisPrint.printM, MisPrint.cellBody, MisPrint.kvBody,
    MisChk.checkCom, MisChk.checkPA, MisChk.checkPB, MisCheck.guard, MisCheck.impGuard,
    MisCheck.chkA, MisCheck.chkALoop, MisCheck.chkB, MisCheck.chkBLoop,
    MisCount.cntCom, MisCount.cntLoop, MisCount.cntBody,
    MisFind.findCom, MisFind.findLoop, MisFind.findBody,
    MisJob.jobCom, MisJob.pdCom, MisJob.vertexCom, MisJob.validCom, MisJob.validNext,
    MisJob.edgeDisp, MisJob.edgeCom,
    FreeAccept.rejectPrint, Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar,
    Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
    EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, layoutM, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 30000 * (Sz + 1) * (l + 1) ^ 3 := by
  intro Sz l
  show KaccM Sz l ≤ _
  exact le_refl _

/--
---
conclusion: Lax117284.Lemma14.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the number of colours, the number of vertices per colour, and the bits of the adjacency matrix; a
first pass over the matrix checks that it is symmetric, has no loop and no edge inside a colour
class; a second checks that the graph is regular of a positive degree and has an even number of
edges, by counting the neighbours of every vertex; and the numbers of the image are then written
cell by cell, the processing time and the due date of each job being a closed form computed from
its day and its client: a case analysis on the kind of day — a vertex day, a validation day or the
day of an edge, whose endpoints are found by scanning the matrix for the corresponding edge — and
on the kind of client. The number of colours and the number of vertices are numbers of the input
and are bounded by its length, since the image is only written for a graph. A word that is not the
code of such a graph is answered with the rejected word. The numbers may be exponential in the
length of the input, which the word length of a polynomial-time word RAM accommodates, and
polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Lemma14.reduce) :=
  WrapTFinal.polyTimeE W layoutM com_ok rfl (by simp [layoutM]) 30000 3 (by omega) Kpoly
    (fun Sz => by
      show 3 * (48 * Sz + 50) ≤ 30000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.MisFinal
