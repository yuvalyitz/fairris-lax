import Lax117284Proofs.Machine.JitHardAccept
import Lax117284Proofs.Machine.JitHardNk
import Lax117284Proofs.Machine.WrapTFinal

/-!
The reduction from interval scheduling with eligible machine sets to just-in-time scheduling, as
a word RAM program on the zeros and ones of its input.
-/

namespace Lax117284Proofs.Machine.JitHardFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.JitHardFormat Lax117284Proofs.Machine.JitHardSem
open Lax117284Proofs.Machine.JitHardAccept Lax117284Proofs.Machine.JitHardNk
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan
open Lax117284Proofs.Machine.TokProg (Tok.val)

open scoped Classical

/-- The word every word that is not the code of a stream of the format is sent to. -/
def rejH : Word := numCode [1, 0, 1]

/-- The reduction, as a map on words: the image of a stream of the format, and the rejected
word for every other word. -/
noncomputable def redH (w : Word) : Word :=
  if h : ∃ ts, w = code ts ∧ Conforms EH ts then numCode (outH (h.choose.map Tok.val))
  else rejH

theorem redH_code (ts : List Tok) (hc : Conforms EH ts) :
    redH (code ts) = numCode (outH (ts.map Tok.val)) := by
  have h : ∃ ts', code ts = code ts' ∧ Conforms EH ts' := ⟨ts, rfl, hc⟩
  unfold redH
  rw [dif_pos h]
  obtain ⟨hw', hs'⟩ := h.choose_spec
  have hnn : h.choose = ts := by
    rw [← (accept_complete EH h.choose hs').2, ← hw']; exact (accept_complete EH ts hc).2
  rw [hnn]

theorem redH_rej (w : Word) (h : ¬ ∃ ts, w = code ts ∧ Conforms EH ts) : redH w = rejH := by
  unfold redH
  rw [dif_neg h]

lemma getD_eq_of_take' {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- The cost of the accepting phase. -/
def KaccW (Sz l : ℕ) : ℕ := 400 * (Sz + 1) * (l + 1) ^ 2

lemma KaccW_mono (Sz a b : ℕ) (h : a ≤ b) : KaccW Sz a ≤ KaccW Sz b := by
  unfold KaccW
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EH
  nk := nkH
  Knk := 100
  hnk := fun B Bt cap hB => nkH_spec (B := B) Bt cap hB
  red := redH
  cond := fun _ => True
  outW := fun ts => numCode (outH (ts.map Tok.val))
  sem_acc := fun ts hc _ => redH_code ts hc
  rejW := rejH
  sem_rej := fun w h => redH_rej w (fun ⟨ts, hw, hc⟩ => h ⟨ts, hw, hc, trivial⟩)
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o]; unfold rejH; rw [natBits_numCode]⟩
  acc := acceptH
  Kacc := KaccW
  Kmono := KaccW_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    obtain ⟨ns, hns⟩ : ∃ ns, ts.map Tok.val = ns := ⟨_, rfl⟩
    rw [hns] at hshape
    have hlenns : ns.length = ts.length := by rw [← hns]; simp
    have harr' : arr.take ns.length = ns := by rw [hlenns, ← hns]; exact harr
    have hg := getD_eq_of_take' harr'
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
    have hp1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hp2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hp3 : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hp4 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hlenL' : ns.length ≤ L := by omega
    have hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B := fun k hk => by
      have := hval k hk
      omega
    have hL : 4 * ns.length + 16 < B := by omega
    obtain ⟨σ', r, o⟩ := acceptH_run (B := B) Sz ns hshape hs hE hL σ
      (fun k hk => by rw [hA]; exact hg k hk) (by rw [hA]; exact hlenA)
    refine ⟨σ', r.mono ?_, ?_⟩
    · show KaccH Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0)) ≤ KaccW Sz ts.length
      unfold KaccW
      rw [← hlenns]
      have hshl := hshape.2.1
      exact KaccH_le Sz _ _ _ (by omega) (wallsN_le_len ns hshape)
    · rw [o, hns]
      simp [natBits_numCode]

/-- The scalars of the program. -/
def layoutH : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "nm",
    "n", "m", "Wl", "J", "o1", "o2", "jj", "kk", "bt", "pp", "dd", "v", "s", "u", "i2", "ix",
    "aa", "M"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutH W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, nkH,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptH, prepH, printH, JitHardLoop.cLoop, JitHardPrint.dueBody, JitHardPrint.rowBody,
    JitHardSem.cellBody, FreeAccept.rejectPrint, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutH, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 400 * (Sz + 1) * (l + 1) ^ 2 := fun _ _ => le_rfl

/-- **The reduction is a polynomial-time word RAM computation on the zeros and ones of its
input.** -/
theorem ramPolytime : Lax759944.RamPolytime.RamPolytime W.redBits :=
  WrapTFinal.ramPolytimeE W layoutH com_ok rfl (by simp [layoutH]) 400 2 (by omega) Kpoly
    (fun Sz => by
      show 3 * (48 * Sz + 50) ≤ 400 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.JitHardFinal
