import Lax117284Proofs.Machine.TsRenAccept
import Lax117284Proofs.Machine.TsRenNk
import Lax117284Proofs.Machine.WrapTFinal

/-!
The renaming reduction from the 2-CNF formulas of the scheduling submission into the 2-SAT of
`lax-429075` is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.TsRenFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434930.PolynomialTime
open Lax117284Proofs.Machine.TsRenFormat Lax117284Proofs.Machine.TsRenSem
open Lax117284Proofs.Machine.TsRenAccept Lax117284Proofs.Machine.TsRenLit
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)
open Lax117284Proofs.TwoSatRename

open scoped Classical

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := ER
  nk := TsRenNk.nkR
  Knk := 80
  hnk := fun B Bt cap hB => TsRenNk.nkR_spec (B := B) Bt cap hB
  red := reduceR
  cond := fun ts => CondR (ts.map Tok.val)
  outW := fun ts => outW (ts.map Tok.val)
  sem_acc := fun ts hc hcond => ren_eq ts hc hcond
  rejW := rejW
  sem_rej := fun w h => ren_rej w h
  rej := rejR
  Krej := fun _ => 6
  rejRun := fun B _ σ _ hB => by
    obtain ⟨σ', r, o⟩ := rejR_run (B := B) σ (by omega)
    exact ⟨σ', r, by rw [o, natBits_rejW]⟩
  acc := acceptR
  Kacc := fun _ l => KaccR l
  Kmono := fun _ a b h => KaccR_mono a b h
  accRun := fun B _ L ts arr σ hconf harr hA hlenL hvals hB _ => by
    obtain ⟨hshape, -⟩ := shape_of_conforms hconf
    obtain ⟨h2, hl, hsg⟩ := hshape
    have hlenns : (ts.map Tok.val).length = ts.length := by simp
    have harr' : arr.take (ts.map Tok.val).length = ts.map Tok.val := by rw [hlenns]; exact harr
    have hg : ∀ k < (ts.map Tok.val).length, arr.getD k 0 = (ts.map Tok.val).getD k 0 := by
      intro k hk
      conv_rhs => rw [← harr']
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
    have hval : ∀ k < (ts.map Tok.val).length, (ts.map Tok.val).getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk)
      rw [← e]
      exact hvals t ht
    obtain ⟨S, hS⟩ : ∃ S, PosN (ts.map Tok.val) = S := ⟨_, rfl⟩
    rw [hS] at hl hsg
    have hPa : PosN arr = S := by
      unfold PosN at hS ⊢; rw [hg 1 (by omega)]; exact hS
    have hlenA : 2 + 2 * S ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hpow : (2 : ℕ) ^ (L + 1) ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hE : ∀ k < 2 + 2 * S, arr.getD k 0 + 8 < B := fun k hk => by
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hSL : S < L := by rw [hlenns] at hl; omega
    have h64 : 8 * L + 64 ≤ B := by have := Nat.zero_le (2 ^ (2 * L + 4)); omega
    obtain ⟨σ', r, o⟩ := acceptR_run (B := B) ts.length arr σ hA (by rw [hPa]; exact hlenA)
      (by rw [hPa]; exact hE) (by rw [hPa, ← hlenns]; omega) (by rw [hPa]; omega)
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    show _ = if CondR (ts.map Tok.val) then natBits (outW (ts.map Tok.val)) else natBits rejW
    have hcongr : CondR arr ↔ CondR (ts.map Tok.val) := by
      unfold CondR PassR
      rw [hPa, hS, hg 0 (by omega)]
      refine forall_congr' fun o => imp_congr_right fun ho => ?_
      rw [hg (2 + 2 * o) (by omega)]
    have hC : arr.getD 1 0 = (ts.map Tok.val).getD 1 0 := hg 1 (by omega)
    by_cases hc : CondR (ts.map Tok.val)
    · rw [if_pos hc, if_pos (hcongr.2 hc), natBits_outW _ ⟨h2, by rw [hl, hS], by rw [hS]; exact hsg⟩, hC,
        outBits_congr arr (ts.map Tok.val) _ (fun k hk => hg k (by
          have : 2 * (ts.map Tok.val).getD 1 0 = S := hS
          omega))]
    · rw [if_neg hc, if_neg (fun h => hc (hcongr.1 h)), natBits_rejW]

/-- The scalars and the arrays of the program. -/
def layoutR : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv",
    "n", "C", "N", "ok", "vp", "r", "vj", "sg", "cn", "cc"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutR W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, TsRenNk.nkR,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptR, prepR, chkLoop, chkBody, printR, rejR, Out.outLoop, clauseBody, litCom,
    TsRenFo.foLoop, TsRenFo.foBody, UEmit.emitRep, UEmit.repLoop, UEmit.repBody, layoutR,
    Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 300 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccR l ≤ _
  unfold KaccR Kprint Kcl Klit
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/-- **The renaming reduction is polynomial-time computable.** The program reads the word,
tokenizes it against the format of a 2-CNF formula — the number of variables, the number of
clauses, and a variable and a sign for each literal of every clause —, checks that every
literal names one of the formula's variables, and then writes, for every literal, the position
of the first occurrence of its variable in unary together with its sign, in the code of
`lax-429075`. The first occurrence is found by a loop over the earlier positions, so the phase
is quadratic in the number of tokens. -/
theorem reduceR_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceR) :=
  WrapTFinal.polyTimeE W layoutR com_ok rfl (by simp [layoutR]) 300 2 (by omega) Kpoly
    (fun Sz => by
      show 6 ≤ 300 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.TsRenFinal
