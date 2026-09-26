import Lax117284Proofs.Machine.D3ZeroAccept
import Lax117284Proofs.Machine.UNk
import Lax117284Proofs.Machine.Wrap
import Lax117284Proofs.Machine.WrapFinal

/-!
The reduction that decides day-independent due dates with zero days is polynomial-time
computable. No dynamic program is needed at zero days: `D3Accept.decideOk_zero_iff` reduces the
class to a comparison of three numbers against zero, decided by `D3Accept.acceptM0`.
-/

namespace Lax117284Proofs.Machine.D3ZeroFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.D3Sem (reduceM reduceM_correct uniform_iff_good)
open Lax117284Proofs.Machine.D3Accept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept

open scoped Classical

/-- **The reduction to the numbers with day-independent due dates and zero days.** -/
noncomputable def W : Wrap where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceM 0
  cond := fun ns => decideOk ns 0
  outW := fun _ => Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF
  sem_acc := fun ns hshS hc => by
    have hmem : numCode ns ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = 0) := by
      obtain ⟨hv, hdid, hgetm, hk⟩ := hc
      exact (uniform_iff_good 0 (numCode ns)).2 ⟨ns, rfl, hshS, hv, ⟨hdid, hgetm⟩, hk⟩
    unfold reduceM
    rw [if_pos hmem]
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w hnex => by
    have hnot : w ∉ Uniform (fun I _ => I.DayIndepD ∧ I.days = 0) := fun hmem => by
      obtain ⟨ns, hw, hshS, hv, ⟨hdid, hgetm⟩, hk⟩ := (uniform_iff_good 0 w).1 hmem
      exact hnex ⟨ns, hw, hshS, hv, hdid, hgetm, hk⟩
    unfold reduceM
    rw [if_neg hnot]
  rej := T9Accept.rejT9
  Krej := T9Accept.Krej9
  rejRun := fun B Sz σ hs hB => T9Accept.rejT9_run (B := B) Sz σ hs hB
  acc := acceptM0
  Kacc := KaccM0
  Kmono := KaccM0_mono
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs =>
    acceptM0_run Sz L ns arr σ hsh harr hA hlenL hvals hB hs

/-- The layout: the tokenizer's scalars, the emitter's scalars, and the three the accepting
phase reads. -/
def layoutM0 : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "v", "s", "u", "i2", "m1", "n0", "pr"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutM0 W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptM0, X1Accept.printZ, T9Accept.rejT9,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, layoutM0, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 1000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show KaccM0 Sz l ≤ _
  unfold KaccM0 T9Accept.Krej9
  nlinarith [Nat.zero_le Sz, Nat.zero_le l]

/-- **The reduction at zero days is a word RAM program**: a one-pass tokenizer reads the numbers of the
instance, and the accepting phase reads the day count and, when it is zero, the parameter and the
client count, writing the satisfiable formula exactly when the parameter is zero or there is no
client and the unsatisfiable formula otherwise — no loop over the table is needed, by
`D3Accept.decideOk_zero_iff`. A word that is not the code of an instance is answered with the
unsatisfiable formula as well. The whole program is linear in the length of the input and in the
word size, and polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduceM0_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduceM 0)) :=
  WrapFinal.polyTime W layoutM0 com_ok rfl (by simp [layoutM0]) 1000 Kpoly (fun Sz => by
    show T9Accept.Krej9 Sz ≤ 1000 * (Sz + 1)
    unfold T9Accept.Krej9
    omega)

end Lax117284Proofs.Machine.D3ZeroFinal
