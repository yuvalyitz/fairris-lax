import Lax117284Proofs.Machine.UAcc
import Lax117284Proofs.Machine.UCongr
import Lax117284Proofs.Machine.WrapNFinal
import Lax117284Proofs.Machine.UNk

/-!
The reduction of the unit processing times to matching, as a reduction on numbers of the shape
`WrapN`, and its running time on the word RAM.
-/

namespace Lax117284Proofs.Machine.UFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.USem Lax117284Proofs.Machine.UAcc Lax117284Proofs.Machine.UCongr
open Lax117284Proofs.Machine.WrapNum Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.URow
open Lax117284Proofs.Machine Lax117284Proofs.Machine.UEmit
open Lax117284Proofs.UnitPGraph
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

open scoped Classical

theorem getD_take_eq {arr ns : List ℕ} (h : arr.take ns.length = ns) {k : ℕ} (hk : k < ns.length) :
    arr.getD k 0 = ns.getD k 0 := by
  conv_rhs => rw [← h]
  simp [List.getD_eq_getElem?_getD, hk]

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccU (_Sz l : ℕ) : ℕ := 200 + 460 * l + 140 * l * l

theorem KaccU_mono (Sz a b : ℕ) (h : a ≤ b) : KaccU Sz a ≤ KaccU Sz b := by
  unfold KaccU
  have := Nat.mul_le_mul h h
  nlinarith

/-- **The accepting phase, on a stream of the format.** -/
theorem accU_stream (B L : ℕ) (ns arr : List ℕ) (σ : Env) (hsh : Shape eU ns)
    (harr : arr.take ns.length = ns) (hA : σ.arrs "TK" = arr) (hlenL : ns.length ≤ L)
    (hvals : ∀ v ∈ ns, v < 2 ^ (L + 1)) (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    ∃ σ', Run B accU σ σ' (KaccU 0 ns.length) ∧
      σ'.out = σ.out ++ (if condU ns then outU ns else rejU) := by
  obtain ⟨h2, hl⟩ := hsh
  simp only [eU] at hl
  have hl' : ns.length = 3 + 2 * (ns.getD 1 0 * ns.getD 0 0) := by omega
  have hg : ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => getD_take_eq harr hk
  have hlenA : ns.length ≤ arr.length := by
    have := congrArg List.length harr
    rw [List.length_take] at this; omega
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
  have hLt : L < 2 ^ L := Nat.lt_two_pow_self
  have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
  have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
  have hN : ns.getD 1 0 * ns.getD 0 0 + 3 + ns.getD 1 0 * ns.getD 0 0 ≤ L := by omega
  have hE : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
    rw [hg k (by omega)]
    have := hval k (by omega)
    omega
  have hBB : 3 + 2 * (ns.getD 1 0 * ns.getD 0 0) + 8 < B := by omega
  obtain ⟨σ', r, o⟩ := accU_run (B := B) arr (ns.getD 0 0) (ns.getD 1 0) (paramOf ns)
    (by rw [hg 0 (by omega)]) (by rw [hg 1 (by omega)]) (by
      have : 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) < ns.length := by omega
      rw [hg _ this]; rfl)
    σ hA (by omega) hE hBB
  refine ⟨σ', r.mono ?_, ?_⟩
  · unfold KaccU
    have hle : ns.getD 1 0 * ns.getD 0 0 ≤ ns.length := by omega
    have := Nat.mul_le_mul hle hle
    nlinarith
  · rw [o]
    congr 1
    have hcond : (∀ t < ns.getD 1 0 * ns.getD 0 0, PassU arr t) ↔ condU ns := by
      unfold condU PassU
      refine forall_congr' fun t => imp_congr_right fun ht => ?_
      rw [hg _ (by omega), hg _ (by omega)]
    by_cases hc : condU ns
    · rw [if_pos (hcond.mpr hc), if_pos hc]
      unfold outU
      exact graphNums_congr (fun t ht => by
        unfold dA dU; rw [hg _ (by omega)])
    · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc]

/-! ### The reduction as a `WrapN` -/

/-- The memory layout: the scalars of the tokenizer and of the accepting phase, the arrays of
the tokenizer. -/
def layoutU : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "k1", "nn", "mm", "V1", "C1", "C2", "CC", "tq", "ci", "cr", "j1", "j2", "tt", "x1", "x2",
    "pa", "da", "pb", "db", "cj", "r2", "i1", "CU", "q", "C", "r", "dj", "rep", "fnd", "jj", "cn",
    "cc", "a1", "a2", "a3", "a4", "a5"], ["a", "TK"], 12⟩

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : WrapN where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := redU
  cond := condU
  outN := outU
  sem_acc := fun ns hs hc => redU_acc ns hs hc
  rejN := rejU
  sem_rej := fun w h => redU_rej w h
  rej := rejCom
  Krej := fun _ => 4
  rejRun := fun B _ σ _ hB => rejCom_run σ (by omega)
  acc := accU
  Kacc := KaccU
  Kmono := KaccU_mono
  accRun := fun B _ L ns arr σ hsh harr hA hlenL hvals hB _ =>
    accU_stream B L ns arr σ hsh harr hA hlenL hvals hB

theorem com_ok : Com.Ok layoutU W.mainW := by
  simp [WrapN.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    accU, prepU, okLoopU, okBodyU, okChkU, rejCom, kBigCom, mainU, rowsLoop,
    FoldLoop.fLoop, rowBody, locCom, setCom, repFind, repFindBody, idxD, cellE, emit6,
    emitRep, repLoop, repBody, layoutU, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 800 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccU Sz l ≤ _
  unfold KaccU
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

theorem redBits_lt (y : List ℕ) : ∀ v ∈ W.redBits y, v < 2 ^ (2 * bitSize y + 10) := by
  intro v hv
  have h1 := redU_lt (bitsOf y) v hv
  have h2 : (bitsOf y).length = y.length := by simp [bitsOf]
  have h3 := length_le_bitSize y
  have h4 : bitSize y < 2 ^ bitSize y := Nat.lt_two_pow_self
  have h5 : (2 : ℕ) ^ bitSize y < 2 ^ (2 * bitSize y + 10) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **The reduction of the unit processing times to matching is a polynomial-time word RAM
computation on the zeros and ones of its input.** -/
theorem redU_ramPolytime : RamPolytime W.redBits :=
  WrapNFinal.ramPolytimeE W layoutU com_ok rfl (by simp [layoutU]) 800 2 (by omega) Kpoly
    (fun Sz => by show 4 ≤ 800 * (Sz + 1); omega) redBits_lt

end Lax117284Proofs.Machine.UFinal
