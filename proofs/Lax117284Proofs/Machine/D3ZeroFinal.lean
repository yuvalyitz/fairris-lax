import Lax117284Proofs.Machine.D3AcceptDefs
import Lax117284Proofs.Machine.BlockFinal
import Lax117284Proofs.Machine.UNk
import Lax117284Proofs.Machine.Wrap
import Lax117284Proofs.Machine.WrapFinal

/-! ### `Lax117284Proofs.Machine.D3ZeroSem` -/

section
/-!
Day-independent due dates with zero days: with no days at all every schedule is vacuously
feasible and serves every client on zero days, so a `k`-fair schedule exists exactly when the
parameter is zero or there is no client. The dynamic-program class of `D3AcceptDefs` at zero days
is therefore this simple numeric condition, with no dynamic program needed to decide it.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax117284.Scheduling Lax117284Proofs.Machine.InstSem

/-- **With no days, a `k`-fair schedule exists exactly when the parameter is zero or there is no
client.** The unique schedule of an instance with no days serves every client on zero days. -/
theorem hasKFair_zero_days {I : Instance} (hd : I.days = 0) (k : ℕ) :
    I.HasKFairSchedule k ↔ k = 0 ∨ I.clients = 0 := by
  have hIE : IsEmpty (Fin I.days) := by rw [hd]; infer_instance
  have huniv : (Finset.univ : Finset (Fin I.days)) = ∅ := Finset.univ_eq_empty
  have hserved : ∀ σ : I.Schedule, ∀ j, I.served σ j = 0 := by
    intro σ j
    unfold Instance.served
    rw [huniv]; simp
  set σ0 : I.Schedule := fun i => (hIE.false i).elim
  have hfeas : I.Feasible σ0 := fun i => (hIE.false i).elim
  unfold Instance.HasKFairSchedule Instance.HasFairSchedule Instance.Fair
  constructor
  · rintro ⟨σ, -, hfair⟩
    rcases Nat.eq_zero_or_pos I.clients with hc | hc
    · exact Or.inr hc
    · refine Or.inl ?_
      have hj : Fin I.clients := ⟨0, hc⟩
      have hle : k ≤ I.served σ hj := hfair hj
      rw [hserved σ hj] at hle
      omega
  · intro hor
    refine ⟨σ0, hfeas, fun j => ?_⟩
    show k ≤ I.served σ0 j
    rw [hserved σ0 j]
    rcases hor with hk | hc
    · omega
    · exact absurd (hc ▸ j.isLt) (Nat.not_lt_zero j.1)

/-- **The dynamic-program class at zero days is the simple numeric condition**: the day count is
zero and either the parameter is zero or there is no client. -/
theorem decideOk_zero_iff (arr : List ℕ) :
    decideOk arr 0 ↔ arr.getD 1 0 = 0 ∧ (paramOf arr = 0 ∨ arr.getD 0 0 = 0) := by
  unfold decideOk
  constructor
  · rintro ⟨hv, -, hm, hk⟩
    exact ⟨hm, (hasKFair_zero_days (hm : (instOf arr hv).days = 0) (paramOf arr)).1 hk⟩
  · rintro ⟨hm, hdisj⟩
    have hv : Valid arr := fun t ht => by rw [hm] at ht; simp at ht
    exact ⟨hv, fun t ht => by rw [hm] at ht; simp at ht, hm,
      (hasKFair_zero_days (hm : (instOf arr hv).days = 0) (paramOf arr)).2 hdisj⟩

end Lax117284Proofs.Machine.D3Accept

end

/-! ### `Lax117284Proofs.Machine.D3ZeroAccept` -/

section
/-!
The accepting phase at zero days: read the day count, and when it is zero, read the parameter and
the client count and write the satisfiable formula exactly when the parameter is zero or there is
no client; write the unsatisfiable formula otherwise. No dynamic program is needed, since
`decideOk_zero_iff` reduces the class to a comparison of three numbers against zero.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.MisBlk
open Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.BlockFinal (getD_eq_of_take)

open scoped Classical

variable {B : ℕ}

/-- The whole of the reduction at zero days, after the tokenizer has accepted. -/
def acceptM0 : Com :=
  .seq (.assign "m1" (.get "TK" (.lit 1)))
  (.ite (.eq (V "m1") (.lit 0))
    (.seq (.assign "n0" (.get "TK" (.lit 0)))
    (.seq (.assign "pr" (.get "TK" (.lit 2)))
      (.ite (.eq (V "pr") (.lit 0)) X1Accept.printZ
        (.ite (.eq (V "n0") (.lit 0)) X1Accept.printZ T9Accept.rejT9))))
    T9Accept.rejT9)

/-- The cost of the accepting phase at zero days: a constant, since no loop over the table is
needed. -/
def KaccM0 (Sz _l : ℕ) : ℕ := 25 + Krej9 Sz

lemma KaccM0_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM0 Sz a ≤ KaccM0 Sz b := le_refl _

/-- **The satisfiable formula, as numbers.** -/
lemma sat_encode :
    Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF =
      encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, Lax117284Proofs.X1Word.satF]

/-- **The satisfiable formula, as bits.** -/
lemma sat_bits :
    natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF) =
      bitsNat 1 ++ bitsNat 0 := by
  rw [sat_encode, Lax117284Proofs.Machine.T9Comp1.natBits_app, natBits_encodeNat, natBits_encodeNat]

/-- **Writing the satisfiable formula.** -/
theorem printZ_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B X1Accept.printZ σ σ' (2 * (48 * Sz + 50)) ∧
      σ'.out = σ.out ++
        natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF) := by
  obtain ⟨σ1, r1, o1, -, -⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, -, -⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ1 trivial
  refine ⟨σ2, (r1.seq r2).mono (by omega), ?_⟩
  rw [o2, o1, sat_bits, List.append_assoc]

set_option maxHeartbeats 1000000 in
/-- **The accepting phase at zero days.** -/
theorem acceptM0_run (Sz L : ℕ) (ns arr : List ℕ) (σ : Env)
    (hsh : Shape eU ns) (harr : arr.take ns.length = ns) (hA : σ.arrs "TK" = arr)
    (hlenL : ns.length ≤ L) (hvals : ∀ v ∈ ns, v < 2 ^ (L + 1))
    (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) :
    ∃ σ', Run B acceptM0 σ σ' (KaccM0 Sz ns.length) ∧
      σ'.out = σ.out ++
        (if decideOk ns 0 then
          natBits (Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF)
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  have hg := getD_eq_of_take harr
  obtain ⟨h2, hl⟩ := hsh
  simp only [eU] at hl
  have hlenA : ns.length ≤ arr.length := by
    have := congrArg List.length harr
    rw [List.length_take] at this; omega
  have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
  have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
  have hPP : (2 : ℕ) ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
  have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
  have hlen3 : 3 ≤ ns.length := by omega
  have hE : ∀ k < 3, arr.getD k 0 + 8 < B := fun k hk => by
    rw [hg k (by omega)]
    have := hval k (by omega)
    omega
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  have hB6 : 6 < B := by have := hE 0 (by omega); omega
  have hidx1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by have := hE 1 (by omega); omega)
  have hev1 := RunStep.eval_get B σ "TK" (.lit 1) 1 hidx1 (by rw [hA]; omega)
    (by rw [hA]; have := hE 1 (by omega); omega)
  rw [hA] at hev1
  have s1 : Run B (.assign "m1" (.get "TK" (.lit 1))) σ (σ.setVar "m1" (arr.getD 1 0)) 3 :=
    (Run.assign hev1).mono (by simp [Expr.size])
  set σ1 := σ.setVar "m1" (arr.getD 1 0) with hσ1
  have m1v : σ1.vars "m1" = arr.getD 1 0 := by simp [hσ1, Env.setVar]
  have a1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have o1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have m1B : σ1.vars "m1" < B := by rw [m1v]; have := hE 1 (by omega); omega
  by_cases hm1 : arr.getD 1 0 = 0
  · have hcondT : (Cond.eq (V "m1") (.lit 0)).evalB B σ1 = some true :=
      condEq_true _ _ σ1 m1B (by simp [MisBlk.small]; omega) (by show σ1.vars "m1" = 0; rw [m1v]; exact hm1)
    have hm1' : ns.getD 1 0 = 0 := by rw [← h1]; exact hm1
    have hidxeq : 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) = 2 := by rw [hm1']; ring
    have hpar : paramOf ns = arr.getD 2 0 := by
      unfold paramOf
      rw [hidxeq, ← hg 2 (by omega)]
    have hidx0 : (Expr.lit 0).evalB B σ1 = some 0 := evalB_lit (by omega)
    have hev0 := RunStep.eval_get B σ1 "TK" (.lit 0) 0 hidx0 (by rw [a1, hA]; omega)
      (by rw [a1, hA]; have := hE 0 (by omega); omega)
    rw [a1, hA] at hev0
    have s2 : Run B (.assign "n0" (.get "TK" (.lit 0))) σ1 (σ1.setVar "n0" (arr.getD 0 0)) 3 :=
      (Run.assign hev0).mono (by simp [Expr.size])
    set σ2 := σ1.setVar "n0" (arr.getD 0 0) with hσ2
    have n0v : σ2.vars "n0" = arr.getD 0 0 := by simp [hσ2, Env.setVar]
    have a2 : σ2.arrs = σ1.arrs := by simp [hσ2, Env.setVar]
    have o2 : σ2.out = σ1.out := by simp [hσ2, Env.setVar]
    have hidx2 : (Expr.lit 2).evalB B σ2 = some 2 := evalB_lit (by have := hE 2 (by omega); omega)
    have hev2 := RunStep.eval_get B σ2 "TK" (.lit 2) 2 hidx2 (by rw [a2, a1, hA]; omega)
      (by rw [a2, a1, hA]; have := hE 2 (by omega); omega)
    rw [a2, a1, hA] at hev2
    have s3 : Run B (.assign "pr" (.get "TK" (.lit 2))) σ2 (σ2.setVar "pr" (arr.getD 2 0)) 3 :=
      (Run.assign hev2).mono (by simp [Expr.size])
    set σ3 := σ2.setVar "pr" (arr.getD 2 0) with hσ3
    have prv : σ3.vars "pr" = arr.getD 2 0 := by simp [hσ3, Env.setVar]
    have a3 : σ3.arrs = σ2.arrs := by simp [hσ3, Env.setVar]
    have o3 : σ3.out = σ2.out := by simp [hσ3, Env.setVar]
    have prB : σ3.vars "pr" < B := by rw [prv]; have := hE 2 (by omega); omega
    have n0v3 : σ3.vars "n0" = arr.getD 0 0 := by simp [hσ3, Env.setVar, n0v]
    have n0B3 : σ3.vars "n0" < B := by rw [n0v3]; have := hE 0 (by omega); omega
    by_cases hpr : arr.getD 2 0 = 0
    · have hcondT2 : (Cond.eq (V "pr") (.lit 0)).evalB B σ3 = some true :=
        condEq_true _ _ σ3 prB (by simp [MisBlk.small]; omega) (by show σ3.vars "pr" = 0; rw [prv]; exact hpr)
      obtain ⟨σ4, r4, o4⟩ := printZ_run (B := B) Sz σ3 hs (by omega)
      refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq
        (Run.ite_true hcondT2 r4))))).mono
        (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
      rw [o4, o3, o2, o1]
      have hcond : decideOk ns 0 := by
        rw [decideOk_zero_iff]
        exact ⟨hm1', Or.inl (by rw [hpar]; exact hpr)⟩
      rw [if_pos hcond]
    · have hcondF2 : (Cond.eq (V "pr") (.lit 0)).evalB B σ3 = some false :=
        condEq_false _ _ σ3 prB (by simp [MisBlk.small]; omega) (by show σ3.vars "pr" ≠ 0; rw [prv]; exact hpr)
      by_cases hn0 : arr.getD 0 0 = 0
      · have hcondT3 : (Cond.eq (V "n0") (.lit 0)).evalB B σ3 = some true :=
          condEq_true _ _ σ3 n0B3 (by simp [MisBlk.small]; omega) (by show σ3.vars "n0" = 0; rw [n0v3]; exact hn0)
        obtain ⟨σ4, r4, o4⟩ := printZ_run (B := B) Sz σ3 hs (by omega)
        refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq (Run.ite_false hcondF2
          (Run.ite_true hcondT3 r4)))))).mono
          (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [o4, o3, o2, o1]
        have hcond : decideOk ns 0 := by
          rw [decideOk_zero_iff]
          exact ⟨hm1', Or.inr (by rw [← h0]; exact hn0)⟩
        rw [if_pos hcond]
      · have hcondF3 : (Cond.eq (V "n0") (.lit 0)).evalB B σ3 = some false :=
          condEq_false _ _ σ3 n0B3 (by simp [MisBlk.small]; omega) (by show σ3.vars "n0" ≠ 0; rw [n0v3]; exact hn0)
        obtain ⟨σ4, r4, o4⟩ := rejT9_run (B := B) Sz σ3 hs (by omega)
        refine ⟨σ4, (s1.seq (Run.ite_true hcondT (s2.seq (s3.seq (Run.ite_false hcondF2
          (Run.ite_false hcondF3 r4)))))).mono
          (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
        rw [o4, o3, o2, o1]
        have hcond : ¬ decideOk ns 0 := by
          rw [decideOk_zero_iff]
          rintro ⟨-, hp | hc⟩
          · exact hpr (hpar.symm.trans hp)
          · exact hn0 (h0.trans hc)
        rw [if_neg hcond]
  · have hcondF : (Cond.eq (V "m1") (.lit 0)).evalB B σ1 = some false :=
      condEq_false _ _ σ1 m1B (by simp [MisBlk.small]; omega) (by show σ1.vars "m1" ≠ 0; rw [m1v]; exact hm1)
    have hm1'' : ns.getD 1 0 ≠ 0 := by rw [← h1]; exact hm1
    obtain ⟨σ2, r2, o2⟩ := rejT9_run (B := B) Sz σ1 hs (by omega)
    refine ⟨σ2, (s1.seq (Run.ite_false hcondF r2)).mono
      (by unfold KaccM0 Krej9; simp only [Cond.size, Expr.size]; omega), ?_⟩
    rw [o2, o1]
    have hcond : ¬ decideOk ns 0 := by
      rw [decideOk_zero_iff]
      rintro ⟨hm0, -⟩
      exact hm1'' hm0
    rw [if_neg hcond]

end Lax117284Proofs.Machine.D3Accept

end

/-! ### `Lax117284Proofs.Machine.D3ZeroFinal` -/

section
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

end
