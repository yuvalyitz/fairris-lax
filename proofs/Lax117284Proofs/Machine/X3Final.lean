import Lax117284Proofs.Machine.X3Loop
import Lax117284Proofs.Machine.X1Accept
import Lax117284Proofs.Machine.X1Final

/-! ### `Lax117284Proofs.Machine.X3Accept` -/

section
/-!
The whole of the algorithm for day-independent due dates and processing times after the tokenizer
has accepted: check the table, check that every day has the table of the first, compute the largest
depth, compare it with the number of days, and write the satisfiable formula or the unsatisfiable
one.
-/

namespace Lax117284Proofs.Machine.X3Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.T9Sem Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.X3Sem Lax117284Proofs.Machine.X3Loop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)

variable {B : ℕ}

/-- The comparison of the parameter times the largest depth with the number of days. -/
def decCom : Com :=
  .ite (.lt (V "m") (mul (V "kp") (V "r2"))) (.assign "ok" (.lit 0)) .skip

/-- The whole algorithm, after the tokenizer has accepted. -/
def acceptD : Com :=
  .seq prepT (.seq fixOk (.seq (.assign "ok" (.lit 1)) (.seq okLoop (.seq diCom (.seq omegaCom
    (.seq decCom (.ite (.eq (V "ok") (.lit 1)) printZ rejT9)))))))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccD (Sz l : ℕ) : ℕ := 1000 + 200 * l + Kmax l + Krej9 Sz

lemma Kmax_mono {a b : ℕ} (h : a ≤ b) : Kmax a ≤ Kmax b := by
  unfold Kmax
  have h1 : (100 + 10 + 4) * a + 100 + 10 + 4 ≤ (100 + 10 + 4) * b + 100 + 10 + 4 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul h1 h) 20

lemma KaccD_mono (Sz a b : ℕ) (h : a ≤ b) : KaccD Sz a ≤ KaccD Sz b := by
  unfold KaccD
  have := Kmax_mono h
  omega

open Classical in
set_option maxHeartbeats 12800000 in
/-- **The accepting phase.** -/
theorem acceptD_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B)
    (hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hn2B : 2 * arr.getD 0 0 + 8 < B)
    (hkn : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 * arr.getD 0 0 + 8 < B)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l) (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptD σ σ' (KaccD Sz l) ∧
      σ'.out = σ.out ++
        (if (∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧ DI arr ∧
            paramOf arr * omegaS arr ≤ arr.getD 1 0
          then bitsNat 1 ++ bitsNat 0
          else natBits (Lax117284.TwoSatisfiability.encodeFormula
            Lax117284.TwoSatisfiability.unsatisfiable)) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hn0 : n + 8 < B := hE 0 (by omega)
  have hm0 : m + 8 < B := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1nn, e1mm, e1V, e1C1, e1C2, e1CC, e1ok, e1a, e1o, e1f⟩ :=
    (prepT_spec (B := B) arr hE hL hlen hNB hnn hmm hC1 hC2 hCC htq) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hkpB : arr.getD (2 + 2 * N) 0 + 8 < B := hE _ (by omega)
  obtain ⟨σ2, r2, f2kp, f2k1, f2CU, f2ok, f2a, f2o, f2f⟩ := fixOk_run (B := B) arr σ1 m n A1 e1m
    e1N2 e1N e1C1 hlen hkpB hm0 hCU (by omega) hNB
  have A2 : σ2.arrs "TK" = arr := by rw [f2a]; exact A1
  have hpar : paramOf arr = arr.getD (2 + 2 * N) 0 := rfl
  -- the flag is set
  have s3 := asgE (B := B) "ok" (.lit 1) σ2 (by simp [MisBlk.small]; omega)
  set σ3 := σ2.setVar "ok" (MisBlk.den σ2 (.lit 1)) with hσ3
  have ok3 : σ3.vars "ok" = 1 := by simp [hσ3, MisBlk.den, Env.setVar]
  have A3 : σ3.arrs "TK" = arr := by simp [hσ3, Env.setVar, A2]
  have O3 : σ3.out = σ.out := by simp [hσ3, Env.setVar, f2o, e1o]
  have N3 : σ3.vars "N" = N := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "N" (by decide) (by decide) (by decide) (by decide), e1N]
  have n3 : σ3.vars "n" = n := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "n" (by decide) (by decide) (by decide) (by decide), e1n]
  have m3 : σ3.vars "m" = m := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "m" (by decide) (by decide) (by decide) (by decide), e1m]
  have kp3 : σ3.vars "kp" = paramOf arr := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2kp, hpar]
  obtain ⟨σ4, r4, e4ok, e4a, e4o, e4f⟩ := okLoop_spec (B := B) arr N 1 σ3
    (fun k hk => hE k (by omega)) (by omega) (by omega) (by omega) le_rfl A3 N3 ok3
  have A4 : σ4.arrs "TK" = arr := by rw [e4a]; exact A3
  have hf4 : flagTo (Pass arr) 1 N ≤ 1 := flagTo_le _ _ _
  have n4 : σ4.vars "n" = n := by
    rw [e4f "n" (by decide) (by decide) (by decide) (by decide)]; exact n3
  have N4 : σ4.vars "N" = N := by
    rw [e4f "N" (by decide) (by decide) (by decide) (by decide)]; exact N3
  obtain ⟨σ5, r5, e5ok, e5a, e5o, e5f⟩ := diCom_run (B := B) arr n m N σ4 A4 n4 N4 hN'
    (by omega) (fun k hk => hE k (by omega)) hNB (by rw [e4ok]; exact hf4)
  have A5 : σ5.arrs "TK" = arr := by rw [e5a]; exact A4
  have n5 : σ5.vars "n" = n := by
    rw [e5f "n" (by simp [SDI])]; exact n4
  have m5 : σ5.vars "m" = m := by
    rw [e5f "m" (by simp [SDI]), e4f "m" (by decide) (by decide) (by decide) (by decide), m3]
  obtain ⟨σ6, r6, e6r2, e6a, e6o, e6f⟩ := omegaCom_run (B := B) arr n m σ5 A5 n5 m5 rfl rfl
    (fun hm => by
      have : n ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ hm
      omega)
    (fun hm k hk => hE k (by
      have : n ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ hm
      omega)) hn2B hm0
  have hkp6 : σ6.vars "kp" = paramOf arr := by
    rw [e6f "kp" (by simp [SOUT]), e5f "kp" (by simp [SDI]),
      e4f "kp" (by decide) (by decide) (by decide) (by decide), kp3]
  have hm6 : σ6.vars "m" = m := by
    rw [e6f "m" (by simp [SOUT])]; exact m5
  have hok6 : σ6.vars "ok" = flagTo (DIp arr n) (flagTo (Pass arr) 1 N) N := by
    rw [e6f "ok" (by simp [SOUT]), e5ok, e4ok]
  have hωle := omegaS_le arr
  have hkω : σ6.vars "kp" * σ6.vars "r2" < B := by
    rw [hkp6, e6r2, hpar]
    calc arr.getD (2 + 2 * N) 0 * omegaS arr ≤ arr.getD (2 + 2 * N) 0 * n :=
          Nat.mul_le_mul_left _ hωle
      _ < B := by omega
  have hs1 : MisBlk.small B σ6 (V "m") := by show σ6.vars "m" < B; rw [hm6]; omega
  have hs2 : MisBlk.small B σ6 (mul (V "kp") (V "r2")) := by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul]
    refine ⟨?_, ?_, hkω⟩
    · show σ6.vars "kp" < B; rw [hkp6, hpar]; omega
    · show σ6.vars "r2" < B; rw [e6r2]; have := omegaS_le arr; omega
  -- the comparison
  have hlt7 : m < σ6.vars "kp" * σ6.vars "r2" ↔ m < paramOf arr * omegaS arr := by
    rw [hkp6, e6r2]
  have hcmp : ∀ (σ7 : Env), σ7.vars "ok" = (if m < paramOf arr * omegaS arr then 0 else
      flagTo (DIp arr n) (flagTo (Pass arr) 1 N) N) → (σ7.vars "ok" = 1 ↔
      ((∀ t < N, Pass arr t) ∧ DI arr ∧ paramOf arr * omegaS arr ≤ m)) := by
    intro σ7 h
    rw [h]
    by_cases hc : m < paramOf arr * omegaS arr
    · rw [if_pos hc]
      constructor
      · intro h0; omega
      · rintro ⟨-, -, h2⟩; omega
    · rw [if_neg hc, flagTo_eq_one, flagTo_eq_one]
      constructor
      · rintro ⟨⟨-, hp⟩, hd⟩
        exact ⟨hp, hd, by omega⟩
      · rintro ⟨hp, hd, -⟩
        exact ⟨⟨rfl, hp⟩, hd⟩
  obtain ⟨σ7, r7, ok7, a7, o7, f7⟩ : ∃ σ7, Run B decCom σ6 σ7 20 ∧
      σ7.vars "ok" = (if m < paramOf arr * omegaS arr then 0 else
        flagTo (DIp arr n) (flagTo (Pass arr) 1 N) N) ∧ σ7.arrs = σ6.arrs ∧ σ7.out = σ6.out ∧
      (∀ y, y ≠ "ok" → σ7.vars y = σ6.vars y) := by
    by_cases hc : m < paramOf arr * omegaS arr
    · have hT : (Cond.lt (V "m") (mul (V "kp") (V "r2"))).evalB B σ6 = some true :=
        condLt_true _ _ σ6 hs1 hs2 (by
          simp only [MisBlk.den_var, MisBlk.den_bin, Bop.apply_mul]
          rw [hm6, hkp6, e6r2]; exact hc)
      have s0 := asgE (B := B) "ok" (.lit 0) σ6 (by simp [MisBlk.small]; omega)
      refine ⟨_, (Run.ite_true hT s0).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_,
        fun y hy => ?_⟩
      · simp [Env.setVar, MisBlk.den, hc]
      · simp [Env.setVar]
      · simp [Env.setVar]
      · simp only [Env.setVar, if_neg hy]
    · have hF : (Cond.lt (V "m") (mul (V "kp") (V "r2"))).evalB B σ6 = some false :=
        condLt_false _ _ σ6 hs1 hs2 (by
          simp only [MisBlk.den_var, MisBlk.den_bin, Bop.apply_mul]
          rw [hm6, hkp6, e6r2]; exact hc)
      refine ⟨σ6, (Run.ite_false hF Run.skip).mono (by simp [Cond.size, Expr.size]), ?_, rfl, rfl,
        fun y _ => rfl⟩
      rw [if_neg hc, hok6]
  have hokB : σ7.vars "ok" < B := by
    rw [ok7]; split
    · omega
    · have := flagTo_le (DIp arr n) (flagTo (Pass arr) 1 N) N; omega
  have hcost : (if 0 < m then Kmax n else 0) ≤ Kmax l := by
    split
    · exact Kmax_mono (by
        rename_i hm
        have : n ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ hm
        omega)
    · exact Nat.zero_le _
  by_cases hok : σ7.vars "ok" = 1
  · have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ7 = some true :=
      MisBlk.condEq_true _ _ σ7 (by show σ7.vars "ok" < B; exact hokB)
        (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hok])
    obtain ⟨σ8, r8, o8, -, -⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs 1 (by omega))) σ7 trivial
    obtain ⟨σ9, r9, o9, -, -⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs 0 (by omega))) σ8 trivial
    refine ⟨σ9, (r1.seq (r2.seq (s3.seq (r4.seq (r5.seq (r6.seq (r7.seq (Run.ite_true hcondT
      (r8.seq r9))))))))).mono ?_, ?_⟩
    · unfold KaccD Krej9
      simp only [Cond.size, Expr.size]
      have hNl : N ≤ l := hl
      omega
    · rw [o9, o8, o7, e6o, e5o, e4o, O3]
      rw [if_pos ((hcmp σ7 ok7).1 hok)]
      simp
  · have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ7 = some false :=
      MisBlk.condEq_false _ _ σ7 (by show σ7.vars "ok" < B; exact hokB)
        (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hok])
    obtain ⟨σ8, r8, o8⟩ := rejT9_run (B := B) Sz σ7 hs hB2
    refine ⟨σ8, (r1.seq (r2.seq (s3.seq (r4.seq (r5.seq (r6.seq (r7.seq (Run.ite_false hcondF
      r8)))))))).mono ?_, ?_⟩
    · unfold KaccD Krej9
      simp only [Cond.size, Expr.size]
      have hNl : N ≤ l := hl
      omega
    · rw [o8, o7, e6o, e5o, e4o, O3]
      rw [if_neg (fun h => hok ((hcmp σ7 ok7).2 h))]

end Lax117284Proofs.Machine.X3Accept

end

/-! ### `Lax117284Proofs.Machine.X3Final` -/

section
/-!
The reduction to 2-satisfiability that decides day-independent due dates and processing times is
polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.X3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Accept
open Lax117284Proofs.Machine.T9Final Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.X3Sem Lax117284Proofs.Machine.X3Loop Lax117284Proofs.Machine.X3Accept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.X3Word

open scoped Classical

/-- **The check reads only the table and the parameter.** -/
theorem cond_iffD (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns) :
    ((∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧ DI arr ∧
        paramOf arr * omegaS arr ≤ arr.getD 1 0) ↔ goodD ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [h0, h1]
    exact hg _ (by omega)
  have hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0 :=
    fun k hk => hg k (by omega)
  have hdi : DI arr ↔ DI ns := by
    unfold DI
    rw [h0, h1]
    constructor
    · intro hd t ht
      have := hd t ht
      have hn : 0 < ns.getD 0 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 0 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hm : 0 < ns.getD 1 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 1 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm
      have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
      rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)] at this
      exact this
    · intro hd t ht
      have := hd t ht
      have hn : 0 < ns.getD 0 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 0 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hm : 0 < ns.getD 1 0 := by
        rcases Nat.eq_zero_or_pos (ns.getD 1 0) with hh | hh
        · rw [hh] at ht; simp at ht
        · exact hh
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm
      have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
      rw [hag _ (by omega), hag _ (by omega), hag _ (by omega), hag _ (by omega)]
      exact this
  have hom : omegaS arr = omegaS ns := by
    unfold omegaS
    rw [h0, h1]
    by_cases hm : ns.getD 1 0 = 0
    · rw [if_pos hm, if_pos hm]
    · rw [if_neg hm, if_neg hm]
      have hm' : 0 < ns.getD 1 0 := Nat.pos_of_ne_zero hm
      unfold omegaN
      rw [h0]
      refine foldl_max_congr _ _ (fun j hj => ?_)
      have hj' := List.mem_range.1 hj
      have hnN : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm'
      unfold cntN
      rw [h0]
      refine List.countP_congr (fun j' hj'' => ?_)
      have hj3 := List.mem_range.1 hj''
      unfold sRow
      rw [hag (3 + 2 * j) (by omega), hag (2 + 2 * j) (by omega), hag (3 + 2 * j') (by omega),
        hag (2 + 2 * j') (by omega)]
  unfold goodD Valid
  rw [hpar, h0, h1, hom, hdi]
  constructor
  · rintro ⟨hp, hd, hk⟩
    refine ⟨fun t ht => ?_, hd, hk⟩
    have := hp t ht
    unfold Pass at this
    rw [hg _ (by omega), hg _ (by omega)] at this
    exact this
  · rintro ⟨hv, hd, hk⟩
    refine ⟨fun t ht => ?_, hd, hk⟩
    have := hv t ht
    unfold Pass
    rw [hg _ (by omega), hg _ (by omega)]
    exact this

lemma KmonoD (Sz a b : ℕ) (h : a ≤ b) : KaccD Sz a ≤ KaccD Sz b := KaccD_mono Sz a b h

lemma encode_sat : Lax117284.TwoSatisfiability.encodeFormula Lax117284Proofs.X1Word.satF =
    encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, Lax117284Proofs.X1Word.satF]

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceD
  cond := goodD
  outW := fun _ => encodeNat 1 ++ encodeNat 0
  sem_acc := fun ns hs hc => by
    have hmem : numCode ns ∈ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) :=
      (uniform_iff_good _).2 ⟨ns, rfl, hs, hc⟩
    unfold reduceD
    rw [if_pos hmem, encode_sat]
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w h => by
    have hnot : w ∉ Uniform (fun I _ => I.DayIndepD ∧ I.DayIndepP) := fun hm => by
      obtain ⟨ns, hw, hs, hg⟩ := (uniform_iff_good w).1 hm
      exact h ⟨ns, hw, hs, hg⟩
    unfold reduceD
    rw [if_neg hnot]
  rej := rejT9
  Krej := Krej9
  rejRun := fun B Sz σ hs hB => rejT9_run (B := B) Sz σ hs hB
  acc := acceptD
  Kacc := KaccD
  Kmono := KmonoD
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
    have hLt : L < 2 ^ L := Nat.lt_two_pow_self
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hn : arr.getD 0 0 < 2 ^ (L + 1) := by rw [h0]; exact hval 0 (by omega)
    have hm : arr.getD 1 0 < 2 ^ (L + 1) := by rw [h1]; exact hval 1 (by omega)
    have hl' : ns.length = 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) := by rw [h0, h1]; omega
    have hmnL : arr.getD 1 0 * arr.getD 0 0 < 2 ^ L := by omega
    have hnn : arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hn.le hn.le
    have hmm : arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hm.le hm.le
    have hpp2 : 2 ^ (L + 1) * 2 ^ (L + 1) = 4 * (2 ^ L * 2 ^ L) := by ring
    have hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ L * 2 ^ (L + 1) :=
      Nat.mul_le_mul hmnL.le hn.le
    have hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ L * 2 ^ (L + 1) := by
      rw [Nat.mul_comm (arr.getD 0 0) (arr.getD 1 0)]
      exact Nat.mul_le_mul hmnL.le hm.le
    have hpp3 : 2 ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
    have htq : arr.getD 0 0 * arr.getD 1 0 ≤ 2 ^ L := by
      rw [Nat.mul_comm]; omega
    have hkp : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 < 2 ^ (L + 1) := by
      rw [hg _ (by omega)]; exact hval _ (by omega)
    have hkn : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 * arr.getD 0 0 ≤
        2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hkp.le hn.le
    have hlm : arr.getD 1 0 * arr.getD 0 0 ≤ ns.length := by omega
    obtain ⟨σ', r, o⟩ := acceptD_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hlm hA
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : goodD ns
    · rw [if_pos hc, if_pos ((cond_iffD arr ns harr ⟨h2, hl⟩).2 hc)]
      simp only [T9Comp1.natBits_app, natBits_encodeNat]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffD arr ns harr ⟨h2, hl⟩).1 h))]

theorem com_ok : Com.Ok X1Final.layoutX W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptD, fixOk, printZ, prepT, rejT9, decCom, omegaCom, maxCom, outerBody, cntCom, innerBody,
    diCom, diBody, FoldLoop.fLoop, SatRank.bumpS,
    FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, X1Final.layoutX, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 2000 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccD Sz l ≤ _
  unfold KaccD Kmax Krej9
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/-- **The reduction is polynomial-time computable.** -/
theorem reduceD_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceD) :=
  WrapFinal.polyTimeE W X1Final.layoutX com_ok rfl (by simp [X1Final.layoutX]) 2000 2 (by omega)
    Kpoly (fun Sz => by
      show 6 * (48 * Sz + 50) + 20 ≤ 2000 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.X3Final

end
