import Lax117284Proofs.Machine.T9Accept
import Lax117284Proofs.Machine.X1Accept
import Lax117284Proofs.Machine.D3Pow
import Lax117284Proofs.Machine.D3Did
import Lax117284Proofs.Machine.D3Setup
import Lax117284Proofs.Machine.D3Sem
import Lax117284Proofs.Machine.D3AcceptDefs
import Lax117284Proofs.D3Link
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.TokRun
import Lax117284Proofs.Machine.FreeMain
import Lax117284Proofs.Machine.FreeFinal
import Lax117284Proofs.Machine.X1Final
import Lax117284Proofs.Machine.BlockFinal

/-! ### `Lax117284Proofs.Machine.D3Accept` -/

section
/-!
The whole of the algorithm for a fixed positive number `m` of days, after the tokenizer has
accepted: read the counts and the parameter, check that the runtime day count is `m`, and only
then — since only then is the number of clients bounded by the length of the input — check the
table and the day-independence of the due dates, order the clients by due date, run the dynamic
program, and write the formula of the case the instance is in.
-/

namespace Lax117284Proofs.Machine.D3Accept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.T9Sem Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.T9Accept Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.MisBlk (asgE)
open Lax117284Proofs.Machine.D3Pow (checkM checkM_run KcheckM powCom powCom_run KpowCom)
open Lax117284Proofs.Machine.D3Did (didCom didCom_run DIDp SDID)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.Machine.D3Rk Lax117284Proofs.Machine.D3Sweep
open Lax117284Proofs.Machine.D3Coll Lax117284Proofs.Machine.D3Client Lax117284Proofs.Machine.D3Setup
open Lax117284Proofs.Machine.D3Sem (DID did_iff goodM qF_eq_qI eOrd_eq_eI ddA_eq_ddI)
open Lax117284Proofs.D3DP Lax117284Proofs.D3Code Lax117284Proofs.D3Tab Lax117284Proofs.D3Rank
open Lax117284Proofs.D3Prog Lax117284Proofs.D3Link

variable {B : ℕ}

/-! ### The gate: read the header, check `m0 = m` -/

/-- The gate on the parameter clears `ok` exactly when a client is present and `kp > m0`. -/
theorem gateK_run (σ : Env) (m0 kp n : ℕ) (hm : σ.vars "m" = m0) (hk : σ.vars "kp" = kp)
    (hn : σ.vars "n" = n) (hm0B : m0 < B) (hkB : kp < B) (hnB : n < B) (hB : 1 < B) :
    Run B gateK σ (σ.setVar "ok" (if m0 < kp ∧ 0 < n then 0 else 1)) 10 := by
  have sm : MisBlk.small B σ (V "m") := by show σ.vars "m" < B; omega
  have sk : MisBlk.small B σ (V "kp") := by show σ.vars "kp" < B; omega
  have sn : MisBlk.small B σ (V "n") := by show σ.vars "n" < B; omega
  have s0 : MisBlk.small B σ (.lit 0) := by simp [MisBlk.small]; omega
  have dm : MisBlk.den σ (V "m") = m0 := hm
  have dk : MisBlk.den σ (V "kp") = kp := hk
  have dn : MisBlk.den σ (V "n") = n := hn
  by_cases h1 : m0 < kp
  · have c1 := MisBlk.condLt_true (V "m") (V "kp") σ sm sk (by rw [dm, dk]; exact h1)
    by_cases h2 : 0 < n
    · have c2 := MisBlk.condLt_true (.lit 0) (V "n") σ s0 sn (by rw [dn]; exact h2)
      have a0 := asgE (B := B) "ok" (.lit 0) σ (by simp [MisBlk.small]; omega)
      rw [if_pos ⟨h1, h2⟩]
      exact (Run.ite_true c1 (Run.ite_true c2 a0)).mono (by simp [Cond.size, Expr.size])
    · have c2 := MisBlk.condLt_false (.lit 0) (V "n") σ s0 sn (by rw [dn]; exact h2)
      have a1 := asgE (B := B) "ok" (.lit 1) σ (by simp [MisBlk.small]; omega)
      rw [if_neg (fun h => h2 h.2)]
      exact (Run.ite_true c1 (Run.ite_false c2 a1)).mono (by simp [Cond.size, Expr.size])
  · have c1 := MisBlk.condLt_false (V "m") (V "kp") σ sm sk (by rw [dm, dk]; exact h1)
    have a1 := asgE (B := B) "ok" (.lit 1) σ (by simp [MisBlk.small]; omega)
    rw [if_neg (fun h => h1 h.1)]
    exact (Run.ite_false c1 a1).mono (by simp [Cond.size, Expr.size])

/-- With a client present, a fair schedule serving every client `k` times needs `k ≤ days`. -/
theorem days_of_kfair (I : Lax117284.Scheduling.Instance) (h : 0 < I.clients) (k : ℕ)
    (hk : I.HasKFairSchedule k) : k ≤ I.days := by
  obtain ⟨σ, -, hf⟩ := hk
  have h1 := hf ⟨0, h⟩
  have h2 : Lax117284.Scheduling.Instance.served σ ⟨0, h⟩ ≤ I.days := by
    unfold Lax117284.Scheduling.Instance.served
    calc _ ≤ (Finset.univ : Finset (Fin I.days)).card := Finset.card_filter_le _ _
      _ = I.days := by simp
  exact h1.trans h2

/-- The gate's second rejection: a client and `m < kp` leave no fair schedule. -/
theorem not_decideOk_of_gate (arr : List ℕ) (m : ℕ) (hn : 0 < arr.getD 0 0)
    (hlt : m < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0) : ¬ decideOk arr m := by
  rintro ⟨hv, -, hm, hk⟩
  have := days_of_kfair (instOf arr hv) hn _ hk
  change paramOf arr ≤ arr.getD 1 0 at this
  unfold paramOf at this
  omega

/-- The client loop's cost is dominated by the bound `KaccDPos` uses. -/
theorem client_le (m n l PK Q : ℕ) (hn : n ≤ l) (hPK : PK ≤ Q) :
    (((((400 + 10 + 4) * PK + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * PK + 6)) + 10 + 4)
        * n + 6 ≤
      (((((400 + 10 + 4) * Q + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * Q + 6)) + 10 + 4)
        * l + 6 := by
  gcongr

/-- What is known of the state right after the `m0 = m` gate check (`prepT`, `fixOk`, `ok := 1`,
`checkM m`), in terms of the abstract `n`, `m0`, `N`, `kp` a caller already has in scope. -/
structure D3GatePrefix (m m0 n N kp : ℕ) (arr : List ℕ) (σ σ4 : Env) : Prop where
  ok4 : σ4.vars "ok" = if m0 = m then (if m0 < kp ∧ 0 < n then 0 else 1) else 0
  m4 : σ4.vars "m" = m0
  A4 : σ4.arrs "TK" = arr
  Afull4 : σ4.arrs = σ.arrs
  O4 : σ4.out = σ.out
  n4 : σ4.vars "n" = n
  kp4 : σ4.vars "kp" = kp
  N4 : σ4.vars "N" = N

/-- Run `prepT`, `fixOk`, `ok := 1` and `checkM m`, the always-run prefix before the `m0 = m` gate
is even tested. -/
theorem gatePrefix_run (m : ℕ) (arr : List ℕ) (σ : Env) (n m0 N kp : ℕ)
    (hn' : n = arr.getD 0 0) (hm0' : m0 = arr.getD 1 0) (hN' : N = m0 * n)
    (hkp' : kp = arr.getD (2 + 2 * N) 0)
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
    (hA : σ.arrs "TK" = arr) :
    ∃ σ1 σ2 σ3 σ4 : Env,
      Run B prepT σ σ1 200 ∧ Run B fixOk σ1 σ2 80 ∧
      Run B gateK σ2 σ3 10 ∧
      Run B (checkM m) σ3 σ4 (KcheckM m) ∧
      D3GatePrefix m m0 n N kp arr σ σ4 := by
  subst hn' hm0' hN' hkp'
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1nn, e1mm, e1V, e1C1, e1C2, e1CC, e1ok, e1a, e1o, e1f⟩ :=
    (prepT_spec (B := B) arr hE hL hlen hNB hnn hmm hC1 hC2 hCC htq) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hkpB : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 8 < B := hE _ (by omega)
  obtain ⟨σ2, r2, f2kp, f2k1, f2CU, f2ok, f2a, f2o, f2f⟩ := fixOk_run (B := B) arr σ1
    (arr.getD 1 0) (arr.getD 0 0) A1 e1m e1N2 e1N e1C1 hlen hkpB (hE 1 (by omega)) hCU
    (by omega) hNB
  have A2 : σ2.arrs "TK" = arr := by rw [f2a]; exact A1
  have m2 : σ2.vars "m" = arr.getD 1 0 := by
    rw [f2f "m" (by decide) (by decide) (by decide) (by decide), e1m]
  have n2 : σ2.vars "n" = arr.getD 0 0 := by
    rw [f2f "n" (by decide) (by decide) (by decide) (by decide), e1n]
  have hn0B : arr.getD 0 0 + 8 < B := hE 0 (by omega)
  have s3 := gateK_run (B := B) σ2 (arr.getD 1 0) (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0)
    (arr.getD 0 0) m2 f2kp n2 (by have := hE 1 (by omega); omega) (by omega) (by omega)
    (by omega)
  set σ3 := σ2.setVar "ok" (if arr.getD 1 0 < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧
    0 < arr.getD 0 0 then 0 else 1) with hσ3
  have ok3 : σ3.vars "ok" = (if arr.getD 1 0 < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧
    0 < arr.getD 0 0 then 0 else 1) := by simp [hσ3, Env.setVar]
  have A3 : σ3.arrs "TK" = arr := by simp [hσ3, Env.setVar, A2]
  have O3 : σ3.out = σ.out := by simp [hσ3, Env.setVar, f2o, e1o]
  have m3 : σ3.vars "m" = arr.getD 1 0 := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "m" (by decide) (by decide) (by decide) (by decide), e1m]
  have n3 : σ3.vars "n" = arr.getD 0 0 := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "n" (by decide) (by decide) (by decide) (by decide), e1n]
  have kp3 : σ3.vars "kp" = arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2kp]
  have N3 : σ3.vars "N" = arr.getD 1 0 * arr.getD 0 0 := by
    simp only [hσ3, Env.setVar]
    rw [if_neg (by decide), f2f "N" (by decide) (by decide) (by decide) (by decide), e1N]
  obtain ⟨σ4, r4, ho4, hm4, hA4, hO4, hF4⟩ := checkM_run (B := B) m σ3 (arr.getD 1 0) _ m3
    (by have := hE 1 (by omega); omega) ok3 (by split_ifs <;> omega)
  have A4 : σ4.arrs "TK" = arr := by rw [hA4]; exact A3
  have n4 : σ4.vars "n" = arr.getD 0 0 := hF4 "n" (by decide) (by decide) (by decide) ▸ n3
  have kp4 : σ4.vars "kp" = arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 :=
    hF4 "kp" (by decide) (by decide) (by decide) ▸ kp3
  have N4 : σ4.vars "N" = arr.getD 1 0 * arr.getD 0 0 :=
    hF4 "N" (by decide) (by decide) (by decide) ▸ N3
  have Afull3 : σ3.arrs = σ2.arrs := by simp [hσ3, Env.setVar]
  have Afull4 : σ4.arrs = σ.arrs := hA4.trans (Afull3.trans (f2a.trans e1a))
  exact ⟨σ1, σ2, σ3, σ4, r1, r2, s3, r4, ho4, hm4, A4, Afull4, hO4.trans O3, n4, kp4, N4⟩

open scoped Classical in
/-- The short rejection tail run when the `m0 = m` gate fails outright. -/
theorem gateFail_run (m : ℕ) (Sz l : ℕ) (arr : List ℕ) (σ : Env)
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
    (hA : σ.arrs "TK" = arr)
    (hbad : ¬ (arr.getD 1 0 = m ∧ ¬ (arr.getD 1 0 < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧
      0 < arr.getD 0 0))) :
    ∃ σ', Run B (acceptDPos m) σ σ' (KaccDPos m Sz l) ∧
      σ'.out = σ.out ++ (if decideOk arr m then bitsNat 1 ++ bitsNat 0
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  have hB2 : 6 < B := by omega
  obtain ⟨σ1, σ2, σ3, σ4, r1, r2, s3, r4, gp⟩ := gatePrefix_run (B := B) m arr σ (arr.getD 0 0)
    (arr.getD 1 0) (arr.getD 1 0 * arr.getD 0 0)
    (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0) rfl rfl rfl rfl hE hL hlen hNB hnn hmm
    hC1 hC2 hCC htq hCU hA
  have ho4' : σ4.vars "ok" = 0 := by
    rw [gp.ok4]
    by_cases h1 : arr.getD 1 0 = m
    · have h2 : arr.getD 1 0 < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧
          0 < arr.getD 0 0 := by
        by_contra hc; exact hbad ⟨h1, hc⟩
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1]
  have hF : (Cond.eq (V "ok") (.lit 1)).evalB B σ4 = some false :=
    MisBlk.condEq_false _ _ σ4 (by show σ4.vars "ok" < B; omega) (by simp [MisBlk.small]; omega)
      (by simp [MisBlk.den, ho4'])
  obtain ⟨σR, rR, oR⟩ := rejT9_run (B := B) Sz σ4 hs hB2
  have hDecideOk : ¬ decideOk arr m := by
    by_cases h1 : arr.getD 1 0 = m
    · have h2 : arr.getD 1 0 < arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 ∧
          0 < arr.getD 0 0 := by
        by_contra hc; exact hbad ⟨h1, hc⟩
      exact not_decideOk_of_gate arr m h2.2 (by rw [← h1]; exact h2.1)
    · rintro ⟨hv, -, hgetD1, -⟩
      exact h1 hgetD1
  refine ⟨σR, ?_, ?_⟩
  · refine (r1.seq (r2.seq (s3.seq (r4.seq (Run.ite_false hF rR))))).mono ?_
    simp only [Cond.size, Expr.size, KaccDPos]
    omega
  · rw [oR, gp.O4, if_neg hDecideOk]

/-! ### The gate passes: check the table, order the clients, set up the table -/

/-- What is known of the state right after the dynamic-program table has been set up (everything
from the `Valid` check through marking the state of no days served), relative to `arr`'s own `n`,
`N`, `kp` and the rank array `R0`. -/
structure D3DPSetup (m kp n N : ℕ) (arr : List ℕ) (σ σ11 : Env) (R0 : List ℕ) : Prop where
  A11 : σ11.arrs "TK" = arr
  n11 : σ11.vars "n" = n
  m11 : σ11.vars "m" = m
  PK11 : σ11.vars "PK" = (n + 1) ^ m * (kp + 1)
  PP11 : σ11.vars "PP" = (n + 1) ^ m
  kp11 : σ11.vars "kp" = kp
  pk11 : σ11.vars "pk" = (n + 1) ^ m * kp
  b111 : σ11.vars "b1" = n + 1
  ok11 : σ11.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N
  O11 : σ11.out = σ.out
  R11 : σ11.arrs "R" = R0.set 0 1
  hR11len : (n + 1) ^ m * (kp + 1) + n ≤ (σ11.arrs "R").length
  RB11 : ∀ j, (σ11.arrs "R").getD j 0 < B
  RTinit : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) 0 0 (σ11.arrs "R")
  hR0eq : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 = ordOf (ddA arr) n c'
  hRv0 : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 < n

set_option maxHeartbeats 800000 in
/-- Check the table (`Valid`), check the due dates are day-independent, order the clients by due
date, run the dynamic program's rank pass and initialize the table: everything the client loop
needs, once the `m0 = m` gate has passed. -/
theorem dpSetup_run (m : ℕ) (hm0 : 0 < m) (arr : List ℕ) (σ σ4 : Env) (n N kp : ℕ)
    (hn' : n = arr.getD 0 0) (hN' : N = arr.getD 1 0 * n)
    (hkp' : kp = arr.getD (2 + 2 * N) 0)
    (hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (_hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (_hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B)
    (hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hR0zero : ∀ j, (σ.arrs "R").getD j 0 = 0) (hRB : ∀ j, (σ.arrs "R").getD j 0 < B)
    (hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B)
    (hPKB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 + 8 < B)
    (hRlen : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 ≤
      (σ.arrs "R").length)
    (hgm : arr.getD 1 0 = m) (hgk : ¬ (arr.getD 1 0 < kp ∧ 0 < n))
    (gp : D3GatePrefix m (arr.getD 1 0) n N kp arr σ σ4) :
    ∃ σ11 σ5 σ6 σ7 σ8 σ9 σ9' σ10 : Env, ∃ R0 : List ℕ,
      Run B okLoop σ4 σ5 ((40 + 4) * N + 6) ∧
      Run B (.assign "b1" (add (V "n") (.lit 1))) σ5 σ6
        (1 + (add (V "n") (.lit 1) : Expr).size) ∧
      Run B (powCom m) σ6 σ7 (KpowCom m) ∧
      Run B (.assign "PK" (mul (V "PP") (add (V "kp") (.lit 1)))) σ7 σ8
        (1 + (mul (V "PP") (add (V "kp") (.lit 1)) : Expr).size) ∧
      Run B (.assign "pk" (mul (V "PP") (V "kp"))) σ8 σ9
        (1 + (mul (V "PP") (V "kp") : Expr).size) ∧
      Run B didCom σ9 σ9' ((80 + 10 + 4) * N + 6) ∧
      Run B rkLoop σ9' σ10 (((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6) ∧
      Run B (.store "R" (.lit 0) (.lit 1)) σ10 σ11 3 ∧
      D3DPSetup (B := B) m kp n N arr σ σ11 R0 := by
  subst hn' hN' hkp'
  set n := arr.getD 0 0 with hn'
  set m0 := arr.getD 1 0 with hm0'
  set N := m0 * n with hN'
  set kp := arr.getD (2 + 2 * N) 0 with hkp'
  have A4 : σ4.arrs "TK" = arr := gp.A4
  have N4 : σ4.vars "N" = N := gp.N4
  have n4 : σ4.vars "n" = n := gp.n4
  have kp4 : σ4.vars "kp" = kp := gp.kp4
  have hm4 : σ4.vars "m" = m0 := gp.m4
  have ho4' : σ4.vars "ok" = 1 := by rw [gp.ok4, if_pos hgm, if_neg hgk]
  have hkpB : arr.getD (2 + 2 * N) 0 + 8 < B := hE _ (by omega)
  have hmN : n ≤ N := by rw [hN', hgm]; exact Nat.le_mul_of_pos_left _ hm0
  have hPKB' := hPKB hgm
  -- Valid check
  obtain ⟨σ5, r5, e5ok, e5a, e5o, e5f⟩ := okLoop_spec (B := B) arr N 1 σ4
    (fun k hk => hE k (by omega)) (by omega) (by omega) (by omega) le_rfl A4 N4 ho4'
  have A5 : σ5.arrs "TK" = arr := by rw [e5a]; exact A4
  have n5 : σ5.vars "n" = n := by
    rw [e5f "n" (by decide) (by decide) (by decide) (by decide)]; exact n4
  have kp5 : σ5.vars "kp" = kp := by
    rw [e5f "kp" (by decide) (by decide) (by decide) (by decide)]; exact kp4
  have N5 : σ5.vars "N" = N := by
    rw [e5f "N" (by decide) (by decide) (by decide) (by decide)]; exact N4
  -- b1 := n + 1
  have s6 := asgE (B := B) "b1" (add (V "n") (.lit 1)) σ5 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_var,
      MisBlk.den_lit, Bop.apply_add, n5]
    have := hPPB hgm
    have hnB : n + 1 ≤ (n + 1) ^ m := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ m := Nat.pow_le_pow_right (by omega) hm0
    omega)
  set σ6 := σ5.setVar "b1" (MisBlk.den σ5 (add (V "n") (.lit 1))) with hσ6
  have b16 : σ6.vars "b1" = n + 1 := by simp [hσ6, MisBlk.den, Env.setVar, n5, Bop.apply_add]
  have n6 : σ6.vars "n" = n := by simp [hσ6, Env.setVar, n5]
  have kp6 : σ6.vars "kp" = kp := by simp [hσ6, Env.setVar, kp5]
  have A6 : σ6.arrs "TK" = arr := by simp [hσ6, Env.setVar, A5]
  have ok6 : σ6.vars "ok" = flagTo (Pass arr) 1 N := by simp [hσ6, Env.setVar, e5ok]
  -- PP := b1 ^ m
  have hbd : ∀ i ≤ m, (n + 1) ^ i + 8 < B := fun i hi => by
    have : (n + 1) ^ i ≤ (n + 1) ^ m := Nat.pow_le_pow_right (by omega) hi
    omega
  obtain ⟨σ7, r7, PP7, hA7, hO7, hF7⟩ := powCom_run (B := B) m σ6 (n + 1) b16 hbd
  have kp7 : σ7.vars "kp" = kp := hF7 "kp" (by decide) ▸ kp6
  have n7 : σ7.vars "n" = n := hF7 "n" (by decide) ▸ n6
  -- PK := PP * (kp + 1)
  have s8 := asgE (B := B) "PK" (mul (V "PP") (add (V "kp") (.lit 1))) σ7 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_var,
      MisBlk.den_lit, MisBlk.den_bin, Bop.apply_add, Bop.apply_mul, PP7, kp7]
    have h1 := hPPB hgm
    have h2 := hkpB
    have h3 := hPKB hgm
    omega)
  set σ8 := σ7.setVar "PK" (MisBlk.den σ7 (mul (V "PP") (add (V "kp") (.lit 1)))) with hσ8
  have PK8 : σ8.vars "PK" = (n + 1) ^ m * (kp + 1) := by
    simp [hσ8, MisBlk.den, Env.setVar, PP7, kp7, Bop.apply_add, Bop.apply_mul]
  have PP8 : σ8.vars "PP" = (n + 1) ^ m := by simp [hσ8, Env.setVar, PP7]
  have kp8 : σ8.vars "kp" = kp := by simp [hσ8, Env.setVar, kp7]
  have n8 : σ8.vars "n" = n := by simp [hσ8, Env.setVar, n7]
  have A8 : σ8.arrs "TK" = arr := by simp [hσ8, Env.setVar, hA7, A6]
  have ok8 : σ8.vars "ok" = flagTo (Pass arr) 1 N := by
    simp only [hσ8, Env.setVar]; rw [if_neg (by decide)]
    simp [hF7 "ok" (by decide), ok6]
  -- pk := PP * kp
  have s9 := asgE (B := B) "pk" (mul (V "PP") (V "kp")) σ8 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, PP8, kp8]
    have h1 := hPPB hgm
    have h2 := hkpB
    have h3 := hPKB hgm
    have h4 : (n + 1) ^ m * kp ≤ (n + 1) ^ m * (kp + 1) := Nat.mul_le_mul_left _ (by omega)
    omega)
  set σ9 := σ8.setVar "pk" (MisBlk.den σ8 (mul (V "PP") (V "kp"))) with hσ9
  have pk9 : σ9.vars "pk" = (n + 1) ^ m * kp := by
    simp [hσ9, MisBlk.den, Env.setVar, PP8, kp8, Bop.apply_mul]
  have PK9 : σ9.vars "PK" = (n + 1) ^ m * (kp + 1) := by simp [hσ9, Env.setVar, PK8]
  have PP9 : σ9.vars "PP" = (n + 1) ^ m := by simp [hσ9, Env.setVar, PP8]
  have kp9 : σ9.vars "kp" = kp := by simp [hσ9, Env.setVar, kp8]
  have n9 : σ9.vars "n" = n := by simp [hσ9, Env.setVar, n8]
  have A9 : σ9.arrs "TK" = arr := by simp [hσ9, Env.setVar, A8]
  have ok9 : σ9.vars "ok" = flagTo (Pass arr) 1 N := by simp [hσ9, Env.setVar, ok8]
  have m9 : σ9.vars "m" = m0 := by
    simp only [hσ9, hσ8, Env.setVar]
    rw [if_neg (by decide), if_neg (by decide), hF7 "m" (by decide)]
    simp only [hσ6, Env.setVar]
    rw [if_neg (by decide), e5f "m" (by decide) (by decide) (by decide) (by decide), hm4]
  have N9 : σ9.vars "N" = N := by
    simp only [hσ9, hσ8, Env.setVar]
    rw [if_neg (by decide), if_neg (by decide), hF7 "N" (by decide)]
    simp only [hσ6, Env.setVar]
    rw [if_neg (by decide), e5f "N" (by decide) (by decide) (by decide) (by decide), N4]
  have hok9le : σ9.vars "ok" ≤ 1 := by rw [ok9]; exact flagTo_le _ _ _
  have hA9arrs : σ9.arrs = σ.arrs := by
    simp only [hσ9, hσ8, Env.setVar]
    rw [hA7]
    simp only [hσ6, Env.setVar]
    rw [e5a, gp.Afull4]
  have b19 : σ9.vars "b1" = n + 1 := by
    simp [hσ9, hσ8, Env.setVar, hF7 "b1" (by decide), b16]
  have R9len : (n + 1) ^ m * (kp + 1) + n ≤ (σ9.arrs "R").length := by
    rw [hA9arrs]; exact hRlen hgm
  have RB9 : ∀ j, (σ9.arrs "R").getD j 0 < B := by rw [hA9arrs]; exact hRB
  -- day-independence of the due dates
  obtain ⟨σ9', r9', ho9', hA9', hO9', hF9'⟩ := didCom_run (B := B) arr n m0 N σ9 A9 n9 N9 hN'
    hlen (fun k hk => hE k (by omega)) hNB hok9le
  have A9' : σ9'.arrs "TK" = arr := by rw [hA9']; exact A9
  have n9' : σ9'.vars "n" = n := hF9' "n" (by simp [SDID]) ▸ n9
  have m9' : σ9'.vars "m" = m0 := hF9' "m" (by simp [SDID]) ▸ m9
  have kp9' : σ9'.vars "kp" = kp := hF9' "kp" (by simp [SDID]) ▸ kp9
  have PK9' : σ9'.vars "PK" = (n + 1) ^ m * (kp + 1) := hF9' "PK" (by simp [SDID]) ▸ PK9
  have PP9' : σ9'.vars "PP" = (n + 1) ^ m := hF9' "PP" (by simp [SDID]) ▸ PP9
  have R9'len : (n + 1) ^ m * (kp + 1) + n ≤ (σ9'.arrs "R").length := by rw [hA9']; exact R9len
  have RB9' : ∀ j, (σ9'.arrs "R").getD j 0 < B := by rw [hA9']; exact RB9
  have hA9'arrs : σ9'.arrs = σ.arrs := by rw [hA9']; exact hA9arrs
  have pk9' : σ9'.vars "pk" = (n + 1) ^ m * kp := hF9' "pk" (by simp [SDID]) ▸ pk9
  have b19' : σ9'.vars "b1" = n + 1 := hF9' "b1" (by simp [SDID]) ▸ b19
  have ok9' : σ9'.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N := by
    rw [ho9', ok9]
  -- rank: order the clients by due date
  obtain ⟨σ10, r10, hR10, hA10, hO10, hF10⟩ := rkLoop_run (B := B) arr n ((n + 1) ^ m * (kp + 1))
    σ9' A9' n9' PK9' (by omega) (fun k hk => hE k (by omega)) (by omega) (by omega) R9'len
  have A10 : σ10.arrs "TK" = arr := hA10
  have n10 : σ10.vars "n" = n := hF10 "n" (by simp [SRKO]) ▸ n9'
  have m10 : σ10.vars "m" = m0 := hF10 "m" (by simp [SRKO]) ▸ m9'
  have PK10 : σ10.vars "PK" = (n + 1) ^ m * (kp + 1) := hF10 "PK" (by simp [SRKO]) ▸ PK9'
  have PP10 : σ10.vars "PP" = (n + 1) ^ m := hF10 "PP" (by simp [SRKO]) ▸ PP9'
  have kp10 : σ10.vars "kp" = kp := hF10 "kp" (by simp [SRKO]) ▸ kp9'
  have pk10 : σ10.vars "pk" = (n + 1) ^ m * kp := hF10 "pk" (by simp [SRKO]) ▸ pk9'
  have ok10 : σ10.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N :=
    hF10 "ok" (by simp [SRKO]) ▸ ok9'
  have b110 : σ10.vars "b1" = n + 1 := hF10 "b1" (by simp [SRKO]) ▸ b19'
  set R0 := σ10.arrs "R" with hR0def
  have hinj0 : ∀ a b, a < n → b < n →
      (n + 1) ^ m * (kp + 1) + rk (ddA arr) n a = (n + 1) ^ m * (kp + 1) + rk (ddA arr) n b →
      a = b := fun a b ha hb h => rk_injOn (dd := ddA arr) ha hb (by omega)
  have hlt0 : ∀ j < n, (n + 1) ^ m * (kp + 1) + rk (ddA arr) n j < (σ9'.arrs "R").length :=
    fun j hj => by have := rk_lt (dd := ddA arr) hj; omega
  obtain ⟨hlen0, hin0, hout0⟩ := D3List.stFold_inv
    (fun i' => (n + 1) ^ m * (kp + 1) + rk (ddA arr) n i') (fun i' => i') (σ9'.arrs "R") n hinj0
    hlt0 n le_rfl
  have R0len : (n + 1) ^ m * (kp + 1) + n ≤ R0.length := by rw [hR10, hlen0]; exact R9'len
  have hR0eq : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 = ordOf (ddA arr) n c' := by
    intro c' hc'
    have ha := ordOf_spec (dd := ddA arr) hc'
    have heq : (n + 1) ^ m * (kp + 1) + rk (ddA arr) n (ordOf (ddA arr) n c') =
        (n + 1) ^ m * (kp + 1) + c' := by rw [ha.2]
    rw [hR10, ← heq, hin0 _ ha.1]
  have hRv0 : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 < n := by
    intro c' hc'; rw [hR0eq c' hc']; exact (ordOf_spec (dd := ddA arr) hc').1
  have hnB : n < B := by omega
  have RB0 : ∀ j, R0.getD j 0 < B := by
    intro j
    rw [hR10]
    by_cases hj : ∃ a < n, (n + 1) ^ m * (kp + 1) + rk (ddA arr) n a = j
    · obtain ⟨a, ha, he⟩ := hj
      rw [← he, hin0 a ha]; omega
    · push Not at hj
      rw [hout0 j hj]; exact RB9' j
  -- init: mark the state of no days served
  have hR0len0 : 0 < R0.length := by
    have hP0 : 0 < (n + 1) ^ m * (kp + 1) := by positivity
    omega
  have s11 := initR_run (B := B) σ10 hR0len0 (by omega)
  set σ11 := σ10.setArr "R" 0 1 with hσ11
  have R11 : σ11.arrs "R" = R0.set 0 1 := by simp [hσ11, hR0def]
  have A11 : σ11.arrs "TK" = arr := by
    rw [hσ11, setArr_arrs_ne σ10 "R" "TK" 0 1 (by decide)]; exact A10
  have n11 : σ11.vars "n" = n := by simp [hσ11, n10]
  have m11 : σ11.vars "m" = m0 := by simp [hσ11, m10]
  have PK11 : σ11.vars "PK" = (n + 1) ^ m * (kp + 1) := by simp [hσ11, PK10]
  have PP11 : σ11.vars "PP" = (n + 1) ^ m := by simp [hσ11, PP10]
  have kp11 : σ11.vars "kp" = kp := by simp [hσ11, kp10]
  have pk11 : σ11.vars "pk" = (n + 1) ^ m * kp := by simp [hσ11, pk10]
  have b111 : σ11.vars "b1" = n + 1 := by simp [hσ11, b110]
  have ok11 : σ11.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N := by
    simp [hσ11, ok10]
  have O11 : σ11.out = σ.out := by
    simp only [hσ11, Env.setArr]
    rw [hO10, hO9', hσ9, hσ8]
    simp only [Env.setVar]
    rw [hO7, hσ6]
    simp only [Env.setVar]
    rw [e5o, gp.O4]
  have hR11len : (n + 1) ^ m * (kp + 1) + n ≤ (σ11.arrs "R").length := by
    rw [R11, List.length_set]; exact R0len
  have RB11 : ∀ j, (σ11.arrs "R").getD j 0 < B := by
    intro j; rw [R11]
    by_cases hj0 : j = 0
    · subst hj0; rw [D3List.getD_set_self _ _ _ (by omega)]; omega
    · rw [D3List.getD_set_ne _ _ _ _ (Ne.symm hj0)]; exact RB0 j
  have RTinit : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) 0 0 (σ11.arrs "R") := by
    apply RT_init
    intro x hx
    rw [R11]
    by_cases h0 : x = 0
    · subst h0; rw [D3List.getD_set_self _ _ _ (by omega)]; simp
    · rw [D3List.getD_set_ne _ _ _ _ (Ne.symm h0), if_neg h0]
      by_cases hj : ∃ a < n, (n + 1) ^ m * (kp + 1) + rk (ddA arr) n a = x
      · obtain ⟨a, ha, he⟩ := hj
        exfalso
        have := rk_lt (dd := ddA arr) ha
        omega
      · push Not at hj
        rw [hR10, hout0 x hj, hA9'arrs]
        exact hR0zero x
  exact ⟨σ11, σ5, σ6, σ7, σ8, σ9, σ9', σ10, R0, r5, s6, r7, s8, s9, r9', r10, s11,
    A11, n11, m11.trans hgm, PK11, PP11, kp11, pk11, b111, ok11, O11, R11, hR11len, RB11, RTinit,
    hR0eq, hRv0⟩

/-! ### The client loop: no clients, or the real dynamic program -/

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- The `n = 0` sub-case: the client loop does nothing, and the table set up by `dpSetup_run`
already decides everything, since `Valid`/`DID` hold vacuously and a schedule always exists. -/
theorem n0Case_run (m : ℕ) (Sz l : ℕ) (arr : List ℕ) (σ σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9 σ9' σ10 σ11 :
    Env) (n N kp : ℕ) (R0 : List ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (r1 : Run B prepT σ σ1 200) (r2 : Run B fixOk σ1 σ2 80)
    (s3 : Run B gateK σ2 σ3 10)
    (r4 : Run B (checkM m) σ3 σ4 (KcheckM m))
    (r5 : Run B okLoop σ4 σ5 ((40 + 4) * N + 6))
    (s6 : Run B (.assign "b1" (add (V "n") (.lit 1))) σ5 σ6
      (1 + (add (V "n") (.lit 1) : Expr).size))
    (r7 : Run B (powCom m) σ6 σ7 (KpowCom m))
    (s8 : Run B (.assign "PK" (mul (V "PP") (add (V "kp") (.lit 1)))) σ7 σ8
      (1 + (mul (V "PP") (add (V "kp") (.lit 1)) : Expr).size))
    (s9 : Run B (.assign "pk" (mul (V "PP") (V "kp"))) σ8 σ9
      (1 + (mul (V "PP") (V "kp") : Expr).size))
    (r9' : Run B didCom σ9 σ9' ((80 + 10 + 4) * N + 6))
    (r10 : Run B rkLoop σ9' σ10 (((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6))
    (s11 : Run B (.store "R" (.lit 0) (.lit 1)) σ10 σ11 3)
    (_hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (_hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (_hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B)
    (_hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B)
    (hT : (Cond.eq (V "ok") (.lit 1)).evalB B σ4 = some true)
    (hn' : n = arr.getD 0 0) (hN' : N = arr.getD 1 0 * n) (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l)
    (hnl : n ≤ l) (hn0 : n = 0)
    (hgm : arr.getD 1 0 = m) (A11 : σ11.arrs "TK" = arr) (n11 : σ11.vars "n" = n)
    (PP11 : σ11.vars "PP" = (n + 1) ^ m)
    (ok11 : σ11.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N)
    (O11 : σ11.out = σ.out) (RB11 : ∀ j, (σ11.arrs "R").getD j 0 < B)
    (hR11len : (n + 1) ^ m * (kp + 1) + n ≤ (σ11.arrs "R").length)
    (RTinit : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) 0 0 (σ11.arrs "R")) :
    ∃ σ', Run B (acceptDPos m) σ σ' (KaccDPos m Sz l) ∧
      σ'.out = σ.out ++ (if decideOk arr m then bitsNat 1 ++ bitsNat 0
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  subst hn' hN'
  set n := arr.getD 0 0 with hn'
  set m0 := arr.getD 1 0 with hm0'
  set N := m0 * n with hN'
  have hPPB' := hPPB hgm
  have hPPle : (n + 1) ^ m ≤ (n + 1) ^ m * (kp + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos kp)
  have hmv0 : σ11.vars "n" = 0 := by rw [n11, hn0]
  obtain ⟨σ12, r12, hQ12⟩ := ILoop.iLoop_spec (B := B) "cl" "n" clientBody
    (fun _ σ' => σ'.vars "n" = 0 ∧ σ'.vars "ok" = σ11.vars "ok" ∧
      σ'.arrs "R" = σ11.arrs "R" ∧ σ'.arrs "TK" = σ11.arrs "TK" ∧ σ'.out = σ11.out ∧
      σ'.vars "PP" = σ11.vars "PP") 0 0 σ11
    hmv0 (fun j σ' hq => hq.1) (by decide) (by omega)
    ⟨by simp [Env.setVar, hmv0], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar]⟩
    (fun j σ' v hq => hq)
    (by intro j σ1 hq hjv hjn; omega)
  have hok12 : σ12.vars "ok" = σ11.vars "ok" := hQ12.2.1
  have hR12 : σ12.arrs "R" = σ11.arrs "R" := hQ12.2.2.1
  have hA12 : σ12.arrs "TK" = arr := by rw [hQ12.2.2.2.1]; exact A11
  have hO12 : σ12.out = σ11.out := hQ12.2.2.2.2.1
  have hPP12 : σ12.vars "PP" = σ11.vars "PP" := hQ12.2.2.2.2.2
  have hRTfin : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n 0 (σ12.arrs "R") := by
    rw [hR12, hn0]; rw [hn0] at RTinit; exact RTinit
  have hReachNE : (Reach m kp (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n).Nonempty := by
    rw [hn0]; exact ⟨fun _ => 0, rfl⟩
  have hex : ∃ s < (n + 1) ^ m, (σ12.arrs "R").getD s 0 = 1 :=
    (RT_final (σ12.arrs "R") hRTfin).2 hReachNE
  -- fnd := 0
  have sFnd := asgE (B := B) "fnd" (.lit 0) σ12 (by simp [MisBlk.small]; omega)
  set σ13 := σ12.setVar "fnd" (MisBlk.den σ12 (.lit 0)) with hσ13
  have fnd13 : σ13.vars "fnd" = 0 := by simp [hσ13, MisBlk.den, Env.setVar]
  have R13 : σ13.arrs "R" = σ12.arrs "R" := by simp [hσ13, Env.setVar]
  have A13 : σ13.arrs "TK" = arr := by simp [hσ13, Env.setVar, hA12]
  have O13 : σ13.out = σ11.out := by simp [hσ13, Env.setVar, hO12]
  have PP13 : σ13.vars "PP" = (n + 1) ^ m := by simp [hσ13, Env.setVar, hPP12, PP11]
  have ok13 : σ13.vars "ok" = σ11.vars "ok" := by simp [hσ13, Env.setVar, hok12]
  have hRB13 : ∀ j, (σ13.arrs "R").getD j 0 < B := by rw [R13, hR12]; exact RB11
  -- scan the table
  obtain ⟨σ14, r14, fnd14, hA14, hO14, hF14⟩ := scanLoop_run (B := B) σ13 (σ13.arrs "R")
    ((n + 1) ^ m) rfl PP13 (by rw [R13, hR12]; omega) hRB13 (by omega) (by omega)
  have hfnd14 : σ14.vars "fnd" = 1 := by
    rw [fnd14, fnd13]
    rw [if_pos (Or.inr (by rw [R13]; exact hex))]
  have hok14 : σ14.vars "ok" = σ11.vars "ok" := by
    rw [hF14 "ok" (by simp [SSC])]; exact ok13
  have hA14' : σ14.arrs "TK" = arr := by rw [hA14]; exact A13
  have hO14' : σ14.out = σ11.out := by rw [hO14]; exact O13
  -- the decision: with no clients, `Valid`/`DID` hold vacuously and a schedule always exists
  have hprod : arr.getD 1 0 * arr.getD 0 0 = 0 := Nat.mul_eq_zero.mpr (Or.inr (hn'.symm.trans hn0))
  have hValid : Valid arr := fun t ht => absurd ht (by omega)
  have hDID : DID arr := fun t ht => absurd ht (by omega)
  have hHasKFair : (instOf arr hValid).HasKFairSchedule (paramOf arr) :=
    WordCorrect.hasKFair_of_clients_zero (instOf arr hValid) (by show n = 0; exact hn0) _
  have hDecideOk : decideOk arr m := ⟨hValid, hDID, hgm, hHasKFair⟩
  -- the final print
  obtain ⟨σ15, r15, o15, -, -⟩ := emitLit_spec (B := B) 1 Sz (by omega) (hs 1 (by omega)) σ14
    trivial
  obtain ⟨σ16, r16, o16, -, -⟩ := emitLit_spec (B := B) 0 Sz (by omega) (hs 0 (by omega)) σ15
    trivial
  have hN0 : N = 0 := by simp [hN', hn0]
  have hokval : σ11.vars "ok" = 1 := by
    rw [ok11, hN0]
    rw [flagTo_zero (DIDp arr n) (flagTo (Pass arr) 1 0) (flagTo_le (Pass arr) 1 0)]
    exact flagTo_zero (Pass arr) 1 (by omega)
  have hokT : (Cond.eq (V "ok") (.lit 1)).evalB B σ14 = some true :=
    MisBlk.condEq_true _ _ σ14 (by show σ14.vars "ok" < B; rw [hok14]; omega)
      (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hok14, hokval])
  have hfndT : (Cond.eq (V "fnd") (.lit 1)).evalB B σ14 = some true :=
    MisBlk.condEq_true _ _ σ14 (by show σ14.vars "fnd" < B; rw [hfnd14]; omega)
      (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hfnd14])
  have hPPl : (n + 1) ^ m ≤ (l + 1) ^ m := Nat.pow_le_pow_left (by omega) m
  refine ⟨σ16, ?_, ?_⟩
  · have dpBodyRun := r5.seq (s6.seq (r7.seq (s8.seq (s9.seq (r9'.seq (r10.seq (s11.seq
        (r12.seq (sFnd.seq r14)))))))))
    refine (r1.seq (r2.seq (s3.seq (r4.seq
      (Run.ite_true hT (dpBodyRun.seq (Run.ite_true hokT
        (Run.ite_true hfndT (r15.seq r16))))))))).mono ?_
    simp only [Cond.size, Expr.size, KaccDPos]
    have hrk : ((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6 ≤
        ((100 + 10 + 4) * l + 60 + 10 + 4) * l + 6 := by gcongr
    have hsc : (20 + 10 + 4) * (n + 1) ^ m + 6 ≤ (20 + 10 + 4) * (l + 1) ^ m + 6 := by gcongr
    have hNl : N ≤ l := hl
    linarith [hrk, hsc, hNl, Nat.zero_le Sz, Nat.zero_le (KpowCom m), Nat.zero_le (KcheckM m),
      Nat.zero_le (Krej9 Sz),
      Nat.zero_le ((((((400 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6 + 60) + 10 + 4) * m + 6 + 60 +
        ((60 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6)) + 10 + 4) * l + 6)]
  · rw [o16, o15, hO14', O11, if_pos hDecideOk, List.append_assoc]

open scoped Classical in
set_option maxHeartbeats 2000000 in
/-- The `n > 0` sub-case: run the real dynamic program (`clientLoop`), then decide by whether a
reachable fair schedule exists. -/
theorem nPosCase_run (m : ℕ) (hm0 : 0 < m) (Sz l : ℕ) (arr : List ℕ) (σ σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9
    σ9' σ10 σ11 : Env) (n N kp : ℕ) (R0 : List ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (r1 : Run B prepT σ σ1 200) (r2 : Run B fixOk σ1 σ2 80)
    (s3 : Run B gateK σ2 σ3 10)
    (r4 : Run B (checkM m) σ3 σ4 (KcheckM m))
    (r5 : Run B okLoop σ4 σ5 ((40 + 4) * N + 6))
    (s6 : Run B (.assign "b1" (add (V "n") (.lit 1))) σ5 σ6
      (1 + (add (V "n") (.lit 1) : Expr).size))
    (r7 : Run B (powCom m) σ6 σ7 (KpowCom m))
    (s8 : Run B (.assign "PK" (mul (V "PP") (add (V "kp") (.lit 1)))) σ7 σ8
      (1 + (mul (V "PP") (add (V "kp") (.lit 1)) : Expr).size))
    (s9 : Run B (.assign "pk" (mul (V "PP") (V "kp"))) σ8 σ9
      (1 + (mul (V "PP") (V "kp") : Expr).size))
    (r9' : Run B didCom σ9 σ9' ((80 + 10 + 4) * N + 6))
    (r10 : Run B rkLoop σ9' σ10 (((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6))
    (s11 : Run B (.store "R" (.lit 0) (.lit 1)) σ10 σ11 3)
    (_hL : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hnn : arr.getD 0 0 * arr.getD 0 0 + 8 < B) (_hmm : arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + 8 < B)
    (_hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_hCC : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
      arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 + 8 < B)
    (_htq : arr.getD 0 0 * arr.getD 1 0 + 8 < B)
    (_hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B)
    (hT : (Cond.eq (V "ok") (.lit 1)).evalB B σ4 = some true)
    (hE2 : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), 2 * arr.getD k 0 + 16 < B)
    (hlen : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hPKB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 + 8 < B)
    (hn' : n = arr.getD 0 0) (hN' : N = arr.getD 1 0 * n)
    (hkp' : kp = arr.getD (2 + 2 * N) 0) (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l) (hnl : n ≤ l)
    (hnpos : 0 < n) (hkm : kp ≤ m) (hgm : arr.getD 1 0 = m) (A11 : σ11.arrs "TK" = arr) (n11 : σ11.vars "n" = n)
    (m11 : σ11.vars "m" = m) (PK11 : σ11.vars "PK" = (n + 1) ^ m * (kp + 1))
    (PP11 : σ11.vars "PP" = (n + 1) ^ m) (kp11 : σ11.vars "kp" = kp)
    (pk11 : σ11.vars "pk" = (n + 1) ^ m * kp) (b111 : σ11.vars "b1" = n + 1)
    (ok11 : σ11.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N)
    (O11 : σ11.out = σ.out) (R11 : σ11.arrs "R" = R0.set 0 1)
    (hR11len : (n + 1) ^ m * (kp + 1) + n ≤ (σ11.arrs "R").length)
    (RB11 : ∀ j, (σ11.arrs "R").getD j 0 < B)
    (RTinit : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
      (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) 0 0 (σ11.arrs "R"))
    (hR0eq : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 = ordOf (ddA arr) n c')
    (hRv0 : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 < n) :
    ∃ σ', Run B (acceptDPos m) σ σ' (KaccDPos m Sz l) ∧
      σ'.out = σ.out ++ (if decideOk arr m then bitsNat 1 ++ bitsNat 0
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  subst hn' hN' hkp'
  set n := arr.getD 0 0 with hn'
  set m0 := arr.getD 1 0 with hm0'
  set N := m0 * n with hN'
  set kp := arr.getD (2 + 2 * N) 0 with hkp'
  have hPPB' := hPPB hgm
  have hPPle : (n + 1) ^ m ≤ (n + 1) ^ m * (kp + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos kp)
  have hmn_eq : m * n = N := by rw [← hgm]
  have hCEnv11 : CEnv B arr n m ((n + 1) ^ m) kp ((n + 1) ^ m * (kp + 1)) σ11 :=
    ⟨A11, n11, m11, PK11, PP11, kp11, b111, pk11, rfl, rfl, hnpos, hm0,
      by rw [hmn_eq]; exact hlen,
      fun j hj => hE2 j (by rw [← hmn_eq]; exact hj),
      by rw [hmn_eq]; exact hNB, hPKB hgm⟩
  have hPKpos : 0 < (n + 1) ^ m * (kp + 1) := by positivity
  have hPKQ : (n + 1) ^ m * (kp + 1) ≤ (l + 1) ^ m * (m + 1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) m) (by omega)
  have hcl := client_le m n l _ _ hnl hPKQ
  have hrk : ((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6 ≤ ((100 + 10 + 4) * l + 60 + 10 + 4) * l + 6 := by
    gcongr
  have hsc : (20 + 10 + 4) * (n + 1) ^ m + 6 ≤ (20 + 10 + 4) * (l + 1) ^ m + 6 := by
    gcongr
  have hNl : N ≤ l := hl
  have hRInv11 : RInv B n ((n + 1) ^ m * (kp + 1)) R0 (σ11.arrs "R") :=
    ⟨hR11len, fun y hy => by rw [R11, D3List.getD_set_ne _ _ _ _ (by omega)], RB11⟩
  obtain ⟨σ12, r12, hC12, hRInv12, hRT12, hO12, hAeq12, hF12⟩ :=
    clientLoop_run (arr := arr) (R0 := R0) σ11 hCEnv11 hRInv11 hRv0 RTinit
  have hokEq12 : σ12.vars "ok" = σ11.vars "ok" :=
    hF12 "ok" (by simp [SCL, SCO, SDL, D3Day.SDAY, SSW, S1, S2])
  have hA12 : σ12.arrs "TK" = arr := by rw [hAeq12]; exact A11
  have hRB12 : ∀ j, (σ12.arrs "R").getD j 0 < B := hRInv12.small
  -- fnd := 0, then scan for a mark
  have sFnd := asgE (B := B) "fnd" (.lit 0) σ12 (by simp [MisBlk.small]; omega)
  set σ13 := σ12.setVar "fnd" (MisBlk.den σ12 (.lit 0)) with hσ13
  have fnd13 : σ13.vars "fnd" = 0 := by simp [hσ13, MisBlk.den, Env.setVar]
  have R13 : σ13.arrs "R" = σ12.arrs "R" := by simp [hσ13, Env.setVar]
  have A13 : σ13.arrs "TK" = arr := by simp [hσ13, Env.setVar, hA12]
  have O13 : σ13.out = σ11.out := by simp [hσ13, Env.setVar, hO12]
  have PP13 : σ13.vars "PP" = (n + 1) ^ m := by simp [hσ13, Env.setVar, hC12.vPP]
  have ok13 : σ13.vars "ok" = σ11.vars "ok" := by simp [hσ13, Env.setVar, hokEq12]
  have hRB13 : ∀ j, (σ13.arrs "R").getD j 0 < B := by rw [R13]; exact hRB12
  obtain ⟨σ14, r14, fnd14, hA14, hO14, hF14⟩ := scanLoop_run (B := B) σ13 (σ13.arrs "R")
      ((n + 1) ^ m) rfl PP13 (by rw [R13]; have := hRInv12.len; omega) hRB13 (by omega)
      (by omega)
  have hok14 : σ14.vars "ok" = σ11.vars "ok" := by
    rw [hF14 "ok" (by simp [SSC])]; exact ok13
  have hA14' : σ14.arrs "TK" = arr := by rw [hA14]; exact A13
  have hO14' : σ14.out = σ11.out := by rw [hO14]; exact O13
  have hexIff : (∃ s < (n + 1) ^ m, (σ12.arrs "R").getD s 0 = 1) ↔
      (Reach m kp (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
        (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n).Nonempty := RT_final (σ12.arrs "R") hRT12
  have hok11le : σ11.vars "ok" ≤ 1 := by rw [ok11]; exact flagTo_le _ _ _
  by_cases hokv : σ11.vars "ok" = 1
  · -- the checks pass: derive Valid/DID, then decide by real reachability
    have hNeq : N = arr.getD 1 0 * arr.getD 0 0 := by rw [hN', hm0', hn']
    have hValidIff : (∀ j < N, Pass arr j) ↔ Valid arr := by rw [hNeq]; exact Iff.rfl
    have hDIDiff : (∀ j < N, DIDp arr n j) ↔ DID arr := by rw [hNeq, hn']; exact Iff.rfl
    have hok11eq1 : flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N = 1 := by
      rw [← ok11]; exact hokv
    have hvd := (flagTo_eq_one _).mp hok11eq1
    have hPass1 := (flagTo_eq_one _).mp hvd.1
    have hValid : Valid arr := hValidIff.mp hPass1.2
    have hDID : DID arr := hDIDiff.mp hvd.2
    have hgetn : arr.getD 0 0 = n := hn'.symm
    have hgetm : arr.getD 1 0 = m := hgm
    have hclients : (instOf arr hValid).clients = n := hgetn
    have hdays' : (instOf arr hValid).days = m := hgetm
    have hddeq : ∀ j < n, ddA arr j = D3Prog.ddI (instOf arr hValid) j :=
      fun j hj => ddA_eq_ddI hValid hgetn hgetm hm0 hj
    have hordcongr : ∀ c < n,
        ordOf (ddA arr) n c = ordOf (D3Prog.ddI (instOf arr hValid)) n c :=
      fun c hc => ordOf_congr hc hddeq
    have hR0ordI : ∀ c < n, R0.getD ((n + 1) ^ m * (kp + 1) + c) 0 =
        D3Prog.ordI (instOf arr hValid) c := fun c hc => by
      rw [hR0eq c hc, hordcongr c hc]
      unfold D3Prog.ordI
      rw [hclients]
    have hqeq : ∀ i < m, ∀ c < n,
        qF arr R0 ((n + 1) ^ m * (kp + 1)) n i c = D3Prog.qI (instOf arr hValid) i c :=
      fun i hi c hc => qF_eq_qI hValid hgetn hgetm hi hc (hR0ordI c hc)
    have heeq : ∀ c < n,
        eOrd arr R0 ((n + 1) ^ m * (kp + 1)) c = D3Prog.eI (instOf arr hValid) c :=
      fun c hc => eOrd_eq_eI hValid hgetn hgetm hm0 hnpos hc (hR0ordI c hc)
    have hReachEq : Reach m kp (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
        (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n =
        Reach m kp (D3Prog.qI (instOf arr hValid)) (D3Prog.eI (instOf arr hValid)) n :=
      reach_eq hqeq heeq
    have hDD : (instOf arr hValid).DayIndepD := (did_iff arr hValid).2 hDID
    have hdayspos : 0 < (instOf arr hValid).days := by rw [hdays']; exact hm0
    have hFairIff0 := D3Prog.hasKFair_iff_reach hDD hdayspos kp
    rw [hdays', hclients] at hFairIff0
    have hparam : paramOf arr = kp := by
      unfold paramOf
      rw [← hn', ← hm0', ← hN']
    have hReachIff : (instOf arr hValid).HasKFairSchedule (paramOf arr) ↔
        (Reach m kp (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
          (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n).Nonempty := by
      rw [hparam, hFairIff0, hReachEq]
    by_cases hReach : (Reach m kp (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
        (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) n).Nonempty
    · -- a fair schedule exists: the scan finds a mark
      have hex : ∃ s < (n + 1) ^ m, (σ12.arrs "R").getD s 0 = 1 := hexIff.2 hReach
      have hHasKFair : (instOf arr hValid).HasKFairSchedule (paramOf arr) :=
        hReachIff.2 hReach
      have hDecideOk : decideOk arr m := ⟨hValid, hDID, hgm, hHasKFair⟩
      have hfnd14 : σ14.vars "fnd" = 1 := by
        rw [fnd14, fnd13]
        exact if_pos (Or.inr (by rw [R13]; exact hex))
      have hokT : (Cond.eq (V "ok") (.lit 1)).evalB B σ14 = some true :=
        MisBlk.condEq_true _ _ σ14 (by show σ14.vars "ok" < B; rw [hok14]; omega)
          (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hok14, hokv])
      have hfndT : (Cond.eq (V "fnd") (.lit 1)).evalB B σ14 = some true :=
        MisBlk.condEq_true _ _ σ14 (by show σ14.vars "fnd" < B; rw [hfnd14]; omega)
          (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hfnd14])
      obtain ⟨σ15, r15, o15, -, -⟩ := emitLit_spec (B := B) 1 Sz (by omega) (hs 1 (by omega))
        σ14 trivial
      obtain ⟨σ16, r16, o16, -, -⟩ := emitLit_spec (B := B) 0 Sz (by omega) (hs 0 (by omega))
        σ15 trivial
      have hPPl : (n + 1) ^ m ≤ (l + 1) ^ m := Nat.pow_le_pow_left (by omega) m
      refine ⟨σ16, ?_, ?_⟩
      · have dpBodyRun := r5.seq (s6.seq (r7.seq (s8.seq (s9.seq (r9'.seq (r10.seq (s11.seq
            (r12.seq (sFnd.seq r14)))))))))
        refine (r1.seq (r2.seq (s3.seq (r4.seq
          (Run.ite_true hT (dpBodyRun.seq (Run.ite_true hokT
            (Run.ite_true hfndT (r15.seq r16))))))))).mono ?_
        simp only [Cond.size, Expr.size, KaccDPos]
        linarith [hcl, hrk, hsc, hNl, Nat.zero_le Sz, Nat.zero_le (KpowCom m), Nat.zero_le (KcheckM m), Nat.zero_le (Krej9 Sz)]
      · rw [o16, o15, hO14', O11, if_pos hDecideOk, List.append_assoc]
    · -- no fair schedule: the scan finds nothing
      have hnex : ¬ ∃ s < (n + 1) ^ m, (σ12.arrs "R").getD s 0 = 1 :=
        fun h => hReach (hexIff.1 h)
      have hHasKFairNot : ¬ (instOf arr hValid).HasKFairSchedule (paramOf arr) :=
        fun h => hReach (hReachIff.1 h)
      have hDecideOk : ¬ decideOk arr m := by
        rintro ⟨hv, -, -, hk⟩
        exact hHasKFairNot hk
      have hfnd14 : σ14.vars "fnd" = 0 := by
        have hcond : ¬ (σ13.vars "fnd" = 1 ∨
            ∃ s < (n + 1) ^ m, (σ13.arrs "R").getD s 0 = 1) := by
          rintro (h1 | h1)
          · rw [fnd13] at h1; omega
          · rw [R13] at h1; exact hnex h1
        rw [fnd14, if_neg hcond]
      have hokT : (Cond.eq (V "ok") (.lit 1)).evalB B σ14 = some true :=
        MisBlk.condEq_true _ _ σ14 (by show σ14.vars "ok" < B; rw [hok14]; omega)
          (by simp [MisBlk.small]; omega) (by simp [MisBlk.den, hok14, hokv])
      have hfndF : (Cond.eq (V "fnd") (.lit 1)).evalB B σ14 = some false :=
        MisBlk.condEq_false _ _ σ14 (by show σ14.vars "fnd" < B; rw [hfnd14]; omega)
          (by simp [MisBlk.small]; omega) (by show σ14.vars "fnd" ≠ 1; rw [hfnd14]; omega)
      obtain ⟨σR, rR, oR⟩ := rejT9_run (B := B) Sz σ14 hs (by omega)
      refine ⟨σR, ?_, ?_⟩
      · have dpBodyRun := r5.seq (s6.seq (r7.seq (s8.seq (s9.seq (r9'.seq (r10.seq (s11.seq
            (r12.seq (sFnd.seq r14)))))))))
        refine (r1.seq (r2.seq (s3.seq (r4.seq (Run.ite_true hT (dpBodyRun.seq
          (Run.ite_true hokT (Run.ite_false hfndF rR)))))))).mono ?_
        simp only [Cond.size, Expr.size, KaccDPos]
        linarith [hcl, hrk, hsc, hNl, Nat.zero_le Sz, Nat.zero_le (KpowCom m), Nat.zero_le (KcheckM m), Nat.zero_le (Krej9 Sz)]
      · rw [oR, hO14', O11, if_neg hDecideOk]
  · -- a check fails: reject regardless of the dynamic program's outcome
    have hDecideOk : ¬ decideOk arr m := by
      rintro ⟨hv, hdid, -, -⟩
      apply hokv
      have hNeq : N = arr.getD 1 0 * arr.getD 0 0 := by rw [hN', hm0', hn']
      have hValidIff : (∀ j < N, Pass arr j) ↔ Valid arr := by rw [hNeq]; exact Iff.rfl
      have hDIDiff : (∀ j < N, DIDp arr n j) ↔ DID arr := by rw [hNeq, hn']; exact Iff.rfl
      rw [ok11, flagTo_eq_one]
      exact ⟨by rw [flagTo_eq_one]; exact ⟨rfl, hValidIff.mpr hv⟩, hDIDiff.mpr hdid⟩
    have hokF : (Cond.eq (V "ok") (.lit 1)).evalB B σ14 = some false :=
      MisBlk.condEq_false _ _ σ14 (by show σ14.vars "ok" < B; rw [hok14]; omega)
        (by simp [MisBlk.small]; omega) (by show σ14.vars "ok" ≠ 1; rw [hok14]; exact hokv)
    obtain ⟨σR, rR, oR⟩ := rejT9_run (B := B) Sz σ14 hs (by omega)
    refine ⟨σR, ?_, ?_⟩
    · have dpBodyRun := r5.seq (s6.seq (r7.seq (s8.seq (s9.seq (r9'.seq (r10.seq (s11.seq
          (r12.seq (sFnd.seq r14)))))))))
      refine (r1.seq (r2.seq (s3.seq (r4.seq
        (Run.ite_true hT (dpBodyRun.seq (Run.ite_false hokF rR))))))).mono ?_
      simp only [Cond.size, Expr.size, KaccDPos]
      linarith [hcl, hrk, hsc, hNl, Nat.zero_le Sz, Nat.zero_le (KpowCom m), Nat.zero_le (KcheckM m), Nat.zero_le (Krej9 Sz)]
    · rw [oR, hO14', O11, if_neg hDecideOk]

open scoped Classical in
set_option maxHeartbeats 12800000 in
/-- **The whole of the algorithm, for a fixed positive number of days.** -/
theorem acceptDPos_run (m : ℕ) (hm0 : 0 < m) (Sz l : ℕ) (arr : List ℕ) (σ : Env)
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
    (hE2 : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), 2 * arr.getD k 0 + 16 < B)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l) (hA : σ.arrs "TK" = arr)
    (hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B)
    (hPKB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 + 8 < B)
    (hRlen : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 ≤
      (σ.arrs "R").length)
    (hR0zero : ∀ j, (σ.arrs "R").getD j 0 = 0) (hRB : ∀ j, (σ.arrs "R").getD j 0 < B) :
    ∃ σ', Run B (acceptDPos m) σ σ' (KaccDPos m Sz l) ∧
      σ'.out = σ.out ++ (if decideOk arr m then bitsNat 1 ++ bitsNat 0
        else natBits (Lax117284.TwoSatisfiability.encodeFormula
          Lax117284.TwoSatisfiability.unsatisfiable)) := by
  set n := arr.getD 0 0 with hn'
  set m0 := arr.getD 1 0 with hm0'
  set N := m0 * n with hN'
  set kp := arr.getD (2 + 2 * N) 0 with hkp'
  have hB2 : 6 < B := by omega
  by_cases hgood : m0 = m ∧ ¬ (m0 < kp ∧ 0 < n)
  · -- the gate passes: m0 = m and (no client or kp ≤ m), so n ≤ N ≤ l
    have hmeq : m0 = m := hgood.1
    have hgk : ¬ (m0 < kp ∧ 0 < n) := hgood.2
    obtain ⟨σ1, σ2, σ3, σ4, r1, r2, s3, r4, gp⟩ := gatePrefix_run (B := B) m arr σ n m0 N kp
      hn' hm0' hN' hkp' hE hL hlen hNB hnn hmm hC1 hC2 hCC htq hCU hA
    have ho4 : σ4.vars "ok" = if m0 = m then (if m0 < kp ∧ 0 < n then 0 else 1) else 0 :=
      gp.ok4
    have hm4 : σ4.vars "m" = m0 := gp.m4
    have A4 : σ4.arrs "TK" = arr := gp.A4
    have O3 : σ4.out = σ.out := gp.O4
    have n4 : σ4.vars "n" = n := gp.n4
    have kp4 : σ4.vars "kp" = kp := gp.kp4
    have N4 : σ4.vars "N" = N := gp.N4
    have ho4' : σ4.vars "ok" = 1 := by rw [ho4, if_pos hmeq, if_neg hgk]
    have hT : (Cond.eq (V "ok") (.lit 1)).evalB B σ4 = some true :=
      MisBlk.condEq_true _ _ σ4 (by show σ4.vars "ok" < B; omega) (by simp [MisBlk.small]; omega)
        (by simp [MisBlk.den, ho4'])
    have hmN : n ≤ N := by rw [hN']; rw [hmeq] at hm4 ⊢; exact Nat.le_mul_of_pos_left _ hm0
    have hnl : n ≤ l := by omega
    have hgm : arr.getD 1 0 = m := hm0'.symm.trans hmeq
    obtain ⟨σ11, σ5, σ6, σ7, σ8, σ9, σ9', σ10, R0, r5, s6, r7, s8, s9, r9', r10, s11, dps⟩ :=
      dpSetup_run (B := B) m hm0 arr σ σ4 n N kp hn' hN' hkp' hE hlen hNB hL hnn hmm hC1 hC2 hCC htq hCU hR0zero hRB hPPB hPKB
        hRlen hgm hgk gp
    have A11 : σ11.arrs "TK" = arr := dps.A11
    have n11 : σ11.vars "n" = n := dps.n11
    have m11 : σ11.vars "m" = m := dps.m11
    have PK11 : σ11.vars "PK" = (n + 1) ^ m * (kp + 1) := dps.PK11
    have PP11 : σ11.vars "PP" = (n + 1) ^ m := dps.PP11
    have kp11 : σ11.vars "kp" = kp := dps.kp11
    have pk11 : σ11.vars "pk" = (n + 1) ^ m * kp := dps.pk11
    have b111 : σ11.vars "b1" = n + 1 := dps.b111
    have ok11 : σ11.vars "ok" = flagTo (DIDp arr n) (flagTo (Pass arr) 1 N) N := dps.ok11
    have O11 : σ11.out = σ.out := dps.O11
    have R11 : σ11.arrs "R" = R0.set 0 1 := dps.R11
    have hR11len : (n + 1) ^ m * (kp + 1) + n ≤ (σ11.arrs "R").length := dps.hR11len
    have RB11 : ∀ j, (σ11.arrs "R").getD j 0 < B := dps.RB11
    have RTinit : RT m kp n (qF arr R0 ((n + 1) ^ m * (kp + 1)) n)
        (eOrd arr R0 ((n + 1) ^ m * (kp + 1))) 0 0 (σ11.arrs "R") := dps.RTinit
    have hR0eq : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 = ordOf (ddA arr) n c' :=
      dps.hR0eq
    have hRv0 : ∀ c' < n, R0.getD ((n + 1) ^ m * (kp + 1) + c') 0 < n := dps.hRv0
    -- the client loop
    by_cases hn0 : n = 0
    · -- no clients: the loop does nothing, the initial table already decides everything
      exact n0Case_run (B := B) m Sz l arr σ σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9 σ9' σ10 σ11 n N kp R0
        hs r1 r2 s3 r4 r5 s6 r7 s8 s9 r9' r10 s11 hL hnn hmm hC1 hC2 hCC htq hCU hPPB hT hn' hN' hl hnl hn0 hgm A11 n11 PP11 ok11 O11
        RB11 hR11len RTinit
    · -- clients: n > 0, run the real dynamic program
      exact nPosCase_run (B := B) m hm0 Sz l arr σ σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9 σ9' σ10 σ11 n N kp
        R0 hs r1 r2 s3 r4 r5 s6 r7 s8 s9 r9' r10 s11 hL hnn hmm hC1 hC2 hCC htq hCU hPPB hT hE2 hlen hNB hPKB hn' hN' hkp' hl hnl
        (by omega) (by by_contra h; exact hgk ⟨by omega, by omega⟩) hgm A11 n11 m11 PK11 PP11 kp11 pk11 b111 ok11 O11 R11 hR11len RB11 RTinit hR0eq
        hRv0

  · -- the gate fails: m0 ≠ m, or a client is present and m < kp
    exact gateFail_run (B := B) m Sz l arr σ hs hE hL hlen hNB hnn hmm hC1 hC2 hCC htq hCU hA hgood

end Lax117284Proofs.Machine.D3Accept

end

/-! ### `Lax117284Proofs.Machine.WrapR` -/

section
/-!
A reduction on the numbers of its input, once and for all: the program reads the word, tokenizes it
against a format of numbers, and then either runs the phase that writes the image or writes the
rejected word. What differs from one reduction to the next is the format, the phase and the
semantics of the image, and they are the fields of the structure.
-/

namespace Lax117284Proofs.Machine.WrapR

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TokLoop Lax117284Proofs.Machine.TokBound Lax117284Proofs.Machine.TokRun
open Lax117284Proofs.Machine.FreeAccept

open scoped Classical

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- **A reduction that reads numbers and writes numbers.** -/
structure WrapR where
  /-- The length of the third array, from the length of the input. -/
  Rext : ℕ → ℕ
  /-- The format of the numbers the word is a stream of. -/
  E : Format
  /-- The streams of the format. -/
  Sh : List ℕ → Prop
  /-- What the format expects next, as a command. -/
  nk : Com
  Knk : ℕ
  /-- The tokenizer does not write the third array. -/
  nk_warrs : "R" ∉ nk.warrs
  hnk : ∀ (B Bt cap : ℕ), 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B → NkSpec B Bt E cap nk Knk
  hconf : ∀ ns, Sh ns → Conforms E (ns.map Tok.num)
  hshape : ∀ ts, Conforms E ts → ∃ ns, ts = ns.map Tok.num ∧ Sh ns
  /-- The reduction, as a map on words. -/
  red : Word → Word
  /-- The streams that are mapped to an image. -/
  cond : List ℕ → Prop
  /-- The image, as a word. -/
  outW : List ℕ → Word
  sem_acc : ∀ ns, Sh ns → cond ns → red (numCode ns) = outW ns
  /-- The word every other word is sent to. -/
  rejW : Word
  sem_rej : ∀ w, ¬ (∃ ns, w = numCode ns ∧ Sh ns ∧ cond ns) → red w = rejW
  /-- The command that writes it. -/
  rej : Com
  Krej : ℕ → ℕ
  rejRun : ∀ (B Sz : ℕ) (σ : Env), (∀ v, v + 4 < B → v.size ≤ Sz) → 6 < B →
    ∃ σ', Run B rej σ σ' (Krej Sz) ∧ σ'.out = σ.out ++ natBits rejW
  /-- The phase that runs once the tokenizer has accepted. -/
  acc : Com
  Kacc : ℕ → ℕ → ℕ
  Kmono : ∀ Sz a b, a ≤ b → Kacc Sz a ≤ Kacc Sz b
  accRun : ∀ (B Sz L : ℕ) (ns arr : List ℕ) (σ : Env), Sh ns → arr.take ns.length = ns →
    σ.arrs "TK" = arr → σ.arrs "R" = List.replicate (Rext L) 0 → ns.length ≤ L →
    (∀ v ∈ ns, v < 2 ^ (L + 1)) →
    2 ^ (2 * L + 4) + 8 * L + 64 ≤ B → (∀ v, v + 4 < B → v.size ≤ Sz) →
    ∃ σ', Run B acc σ σ' (Kacc Sz ns.length) ∧
      σ'.out = σ.out ++ (if cond ns then natBits (outW ns) else natBits rejW)

variable (W : WrapR)

/-- The reduction: read the word, tokenize it against the format, and then either write the
output or the rejected word. -/
def WrapR.mainW : Com :=
  .seq ReadAll.readAll (.seq (tokRun "a" "L" W.nk)
    (.ite (.eq (.var "ph") (.lit 0))
      (.ite (.eq (.var "L") (.lit 0))
        (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej) W.rej))

/-- The cost of the whole program on an input of length `l` at word size `Sz`. -/
def WrapR.Kmain (l Sz : ℕ) : ℕ :=
  (12 * l + 10) + (20 + W.Knk + ((100 + W.Knk + 4) * l + 6)) + 20 + W.Kacc Sz l + W.Krej Sz

/-- What the reduction computes, on the zeros and ones of its input. -/
noncomputable def WrapR.redBits (y : List ℕ) : List ℕ := natBits (W.red (bitsOf y))

lemma code_map_num' (ns : List ℕ) : code (ns.map Tok.num) = numCode ns :=
  Lax117284Proofs.Machine.FreeMain.code_map_num ns

/-- **A word the tokenizer accepts is the numbers of a stream of the format.** -/
theorem WrapR.accepted_stream (y : List ℕ) (hacc : Accepts W.E (run W.E init (bitsOf y))) :
    ∃ ns : List ℕ, bitsOf y = numCode ns ∧ W.Sh ns ∧
      (run W.E init (bitsOf y)).toks = ns.map Tok.num := by
  obtain ⟨hcode, hconf⟩ := accept_sound W.E hacc
  obtain ⟨ns, hns, hsh⟩ := W.hshape _ hconf
  refine ⟨ns, ?_, hsh, hns⟩
  rw [← hcode, hns, code_map_num']

theorem WrapR.bits_accept (y : List ℕ) (ns : List ℕ) (hw : bitsOf y = numCode ns) (hsh : W.Sh ns) :
    W.redBits y = if W.cond ns then natBits (W.outW ns) else natBits W.rejW := by
  unfold WrapR.redBits
  rw [hw]
  by_cases hc : W.cond ns
  · rw [if_pos hc, W.sem_acc ns hsh hc]
  · rw [if_neg hc, W.sem_rej]
    rintro ⟨ns', hw', hs', hc'⟩
    have hnn : ns' = ns := (numCode_inj hw').symm
    subst hnn
    exact hc hc'

theorem WrapR.bits_reject (y : List ℕ) (hn : ¬ Accepts W.E (run W.E init (bitsOf y))) :
    W.redBits y = natBits W.rejW := by
  unfold WrapR.redBits
  rw [W.sem_rej]
  rintro ⟨ns', hw', hs', -⟩
  apply hn
  have := (accept_complete W.E (ns'.map Tok.num) (W.hconf ns' hs')).1
  rwa [code_map_num', ← hw'] at this

lemma warrs_readAll : ReadAll.readAll.warrs = ["a"] := by
  simp [ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, Com.warrs]

variable {W} {B : ℕ} (y : List ℕ)

theorem mainW_spec (hyB : ∀ v ∈ y, v < B)
    (hB : 2 ^ (2 * y.length + 4) + 8 * y.length + 64 ≤ B) :
    ∃ σ', Run B W.mainW (initEnv (fun a => if a = "R" then W.Rext y.length else y.length) (y.length :: y)) σ'
        (W.Kmain y.length B.size) ∧ σ'.out = W.redBits y := by
  have hpow : y.length < 2 ^ y.length := Nat.lt_two_pow_self
  have hpow1 : (2 : ℕ) ^ (y.length + 1) = 2 * 2 ^ y.length := by ring
  have hpow2 : (2 : ℕ) ^ (2 * y.length + 4) = 16 * (2 ^ y.length * 2 ^ y.length) := by ring
  have hPP : 2 ^ y.length ≤ 2 ^ y.length * 2 ^ y.length :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hs : ∀ v, v + 4 < B → v.size ≤ B.size := fun v hv => Nat.size_le_size (by omega)
  set σ0 := initEnv (fun a => if a = "R" then W.Rext y.length else y.length) (y.length :: y) with hσ0
  -- read the word
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, -⟩, fv1, fa1, -, -⟩ :=
    (ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨by simp [hσ0, initEnv], by simp [hσ0, initEnv], by simp [hσ0, initEnv]⟩
  have tk1 : σ1.arrs "TK" = List.replicate y.length 0 := by
    rw [fa1 "TK" (by simp [warrs_readAll])]; simp [hσ0, initEnv]
  have hR1 : σ1.arrs "R" = List.replicate (W.Rext y.length) 0 := by
    rw [fa1 "R" (by simp [warrs_readAll])]; simp [hσ0, initEnv]
  -- tokenize
  have hnk : NkSpec B (2 ^ y.length) W.E y.length W.nk W.Knk :=
    W.hnk B _ _ (by nlinarith)
  obtain ⟨σ2, r2, ⟨hR, ho2, hlen2⟩, fv2, fa2, -, -⟩ := (tokRun_spec (B := B) "a" "L" W.nk (by decide)
    y y.length (le_refl _) hnk (by omega) hyB).frame σ1
    ⟨by rw [ha1, List.take_length], hL1, by rw [tk1]; simp, ho1⟩
  have hR2 : σ2.arrs "R" = List.replicate (W.Rext y.length) 0 := by
    rw [fa2 "R" (by
      simp [tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
        TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
        Com.warrs, W.nk_warrs])]
    exact hR1
  set st := run W.E init (bitsOf y) with hst
  have hbd : Bd st y.length := by
    have h := bd_stAt W.E y y.length (le_refl _)
    have e : stAt W.E y y.length = st := by unfold stAt; rw [List.take_length]
    rwa [e] at h
  have hkB : σ2.vars "kind" < B := by
    rw [hR.kind]; cases W.E st.toks <;> simp [kcode] <;> omega
  have hphB : σ2.vars "ph" < B := by rw [hR.ph]; have := hbd.ph; omega
  have hLB : σ2.vars "L" < B := by rw [hR.L]; have := hbd.L; omega
  by_cases hacc : Accepts W.E st
  · obtain ⟨h0, hL0, hk⟩ := hacc
    have hph : σ2.vars "ph" = 0 := by rw [hR.ph]; exact h0
    have hLv : σ2.vars "L" = 0 := by rw [hR.L]; exact hL0
    have hkind : σ2.vars "kind" = 2 := by rw [hR.kind, hk]; rfl
    obtain ⟨ns, hw, hsh, hns⟩ := W.accepted_stream y ⟨h0, hL0, hk⟩
    rw [← hst] at hns
    have hlenT : ns.length ≤ y.length := by
      have := hbd.T; rw [hns] at this; simpa using this
    have hval : ∀ v ∈ ns, v < 2 ^ (y.length + 1) := fun v hv => by
      have := hbd.tok (.num v) (by rw [hns]; exact List.mem_map_of_mem hv)
      simpa [Tok.val] using this
    obtain ⟨hTv, hTK⟩ := hR.tok
    have harr : (σ2.arrs "TK").take ns.length = ns := by
      rw [hns] at hTK
      simpa [List.map_map, Function.comp_def, Tok.val] using hTK
    obtain ⟨σa, ra, oa⟩ := W.accRun B B.size y.length ns (σ2.arrs "TK") σ2 hsh harr rfl hR2 hlenT hval hB hs
    have rite := Run.ite_true (d := W.rej)
      (cond_lit_true (B := B) hph (by omega))
      (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hLv (by omega))
        (Run.ite_true (d := W.rej) (cond_lit_true (B := B) hkind (by omega)) ra))
    refine ⟨σa, (r1.seq (r2.seq rite)).mono ?_, ?_⟩
    · unfold WrapR.Kmain
      simp only [Cond.size, Expr.size]
      have := W.Kmono B.size ns.length y.length hlenT
      omega
    · rw [oa, ho2, W.bits_accept y ns hw hsh]
      simp only [List.nil_append]
  · have hrej := W.bits_reject y hacc
    obtain ⟨σr, rr, orr⟩ := W.rejRun B B.size σ2 hs (by omega)
    have houtr : σr.out = W.redBits y := by
      rw [orr, ho2, hrej]; simp
    have hKrej : W.Krej B.size ≤ W.Kmain y.length B.size := by
      unfold WrapR.Kmain; omega
    by_cases h0 : st.ph = 0
    · by_cases hL0 : st.L = 0
      · have hk : W.E st.toks ≠ .done := fun hk => hacc ⟨h0, hL0, hk⟩
        have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_true (d := W.rej) (cond_lit_true (B := B) (hR.L.trans hL0) (by omega))
            (Run.ite_false (c := W.acc) (cond_lit_false (B := B)
              (by rw [hR.kind]; exact fun h => hk (kcode_done.mp h)) hkB (by omega)) rr))
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapR.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
      · have rite := Run.ite_true (d := W.rej)
          (cond_lit_true (B := B) (hR.ph.trans h0) (by omega))
          (Run.ite_false (c := Com.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej)
            (cond_lit_false (B := B) (by rw [hR.L]; exact hL0) hLB (by omega)) rr)
        exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
          unfold WrapR.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩
    · have rite := Run.ite_false
        (c := Com.ite (.eq (.var "L") (.lit 0))
          (.ite (.eq (.var "kind") (.lit 2)) W.acc W.rej) W.rej)
        (cond_lit_false (B := B) (by rw [hR.ph]; exact h0) hphB (by omega)) rr
      exact ⟨σr, (r1.seq (r2.seq rite)).mono (by
        unfold WrapR.Kmain; simp only [Cond.size, Expr.size]; omega), houtr⟩

end Lax117284Proofs.Machine.WrapR

end

/-! ### `Lax117284Proofs.Machine.WrapRFinal` -/

section
/-!
A reduction of the shape of `Wrap` is polynomial-time computable: on the word RAM, and hence on a
Turing machine, once its program is laid out in memory and its accepting phase is linear in the
size of its input times the word size.
-/

namespace Lax117284Proofs.Machine.WrapRFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.WrapR Lax117284Proofs.Machine.FreeFinal
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding

variable (W : WrapR) (layout : Layout)

theorem solves (hok : Com.Ok layout W.mainW) :
    Solves layout W.mainW FreeFinal.Shape (fun x => W.redBits x.tail) (fun x => Bd x.tail)
      (fun x => W.Kmain x.tail.length (Bd x.tail).size) where
  ok := hok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    have hpow : x.tail.length < 2 ^ (2 * x.tail.length + 4) := by
      have := Nat.lt_two_pow_self (n := x.tail.length)
      have h2 : 2 ^ x.tail.length ≤ 2 ^ (2 * x.tail.length + 4) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd; omega
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := WrapR.mainW_spec (W := W) (B := Bd x.tail) x.tail
      (fun v hv => by
        have := le_Mx hv
        have h2 : 2 ^ (2 * x.tail.length + 4) ≥ 1 := Nat.one_le_two_pow
        unfold Bd; omega)
      (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

theorem prog_runs (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 3)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (w : ℕ) (x : List ℕ)
    (hfit : 202 + 3 * Bd x ≤ 2 ^ w) :
    ∃ t ≤ 10 * W.Kmain x.length (Bd x).size + 1,
      RunsTo w (compileProgram layout W.mainW) (x.length :: x) (W.redBits x) t := by
  have hs : Solves layout W.mainW {z | z = x.length :: x} (fun z => W.redBits z.tail)
      (fun z => Bd z.tail) (fun z => W.Kmain z.tail.length (Bd z.tail).size) :=
    ⟨(solves W layout hok).ok, fun z hz => (solves W layout hok).inp z
      (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => (solves W layout hok).run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w)
    (T := fun z => 10 * W.Kmain z.tail.length (Bd z.tail).size + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 64 ≤ Bd x := by
        have := Nat.zero_le (2 ^ (2 * x.length + 4))
        unfold Bd; omega
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, harr, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa using hrun⟩

/-- **The reduction is a polynomial-time word RAM computation on the zeros and ones of its
input**, when its accepting phase costs at most `C · (Sz + 1) · (l + 1) ^ e`. -/
theorem ramPolytimeE (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 3)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (C e : ℕ) (he : 1 ≤ e)
    (hK : ∀ Sz l, W.Kacc Sz l ≤ C * (Sz + 1) * (l + 1) ^ e)
    (hKr : ∀ Sz, W.Krej Sz ≤ C * (Sz + 1)) :
    RamPolytime W.redBits := by
  refine Lax117284Proofs.Machine.RamBridge2.ramPolytime_of_wordlen (d := 2) (K := 10)
    (prog := compileProgram layout W.mainW)
    (Polynomial.C (100 * (2 * C + W.Knk + 1000)) * (Polynomial.X + Polynomial.C 1) ^ (e + 1))
    (by omega) ?_ ?_
  · intro x v hv
    unfold WrapR.redBits at hv
    simp only [natBits, List.mem_map] at hv
    obtain ⟨b, -, rfl⟩ := hv
    have : (2 : ℕ) ^ 10 ≤ 2 ^ (2 * bitSize x + 10) := Nat.pow_le_pow_right (by omega) (by omega)
    split <;> omega
  · intro w x hw
    have hB := Bd_lt x
    have hlen := length_le_bitSize x
    have hfit : 202 + 3 * Bd x ≤ 2 ^ w := by
      have h1 : (2 : ℕ) ^ (2 * bitSize x + 11) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
      have e : (2 : ℕ) ^ (2 * bitSize x + 11) = 16 * 2 ^ (2 * bitSize x + 7) := by ring
      have h5 : 128 ≤ 2 ^ (2 * bitSize x + 7) := by
        calc (128 : ℕ) = 2 ^ 7 := by norm_num
          _ ≤ 2 ^ (2 * bitSize x + 7) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    obtain ⟨t, ht, hrun⟩ := prog_runs W layout hok harr hsc w x hfit
    refine ⟨t, ?_, hrun⟩
    have hsz : (Bd x).size ≤ 2 * bitSize x + 7 := Nat.size_le.mpr hB
    unfold WrapR.Kmain at ht
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    obtain ⟨u, hu⟩ : ∃ u, u = bitSize x + 1 := ⟨_, rfl⟩
    rw [← hu]
    have hu1 : 1 ≤ u := by omega
    have hT1 : u ≤ u ^ (e + 1) := Nat.le_self_pow (by omega) u
    have hT0 : 1 ≤ u ^ (e + 1) := le_trans hu1 hT1
    have hpe : (x.length + 1) ^ e ≤ u ^ e := Nat.pow_le_pow_left (by omega) e
    have h8 : (Bd x).size + 1 ≤ 8 * u := by omega
    have hTe : u * u ^ e = u ^ (e + 1) := by rw [pow_succ']
    have hKa : W.Kacc (Bd x).size x.length ≤ 8 * C * u ^ (e + 1) := by
      calc W.Kacc (Bd x).size x.length ≤ C * ((Bd x).size + 1) * (x.length + 1) ^ e := hK _ _
        _ ≤ C * (8 * u) * u ^ e := Nat.mul_le_mul (Nat.mul_le_mul_left _ h8) hpe
        _ = 8 * C * (u * u ^ e) := by ring
        _ = 8 * C * u ^ (e + 1) := by rw [hTe]
    have hKb : W.Krej (Bd x).size ≤ 8 * C * u ^ (e + 1) := by
      calc W.Krej (Bd x).size ≤ C * ((Bd x).size + 1) := hKr _
        _ ≤ C * (8 * u) := Nat.mul_le_mul_left _ h8
        _ = 8 * C * u := by ring
        _ ≤ 8 * C * u ^ (e + 1) := Nat.mul_le_mul_left _ hT1
    have hL1 : (W.Knk + 116) * x.length ≤ (W.Knk + 116) * u ^ (e + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hL2 : W.Knk + 56 ≤ (W.Knk + 56) * u ^ (e + 1) := Nat.le_mul_of_pos_right _ hT0
    have hmain : 12 * x.length + 10 + (20 + W.Knk + ((100 + W.Knk + 4) * x.length + 6)) + 20 +
        W.Kacc (Bd x).size x.length + W.Krej (Bd x).size ≤
        (2 * W.Knk + 172 + 16 * C) * u ^ (e + 1) := by nlinarith
    nlinarith [hmain, hT0, Nat.zero_le C, Nat.zero_le W.Knk]

/-- **The reduction is polynomial-time computable.** -/
theorem polyTimeE (hok : Com.Ok layout W.mainW) (harr : layout.arrays.length = 3)
    (hsc : layout.temps + layout.scalars.length ≤ 200) (C e : ℕ) (he : 1 ≤ e)
    (hK : ∀ Sz l, W.Kacc Sz l ≤ C * (Sz + 1) * (l + 1) ^ e)
    (hKr : ∀ Sz, W.Krej Sz ≤ C * (Sz + 1)) :
    Nonempty (Turing.TM2ComputableInPolyTime id id W.red) := by
  refine Lax117284Proofs.Machine.RamToTuring.polyTime_of_ram
    (ramPolytimeE W layout hok harr hsc C e he hK hKr) ?_
  intro w
  unfold WrapR.redBits
  rw [bitsOf_natBits]

end Lax117284Proofs.Machine.WrapRFinal

end

/-! ### `Lax117284Proofs.Machine.D3Final` -/

section
/-!
The reduction that decides day-independent due dates with a fixed number of days is
polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.D3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Accept
open Lax117284Proofs.Machine.T9Final Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.D3Sem (DID did_iff goodM reduceM reduceM_correct uniform_iff_good
  divmod_row)
open Lax117284Proofs.Machine.D3Accept
open Lax117284Proofs.Machine.D3Pow (checkM checkMLoop powCom KcheckM KpowCom)
open Lax117284Proofs.Machine.D3Did (didCom SDID)
open Lax117284Proofs.Machine.D3Rk (rkLoop rkOuter rkInner rkCntCom ddA SRKO SRKC)
open Lax117284Proofs.Machine.D3Day (dayBody SDAY)
open Lax117284Proofs.Machine.D3Client (dayLoop clientBody clientLoop SDL SCL CVars)
open Lax117284Proofs.Machine.D3Coll (collLoop collBody)
open Lax117284Proofs.Machine.D3Setup (scanLoop scanBody initR_run SSC)
open Lax117284Proofs.Machine.WrapR Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.D3DP Lax117284Proofs.D3Rank Lax117284Proofs.D3Prog Lax117284Proofs.D3Link
open Lax117284Proofs.X1Word (satF)

open scoped Classical

/-! ### The output of the reduction, as numbers -/

lemma encode_sat : Lax117284.TwoSatisfiability.encodeFormula satF = encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, satF]

/-! ### The condition read off the array agrees with the condition on the stream -/

section Congr

variable {arr ns : List ℕ} (hv : Valid arr) (hv2 : Valid ns)

/-- **A due date below `n`, on the array's stream, agrees with the one on `ns`'s.** -/
theorem ddI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {j : ℕ} (hj : j < ns.getD 0 0) :
    D3Prog.ddI (instOf arr hv) j = D3Prog.ddI (instOf ns hv2) j := by
  have ht2 : j < ns.getD 1 0 * ns.getD 0 0 := lt_of_lt_of_le hj (Nat.le_mul_of_pos_left _ hm1)
  have ht : j < arr.getD 1 0 * arr.getD 0 0 := by rw [h0, h1]; exact ht2
  have e1 := (instOf_pAt arr hv ht).2
  have e2 := (instOf_pAt ns hv2 ht2).2
  have hdiv1 : j / arr.getD 0 0 = 0 := by rw [h0]; exact Nat.div_eq_of_lt hj
  have hmod1 : j % arr.getD 0 0 = j := by rw [h0]; exact Nat.mod_eq_of_lt hj
  have hdiv2 : j / ns.getD 0 0 = 0 := Nat.div_eq_of_lt hj
  have hmod2 : j % ns.getD 0 0 = j := Nat.mod_eq_of_lt hj
  rw [hdiv1, hmod1] at e1
  rw [hdiv2, hmod2] at e2
  unfold D3Prog.ddI
  rw [e1, e2, hag (2 + 2 * j + 1) (by omega)]

/-- **The client at a position below `n`, on the array's stream, agrees with the one on `ns`'s.** -/
theorem ordI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {c : ℕ} (hc : c < ns.getD 0 0) :
    D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c := by
  have hcl : (instOf arr hv).clients = ns.getD 0 0 := h0
  unfold D3Prog.ordI
  rw [hcl]
  refine ordOf_congr hc (fun j hj => ?_)
  exact ddI_congr hv hv2 h0 h1 hag hm1 hj

/-- **The processing time of the client at a position, on the array's stream, agrees with the
one on `ns`'s.** -/
theorem qI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {i c : ℕ} (hi : i < ns.getD 1 0) (hc : c < ns.getD 0 0) :
    D3Prog.qI (instOf arr hv) i c = D3Prog.qI (instOf ns hv2) i c := by
  have hordlt : D3Prog.ordI (instOf ns hv2) c < ns.getD 0 0 := by
    have h := D3Prog.ordI_lt (I := instOf ns hv2) (c := c) hc
    have h' : D3Prog.ordI (instOf ns hv2) c < (instOf ns hv2).clients := h
    have hcl : (instOf ns hv2).clients = ns.getD 0 0 := rfl
    rwa [hcl] at h'
  have hordeq : D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c :=
    ordI_congr hv hv2 h0 h1 hag hm1 hc
  have ht2 : i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c < ns.getD 1 0 * ns.getD 0 0 :=
    cell_lt hi hordlt
  have ht : i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c < arr.getD 1 0 * arr.getD 0 0 := by
    rw [h0, h1, hordeq]; exact ht2
  have hidxeq : i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c =
      i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c := by rw [h0, hordeq]
  have e1 := (instOf_pAt arr hv ht).1
  have e2 := (instOf_pAt ns hv2 ht2).1
  have hdiv1 : (i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c) / arr.getD 0 0 = i := by
    rw [hidxeq, h0]; exact (divmod_row (by omega) hordlt).1
  have hmod1 : (i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c) % arr.getD 0 0 =
      D3Prog.ordI (instOf arr hv) c := by
    rw [hidxeq, h0, hordeq]; exact (divmod_row (by omega) hordlt).2
  have hdiv2 : (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c) / ns.getD 0 0 = i :=
    (divmod_row (by omega) hordlt).1
  have hmod2 : (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c) % ns.getD 0 0 =
      D3Prog.ordI (instOf ns hv2) c := (divmod_row (by omega) hordlt).2
  rw [hdiv1, hmod1] at e1
  rw [hdiv2, hmod2] at e2
  unfold D3Prog.qI
  rw [e1, e2, hidxeq, hag (2 + 2 * (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c)) (by omega)]

/-- **The due date of the client at a position, on the array's stream, agrees with the one on
`ns`'s.** -/
theorem eI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {c : ℕ} (hc : c < ns.getD 0 0) :
    D3Prog.eI (instOf arr hv) c = D3Prog.eI (instOf ns hv2) c := by
  have hordlt : D3Prog.ordI (instOf ns hv2) c < ns.getD 0 0 := by
    have h := D3Prog.ordI_lt (I := instOf ns hv2) (c := c) hc
    have h' : D3Prog.ordI (instOf ns hv2) c < (instOf ns hv2).clients := h
    have hcl : (instOf ns hv2).clients = ns.getD 0 0 := rfl
    rwa [hcl] at h'
  have hordeq : D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c :=
    ordI_congr hv hv2 h0 h1 hag hm1 hc
  unfold D3Prog.eI
  rw [hordeq]
  exact ddI_congr hv hv2 h0 h1 hag hm1 hordlt

/-- **A fair schedule on the array's stream exists exactly when one exists on `ns`'s.** -/
theorem hasKFair_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hda : (instOf arr hv).DayIndepD) (hdn : (instOf ns hv2).DayIndepD) (hm1 : 0 < ns.getD 1 0)
    (k : ℕ) : (instOf arr hv).HasKFairSchedule k ↔ (instOf ns hv2).HasKFairSchedule k := by
  have hclA : (instOf arr hv).clients = arr.getD 0 0 := rfl
  have hdayA : (instOf arr hv).days = arr.getD 1 0 := rfl
  have hclN : (instOf ns hv2).clients = ns.getD 0 0 := rfl
  have hdayN : (instOf ns hv2).days = ns.getD 1 0 := rfl
  have hmA : 0 < (instOf arr hv).days := by rw [hdayA, h1]; exact hm1
  have hmN : 0 < (instOf ns hv2).days := by rw [hdayN]; exact hm1
  have hA := D3Prog.hasKFair_iff_reach hda hmA k
  have hN := D3Prog.hasKFair_iff_reach hdn hmN k
  rw [hdayA, hclA] at hA
  rw [hdayN, hclN] at hN
  rw [hA, hN, h1, h0,
    D3Link.reach_eq (fun i hi c hc => qI_congr hv hv2 h0 h1 hag hm1 hi hc)
      (fun c hc => eI_congr hv hv2 h0 h1 hag hm1 hc)]

end Congr

/-- **The array's own instance is fair exactly when the stream's is, once the counts and the
values below the table's length agree.** -/
theorem decideOk_congr (m : ℕ) (hm0 : 0 < m) (arr ns : List ℕ) (h : arr.take ns.length = ns)
    (hs : Shape eU ns) : decideOk arr m ↔ decideOk ns m := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  have hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0 :=
    fun k hk => hg k (by omega)
  have hpar : paramOf arr = paramOf ns := by unfold paramOf; rw [h0, h1]; exact hg _ (by omega)
  have hValidIff : Valid arr ↔ Valid ns := by
    unfold Valid; rw [h0, h1]
    constructor
    · intro hVa t ht
      have e1 := hag (2 + 2 * t) (by omega)
      have e2 := hag (2 + 2 * t + 1) (by omega)
      have := hVa t ht
      rwa [e1, e2] at this
    · intro hVn t ht
      have e1 := hag (2 + 2 * t) (by omega)
      have e2 := hag (2 + 2 * t + 1) (by omega)
      rw [e1, e2]; exact hVn t ht
  have hDIDIff : DID arr ↔ DID ns := by
    unfold DID; rw [h0, h1]
    constructor
    · intro hDa t ht
      have hmle : t % ns.getD 0 0 ≤ t := Nat.mod_le _ _
      have e1 := hag (2 + 2 * t + 1) (by omega)
      have e2 := hag (2 + 2 * (t % ns.getD 0 0) + 1) (by omega)
      have := hDa t ht
      rwa [e1, e2] at this
    · intro hDn t ht
      have hmle : t % ns.getD 0 0 ≤ t := Nat.mod_le _ _
      have e1 := hag (2 + 2 * t + 1) (by omega)
      have e2 := hag (2 + 2 * (t % ns.getD 0 0) + 1) (by omega)
      rw [e1, e2]; exact hDn t ht
  unfold decideOk
  constructor
  · rintro ⟨hv, hdid, hm', hk⟩
    have hv2 : Valid ns := hValidIff.mp hv
    have hdid2 : DID ns := hDIDIff.mp hdid
    have hm'2 : ns.getD 1 0 = m := by rw [← h1]; exact hm'
    have hm1 : 0 < ns.getD 1 0 := by rw [hm'2]; exact hm0
    have hda : (instOf arr hv).DayIndepD := (did_iff arr hv).2 hdid
    have hdn : (instOf ns hv2).DayIndepD := (did_iff ns hv2).2 hdid2
    refine ⟨hv2, hdid2, hm'2, ?_⟩
    rw [← hpar]
    exact (hasKFair_congr hv hv2 h0 h1 hag hda hdn hm1 _).1 hk
  · rintro ⟨hv2, hdid2, hm', hk⟩
    have hv : Valid arr := hValidIff.mpr hv2
    have hdid : DID arr := hDIDIff.mpr hdid2
    have hm1 : 0 < ns.getD 1 0 := by rw [hm']; exact hm0
    have hda : (instOf arr hv).DayIndepD := (did_iff arr hv).2 hdid
    have hdn : (instOf ns hv2).DayIndepD := (did_iff ns hv2).2 hdid2
    refine ⟨hv, hdid, by rw [h1]; exact hm', ?_⟩
    rw [hpar]
    exact (hasKFair_congr hv hv2 h0 h1 hag hda hdn hm1 _).2 hk

/-! ### The cost of the accepting phase is monotone -/

lemma KaccDPos_mono (m Sz : ℕ) {a b : ℕ} (h : a ≤ b) : KaccDPos m Sz a ≤ KaccDPos m Sz b := by
  unfold KaccDPos
  gcongr

/-! ### The reduction, as a `WrapR` -/

lemma nk_warrs' : "R" ∉ (UNk.nkU).warrs := by simp [UNk.nkU, Com.warrs]

open Classical in
/-- **The reduction to the numbers with day-independent due dates and `m` days.** -/
noncomputable def W (m : ℕ) (hm0 : 0 < m) : WrapR where
  Rext := fun L => 2 ^ (2 * L + 4)
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  nk_warrs := nk_warrs'
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceM m
  cond := fun ns => decideOk ns m
  outW := fun _ => Lax117284.TwoSatisfiability.encodeFormula satF
  sem_acc := fun ns hshS hc => by
    have hmem : numCode ns ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) := by
      obtain ⟨hv, hdid, hgetm, hk⟩ := hc
      exact (uniform_iff_good m (numCode ns)).2 ⟨ns, rfl, hshS, hv, ⟨hdid, hgetm⟩, hk⟩
    unfold reduceM
    rw [if_pos hmem]
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w hnex => by
    have hnot : w ∉ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) := fun hmem => by
      obtain ⟨ns, hw, hshS, hv, ⟨hdid, hgetm⟩, hk⟩ := (uniform_iff_good m w).1 hmem
      exact hnex ⟨ns, hw, hshS, hv, hdid, hgetm, hk⟩
    unfold reduceM
    rw [if_neg hnot]
  rej := rejT9
  Krej := Krej9
  rejRun := fun B Sz σ hs hB => rejT9_run (B := B) Sz σ hs hB
  acc := acceptDPos m
  Kacc := KaccDPos m
  Kmono := fun Sz a b h => KaccDPos_mono m Sz h
  accRun := fun B Sz L ns arr σ hsh harr hA hR hlenL hvals hB hs => by
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
    have hpp2 : (2 : ℕ) ^ (L + 1) * 2 ^ (L + 1) = 4 * (2 ^ L * 2 ^ L) := by ring
    have hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ L * 2 ^ (L + 1) :=
      Nat.mul_le_mul hmnL.le hn.le
    have hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ L * 2 ^ (L + 1) := by
      rw [Nat.mul_comm (arr.getD 0 0) (arr.getD 1 0)]
      exact Nat.mul_le_mul hmnL.le hm.le
    have hpp3 : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
    have htq : arr.getD 0 0 * arr.getD 1 0 ≤ 2 ^ L := by rw [Nat.mul_comm]; omega
    have hkp : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 < 2 ^ (L + 1) := by
      rw [hg _ (by omega)]; exact hval _ (by omega)
    have hkn : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 * arr.getD 0 0 ≤
        2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hkp.le hn.le
    have hlm : arr.getD 1 0 * arr.getD 0 0 ≤ ns.length := by omega
    -- the day-count-cubed and doubled-coefficient bounds
    have hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
        arr.getD 1 0 * arr.getD 0 0 + 8 < B := by omega
    have hE2 : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), 2 * arr.getD k 0 + 16 < B :=
      fun k hk => by
        rw [h0, h1] at hk
        rw [hg k (by omega)]
        have := hval k (by omega)
        omega
    -- the polynomial fit of the power of a fixed number of days, once the day count matches
    have hPPle : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m ≤ 2 ^ L := fun hgm => by
      rcases Nat.eq_zero_or_pos (arr.getD 0 0) with hn0 | hn0
      · rw [hn0]
        have : (0:ℕ) < 2 ^ L := by positivity
        simp only [Nat.zero_add, one_pow]
        omega
      · have hshape : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ L := by rw [← hl']; exact hlenL
        have hshape2 : 3 + 2 * (m * arr.getD 0 0) ≤ L := by rw [← hgm]; exact hshape
        have hle : m ≤ m * arr.getD 0 0 := Nat.le_mul_of_pos_right _ hn0
        have hbase : arr.getD 0 0 + 1 ≤ 2 ^ (arr.getD 0 0 + 1) := (Nat.lt_two_pow_self).le
        have hppbound : (arr.getD 0 0 + 1) ^ m ≤ (2 ^ (arr.getD 0 0 + 1) : ℕ) ^ m :=
          Nat.pow_le_pow_left hbase m
        have hexp : (2 ^ (arr.getD 0 0 + 1) : ℕ) ^ m = 2 ^ (m * arr.getD 0 0 + m) := by
          rw [← pow_mul]; congr 1; ring
        have hfinal : (2 : ℕ) ^ (m * arr.getD 0 0 + m) ≤ 2 ^ L :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [hexp] at hppbound
        omega
    have hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B := fun hgm => by
      have h1' := hPPle hgm
      have h2' : (2 : ℕ) ^ L ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hPKB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 + 8 < B :=
      fun hgm => by
        have h1' := hPPle hgm
        have h3' : (arr.getD 0 0 + 1) ^ m *
            (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) ≤ 2 ^ L * 2 ^ (L + 1) :=
          Nat.mul_le_mul h1' (by omega)
        have h4' : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
        omega
    have hRlen : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 ≤
        (σ.arrs "R").length := fun hgm => by
      have hlen' : (σ.arrs "R").length = 2 ^ (2 * L + 4) := by
        rw [hR]; simp
      have h1' := hPPle hgm
      have h3' : (arr.getD 0 0 + 1) ^ m *
          (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) ≤ 2 ^ L * 2 ^ (L + 1) :=
        Nat.mul_le_mul h1' (by omega)
      have h4' : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
      rw [hlen']
      omega
    have hR0zero : ∀ j, (σ.arrs "R").getD j 0 = 0 := fun j => by rw [hR]; simp
    have hRB : ∀ j, (σ.arrs "R").getD j 0 < B := fun j => by
      rw [hR0zero j]; omega
    have houtEq : natBits (Lax117284.TwoSatisfiability.encodeFormula satF) =
        bitsNat 1 ++ bitsNat 0 := by
      rw [encode_sat]
      simp only [T9Comp1.natBits_app, natBits_encodeNat]
    obtain ⟨σ', r, o⟩ := acceptDPos_run m hm0 Sz ns.length arr σ hs hE (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hCU hE2 hlm hA
      hPPB hPKB hRlen hR0zero hRB
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : decideOk ns m
    · have hca : decideOk arr m := (decideOk_congr m hm0 arr ns harr ⟨h2, hl⟩).2 hc
      rw [if_pos hca, if_pos hc, houtEq]
    · have hca : ¬ decideOk arr m := fun h => hc ((decideOk_congr m hm0 arr ns harr ⟨h2, hl⟩).1 h)
      rw [if_neg hca, if_neg hc]

/-! ### The layout and the polynomial bound -/

/-- The layout the machine of the reduction runs in. -/
abbrev layoutD3 : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "k1", "nn", "mm", "V1", "C1", "C2", "CC", "tq", "ci", "cr", "j1", "j2", "tt", "x1", "x2", "pa",
    "da", "pb", "db", "cj", "r2", "i1", "CU",
    "PK", "PP", "b1", "cl", "cx", "dj", "dq", "dy", "ec", "fnd", "ix2", "jc", "jj", "mc", "pk",
    "qic", "sc", "dg", "dm", "dp", "dq2", "dr", "dw", "fvv", "sm", "ss", "tp", "tt2", "xx", "yy",
    "jd"], ["a", "TK", "R"], 12⟩

lemma powCom_ok (hPP : "PP" ∈ layoutD3.scalars) (hb1 : "b1" ∈ layoutD3.scalars)
    (hT : 0 < layoutD3.temps) : ∀ k, Com.Ok layoutD3 (powCom k) := by
  intro k
  induction k with
  | zero => simp [powCom, Com.Ok, Expr.Ok, hPP]
  | succ k ih => simp [powCom, Com.Ok, Expr.Ok, ih, hPP, hb1, hT]

lemma checkMLoop_ok (hmc : "mc" ∈ layoutD3.scalars) (hok : "ok" ∈ layoutD3.scalars)
    (hT : 1 < layoutD3.temps) : ∀ d, Com.Ok layoutD3 (checkMLoop d) := by
  have hT0 : 0 < layoutD3.temps := by omega
  intro d
  induction d with
  | zero => simp [checkMLoop, Com.Ok, Cond.Ok, condExpr, Expr.Ok, hmc, hok, hT, hT0]
  | succ d ih => simp [checkMLoop, Com.Ok, Cond.Ok, condExpr, Expr.Ok, hmc, hok, hT, hT0, ih]

theorem com_ok (m : ℕ) (hm0 : 0 < m) : Com.Ok layoutD3 (W m hm0).mainW := by
  have hPow := powCom_ok (by simp [layoutD3]) (by simp [layoutD3]) (by simp [layoutD3]) m
  have hChk := checkMLoop_ok (by simp [layoutD3]) (by simp [layoutD3]) (by simp [layoutD3]) m
  simp [WrapR.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptDPos, gateK, dpBody, fixOk, printZ, prepT, rejT9, checkM, hChk, hPow,
    didCom, D3Did.didBody, D3Did.SDID, rkLoop, D3Rk.rkOuter, D3Rk.rkInner, D3Rk.rkCntCom,
    clientLoop, D3Client.clientBody, D3Client.dayLoop, D3Day.dayBody, D3Coll.collLoop,
    D3Coll.collBody, D3Setup.scanLoop, D3Setup.scanBody, FoldLoop.fLoop,
    D3Sweep.sweepLoop, D3Sweep.sweepBody, D3Sweep.sweepServe, D3Sweep.sweepTry,
    D3Sweep.sweepSet, D3Sweep.seg1, D3Sweep.seg2,
    FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, layoutD3, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

lemma KcheckMLoop_le (d : ℕ) :
    Lax117284Proofs.Machine.D3Pow.KcheckMLoop d ≤ 24 * d + 20 := by
  induction d with
  | zero => simp [Lax117284Proofs.Machine.D3Pow.KcheckMLoop]
  | succ d ih =>
    show Lax117284Proofs.Machine.D3Pow.KcheckMLoop (d + 1) ≤ 24 * (d + 1) + 20
    unfold Lax117284Proofs.Machine.D3Pow.KcheckMLoop
    simp only [Expr.size]
    omega

lemma KcheckM_le (m : ℕ) : KcheckM m ≤ 24 * m + 22 := by
  unfold KcheckM
  have := KcheckMLoop_le m
  simp only [Expr.size]
  omega

lemma KpowCom_le (k : ℕ) : KpowCom k ≤ 4 * k + 2 := by
  induction k with
  | zero => simp [KpowCom]
  | succ k ih =>
    show KpowCom (k + 1) ≤ 4 * (k + 1) + 2
    unfold KpowCom
    simp only [Expr.size]
    omega

theorem Kpoly (m : ℕ) (hm0 : 0 < m) :
    ∀ Sz l, (W m hm0).Kacc Sz l ≤ (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by
  intro Sz l
  show KaccDPos m Sz l ≤ _
  unfold KaccDPos Krej9
  have hck := KcheckM_le m
  have hpc := KpowCom_le m
  have h2 : (l + 1) ^ m * (l + 1) ≤ (l + 1) ^ (m + 3) := by
    calc (l + 1) ^ m * (l + 1) = (l + 1) ^ (m + 1) := (pow_succ _ _).symm
      _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (l + 1) ^ m ≤ (l + 1) ^ (m + 3) := by
    have : (l + 1) ^ m ≤ (l + 1) ^ m * (l + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hPl : (l + 1) ^ m * l ≤ (l + 1) ^ (m + 3) :=
    le_trans (Nat.mul_le_mul_left _ (by omega)) h2
  have hl1 : l ≤ (l + 1) ^ (m + 3) := by
    have : l + 1 ≤ (l + 1) ^ (m + 3) := by
      calc l + 1 = (l + 1) ^ 1 := (pow_one _).symm
        _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hl2 : l * l ≤ (l + 1) ^ (m + 3) := by
    calc l * l ≤ (l + 1) * (l + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (l + 1) ^ 2 := (sq (l + 1)).symm
      _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX3pos : 1 ≤ (l + 1) ^ (m + 3) := Nat.one_le_pow _ _ (by omega)
  have hAm : m ≤ (m + 1) * (m + 1) := by nlinarith
  have hA1 : 1 ≤ (m + 1) * (m + 1) := by nlinarith
  have hAm1 : m + 1 ≤ (m + 1) * (m + 1) := by nlinarith
  have hTeq : ((((((400 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6)) + 10 + 4) * l + 6) =
      ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l) + (80 * m + 86) * l + 6 := by ring
  have hc : (414 * m + 74) * (m + 1) ≤ 500 * ((m + 1) * (m + 1)) := by nlinarith
  have hTb : ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l) ≤
      500 * ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    calc ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l)
        ≤ (500 * ((m + 1) * (m + 1))) * ((l + 1) ^ m * l) := Nat.mul_le_mul_right _ hc
      _ ≤ (500 * ((m + 1) * (m + 1))) * (l + 1) ^ (m + 3) := Nat.mul_le_mul_left _ hPl
  have hml : m * l ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) := Nat.mul_le_mul (by omega) hl1
  have hAX : (l + 1) ^ (m + 3) ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmA : (m + 1) * (l + 1) ^ (m + 3) ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    Nat.mul_le_mul_right _ hAm1
  have hmA0 : m ≤ (m + 1) * (l + 1) ^ (m + 3) := by nlinarith
  have hsum : ((l + 1) ^ (m + 3) + Sz) ≤ (Sz + 1) * (l + 1) ^ (m + 3) := by nlinarith [hX3pos]
  have hbig : (100000 * ((m + 1) * (m + 1))) * ((l + 1) ^ (m + 3) + Sz) ≤
      (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by
    calc (100000 * ((m + 1) * (m + 1))) * ((l + 1) ^ (m + 3) + Sz) ≤
        (100000 * ((m + 1) * (m + 1))) * ((Sz + 1) * (l + 1) ^ (m + 3)) :=
          Nat.mul_le_mul_left _ hsum
      _ = (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by ring
  have hSzA : Sz ≤ ((m + 1) * (m + 1)) * Sz := Nat.le_mul_of_pos_left _ (by omega)
  rw [hTeq]
  nlinarith [hck, hpc, h1, hPl, hl1, hl2, hX3pos, hTb, hml, hAX, hmA, hmA0, hbig, hSzA,
    Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le m, Nat.zero_le ((l + 1) ^ (m + 3))]

/-- **The reduction that decides day-independent due dates with a fixed positive number of days
is polynomial-time computable.** -/
theorem reduceM_polyTime (m : ℕ) (hm0 : 0 < m) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduceM m)) :=
  WrapRFinal.polyTimeE (W m hm0) layoutD3 (com_ok m hm0) (by simp [layoutD3]) (by simp [layoutD3])
    (100000 * ((m + 1) * (m + 1))) (m + 3) (by omega) (Kpoly m hm0) (fun Sz => by
      show 6 * (48 * Sz + 50) + 20 ≤ (100000 * ((m + 1) * (m + 1))) * (Sz + 1)
      have hA1 : 1 ≤ (m + 1) * (m + 1) := by nlinarith
      nlinarith [Nat.zero_le Sz, Nat.zero_le m, Nat.mul_le_mul_left (100000 * (Sz + 1)) hA1])

end Lax117284Proofs.Machine.D3Final

end
