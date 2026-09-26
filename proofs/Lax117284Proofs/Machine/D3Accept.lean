import Lax117284Proofs.Machine.T9Accept
import Lax117284Proofs.Machine.X1Accept
import Lax117284Proofs.Machine.D3Pow
import Lax117284Proofs.Machine.D3Did
import Lax117284Proofs.Machine.D3Setup
import Lax117284Proofs.Machine.D3Sem
import Lax117284Proofs.Machine.D3AcceptDefs
import Lax117284Proofs.D3Link

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
