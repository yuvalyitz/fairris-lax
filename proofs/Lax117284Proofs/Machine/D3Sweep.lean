import Lax117284Proofs.Machine.D3Rk
import Lax117284Proofs.D3Tab

/-!
The sweep that serves the client at position `c` on day `i`: the cells of the table from the last
to the first, each cell that holds a state and can serve the client setting the cell of the state
it leads to.
-/

namespace Lax117284Proofs.Machine.D3Sweep

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false condEq_true condEq_false)
open Lax117284Proofs.Machine.X3Loop (rd)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.D3Code

variable {B : ℕ}

/-- The client number and the digit of a cell: `tt2` is the number of days served and `dg` the
digit of the day. -/
def seg1 : Com :=
  .seq (.assign "tt2" (.bin .div (V "xx") (V "PP")))
  (.seq (.assign "tp" (mul (V "tt2") (V "PP")))
  (.seq (.assign "ss" (sub (V "xx") (V "tp")))
  (.seq (.assign "dq2" (.bin .div (V "ss") (V "pw")))
  (.seq (.assign "dr" (mul (.bin .div (V "dq2") (V "b1")) (V "b1")))
        (.assign "dg" (sub (V "dq2") (V "dr")))))))

/-- The scalars `seg1` assigns. -/
def S1 : List String := ["tt2", "tp", "ss", "dq2", "dr", "dg"]

lemma mod_sub (i n : ℕ) : i - i / n * n = i % n := by
  have := Nat.div_add_mod i n
  rw [Nat.mul_comm] at this
  omega

set_option maxHeartbeats 3200000 in
/-- **The days served and the digit of a cell.** -/
theorem seg1_run (σ : Env) (x PP pw b1 i : ℕ) (hx : σ.vars "xx" = x) (hPP : σ.vars "PP" = PP)
    (hpw : σ.vars "pw" = pw) (hb1 : σ.vars "b1" = b1) (hxB : x + 8 < B) (hPPB : PP + 8 < B)
    (hpwB : pw + 8 < B) (hb1B : b1 + 8 < B) :
    ∃ σ', Run B seg1 σ σ' 60 ∧ σ'.vars "tt2" = x / PP ∧ σ'.vars "dg" = x % PP / pw % b1 ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.vars "ss" = x % PP ∧
      ∀ y, y ∉ S1 → σ'.vars y = σ.vars y := by
  have s1 := asgE (B := B) "tt2" (.bin .div (V "xx") (V "PP")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_div, hx, hPP]
    refine ⟨by omega, by omega, ?_⟩
    have := Nat.div_le_self x PP; omega)
  set σ1 := σ.setVar "tt2" (MisBlk.den σ (.bin .div (V "xx") (V "PP"))) with hσ1
  have htt1 : σ1.vars "tt2" = x / PP := by simp [hσ1, MisBlk.den, Env.setVar, hx, hPP]
  have hx1 : σ1.vars "xx" = x := by simp [hσ1, Env.setVar, hx]
  have hPP1 : σ1.vars "PP" = PP := by simp [hσ1, Env.setVar, hPP]
  have hle1 : x / PP * PP ≤ x := Nat.div_mul_le_self _ _
  have hle2 : x / PP ≤ x := Nat.div_le_self _ _
  have s2 := asgE (B := B) "tp" (mul (V "tt2") (V "PP")) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, htt1, hPP1]
    omega)
  set σ2 := σ1.setVar "tp" (MisBlk.den σ1 (mul (V "tt2") (V "PP"))) with hσ2
  have htp2 : σ2.vars "tp" = x / PP * PP := by simp [hσ2, MisBlk.den, Env.setVar, htt1, hPP1]
  have hx2 : σ2.vars "xx" = x := by simp [hσ2, Env.setVar, hx1]
  have s3 := asgE (B := B) "ss" (sub (V "xx") (V "tp")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, htp2, hx2]
    omega)
  set σ3 := σ2.setVar "ss" (MisBlk.den σ2 (sub (V "xx") (V "tp"))) with hσ3
  have hss3 : σ3.vars "ss" = x % PP := by
    simp [hσ3, MisBlk.den, Env.setVar, htp2, hx2, Bop.apply_sub, mod_sub]
  have hpw3 : σ3.vars "pw" = pw := by simp [hσ3, hσ2, hσ1, Env.setVar, hpw]
  have hb13 : σ3.vars "b1" = b1 := by simp [hσ3, hσ2, hσ1, Env.setVar, hb1]
  have hmle : x % PP ≤ x := Nat.mod_le _ _
  have s4 := asgE (B := B) "dq2" (.bin .div (V "ss") (V "pw")) σ3 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_div, hss3, hpw3]
    refine ⟨by omega, by omega, ?_⟩
    have := Nat.div_le_self (x % PP) pw; omega)
  set σ4 := σ3.setVar "dq2" (MisBlk.den σ3 (.bin .div (V "ss") (V "pw"))) with hσ4
  have hdq4 : σ4.vars "dq2" = x % PP / pw := by simp [hσ4, MisBlk.den, Env.setVar, hss3, hpw3]
  have hb14 : σ4.vars "b1" = b1 := by simp [hσ4, Env.setVar, hb13]
  have hdle : x % PP / pw ≤ x := le_trans (Nat.div_le_self _ _) hmle
  have s5 := asgE (B := B) "dr" (mul (.bin .div (V "dq2") (V "b1")) (V "b1")) σ4 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, MisBlk.den_bin, Bop.apply_mul,
      Bop.apply_div, hdq4, hb14]
    have h1 : x % PP / pw / b1 * b1 ≤ x % PP / pw := Nat.div_mul_le_self _ _
    have h2 : x % PP / pw / b1 ≤ x % PP / pw := Nat.div_le_self _ _
    have h3 : x % PP / pw / b1 * b1 < B := lt_of_le_of_lt (le_trans h1 hdle) (by omega)
    have h4 : x % PP / pw / b1 < B := lt_of_le_of_lt (le_trans h2 hdle) (by omega)
    have h5 : x % PP / pw < B := lt_of_le_of_lt hdle (by omega)
    exact ⟨⟨h5, by omega, h4⟩, by omega, h3⟩)
  set σ5 := σ4.setVar "dr" (MisBlk.den σ4 (mul (.bin .div (V "dq2") (V "b1")) (V "b1"))) with hσ5
  have hdr5 : σ5.vars "dr" = x % PP / pw / b1 * b1 := by
    simp [hσ5, MisBlk.den, Env.setVar, hdq4, hb14]
  have hdq5 : σ5.vars "dq2" = x % PP / pw := by simp [hσ5, Env.setVar, hdq4]
  have s6 := asgE (B := B) "dg" (sub (V "dq2") (V "dr")) σ5 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, hdr5, hdq5]
    have h1 : x % PP / pw / b1 * b1 ≤ x % PP / pw := Nat.div_mul_le_self _ _
    omega)
  set σ6 := σ5.setVar "dg" (MisBlk.den σ5 (sub (V "dq2") (V "dr"))) with hσ6
  refine ⟨σ6, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))).mono (by simp [Expr.size]), ?_, ?_,
    ?_, ?_, ?_, fun y hy => ?_⟩
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, MisBlk.den, hx, hPP]
  · simp [hσ6, MisBlk.den, Env.setVar, hdr5, hdq5, Bop.apply_sub, mod_sub]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  · have h4 : σ4.vars "ss" = x % PP := by simp [hσ4, Env.setVar, hss3]
    have h5 : σ5.vars "ss" = x % PP := by simp [hσ5, Env.setVar, h4]
    simp [hσ6, Env.setVar, h5]
  · have g : ∀ z, z ∈ S1 → y ≠ z := fun z hz h => hy (h ▸ hz)
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, g "tt2" (by simp [S1]), g "tp" (by simp [S1]),
      g "ss" (by simp [S1]), g "dq2" (by simp [S1]), g "dr" (by simp [S1]), g "dg" (by simp [S1])]

/-- The time the day is free from, given the digit `dg`. -/
def seg2 : Com :=
  .ite (.eq (V "dg") (.lit 0)) (.assign "fvv" (.lit 0))
    (.seq (.assign "dm" (sub (V "dg") (.lit 1)))
    (.seq (.assign "jd" (.get "R" (add (V "PK") (V "dm"))))
          (.assign "fvv" (rd "jd" 1))))

/-- The scalars `seg2` assigns. -/
def S2 : List String := ["fvv", "dm", "jd"]

/-- The due date of the client at position `c'`, read through the order in `R`. -/
def eOrd (arr Rl : List ℕ) (PK c' : ℕ) : ℕ := arr.getD (3 + 2 * Rl.getD (PK + c') 0) 0

set_option maxHeartbeats 3200000 in
/-- **The time a day is free from.** -/
theorem seg2_run (arr : List ℕ) (σ : Env) (dg PK n : ℕ) (hA : σ.arrs "TK" = arr)
    (hdg : σ.vars "dg" = dg) (hPK : σ.vars "PK" = PK) (hdgn : dg ≤ n)
    (hRlen : PK + n ≤ (σ.arrs "R").length) (hRv : ∀ c' < n, (σ.arrs "R").getD (PK + c') 0 < n)
    (hlen : 3 + 2 * n ≤ arr.length) (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B)
    (hnB : 2 * n + 8 < B) (hPKB : PK + n + 8 < B) :
    ∃ σ', Run B seg2 σ σ' 60 ∧
      σ'.vars "fvv" = D3DP.fv (eOrd arr (σ.arrs "R") PK) dg ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ S2 → σ'.vars y = σ.vars y := by
  have hsdg : MisBlk.small B σ (V "dg") := by show σ.vars "dg" < B; rw [hdg]; omega
  have hs0 : MisBlk.small B σ (.lit 0) := by simp [MisBlk.small]; omega
  by_cases h0 : dg = 0
  · have hT : (Cond.eq (V "dg") (.lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ hsdg hs0 (by simp [MisBlk.den, hdg, h0])
    have s := asgE (B := B) "fvv" (.lit 0) σ hs0
    refine ⟨_, (Run.ite_true hT s).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_, fun y hy => ?_⟩
    · simp [Env.setVar, MisBlk.den, D3DP.fv, h0]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · have : y ≠ "fvv" := fun h => hy (by simp [S2, h])
      simp only [Env.setVar, if_neg this]
  · have hF : (Cond.eq (V "dg") (.lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ hsdg hs0 (by simp [MisBlk.den, hdg, h0])
    have s1 := asgE (B := B) "dm" (sub (V "dg") (.lit 1)) σ (by
      simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_var,
        MisBlk.den_lit, Bop.apply_sub, hdg]
      omega)
    set σ1 := σ.setVar "dm" (MisBlk.den σ (sub (V "dg") (.lit 1))) with hσ1
    have hdm1 : σ1.vars "dm" = dg - 1 := by simp [hσ1, MisBlk.den, Env.setVar, hdg, Bop.apply_sub]
    have hPK1 : σ1.vars "PK" = PK := by simp [hσ1, Env.setVar, hPK]
    have hR1 : σ1.arrs "R" = σ.arrs "R" := by simp [hσ1, Env.setVar]
    have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
    have hdn : dg - 1 < n := by omega
    have hrv := hRv (dg - 1) hdn
    have s2 := asg_R2 (B := B) "jd" "PK" "dm" σ1 PK (dg - 1) hPK1 hdm1 (by rw [hR1]; omega)
      (by rw [hR1]; omega) (by omega) (by omega) (by omega)
    set σ2 := σ1.setVar "jd" ((σ1.arrs "R").getD (PK + (dg - 1)) 0) with hσ2
    have hjd2 : σ2.vars "jd" = (σ.arrs "R").getD (PK + (dg - 1)) 0 := by
      simp [hσ2, Env.setVar, hR1]
    have hA2 : σ2.arrs "TK" = arr := by simp [hσ2, Env.setVar, hA1]
    have hjn : (σ.arrs "R").getD (PK + (dg - 1)) 0 < n := hrv
    have e1 := hE (2 + 2 * (σ.arrs "R").getD (PK + (dg - 1)) 0 + 1) (by omega)
    have s3 := asg_tk (B := B) "jd" "fvv" 1 σ2 arr _ hA2 hjd2 (by omega) (by omega) (by omega)
    have hz : arr.getD (2 + 2 * (σ.arrs "R").getD (PK + (dg - 1)) 0 + 1) 0 =
        eOrd arr (σ.arrs "R") PK (dg - 1) := by
      unfold eOrd; rw [show 3 + 2 * (σ.arrs "R").getD (PK + (dg - 1)) 0 =
        2 + 2 * (σ.arrs "R").getD (PK + (dg - 1)) 0 + 1 by omega]
    refine ⟨_, (Run.ite_false hF (s1.seq (s2.seq s3))).mono (by simp [Cond.size, Expr.size]), ?_,
      ?_, ?_, fun y hy => ?_⟩
    · simp only [Env.setVar, if_true]
      rw [hz]; simp [D3DP.fv, h0]
    · simp [Env.setVar, hσ2, hσ1]
    · simp [Env.setVar, hσ2, hσ1]
    · have g : ∀ z, z ∈ S2 → y ≠ z := fun z hz h => hy (h ▸ hz)
      simp [Env.setVar, hσ2, hσ1, g "fvv" (by simp [S2]), g "dm" (by simp [S2]),
        g "jd" (by simp [S2])]

/-- The target of a cell, from the numbers the sweep holds. -/
def tgtM (P k b1 pw c qic ec : ℕ) (eO : ℕ → ℕ) (x : ℕ) : Option ℕ :=
  if x / P < k ∧ qic + D3DP.fv eO (x % P / pw % b1) ≤ ec then
    some (x + P + ((c + 1) - x % P / pw % b1) * pw)
  else none

/-- The state the cell leads to is marked. -/
def sweepSet : Com :=
  .seq (.assign "yy" (add (V "xx") (V "PP")))
  (.seq (.assign "dw" (sub (add (V "cl") (.lit 1)) (V "dg")))
  (.seq (.assign "dp" (mul (V "dw") (V "pw")))
  (.seq (.assign "yy" (add (V "yy") (V "dp")))
        (.store "R" (V "yy") (.lit 1)))))

/-- The client is served on the day if the day is free early enough. -/
def sweepTry : Com :=
  .seq seg2
  (.seq (.assign "sm" (add (V "qic") (V "fvv")))
  (.ite (.lt (V "ec") (V "sm")) .skip sweepSet))

/-- What a cell holding a state does: serve the client if it can. -/
def sweepServe : Com :=
  .seq seg1 (.ite (.lt (V "tt2") (V "kp")) sweepTry .skip)

/-- The body of the sweep: the cell `PK - 1 - jj`. -/
def sweepBody : Com :=
  .seq (.assign "xx" (sub (sub (V "PK") (.lit 1)) (V "jj")))
  (.seq (.assign "aa" (.get "R" (V "xx")))
  (.ite (.eq (V "aa") (.lit 1)) sweepServe .skip))

/-- The scalars the sweep body assigns. -/
def SSW : List String :=
  ["xx", "aa", "sm", "yy", "dw", "dp"] ++ S1 ++ S2

/-- What the sweep reads: the scalars and the arrays. -/
structure SwEnv (B : ℕ) (arr : List ℕ) (n P k b1 pw c qic ec PK : ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = arr
  vPK : σ.vars "PK" = PK
  vPP : σ.vars "PP" = P
  vkp : σ.vars "kp" = k
  vb1 : σ.vars "b1" = b1
  vpw : σ.vars "pw" = pw
  vcl : σ.vars "cl" = c
  vqic : σ.vars "qic" = qic
  vec : σ.vars "ec" = ec
  hlen : 3 + 2 * n ≤ arr.length
  hE : ∀ j < 3 + 2 * n, arr.getD j 0 + 8 < B
  hnB : 2 * n + 8 < B
  hRlen : PK + n ≤ (σ.arrs "R").length
  hRK : PK ≤ (σ.arrs "R").length
  hRv : ∀ c' < n, (σ.arrs "R").getD (PK + c') 0 < n
  hRB : ∀ j, (σ.arrs "R").getD j 0 < B
  hPKB : PK + n + 8 < B
  hPB : P + 8 < B
  hkB : k + 8 < B
  hb1B : b1 + 8 < B
  hpwB : pw + 8 < B
  hcB : c + 8 < B
  hqB : qic + 8 < B
  heB : ec + 8 < B

lemma SwEnv.step {B : ℕ} {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} {σ σ' : Env}
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (hv : ∀ y, y ∉ SSW → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) : SwEnv B arr n P k b1 pw c qic ec PK σ' := by
  have f : ∀ y, y ∉ SSW → σ'.vars y = σ.vars y := hv
  refine ⟨by rw [ha]; exact h.hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hlen, h.hE, h.hnB,
    by rw [ha]; exact h.hRlen, by rw [ha]; exact h.hRK, by rw [ha]; exact h.hRv,
    by rw [ha]; exact h.hRB, h.hPKB, h.hPB, h.hkB, h.hb1B, h.hpwB, h.hcB, h.hqB, h.heB⟩
  · rw [f "PK" (by simp [SSW, S1, S2])]; exact h.vPK
  · rw [f "PP" (by simp [SSW, S1, S2])]; exact h.vPP
  · rw [f "kp" (by simp [SSW, S1, S2])]; exact h.vkp
  · rw [f "b1" (by simp [SSW, S1, S2])]; exact h.vb1
  · rw [f "pw" (by simp [SSW, S1, S2])]; exact h.vpw
  · rw [f "cl" (by simp [SSW, S1, S2])]; exact h.vcl
  · rw [f "qic" (by simp [SSW, S1, S2])]; exact h.vqic
  · rw [f "ec" (by simp [SSW, S1, S2])]; exact h.vec

set_option maxHeartbeats 3200000 in
/-- **The state a cell leads to is marked.** -/
theorem sweepSet_run {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (x dg y : ℕ) (hx : σ.vars "xx" = x)
    (hdg : σ.vars "dg" = dg) (hdgc : dg ≤ c + 1) (hy : y = x + P + ((c + 1) - dg) * pw)
    (hyPK : y < PK) :
    ∃ σ', Run B sweepSet σ σ' 40 ∧ σ'.arrs "R" = (σ.arrs "R").set y 1 ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ z, z ∉ ["yy", "dw", "dp"] → σ'.vars z = σ.vars z := by
  have hyB : y + 8 < B := by have := h.hPKB; omega
  have hxy : x + P ≤ y := by rw [hy]; omega
  have hdw : ((c + 1) - dg) * pw ≤ y := by rw [hy]; omega
  have s1 := asgE (B := B) "yy" (add (V "xx") (V "PP")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_add, hx, h.vPP]
    omega)
  set σ1 := σ.setVar "yy" (MisBlk.den σ (add (V "xx") (V "PP"))) with hσ1
  have hyy1 : σ1.vars "yy" = x + P := by simp [hσ1, MisBlk.den, Env.setVar, hx, h.vPP]
  have hcl1 : σ1.vars "cl" = c := by simp [hσ1, Env.setVar, h.vcl]
  have hdg1 : σ1.vars "dg" = dg := by simp [hσ1, Env.setVar, hdg]
  have hpw1 : σ1.vars "pw" = pw := by simp [hσ1, Env.setVar, h.vpw]
  have s2 := asgE (B := B) "dw" (sub (add (V "cl") (.lit 1)) (V "dg")) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_var, MisBlk.den_lit,
      MisBlk.den_bin, Bop.apply_add, Bop.apply_sub, hcl1, hdg1]
    have := h.hcB
    refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩)
  set σ2 := σ1.setVar "dw" (MisBlk.den σ1 (sub (add (V "cl") (.lit 1)) (V "dg"))) with hσ2
  have hdw2 : σ2.vars "dw" = (c + 1) - dg := by
    simp [hσ2, MisBlk.den, Env.setVar, hcl1, hdg1, Bop.apply_sub, Bop.apply_add]
  have hpw2 : σ2.vars "pw" = pw := by simp [hσ2, Env.setVar, hpw1]
  have s3 := asgE (B := B) "dp" (mul (V "dw") (V "pw")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, hdw2, hpw2]
    have := h.hpwB
    have h1 : (c + 1) - dg ≤ c + 1 := by omega
    have := h.hcB
    exact ⟨by omega, by omega, by omega⟩)
  set σ3 := σ2.setVar "dp" (MisBlk.den σ2 (mul (V "dw") (V "pw"))) with hσ3
  have hdp3 : σ3.vars "dp" = ((c + 1) - dg) * pw := by
    simp [hσ3, MisBlk.den, Env.setVar, hdw2, hpw2]
  have hyy3 : σ3.vars "yy" = x + P := by simp [hσ3, hσ2, Env.setVar, hyy1]
  have s4 := asgE (B := B) "yy" (add (V "yy") (V "dp")) σ3 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_add, hyy3, hdp3]
    exact ⟨by omega, by omega, by omega⟩)
  set σ4 := σ3.setVar "yy" (MisBlk.den σ3 (add (V "yy") (V "dp"))) with hσ4
  have hyy4 : σ4.vars "yy" = y := by
    simp [hσ4, MisBlk.den, Env.setVar, hyy3, hdp3, hy]
  have hR4 : y < (σ4.arrs "R").length := by
    simp only [hσ4, hσ3, hσ2, hσ1, Env.setVar]; have := h.hRK; omega
  have s5 := store_R_lit (B := B) "yy" σ4 y 1 hyy4 hR4 (by omega) (by omega)
  refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono (by simp [Expr.size]), ?_, ?_, ?_, fun z hz => ?_⟩
  · simp only [setArr_arrs_R]
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  · rw [setArr_arrs_ne _ _ _ _ _ (by decide)]
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  · simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]
  · have g1 : z ≠ "yy" := fun e => hz (by simp [e])
    have g2 : z ≠ "dw" := fun e => hz (by simp [e])
    have g3 : z ≠ "dp" := fun e => hz (by simp [e])
    simp only [setArr_vars]
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, g1, g2, g3]

set_option maxHeartbeats 6400000 in
/-- **The client is served on the day if the day is free early enough.** -/
theorem sweepTry_run {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (x dg : ℕ) (hx : σ.vars "xx" = x)
    (hdg : σ.vars "dg" = dg) (hdgn : dg ≤ n) (hdgc : dg ≤ c + 1)
    (hsm : qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) dg + 8 < B)
    (hyPK : qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) dg ≤ ec →
      x + P + ((c + 1) - dg) * pw < PK) :
    ∃ σ', Run B sweepTry σ σ' 200 ∧
      σ'.arrs "R" = (if qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) dg ≤ ec then
        (σ.arrs "R").set (x + P + ((c + 1) - dg) * pw) 1 else σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ z, z ∉ SSW → σ'.vars z = σ.vars z := by
  obtain ⟨σ1, r1, hfv, ha1, ho1, hf1⟩ := seg2_run (B := B) arr σ dg PK n h.hA hdg h.vPK hdgn
    h.hRlen h.hRv h.hlen h.hE h.hnB h.hPKB
  have hqic1 : σ1.vars "qic" = qic := by rw [hf1 "qic" (by simp [S2])]; exact h.vqic
  have hec1 : σ1.vars "ec" = ec := by rw [hf1 "ec" (by simp [S2])]; exact h.vec
  have hx1 : σ1.vars "xx" = x := by rw [hf1 "xx" (by simp [S2])]; exact hx
  have hdg1 : σ1.vars "dg" = dg := by rw [hf1 "dg" (by simp [S2])]; exact hdg
  have hh1 : SwEnv B arr n P k b1 pw c qic ec PK σ1 := by
    refine h.step (fun y hy => hf1 y (fun hm => hy (by simp [SSW, hm]))) ha1
  have hs1 : MisBlk.small B σ1 (V "qic") := by show σ1.vars "qic" < B; rw [hqic1]; have := h.hqB; omega
  have hs2 : MisBlk.small B σ1 (V "fvv") := by
    show σ1.vars "fvv" < B; rw [hfv]; omega
  have s2 := asgE (B := B) "sm" (add (V "qic") (V "fvv")) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_add, hqic1, hfv]
    have := h.hqB
    exact ⟨by omega, by omega, by omega⟩)
  set σ2 := σ1.setVar "sm" (MisBlk.den σ1 (add (V "qic") (V "fvv"))) with hσ2
  have hsm2 : σ2.vars "sm" = qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) dg := by
    simp [hσ2, MisBlk.den, Env.setVar, hqic1, hfv]
  have hec2 : σ2.vars "ec" = ec := by simp [hσ2, Env.setVar, hec1]
  have hsec : MisBlk.small B σ2 (V "ec") := by
    show σ2.vars "ec" < B; rw [hec2]; have := h.heB; omega
  have hssm : MisBlk.small B σ2 (V "sm") := by
    show σ2.vars "sm" < B; rw [hsm2]; omega
  have hA2 : σ2.arrs = σ1.arrs := by simp [hσ2, Env.setVar]
  have hf2 : ∀ z, z ≠ "sm" → σ2.vars z = σ1.vars z := by
    intro z hz; simp [hσ2, Env.setVar, hz]
  by_cases hfe : qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) dg ≤ ec
  · have hF : (Cond.lt (V "ec") (V "sm")).evalB B σ2 = some false :=
      condLt_false _ _ σ2 hsec hssm (by
        show ¬ (σ2.vars "ec" < σ2.vars "sm"); rw [hec2, hsm2]; omega)
    have hh2 : SwEnv B arr n P k b1 pw c qic ec PK σ2 := by
      refine hh1.step (fun y hy => ?_) hA2
      have : y ≠ "sm" := fun e => hy (by simp [SSW, e])
      rw [hf2 y this]
    obtain ⟨σ3, r3, hR3, hA3, hO3, hF3⟩ := sweepSet_run (B := B) σ2 hh2 x dg
      (x + P + ((c + 1) - dg) * pw) (by rw [hf2 "xx" (by decide)]; exact hx1)
      (by rw [hf2 "dg" (by decide)]; exact hdg1) hdgc rfl (hyPK hfe)
    refine ⟨σ3, (r1.seq (s2.seq (Run.ite_false hF r3))).mono (by simp [Cond.size, Expr.size]), ?_,
      ?_, ?_, fun z hz => ?_⟩
    · rw [hR3, if_pos hfe, hA2, ha1]
    · rw [hA3, hA2, ha1]
    · rw [hO3, hσ2]; simp [Env.setVar, ho1]
    · have g1 : z ∉ ["yy", "dw", "dp"] := fun e => hz (by
        simp only [SSW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at e ⊢; tauto)
      have g2 : z ≠ "sm" := fun e => hz (by simp [SSW, e])
      rw [hF3 z g1, hf2 z g2, hf1 z (fun e => hz (by simp [SSW, e]))]
  · have hT : (Cond.lt (V "ec") (V "sm")).evalB B σ2 = some true :=
      condLt_true _ _ σ2 hsec hssm (by
        show σ2.vars "ec" < σ2.vars "sm"; rw [hec2, hsm2]; omega)
    refine ⟨σ2, (r1.seq (s2.seq (Run.ite_true hT Run.skip))).mono (by simp [Cond.size, Expr.size]),
      ?_, ?_, ?_, fun z hz => ?_⟩
    · rw [if_neg hfe, hA2, ha1]
    · rw [hA2, ha1]
    · simp [hσ2, Env.setVar, ho1]
    · have g2 : z ≠ "sm" := fun e => hz (by simp [SSW, e])
      rw [hf2 z g2, hf1 z (fun e => hz (by simp [SSW, e]))]

/-- What a state cell must satisfy for the sweep to serve from it safely. -/
def CellOk (arr Rl : List ℕ) (n P k b1 pw c qic ec PK B x : ℕ) : Prop :=
  x % P / pw % b1 ≤ c + 1 ∧ c + 1 ≤ n ∧
    qic + D3DP.fv (eOrd arr Rl PK) (x % P / pw % b1) + 8 < B ∧
    (x / P < k ∧ qic + D3DP.fv (eOrd arr Rl PK) (x % P / pw % b1) ≤ ec →
      x + P + ((c + 1) - x % P / pw % b1) * pw < PK)

set_option maxHeartbeats 6400000 in
/-- **A cell that holds a state serves the client if it can.** -/
theorem sweepServe_run {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (x : ℕ) (hx : σ.vars "xx" = x) (hxPK : x < PK)
    (hcell : CellOk arr (σ.arrs "R") n P k b1 pw c qic ec PK B x) :
    ∃ σ', Run B sweepServe σ σ' 300 ∧
      σ'.arrs "R" = (if x / P < k ∧ qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) (x % P / pw % b1) ≤ ec then
        (σ.arrs "R").set (x + P + ((c + 1) - x % P / pw % b1) * pw) 1 else σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ z, z ∉ SSW → σ'.vars z = σ.vars z := by
  obtain ⟨hdgc, hcn, hsm, hyPK⟩ := hcell
  obtain ⟨σ1, r1, htt, hdg, ha1, ho1, hss, hf1⟩ := seg1_run (B := B) σ x P pw b1 c hx h.vPP h.vpw h.vb1
    (by have := h.hPKB; omega) h.hPB h.hpwB h.hb1B
  have hh1 : SwEnv B arr n P k b1 pw c qic ec PK σ1 := by
    refine h.step (fun y hy => hf1 y (fun hm => hy (by
      simp only [SSW, List.mem_append]; left; right; exact hm))) ha1
  have hx1 : σ1.vars "xx" = x := by rw [hf1 "xx" (by simp [S1])]; exact hx
  have hkp1 : σ1.vars "kp" = k := hh1.vkp
  have hs1 : MisBlk.small B σ1 (V "tt2") := by
    show σ1.vars "tt2" < B; rw [htt]
    have := Nat.div_le_self x P
    have := h.hPKB; omega
  have hs2 : MisBlk.small B σ1 (V "kp") := by
    show σ1.vars "kp" < B; rw [hkp1]; have := h.hkB; omega
  have hR1 : σ1.arrs "R" = σ.arrs "R" := by rw [ha1]
  by_cases hg : x / P < k
  · have hT : (Cond.lt (V "tt2") (V "kp")).evalB B σ1 = some true :=
      condLt_true _ _ σ1 hs1 hs2 (by show σ1.vars "tt2" < σ1.vars "kp"; rw [htt, hkp1]; exact hg)
    obtain ⟨σ2, r2, hR2, hA2, hO2, hF2⟩ := sweepTry_run (B := B) σ1 hh1 x (x % P / pw % b1) hx1 hdg
      (by omega) hdgc (by rw [hR1]; exact hsm) (by rw [hR1]; intro hfe; exact hyPK ⟨hg, hfe⟩)
    refine ⟨σ2, (r1.seq (Run.ite_true hT r2)).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_,
      fun z hz => ?_⟩
    · rw [hR2, hR1]
      by_cases hfe : qic + D3DP.fv (eOrd arr (σ.arrs "R") PK) (x % P / pw % b1) ≤ ec
      · rw [if_pos hfe, if_pos ⟨hg, hfe⟩]
      · rw [if_neg hfe, if_neg (fun e => hfe e.2)]
    · rw [hA2, ha1]
    · rw [hO2, ho1]
    · have g : z ∉ SSW := hz
      rw [hF2 z hz, hf1 z (fun e => hz (by simp only [SSW, List.mem_append]; left; right; exact e))]
  · have hF : (Cond.lt (V "tt2") (V "kp")).evalB B σ1 = some false :=
      condLt_false _ _ σ1 hs1 hs2 (by show ¬ (σ1.vars "tt2" < σ1.vars "kp"); rw [htt, hkp1]; exact hg)
    refine ⟨σ1, (r1.seq (Run.ite_false hF Run.skip)).mono (by simp [Cond.size, Expr.size]), ?_, ?_,
      ?_, fun z hz => ?_⟩
    · rw [hR1, if_neg (fun e => hg e.1)]
    · rw [ha1]
    · exact ho1
    · rw [hf1 z (fun e => hz (by simp only [SSW, List.mem_append]; left; right; exact e))]

lemma swStep_tgtM (P k b1 pw c qic ec : ℕ) (eO : ℕ → ℕ) (x : ℕ) (A : List ℕ) :
    D3List.swStep (tgtM P k b1 pw c qic ec eO) x A =
      if A.getD x 0 = 1 ∧ (x / P < k ∧ qic + D3DP.fv eO (x % P / pw % b1) ≤ ec) then
        A.set (x + P + ((c + 1) - x % P / pw % b1) * pw) 1 else A := by
  unfold D3List.swStep tgtM
  by_cases hg : x / P < k ∧ qic + D3DP.fv eO (x % P / pw % b1) ≤ ec
  · rw [if_pos hg]
    dsimp only
    by_cases ha : A.getD x 0 = 1
    · rw [if_pos ha, if_pos ⟨ha, hg⟩]
    · rw [if_neg ha, if_neg (fun e => ha e.1)]
  · rw [if_neg hg]
    dsimp only
    rw [if_neg (fun e => hg e.2)]

set_option maxHeartbeats 6400000 in
/-- **One cell of the sweep.** -/
theorem sweepBody_run {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (j : ℕ) (hj : σ.vars "jj" = j) (hjPK : j < PK)
    (hcell : (σ.arrs "R").getD (PK - 1 - j) 0 = 1 →
      CellOk arr (σ.arrs "R") n P k b1 pw c qic ec PK B (PK - 1 - j)) :
    ∃ σ', Run B sweepBody σ σ' 400 ∧
      σ'.arrs "R" = D3List.swStep (tgtM P k b1 pw c qic ec (eOrd arr (σ.arrs "R") PK)) (PK - 1 - j)
        (σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ z, z ∉ SSW → σ'.vars z = σ.vars z := by
  have hjB : j + 8 < B := by have := h.hPKB; omega
  have s1 := asgE (B := B) "xx" (sub (sub (V "PK") (.lit 1)) (V "jj")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.small_lit, MisBlk.den_var, MisBlk.den_lit,
      MisBlk.den_bin, Bop.apply_sub, h.vPK, hj]
    have := h.hPKB
    refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega⟩)
  set σ1 := σ.setVar "xx" (MisBlk.den σ (sub (sub (V "PK") (.lit 1)) (V "jj"))) with hσ1
  have hxx1 : σ1.vars "xx" = PK - 1 - j := by
    simp [hσ1, MisBlk.den, Env.setVar, h.vPK, hj, Bop.apply_sub, Bop.apply_add]
  have hA1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have hf1 : ∀ z, z ≠ "xx" → σ1.vars z = σ.vars z := by intro z hz; simp [hσ1, Env.setVar, hz]
  have hh1 : SwEnv B arr n P k b1 pw c qic ec PK σ1 := by
    refine h.step (fun y hy => hf1 y (fun e => hy (by simp [SSW, e]))) hA1
  have hxlt : PK - 1 - j < (σ1.arrs "R").length := by rw [hA1]; have := h.hRK; omega
  have s2 := asg_R (B := B) "aa" "xx" σ1 (PK - 1 - j) hxx1 hxlt (h.hRB _) (by have := h.hPKB; omega)
  set σ2 := σ1.setVar "aa" ((σ1.arrs "R").getD (PK - 1 - j) 0) with hσ2
  have haa2 : σ2.vars "aa" = (σ.arrs "R").getD (PK - 1 - j) 0 := by simp [hσ2, Env.setVar, hA1]
  have hxx2 : σ2.vars "xx" = PK - 1 - j := by simp [hσ2, Env.setVar, hxx1]
  have hA2 : σ2.arrs = σ.arrs := by simp [hσ2, Env.setVar, hA1]
  have hf2 : ∀ z, z ≠ "aa" → z ≠ "xx" → σ2.vars z = σ.vars z := by
    intro z a b; simp [hσ2, Env.setVar, hσ1, a, b]
  have hh2 : SwEnv B arr n P k b1 pw c qic ec PK σ2 := by
    refine h.step (fun y hy => hf2 y (fun e => hy (by simp [SSW, e])) (fun e => hy (by simp [SSW, e]))) hA2
  have hsa : MisBlk.small B σ2 (V "aa") := by
    show σ2.vars "aa" < B; rw [haa2]; exact h.hRB _
  have hs1 : MisBlk.small B σ2 (.lit 1) := by simp [MisBlk.small]; have := h.hPKB; omega
  by_cases ha : (σ.arrs "R").getD (PK - 1 - j) 0 = 1
  · have hT : (Cond.eq (V "aa") (.lit 1)).evalB B σ2 = some true :=
      condEq_true _ _ σ2 hsa hs1 (by show σ2.vars "aa" = 1; rw [haa2]; exact ha)
    obtain ⟨σ3, r3, hR3, hA3, hO3, hF3⟩ := sweepServe_run (B := B) σ2 hh2 (PK - 1 - j) hxx2
      (by omega) (by rw [hA2]; exact hcell ha)
    refine ⟨σ3, (s1.seq (s2.seq (Run.ite_true hT r3))).mono (by simp [Cond.size, Expr.size]), ?_, ?_,
      ?_, fun z hz => ?_⟩
    · rw [hR3, hA2, swStep_tgtM]; simp only [ha, true_and]
    · rw [hA3, hA2]
    · rw [hO3]; simp [hσ2, hσ1, Env.setVar]
    · rw [hF3 z hz, hf2 z (fun e => hz (by simp [SSW, e])) (fun e => hz (by simp [SSW, e]))]
  · have hF : (Cond.eq (V "aa") (.lit 1)).evalB B σ2 = some false :=
      condEq_false _ _ σ2 hsa hs1 (by show σ2.vars "aa" ≠ 1; rw [haa2]; exact ha)
    refine ⟨σ2, (s1.seq (s2.seq (Run.ite_false hF Run.skip))).mono (by simp [Cond.size, Expr.size]),
      ?_, ?_, ?_, fun z hz => ?_⟩
    · rw [hA2, swStep_tgtM, if_neg (fun e => ha e.1)]
    · rw [hA2]
    · rfl
    · rw [hf2 z (fun e => hz (by simp [SSW, e])) (fun e => hz (by simp [SSW, e]))]

lemma eOrd_congr (arr R R0 : List ℕ) (PK : ℕ) (h : ∀ y, PK ≤ y → R.getD y 0 = R0.getD y 0) :
    eOrd arr R PK = eOrd arr R0 PK := by
  funext c'
  unfold eOrd
  rw [h (PK + c') (by omega)]

/-- The scalars a sweep reads. -/
def SwVars : List String := ["PK", "PP", "kp", "b1", "pw", "cl", "qic", "ec"]

/-- The environment after the scalars it reads are kept and the array changes in the table only. -/
lemma SwEnv.newR2 {B : ℕ} {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} {σ σ' : Env}
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (hv : ∀ y ∈ SwVars, σ'.vars y = σ.vars y)
    (ha : σ'.arrs "TK" = σ.arrs "TK") (hl : (σ'.arrs "R").length = (σ.arrs "R").length)
    (hhi : ∀ y, PK ≤ y → (σ'.arrs "R").getD y 0 = (σ.arrs "R").getD y 0)
    (hlow : ∀ y, y < PK → (σ'.arrs "R").getD y 0 < B) :
    SwEnv B arr n P k b1 pw c qic ec PK σ' := by
  refine ⟨by rw [ha]; exact h.hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hlen, h.hE, h.hnB,
    by rw [hl]; exact h.hRlen, by rw [hl]; exact h.hRK, ?_, ?_, h.hPKB, h.hPB, h.hkB, h.hb1B,
    h.hpwB, h.hcB, h.hqB, h.heB⟩
  · rw [hv "PK" (by simp [SwVars])]; exact h.vPK
  · rw [hv "PP" (by simp [SwVars])]; exact h.vPP
  · rw [hv "kp" (by simp [SwVars])]; exact h.vkp
  · rw [hv "b1" (by simp [SwVars])]; exact h.vb1
  · rw [hv "pw" (by simp [SwVars])]; exact h.vpw
  · rw [hv "cl" (by simp [SwVars])]; exact h.vcl
  · rw [hv "qic" (by simp [SwVars])]; exact h.vqic
  · rw [hv "ec" (by simp [SwVars])]; exact h.vec
  · intro c' hc'; rw [hhi _ (by omega)]; exact h.hRv c' hc'
  · intro y
    by_cases hy : y < PK
    · exact hlow y hy
    · rw [hhi y (by omega)]; exact h.hRB y

/-- The sweep loop. -/
def sweepLoop : Com := fLoop "jj" "PK" sweepBody

lemma swVars_of {y : String} (hy : y ∈ SwVars) : y ∉ "jj" :: SSW := by
  simp only [SwVars, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [SSW, S1, S2, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 12800000 in
/-- **The sweep of a day.** -/
theorem sweepLoop_run {arr : List ℕ} {n P k b1 pw c qic ec PK : ℕ} (σ : Env)
    (h : SwEnv B arr n P k b1 pw c qic ec PK σ) (hP0 : 0 < P)
    (hcells : ∀ x < PK, (σ.arrs "R").getD x 0 = 1 →
      CellOk arr (σ.arrs "R") n P k b1 pw c qic ec PK B x)
    (h01 : ∀ x < PK, (σ.arrs "R").getD x 0 ≤ 1) :
    ∃ σ', Run B sweepLoop σ σ' ((400 + 10 + 4) * PK + 6) ∧
      SwEnv B arr n P k b1 pw c qic ec PK σ' ∧
      σ'.arrs "R" = D3List.swRun PK (tgtM P k b1 pw c qic ec (eOrd arr (σ.arrs "R") PK))
        (σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ "jj" :: SSW → σ'.vars y = σ.vars y := by
  set R0 := σ.arrs "R" with hR0
  set f := tgtM P k b1 pw c qic ec (eOrd arr R0 PK) with hf
  have hfx : ∀ x < PK, R0.getD x 0 = 1 → ∀ y, f x = some y → x < y ∧ y < PK := by
    intro x hx h1 y hy
    have hc := hcells x hx h1
    have hy' : tgtM P k b1 pw c qic ec (eOrd arr R0 PK) x = some y := hy
    unfold tgtM at hy'
    split at hy'
    · rename_i hg
      have h4 := hc.2.2.2 hg
      have := Option.some.inj hy'
      subst this
      exact ⟨by omega, h4⟩
    · exact absurd hy' (by simp)
  have hlen0 : PK ≤ R0.length := h.hRK
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "jj" "PK" sweepBody
    (fun j σ' => SwEnv B arr n P k b1 pw c qic ec PK σ' ∧
      σ'.arrs "R" = (List.range j).foldl (fun A j => D3List.swStep f (PK - 1 - j) A) R0 ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ "jj" :: SSW → σ'.vars y = σ.vars y)
    400 PK σ h.vPK (fun j σ' hq => hq.1.vPK) (by decide) (by have := h.hPKB; omega)
    ⟨h.newR2 (fun y hy => by
        have : y ≠ "jj" := fun e => swVars_of hy (by simp [e])
        simp [Env.setVar, this]) (by simp [Env.setVar]) (by simp [Env.setVar]) (by simp [Env.setVar])
        (fun y hy => by simpa [Env.setVar] using h.hRB y),
      by simp [Env.setVar, hR0], by simp [Env.setVar], by simp [Env.setVar],
      fun y hy => by
        have : y ≠ "jj" := fun e => hy (by simp [e])
        simp [Env.setVar, this]⟩
    (fun j σ' v hq => ⟨hq.1.newR2 (fun y hy => by
          have : y ≠ "jj" := fun e => swVars_of hy (by simp [e])
          simp [Env.setVar, this]) (by simp [Env.setVar]) (by simp [Env.setVar])
          (by intro y hy; simp [Env.setVar]) (fun y hy => by simpa [Env.setVar] using hq.1.hRB y),
        by simpa [Env.setVar] using hq.2.1, by simpa [Env.setVar] using hq.2.2.1,
        by simpa [Env.setVar] using hq.2.2.2.1, fun y hy => by
          have : y ≠ "jj" := fun e => hy (by simp [e])
          simp only [Env.setVar, if_neg this]; exact hq.2.2.2.2 y hy⟩)
    (by
      intro j σ1 hq hjv hjn
      obtain ⟨hh1, hR1, hA1, hO1, hF1⟩ := hq
      have hinv := D3List.swRun_inv PK f R0 hfx (fun x hx => h01 x hx) hlen0 j (by omega)
      obtain ⟨hl1, hhi1, hin1⟩ := hinv
      have hpre := D3List.swRun_pre PK f R0 hfx (fun x hx => h01 x hx) hlen0 j (by omega) (PK - 1 - j)
        (by omega)
      have hcong : eOrd arr (σ1.arrs "R") PK = eOrd arr R0 PK :=
        eOrd_congr arr _ _ PK (fun y hy => by rw [hR1]; exact hhi1 y hy)
      obtain ⟨σ2, r2, hR2, hA2, hO2, hF2⟩ := sweepBody_run (B := B) σ1 hh1 j hjv hjn (by
        intro h1
        have hx : R0.getD (PK - 1 - j) 0 = 1 := by rw [← hpre, ← hR1]; exact h1
        have := hcells _ (by omega) hx
        unfold CellOk at this ⊢
        rw [hcong]
        exact this)
      have hR2' : σ2.arrs "R" = (List.range (j + 1)).foldl
          (fun A j => D3List.swStep f (PK - 1 - j) A) R0 := by
        rw [hR2, hcong, hR1, List.range_succ, List.foldl_append]
        rfl
      obtain ⟨hl2, hhi2, hin2⟩ := D3List.swRun_inv PK f R0 hfx (fun x hx => h01 x hx) hlen0 (j + 1)
        (by omega)
      refine ⟨σ2, r2, ⟨hh1.newR2 (fun y hy => hF2 y (fun e => swVars_of hy (by
          simp only [List.mem_cons]; right; exact e))) (by rw [hA2]) (by rw [hR2', hl2, hR1, hl1])
          (fun y hy => by rw [hR2', hhi2 y hy]; rw [hR1, hhi1 y hy])
          (fun y hy => by
            rw [hR2', hin2 y hy]
            have := h.hPKB
            split <;> omega), hR2', by rw [hA2, hA1], by rw [hO2, hO1], fun z hz => ?_⟩, ?_⟩
      · have hz' : z ∉ SSW := fun e => hz (List.mem_cons_of_mem _ e)
        rw [hF2 z hz']; exact hF1 z hz
      · rw [hF2 "jj" (by simp [SSW, S1, S2])]; exact hjv)
  obtain ⟨hh, hRfin, hAfin, hOfin, hFfin⟩ := hQ
  exact ⟨σ', r, hh, by rw [hRfin]; rfl, hAfin, hOfin, hFfin⟩

end Lax117284Proofs.Machine.D3Sweep
