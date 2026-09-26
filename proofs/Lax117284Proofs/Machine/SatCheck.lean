import Lax117284Proofs.Machine.SatRank
import Lax117284Proofs.Machine.Flag

/-!
The pass over the positions of the formula that checks that every position names a variable of the
formula and is the first or the second occurrence of its literal.
-/

namespace Lax117284Proofs.Machine.SatCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank

variable {B : ℕ}

/-- The check of position `i`. -/
def chkBody : Com :=
  .seq (.assign "o" (V "i"))
  (.seq rankCom
  (.seq (.ite (.lt (V "vo") (V "n")) .skip (.assign "ok" (.lit 0)))
  (.seq (.ite (.lt (.lit 1) (V "cnt")) (.assign "ok" (.lit 0)) .skip)
    (bumpS "i"))))

def chkLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) chkBody)

/-- The scalars the pass assigns. -/
def AC : List String := ARC ++ ["o", "ok", "i"]

structure CInv (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = S
  vn : σ.vars "n" = n
  hi : σ.vars "i" ≤ S
  hok : σ.vars "ok" = flagTo (PassS arr) ok0 (σ.vars "i")
  fr : ∀ y, y ∉ AC → σ.vars y = σ0.vars y

lemma flag_fail (P : ℕ → Prop) [DecidablePred P] (ok0 i : ℕ) (h : ¬ P i) :
    flagTo P ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flag_pass (P : ℕ → Prop) [DecidablePred P] (ok0 i : ℕ) (h : P i) (hok : ok0 ≤ 1) :
    flagTo P ok0 (i + 1) = flagTo P ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le P ok0 i
  by_cases h1 : flagTo P ok0 i = 1
  · simp [h1, h]
  · have : flagTo P ok0 i = 0 := by omega
    simp [this]

lemma cinv_step (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ σ' : Env) (hI : CInv arr S n ok0 σ0 σ)
    (hlt : σ.vars "i" < S) (hv : ∀ y, y ∉ AC → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (PassS arr) ok0 (σ.vars "i" + 1)) :
    CInv arr S n ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hNv := hI.vN
  have hnv := hI.vn
  have hile := hI.hi
  have hokv := hI.hok
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]
    rw [if_neg (by decide), hv "N" (by simp [AC, ARC]), hNv]
  · simp only [Env.setVar]
    rw [if_neg (by decide), hv "n" (by simp [AC, ARC]), hnv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 6400000 in
theorem chkBody_spec (arr : List ℕ) (S n ok0 : ℕ) (σ0 : Env)
    (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * S ≤ arr.length) (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => CInv arr S n ok0 σ0 σ ∧ σ.vars "i" < S) chkBody
      (fun σ σ' => CInv arr S n ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) (120 + 64 * S) := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hNv, hnv, hile, hokv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨k, hk⟩ : ∃ k, σ.vars "i" = k := ⟨_, rfl⟩
  rw [hk] at hlt hokv
  have hokle : flagTo (PassS arr) ok0 k ≤ 1 := flagTo_le _ _ _
  have r0 : Run B (.assign "o" (V "i")) σ (σ.setVar "o" k) (1 + (V "i").size) := by
    have := Run.assign (B := B) (x := "o") (σ := σ) (e := V "i") (v := k)
      (by have := evalB_var (B := B) (x := "i") (σ := σ) (by omega); rwa [hk] at this)
    exact this
  set σ1 := σ.setVar "o" k with hσ1
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have ho1 : σ1.vars "o" = k := by simp [hσ1, Env.setVar]
  obtain ⟨σ2, r2, hc2, hvo2, hso2, ha2, hout2, hf2⟩ := rankCom_run (B := B) arr k σ1
    (fun k' hk' => hEv k' (by omega)) (fun k' hk' => hEs k' (by omega)) (by omega) (by omega)
    hA1 ho1
  have hn2 : σ2.vars "n" = n := by
    rw [hf2 "n" (by simp [ARC])]; simp [hσ1, Env.setVar, hnv]
  have hcnt_le : rankN arr k ≤ k := by
    unfold rankN
    have := List.countP_le_length (p := fun o' => decide (arr.getD (3 + 2 * o') 0 =
      arr.getD (3 + 2 * k) 0 ∧ arr.getD (4 + 2 * o') 0 = arr.getD (4 + 2 * k) 0))
      (l := List.range k)
    simpa using this
  have e1 := hEv k hlt
  have hframe2 : ∀ y, y ∉ AC → σ2.vars y = σ.vars y := by
    intro y hy
    have g1 : y ∉ ARC := fun h => hy (List.mem_append_left _ h)
    have g2 : y ≠ "o" := fun h => hy (by simp [AC, h])
    rw [hf2 y g1]; simp [hσ1, Env.setVar, g2]
  have hk2 : σ2.vars "i" = k := by
    have g : "i" ∉ ARC := by decide
    rw [hf2 "i" g]; simp [hσ1, Env.setVar, hk]
  have hok2 : σ2.vars "ok" = flagTo (PassS arr) ok0 k := by
    have g : "ok" ∉ ARC := by decide
    rw [hf2 "ok" g]; simp [hσ1, Env.setVar, hokv]
  have hasg2 : σ2.arrs = σ.arrs := by rw [ha2]; simp [hσ1, Env.setVar]
  have hout2' : σ2.out = σ.out := by rw [hout2]; simp [hσ1, Env.setVar]
  have c1 := cond_ltv (B := B) "vo" "n" σ2 _ _ hvo2 hn2 (by omega) (by omega)
  have c2 : (Cond.lt (.lit 1) (V "cnt")).evalB B σ2 = some (decide (1 < rankN arr k)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_lit (B := B) (σ := σ2) (n := 1) (by omega))
      (evalB_var (B := B) (x := "cnt") (σ := σ2) (by rw [hc2]; omega))
    rw [hc2] at h
    exact h
  have c2ok : ∀ σ' : Env, σ'.vars "cnt" = rankN arr k →
      (Cond.lt (.lit 1) (V "cnt")).evalB B σ' = some (decide (1 < rankN arr k)) := fun σ' h => by
    have := evalB_condLt (B := B) (σ := σ') (evalB_lit (B := B) (σ := σ') (n := 1) (by omega))
      (evalB_var (B := B) (x := "cnt") (σ := σ') (by rw [h]; omega))
    rw [h] at this
    exact this
  have rI : ∀ σ' : Env, σ'.vars "i" = k →
      Run B (bumpS "i") σ' (σ'.setVar "i" (k + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ'
          (σ'.setVar "i" (σ'.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hrok : ∀ σ' : Env, Run B (.assign "ok" (.lit 0)) σ' (σ'.setVar "ok" 0) 2 := fun σ' =>
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hokframe : ∀ σ' : Env, (∀ y, y ∉ AC → σ'.vars y = σ.vars y) →
      ∀ y, y ∉ AC → (σ'.setVar "ok" 0).vars y = σ.vars y := fun σ' h y hy => by
    have hyo : y ≠ "ok" := fun h' => hy (by simp [AC, h'])
    simp only [Env.setVar, if_neg hyo]
    exact h y hy
  have hcost : Krank k ≤ 46 + 64 * S := by unfold Krank; omega
  by_cases hp1 : arr.getD (3 + 2 * k) 0 < n
  · have hT1 : (Cond.lt (V "vo") (V "n")).evalB B σ2 = some true := by
      rw [c1]; exact congrArg some (decide_eq_true hp1)
    by_cases hp2 : 1 < rankN arr k
    · have hT2 : (Cond.lt (.lit 1) (V "cnt")).evalB B σ2 = some true := by
        rw [c2]; exact congrArg some (decide_eq_true hp2)
      have hfail : ¬ PassS arr k := fun h => by have := h.2; omega
      obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ (σ2.setVar "ok" 0) hI' (by rw [hk]; exact hlt)
        (hokframe σ2 hframe2) (by simp [Env.setVar, hasg2]) (by simp [Env.setVar, hout2'])
        (by simp [Env.setVar, hk2, hk])
        (by simp [Env.setVar, hk]; exact (flag_fail (PassS arr) ok0 _ hfail).symm)
      have hi3 : (σ2.setVar "ok" 0).vars "i" = k := by simp [Env.setVar, hk2]
      exact ⟨_, ((r0.seq (r2.seq ((Run.ite_true hT1 Run.skip).seq
        ((Run.ite_true hT2 (hrok σ2)).seq (rI _ hi3))))).mono (by
          simp [Cond.size, Expr.size]; omega)), by rw [hk] at hJ; exact hJ, by
          rw [hk] at hJi ⊢; exact hJi⟩
    · have hF2 : (Cond.lt (.lit 1) (V "cnt")).evalB B σ2 = some false := by
        rw [c2]; exact congrArg some (decide_eq_false hp2)
      have hpass : PassS arr k := ⟨by omega, by omega⟩
      obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ σ2 hI' (by rw [hk]; exact hlt) hframe2 hasg2
        hout2' (by rw [hk2, hk]) (by
          rw [hok2, hk, flag_pass (PassS arr) ok0 k hpass hok0])
      exact ⟨_, ((r0.seq (r2.seq ((Run.ite_true hT1 Run.skip).seq
        ((Run.ite_false hF2 Run.skip).seq (rI _ hk2))))).mono (by
          simp [Cond.size, Expr.size]; omega)), by rw [hk] at hJ; exact hJ, by
          rw [hk] at hJi ⊢; exact hJi⟩
  · have hF1 : (Cond.lt (V "vo") (V "n")).evalB B σ2 = some false := by
      rw [c1]; exact congrArg some (decide_eq_false hp1)
    have hfail : ¬ PassS arr k := fun h => hp1 (by have := h.1; rwa [← hn] at this)
    have hi3 : (σ2.setVar "ok" 0).vars "i" = k := by simp [Env.setVar, hk2]
    have hokz : (σ2.setVar "ok" 0).vars "ok" = flagTo (PassS arr) ok0 (k + 1) := by
      simp [Env.setVar]; exact (flag_fail (PassS arr) ok0 _ hfail).symm
    by_cases hp2 : 1 < rankN arr k
    · have hT2 : (Cond.lt (.lit 1) (V "cnt")).evalB B (σ2.setVar "ok" 0) = some true := by
        rw [c2ok _ (by simp [Env.setVar, hc2])]; exact congrArg some (decide_eq_true hp2)
      obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ ((σ2.setVar "ok" 0).setVar "ok" 0) hI'
        (by rw [hk]; exact hlt)
        (fun y hy => by
          have hyo : y ≠ "ok" := fun h' => hy (by simp [AC, h'])
          simp only [Env.setVar, if_neg hyo]; exact hframe2 y hy)
        (by simp [Env.setVar, hasg2]) (by simp [Env.setVar, hout2'])
        (by simp [Env.setVar, hk2, hk]) (by simp [Env.setVar, hk]; exact (flag_fail (PassS arr) ok0 _ hfail).symm)
      have hi4 : ((σ2.setVar "ok" 0).setVar "ok" 0).vars "i" = k := by simp [Env.setVar, hk2]
      exact ⟨_, ((r0.seq (r2.seq ((Run.ite_false hF1 (hrok σ2)).seq
        ((Run.ite_true hT2 (hrok _)).seq (rI _ hi4))))).mono (by
          simp [Cond.size, Expr.size]; omega)), by rw [hk] at hJ; exact hJ, by
          rw [hk] at hJi ⊢; exact hJi⟩
    · have hF2 : (Cond.lt (.lit 1) (V "cnt")).evalB B (σ2.setVar "ok" 0) = some false := by
        rw [c2ok _ (by simp [Env.setVar, hc2])]; exact congrArg some (decide_eq_false hp2)
      obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ (σ2.setVar "ok" 0) hI'
        (by rw [hk]; exact hlt) (hokframe σ2 hframe2) (by simp [Env.setVar, hasg2])
        (by simp [Env.setVar, hout2']) (by simp [Env.setVar, hk2, hk]) (by rw [hk]; exact hokz)
      exact ⟨_, ((r0.seq (r2.seq ((Run.ite_false hF1 (hrok σ2)).seq
        ((Run.ite_false hF2 Run.skip).seq (rI _ hi3))))).mono (by
          simp [Cond.size, Expr.size]; omega)), by rw [hk] at hJ; exact hJ, by
          rw [hk] at hJi ⊢; exact hJi⟩

/-- **The pass.** -/
theorem chkLoop_spec (arr : List ℕ) (S n ok0 : ℕ) (σ : Env)
    (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * S ≤ arr.length) (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = S) (hnv : σ.vars "n" = n)
    (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B chkLoop σ σ' ((120 + 64 * S + 4) * S + 6) ∧
      σ'.vars "ok" = flagTo (PassS arr) ok0 S ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AC → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := chkBody) "i" "N"
    (CInv arr S n ok0 σ) S (120 + 64 * S) (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (chkBody_spec arr S n ok0 σ hn hEv hEs hlen hSB hnB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hNv],
      by simp [Env.setVar, hnv], by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassS arr) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

end Lax117284Proofs.Machine.SatCheck
