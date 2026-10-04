import Lax117284Proofs.Machine.JitCheck
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.JitSem
import Lax117284Proofs.Machine.WrapFinal
import Lax117284Proofs.Machine.BlockFinal

/-! ### `Lax117284Proofs.Machine.JitPass` -/

section
/-!
The pass over the table of processing times that checks that every job takes some time and is not
due before it starts.
-/

namespace Lax117284Proofs.Machine.JitPass

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.JitSem
open Lax117284Proofs.Machine.JitCheck

variable {B : ℕ}

/-- The job of cell `t` takes some time and is not due before it starts. -/
def PassJ (arr : List ℕ) (n t : ℕ) : Prop :=
  0 < arr.getD (2 + n + t) 0 ∧ arr.getD (2 + n + t) 0 ≤ arr.getD (2 + (t - t / n * n)) 0

instance (arr : List ℕ) (n : ℕ) : DecidablePred (PassJ arr n) := fun t => by
  unfold PassJ; infer_instance

/-- The test of cell `i`. -/
def jokChk : Com :=
  .seq cellIdx
    (.seq (.assign "pv" (.get "TK" (V "ip")))
      (.seq (.assign "dv" (.get "TK" (V "ij")))
        (.ite (.lt (.lit 0) (V "pv"))
          (.ite (.lt (V "dv") (V "pv")) (.assign "ok" (.lit 0)) .skip)
          (.assign "ok" (.lit 0)))))

def jokBody : Com := .seq jokChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def jokLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) jokBody)

/-- The scalars the pass assigns. -/
def AJ : List String := AI ++ ["pv", "dv", "ok", "i"]

structure JInv (arr : List ℕ) (m n ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = m * n
  hi : σ.vars "i" ≤ m * n
  hok : σ.vars "ok" = flagTo (PassJ arr n) ok0 (σ.vars "i")
  fr : ∀ y, y ∉ AJ → σ.vars y = σ0.vars y

lemma flagJ_fail (arr : List ℕ) (n ok0 i : ℕ) (h : ¬ PassJ arr n i) :
    flagTo (PassJ arr n) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flagJ_pass (arr : List ℕ) (n ok0 i : ℕ) (h : PassJ arr n i) (hok : ok0 ≤ 1) :
    flagTo (PassJ arr n) ok0 (i + 1) = flagTo (PassJ arr n) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (PassJ arr n) ok0 i
  by_cases h1 : flagTo (PassJ arr n) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (PassJ arr n) ok0 i = 0 := by omega
    simp [this]

lemma jinv_step (arr : List ℕ) (m n ok0 : ℕ) (σ0 σ σ' : Env) (hI : JInv arr m n ok0 σ0 σ)
    (hlt : σ.vars "i" < m * n) (hv : ∀ y, y ∉ AJ → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (PassJ arr n) ok0 (σ.vars "i" + 1)) :
    JInv arr m n ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hNv := hI.vN
  have hile := hI.hi
  have hokv := hI.hok
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]
    rw [if_neg (by decide), hv "N" (by simp [AJ, AI]), hNv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AJ, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 3200000 in
theorem jokBody_spec (arr : List ℕ) (m n ok0 : ℕ) (σ0 : Env)
    (hn0v : σ0.vars "n" = n) (ho0v : σ0.vars "o" = 2 + n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => JInv arr m n ok0 σ0 σ ∧ σ.vars "i" < m * n) jokBody
      (fun σ σ' => JInv arr m n ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 80 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hNv, hile, hokv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  have hnv : σ.vars "n" = n := by rw [hfr "n" (by simp [AJ, AI])]; exact hn0v
  have hov : σ.vars "o" = 2 + n := by rw [hfr "o" (by simp [AJ, AI])]; exact ho0v
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by rw [h] at hlt; simp at hlt)
  have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero (fun h => by
    rw [h] at hlt; simp at hlt))
  have hdiv : σ.vars "i" / n * n ≤ σ.vars "i" := Nat.div_mul_le_self _ _
  have hdiv2 : σ.vars "i" - σ.vars "i" / n * n < n := by
    have := Nat.mod_lt (σ.vars "i") hn0
    have := Nat.mod_def (σ.vars "i") n
    have e : σ.vars "i" / n * n = n * (σ.vars "i" / n) := Nat.mul_comm _ _
    omega
  obtain ⟨σ1, r1, a1, o1, hip, hij, hfr1⟩ := cellIdx_run (B := B) n (2 + n) (σ.vars "i") σ rfl hnv
    hov (by omega) (by omega) hn0 (by omega)
  have hp := hE (2 + n + σ.vars "i") (by omega)
  have hd := hE (2 + (σ.vars "i" - σ.vars "i" / n * n)) (by omega)
  have hA1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  have s2 := asg_tkv (B := B) "ip" "pv" σ1 arr (2 + n + σ.vars "i") hA1 hip (by omega) (by omega)
    (by omega)
  set σ2 := σ1.setVar "pv" (arr.getD (2 + n + σ.vars "i") 0) with hσ2
  have hij2 : σ2.vars "ij" = 2 + (σ.vars "i" - σ.vars "i" / n * n) := by
    simp [hσ2, Env.setVar, hij]
  have hA2 : σ2.arrs "TK" = arr := by simp [hσ2, Env.setVar, hA1]
  have s3 := asg_tkv (B := B) "ij" "dv" σ2 arr (2 + (σ.vars "i" - σ.vars "i" / n * n)) hA2 hij2
    (by omega) (by omega) (by omega)
  set σ3 := σ2.setVar "dv" (arr.getD (2 + (σ.vars "i" - σ.vars "i" / n * n)) 0) with hσ3
  have hpv : σ3.vars "pv" = arr.getD (2 + n + σ.vars "i") 0 := by simp [hσ3, hσ2, Env.setVar]
  have hdv : σ3.vars "dv" = arr.getD (2 + (σ.vars "i" - σ.vars "i" / n * n)) 0 := by
    simp [hσ3, Env.setVar]
  have hokv3 : σ3.vars "ok" = σ.vars "ok" := by
    simp [hσ3, hσ2, Env.setVar, hfr1 "ok" (by simp [AI])]
  have hiv3 : σ3.vars "i" = σ.vars "i" := by
    simp [hσ3, hσ2, Env.setVar, hfr1 "i" (by simp [AI])]
  have hframe3 : ∀ y, y ∉ AJ → σ3.vars y = σ.vars y := by
    intro y hy
    have hyAI : y ∉ AI := fun h => hy (List.mem_append_left _ h)
    have g6 : y ≠ "pv" := fun h => hy (by simp [AJ, h])
    have g7 : y ≠ "dv" := fun h => hy (by simp [AJ, h])
    simp [hσ3, hσ2, Env.setVar, g6, g7, hfr1 y hyAI]
  have ha3 : σ3.arrs = σ.arrs := by simp [hσ3, hσ2, Env.setVar, a1]
  have ho3 : σ3.out = σ.out := by simp [hσ3, hσ2, Env.setVar, o1]
  have hokle : flagTo (PassJ arr n) ok0 (σ.vars "i") ≤ 1 := flagTo_le _ _ _
  have hc1 : (Cond.lt (.lit 0) (V "pv")).evalB B σ3 = some (decide (0 < arr.getD (2 + n +
      σ.vars "i") 0)) := by
    have h := evalB_condLt (B := B) (σ := σ3) (evalB_lit (B := B) (σ := σ3) (n := 0) (by omega))
      (evalB_var (B := B) (x := "pv") (σ := σ3) (by rw [hpv]; omega))
    rw [hpv] at h
    exact h
  have hc2 : (Cond.lt (V "dv") (V "pv")).evalB B σ3 = some (decide (arr.getD (2 + (σ.vars "i" -
      σ.vars "i" / n * n)) 0 < arr.getD (2 + n + σ.vars "i") 0)) := by
    have h := evalB_condLt (B := B) (σ := σ3) (evalB_var (B := B) (x := "dv") (σ := σ3)
        (by rw [hdv]; omega))
      (evalB_var (B := B) (x := "pv") (σ := σ3) (by rw [hpv]; omega))
    rw [hdv, hpv] at h
    exact h
  have rI : ∀ σ' : Env, σ'.vars "i" = σ.vars "i" →
      Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ' (σ'.setVar "i" (σ.vars "i" + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ'
          (σ'.setVar "i" (σ'.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hrok : Run B (.assign "ok" (.lit 0)) σ3 (σ3.setVar "ok" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  have hokframe : ∀ y, y ∉ AJ → (σ3.setVar "ok" 0).vars y = σ.vars y := fun y hy => by
    have hyo : y ≠ "ok" := fun h => hy (by simp [AJ, h])
    simp only [Env.setVar, if_neg hyo]
    exact hframe3 y hy
  by_cases hpos : 0 < arr.getD (2 + n + σ.vars "i") 0
  · have hT1 : (Cond.lt (.lit 0) (V "pv")).evalB B σ3 = some true := by
      rw [hc1]; exact congrArg some (decide_eq_true hpos)
    by_cases hlt2 : arr.getD (2 + (σ.vars "i" - σ.vars "i" / n * n)) 0 <
        arr.getD (2 + n + σ.vars "i") 0
    · have hT2 : (Cond.lt (V "dv") (V "pv")).evalB B σ3 = some true := by
        rw [hc2]; exact congrArg some (decide_eq_true hlt2)
      have hfail : ¬ PassJ arr n (σ.vars "i") := fun h => by
        have := h.2; omega
      obtain ⟨hJ, hJi⟩ := jinv_step arr m n ok0 σ0 σ (σ3.setVar "ok" 0) hI' hlt hokframe
        (by simp [Env.setVar, ha3]) (by simp [Env.setVar, ho3]) (by simp [Env.setVar, hiv3])
        (by simp [Env.setVar]; exact (flagJ_fail arr n ok0 _ hfail).symm)
      exact ⟨_, ((r1.seq (s2.seq (s3.seq (Run.ite_true hT1 (Run.ite_true hT2 hrok))))).seq
        (rI _ (by simp [Env.setVar, hiv3]))).mono (by simp [Cond.size]), hJ, hJi⟩
    · have hF2 : (Cond.lt (V "dv") (V "pv")).evalB B σ3 = some false := by
        rw [hc2]; exact congrArg some (decide_eq_false hlt2)
      have hpass : PassJ arr n (σ.vars "i") := ⟨hpos, by omega⟩
      obtain ⟨hJ, hJi⟩ := jinv_step arr m n ok0 σ0 σ σ3 hI' hlt hframe3 ha3 ho3 hiv3
        (by rw [hokv3, flagJ_pass arr n ok0 _ hpass hok0, hokv])
      exact ⟨_, ((r1.seq (s2.seq (s3.seq (Run.ite_true hT1 (Run.ite_false hF2 Run.skip))))).seq
        (rI _ hiv3)).mono (by simp [Cond.size]), hJ, hJi⟩
  · have hF1 : (Cond.lt (.lit 0) (V "pv")).evalB B σ3 = some false := by
      rw [hc1]; exact congrArg some (decide_eq_false hpos)
    have hfail : ¬ PassJ arr n (σ.vars "i") := fun h => hpos h.1
    obtain ⟨hJ, hJi⟩ := jinv_step arr m n ok0 σ0 σ (σ3.setVar "ok" 0) hI' hlt hokframe
      (by simp [Env.setVar, ha3]) (by simp [Env.setVar, ho3]) (by simp [Env.setVar, hiv3])
      (by simp [Env.setVar]; exact (flagJ_fail arr n ok0 _ hfail).symm)
    exact ⟨_, ((r1.seq (s2.seq (s3.seq (Run.ite_false hF1 hrok)))).seq
      (rI _ (by simp [Env.setVar, hiv3]))).mono (by simp [Cond.size]), hJ, hJi⟩

end Lax117284Proofs.Machine.JitPass

end

/-! ### `Lax117284Proofs.Machine.JitPrint` -/

section
/-!
Writing the image of Theorem 11: the two counts, the table of `(p, d)` cell by cell, and the
parameter `1`.
-/

namespace Lax117284Proofs.Machine.JitPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitCheck Lax117284Proofs.Machine.JitPass

variable {B : ℕ}

/-- The loop over the table: run the pass. -/
theorem jokLoop_spec (arr : List ℕ) (m n ok0 : ℕ) (σ : Env)
    (hn0v : σ.vars "n" = n) (ho0v : σ.vars "o" = 2 + n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = m * n) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B jokLoop σ σ' ((80 + 4) * (m * n) + 6) ∧
      σ'.vars "ok" = flagTo (PassJ arr n) ok0 (m * n) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AJ → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := jokBody) "i" "N"
    (JInv arr m n ok0 σ) (m * n) 80 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (jokBody_spec arr m n ok0 σ hn0v ho0v hE hL hlen hnB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hNv],
      by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassJ arr n) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AJ, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

/-- Write a cell of the image. -/
def cellPrint : Com :=
  .seq cellIdx (.seq (emitAt "TK" "ip") (emitAt "TK" "ij"))

/-- Scratch scalars of a cell. -/
def SJ : List String := AI ++ SCR

/-- The cost of a cell. -/
def KcellJ (Sz : ℕ) : ℕ := 30 + 2 * (48 * Sz + 50) + 20

/-- **A cell of the image.** -/
theorem cellPrint_run (Sz : ℕ) (arr : List ℕ) (n o c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hi : σ.vars "i" = c) (hn : σ.vars "n" = n) (ho : σ.vars "o" = 2 + n) (hn0 : 0 < n)
    (hc : c < B) (hnB : n < B) (hoB : 2 + n + c < B)
    (hp : 2 + n + c < arr.length) (hd : 2 + (c - c / n * n) < arr.length)
    (hpB : arr.getD (2 + n + c) 0 + 4 < B) (hdB : arr.getD (2 + (c - c / n * n)) 0 + 4 < B) :
    ∃ σ', Run B cellPrint σ σ' (KcellJ Sz) ∧
      σ'.out = σ.out ++ (bitsNat (arr.getD (2 + n + c) 0) ++
        bitsNat (arr.getD (2 + (c - c / n * n)) 0)) ∧
      (∀ y ∉ SJ, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  have hq : c / n * n ≤ c := Nat.div_mul_le_self c n
  obtain ⟨σ1, r1, a1, o1, hip, hij, hfr1⟩ := cellIdx_run (B := B) n (2 + n) c σ hi hn ho hc hnB
    hn0 hoB
  have hA1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "TK" "ip" Sz (by decide) σ1
    ⟨by rw [hA1, hip]; exact hp, by rw [hip]; omega, by rw [hA1, hip]; exact hpB,
      by rw [hA1, hip]; exact hs _ hpB⟩
  have hij2 : σ2.vars "ij" = 2 + (c - c / n * n) := by rw [v2 "ij" (by decide)]; exact hij
  have hA2 : σ2.arrs "TK" = arr := by rw [a2]; exact hA1
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitAt_spec (B := B) "TK" "ij" Sz (by decide) σ2
    ⟨by rw [hA2, hij2]; exact hd, by rw [hij2]; omega, by rw [hA2, hij2]; exact hdB,
      by rw [hA2, hij2]; exact hs _ hdB⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold KcellJ; omega), ?_, fun y hy => ?_, ?_⟩
  · rw [o3, o2, o1, hA2, hA1, hij2, hip, List.append_assoc]
  · have hyAI : y ∉ AI := fun h => hy (List.mem_append_left _ h)
    have hyS : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SJ, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v3 y hyS, v2 y hyS, hfr1 y hyAI]
  · rw [a3, a2, a1]

end Lax117284Proofs.Machine.JitPrint

end

/-! ### `Lax117284Proofs.Machine.JitAccept` -/

section
/-!
The whole of the reduction of Theorem 11 after the tokenizer has accepted: read the counts off the
array, check the table, and write either the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.JitAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitCheck Lax117284Proofs.Machine.JitPass
open Lax117284Proofs.Machine.JitPrint Lax117284Proofs.Machine.FreeAccept

variable {B : ℕ}

/-- The numbers of the image, read off an array. -/
def outJG (arr : List ℕ) (n m : ℕ) : List ℕ :=
  [n, m] ++ (List.range (m * n)).flatMap
    (fun t => [arr.getD (2 + n + t) 0, arr.getD (2 + (t - t / n * n)) 0]) ++ [1]

/-- **A loop over the cells.** -/
theorem cellLoopJ_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ0.arrs "TK" = arr)
    (hn : σ0.vars "n" = n) (ho : σ0.vars "o" = 2 + n) (hN : σ0.vars "N" = m * n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) :
    ∃ σ', Run B (outLoop "N" cellPrint) σ0 σ' ((KcellJ Sz + 10 + 4) * (m * n) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (m * n)).flatMap
        (fun t => [arr.getD (2 + n + t) 0, arr.getD (2 + (t - t / n * n)) 0])) ∧
      (∀ y ∉ "i" :: SJ, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "N" cellPrint ("i" :: SJ)
    (fun t => bitsNat (arr.getD (2 + n + t) 0) ++ bitsNat (arr.getD (2 + (t - t / n * n)) 0))
    (KcellJ Sz) (m * n) σ0 (by simp) (by decide) hN (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have ho' : σ.vars "o" = 2 + n := by rw [hAg.2 "o" (by decide)]; exact ho
      have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by rw [h] at hlt; simp at hlt)
      have hnm : n ≤ m * n := Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero (fun h => by
        rw [h] at hlt; simp at hlt))
      have hq : σ.vars "i" / n * n ≤ σ.vars "i" := Nat.div_mul_le_self _ _
      have hdiv2 : σ.vars "i" - σ.vars "i" / n * n < n := by
        have := Nat.mod_lt (σ.vars "i") hn0
        have := Nat.mod_def (σ.vars "i") n
        have e : σ.vars "i" / n * n = n * (σ.vars "i" / n) := Nat.mul_comm _ _
        omega
      have hp := hE (2 + n + σ.vars "i") (by omega)
      have hd := hE (2 + (σ.vars "i" - σ.vars "i" / n * n)) (by omega)
      obtain ⟨σ1, r1, o1, v1, a1⟩ := cellPrint_run (B := B) Sz arr n (2 + n) (σ.vars "i") σ hs hA'
        rfl hn' ho' hn0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ SJ := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o]
  congr 1
  simp only [numBits, List.flatMap_assoc]
  refine List.flatMap_congr fun t _ => ?_
  simp [numBits]


/-- Write the whole image. -/
def printJ : Com :=
  .seq (emitVar "n") (.seq (emitVar "m") (.seq (outLoop "N" cellPrint) (emitLit 1)))

/-- The cost of writing the image. -/
def KprintJ (Sz N : ℕ) : ℕ := 3 * (48 * Sz + 50) + (KcellJ Sz + 10 + 4) * N + 6

/-- **Writing the image.** -/
theorem printJ_run (Sz : ℕ) (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hn : σ.vars "n" = n) (hm : σ.vars "m" = m) (ho : σ.vars "o" = 2 + n)
    (hN : σ.vars "N" = m * n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) :
    ∃ σ', Run B printJ σ σ' (KprintJ Sz (m * n)) ∧
      σ'.out = σ.out ++ numBits (outJG arr n m) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n" Sz σ
    ⟨by rw [hn]; omega, by rw [hn]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m" Sz σ1
    ⟨by rw [v1 "m" (by decide), hm]; omega,
      by rw [v1 "m" (by decide), hm]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cellLoopJ_run (B := B) Sz arr n m σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "o" (by decide)]; exact ho)
    (by rw [z2 "N" (by decide)]; exact hN) hE hL hlen hnB
  obtain ⟨σ4, r4, o4, v4, a4⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ3 trivial
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintJ; omega), ?_⟩
  rw [o4, o3, o2, o1, z1 "m" (by decide), hm, hn]
  unfold outJG
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

/-- Read the counts off the array. -/
def prepJ : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "o" (add (.lit 2) (V "n")))
    (.assign "ok" (.lit 1)))))

theorem prepJ_spec (arr : List ℕ)
    (hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B) (hlen : 2 ≤ arr.length) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepJ
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧ σ'.vars "o" = 2 + arr.getD 0 0 ∧
        σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "o" → y ≠ "ok" → σ'.vars y = σ.vars y) 40 := by
  run_vcg
  all_goals (
    have hA := ‹σ.arrs "TK" = arr›
    have e0 := hE 0 (by omega)
    have e1 := hE 1 (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    intro y a b c d e
    simp [a, b, c, d, e])

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptJ : Com :=
  .seq prepJ (.seq jokLoop (.ite (.eq (V "ok") (.lit 1)) printJ rejectPrint))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccJ (Sz l : ℕ) : ℕ := 200 + 84 * l + KprintJ Sz l + 3 * (48 * Sz + 50)

lemma KaccJ_mono (Sz a b : ℕ) (h : a ≤ b) : KaccJ Sz a ≤ KaccJ Sz b := by
  unfold KaccJ KprintJ
  have := Nat.mul_le_mul_left (KcellJ Sz + 10 + 4) h
  omega

theorem acceptJ_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 + 8 < B)
    (hlen : 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0 ≤ arr.length)
    (hl : arr.getD 1 0 * arr.getD 0 0 ≤ l) (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptJ σ σ' (KaccJ Sz l) ∧
      σ'.out = σ.out ++
        (if ∀ t < arr.getD 1 0 * arr.getD 0 0, PassJ arr (arr.getD 0 0) t
          then numBits (outJG arr (arr.getD 0 0) (arr.getD 1 0)) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  have hB2 : 6 < B := by omega
  have hnB : n + 8 < B := hE 0 (by omega)
  have hmB : m + 8 < B := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1o, e1ok, e1a, e1o', e1f⟩ :=
    (prepJ_spec (B := B) arr hE hL (by omega)) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := jokLoop_spec (B := B) arr m n 1 σ1 e1n e1o hE hL hlen hnB
    le_rfl A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassJ arr n) 1 (m * n); omega
  have hcond : (σ2.vars "ok" = 1) ↔ ∀ t < m * n, PassJ arr n t := by
    rw [e2ok, flagTo_eq_one]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  by_cases hok : σ2.vars "ok" = 1
  · have hpass := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := printJ_run (B := B) Sz arr n m σ2 hs A2
      (by rw [e2f "n" (by simp [AJ, AI]), e1n])
      (by rw [e2f "m" (by simp [AJ, AI]), e1m])
      (by rw [e2f "o" (by simp [AJ, AI]), e1o])
      (by rw [e2f "N" (by simp [AJ, AI]), e1N]) hE hL hlen hnB hmB
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccJ
      simp only [Cond.size, Expr.size]
      have : KprintJ Sz (m * n) ≤ KprintJ Sz l := by
        unfold KprintJ
        have := Nat.mul_le_mul_left (KcellJ Sz + 10 + 4) hl
        omega
      omega
    · rw [o3, e2o, e1o', if_pos hpass]
  · have hno : ¬ ∀ t < m * n, PassJ arr n t := fun h => hok (hcond.2 h)
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccJ
      simp only [Cond.size, Expr.size]
      omega
    · rw [e3o, e2o, e1o', if_neg hno]

end Lax117284Proofs.Machine.JitAccept

end

/-! ### `Lax117284Proofs.Machine.JNk` -/

section
/-!
What the format of an instance with a fairness parameter expects next, as a command.
-/

namespace Lax117284Proofs.Machine.JNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.JitSem

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev add (e f : Expr) : Expr := .bin .add e f

/-- What the format expects, the counts and the parameter being `n`, `m`: a number as long as the
table has not been read, and the end after it. -/
def nkJ : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (add (.get "TK" (.lit 0))
          (mul (.get "TK" (.lit 1)) (.get "TK" (.lit 0)))))
        (.ite (.lt (V "j") (V "n3")) (set "kind" 0) (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the counts being `n` and `m`. -/
def kindCodeJ (Tn n m : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindJ n m (Tn - 2))

variable {B : ℕ}

theorem nkJ_flat (Tn n m : ℕ) (hB : 2 * (m * n) + Tn + n + 8 < B) (hm : m + 8 < B) (hn : n + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (σ.arrs "TK").getD 1 0 = m ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkJ
      (fun σ σ' => σ'.vars "kind" = kindCodeJ Tn n m ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 60 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = m›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k2 : kcode .done = 2 := rfl
    unfold kindCodeJ kindJ
    split_ifs <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkJ_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt (EJ) cap nkJ 60 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · -- fewer than two tokens: a count is expected
    have hE : EJ toks = .num := by
      rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · cases a <;> rfl
      · simp at h2
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · -- the counts are known
    rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    have ha : a.kind = .num := by simpa [EJ] using hfol 0 (by simp)
    have hb : b.kind = .num := by
      have := hfol 1 (by simp)
      simpa [EJ] using this
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := by cases a <;> simp_all [Tok.kind]
    obtain ⟨m, rfl⟩ : ∃ m, b = .num m := by cases b <;> simp_all [Tok.kind]
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hm : m < Bt := hsm (.num m) (by simp)
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    have g1 : (σ.arrs "TK").getD 1 0 = m := by
      have := congrArg (fun l => l.getD 1 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    have hmn : m * n ≤ Bt * Bt := Nat.mul_le_mul hm.le hn.le
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkJ_flat (B := B) (rest.length + 2) n m (by omega)
      (by omega) (by omega) σ ⟨by rw [hT], g0, g1, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, EJ_cons]
    simp [kindCodeJ]

end Lax117284Proofs.Machine.JNk

end

/-! ### `Lax117284Proofs.Machine.JitFinal` -/

section
/-!
The reduction of Theorem 11 from just-in-time scheduling on unrelated machines to the problem with
day-independent due dates is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.JitFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitPass Lax117284Proofs.Machine.JitAccept
open Lax117284Proofs.Machine.Wrap Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.Machine.TokModel

open scoped Classical

lemma sub_div_mul (t n : ℕ) : t - t / n * n = t % n := by
  have := Nat.mod_def t n
  rw [Nat.mul_comm]; omega

theorem outJG_eq (arr ns : List ℕ) (hs : ShapeJ ns) (h : arr.take ns.length = ns) :
    outJG arr (arr.getD 0 0) (arr.getD 1 0) = outJ ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold outJG outJ
  rw [h0, h1]
  congr 2
  refine List.flatMap_congr fun t ht => ?_
  have ht' := List.mem_range.mp ht
  have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht'; simp at ht')
  have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
  have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
    Nat.pos_of_ne_zero (fun h => by rw [h] at ht'; simp at ht'))
  rw [sub_div_mul, hg (2 + ns.getD 0 0 + t) (by omega), hg (2 + t % ns.getD 0 0) (by omega)]

theorem cond_iffJ (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : ShapeJ ns) :
    (∀ t < arr.getD 1 0 * arr.getD 0 0, PassJ arr (arr.getD 0 0) t) ↔ ValidJ ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold ValidJ
  rw [h0, h1]
  constructor
  · intro hp t ht
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht)
    have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
      Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht))
    have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have := hp t ht
    unfold PassJ at this
    rw [sub_div_mul, hg _ (by omega), hg _ (by omega)] at this
    exact this
  · intro hv t ht
    have hn : 0 < ns.getD 0 0 := Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht)
    have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ (
      Nat.pos_of_ne_zero (fun h => by rw [h] at ht; simp at ht))
    have hmod : t % ns.getD 0 0 < ns.getD 0 0 := Nat.mod_lt _ hn
    have := hv t ht
    unfold PassJ
    rw [sub_div_mul, hg _ (by omega), hg _ (by omega)]
    exact this

lemma KmonoJ (Sz a b : ℕ) (h : a ≤ b) : KaccJ Sz a ≤ KaccJ Sz b := KaccJ_mono Sz a b h

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EJ
  Sh := ShapeJ
  nk := JNk.nkJ
  Knk := 60
  hnk := fun B Bt cap hB => JNk.nkJ_spec (B := B) Bt cap hB
  hconf := fun ns hs => conformsJ_of_shape hs
  hshape := fun ts h => shapeJ_of_conforms h
  red := Lax117284.Theorem11.reduce
  cond := ValidJ
  outW := fun ns => numCode (outJ ns)
  sem_acc := fun ns hs hc => t11_eq ns hc hs
  rejW := rejected
  sem_rej := fun w h => t11_rej w (by
    rintro ⟨ns, hw, hs, hv⟩
    exact h ⟨ns, hw, hs, hv⟩)
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptJ
  Kacc := KaccJ
  Kmono := KmonoJ
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hl' : ns.length = 2 + (arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0) := by
      rw [h0, h1]; exact hl
    have hE : ∀ k < 2 + arr.getD 0 0 + arr.getD 1 0 * arr.getD 0 0, arr.getD k 0 + 8 < B :=
      fun k hk => by
        rw [hg k (by omega)]
        have := hval k (by omega)
        omega
    obtain ⟨σ', r, o⟩ := acceptJ_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) hA
    have hK : KaccJ Sz ns.length ≤ KaccJ Sz ns.length := le_rfl
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : ValidJ ns
    · rw [if_pos hc, if_pos ((cond_iffJ arr ns harr ⟨h2, hl⟩).2 hc)]
      show numBits (outJG arr (arr.getD 0 0) (arr.getD 1 0)) = natBits (numCode (outJ ns))
      rw [natBits_numCode, outJG_eq arr ns ⟨h2, hl⟩ harr]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffJ arr ns harr ⟨h2, hl⟩).1 h)),
        FreeMain.natBits_rejected]

def layoutJ : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "o", "q", "tt", "jj", "ip", "ij", "pv", "dv"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutJ W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, JNk.nkJ,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptJ, prepJ, printJ, JitPrint.cellPrint, JitCheck.cellIdx, jokLoop, jokBody, jokChk,
    FreeAccept.rejectPrint, Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutJ, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 1000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show KaccJ Sz l ≤ _
  unfold KaccJ KprintJ JitPrint.KcellJ
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l)]

/--
---
conclusion: Lax117284.Theorem11.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the numbers of the instance — the counts, the due dates and the processing times machine by
machine —, a pass over the table of processing times checks that every job takes some time and is
not due before it starts, and the numbers of the image are written cell by cell, each cell being
the processing time of its job on its machine and the due date of that job, found from the cell's
index by division. The counts are the same, and the parameter is `1`. A word that is not the code
of an instance is answered with the rejected word. The numbers may be exponential in the length
of the input, which the word length of a polynomial-time word RAM accommodates, and polynomial
time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Theorem11.reduce) :=
  WrapFinal.polyTime W layoutJ com_ok rfl (by simp [layoutJ]) 1000 Kpoly (fun Sz => by
    show 3 * (48 * Sz + 50) ≤ 1000 * (Sz + 1)
    omega)

end Lax117284Proofs.Machine.JitFinal

end
