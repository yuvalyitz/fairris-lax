import Lax117284Proofs.Machine.JitCheck

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
