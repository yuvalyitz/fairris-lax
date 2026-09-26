import Lax117284Proofs.Machine.SatOps
import Lax117284Proofs.Machine.SatRank
import Lax117284Proofs.Machine.MisSem

/-!
Counting the ones in a run of the array: a loop over `bd` consecutive entries starting at `bs`. The
number of neighbours of a vertex, and the position of a neighbour among them, are such counts.
-/

namespace Lax117284Proofs.Machine.MisCount

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatRank (bumpS countP_range_succ)

variable {B : ℕ}

/-- The entry at `bs + j` is one. -/
def onePred (arr : List ℕ) (bs j : ℕ) : Bool := decide (arr.getD (bs + j) 0 = 1)

/-- The body of the loop. -/
def cntBody : Com :=
  .seq (.assign "xj" (.get "TK" (.bin .add (V "bs") (V "j"))))
  (.seq (.ite (.eq (V "xj") (.lit 1)) (bumpS "cnt") .skip) (bumpS "j"))

def cntLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "bd")) cntBody)

/-- Count the ones among the `bd` entries from `bs`. -/
def cntCom : Com := .seq (.assign "cnt" (.lit 0)) cntLoop

/-- The scalars the loop assigns. -/
def AN : List String := ["j", "xj", "cnt"]

structure NInv (arr : List ℕ) (bs bd : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vbs : σ.vars "bs" = bs
  vbd : σ.vars "bd" = bd
  hj : σ.vars "j" ≤ bd
  hc : σ.vars "cnt" = (List.range (σ.vars "j")).countP (onePred arr bs)
  fr : ∀ y, y ∉ AN → σ.vars y = σ0.vars y

lemma ninv_step (arr : List ℕ) (bs bd : ℕ) (σ0 σ σ' : Env) (hI : NInv arr bs bd σ0 σ)
    (hlt : σ.vars "j" < bd) (hv : ∀ y, y ∉ AN → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hj : σ'.vars "j" = σ.vars "j")
    (hcnt : σ'.vars "cnt" = (List.range (σ.vars "j" + 1)).countP (onePred arr bs)) :
    NInv arr bs bd σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hbs := hI.vbs
  have hbd := hI.vbd
  have hjle := hI.hj
  have hc := hI.hc
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "bs" (by simp [AN]), hbs]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "bd" (by simp [AN]), hbd]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hcnt]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AN, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 1600000 in
theorem cntBody_spec (arr : List ℕ) (bs bd : ℕ) (σ0 : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) :
    Spec B (fun σ => NInv arr bs bd σ0 σ ∧ σ.vars "j" < bd) cntBody
      (fun σ σ' => NInv arr bs bd σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 40 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hbs, hbd, hjle, hc, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨j, hjv⟩ : ∃ j, σ.vars "j" = j := ⟨_, rfl⟩
  rw [hjv] at hlt hc
  have hcnt_le : (List.range j).countP (onePred arr bs) ≤ j := by
    have := List.countP_le_length (p := onePred arr bs) (l := List.range j)
    simpa using this
  have hcB : σ.vars "cnt" < B := by rw [hc]; omega
  have e1 := hE j hlt
  have hidx : (V "bs" : Expr).evalB B σ = some bs := by
    have := evalB_var (B := B) (x := "bs") (σ := σ) (by omega)
    rwa [hbs] at this
  have hidj : (V "j" : Expr).evalB B σ = some j := by
    have := evalB_var (B := B) (x := "j") (σ := σ) (by omega)
    rwa [hjv] at this
  have hsum : (Expr.bin .add (V "bs") (V "j")).evalB B σ = some (bs + j) :=
    evalB_bin hidx hidj (by simp; omega)
  have hget := RunStep.eval_get B σ "TK" (Expr.bin .add (V "bs") (V "j")) (bs + j) hsum
    (by rw [hA]; omega) (by rw [hA]; omega)
  rw [hA] at hget
  have s1 : Run B (.assign "xj" (.get "TK" (.bin .add (V "bs") (V "j")))) σ
      (σ.setVar "xj" (arr.getD (bs + j) 0)) (1 + (Expr.get "TK" (Expr.bin .add (V "bs") (V "j"))).size) :=
    Run.assign hget
  set σ1 := σ.setVar "xj" (arr.getD (bs + j) 0) with hσ1
  have hxj : σ1.vars "xj" = arr.getD (bs + j) 0 := by simp [hσ1, Env.setVar]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have hcn1 : σ1.vars "cnt" = σ.vars "cnt" := by simp [hσ1, Env.setVar]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AN → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "xj" := fun h => hy (by simp [AN, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_eql (B := B) "xj" 1 σ1 _ hxj (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (bumpS "j") σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hpj : ∀ b : Bool, onePred arr bs j = b → True := fun _ _ => trivial
  by_cases hone : arr.getD (bs + j) 0 = 1
  · have hT : (Cond.eq (V "xj") (.lit 1)).evalB B σ1 = some true := by
      rw [c1, hone]; simp
    have hp1 : onePred arr bs j = true := decide_eq_true hone
    have s3 := asg_addl (B := B) "cnt" "cnt" 1 σ1 (σ.vars "cnt") (by rw [hcn1]) (by omega)
      (by omega) (by omega)
    have s3' : Run B (bumpS "cnt") σ1 (σ1.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s3
    obtain ⟨hJ, hJi⟩ := ninv_step arr bs bd σ0 σ (σ1.setVar "cnt" (σ.vars "cnt" + 1)) hI' (by rw [hjv]; exact hlt)
      (fun y hy => by
        have : y ≠ "cnt" := fun h => hy (by simp [AN, h])
        simp only [Env.setVar, if_neg this]; exact hfr1 y hy)
      (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by simp [Env.setVar, hj1, hjv])
      (by
        simp only [Env.setVar, if_true]
        rw [hjv, countP_range_succ, hp1, ← hc]
        simp)
    exact ⟨_, (s1.seq ((Run.ite_true hT s3').seq (rI _ (by simp [Env.setVar, hj1])))).mono
      (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
        rw [hjv] at hJi ⊢; exact hJi⟩
  · have hF : (Cond.eq (V "xj") (.lit 1)).evalB B σ1 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hone]
    have hp0 : onePred arr bs j = false := decide_eq_false hone
    obtain ⟨hJ, hJi⟩ := ninv_step arr bs bd σ0 σ σ1 hI' (by rw [hjv]; exact hlt) hfr1 ha1 ho1
      (by rw [hj1, hjv])
      (by rw [hcn1, hjv, countP_range_succ, hp0, ← hc]; simp)
    exact ⟨_, (s1.seq ((Run.ite_false hF Run.skip).seq (rI _ hj1))).mono
      (by simp [Cond.size, Expr.size]), by rw [hjv] at hJ; exact hJ, by
        rw [hjv] at hJi ⊢; exact hJi⟩

/-- **The loop counts.** -/
theorem cntLoop_spec (arr : List ℕ) (bs bd : ℕ) (σ : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) (hA : σ.arrs "TK" = arr) (hbs : σ.vars "bs" = bs)
    (hbd : σ.vars "bd" = bd) (hcn : σ.vars "cnt" = 0) :
    ∃ σ', Run B cntLoop σ σ' ((40 + 4) * bd + 6) ∧
      σ'.vars "cnt" = (List.range bd).countP (onePred arr bs) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AN → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := cntBody) "j" "bd"
    (NInv arr bs bd σ) bd 40 (by omega) (fun _ h => h.hj) (fun _ h => h.vbd)
    (cntBody_spec arr bs bd σ hE hlen hB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hbs],
      by simp [Env.setVar, hbd], by simp [Env.setVar], by
        simp [Env.setVar, hcn], fun y hy => by
      have hyj : y ≠ "j" := fun h => hy (by simp [AN, h])
      simp [Env.setVar, hyj]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hc, hi]
  · intro y hy
    rw [hI.fr y hy]

/-- **The count of the ones in a run.** -/
theorem cntCom_run (arr : List ℕ) (bs bd : ℕ) (σ : Env)
    (hE : ∀ k < bd, arr.getD (bs + k) 0 + 8 < B) (hlen : bs + bd ≤ arr.length)
    (hB : bs + bd + 16 < B) (hA : σ.arrs "TK" = arr) (hbs : σ.vars "bs" = bs)
    (hbd : σ.vars "bd" = bd) :
    ∃ σ', Run B cntCom σ σ' ((40 + 4) * bd + 20) ∧
      σ'.vars "cnt" = (List.range bd).countP (onePred arr bs) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AN → σ'.vars y = σ.vars y := by
  have s0 := asg_lit (B := B) "cnt" 0 σ (by omega)
  obtain ⟨σ', r, c, a, o, f⟩ := cntLoop_spec (B := B) arr bs bd (σ.setVar "cnt" 0) hE hlen hB
    (by simp [Env.setVar, hA]) (by simp [Env.setVar, hbs]) (by simp [Env.setVar, hbd])
    (by simp [Env.setVar])
  refine ⟨σ', (s0.seq r).mono (by omega), c, a.trans (by simp [Env.setVar]),
    o.trans (by simp [Env.setVar]), fun y hy => ?_⟩
  rw [f y hy]
  have : y ≠ "cnt" := fun h => hy (by simp [AN, h])
  simp [Env.setVar, this]

end Lax117284Proofs.Machine.MisCount
