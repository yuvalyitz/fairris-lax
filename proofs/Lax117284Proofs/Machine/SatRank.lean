import Lax117284Proofs.Machine.SatOps

/-!
The number of earlier positions of the formula that carry the same variable and sign as a given
position: a loop over the earlier positions that counts.
-/

namespace Lax117284Proofs.Machine.SatRank

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.SatSem

variable {B : ℕ}

abbrev bumpS (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- The position `o'` carries the variable `v` and the sign `s`. -/
def rpred (arr : List ℕ) (v s : ℕ) (o' : ℕ) : Bool :=
  decide (arr.getD (3 + 2 * o') 0 = v ∧ arr.getD (4 + 2 * o') 0 = s)

/-- The body of the loop: compare the earlier position `j` with the given one. -/
def rankBody : Com :=
  .seq (.assign "vj" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "j")))))
  (.seq (.assign "sj" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "j")))))
  (.seq (.ite (.eq (V "vj") (V "vo")) (.ite (.eq (V "sj") (V "so")) (bumpS "cnt") .skip) .skip)
    (bumpS "j")))

def rankLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "o")) rankBody)

/-- The scalars the loop assigns. -/
def AR : List String := ["j", "vj", "sj", "cnt"]

structure RInv (arr : List ℕ) (v s o : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vo : σ.vars "o" = o
  hv : σ.vars "vo" = v
  hs : σ.vars "so" = s
  hj : σ.vars "j" ≤ o
  hc : σ.vars "cnt" = (List.range (σ.vars "j")).countP (rpred arr v s)
  fr : ∀ y, y ∉ AR → σ.vars y = σ0.vars y

lemma countP_range_succ (p : ℕ → Bool) (j : ℕ) :
    (List.range (j + 1)).countP p = (List.range j).countP p + if p j = true then 1 else 0 := by
  rw [List.range_succ, List.countP_append]
  by_cases h : p j = true
  · rw [List.countP_cons_of_pos h, if_pos h]; rfl
  · rw [List.countP_cons_of_neg h, if_neg h]; rfl

lemma rinv_step (arr : List ℕ) (v s o : ℕ) (σ0 σ σ' : Env) (hI : RInv arr v s o σ0 σ)
    (hlt : σ.vars "j" < o) (hv : ∀ y, y ∉ AR → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (hj : σ'.vars "j" = σ.vars "j")
    (hcnt : σ'.vars "cnt" = (List.range (σ.vars "j" + 1)).countP (rpred arr v s)) :
    RInv arr v s o σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hov := hI.vo
  have hvo := hI.hv
  have hsv := hI.hs
  have hjle := hI.hj
  have hc := hI.hc
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "o" (by simp [AR]), hov]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "vo" (by simp [AR]), hvo]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "so" (by simp [AR]), hsv]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hcnt]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AR, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 1600000 in
theorem rankBody_spec (arr : List ℕ) (v s o : ℕ) (σ0 : Env)
    (hEv : ∀ k < o, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < o, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * o ≤ arr.length) (hoB : 2 * o + 16 < B) (hvB : v + 8 < B) (hsB : s + 8 < B) :
    Spec B (fun σ => RInv arr v s o σ0 σ ∧ σ.vars "j" < o) rankBody
      (fun σ σ' => RInv arr v s o σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 60 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hov, hvo, hsv, hjle, hc, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  set j := σ.vars "j" with hjdef
  have hjv : σ.vars "j" = j := rfl
  have hcnt_le : (List.range j).countP (rpred arr v s) ≤ j := by
    have := List.countP_le_length (p := rpred arr v s) (l := List.range j)
    simpa using this
  have hcB : σ.vars "cnt" < B := by rw [hc]; omega
  have e1 := hEv j hlt
  have e2 := hEs j hlt
  have s1 := asg_idx (B := B) "vj" 3 2 "j" σ arr j hA rfl (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vj" (arr.getD (3 + 2 * j) 0) with hσ1
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have s2 := asg_idx (B := B) "sj" 4 2 "j" σ1 arr j hA1 hj1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "sj" (arr.getD (4 + 2 * j) 0) with hσ2
  have hvj : σ2.vars "vj" = arr.getD (3 + 2 * j) 0 := by simp [hσ2, hσ1, Env.setVar]
  have hsj : σ2.vars "sj" = arr.getD (4 + 2 * j) 0 := by simp [hσ2, Env.setVar]
  have hvo2 : σ2.vars "vo" = v := by simp [hσ2, hσ1, Env.setVar, hvo]
  have hso2 : σ2.vars "so" = s := by simp [hσ2, hσ1, Env.setVar, hsv]
  have hj2 : σ2.vars "j" = j := by simp [hσ2, hσ1, Env.setVar, hjv]
  have hcn2 : σ2.vars "cnt" = σ.vars "cnt" := by simp [hσ2, hσ1, Env.setVar]
  have ha2 : σ2.arrs = σ.arrs := by simp [hσ2, hσ1, Env.setVar]
  have ho2 : σ2.out = σ.out := by simp [hσ2, hσ1, Env.setVar]
  have hfr2 : ∀ y, y ∉ AR → σ2.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "vj" := fun h => hy (by simp [AR, h])
    have g2 : y ≠ "sj" := fun h => hy (by simp [AR, h])
    simp [hσ2, hσ1, Env.setVar, g1, g2]
  have c1 := cond_eqv (B := B) "vj" "vo" σ2 _ _ hvj hvo2 (by omega) (by omega)
  have c2 := cond_eqv (B := B) "sj" "so" σ2 _ _ hsj hso2 (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  by_cases hm1 : arr.getD (3 + 2 * j) 0 = v
  · have hT1 : (Cond.eq (V "vj") (V "vo")).evalB B σ2 = some true := by
      rw [c1, hm1]; simp
    by_cases hm2 : arr.getD (4 + 2 * j) 0 = s
    · have hT2 : (Cond.eq (V "sj") (V "so")).evalB B σ2 = some true := by
        rw [c2, hm2]; simp
      have hp1 : rpred arr v s j = true := by
        unfold rpred; simp only [decide_eq_true_eq]; exact ⟨hm1, hm2⟩
      have s3 := asg_addl (B := B) "cnt" "cnt" 1 σ2 (σ.vars "cnt") (by rw [hcn2]) (by omega)
        (by omega) (by omega)
      obtain ⟨hJ, hJi⟩ := rinv_step arr v s o σ0 σ (σ2.setVar "cnt" (σ.vars "cnt" + 1)) hI' hlt
        (fun y hy => by
          have : y ≠ "cnt" := fun h => hy (by simp [AR, h])
          simp only [Env.setVar, if_neg this]; exact hfr2 y hy)
        (by simp [Env.setVar, ha2]) (by simp [Env.setVar, ho2]) (by simp [Env.setVar, hj2, hjdef])
        (by
          simp only [Env.setVar, if_true]
          rw [countP_range_succ, hp1, ← hc]
          simp)
      have s3' : Run B (bumpS "cnt") σ2 (σ2.setVar "cnt" (σ.vars "cnt" + 1)) 5 := s3
      exact ⟨_, (s1.seq (s2.seq ((Run.ite_true hT1 (Run.ite_true hT2 s3')).seq
        (rI _ (by simp [Env.setVar, hj2]))))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
    · have hF2 : (Cond.eq (V "sj") (V "so")).evalB B σ2 = some false := by
        rw [c2]; simp only [beq_eq_false_iff_ne.mpr hm2]
      have hp0 : rpred arr v s j = false := by
        unfold rpred; simp only [decide_eq_false_iff_not]; exact fun h => hm2 h.2
      obtain ⟨hJ, hJi⟩ := rinv_step arr v s o σ0 σ σ2 hI' hlt hfr2 ha2 ho2 hj2
        (by rw [hcn2, countP_range_succ, hp0, ← hc]; simp)
      exact ⟨_, (s1.seq (s2.seq ((Run.ite_true hT1 (Run.ite_false hF2 Run.skip)).seq
        (rI _ hj2)))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
  · have hF1 : (Cond.eq (V "vj") (V "vo")).evalB B σ2 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hm1]
    have hp0 : rpred arr v s j = false := by
      unfold rpred; simp only [decide_eq_false_iff_not]; exact fun h => hm1 h.1
    obtain ⟨hJ, hJi⟩ := rinv_step arr v s o σ0 σ σ2 hI' hlt hfr2 ha2 ho2 hj2
      (by rw [hcn2, countP_range_succ, hp0, ← hc]; simp)
    exact ⟨_, (s1.seq (s2.seq ((Run.ite_false hF1 Run.skip).seq
      (rI _ hj2)))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩

/-- **The loop counts.** -/
theorem rankLoop_spec (arr : List ℕ) (v s o : ℕ) (σ : Env)
    (hEv : ∀ k < o, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < o, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * o ≤ arr.length) (hoB : 2 * o + 16 < B) (hvB : v + 8 < B) (hsB : s + 8 < B)
    (hA : σ.arrs "TK" = arr) (hov : σ.vars "o" = o) (hvo : σ.vars "vo" = v)
    (hso : σ.vars "so" = s) (hcn : σ.vars "cnt" = 0) :
    ∃ σ', Run B rankLoop σ σ' ((60 + 4) * o + 6) ∧
      σ'.vars "cnt" = (List.range o).countP (rpred arr v s) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AR → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := rankBody) "j" "o"
    (RInv arr v s o σ) o 60 (by omega) (fun _ h => h.hj) (fun _ h => h.vo)
    (rankBody_spec arr v s o σ hEv hEs hlen hoB hvB hsB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hov],
      by simp [Env.setVar, hvo], by simp [Env.setVar, hso], by simp [Env.setVar], by
        simp [Env.setVar, hcn], fun y hy => by
      have hyj : y ≠ "j" := fun h => hy (by simp [AR, h])
      simp [Env.setVar, hyj]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hc, hi]
  · intro y hy
    rw [hI.fr y hy]

/-- Read the given position and count. -/
def rankCom : Com :=
  .seq (.assign "vo" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "o")))))
  (.seq (.assign "so" (.get "TK" (add (.lit 4) (mul (.lit 2) (V "o")))))
  (.seq (.assign "cnt" (.lit 0)) rankLoop))

/-- The scalars `rankCom` assigns. -/
def ARC : List String := ["vo", "so", "j", "vj", "sj", "cnt"]

/-- The cost of the count. -/
def Krank (o : ℕ) : ℕ := 40 + (60 + 4) * o + 6

/-- **The rank of a position.** -/
theorem rankCom_run (arr : List ℕ) (o : ℕ) (σ : Env)
    (hEv : ∀ k < o + 1, arr.getD (3 + 2 * k) 0 + 8 < B)
    (hEs : ∀ k < o + 1, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hlen : 5 + 2 * o ≤ arr.length) (hoB : 2 * o + 16 < B)
    (hA : σ.arrs "TK" = arr) (hov : σ.vars "o" = o) :
    ∃ σ', Run B rankCom σ σ' (Krank o) ∧ σ'.vars "cnt" = rankN arr o ∧
      σ'.vars "vo" = arr.getD (3 + 2 * o) 0 ∧ σ'.vars "so" = arr.getD (4 + 2 * o) 0 ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ ARC → σ'.vars y = σ.vars y := by
  have e1 := hEv o (by omega)
  have e2 := hEs o (by omega)
  have s1 := asg_idx (B := B) "vo" 3 2 "o" σ arr o hA hov (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vo" (arr.getD (3 + 2 * o) 0) with hσ1
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have ho1 : σ1.vars "o" = o := by simp [hσ1, Env.setVar, hov]
  have s2 := asg_idx (B := B) "so" 4 2 "o" σ1 arr o hA1 ho1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "so" (arr.getD (4 + 2 * o) 0) with hσ2
  have s3 := asg_lit (B := B) "cnt" 0 σ2 (by omega)
  set σ3 := σ2.setVar "cnt" 0 with hσ3
  obtain ⟨σ4, r4, c4, a4, o4, f4⟩ := rankLoop_spec (B := B) arr (arr.getD (3 + 2 * o) 0)
    (arr.getD (4 + 2 * o) 0) o σ3 (fun k hk => hEv k (by omega)) (fun k hk => hEs k (by omega))
    (by omega) hoB e1 e2 (by simp [hσ3, hσ2, hσ1, Env.setVar, hA])
    (by simp [hσ3, hσ2, hσ1, Env.setVar, hov])
    (by simp [hσ3, hσ2, hσ1, Env.setVar]) (by simp [hσ3, hσ2, Env.setVar])
    (by simp [hσ3, Env.setVar])
  refine ⟨σ4, (s1.seq (s2.seq (s3.seq r4))).mono (by unfold Krank; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c4]; rfl
  · rw [f4 "vo" (by simp [AR])]; simp [hσ3, hσ2, hσ1, Env.setVar]
  · rw [f4 "so" (by simp [AR])]; simp [hσ3, hσ2, Env.setVar]
  · rw [a4]; simp [hσ3, hσ2, hσ1, Env.setVar]
  · rw [o4]; simp [hσ3, hσ2, hσ1, Env.setVar]
  · intro y hy
    have g1 : y ≠ "vo" := fun h => hy (by simp [ARC, h])
    have g2 : y ≠ "so" := fun h => hy (by simp [ARC, h])
    have g3 : y ∉ AR := fun h => hy (by
      simp only [AR, ARC, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    rw [f4 y g3]
    simp [hσ3, hσ2, hσ1, Env.setVar, g1, g2, show y ≠ "cnt" from fun h => hy (by simp [ARC, h])]

end Lax117284Proofs.Machine.SatRank
