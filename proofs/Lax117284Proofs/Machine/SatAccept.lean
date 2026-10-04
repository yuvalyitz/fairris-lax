import Lax117284Proofs.Machine.SatCheck
import Lax117284Proofs.Machine.FreeAccept

/-! ### `Lax117284Proofs.Machine.SatDue` -/

section
/-!
The due date of a client on a day: the case analysis of the construction as a command.
-/

namespace Lax117284Proofs.Machine.SatDue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank

variable {B : ℕ}

/-! ### The command -/

/-- A variable client: the variable it belongs to and, on the third day, which of the two. -/
def varCom : Com :=
  .seq (.assign "t3" (.bin .sub (V "i") (.lit 3)))
  (.seq (.assign "q1" (.bin .div (V "t3") (.lit 2)))
  (.ite (.eq (V "dy") (.lit 0)) (.assign "dv" (add (.lit 5) (mul (.lit 2) (V "q1"))))
    (.ite (.eq (V "dy") (.lit 1)) (.assign "dv" (.lit 2))
      (.seq (.assign "q2" (.bin .mul (V "q1") (.lit 2)))
      (.seq (.assign "r1" (.bin .sub (V "t3") (V "q2")))
        (.ite (.eq (V "r1") (.lit 0))
          (.assign "dv" (add (.lit 6) (mul (.lit 10) (V "q1"))))
          (.assign "dv" (add (.lit 11) (mul (.lit 10) (V "q1"))))))))))

/-- The client of an occurrence: on the third day it sits next to the variable that falsifies the
literal, on the others in the group of its clause. -/
def slotCom : Com :=
  .seq (.assign "o" (.bin .sub (V "i") (V "V3")))
  (.ite (.eq (V "dy") (.lit 2))
    (.seq rankCom
      (.seq (.assign "w5" (.bin .mul (V "vo") (.lit 5)))
      (.seq (.assign "w" (.bin .add (V "cnt") (V "w5")))
        (.ite (.lt (.lit 0) (V "so"))
          (.assign "dv" (add (.lit 5) (mul (.lit 2) (V "w"))))
          (.assign "dv" (add (.lit 10) (mul (.lit 2) (V "w"))))))))
    (.ite (.lt (V "o") (V "A2"))
      (.ite (.eq (V "dy") (.lit 0))
        (.seq (.assign "h" (.bin .div (V "o") (.lit 2)))
          (.assign "dv" (add (V "K7") (mul (.lit 2) (V "h")))))
        (.assign "dv" (.lit 2)))
      (.seq (.assign "t3" (.bin .sub (V "o") (V "A2")))
      (.seq (.assign "p" (.bin .div (V "t3") (.lit 3)))
        (.ite (.eq (V "dy") (.lit 0))
          (.assign "dv" (add (V "K9") (mul (.lit 2) (V "p"))))
          (.assign "dv" (add (.lit 6) (mul (.lit 3) (V "p")))))))))

/-- The due date of client `i` on day `dy`. -/
def dueCom : Com :=
  .ite (.lt (V "i") (.lit 3)) (.assign "dv" (.lit 2))
    (.ite (.lt (V "i") (V "V3")) varCom slotCom)

/-- The scalars the command assigns. -/
def AD : List String := ARC ++ ["dv", "q1", "r1", "o", "w", "h", "p", "t3", "q2", "w5"]

/-- Nothing changed but the scalars the command assigns. -/
def Step (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ AD → σ'.vars y = σ.vars y

lemma Step.trans {σ σ' σ'' : Env} (h : Step σ σ') (h' : Step σ' σ'') : Step σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun y hy => (h'.2.2 y hy).trans (h.2.2 y hy)⟩

lemma Step.setVar (σ : Env) (z : String) (v : ℕ) (hz : z ∈ AD) : Step σ (σ.setVar z v) :=
  ⟨rfl, rfl, fun y hy => by
    have : y ≠ z := fun h => hy (h ▸ hz)
    simp [Env.setVar, this]⟩

/-! ### The due date, by cases -/

section Cases

variable (arr : List ℕ)

lemma dueN_lt3 (d c : ℕ) (h : c < 3) : dueN arr d c = 2 := by
  unfold dueN; rw [if_pos h]

lemma dueN_var (d c : ℕ) (h3 : ¬ c < 3) (hv : c < 3 + 2 * arr.getD 0 0) :
    dueN arr d c = if d = 0 then 2 * ((c - 3) / 2) + 5 else if d = 1 then 2
      else if (c - 3) % 2 = 0 then 10 * ((c - 3) / 2) + 6 else 10 * ((c - 3) / 2) + 11 := by
  unfold dueN; rw [if_neg h3, if_pos hv]

lemma dueN_slot2 (c : ℕ) (h3 : ¬ c < 3) (hv : ¬ c < 3 + 2 * arr.getD 0 0) :
    dueN arr 2 c = (if arr.getD (4 + 2 * (c - 3 - 2 * arr.getD 0 0)) 0 ≠ 0 then
        10 * arr.getD (3 + 2 * (c - 3 - 2 * arr.getD 0 0)) 0 + 5 +
          2 * rankN arr (c - 3 - 2 * arr.getD 0 0)
      else 10 * arr.getD (3 + 2 * (c - 3 - 2 * arr.getD 0 0)) 0 + 10 +
          2 * rankN arr (c - 3 - 2 * arr.getD 0 0)) := by
  unfold dueN; rw [if_neg h3, if_neg hv, if_pos rfl]

lemma dueN_slotA (d c : ℕ) (h3 : ¬ c < 3) (hv : ¬ c < 3 + 2 * arr.getD 0 0) (hd : d ≠ 2)
    (ho : c - 3 - 2 * arr.getD 0 0 < 2 * arr.getD 1 0) :
    dueN arr d c = if d = 0 then 2 * arr.getD 0 0 + 2 * ((c - 3 - 2 * arr.getD 0 0) / 2) + 7
      else 2 := by
  unfold dueN; rw [if_neg h3, if_neg hv, if_neg hd, if_pos ho]

lemma dueN_slotB (d c : ℕ) (h3 : ¬ c < 3) (hv : ¬ c < 3 + 2 * arr.getD 0 0) (hd : d ≠ 2)
    (ho : ¬ c - 3 - 2 * arr.getD 0 0 < 2 * arr.getD 1 0) :
    dueN arr d c = if d = 0 then
        2 * arr.getD 0 0 + 2 * arr.getD 1 0 +
          2 * ((c - 3 - 2 * arr.getD 0 0 - 2 * arr.getD 1 0) / 3) + 9
      else 3 * ((c - 3 - 2 * arr.getD 0 0 - 2 * arr.getD 1 0) / 3) + 6 := by
  unfold dueN; rw [if_neg h3, if_neg hv, if_neg hd, if_neg ho]

end Cases

/-! ### The runs -/

/-- What the command reads. -/
structure DCtx (arr : List ℕ) (c d : ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = arr
  vi : σ.vars "i" = c
  vdy : σ.vars "dy" = d
  vV3 : σ.vars "V3" = 3 + 2 * arr.getD 0 0
  vA2 : σ.vars "A2" = 2 * arr.getD 1 0
  vK7 : σ.vars "K7" = 7 + 2 * arr.getD 0 0
  vK9 : σ.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0

/-- **A variable client.** -/
theorem varCom_run (arr : List ℕ) (S c d : ℕ) (σ : Env) (hx : DCtx arr c d σ) (hd : d < 3)
    (h3 : ¬ c < 3) (hv : c < 3 + 2 * arr.getD 0 0) (hn : arr.getD 0 0 ≤ S)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B varCom σ σ' 60 ∧ σ'.vars "dv" = dueN arr d c ∧ Step σ σ' := by
  obtain ⟨hA, vi, vdy, -, -, -, -⟩ := hx
  have hcB : c < B := by omega
  have s1 := asg_binr (B := B) .sub "i" 3 "t3" σ c vi (by simp only [Bop.apply_sub]; omega)
    (by omega) (by omega)
  simp only [Bop.apply_sub] at s1
  set σ1 := σ.setVar "t3" (c - 3) with hσ1
  have t1 : σ1.vars "t3" = c - 3 := by simp [hσ1, Env.setVar]
  have s2 := asg_binr (B := B) .div "t3" 2 "q1" σ1 (c - 3) t1 (by simp only [Bop.apply_div]; omega)
    (by omega) (by omega)
  simp only [Bop.apply_div] at s2
  set σ2 := σ1.setVar "q1" ((c - 3) / 2) with hσ2
  have q1 : σ2.vars "q1" = (c - 3) / 2 := by simp [hσ2, Env.setVar]
  have t2 : σ2.vars "t3" = c - 3 := by simp [hσ2, hσ1, Env.setVar]
  have vdy2 : σ2.vars "dy" = d := by simp [hσ2, hσ1, Env.setVar, vdy]
  have st2 : Step σ σ2 := (Step.setVar σ "t3" _ (by simp [AD])).trans
    (Step.setVar σ1 "q1" _ (by simp [AD]))
  have c1 := cond_eql (B := B) "dy" 0 σ2 d vdy2 (by omega) (by omega)
  by_cases hd0 : d = 0
  · have hT : (Cond.eq (V "dy") (.lit 0)).evalB B σ2 = some true := by rw [c1]; simp [hd0]
    have l := asg_linl (B := B) "dv" 5 2 "q1" σ2 ((c - 3) / 2) q1 (by omega) (by omega)
      (by omega) (by omega) (by omega)
    refine ⟨_, (s1.seq (s2.seq (Run.ite_true hT l))).mono (by simp [Cond.size, Expr.size]), ?_,
      st2.trans (Step.setVar σ2 "dv" _ (by simp [AD]))⟩
    rw [dueN_var arr d c h3 hv, if_pos hd0]
    simp [Env.setVar]; omega
  · have hF : (Cond.eq (V "dy") (.lit 0)).evalB B σ2 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hd0]
    have c2 := cond_eql (B := B) "dy" 1 σ2 d vdy2 (by omega) (by omega)
    by_cases hd1 : d = 1
    · have hT : (Cond.eq (V "dy") (.lit 1)).evalB B σ2 = some true := by rw [c2]; simp [hd1]
      have l := asg_lit (B := B) "dv" 2 σ2 (by omega)
      refine ⟨_, (s1.seq (s2.seq (Run.ite_false hF (Run.ite_true hT l)))).mono
        (by simp [Cond.size, Expr.size]), ?_, st2.trans (Step.setVar σ2 "dv" _ (by simp [AD]))⟩
      rw [dueN_var arr d c h3 hv, if_neg hd0, if_pos hd1]
      simp [Env.setVar]
    · have hF2 : (Cond.eq (V "dy") (.lit 1)).evalB B σ2 = some false := by
        rw [c2]; simp only [beq_eq_false_iff_ne.mpr hd1]
      have s3 := asg_binr (B := B) .mul "q1" 2 "q2" σ2 ((c - 3) / 2) q1
        (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
      simp only [Bop.apply_mul] at s3
      set σ3 := σ2.setVar "q2" ((c - 3) / 2 * 2) with hσ3
      have t3v : σ3.vars "t3" = c - 3 := by simp [hσ3, hσ2, hσ1, Env.setVar]
      have q2v : σ3.vars "q2" = (c - 3) / 2 * 2 := by simp [hσ3, Env.setVar]
      have s4 := asg_bin (B := B) .sub "t3" "q2" "r1" σ3 (c - 3) ((c - 3) / 2 * 2) t3v q2v
        (by simp only [Bop.apply_sub]; omega) (by omega) (by omega)
      simp only [Bop.apply_sub] at s4
      set σ4 := σ3.setVar "r1" (c - 3 - (c - 3) / 2 * 2) with hσ4
      have r1v : σ4.vars "r1" = c - 3 - (c - 3) / 2 * 2 := by simp [hσ4, Env.setVar]
      have q1v : σ4.vars "q1" = (c - 3) / 2 := by simp [hσ4, hσ3, hσ2, Env.setVar]
      have st4 : Step σ σ4 := (st2.trans (Step.setVar σ2 "q2" _ (by simp [AD]))).trans
        (Step.setVar σ3 "r1" _ (by simp [AD]))
      have c3 := cond_eql (B := B) "r1" 0 σ4 _ r1v (by omega) (by omega)
      by_cases hr : c - 3 - (c - 3) / 2 * 2 = 0
      · have hT : (Cond.eq (V "r1") (.lit 0)).evalB B σ4 = some true := by rw [c3]; simp [hr]
        have l := asg_linl (B := B) "dv" 6 10 "q1" σ4 ((c - 3) / 2) q1v (by omega) (by omega)
          (by omega) (by omega) (by omega)
        refine ⟨_, (s1.seq (s2.seq (Run.ite_false hF (Run.ite_false hF2
          (s3.seq (s4.seq (Run.ite_true hT l))))))).mono (by simp [Cond.size, Expr.size]), ?_,
          st4.trans (Step.setVar σ4 "dv" _ (by simp [AD]))⟩
        rw [dueN_var arr d c h3 hv, if_neg hd0, if_neg hd1, if_pos (by omega)]
        simp [Env.setVar]; omega
      · have hF3 : (Cond.eq (V "r1") (.lit 0)).evalB B σ4 = some false := by
          rw [c3]; simp only [beq_eq_false_iff_ne.mpr hr]
        have l := asg_linl (B := B) "dv" 11 10 "q1" σ4 ((c - 3) / 2) q1v (by omega) (by omega)
          (by omega) (by omega) (by omega)
        refine ⟨_, (s1.seq (s2.seq (Run.ite_false hF (Run.ite_false hF2
          (s3.seq (s4.seq (Run.ite_false hF3 l))))))).mono (by simp [Cond.size, Expr.size]), ?_,
          st4.trans (Step.setVar σ4 "dv" _ (by simp [AD]))⟩
        rw [dueN_var arr d c h3 hv, if_neg hd0, if_neg hd1, if_neg (by omega)]
        simp [Env.setVar]; omega

lemma Step.rank {σ σ' : Env} (a : σ'.arrs = σ.arrs) (o : σ'.out = σ.out)
    (f : ∀ y, y ∉ ARC → σ'.vars y = σ.vars y) : Step σ σ' :=
  ⟨a, o, fun y hy => f y (fun h => hy (List.mem_append_left _ h))⟩

/-- **A client of an occurrence.** -/
theorem slotCom_run (arr : List ℕ) (S c d : ℕ) (σ : Env) (hx : DCtx arr c d σ) (hd : d < 3)
    (h3 : ¬ c < 3) (hv : ¬ c < 3 + 2 * arr.getD 0 0) (hcl : c < 3 + 2 * arr.getD 0 0 + S)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S)
    (hpass : ∀ k < S, PassS arr k) (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B slotCom σ σ' (100 + 64 * S) ∧ σ'.vars "dv" = dueN arr d c ∧ Step σ σ' := by
  have hA := hx.hA
  have vi := hx.vi
  have vdy := hx.vdy
  have vV3 := hx.vV3
  have vA2 := hx.vA2
  have vK7 := hx.vK7
  have vK9 := hx.vK9
  clear hx
  have hcB : c < B := by omega
  have s1 := asg_bin (B := B) .sub "i" "V3" "o" σ c (3 + 2 * arr.getD 0 0) vi vV3
    (by simp only [Bop.apply_sub]; omega) (by omega) (by omega)
  simp only [Bop.apply_sub] at s1
  set σ1 := σ.setVar "o" (c - (3 + 2 * arr.getD 0 0)) with hσ1
  have ov : σ1.vars "o" = c - (3 + 2 * arr.getD 0 0) := by simp [hσ1, Env.setVar]
  have hoS : c - (3 + 2 * arr.getD 0 0) < S := by omega
  have st1 : Step σ σ1 := Step.setVar σ "o" _ (by simp [AD])
  have vdy1 : σ1.vars "dy" = d := by simp [hσ1, Env.setVar, vdy]
  have c1 := cond_eql (B := B) "dy" 2 σ1 d vdy1 (by omega) (by omega)
  by_cases hd2 : d = 2
  · have hT : (Cond.eq (V "dy") (.lit 2)).evalB B σ1 = some true := by rw [c1]; simp [hd2]
    set o := c - (3 + 2 * arr.getD 0 0) with ho
    obtain ⟨σ2, r2, hc2, hvo2, hso2, ha2, hout2, hf2⟩ := rankCom_run (B := B) arr o σ1
      (fun k' hk' => hEv k' (by omega)) (fun k' hk' => hEs k' (by omega)) (by omega) (by omega)
      (by simp [hσ1, Env.setVar, hA]) ov
    have st2 : Step σ σ2 := st1.trans (Step.rank ha2 hout2 hf2)
    have hp := hpass o hoS
    have hvoS : arr.getD (3 + 2 * o) 0 < S := by have := hp.1; omega
    have hrk : rankN arr o ≤ 1 := hp.2
    have s3 := asg_binr (B := B) .mul "vo" 5 "w5" σ2 (arr.getD (3 + 2 * o) 0) hvo2
      (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
    simp only [Bop.apply_mul] at s3
    set σ3 := σ2.setVar "w5" (arr.getD (3 + 2 * o) 0 * 5) with hσ3
    have cnt3 : σ3.vars "cnt" = rankN arr o := by simp [hσ3, Env.setVar, hc2]
    have w53 : σ3.vars "w5" = arr.getD (3 + 2 * o) 0 * 5 := by simp [hσ3, Env.setVar]
    have s4 := asg_bin (B := B) .add "cnt" "w5" "w" σ3 (rankN arr o) (arr.getD (3 + 2 * o) 0 * 5)
      cnt3 w53 (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
    simp only [Bop.apply_add] at s4
    set σ4 := σ3.setVar "w" (rankN arr o + arr.getD (3 + 2 * o) 0 * 5) with hσ4
    have wv : σ4.vars "w" = rankN arr o + arr.getD (3 + 2 * o) 0 * 5 := by simp [hσ4, Env.setVar]
    have so4 : σ4.vars "so" = arr.getD (4 + 2 * o) 0 := by
      simp [hσ4, hσ3, Env.setVar, hso2]
    have c3 := cond_lll (B := B) 0 "so" σ4 _ so4 (by have := hEs o hoS; omega) (by omega)
    have st4 : Step σ σ4 := (st2.trans (Step.setVar σ2 "w5" _ (by simp [AD]))).trans
      (Step.setVar σ3 "w" _ (by simp [AD]))
    by_cases hs : 0 < arr.getD (4 + 2 * o) 0
    · have hT3 : (Cond.lt (.lit 0) (V "so")).evalB B σ4 = some true := by
        rw [c3]; exact congrArg some (decide_eq_true hs)
      have l := asg_linl (B := B) "dv" 5 2 "w" σ4 (rankN arr o + arr.getD (3 + 2 * o) 0 * 5) wv
        (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨_, (s1.seq (Run.ite_true hT (r2.seq (s3.seq (s4.seq (Run.ite_true hT3 l)))))).mono
        (by simp [Cond.size, Expr.size, Krank]; omega), ?_,
        st4.trans (Step.setVar σ4 "dv" _ (by simp [AD]))⟩
      rw [hd2, dueN_slot2 arr c h3 hv, show c - 3 - 2 * arr.getD 0 0 = o by omega,
        if_pos (by omega)]
      simp only [Env.setVar, if_true]; omega
    · have hF3 : (Cond.lt (.lit 0) (V "so")).evalB B σ4 = some false := by
        rw [c3]; exact congrArg some (decide_eq_false hs)
      have l := asg_linl (B := B) "dv" 10 2 "w" σ4 (rankN arr o + arr.getD (3 + 2 * o) 0 * 5) wv
        (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨_, (s1.seq (Run.ite_true hT (r2.seq (s3.seq (s4.seq (Run.ite_false hF3 l)))))).mono
        (by simp [Cond.size, Expr.size, Krank]; omega), ?_,
        st4.trans (Step.setVar σ4 "dv" _ (by simp [AD]))⟩
      rw [hd2, dueN_slot2 arr c h3 hv, show c - 3 - 2 * arr.getD 0 0 = o by omega,
        if_neg (by omega)]
      simp only [Env.setVar, if_true]; omega
  · have hF : (Cond.eq (V "dy") (.lit 2)).evalB B σ1 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hd2]
    have vA21 : σ1.vars "A2" = 2 * arr.getD 1 0 := by simp [hσ1, Env.setVar, vA2]
    have c2 := cond_ltv (B := B) "o" "A2" σ1 _ _ ov vA21 (by omega) (by omega)
    have vdyo : d = 0 ∨ d = 1 := by omega
    by_cases ho2 : c - (3 + 2 * arr.getD 0 0) < 2 * arr.getD 1 0
    · have hT2 : (Cond.lt (V "o") (V "A2")).evalB B σ1 = some true := by
        rw [c2]; exact congrArg some (decide_eq_true ho2)
      have c3 := cond_eql (B := B) "dy" 0 σ1 d vdy1 (by omega) (by omega)
      by_cases hd0 : d = 0
      · have hT3 : (Cond.eq (V "dy") (.lit 0)).evalB B σ1 = some true := by rw [c3]; simp [hd0]
        have s5 := asg_binr (B := B) .div "o" 2 "h" σ1 (c - (3 + 2 * arr.getD 0 0)) ov
          (by simp only [Bop.apply_div]; omega) (by omega) (by omega)
        simp only [Bop.apply_div] at s5
        set σ5 := σ1.setVar "h" ((c - (3 + 2 * arr.getD 0 0)) / 2) with hσ5
        have hv5 : σ5.vars "h" = (c - (3 + 2 * arr.getD 0 0)) / 2 := by simp [hσ5, Env.setVar]
        have vK75 : σ5.vars "K7" = 7 + 2 * arr.getD 0 0 := by simp [hσ5, hσ1, Env.setVar, vK7]
        have l := asg_linv (B := B) "dv" "K7" 2 "h" σ5 _ _ vK75 hv5 (by omega) (by omega)
          (by omega) (by omega) (by omega)
        refine ⟨_, (s1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_true hT3
          (s5.seq l))))).mono (by simp [Cond.size, Expr.size]; omega), ?_,
          (st1.trans (Step.setVar σ1 "h" _ (by simp [AD]))).trans
            (Step.setVar σ5 "dv" _ (by simp [AD]))⟩
        rw [dueN_slotA arr d c h3 hv hd2 (by omega), if_pos hd0]
        simp [Env.setVar]; omega
      · have hF3 : (Cond.eq (V "dy") (.lit 0)).evalB B σ1 = some false := by
          rw [c3]; simp only [beq_eq_false_iff_ne.mpr hd0]
        have l := asg_lit (B := B) "dv" 2 σ1 (by omega)
        refine ⟨_, (s1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_false hF3 l)))).mono
          (by simp [Cond.size, Expr.size]; omega), ?_,
          st1.trans (Step.setVar σ1 "dv" _ (by simp [AD]))⟩
        rw [dueN_slotA arr d c h3 hv hd2 (by omega), if_neg hd0]
        simp [Env.setVar]
    · have hF2 : (Cond.lt (V "o") (V "A2")).evalB B σ1 = some false := by
        rw [c2]; exact congrArg some (decide_eq_false ho2)
      have s5 := asg_bin (B := B) .sub "o" "A2" "t3" σ1 (c - (3 + 2 * arr.getD 0 0))
        (2 * arr.getD 1 0) ov vA21 (by simp only [Bop.apply_sub]; omega) (by omega) (by omega)
      simp only [Bop.apply_sub] at s5
      set σ5 := σ1.setVar "t3" (c - (3 + 2 * arr.getD 0 0) - 2 * arr.getD 1 0) with hσ5
      have t5 : σ5.vars "t3" = c - (3 + 2 * arr.getD 0 0) - 2 * arr.getD 1 0 := by
        simp [hσ5, Env.setVar]
      have s6 := asg_binr (B := B) .div "t3" 3 "p" σ5 _ t5 (by simp only [Bop.apply_div]; omega)
        (by omega) (by omega)
      simp only [Bop.apply_div] at s6
      set σ6 := σ5.setVar "p" ((c - (3 + 2 * arr.getD 0 0) - 2 * arr.getD 1 0) / 3) with hσ6
      have p6 : σ6.vars "p" = (c - (3 + 2 * arr.getD 0 0) - 2 * arr.getD 1 0) / 3 := by
        simp [hσ6, Env.setVar]
      have vdy6 : σ6.vars "dy" = d := by simp [hσ6, hσ5, hσ1, Env.setVar, vdy]
      have vK96 : σ6.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0 := by
        simp [hσ6, hσ5, hσ1, Env.setVar, vK9]
      have st6 : Step σ σ6 := (st1.trans (Step.setVar σ1 "t3" _ (by simp [AD]))).trans
        (Step.setVar σ5 "p" _ (by simp [AD]))
      have c3 := cond_eql (B := B) "dy" 0 σ6 d vdy6 (by omega) (by omega)
      by_cases hd0 : d = 0
      · have hT3 : (Cond.eq (V "dy") (.lit 0)).evalB B σ6 = some true := by rw [c3]; simp [hd0]
        have l := asg_linv (B := B) "dv" "K9" 2 "p" σ6 _ _ vK96 p6 (by omega) (by omega)
          (by omega) (by omega) (by omega)
        refine ⟨_, (s1.seq (Run.ite_false hF (Run.ite_false hF2 (s5.seq (s6.seq
          (Run.ite_true hT3 l)))))).mono (by simp [Cond.size, Expr.size]; omega), ?_,
          st6.trans (Step.setVar σ6 "dv" _ (by simp [AD]))⟩
        rw [dueN_slotB arr d c h3 hv hd2 (by omega), if_pos hd0]
        simp [Env.setVar]; omega
      · have hF3 : (Cond.eq (V "dy") (.lit 0)).evalB B σ6 = some false := by
          rw [c3]; simp only [beq_eq_false_iff_ne.mpr hd0]
        have l := asg_linl (B := B) "dv" 6 3 "p" σ6 _ p6 (by omega) (by omega) (by omega)
          (by omega) (by omega)
        refine ⟨_, (s1.seq (Run.ite_false hF (Run.ite_false hF2 (s5.seq (s6.seq
          (Run.ite_false hF3 l)))))).mono (by simp [Cond.size, Expr.size]; omega), ?_,
          st6.trans (Step.setVar σ6 "dv" _ (by simp [AD]))⟩
        rw [dueN_slotB arr d c h3 hv hd2 (by omega), if_neg hd0]
        simp [Env.setVar]; omega

/-- **The due date of a client on a day.** -/
theorem dueCom_run (arr : List ℕ) (S c d : ℕ) (σ : Env) (hx : DCtx arr c d σ) (hd : d < 3)
    (hcl : c < 3 + 2 * arr.getD 0 0 + S) (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S)
    (hpass : ∀ k < S, PassS arr k) (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B dueCom σ σ' (110 + 64 * S) ∧ σ'.vars "dv" = dueN arr d c ∧ Step σ σ' := by
  have hx' := hx
  obtain ⟨hA, vi, vdy, vV3, vA2, vK7, vK9⟩ := hx
  have c1 := cond_ltl (B := B) "i" 3 σ c vi (by omega) (by omega)
  by_cases h3 : c < 3
  · have hT : (Cond.lt (V "i") (.lit 3)).evalB B σ = some true := by
      rw [c1]; exact congrArg some (decide_eq_true h3)
    have l := asg_lit (B := B) "dv" 2 σ (by omega)
    refine ⟨_, (Run.ite_true hT l).mono (by simp [Cond.size, Expr.size]; omega), ?_,
      Step.setVar σ "dv" _ (by simp [AD])⟩
    rw [dueN_lt3 arr d c h3]; simp [Env.setVar]
  · have hF : (Cond.lt (V "i") (.lit 3)).evalB B σ = some false := by
      rw [c1]; exact congrArg some (decide_eq_false h3)
    have c2 := cond_ltv (B := B) "i" "V3" σ c _ vi vV3 (by omega) (by omega)
    by_cases hv : c < 3 + 2 * arr.getD 0 0
    · have hT : (Cond.lt (V "i") (V "V3")).evalB B σ = some true := by
        rw [c2]; exact congrArg some (decide_eq_true hv)
      obtain ⟨σ', r, e, st⟩ := varCom_run (B := B) arr S c d σ hx' hd h3 hv hn hB
      exact ⟨σ', (Run.ite_false hF (Run.ite_true hT r)).mono (by
        simp [Cond.size, Expr.size]; omega), e, st⟩
    · have hF2 : (Cond.lt (V "i") (V "V3")).evalB B σ = some false := by
        rw [c2]; exact congrArg some (decide_eq_false hv)
      obtain ⟨σ', r, e, st⟩ := slotCom_run (B := B) arr S c d σ hx' hd h3 hv hcl hn hna hpass hlen
        hEv hEs hB
      exact ⟨σ', (Run.ite_false hF (Run.ite_false hF2 r)).mono (by
        simp [Cond.size, Expr.size]; omega), e, st⟩

end Lax117284Proofs.Machine.SatDue

end

/-! ### `Lax117284Proofs.Machine.SatPrint` -/

section
/-!
Writing the image of Theorem 7: the number of clients, the number of days, the processing time and
the due date of every job day by day, and the parameter `1`.
-/

namespace Lax117284Proofs.Machine.SatPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatDue
open Lax117284Proofs.Machine.SatFormat (SlotsN)

variable {B : ℕ}

/-- **A due date is small.** -/
lemma dueN_le (arr : List ℕ) (S c d : ℕ) (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S)
    (hpass : ∀ k < S, PassS arr k) (hcl : c < 3 + 2 * arr.getD 0 0 + S) :
    dueN arr d c ≤ 12 * S + 12 := by
  unfold dueN
  by_cases h1 : c < 3
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : c < 3 + 2 * arr.getD 0 0
    · rw [if_pos h2]
      split_ifs <;> omega
    · rw [if_neg h2]
      have hp := hpass (c - 3 - 2 * arr.getD 0 0) (by omega)
      obtain ⟨hp1, hp2⟩ := hp
      split_ifs <;> omega

/-- The cell of the image: the processing time and the due date. -/
def cellBody : Com :=
  .seq dueCom (.seq (emitLit 2) (emitVar "dv"))

/-- The scalars a cell assigns. -/
def SC : List String := "i" :: (AD ++ SCR)

/-- The cost of a cell. -/
def Kcell (Sz S : ℕ) : ℕ := 110 + 64 * S + 2 * (48 * Sz + 50) + 10

/-- **A cell of the image.** -/
theorem cellBody_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3)
    (hAg : Agr SC σ0 σ) (hA : σ0.arrs "TK" = arr)
    (hdy : σ0.vars "dy" = d) (vV3 : σ0.vars "V3" = 3 + 2 * arr.getD 0 0)
    (vA2 : σ0.vars "A2" = 2 * arr.getD 1 0) (vK7 : σ0.vars "K7" = 7 + 2 * arr.getD 0 0)
    (vK9 : σ0.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0)
    (hlt : σ.vars "i" < 3 + 2 * arr.getD 0 0 + S) (hn : arr.getD 0 0 ≤ S)
    (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k) (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B cellBody σ σ' (Kcell Sz S) ∧
      σ'.out = σ.out ++ (bitsNat 2 ++ bitsNat (dueN arr d (σ.vars "i"))) ∧ Agr SC σ0 σ' ∧
      σ'.vars "i" = σ.vars "i" := by
  have fr : ∀ y, y ∉ SC → σ.vars y = σ0.vars y := hAg.2
  have hx : DCtx arr (σ.vars "i") d σ :=
    ⟨by rw [hAg.1]; exact hA, rfl, by rw [fr "dy" (by decide)]; exact hdy,
      by rw [fr "V3" (by decide)]; exact vV3, by rw [fr "A2" (by decide)]; exact vA2,
      by rw [fr "K7" (by decide)]; exact vK7, by rw [fr "K9" (by decide)]; exact vK9⟩
  obtain ⟨σ1, r1, e1, st1⟩ := dueCom_run (B := B) arr S (σ.vars "i") d σ hx hd hlt hn hna hpass
    hlen hEv hEs hB
  have hle := dueN_le arr S (σ.vars "i") d hn hna hpass hlt
  have hv1 : σ1.vars "dv" + 4 < B := by rw [e1]; omega
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 2 Sz (by omega) (hs _ (by omega))) σ1 trivial
  have hv2 : σ2.vars "dv" = σ1.vars "dv" := v2 "dv" (by decide)
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitVar_spec (B := B) "dv" Sz σ2
    ⟨by rw [hv2]; exact hv1, by rw [hv2]; exact hs _ hv1⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold Kcell; omega), ?_, ⟨?_, fun y hy => ?_⟩, ?_⟩
  · rw [o3, o2, hv2, e1, st1.2.1]
    simp [List.append_assoc]
  · rw [a3, a2, st1.1]; exact hAg.1
  · have hyAD : y ∉ AD := fun h => hy (by simp [SC, h])
    have hyS : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SC, SCR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v3 y hyS, v2 y hyS, st1.2.2 y hyAD, hAg.2 y hy]
  · have hyAD : "i" ∉ AD := by decide
    rw [v3 "i" (by decide), v2 "i" (by decide), st1.2.2 "i" hyAD]

/-- **The cells of a day.** -/
theorem dayLoop_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3) (hA : σ0.arrs "TK" = arr)
    (hdy : σ0.vars "dy" = d) (vV3 : σ0.vars "V3" = 3 + 2 * arr.getD 0 0)
    (vA2 : σ0.vars "A2" = 2 * arr.getD 1 0) (vK7 : σ0.vars "K7" = 7 + 2 * arr.getD 0 0)
    (vK9 : σ0.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0)
    (vC : σ0.vars "C" = 3 + 2 * arr.getD 0 0 + S) (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B (outLoop "C" cellBody) σ0 σ' ((Kcell Sz S + 10 + 4) * (3 + 2 * arr.getD 0 0 + S) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (3 + 2 * arr.getD 0 0 + S)).flatMap
        fun c => [2, dueN arr d c]) ∧ (∀ y ∉ SC, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C" cellBody SC
    (fun c => bitsNat 2 ++ bitsNat (dueN arr d c)) (Kcell Sz S) (3 + 2 * arr.getD 0 0 + S) σ0
    (by simp [SC]) (by decide) vC hCB (by
      intro σ hAg hlt
      exact cellBody_run (B := B) Sz arr S d σ0 σ hs hd hAg hA hdy vV3 vA2 vK7 vK9 hlt hn hna hpass
        hlen hEv hEs hB)
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o]
  congr 1
  simp only [numBits, List.flatMap_assoc]
  refine List.flatMap_congr fun t _ => ?_
  simp [numBits]

/-- The day is set and the cells of the day are written. -/
def dayC (d : ℕ) : Com := .seq (.assign "dy" (.lit d)) (outLoop "C" cellBody)

/-- Write the whole image. -/
def printSat : Com :=
  .seq (emitVar "C") (.seq (emitLit 3) (.seq (dayC 0) (.seq (dayC 1) (.seq (dayC 2) (emitLit 1)))))

/-- The cost of writing the image. -/
def KprintS (Sz S N : ℕ) : ℕ := 3 * (48 * Sz + 50) + 3 * ((Kcell Sz S + 10 + 4) * N + 6 + 10)

/-- The scalars the image is written from. -/
structure PCtx (arr : List ℕ) (S : ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = arr
  vV3 : σ.vars "V3" = 3 + 2 * arr.getD 0 0
  vA2 : σ.vars "A2" = 2 * arr.getD 1 0
  vK7 : σ.vars "K7" = 7 + 2 * arr.getD 0 0
  vK9 : σ.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0
  vC : σ.vars "C" = 3 + 2 * arr.getD 0 0 + S

lemma PCtx.of_frame {arr : List ℕ} {S : ℕ} {σ σ' : Env} (h : PCtx arr S σ)
    (ha : σ'.arrs = σ.arrs) (hf : ∀ y ∉ SC, σ'.vars y = σ.vars y) : PCtx arr S σ' :=
  ⟨by rw [ha]; exact h.hA, by rw [hf "V3" (by decide)]; exact h.vV3,
    by rw [hf "A2" (by decide)]; exact h.vA2, by rw [hf "K7" (by decide)]; exact h.vK7,
    by rw [hf "K9" (by decide)]; exact h.vK9, by rw [hf "C" (by decide)]; exact h.vC⟩

lemma PCtx.of_emit {arr : List ℕ} {S : ℕ} {σ σ' : Env} (h : PCtx arr S σ)
    (ha : σ'.arrs = σ.arrs) (hf : ∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) :
    PCtx arr S σ' :=
  h.of_frame ha (fun y hy => hf y (fun h' => hy (by
    simp only [SC, SCR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h' ⊢
    tauto)))

lemma PCtx.setDy {arr : List ℕ} {S : ℕ} {σ : Env} (h : PCtx arr S σ) (d : ℕ) :
    PCtx arr S (σ.setVar "dy" d) :=
  ⟨by simp [Env.setVar, h.hA], by simp [Env.setVar, h.vV3], by simp [Env.setVar, h.vA2],
    by simp [Env.setVar, h.vK7], by simp [Env.setVar, h.vK9], by simp [Env.setVar, h.vC]⟩

/-- **One day: set it, and write its cells.** -/
theorem dayC_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3) (hctx : PCtx arr S σ)
    (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B (dayC d) σ σ' ((Kcell Sz S + 10 + 4) * (3 + 2 * arr.getD 0 0 + S) + 6 + 10) ∧
      σ'.out = σ.out ++ numBits ((List.range (3 + 2 * arr.getD 0 0 + S)).flatMap
        fun c => [2, dueN arr d c]) ∧ PCtx arr S σ' := by
  have s0 := asg_lit (B := B) "dy" d σ (by omega)
  have h1 : PCtx arr S (σ.setVar "dy" d) := hctx.setDy d
  obtain ⟨σ', r, o, hf, ha⟩ := dayLoop_run (B := B) Sz arr S d (σ.setVar "dy" d) hs hd h1.hA
    (by simp [Env.setVar]) h1.vV3 h1.vA2 h1.vK7 h1.vK9 h1.vC hCB hn hna hpass hlen hEv hEs hB
  refine ⟨σ', (s0.seq r).mono (by omega), ?_, h1.of_frame ha hf⟩
  rw [o]; simp [Env.setVar]

/-- **Writing the image.** -/
theorem printSat_run (Sz : ℕ) (arr : List ℕ) (S : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hctx : PCtx arr S σ) (hS : SlotsN arr = S)
    (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B printSat σ σ' (KprintS Sz S (3 + 2 * arr.getD 0 0 + S)) ∧
      σ'.out = σ.out ++ numBits (outNums arr) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "C" Sz σ
    ⟨by rw [hctx.vC]; omega, by rw [hctx.vC]; exact hs _ (by omega)⟩
  have h1 : PCtx arr S σ1 := hctx.of_emit a1 v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 3 Sz (by omega) (hs _ (by omega))) σ1 trivial
  have h2 : PCtx arr S σ2 := h1.of_emit a2 v2
  obtain ⟨σ3, r3, o3, h3⟩ := dayC_run (B := B) Sz arr S 0 σ2 hs (by omega) h2 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ4, r4, o4, h4⟩ := dayC_run (B := B) Sz arr S 1 σ3 hs (by omega) h3 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ5, r5, o5, h5⟩ := dayC_run (B := B) Sz arr S 2 σ4 hs (by omega) h4 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ6, r6, o6, v6, a6⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ5 trivial
  refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by unfold KprintS; omega), ?_⟩
  rw [o6, o5, o4, o3, o2, o1, hctx.vC]
  unfold outNums clientsN
  have hSN : SlotsN arr = S := hS
  rw [hSN]
  have hr : (List.range 3).flatMap (fun i => (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap fun c =>
      [2, dueN arr i c]) =
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 0 c]) ++
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 1 c]) ++
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 2 c]) := by
    simp [List.range_succ]
  rw [hr]
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

end Lax117284Proofs.Machine.SatPrint

end

/-! ### `Lax117284Proofs.Machine.SatAccept` -/

section
/-!
The whole of the reduction of Theorem 7 after the tokenizer has accepted: read the counts off the
array, check the positions, and write either the image or the rejected word.
-/

namespace Lax117284Proofs.Machine.SatAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank
open Lax117284Proofs.Machine.SatCheck Lax117284Proofs.Machine.SatDue Lax117284Proofs.Machine.SatPrint
open Lax117284Proofs.Machine.FreeAccept
open Lax117284Proofs.Machine.SatFormat (SlotsN)

variable {B : ℕ}

/-- Read the counts off the array and derive the scalars the rest reads. -/
def prepSat : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "na" (.get "TK" (.lit 1)))
  (.seq (.assign "nb" (.get "TK" (.lit 2)))
  (.seq (.assign "A2" (.bin .mul (V "na") (.lit 2)))
  (.seq (.assign "t3" (.bin .mul (V "nb") (.lit 3)))
  (.seq (.assign "N" (.bin .add (V "A2") (V "t3")))
  (.seq (.assign "V3" (add (.lit 3) (mul (.lit 2) (V "n"))))
  (.seq (.assign "C" (.bin .add (V "V3") (V "N")))
  (.seq (.assign "K7" (add (.lit 7) (mul (.lit 2) (V "n"))))
  (.seq (.assign "K9" (add (.lit 9) (mul (.lit 2) (V "n"))))
  (.seq (.assign "K9" (.bin .add (V "K9") (V "A2")))
    (.ite (.lt (V "N") (V "n")) (.assign "ok" (.lit 0)) (.assign "ok" (.lit 1)))))))))))))

/-- The scalars the preparation assigns. -/
def AP : List String := ["n", "na", "nb", "A2", "t3", "N", "V3", "C", "K7", "K9", "ok"]

set_option maxHeartbeats 6400000 in
theorem prepSat_run (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr) (h3 : 3 ≤ arr.length)
    (hE : ∀ k < 3, arr.getD k 0 + 8 < B)
    (hb : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B) :
    ∃ σ', Run B prepSat σ σ' 120 ∧ σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "N" = SlotsN arr ∧
      σ'.vars "V3" = 3 + 2 * arr.getD 0 0 ∧ σ'.vars "A2" = 2 * arr.getD 1 0 ∧
      σ'.vars "K7" = 7 + 2 * arr.getD 0 0 ∧
      σ'.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0 ∧
      σ'.vars "C" = 3 + 2 * arr.getD 0 0 + SlotsN arr ∧
      σ'.vars "ok" = (if SlotsN arr < arr.getD 0 0 then 0 else 1) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ AP → σ'.vars y = σ.vars y := by
  have e0 := hE 0 (by omega)
  have e1 := hE 1 (by omega)
  have e2 := hE 2 (by omega)
  have s0 := asg_tkl (B := B) "n" 0 σ arr hA (by omega) (by omega) (by omega)
  set σ0 := σ.setVar "n" (arr.getD 0 0) with h0
  have A0 : σ0.arrs "TK" = arr := by simp [h0, Env.setVar, hA]
  have s1 := asg_tkl (B := B) "na" 1 σ0 arr A0 (by omega) (by omega) (by omega)
  set σ1 := σ0.setVar "na" (arr.getD 1 0) with h1
  have A1 : σ1.arrs "TK" = arr := by simp [h1, h0, Env.setVar, hA]
  have s2 := asg_tkl (B := B) "nb" 2 σ1 arr A1 (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "nb" (arr.getD 2 0) with h2
  have vna : σ2.vars "na" = arr.getD 1 0 := by simp [h2, h1, Env.setVar]
  have vnb : σ2.vars "nb" = arr.getD 2 0 := by simp [h2, Env.setVar]
  have vn2 : σ2.vars "n" = arr.getD 0 0 := by simp [h2, h1, h0, Env.setVar]
  have s3 := asg_binr (B := B) .mul "na" 2 "A2" σ2 (arr.getD 1 0) vna
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s3
  set σ3 := σ2.setVar "A2" (arr.getD 1 0 * 2) with h3'
  have vnb3 : σ3.vars "nb" = arr.getD 2 0 := by simp [h3', Env.setVar, vnb]
  have s4 := asg_binr (B := B) .mul "nb" 3 "t3" σ3 (arr.getD 2 0) vnb3
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s4
  set σ4 := σ3.setVar "t3" (arr.getD 2 0 * 3) with h4
  have vA24 : σ4.vars "A2" = arr.getD 1 0 * 2 := by simp [h4, h3', Env.setVar]
  have vt4 : σ4.vars "t3" = arr.getD 2 0 * 3 := by simp [h4, Env.setVar]
  have s5 := asg_bin (B := B) .add "A2" "t3" "N" σ4 (arr.getD 1 0 * 2) (arr.getD 2 0 * 3) vA24 vt4
    (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
  simp only [Bop.apply_add] at s5
  set σ5 := σ4.setVar "N" (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) with h5
  have vn5 : σ5.vars "n" = arr.getD 0 0 := by simp [h5, h4, h3', Env.setVar, vn2]
  have s6 := asg_linl (B := B) "V3" 3 2 "n" σ5 (arr.getD 0 0) vn5 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ6 := σ5.setVar "V3" (3 + 2 * arr.getD 0 0) with h6
  have vV6 : σ6.vars "V3" = 3 + 2 * arr.getD 0 0 := by simp [h6, Env.setVar]
  have vN6 : σ6.vars "N" = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by
    simp [h6, h5, Env.setVar]
  have s7 := asg_bin (B := B) .add "V3" "N" "C" σ6 (3 + 2 * arr.getD 0 0)
    (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) vV6 vN6 (by simp only [Bop.apply_add]; omega)
    (by omega) (by omega)
  simp only [Bop.apply_add] at s7
  set σ7 := σ6.setVar "C" (3 + 2 * arr.getD 0 0 + (arr.getD 1 0 * 2 + arr.getD 2 0 * 3)) with h7
  have vn7 : σ7.vars "n" = arr.getD 0 0 := by simp [h7, h6, h5, h4, h3', Env.setVar, vn2]
  have s8 := asg_linl (B := B) "K7" 7 2 "n" σ7 (arr.getD 0 0) vn7 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ8 := σ7.setVar "K7" (7 + 2 * arr.getD 0 0) with h8
  have vn8 : σ8.vars "n" = arr.getD 0 0 := by simp [h8, h7, h6, h5, h4, h3', Env.setVar, vn2]
  have s9 := asg_linl (B := B) "K9" 9 2 "n" σ8 (arr.getD 0 0) vn8 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  set σ9 := σ8.setVar "K9" (9 + 2 * arr.getD 0 0) with h9
  have vK9 : σ9.vars "K9" = 9 + 2 * arr.getD 0 0 := by simp [h9, Env.setVar]
  have vA29 : σ9.vars "A2" = arr.getD 1 0 * 2 := by
    simp [h9, h8, h7, h6, h5, h4, h3', Env.setVar]
  have s10 := asg_bin (B := B) .add "K9" "A2" "K9" σ9 (9 + 2 * arr.getD 0 0) (arr.getD 1 0 * 2)
    vK9 vA29 (by simp only [Bop.apply_add]; omega) (by omega) (by omega)
  simp only [Bop.apply_add] at s10
  set σ10 := σ9.setVar "K9" (9 + 2 * arr.getD 0 0 + arr.getD 1 0 * 2) with h10
  have vN10 : σ10.vars "N" = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by
    simp [h10, h9, h8, h7, h6, h5, Env.setVar]
  have vn10 : σ10.vars "n" = arr.getD 0 0 := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3', Env.setVar, vn2]
  have c := cond_ltv (B := B) "N" "n" σ10 _ _ vN10 vn10 (by omega) (by omega)
  have hA10 : σ10.arrs = σ.arrs := by simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar]
  have hO10 : σ10.out = σ.out := by simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar]
  have hSN : SlotsN arr = arr.getD 1 0 * 2 + arr.getD 2 0 * 3 := by unfold SlotsN; omega
  have hfr : ∀ y, y ∉ AP → ∀ z ∈ AP, y ≠ z := fun y hy z hz h => hy (h ▸ hz)
  have hframe10 : ∀ y, y ∉ AP → σ10.vars y = σ.vars y := by
    intro y hy
    have g : ∀ z, z ∈ AP → y ≠ z := hfr y hy
    simp [h10, h9, h8, h7, h6, h5, h4, h3', h2, h1, h0, Env.setVar, g "n" (by simp [AP]),
      g "na" (by simp [AP]), g "nb" (by simp [AP]), g "A2" (by simp [AP]), g "t3" (by simp [AP]),
      g "N" (by simp [AP]), g "V3" (by simp [AP]), g "C" (by simp [AP]), g "K7" (by simp [AP]),
      g "K9" (by simp [AP])]
  have fV3 : σ10.vars "V3" = 3 + 2 * arr.getD 0 0 := by
    simp [h10, h9, h8, h7, h6, Env.setVar]
  have fA2 : σ10.vars "A2" = arr.getD 1 0 * 2 := by
    simp [h10, h9, h8, h7, h6, h5, h4, h3', Env.setVar]
  have fK7 : σ10.vars "K7" = 7 + 2 * arr.getD 0 0 := by simp [h10, h9, h8, Env.setVar]
  have fK9 : σ10.vars "K9" = 9 + 2 * arr.getD 0 0 + arr.getD 1 0 * 2 := by
    simp [h10, Env.setVar]
  have fC : σ10.vars "C" = 3 + 2 * arr.getD 0 0 + (arr.getD 1 0 * 2 + arr.getD 2 0 * 3) := by
    simp [h10, h9, h8, h7, Env.setVar]
  have hfin : ∀ (v : ℕ), (σ10.setVar "ok" v).vars "n" = arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "N" = SlotsN arr ∧
      (σ10.setVar "ok" v).vars "V3" = 3 + 2 * arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "A2" = 2 * arr.getD 1 0 ∧
      (σ10.setVar "ok" v).vars "K7" = 7 + 2 * arr.getD 0 0 ∧
      (σ10.setVar "ok" v).vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0 ∧
      (σ10.setVar "ok" v).vars "C" = 3 + 2 * arr.getD 0 0 + SlotsN arr ∧
      (σ10.setVar "ok" v).arrs = σ.arrs ∧ (σ10.setVar "ok" v).out = σ.out ∧
      ∀ y, y ∉ AP → (σ10.setVar "ok" v).vars y = σ.vars y := by
    intro v
    refine ⟨by simp [Env.setVar, vn10], by simp [Env.setVar, vN10, hSN],
      by simp [Env.setVar, fV3], by simp [Env.setVar, fA2]; omega, by simp [Env.setVar, fK7],
      by simp [Env.setVar, fK9]; omega, by simp [Env.setVar, fC, hSN], by simp [Env.setVar, hA10],
      by simp [Env.setVar, hO10], fun y hy => ?_⟩
    have hyo : y ≠ "ok" := fun h => hy (by simp [AP, h])
    simp only [Env.setVar, if_neg hyo]
    exact hframe10 y hy
  by_cases hlt : arr.getD 1 0 * 2 + arr.getD 2 0 * 3 < arr.getD 0 0
  · have hT : (Cond.lt (V "N") (V "n")).evalB B σ10 = some true := by
      rw [c]; exact congrArg some (decide_eq_true hlt)
    have l := asg_lit (B := B) "ok" 0 σ10 (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hfin 0
    exact ⟨_, (s0.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
      (s10.seq (Run.ite_true hT l)))))))))))).mono (by simp [Cond.size, Expr.size]),
      g1, g2, g3, g4, g5, g6, g7, by simp only [Env.setVar, if_true]; rw [hSN, if_pos hlt], g8, g9, g10⟩
  · have hF : (Cond.lt (V "N") (V "n")).evalB B σ10 = some false := by
      rw [c]; exact congrArg some (decide_eq_false hlt)
    have l := asg_lit (B := B) "ok" 1 σ10 (by omega)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hfin 1
    exact ⟨_, (s0.seq (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq
      (s10.seq (Run.ite_false hF l)))))))))))).mono (by simp [Cond.size, Expr.size]),
      g1, g2, g3, g4, g5, g6, g7, by simp only [Env.setVar, if_true]; rw [hSN, if_neg hlt], g8, g9, g10⟩

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptSat : Com :=
  .seq prepSat (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printSat rejectPrint))

/-- The cost of the accepting phase, on an input of `l` tokens. -/
def KaccS (Sz l : ℕ) : ℕ :=
  200 + ((120 + 64 * l + 4) * l + 6) + KprintS Sz l (3 + 3 * l) + 3 * (48 * Sz + 50)

lemma KprintS_mono (Sz a b N N' : ℕ) (h : a ≤ b) (h' : N ≤ N') :
    KprintS Sz a N ≤ KprintS Sz b N' := by
  unfold KprintS Kcell
  have h1 : (110 + 64 * a + 2 * (48 * Sz + 50) + 10 + 10 + 4) * N ≤
      (110 + 64 * b + 2 * (48 * Sz + 50) + 10 + 10 + 4) * N' :=
    Nat.mul_le_mul (by omega) h'
  omega

lemma KaccS_mono (Sz a b : ℕ) (h : a ≤ b) : KaccS Sz a ≤ KaccS Sz b := by
  unfold KaccS
  have h1 : (120 + 64 * a + 4) * a ≤ (120 + 64 * b + 4) * b := Nat.mul_le_mul (by omega) h
  have h2 := KprintS_mono Sz a b (3 + 3 * a) (3 + 3 * b) h (by omega)
  omega

open Classical in
set_option maxHeartbeats 3200000 in
theorem acceptSat_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hlen : 3 + 2 * SlotsN arr ≤ arr.length)
    (hE : ∀ k < 3 + 2 * SlotsN arr, arr.getD k 0 + 8 < B) (hl : SlotsN arr ≤ l)
    (hB : 60 * (SlotsN arr + 4) < B)
    (hb : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B) :
    ∃ σ', Run B acceptSat σ σ' (KaccS Sz l) ∧
      σ'.out = σ.out ++ (if CondN arr then numBits (outNums arr) else numBits [1, 0, 1]) := by
  obtain ⟨S, hSdef⟩ : ∃ S, SlotsN arr = S := ⟨_, rfl⟩
  rw [hSdef] at hlen hE hl hB
  have hB2 : 6 < B := by omega
  obtain ⟨σ1, r1, e1n, e1N, e1V3, e1A2, e1K7, e1K9, e1C, e1ok, e1a, e1o, e1f⟩ :=
    prepSat_run (B := B) arr σ hA (by omega) (fun k hk => hE k (by omega)) hb
  rw [hSdef] at e1N e1C e1ok
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hok0 : (if S < arr.getD 0 0 then 0 else 1) ≤ 1 := by split <;> omega
  have hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B := fun k hk => hE _ (by omega)
  have hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B := fun k hk => hE _ (by omega)
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_spec (B := B) arr S (arr.getD 0 0)
    (if S < arr.getD 0 0 then 0 else 1) σ1 rfl hEv hEs hlen (by omega)
    (hE 0 (by omega)) hok0 A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hcond : σ2.vars "ok" = 1 ↔ CondN arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondN
    rw [hSdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h
      have : S < arr.getD 0 0 := by omega
      rw [if_pos this] at h1
      exact absurd h1 (by decide)
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_neg (by omega)], h2⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassS arr) (if S < arr.getD 0 0 then 0 else 1) S; omega
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨hn, hpass⟩ : arr.getD 0 0 ≤ S ∧ ∀ k < S, PassS arr k := by
      have := hc; unfold CondN at this; rw [hSdef] at this; exact this
    have hctx : PCtx arr S σ2 :=
      ⟨A2, by rw [e2f "V3" (by decide)]; exact e1V3, by rw [e2f "A2" (by decide)]; exact e1A2,
        by rw [e2f "K7" (by decide)]; exact e1K7, by rw [e2f "K9" (by decide)]; exact e1K9,
        by rw [e2f "C" (by decide)]; exact e1C⟩
    obtain ⟨σ3, r3, o3⟩ := printSat_run (B := B) Sz arr S σ2 hs hctx hSdef (by omega) hn
      (by have := hSdef; unfold SlotsN at this; omega) hpass hlen hEv hEs hB
    have hK := KprintS_mono Sz S l (3 + 2 * arr.getD 0 0 + S) (3 + 3 * l) hl (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccS
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_pos hc]
  · have hno : ¬ CondN arr := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, e3o, e3a, e3f⟩ := rejectPrint_run (B := B) Sz σ2 hs hB2
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccS
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [e3o, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.SatAccept

end
