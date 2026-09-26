import Lax117284Proofs.Machine.SatCheck

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
