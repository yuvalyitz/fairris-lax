import Lax117284Proofs.Machine.FoldLoop
import Lax117284Proofs.Machine.T9Ops
import Lax117284Proofs.Machine.MisBlk
import Lax117284Proofs.Machine.SatRank
import Lax117284Proofs.Machine.X3Sem
import Lax117284Proofs.X3Word

/-!
The loops of the algorithm for day-independent due dates and processing times: the count of the jobs
of the first day that run at the instant one of them starts, the running maximum of the counts, and
the check that every day has the table of the first.
-/

namespace Lax117284Proofs.Machine.X3Loop

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.X3Sem
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)
open Lax117284Proofs.Machine.SatRank (bumpS)
open Lax117284Proofs.Machine.SatOps (asg_addl)

variable {B : ℕ}

/-- The entry of the token array at `2 + 2 x + o`. -/
abbrev rd (x : String) (o : ℕ) : Expr := .get "TK" (add (add (.lit 2) (mul (.lit 2) (V x))) (.lit o))

/-- The job of client `j` runs at the instant `si`. -/
def runs (arr : List ℕ) (si j : ℕ) : Bool :=
  decide (sRow arr j ≤ si ∧ si < arr.getD (3 + 2 * j) 0)

lemma cntN_eq (arr : List ℕ) (i : ℕ) :
    cntN arr i = (List.range (arr.getD 0 0)).countP (runs arr (sRow arr i)) := rfl

/-- The body of the count: the job of client `j`. -/
def innerBody : Com :=
  .seq (.assign "pb" (rd "j" 0))
  (.seq (.assign "db" (rd "j" 1))
  (.seq (.assign "x2" (sub (V "db") (V "pb")))
    (.ite (.lt (V "x1") (V "x2")) .skip
      (.ite (.lt (V "x1") (V "db")) (bumpS "cj") .skip))))

set_option maxHeartbeats 3200000 in
/-- **One job of the count.** -/
theorem innerBody_run (arr : List ℕ) (n j si : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hj : σ.vars "j" = j) (hjn : j < n) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hx1 : σ.vars "x1" = si) (hsi : si + 8 < B)
    (hcj : σ.vars "cj" + 8 < B) (hnB : 2 * n + 8 < B) :
    ∃ σ', Run B innerBody σ σ' 100 ∧
      σ'.vars "cj" = σ.vars "cj" + (if runs arr si j then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "pb" → y ≠ "db" → y ≠ "x2" → y ≠ "cj" → σ'.vars y = σ.vars y := by
  have e1 := hE (2 + 2 * j) (by omega)
  have e2 := hE (2 + 2 * j + 1) (by omega)
  have e0 : arr.getD (2 + 2 * j + 0) 0 = arr.getD (2 + 2 * j) 0 := rfl
  have s1 := asg_tk (B := B) "j" "pb" 0 σ arr j hA hj (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "pb" (arr.getD (2 + 2 * j + 0) 0) with hσ1
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hj]
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have s2 := asg_tk (B := B) "j" "db" 1 σ1 arr j hA1 hj1 (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "db" (arr.getD (2 + 2 * j + 1) 0) with hσ2
  have hpb2 : σ2.vars "pb" = arr.getD (2 + 2 * j) 0 := by simp [hσ2, hσ1, Env.setVar]
  have hdb2 : σ2.vars "db" = arr.getD (2 + 2 * j + 1) 0 := by simp [hσ2, Env.setVar]
  have s3 := asgE (B := B) "x2" (sub (V "db") (V "pb")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, hpb2, hdb2]
    omega)
  set σ3 := σ2.setVar "x2" (MisBlk.den σ2 (sub (V "db") (V "pb"))) with hσ3
  have hx23 : σ3.vars "x2" = arr.getD (2 + 2 * j + 1) 0 - arr.getD (2 + 2 * j) 0 := by
    simp [hσ3, MisBlk.den, Env.setVar, hpb2, hdb2, Bop.apply_sub]
  have hx13 : σ3.vars "x1" = si := by simp [hσ3, hσ2, hσ1, Env.setVar, hx1]
  have hdb3 : σ3.vars "db" = arr.getD (2 + 2 * j + 1) 0 := by simp [hσ3, Env.setVar, hdb2]
  have hcj3 : σ3.vars "cj" = σ.vars "cj" := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have hs1 : MisBlk.small B σ3 (V "x1") := by
    show σ3.vars "x1" < B; rw [hx13]; omega
  have hs2 : MisBlk.small B σ3 (V "x2") := by
    show σ3.vars "x2" < B; rw [hx23]; omega
  have hsd : MisBlk.small B σ3 (V "db") := by
    show σ3.vars "db" < B; rw [hdb3]; omega
  have hfr3 : ∀ y, y ≠ "pb" → y ≠ "db" → y ≠ "x2" → σ3.vars y = σ.vars y := by
    intro y a b c
    simp [hσ3, hσ2, hσ1, Env.setVar, a, b, c]
  have hA3 : σ3.arrs = σ.arrs := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have hO3 : σ3.out = σ.out := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have e3 : arr.getD (3 + 2 * j) 0 = arr.getD (2 + 2 * j + 1) 0 := by
    rw [show 3 + 2 * j = 2 + 2 * j + 1 by omega]
  have hrun : runs arr si j = true ↔ ¬ (si < arr.getD (2 + 2 * j + 1) 0 - arr.getD (2 + 2 * j) 0) ∧
      si < arr.getD (2 + 2 * j + 1) 0 := by
    unfold runs sRow
    rw [e3]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have : arr.getD (2 + 2 * j + 1) 0 - arr.getD (2 + 2 * j) 0 ≤ si := by
        have h1' := h1
        rw [show 2 + 2 * j = 2 + 2 * j from rfl] at h1'
        omega
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      omega
  by_cases hlt : si < arr.getD (2 + 2 * j + 1) 0 - arr.getD (2 + 2 * j) 0
  · have hT : (Cond.lt (V "x1") (V "x2")).evalB B σ3 = some true :=
      condLt_true _ _ σ3 hs1 hs2 (by show σ3.vars "x1" < σ3.vars "x2"; rw [hx13, hx23]; exact hlt)
    have hr : runs arr si j = false := by
      by_contra h
      have := hrun.1 (by simpa using h)
      exact this.1 hlt
    refine ⟨σ3, (s1.seq (s2.seq (s3.seq (Run.ite_true hT Run.skip)))).mono (by
      simp [Cond.size, Expr.size]), ?_, hA3, hO3, fun y a b c d => ?_⟩
    · rw [hr, hcj3]; simp
    · rw [hfr3 y a b c]
  · have hF : (Cond.lt (V "x1") (V "x2")).evalB B σ3 = some false :=
      condLt_false _ _ σ3 hs1 hs2 (by show ¬ (σ3.vars "x1" < σ3.vars "x2"); rw [hx13, hx23]; exact hlt)
    by_cases hlt2 : si < arr.getD (2 + 2 * j + 1) 0
    · have hT2 : (Cond.lt (V "x1") (V "db")).evalB B σ3 = some true :=
        condLt_true _ _ σ3 hs1 hsd (by show σ3.vars "x1" < σ3.vars "db"; rw [hx13, hdb3]; exact hlt2)
      have hcjB : σ3.vars "cj" < B := by rw [hcj3]; omega
      have b := asg_addl (B := B) "cj" "cj" 1 σ3 (σ3.vars "cj") rfl hcjB (by omega) (by omega)
      have b' : Run B (bumpS "cj") σ3 (σ3.setVar "cj" (σ3.vars "cj" + 1)) 5 := b
      have hr : runs arr si j = true := hrun.2 ⟨hlt, hlt2⟩
      refine ⟨_, (s1.seq (s2.seq (s3.seq (Run.ite_false hF (Run.ite_true hT2 b'))))).mono (by
        simp [Cond.size, Expr.size]), ?_, ?_, ?_, fun y a b c d => ?_⟩
      · simp [Env.setVar, hcj3, hr]
      · simp [Env.setVar, hA3]
      · simp [Env.setVar, hO3]
      · simp only [Env.setVar, if_neg d]; exact hfr3 y a b c
    · have hF2 : (Cond.lt (V "x1") (V "db")).evalB B σ3 = some false :=
        condLt_false _ _ σ3 hs1 hsd (by show ¬ (σ3.vars "x1" < σ3.vars "db"); rw [hx13, hdb3]; exact hlt2)
      have hr : runs arr si j = false := by
        by_contra h
        have := hrun.1 (by simpa using h)
        exact hlt2 this.2
      refine ⟨σ3, (s1.seq (s2.seq (s3.seq (Run.ite_false hF (Run.ite_false hF2 Run.skip))))).mono (by
        simp [Cond.size, Expr.size]), ?_, hA3, hO3, fun y a b c d => ?_⟩
      · rw [hr, hcj3]; simp
      · rw [hfr3 y a b c]

lemma foldl_count (P : ℕ → Bool) (a k : ℕ) :
    (List.range k).foldl (fun a j => a + if P j = true then 1 else 0) a =
      a + (List.range k).countP P := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih, List.countP_append]
    simp only [List.foldl_cons, List.foldl_nil, List.countP_cons, List.countP_nil]
    split <;> omega

/-- The count of the jobs that run at the instant `x1`. -/
def cntCom : Com := .seq (.assign "cj" (.lit 0)) (fLoop "j" "n" innerBody)

/-- The scalars the count assigns. -/
def SIN : List String := ["j", "pb", "db", "x2", "cj"]

set_option maxHeartbeats 3200000 in
/-- **The count.** -/
theorem cntCom_run (arr : List ℕ) (n si : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hx1 : σ.vars "x1" = si) (hsi : si + 8 < B)
    (hnB : 2 * n + 8 < B) :
    ∃ σ', Run B cntCom σ σ' ((100 + 10 + 4) * n + 20) ∧
      σ'.vars "cj" = (List.range n).countP (runs arr si) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ SIN → σ'.vars y = σ.vars y := by
  have s0 := MisBlk.asgE (B := B) "cj" (.lit 0) σ (by simp [MisBlk.small]; omega)
  set σ0 := σ.setVar "cj" (MisBlk.den σ (.lit 0)) with hσ0
  have hc0 : σ0.vars "cj" = 0 := by simp [hσ0, MisBlk.den, Env.setVar]
  have hn0 : σ0.vars "n" = n := by simp [hσ0, Env.setVar, hn]
  obtain ⟨σ', r, hacc, hag, hout⟩ := fLoop_spec (B := B) "j" "n" "cj" innerBody SIN
    (fun j a => a + if runs arr si j = true then 1 else 0) (fun j a => a ≤ j) (100) n σ0
    (by simp [SIN]) (by simp [SIN]) (by decide) hn0 (by omega) (by rw [hc0])
    (fun j a ha => by split <;> omega) (by
      intro σ1 hAg hlt hq
      have hA1 : σ1.arrs "TK" = arr := by rw [hAg.1]; simp [hσ0, Env.setVar, hA]
      have hx1' : σ1.vars "x1" = si := by
        rw [hAg.2 "x1" (by simp [SIN])]; simp [hσ0, Env.setVar, hx1]
      obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := innerBody_run (B := B) arr n (σ1.vars "j") si σ1 hA1 rfl
        hlt hlen hE hx1' hsi (by omega) hnB
      refine ⟨σ2, r2, c2, ⟨by rw [a2, hAg.1], fun y hy => ?_⟩, f2 "j" (by decide) (by decide)
        (by decide) (by decide), o2⟩
      have h1 : y ≠ "pb" := fun h => hy (by simp [SIN, h])
      have h2 : y ≠ "db" := fun h => hy (by simp [SIN, h])
      have h3 : y ≠ "x2" := fun h => hy (by simp [SIN, h])
      have h4 : y ≠ "cj" := fun h => hy (by simp [SIN, h])
      rw [f2 y h1 h2 h3 h4, hAg.2 y hy])
  refine ⟨σ', (s0.seq r).mono (by simp [Expr.size]; omega), ?_, ?_, ?_, fun y hy => ?_⟩
  · rw [hacc, hc0, foldl_count, Nat.zero_add]
  · rw [hag.1]; simp [hσ0, Env.setVar]
  · rw [hout]; simp [hσ0, Env.setVar]
  · rw [hag.2 y hy]; simp only [hσ0, Env.setVar]
    have : y ≠ "cj" := fun h => hy (by simp [SIN, h])
    simp [this]

/-- The body of the running maximum: the count of the job of client `i`. -/
def outerBody : Com :=
  .seq (.assign "pa" (rd "i" 0))
  (.seq (.assign "da" (rd "i" 1))
  (.seq (.assign "x1" (sub (V "da") (V "pa")))
  (.seq cntCom
    (.ite (.lt (V "r2") (V "cj")) (.assign "r2" (V "cj")) .skip))))

/-- The scalars the running maximum assigns. -/
def SOUT : List String := ["pa", "da", "x1", "cj", "j", "pb", "db", "x2", "r2"]

lemma cntN_le (arr : List ℕ) (i : ℕ) : cntN arr i ≤ arr.getD 0 0 := by
  unfold cntN
  have := List.countP_le_length (p := fun j' => decide (sRow arr j' ≤ sRow arr i ∧
    sRow arr i < arr.getD (3 + 2 * j') 0)) (l := List.range (arr.getD 0 0))
  simpa using this

set_option maxHeartbeats 6400000 in
/-- **One job of the running maximum.** -/
theorem outerBody_run (arr : List ℕ) (n i : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = i) (hin : i < n) (hn : σ.vars "n" = n)
    (hn' : arr.getD 0 0 = n) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hnB : 2 * n + 8 < B)
    (hr2 : σ.vars "r2" ≤ n) :
    ∃ σ', Run B outerBody σ σ' ((100 + 10 + 4) * n + 100) ∧
      σ'.vars "r2" = max (σ.vars "r2") (cntN arr i) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ SOUT → σ'.vars y = σ.vars y := by
  have e1 := hE (2 + 2 * i) (by omega)
  have e2 := hE (2 + 2 * i + 1) (by omega)
  have e0 : arr.getD (2 + 2 * i + 0) 0 = arr.getD (2 + 2 * i) 0 := rfl
  have s1 := asg_tk (B := B) "i" "pa" 0 σ arr i hA hi (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "pa" (arr.getD (2 + 2 * i + 0) 0) with hσ1
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hi]
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have s2 := asg_tk (B := B) "i" "da" 1 σ1 arr i hA1 hi1 (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "da" (arr.getD (2 + 2 * i + 1) 0) with hσ2
  have hpa2 : σ2.vars "pa" = arr.getD (2 + 2 * i) 0 := by simp [hσ2, hσ1, Env.setVar]
  have hda2 : σ2.vars "da" = arr.getD (2 + 2 * i + 1) 0 := by simp [hσ2, Env.setVar]
  have s3 := asgE (B := B) "x1" (sub (V "da") (V "pa")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, hpa2, hda2]
    omega)
  set σ3 := σ2.setVar "x1" (MisBlk.den σ2 (sub (V "da") (V "pa"))) with hσ3
  have hsr : sRow arr i = arr.getD (2 + 2 * i + 1) 0 - arr.getD (2 + 2 * i) 0 := by
    unfold sRow; rw [show 3 + 2 * i = 2 + 2 * i + 1 by omega]
  have hx13 : σ3.vars "x1" = sRow arr i := by
    simp [hσ3, MisBlk.den, Env.setVar, hpa2, hda2, Bop.apply_sub, hsr]
  have hA3 : σ3.arrs "TK" = arr := by simp [hσ3, hσ2, hσ1, Env.setVar, hA]
  have hn3 : σ3.vars "n" = n := by simp [hσ3, hσ2, hσ1, Env.setVar, hn]
  have hsi : sRow arr i + 8 < B := by
    rw [hsr]; omega
  obtain ⟨σ4, r4, c4, a4, o4, f4⟩ := cntCom_run (B := B) arr n (sRow arr i) σ3 hA3 hn3 hlen hE
    hx13 hsi hnB
  have hcnt : σ4.vars "cj" = cntN arr i := by rw [c4, cntN_eq, hn']
  have hcn := cntN_le arr i
  rw [hn'] at hcn
  have hr24 : σ4.vars "r2" = σ.vars "r2" := by
    rw [f4 "r2" (by simp [SIN])]; simp [hσ3, hσ2, hσ1, Env.setVar]
  have hs1 : MisBlk.small B σ4 (V "r2") := by show σ4.vars "r2" < B; rw [hr24]; omega
  have hs2 : MisBlk.small B σ4 (V "cj") := by show σ4.vars "cj" < B; rw [hcnt]; omega
  have hA4 : σ4.arrs = σ.arrs := by rw [a4]; simp [hσ3, hσ2, hσ1, Env.setVar]
  have hO4 : σ4.out = σ.out := by rw [o4]; simp [hσ3, hσ2, hσ1, Env.setVar]
  have hfr4 : ∀ y, y ∉ SOUT → σ4.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "pa" := fun h => hy (by simp [SOUT, h])
    have g2 : y ≠ "da" := fun h => hy (by simp [SOUT, h])
    have g3 : y ≠ "x1" := fun h => hy (by simp [SOUT, h])
    have g4 : y ∉ SIN := fun h => hy (by
      simp only [SIN, SOUT, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [f4 y g4]
    simp [hσ3, hσ2, hσ1, Env.setVar, g1, g2, g3]
  by_cases hlt : σ.vars "r2" < cntN arr i
  · have hT : (Cond.lt (V "r2") (V "cj")).evalB B σ4 = some true :=
      condLt_true _ _ σ4 hs1 hs2 (by show σ4.vars "r2" < σ4.vars "cj"; rw [hr24, hcnt]; exact hlt)
    have s5 := asgE (B := B) "r2" (V "cj") σ4 hs2
    refine ⟨_, (s1.seq (s2.seq (s3.seq (r4.seq (Run.ite_true hT s5))))).mono (by
      simp [Cond.size, Expr.size]; omega), ?_, ?_, ?_, fun y hy => ?_⟩
    · simp [Env.setVar, MisBlk.den, hcnt]; omega
    · simp [Env.setVar, hA4]
    · simp [Env.setVar, hO4]
    · have : y ≠ "r2" := fun h => hy (by simp [SOUT, h])
      simp only [Env.setVar, if_neg this]; exact hfr4 y hy
  · have hF : (Cond.lt (V "r2") (V "cj")).evalB B σ4 = some false :=
      condLt_false _ _ σ4 hs1 hs2 (by show ¬ (σ4.vars "r2" < σ4.vars "cj"); rw [hr24, hcnt]; exact hlt)
    refine ⟨σ4, (s1.seq (s2.seq (s3.seq (r4.seq (Run.ite_false hF Run.skip))))).mono (by
      simp [Cond.size, Expr.size]; omega), ?_, hA4, hO4, hfr4⟩
    rw [hr24]; omega

/-- The running maximum of the counts. -/
def maxCom : Com := .seq (.assign "r2" (.lit 0)) (fLoop "i" "n" outerBody)

/-- The cost of the running maximum. -/
def Kmax (n : ℕ) : ℕ := ((100 + 10 + 4) * n + 100 + 10 + 4) * n + 20

set_option maxHeartbeats 3200000 in
/-- **The running maximum.** -/
theorem maxCom_run (arr : List ℕ) (n : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hn' : arr.getD 0 0 = n)
    (hlen : 3 + 2 * n ≤ arr.length) (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B)
    (hnB : 2 * n + 8 < B) :
    ∃ σ', Run B maxCom σ σ' (Kmax n) ∧ σ'.vars "r2" = omegaN arr ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ "i" :: SOUT → σ'.vars y = σ.vars y := by
  have s0 := MisBlk.asgE (B := B) "r2" (.lit 0) σ (by simp [MisBlk.small]; omega)
  set σ0 := σ.setVar "r2" (MisBlk.den σ (.lit 0)) with hσ0
  have hr0 : σ0.vars "r2" = 0 := by simp [hσ0, MisBlk.den, Env.setVar]
  have hn0 : σ0.vars "n" = n := by simp [hσ0, Env.setVar, hn]
  obtain ⟨σ', r, hacc, hag, hout⟩ := fLoop_spec (B := B) "i" "n" "r2" outerBody ("i" :: SOUT)
    (fun j a => max a (cntN arr j)) (fun j a => a ≤ n) ((100 + 10 + 4) * n + 100) n σ0
    (by simp) (by simp [SOUT]) (by decide) hn0 (by omega) (by rw [hr0]; omega)
    (fun j a ha => max_le ha (by have := cntN_le arr j; rw [hn'] at this; exact this)) (by
      intro σ1 hAg hlt hq
      have hA1 : σ1.arrs "TK" = arr := by rw [hAg.1]; simp [hσ0, Env.setVar, hA]
      have hn1 : σ1.vars "n" = n := by
        rw [hAg.2 "n" (by simp [SOUT])]; exact hn0
      obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := outerBody_run (B := B) arr n (σ1.vars "i") σ1 hA1 rfl
        hlt hn1 hn' hlen hE hnB hq
      refine ⟨σ2, r2, c2, ⟨by rw [a2, hAg.1], fun y hy => ?_⟩, f2 "i" (by simp [SOUT]), o2⟩
      have hy' : y ∉ SOUT := fun h => hy (List.mem_cons_of_mem _ h)
      rw [f2 y hy', hAg.2 y hy])
  refine ⟨σ', (s0.seq r).mono (by unfold Kmax; simp [Expr.size]; nlinarith), ?_, ?_, ?_,
    fun y hy => ?_⟩
  · rw [hacc, hr0]; unfold omegaN; rw [hn']
  · rw [hag.1]; simp [hσ0, Env.setVar]
  · rw [hout]; simp [hσ0, Env.setVar]
  · rw [hag.2 y hy]; simp only [hσ0, Env.setVar]
    have : y ≠ "r2" := fun h => hy (by simp [SOUT, h])
    simp [this]

/-- The number the parameter is multiplied by. -/
def omegaCom : Com :=
  .ite (.lt (.lit 0) (V "m")) maxCom (.assign "r2" (V "n"))

set_option maxHeartbeats 3200000 in
/-- **The number the parameter is multiplied by.** -/
theorem omegaCom_run (arr : List ℕ) (n m : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn' : arr.getD 0 0 = n) (hm' : arr.getD 1 0 = m)
    (hlen : 0 < m → 3 + 2 * n ≤ arr.length) (hE : 0 < m → ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B)
    (hnB : 2 * n + 8 < B) (hmB : m + 8 < B) :
    ∃ σ', Run B omegaCom σ σ' ((if 0 < m then Kmax n else 0) + 20) ∧ σ'.vars "r2" = omegaS arr ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ "i" :: SOUT → σ'.vars y = σ.vars y := by
  have hs0 : MisBlk.small B σ (.lit 0) := by simp [MisBlk.small]; omega
  have hsm : MisBlk.small B σ (V "m") := by show σ.vars "m" < B; rw [hm]; omega
  by_cases hm0 : 0 < m
  · have hT : (Cond.lt (.lit 0) (V "m")).evalB B σ = some true :=
      condLt_true _ _ σ hs0 hsm (by show 0 < σ.vars "m"; rw [hm]; exact hm0)
    obtain ⟨σ', r, c, a, o, f⟩ := maxCom_run (B := B) arr n σ hA hn hn' (hlen hm0) (hE hm0) hnB
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size, hm0]; omega), ?_, a, o, f⟩
    rw [c]
    unfold omegaS
    rw [hm', if_neg (by omega)]
  · have hF : (Cond.lt (.lit 0) (V "m")).evalB B σ = some false :=
      condLt_false _ _ σ hs0 hsm (by show ¬ (0 < σ.vars "m"); rw [hm]; exact hm0)
    have hnb : MisBlk.small B σ (V "n") := by show σ.vars "n" < B; rw [hn]; omega
    have s := MisBlk.asgE (B := B) "r2" (V "n") σ hnb
    refine ⟨_, (Run.ite_false hF s).mono (by simp [Cond.size, Expr.size, hm0]), ?_, ?_, ?_,
      fun y hy => ?_⟩
    · unfold omegaS
      have : m = 0 := by omega
      rw [hm', if_pos this, hn']
      simp [Env.setVar, MisBlk.den, hn]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · have : y ≠ "r2" := fun h => hy (by simp [SOUT, h])
      simp only [Env.setVar, if_neg this]

open Lax117284Proofs.Machine.Flag in
lemma foldl_flag (P : ℕ → Prop) [DecidablePred P] (ok0 : ℕ) (h : ok0 ≤ 1) (k : ℕ) :
    (List.range k).foldl (fun a j => if a = 1 ∧ P j then 1 else 0) ok0 = flagTo P ok0 k := by
  induction k with
  | zero => simp [flagTo_zero P ok0 h]
  | succ k ih => rw [List.range_succ, List.foldl_append, ih, flagTo_succ]; simp

/-- The cell `t` equals the cell of its client on the first day. -/
def DIp (arr : List ℕ) (n t : ℕ) : Prop :=
  arr.getD (2 + 2 * t) 0 = arr.getD (2 + 2 * (t % n)) 0 ∧
    arr.getD (2 + 2 * t + 1) 0 = arr.getD (2 + 2 * (t % n) + 1) 0

instance (arr : List ℕ) (n t : ℕ) : Decidable (DIp arr n t) := by unfold DIp; infer_instance

/-- The body of the day-independence check: the cell `i`. -/
def diBody : Com :=
  .seq (.assign "ci" (.bin .div (V "i") (V "n")))
  (.seq (.assign "cr" (mul (V "ci") (V "n")))
  (.seq (.assign "tt" (sub (V "i") (V "cr")))
  (.seq (.assign "pa" (rd "i" 0))
  (.seq (.assign "pb" (rd "tt" 0))
  (.seq (.assign "da" (rd "i" 1))
  (.seq (.assign "db" (rd "tt" 1))
    (.ite (.eq (V "pa") (V "pb"))
      (.ite (.eq (V "da") (V "db")) .skip (.assign "ok" (.lit 0)))
      (.assign "ok" (.lit 0)))))))))

/-- The scalars the check assigns. -/
def SDI : List String := ["ci", "cr", "tt", "pa", "pb", "da", "db", "ok"]

lemma mod_eq_sub' (i n : ℕ) : i - i / n * n = i % n := by
  have := Nat.div_add_mod i n
  rw [Nat.mul_comm] at this
  omega

set_option maxHeartbeats 6400000 in
/-- **One cell of the check.** -/
theorem diBody_run (arr : List ℕ) (n N i : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hi : σ.vars "i" = i) (hiN : i < N) (hn : σ.vars "n" = n)
    (hn0 : 0 < n) (hnN : n ≤ N) (hlen : 3 + 2 * N ≤ arr.length)
    (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B) (hNB : 2 * N + 8 < B) (hok : σ.vars "ok" ≤ 1) :
    ∃ σ', Run B diBody σ σ' 100 ∧
      σ'.vars "ok" = (if σ.vars "ok" = 1 ∧ DIp arr n i then 1 else 0) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ SDI → σ'.vars y = σ.vars y := by
  have hmod : i % n < n := Nat.mod_lt _ hn0
  have hdiv : i / n * n ≤ i := Nat.div_mul_le_self _ _
  have hdle : i / n ≤ i := Nat.div_le_self _ _
  have hmsub := mod_eq_sub' i n
  -- ci
  have s1 := asgE (B := B) "ci" (.bin .div (V "i") (V "n")) σ (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_div, hi, hn]; omega)
  set σ1 := σ.setVar "ci" (MisBlk.den σ (.bin .div (V "i") (V "n"))) with hσ1
  have hci1 : σ1.vars "ci" = i / n := by simp [hσ1, MisBlk.den, Env.setVar, hi, hn]
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hi]
  have hn1 : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  -- cr
  have s2 := asgE (B := B) "cr" (mul (V "ci") (V "n")) σ1 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_mul, hci1, hn1]
    omega)
  set σ2 := σ1.setVar "cr" (MisBlk.den σ1 (mul (V "ci") (V "n"))) with hσ2
  have hcr2 : σ2.vars "cr" = i / n * n := by simp [hσ2, MisBlk.den, Env.setVar, hci1, hn1]
  have hi2 : σ2.vars "i" = i := by simp [hσ2, Env.setVar, hi1]
  -- tt
  have s3 := asgE (B := B) "tt" (sub (V "i") (V "cr")) σ2 (by
    simp only [MisBlk.small_bin, MisBlk.small_var, MisBlk.den_var, Bop.apply_sub, hcr2, hi2]
    omega)
  set σ3 := σ2.setVar "tt" (MisBlk.den σ2 (sub (V "i") (V "cr"))) with hσ3
  have htt3 : σ3.vars "tt" = i % n := by
    simp [hσ3, MisBlk.den, Env.setVar, hcr2, hi2, Bop.apply_sub, hmsub]
  have hi3 : σ3.vars "i" = i := by simp [hσ3, Env.setVar, hi2]
  have hA3 : σ3.arrs "TK" = arr := by simp [hσ3, hσ2, hσ1, Env.setVar, hA]
  have e1 := hE (2 + 2 * i) (by omega)
  have e2 := hE (2 + 2 * i + 1) (by omega)
  have e3 := hE (2 + 2 * (i % n)) (by omega)
  have e4 := hE (2 + 2 * (i % n) + 1) (by omega)
  have z1 : arr.getD (2 + 2 * i + 0) 0 = arr.getD (2 + 2 * i) 0 := rfl
  have z2 : arr.getD (2 + 2 * (i % n) + 0) 0 = arr.getD (2 + 2 * (i % n)) 0 := rfl
  -- the four reads
  have s4 := asg_tk (B := B) "i" "pa" 0 σ3 arr i hA3 hi3 (by omega) (by omega) (by omega)
  set σ4 := σ3.setVar "pa" (arr.getD (2 + 2 * i + 0) 0) with hσ4
  have hA4 : σ4.arrs "TK" = arr := by simp [hσ4, Env.setVar, hA3]
  have htt4 : σ4.vars "tt" = i % n := by simp [hσ4, Env.setVar, htt3]
  have s5 := asg_tk (B := B) "tt" "pb" 0 σ4 arr (i % n) hA4 htt4 (by omega) (by omega) (by omega)
  set σ5 := σ4.setVar "pb" (arr.getD (2 + 2 * (i % n) + 0) 0) with hσ5
  have hA5 : σ5.arrs "TK" = arr := by simp [hσ5, Env.setVar, hA4]
  have hi5 : σ5.vars "i" = i := by simp [hσ5, hσ4, Env.setVar, hi3]
  have s6 := asg_tk (B := B) "i" "da" 1 σ5 arr i hA5 hi5 (by omega) (by omega) (by omega)
  set σ6 := σ5.setVar "da" (arr.getD (2 + 2 * i + 1) 0) with hσ6
  have hA6 : σ6.arrs "TK" = arr := by simp [hσ6, Env.setVar, hA5]
  have htt6 : σ6.vars "tt" = i % n := by simp [hσ6, hσ5, hσ4, Env.setVar, htt3]
  have s7 := asg_tk (B := B) "tt" "db" 1 σ6 arr (i % n) hA6 htt6 (by omega) (by omega) (by omega)
  set σ7 := σ6.setVar "db" (arr.getD (2 + 2 * (i % n) + 1) 0) with hσ7
  have hpa7 : σ7.vars "pa" = arr.getD (2 + 2 * i) 0 := by
    simp [hσ7, hσ6, hσ5, hσ4, Env.setVar]
  have hpb7 : σ7.vars "pb" = arr.getD (2 + 2 * (i % n)) 0 := by
    simp [hσ7, hσ6, hσ5, Env.setVar]
  have hda7 : σ7.vars "da" = arr.getD (2 + 2 * i + 1) 0 := by simp [hσ7, hσ6, Env.setVar]
  have hdb7 : σ7.vars "db" = arr.getD (2 + 2 * (i % n) + 1) 0 := by simp [hσ7, Env.setVar]
  have hok7 : σ7.vars "ok" = σ.vars "ok" := by
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hA7 : σ7.arrs = σ.arrs := by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hO7 : σ7.out = σ.out := by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar]
  have hfr7 : ∀ y, y ∉ SDI → σ7.vars y = σ.vars y := by
    intro y hy
    have g : ∀ z, z ∈ SDI → y ≠ z := fun z hz h => hy (h ▸ hz)
    simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Env.setVar, g "ci" (by simp [SDI]),
      g "cr" (by simp [SDI]), g "tt" (by simp [SDI]), g "pa" (by simp [SDI]),
      g "pb" (by simp [SDI]), g "da" (by simp [SDI]), g "db" (by simp [SDI])]
  have sp : MisBlk.small B σ7 (V "pa") := by show σ7.vars "pa" < B; rw [hpa7]; omega
  have sq : MisBlk.small B σ7 (V "pb") := by show σ7.vars "pb" < B; rw [hpb7]; omega
  have sd : MisBlk.small B σ7 (V "da") := by show σ7.vars "da" < B; rw [hda7]; omega
  have se : MisBlk.small B σ7 (V "db") := by show σ7.vars "db" < B; rw [hdb7]; omega
  have s0 := MisBlk.asgE (B := B) "ok" (.lit 0) σ7 (by simp [MisBlk.small]; omega)
  have hz : (σ7.setVar "ok" (MisBlk.den σ7 (.lit 0))).vars "ok" = 0 := by
    simp [Env.setVar, MisBlk.den]
  have hfz : ∀ y, y ∉ SDI →
      (σ7.setVar "ok" (MisBlk.den σ7 (.lit 0))).vars y = σ.vars y := by
    intro y hy
    have : y ≠ "ok" := fun h => hy (by simp [SDI, h])
    simp only [Env.setVar, if_neg this]
    exact hfr7 y hy
  have hAz : (σ7.setVar "ok" (MisBlk.den σ7 (.lit 0))).arrs = σ.arrs := by simp [Env.setVar, hA7]
  have hOz : (σ7.setVar "ok" (MisBlk.den σ7 (.lit 0))).out = σ.out := by simp [Env.setVar, hO7]
  by_cases hpa : arr.getD (2 + 2 * i) 0 = arr.getD (2 + 2 * (i % n)) 0
  · have hT1 : (Cond.eq (V "pa") (V "pb")).evalB B σ7 = some true :=
      MisBlk.condEq_true _ _ σ7 sp sq (by show σ7.vars "pa" = σ7.vars "pb"; rw [hpa7, hpb7]; exact hpa)
    by_cases hpd : arr.getD (2 + 2 * i + 1) 0 = arr.getD (2 + 2 * (i % n) + 1) 0
    · have hT2 : (Cond.eq (V "da") (V "db")).evalB B σ7 = some true :=
        MisBlk.condEq_true _ _ σ7 sd se (by
          show σ7.vars "da" = σ7.vars "db"; rw [hda7, hdb7]; exact hpd)
      refine ⟨σ7, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (Run.ite_true hT1 (Run.ite_true hT2 Run.skip))))))))).mono (by
        simp [Cond.size, Expr.size]), ?_, hA7, hO7, fun y hy => ?_⟩
      · rw [hok7]
        by_cases h1 : σ.vars "ok" = 1
        · rw [if_pos ⟨h1, hpa, hpd⟩]; omega
        · rw [if_neg (fun h => h1 h.1)]; omega
      · exact hfr7 y hy
    · have hF2 : (Cond.eq (V "da") (V "db")).evalB B σ7 = some false :=
        MisBlk.condEq_false _ _ σ7 sd se (by
          show σ7.vars "da" ≠ σ7.vars "db"; rw [hda7, hdb7]; exact hpd)
      refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (Run.ite_true hT1 (Run.ite_false hF2 s0))))))))).mono (by
        simp [Cond.size, Expr.size]), ?_, hAz, hOz, hfz⟩
      · rw [hz, if_neg (fun h => hpd h.2.2)]
  · have hF1 : (Cond.eq (V "pa") (V "pb")).evalB B σ7 = some false :=
      MisBlk.condEq_false _ _ σ7 sp sq (by
        show σ7.vars "pa" ≠ σ7.vars "pb"; rw [hpa7, hpb7]; exact hpa)
    refine ⟨_, (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (Run.ite_false hF1 s0)))))))).mono (by
      simp [Cond.size, Expr.size]), ?_, hAz, hOz, hfz⟩
    rw [hz, if_neg (fun h => hpa h.2.1)]

/-- The day-independence check. -/
def diCom : Com := fLoop "i" "N" diBody

open Lax117284Proofs.Machine.Flag in
set_option maxHeartbeats 3200000 in
/-- **The day-independence check.** -/
theorem diCom_run (arr : List ℕ) (n m N : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hN : σ.vars "N" = N) (hNmn : N = m * n)
    (hlen : 3 + 2 * N ≤ arr.length) (hE : ∀ k < 3 + 2 * N, arr.getD k 0 + 8 < B)
    (hNB : 2 * N + 8 < B) (hok : σ.vars "ok" ≤ 1) :
    ∃ σ', Run B diCom σ σ' ((100 + 10 + 4) * N + 6) ∧
      σ'.vars "ok" = flagTo (DIp arr n) (σ.vars "ok") N ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ "i" :: SDI → σ'.vars y = σ.vars y := by
  have hs0 := σ
  obtain ⟨σ', r, hacc, hag, hout⟩ := fLoop_spec (B := B) "i" "N" "ok" diBody ("i" :: SDI)
    (fun j a => if a = 1 ∧ DIp arr n j then 1 else 0) (fun j a => a ≤ 1) 100 N σ
    (by simp) (by simp [SDI]) (by decide) hN (by omega) hok
    (fun j a ha => by split <;> omega) (by
      intro σ1 hAg hlt hq
      have hA1 : σ1.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn1 : σ1.vars "n" = n := by rw [hAg.2 "n" (by simp [SDI])]; exact hn
      have hn0 : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp at hNmn; omega
        · exact h
      have hnN : n ≤ N := by rw [hNmn]; exact Nat.le_mul_of_pos_left _ (by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hNmn; omega
        · exact h)
      obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := diBody_run (B := B) arr n N (σ1.vars "i") σ1 hA1 rfl hlt
        hn1 hn0 hnN hlen hE hNB hq
      refine ⟨σ2, r2, c2, ⟨by rw [a2, hAg.1], fun y hy => ?_⟩, f2 "i" (by simp [SDI]), o2⟩
      have hy' : y ∉ SDI := fun h => hy (List.mem_cons_of_mem _ h)
      rw [f2 y hy', hAg.2 y hy])
  refine ⟨σ', r, ?_, hag.1, hout, fun y hy => hag.2 y hy⟩
  rw [hacc]
  exact foldl_flag (DIp arr n) (σ.vars "ok") hok N

lemma omegaN_le (arr : List ℕ) : omegaN arr ≤ arr.getD 0 0 := by
  unfold omegaN
  exact Lax117284Proofs.X3Word.foldl_max_le (f := fun j => cntN arr j) _ 0 (Nat.zero_le _) (fun j _ => cntN_le arr j)

lemma omegaS_le (arr : List ℕ) : omegaS arr ≤ arr.getD 0 0 := by
  unfold omegaS
  split
  · exact le_rfl
  · exact omegaN_le arr

end Lax117284Proofs.Machine.X3Loop
