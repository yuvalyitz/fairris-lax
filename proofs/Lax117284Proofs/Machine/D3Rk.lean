import Lax117284Proofs.Machine.X3Loop
import Lax117284Proofs.Machine.D3Ops
import Lax117284Proofs.Machine.ILoop
import Lax117284Proofs.D3Rank
import Lax117284Proofs.D3List

/-!
The order of the clients by due date: the rank of every client is the number of clients that
precede it, computed by a count over the clients, and the client is stored at its rank.
-/

namespace Lax117284Proofs.Machine.D3Rk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)
open Lax117284Proofs.Machine.SatRank (bumpS)
open Lax117284Proofs.Machine.SatOps (asg_addl)
open Lax117284Proofs.Machine.X3Loop (rd)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.D3Rank

variable {B : ℕ}

/-- The due date of a client. -/
def ddA (arr : List ℕ) (j : ℕ) : ℕ := arr.getD (3 + 2 * j) 0

/-- The body of the count of the clients that precede client `i`: the client `j`. -/
def rkInner : Com :=
  .seq (.assign "dq" (rd "j" 1))
    (.ite (.lt (V "dq") (V "dj")) (bumpS "cj")
      (.ite (.eq (V "dq") (V "dj"))
        (.ite (.lt (V "j") (V "i")) (bumpS "cj") .skip) .skip))

set_option maxHeartbeats 3200000 in
/-- **One client of the count.** -/
theorem rkInner_run (arr : List ℕ) (n j i dj : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hj : σ.vars "j" = j) (hjn : j < n) (hi : σ.vars "i" = i)
    (hin : i < n) (hdj : σ.vars "dj" = dj) (hddj : dj = ddA arr i) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hcj : σ.vars "cj" + 8 < B)
    (hnB : 2 * n + 8 < B) :
    ∃ σ', Run B rkInner σ σ' 100 ∧
      σ'.vars "cj" = σ.vars "cj" + (if Lt2 (ddA arr) j i then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "dq" → y ≠ "cj" → σ'.vars y = σ.vars y := by
  have e1 := hE (2 + 2 * j + 1) (by omega)
  have e0 : arr.getD (2 + 2 * j + 1) 0 = ddA arr j := by
    unfold ddA; rw [show 3 + 2 * j = 2 + 2 * j + 1 by omega]
  have e2 : dj + 8 < B := by
    rw [hddj]; unfold ddA; have := hE (3 + 2 * i) (by omega); omega
  have s1 := asg_tk (B := B) "j" "dq" 1 σ arr j hA hj (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "dq" (arr.getD (2 + 2 * j + 1) 0) with hσ1
  have hdq : σ1.vars "dq" = ddA arr j := by
    rw [← e0]; simp only [hσ1, Env.setVar, if_true]
  have hdj1 : σ1.vars "dj" = dj := by simp [hσ1, Env.setVar, hdj]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hj]
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hi]
  have hcj1 : σ1.vars "cj" = σ.vars "cj" := by simp [hσ1, Env.setVar]
  have hA1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have hO1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ≠ "dq" → σ1.vars y = σ.vars y := by
    intro y hy; simp [hσ1, Env.setVar, hy]
  have hsq : MisBlk.small B σ1 (V "dq") := by
    show σ1.vars "dq" < B; rw [hdq, ← e0]; omega
  have hsd : MisBlk.small B σ1 (V "dj") := by
    show σ1.vars "dj" < B; rw [hdj1]; omega
  have hsj : MisBlk.small B σ1 (V "j") := by show σ1.vars "j" < B; rw [hj1]; omega
  have hsi : MisBlk.small B σ1 (V "i") := by show σ1.vars "i" < B; rw [hi1]; omega
  have hcjB : σ1.vars "cj" < B := by rw [hcj1]; omega
  have b := asg_addl (B := B) "cj" "cj" 1 σ1 (σ1.vars "cj") rfl hcjB (by omega) (by omega)
  have b' : Run B (bumpS "cj") σ1 (σ1.setVar "cj" (σ1.vars "cj" + 1)) 5 := b
  have hbump : ∀ y, y ≠ "dq" → y ≠ "cj" →
      (σ1.setVar "cj" (σ1.vars "cj" + 1)).vars y = σ.vars y := by
    intro y a c; simp only [Env.setVar, if_neg c]; exact hfr1 y a
  have hlt2 : Lt2 (ddA arr) j i ↔ ddA arr j < dj ∨ (ddA arr j = dj ∧ j < i) := by
    unfold Lt2; rw [hddj]
  by_cases h1 : ddA arr j < dj
  · have hT : (Cond.lt (V "dq") (V "dj")).evalB B σ1 = some true :=
      condLt_true _ _ σ1 hsq hsd (by show σ1.vars "dq" < σ1.vars "dj"; rw [hdq, hdj1]; exact h1)
    refine ⟨_, (s1.seq (Run.ite_true hT b')).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_,
      fun y a c => hbump y a c⟩
    · rw [if_pos (hlt2.2 (Or.inl h1))]; simp [Env.setVar, hcj1]
    · simp [Env.setVar, hA1]
    · simp [Env.setVar, hO1]
  · have hF : (Cond.lt (V "dq") (V "dj")).evalB B σ1 = some false :=
      condLt_false _ _ σ1 hsq hsd (by show ¬ (σ1.vars "dq" < σ1.vars "dj"); rw [hdq, hdj1]; exact h1)
    by_cases h2 : ddA arr j = dj
    · have hT2 : (Cond.eq (V "dq") (V "dj")).evalB B σ1 = some true :=
        MisBlk.condEq_true _ _ σ1 hsq hsd (by show σ1.vars "dq" = σ1.vars "dj"; rw [hdq, hdj1]; exact h2)
      by_cases h3 : j < i
      · have hT3 : (Cond.lt (V "j") (V "i")).evalB B σ1 = some true :=
          condLt_true _ _ σ1 hsj hsi (by show σ1.vars "j" < σ1.vars "i"; rw [hj1, hi1]; exact h3)
        refine ⟨_, (s1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_true hT3 b')))).mono (by
          simp [Cond.size, Expr.size]), ?_, ?_, ?_, fun y a c => hbump y a c⟩
        · rw [if_pos (hlt2.2 (Or.inr ⟨h2, h3⟩))]; simp [Env.setVar, hcj1]
        · simp [Env.setVar, hA1]
        · simp [Env.setVar, hO1]
      · have hF3 : (Cond.lt (V "j") (V "i")).evalB B σ1 = some false :=
          condLt_false _ _ σ1 hsj hsi (by show ¬ (σ1.vars "j" < σ1.vars "i"); rw [hj1, hi1]; exact h3)
        refine ⟨σ1, (s1.seq (Run.ite_false hF (Run.ite_true hT2 (Run.ite_false hF3 Run.skip)))).mono (by
          simp [Cond.size, Expr.size]), ?_, hA1, hO1, fun y a c => hfr1 y a⟩
        rw [hcj1]
        have : ¬ Lt2 (ddA arr) j i := fun h => by
          rcases hlt2.1 h with h | h
          · exact h1 h
          · exact h3 h.2
        rw [if_neg this]; simp
    · have hF2 : (Cond.eq (V "dq") (V "dj")).evalB B σ1 = some false :=
        MisBlk.condEq_false _ _ σ1 hsq hsd (by show σ1.vars "dq" ≠ σ1.vars "dj"; rw [hdq, hdj1]; exact h2)
      refine ⟨σ1, (s1.seq (Run.ite_false hF (Run.ite_false hF2 Run.skip))).mono (by
        simp [Cond.size, Expr.size]), ?_, hA1, hO1, fun y a c => hfr1 y a⟩
      rw [hcj1]
      have : ¬ Lt2 (ddA arr) j i := fun h => by
        rcases hlt2.1 h with h | h
        · exact h1 h
        · exact h2 h.1
      rw [if_neg this]; simp

/-- The number of clients that precede client `i`. -/
def rkCntCom : Com := .seq (.assign "cj" (.lit 0)) (fLoop "j" "n" rkInner)

/-- The scalars the count assigns. -/
def SRKC : List String := ["j", "dq", "cj"]

set_option maxHeartbeats 3200000 in
/-- **The count of the clients that precede a client.** -/
theorem rkCntCom_run (arr : List ℕ) (n i dj : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hi : σ.vars "i" = i) (hin : i < n)
    (hdj : σ.vars "dj" = dj) (hddj : dj = ddA arr i) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hnB : 2 * n + 8 < B) :
    ∃ σ', Run B rkCntCom σ σ' ((100 + 10 + 4) * n + 20) ∧
      σ'.vars "cj" = rk (ddA arr) n i ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ SRKC → σ'.vars y = σ.vars y := by
  have s0 := MisBlk.asgE (B := B) "cj" (.lit 0) σ (by simp [MisBlk.small]; omega)
  set σ0 := σ.setVar "cj" (MisBlk.den σ (.lit 0)) with hσ0
  have hc0 : σ0.vars "cj" = 0 := by simp [hσ0, MisBlk.den, Env.setVar]
  have hn0 : σ0.vars "n" = n := by simp [hσ0, Env.setVar, hn]
  obtain ⟨σ', r, hacc, hag, hout⟩ := fLoop_spec (B := B) "j" "n" "cj" rkInner SRKC
    (fun j a => a + if decide (Lt2 (ddA arr) j i) = true then 1 else 0) (fun j a => a ≤ j) 100 n σ0
    (by simp [SRKC]) (by simp [SRKC]) (by decide) hn0 (by omega) (by rw [hc0])
    (fun j a ha => by split <;> omega) (by
      intro σ1 hAg hlt hq
      have hA1 : σ1.arrs "TK" = arr := by rw [hAg.1]; simp [hσ0, Env.setVar, hA]
      have hi1 : σ1.vars "i" = i := by
        rw [hAg.2 "i" (by simp [SRKC])]; simp [hσ0, Env.setVar, hi]
      have hdj1 : σ1.vars "dj" = dj := by
        rw [hAg.2 "dj" (by simp [SRKC])]; simp [hσ0, Env.setVar, hdj]
      obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := rkInner_run (B := B) arr n (σ1.vars "j") i dj σ1 hA1 rfl
        hlt hi1 hin hdj1 hddj hlen hE (by omega) hnB
      refine ⟨σ2, r2, ?_, ⟨by rw [a2, hAg.1], fun y hy => ?_⟩, f2 "j" (by decide) (by decide),
        o2⟩
      · rw [c2]; simp
      · have h1 : y ≠ "dq" := fun h => hy (by simp [SRKC, h])
        have h3 : y ≠ "cj" := fun h => hy (by simp [SRKC, h])
        rw [f2 y h1 h3, hAg.2 y hy])
  refine ⟨σ', (s0.seq r).mono (by simp [Expr.size]; omega), ?_, ?_, ?_, fun y hy => ?_⟩
  · rw [hacc, hc0, X3Loop.foldl_count (fun j => decide (Lt2 (ddA arr) j i)), Nat.zero_add]
    rfl
  · rw [hag.1]; simp [hσ0, Env.setVar]
  · rw [hout]; simp [hσ0, Env.setVar]
  · rw [hag.2 y hy]; simp only [hσ0, Env.setVar]
    have : y ≠ "cj" := fun h => hy (by simp [SRKC, h])
    simp [this]

/-- The body of the rank loop: the client `i` is stored at its rank. -/
def rkOuter : Com :=
  .seq (.assign "dj" (rd "i" 1)) (.seq rkCntCom (.store "R" (add (V "PK") (V "cj")) (V "i")))

/-- The scalars the body assigns. -/
def SRKO : List String := ["dj", "j", "dq", "cj"]

set_option maxHeartbeats 3200000 in
/-- **One client of the rank loop.** -/
theorem rkOuter_run (arr : List ℕ) (n i PK : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hi : σ.vars "i" = i) (hin : i < n)
    (hPK : σ.vars "PK" = PK) (hlen : 3 + 2 * n ≤ arr.length)
    (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B) (hnB : 2 * n + 8 < B) (hPKB : PK + n + 8 < B)
    (hR : PK + n ≤ (σ.arrs "R").length) :
    ∃ σ', Run B rkOuter σ σ' ((100 + 10 + 4) * n + 60) ∧
      σ'.arrs "R" = (σ.arrs "R").set (PK + rk (ddA arr) n i) i ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ SRKO → σ'.vars y = σ.vars y := by
  have e1 := hE (2 + 2 * i + 1) (by omega)
  have e0 : arr.getD (2 + 2 * i + 1) 0 = ddA arr i := by
    unfold ddA; rw [show 3 + 2 * i = 2 + 2 * i + 1 by omega]
  have e00 : arr.getD (2 + 2 * i + 0) 0 = arr.getD (2 + 2 * i) 0 := rfl
  have s1 := asg_tk (B := B) "i" "dj" 1 σ arr i hA hi (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "dj" (arr.getD (2 + 2 * i + 1) 0) with hσ1
  have hdj : σ1.vars "dj" = ddA arr i := by
    rw [← e0]; simp only [hσ1, Env.setVar, if_true]
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, hA]
  have hn1 : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hn]
  have hi1 : σ1.vars "i" = i := by simp [hσ1, Env.setVar, hi]
  have hPK1 : σ1.vars "PK" = PK := by simp [hσ1, Env.setVar, hPK]
  obtain ⟨σ2, r2, c2, a2, o2, f2⟩ := rkCntCom_run (B := B) arr n i (ddA arr i) σ1 hA1 hn1 hi1 hin
    hdj rfl hlen hE hnB
  have hrk : rk (ddA arr) n i < n := rk_lt hin
  have hPK2 : σ2.vars "PK" = PK := by rw [f2 "PK" (by simp [SRKC])]; exact hPK1
  have hi2 : σ2.vars "i" = i := by rw [f2 "i" (by simp [SRKC])]; exact hi1
  have hR2 : PK + rk (ddA arr) n i < (σ2.arrs "R").length := by
    rw [a2]; simp only [hσ1, Env.setVar]; omega
  have s3 := store_R2 (B := B) "PK" "cj" "i" σ2 PK (rk (ddA arr) n i) i hPK2 c2 hi2 hR2 (by omega)
    (by omega) (by omega) (by omega)
  refine ⟨_, (s1.seq (r2.seq s3)).mono (by simp [Expr.size]; omega), ?_, ?_, ?_, fun y hy => ?_⟩
  · simp only [setArr_arrs_R]
    rw [a2]; simp [hσ1, Env.setVar]
  · rw [setArr_arrs_ne _ _ _ _ _ (by decide), a2]; simp [hσ1, Env.setVar]
  · simp [o2, hσ1, Env.setVar]
  · have h1 : y ≠ "dj" := fun h => hy (by simp [SRKO, h])
    have h2 : y ∉ SRKC := fun h => hy (by simp only [SRKC, SRKO, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    simp only [setArr_vars]
    rw [f2 y h2]; simp [hσ1, Env.setVar, h1]

lemma stFold_succ (idx val : ℕ → ℕ) (A0 : List ℕ) (j : ℕ) :
    D3List.stFold (j + 1) idx val A0 = (D3List.stFold j idx val A0).set (idx j) (val j) := by
  unfold D3List.stFold
  rw [List.range_succ, List.foldl_append]
  simp

/-- The rank loop. -/
def rkLoop : Com := fLoop "i" "n" rkOuter

set_option maxHeartbeats 3200000 in
/-- **The order of the clients.** -/
theorem rkLoop_run (arr : List ℕ) (n PK : ℕ) (σ : Env)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hPK : σ.vars "PK" = PK)
    (hlen : 3 + 2 * n ≤ arr.length) (hE : ∀ k < 3 + 2 * n, arr.getD k 0 + 8 < B)
    (hnB : 2 * n + 8 < B) (hPKB : PK + n + 8 < B) (hR : PK + n ≤ (σ.arrs "R").length) :
    ∃ σ', Run B rkLoop σ σ' (((100 + 10 + 4) * n + 60 + 10 + 4) * n + 6) ∧
      σ'.arrs "R" = D3List.stFold n (fun i' => PK + rk (ddA arr) n i') (fun i' => i') (σ.arrs "R") ∧
      σ'.arrs "TK" = arr ∧ σ'.out = σ.out ∧ ∀ y, y ∉ "i" :: SRKO → σ'.vars y = σ.vars y := by
  have hinj : ∀ a b, a < n → b < n → PK + rk (ddA arr) n a = PK + rk (ddA arr) n b → a = b :=
    fun a b ha hb h => rk_injOn (dd := ddA arr) ha hb (by omega)
  have hlt : ∀ j < n, PK + rk (ddA arr) n j < (σ.arrs "R").length :=
    fun j hj => by have := rk_lt (dd := ddA arr) hj; omega
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "i" "n" rkOuter
    (fun j σ' => σ'.arrs "R" = D3List.stFold j (fun i' => PK + rk (ddA arr) n i') (fun i' => i')
        (σ.arrs "R") ∧ σ'.arrs "TK" = arr ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ "i" :: SRKO → σ'.vars y = σ.vars y)
    ((100 + 10 + 4) * n + 60) n σ hn
    (fun j σ' h => by rw [h.2.2.2 "n" (by simp [SRKO])]; exact hn) (by decide) (by omega)
    ⟨by simp [D3List.stFold, Env.setVar], by simp [Env.setVar, hA], by simp [Env.setVar],
      fun y hy => by
        have : y ≠ "i" := fun h => hy (by simp [h])
        simp [Env.setVar, this]⟩
    (fun j σ' v h => ⟨by simpa [Env.setVar] using h.1, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2.1, fun y hy => by
        have : y ≠ "i" := fun h => hy (by simp [h])
        simp only [Env.setVar, if_neg this]; exact h.2.2.2 y hy⟩)
    (by
      intro j σ1 hq hjv hjn
      obtain ⟨hR1, hA1, hO1, hF1⟩ := hq
      have hlen1 := (D3List.stFold_inv (fun i' => PK + rk (ddA arr) n i') (fun i' => i') (σ.arrs "R")
        n hinj hlt j (by omega)).1
      have hn1 : σ1.vars "n" = n := by rw [hF1 "n" (by simp [SRKO])]; exact hn
      have hPK1 : σ1.vars "PK" = PK := by rw [hF1 "PK" (by simp [SRKO])]; exact hPK
      obtain ⟨σ2, r2, hR2, hA2, hO2, hF2⟩ := rkOuter_run (B := B) arr n j PK σ1 hA1 hn1 hjv hjn hPK1
        hlen hE hnB hPKB (by rw [hR1, hlen1]; exact hR)
      refine ⟨σ2, r2, ⟨?_, ?_, ?_, fun y hy => ?_⟩, ?_⟩
      · rw [hR2, hR1, stFold_succ]
      · rw [hA2]; exact hA1
      · rw [hO2]; exact hO1
      · have hy' : y ∉ SRKO := fun h => hy (List.mem_cons_of_mem _ h)
        rw [hF2 y hy']; exact hF1 y hy
      · rw [hF2 "i" (by simp [SRKO])]; exact hjv)
  refine ⟨σ', r, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hQ
  refine ⟨h1, h2, h3, fun y hy => ?_⟩
  exact h4 y hy

end Lax117284Proofs.Machine.D3Rk
