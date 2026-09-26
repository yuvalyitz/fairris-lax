import Lax117284Proofs.Machine.D3Rk
import Lax117284Proofs.Machine.D3Client
import Lax117284Proofs.D3Link

/-!
Setting the table up for a client: the clients are ordered by due date, the state of no days
served is marked, and, once the last client is processed, the table is scanned for a mark below
the number of states of the last day.
-/

namespace Lax117284Proofs.Machine.D3Setup

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false condEq_true condEq_false)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.Machine.D3Rk Lax117284Proofs.Machine.D3Client
open Lax117284Proofs.D3Rank Lax117284Proofs.D3Link

variable {B : ℕ}

/-- The initial mark: the state of no days served. -/
theorem initR_run (σ : Env) (hlen : 0 < (σ.arrs "R").length) (hB : 1 < B) :
    Run B (.store "R" (.lit 0) (.lit 1)) σ (σ.setArr "R" 0 1) 3 :=
  (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) hlen).mono (by simp [Expr.size])

/-- The body of the scan: the state `sc`. -/
def scanBody : Com :=
  .seq (.assign "rv" (.get "R" (V "sc")))
    (.ite (.eq (V "rv") (.lit 1)) (.assign "fnd" (.lit 1)) .skip)

/-- The scalars the scan assigns. -/
def SSC : List String := ["rv", "fnd"]

set_option maxHeartbeats 3200000 in
/-- **One state of the scan.** -/
theorem scanBody_run (σ : Env) (R : List ℕ) (s : ℕ) (hR : σ.arrs "R" = R) (hs : σ.vars "sc" = s)
    (hsl : s < R.length) (hsB : s < B) (hRB : ∀ j, R.getD j 0 < B) (hB1 : 1 < B)
    (hfnd : σ.vars "fnd" ≤ 1) :
    ∃ σ', Run B scanBody σ σ' 20 ∧
      σ'.vars "fnd" = (if σ.vars "fnd" = 1 ∨ R.getD s 0 = 1 then 1 else 0) ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ SSC → σ'.vars y = σ.vars y := by
  have hss : MisBlk.small B σ (V "sc") := by show σ.vars "sc" < B; rw [hs]; exact hsB
  have s1 := asg_R (B := B) "rv" "sc" σ s hs (by rw [hR]; exact hsl) (by rw [hR]; exact hRB s) hsB
  set σ1 := σ.setVar "rv" ((σ.arrs "R").getD s 0) with hσ1
  have hrv1 : σ1.vars "rv" = R.getD s 0 := by rw [← hR]; simp [hσ1, Env.setVar]
  have hA1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have hO1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfnd1 : σ1.vars "fnd" = σ.vars "fnd" := by simp [hσ1, Env.setVar]
  have hsr : MisBlk.small B σ1 (V "rv") := by show σ1.vars "rv" < B; rw [hrv1]; exact hRB s
  have hsl1 : MisBlk.small B σ1 (Expr.lit 1) := by simp [MisBlk.small]; omega
  by_cases hc : R.getD s 0 = 1
  · have hT : (Cond.eq (V "rv") (.lit 1)).evalB B σ1 = some true :=
      condEq_true _ _ σ1 hsr hsl1 (by show σ1.vars "rv" = 1; rw [hrv1]; exact hc)
    have s2 := asgE (B := B) "fnd" (.lit 1) σ1 (by simp [MisBlk.small]; omega)
    refine ⟨_, (s1.seq (Run.ite_true hT s2)).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_,
      fun y hy => ?_⟩
    · have hv1 : (σ1.setVar "fnd" (MisBlk.den σ1 (Expr.lit 1))).vars "fnd" = 1 := by
        simp [Env.setVar, MisBlk.den]
      rw [hv1, if_pos (Or.inr hc)]
    · simp [Env.setVar, hA1]
    · simp [Env.setVar, hO1]
    · have h1 : y ≠ "rv" := fun e => hy (by simp [SSC, e])
      have h2 : y ≠ "fnd" := fun e => hy (by simp [SSC, e])
      simp [Env.setVar, hσ1, h1, h2]
  · have hF : (Cond.eq (V "rv") (.lit 1)).evalB B σ1 = some false :=
      condEq_false _ _ σ1 hsr hsl1 (by show σ1.vars "rv" ≠ 1; rw [hrv1]; exact hc)
    refine ⟨_, (s1.seq (Run.ite_false hF Run.skip)).mono (by simp [Cond.size, Expr.size]), ?_, ?_,
      ?_, fun y hy => ?_⟩
    · rw [hfnd1]
      by_cases h2 : σ.vars "fnd" = 1
      · rw [if_pos (Or.inl h2)]; omega
      · rw [if_neg (fun h => h.elim h2 hc)]; omega
    · simp [hA1]
    · simp [hO1]
    · have h1 : y ≠ "rv" := fun e => hy (by simp [SSC, e])
      simp [hσ1, Env.setVar, h1, hfnd1]

/-- The scan of the table. -/
def scanLoop : Com := fLoop "sc" "PP" scanBody

set_option maxHeartbeats 6400000 in
/-- **The scan of the table for a mark.** -/
theorem scanLoop_run (σ : Env) (R : List ℕ) (P : ℕ) (hR : σ.arrs "R" = R) (hPP : σ.vars "PP" = P)
    (hPl : P ≤ R.length) (hRB : ∀ j, R.getD j 0 < B) (hPB : P + 1 < B) (hfnd : σ.vars "fnd" ≤ 1) :
    ∃ σ', Run B scanLoop σ σ' ((20 + 10 + 4) * P + 6) ∧
      σ'.vars "fnd" = (if σ.vars "fnd" = 1 ∨ ∃ s < P, R.getD s 0 = 1 then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ ∀ y, y ∉ "sc" :: SSC → σ'.vars y = σ.vars y := by
  have hB1 : 1 < B := by omega
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "sc" "PP" scanBody
    (fun j σ' => σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.vars "fnd" = (if σ.vars "fnd" = 1 ∨ ∃ s < j, R.getD s 0 = 1 then 1 else 0) ∧
      ∀ y, y ∉ "sc" :: SSC → σ'.vars y = σ.vars y)
    20 P σ hPP (fun j σ' hq => by rw [hq.2.2.2 "PP" (by simp [SSC])]; exact hPP) (by decide)
    (by omega)
    ⟨by simp [Env.setVar], by simp [Env.setVar], by
      have hnex : ¬ ∃ s < 0, R.getD s 0 = 1 := fun ⟨s, hs, _⟩ => absurd hs (by omega)
      have hv0 : (σ.setVar "sc" 0).vars "fnd" = σ.vars "fnd" := by simp [Env.setVar]
      rw [hv0]
      by_cases h2 : σ.vars "fnd" = 1
      · rw [if_pos (Or.inl h2)]; exact h2
      · rw [if_neg (fun h => h.elim h2 hnex)]; omega,
      fun y hy => by
        have : y ≠ "sc" := fun e => hy (by simp [e])
        simp [Env.setVar, this]⟩
    (fun j σ' v hq => ⟨by simpa [Env.setVar] using hq.1, by simpa [Env.setVar] using hq.2.1,
      by simpa [Env.setVar] using hq.2.2.1, fun y hy => by
        have : y ≠ "sc" := fun e => hy (by simp [e])
        simp only [Env.setVar, if_neg this]; exact hq.2.2.2 y hy⟩)
    (by
      intro j σ1 hq hjv hjn
      obtain ⟨hA1, hO1, hfnd1, hF1⟩ := hq
      have hRA1 : σ1.arrs "R" = R := by rw [hA1, hR]
      obtain ⟨σ2, r2, hfnd2, hA2, hO2, hF2⟩ := scanBody_run σ1 R j hRA1 hjv (by omega) (by omega)
        hRB hB1 (by rw [hfnd1]; split <;> omega)
      refine ⟨σ2, r2, ⟨by rw [hA2, hA1], by rw [hO2, hO1], ?_, fun y hy => ?_⟩, ?_⟩
      · rw [hfnd2, hfnd1]
        have hiff : (σ.vars "fnd" = 1 ∨ ∃ s < j + 1, R.getD s 0 = 1) ↔
            ((if σ.vars "fnd" = 1 ∨ ∃ s < j, R.getD s 0 = 1 then (1 : ℕ) else 0) = 1 ∨
              R.getD j 0 = 1) := by
          constructor
          · rintro (h1 | ⟨s, hs, hRs⟩)
            · exact Or.inl (by rw [if_pos (Or.inl h1)])
            · rcases Nat.lt_or_ge s j with hsj | hsj
              · exact Or.inl (by rw [if_pos (Or.inr ⟨s, hsj, hRs⟩)])
              · have hsj' : s = j := by omega
                exact Or.inr (hsj' ▸ hRs)
          · rintro (h1 | h1)
            · by_cases h2 : σ.vars "fnd" = 1 ∨ ∃ s < j, R.getD s 0 = 1
              · rcases h2 with h2 | ⟨s, hs, hRs⟩
                · exact Or.inl h2
                · exact Or.inr ⟨s, by omega, hRs⟩
              · rw [if_neg h2] at h1; omega
            · exact Or.inr ⟨j, by omega, h1⟩
        by_cases hfin : σ.vars "fnd" = 1 ∨ ∃ s < j + 1, R.getD s 0 = 1
        · rw [if_pos hfin, if_pos (hiff.1 hfin)]
        · rw [if_neg hfin, if_neg (fun h => hfin (hiff.2 h))]
      · have hy' : y ∉ SSC := fun e => hy (List.mem_cons_of_mem _ e)
        rw [hF2 y hy']; exact hF1 y hy
      · rw [hF2 "sc" (by simp [SSC])]; exact hjv)
  obtain ⟨a1, a2, a3, a4⟩ := hQ
  exact ⟨σ', r, a3, a1, a2, a4⟩

end Lax117284Proofs.Machine.D3Setup
