import Lax117284Proofs.Machine.D3Sweep

/-!
The collapse of the table after a client: the states that served `k` days move to the first layer
and everything else is cleared.
-/

namespace Lax117284Proofs.Machine.D3Coll

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)
open Lax117284Proofs.Machine.D3Ops

variable {B : ℕ}

/-- The body of the collapse: the cell `cx`. -/
def collBody : Com :=
  .ite (.lt (V "cx") (V "PP"))
    (.seq (.assign "aa" (.get "R" (add (V "cx") (V "pk")))) (.store "R" (V "cx") (V "aa")))
    (.store "R" (V "cx") (.lit 0))

/-- The scalars the collapse assigns. -/
def SCO : List String := ["aa"]

/-- What the collapse reads. -/
structure ClEnv (B P k PK : ℕ) (σ : Env) : Prop where
  vPP : σ.vars "PP" = P
  vpk : σ.vars "pk" = P * k
  hPK : PK = P * (k + 1)
  hRK : PK ≤ (σ.arrs "R").length
  hRB : ∀ j, (σ.arrs "R").getD j 0 < B
  hPKB : PK + 8 < B

set_option maxHeartbeats 3200000 in
/-- **One cell of the collapse.** -/
theorem collBody_run {P k PK : ℕ} (σ : Env) (h : ClEnv B P k PK σ) (x : ℕ)
    (hx : σ.vars "cx" = x) (hxPK : x < PK) :
    ∃ σ', Run B collBody σ σ' 60 ∧
      σ'.arrs "R" = D3List.clStep P k x (σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ SCO → σ'.vars y = σ.vars y := by
  have hRK := h.hRK
  have hPKB := h.hPKB
  have hxB : x < B := by omega
  have hsx : MisBlk.small B σ (V "cx") := by show σ.vars "cx" < B; rw [hx]; exact hxB
  have hsP : MisBlk.small B σ (V "PP") := by
    show σ.vars "PP" < B; rw [h.vPP]
    have : P ≤ PK := by rw [h.hPK]; nlinarith [Nat.zero_le (P * k)]
    have := h.hPKB; omega
  by_cases hlt : x < P
  · have hT : (Cond.lt (V "cx") (V "PP")).evalB B σ = some true :=
      condLt_true _ _ σ hsx hsP (by show σ.vars "cx" < σ.vars "PP"; rw [hx, h.vPP]; exact hlt)
    have hxk : x + P * k < PK := by rw [h.hPK]; nlinarith
    have s1 := asg_R2 (B := B) "aa" "cx" "pk" σ x (P * k) hx h.vpk (by omega) (h.hRB _) (by omega)
      hxB (by have := h.hPKB; omega)
    set σ1 := σ.setVar "aa" ((σ.arrs "R").getD (x + P * k) 0) with hσ1
    have hcx1 : σ1.vars "cx" = x := by simp [hσ1, Env.setVar, hx]
    have haa1 : σ1.vars "aa" = (σ.arrs "R").getD (x + P * k) 0 := by simp [hσ1, Env.setVar]
    have hR1 : σ1.arrs "R" = σ.arrs "R" := by simp [hσ1, Env.setVar]
    have s2 := store_R (B := B) "cx" "aa" σ1 x _ hcx1 haa1 (by rw [hR1]; omega) hxB (h.hRB _)
    refine ⟨_, (Run.ite_true hT (s1.seq s2)).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_,
      fun y hy => ?_⟩
    · simp only [setArr_arrs_R, D3List.clStep, if_pos hlt]
      rw [hR1]
    · rw [setArr_arrs_ne _ _ _ _ _ (by decide)]; simp [hσ1, Env.setVar]
    · simp [hσ1, Env.setVar]
    · have : y ≠ "aa" := fun e => hy (by simp [SCO, e])
      simp [hσ1, Env.setVar, this]
  · have hF : (Cond.lt (V "cx") (V "PP")).evalB B σ = some false :=
      condLt_false _ _ σ hsx hsP (by show ¬ (σ.vars "cx" < σ.vars "PP"); rw [hx, h.vPP]; exact hlt)
    have s := store_R_lit (B := B) "cx" σ x 0 hx (by have := h.hRK; omega) hxB (by omega)
    refine ⟨_, (Run.ite_false hF s).mono (by simp [Cond.size, Expr.size]), ?_, ?_, ?_, fun y hy => ?_⟩
    · simp only [setArr_arrs_R, D3List.clStep, if_neg hlt]
    · rw [setArr_arrs_ne _ _ _ _ _ (by decide)]
    · rfl
    · rfl

/-- The collapse loop. -/
def collLoop : Com := fLoop "cx" "PK" collBody

set_option maxHeartbeats 6400000 in
/-- **The collapse of the table.** -/
theorem collLoop_run {P k PK : ℕ} (σ : Env) (h : ClEnv B P k PK σ) (hvPK : σ.vars "PK" = PK) :
    ∃ σ', Run B collLoop σ σ' ((60 + 10 + 4) * PK + 6) ∧
      σ'.arrs "R" = (List.range PK).foldl (fun A x => D3List.clStep P k x A) (σ.arrs "R") ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ "cx" :: SCO → σ'.vars y = σ.vars y := by
  set R0 := σ.arrs "R" with hR0
  have hlen : P * (k + 1) ≤ R0.length := by rw [← h.hPK]; exact h.hRK
  have hkeep : ∀ (σ' : Env), (σ'.vars "PP" = P) → (σ'.vars "pk" = P * k) →
      PK ≤ (σ'.arrs "R").length → (∀ j, (σ'.arrs "R").getD j 0 < B) →
      ClEnv B P k PK σ' := fun σ' a b c d =>
    ⟨a, b, h.hPK, c, d, h.hPKB⟩
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "cx" "PK" collBody
    (fun j σ' => ClEnv B P k PK σ' ∧
      σ'.arrs "R" = (List.range j).foldl (fun A x => D3List.clStep P k x A) R0 ∧
      σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ "cx" :: SCO → σ'.vars y = σ.vars y)
    60 PK σ hvPK (fun j σ' hq => by
      have := hq.2.2.2.2 "PK" (by simp [SCO]); rw [this]; exact hvPK) (by decide)
    (by have := h.hPKB; omega)
    ⟨hkeep _ (by simp [Env.setVar, h.vPP]) (by simp [Env.setVar, h.vpk])
        (by simpa [Env.setVar] using h.hRK) (fun j => by simpa [Env.setVar] using h.hRB j),
      by simp [Env.setVar, hR0], by simp [Env.setVar], by simp [Env.setVar], fun y hy => by
        have : y ≠ "cx" := fun e => hy (by simp [e])
        simp [Env.setVar, this]⟩
    (fun j σ' v hq => ⟨hkeep _ (by simpa [Env.setVar] using hq.1.vPP)
        (by simpa [Env.setVar] using hq.1.vpk) (by simpa [Env.setVar] using hq.1.hRK)
        (fun j => by simpa [Env.setVar] using hq.1.hRB j),
      by simpa [Env.setVar] using hq.2.1, by simpa [Env.setVar] using hq.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.1, fun y hy => by
        have : y ≠ "cx" := fun e => hy (by simp [e])
        simp only [Env.setVar, if_neg this]; exact hq.2.2.2.2 y hy⟩)
    (by
      intro j σ1 hq hjv hjn
      obtain ⟨hh1, hR1, hA1, hO1, hF1⟩ := hq
      obtain ⟨σ2, r2, hR2, hA2, hO2, hF2⟩ := collBody_run (B := B) σ1 hh1 j hjv hjn
      obtain ⟨hl2, hout2, hin2⟩ := D3List.clRun_inv P k R0 hlen (j + 1) (by rw [← h.hPK]; omega)
      have hR2' : σ2.arrs "R" = (List.range (j + 1)).foldl
          (fun A x => D3List.clStep P k x A) R0 := by
        rw [hR2, hR1, List.range_succ, List.foldl_append]; rfl
      refine ⟨σ2, r2, ⟨?_, hR2', by rw [hA2, hA1], by rw [hO2, hO1], fun z hz => ?_⟩, ?_⟩
      · refine hkeep _ ?_ ?_ ?_ ?_
        · rw [hF2 "PP" (by simp [SCO])]; exact hh1.vPP
        · rw [hF2 "pk" (by simp [SCO])]; exact hh1.vpk
        · rw [hR2', hl2]; exact h.hRK
        · intro y
          rw [hR2']
          by_cases hy : y < j + 1
          · rw [hin2 y hy]; split
            · exact h.hRB _
            · have := h.hPKB; omega
          · rw [hout2 y (by omega)]; exact h.hRB y
      · have hz' : z ∉ SCO := fun e => hz (List.mem_cons_of_mem _ e)
        rw [hF2 z hz']; exact hF1 z hz
      · rw [hF2 "cx" (by simp [SCO])]; exact hjv)
  obtain ⟨hh, hRfin, hAfin, hOfin, hFfin⟩ := hQ
  exact ⟨σ', r, hRfin, hAfin, hOfin, hFfin⟩

end Lax117284Proofs.Machine.D3Coll
