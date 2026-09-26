import Lax117284Proofs.Bipartite.Ram2.Restart
import Lax117284Proofs.Bipartite.Ram2.OuterMath

/-!
The outer loop of Kuhn's algorithm: for each left vertex `l0 = 0, 1, …, n-1`, restart the search
and run it, then move on to the next left vertex whether the search succeeded or not. The loop's
invariant is `OuterMath.MatchInv` for the vertices processed so far.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The scalars the search may assign. -/
def searchVars : List String :=
  ["top", "result", "t1", "i", "x", "xe", "found", "foundJ", "cand", "occ", "k", "rr", "ll", "cont"]

theorem searchCom_wvars : ∀ y ∈ searchCom.wvars, y ∈ searchVars := by
  intro y hy
  simp [searchCom, turnCom, preludeCom, scanRowEarly, afterScanCom, popCom, foundCom, pushCom,
    applyCom, applyBodyCom, readMu, writeMu, computeCont, scanBody, Com.wvars] at hy
  simp only [searchVars, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem search_frame {σ σ' : Env} {K : ℕ} (h : Run B searchCom σ σ' K) {y : String}
    (hy : y ∉ searchVars) : σ'.vars y = σ.vars y :=
  h.frame_var y (fun hm => hy (searchCom_wvars y hm))

/-- One outer iteration: restart the search for `l0`, run it, advance. -/
def outerBody : Com :=
  .seq restartCom (.seq searchCom (.assign "l0" (.add (.var "l0") (.lit 1))))

/-- The outer loop over the left vertices. -/
def outerLoop : Com := .while (.lt (.var "l0") (.var "n")) outerBody

/-- The outer loop's invariant: the vertices below `l0` have been processed, and the realized
matching satisfies `MatchInv` for them. -/
def OuterInv (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "l0" ≤ nw x ∧ ∃ (μ : ℕ → Option ℕ) (b : AS), Real x μ b σ ∧
    MatchInv (adjw x) (nw x) (mw x) (σ.vars "l0") μ

theorem OuterInv.n {x : List ℕ} {σ : Env} (h : OuterInv x σ) : σ.vars "n" = nw x := by
  obtain ⟨-, μ, b, hR, -⟩ := h
  exact hR.n

/-- The cost of one outer iteration. -/
def iterCost (x : List ℕ) : ℕ := restartCost x + searchCost x + 8

section Iter

variable {x : List ℕ}

theorem Ctx.of_inv (hg : Good x) (hB : x.length + 8 ≤ B) {μ : ℕ → Option ℕ} {l : ℕ}
    (hl : l < nw x) (hM : MatchInv (adjw x) (nw x) (mw x) l μ) : Ctx B x μ l :=
  ⟨hg, hB, hl, hM.res, hM.inj, hM.unm, hM.hμn (by omega), hM.supp⟩

theorem outer_iter (hg : Good x) (hB : x.length + 8 ≤ B) {σ : Env} (hI : OuterInv x σ)
    (hlt : σ.vars "l0" < nw x) :
    ∃ σ' K, Run B outerBody σ σ' K ∧ OuterInv x σ' ∧ σ'.vars "l0" = σ.vars "l0" + 1 ∧
      K + 4 ≤ iterCost x := by
  obtain ⟨hl0le, μ, b, hR, hM⟩ := hI
  obtain ⟨σ₁, hr1, hR₁, hres₁, hfr₁⟩ := (restart_spec (μ := μ) (b := b) hg hB hlt).run ⟨hR, rfl⟩
  obtain ⟨σ₂, K₂, hr2, hK₂, hd⟩ := search_run_restart (Ctx.of_inv hg hB hlt hM) hR₁ hres₁
  have hfr₂ : ∀ y, y ∉ searchVars → y ≠ "top" → y ≠ "result" → y ≠ "j" →
      σ₂.vars y = σ.vars y := fun y h0 h1 h2 h3 => by rw [search_frame hr2 h0, hfr₁ y h1 h2 h3]
  have hl₂ : σ₂.vars "l0" = σ.vars "l0" := hfr₂ "l0" (by decide) (by decide) (by decide) (by decide)
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hl0B : σ.vars "l0" + 1 < B := by omega
  have r3 : Run B (.assign "l0" (.add (.var "l0") (.lit 1))) σ₂
      (σ₂.setVar "l0" (σ.vars "l0" + 1)) (1 + 3) := by
    have := RunStep.eval_add B σ₂ (.var "l0") (.lit 1) (σ.vars "l0") 1
      (by rw [← hl₂]; exact RunStep.eval_var B σ₂ "l0" (by omega))
      (RunStep.eval_lit B 1 σ₂ (by omega)) hl0B
    exact RunStep.assign B σ₂ "l0" _ _ this
  have e : (σ₂.setVar "l0" (σ.vars "l0" + 1)).vars "l0" = σ.vars "l0" + 1 := by simp
  refine ⟨σ₂.setVar "l0" (σ.vars "l0" + 1), _, hr1.seq (hr2.seq r3), ?_, e, ?_⟩
  · refine ⟨by rw [e]; omega, ?_⟩
    rcases hd with ⟨-, b', μ', hR', hg', hsupp'⟩ | ⟨-, b', hR', hF⟩
    · refine ⟨μ', b', hR'.setVar "l0" (by simp) _, ?_⟩
      rw [e]
      exact hM.succ_good hlt hg' hsupp'
    · refine ⟨μ, b', hR'.setVar "l0" (by simp) _, ?_⟩
      rw [e]
      exact hM.succ_fail hlt hF
  · unfold iterCost; omega

/-- **The outer loop, run to completion.** -/
theorem outerLoop_run (hg : Good x) (hB : x.length + 8 ≤ B) {σ : Env} (hI : OuterInv x σ) :
    ∃ σ' K, Run B outerLoop σ σ' K ∧ OuterInv x σ' ∧ σ'.vars "l0" = nw x ∧
      K ≤ iterCost x * (nw x - σ.vars "l0") + 4 := by
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hdef : ∀ τ, OuterInv x τ → ∃ v,
      (Cond.lt (.var "l0") (.var "n")).evalB B τ = some v := fun τ hτ =>
    evalB_condLt_vars (by have := hτ.1; omega) (by rw [hτ.n]; exact hnB)
  have hstep : ∀ τ, OuterInv x τ → (Cond.lt (.var "l0") (.var "n")).evalB B τ = some true →
      ∃ τ' K, Run B outerBody τ τ' K ∧ OuterInv x τ' ∧
        1 + (Cond.lt (.var "l0") (.var "n")).size + K + iterCost x * (nw x - τ'.vars "l0") ≤
          iterCost x * (nw x - τ.vars "l0") := by
    intro τ hτ hv
    have hlt : τ.vars "l0" < nw x := by
      have := lt_of_condLt_true hv
      rw [hτ.n] at this
      exact this
    obtain ⟨τ', K', hr, hI', hgt, hK⟩ := outer_iter hg hB hτ hlt
    refine ⟨τ', K', hr, hI', ?_⟩
    have hd : nw x - τ'.vars "l0" + 1 = nw x - τ.vars "l0" := by omega
    have := congrArg (iterCost x * ·) hd
    simp only [Nat.mul_add, Nat.mul_one] at this
    simp only [size_condLt, size_var]
    omega
  obtain ⟨σ', K, hrun, hI', hfalse, hpay⟩ := Run.while_potential (B := B)
    (b := .lt (.var "l0") (.var "n")) (c := outerBody) (OuterInv x)
    (fun τ => iterCost x * (nw x - τ.vars "l0")) hdef hstep hI
  refine ⟨σ', K, hrun, hI', ?_, by simp only [size_condLt, size_var] at hpay; omega⟩
  have := le_of_condLt_false (x := "l0") (y := "n") (by simpa using hfalse)
  have h2 := hI'.n
  have h3 := hI'.1
  omega

end Iter

end Lax117284Proofs.Bipartite.Ram2
