import Lax117284Proofs.Bipartite.Ram2.SearchTurn

/-!
The whole search loop: one turn (`turn_run`), a while rule whose potential is a function of a
*ghost* abstract state (`while_ghost`), and `search_run`, the loop-level specification; then the
cost of a search restarted from a fresh left vertex, linear in the word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

section Turn

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {a : AS} {σ : Env}

/-- The scan's precondition, for the pending frame, in the state the prelude leaves. -/
theorem scanInv_of_prelude (hR : Real x μ₀ a σ)
    (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) {σ₁ : Env}
    (hσ₁ : σ₁ = (((((σ.setVar "t1" (a.top - 1)).setVar "i" (a.Ls (a.top - 1))).setVar "x"
        (a.Xs (a.top - 1))).setVar "xe" (offw x (a.Ls (a.top - 1) + 1))).setVar "found" 0).setVar
        "foundJ" 0) :
    ScanInv x a.visB (a.Ls (a.top - 1)) σ₁ := by
  have hpos := hI.top_pos
  have hXlo := hI.Xlo (a.top - 1) (by omega)
  have hXhi := hI.Xhi (a.top - 1) (by omega)
  subst hσ₁
  refine ⟨by simp, by simp, by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), hR.vis.congr (by simp), by simpa using hXlo, by simpa using hXhi,
    by simp, by simp, ?_⟩
  left
  refine ⟨by simp, ?_⟩
  simp only [vars_setVar, String.reduceEq, ↓reduceIte]
  intro s hs1 hs2 j hj
  exact hI.Xcl (a.top - 1) (by omega) s hs1 hs2 j hj

/-- **One turn of the search**: a step of the loop, paying for itself out of the potential. -/
theorem turn_run (ctx : Ctx B x μ₀ l₀) (hR : Real x μ₀ a σ)
    (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) (hres : σ.vars "result" = 2) :
    ∃ a' σ' K, Run B turnCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hLn := hI.Lbd (a.top - 1) (by omega)
  obtain ⟨σ₁, hr1, hq1⟩ := (prelude_spec ctx (a := a)).run ⟨hR, hI⟩
  have hSI := scanInv_of_prelude hR hI hq1
  have hR₁ : Real x μ₀ a σ₁ := by
    subst hq1; exact hR.congr (by simp) (by simp) (by simp) (by simp) (by simp)
  have hf₁ : σ₁.vars "found" = 0 := by subst hq1; simp
  have hx₁ : σ₁.vars "x" = a.Xs (a.top - 1) := by subst hq1; simp
  obtain ⟨σ₂, K₂, hr2, hI₂, hstop, hxle, hK₂, hfv, hfa⟩ :=
    scanRowEarly_run (B := B) (visB := a.visB) hg hB hLn hSI hf₁
  have hres₁ : σ₁.vars "result" = 2 := by subst hq1; simpa using hres
  have ht1₁ : σ₁.vars "t1" + 1 = a.top := by subst hq1; simp; omega
  have hP : PostScan x μ₀ a σ₂ :=
    ⟨hR₁.congr (by rw [hfv "top" (by simp)]) (by rw [hfv "V" (by simp)])
      (by rw [hfv "n" (by simp)]) (by rw [hfv "m" (by simp)]) hfa,
      by rw [hfv "result" (by simp)]; exact hres₁,
      by rw [hfv "t1" (by simp)]; exact ht1₁, hI₂, hstop⟩
  have hfle : σ₂.vars "found" ≤ 1 := hI₂.fle
  rw [hx₁] at hK₂
  by_cases hf : σ₂.vars "found" = 0
  · have hx : σ₂.vars "x" = offw x (a.Ls (a.top - 1) + 1) := by rcases hstop with h | h <;> omega
    obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_pop ctx hI hP hf (K₀ := 20 + K₂) (by omega)
    exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩
  · have hf1 : σ₂.vars "found" = 1 := by omega
    have hK₀ : (20 + K₂) + 40 * a.Xs (a.top - 1) ≤ 40 * σ₂.vars "x" + 34 := by omega
    rcases hμ : μ₀ (σ₂.vars "foundJ") with _ | l'
    · obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_success ctx hI hP hf1 hμ hK₀
      exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩
    · obtain ⟨a', σ', K, hrA, hL, hK⟩ := turn_push ctx hI hP hf1 hμ hK₀
      exact ⟨a', σ', 20 + (K₂ + K), hr1.seq (hr2.seq hrA), hL, by omega⟩

end Turn

/-! ### The loop -/

/-- **The while rule, with a potential on a ghost state.** As `Run.while_potential`, but the
invariant and the potential range over an auxiliary ghost value carried along the run. -/
theorem while_ghost {G : Type*} {b : Cond} {c : Com} (I : G → Env → Prop) (Φ : G → ℕ)
    (hdef : ∀ g σ, I g σ → ∃ v, b.evalB B σ = some v)
    (hstep : ∀ g σ, I g σ → b.evalB B σ = some true →
      ∃ g' σ' K, Run B c σ σ' K ∧ I g' σ' ∧ 1 + b.size + K + Φ g' ≤ Φ g)
    {g : G} {σ : Env} (hI : I g σ) :
    ∃ g' σ' K, Run B (.while b c) σ σ' K ∧ I g' σ' ∧ b.evalB B σ' = some false ∧
      K + Φ g' ≤ Φ g + 1 + b.size := by
  suffices H : ∀ N (g : G) σ, I g σ → Φ g ≤ N →
      ∃ g' σ' K, Run B (.while b c) σ σ' K ∧ I g' σ' ∧ b.evalB B σ' = some false ∧
        K + Φ g' ≤ Φ g + 1 + b.size from H (Φ g) g σ hI le_rfl
  intro N
  induction N with
  | zero =>
      intro g σ hI hΦ
      obtain ⟨v, hv⟩ := hdef g σ hI
      cases v with
      | false => exact ⟨g, σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨g₁, σ₁, K, hrun, _, hpay⟩ := hstep g σ hI hv
          omega
  | succ N ih =>
      intro g σ hI hΦ
      obtain ⟨v, hv⟩ := hdef g σ hI
      cases v with
      | false => exact ⟨g, σ, _, Run.while_false hv, hI, hv, by omega⟩
      | true =>
          obtain ⟨g₁, σ₁, K, hrun, hI₁, hpay⟩ := hstep g σ hI hv
          obtain ⟨g', σ', K', hrun', hI', hfalse, hpay'⟩ := ih g₁ σ₁ hI₁ (by omega)
          obtain ⟨k, hk, hbs⟩ := hrun
          obtain ⟨k', hk', hbs'⟩ := hrun'
          exact ⟨g', σ', 1 + b.size + k + k', ⟨1 + b.size + k + k', le_rfl,
            .while_true hv hbs hbs'⟩, hI', hfalse, by omega⟩

section Loop

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ}

/-- **The search loop, run to completion.** From a well-formed state whose `result` is `2`, the
loop `while result = 2 do turn` halts within `pot a + 4` instructions in a state that has either
**succeeded** (`Done1`: `mu` holds a `GoodResult` for `l₀`) or **failed** (`Done0`: the visited
set is a `FailCert`). -/
theorem search_run (ctx : Ctx B x μ₀ l₀) {a : AS} {σ : Env}
    (hR : Real x μ₀ a σ) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hres : σ.vars "result" = 2) :
    ∃ σ' K, Run B searchCom σ σ' K ∧ K ≤ a.pot (offw x) μ₀ (mw x) + 4 ∧
      (Done1 x μ₀ l₀ σ' ∨ Done0 x μ₀ l₀ σ') := by
  have h3 : 3 < B := by have := ctx.hB; omega
  have hresB : ∀ (g : AS) (τ : Env), LoopInv x μ₀ l₀ g τ → τ.vars "result" < B := by
    intro g τ h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨g', σ', K, hrun, hL, hfalse, hpay⟩ := while_ghost (B := B)
    (b := .eq (.var "result") (.lit 2)) (c := turnCom) (LoopInv x μ₀ l₀)
    (fun g => g.pot (offw x) μ₀ (mw x))
    (fun g τ h => ⟨_, evalB_condEq (evalB_var (hresB g τ h)) (evalB_lit (n := 2) (by omega))⟩)
    (fun g τ h hb => by
      have hτ : τ.vars "result" = 2 := by
        have heq := evalB_condEq (evalB_var (hresB g τ h)) (evalB_lit (n := 2) (by omega))
        rw [hb] at heq
        simpa using heq.symm
      rcases h with ⟨-, hR', hI'⟩ | ⟨h1, -⟩ | ⟨h0, -⟩
      · obtain ⟨a', τ', K, hrun, hL, hK⟩ := turn_run ctx hR' hI' hτ
        refine ⟨a', τ', K, hrun, hL, ?_⟩
        simp only [size_condEq, size_var, size_lit]
        omega
      · omega
      · omega)
    (Or.inl ⟨hres, hR, hI⟩)
  refine ⟨σ', K, hrun, by simp only [size_condEq, size_var, size_lit] at hpay; omega, ?_⟩
  have hne : σ'.vars "result" ≠ 2 := by
    intro h2
    have heq := evalB_condEq (evalB_var (hresB g' σ' hL)) (evalB_lit (n := 2) (by omega))
    rw [hfalse, h2] at heq
    simp at heq
  rcases hL with ⟨h, -⟩ | h | h
  · omega
  · exact Or.inl h
  · exact Or.inr h

/-- The cost of one search, restarted from a fresh left vertex: linear in the word. -/
def searchCost (x : List ℕ) : ℕ := 80 * offw x (Vw x) + potD + potW * mw x + 4

/-- **A restarted search costs `O(|x|)`** — from any left-over stack arrays, with `top` reset
to `1`, `stkL[0] := l₀`, `stkX[0] := off l₀` and the visited table cleared. -/
theorem search_run_restart (ctx : Ctx B x μ₀ l₀) {b : AS} {σ : Env}
    (hR : Real x μ₀ (AS.restart (offw x) b l₀) σ) (hres : σ.vars "result" = 2) :
    ∃ σ' K, Run B searchCom σ σ' K ∧ K ≤ searchCost x ∧
      (Done1 x μ₀ l₀ σ' ∨ Done0 x μ₀ l₀ σ') := by
  have hg := ctx.good
  have hmono : offw x l₀ ≤ offw x (l₀ + 1) := hg.mono l₀ (by have := hg.nV; have := ctx.hl₀; omega)
  obtain ⟨σ', K, hrun, hK, hd⟩ := search_run ctx hR (AbsInv.restart b ctx.hl₀ hmono) hres
  have hpot := restart_pot_le (off := offw x) (μ₀ := μ₀) (n := nw x) (m := mw x) b l₀ ctx.inj
    ctx.hμn (fun l hl => hg.mono l (by have := hg.nV; omega)) (R := offw x (Vw x))
    (hg.off_le_last (nw x) hg.nV) (hg.rowlen_le ctx.hl₀)
  exact ⟨σ', K, hrun, by unfold searchCost; omega, hd⟩

end Loop

end Lax117284Proofs.Bipartite.Ram2
