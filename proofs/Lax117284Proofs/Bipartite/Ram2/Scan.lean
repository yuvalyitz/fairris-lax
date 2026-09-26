import Lax117284Proofs.Bipartite.Ram2.Word

/-!
The row scan over compressed sparse rows: find the first slot `s` at or after the resume point of
the row of left vertex `i` whose target `a[3 + V + s]` names a right vertex `cand = target - n`
not yet visited — the machine-level version of the head of a vertex's candidate list.

The scan stops the instant it finds one (or reaches the end of the row, `xe = off (i + 1)`), so
that a frame resumed after its candidate's sub-search failed pays only for the *new* segment it
sweeps; resume points strictly increase, so a row is swept at most once per search.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- The `vis` array agrees with `visB`, for every right index below `m`. -/
def VisOK (visB : ℕ → Prop) (m : ℕ) (σ : Env) : Prop :=
  σ.arrs "vis" = arrOf m (fun j => if visB j then 1 else 0)

theorem VisOK.length {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) :
    (σ.arrs "vis").length = m := by rw [h]; simp

theorem VisOK.getD {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) {j : ℕ} (hj : j < m) :
    (σ.arrs "vis").getD j 0 = if visB j then 1 else 0 := by rw [h]; exact getD_arrOf _ hj

theorem VisOK.getD_lt {visB : ℕ → Prop} {m : ℕ} {σ : Env} (h : VisOK visB m σ) {j : ℕ}
    (hj : j < m) (hB : 1 < B) : (σ.arrs "vis").getD j 0 < B := by
  rw [h.getD hj]; split <;> omega

theorem VisOK.congr {visB : ℕ → Prop} {m : ℕ} {σ σ' : Env} (h : VisOK visB m σ)
    (ha : σ'.arrs "vis" = σ.arrs "vis") : VisOK visB m σ' := by unfold VisOK; rw [ha]; exact h

/-- Slots `[off l, p)` of row `l` all name visited right vertices. -/
def SlotsVis (x : List ℕ) (visB : ℕ → Prop) (l p : ℕ) : Prop :=
  ∀ s, offw x l ≤ s → s < p → ∀ j, tgtw x s = nw x + j → visB j

/-- **The scan invariant**: `x` has swept the slots `[off i, x)` of the row of `i`, and
`found`/`foundJ` summarize what that sweep saw — either every swept slot names a visited vertex,
or the last swept slot names the unvisited `foundJ` and every earlier one a visited vertex. -/
structure ScanInv (x : List ℕ) (visB : ℕ → Prop) (l : ℕ) (σ : Env) : Prop where
  i : σ.vars "i" = l
  xe : σ.vars "xe" = offw x (l + 1)
  V : σ.vars "V" = Vw x
  n : σ.vars "n" = nw x
  m : σ.vars "m" = mw x
  arr : ArrOK x σ
  vis : VisOK visB (mw x) σ
  xlo : offw x l ≤ σ.vars "x"
  xhi : σ.vars "x" ≤ offw x (l + 1)
  fle : σ.vars "found" ≤ 1
  fJ : σ.vars "foundJ" ≤ mw x
  cases : (σ.vars "found" = 0 ∧ SlotsVis x visB l (σ.vars "x")) ∨
    (σ.vars "found" = 1 ∧ offw x l < σ.vars "x" ∧
      tgtw x (σ.vars "x" - 1) = nw x + σ.vars "foundJ" ∧ ¬ visB (σ.vars "foundJ") ∧
      SlotsVis x visB l (σ.vars "x" - 1))

/-- The scalars the scan invariant reads. -/
def scanReads : List String := ["i", "xe", "V", "n", "m", "x", "found", "foundJ"]

theorem ScanInv.congr {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} {σ σ' : Env}
    (h : ScanInv x visB l σ) (hv : ∀ y ∈ scanReads, σ'.vars y = σ.vars y)
    (ha : σ'.arrs "a" = σ.arrs "a") (hvis : σ'.arrs "vis" = σ.arrs "vis") :
    ScanInv x visB l σ' := by
  have hi := hv "i" (by simp [scanReads])
  have hxe := hv "xe" (by simp [scanReads])
  have hV := hv "V" (by simp [scanReads])
  have hn := hv "n" (by simp [scanReads])
  have hm := hv "m" (by simp [scanReads])
  have hx := hv "x" (by simp [scanReads])
  have hf := hv "found" (by simp [scanReads])
  have hfJ := hv "foundJ" (by simp [scanReads])
  refine ⟨by rw [hi]; exact h.i, by rw [hxe]; exact h.xe, by rw [hV]; exact h.V,
    by rw [hn]; exact h.n, by rw [hm]; exact h.m, h.arr.congr ha, h.vis.congr hvis,
    by rw [hx]; exact h.xlo, by rw [hx]; exact h.xhi, by rw [hf]; exact h.fle,
    by rw [hfJ]; exact h.fJ, by rw [hx, hf, hfJ]; exact h.cases⟩

/-- Setting a scalar the invariant does not read keeps it. -/
theorem ScanInv.setVar {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} {σ : Env}
    (h : ScanInv x visB l σ) (y : String) (hy : y ∉ scanReads) (v : ℕ) :
    ScanInv x visB l (σ.setVar y v) :=
  h.congr (fun z hz => by
    simp only [vars_setVar]
    rw [if_neg]
    rintro rfl
    exact hy hz) rfl rfl

/-! ### One slot -/

/-- The candidate of the current slot: `a[3 + V + x] - n`. -/
def candExpr : Expr :=
  .sub (.get "a" (.add (.add (.lit 3) (.var "V")) (.var "x"))) (.var "n")

/-- One slot of the row: compute its candidate; if unvisited, record it; move on. -/
def scanBody : Com :=
  .seq (.assign "cand" candExpr)
    (.seq (.ite (.eq (.get "vis" (.var "cand")) (.lit 0))
        (.seq (.assign "foundJ" (.var "cand")) (.assign "found" (.lit 1)))
        .skip)
      (.assign "x" (.add (.var "x") (.lit 1))))

theorem candExpr_size : candExpr.size = 8 := by simp [candExpr]

/-- **One slot of the row, examined.** Only run with nothing found yet. -/
theorem scanBody_run {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hI : ScanInv x visB l σ)
    (hx : σ.vars "x" < offw x (l + 1)) (hf : σ.vars "found" = 0) :
    ∃ σ' K, Run B scanBody σ σ' K ∧ K ≤ 26 ∧ ScanInv x visB l σ' ∧
      σ'.vars "x" = σ.vars "x" + 1 := by
  have hV := hI.V
  have hn := hI.n
  have hxlo := hI.xlo
  have hsV : σ.vars "x" < offw x (Vw x) := hg.slot_lt hl hx
  have hpos : 3 + Vw x + σ.vars "x" < x.length := hg.tgtPos_lt hsV
  have hread : (σ.arrs "a").getD (3 + Vw x + σ.vars "x") 0 = tgtw x (σ.vars "x") :=
    hI.arr.getD_tgtw hg hsV
  have htB : tgtw x (σ.vars "x") < x.length := by unfold tgtw; exact hg.getD_lt _ hpos
  have hlenA : (σ.arrs "a").length = x.length := hI.arr.length
  have hcm : tgtw x (σ.vars "x") - nw x < mw x := hg.cand_lt hl hxlo hx
  have hce : tgtw x (σ.vars "x") = nw x + (tgtw x (σ.vars "x") - nw x) := hg.cand_eq hl hxlo hx
  set c := tgtw x (σ.vars "x") - nw x with hc
  have hVB : Vw x < B := by have := hg.V_lt; omega
  have hmB : mw x < B := by have := hg.m_lt; omega
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hxB : σ.vars "x" < B := by have := hg.off_lt_len (i := Vw x) le_rfl; omega
  -- evaluate `cand`
  have e1 : candExpr.evalB B σ = some c := by
    have h3 := RunStep.eval_lit B 3 σ (by omega)
    have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
      rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
    have hxe : (Expr.var "x").evalB B σ = some (σ.vars "x") := RunStep.eval_var B σ "x" hxB
    have hne : (Expr.var "n").evalB B σ = some (nw x) := by
      rw [← hn]; exact RunStep.eval_var B σ "n" (by omega)
    have h4 := RunStep.eval_add B σ _ _ _ _ h3 hVe (by omega)
    have h5 := RunStep.eval_add B σ _ _ _ _ h4 hxe (by omega)
    have h6 := RunStep.eval_get B σ "a" _ _ h5 (by omega) (by rw [hread]; omega)
    rw [hread] at h6
    exact RunStep.eval_sub B σ _ _ _ _ h6 hne (by omega)
  have r1 := RunStep.assign B σ "cand" candExpr c e1
  set σ₁ := σ.setVar "cand" c with hσ₁
  have hI₁ : ScanInv x visB l σ₁ := hI.setVar "cand" (by simp [scanReads]) c
  have hvisv : (σ₁.arrs "vis").getD c 0 = if visB c then 1 else 0 := hI₁.vis.getD hcm
  have hvislen : (σ₁.arrs "vis").length = mw x := hI₁.vis.length
  have hcand1 : σ₁.vars "cand" = c := by simp [hσ₁]
  have ecand : (Expr.var "cand").evalB B σ₁ = some c := by
    rw [← hcand1]; exact RunStep.eval_var B σ₁ "cand" (by rw [hcand1]; omega)
  have eget : (Expr.get "vis" (.var "cand")).evalB B σ₁ = some ((σ₁.arrs "vis").getD c 0) :=
    RunStep.eval_get B σ₁ "vis" _ c ecand (by omega) (hI₁.vis.getD_lt hcm (by omega))
  have e0 := RunStep.eval_lit B 0 σ₁ (by omega)
  have hx₁ : σ₁.vars "x" = σ.vars "x" := by simp [hσ₁]
  -- the increment of `x`, from any state agreeing with `σ` on `x`
  have einc : ∀ τ : Env, τ.vars "x" = σ.vars "x" →
      (Expr.add (.var "x") (.lit 1)).evalB B τ = some (σ.vars "x" + 1) := by
    intro τ hτ
    have := RunStep.eval_add B τ (.var "x") (.lit 1) (σ.vars "x") 1
      (by rw [← hτ]; exact RunStep.eval_var B τ "x" (by omega)) (RunStep.eval_lit B 1 τ (by omega))
      (by omega)
    exact this
  have hcases := hI.cases
  have hslots : SlotsVis x visB l (σ.vars "x") := by
    rcases hcases with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · omega
  by_cases hvc : visB c
  · -- the candidate is visited: nothing found, move on
    have hcond : (Cond.eq (.get "vis" (.var "cand")) (.lit 0)).evalB B σ₁ = some false :=
      RunStep.cond_eq_false B σ₁ _ _ _ 0 eget e0 (by rw [hvisv, if_pos hvc]; omega)
    have r2 := RunStep.ite_false B _
      (.seq (.assign "foundJ" (.var "cand")) (.assign "found" (.lit 1))) .skip σ₁ σ₁ 1 hcond
      (RunStep.skip B σ₁)
    have r4 := RunStep.assign B σ₁ "x" (.add (.var "x") (.lit 1)) (σ.vars "x" + 1) (einc σ₁ hx₁)
    refine ⟨σ₁.setVar "x" (σ.vars "x" + 1), _, r1.seq (r2.seq r4), ?_, ?_, by simp⟩
    · simp only [candExpr_size, size_condEq, size_get, size_var, size_lit, size_add]; omega
    · refine ⟨by simp [hσ₁]; exact hI.i, by simp [hσ₁]; exact hI.xe, by simp [hσ₁]; exact hI.V,
        by simp [hσ₁]; exact hI.n, by simp [hσ₁]; exact hI.m, hI.arr.congr (by simp [hσ₁]),
        hI.vis.congr (by simp [hσ₁]), by simp; omega, by simp; omega, by simp [hσ₁]; omega,
        by simp [hσ₁]; exact hI.fJ, ?_⟩
      left
      refine ⟨by simp [hσ₁]; exact hf, ?_⟩
      show SlotsVis x visB l (σ.vars "x" + 1)
      intro s hs1 hs2 j hj
      rcases Nat.lt_or_ge s (σ.vars "x") with h | h
      · exact hslots s hs1 h j hj
      · have : s = σ.vars "x" := by omega
        subst this
        have : j = c := by omega
        rw [this]; exact hvc
  · -- the candidate is fresh: record it
    have hcond : (Cond.eq (.get "vis" (.var "cand")) (.lit 0)).evalB B σ₁ = some true :=
      RunStep.cond_eq_true B σ₁ _ _ _ 0 eget e0 (by rw [hvisv, if_neg hvc])
    have r2 := RunStep.assign B σ₁ "foundJ" (.var "cand") c ecand
    set σ₂ := σ₁.setVar "foundJ" c with hσ₂
    have r3 := RunStep.assign B σ₂ "found" (.lit 1) 1 (RunStep.eval_lit B 1 σ₂ (by omega))
    set σ₃ := σ₂.setVar "found" 1 with hσ₃
    have rite := RunStep.ite_true B _ _ .skip σ₁ σ₃ _ hcond (r2.seq r3)
    have hx₃ : σ₃.vars "x" = σ.vars "x" := by simp [hσ₃, hσ₂, hσ₁]
    have r4 := RunStep.assign B σ₃ "x" (.add (.var "x") (.lit 1)) (σ.vars "x" + 1) (einc σ₃ hx₃)
    refine ⟨σ₃.setVar "x" (σ.vars "x" + 1), _, r1.seq (rite.seq r4), ?_, ?_, by simp⟩
    · simp only [candExpr_size, size_condEq, size_get, size_var, size_lit, size_add]; omega
    · refine ⟨by simp [hσ₃, hσ₂, hσ₁]; exact hI.i, by simp [hσ₃, hσ₂, hσ₁]; exact hI.xe,
        by simp [hσ₃, hσ₂, hσ₁]; exact hI.V, by simp [hσ₃, hσ₂, hσ₁]; exact hI.n,
        by simp [hσ₃, hσ₂, hσ₁]; exact hI.m, hI.arr.congr (by simp [hσ₃, hσ₂, hσ₁]),
        hI.vis.congr (by simp [hσ₃, hσ₂, hσ₁]), by simp; omega, by simp; omega,
        by simp [hσ₃, hσ₂, hσ₁], by simp [hσ₃, hσ₂, hσ₁]; omega, ?_⟩
      right
      refine ⟨by simp [hσ₃, hσ₂, hσ₁], by simp; omega, ?_, ?_, ?_⟩
      · simp [hσ₃, hσ₂, hσ₁]; exact hce
      · simp [hσ₃, hσ₂, hσ₁]; exact hvc
      · simp only [vars_setVar, ↓reduceIte, Nat.add_sub_cancel]
        exact hslots

/-! ### Early exit -/

/-- Whether the scan should keep going: `x` has not yet reached the end of the row, and nothing
has been found yet. `Cond` has no conjunction, so this is computed into a scalar. -/
def computeCont : Com :=
  .ite (.lt (.var "x") (.var "xe"))
    (.ite (.eq (.var "found") (.lit 0)) (.assign "cont" (.lit 1)) (.assign "cont" (.lit 0)))
    (.assign "cont" (.lit 0))

/-- **What `computeCont` computes**, walked by `run_vcg`. -/
theorem computeCont_run {σ : Env} (h1B : 1 < B) (hxB : σ.vars "x" < B)
    (hxeB : σ.vars "xe" < B) (hfB : σ.vars "found" < B) :
    ∃ σ' K, Run B computeCont σ σ' K ∧ K ≤ 10 ∧
      σ' = σ.setVar "cont" (if σ.vars "x" < σ.vars "xe" ∧ σ.vars "found" = 0 then 1 else 0) := by
  unfold computeCont
  run_vcg <;> (split_ifs with h <;> simp_all)

/-- **The row scan with early exit**: `cont := (x < xe ∧ found = 0); while cont = 1 do
(scanBody; cont := ...)`. -/
def scanRowEarly : Com :=
  .seq computeCont (.while (.eq (.var "cont") (.lit 1)) (.seq scanBody computeCont))

/-- The loop invariant of the early-exit scan. -/
def ScanLoopInv (x : List ℕ) (visB : ℕ → Prop) (l x₀ : ℕ) (σ : Env) : Prop :=
  ScanInv x visB l σ ∧
    σ.vars "cont" = (if σ.vars "x" < offw x (l + 1) ∧ σ.vars "found" = 0 then 1 else 0) ∧
    x₀ ≤ σ.vars "x"

/-- One turn of the early-exit loop moves `x` up by exactly one. -/
theorem scanLoop_step {x : List ℕ} {visB : ℕ → Prop} {l x₀ : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hJ : ScanLoopInv x visB l x₀ σ)
    (hcont : σ.vars "cont" = 1) :
    ∃ σ' K, Run B (.seq scanBody computeCont) σ σ' K ∧ K ≤ 36 ∧
      ScanLoopInv x visB l x₀ σ' ∧ σ'.vars "x" = σ.vars "x" + 1 := by
  obtain ⟨hI, hc, hx0⟩ := hJ
  have hxlt : σ.vars "x" < offw x (l + 1) ∧ σ.vars "found" = 0 := by
    by_contra h; simp [h] at hc; omega
  obtain ⟨σ₁, K₁, hrun1, hK1, hI1, hx1⟩ := scanBody_run hg hB hl hI hxlt.1 hxlt.2
  have hoffB : offw x (l + 1) < B := by
    have := hg.off_lt_len (i := l + 1) (by have := hg.nV; omega); omega
  have hxB1 : σ₁.vars "x" < B := by have := hI1.xhi; omega
  have hxeB1 : σ₁.vars "xe" < B := by rw [hI1.xe]; exact hoffB
  have hfB1 : σ₁.vars "found" < B := by have := hI1.fle; omega
  obtain ⟨σ₂, K₂, hrun2, hK2, hσ₂⟩ := computeCont_run (σ := σ₁) (by omega) hxB1 hxeB1 hfB1
  have hxe1 := hI1.xe
  refine ⟨σ₂, K₁ + K₂, hrun1.seq hrun2, by omega, ⟨?_, ?_, ?_⟩, ?_⟩
  · subst hσ₂; exact hI1.setVar "cont" (by simp [scanReads]) _
  · subst hσ₂; simp [hxe1]
  · subst hσ₂; simp; omega
  · subst hσ₂; simp; omega

/-- **The early-exit row scan, with segment-sensitive cost.** Started with `found = 0`, it stops
at the first fresh candidate at or after `x`, or at the end of the row; it costs `40` per slot
swept plus `14`; it changes only `cont`, `x`, `found`, `foundJ`, `cand`. -/
theorem scanRowEarly_run {x : List ℕ} {visB : ℕ → Prop} {l : ℕ} (hg : Good x)
    (hB : x.length + 8 ≤ B) (hl : l < nw x) {σ : Env} (hI : ScanInv x visB l σ)
    (hf : σ.vars "found" = 0) :
    ∃ σ' K, Run B scanRowEarly σ σ' K ∧ ScanInv x visB l σ' ∧
      (σ'.vars "x" = offw x (l + 1) ∨ σ'.vars "found" = 1) ∧
      σ.vars "x" ≤ σ'.vars "x" ∧ K + 40 * σ.vars "x" ≤ 40 * σ'.vars "x" + 14 ∧
      (∀ y, y ∉ ["cont", "x", "found", "foundJ", "cand"] → σ'.vars y = σ.vars y) ∧
      (∀ b, σ'.arrs b = σ.arrs b) := by
  have h1B : 1 < B := by omega
  have hoffB : offw x (l + 1) < B := by
    have := hg.off_lt_len (i := l + 1) (by have := hg.nV; omega); omega
  have hxB : σ.vars "x" < B := by have := hI.xhi; omega
  have hxeB : σ.vars "xe" < B := by rw [hI.xe]; exact hoffB
  have hfB : σ.vars "found" < B := by have := hI.fle; omega
  obtain ⟨σ₁, K₁, hrun1, hK1, hσ₁⟩ := computeCont_run (σ := σ) h1B hxB hxeB hfB
  have hxe := hI.xe
  have hJ₁ : ScanLoopInv x visB l (σ.vars "x") σ₁ := by
    subst hσ₁
    refine ⟨hI.setVar "cont" (by simp [scanReads]) _, ?_, ?_⟩
    · simp [hxe]
    · simp
  have hloop := Run.while_potential (B := B) (b := .eq (.var "cont") (.lit 1))
    (c := .seq scanBody computeCont) (ScanLoopInv x visB l (σ.vars "x"))
    (fun τ => 40 * (offw x (l + 1) - τ.vars "x"))
    (fun τ hτ => by
      have hcB : τ.vars "cont" < B := by rw [hτ.2.1]; split <;> omega
      exact ⟨_, evalB_condEq (evalB_var hcB) (evalB_lit (n := 1) h1B)⟩)
    (fun τ hτ hb => by
      have hcB : τ.vars "cont" < B := by rw [hτ.2.1]; split <;> omega
      have hbtrue : τ.vars "cont" = 1 := by
        have heq := evalB_condEq (evalB_var hcB) (evalB_lit (n := 1) h1B)
        rw [hb] at heq
        simpa using heq.symm
      obtain ⟨τ', K, hrun, hK, hJ', hx'⟩ := scanLoop_step hg hB hl hτ hbtrue
      have hxle : τ'.vars "x" ≤ offw x (l + 1) := hJ'.1.xhi
      refine ⟨τ', K, hrun, hJ', ?_⟩
      simp only [size_condEq, size_var, size_lit]
      omega) hJ₁
  obtain ⟨σ', K₂, hrun2, hJ', hfalse, hpay⟩ := hloop
  have hxle₀ : σ.vars "x" ≤ offw x (l + 1) := hI.xhi
  have hx₁ : σ₁.vars "x" = σ.vars "x" := by subst hσ₁; simp
  have hxle' : σ'.vars "x" ≤ offw x (l + 1) := hJ'.1.xhi
  refine ⟨σ', K₁ + K₂, hrun1.seq hrun2, hJ'.1, ?_, hJ'.2.2, ?_, ?_, ?_⟩
  · have hcB'' : σ'.vars "cont" < B := by rw [hJ'.2.1]; split <;> omega
    have hbfalse : σ'.vars "cont" ≠ 1 := by
      have heq := evalB_condEq (evalB_var hcB'') (evalB_lit (n := 1) h1B)
      rw [hfalse] at heq
      intro hc; rw [hc] at heq; simp at heq
    by_contra hcon
    push Not at hcon
    have hxlt : σ'.vars "x" < offw x (l + 1) := by omega
    have hfle : σ'.vars "found" ≤ 1 := hJ'.1.fle
    have hf0 : σ'.vars "found" = 0 := by omega
    exact hbfalse (by rw [hJ'.2.1]; simp [hxlt, hf0])
  · simp only [size_condEq, size_var, size_lit] at hpay
    rw [hx₁] at hpay
    omega
  · intro y hy
    have h1 := hrun1.frame_var y (fun h => hy (by
      simp [computeCont, Com.wvars] at h; simp; tauto))
    have h2 := hrun2.frame_var y (fun h => hy (by
      simp [Com.wvars, scanBody, computeCont] at h; simp; tauto))
    rw [h2, h1]
  · intro b
    have h1 := hrun1.frame_arr b (by simp [computeCont, Com.warrs])
    have h2 := hrun2.frame_arr b (by simp [Com.warrs, scanBody, computeCont])
    rw [h2, h1]

end Lax117284Proofs.Bipartite.Ram2
