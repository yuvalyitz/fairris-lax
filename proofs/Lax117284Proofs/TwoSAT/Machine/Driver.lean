import Lax117284Proofs.TwoSAT.Machine.Bfs
import Lax117284Proofs.TwoSAT.Machine.Width
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The driver: for every variable `x` below the index bound that occurs, a search from the
positive literal `2x + 1`; if it reaches the negative literal `2x`, a search from `2x`; if
that reaches `2x + 1`, the variable is contradictory and the answer is `0`.

The cost is paid out of a potential that charges every variable a constant and every
*occurring* variable two searches, so that the loop costs `O(mx + v · (N + E))` where `v` is the
number of variables that occur — the bound the concept states.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Driver

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Width Lax117284Proofs.TwoSAT.Machine.Bfs
open scoped Classical

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- The second search, from the negative literal, and the verdict. -/
def secondCom : Com :=
  .seq (.assign "s" (.mul (.lit 2) (V "x")))
    (.seq bfs
      (.seq (.assign "r" (.get "vis" (.add (.mul (.lit 2) (V "x")) (.lit 1))))
        (.ite (.eq (V "r") (.lit 1)) (.assign "ans" (.lit 0)) .skip)))

/-- The searches of one occurring variable. -/
def searchesCom : Com :=
  .seq (.assign "s" (.add (.mul (.lit 2) (V "x")) (.lit 1)))
    (.seq bfs
      (.seq (.assign "r" (.get "vis" (.mul (.lit 2) (V "x"))))
        (.ite (.eq (V "r") (.lit 1)) secondCom .skip)))

/-- One variable: the searches if it occurs, then on to the next. -/
def varBody : Com :=
  .seq (.assign "o" (.get "occ" (V "x")))
    (.seq (.ite (.eq (V "o") (.lit 1)) searchesCom .skip) (bump "x"))

/-- The driver: every variable below the bound, then the answer. -/
def driver : Com :=
  .seq (.assign "ans" (.lit 1))
    (.seq (.assign "x" (.lit 0)) (.seq (.while (.lt (V "x") (V "mx")) varBody) (.write (V "ans"))))

/-! ### The invariant -/

variable (F : Formula) (y : List ℕ) (off tgt : ℕ → ℕ)

/-- The graph in memory is the implication graph. -/
def Graph (σ : Env) : Prop :=
  Csr "off" "tgt" (N F) (edges F).length (N F) off tgt σ ∧
    ∀ u v, Succ off tgt u v ↔ E F u v

/-- Reachability in the stored graph is reachability in the implication graph. -/
theorem reach_iff (h : ∀ u v, Succ off tgt u v ↔ E F u v) (s v : ℕ) :
    Reach off tgt s v ↔ RT F s v := by
  have : Succ off tgt = E F := by funext a b; exact propext (h a b)
  unfold Reach RT; rw [this]

/-- The invariant of the loop over the variables. -/
structure Core (σ : Env) : Prop where
  graph : Graph F off tgt σ
  hN : σ.vars "N" = N F
  mx : σ.vars "mx" = mxOf (lits F)
  x : σ.vars "x" ≤ mxOf (lits F)
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occF F)
  lvis : (σ.arrs "vis").length = N F
  lq : (σ.arrs "q").length = N F
  hmx : mxOf (lits F) ≤ y.length + 1
  out : σ.out = []

/-- The invariant of the loop: the core, and the answer so far. -/
structure Inv (σ : Env) : Prop where
  core : Core F y off tgt σ
  ans1 : σ.vars "ans" ≤ 1
  ans : σ.vars "ans" = 1 ↔ ∀ x' < σ.vars "x", x' ∈ vars F → ¬ Bad F x'

/-- The cost of one search. -/
def Ks : ℕ := Kbfs * (N F + (edges F).length + 1)

/-- The potential: a constant per variable left, and two searches per occurring variable
left. -/
def Pot (σ : Env) : ℕ :=
  60 * (mxOf (lits F) - σ.vars "x") +
    (2 * Ks F + 40) * ((Finset.Ico (σ.vars "x") (mxOf (lits F))).filter (· ∈ vars F)).card

theorem pot_zero_le : ∀ σ, σ.vars "x" = 0 →
    Pot F σ ≤ 60 * mxOf (lits F) + (2 * Ks F + 40) * varCount F := by
  intro σ hx
  unfold Pot; rw [hx]
  refine Nat.add_le_add (by simp) (Nat.mul_le_mul_left _ ?_)
  unfold varCount
  apply Finset.card_le_card
  intro x hx; simp only [Finset.mem_filter] at hx; exact hx.2

theorem pot_step (σ : Env) (hlt : σ.vars "x" < mxOf (lits F)) :
    Pot F σ = 60 + (if σ.vars "x" ∈ vars F then 2 * Ks F + 40 else 0) +
      (60 * (mxOf (lits F) - (σ.vars "x" + 1)) +
        (2 * Ks F + 40) * ((Finset.Ico (σ.vars "x" + 1) (mxOf (lits F))).filter (· ∈ vars F)).card) := by
  unfold Pot
  have hsplit : Finset.Ico (σ.vars "x") (mxOf (lits F)) =
      insert (σ.vars "x") (Finset.Ico (σ.vars "x" + 1) (mxOf (lits F))) := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [hsplit, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem (by simp)]
    have : mxOf (lits F) - σ.vars "x" = (mxOf (lits F) - (σ.vars "x" + 1)) + 1 := by omega
    rw [this]; ring
  · have : mxOf (lits F) - σ.vars "x" = (mxOf (lits F) - (σ.vars "x" + 1)) + 1 := by omega
    rw [this]; ring

/-! ### The searches -/

variable {B : ℕ}

lemma bfs_noWrite : bfs.NoWrite := by
  simp [bfs, clear, initDrain, drain, expandBody, scanBody, Com.NoWrite]

lemma mem_wvars_bfs {z : String} (hz : z ∈ bfs.wvars) :
    z ∈ ["i", "head", "tail", "u", "j", "jend", "v"] := by
  simp only [bfs, clear, initDrain, drain, expandBody, scanBody, Com.wvars, List.mem_append,
    List.mem_cons, List.not_mem_nil] at hz ⊢
  tauto

lemma mem_warrs_bfs {a : String} (ha : a ∈ bfs.warrs) : a ∈ ["vis", "q"] := by
  simp only [bfs, clear, initDrain, drain, expandBody, scanBody, Com.warrs, List.mem_append,
    List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

/-- The search from whatever `s` holds, relationally. -/
theorem bfsAny_spec (hB : N F + (edges F).length + 16 < B) :
    Spec B (fun σ => Graph F off tgt σ ∧ σ.vars "N" = N F ∧ σ.vars "s" < N F ∧
        (σ.arrs "vis").length = N F ∧ (σ.arrs "q").length = N F)
      bfs
      (fun σ σ' => σ'.arrs "vis" = arrOf (N F) (fun v => if RT F (σ.vars "s") v then 1 else 0) ∧
        Graph F off tgt σ' ∧ σ'.vars "N" = N F ∧ σ'.vars "s" = σ.vars "s" ∧
        (σ'.arrs "q").length = N F ∧ (σ'.arrs "vis").length = N F ∧
        (∀ z, z ∉ bfs.wvars → σ'.vars z = σ.vars z) ∧
        (∀ a, a ∉ bfs.warrs → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out)
      (Ks F) := by
  intro σ hσ
  obtain ⟨σ', hr, ⟨hvis, hcsr, hN, hs, hq⟩, fv, fa, -, hout⟩ :=
    (bfs_spec (B := B) (N F) (edges F).length (σ.vars "s") off tgt hσ.2.2.1 hB).frame.run
      ⟨hσ.1.1, hσ.2.1, rfl, hσ.2.2.2.1, hσ.2.2.2.2⟩
  refine ⟨σ', hr, ?_, ⟨hcsr, hσ.1.2⟩, hN, hs, hq, by rw [hvis]; simp, fv, fa,
    hout bfs_noWrite⟩
  rw [hvis]
  exact arrOf_congr fun v _ => by rw [reach_iff F off tgt hσ.1.2]

/-- What the searches of one variable leave. -/
def SPost (σ σ' : Env) : Prop :=
  Core F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" ∧ σ'.vars "ans" ≤ 1 ∧
    (σ'.vars "ans" = 1 ↔ σ.vars "ans" = 1 ∧ ¬ Bad F (σ.vars "x"))

theorem core_of_bfs {σ σ' : Env} (hc : Core F y off tgt σ) (s : ℕ)
    (h : σ'.arrs "vis" = arrOf (N F) (fun v => if RT F s v then 1 else 0) ∧
      Graph F off tgt σ' ∧ σ'.vars "N" = N F ∧ σ'.vars "s" = s ∧
      (σ'.arrs "q").length = N F ∧ (σ'.arrs "vis").length = N F ∧
      (∀ z, z ∉ bfs.wvars → σ'.vars z = σ.vars z) ∧
      (∀ a, a ∉ bfs.warrs → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out) :
    Core F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" ∧ σ'.vars "ans" = σ.vars "ans" ∧
      σ'.vars "mx" = σ.vars "mx" := by
  obtain ⟨-, hg, hN, -, hq, hvis, fv, fa, hout⟩ := h
  have hx : σ'.vars "x" = σ.vars "x" :=
    fv "x" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  have hans : σ'.vars "ans" = σ.vars "ans" :=
    fv "ans" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  have hmx : σ'.vars "mx" = σ.vars "mx" :=
    fv "mx" (fun hm => by have := mem_wvars_bfs hm; simp at this)
  refine ⟨⟨hg, hN, by rw [hmx]; exact hc.mx, by rw [hx]; exact hc.x, ?_, hvis, hq, hc.hmx,
    by rw [hout]; exact hc.out⟩, hx, hans, hmx⟩
  rw [fa "occ" (fun hm => by have := mem_warrs_bfs hm; simp at this)]
  exact hc.occ

theorem two_mul_lt {x : ℕ} (hx : x < mxOf (lits F)) : 2 * x + 1 < N F := by
  unfold N; omega

theorem vis_read (s v : ℕ) (hv : v < N F) {σ : Env}
    (h : σ.arrs "vis" = arrOf (N F) (fun v => if RT F s v then 1 else 0)) :
    (σ.arrs "vis").getD v 0 = if RT F s v then 1 else 0 := by
  rw [h, getD_arrOf _ hv]

variable {F y off tgt} in
theorem Core.setVar {σ : Env} (hc : Core F y off tgt σ) (z : String)
    (hz : z ≠ "N" ∧ z ≠ "mx" ∧ z ≠ "x") (v : ℕ) : Core F y off tgt (σ.setVar z v) := by
  obtain ⟨hz1, hz2, hz3⟩ := hz
  refine ⟨⟨?_, hc.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
  · simpa using hc.graph.1
  · simp [hz1.symm]; exact hc.hN
  · simp [hz2.symm]; exact hc.mx
  · simp [hz3.symm]; exact hc.x
  · simpa using hc.occ
  · simpa using hc.lvis
  · simpa using hc.lq
  · simpa using hc.out

/-! #### The atomic steps -/

theorem assign_s1_run {σ : Env} (hxB : 2 * σ.vars "x" + 1 < B) (h2B : 2 < B) :
    Run B (.assign "s" (.add (.mul (.lit 2) (V "x")) (.lit 1))) σ
      (σ.setVar "s" (2 * σ.vars "x" + 1)) 6 := by
  have e1 : (Expr.mul (.lit 2) (V "x")).evalB B σ = some (2 * σ.vars "x") := by
    have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
      (evalB_var (x := "x") (by omega)) (by show 2 * σ.vars "x" < B; omega)
    simpa [Bop.apply] using this
  have e2 : (Expr.add (.mul (.lit 2) (V "x")) (.lit 1)).evalB B σ =
      some (2 * σ.vars "x" + 1) := by
    have := evalB_bin (op := .add) e1 (evalB_lit (B := B) (σ := σ) (n := 1) (by omega))
      (by show 2 * σ.vars "x" + 1 < B; omega)
    simpa [Bop.apply] using this
  exact (Run.assign e2).mono (by simp)

theorem assign_s0_run {σ : Env} (hxB : 2 * σ.vars "x" + 1 < B) (h2B : 2 < B) :
    Run B (.assign "s" (.mul (.lit 2) (V "x"))) σ (σ.setVar "s" (2 * σ.vars "x")) 4 := by
  have e1 : (Expr.mul (.lit 2) (V "x")).evalB B σ = some (2 * σ.vars "x") := by
    have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ) (n := 2) (by omega))
      (evalB_var (x := "x") (by omega)) (by show 2 * σ.vars "x" < B; omega)
    simpa [Bop.apply] using this
  exact (Run.assign e1).mono (by simp)

theorem read_r_run {σ : Env} {e : Expr} {idx : ℕ} (he : e.evalB B σ = some idx)
    (hidx : idx < (σ.arrs "vis").length) (hv : (σ.arrs "vis").getD idx 0 < B) :
    Run B (.assign "r" (.get "vis" e)) σ (σ.setVar "r" ((σ.arrs "vis").getD idx 0))
      (e.size + 2) := by
  refine (Run.assign (evalB_get he ?_ hv)).mono (by simp; omega)
  rw [List.getD_eq_getElem _ _ hidx, List.getElem?_eq_getElem hidx]

theorem cond_r_true {σ : Env} (hr : σ.vars "r" = 1) (h1 : 1 < B) :
    (Cond.eq (V "r") (.lit 1)).evalB B σ = some true := by
  rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1), hr]; rfl

theorem cond_r_false {σ : Env} (hr : σ.vars "r" = 0) (h1 : 1 < B) :
    (Cond.eq (V "r") (.lit 1)).evalB B σ = some false := by
  rw [evalB_condEq (evalB_var (by omega)) (evalB_lit h1), hr]; rfl

/-- **The searches of one occurring variable.** -/
theorem searches_spec (hB : N F + (edges F).length + 16 < B) :
    Spec B (fun σ => Core F y off tgt σ ∧ σ.vars "x" < mxOf (lits F) ∧ σ.vars "ans" ≤ 1)
      searchesCom (SPost F y off tgt) (2 * Ks F + 40) := by
  intro σ ⟨hc, hlt, hans⟩
  have hNB : N F < B := by omega
  have h1B : 1 < B := by omega
  have h2x : 2 * σ.vars "x" + 1 < N F := two_mul_lt F hlt
  set x := σ.vars "x" with hxdef
  -- s := 2x + 1
  have h2B : 2 < B := by omega
  have r1 := assign_s1_run (B := B) (σ := σ) (by omega) h2B
  set σ1 := σ.setVar "s" (2 * x + 1) with hσ1
  have hc1 : Core F y off tgt σ1 := hc.setVar "s" (by decide) _
  have hs1 : σ1.vars "s" = 2 * x + 1 := by rw [hσ1]; simp
  -- the first search
  obtain ⟨σ2, r2, h2⟩ := (bfsAny_spec F off tgt hB).run (σ := σ1)
    ⟨hc1.graph, hc1.hN, by rw [hs1]; exact h2x, hc1.lvis, hc1.lq⟩
  rw [hs1] at h2
  obtain ⟨hc2, hx2, hans2, -⟩ := core_of_bfs F y off tgt hc1 _ h2
  have hx2' : σ2.vars "x" = x := by rw [hx2, hσ1]; simp [← hxdef]
  have hans2' : σ2.vars "ans" = σ.vars "ans" := by rw [hans2, hσ1]; simp
  have hvis2 := h2.1
  -- r := vis[2x]
  have hv1 : (σ2.arrs "vis").getD (2 * x) 0 = if RT F (2 * x + 1) (2 * x) then 1 else 0 :=
    vis_read F (2 * x + 1) (2 * x) (by omega) hvis2
  have r3 := read_r_run (B := B) (σ := σ2) (e := .mul (.lit 2) (V "x")) (idx := 2 * x)
    (by
      have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ2) (n := 2) (by omega))
        (evalB_var (x := "x") (by rw [hx2']; omega)) (by rw [hx2']; show 2 * x < B; omega)
      simpa [Bop.apply, hx2'] using this)
    (by rw [hc2.lvis]; omega) (by rw [hv1]; split <;> omega)
  set σ3 := σ2.setVar "r" ((σ2.arrs "vis").getD (2 * x) 0) with hσ3
  have hc3 : Core F y off tgt σ3 := hc2.setVar "r" (by decide) _
  have hx3 : σ3.vars "x" = x := by simp [hσ3, hx2']
  have hans3 : σ3.vars "ans" = σ.vars "ans" := by simp [hσ3, hans2']
  have hr3 : σ3.vars "r" = if RT F (2 * x + 1) (2 * x) then 1 else 0 := by
    rw [hσ3]; simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hv1
  by_cases hA : RT F (2 * x + 1) (2 * x)
  · -- the negative literal is reached: the second search
    have hr3' : σ3.vars "r" = 1 := by rw [hr3, if_pos hA]
    have r4 := assign_s0_run (B := B) (σ := σ3) (by rw [hx3]; omega) h2B
    set σ4 := σ3.setVar "s" (2 * σ3.vars "x") with hσ4
    have hc4 : Core F y off tgt σ4 := hc3.setVar "s" (by decide) _
    have hs4 : σ4.vars "s" = 2 * x := by rw [hσ4]; simp [hx3]
    obtain ⟨σ5, r5, h5⟩ := (bfsAny_spec F off tgt hB).run (σ := σ4)
      ⟨hc4.graph, hc4.hN, by rw [hs4]; omega, hc4.lvis, hc4.lq⟩
    rw [hs4] at h5
    obtain ⟨hc5, hx5, hans5, -⟩ := core_of_bfs F y off tgt hc4 _ h5
    have hx5' : σ5.vars "x" = x := by rw [hx5, hσ4]; simp [hx3]
    have hans5' : σ5.vars "ans" = σ.vars "ans" := by rw [hans5, hσ4]; simp [hans3]
    have hv2 : (σ5.arrs "vis").getD (2 * x + 1) 0 =
        if RT F (2 * x) (2 * x + 1) then 1 else 0 :=
      vis_read F (2 * x) (2 * x + 1) (by omega) h5.1
    have r6 := read_r_run (B := B) (σ := σ5) (e := .add (.mul (.lit 2) (V "x")) (.lit 1))
      (idx := 2 * x + 1)
      (by
        have e1 := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ5) (n := 2) (by omega))
          (evalB_var (x := "x") (by rw [hx5']; omega)) (by rw [hx5']; show 2 * x < B; omega)
        have := evalB_bin (op := .add) e1 (evalB_lit (B := B) (σ := σ5) (n := 1) (by omega))
          (by rw [hx5']; show 2 * x + 1 < B; omega)
        simpa [Bop.apply, hx5'] using this)
      (by rw [hc5.lvis]; omega) (by rw [hv2]; split <;> omega)
    set σ6 := σ5.setVar "r" ((σ5.arrs "vis").getD (2 * x + 1) 0) with hσ6
    have hc6 : Core F y off tgt σ6 := hc5.setVar "r" (by decide) _
    have hx6 : σ6.vars "x" = x := by simp [hσ6, hx5']
    have hans6 : σ6.vars "ans" = σ.vars "ans" := by simp [hσ6, hans5']
    have hr6 : σ6.vars "r" = if RT F (2 * x) (2 * x + 1) then 1 else 0 := by
      rw [hσ6]; simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hv2
    by_cases hA2 : RT F (2 * x) (2 * x + 1)
    · -- contradictory: the answer is no
      have hr6' : σ6.vars "r" = 1 := by rw [hr6, if_pos hA2]
      have r7 : Run B (.assign "ans" (.lit 0)) σ6 (σ6.setVar "ans" 0) 2 :=
        Run.assign (evalB_lit (by omega))
      have run : Run B searchesCom σ (σ6.setVar "ans" 0)
          (6 + (Ks F + (5 + (1 + 3 + (4 + (Ks F + (7 + (1 + 3 + 2)))))))) := by
        refine r1.seq (r2.seq (r3.seq (Run.ite_true (cond_r_true hr3' h1B)
          (r4.seq (r5.seq (r6.seq (Run.ite_true (cond_r_true hr6' h1B) r7)))))))
      refine ⟨_, run.mono (by omega), hc6.setVar "ans" (by decide) _,
        by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact hx6, by simp, ?_⟩
      simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      constructor
      · intro h; omega
      · rintro ⟨-, hb⟩; exact absurd ⟨hA, hA2⟩ hb
    · -- not contradictory
      have hr6' : σ6.vars "r" = 0 := by rw [hr6, if_neg hA2]
      have run : Run B searchesCom σ σ6
          (6 + (Ks F + (5 + (1 + 3 + (4 + (Ks F + (7 + (1 + 3 + 1)))))))) := by
        refine r1.seq (r2.seq (r3.seq (Run.ite_true (cond_r_true hr3' h1B)
          (r4.seq (r5.seq (r6.seq (Run.ite_false (cond_r_false hr6' h1B) Run.skip)))))))
      refine ⟨_, run.mono (by omega), hc6, hx6, by rw [hans6]; exact hans, ?_⟩
      rw [hans6]
      constructor
      · intro h; exact ⟨h, fun hb => hA2 hb.2⟩
      · exact fun h => h.1
  · -- the negative literal is not reached
    have hr3' : σ3.vars "r" = 0 := by rw [hr3, if_neg hA]
    have run : Run B searchesCom σ σ3 (6 + (Ks F + (5 + (1 + 3 + 1)))) :=
      r1.seq (r2.seq (r3.seq (Run.ite_false (cond_r_false hr3' h1B) Run.skip)))
    refine ⟨_, run.mono (by omega), hc3, hx3, by rw [hans3]; exact hans, ?_⟩
    rw [hans3]
    constructor
    · intro h; exact ⟨h, fun hb => hA hb.1⟩
    · exact fun h => h.1

/-! ### One variable -/

variable {F y off tgt} in
theorem Core.bumpX {σ : Env} (hc : Core F y off tgt σ) (h : σ.vars "x" + 1 ≤ mxOf (lits F)) :
    Core F y off tgt (σ.setVar "x" (σ.vars "x" + 1)) := by
  refine ⟨⟨?_, hc.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
  · simpa using hc.graph.1
  · simp; exact hc.hN
  · simp; exact hc.mx
  · simp; exact h
  · simpa using hc.occ
  · simpa using hc.lvis
  · simpa using hc.lq
  · simpa using hc.out

theorem mem_vars_lt {x : ℕ} (hx : x ∈ vars F) : x < mxOf (lits F) := by
  obtain ⟨j, hj, rfl⟩ := (mem_vars_iff F x).1 hx
  have := iv_lt F j hj; omega

/-- **One variable.** The cost is a constant, plus two searches if the variable occurs. -/
theorem varBody_run (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B)
    {σ : Env} (hI : Inv F y off tgt σ) (hlt : σ.vars "x" < mxOf (lits F)) :
    ∃ σ' K, Run B varBody σ σ' K ∧ Inv F y off tgt σ' ∧ σ'.vars "x" = σ.vars "x" + 1 ∧
      K ≤ 12 + (if σ.vars "x" ∈ vars F then 2 * Ks F + 40 else 0) := by
  have hc := hI.core
  have hmx := hc.hmx
  have hxB : σ.vars "x" < B := by omega
  have h1B : 1 < B := by omega
  -- o := occ[x]
  have hocc : (σ.arrs "occ")[σ.vars "x"]? = some (occF F (σ.vars "x")) := by
    rw [hc.occ, getElem?_arrOf _ (by omega)]
  have hoccB : occF F (σ.vars "x") < B := by unfold occF; split <;> omega
  have r1 : Run B (.assign "o" (.get "occ" (V "x"))) σ (σ.setVar "o" (occF F (σ.vars "x"))) 3 :=
    (Run.assign (evalB_get (evalB_var hxB) hocc hoccB)).mono (by simp)
  set σ1 := σ.setVar "o" (occF F (σ.vars "x")) with hσ1
  have hc1 : Core F y off tgt σ1 := hc.setVar "o" (by decide) _
  have hx1 : σ1.vars "x" = σ.vars "x" := by simp [hσ1]
  have hans1 : σ1.vars "ans" = σ.vars "ans" := by simp [hσ1]
  have ho1 : σ1.vars "o" = occF F (σ.vars "x") := by simp [hσ1]
  have hcond : (Cond.eq (V "o") (.lit 1)).evalB B σ1 = some (occF F (σ.vars "x") == 1) := by
    rw [evalB_condEq (evalB_var (by rw [ho1]; exact hoccB)) (evalB_lit h1B), ho1]
  -- the bump, from any state with the right `x`
  have bump_run : ∀ τ : Env, τ.vars "x" = σ.vars "x" →
      Run B (bump "x") τ (τ.setVar "x" (σ.vars "x" + 1)) 4 := by
    intro τ hτ
    have := evalB_bin (op := .add) (evalB_var (B := B) (x := "x") (σ := τ) (by omega))
      (evalB_lit (B := B) (n := 1) (by omega)) (by rw [hτ]; show σ.vars "x" + 1 < B; omega)
    rw [hτ] at this
    exact (Run.assign (by simpa [Bop.apply] using this)).mono (by simp)
  by_cases hv : σ.vars "x" ∈ vars F
  · -- the variable occurs: the searches
    have hocc1 : occF F (σ.vars "x") = 1 := by unfold occF; rw [if_pos hv]
    rw [hocc1] at hcond
    obtain ⟨σ2, r2, hc2, hx2, hans2, hiff⟩ := (searches_spec F y off tgt hB).run (σ := σ1)
      ⟨hc1, by rw [hx1]; exact hlt, by rw [hans1]; exact hI.ans1⟩
    rw [hx1] at hx2 hiff; rw [hans1] at hiff
    have r3 := bump_run σ2 hx2
    refine ⟨_, _, r1.seq ((Run.ite_true hcond r2).seq r3), ?_, by simp, by rw [if_pos hv]; simp; omega⟩
    have hcb := hc2.bumpX (by rw [hx2]; omega)
    rw [hx2] at hcb
    refine ⟨hcb, by simp; exact hans2, ?_⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hiff, hI.ans]
    constructor
    · rintro ⟨h1, h2⟩ x' hx' hx'v
      rcases Nat.lt_or_ge x' (σ.vars "x") with h | h
      · exact h1 x' h hx'v
      · have : x' = σ.vars "x" := by omega
        subst this; exact h2
    · intro h
      exact ⟨fun x' hx' hx'v => h x' (by omega) hx'v, h _ (by omega) hv⟩
  · -- the variable does not occur
    have hocc0 : occF F (σ.vars "x") = 0 := by unfold occF; rw [if_neg hv]
    rw [hocc0] at hcond
    have r3 := bump_run σ1 hx1
    refine ⟨_, _, r1.seq ((Run.ite_false hcond Run.skip).seq r3), ?_, by simp, by rw [if_neg hv]; simp⟩
    have hcb := hc1.bumpX (by rw [hx1]; omega)
    rw [hx1] at hcb
    refine ⟨hcb, by simp; rw [hans1]; exact hI.ans1, ?_⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hans1, hI.ans]
    constructor
    · intro h1 x' hx' hx'v
      rcases Nat.lt_or_ge x' (σ.vars "x") with h | h
      · exact h1 x' h hx'v
      · have : x' = σ.vars "x" := by omega
        subst this; exact absurd hx'v hv
    · intro h x' hx' hx'v; exact h x' (by omega) hx'v

/-! ### The loop -/

/-- The cost of the loop over the variables. -/
def Kloop : ℕ := 60 * mxOf (lits F) + (2 * Ks F + 40) * varCount F + 4

/-- **The loop over the variables**, paid out of the potential. -/
theorem loop_spec (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B) :
    Spec B (fun σ => Inv F y off tgt σ ∧ σ.vars "x" = 0) (.while (.lt (V "x") (V "mx")) varBody)
      (fun _ σ' => Inv F y off tgt σ' ∧ σ'.vars "x" = mxOf (lits F)) (Kloop F) := by
  refine (Spec.while_potential (Inv F y off tgt) (Pot F) ?_ ?_ (fun _ h => h.1) ?_).post ?_
  · intro σ hI
    have := hI.core.x; have := hI.core.hmx; have := hI.core.mx
    exact evalB_condLt_vars (by omega) (by omega)
  · intro σ hI hcond
    have hlt : σ.vars "x" < mxOf (lits F) := by
      have := lt_of_condLt_true hcond; rw [hI.core.mx] at this; exact this
    obtain ⟨σ', K, hr, hI', hx', hK⟩ := varBody_run F y off tgt hB hyB hI hlt
    refine ⟨σ', K, hr, hI', ?_⟩
    rw [pot_step F σ hlt]
    unfold Pot
    rw [hx']
    simp only [size_condLt, size_var]
    split_ifs at hK ⊢ <;> omega
  · intro σ ⟨hI, hx⟩
    have := pot_zero_le F σ hx
    simp only [size_condLt, size_var]
    unfold Kloop; omega
  · intro σ σ' _ ⟨hI', hfalse⟩
    have := le_of_condLt_false hfalse
    rw [hI'.core.mx] at this
    exact ⟨hI', by have := hI'.core.x; omega⟩

/-- **The driver**: from a core state, the answer is written. -/
theorem driver_spec (hB : N F + (edges F).length + 16 < B) (hyB : 2 * y.length + 8 < B) :
    Spec B (Core F y off tgt) driver
      (fun _ σ' => σ'.out = [if ∀ x ∈ vars F, ¬ Bad F x then 1 else 0]) (2 + 2 + Kloop F + 2) := by
  intro σ hc
  unfold driver
  have h1B : 1 < B := by omega
  have r1 : Run B (.assign "ans" (.lit 1)) σ (σ.setVar "ans" 1) 2 :=
    Run.assign (evalB_lit h1B)
  have r2 : Run B (.assign "x" (.lit 0)) (σ.setVar "ans" 1) ((σ.setVar "ans" 1).setVar "x" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have hI : Inv F y off tgt ((σ.setVar "ans" 1).setVar "x" 0) := by
    refine ⟨?_, by simp, ?_⟩
    · have := (hc.setVar "ans" (by decide) 1)
      refine ⟨⟨?_, this.graph.2⟩, ?_, ?_, ?_, ?_, ?_, ?_, hc.hmx, ?_⟩
      · simpa using this.graph.1
      · simp; exact this.hN
      · simp; exact this.mx
      · simp
      · simpa using this.occ
      · simpa using this.lvis
      · simpa using this.lq
      · simpa using this.out
    · simp
  obtain ⟨σ3, r3, hI3, hx3⟩ := (loop_spec F y off tgt hB hyB).run ⟨hI, by simp⟩
  have hansB : σ3.vars "ans" < B := by have := hI3.ans1; omega
  have r4 : Run B (.write (V "ans")) σ3 { σ3 with out := σ3.out ++ [σ3.vars "ans"] } 2 :=
    Run.write (evalB_var hansB)
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by omega), ?_⟩
  show σ3.out ++ [σ3.vars "ans"] = _
  rw [hI3.core.out]
  have hiff : σ3.vars "ans" = 1 ↔ ∀ x ∈ vars F, ¬ Bad F x := by
    rw [hI3.ans, hx3]
    exact ⟨fun h x hx => h x (mem_vars_lt F hx) hx, fun h x _ hx => h x hx⟩
  have hans1 := hI3.ans1
  rw [List.nil_append]
  split
  · rw [hiff.2 ‹_›]
  · have h1 : σ3.vars "ans" ≠ 1 := fun h => ‹¬ _› (hiff.1 h)
    have h0 : σ3.vars "ans" = 0 := by omega
    rw [h0]

end Lax117284Proofs.TwoSAT.Machine.Driver
