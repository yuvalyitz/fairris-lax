import Lax117284Proofs.Bipartite.Ram2.SearchReal
import Lax117284Proofs.Bipartite.Ram2.Pot

/-!
The three kinds of turn — **pop** (the scan found nothing), **success** (the scan found a free
right vertex) and **push** (it found an occupied one) — each proved to run `afterScanCom` from a
finished scan to a state satisfying the search's loop invariant `LoopInv`, at a cost paid by the
drop in the potential `AS.pot`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- Applying frames whose right vertices are below `m` keeps the support below `m`. -/
theorem applyN_supp {μ : ℕ → Option ℕ} {Ls Rs : ℕ → ℕ} {m : ℕ}
    (hμ : ∀ j l, μ j = some l → j < m) :
    ∀ t, (∀ k < t, Rs k < m) → ∀ j l, applyN μ Ls Rs t j = some l → j < m
  | 0, _, j, l, h => hμ j l h
  | t + 1, hR, j, l, h => by
      have h' : Function.update (applyN μ Ls Rs t) (Rs t) (some (Ls t)) j = some l := h
      by_cases hj : j = Rs t
      · subst hj; exact hR _ (by omega)
      · rw [Function.update_of_ne hj] at h'
        exact applyN_supp hμ t (fun k hk => hR k (by omega)) j l h'

/-- **The search has succeeded**: `mu` holds a `GoodResult` (with the stacks and the visited
table still standing in `b`), whose support is below `m`. -/
def Done1 (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (σ : Env) : Prop :=
  σ.vars "result" = 1 ∧ ∃ (b : AS) (μ' : ℕ → Option ℕ), Real x μ' b σ ∧
    GoodResult (adjw x) μ₀ ∅ l₀ μ' ∧ ∀ j l, μ' j = some l → j < mw x

/-- **The search has failed**: the visited set certifies that no augmenting path exists. -/
def Done0 (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (σ : Env) : Prop :=
  σ.vars "result" = 0 ∧ ∃ b : AS, Real x μ₀ b σ ∧ FailCert (adjw x) μ₀ (mw x) l₀ b.visB

/-- **The invariant of the search loop**: still searching from a well-formed state `a`, or done. -/
def LoopInv (x : List ℕ) (μ₀ : ℕ → Option ℕ) (l₀ : ℕ) (a : AS) (σ : Env) : Prop :=
  (σ.vars "result" = 2 ∧ Real x μ₀ a σ ∧ AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a) ∨
    Done1 x μ₀ l₀ σ ∨ Done0 x μ₀ l₀ σ

/-- **A finished scan.** -/
structure PostScan (x : List ℕ) (μ₀ : ℕ → Option ℕ) (a : AS) (σ : Env) : Prop where
  real : Real x μ₀ a σ
  res : σ.vars "result" = 2
  t1 : σ.vars "t1" + 1 = a.top
  scan : ScanInv x a.visB (a.Ls (a.top - 1)) σ
  stop : σ.vars "x" = offw x (a.Ls (a.top - 1) + 1) ∨ σ.vars "found" = 1

section Turns

variable {x : List ℕ} {μ₀ : ℕ → Option ℕ} {l₀ : ℕ} {a : AS} {σ : Env}

/-- A scan that found something names a `Found`, at the slot before `x`. -/
theorem PostScan.found (hg : Good x) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1) :
    Found (offw x) (tgtw x) (nw x) (mw x) a (σ.vars "x" - 1) (σ.vars "foundJ") ∧
      1 ≤ σ.vars "x" := by
  have hpos := hI.top_pos
  have hLn := hI.Lbd (a.top - 1) (by omega)
  have hxhi := hP.scan.xhi
  rcases hP.scan.cases with ⟨h0, -⟩ | ⟨-, hlt, htg, hfresh, hslots⟩
  · omega
  · refine ⟨⟨by omega, by omega, htg, ?_, hfresh, hslots⟩, by omega⟩
    have hsV : σ.vars "x" - 1 < offw x (Vw x) := hg.slot_lt hLn (by omega)
    have := hg.tgt_lt _ hsV
    unfold mw; omega

/-- A scan that found nothing has closed the pending frame's row. -/
theorem PostScan.closed (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 0) :
    Cl (adjOff (offw x) (tgtw x) (nw x)) a.visB (mw x) (a.Ls (a.top - 1)) := by
  have hx : σ.vars "x" = offw x (a.Ls (a.top - 1) + 1) := by
    rcases hP.stop with h | h
    · exact h
    · omega
  rcases hP.scan.cases with ⟨-, hslots⟩ | ⟨h1, -⟩
  · rintro j _ ⟨s, hlo, hhi, ht⟩
    exact hslots s hlo (by omega) j ht
  · omega

/-- **Pop**: the scan found nothing, so the frame is exhausted. -/
theorem turn_pop (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 0) {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * offw x (a.Ls (a.top - 1) + 1) + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hcl := hP.closed hf
  obtain ⟨σ', hrun, hQ⟩ := (pop_spec (x := x) (μ₀ := μ₀) (by omega) hle hpos hmB).run
    ⟨hP.real, hP.res, hP.t1⟩
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some true := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  refine ⟨a.pop, σ', _, Run.ite_true hcond hrun, ?_, ?_⟩
  · by_cases h1 : a.top = 1
    · exact Or.inr (Or.inr ⟨hQ.2.1 h1, a.pop, hQ.1, hI.failCert hcl h1⟩)
    · exact Or.inl ⟨hQ.2.2 (by omega), hQ.1, hI.pop hcl (by omega)⟩
  · have hX := hI.Xhi (a.top - 1) (by omega)
    have := pot_pop (off := offw x) (μ₀ := μ₀) (m := mw x) a hpos
    simp only [size_condEq, size_var, size_lit, potD] at *
    omega

/-- **Success**: the scan found a free right vertex; every frame's choice goes into `mu`. -/
theorem turn_success (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1)
    (hfree : μ₀ (σ.vars "foundJ") = none) {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * σ.vars "x" + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  obtain ⟨hF, hx1⟩ := hP.found hg hI hf
  set j := σ.vars "foundJ" with hj
  set s := σ.vars "x" - 1 with hs
  have hxs : σ.vars "x" = s + 1 := by omega
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hnB : nw x + 2 ≤ B := by have := hg.n_lt; omega
  have hxB : σ.vars "x" < B := by
    have := hP.scan.xhi
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hI.Lbd (a.top - 1) (by omega); have := hg.nV; omega)
    omega
  -- record the candidate
  obtain ⟨σ₃, hrun3, hQ3⟩ := (found_spec (x := x) (μ₀ := μ₀) (a := a) (j := j) (xv := σ.vars "x")
    (by omega) hle hpos hmB hF.lt (fun l hl => by have := ctx.hμn j l hl; omega)
    (by omega) hxB).run ⟨hP.real, hP.t1, rfl, rfl⟩
  rw [hxs] at hQ3
  subst hQ3
  have hR3 := hP.real.found (s := s) (j := j) (match μ₀ j with | none => 0 | some l => l + 1)
  have hocc : ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)).vars "occ" = 0 := by
    simp [hfree]
  set σ3 := ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) with hσ3
  have hRb : ∀ k < (a.choose s j).top, (a.choose s j).Rs k < mw x := by
    intro k hk
    show Function.update a.Rs (a.top - 1) j k < mw x
    by_cases hk1 : k = a.top - 1
    · rw [hk1, Function.update_self]; exact hF.lt
    · rw [Function.update_of_ne hk1]
      exact (hI.Rvis k (by have : k < a.top := hk; omega)).1
  have hLb : ∀ k < (a.choose s j).top, (a.choose s j).Ls k < nw x := fun k hk => hI.Lbd k hk
  obtain ⟨σ₄, hrun4, hQ4⟩ := (apply_spec (x := x) (μ₀ := μ₀) (by omega)
    (b := a.choose s j) hle hmB hnB hRb hLb).run hR3
  have hres1 : (1 : ℕ) < B := by omega
  have hrun5 := Run.assign (B := B) (σ := σ₄) (x := "result") (e := .lit 1) (v := 1)
    (evalB_lit hres1)
  have hoccB : σ3.vars "occ" < B := by rw [hocc]; omega
  have hcond : (Cond.eq (.var "occ") (.lit 0)).evalB B σ3 = some true := by
    rw [evalB_condEq (evalB_var hoccB) (evalB_lit (by omega)), hocc]; simp
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond0 : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  refine ⟨AS.done, σ₄.setVar "result" 1, _,
    Run.ite_false hcond0 (hrun3.seq (Run.ite_true hcond (hrun4.seq hrun5))), ?_, ?_⟩
  · refine Or.inr (Or.inl ⟨by simp, a.choose s j, _,
      hQ4.congr (by simp) (by simp) (by simp) (by simp) (by simp), ?_, ?_⟩)
    · exact hI.success ctx.res ctx.inj ctx.unm hF hfree
    · exact applyN_supp ctx.supp _ hRb
  · have hpc := pot_success hI hF
    have hge := hF.ge hI
    have htopc : (a.choose s j).top = a.top := rfl
    rw [AS.done_pot]
    simp only [size_condEq, size_var, size_lit, potW, potD] at *
    omega

/-- **Push**: the scan found an occupied right vertex; a frame for its occupant goes on top. -/
theorem turn_push (ctx : Ctx B x μ₀ l₀) (hI : AbsInv (offw x) (tgtw x) μ₀ (nw x) (mw x) l₀ a)
    (hP : PostScan x μ₀ a σ) (hf : σ.vars "found" = 1) {l' : ℕ}
    (hocc : μ₀ (σ.vars "foundJ") = some l') {K₀ : ℕ}
    (hK₀ : K₀ + 40 * a.Xs (a.top - 1) ≤ 40 * σ.vars "x" + 34) :
    ∃ a' σ' K, Run B afterScanCom σ σ' K ∧ LoopInv x μ₀ l₀ a' σ' ∧
      K₀ + K + 4 + a'.pot (offw x) μ₀ (mw x) ≤ a.pot (offw x) μ₀ (mw x) := by
  have hg := ctx.good
  have hB := ctx.hB
  obtain ⟨hF, hx1⟩ := hP.found hg hI hf
  set j := σ.vars "foundJ" with hj
  set s := σ.vars "x" - 1 with hs
  have hxs : σ.vars "x" = s + 1 := by omega
  have hpos := hI.top_pos
  have hle := top_le_succ hI
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  have hnB : nw x + 2 ≤ B := by have := hg.n_lt; omega
  have hl'n : l' < nw x := ctx.hμn j l' hocc
  have hxB : σ.vars "x" < B := by
    have := hP.scan.xhi
    have := hg.off_lt_len (i := a.Ls (a.top - 1) + 1) (by have := hI.Lbd (a.top - 1) (by omega); have := hg.nV; omega)
    omega
  obtain ⟨σ₃, hrun3, hQ3⟩ := (found_spec (x := x) (μ₀ := μ₀) (a := a) (j := j) (xv := σ.vars "x")
    (by omega) hle hpos hmB hF.lt (fun l hl => by have := ctx.hμn j l hl; omega)
    (by omega) hxB).run ⟨hP.real, hP.t1, rfl, rfl⟩
  rw [hxs] at hQ3
  subst hQ3
  have hR3 := hP.real.found (s := s) (j := j) (match μ₀ j with | none => 0 | some l => l + 1)
  have hocc' : ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)).vars "occ" =
      l' + 1 := by
    simp [hocc]
  set σ3 := ((((σ.setArr "stkR" (a.top - 1) j).setArr "stkX" (a.top - 1) (s + 1)).setArr
      "vis" j 1).setVar "occ" (match μ₀ j with | none => 0 | some l => l + 1)) with hσ3
  have hbt : (a.choose s j).top ≤ mw x := by
    have h1 := hI.top_le
    have h2 := nvis_choose a s hF.lt hF.fresh
    have h3 := nvis_le (a.choose s j) (mw x)
    show a.top ≤ mw x
    omega
  obtain ⟨σ₄, hrun4, hQ4⟩ := (push_spec (x := x) (μ₀ := μ₀) hg hB (l' := l')
    (by omega) (b := a.choose s j) hbt hmB hnB hl'n).run ⟨hR3, hocc'⟩
  have hoccB : σ3.vars "occ" < B := by rw [hocc']; omega
  have hcond : (Cond.eq (.var "occ") (.lit 0)).evalB B σ3 = some false := by
    rw [evalB_condEq (evalB_var hoccB) (evalB_lit (by omega)), hocc']; simp
  have hfB : σ.vars "found" < B := by have := hP.scan.fle; omega
  have hcond0 : (Cond.eq (.var "found") (.lit 0)).evalB B σ = some false := by
    rw [evalB_condEq (evalB_var hfB) (evalB_lit (by omega)), hf]; simp
  have hmono : offw x l' ≤ offw x (l' + 1) := hg.mono l' (by have := hg.nV; omega)
  refine ⟨(a.choose s j).push (offw x) l', σ₄, _,
    Run.ite_false hcond0 (hrun3.seq (Run.ite_false hcond hrun4)), ?_, ?_⟩
  · subst hQ4
    refine Or.inl ⟨?_, Real.push hR3, hI.push hF hocc hl'n hmono⟩
    have := hP.res
    simp [hσ3, this]
  · have hpc := pot_push hI hF hocc
    have hge := hF.ge hI
    simp only [size_condEq, size_var, size_lit, potW, potD] at *
    omega

end Turns

end Lax117284Proofs.Bipartite.Ram2
