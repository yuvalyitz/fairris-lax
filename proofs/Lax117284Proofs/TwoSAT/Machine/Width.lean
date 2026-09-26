import Lax808846Proofs.Lib.Basic
import Lax117284Proofs.TwoSAT.Machine.Scan

/-!
The width check: one pass over the literals counts, for every clause, how many literals it has
(`cnt`) and marks every variable that occurs (`occ`); one pass over the clauses then sets `ok`
to `0` if some clause has no literal or more than two.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Width

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan
open scoped Classical

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- One literal: count it for its clause and mark its variable. -/
def countBody : Com :=
  .seq (.assign "cc" (.get "cl" (V "i")))
    (.seq (.store "cnt" (V "cc") (.add (.get "cnt" (V "cc")) (.lit 1)))
      (.seq (.assign "x" (.get "vr" (V "i")))
        (.seq (.store "occ" (V "x") (.lit 1)) (bump "i"))))

def countLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "k")) countBody)

/-- One clause: a count of `0` or more than `2` clears `ok`. -/
def checkBody : Com :=
  .seq (.assign "t" (.get "cnt" (V "cc")))
    (.seq (.ite (.eq (V "t") (.lit 0)) (.assign "ok" (.lit 0))
      (.ite (.lt (.lit 2) (V "t")) (.assign "ok" (.lit 0)) .skip))
      (bump "cc"))

def checkLoop : Com :=
  .seq (.assign "ok" (.lit 1))
    (.seq (.assign "cc" (.lit 0)) (.while (.lt (V "cc") (V "C")) checkBody))

/-- The width check. -/
def width : Com := .seq countLoop checkLoop

/-! ### The mathematics of the counts -/

variable (F : Formula)

/-- The number of literals among the first `i` with clause number `c`. -/
def cntUpTo (i c : ℕ) : ℕ := ((List.range i).filter fun j => cv F j = c).length

theorem cntUpTo_succ (i c : ℕ) :
    cntUpTo F (i + 1) c = cntUpTo F i c + if cv F i = c then 1 else 0 := by
  unfold cntUpTo
  rw [List.range_succ, List.filter_append, List.length_append, List.filter_singleton]
  split <;> simp_all

theorem cntUpTo_le (i c : ℕ) : cntUpTo F i c ≤ i := by
  unfold cntUpTo
  exact (List.length_filter_le _ _).trans (by simp)

theorem cntUpTo_zero (c : ℕ) : cntUpTo F 0 c = 0 := by simp [cntUpTo]

/-- The final counts: the length of each clause. -/
def cntF (c : ℕ) : ℕ := if c < F.length then (F.getD c []).length else 0

theorem cntUpTo_length (c : ℕ) : cntUpTo F (lits F).length c = cntF F c := by
  unfold cntF
  split
  · exact count_cv F c ‹_›
  · unfold cntUpTo
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro j hj
    rw [List.mem_range] at hj
    have := cv_lt F j hj
    simp; omega

/-- The variables among the first `i` literals. -/
def occUpTo (i x : ℕ) : ℕ := if ∃ j < i, iv F j = x then 1 else 0

theorem occUpTo_zero (x : ℕ) : occUpTo F 0 x = 0 := by
  unfold occUpTo; rw [if_neg]; rintro ⟨j, hj, -⟩; omega

theorem mem_vars_iff (x : ℕ) : x ∈ vars F ↔ ∃ j < (lits F).length, iv F j = x := by
  unfold vars literals
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hl
    exact ⟨j, hj, by unfold iv lits; rw [List.getD_eq_getElem _ _ hj]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, getD_mem_lits F j hj, rfl⟩

/-- The final marks: the indicator of the variables. -/
def occF (x : ℕ) : ℕ := if x ∈ vars F then 1 else 0

theorem occUpTo_length (x : ℕ) : occUpTo F (lits F).length x = occF F x := by
  unfold occUpTo occF
  by_cases h : x ∈ vars F
  · rw [if_pos h, if_pos ((mem_vars_iff F x).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((mem_vars_iff F x).2 h'))]

theorem widthOk_iff_cnt : WidthOk F ↔ ∀ c < F.length, 1 ≤ cntF F c ∧ cntF F c ≤ 2 := by
  unfold WidthOk
  rw [Lax117284Proofs.TwoSAT.Bridge.forall_mem_iff]
  refine forall_congr' fun c => imp_congr_right fun hc => ?_
  unfold cntF; rw [if_pos hc]

/-! ### The counting pass -/

variable {B : ℕ} {y : List ℕ} {ext : String → ℕ}

/-- The invariant of the counting pass. -/
structure CountInv (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  k : σ.vars "k" = (lits F).length
  i : σ.vars "i" ≤ (lits F).length
  vr : ∀ j < (lits F).length, (σ.arrs "vr").getD j 0 = iv F j
  cl : ∀ j < (lits F).length, (σ.arrs "cl").getD j 0 = cv F j
  lvr : (σ.arrs "vr").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntUpTo F (σ.vars "i"))
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occUpTo F (σ.vars "i"))
  hk : (lits F).length ≤ y.length
  hC : F.length ≤ y.length
  hmx : mxOf (lits F) ≤ y.length + 1

theorem countBody_flat :
    Spec B (fun σ => CountInv F y σ ∧ σ.vars "i" < (lits F).length ∧
        σ.vars "i" < (σ.arrs "cl").length ∧ (σ.arrs "cl").getD (σ.vars "i") 0 < B ∧
        (σ.arrs "cl").getD (σ.vars "i") 0 < (σ.arrs "cnt").length ∧
        (σ.arrs "cnt").getD ((σ.arrs "cl").getD (σ.vars "i") 0) 0 + 1 < B ∧
        σ.vars "i" < (σ.arrs "vr").length ∧ (σ.arrs "vr").getD (σ.vars "i") 0 < B ∧
        (σ.arrs "vr").getD (σ.vars "i") 0 < (σ.arrs "occ").length ∧ σ.vars "i" + 1 < B ∧
        σ.vars "i" < B ∧ 1 < B) countBody
      (fun σ σ' => CountInv F y σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals try (simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]; first | omega | assumption)
  have hI : CountInv F y σ := ‹_›
  have hi : σ.vars "i" < (lits F).length := ‹_›
  have hcl := hI.cl _ hi
  have hvr := hI.vr _ hi
  have hcv := cv_lt F _ hi
  have hiv := iv_lt F _ hi
  have hC := hI.hC
  have hmx := hI.hmx
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.hk, hI.hC, hI.hmx⟩, ?_⟩
  all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]
  · exact hI.k
  · omega
  · exact hI.vr
  · exact hI.cl
  · exact hI.lvr
  · exact hI.lcl
  · rw [hcl, hI.cnt, set_arrOf_eq_upd]
    apply arrOf_congr
    intro c hc
    rw [cntUpTo_succ, upd_apply, getD_arrOf _ (by omega)]
    by_cases h : c = cv F (σ.vars "i")
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), Nat.add_zero]
  · rw [hvr, hI.occ, set_arrOf_eq_upd]
    apply arrOf_congr
    intro x hx
    rw [upd_apply]
    unfold occUpTo
    by_cases hxe : x = iv F (σ.vars "i")
    · rw [if_pos hxe, if_pos ⟨σ.vars "i", by omega, hxe.symm⟩]
    · rw [if_neg hxe]
      by_cases h : ∃ j < σ.vars "i", iv F j = x
      · have h' : ∃ j < σ.vars "i" + 1, iv F j = x := by
          obtain ⟨j, hj, hjx⟩ := h; exact ⟨j, by omega, hjx⟩
        rw [if_pos h, if_pos h']
      · have h' : ¬ ∃ j < σ.vars "i" + 1, iv F j = x := by
          rintro ⟨j, hj, hjx⟩
          rcases Nat.lt_or_ge j (σ.vars "i") with h' | h'
          · exact h ⟨j, h', hjx⟩
          · exact hxe (by rw [← hjx]; congr 1; omega)
        rw [if_neg h, if_neg h']

theorem countBody_spec (hB : 2 * y.length + 8 < B) :
    Spec B (fun σ => CountInv F y σ ∧ σ.vars "i" < (lits F).length) countBody
      (fun σ σ' => CountInv F y σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  refine Spec.pre (countBody_flat F) ?_
  rintro σ ⟨hI, hi⟩
  have hcl := hI.cl _ hi
  have hvr := hI.vr _ hi
  have hcv := cv_lt F _ hi
  have hiv := iv_lt F _ hi
  have hC := hI.hC
  have hmx := hI.hmx
  have hk := hI.hk
  have hcnt : (σ.arrs "cnt").getD (cv F (σ.vars "i")) 0 ≤ σ.vars "i" := by
    rw [hI.cnt, getD_arrOf _ (by omega)]; exact cntUpTo_le F _ _
  refine ⟨hI, hi, by rw [hI.lcl]; omega, by rw [hcl]; omega,
    by rw [hcl, hI.cnt, length_arrOf]; omega, by rw [hcl]; omega, by rw [hI.lvr]; omega,
    by rw [hvr]; omega, by rw [hvr, hI.occ, length_arrOf]; omega, by omega, by omega, by omega⟩

/-- **The counting pass.** -/
theorem countLoop_spec (hB : 2 * y.length + 8 < B) (hk : (lits F).length ≤ y.length) :
    Spec B (fun σ => CountInv F y (σ.setVar "i" 0)) countLoop
      (fun _ σ' => CountInv F y σ' ∧ σ'.vars "i" = (lits F).length) (44 * (lits F).length + 6) :=
  Spec.forRangeZero "i" "k" (CountInv F y) (lits F).length 40 (by omega)
    (fun _ h => h.i) (fun _ h => h.k) (countBody_spec F hB)

/-! ### The checking pass -/

/-- The invariant of the checking pass. -/
structure CheckInv (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  C : σ.vars "C" = F.length
  cc : σ.vars "cc" ≤ F.length
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntF F)
  ok : σ.vars "ok" = 1 ↔ ∀ c < σ.vars "cc", 1 ≤ cntF F c ∧ cntF F c ≤ 2
  ok1 : σ.vars "ok" ≤ 1
  hC : F.length ≤ y.length
  hk : (lits F).length ≤ y.length

theorem checkBody_flat :
    Spec B (fun σ => CheckInv F y σ ∧ σ.vars "cc" < F.length ∧
        σ.vars "cc" < (σ.arrs "cnt").length ∧ (σ.arrs "cnt").getD (σ.vars "cc") 0 < B ∧
        σ.vars "cc" + 1 < B ∧ σ.vars "cc" < B ∧ 2 < B ∧
        (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc")) checkBody
      (fun σ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 30 := by
  run_vcg
  all_goals try (simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte]; first | omega | assumption)
  all_goals (
    have hI : CheckInv F y σ := ‹_›
    have hlt : σ.vars "cc" < F.length := ‹_›
    have ht : (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc") := ‹_›
    have hok := hI.ok
    have hok1 := hI.ok1
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hI.hC, hI.hk⟩, ?_⟩
    all_goals try simp only [Env.setVar, Env.setArr, String.reduceEq, ↓reduceIte] at *)
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is zero: the answer is no
    rw [ht] at *
    constructor
    · intro h; omega
    · intro h; have := (h (σ.vars "cc") (by omega)).1; omega
  · omega
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is more than two: the answer is no
    rw [ht] at *
    constructor
    · intro h; omega
    · intro h; have := (h (σ.vars "cc") (by omega)).2; omega
  · omega
  · exact hI.C
  · omega
  · exact hI.cnt
  · -- the count is one or two: the answer stands
    rw [ht] at *
    rw [hok]
    constructor
    · intro h c hc
      rcases Nat.lt_or_ge c (σ.vars "cc") with h' | h'
      · exact h c h'
      · have : c = σ.vars "cc" := by omega
        subst this; omega
    · intro h c hc; exact h c (by omega)
  · exact hok1

theorem checkBody_spec (hB : y.length + 8 < B) :
    Spec B (fun σ => CheckInv F y σ ∧ σ.vars "cc" < F.length) checkBody
      (fun σ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = σ.vars "cc" + 1) 30 := by
  refine Spec.pre (checkBody_flat F) ?_
  rintro σ ⟨hI, hlt⟩
  have hC := hI.hC
  have ht : (σ.arrs "cnt").getD (σ.vars "cc") 0 = cntF F (σ.vars "cc") := by
    rw [hI.cnt, getD_arrOf _ (by omega)]
  have hle : cntF F (σ.vars "cc") ≤ y.length := by
    unfold cntF; rw [if_pos hlt]
    have := start_add_le F _ hlt
    have := hI.hk
    omega
  refine ⟨hI, hlt, by rw [hI.cnt, length_arrOf]; omega, by rw [ht]; omega, by omega, by omega,
    by omega, ht⟩

/-- **The checking pass.** -/
theorem checkLoop_spec (hB : y.length + 8 < B) (hC : F.length ≤ y.length) :
    Spec B (fun σ => CheckInv F y ((σ.setVar "ok" 1).setVar "cc" 0)) checkLoop
      (fun _ σ' => CheckInv F y σ' ∧ σ'.vars "cc" = F.length) (2 + (34 * F.length + 6)) := by
  refine Spec.of_exists fun σ hσ => ?_
  have r1 : Run B (.assign "ok" (.lit 1)) σ (σ.setVar "ok" 1) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ', r2, h2⟩ := (Spec.forRangeZero "cc" "C" (CheckInv F y) F.length 30 (by omega)
    (fun _ h => h.cc) (fun _ h => h.C) (checkBody_spec F hB)).run hσ
  exact ⟨σ', _, r1.seq r2, le_rfl, h2⟩

/-! ### The whole width check -/

/-- What the width check leaves. -/
structure WidthPost (F : Formula) (y : List ℕ) (σ : Env) : Prop where
  cnt : σ.arrs "cnt" = arrOf (y.length + 1) (cntF F)
  occ : σ.arrs "occ" = arrOf (y.length + 2) (occF F)
  ok : σ.vars "ok" = 1 ↔ WidthOk F
  ok1 : σ.vars "ok" ≤ 1
  k : σ.vars "k" = (lits F).length
  C : σ.vars "C" = F.length

lemma wvars_countLoop : countLoop.wvars = ["i", "cc", "x", "i"] := by
  simp [countLoop, countBody, Com.wvars]
lemma wvars_checkLoop : checkLoop.wvars = ["ok", "cc", "t", "ok", "ok", "cc"] := by
  simp [checkLoop, checkBody, Com.wvars]
lemma warrs_checkLoop : checkLoop.warrs = [] := by
  simp [checkLoop, checkBody, Com.warrs]

/-- **The width check**: from the facts of an accepted scan, with fresh `cnt` and `occ`. -/
theorem width_spec (hB : 2 * y.length + 8 < B)
    (hext : ext "cnt" = y.length + 1 ∧ ext "occ" = y.length + 2) :
    Spec B (Facts F y ext) width (fun _ σ' => WidthPost F y σ')
      ((44 * (lits F).length + 6) + (2 + (34 * F.length + 6))) := by
  intro σ hF
  have hk := hF.hk
  have hC := hF.hC
  -- the counting pass
  obtain ⟨σ1, r1, ⟨hI1, hi1⟩, fv1, fa1, -, -⟩ :=
    (countLoop_spec F hB hk).frame.run (σ := σ) (by
      refine ⟨by simp [hF.k], by simp, ?_, ?_, by simp [hF.lvr], by simp [hF.lcl], ?_, ?_,
        hk, hC, hF.hmx⟩
      · intro j hj; simp only [Env.setVar]; exact hF.vr j hj
      · intro j hj; simp only [Env.setVar]; exact hF.cl j hj
      · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
        rw [hF.arr "cnt" (by decide), hext.1, replicate_eq_arrOf]
        exact arrOf_congr fun c _ => (cntUpTo_zero F c).symm
      · simp only [Env.setVar, String.reduceEq, ↓reduceIte]
        rw [hF.arr "occ" (by decide), hext.2, replicate_eq_arrOf]
        exact arrOf_congr fun x _ => (occUpTo_zero F x).symm)
  have hC1 : σ1.vars "C" = F.length := by
    rw [fv1 "C" (by rw [wvars_countLoop]; decide)]; exact hF.C
  have hcnt1 : σ1.arrs "cnt" = arrOf (y.length + 1) (cntF F) := by
    rw [hI1.cnt, hi1]; exact arrOf_congr fun c _ => cntUpTo_length F c
  have hocc1 : σ1.arrs "occ" = arrOf (y.length + 2) (occF F) := by
    rw [hI1.occ, hi1]; exact arrOf_congr fun x _ => occUpTo_length F x
  -- the checking pass
  have hB' : y.length + 8 < B := by omega
  obtain ⟨σ2, r2, ⟨hI2, hcc2⟩, fv2, fa2, -, -⟩ :=
    (checkLoop_spec F hB' hC).frame.run (σ := σ1) (by
      refine ⟨by simp [hC1], by simp, by simp [hcnt1], ?_, by simp, hC, hk⟩
      simp only [Env.setVar, String.reduceEq, ↓reduceIte]
      first
        | trivial
        | exact ⟨fun _ c hc => absurd hc (by omega), fun _ => trivial⟩
        | exact ⟨fun _ c hc => absurd hc (by omega), fun _ => rfl⟩)
  refine ⟨σ2, r1.seq r2, ?_⟩
  refine ⟨?_, ?_, ?_, hI2.ok1, ?_, hI2.C⟩
  · exact hI2.cnt
  · rw [fa2 "occ" (by rw [warrs_checkLoop]; decide)]; exact hocc1
  · rw [hI2.ok, hcc2, widthOk_iff_cnt]
  · rw [fv2 "k" (by rw [wvars_checkLoop]; decide), fv1 "k" (by rw [wvars_countLoop]; decide)]
    exact hF.k

end Lax117284Proofs.TwoSAT.Machine.Width
