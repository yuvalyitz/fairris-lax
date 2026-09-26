import Lax117284Proofs.TwoSAT.Machine.Build
import Lax117284Proofs.TwoSAT.Machine.Driver
import Lax117284Proofs.TwoSAT.Machine.Language

/-!
The whole program, after the word has been read into `a` with its length in `L`: the scan, and
then either the answer `0` — the bits are no encoding of a formula, or a clause has no literal
or more than two — or the graph and the searches.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Main

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Width
open Lax117284Proofs.TwoSAT.Machine.Driver Lax117284Proofs.TwoSAT.Machine.Language
open scoped Classical

abbrev V (s : String) : Expr := .var s

/-- The answer `0`. -/
def reject : Com := .write (.lit 0)

/-- The accepting path: the number of nodes, the graph, the searches. -/
def accept : Com :=
  .seq (.assign "N" (.mul (.lit 2) (V "mx")))
    (.seq (.assign "x" (.lit 0)) (.seq Build.build driver))

/-- After the scan: reject unless it accepted; the width check; reject unless it passed. -/
def afterScan : Com :=
  .ite (.eq (V "ph") (.lit 4))
    (.seq width (.ite (.eq (V "ok") (.lit 1)) accept reject))
    reject

/-- The program after the word has been read. -/
def body : Com := .seq scanPart afterScan

/-- The array lengths, as functions of the word. -/
def ext (y : List ℕ) : String → ℕ := fun a =>
  if a = "cnt" then y.length + 1
  else if a = "occ" then y.length + 2
  else if a = "deg" ∨ a = "off" ∨ a = "pos" then N (formulaOf y) + 1
  else if a = "tgt" then (edges (formulaOf y)).length
  else if a = "vis" ∨ a = "q" then N (formulaOf y)
  else y.length

/-- The cost of the accepting path, on the formula. -/
def Kacc (F : Formula) : ℕ :=
  (44 * (lits F).length + 6) + (2 + (34 * F.length + 6)) + 4 + 4 + 2 +
    138 * ((lits F).length + N F + F.length + 1) + (2 + 2 + Kloop F + 2)

/-- The cost of the program after the read. -/
noncomputable def Kbody (y : List ℕ) : ℕ :=
  (2 + (64 * y.length + 6)) + 4 + (if Accepted y then 4 + Kacc (formulaOf y) else 2)

/-! ### Frame facts -/

lemma width_noWrite : width.NoWrite := by
  simp [width, countLoop, countBody, checkLoop, checkBody, Com.NoWrite]

lemma build_noWrite : Build.build.NoWrite := by
  simp [Build.build, Build.degPass, Build.degBody, Build.degUnit, Build.degPair, Build.prefPass,
    Build.prefBody, Build.fillPass, Build.fillBody, Build.fillUnit, Build.fillPair, Com.NoWrite]

lemma mem_wvars_width {z : String} (hz : z ∈ width.wvars) : z ∈ ["i", "cc", "x", "t", "ok"] := by
  simp only [width, countLoop, countBody, checkLoop, checkBody, Com.wvars, List.mem_append,
    List.mem_cons, List.not_mem_nil] at hz ⊢
  tauto

lemma mem_warrs_width {a : String} (ha : a ∈ width.warrs) : a ∈ ["cnt", "occ"] := by
  simp only [width, countLoop, countBody, checkLoop, checkBody, Com.warrs, List.mem_append,
    List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

lemma mem_warrs_build {a : String} (ha : a ∈ Build.build.warrs) :
    a ∈ ["deg", "off", "pos", "tgt"] := by
  simp only [Build.build, Build.degPass, Build.degBody, Build.degUnit, Build.degPair,
    Build.prefPass, Build.prefBody, Build.fillPass, Build.fillBody, Build.fillUnit,
    Build.fillPair, Com.warrs, List.mem_append, List.mem_cons, List.not_mem_nil] at ha ⊢
  tauto

lemma mx_not_wvars_build : "mx" ∉ Build.build.wvars := by decide

/-! ### The whole program -/

variable {B : ℕ} {y : List ℕ}

theorem ph_le (y : List ℕ) : (st y).ph ≤ 5 := ph_run_le _

/-- **The program after the read** writes the answer. -/
theorem body_spec (hB : 5 * y.length + 24 < B) (hyB : ∀ v ∈ y, v < B) :
    Spec B (ReadPost y (ext y)) body
      (fun _ σ' => σ'.out = [if Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT then 1 else 0])
      (Kbody y) := by
  intro σ h0
  have h4B : 4 < B := by omega
  have h1B : 1 < B := by omega
  -- the scan
  obtain ⟨σ1, r1, hS⟩ := (scanPart_spec (B := B) (ext := ext y) (by omega) hyB
    (by simp [ext])).run h0
  have hph : σ1.vars "ph" = (st y).ph := hS.ph
  have hphB : σ1.vars "ph" < B := by rw [hph]; have := ph_le y; omega
  have hcond : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some ((st y).ph == 4) := by
    rw [evalB_condEq (evalB_var hphB) (evalB_lit h4B), hph]
  by_cases hacc : Accepted y
  · -- accepted: the width check
    have hF := hS.facts hacc
    set F := formulaOf y with hFdef
    have hcond' : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some true := by
      rw [hcond]; have : (st y).ph = 4 := hacc; rw [this]; rfl
    have hk := hF.hk; have hC := hF.hC; have hmx := hF.hmx
    have hN : N F = 2 * mxOf (lits F) := rfl
    have hE := length_edges_le F
    obtain ⟨σ2, r2, hW, fv2, fa2, -, hout2⟩ := (width_spec (B := B) (ext := ext y) F (by omega)
      (by simp [ext])).frame.run hF
    have hout2' : σ2.out = [] := by rw [hout2 width_noWrite]; exact hF.out
    have hokB : σ2.vars "ok" < B := by have := hW.ok1; omega
    have hcondok : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some (σ2.vars "ok" == 1) :=
      evalB_condEq (evalB_var hokB) (evalB_lit h1B)
    have hfv2 : ∀ z, z ∉ ["i", "cc", "x", "t", "ok"] → σ2.vars z = σ1.vars z :=
      fun z hz => fv2 z fun hm => hz (mem_wvars_width hm)
    have hfa2 : ∀ a, a ∉ ["cnt", "occ"] → σ2.arrs a = σ1.arrs a :=
      fun a ha => fa2 a fun hm => ha (mem_warrs_width hm)
    by_cases hw : WidthOk F
    · -- the graph and the searches
      have hok1 : σ2.vars "ok" = 1 := hW.ok.2 hw
      have hcondok' : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
        rw [hcondok, hok1]; rfl
      have hmx2 : σ2.vars "mx" = mxOf (lits F) := by rw [hfv2 "mx" (by decide)]; exact hF.mx
      -- N := 2 * mx
      have rN : Run B (.assign "N" (.mul (.lit 2) (V "mx"))) σ2 (σ2.setVar "N" (N F)) 4 := by
        have := evalB_bin (op := .mul) (evalB_lit (B := B) (σ := σ2) (n := 2) (by omega))
          (evalB_var (x := "mx") (by rw [hmx2]; omega)) (by rw [hmx2]; show 2 * mxOf (lits F) < B; omega)
        rw [hmx2] at this
        exact (Run.assign (by simpa [Bop.apply, N] using this)).mono (by simp)
      set σ3 := σ2.setVar "N" (N F) with hσ3
      have rX : Run B (.assign "x" (.lit 0)) σ3 (σ3.setVar "x" 0) 2 := Run.assign (evalB_lit (by omega))
      set σ4 := σ3.setVar "x" 0 with hσ4
      -- what the construction needs
      have hvr4 : σ4.arrs "vr" = σ1.arrs "vr" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "vr" (by decide)
      have hsg4 : σ4.arrs "sg" = σ1.arrs "sg" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "sg" (by decide)
      have hcl4 : σ4.arrs "cl" = σ1.arrs "cl" := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hfa2 "cl" (by decide)
      have hcnt4 : σ4.arrs "cnt" = arrOf (y.length + 1) (cntF F) := by
        simp only [hσ4, hσ3, arrs_setVar]; exact hW.cnt
      have hfresh : ∀ a, a ∉ ["a", "vr", "sg", "cl", "cnt", "occ"] →
          σ4.arrs a = List.replicate (ext y a) 0 := by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
        simp only [hσ4, hσ3, arrs_setVar]
        rw [hfa2 a (by simp; tauto)]
        exact hF.arr a (by simp; tauto)
      have hpre : Build.Pre F σ4 := by
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hW.k
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hW.C
        · simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]
        · rw [hvr4, hF.lvr]; exact hk
        · rw [hsg4, hF.lsg]; exact hk
        · rw [hcnt4, length_arrOf]; omega
        · intro i hi; rw [hvr4]; exact hF.vr i hi
        · intro i hi; rw [hsg4]; exact hF.sg i hi
        · intro c hc; rw [hcnt4, getD_arrOf _ (by omega)]; unfold cntF; rw [if_pos hc]
        · rw [hcl4, hF.lcl]; exact hk
        · intro i hi; rw [hcl4]; exact hF.cl i hi
        · rw [hfresh "deg" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "off" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "pos" (by decide)]; simp [ext, ← hFdef]
        · rw [hfresh "tgt" (by decide)]; simp [ext, ← hFdef]
      obtain ⟨σ5, r5, ⟨off, tgt, hcsr, hrows, hE5, hN5, -, -⟩, fv5, fa5, -, hout5⟩ :=
        (Build.build_spec (B := B) F hw (by omega)).frame.run hpre
      have hfa5 : ∀ a, a ∉ ["deg", "off", "pos", "tgt"] → σ5.arrs a = σ4.arrs a :=
        fun a ha => fa5 a fun hm => ha (mem_warrs_build hm)
      -- what the driver needs
      have hcore : Core F y off tgt σ5 := by
        refine ⟨⟨hcsr, hrows⟩, hN5, ?_, ?_, ?_, ?_, ?_, hmx, ?_⟩
        · rw [fv5 "mx" mx_not_wvars_build]
          simp only [hσ4, hσ3, vars_setVar, String.reduceEq, ↓reduceIte]; exact hmx2
        · rw [fv5 "x" (by decide)]
          simp only [hσ4, vars_setVar, ↓reduceIte]; omega
        · rw [hfa5 "occ" (by decide)]
          simp only [hσ4, hσ3, arrs_setVar]; exact hW.occ
        · rw [hfa5 "vis" (by decide), hfresh "vis" (by decide)]; simp [ext, ← hFdef]
        · rw [hfa5 "q" (by decide), hfresh "q" (by decide)]; simp [ext, ← hFdef]
        · rw [hout5 build_noWrite]; simp only [hσ4, hσ3, out_setVar]; exact hout2'
      obtain ⟨σ6, r6, hout6⟩ := (driver_spec (B := B) F y off tgt (by omega) (by omega)).run hcore
      refine ⟨σ6, ?_, ?_⟩
      · have run := r1.seq (Run.ite_true (d := reject) hcond' (r2.seq
          (Run.ite_true (d := reject) hcondok' (rN.seq (rX.seq (r5.seq r6))))))
        refine run.mono ?_
        unfold Kbody Kacc
        rw [if_pos hacc]
        simp only [size_condEq, size_var, size_lit]
        try simp only [← hFdef]
        try rw [hmx2]
        omega
      · show σ6.out = _
        rw [hout6, mem_twoSAT_iff', ← hFdef]
        simp only [hacc, hw, true_and]
    · -- a clause of the wrong width
      have hok0 : σ2.vars "ok" ≠ 1 := fun h => hw (hW.ok.1 h)
      have hcondok' : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
        rw [hcondok]; exact congrArg some (beq_eq_false_iff_ne.mpr hok0)
      have r3 : Run B reject σ2 { σ2 with out := σ2.out ++ [0] } 2 := Run.write (evalB_lit (by omega))
      refine ⟨{ σ2 with out := σ2.out ++ [0] }, ?_, ?_⟩
      · have run := r1.seq (Run.ite_true (d := reject) hcond'
          (r2.seq (Run.ite_false (c := accept) hcondok' r3)))
        refine run.mono ?_
        unfold Kbody Kacc
        rw [if_pos hacc]
        simp only [size_condEq, size_var, size_lit]
        try simp only [← hFdef]
        omega
      · show σ2.out ++ [0] = _
        rw [hout2', mem_twoSAT_iff', ← hFdef]
        simp [hw]
  · -- not the encoding of a formula
    have hcond' : (Cond.eq (V "ph") (.lit 4)).evalB B σ1 = some false := by
      rw [hcond]; exact congrArg some (beq_eq_false_iff_ne.mpr hacc)
    have r3 : Run B reject σ1 { σ1 with out := σ1.out ++ [0] } 2 := Run.write (evalB_lit (by omega))
    refine ⟨{ σ1 with out := σ1.out ++ [0] }, ?_, ?_⟩
    · have run := r1.seq (Run.ite_false
        (c := .seq width (.ite (.eq (V "ok") (.lit 1)) accept reject)) hcond' r3)
      refine run.mono ?_
      unfold Kbody
      rw [if_neg hacc]
      simp only [size_condEq, size_var, size_lit]
      omega
    · show σ1.out ++ [0] = _
      rw [hS.out, mem_twoSAT_iff']
      simp [hacc]

end Lax117284Proofs.TwoSAT.Machine.Main
