import Lax117284Proofs.TwoSAT.Machine.Main
import Lax117284Proofs.TwoSAT.Machine.Wrap
import Lax117284Proofs.TwoSAT.Machine.ToP
import Lax391470Proofs.ReadAll

/-!
The program on the word RAM: the layout, the two entry points — the raw word with its length
supplied by the machine, and the length-prefixed word of the polynomial-time predicate — and
the concept's running-time statement.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax117284.TwoSatCNF
open Lax117284Proofs.TwoSAT.Machine.Model Lax117284Proofs.TwoSAT.Machine.Scan Lax117284Proofs.TwoSAT.Machine.Width
open Lax117284Proofs.TwoSAT.Machine.Driver Lax117284Proofs.TwoSAT.Machine.Language Lax117284Proofs.TwoSAT.Machine.Main
open Lax117284Proofs.TwoSAT.Machine.Wrap Lax391470Proofs.ReadAll
open scoped Classical

/-- The layout: every scalar and every array the program mentions. -/
def layout : Layout :=
  ⟨["L", "rt", "rv", "len", "mx", "ph", "n", "C", "k", "p", "c", "i", "cc", "x", "t", "ok",
    "N", "E", "na", "nb", "ca", "cb", "u", "s", "head", "tail", "v", "j", "jend", "r", "o", "ans"],
   ["a", "vr", "sg", "cl", "cnt", "occ", "deg", "off", "pos", "tgt", "vis", "q"], 12⟩

/-- The program on the raw word: the machine has put its length into `len`. -/
def mainRaw : Com := .seq (.assign "L" (.var "len")) (.seq readLoop body)

/-- The program on the length-prefixed word. -/
def mainPre : Com := .seq readAll body

theorem body_ok : Com.Ok layout body := by
  simp [body, scanPart, Lax391470Proofs.L2Scan.scanLoop, Lax391470Proofs.L2Scan.scanBody,
    Lax391470Proofs.L2Scan.dispatch, Lax391470Proofs.L2Scan.phase3, afterScan, accept, reject,
    width, countLoop, countBody, checkLoop, checkBody, Build.build, Build.degPass, Build.degBody,
    Build.degUnit, Build.degPair, Build.prefPass, Build.prefBody, Build.fillPass, Build.fillBody,
    Build.fillUnit, Build.fillPair, driver, varBody, searchesCom, secondCom, Bfs.bfs, Bfs.clear,
    Bfs.initDrain, Bfs.drain, Bfs.expandBody, Bfs.scanBody, layout, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

theorem mainRaw_ok : Com.Ok layout mainRaw := by
  refine ⟨?_, ?_, body_ok⟩
  · simp [layout, Com.Ok, Expr.Ok]
  · simp [readLoop, readBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem mainPre_ok : Com.Ok layout mainPre := by
  refine ⟨?_, body_ok⟩
  simp [readAll, readLoop, readBody, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-! ### Reading the raw word -/

/-- The value bound on a word of zeros and ones. -/
def Bd (y : List ℕ) : ℕ := 5 * y.length + 25

/-- The cost of the program on the raw word. -/
noncomputable def KRaw (y : List ℕ) : ℕ := 2 + (12 * y.length + 10) + Kbody y

lemma wvars_readLoop : readLoop.wvars = ["rt", "rv", "rt"] := by
  simp [readLoop, readBody, Com.wvars]
lemma warrs_readLoop : readLoop.warrs = ["a"] := by
  simp [readLoop, readBody, Com.warrs]

/-- After the read loop, the array `a` is the word. -/
theorem a_eq_of_rinv {y : List ℕ} {σ : Env} (h : RInv y σ) (ht : σ.vars "rt" = y.length) :
    σ.arrs "a" = y := by
  obtain ⟨-, -, hlen, hcell, -, -⟩ := h
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have := hcell i (by rw [ht]; exact h2)
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at this

/-- **The program on the raw word.** -/
theorem mainRaw_run (y : List ℕ) (hy1 : ∀ v ∈ y, v ≤ 1) :
    ∃ σ', Run (Bd y) mainRaw (lenEnv (ext y) y) σ' (KRaw y) ∧
      σ'.out = [if Lax391470Proofs.Bits.bitsOf y ∈ TwoSAT then 1 else 0] := by
  have hB : 5 * y.length + 24 < Bd y := by unfold Bd; omega
  have hyB : ∀ v ∈ y, v < Bd y := fun v hv => by have := hy1 v hv; unfold Bd; omega
  set σ0 := lenEnv (ext y) y with hσ0
  have hlen0 : σ0.vars "len" = y.length := by simp [hσ0, lenEnv]
  -- L := len
  have r0 : Run (Bd y) (.assign "L" (.var "len")) σ0 (σ0.setVar "L" y.length) 2 := by
    have := Run.assign (B := Bd y) (σ := σ0) (x := "L") (e := .var "len")
      (evalB_var (by rw [hlen0]; unfold Bd; omega))
    rw [hlen0] at this
    exact this.mono (by simp)
  set σ1 := σ0.setVar "L" y.length with hσ1
  -- the read loop
  obtain ⟨σ2, r2, ⟨hI2, ht2⟩, fv2, fa2, -, -⟩ :=
    (readLoop_spec (B := Bd y) (y := y) hyB (by unfold Bd; omega)).frame.run (σ := σ1) (by
      refine ⟨by simp [hσ1], by simp, ?_, fun i hi => by simp at hi, by simp [hσ1, hσ0, lenEnv, initEnv],
        by simp [hσ1, hσ0, lenEnv, initEnv]⟩
      simp [hσ1, hσ0, lenEnv, initEnv, ext])
  have hpost : ReadPost y (ext y) σ2 := by
    refine ⟨hI2.1, a_eq_of_rinv hI2 ht2, hI2.2.2.2.2.2, ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      rw [fv2 z (by rw [wvars_readLoop]; simp; tauto)]
      simp [hσ1, hσ0, lenEnv, initEnv, hz.1, hz.2.2.2]
    · intro b hb
      rw [fa2 b (by rw [warrs_readLoop]; simp [hb])]
      simp [hσ1, hσ0, lenEnv, initEnv]
  obtain ⟨σ3, r3, hout⟩ := (body_spec (B := Bd y) hB hyB).run hpost
  exact ⟨σ3, (r0.seq (r2.seq r3)).mono (by unfold KRaw; omega), hout⟩

/-! ### The cost, against the concept's bound -/

theorem varCount_le (F : Formula) : varCount F ≤ (lits F).length := by
  unfold varCount vars literals
  exact (List.toFinset_card_le _).trans (by rw [List.length_map]; rfl)

/-- The constant of the running time. -/
def c0 : ℕ := 8000

theorem KRaw_le (y : List ℕ) :
    10 * KRaw y + 2 ≤ c0 * (y.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount y + 1) := by
  unfold KRaw Kbody c0
  by_cases hacc : Accepted y
  · rw [if_pos hacc, wordVarCount_eq y hacc]
    set F := formulaOf y with hF
    obtain ⟨hk, hC, hmx⟩ := sizes_le hacc
    rw [← hF] at hk hC hmx
    have hE := length_edges_le F
    have hN : N F = 2 * mxOf (lits F) := rfl
    have hv := varCount_le F
    unfold Kacc Kloop Ks
    simp only [Bfs.Kbfs_eq]
    set v := varCount F with hvdef
    set L := y.length with hL
    have h1 : (2 * (40 * (N F + (edges F).length + 1)) + 40) * v ≤ (240 * L + 280) * v :=
      Nat.mul_le_mul_right v (by omega)
    have h2 : (240 * L + 280) * v = 240 * (L * v) + 280 * v := by ring
    have h3 : 8000 * (L + 1) * (v + 1) = 8000 * (L * v) + 8000 * L + 8000 * v + 8000 := by ring
    have h4 : L * v ≥ 0 := Nat.zero_le _
    have h5 : v ≤ L := by omega
    have h6 : v ≤ L * v + v := by omega
    rw [h3]
    omega
  · rw [if_neg hacc, wordVarCount_eq_zero y hacc]
    nlinarith

/-! ### The concept's statement -/

theorem fits (w : ℕ) (x : List ℕ) (h : c0 * (x.length + 1) ≤ 2 ^ w) :
    layout.FitsWords (Bd x) w := by
  refine fitsWords_of_max_le (by unfold Bd; omega) ?_
  simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
  unfold Bd; unfold c0 at h
  omega

/--
---
conclusion: Lax117284.TwoSatRunningTime.decides
---
The program reads the word, scans it with the verified scanner of `lax-391470`, checks the
width of every clause, builds the implication graph in compressed sparse row form by a counting
sort, and searches from both literals of every occurring variable; the searches are paid out of a
potential that charges a constant to every variable and two searches to every occurring one,
which gives the factor `v + 1`. The constant is `8000`.
-/
theorem decides : ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog
      {x | (∀ v ∈ x, v ≤ 1) ∧ c * (x.length + 1) ≤ 2 ^ w}
      (fun x => if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0])
      (fun x => c * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1)) := by
  refine ⟨wrapProgram layout mainRaw, c0, fun w x ⟨hx1, hfit⟩ => ?_⟩
  obtain ⟨σ', ⟨k, hk, hbs⟩, hout⟩ := mainRaw_run x hx1
  obtain ⟨t, ht, hrun⟩ := wrap_runsTo (fits w x hfit) mainRaw_ok (by simp [layout])
    (fun v hv => by have := hx1 v hv; unfold Bd; omega) (by unfold Bd; omega) hbs
  refine ⟨t, ?_, ?_⟩
  · show t ≤ c0 * (x.length + 1) * (Lax117284.TwoSatRunningTime.wordVarCount x + 1)
    have := KRaw_le x
    simp only [Layout.const] at ht
    omega
  · rw [hout] at hrun
    have e : (if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0]) =
        [if Lax391470Proofs.Bits.bitsOf x ∈ TwoSAT then 1 else 0] := by
      rw [bitsOf_eq]; split <;> rfl
    show RunsTo w (wrapProgram layout mainRaw) x
      (if Lax117284.TwoSatRunningTime.bitsOf x ∈ TwoSAT then [1] else [0]) t
    rw [e]; exact hrun

end Lax117284Proofs.TwoSAT.Machine.Final
