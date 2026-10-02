import Lax391470Proofs.L2Scan
import Lax117284Proofs.TwoSAT.Machine.Model

/-!
The first phase of the program: the word is in the array `a` with its length in `L`, and the
scan of `lax-391470` reads the formula off its bits into the arrays `vr`, `sg`, `cl`, leaving
the phase of the scan in `ph` (`4` for an accepted encoding), the numbers of literals and
clauses in `k` and `C`, and one more than the largest index in `mx`.

Everything here is the verified scanner of `lax-391470`, applied; what is added is the reading
of its invariant into the facts the later phases consume.
-/

namespace Lax117284Proofs.TwoSAT.Machine.Scan

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan
open Lax391470Proofs.Bits Lax117284Proofs.TwoSAT.Machine.Model

/-- The state of the scan on the bits of a word. -/
def st (y : List ℕ) : St := run init (bitsOf y)

/-- The formula a word scans to: the clauses completed. -/
def formulaOf (y : List ℕ) : Formula := (st y).done

/-- The word is accepted by the scan. -/
def Accepted (y : List ℕ) : Prop := (st y).ph = 4

/-- The scan, after the word has been read: the index bound starts at `1`. -/
def scanPart : Com := .seq (.assign "mx" (.lit 1)) scanLoop

/-- What the reader leaves and the scan needs. -/
structure ReadPost (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  L : σ.vars "L" = y.length
  a : σ.arrs "a" = y
  out : σ.out = []
  zero : ∀ x, x ∉ ["L", "rt", "rv", "len"] → σ.vars x = 0
  arr : ∀ b, b ≠ "a" → σ.arrs b = List.replicate (ext b) 0

/-- What the scan leaves, in terms of the state of the abstract scan. -/
structure ScanPost (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  ph : σ.vars "ph" = (st y).ph
  C : σ.vars "C" = (st y).done.length
  k : σ.vars "k" = (flat (st y)).length
  mx : σ.vars "mx" = mxOf (flat (st y))
  vr : (σ.arrs "vr").take (flat (st y)).length = (flat (st y)).map Literal.index
  sg : (σ.arrs "sg").take (flat (st y)).length =
    (flat (st y)).map fun l => if l.positive then 1 else 0
  cl : (σ.arrs "cl").take (flat (st y)).length = nums (st y)
  lvr : (σ.arrs "vr").length = y.length
  lsg : (σ.arrs "sg").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  out : σ.out = []
  arr : ∀ b, b ∉ ["a", "vr", "sg", "cl"] → σ.arrs b = List.replicate (ext b) 0

lemma warrs_scan : scanLoop.warrs = ["vr", "sg", "sg", "cl"] := by
  simp [scanLoop, scanBody, dispatch, phase3, Com.warrs]

variable {B : ℕ} {y : List ℕ} {ext : String → ℕ}

/-- **The scan.** -/
theorem scanPart_spec (hB : y.length + 8 < B) (hyB : ∀ v ∈ y, v < B)
    (hext : ext "vr" = y.length ∧ ext "sg" = y.length ∧ ext "cl" = y.length) :
    Spec B (ReadPost y ext) scanPart (fun _ σ' => ScanPost y ext σ') (2 + (64 * y.length + 6)) := by
  intro σ1 h1
  have r2 : Run B (.assign "mx" (.lit 1)) σ1 (σ1.setVar "mx" 1) (1 + (Expr.lit 1).size) :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σ3, r3, ⟨I3, p3⟩, -, fa3, -, -⟩ := (scanLoop_spec (B := B) (y := y) hB hyB).frame
    (σ1.setVar "mx" 1) (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init, flat, lits, nums, cn, mxOf]
    · exact h1.zero "ph" (by decide)
    · exact h1.zero "n" (by decide)
    · exact h1.zero "C" (by decide)
    · exact h1.zero "k" (by decide)
    · exact h1.a
    · exact h1.L
    · rw [h1.arr "vr" (by decide)]; simp [hext.1]
    · rw [h1.arr "sg" (by decide)]; simp [hext.2.1]
    · rw [h1.arr "cl" (by decide)]; simp [hext.2.2]
    · exact h1.out)
  obtain ⟨hR, -, -, -, lvr, lsg, lcl, out3⟩ := I3
  have hst : stAt y (σ3.vars "p") = st y := by
    rw [p3]; unfold stAt st; rw [List.take_length]
  rw [hst] at hR
  refine ⟨σ3, (r2.seq r3).mono (by simp), ?_⟩
  refine ⟨hR.ph, hR.C, hR.k, hR.mx, hR.vr, hR.sg, hR.cl, lvr, lsg, lcl, out3, ?_⟩
  · intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
    rw [fa3 b (by rw [warrs_scan]; simp; tauto)]
    simp only [Env.setVar]
    exact h1.arr b hb.1

/-! ### Reading the result of an accepted scan -/

lemma getD_of_take (l : List ℕ) (K i : ℕ) (hi : i < K) : l.getD i 0 = (l.take K).getD i 0 := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma getD_map {α : Type} (l : List α) (f : α → ℕ) (d : α) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]

theorem cur_nil (h : Accepted y) : (st y).cur = [] :=
  (run_inv (bitsOf y) (by unfold Accepted st at *; omega)).1 (Or.inr h)

theorem flat_eq (h : Accepted y) : flat (st y) = lits (formulaOf y) := by
  simp [flat, cur_nil h, formulaOf]

theorem nums_eq (h : Accepted y) : nums (st y) = cn (formulaOf y) := by
  simp [nums, cur_nil h, formulaOf]

/-- The sizes the scan produces are bounded by the length of the word. -/
theorem sizes_le (h : Accepted y) :
    (lits (formulaOf y)).length ≤ y.length ∧ (formulaOf y).length ≤ y.length ∧
      mxOf (lits (formulaOf y)) ≤ y.length + 1 := by
  have hs : Lax391470Proofs.L2ScanModel.size (st y) ≤ (bitsOf y).length := size_run (bitsOf y)
  have hl : (bitsOf y).length = y.length := by simp [bitsOf]
  simp only [Lax391470Proofs.L2ScanModel.size, hl, flat_eq h] at hs
  unfold formulaOf at hs ⊢
  omega

/-- **The facts an accepted scan leaves**, in terms of the formula. -/
structure Facts (F : Formula) (y : List ℕ) (ext : String → ℕ) (σ : Env) : Prop where
  C : σ.vars "C" = F.length
  k : σ.vars "k" = (lits F).length
  mx : σ.vars "mx" = mxOf (lits F)
  vr : ∀ i < (lits F).length, (σ.arrs "vr").getD i 0 = iv F i
  sg : ∀ i < (lits F).length, (σ.arrs "sg").getD i 0 = sv F i
  cl : ∀ i < (lits F).length, (σ.arrs "cl").getD i 0 = cv F i
  lvr : (σ.arrs "vr").length = y.length
  lsg : (σ.arrs "sg").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  out : σ.out = []
  arr : ∀ b, b ∉ ["a", "vr", "sg", "cl"] → σ.arrs b = List.replicate (ext b) 0
  hk : (lits F).length ≤ y.length
  hC : F.length ≤ y.length
  hmx : mxOf (lits F) ≤ y.length + 1

theorem ScanPost.facts {σ : Env} (hσ : ScanPost y ext σ) (h : Accepted y) :
    Facts (formulaOf y) y ext σ := by
  have e1 := hσ.vr; have e2 := hσ.sg; have e3 := hσ.cl
  rw [flat_eq h] at e1 e2 e3
  rw [nums_eq h] at e3
  have hk := hσ.k; rw [flat_eq h] at hk
  have hmx := hσ.mx; rw [flat_eq h] at hmx
  obtain ⟨s1, s2, s3⟩ := sizes_le h
  refine ⟨hσ.C, hk, hmx, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, hσ.lvr, hσ.lsg,
    hσ.lcl, hσ.out, hσ.arr, s1, s2, s3⟩
  · rw [getD_of_take _ _ _ hi, e1, getD_map _ _ dflt _ hi]; rfl
  · rw [getD_of_take _ _ _ hi, e2, getD_map _ _ dflt _ hi]; rfl
  · rw [getD_of_take _ _ _ hi, e3]; rfl

end Lax117284Proofs.TwoSAT.Machine.Scan
