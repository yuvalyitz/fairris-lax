import Lax117284Proofs.Treewidth.Fun.VMSolveWrite

/-!
# WP V3 (8): the whole program `solveCom`, its layout, and the numeric quantities

`solveCom Δ N main fmt p` is the single IMP+ command of `compile_solves`:

    read the word into the heap array · compute `K`, `B` · fill `HB` · initial scalars · load `OP`, `OA`, `FT`
    · `vmLoop` · write the output list.

Numeric quantities (all functions of the input `x` and of the fixed data `Δ N main fmt p`):

* `Kx p fmt x = c₀ · 2^(c₁ kw³) · (|x| + c₂)^c₃` — the cost bound of the functional run (`kw = fmt.kw x`, the entry `k`/`l`);
* `Bx p fmt x = (maxEntry x + Kx + 2)² + 1` — the tag bound of the VM;
* `kappa Δ N main p` — the constant, `1000 ·` (program length + table size + largest operand + largest table entry
  + `c₀ + c₁ + c₂` + size of `kE` + 1);
* the IMP+ value bound `Bimp = 2 Bx + 4 (Kx + |x| + 8) + kappa`, the word bound `Wx`, the array length `Wx + 1`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram

/-- The input formats: `g ++ [k]` and `g ++ [k, l] ++ D` (`g = n :: n²` adjacency entries, `D = d :: 3d` entries). -/
inductive Fmt where
  | graphK
  | graphKLD
  deriving DecidableEq

def nOfWord (x : List ℕ) : ℕ := x.getD 0 0

/-- The length of the word in the format, read off the header. -/
def fmtLen : Fmt → List ℕ → ℕ
  | .graphK, x => nOfWord x * nOfWord x + 2
  | .graphKLD, x => 1 + nOfWord x * nOfWord x + 2 + 1 + 3 * x.getD (1 + nOfWord x * nOfWord x + 2) 0

/-- Position of the parameter entry: `k` (last entry) for `graphK`, `l` for `graphKLD`, relative to `n²`. -/
def Fmt.off : Fmt → ℕ
  | .graphK => 1
  | .graphKLD => 2

/-- The parameter entry of the word (`k`, resp. `l`). -/
def Fmt.kw (fmt : Fmt) (x : List ℕ) : ℕ := x.getD (x.getD 0 0 * x.getD 0 0 + fmt.off) 0

def Fmt.loadCom : Fmt → Com
  | .graphK => loadK
  | .graphKLD => loadKLD

/-- The largest entry of a word. -/
def maxEntry (x : List ℕ) : ℕ := x.foldr max 0

theorem maxEntry_eq (x : List ℕ) : maxEntry x = wordMax x := rfl

/-- The cost bound. -/
def Kx (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ := p.k x.length (fmt.kw x)

/-- The tag bound of the VM. -/
def Bx (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ := bexp (maxEntry x) (Kx p fmt x)

/-! ## The constants of the program -/

def progLen (Δ : ℕ → Option Tm) (N main : ℕ) : ℕ := (codeL Δ N main).length

def kS (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ :=
  progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 + (kE p).size + 1

def kappa (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ := 1000 * kS Δ N main p

/-- The IMP+ value bound. -/
def Bimp (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  2 * Bx p fmt x + 4 * (Kx p fmt x + x.length + 8) + kappa Δ N main p

/-- The IMP+ cost bound. -/
def Cimp (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  kappa Δ N main p * (Kx p fmt x + x.length + 1)

/-- The word bound of the VM run: `W₀ + len + B + 3K + 3` with `W₀ = B + |x| + 1`. -/
def Wx (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  (Bx p fmt x + x.length + 1) + progLen Δ N main + Bx p fmt x + 3 * Kx p fmt x + 3

/-! ## The program -/

def solveCom (Δ : ℕ → Option Tm) (N main : ℕ) (fmt : Fmt) (p : KP) : Com :=
  .seq fmt.loadCom (.seq (setKB fmt.off p) (.seq hbCom (.seq setupCom
    (.seq (storeSeq "OP" 0 (opsL Δ N main)) (.seq (storeSeq "OA" 0 (opasL Δ N main))
      (.seq (storeSeq "FT" 0 (ftL Δ N)) (.seq vmLoop wrCom)))))))

/-- The layout: the interpreter's plus the loader's scalars. -/
def solveLayout : Layout where
  scalars := ["pc", "sp", "rp", "hp", "B", "run", "op", "oa", "t1", "t2", "i", "tot", "v", "M", "len", "kw", "K", "w"]
  arrays := arrNames
  temps := 8

/-! ## Compilability -/

macro "okS" : tactic => `(tactic| simp [Com.Ok, Cond.Ok, Expr.Ok, condExpr, solveLayout, arrNames, V, L, G, pl, ml, mi,
  bump])

theorem ok_hdrCom (t0 : ℕ) : Com.Ok solveLayout (hdrCom t0) := by unfold hdrCom; okS
theorem ok_rdOne : Com.Ok solveLayout rdOne := by unfold rdOne; okS
theorem ok_rdLoop : Com.Ok solveLayout rdLoop := by unfold rdLoop; simp only [Com.Ok]; refine ⟨?_, ok_rdOne⟩; okS
theorem ok_loadK : Com.Ok solveLayout loadK := ⟨ok_hdrCom 2, ok_rdLoop⟩
theorem ok_loadKLD : Com.Ok solveLayout loadKLD := by
  unfold loadKLD
  refine ⟨ok_hdrCom 3, ok_rdLoop, ok_rdOne, ?_, ok_rdLoop⟩
  okS

theorem ok_loadCom (fmt : Fmt) : Com.Ok solveLayout fmt.loadCom := by
  cases fmt
  · exact ok_loadK
  · exact ok_loadKLD

theorem pwE_ok {Ly : Layout} {e : Expr} {d : ℕ} (h1 : Expr.Ok Ly e (d + 1))
    (hd : d < Ly.temps) : ∀ n, Expr.Ok Ly (pwE e n) d := by
  intro n
  induction n with
  | zero => exact Expr.ok_lit _ _ _
  | succ n ih => exact ⟨ih, h1, hd⟩

theorem ok_kE (p : KP) : Expr.Ok solveLayout (kE p) 0 := by
  unfold kE
  refine ⟨?_, ?_, by simp [solveLayout]⟩
  · refine pwE_ok ?_ (by simp [solveLayout]) _
    simp [Expr.Ok, solveLayout, pl, V, L]
  · simp [Expr.Ok, solveLayout, ml, V, L]

theorem ok_setKB (off : ℕ) (p : KP) : Com.Ok solveLayout (setKB off p) := by
  unfold setKB
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Com.Ok, Expr.Ok, solveLayout, V]
  · simp [Com.Ok, Expr.Ok, solveLayout, V, L, G, pl, ml, arrNames]
  · exact ⟨by simp [solveLayout], ok_kE p⟩
  · refine ⟨by simp [solveLayout], ?_⟩
    simp [bE, Expr.Ok, solveLayout, V, L, pl, ml]

theorem ok_hbCom : Com.Ok solveLayout hbCom := by
  unfold hbCom hbLoop hbBody; okS

theorem ok_setupCom : Com.Ok solveLayout setupCom := by unfold setupCom; okS

theorem ok_wrCom : Com.Ok solveLayout wrCom := by unfold wrCom wrLoop wrBody; okS

theorem ok_vmLoop' : Com.Ok solveLayout vmLoop :=
  com_ok_mono (L := Lvm) (L' := solveLayout) (by intro x hx; simp [Lvm] at hx; simp [solveLayout]; tauto)
    (by intro a ha; exact ha) (by simp [Lvm, solveLayout]) _ ok_vmLoop

theorem ok_solveCom (Δ : ℕ → Option Tm) (N main : ℕ) (fmt : Fmt) (p : KP) :
    Com.Ok solveLayout (solveCom Δ N main fmt p) := by
  have h0 : 0 < solveLayout.temps := by simp [solveLayout]
  unfold solveCom
  refine ⟨ok_loadCom fmt, ok_setKB _ p, ok_hbCom, ok_setupCom, ?_, ?_, ?_, ok_vmLoop', ok_wrCom⟩
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _

end Lax117284Proofs.Treewidth.Fun.Load
