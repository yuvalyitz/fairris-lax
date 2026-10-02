import Lax117284Proofs.Treewidth.Fun.VMSolveGuard
import Lax117284Proofs.Treewidth.Fun.E4Defs
import Lax117284Proofs.Treewidth.Wrap.ImproveC
import Lax117284.GraphWords

/-!
# The shared statement between the assembly A1 and the concept statements A2/A3

`DecompRun` is what the top-level functional program must deliver (A1 proves it); the two concept statements
`niceDecomposition_computable` and `improveDecomposition` are derived from it through the compiler
(`Load.compile_computes`) by A2 and A3 without looking at the program.
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The output word of the exact algorithm on the input word `g ++ [k]` (P0's `decomposeC` with the
adjacency read off the word). -/
def outWord (x : List ℕ) : List ℕ :=
  match Lax117284Proofs.Treewidth.Chars.decomposeC (E4.adjOfWord x) (Fmt.graphK.kw x) (x.getD 0 0) with
  | none => [0]
  | some t => 1 :: t.encode

/-- The admissible inputs: the word of a graph followed by `k`. -/
def D2 : Set (List ℕ) :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ) (k : ℕ), x = g ++ [k] ∧ EncodesGraph g G}

/-- The cost parameters of the top-level run: `K x = C · 2^(C·k³) · (|x|+1)^C`. -/
def pC (C : ℕ) : KP := ⟨C, C, 1, C⟩

/-- **What A1 proves.**  One function table `Δ` (finite: ids `< N`), one entry `main` and one constant `C` such that on every
admissible input the entry evaluates `[toVal x]` to `toVal (outWord x)` within `K x` steps at the tag bound `Bx`,
and the output is no longer than `K x`. -/
def DecompRun : Prop :=
  ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
    ∀ x ∈ D2, Runs Δ (Bx (pC C) Fmt.graphK x) main [toVal x] (toVal (outWord x)) (Kx (pC C) Fmt.graphK x) ∧
      (outWord x).length ≤ Kx (pC C) Fmt.graphK x

end Lax117284Proofs.Treewidth.Fun.A2
