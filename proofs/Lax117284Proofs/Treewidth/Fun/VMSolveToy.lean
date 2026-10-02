import Lax117284Proofs.Treewidth.Fun.VMSolveGuard
import Lax117284Proofs.Treewidth.Fun.LibEmbeds

/-!
# GATE G1: an end-to-end toy — `x ↦ x.reverse` on words of the format `graphK`, through the compiler

The smallest real function of the library (`Lib2.fReverse`, embedded in `LibEmbeds.embeds_reverse`) is compiled to a single word-RAM
program (`compileProgram solveLayout (solveCom Lib.Δ 128 34 Fmt.graphK toyP)`), and `ComputesInTime` is proved for it.
No axioms, no `sorry`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load.Toy

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax117284Proofs.Treewidth.Fun.VM.Ram Lax808846.Ram Lax808846.RamComputes ToVal

/-- The cost formula of the toy: `K x = 22 · 2^(kw³) · (|x| + 1)`. -/
def toyP : KP := ⟨22, 1, 1, 1⟩

/-- Admissible inputs: the words `n :: (n² entries) ++ [k]`. -/
def Dtoy : Set (List ℕ) := {x | fmtLen Fmt.graphK x = x.length}

end Lax117284Proofs.Treewidth.Fun.Load.Toy
