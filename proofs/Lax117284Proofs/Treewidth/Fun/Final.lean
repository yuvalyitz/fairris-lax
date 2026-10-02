import Lax117284Proofs.Treewidth.Fun.A1Final
import Lax117284Proofs.Treewidth.Fun.A3Main
import Lax117284.BodlaenderGeneral
import Lax117284.BodlaenderKloks

/-!
# The two concept statements, proved

`niceDecomposition_computable` (Bodlaender–Kloks, a nice tree decomposition of width at most `k` in time
`c·2^(c·k³)·(|g|+2)^c`) and `improveDecomposition` (Bodlaender–Kloks' improvement step, in time
`c·2^(c·ℓ³)·(|input|+2)^c`), from the exact algorithm.

The algorithm is the vertex-by-vertex wrapper `decomposeC` around Bodlaender–Kloks' dynamic programming over
characteristics of partial decompositions (typical sequences, normal form, introduce/forget/join, extraction of a decomposition
from a table entry).  Its correctness is `Wrap/ImproveC` and `Chars/*`; its running time is obtained by running the
Lean functions themselves on a verified virtual machine for a first-order functional fragment (`Fun/*`), compiled to a word RAM
program by the archive's verified pipeline; the cost analysis is in `Fun/E*` and `Fun/A1*`, the concept-level transfer in `Fun/A2*`, `Fun/A3*`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Final

/--
---
conclusion: Lax117284.BodlaenderGeneral.niceDecomposition_computable
---
Bodlaender's theorem with Kloks' niceness on a word RAM, proved by running the exact Bodlaender–Kloks algorithm (the vertex-by-vertex
wrapper around the dynamic program over characteristics) as a functional program on a verified virtual machine and compiling it.
-/
theorem niceDecomposition_computable_proved :
    type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  A2.niceDecomposition_computable_of A1.decompose_run

/--
---
conclusion: Lax117284.BodlaenderKloks.improveDecomposition
---
The improvement step of Bodlaender–Kloks on a word RAM: given a nice decomposition of width `ℓ` it returns one of width at most `k`
or `[0]`, proved by a dispatcher over the same exact algorithm (if `ℓ ≤ k` the given decomposition is returned; otherwise the main
algorithm runs on the graph and `k`).
-/
theorem improveDecomposition_proved :
    type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  A3.improveDecomposition_of A1.decompose_run

end Lax117284Proofs.Treewidth.Fun.Final

example : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  Lax117284Proofs.Treewidth.Fun.Final.niceDecomposition_computable_proved

example : type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  Lax117284Proofs.Treewidth.Fun.Final.improveDecomposition_proved
