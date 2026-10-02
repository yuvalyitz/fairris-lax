import Lax117284Proofs.Treewidth.Fun.Lib

/-!
# `Embeds` instances of the library (unary, typed) — the shape the algorithm embeddings E1–E6 use

`Embeds Δ fid P f cost`: for every `B` with `Fits B (toVal a) (cost a)` the function `fid` computes `f a` in `cost a`.
The needed size hypotheses of the `Runs` lemmas (`1 < B`, `8·len+8 < B`, …) follow from `Fits` (`Fits.cost_lt`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib

open ToVal

variable {Δ' : ℕ → Option Tm} (hΔ : Lib.Δ ⊑ Δ') {α : Type} [ToVal α]
include hΔ

end Lib

/-! ### a toy composition through the closure lemmas: `l ↦ (reverse l).length` -/

section toy
open ToVal Lib

def toyTm : Tm := .call Lib1.fLength [.call Lib2.fReverse [.var 0]]
def toyΔ : ℕ → Option Tm := Lib.extend (fun f => if f = 128 then some toyTm else none)

end toy

end Lax117284Proofs.Treewidth.Fun
