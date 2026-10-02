import Lax117284Proofs.Treewidth.Fun.VMRamTop

/-!
# WP V2 (7): a smoke test — the hypotheses of `vm_ram_correct` are satisfiable

The table `Δ₀ 0 = lit 5`; the environment `σ₀` is the one a loader would leave (arrays `OP`, `OA`, `FT` filled,
other arrays zero); `vm_ram_correct` then runs the interpreter to a representation of the value `5`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram.Example

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def Δ₀ : ℕ → Option Tm := fun f => if f = 0 then some (.lit 5) else none

/-- The machine program of `Δ₀` (one function, entry `0` of arity `0`, `B = 10`). -/
abbrev P₀ : Prog := mkProg Δ₀ 1 0 0 10

/-- The word bound `W₀ + len + B + 3c + 3` for `W₀ = 0`, `c = 1` (here `len = 5`, so `W = 21`). -/
abbrev W₀' : ℕ := 0 + P₀.len + 10 + 3 * 1 + 3

def σ₀ : Lax808846Proofs.Imp.Env where
  vars := fun x => if x = "B" then 10 else if x = "run" then 1 else 0
  arrs := fun a =>
    if a = "OP" then arrOf (W₀' + 1) (fun i => opc (P₀.code i))
    else if a = "OA" then arrOf (W₀' + 1) (fun i => opa (P₀.code i))
    else if a = "FT" then arrOf (W₀' + 1) P₀.ft
    else List.replicate (W₀' + 1) 0
  inp := []
  out := []

end Lax117284Proofs.Treewidth.Fun.VM.Ram.Example
