import Lax117284Proofs.Treewidth.Fun.VMSolveRun

/-!
# WP V3 (11): `compile_solves` — the compiler theorem

`solve_solves` : the single IMP+ program `solveCom Δ N main fmt p` under the layout `solveLayout` **solves** the function `f`
(`Transfer.Solves`) on every set `D` of words of the format `fmt` on which the table `Δ` computes `f` functionally:

    `Runs Δ (Bx x) main [toVal x] (toVal (f x)) (Kx x)`  and  `|f x| ≤ Kx x`

with the explicit bounds `Bimp = 2 Bx + 4 (Kx + |x| + 8) + κ` (IMP+ values) and `Cimp = κ (Kx + |x| + 1)` (IMP+ cost), where
`Kx = c₀ · 2^(c₁ kw³) · (|x| + c₂)^c₃`, `Bx = (maxEntry x + Kx + 2)² + 1`, `kw` = the parameter entry (`k`, resp. `l`).

`compile_solves` is the `∃ layout, program, κ, ∀ D f, …` form asked for by `proofs-todo/Machine.lean`, modified in two ways that
the mathematics forces: (i) the tag bound `Bv` and the cost bound `K` are the closed formulas above rather than arbitrary
functions (the program is fixed before them, so it must be able to *compute* them); (ii) the output length is charged
(`|f x| ≤ Kx x`): a value's tree size is not bounded by the derivation cost (`cons (var 0) (var 0)` doubles the size).
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal
open Lax808846Proofs.Transfer

theorem solve_solves (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt) (p : KP)
    (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) {D : Set (List ℕ)} {f : List ℕ → List ℕ}
    (hfmt : ∀ x ∈ D, fmtLen fmt x = x.length)
    (hruns : ∀ x ∈ D, Runs Δ (Bx p fmt x) main [toVal x] (toVal (f x)) (Kx p fmt x))
    (hlen : ∀ x ∈ D, (f x).length ≤ Kx p fmt x) :
    Solves solveLayout (solveCom Δ N main fmt p) D f (Bimp Δ N main p fmt) (Cimp Δ N main p fmt) where
  ok := ok_solveCom Δ N main fmt p
  inp := by
    intro x hx v hv
    have := entry_lt_Bx p fmt x v hv
    unfold Bimp; omega
  run := by
    intro x hx
    obtain ⟨σ', hr, ho⟩ := solve_run Δ hN main fmt p h0 h1 h2 (hfmt x hx) (hruns x hx) (hlen x hx)
    exact ⟨_, σ', hr, ho⟩

end Lax117284Proofs.Treewidth.Fun.Load
