import Lax117284Proofs.Treewidth.Fun.A2Corr

/-!
# WP A3 (1): the statement `ImproveRun` (the analogue of `A2.DecompRun` for the improvement stage)

The input word of `improveDecomposition` is `x = g ++ [k, l] ++ D` (`g = n :: n²` entries, `D = d :: 3d` entries); it is read off
`x` by the header `n = x[0]`: `k = x[n²+1]`, `l = x[n²+2]`, `D = drop (n²+3) x`.

* `outWord1 x` = `1 :: D` when `l ≤ k` (the decomposition already has width `≤ k`), else `outWord (g ++ [k])`;
* `D1`  : the structurally admissible inputs (a graph word, `k`, `l`, and a word `D` whose length is `1 + 3 · D[0]`);
* `pC1 C` : the cost parameters of the top-level run, `K x = (C + 100) · 2^(C·l³) · (|x|+1)^C`, `l` = the parameter entry.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The output word of the improvement stage on `g ++ [k, l] ++ D`. -/
def outWord1 (x : List ℕ) : List ℕ :=
  if x.getD (x.getD 0 0 * x.getD 0 0 + 2) 0 ≤ x.getD (x.getD 0 0 * x.getD 0 0 + 1) 0 then
    1 :: x.drop (x.getD 0 0 * x.getD 0 0 + 3)
  else A2.outWord (x.take (x.getD 0 0 * x.getD 0 0 + 2))

/-- The structurally admissible inputs. -/
def D1 : Set (List ℕ) :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ) (k l : ℕ) (D : List ℕ),
    x = g ++ [k, l] ++ D ∧ EncodesGraph g G ∧ D.length = 1 + 3 * D.getD 0 0}

/-- The cost parameters of the top-level run (`c₀ = C + 100`, `c₁ = C`, `c₂ = 1`, `c₃ = C`). -/
def pC1 (C : ℕ) : KP := ⟨C + 100, C, 1, C⟩

/-- **What `improveRun_of` proves.**  One function table (ids `< N`), one entry `main`, one constant `C`, such that on every
admissible input the entry evaluates `[toVal x]` to `toVal (outWord1 x)` within `K x` steps at the tag bound `Bx`, and the output
is no longer than `K x`. -/
def ImproveRun : Prop :=
  ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
    ∀ x ∈ D1, Runs Δ (Bx (pC1 C) Fmt.graphKLD x) main [toVal x] (toVal (outWord1 x)) (Kx (pC1 C) Fmt.graphKLD x) ∧
      (outWord1 x).length ≤ Kx (pC1 C) Fmt.graphKLD x

end Lax117284Proofs.Treewidth.Fun.A3
