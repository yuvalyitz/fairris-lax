import Lax117284Proofs.Treewidth.Fun.E4Tables

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4: `tables` is computed in the table `e4Tbl` (ids `384 … 396`) — `E_tables`

`e4Tbl : ℕ → Option Tm` (`E4Defs`); `e4Δ = layerΔ Lib.Δ 128 e4Tbl`.  Every theorem is stated for an arbitrary table `Δ'`
with `Ext4 Δ'` (it contains the tables of E1, E2 (with `ringTypList` at `152`), E3 and `e4Δ`); the assembly obtains
`Ext4` from `E4Assembly.ext4_asm`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `adjOfWord x u v` | `fAdjW = 384` | `[x, u, v]` | `adjW_runs` | `28 |x| + 60` (`E4Base`) |
| `nbrs (adjOfWord x) v B` | `fNbrs = 386` | `[x, v, B]` | `nbrs_runs` | `|B| (28 |x| + 120) + 60` (`E4Base`) |
| `NT.bag nt` | `fNtBag = 387` | `[nt]` | `ntBag_runs` | `60 (sz nt)^2` (`E4Base`) |
| `forgetTable` | `fForgetTable = 388` | `[x, T]` | `forgetTable_runs` | `7300 (s+1)^5 (L+1)^2` (`E4Steps`) |
| `introTable` | `fIntroTable = 390` | `[kmax, v, N, T]` | `introTable_runs` | `introCostF` (`E4Steps`) |
| `joinTable` | `fJoinTable = 393` | `[kmax, Ta, Tb]` | `joinTable_runs` | `joinCostF` (`E4Steps`) |
| **`tables`** | `fTables = 394` | `[x, k, nt]` | **`tables_runs`** (`E4Tables`) | `nt.size · cnode M k` |
| `tables` (packed) | `fTablesUn = 395` | `[(x, k, nt)]` | **`E_tables`** | `(|x| + sz nt + 1)^16 · 2^(4000 (k+2)^3)` |
| `(tables …).head?` | `fTablesFirst = 396` | `[x, k, nt]` | `tables_first_runs` | as `tables`, `+ 40` |

`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)` with `M ≥ |x|, sz nt, mx nt`.  Adjacency is read from the word `x`
(`adjOfWord`, as in `proofs-todo/Machine.lean`); **no symmetry and no well-formedness of the word is needed** (`nth` returns `0`
out of range, exactly `List.getD`); the hypotheses are `nt.Good (adjOfWord x)` and `nt.toRT.Width (k+1)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

/-- the side conditions of the machine layer (`ntOk` of `proofs-todo/Machine.lean`) -/
def ntOk (x : List ℕ) (k : ℕ) (nt : NT) : Prop := nt.Good (adjOfWord x) ∧ nt.toRT.Width (k + 1)

theorem size_le_M {nt : NT} {M : ℕ} (h : sz nt ≤ M) : nt.size ≤ M := by
  have := size_le_sz_nt nt; omega

section top
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

end top

end E4
end Lax117284Proofs.Treewidth.Fun
