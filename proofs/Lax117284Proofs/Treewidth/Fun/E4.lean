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

theorem nOfWord_le_mx (x : List ℕ) : nOfWord x ≤ mx x := by
  cases x with
  | nil => simp [nOfWord]
  | cons a l => simpa [nOfWord] using mx_le_of_mem (List.mem_cons_self (a := a) (l := l))

theorem size_le_M {nt : NT} {M : ℕ} (h : sz nt ≤ M) : nt.size ≤ M := by
  have := size_le_sz_nt nt; omega

theorem tablesCost_le (nt : NT) (M k : ℕ) (h : sz nt ≤ M) :
    nt.size * cnode M k + 20 ≤ (M + 1) ^ 16 * 2 ^ (4000 * (k + 2) ^ 3) := by
  have hn := size_le_M h
  have hc := cnode_ge M k
  have h1 : nt.size * cnode M k + 20 ≤ (nt.size + 1) * cnode M k := by nlinarith
  have h2 : (nt.size + 1) * cnode M k ≤ (M + 1) * cnode M k := Nat.mul_le_mul_right _ (by omega)
  have h3 : (M + 1) * cnode M k = (M + 1) ^ 16 * 2 ^ (4000 * (k + 2) ^ 3) := by
    unfold cnode; rw [← mul_assoc, ← pow_succ']
  omega

section top
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

/-- **`tables` on the packed argument**, exact cost `nt.size · cnode M k + 20`. -/
theorem tablesUn_runs (x : List ℕ) (k : ℕ) (nt : NT) (M : ℕ) (hxM : x.length ≤ M) (hg : nt.Good (adjOfWord x))
    (hw : nt.toRT.Width (k + 1)) (hs : sz nt ≤ M) (hm : mx nt ≤ M) (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B)
    (hB : (nt.size * cnode M k + 2) ^ 2 < B) :
    Runs Δ' B fTablesUn [toVal (x, k, nt)] (toVal (tables (adjOfWord x) k nt)) (nt.size * cnode M k + 20) := by
  have hc := cnode_ge M k
  have h := tables_runs hΔ B x k M hxM hn hk nt hg hw hs hm hB
  refine Runs.mk (hΔ.e4 _ _ Δ_tablesUn) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- **`E_tables`** (unary `Embeds` form, cost in `M = |x| + sz nt + mx nt`). -/
theorem embeds_tables :
    Embeds Δ' fTablesUn (fun p : List ℕ × ℕ × NT => ntOk p.1 p.2.1 p.2.2)
      (fun p => tables (adjOfWord p.1) p.2.1 p.2.2)
      (fun p => p.2.2.size * cnode (p.1.length + sz p.2.2 + mx p.2.2) p.2.1 + 20) := by
  rintro B ⟨x, k, nt⟩ ⟨hg, hw⟩ hfit
  simp only at hg hw hfit ⊢
  have hmxv : (toVal (x, k, nt)).maxNat = max (toVal x).maxNat (max k (toVal nt).maxNat) := by
    simp only [toVal_pair, toVal_nat, Val.maxNat]
  have hc := cnode_ge (x.length + sz nt + mx nt) k
  have hn1 : nOfWord x ≤ mx x := nOfWord_le_mx x
  have hn2 : mx x = (toVal x).maxNat := rfl
  have hkB : k + 2 < B := hfit.lt (by omega)
  have hnB : (nOfWord x) ^ 2 < B := by
    have : nOfWord x ≤ (toVal (x, k, nt)).maxNat + (nt.size * cnode (x.length + sz nt + mx nt) k + 20) + 2 := by
      omega
    exact lt_of_le_of_lt (le_trans (Nat.pow_le_pow_left this 2)
      (Nat.pow_le_pow_left (by omega) 2)) hfit
  have hBc : (nt.size * cnode (x.length + sz nt + mx nt) k + 2) ^ 2 < B :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hfit
  exact tablesUn_runs hΔ B x k nt (x.length + sz nt + mx nt) (by omega) hg hw (by omega) (by omega)
    hnB hkB hBc

/-- **`E_tables`** with the labels bounded by the word length (`mx nt ≤ |x|`, true for the decompositions of the
wrapper: their vertices are `< n ≤ |x|`): the cost is a polynomial in `|x| + sz nt` times `2^(4000 (k+2)^3)`. -/
theorem E_tables :
    Embeds Δ' fTablesUn (fun p : List ℕ × ℕ × NT => ntOk p.1 p.2.1 p.2.2 ∧ mx p.2.2 ≤ p.1.length)
      (fun p => tables (adjOfWord p.1) p.2.1 p.2.2)
      (fun p => (p.1.length + sz p.2.2 + 1) ^ 16 * 2 ^ (4000 * (p.2.1 + 2) ^ 3)) := by
  rintro B ⟨x, k, nt⟩ ⟨⟨hg, hw⟩, hmx⟩ hfit
  simp only at hg hw hmx hfit ⊢
  have hcost := tablesCost_le nt (x.length + sz nt) k (by omega)
  have hmxv : (toVal (x, k, nt)).maxNat = max (toVal x).maxNat (max k (toVal nt).maxNat) := by
    simp only [toVal_pair, toVal_nat, Val.maxNat]
  have hc := cnode_ge (x.length + sz nt) k
  have hn1 : nOfWord x ≤ mx x := nOfWord_le_mx x
  have hn2 : mx x = (toVal x).maxNat := rfl
  have hkB : k + 2 < B := hfit.lt (by omega)
  have hnB : (nOfWord x) ^ 2 < B := by
    have : nOfWord x ≤ (toVal (x, k, nt)).maxNat +
        ((x.length + sz nt + 1) ^ 16 * 2 ^ (4000 * (k + 2) ^ 3)) + 2 := by omega
    exact lt_of_le_of_lt (le_trans (Nat.pow_le_pow_left this 2)
      (Nat.pow_le_pow_left (by omega) 2)) hfit
  have hBc : (nt.size * cnode (x.length + sz nt) k + 2) ^ 2 < B :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hfit
  exact (tablesUn_runs hΔ B x k nt (x.length + sz nt) (by omega) hg hw (by omega) (by omega)
    hnB hkB hBc).mono hcost

/-- `head?` of the tables (`improveC` matches on `tables … = c :: _`). -/
theorem tables_first_runs (x : List ℕ) (k : ℕ) (nt : NT) (M : ℕ) (hxM : x.length ≤ M) (hg : nt.Good (adjOfWord x))
    (hw : nt.toRT.Width (k + 1)) (hs : sz nt ≤ M) (hm : mx nt ≤ M) (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B)
    (hB : (nt.size * cnode M k + 40 + 2) ^ 2 < B) :
    Runs Δ' B fTablesFirst [toVal x, toVal k, toVal nt] (toVal (tables (adjOfWord x) k nt).head?)
      (nt.size * cnode M k + 40) := by
  have hc := cnode_ge M k
  have hB1 : 1 < B := by
    have := Nat.pow_le_pow_left (show 2 ≤ nt.size * cnode M k + 40 + 2 by omega) 2
    omega
  have h := tables_runs hΔ B x k M hxM hn hk nt hg hw hs hm
    (lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB)
  have hh := Lib4.head_runs hΔ.l4 B (tables (adjOfWord x) k nt) hB1
  refine Runs.mk (hΔ.e4 _ _ Δ_tablesFirst) ?_
  ev_start
  · ev_run
  · omega

end top

end E4
end Lax117284Proofs.Treewidth.Fun
