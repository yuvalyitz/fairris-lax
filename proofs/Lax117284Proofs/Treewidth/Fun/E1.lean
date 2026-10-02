import Lax117284Proofs.Treewidth.Fun.E1Path

/-!
# WP E1: the table `e1Tbl` (ids `128 … 157`) and the `Embeds` statements of the sequence layer

`e1Tbl : ℕ → Option Tm` has the functions of layers A–D of `E1Seq / E1Wit / E1Lat / E1Path`;
`e1Δ = Lib.extend e1Tbl = layerΔ Lib.Δ 128 e1Tbl`.  Every `Runs`/`Embeds` theorem of E1 is stated for an arbitrary
extension `Δ'` of the layer table of the file it lives in; `E1.ext : E1D.Δ ⊑ e1Δ` (and hence, by `Ext.trans`, every
layer's table is contained in `e1Δ` and in any larger assembly `layerΔ Lib.Δ 128 (orElseΔ e1Tbl …)`, see
`E1.ext_orElse_left`).

| function | id | file | `Runs` lemma (cost) | unary `Embeds` |
|---|---|---|---|---|
| `Seq.typical` | `fTypical = 134` | `E1Seq` | `typical_runs` `110 (n+1)^3` | `embeds_typical`, `embeds_typical_os` (`osCost 3`) |
| `Seq.cut`, `Seq.push` | `130`, `131` (`132`: `foldl` convention) | `E1Seq` | `cut_runs` `60 (n+1)^2`, `push_runs` `80 (n+1)^2` | — |
| `Seq.domB` | `fDomB = 135` (`fDomBP = 136`, pair) | `E1Seq` | `domB_runs` `60·3^(|a|+|b|)` (exponential, as the Lean recursion) | `embeds_domB` |
| `Chars.witnesses` (`wpush`, `witnessesAux`) | `fWitnesses = 141` (`138`, `139`) | `E1Wit` | `witnesses_runs` `150 (n+1)^3` | `embeds_witnesses`, `_os` |
| `Chars.dedupKey`, `cellOf`, `rowCells`, `latticeRows` | `144, 146, 147, 148` | `E1Lat` | `dedupKey_runs`, `cellOf_runs`, `rowCells_runs`, `latRows_runs` | — |
| `Chars.latticeStates` | `fLatticeStates = 150` | `E1Lat` | `latticeStates_runs` | — |
| `CT.ringTypList` | `fRingTypList = 152` (`fRingTypListP = 153`, pair) | `E1Lat` | `ringTypList_runs` `6000 (|a|+1)(|b|+1)(4^(L₁+L₂+1)+1)^2 (2(L₁+L₂)+3)^2`, entries `≤ L₁, L₂` | `embeds_ringTypList` (`ringCost`, `L = maxOf`) |
| `Chars.findPath` | `fFindPath = 156` (`fFindPathP = 157`, 4-tuple) | `E1Path` | `findPath_runs` (lattice DP + `4^(L+1)` many `domB`s) | `embeds_findPath` (`findPathCost`) |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E1

/-- The functions of WP E1: ids `128 … 157`. -/
def e1Tbl : ℕ → Option Tm := fun f =>
  if 154 ≤ f then E1D.tbl f else if 142 ≤ f then E1C.tbl f else if 137 ≤ f then E1B.tbl f else E1A.tbl f

/-- The library extended by the E1 functions. -/
def e1Δ : ℕ → Option Tm := Lib.extend e1Tbl

theorem e1Tbl_lt {f : ℕ} {b : Tm} (h : e1Tbl f = some b) : f < 158 := by
  by_contra hf
  have : 154 ≤ f := by omega
  simp only [e1Tbl, this, if_true] at h
  have h2 : E1D.Δ f = some b := by
    simp [E1D.Δ, layerΔ, this, h]
  have := E1D.Δ_lt h2
  simp [E1D.size] at this
  omega

/-- every layer table is contained in `e1Δ`. -/
theorem ext : E1D.Δ ⊑ e1Δ := by
  intro f b h
  unfold e1Δ Lib.extend layerΔ
  unfold E1D.Δ layerΔ at h
  by_cases h1 : 154 ≤ f
  · simp only [h1, if_true] at h
    have : 128 ≤ f := by omega
    simp [this, e1Tbl, h1, h]
  · simp only [h1, if_false] at h
    unfold E1C.Δ layerΔ at h
    by_cases h2 : 142 ≤ f
    · simp only [h2, if_true] at h
      have : 128 ≤ f := by omega
      simp [this, e1Tbl, h1, h2, h]
    · simp only [h2, if_false] at h
      unfold E1B.Δ layerΔ at h
      by_cases h3 : 137 ≤ f
      · simp only [h3, if_true] at h
        have : 128 ≤ f := by omega
        simp [this, e1Tbl, h1, h2, h3, h]
      · simp only [h3, if_false] at h
        unfold E1A.Δ layerΔ at h
        by_cases h4 : 128 ≤ f
        · simp only [h4, if_true] at h
          simp [h4, e1Tbl, h1, h2, h3, h]
        · simp only [h4, if_false] at h
          simp [h4, h]

theorem extA : E1A.Δ ⊑ e1Δ := Ext.trans E1D.extA ext
theorem extB : E1B.Δ ⊑ e1Δ := Ext.trans E1D.extB ext
theorem extC : E1C.Δ ⊑ e1Δ := Ext.trans E1D.extC ext
theorem extLib : Lib.Δ ⊑ e1Δ := Lib.ext_extend e1Tbl

/-! ### the statements for the assembled table `e1Δ` (use `Embeds.ext` to pass to a larger table) -/

end E1
end Lax117284Proofs.Treewidth.Fun
