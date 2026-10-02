import Lax117284Proofs.Treewidth.Fun.Lib4
import Lax117284Proofs.Treewidth.Fun.Embeds
import Mathlib.Tactic.IntervalCases

/-!
# The F library as one table

`Lib.entries` is the library as a finite association list (ids `0 … 71`; **ids `0 … 127` are reserved for the
library**), `Lib.Δ = lookupL Lib.entries`.  Algorithm-specific functions use ids `≥ 128`:

    def eTbl : ℕ → Option Tm := …            -- ids ≥ 128 only
    def algΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 eTbl       -- `Lib.Δ ⊑ algΔ`   (`Lib.ext_layer`)

Several owners: give each a disjoint id range and a table `eTbl₁, eTbl₂ : ℕ → Option Tm`; the assembly uses
`layerΔ Lib.Δ 128 (orElseΔ eTbl₁ eTbl₂)` and `Ext.layer_mono (Ext.orElse_left …)` /
`Ext.layer_mono (Ext.orElse_right …)` to see that it extends each owner's own `layerΔ Lib.Δ 128 eTbl_i`.
All library lemmas take `hΔ : Lib_i.Δ ⊑ Δ'`; `Lib.ext1 … Lib.ext4` turn `Lib.Δ ⊑ Δ'` into that.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib

open Lib1 Lib2 Lib3 Lib4

/-- ids reserved for the library -/
abbrev reserved : ℕ := 128

def entries : List (ℕ × Tm) :=
  [ (fAppend, appendTm), (fLength, lengthTm), (fNth, nthTm), (fTake, takeTm), (fDrop, dropTm), (fMap, mapTm),
    (fFilter, filterTm), (fFoldl, foldlTm), (fFlatMap, flatMapTm), (fAny, anyTm), (fAll, allTm),
    (fRangeAux, rangeAuxTm), (fRange, rangeTm), (fZip, zipTm), (fEqV, eqVTm), (fMem, memTm), (fMin, minTm),
    (fMax, maxTm),
    (Lib2.fFoldr, foldrTm), (Lib2.fRevAux, revAuxTm), (Lib2.fReverse, reverseTm), (Lib2.fDedup, dedupTm),
    (Lib2.fIns, insTm), (Lib2.fISort, isortTm),
    (Lib3.fMemS, memSTm), (Lib3.fInsertS, insertSTm), (Lib3.fEraseS, eraseSTm), (Lib3.fUnionS, unionSTm),
    (Lib3.fInterS, interSTm), (Lib3.fDiffS, diffSTm), (Lib3.fSubsetS, subsetSTm),
    (Lib4.fFind, findTm), (Lib4.fFindSome, findSomeTm), (Lib4.fFilterMap, filterMapTm), (Lib4.fSum, sumTm),
    (Lib4.fHead, headTm), (Lib4.fToFinset, toFinsetTm), (Lib4.fSublists, sublistsTm), (Lib4.fPairUp, pairUpTm) ]

/-- The library table. -/
def Δ : ℕ → Option Tm := lookupL entries

theorem entries_lt : ∀ p ∈ entries, p.1 < reserved := by
  unfold entries; decide

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < reserved := lookupL_lt entries_lt h

/-- the layered tables of the individual files are all contained in the library table -/
theorem ext4 : Lib4.Δ ⊑ Δ := by
  intro f b h
  have hf : f < Lib4.size := Lib4.Δ_lt h
  have h72 : f < 72 := hf
  interval_cases f <;> first | (rw [← h]; rfl) | (exfalso; simp [Lib4.Δ, layerΔ, Lib3.Δ, Lib2.Δ, Lib1.Δ, Lib4.tbl, Lib3.tbl, Lib2.tbl] at h)

theorem ext3 : Lib3.Δ ⊑ Δ := Ext.trans Lib4.ext3 ext4
theorem ext2 : Lib2.Δ ⊑ Δ := Ext.trans Lib4.ext2 ext4
theorem ext1 : Lib1.Δ ⊑ Δ := Ext.trans Lib4.ext1 ext4

/-- extend the library by algorithm functions (ids `≥ 128`) -/
def extend (tbl : ℕ → Option Tm) : ℕ → Option Tm := layerΔ Δ reserved tbl

theorem ext_extend (tbl : ℕ → Option Tm) : Δ ⊑ extend tbl := Ext.layer tbl (fun _ _ h => Δ_lt h)

end Lib
end Lax117284Proofs.Treewidth.Fun
