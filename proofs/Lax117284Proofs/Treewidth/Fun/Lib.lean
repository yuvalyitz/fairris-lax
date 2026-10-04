import Lax117284Proofs.Treewidth.Fun.Kit
import Mathlib.Tactic.Linarith
import Lax117284Proofs.Treewidth.Fun.Lib4
import Mathlib.Tactic.IntervalCases

/-! ### `Lax117284Proofs.Treewidth.Fun.Embeds` -/

section
/-!
# WP F0 (3): `Embeds` and its closure lemmas

`Embeds Δ fid P f cost` — the function `fid` of the table computes the Lean function `f` on the inputs satisfying
`P`, within cost `cost a`, whenever `B` is large (`Fits`).  (Same definition as `proofs-todo/Machine.lean`.)

`EmbedsE Δ t P env f cost` is the term-level version over an arbitrary environment `env a : List Val`
(`Embeds` is the case `t = body`, `env a = [toVal a]`).  Closure lemmas: `call1` (composition with a function),
`ite`, `letE`, `var`, `lit`, `cons`, monotonicity in the precondition and in the cost.
-/

set_option linter.unusedSectionVars false

namespace Lax117284Proofs.Treewidth.Fun

open ToVal

/-- `f` is computed by the function `fid` of the table, within cost `cost a`, on every `a` with `P a`. -/
def Embeds {α β : Type} [ToVal α] [ToVal β] (Δ : ℕ → Option Tm) (fid : ℕ) (P : α → Prop) (f : α → β)
    (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → Fits B (toVal a) (cost a) → Runs Δ B fid [toVal a] (toVal (f a)) (cost a)

/-- Output-sensitive polynomial cost of degree `d`. -/
def osCost {α β : Type} [ToVal α] [ToVal β] (d : ℕ) (f : α → β) (a : α) : ℕ := 64 * (sz a + sz (f a) + 1) ^ d

/-! ### `Fits` -/

theorem Fits.cost_lt {B : ℕ} {v : Val} {c : ℕ} (h : Fits B v c) : c + 3 < B := by
  have h1 : (v.maxNat + c + 2) ^ 2 ≥ c + 3 := by nlinarith [Nat.zero_le v.maxNat, Nat.zero_le c]
  have h' : (v.maxNat + c + 2) ^ 2 < B := h
  omega

/-- the largest natural in an environment -/
def Val.maxNatL : List Val → ℕ
  | [] => 0
  | v :: vs => max v.maxNat (Val.maxNatL vs)

/-- `Fits` for a whole environment. -/
def FitsL (B : ℕ) (ρ : List Val) (c : ℕ) : Prop := (Val.maxNatL ρ + c + 2) ^ 2 < B

/-! ### term-level embeddings -/

/-- `t`, evaluated in the environment `env a`, computes `f a` within cost `cost a`. -/
def EmbedsE {α β : Type} [ToVal β] (Δ : ℕ → Option Tm) (t : Tm) (P : α → Prop) (env : α → List Val)
    (f : α → β) (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → FitsL B (env a) (cost a) → EvLe Δ B (env a) t (toVal (f a)) (cost a)

namespace EmbedsE
variable {α β γ : Type} [ToVal α] [ToVal β] [ToVal γ] {Δ : ℕ → Option Tm} {t : Tm} {P : α → Prop}
  {env : α → List Val} {f : α → β} {cost : α → ℕ}

end EmbedsE

end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.Lib` -/

section
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

end
