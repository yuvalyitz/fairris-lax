import Lax117284Proofs.Treewidth.Fun.LibEmbeds
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Fun.E1Seq

/-!
# WP E2: the table `e2Tbl` (ids `160 … 255`) — `norm`, `forgetC`, `joinC`, `domCB` as F-functions

Ids:

| id | function | arguments |
|---|---|---|
| 160 `fVerts` | `CT.verts` | `[c]` |
| 161 `fVertsL` | `CT.vertsL` | `[ks]` |
| 162 `fKeyLe` | `decide (key S a ≤ key S b)` | `[S, a, b]` |
| 163 `fSortKids` | `CT.sortKids` | `[S, ks]` |
| 164 `fKeep` | `CT.keep` | `[S, k]` |
| 165 `fNormNode` | `CT.normF`-shaped `normNode` on the *filtered/normalised* kids | `[S, y, ks]` |
| 166 `fNorm` | `CT.norm` | `[c]` |
| 167 `fNormC` | `norm` with a dummy context (calling convention of `map`) | `[ctx, c]` |
| 168 `fRelE` | `CT.relabel (·.erase x)` (also usable as a `map` callee) | `[x, c]` |
| 169 `fForgetC` | `CT.forgetC` | `[x, c]` |
| 170 `fSubC` | `e - c` (`map` callee) | `[c, e]` |
| 171 `fSubMap` | `d.map (· - c)` (`map` callee) | `[c, d]` |
| 172 `fLeK` | `decide (e ≤ kmax)` | `[kmax, e]` |
| 173 `fAllLe` | `d.all (· ≤ kmax)` | `[kmax, d]` |
| 174 `fJoinYs` | the list `ys` of `joinC` | `[S, kmax, y, y']` |
| 175 `fMkNode` | `node S d kk` (`map` callee, context `(S, kk)`) | `[(S, kk), d]` |
| 176 `fMapKK` | `ys.map (node S · kk)` (`flatMap` callee, context `(S, ys)`) | `[(S, ys), kk]` |
| 177 `fJoinC` | `CT.joinC` | `[kmax, a, b]` |
| 178 `fJoinKids` | `CT.joinKids` | `[kmax, ks, ks']` |
| 179 `fConsTo` | `c :: l` | `[c, l]` |
| 180 `fConsAll` | `rest.map (c :: ·)` (`flatMap` callee, context `rest`) | `[rest, c]` |
| 181 `fDomC` | `CT.domCB` | `[a, b]` |
| 182 `fDomCL` | `CT.domCBL` | `[ks, ks']` |

The function `ringTypList` (WP E1) is called through an id `rid` that the assembler chooses (`e2Tbl rid`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open Lib1

abbrev fVerts : ℕ := 160
abbrev fVertsL : ℕ := 161
abbrev fKeyLe : ℕ := 162
abbrev fSortKids : ℕ := 163
abbrev fKeep : ℕ := 164
abbrev fNormNode : ℕ := 165
abbrev fNorm : ℕ := 166
abbrev fNormC : ℕ := 167
abbrev fRelE : ℕ := 168
abbrev fForgetC : ℕ := 169
abbrev fSubC : ℕ := 170
abbrev fSubMap : ℕ := 171
abbrev fLeK : ℕ := 172
abbrev fAllLe : ℕ := 173
abbrev fJoinYs : ℕ := 174
abbrev fMkNode : ℕ := 175
abbrev fMapKK : ℕ := 176
abbrev fJoinC : ℕ := 177
abbrev fJoinKids : ℕ := 178
abbrev fConsTo : ℕ := 179
abbrev fConsAll : ℕ := 180
abbrev fDomC : ℕ := 181
abbrev fDomCL : ℕ := 182

/-- `a ≤ b` as a term (`1 - (b < a)`). -/
abbrev leT (a b : Tm) : Tm := .sub (.lit 1) (.lt b a)

-- accessors of a characteristic `node S y ks = cons S (cons y ks)`
abbrev cS (t : Tm) : Tm := .fst t
abbrev cY (t : Tm) : Tm := .fst (.snd t)
abbrev cK (t : Tm) : Tm := .snd (.snd t)

def vertsTm : Tm := .call Lib3.fUnionS [cS (V 0), .call fVertsL [cK (V 0)]]
def vertsLTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0) (.call Lib3.fUnionS [.call fVerts [.fst (V 0)], .call fVertsL [.snd (V 0)]])

def keyLeTm : Tm :=
  .letE (.call Lib3.fDiffS [.call fVerts [V 1], V 0])
    (.letE (.call Lib3.fDiffS [.call fVerts [V 3], V 1])
      (.ite (.isNat (V 0)) (.lit 1) (.ite (.isNat (V 1)) (.lit 0) (leT (.fst (V 1)) (.fst (V 0))))))

def sortKidsTm : Tm := .call Lib2.fISort [.lit fKeyLe, V 0, V 1]

def keepTm : Tm :=
  .sub (.lit 1) (.mul (.isNat (cK (V 1))) (.call Lib3.fSubsetS [cS (V 1), V 0]))

def normNodeTm : Tm :=
  .letE (.call fFilter [.lit fKeep, V 0, V 2])
    (.ite (.isNat (V 0))
      (.cons (V 1) (.cons (.call fTake [.lit 1, V 2]) (.lit 0)))
      (.ite (.isNat (.snd (V 0)))
        (.ite (.call fEqV [cS (.fst (V 0)), V 1])
          (.cons (V 1) (.cons (.call E1A.fTypical [.call fAppend [V 2, cY (.fst (V 0))]]) (cK (.fst (V 0)))))
          (.cons (V 1) (.cons (V 2) (.cons (.fst (V 0)) (.lit 0)))))
        (.cons (V 1) (.cons (V 2) (.call fSortKids [V 1, V 0])))))

def normTm : Tm :=
  .call fNormNode [cS (V 0), cY (V 0), .call fMap [.lit fNormC, .lit 0, cK (V 0)]]

def normCTm : Tm := .call fNorm [V 1]

def relETm : Tm :=
  .cons (.call Lib3.fEraseS [V 0, cS (V 1)]) (.cons (cY (V 1)) (.call fMap [.lit fRelE, V 0, cK (V 1)]))

def forgetCTm : Tm := .call fNorm [.call fRelE [V 0, V 1]]

def subCTm : Tm := .sub (V 1) (V 0)
def subMapTm : Tm := .call fMap [.lit fSubC, V 0, V 1]
def leKTm : Tm := leT (V 1) (V 0)
def allLeTm : Tm := .call fAll [.lit fLeK, V 0, V 1]

/-- `ys` of `joinC`, given the id `rid` of `ringTypList`. -/
def joinYsTm (rid : ℕ) : Tm :=
  .call fFilter [.lit fAllLe, V 1,
    .call Lib2.fDedup [.call fMap [.lit fSubMap, .call fLength [V 0], .call rid [V 2, V 3]]]]

def mkNodeTm : Tm := .cons (.fst (V 0)) (.cons (V 1) (.snd (V 0)))
def mapKKTm : Tm := .call fMap [.lit fMkNode, .cons (.fst (V 0)) (V 1), .snd (V 0)]

def joinCTm : Tm :=
  .ite (.call fEqV [cS (V 1), cS (V 2)])
    (.ite (.eq (.call fLength [cK (V 1)]) (.call fLength [cK (V 2)]))
      (.letE (.call fJoinYs [cS (V 1), V 0, cY (V 1), cY (V 2)])
        (.letE (.call fJoinKids [V 1, cK (V 2), cK (V 3)])
          (.call fFlatMap [.lit fMapKK, .cons (.fst (V 3)) (V 1), V 0])))
      (.lit 0))
    (.lit 0)

def consToTm : Tm := .cons (V 0) (V 1)
def consAllTm : Tm := .call fMap [.lit fConsTo, V 1, V 0]

def joinKidsTm : Tm :=
  .ite (.isNat (V 1))
    (.ite (.isNat (V 2)) (.cons (.lit 0) (.lit 0)) (.lit 0))
    (.ite (.isNat (V 2)) (.lit 0)
      (.letE (.call fJoinKids [V 0, .snd (V 1), .snd (V 2)])
        (.call fFlatMap [.lit fConsAll, V 0, .call fJoinC [V 1, .fst (V 2), .fst (V 3)]])))

def domCTm : Tm :=
  .ite (.call fEqV [cS (V 0), cS (V 1)])
    (.ite (.call E1A.fDomB [cY (V 0), cY (V 1)]) (.call fDomCL [cK (V 0), cK (V 1)]) (.lit 0))
    (.lit 0)

def domCLTm : Tm :=
  .ite (.isNat (V 0)) (.ite (.isNat (V 1)) (.lit 1) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.call fDomC [.fst (V 0), .fst (V 1)]) (.call fDomCL [.snd (V 0), .snd (V 1)]) (.lit 0)))

/-- the table of WP E2 (ids `160 … 182`); `rid` is the id of `ringTypList` in the assembled table. -/
def e2Tbl (rid : ℕ) : ℕ → Option Tm := fun f =>
  match f with
  | 160 => some vertsTm | 161 => some vertsLTm | 162 => some keyLeTm | 163 => some sortKidsTm
  | 164 => some keepTm | 165 => some normNodeTm | 166 => some normTm | 167 => some normCTm
  | 168 => some relETm | 169 => some forgetCTm | 170 => some subCTm | 171 => some subMapTm
  | 172 => some leKTm | 173 => some allLeTm | 174 => some (joinYsTm rid) | 175 => some mkNodeTm
  | 176 => some mapKKTm | 177 => some joinCTm | 178 => some joinKidsTm | 179 => some consToTm
  | 180 => some consAllTm | 181 => some domCTm | 182 => some domCLTm
  | _ => none

/-- the E2 layer on top of the library -/
def e2Δ (rid : ℕ) : ℕ → Option Tm := layerΔ Lib.Δ 128 (e2Tbl rid)

theorem e2Tbl_lt (rid : ℕ) {f : ℕ} {b : Tm} (h : e2Tbl rid f = some b) : 160 ≤ f ∧ f < 183 := by
  unfold e2Tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem ext_lib (rid : ℕ) : Lib.Δ ⊑ e2Δ rid := Ext.layer (e2Tbl rid) (fun _ _ h => Lib.Δ_lt h)

theorem Δ_verts (rid : ℕ) : e2Δ rid fVerts = some vertsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fVerts by decide)]; rfl
theorem Δ_vertsL (rid : ℕ) : e2Δ rid fVertsL = some vertsLTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fVertsL by decide)]; rfl
theorem Δ_keyLe (rid : ℕ) : e2Δ rid fKeyLe = some keyLeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fKeyLe by decide)]; rfl
theorem Δ_sortKids (rid : ℕ) : e2Δ rid fSortKids = some sortKidsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSortKids by decide)]; rfl
theorem Δ_keep (rid : ℕ) : e2Δ rid fKeep = some keepTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fKeep by decide)]; rfl
theorem Δ_normNode (rid : ℕ) : e2Δ rid fNormNode = some normNodeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNormNode by decide)]; rfl
theorem Δ_norm (rid : ℕ) : e2Δ rid fNorm = some normTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNorm by decide)]; rfl
theorem Δ_normC (rid : ℕ) : e2Δ rid fNormC = some normCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNormC by decide)]; rfl
theorem Δ_relE (rid : ℕ) : e2Δ rid fRelE = some relETm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fRelE by decide)]; rfl
theorem Δ_forgetC (rid : ℕ) : e2Δ rid fForgetC = some forgetCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fForgetC by decide)]; rfl
theorem Δ_subC (rid : ℕ) : e2Δ rid fSubC = some subCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSubC by decide)]; rfl
theorem Δ_subMap (rid : ℕ) : e2Δ rid fSubMap = some subMapTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSubMap by decide)]; rfl
theorem Δ_leK (rid : ℕ) : e2Δ rid fLeK = some leKTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fLeK by decide)]; rfl
theorem Δ_allLe (rid : ℕ) : e2Δ rid fAllLe = some allLeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fAllLe by decide)]; rfl
theorem Δ_joinYs (rid : ℕ) : e2Δ rid fJoinYs = some (joinYsTm rid) := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinYs by decide)]; rfl
theorem Δ_mkNode (rid : ℕ) : e2Δ rid fMkNode = some mkNodeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fMkNode by decide)]; rfl
theorem Δ_mapKK (rid : ℕ) : e2Δ rid fMapKK = some mapKKTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fMapKK by decide)]; rfl
theorem Δ_joinC (rid : ℕ) : e2Δ rid fJoinC = some joinCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinC by decide)]; rfl
theorem Δ_joinKids (rid : ℕ) : e2Δ rid fJoinKids = some joinKidsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinKids by decide)]; rfl
theorem Δ_consTo (rid : ℕ) : e2Δ rid fConsTo = some consToTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fConsTo by decide)]; rfl
theorem Δ_consAll (rid : ℕ) : e2Δ rid fConsAll = some consAllTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fConsAll by decide)]; rfl
theorem Δ_domC (rid : ℕ) : e2Δ rid fDomC = some domCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fDomC by decide)]; rfl
theorem Δ_domCL (rid : ℕ) : e2Δ rid fDomCL = some domCLTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fDomCL by decide)]; rfl

end E2
end Lax117284Proofs.Treewidth.Fun
