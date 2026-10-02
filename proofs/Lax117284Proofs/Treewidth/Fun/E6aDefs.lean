import Lax117284Proofs.Treewidth.Fun.Lib
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize

/-!
# WP E6a (1): the table `e6aTbl` (ids `640 … 703`) — `compress`, `niceOf`, `NT.addEverywhere`, `NT.encode` as F-functions

The functions use only the library (`Lib.Δ`); `e6aΔ = layerΔ Lib.Δ 128 e6aTbl` and every theorem is stated for an arbitrary
`Δ'` with `e6aΔ ⊑ Δ'`.

| id | function | arguments |
|---|---|---|
| 640 `fFlatKids` | `flatKids` | `[X, L]` |
| 641 `fCompress` | `compress` | `[t]` |
| 642 `fCompressC` | `compress` (`map` callee) | `[ctx, t]` |
| 643 `fBagNT` | `NT.bag` | `[nt]` |
| 644 `fIntroMany` | `introMany` | `[l, t]` |
| 645 `fForgetMany` | `forgetMany` | `[l, t]` |
| 646 `fConv` | `conv` | `[X, t]` |
| 647 `fConvNice` | `conv X (niceOf k)` (`map` callee) | `[X, k]` |
| 648 `fJoinFold` | `ts.foldl NT.join t` | `[ts, t]` |
| 649 `fNiceOf` | `niceOf` | `[t]` |
| 650 `fAddEv` | `NT.addEverywhere` | `[v, nt]` |
| 651 `fAddEvP` | `NT.addEverywhere` (tuple argument) | `[(v, nt)]` |
| 652 `fRecs` | `NT.recs` | `[b, nt]` |
| 653 `fTriple` | `[r.1, r.2.1, r.2.2]` (`flatMap` callee) | `[ctx, r]` |
| 654 `fEncode` | `NT.encode` | `[nt]` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open Lib1

abbrev fFlatKids : ℕ := 640
abbrev fCompress : ℕ := 641
abbrev fCompressC : ℕ := 642
abbrev fBagNT : ℕ := 643
abbrev fIntroMany : ℕ := 644
abbrev fForgetMany : ℕ := 645
abbrev fConv : ℕ := 646
abbrev fConvNice : ℕ := 647
abbrev fJoinFold : ℕ := 648
abbrev fNiceOf : ℕ := 649
abbrev fAddEv : ℕ := 650
abbrev fAddEvP : ℕ := 651
abbrev fRecs : ℕ := 652
abbrev fTriple : ℕ := 653
abbrev fEncode : ℕ := 654

/-- `flatKids X L`, on `[X, L]`; a kid `node Y ls` is `cons Y ls`. -/
def flatKidsTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.letE (.fst (V 1))
      (.ite (.call Lib3.fSubsetS [.fst (V 0), V 1])
        (.call fAppend [.snd (V 0), .call fFlatKids [V 1, .snd (V 2)]])
        (.cons (V 0) (.call fFlatKids [V 1, .snd (V 2)]))))

def compressTm : Tm :=
  .cons (.fst (V 0)) (.call fFlatKids [.fst (V 0), .call fMap [.lit fCompressC, .lit 0, .snd (V 0)]])

def compressCTm : Tm := .call fCompress [V 1]

/-- `NT.bag`; the nice tree `intro v c = (1, (v, c))`, `forget v c = (2, (v, c))`, `join a b = (3, (a, b))`. -/
def bagNTTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.eq (.fst (V 0)) (.lit 1))
      (.call Lib3.fInsertS [.fst (.snd (V 0)), .call fBagNT [.snd (.snd (V 0))]])
      (.ite (.eq (.fst (V 0)) (.lit 2))
        (.call Lib3.fEraseS [.fst (.snd (V 0)), .call fBagNT [.snd (.snd (V 0))]])
        (.call fBagNT [.fst (.snd (V 0))])))

def introManyTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fIntroMany [.snd (V 0), .cons (.lit 1) (.cons (.fst (V 0)) (V 1))])

def forgetManyTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fForgetMany [.snd (V 0), .cons (.lit 2) (.cons (.fst (V 0)) (V 1))])

/-- `conv X t = introMany (X \ bag t) (forgetMany (bag t \ X) t)`; environment `[b, X, t]` under the `let`. -/
def convTm : Tm :=
  .letE (.call fBagNT [V 1])
    (.call fIntroMany [.call Lib3.fDiffS [V 1, V 0], .call fForgetMany [.call Lib3.fDiffS [V 0, V 1], V 2]])

def convNiceTm : Tm := .call fConv [V 0, .call fNiceOf [V 1]]

def joinFoldTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fJoinFold [.snd (V 0), .cons (.lit 3) (.cons (V 1) (.fst (V 0)))])

def niceOfTm : Tm :=
  .letE (.call fMap [.lit fConvNice, .fst (V 0), .snd (V 0)])
    (.ite (.isNat (V 0)) (.call fIntroMany [.fst (V 1), .lit 0])
      (.call fJoinFold [.snd (V 0), .fst (V 0)]))

def addEvTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.lit 1) (.cons (V 0) (.lit 0)))
    (.ite (.eq (.fst (V 1)) (.lit 3))
      (.cons (.lit 3) (.cons (.call fAddEv [V 0, .fst (.snd (V 1))]) (.call fAddEv [V 0, .snd (.snd (V 1))])))
      (.cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.call fAddEv [V 0, .snd (.snd (V 1))]))))

def addEvPTm : Tm := .call fAddEv [.fst (V 0), .snd (V 0)]

/-- `NT.recs b t` (records `(kind, (vertex, other))`); for a join the second child is numbered first. -/
def recsTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.cons (.lit 0) (.cons (.lit 0) (.lit 0))) (.lit 0))
    (.ite (.eq (.fst (V 1)) (.lit 3))
      (.letE (.call fRecs [V 0, .snd (.snd (V 1))])
        (.letE (.call fRecs [.add (V 1) (.call fLength [V 0]), .fst (.snd (V 2))])
          (.call fAppend [V 1, .call fAppend [V 0,
            .cons (.cons (.lit 3) (.cons (.lit 0) (.sub (.add (V 2) (.call fLength [V 1])) (.lit 1)))) (.lit 0)]])))
      (.call fAppend [.call fRecs [V 0, .snd (.snd (V 1))],
        .cons (.cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.lit 0))) (.lit 0)]))

def tripleTm : Tm :=
  .cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.cons (.snd (.snd (V 1))) (.lit 0)))

def encodeTm : Tm :=
  .letE (.call fRecs [.lit 0, V 0])
    (.cons (.call fLength [V 0]) (.call fFlatMap [.lit fTriple, .lit 0, V 0]))

/-- the table of WP E6a (ids `640 … 654`) -/
def e6aTbl : ℕ → Option Tm := fun f =>
  match f with
  | 640 => some flatKidsTm | 641 => some compressTm | 642 => some compressCTm | 643 => some bagNTTm
  | 644 => some introManyTm | 645 => some forgetManyTm | 646 => some convTm | 647 => some convNiceTm
  | 648 => some joinFoldTm | 649 => some niceOfTm | 650 => some addEvTm | 651 => some addEvPTm
  | 652 => some recsTm | 653 => some tripleTm | 654 => some encodeTm
  | _ => none

/-- the E6a layer on top of the library -/
def e6aΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 e6aTbl

theorem e6aTbl_lt {f : ℕ} {b : Tm} (h : e6aTbl f = some b) : 640 ≤ f ∧ f < 655 := by
  unfold e6aTbl at h
  split at h <;> first | (simp at h; done) | omega

theorem ext_lib : Lib.Δ ⊑ e6aΔ := Ext.layer e6aTbl (fun _ _ h => Lib.Δ_lt h)

theorem ext1 {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans ext_lib hΔ)
theorem ext3 {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans ext_lib hΔ)

theorem Δ_flatKids : e6aΔ fFlatKids = some flatKidsTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fFlatKids by decide)]; rfl
theorem Δ_compress : e6aΔ fCompress = some compressTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fCompress by decide)]; rfl
theorem Δ_compressC : e6aΔ fCompressC = some compressCTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fCompressC by decide)]; rfl
theorem Δ_bagNT : e6aΔ fBagNT = some bagNTTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fBagNT by decide)]; rfl
theorem Δ_introMany : e6aΔ fIntroMany = some introManyTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fIntroMany by decide)]; rfl
theorem Δ_forgetMany : e6aΔ fForgetMany = some forgetManyTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fForgetMany by decide)]; rfl
theorem Δ_conv : e6aΔ fConv = some convTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fConv by decide)]; rfl
theorem Δ_convNice : e6aΔ fConvNice = some convNiceTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fConvNice by decide)]; rfl
theorem Δ_joinFold : e6aΔ fJoinFold = some joinFoldTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fJoinFold by decide)]; rfl
theorem Δ_niceOf : e6aΔ fNiceOf = some niceOfTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fNiceOf by decide)]; rfl
theorem Δ_addEv : e6aΔ fAddEv = some addEvTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fAddEv by decide)]; rfl
theorem Δ_recs : e6aΔ fRecs = some recsTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fRecs by decide)]; rfl
theorem Δ_triple : e6aΔ fTriple = some tripleTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fTriple by decide)]; rfl
theorem Δ_encode : e6aΔ fEncode = some encodeTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fEncode by decide)]; rfl

end E6a
end Lax117284Proofs.Treewidth.Fun
