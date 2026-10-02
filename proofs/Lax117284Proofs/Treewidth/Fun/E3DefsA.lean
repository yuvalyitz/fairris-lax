import Lax117284Proofs.Treewidth.Fun.LibEmbeds
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize

/-!
# WP E3 (layer A): helpers, `winPlans`, `kidChoices` — the terms (ids `256 …`)

| id | function | arguments |
|---|---|---|
| 256 `fPlus1` | `plus1 y` | `[y]` |
| 257 `fRangeP` | `List.range' lo n` | `[lo, n]` |
| 258 `fEnds1` | the first-type end plans of `winPlans` (`map` callee) | `[(v,lo,t), f]` |
| 259 `fEnds2` | the second-type end plans | `[(v,lo,t), f]` |
| 260 `fFstF` | `x.1` (`map` callee) | `[_, x]` |
| 261 `fSndFstF` | `x.2.1` | `[_, x]` |
| 262 `fUnionStep` | `acc ∪ x.2.2` (`foldl` callee) | `[_, acc, x]` |
| 263 `fWhole` | the whole-plans of `winPlans` (`map` callee) | `[(v,lo,t), combo]` |
| 264 `fWinPlans` | `CT.winPlans` | `[v, lo, t]` |
| 265 `fSomeF` | `(some p.1, p.2.1, p.2.2)` | `[_, p]` |
| 266 `fConsF` | `o :: x` (`map` callee, context `o`) | `[o, x]` |
| 267 `fKcLam` | `(kidChoices v ks).map (o :: ·)` (`flatMap` callee, context = that list) | `[kc, o]` |
| 268 `fKidChoices` | `CT.kidChoices` | `[v, ks]` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3A

open Lib1

abbrev fPlus1 : ℕ := 256
abbrev fRangeP : ℕ := 257
abbrev fEnds1 : ℕ := 258
abbrev fEnds2 : ℕ := 259
abbrev fFstF : ℕ := 260
abbrev fSndFstF : ℕ := 261
abbrev fUnionStep : ℕ := 262
abbrev fWhole : ℕ := 263
abbrev fWinPlans : ℕ := 264
abbrev fSomeF : ℕ := 265
abbrev fConsF : ℕ := 266
abbrev fKcLam : ℕ := 267
abbrev fKidChoices : ℕ := 268

/-- `plus1 y = y.map (· + 1)` -/
def plus1Tm : Tm :=
  .ite (.isNat (V 0)) (V 0) (.cons (.add (.fst (V 0)) (.lit 1)) (.call fPlus1 [.snd (V 0)]))

/-- `List.range' lo n` -/
def rangePTm : Tm :=
  .ite (.eq (V 1) (.lit 0)) (.lit 0)
    (.cons (V 0) (.call fRangeP [.add (V 0) (.lit 1), .sub (V 1) (.lit 1)]))

-- accessors of the context `(v, lo, t)` and of a characteristic `t = (S, y, ks)`
abbrev cxV (c : Tm) : Tm := .fst c
abbrev cxLo (c : Tm) : Tm := .fst (.snd c)
abbrev cxT (c : Tm) : Tm := .snd (.snd c)
abbrev cS (t : Tm) : Tm := .fst t
abbrev cY (t : Tm) : Tm := .fst (.snd t)
abbrev cK (t : Tm) : Tm := .snd (.snd t)

/-- `f ↦ (endAt (t1 f), node (insert v S) (plus1 ((y.take (f+1)).drop lo)) [node S (y.drop f) ks], S)` -/
def ends1Tm : Tm :=
  .cons (.cons (.lit 1) (.cons (.lit 1) (V 1)))
    (.cons
      (.cons (.call Lib3.fInsertS [cxV (V 0), cS (cxT (V 0))])
        (.cons (.call fPlus1 [.call fDrop [cxLo (V 0), .call fTake [.add (V 1) (.lit 1), cY (cxT (V 0))]]])
          (.cons (.cons (cS (cxT (V 0))) (.cons (.call fDrop [V 1, cY (cxT (V 0))]) (cK (cxT (V 0))))) (.lit 0))))
      (cS (cxT (V 0))))

/-- the second-type variant (`y.drop (f+1)`, cut `t2 f`) -/
def ends2Tm : Tm :=
  .cons (.cons (.lit 1) (.cons (.lit 2) (V 1)))
    (.cons
      (.cons (.call Lib3.fInsertS [cxV (V 0), cS (cxT (V 0))])
        (.cons (.call fPlus1 [.call fDrop [cxLo (V 0), .call fTake [.add (V 1) (.lit 1), cY (cxT (V 0))]]])
          (.cons (.cons (cS (cxT (V 0))) (.cons (.call fDrop [.add (V 1) (.lit 1), cY (cxT (V 0))]) (cK (cxT (V 0)))))
            (.lit 0))))
      (cS (cxT (V 0))))

def fstFTm : Tm := .fst (V 1)
def sndFstFTm : Tm := .fst (.snd (V 1))
def unionStepTm : Tm := .call Lib3.fUnionS [V 1, .snd (.snd (V 2))]

/-- `combo ↦ (whole (combo.map (·.1)), node (insert v S) (plus1 (y.drop lo)) (combo.map (·.2.1)), combo.foldl (· ∪ ·.2.2) S)` -/
def wholeTm : Tm :=
  .cons (.cons (.lit 2) (.call fMap [.lit fFstF, .lit 0, V 1]))
    (.cons
      (.cons (.call Lib3.fInsertS [cxV (V 0), cS (cxT (V 0))])
        (.cons (.call fPlus1 [.call fDrop [cxLo (V 0), cY (cxT (V 0))]])
          (.call fMap [.lit fSndFstF, .lit 0, V 1])))
      (.call fFoldl [.lit fUnionStep, .lit 0, cS (cxT (V 0)), V 1]))

/-- `winPlans v lo t` -/
def winPlansTm : Tm :=
  .letE (.cons (V 0) (.cons (V 1) (V 2)))
    (.call fAppend
      [.call fAppend
        [.call fMap [.lit fEnds1, V 0, .call fRangeP [V 2, .sub (.call fLength [cY (V 3)]) (V 2)]],
         .call fMap [.lit fEnds2, V 0,
           .call fRangeP [V 2, .sub (.sub (.call fLength [cY (V 3)]) (.lit 1)) (V 2)]]],
       .call fMap [.lit fWhole, V 0, .call fKidChoices [V 1, cK (V 3)]]])

def someFTm : Tm :=
  .cons (.cons (.lit 1) (.fst (V 1))) (.cons (.fst (.snd (V 1))) (.snd (.snd (V 1))))

def consFTm : Tm := .cons (V 0) (V 1)

def kcLamTm : Tm := .call fMap [.lit fConsF, V 1, V 0]

/-- `kidChoices v ks` -/
def kidChoicesTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.lit 0) (.lit 0))
    (.letE (.call fWinPlans [V 0, .lit 0, .fst (V 1)])
      (.letE (.cons (.cons (.lit 0) (.cons (.fst (V 2)) (.lit 0))) (.call fMap [.lit fSomeF, .lit 0, V 0]))
        (.letE (.call fKidChoices [V 2, .snd (V 3)])
          (.call fFlatMap [.lit fKcLam, V 0, V 1]))))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 256 => some plus1Tm | 257 => some rangePTm | 258 => some ends1Tm | 259 => some ends2Tm
  | 260 => some fstFTm | 261 => some sndFstFTm | 262 => some unionStepTm | 263 => some wholeTm
  | 264 => some winPlansTm | 265 => some someFTm | 266 => some consFTm | 267 => some kcLamTm
  | 268 => some kidChoicesTm | _ => none

/-- layer A of the E3 table -/
def Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 tbl

theorem tbl_lt {f : ℕ} {b : Tm} (h : tbl f = some b) : 256 ≤ f ∧ f < 269 := by
  unfold tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem extLib : Lib.Δ ⊑ Δ := Ext.layer tbl (fun f b h => Lib.Δ_lt h)

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < 269 := by
  unfold Δ layerΔ at h
  by_cases hf : 128 ≤ f
  · rw [if_pos hf] at h; exact (tbl_lt h).2
  · omega

theorem Δ_plus1 : Δ fPlus1 = some plus1Tm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fPlus1 by decide)]; rfl
theorem Δ_rangeP : Δ fRangeP = some rangePTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fRangeP by decide)]; rfl
theorem Δ_ends1 : Δ fEnds1 = some ends1Tm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fEnds1 by decide)]; rfl
theorem Δ_ends2 : Δ fEnds2 = some ends2Tm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fEnds2 by decide)]; rfl
theorem Δ_fstF : Δ fFstF = some fstFTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fFstF by decide)]; rfl
theorem Δ_sndFstF : Δ fSndFstF = some sndFstFTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fSndFstF by decide)]; rfl
theorem Δ_unionStep : Δ fUnionStep = some unionStepTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fUnionStep by decide)]; rfl
theorem Δ_whole : Δ fWhole = some wholeTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fWhole by decide)]; rfl
theorem Δ_winPlans : Δ fWinPlans = some winPlansTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fWinPlans by decide)]; rfl
theorem Δ_someF : Δ fSomeF = some someFTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fSomeF by decide)]; rfl
theorem Δ_consF : Δ fConsF = some consFTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fConsF by decide)]; rfl
theorem Δ_kcLam : Δ fKcLam = some kcLamTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fKcLam by decide)]; rfl
theorem Δ_kidChoices : Δ fKidChoices = some kidChoicesTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fKidChoices by decide)]; rfl

theorem ids_lt {B : ℕ} (h : 300 < B) :
    fPlus1 < B ∧ fRangeP < B ∧ fEnds1 < B ∧ fEnds2 < B ∧ fFstF < B ∧ fSndFstF < B ∧ fUnionStep < B ∧
      fWhole < B ∧ fWinPlans < B ∧ fSomeF < B ∧ fConsF < B ∧ fKcLam < B ∧ fKidChoices < B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.lt_of_le_of_lt (by decide) h

end E3A
end Lax117284Proofs.Treewidth.Fun
