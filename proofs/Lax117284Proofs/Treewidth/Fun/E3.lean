import Lax117284Proofs.Treewidth.Fun.LibEmbeds
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Fun.Lib1
import Lax117284Proofs.Treewidth.Fun.Lib2
import Lax117284Proofs.Treewidth.Size.Plans
import Lax117284Proofs.Treewidth.Size.PlanSize
import Mathlib.Tactic

/-! ### `Lax117284Proofs.Treewidth.Fun.E3DefsA` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3DefsB` -/

section
/-!
# WP E3 (layer B): `wtopPlans`, `allChains`, `attachPlans` — the terms (ids `288 …`)

| id | function | arguments |
|---|---|---|
| 288 `fTopDirect` | `(top none p.1, p.2.1, p.2.2)` (`map` callee) | `[_, p]` |
| 289 `fPre1In` | first-type pre-cut result (`map` callee, context `(f, v, t)`) | `[(f,v,t), p]` |
| 290 `fPre1` | `f ↦ (winPlans v f t).map …` (`flatMap` callee, context `(v, t)`) | `[(v,t), f]` |
| 291 `fPre2In` | second-type pre-cut result | `[(f,v,t), p]` |
| 292 `fPre2` | `f ↦ (winPlans v (f+1) t).map …` | `[(v,t), f]` |
| 293 `fWtopPlans` | `CT.wtopPlans` | `[v, t]` |
| 294 `fCandFn` | `c ↦ N ∪ c.toFinset` (context `N`) | `[N, c]` |
| 295 `fChainCands` | `CT.chainCands` | `[S, N]` |
| 296 `fPairCh` | `M ↦ (chain, M)` (context `chain`) | `[chain, M]` |
| 297 `fSubOf` | `X ↦ decide (X ⊆ bound)` (context `bound`) | `[bound, X]` |
| 298 `fSel` | `X ↦ X ⊆ bound && (chain.isEmpty || X ⊂ bound)` (context `(bound, chain)`) | `[(bound,chain), X]` |
| 299 `fGoStep` | `X ↦ chainsGo cands fuel X (chain ++ [X])` (context `(cands, fuel, chain)`) | `[ctx, X]` |
| 300 `fChainsGo` | `CT.chainsGo` | `[cands, fuel, bound, chain]` |
| 301 `fAllChains` | `CT.allChains` | `[S, N]` |
| 302 `fPathStep` | `node X [X.card] [acc]` (`foldr` callee) | `[_, X, acc]` |
| 303 `fPathSubtree` | `CT.pathSubtree` | `[v, chain, M]` |
| 304 `fAttIn1` | first-type cut result of `attachPlans` (context `(br, cm, t)`) | `[ctx, f]` |
| 305 `fAttIn2` | second-type cut result | `[ctx, f]` |
| 306 `fAtt` | `cm ↦ …` (`flatMap` callee, context `(v, t)`) | `[(v,t), cm]` |
| 307 `fAttachPlans` | `CT.attachPlans` | `[v, N, t]` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3B

open Lib1

abbrev fTopDirect : ℕ := 288
abbrev fPre1In : ℕ := 289
abbrev fPre1 : ℕ := 290
abbrev fPre2In : ℕ := 291
abbrev fPre2 : ℕ := 292
abbrev fWtopPlans : ℕ := 293
abbrev fCandFn : ℕ := 294
abbrev fChainCands : ℕ := 295
abbrev fPairCh : ℕ := 296
abbrev fSubOf : ℕ := 297
abbrev fSel : ℕ := 298
abbrev fGoStep : ℕ := 299
abbrev fChainsGo : ℕ := 300
abbrev fAllChains : ℕ := 301
abbrev fPathStep : ℕ := 302
abbrev fPathSubtree : ℕ := 303
abbrev fAttIn1 : ℕ := 304
abbrev fAttIn2 : ℕ := 305
abbrev fAtt : ℕ := 306
abbrev fAttachPlans : ℕ := 307

open E3A in
/-- `p ↦ (Plan.top none p.1, p.2.1, p.2.2)` -/
def topDirectTm : Tm :=
  .cons (.cons (.lit 2) (.cons (.lit 0) (.fst (V 1)))) (.cons (.fst (.snd (V 1))) (.snd (.snd (V 1))))

-- the context `(f, v, t)` of the pre-cut lambdas: `f = fst`, `t = snd (snd)`
open E3A in
/-- `(top (some (t1 f)) p.1, node S (y.take (f+1)) [p.2.1], p.2.2)` -/
def pre1InTm : Tm :=
  .cons (.cons (.lit 2) (.cons (.cons (.lit 1) (.cons (.lit 1) (.fst (V 0)))) (.fst (V 1))))
    (.cons
      (.cons (cS (cxT (V 0)))
        (.cons (.call fTake [.add (.fst (V 0)) (.lit 1), cY (cxT (V 0))]) (.cons (.fst (.snd (V 1))) (.lit 0))))
      (.snd (.snd (V 1))))

open E3A in
def pre2InTm : Tm :=
  .cons (.cons (.lit 2) (.cons (.cons (.lit 1) (.cons (.lit 2) (.fst (V 0)))) (.fst (V 1))))
    (.cons
      (.cons (cS (cxT (V 0)))
        (.cons (.call fTake [.add (.fst (V 0)) (.lit 1), cY (cxT (V 0))]) (.cons (.fst (.snd (V 1))) (.lit 0))))
      (.snd (.snd (V 1))))

/-- `f ↦ (winPlans v f t).map …` with context `(v, t)` -/
def pre1Tm : Tm :=
  .call fMap [.lit fPre1In, .cons (V 1) (V 0), .call E3A.fWinPlans [.fst (V 0), V 1, .snd (V 0)]]

def pre2Tm : Tm :=
  .call fMap [.lit fPre2In, .cons (V 1) (V 0), .call E3A.fWinPlans [.fst (V 0), .add (V 1) (.lit 1), .snd (V 0)]]

open E3A in
/-- `wtopPlans v t` -/
def wtopPlansTm : Tm :=
  .letE (.cons (V 0) (V 1))
    (.call fAppend
      [.call fAppend
        [.call fMap [.lit fTopDirect, .lit 0, .call fWinPlans [V 1, .lit 0, V 2]],
         .call fFlatMap [.lit fPre1, V 0, .call fRange [.call fLength [cY (V 2)]]]],
       .call fFlatMap [.lit fPre2, V 0, .call fRange [.sub (.call fLength [cY (V 2)]) (.lit 1)]]])

/-- `c ↦ N ∪ c.toFinset` -/
def candFnTm : Tm := .call Lib3.fUnionS [V 0, .call Lib4.fToFinset [V 1]]

/-- `chainCands S N` -/
def chainCandsTm : Tm :=
  .call fMap [.lit fCandFn, V 1, .call Lib4.fSublists [.call Lib3.fDiffS [V 0, V 1]]]

def pairChTm : Tm := .cons (V 0) (V 1)
def subOfTm : Tm := .call Lib3.fSubsetS [V 1, V 0]

/-- `X ⊆ bound && (chain.isEmpty || X ⊂ bound)` with context `(bound, chain)` -/
def selTm : Tm :=
  .ite (.call Lib3.fSubsetS [V 1, .fst (V 0)])
    (.ite (.isNat (.snd (V 0))) (.lit 1) (.sub (.lit 1) (.call Lib3.fSubsetS [.fst (V 0), V 1])))
    (.lit 0)

/-- `X ↦ chainsGo cands fuel X (chain ++ [X])` with context `(cands, fuel, chain)` -/
def goStepTm : Tm :=
  .call fChainsGo [.fst (V 0), .fst (.snd (V 0)), V 1, .call fAppend [.snd (.snd (V 0)), .cons (V 1) (.lit 0)]]

/-- `chainsGo cands fuel bound chain` -/
def chainsGoTm : Tm :=
  .letE (.call fMap [.lit fPairCh, V 3, .call fFilter [.lit fSubOf, V 2, V 0]])
    (.ite (.eq (V 2) (.lit 0)) (V 0)
      (.call fAppend
        [V 0,
         .call fFlatMap [.lit fGoStep, .cons (V 1) (.cons (.sub (V 2) (.lit 1)) (V 4)),
           .call fFilter [.lit fSel, .cons (V 3) (V 4), V 1]]]))

/-- `allChains S N` -/
def allChainsTm : Tm :=
  .letE (.call fChainCands [V 0, V 1])
    (.call fChainsGo [V 0, .add (.call fLength [V 1]) (.lit 1), V 1, .lit 0])

def pathStepTm : Tm :=
  .cons (V 1) (.cons (.cons (.call fLength [V 1]) (.lit 0)) (.cons (V 2) (.lit 0)))

/-- `pathSubtree v chain M` -/
def pathSubtreeTm : Tm :=
  .call Lib2.fFoldr
    [.lit fPathStep, .lit 0,
     .cons (.call Lib3.fInsertS [V 0, V 2]) (.cons (.cons (.add (.call fLength [V 2]) (.lit 1)) (.lit 0)) (.lit 0)),
     V 1]

-- the context `(br, cm, t)` of the attach lambdas
open E3A in
/-- `(att (some (t1 f)) cm.1 cm.2, node S (y.take (f+1)) [br, node S (y.drop f) ks])` -/
def attIn1Tm : Tm :=
  .cons
    (.cons (.lit 1) (.cons (.cons (.lit 1) (.cons (.lit 1) (V 1)))
      (.cons (.fst (.fst (.snd (V 0)))) (.snd (.fst (.snd (V 0)))))))
    (.cons (cS (.snd (.snd (V 0))))
      (.cons (.call fTake [.add (V 1) (.lit 1), cY (.snd (.snd (V 0)))])
        (.cons (.fst (V 0))
          (.cons (.cons (cS (.snd (.snd (V 0)))) (.cons (.call fDrop [V 1, cY (.snd (.snd (V 0)))]) (cK (.snd (.snd (V 0))))))
            (.lit 0)))))

open E3A in
def attIn2Tm : Tm :=
  .cons
    (.cons (.lit 1) (.cons (.cons (.lit 1) (.cons (.lit 2) (V 1)))
      (.cons (.fst (.fst (.snd (V 0)))) (.snd (.fst (.snd (V 0)))))))
    (.cons (cS (.snd (.snd (V 0))))
      (.cons (.call fTake [.add (V 1) (.lit 1), cY (.snd (.snd (V 0)))])
        (.cons (.fst (V 0))
          (.cons (.cons (cS (.snd (.snd (V 0)))) (.cons (.call fDrop [.add (V 1) (.lit 1), cY (.snd (.snd (V 0)))]) (cK (.snd (.snd (V 0))))))
            (.lit 0)))))

open E3A in
/-- `cm ↦ (att none … :: …) ++ …` with context `(v, t)` -/
def attTm : Tm :=
  .letE (.call fPathSubtree [.fst (V 0), .fst (V 1), .snd (V 1)])
    (.call fAppend
      [.cons
        (.cons (.cons (.lit 1) (.cons (.lit 0) (.cons (.fst (V 2)) (.snd (V 2)))))
          (.cons (cS (.snd (V 1)))
            (.cons (cY (.snd (V 1))) (.call fAppend [cK (.snd (V 1)), .cons (V 0) (.lit 0)]))))
        (.call fMap [.lit fAttIn1, .cons (V 0) (.cons (V 2) (.snd (V 1))),
          .call fRange [.call fLength [cY (.snd (V 1))]]]),
       .call fMap [.lit fAttIn2, .cons (V 0) (.cons (V 2) (.snd (V 1))),
         .call fRange [.sub (.call fLength [cY (.snd (V 1))]) (.lit 1)]]])

open E3A in
/-- `attachPlans v N t` -/
def attachPlansTm : Tm :=
  .letE (.cons (V 0) (V 2))
    (.call fFlatMap [.lit fAtt, V 0, .call fAllChains [cS (V 3), V 2]])

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 288 => some topDirectTm | 289 => some pre1InTm | 290 => some pre1Tm | 291 => some pre2InTm
  | 292 => some pre2Tm | 293 => some wtopPlansTm | 294 => some candFnTm | 295 => some chainCandsTm
  | 296 => some pairChTm | 297 => some subOfTm | 298 => some selTm | 299 => some goStepTm
  | 300 => some chainsGoTm | 301 => some allChainsTm | 302 => some pathStepTm | 303 => some pathSubtreeTm
  | 304 => some attIn1Tm | 305 => some attIn2Tm | 306 => some attTm | 307 => some attachPlansTm
  | _ => none

/-- layers A and B of the E3 table -/
def Δ : ℕ → Option Tm := layerΔ E3A.Δ 288 tbl

theorem tbl_lt {f : ℕ} {b : Tm} (h : tbl f = some b) : 288 ≤ f ∧ f < 308 := by
  unfold tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem extA : E3A.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E3A.Δ_lt h; omega)

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < 308 := by
  unfold Δ layerΔ at h
  by_cases hf : 288 ≤ f
  · rw [if_pos hf] at h; exact (tbl_lt h).2
  · rw [if_neg hf] at h; have := E3A.Δ_lt h; omega

theorem Δ_topDirect : Δ fTopDirect = some topDirectTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fTopDirect by decide)]; rfl
theorem Δ_pre1In : Δ fPre1In = some pre1InTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPre1In by decide)]; rfl
theorem Δ_pre1 : Δ fPre1 = some pre1Tm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPre1 by decide)]; rfl
theorem Δ_pre2In : Δ fPre2In = some pre2InTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPre2In by decide)]; rfl
theorem Δ_pre2 : Δ fPre2 = some pre2Tm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPre2 by decide)]; rfl
theorem Δ_wtopPlans : Δ fWtopPlans = some wtopPlansTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fWtopPlans by decide)]; rfl
theorem Δ_candFn : Δ fCandFn = some candFnTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fCandFn by decide)]; rfl
theorem Δ_chainCands : Δ fChainCands = some chainCandsTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fChainCands by decide)]; rfl
theorem Δ_pairCh : Δ fPairCh = some pairChTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPairCh by decide)]; rfl
theorem Δ_subOf : Δ fSubOf = some subOfTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fSubOf by decide)]; rfl
theorem Δ_sel : Δ fSel = some selTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fSel by decide)]; rfl
theorem Δ_goStep : Δ fGoStep = some goStepTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fGoStep by decide)]; rfl
theorem Δ_chainsGo : Δ fChainsGo = some chainsGoTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fChainsGo by decide)]; rfl
theorem Δ_allChains : Δ fAllChains = some allChainsTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fAllChains by decide)]; rfl
theorem Δ_pathStep : Δ fPathStep = some pathStepTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPathStep by decide)]; rfl
theorem Δ_pathSubtree : Δ fPathSubtree = some pathSubtreeTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fPathSubtree by decide)]; rfl
theorem Δ_attIn1 : Δ fAttIn1 = some attIn1Tm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fAttIn1 by decide)]; rfl
theorem Δ_attIn2 : Δ fAttIn2 = some attIn2Tm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fAttIn2 by decide)]; rfl
theorem Δ_att : Δ fAtt = some attTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fAtt by decide)]; rfl
theorem Δ_attachPlans : Δ fAttachPlans = some attachPlansTm := by simp [Δ, layerΔ_ge tbl (show 288 ≤ fAttachPlans by decide)]; rfl

theorem ids_lt {B : ℕ} (h : 400 < B) :
    fTopDirect < B ∧ fPre1In < B ∧ fPre1 < B ∧ fPre2In < B ∧ fPre2 < B ∧ fWtopPlans < B ∧ fCandFn < B ∧
      fChainCands < B ∧ fPairCh < B ∧ fSubOf < B ∧ fSel < B ∧ fGoStep < B ∧ fChainsGo < B ∧ fAllChains < B ∧
      fPathStep < B ∧ fPathSubtree < B ∧ fAttIn1 < B ∧ fAttIn2 < B ∧ fAtt < B ∧ fAttachPlans < B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Nat.lt_of_le_of_lt (by decide) h

end E3B
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3DefsC` -/

section
/-!
# WP E3 (layer C): `introKids`, `introPlans`, `maxEntry`, `introC` — the terms (ids `320 …`)

| id | function | arguments |
|---|---|---|
| 320 `fSubN` | `p ↦ decide (N ⊆ p.2.2)` (`filter` callee, context `N`) | `[N, p]` |
| 321 `fMk1` | `p ↦ ([], p.1, p.2.1)` (`map` callee) | `[_, p]` |
| 322 `fMk2` | `p ↦ ([], p.1, p.2)` (`map` callee) | `[_, p]` |
| 323 `fKid` | `r ↦ (pre.length :: r.1, r.2.1, node S y (pre ++ r.2.2 :: post))` (context `(pre.length, S, y, pre, post)`) | `[ctx, r]` |
| 324 `fIntroKids` | `CT.introKids` | `[v, N, S, y, pre, ks]` |
| 325 `fIntroPlans` | `CT.introPlans` | `[v, N, t]` |
| 326 `fMaxL` | `l.foldr max 0` | `[l]` |
| 327 `fMaxEntryL` | `CT.maxEntryL` | `[ks]` |
| 328 `fMaxEntry` | `CT.maxEntry` | `[c]` |
| 329 `fNormOf` | `r ↦ norm r.2.2` (`map` callee; calls the id `fNormId = 166` of `E2`) | `[_, r]` |
| 330 `fLeKC` | `c ↦ decide (c.maxEntry ≤ kmax)` (`filter` callee, context `kmax`) | `[kmax, c]` |
| 331 `fIntroC` | `CT.introC` | `[kmax, v, N, t]` |
| 332 `fIntroCUn` | `CT.introC` on the packed argument `(kmax, v, N, t)` | `[p]` |

The id of `CT.norm` in the table of WP E2 is `fNormId = 166` (`E2.fNorm`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open Lib1

abbrev fSubN : ℕ := 320
abbrev fMk1 : ℕ := 321
abbrev fMk2 : ℕ := 322
abbrev fKid : ℕ := 323
abbrev fIntroKids : ℕ := 324
abbrev fIntroPlans : ℕ := 325
abbrev fMaxL : ℕ := 326
abbrev fMaxEntryL : ℕ := 327
abbrev fMaxEntry : ℕ := 328
abbrev fNormOf : ℕ := 329
abbrev fLeKC : ℕ := 330
abbrev fIntroC : ℕ := 331
abbrev fIntroCUn : ℕ := 332

/-- the id of `CT.norm` in the table of WP E2 (`E2.fNorm`) -/
abbrev fNormId : ℕ := 166

def subNTm : Tm := .call Lib3.fSubsetS [V 0, .snd (.snd (V 1))]
def mk1Tm : Tm := .cons (.lit 0) (.cons (.fst (V 1)) (.fst (.snd (V 1))))
def mk2Tm : Tm := .cons (.lit 0) (.cons (.fst (V 1)) (.snd (V 1)))

-- the context `(len, S, y, pre, post)` of `fKid`
def kidTm : Tm :=
  .cons (.cons (.fst (V 0)) (.fst (V 1)))
    (.cons (.fst (.snd (V 1)))
      (.cons (.fst (.snd (V 0)))
        (.cons (.fst (.snd (.snd (V 0))))
          (.call fAppend
            [.fst (.snd (.snd (.snd (V 0)))), .cons (.snd (.snd (V 1))) (.snd (.snd (.snd (.snd (V 0)))))]))))

/-- `introKids v N S y pre ks` -/
def introKidsTm : Tm :=
  .ite (.isNat (V 5)) (.lit 0)
    (.letE (.call fIntroPlans [V 0, V 1, .fst (V 5)])
      (.call fAppend
        [.call fMap [.lit fKid, .cons (.call fLength [V 5]) (.cons (V 3) (.cons (V 4) (.cons (V 5) (.snd (V 6))))), V 0],
         .call fIntroKids [V 1, V 2, V 3, V 4, .call fAppend [V 5, .cons (.fst (V 6)) (.lit 0)], .snd (V 6)]]))

open E3A in
/-- `introPlans v N t` -/
def introPlansTm : Tm :=
  .call fAppend
    [.call fAppend
      [.call fMap [.lit fMk1, .lit 0, .call fFilter [.lit fSubN, V 1, .call E3B.fWtopPlans [V 0, V 2]]],
       .ite (.call Lib3.fSubsetS [V 1, cS (V 2)])
         (.call fMap [.lit fMk2, .lit 0, .call E3B.fAttachPlans [V 0, V 1, V 2]]) (.lit 0)],
     .call fIntroKids [V 0, V 1, cS (V 2), cY (V 2), .lit 0, cK (V 2)]]

def maxLTm : Tm := .ite (.isNat (V 0)) (.lit 0) (.call fMax [.fst (V 0), .call fMaxL [.snd (V 0)]])

def maxEntryLTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0) (.call fMax [.call fMaxEntry [.fst (V 0)], .call fMaxEntryL [.snd (V 0)]])

open E3A in
def maxEntryTm : Tm := .call fMax [.call fMaxL [cY (V 0)], .call fMaxEntryL [cK (V 0)]]

def normOfTm : Tm := .call fNormId [.snd (.snd (V 1))]

def leKCTm : Tm := .sub (.lit 1) (.lt (V 0) (.call fMaxEntry [V 1]))

/-- `introC kmax v N t` -/
def introCTm : Tm :=
  .call fFilter [.lit fLeKC, V 0, .call fMap [.lit fNormOf, .lit 0, .call fIntroPlans [V 1, V 2, V 3]]]

/-- `introC` on the packed argument `p = (kmax, v, N, t)` -/
def introCUnTm : Tm :=
  .call fIntroC [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 320 => some subNTm | 321 => some mk1Tm | 322 => some mk2Tm | 323 => some kidTm
  | 324 => some introKidsTm | 325 => some introPlansTm | 326 => some maxLTm | 327 => some maxEntryLTm
  | 328 => some maxEntryTm | 329 => some normOfTm | 330 => some leKCTm | 331 => some introCTm
  | 332 => some introCUnTm
  | _ => none

/-- layers A, B and C of the E3 table -/
def Δ : ℕ → Option Tm := layerΔ E3B.Δ 320 tbl

theorem tbl_lt {f : ℕ} {b : Tm} (h : tbl f = some b) : 320 ≤ f ∧ f < 333 := by
  unfold tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem extB : E3B.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E3B.Δ_lt h; omega)

theorem Δ_subN : Δ fSubN = some subNTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fSubN by decide)]; rfl
theorem Δ_mk1 : Δ fMk1 = some mk1Tm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fMk1 by decide)]; rfl
theorem Δ_mk2 : Δ fMk2 = some mk2Tm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fMk2 by decide)]; rfl
theorem Δ_kid : Δ fKid = some kidTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fKid by decide)]; rfl
theorem Δ_introKids : Δ fIntroKids = some introKidsTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fIntroKids by decide)]; rfl
theorem Δ_introPlans : Δ fIntroPlans = some introPlansTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fIntroPlans by decide)]; rfl
theorem Δ_maxL : Δ fMaxL = some maxLTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fMaxL by decide)]; rfl
theorem Δ_maxEntryL : Δ fMaxEntryL = some maxEntryLTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fMaxEntryL by decide)]; rfl
theorem Δ_maxEntry : Δ fMaxEntry = some maxEntryTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fMaxEntry by decide)]; rfl
theorem Δ_normOf : Δ fNormOf = some normOfTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fNormOf by decide)]; rfl
theorem Δ_leKC : Δ fLeKC = some leKCTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fLeKC by decide)]; rfl
theorem Δ_introC : Δ fIntroC = some introCTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fIntroC by decide)]; rfl

theorem ids_lt {B : ℕ} (h : 500 < B) :
    fSubN < B ∧ fMk1 < B ∧ fMk2 < B ∧ fKid < B ∧ fIntroKids < B ∧ fIntroPlans < B ∧ fMaxL < B ∧
      fMaxEntryL < B ∧ fMaxEntry < B ∧ fNormOf < B ∧ fLeKC < B ∧ fIntroC < B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.lt_of_le_of_lt (by decide) h

end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3Util` -/

section
/-!
# WP E3: small utilities (size / `mx` facts about the data the enumerations manipulate)
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars

theorem mx_le_of_sublist {l l' : List ℕ} (h : l.Sublist l') : mx l ≤ mx l' := by
  rw [mx_list_le]
  intro a ha
  exact mx_le_of_mem (h.subset ha)

theorem mx_take_le (n : ℕ) (l : List ℕ) : mx (l.take n) ≤ mx l := mx_le_of_sublist (List.take_sublist _ _)
theorem mx_drop_le (n : ℕ) (l : List ℕ) : mx (l.drop n) ≤ mx l := mx_le_of_sublist (List.drop_sublist _ _)

/-- the pieces of a well-bounded characteristic node -/
theorem ct_node_facts {U : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT}
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) :
    S.card ≤ U ∧ y.length ≤ U ∧ sz ks + 1 ≤ U ∧ mx S ≤ U ∧ mx y ≤ U ∧ mx ks ≤ U ∧ sz S ≤ U ∧ sz y ≤ U := by
  rw [sz_ct_node] at hU
  rw [mx_ct_node] at hM
  have h1 := sz_finset S
  have h2 := sz_list_nat y
  have h3 := sz_pos ks
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem foldCost_le {α β : Type} (g : β → α → β) (cf : β → α → ℕ) (P : β → Prop) (c : ℕ) :
    ∀ (l : List α) (b : β), P b → (∀ b' a, P b' → a ∈ l → P (g b' a)) →
      (∀ b' a, P b' → a ∈ l → cf b' a ≤ c) → Lib1.foldCost g cf b l ≤ l.length * c := by
  intro l
  induction l with
  | nil => intro b _ _ _; simp [Lib1.foldCost]
  | cons a l ih =>
    intro b hb hstep hcf
    have h1 := hcf b a hb (List.mem_cons_self ..)
    have h2 := ih (g b a) (hstep b a hb (List.mem_cons_self ..))
      (fun b' x hb' hx => hstep b' x hb' (List.mem_cons_of_mem _ hx))
      (fun b' x hb' hx => hcf b' x hb' (List.mem_cons_of_mem _ hx))
    simp only [Lib1.foldCost, List.length_cons]
    nlinarith

theorem sum_map_le {α : Type} (f : α → ℕ) (c : ℕ) (l : List α) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- the arithmetic of one step of `kidChoices` -/
theorem kc_arith (m n a K Q : ℕ) (hK : 1 ≤ K) (hQ : 1000 ≤ Q) :
    60 + Q * m * (a + 1) + 32 * a + Q * n * (K + 1) + (a + 1) * (33 * K + 32) + 20 ≤
      Q * (m + n + 1) * ((a + 1) * K + 1) := by
  have hAK : a + 1 ≤ (a + 1) * K := Nat.le_mul_of_pos_right _ hK
  have s1 : Q * m * (a + 1) ≤ Q * m * ((a + 1) * K + 1) := Nat.mul_le_mul_left _ (by omega)
  have s2 : Q * n * (K + 1) ≤ Q * n * ((a + 1) * K + 1) := Nat.mul_le_mul_left _ (by nlinarith)
  have s3 : 32 * a + (a + 1) * (33 * K + 32) + 80 ≤ Q * ((a + 1) * K + 1) := by
    have : (a + 1) * (33 * K + 32) ≤ 65 * ((a + 1) * K) := by nlinarith
    nlinarith
  have e : Q * (m + n + 1) * ((a + 1) * K + 1) =
      Q * m * ((a + 1) * K + 1) + Q * n * ((a + 1) * K + 1) + Q * ((a + 1) * K + 1) := by ring
  omega

theorem flatMap_sum_le {α β : Type} (g : α → List β) (cf : α → ℕ) (C : ℕ) :
    ∀ (l : List α), (∀ a ∈ l, cf a + 10 * (g a).length + 20 ≤ C * (g a).length) →
      (l.map (fun a => cf a + 10 * (g a).length + 20)).sum ≤ C * (l.flatMap g).length
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (List.mem_cons_self ..)
    have h2 := flatMap_sum_le g cf C l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    nlinarith

theorem foldrCost_le {α β : Type} (g : α → β → β) (cf : α → β → ℕ) (P : β → Prop) (z : β) (c : ℕ) (hz : P z) :
    ∀ (l : List α), (∀ a b, a ∈ l → P b → P (g a b)) → (∀ a b, a ∈ l → P b → cf a b ≤ c) →
      Lib2.foldrCost g cf z l ≤ l.length * c
  | [], _, _ => by simp [Lib2.foldrCost]
  | a :: l, hs, hc => by
    have hP : P (l.foldr g z) :=
      Lib2.foldr_inv g P z hz l (fun a' b ha' hb => hs a' b (List.mem_cons_of_mem _ ha') hb)
    have h1 := hc a _ (List.mem_cons_self ..) hP
    have h2 := foldrCost_le g cf P z c hz l (fun a' b ha' hb => hs a' b (List.mem_cons_of_mem _ ha') hb)
      (fun a' b ha' hb => hc a' b (List.mem_cons_of_mem _ ha') hb)
    simp only [Lib2.foldrCost, List.length_cons]
    nlinarith

theorem sum_affine_le {α β : Type} (g : α → List β) (cf : α → ℕ) (a b : ℕ) :
    ∀ (l : List α), (∀ x ∈ l, cf x + 10 * (g x).length + 20 ≤ a * (g x).length + b) →
      (l.map (fun x => cf x + 10 * (g x).length + 20)).sum ≤ a * (l.flatMap g).length + b * l.length
  | [], _ => by simp
  | x :: l, h => by
    have h1 := h x (List.mem_cons_self ..)
    have h2 := sum_affine_le g cf a b l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem filter_len_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | a :: l, h => by
    have ih := filter_len_le_of_imp p q l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    by_cases hp : p a = true
    · have hq := ha hp
      simp [List.filter_cons, hp, hq]; omega
    · by_cases hq : q a = true
      · simp [List.filter_cons, hp, hq]; omega
      · simp [List.filter_cons, hp, hq]; omega

end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3MathA` -/

section
/-!
# WP E3: facts about `winPlans` / `kidChoices` used by the cost analysis

* every vertex set in the output is contained in `verts` of the input (so its cardinality is `≤ sz`);
* `card_verts_le_sz`;
* every combination has one entry per kid, and `kidChoices` is never empty;
* the `whole` part of `winPlans` is at least as long as `kidChoices`.
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars CT

theorem card_vertsL_le_sz : ∀ (ks : List CT), (∀ k ∈ ks, (verts k).card ≤ sz k) → (vertsL ks).card ≤ sz ks
  | [], _ => by simp [vertsL, sz_nil]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := card_vertsL_le_sz ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    have := Finset.card_union_le (verts k) (vertsL ks)
    rw [sz_cons]; simp only [vertsL]; omega

theorem card_verts_le_sz (t : CT) : (verts t).card ≤ sz t := by
  induction t using CT.ind with
  | h S y ks ih =>
    have h1 := card_vertsL_le_sz ks ih
    have h2 := Finset.card_union_le S (vertsL ks)
    rw [sz_ct_node, sz_finset, verts_node]
    have := sz_pos y
    omega

theorem foldl_union_sub (V : Finset ℕ) :
    ∀ (combo : List (Option WPlan × CT × Finset ℕ)) (S : Finset ℕ), S ⊆ V → (∀ c ∈ combo, c.2.2 ⊆ V) →
      combo.foldl (fun a c => a ∪ c.2.2) S ⊆ V
  | [], S, hS, _ => by simpa using hS
  | c :: combo, S, hS, h => by
    simp only [List.foldl_cons]
    exact foldl_union_sub V combo _ (Finset.union_subset hS (h c (by simp)))
      (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

mutual
theorem winPlans_sub (v : ℕ) : ∀ (lo : ℕ) (t : CT), ∀ x ∈ winPlans v lo t, x.2.2 ⊆ t.verts
  | lo, node S y ks, x, hx => by
    simp only [winPlans, List.mem_append, List.mem_map] at hx
    have hS : S ⊆ (node S y ks).verts := subset_verts (node S y ks)
    rcases hx with (⟨f, _, rfl⟩ | ⟨f, _, rfl⟩) | ⟨combo, hcombo, rfl⟩
    · exact hS
    · exact hS
    · have := kidChoices_sub v ks combo hcombo
      refine foldl_union_sub _ combo S hS (fun c hc => ?_)
      exact fun w hw => mem_verts_node.2 (Or.inr (by
        have := (mem_vertsL.1 (this c hc hw)); exact this))
theorem kidChoices_sub (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks, ∀ c ∈ combo, c.2.2 ⊆ vertsL ks
  | [], combo, h, c, hc => by
    simp only [kidChoices, List.mem_singleton] at h; subst h; simp at hc
  | k :: ks, combo, h, c, hc => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    have ih := kidChoices_sub v ks combo' hcombo'
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases List.mem_cons.1 ho with rfl | ho
      · intro w hw; simp at hw
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        have := winPlans_sub v 0 k p hp
        intro w hw
        simp only [vertsL, Finset.mem_union]
        exact Or.inl (this hw)
    · intro w hw
      simp only [vertsL, Finset.mem_union]
      exact Or.inr (ih c hc hw)
end

theorem kidChoices_combo_length (v : ℕ) : ∀ (ks : List CT), ∀ combo ∈ kidChoices v ks, combo.length = ks.length
  | [], combo, h => by simp only [kidChoices, List.mem_singleton] at h; subst h; simp
  | k :: ks, combo, h => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map] at h
    obtain ⟨o, ho, combo', hcombo', rfl⟩ := h
    simp [kidChoices_combo_length v ks combo' hcombo']

theorem kidChoices_length_pos (v : ℕ) : ∀ (ks : List CT), 1 ≤ (kidChoices v ks).length
  | [] => by simp [kidChoices]
  | k :: ks => by
    have := kidChoices_length_pos v ks
    simp only [kidChoices, List.length_flatMap]
    have h1 : (kidChoices v ks).length ≤ (List.map (fun o => (List.map (fun x => o :: x) (kidChoices v ks)).length) ((none, k, (∅ : Finset ℕ)) :: List.map (fun p => (some p.1, p.2.1, p.2.2)) (winPlans v 0 k))).sum := by
      simp only [List.map_cons, List.sum_cons, List.length_map]; omega
    omega

theorem kidChoices_le_winPlans (v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    (kidChoices v ks).length ≤ (winPlans v lo (node S y ks)).length := by
  simp only [winPlans, List.length_append, List.length_map]; omega

end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3A1` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3A

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem plus1_runs : ∀ (y : List ℕ), mx y + 2 < B →
    Runs Δ' B fPlus1 [toVal y] (toVal (CT.plus1 y)) (12 * y.length + 6) := by
  intro y
  induction y with
  | nil =>
    intro _
    refine Runs.mk (hΔ _ _ Δ_plus1) ?_
    ev_start
    · ev_run
    · simp [CT.plus1]
  | cons a l ih =>
    intro hB
    have hm : mx l + 2 < B := by simp only [mx_cons, mx_nat] at hB; omega
    have ha : a + 1 < B := by simp only [mx_cons, mx_nat] at hB; omega
    have ih := ih hm
    refine Runs.mk (hΔ _ _ Δ_plus1) ?_
    ev_start
    · ev_run
    · simp [CT.plus1]; omega

theorem rangeP_runs : ∀ (n lo : ℕ), lo + n + 2 < B →
    Runs Δ' B fRangeP [toVal lo, toVal n] (toVal (List.range' lo n)) (14 * n + 6) := by
  intro n
  induction n with
  | zero =>
    intro lo _
    refine Runs.mk (hΔ _ _ Δ_rangeP) ?_
    ev_start
    · ev_run
    · simp
  | succ n ih =>
    intro lo hB
    have ih := ih (lo + 1) (by omega)
    refine Runs.mk (hΔ _ _ Δ_rangeP) ?_
    ev_start
    · ev_run
    · simp; omega

theorem x1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans extLib hΔ)
theorem x3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans extLib hΔ)

theorem ends1_runs (U v lo f : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U) (hf : f ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fEnds1 [toVal (v, lo, CT.node S y ks), toVal f]
      (toVal (CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S))
      (400 * (U + 1)) := by
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h2 := take_runs (x1 hΔ) B (f + 1) y (by omega)
  have h3 := drop_runs (x1 hΔ) B lo (y.take (f + 1)) (by omega)
  have h4 := drop_runs (x1 hΔ) B f y (by omega)
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h5 := plus1_runs hΔ B ((y.take (f + 1)).drop lo)
    (by have := mx_drop_le lo (y.take (f + 1)); have := mx_take_le (f + 1) y; omega)
  have h6 : ((y.take (f + 1)).drop lo).length ≤ U := by simp only [List.length_drop, List.length_take]; omega
  have h7 : min lo (y.take (f + 1)).length ≤ U := by omega
  have h8 : min f y.length ≤ U := by omega
  have h9 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_ends1) ?_
  simp only [toVal_pair, CT.WPlan.endAt, toVal_wp_endAt, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem ends2_runs (U v lo f : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U) (hf : f ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fEnds2 [toVal (v, lo, CT.node S y ks), toVal f]
      (toVal (CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S))
      (400 * (U + 1)) := by
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h2 := take_runs (x1 hΔ) B (f + 1) y (by omega)
  have h3 := drop_runs (x1 hΔ) B lo (y.take (f + 1)) (by omega)
  have h4 := drop_runs (x1 hΔ) B (f + 1) y (by omega)
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h5 := plus1_runs hΔ B ((y.take (f + 1)).drop lo)
    (by have := mx_drop_le lo (y.take (f + 1)); have := mx_take_le (f + 1) y; omega)
  have h6 : ((y.take (f + 1)).drop lo).length ≤ U := by simp only [List.length_drop, List.length_take]; omega
  have h7 : min lo (y.take (f + 1)).length ≤ U := by omega
  have h8 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_ends2) ?_
  simp only [toVal_pair, CT.WPlan.endAt, toVal_wp_endAt, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem fstF_runs (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fFstF [Val.nat 0, toVal (o, c, s)] (toVal o) 2 := by
  refine Runs.mk (hΔ _ _ Δ_fstF) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sndFstF_runs (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fSndFstF [Val.nat 0, toVal (o, c, s)] (toVal c) 3 := by
  refine Runs.mk (hΔ _ _ Δ_sndFstF) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem unionStep_runs (acc : Finset ℕ) (o : Option CT.WPlan) (c : CT) (s : Finset ℕ) :
    Runs Δ' B fUnionStep [Val.nat 0, toVal acc, toVal (o, c, s)] (toVal (acc ∪ s)) (60 * (acc.card + s.card) + 40) := by
  have h1 := Lib3.union_runs (x3 hΔ) B acc s
  refine Runs.mk (hΔ _ _ Δ_unionStep) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem whole_runs (U v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (V : Finset ℕ)
    (combo : List (Option CT.WPlan × CT × Finset ℕ))
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hlo : lo ≤ U)
    (hV : V.card ≤ U) (hSV : S ⊆ V) (hc : ∀ c ∈ combo, c.2.2 ⊆ V) (hlen : combo.length ≤ U)
    (hB : 4 * U + 400 < B) :
    Runs Δ' B fWhole [toVal (v, lo, CT.node S y ks), toVal combo]
      (toVal (CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S))
      (400 * (U + 1) * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := Lib3.insert_runs (x3 hΔ) B v S
  have h3 := drop_runs (x1 hΔ) B lo y (by omega)
  have h5 := plus1_runs hΔ B (y.drop lo) (by have := mx_drop_le lo y; omega)
  have h6 : (y.drop lo).length ≤ U := by simp only [List.length_drop]; omega
  have h7 : min lo y.length ≤ U := by omega
  have hm1 := map_runs (x1 hΔ) B fFstF (Val.nat 0) (fun x : Option CT.WPlan × CT × Finset ℕ => x.1) (fun _ => 2)
    combo (fun a _ => by obtain ⟨o, c, s⟩ := a; exact fstF_runs hΔ B o c s)
  have hm2 := map_runs (x1 hΔ) B fSndFstF (Val.nat 0) (fun x : Option CT.WPlan × CT × Finset ℕ => x.2.1) (fun _ => 3)
    combo (fun a _ => by obtain ⟨o, c, s⟩ := a; exact sndFstF_runs hΔ B o c s)
  have hfold := foldl_runs (x1 hΔ) B fUnionStep (Val.nat 0)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => a ∪ c.2.2)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => 60 * (a.card + c.2.2.card) + 40)
    (fun b => b ⊆ V) S combo hSV
    (fun b' a hb ha => Finset.union_subset hb (hc a ha))
    (fun b' a hb ha => by obtain ⟨o, c, s⟩ := a; exact unionStep_runs hΔ B b' o c s)
  have hfc := foldCost_le (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => a ∪ c.2.2)
    (fun (a : Finset ℕ) (c : Option CT.WPlan × CT × Finset ℕ) => 60 * (a.card + c.2.2.card) + 40)
    (fun b => b ⊆ V) (120 * U + 40) combo S hSV
    (fun b' a hb ha => Finset.union_subset hb (hc a ha))
    (fun b' a hb ha => by
      have h1 := Finset.card_le_card hb
      have h2 := Finset.card_le_card (hc a ha)
      show 60 * (b'.card + a.2.2.card) + 40 ≤ 120 * U + 40
      omega)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm1 hm2
  have hid := ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_whole) ?_
  simp only [toVal_pair, CT.WPlan.whole, toVal_wp_whole, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · have e1 : combo.length * (120 * U + 40) ≤ U * (120 * U + 40) := Nat.mul_le_mul_right _ hlen
    have e2 : U * (120 * U + 40) + 900 * U + 500 ≤ 400 * (U + 1) * (U + 1) := by nlinarith
    omega

theorem someF_runs (c : CT) (s : Finset ℕ) (p : CT.WPlan) (hB : 1 < B) :
    Runs Δ' B fSomeF [Val.nat 0, toVal (p, c, s)] (toVal ((some p, c, s) : Option CT.WPlan × CT × Finset ℕ)) 12 := by
  refine Runs.mk (hΔ _ _ Δ_someF) ?_
  simp only [toVal_pair, toVal_some]
  ev_start
  · ev_run
  · omega

theorem consF_runs {α : Type} [ToVal α] (o : α) (x : List α) :
    Runs Δ' B fConsF [toVal o, toVal x] (toVal (o :: x)) 3 := by
  refine Runs.mk (hΔ _ _ Δ_consF) ?_
  simp only [toVal_cons]
  ev_start
  · ev_run
  · omega

theorem kcLam_runs {α : Type} [ToVal α] (o : α) (kc : List (List α)) (hB : 300 < B) :
    Runs Δ' B fKcLam [toVal kc, toVal o] (toVal (kc.map (o :: ·))) (23 * kc.length + 12) := by
  have hm := map_runs (x1 hΔ) B fConsF (toVal o) (fun x : List α => o :: x) (fun _ => 3) kc
    (fun a _ => consF_runs hΔ B o a)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm
  have hid := ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_kcLam) ?_
  ev_start
  · ev_run
  · omega

end proofs
end E3A
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3A2` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3A

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem winPlans_runs_rec (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (v lo : ℕ) (hv : v ≤ U) (hlo : lo ≤ U) :
    ∀ (t : CT), sz t ≤ U → mx t ≤ U → 10 * U + 400 < B →
      Runs Δ' B fWinPlans [toVal v, toVal lo, toVal t] (toVal (winPlans v lo t))
        (Q * (3 * CT.count t - 1) * ((winPlans v lo t).length + 1))
  | CT.node S y ks, hU, hM, hB => by
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
    have hkc := kidChoices_runs_rec U Q hQ v hv ks (by omega) (by omega) hB
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    have hlen := length_runs (x1 hΔ) B y (by omega)
    have hr1 := rangeP_runs hΔ B (y.length - lo) lo (by omega)
    have hr2 := rangeP_runs hΔ B (y.length - 1 - lo) lo (by omega)
    have hm1 := map_runs (x1 hΔ) B fEnds1 (toVal (v, lo, CT.node S y ks))
      (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1)) (List.range' lo (y.length - lo))
      (fun f hf => by
        rw [List.mem_range'_1] at hf
        exact ends1_runs hΔ B U v lo f S y ks hU hM hv hlo (by omega) (by omega))
    have hm2 := map_runs (x1 hΔ) B fEnds2 (toVal (v, lo, CT.node S y ks))
      (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1)) (List.range' lo (y.length - 1 - lo))
      (fun f hf => by
        rw [List.mem_range'_1] at hf
        exact ends2_runs hΔ B U v lo f S y ks hU hM hv hlo (by omega) (by omega))
    have hV : (CT.node S y ks).verts.card ≤ U := le_trans (card_verts_le_sz _) hU
    have hSV : S ⊆ (CT.node S y ks).verts := CT.subset_verts (CT.node S y ks)
    have hm3 := map_runs (x1 hΔ) B fWhole (toVal (v, lo, CT.node S y ks))
      (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ))
      (fun _ => 400 * (U + 1) * (U + 1)) (kidChoices v ks)
      (fun combo hc => whole_runs hΔ B U v lo S y ks (CT.node S y ks).verts combo hU hM hv hlo hV hSV
        (fun c hc' w hw => CT.mem_verts_node.2 (Or.inr (CT.mem_vertsL.1 (kidChoices_sub v ks combo hc c hc' hw))))
        (by rw [kidChoices_combo_length v ks combo hc]; exact le_trans (length_le_sz ks) (by omega)) (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hm1 hm2 hm3
    have ha1 := append_runs (x1 hΔ) B
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)))
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)))
    have ha2 := append_runs (x1 hΔ) B
      (List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)) ++
       List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)))
      (List.map (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
        combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ)) (kidChoices v ks))
    have hshow : winPlans v lo (CT.node S y ks) =
        List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t1 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop f) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - lo)) ++
        List.map (fun f : ℕ => ((CT.WPlan.endAt (CT.Cut.t2 f), CT.node (insert v S) (CT.plus1 ((y.take (f + 1)).drop lo)) [CT.node S (y.drop (f + 1)) ks], S) : CT.WPlan × CT × Finset ℕ)) (List.range' lo (y.length - 1 - lo)) ++
        List.map (fun combo : List (Option CT.WPlan × CT × Finset ℕ) => ((CT.WPlan.whole (combo.map (·.1)), CT.node (insert v S) (CT.plus1 (y.drop lo)) (combo.map (·.2.1)),
          combo.foldl (fun a c => a ∪ c.2.2) S) : CT.WPlan × CT × Finset ℕ)) (kidChoices v ks) := rfl
    rw [hshow]
    simp only [toVal_pair, toVal_ct] at hm1 hm2 hm3
    refine Runs.mk (hΔ _ _ Δ_winPlans) ?_
    simp only [toVal_ct]
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_step
    · simp only [List.length_append, List.length_map, List.length_range']
      have hcnt : CT.count (CT.node S y ks) = 1 + countL ks := rfl
      have q1 : 400 * (U + 1) + 64 ≤ Q := by nlinarith
      have q2 : 400 * (U + 1) * (U + 1) + 32 ≤ Q := by nlinarith
      have q3 : 16 * U + 300 ≤ Q := by nlinarith
      have p1 : (y.length - lo) * (400 * (U + 1) + 64) ≤ (y.length - lo) * Q := Nat.mul_le_mul_left _ q1
      have p2 : (y.length - 1 - lo) * (400 * (U + 1) + 64) ≤ (y.length - 1 - lo) * Q := Nat.mul_le_mul_left _ q1
      have p3 : (kidChoices v ks).length * (400 * (U + 1) * (U + 1) + 32) ≤ (kidChoices v ks).length * Q :=
        Nat.mul_le_mul_left _ q2
      have hKL : (kidChoices v ks).length ≤ (y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length := by omega
      have eP : Q * (3 * countL ks + 1) * ((kidChoices v ks).length + 1) ≤
          Q * (3 * countL ks + 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have eR : Q * (3 * CT.count (CT.node S y ks) - 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) =
          Q * (3 * countL ks + 1) * ((y.length - lo) + (y.length - 1 - lo) + (kidChoices v ks).length + 1) +
          (Q * (y.length - lo) + Q * (y.length - 1 - lo) + Q * (kidChoices v ks).length + Q) := by
        rw [hcnt]
        have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
        rw [this]; ring
      have m1 : (y.length - lo) * Q = Q * (y.length - lo) := Nat.mul_comm _ _
      have m2 : (y.length - 1 - lo) * Q = Q * (y.length - 1 - lo) := Nat.mul_comm _ _
      have m3 : (kidChoices v ks).length * Q = Q * (kidChoices v ks).length := Nat.mul_comm _ _
      have m4 : ∀ a b : ℕ, a * (400 * (U + 1) + 64) = a * (400 * (U + 1)) + 64 * a := fun a b => by ring
      have m5 : ∀ a : ℕ, a * (400 * (U + 1) * (U + 1) + 32) = a * (400 * (U + 1) * (U + 1)) + 32 * a := fun a => by ring
      have := m4 (y.length - lo) 0
      have := m4 (y.length - 1 - lo) 0
      have := m5 (kidChoices v ks).length
      omega
theorem kidChoices_runs_rec (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (v : ℕ) (hv : v ≤ U) :
    ∀ (ks : List CT), sz ks ≤ U → mx ks ≤ U → 10 * U + 400 < B →
      Runs Δ' B fKidChoices [toVal v, toVal ks] (toVal (kidChoices v ks))
        (Q * (3 * CT.countL ks + 1) * ((kidChoices v ks).length + 1))
  | [], hU, hM, hB => by
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    refine Runs.mk (hΔ _ _ Δ_kidChoices) ?_
    simp only [kidChoices, toVal_cons, toVal_nil]
    ev_start
    · ev_run
    · simp [CT.countL]; omega
  | k :: ks, hU, hM, hB => by
    have hQ1 : 1000 ≤ Q := by nlinarith
    have hid := ids_lt (B := B) (by omega)
    have hU' : sz k ≤ U ∧ sz ks ≤ U := by rw [sz_cons] at hU; omega
    have hM' : mx k ≤ U ∧ mx ks ≤ U := by rw [mx_cons] at hM; omega
    have hw := winPlans_runs_rec U Q hQ v 0 hv (Nat.zero_le _) k hU'.1 hM'.1 hB
    have hkc := kidChoices_runs_rec U Q hQ v hv ks hU'.2 hM'.2 hB
    have hmap := map_runs (x1 hΔ) B fSomeF (Val.nat 0)
      (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))
      (fun _ => 12) (winPlans v 0 k)
      (fun p _ => by obtain ⟨w, c, s⟩ := p; exact someF_runs hΔ B c s w (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hfm := flatMap_runs (x1 hΔ) B fKcLam (toVal (kidChoices v ks))
      (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·))
      (fun _ => 23 * (kidChoices v ks).length + 12)
      ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ)))
      (fun o _ => kcLam_runs hΔ B o (kidChoices v ks) (by omega))
    have hsum := sum_map_le (fun (a : Option CT.WPlan × CT × Finset ℕ) => (23 * (kidChoices v ks).length + 12) + 10 * ((kidChoices v ks).map (a :: ·)).length + 20) (33 * (kidChoices v ks).length + 32)
      ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ)))
      (fun a _ => by simp only [List.length_map]; omega)
    have hlen := kidChoices_length_pos v ks
    have hshow : kidChoices v (k :: ks) = ((none, k, ∅) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))).flatMap (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·)) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_kidChoices) ?_
    simp only [toVal_cons, toVal_pair, toVal_none, toVal_empty_finset]
    ev_start
    · ev_run
    · have hpos := count_pos k
      have hlo : ((none, k, (∅ : Finset ℕ)) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))).length = (winPlans v 0 k).length + 1 := by simp
      have hlenout : List.length (List.flatMap (fun o : Option CT.WPlan × CT × Finset ℕ => (kidChoices v ks).map (o :: ·))
          ((none, k, (∅ : Finset ℕ)) :: (winPlans v 0 k).map (fun p : CT.WPlan × CT × Finset ℕ => ((some p.1, p.2.1, p.2.2) : Option CT.WPlan × CT × Finset ℕ))))
          = ((winPlans v 0 k).length + 1) * (kidChoices v ks).length := by
        rw [length_flatMap_eq (n := (kidChoices v ks).length)]
        · rw [hlo]
        · intro o _; simp
      rw [hlo] at hsum
      rw [hlenout]
      have key := kc_arith (3 * count k - 1) (3 * countL ks + 1) (winPlans v 0 k).length
        (kidChoices v ks).length Q hlen hQ1
      have e : 3 * countL (k :: ks) + 1 = (3 * count k - 1) + (3 * countL ks + 1) + 1 := by
        simp only [countL]; omega
      rw [e]
      omega
end

end proofs

theorem winPlans_runs_pair : (type_of% @winPlans_runs_rec) ∧ (type_of% @kidChoices_runs_rec) :=
  ⟨@winPlans_runs_rec, @kidChoices_runs_rec⟩

theorem winPlans_runs : type_of% @winPlans_runs_rec := winPlans_runs_pair.1

end E3A
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3B1` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem xA : E3A.Δ ⊑ Δ' := Ext.trans extA hΔ
theorem y1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans E3A.extLib (xA hΔ))
theorem y2 : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans E3A.extLib (xA hΔ))
theorem y3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans E3A.extLib (xA hΔ))
theorem y4 : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans E3A.extLib (xA hΔ))

theorem topDirect_runs (w : CT.WPlan) (c : CT) (s : Finset ℕ) (hB : 2 < B) :
    Runs Δ' B fTopDirect [Val.nat 0, toVal (w, c, s)]
      (toVal ((CT.Plan.top none w, c, s) : CT.Plan × CT × Finset ℕ)) 14 := by
  refine Runs.mk (hΔ _ _ Δ_topDirect) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_none]
  ev_start
  · ev_run
  · omega

theorem pre1In_runs (U f v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (w : CT.WPlan) (c : CT) (s : Finset ℕ)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPre1In [toVal (f, v, CT.node S y ks), toVal (w, c, s)]
      (toVal ((CT.Plan.top (some (CT.Cut.t1 f)) w, CT.node S (y.take (f + 1)) [c], s) : CT.Plan × CT × Finset ℕ))
      (30 * U + 100) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_pre1In) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_some, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem pre2In_runs (U f v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) (w : CT.WPlan) (c : CT) (s : Finset ℕ)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPre2In [toVal (f, v, CT.node S y ks), toVal (w, c, s)]
      (toVal ((CT.Plan.top (some (CT.Cut.t2 f)) w, CT.node S (y.take (f + 1)) [c], s) : CT.Plan × CT × Finset ℕ))
      (30 * U + 100) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_pre2In) ?_
  simp only [toVal_pair, toVal_plan_top, toVal_some, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

omit hΔ in
theorem winPlans_length_pos (v lo : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    1 ≤ (winPlans v lo (CT.node S y ks)).length :=
  le_trans (kidChoices_length_pos v ks) (kidChoices_le_winPlans v lo S y ks)

theorem pre1_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v f : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fPre1 [toVal (v, CT.node S y ks), toVal f]
      (toVal ((winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
      (8 * (P * (winPlans v f (CT.node S y ks)).length)) := by
  have hcnt := count_pos (CT.node S y ks)
  have hL := winPlans_length_pos v f S y ks
  have hw := (E3A.winPlans_runs (xA hΔ) B U Q hQ v f hv hf (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap := map_runs (y1 hΔ) B fPre1In (toVal (f, v, CT.node S y ks))
    (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 30 * U + 100) (winPlans v f (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact pre1In_runs hΔ B U f v S y ks w c s hU hM hf hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_pre1) ?_
  simp only [toVal_pair] at hmap ⊢
  ev_start
  · ev_run
  · have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
    have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
    have hq : 30 * U + 120 ≤ P := by omega
    have e1 : (winPlans v f (CT.node S y ks)).length * (30 * U + 100) ≤
        (winPlans v f (CT.node S y ks)).length * P := Nat.mul_le_mul_left _ (by omega)
    have e2 : P * ((winPlans v f (CT.node S y ks)).length + 1) = P * (winPlans v f (CT.node S y ks)).length + P := by ring
    have e3 : (winPlans v f (CT.node S y ks)).length * P = P * (winPlans v f (CT.node S y ks)).length := Nat.mul_comm _ _
    have e4 : P ≤ P * (winPlans v f (CT.node S y ks)).length := Nat.le_mul_of_pos_right _ hL
    have e5 := Nat.mul_le_mul_left (winPlans v f (CT.node S y ks)).length (show 20 ≤ P by omega)
    omega

theorem pre2_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v f : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U) (hf : f + 1 ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fPre2 [toVal (v, CT.node S y ks), toVal f]
      (toVal ((winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
      (8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) := by
  have hcnt := count_pos (CT.node S y ks)
  have hL := winPlans_length_pos v (f + 1) S y ks
  have hw := (E3A.winPlans_runs (xA hΔ) B U Q hQ v (f + 1) hv hf (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap := map_runs (y1 hΔ) B fPre2In (toVal (f, v, CT.node S y ks))
    (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 30 * U + 100) (winPlans v (f + 1) (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact pre2In_runs hΔ B U f v S y ks w c s hU hM (by omega) hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  refine Runs.mk (hΔ _ _ Δ_pre2) ?_
  simp only [toVal_pair] at hmap ⊢
  ev_start
  · ev_run
  · have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
    have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
    have hq : 30 * U + 120 ≤ P := by omega
    have e1 : (winPlans v (f + 1) (CT.node S y ks)).length * (30 * U + 100) ≤
        (winPlans v (f + 1) (CT.node S y ks)).length * P := Nat.mul_le_mul_left _ (by omega)
    have e2 : P * ((winPlans v (f + 1) (CT.node S y ks)).length + 1) = P * (winPlans v (f + 1) (CT.node S y ks)).length + P := by ring
    have e3 : (winPlans v (f + 1) (CT.node S y ks)).length * P = P * (winPlans v (f + 1) (CT.node S y ks)).length := Nat.mul_comm _ _
    have e4 : P ≤ P * (winPlans v (f + 1) (CT.node S y ks)).length := Nat.le_mul_of_pos_right _ hL
    have e5 := Nat.mul_le_mul_left (winPlans v (f + 1) (CT.node S y ks)).length (show 20 ≤ P by omega)
    omega

theorem wtopPlans_runs (U Q : ℕ) (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (P v : ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hB : 10 * U + 400 < B) (hP : Q * (3 * CT.count (CT.node S y ks) - 1) ≤ P) :
    Runs Δ' B fWtopPlans [toVal v, toVal (CT.node S y ks)] (toVal (wtopPlans v (CT.node S y ks)))
      (100 * (P * ((wtopPlans v (CT.node S y ks)).length + 1))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hcnt := count_pos (CT.node S y ks)
  have hL0 := winPlans_length_pos v 0 S y ks
  have hq1 : 1000 * (U + 1) ≤ Q := by nlinarith
  have hq2 : Q * 2 ≤ Q * (3 * CT.count (CT.node S y ks) - 1) := Nat.mul_le_mul_left _ (by omega)
  have hq : 1000 * (U + 1) ≤ P := le_trans hq1 (le_trans (Nat.le_mul_of_pos_right Q (by norm_num)) (le_trans hq2 hP))
  have hw0 := (E3A.winPlans_runs (xA hΔ) B U Q hQ v 0 hv (Nat.zero_le _) (CT.node S y ks) hU hM hB).mono
    (Nat.mul_le_mul_right _ hP)
  have hmap0 := map_runs (y1 hΔ) B fTopDirect (Val.nat 0)
    (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ))
    (fun _ => 14) (winPlans v 0 (CT.node S y ks))
    (fun p _ => by obtain ⟨w, c, s⟩ := p; exact topDirect_runs hΔ B w c s (by omega))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap0
  have hlen := length_runs (y1 hΔ) B y (by omega)
  have hr1 := range_runs (y1 hΔ) B y.length (by omega)
  have hr2 := range_runs (y1 hΔ) B (y.length - 1) (by omega)
  have hf1 := flatMap_runs (y1 hΔ) B fPre1 (toVal (v, CT.node S y ks))
    (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v f (CT.node S y ks)).length)) (List.range y.length)
    (fun f hf => pre1_runs hΔ B U Q hQ P v f S y ks hU hM hv (by rw [List.mem_range] at hf; omega) hB hP)
  have hs1 := flatMap_sum_le
    (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v f (CT.node S y ks)).length)) (9 * P) (List.range y.length)
    (fun f _ => by
      have hL := winPlans_length_pos v f S y ks
      simp only [List.length_map]
      have := Nat.mul_le_mul_left (winPlans v f (CT.node S y ks)).length (show 30 ≤ P by omega)
      have e : P * (winPlans v f (CT.node S y ks)).length = (winPlans v f (CT.node S y ks)).length * P := Nat.mul_comm _ _
      have e2 : 9 * P * (winPlans v f (CT.node S y ks)).length = 9 * ((winPlans v f (CT.node S y ks)).length * P) := by ring
      omega)
  have hf2 := flatMap_runs (y1 hΔ) B fPre2 (toVal (v, CT.node S y ks))
    (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) (List.range (y.length - 1))
    (fun f hf => pre2_runs hΔ B U Q hQ P v f S y ks hU hM hv (by rw [List.mem_range] at hf; omega) hB hP)
  have hs2 := flatMap_sum_le
    (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
    (fun f => 8 * (P * (winPlans v (f + 1) (CT.node S y ks)).length)) (9 * P) (List.range (y.length - 1))
    (fun f _ => by
      have hL := winPlans_length_pos v (f + 1) S y ks
      simp only [List.length_map]
      have := Nat.mul_le_mul_left (winPlans v (f + 1) (CT.node S y ks)).length (show 30 ≤ P by omega)
      have e : P * (winPlans v (f + 1) (CT.node S y ks)).length = (winPlans v (f + 1) (CT.node S y ks)).length * P := Nat.mul_comm _ _
      have e2 : 9 * P * (winPlans v (f + 1) (CT.node S y ks)).length = 9 * ((winPlans v (f + 1) (CT.node S y ks)).length * P) := by ring
      omega)
  have ha1 := append_runs (y1 hΔ) B
    ((winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)))
    ((List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
  have ha2 := append_runs (y1 hΔ) B
    ((winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)) ++
    (List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
    ((List.range (y.length - 1)).flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))))
  have hshow : wtopPlans v (CT.node S y ks) =
      (winPlans v 0 (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ => ((CT.Plan.top none p.1, p.2.1, p.2.2) : CT.Plan × CT × Finset ℕ)) ++
      (List.range y.length).flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))) ++
      (List.range (y.length - 1)).flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ))) := rfl
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_wtopPlans) ?_
  simp only [toVal_pair, toVal_ct] at hf1 hf2 hw0 ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_step
  · simp only [List.length_append, List.length_map] at hs1 hs2 ⊢
    set X0 := (winPlans v 0 (CT.node S y ks)).length with hX0
    set X1 := (List.flatMap (fun f : ℕ => (winPlans v f (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t1 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
        (List.range y.length)).length with hX1
    set X2 := (List.flatMap (fun f : ℕ => (winPlans v (f + 1) (CT.node S y ks)).map (fun p : CT.WPlan × CT × Finset ℕ =>
        ((CT.Plan.top (some (CT.Cut.t2 f)) p.1, CT.node S (y.take (f + 1)) [p.2.1], p.2.2) : CT.Plan × CT × Finset ℕ)))
        (List.range (y.length - 1))).length with hX2
    have e0 : P * (X0 + 1) = P * X0 + P := by ring
    have e1 : 9 * P * X1 = 9 * (P * X1) := by ring
    have e2 : 9 * P * X2 = 9 * (P * X2) := by ring
    have e3 : P * (X0 + X1 + X2 + 1) = P * X0 + P * X1 + P * X2 + P := by ring
    have f0 : X0 * 100 ≤ X0 * P := Nat.mul_le_mul_left _ (by omega)
    have f1 : X1 * 100 ≤ X1 * P := Nat.mul_le_mul_left _ (by omega)
    have g0 : X0 * P = P * X0 := Nat.mul_comm _ _
    have g1 : X1 * P = P * X1 := Nat.mul_comm _ _
    have hmul : ∀ a b : ℕ, 100 * (a * b) = 100 * (a * b) := fun _ _ => rfl
    have hy1 : y.length * 100 ≤ P := by omega
    have hp1 : P * X0 ≥ P := Nat.le_mul_of_pos_right _ (by omega)
    omega

end proofs
end E3B
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3B2` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem candFn_runs (U : ℕ) (N : Finset ℕ) (c : List ℕ) (hN : N.card ≤ U) (hc : c.length ≤ U) :
    Runs Δ' B fCandFn [toVal N, toVal c] (toVal (N ∪ c.toFinset)) (200 * ((U + 1) * (U + 1))) := by
  have h1 := Lib4.toFinset_runs (y4 hΔ) B c
  have h2 := Lib3.union_runs (y3 hΔ) B N c.toFinset
  have hc2 : c.toFinset.card ≤ U := le_trans (List.toFinset_card_le c) hc
  refine Runs.mk (hΔ _ _ Δ_candFn) ?_
  ev_start
  · ev_run
  · have e1 : (c.length + 1) ^ 2 ≤ (U + 1) * (U + 1) := by nlinarith
    have e2 : U + 1 ≤ (U + 1) * (U + 1) := by nlinarith
    omega

theorem chainCands_runs (U : ℕ) (S N : Finset ℕ) (hS : S.card ≤ U) (hN : N.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fChainCands [toVal S, toVal N] (toVal (chainCands S N))
      (500 * ((U + 1) * (U + 1)) * (chainCands S N).length) := by
  have hd := Lib3.sdiff_runs (y3 hΔ) B S N
  have hcard : ((S \ N).sort (· ≤ ·)).length ≤ U := by
    rw [Finset.length_sort]; exact le_trans (Finset.card_le_card Finset.sdiff_subset) hS
  have hsub := Lib4.sublists_runs (y4 hΔ) B (by omega) ((S \ N).sort (· ≤ ·))
  have hmap := map_runs (y1 hΔ) B fCandFn (toVal N)
    (fun c : List ℕ => N ∪ c.toFinset) (fun _ => 200 * ((U + 1) * (U + 1)))
    ((S \ N).sort (· ≤ ·)).sublists
    (fun c hc => candFn_runs hΔ B U N c hN
      (le_trans (List.mem_sublists.1 hc).length_le hcard))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hid := ids_lt (B := B) (by omega)
  have hlen : (chainCands S N).length = 2 ^ ((S \ N).sort (· ≤ ·)).length := by
    simp [chainCands, List.length_sublists]
  have hpos : 1 ≤ (chainCands S N).length := by rw [hlen]; exact Nat.one_le_two_pow
  have hshow : chainCands S N = ((S \ N).sort (· ≤ ·)).sublists.map (fun c : List ℕ => N ∪ c.toFinset) := rfl
  rw [hshow] at hlen hpos ⊢
  refine Runs.mk (hΔ _ _ Δ_chainCands) ?_
  ev_start
  · ev_run
  · simp only [List.length_map, List.length_sublists] at hlen hpos ⊢ hmap
    set T := 2 ^ ((S \ N).sort fun x1 x2 => x1 ≤ x2).length with hT
    have hT1 : 1 ≤ T := Nat.one_le_two_pow
    have hf1 : U + 1 ≤ (U + 1) * (U + 1) := by nlinarith
    have e1 : T * (200 * ((U + 1) * (U + 1))) = 200 * (T * ((U + 1) * (U + 1))) := by ring
    have e2 : 500 * ((U + 1) * (U + 1)) * T = 500 * (T * ((U + 1) * (U + 1))) := by ring
    have e3 : (U + 1) * (U + 1) ≤ T * ((U + 1) * (U + 1)) := Nat.le_mul_of_pos_left _ (by omega)
    have e4 : T ≤ T * ((U + 1) * (U + 1)) := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem subOf_runs (bound X : Finset ℕ) (b : Bool) (hb : b = true ↔ X ⊆ bound) (hB : 1 < B) :
    Runs Δ' B fSubOf [toVal bound, toVal X] (toVal b) (60 * (X.card + bound.card) + 30) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB X bound b hb
  refine Runs.mk (hΔ _ _ Δ_subOf) ?_
  ev_start
  · ev_run
  · omega

theorem pairCh_runs (chain : List (Finset ℕ)) (M : Finset ℕ) :
    Runs Δ' B fPairCh [toVal chain, toVal M] (toVal (chain, M)) 3 := by
  refine Runs.mk (hΔ _ _ Δ_pairCh) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sel_runs (bound X : Finset ℕ) (chain : List (Finset ℕ)) (hB : 1 < B) :
    Runs Δ' B fSel [toVal (bound, chain), toVal X]
      (toVal (decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))
      (120 * (X.card + bound.card) + 60) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB X bound (decide (X ⊆ bound)) (by simp)
  have h2 := Lib3.subset_runs (y3 hΔ) B hB bound X (decide (bound ⊆ X)) (by simp)
  refine Runs.mk (hΔ _ _ Δ_sel) ?_
  simp only [toVal_pair]
  by_cases hX : X ⊆ bound
  · simp only [hX, decide_true] at h1 ⊢
    cases chain with
    | nil =>
      simp only [toVal_nil, List.isEmpty_nil, Bool.true_or, Bool.and_true, decide_true, toVal_true] 
      ev_start
      · ev_run
      · omega
    | cons c cs =>
      by_cases hb : bound ⊆ X
      · have hne : ¬ X ⊂ bound := fun h => (Finset.ssubset_def.1 h).2 hb
        simp only [hb, decide_true] at h2
        simp only [List.isEmpty_cons, Bool.false_or, Bool.true_and, hne, decide_false, toVal_false]
        ev_start
        · ev_run
        · omega
      · have hss : X ⊂ bound := Finset.ssubset_def.2 ⟨hX, hb⟩
        simp only [hb, decide_false] at h2
        simp only [List.isEmpty_cons, Bool.false_or, Bool.true_and, hss, decide_true, toVal_true]
        ev_start
        · ev_run
        · omega
  · simp only [hX, decide_false, Bool.false_and, toVal_false] at h1 ⊢
    ev_start
    · ev_run
    · omega

theorem goStep_runs (cands : List (Finset ℕ)) (f : ℕ) (chain : List (Finset ℕ)) (X : Finset ℕ)
    (res : List (List (Finset ℕ) × Finset ℕ)) (cc : ℕ)
    (hc : Runs Δ' B fChainsGo [toVal cands, toVal f, toVal X, toVal (chain ++ [X])] (toVal res) cc) (hB : 0 < B) :
    Runs Δ' B fGoStep [toVal (cands, f, chain), toVal X] (toVal res) (cc + 10 * chain.length + 30) := by
  have h1 := append_runs (y1 hΔ) B chain [X]
  simp only [toVal_cons, toVal_nil] at h1
  refine Runs.mk (hΔ _ _ Δ_goStep) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem chainsGo_runs (U Qc : ℕ) (cands : List (Finset ℕ)) (hcands : ∀ X ∈ cands, X.card ≤ U)
    (hQc : 1000 * ((U + 1) * (cands.length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    ∀ (fuel : ℕ) (bound : Finset ℕ) (chain : List (Finset ℕ)), bound.card ≤ U → chain.length + fuel ≤ U →
      Runs Δ' B fChainsGo [toVal cands, toVal fuel, toVal bound, toVal chain]
        (toVal (chainsGo cands fuel bound chain))
        (Qc * (fuel + 1) * (2 * (chainsGo cands fuel bound chain).length + 1)) := by
  have hid := ids_lt (B := B) (by omega)
  have hid' := E3A.ids_lt (B := B) (by omega)
  have arithN : cands.length * (120 * U + 30) + cands.length * (240 * U + 60) + 48 * cands.length + 200
      ≤ 1000 * ((U + 1) * (cands.length + 1)) := by nlinarith
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain hb hf
    have hfil := filter_runs (y1 hΔ) B fSubOf (toVal bound) (fun X : Finset ℕ => decide (X ⊆ bound))
      (fun X => 60 * (X.card + bound.card) + 30) cands
      (fun X _ => subOf_runs hΔ B bound X _ (by simp) (by omega))
    have hsum := sum_map_le (fun X : Finset ℕ => 60 * (X.card + bound.card) + 30) (120 * U + 30) cands
      (fun X hX => by have := hcands X hX; omega)
    have hmap := map_runs (y1 hΔ) B fPairCh (toVal chain) (fun M : Finset ℕ => (chain, M))
      (fun _ => 3) (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound)))
      (fun M _ => pairCh_runs hΔ B chain M)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hshow : chainsGo cands 0 bound chain =
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_chainsGo) ?_
    simp only [List.length_map] 
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_run
    · set m := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length with hm
      have e : Qc * (0 + 1) * (2 * m + 1) = 2 * (Qc * m) + Qc := by ring
      have hq : 23 ≤ Qc := by nlinarith
      have hqm : 23 * m ≤ Qc * m := Nat.mul_le_mul_right _ hq
      omega
  | succ f ih =>
    intro bound chain hb hf
    have hfil := filter_runs (y1 hΔ) B fSubOf (toVal bound) (fun X : Finset ℕ => decide (X ⊆ bound))
      (fun X => 60 * (X.card + bound.card) + 30) cands
      (fun X _ => subOf_runs hΔ B bound X _ (by simp) (by omega))
    have hsum := sum_map_le (fun X : Finset ℕ => 60 * (X.card + bound.card) + 30) (120 * U + 30) cands
      (fun X hX => by have := hcands X hX; omega)
    have hmap := map_runs (y1 hΔ) B fPairCh (toVal chain) (fun M : Finset ℕ => (chain, M))
      (fun _ => 3) (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound)))
      (fun M _ => pairCh_runs hΔ B chain M)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hsel := filter_runs (y1 hΔ) B fSel (toVal (bound, chain))
      (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))
      (fun X => 120 * (X.card + bound.card) + 60) cands
      (fun X _ => sel_runs hΔ B bound X chain (by omega))
    have hsum2 := sum_map_le (fun X : Finset ℕ => 120 * (X.card + bound.card) + 60) (240 * U + 60) cands
      (fun X hX => by have := hcands X hX; omega)
    have hlen12 : (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).length ≤
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length :=
      filter_len_le_of_imp _ _ cands (fun X _ h => by simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1)
    have hgo : ∀ X ∈ cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))),
        Runs Δ' B fGoStep [toVal (cands, f, chain), toVal X] (toVal (chainsGo cands f X (chain ++ [X])))
          (2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30)) := by
      intro X hX
      have hXc : X ∈ cands := (List.mem_filter.1 hX).1
      have hch := ih X (chain ++ [X]) (hcands X hXc) (by simp only [List.length_append, List.length_singleton]; omega)
      have h3 := goStep_runs hΔ B cands f chain X _ _ hch (by omega)
      refine h3.mono ?_
      have e : Qc * (f + 1) * (2 * (chainsGo cands f X (chain ++ [X])).length + 1) =
          2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + Qc * (f + 1) := by ring
      omega
    have hfm := flatMap_runs (y1 hΔ) B fGoStep (toVal (cands, f, chain))
      (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
      (fun X => 2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30))
      (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))) hgo
    have hsm := sum_affine_le (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
      (fun X => 2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length + (Qc * (f + 1) + 10 * U + 30))
      (2 * (Qc * (f + 1)) + 10) (Qc * (f + 1) + 10 * U + 50)
      (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))
      (fun X _ => by
        have e : (2 * (Qc * (f + 1)) + 10) * (chainsGo cands f X (chain ++ [X])).length =
            2 * (Qc * (f + 1)) * (chainsGo cands f X (chain ++ [X])).length +
              10 * (chainsGo cands f X (chain ++ [X])).length := by ring
        omega)
    have happ := append_runs (y1 hΔ) B
      ((cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)))
      ((cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
        (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X])))
    have hshow : chainsGo cands (f + 1) bound chain =
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).map (fun M : Finset ℕ => (chain, M)) ++
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).flatMap
          (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X])) := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_chainsGo) ?_
    simp only [toVal_pair] at hsel hfm
    ev_start
    · apply EvLe.letE
      · ev_run
      · ev_run
    · simp only [List.length_append, List.length_map] at hsm ⊢
      set n := cands.length with hn
      set m := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound))).length with hm
      set m2 := (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound)))).length with hm2
      set SL := (List.flatMap (fun X : Finset ℕ => chainsGo cands f X (chain ++ [X]))
        (cands.filter (fun X : Finset ℕ => decide (X ⊆ bound) && (chain.isEmpty || decide (X ⊂ bound))))).length with hSL
      set W := Qc * (f + 1) with hW
      have hW2 : Qc * (f + 1 + 1) = W + Qc := by rw [hW]; ring
      have eR : (W + Qc) * (2 * (m + SL) + 1) = 2 * (W * m) + 2 * (W * SL) + W + 2 * (Qc * m) + 2 * (Qc * SL) + Qc := by ring
      have eA : (2 * W + 10) * SL = 2 * (W * SL) + 10 * SL := by ring
      have eB : (W + 10 * U + 50) * m2 = W * m2 + (10 * U + 50) * m2 := by ring
      have f1 : W * m2 ≤ W * m := Nat.mul_le_mul_left _ hlen12
      have f2 : (10 * U + 50) * m2 ≤ (10 * U + 50) * m := Nat.mul_le_mul_left _ hlen12
      have hq1 : 10 * U + 83 ≤ Qc := by nlinarith
      have hqm : (10 * U + 83) * m ≤ Qc * m := Nat.mul_le_mul_right _ hq1
      have hqs : 10 * SL ≤ Qc * SL := Nat.mul_le_mul_right _ (by omega)
      have hqm2 : (10 * U + 83) * m = (10 * U + 50) * m + 33 * m := by ring
      rw [hW2, eR]
      omega

theorem allChains_runs (U Qc : ℕ) (S N : Finset ℕ) (hNS : N ⊆ S) (hS : S.card + 1 ≤ U)
    (hQc : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAllChains [toVal S, toVal N] (toVal (allChains S N))
      (Qc * (U + 1) * (2 * (allChains S N).length + 2)) := by
  have hid := ids_lt (B := B) (by omega)
  have hcc := chainCands_runs hΔ B U S N (by omega) (le_trans (Finset.card_le_card hNS) (by omega)) hB
  have hlen := Lib4.card_runs (y4 hΔ) B S (by omega)
  have hgo := (chainsGo_runs hΔ B U Qc (chainCands S N)
    (fun X hX => le_trans (Finset.card_le_card (mem_chainCands_sub hNS hX)) (by omega)) hQc hB
    (S.card + 1) S [] (by omega) (by simp; omega)).mono (show Qc * (S.card + 1 + 1) * (2 * (chainsGo (chainCands S N) (S.card + 1) S []).length + 1) ≤
      Qc * (U + 1) * (2 * (chainsGo (chainCands S N) (S.card + 1) S []).length + 1) from
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
  have hshow : allChains S N = chainsGo (chainCands S N) (S.card + 1) S [] := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_allChains) ?_
  ev_start
  · ev_run
  · set L := (chainsGo (chainCands S N) (S.card + 1) S []).length with hL
    set n := (chainCands S N).length with hn
    have e : Qc * (U + 1) * (2 * L + 2) = Qc * (U + 1) * (2 * L + 1) + Qc * (U + 1) := by ring
    have e2 : 500 * ((U + 1) * (U + 1)) * n + 8 * S.card + 100 ≤ Qc * (U + 1) := by nlinarith
    omega

theorem pathStep_runs (U : ℕ) (X : Finset ℕ) (acc : CT) (hX : X.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPathStep [Val.nat 0, toVal X, toVal acc] (toVal (CT.node X [X.card] [acc])) (8 * U + 30) := by
  have h1 := Lib4.card_runs (y4 hΔ) B X (by omega)
  refine Runs.mk (hΔ _ _ Δ_pathStep) ?_
  simp only [toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem pathSubtree_runs (U v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (hch : ∀ X ∈ chain, X.card ≤ U)
    (hlen : chain.length ≤ U) (hM : M.card ≤ U) (hv : v ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fPathSubtree [toVal v, toVal chain, toVal M] (toVal (pathSubtree v chain M))
      (300 * ((U + 1) * (U + 1))) := by
  have hid := ids_lt (B := B) (by omega)
  have h1 := Lib3.insert_runs (y3 hΔ) B v M
  have h2 := Lib4.card_runs (y4 hΔ) B M (by omega)
  have hfold := Lib2.foldr_runs (y2 hΔ) B fPathStep (Val.nat 0)
    (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc])
    (fun (X : Finset ℕ) (acc : CT) => 8 * U + 30) (fun _ => True)
    (CT.node (insert v M) [M.card + 1] []) chain trivial (fun _ _ _ _ => trivial)
    (fun X acc hX _ => pathStep_runs hΔ B U X acc (hch X hX) hB)
  have hfc := foldrCost_le (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc])
    (fun (X : Finset ℕ) (acc : CT) => 8 * U + 30) (fun _ => True) (CT.node (insert v M) [M.card + 1] [])
    (8 * U + 30) trivial chain (fun _ _ _ _ => trivial) (fun _ _ _ _ => le_rfl)
  have hshow : pathSubtree v chain M =
      chain.foldr (fun (X : Finset ℕ) (acc : CT) => CT.node X [X.card] [acc]) (CT.node (insert v M) [M.card + 1] []) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_pathSubtree) ?_
  simp only [toVal_ct, toVal_cons, toVal_nil] at hfold ⊢
  ev_start
  · ev_run
  · have e1 : chain.length * (8 * U + 30) ≤ U * (8 * U + 30) := Nat.mul_le_mul_right _ hlen
    have e2 : U * (8 * U + 30) + 100 * U + 300 ≤ 300 * ((U + 1) * (U + 1)) := by nlinarith
    omega

theorem attIn1_runs (U f : ℕ) (br : CT) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttIn1 [toVal (br, (chain, M), CT.node S y ks), toVal f]
      (toVal (((CT.Plan.att (some (CT.Cut.t1 f)) chain M, CT.node S (y.take (f + 1)) [br, CT.node S (y.drop f) ks]) :
        CT.Plan × CT))) (100 * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 := drop_runs (y1 hΔ) B f y (by omega)
  have h3 : min (f + 1) y.length ≤ U := by omega
  have h4 : min f y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_attIn1) ?_
  simp only [toVal_pair, toVal_plan_att, toVal_some, toVal_cut_t1, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem attIn2_runs (U f : ℕ) (br : CT) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ)
    (ks : List CT) (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hf : f ≤ U)
    (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttIn2 [toVal (br, (chain, M), CT.node S y ks), toVal f]
      (toVal (((CT.Plan.att (some (CT.Cut.t2 f)) chain M, CT.node S (y.take (f + 1)) [br, CT.node S (y.drop (f + 1)) ks]) :
        CT.Plan × CT))) (100 * (U + 1)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have h1 := take_runs (y1 hΔ) B (f + 1) y (by omega)
  have h2 := drop_runs (y1 hΔ) B (f + 1) y (by omega)
  have h3 : min (f + 1) y.length ≤ U := by omega
  refine Runs.mk (hΔ _ _ Δ_attIn2) ?_
  simp only [toVal_pair, toVal_plan_att, toVal_some, toVal_cut_t2, toVal_ct, toVal_cons, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem att_runs (U v : ℕ) (chain : List (Finset ℕ)) (M : Finset ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hch : ∀ X ∈ chain, X.card ≤ U) (hlen : chain.length ≤ U) (hMc : M.card ≤ U) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAtt [toVal (v, CT.node S y ks), toVal (chain, M)]
      (toVal (((CT.Plan.att none chain M, CT.node S y (ks ++ [pathSubtree v chain M])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))))
      (800 * ((U + 1) * (U + 1))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hid := ids_lt (B := B) (by omega)
  have hbr := pathSubtree_runs hΔ B U v chain M hch hlen hMc hv hB
  have hks : ks.length ≤ U := le_trans (length_le_sz ks) (by omega)
  have hlenr := length_runs (y1 hΔ) B y (by omega)
  have hr1 := range_runs (y1 hΔ) B y.length (by omega)
  have hr2 := range_runs (y1 hΔ) B (y.length - 1) (by omega)
  have hm1 := map_runs (y1 hΔ) B fAttIn1 (toVal (pathSubtree v chain M, (chain, M), CT.node S y ks))
    (fun f : ℕ => ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT))
    (fun _ => 100 * (U + 1)) (List.range y.length)
    (fun f hf => attIn1_runs hΔ B U f _ chain M S y ks hU hM (by rw [List.mem_range] at hf; omega) hB)
  have hm2 := map_runs (y1 hΔ) B fAttIn2 (toVal (pathSubtree v chain M, (chain, M), CT.node S y ks))
    (fun f : ℕ => ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))
    (fun _ => 100 * (U + 1)) (List.range (y.length - 1))
    (fun f hf => attIn2_runs hΔ B U f _ chain M S y ks hU hM (by rw [List.mem_range] at hf; omega) hB)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_range] at hm1 hm2
  have hap1 := append_runs (y1 hΔ) B ks [pathSubtree v chain M]
  have hap2 := append_runs (y1 hΔ) B
    ((CT.Plan.att none chain M, CT.node S y (ks ++ [pathSubtree v chain M])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop f) ks]) : CT.Plan × CT)))
    ((List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) chain M,
            CT.node S (y.take (f + 1)) [pathSubtree v chain M, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT)))
  simp only [toVal_cons, toVal_nil] at hap1
  refine Runs.mk (hΔ _ _ Δ_att) ?_
  simp only [toVal_pair, toVal_ct, toVal_plan_att, toVal_none, toVal_cons, toVal_nil] at hm1 hm2 hap2 ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_run
  · simp only [List.length_cons, List.length_map, List.length_range]
    have e1 : y.length * (100 * (U + 1)) ≤ U * (100 * (U + 1)) := Nat.mul_le_mul_right _ hc2
    have e2 : (y.length - 1) * (100 * (U + 1)) ≤ U * (100 * (U + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e3 : U * (100 * (U + 1)) + U * (100 * (U + 1)) + 300 * ((U + 1) * (U + 1)) + 200 * U + 300 ≤ 800 * ((U + 1) * (U + 1)) := by nlinarith
    clear hm1 hm2 hap1 hap2 hbr hlenr hr1 hr2 hid
    have hs1 : y.length - 1 ≤ y.length := Nat.sub_le _ _
    have hks10 : 10 * ks.length ≤ 10 * U := by omega
    have hs : 24 * (y.length - 1) ≤ 24 * y.length := by omega
    linarith

theorem attachPlans_runs (U Qc v : ℕ) (N S : Finset ℕ) (y : List ℕ) (ks : List CT) (hNS : N ⊆ S)
    (hU : sz (CT.node S y ks) ≤ U) (hM : mx (CT.node S y ks) ≤ U) (hv : v ≤ U)
    (hQc : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc) (hB : 10 * U + 400 < B) :
    Runs Δ' B fAttachPlans [toVal v, toVal N, toVal (CT.node S y ks)] (toVal (attachPlans v N (CT.node S y ks)))
      (2 * (Qc * (U + 1) * (2 * (allChains S N).length + 2))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
  have hU5 : 5 ≤ U := by
    have := sz_pos ks; have := sz_pos y; have := sz_pos S
    rw [sz_ct_node] at hU; omega
  have hS : S.card + 1 ≤ U := by have := sz_finset S; omega
  have hid := ids_lt (B := B) (by omega)
  have hac := allChains_runs hΔ B U Qc S N hNS hS hQc hB
  have hatt := flatMap_runs (y1 hΔ) B fAtt (toVal (v, CT.node S y ks))
    (fun cm : List (Finset ℕ) × Finset ℕ =>
      ((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT)))
    (fun _ => 800 * ((U + 1) * (U + 1))) (allChains S N)
    (fun cm hcm => by
      obtain ⟨chain, M⟩ := cm
      obtain ⟨h1, h2⟩ := allChains_sub S N _ hcm
      have h3 := allChains_chain_length_le S N _ hcm
      exact att_runs hΔ B U v chain M S y ks hU hM hv
        (fun X hX => le_trans (Finset.card_le_card (h2 X hX)) (by omega)) (by simp only at h3; omega)
        (le_trans (Finset.card_le_card h1) (by omega)) hB)
  have hsum := sum_map_le
    (fun cm : List (Finset ℕ) × Finset ℕ => 800 * ((U + 1) * (U + 1)) + 10 *
      (((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))).length + 20)
    (900 * ((U + 1) * (U + 1))) (allChains S N)
    (fun cm _ => by
      simp only [List.length_append, List.length_cons, List.length_map, List.length_range]
      have : U ≤ (U + 1) * (U + 1) := by nlinarith
      omega)
  have hshow : attachPlans v N (CT.node S y ks) = (allChains S N).flatMap
    (fun cm : List (Finset ℕ) × Finset ℕ =>
      ((CT.Plan.att none cm.1 cm.2, CT.node S y (ks ++ [pathSubtree v cm.1 cm.2])) ::
        (List.range y.length).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t1 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop f) ks]) : CT.Plan × CT))) ++
        (List.range (y.length - 1)).map (fun f : ℕ =>
          ((CT.Plan.att (some (CT.Cut.t2 f)) cm.1 cm.2,
            CT.node S (y.take (f + 1)) [pathSubtree v cm.1 cm.2, CT.node S (y.drop (f + 1)) ks]) : CT.Plan × CT))) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_attachPlans) ?_
  simp only [toVal_pair, toVal_ct] at hatt ⊢
  ev_start
  · apply EvLe.letE
    · ev_run
    · ev_run
  · set A := (allChains S N).length with hA
    have e : Qc * (U + 1) * (2 * A + 2) ≥ 2000 * ((U + 1) * (U + 1)) * (A + 1) := by
      have h1 : 1000 * (U + 1) ≤ Qc := by nlinarith
      have h2 : 1000 * (U + 1) * (U + 1) ≤ Qc * (U + 1) := Nat.mul_le_mul_right _ h1
      nlinarith
    have e2 : A * (900 * ((U + 1) * (U + 1))) + 100 ≤ 2000 * ((U + 1) * (U + 1)) * (A + 1) := by nlinarith
    omega

end proofs
end E3B
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3MathC` -/

section
/-!
# WP E3: facts about `wtopPlans` used by the cost analysis of `introPlans`
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- every vertex set in the output of `wtopPlans` lies in `verts` -/
theorem wtopPlans_sub (v : ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    ∀ x ∈ wtopPlans v (node S y ks), x.2.2 ⊆ (node S y ks).verts := by
  intro x hx
  simp only [wtopPlans, List.mem_append, List.mem_map, List.mem_flatMap] at hx
  rcases hx with (⟨p, hp, rfl⟩ | ⟨f, _, p, hp, rfl⟩) | ⟨f, _, p, hp, rfl⟩
  · exact winPlans_sub v 0 _ p hp
  · exact winPlans_sub v f _ p hp
  · exact winPlans_sub v (f + 1) _ p hp

end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3C1` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem xB : E3B.Δ ⊑ Δ' := Ext.trans extB hΔ
theorem xA : E3A.Δ ⊑ Δ' := Ext.trans E3B.extA (xB hΔ)
theorem y1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans E3A.extLib (xA hΔ))
theorem y3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans E3A.extLib (xA hΔ))

theorem subN_runs (N : Finset ℕ) (pl : CT.Plan) (c : CT) (s : Finset ℕ) (hB : 1 < B) :
    Runs Δ' B fSubN [toVal N, toVal (pl, c, s)] (toVal (decide (N ⊆ s)))
      (60 * (N.card + s.card) + 30) := by
  have h1 := Lib3.subset_runs (y3 hΔ) B hB N s (decide (N ⊆ s)) (by simp)
  refine Runs.mk (hΔ _ _ Δ_subN) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem mk1_runs (pl : CT.Plan) (c : CT) (s : Finset ℕ) (hB : 0 < B) :
    Runs Δ' B fMk1 [Val.nat 0, toVal (pl, c, s)] (toVal ((([] : List ℕ), pl, c) : List ℕ × CT.Plan × CT)) 8 := by
  refine Runs.mk (hΔ _ _ Δ_mk1) ?_
  simp only [toVal_pair, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem mk2_runs (pl : CT.Plan) (c : CT) (hB : 0 < B) :
    Runs Δ' B fMk2 [Val.nat 0, toVal (pl, c)] (toVal ((([] : List ℕ), pl, c) : List ℕ × CT.Plan × CT)) 7 := by
  refine Runs.mk (hΔ _ _ Δ_mk2) ?_
  simp only [toVal_pair, toVal_nil]
  ev_start
  · ev_run
  · omega

theorem kid_runs (S : Finset ℕ) (y : List ℕ) (pre post : List CT) (path : List ℕ) (pl : CT.Plan) (c : CT) :
    Runs Δ' B fKid [toVal (pre.length, S, y, pre, post), toVal (path, pl, c)]
      (toVal (((pre.length :: path, pl, CT.node S y (pre ++ c :: post)) : List ℕ × CT.Plan × CT)))
      (10 * pre.length + 40) := by
  have h1 := append_runs (y1 hΔ) B pre (c :: post)
  simp only [toVal_cons] at h1
  refine Runs.mk (hΔ _ _ Δ_kid) ?_
  simp only [toVal_pair, toVal_cons, toVal_ct]
  ev_start
  · ev_run
  · omega

/-! ### `maxEntry` -/

theorem maxL_runs (l : List ℕ) (hB : 0 < B) :
    Runs Δ' B fMaxL [toVal l] (toVal (l.foldr max 0)) (20 * l.length + 6) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_maxL) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have h1 := max_runs (y1 hΔ) B a (l.foldr max 0)
    refine Runs.mk (hΔ _ _ Δ_maxL) ?_
    simp only [List.foldr_cons]
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem maxEntryL_runs (hB : 0 < B) : ∀ (ks : List CT),
    (∀ k ∈ ks, Runs Δ' B fMaxEntry [toVal k] (toVal k.maxEntry) (40 * sz k)) →
    Runs Δ' B fMaxEntryL [toVal ks] (toVal (maxEntryL ks)) (40 * sz ks)
  | [], _ => by
    refine Runs.mk (hΔ _ _ Δ_maxEntryL) ?_
    simp only [maxEntryL]
    ev_start
    · ev_run
    · simp
  | k :: ks, h => by
    have h1 := h k (List.mem_cons_self ..)
    have h2 := maxEntryL_runs hB ks (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    have h3 := max_runs (y1 hΔ) B k.maxEntry (maxEntryL ks)
    refine Runs.mk (hΔ _ _ Δ_maxEntryL) ?_
    simp only [maxEntryL, toVal_cons]
    ev_start
    · ev_run
    · rw [sz_cons]; omega

theorem maxEntry_runs (hB : 0 < B) : ∀ (c : CT), Runs Δ' B fMaxEntry [toVal c] (toVal c.maxEntry) (40 * sz c) := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    have h1 := maxL_runs hΔ B y hB
    have h2 := maxEntryL_runs hΔ B hB ks ih
    have h3 := max_runs (y1 hΔ) B (y.foldr max 0) (maxEntryL ks)
    refine Runs.mk (hΔ _ _ Δ_maxEntry) ?_
    simp only [maxEntry, toVal_ct]
    ev_start
    · ev_run
    · rw [sz_ct_node, sz_list_nat y]; omega

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3C2` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem introPlans_runs_rec (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B) :
    ∀ (t : CT), sz t ≤ U → mx t ≤ U → Good Bs t → maxEntry t ≤ kmax → count t ≤ M →
      Runs Δ' B fIntroPlans [toVal v, toVal N, toVal t] (toVal (introPlans v N t)) (Q₀ * (3 * count t - 1))
  | CT.node S y ks, hU, hM, hg, hm, hc => by
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩ := ct_node_facts hU hM
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    have hid' := E3B.ids_lt (B := B) (by omega)
    have hid'' := E3A.ids_lt (B := B) (by omega)
    obtain ⟨hgk, hmk⟩ := kids_good hg hm
    have hcnt : count (CT.node S y ks) = 1 + countL ks := rfl
    have hG' := hG (CT.node S y ks) hg hm hc
    have hΩ' : (chainCands S N).length + 1 ≤ Ω := hΩ _ hg
    have hkids : ∀ k ∈ ks, sz k ≤ U ∧ mx k ≤ U ∧ Good Bs k ∧ maxEntry k ≤ kmax ∧ count k ≤ M :=
      fun k hk => ⟨le_trans (sz_le_of_mem hk) (by omega), le_trans (mx_le_of_mem hk) (by omega), hgk k hk, hmk k hk,
        le_trans (count_le_countL_of_mem hk) (by omega)⟩
    have hrec := introKids_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB ks [] S y hkids
      (by simp only [List.length_nil, Nat.zero_add]; exact le_trans (length_le_sz ks) (by omega))
    have hPt : Q * (3 * count (CT.node S y ks) - 1) ≤ P :=
      le_trans (Nat.mul_le_mul_left _ (by omega)) hP
    have hwt := E3B.wtopPlans_runs (xB hΔ) B U Q hQ P v S y ks hU hM hv (by omega) hPt
    have hfil := filter_runs (y1 hΔ) B fSubN (toVal N)
      (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))
      (fun p => 60 * (N.card + p.2.2.card) + 30) (wtopPlans v (CT.node S y ks))
      (fun p _ => by obtain ⟨pl, c, s⟩ := p; exact subN_runs hΔ B N pl c s (by omega))
    have hsum := sum_map_le (fun p : CT.Plan × CT × Finset ℕ => 60 * (N.card + p.2.2.card) + 30) (120 * U + 30)
      (wtopPlans v (CT.node S y ks))
      (fun p hp => by
        have h1 := Finset.card_le_card (wtopPlans_sub v S y ks p hp)
        have h2 := card_verts_le_sz (CT.node S y ks)
        show 60 * (N.card + p.2.2.card) + 30 ≤ 120 * U + 30
        omega)
    have hmap1 := map_runs (y1 hΔ) B fMk1 (Val.nat 0)
      (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) (fun _ => 8)
      ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2)))
      (fun p _ => by obtain ⟨pl, c, s⟩ := p; exact mk1_runs hΔ B pl c s (by omega))
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap1
    have hlenF : ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).length ≤
        (wtopPlans v (CT.node S y ks)).length := List.length_filter_le _ _
    have hsubS := Lib3.subset_runs (y3 hΔ) B (by omega) N S (decide (N ⊆ S)) (by simp)
    have hshow : introPlans v N (CT.node S y ks) =
        ((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++
        (if N ⊆ S then (attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)) else []) ++
        introKids v N S y [] ks := rfl
    by_cases hNS : N ⊆ S
    · have hQc' : 1000 * ((U + 1) * ((chainCands S N).length + 1)) ≤ Qc :=
        le_trans (Nat.mul_le_mul_left 1000 (Nat.mul_le_mul_left _ hΩ')) hQc
      have hatt := E3B.attachPlans_runs (xB hΔ) B U Qc v N S y ks hNS hU hM hv hQc' (by omega)
      have hmap2 := map_runs (y1 hΔ) B fMk2 (Val.nat 0)
        (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)) (fun _ => 7)
        (attachPlans v N (CT.node S y ks))
        (fun p _ => by obtain ⟨pl, c⟩ := p; exact mk2_runs hΔ B pl c (by omega))
      simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap2
      have ha1 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)))
        ((attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)))
      have ha2 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++
        (attachPlans v N (CT.node S y ks)).map
          (fun p : CT.Plan × CT => ((([] : List ℕ), p.1, p.2) : List ℕ × CT.Plan × CT)))
        (introKids v N S y [] ks)
      rw [hshow, if_pos hNS]
      refine Runs.mk (hΔ _ _ Δ_introPlans) ?_
      simp only [hNS, decide_true] at hsubS
      simp only [toVal_ct, toVal_nil] at hrec hwt hatt ⊢
      ev_start
      · ev_run
      · simp only [List.length_append, List.length_map]
        obtain ⟨hG1, hG2, hG3, hG4⟩ := hG'
        have hLw : (wtopPlans v (CT.node S y ks)).length ≤ G := by omega
        have e1 : P * ((wtopPlans v (CT.node S y ks)).length + 1) ≤ P * G := Nat.mul_le_mul_left _ hG1
        have e2 : (wtopPlans v (CT.node S y ks)).length * (120 * U + 30) ≤ G * (120 * U + 30) :=
          Nat.mul_le_mul_right _ hLw
        have e2' : G * (120 * U + 30) = 120 * (U * G) + 30 * G := by ring
        have e3 : Qc * (U + 1) * (2 * (allChains S N).length + 2) ≤ Qc * (U + 1) * (2 * G) :=
          Nat.mul_le_mul_left _ (by simp only [CT.S] at hG2; omega)
        have e3' : Qc * (U + 1) * (2 * G) = 2 * (Qc * (U + 1) * G) := by ring
        have e4 : (U + 1) * G = U * G + G := by ring
        have e5 : Q₀ * (3 * count (CT.node S y ks) - 1) = Q₀ * (3 * countL ks + 1) + Q₀ := by
          rw [hcnt]; have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
          rw [this]; ring
        have e6 := le_trans hlenF hLw
        rw [e5]
        clear hG hΩ hkids hgk hmk hwt hfil hmap1 hatt hmap2 ha1 ha2 hrec hsubS hshow hid hid' hid''
        omega
    · have ha1 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)))
        ([] : List (List ℕ × CT.Plan × CT))
      have ha2 := append_runs (y1 hΔ) B
        (((wtopPlans v (CT.node S y ks)).filter (fun p : CT.Plan × CT × Finset ℕ => decide (N ⊆ p.2.2))).map
          (fun p : CT.Plan × CT × Finset ℕ => ((([] : List ℕ), p.1, p.2.1) : List ℕ × CT.Plan × CT)) ++ [])
        (introKids v N S y [] ks)
      rw [hshow, if_neg hNS]
      refine Runs.mk (hΔ _ _ Δ_introPlans) ?_
      simp only [hNS, decide_false] at hsubS
      simp only [toVal_ct, toVal_nil] at hrec hwt ha1 ha2 ⊢
      ev_start
      · ev_run
      · simp only [List.length_append, List.length_map, List.length_nil]
        obtain ⟨hG1, hG2, hG3, hG4⟩ := hG'
        have hLw : (wtopPlans v (CT.node S y ks)).length ≤ G := by omega
        have e1 : P * ((wtopPlans v (CT.node S y ks)).length + 1) ≤ P * G := Nat.mul_le_mul_left _ hG1
        have e2 : (wtopPlans v (CT.node S y ks)).length * (120 * U + 30) ≤ G * (120 * U + 30) :=
          Nat.mul_le_mul_right _ hLw
        have e2' : G * (120 * U + 30) = 120 * (U * G) + 30 * G := by ring
        have e4 : (U + 1) * G = U * G + G := by ring
        have e5 : Q₀ * (3 * count (CT.node S y ks) - 1) = Q₀ * (3 * countL ks + 1) + Q₀ := by
          rw [hcnt]; have : 3 * (1 + countL ks) - 1 = (3 * countL ks + 1) + 1 := by omega
          rw [this]; ring
        have e6 := le_trans hlenF hLw
        rw [e5]
        clear hG hΩ hkids hgk hmk hwt hfil hmap1 ha1 ha2 hrec hsubS hshow hid hid' hid''
        omega
theorem introKids_runs_rec (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B) :
    ∀ (ks pre : List CT) (S : Finset ℕ) (y : List ℕ),
      (∀ k ∈ ks, sz k ≤ U ∧ mx k ≤ U ∧ Good Bs k ∧ maxEntry k ≤ kmax ∧ count k ≤ M) → pre.length + ks.length ≤ U →
      Runs Δ' B fIntroKids [toVal v, toVal N, toVal S, toVal y, toVal pre, toVal ks]
        (toVal (introKids v N S y pre ks)) (Q₀ * (3 * countL ks + 1))
  | [], pre, S, y, hks, hpre => by
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    refine Runs.mk (hΔ _ _ Δ_introKids) ?_
    simp only [introKids]
    ev_start
    · ev_run
    · simp [countL]; omega
  | k :: post, pre, S, y, hks, hpre => by
    have hu1 : 1000 ≤ 1000 * (U + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos U)
    have hQ₀1 : 1000 ≤ Q₀ := le_trans hu1 (le_trans (Nat.le_add_left _ _) hQ₀)
    have hid := ids_lt (B := B) (by omega)
    obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hks k (List.mem_cons_self ..)
    have hks' : ∀ k' ∈ post, sz k' ≤ U ∧ mx k' ≤ U ∧ Good Bs k' ∧ maxEntry k' ≤ kmax ∧ count k' ≤ M :=
      fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')
    have hip := introPlans_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB k hk1 hk2 hk3 hk4 hk5
    have hrec := introKids_runs_rec U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB post (pre ++ [k]) S y hks'
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hpre ⊢; omega)
    have hlen := length_runs (y1 hΔ) B pre (by simp only [List.length_cons, List.length_nil] at hpre; omega)
    have hOG := (hG k hk3 hk4 hk5).2.2.2
    have hmap := map_runs (y1 hΔ) B fKid (toVal (pre.length, S, y, pre, post))
      (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT))
      (fun _ => 10 * pre.length + 40) (introPlans v N k)
      (fun r _ => by obtain ⟨path, pl, c⟩ := r; exact kid_runs hΔ B S y pre post path pl c)
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
    have hap1 := append_runs (y1 hΔ) B pre [k]
    simp only [toVal_cons, toVal_nil] at hap1
    have hap2 := append_runs (y1 hΔ) B
      ((introPlans v N k).map (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT)))
      (introKids v N S y (pre ++ [k]) post)
    have hshow : introKids v N S y pre (k :: post) =
        (introPlans v N k).map (fun r : List ℕ × CT.Plan × CT => ((pre.length :: r.1, r.2.1, CT.node S y (pre ++ r.2.2 :: post)) : List ℕ × CT.Plan × CT)) ++
        introKids v N S y (pre ++ [k]) post := rfl
    rw [hshow]
    refine Runs.mk (hΔ _ _ Δ_introKids) ?_
    simp only [toVal_cons, toVal_pair] at hmap ⊢
    ev_start
    · ev_run
    · simp only [List.length_map]
      have hcnt := count_pos k
      have hpl : pre.length ≤ U := by simp only [List.length_cons] at hpre; omega
      have e1 : (introPlans v N k).length * (10 * pre.length + 40) ≤ G * (10 * U + 40) :=
        Nat.mul_le_mul hOG (by omega)
      have e2 : G * (10 * U + 40) = 10 * (U * G) + 40 * G := by ring
      have e3 : (U + 1) * G = U * G + G := by ring
      have e4 : Q₀ * (3 * countL (k :: post) + 1) =
          Q₀ * (3 * count k - 1) + Q₀ * (3 * countL post + 1) + Q₀ := by
        have : 3 * countL (k :: post) + 1 = (3 * count k - 1) + (3 * countL post + 1) + 1 := by
          simp only [countL]; omega
        rw [this]; ring
      have e5 : 100 * (P * G) + 4 * (Qc * (U + 1) * G) ≥ 0 := Nat.zero_le _
      rw [e4]
      clear hG hΩ hks hks'
      omega
end

end proofs

theorem introPlans_runs_pair : (type_of% @introPlans_runs_rec) ∧ (type_of% @introKids_runs_rec) :=
  ⟨@introPlans_runs_rec, @introKids_runs_rec⟩

theorem introPlans_runs : type_of% @introPlans_runs_rec := introPlans_runs_pair.1

end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3C3` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars CT

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem leKC_runs (kmax : ℕ) (c : CT) (hB : 1 < B) (s : ℕ) (hs : sz c ≤ s) :
    Runs Δ' B fLeKC [toVal kmax, toVal c] (toVal (decide (c.maxEntry ≤ kmax))) (40 * s + 10) := by
  have h1 := maxEntry_runs hΔ B (by omega) c
  refine Runs.mk (hΔ _ _ Δ_leKC) ?_
  by_cases hk : c.maxEntry ≤ kmax
  · have : ¬ kmax < c.maxEntry := by omega
    simp only [hk, decide_true, toVal_true]
    ev_start
    · ev_run
    · omega
  · have : kmax < c.maxEntry := by omega
    simp only [hk, decide_false, toVal_false]
    ev_start
    · ev_run
    · omega

theorem normOf_runs (path : List ℕ) (pl : CT.Plan) (c : CT) (Cn : ℕ)
    (hnorm : Runs Δ' B fNormId [toVal c] (toVal (norm c)) Cn) :
    Runs Δ' B fNormOf [Val.nat 0, toVal (path, pl, c)] (toVal (norm c)) (Cn + 6) := by
  refine Runs.mk (hΔ _ _ Δ_normOf) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem introC_runs (U Q P G Ω Qc Q₀ Cn Sn : ℕ) (Bs : Finset ℕ) (kmax M v : ℕ) (N : Finset ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P)
    (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hv : v ≤ U) (hN : N.card ≤ U)
    (hG : ∀ ν : CT, Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ ν : CT, Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω) (hB : 10 * U + 600 < B)
    (t : CT) (hU : sz t ≤ U) (hM : mx t ≤ U) (hg : Good Bs t) (hm : maxEntry t ≤ kmax) (hc : count t ≤ M)
    (hnorm : ∀ x ∈ introPlans v N t, Runs Δ' B fNormId [toVal x.2.2] (toVal (norm x.2.2)) Cn)
    (hsz : ∀ x ∈ introPlans v N t, sz (norm x.2.2) ≤ Sn) :
    Runs Δ' B fIntroC [toVal kmax, toVal v, toVal N, toVal t] (toVal (introC kmax v N t))
      (Q₀ * (3 * count t - 1) + (G * (Cn + 40 * Sn + 80) + 100)) := by
  have hid := ids_lt (B := B) (by omega)
  have hip := introPlans_runs hΔ B U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN hG hΩ hB t hU hM hg hm hc
  have hOG := (hG t hg hm hc).2.2.2
  have hmap := map_runs (y1 hΔ) B fNormOf (Val.nat 0) (fun r : List ℕ × CT.Plan × CT => norm r.2.2)
    (fun _ => Cn + 6) (introPlans v N t)
    (fun r hr => by obtain ⟨path, pl, c⟩ := r; exact normOf_runs hΔ B path pl c Cn (hnorm _ hr))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hmap
  have hfil := filter_runs (y1 hΔ) B fLeKC (toVal kmax) (fun c : CT => decide (c.maxEntry ≤ kmax))
    (fun _ => 40 * Sn + 10) ((introPlans v N t).map (fun r : List ℕ × CT.Plan × CT => norm r.2.2))
    (fun c hc' => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc'
      exact leKC_runs hΔ B kmax _ (by omega) Sn (hsz r hr))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hfil
  have hshow : introC kmax v N t =
      ((introPlans v N t).map (fun r : List ℕ × CT.Plan × CT => norm r.2.2)).filter
        (fun c : CT => decide (c.maxEntry ≤ kmax)) := rfl
  rw [hshow]
  refine Runs.mk (hΔ _ _ Δ_introC) ?_
  ev_start
  · ev_run
  · have e1 : (introPlans v N t).length * (Cn + 6) ≤ G * (Cn + 6) := Nat.mul_le_mul_right _ hOG
    have e2 : (introPlans v N t).length * (40 * Sn + 10) ≤ G * (40 * Sn + 10) := Nat.mul_le_mul_right _ hOG
    have e3 : G * (Cn + 40 * Sn + 80) = G * (Cn + 6) + G * (40 * Sn + 10) + 64 * G := by ring
    clear hG hΩ hnorm hsz hmap hfil hip hshow
    omega

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3D` -/

section
/-!
# WP E3 (assembly, part 1): discharging the length hypotheses of `introPlans_runs` with the bounds of P1

For a well-formed characteristic `t` (`Wf Bs kmax t`), with `b = |Bs|` and `M = runBound b`:

* `AM = (4·kmax+3)·(4·kmax+4)^(2M) + (2^b+1)^(b+2)·(4·kmax+3)`,
* `G = M·AM + 1`, `Ω = 2^b + 1`,

and every sub-run-tree `ν` (`Good Bs ν`, `maxEntry ν ≤ kmax`, `count ν ≤ M`) satisfies the hypotheses `hG`, `hΩ` of
`introPlans_runs` (`wtopPlans`, `allChains`, `attachPlans`, `introPlans` have fewer than `G` elements,
`chainCands` fewer than `Ω`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- `A_M` of `introPlans_length_le_aux` -/
def AM (b kmax : ℕ) : ℕ :=
  (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)

/-- the uniform length bound -/
def Gp (b kmax : ℕ) : ℕ := runBound b * AM b kmax + 1

theorem runBound_pos (b : ℕ) : 1 ≤ runBound b := by unfold runBound; nlinarith

theorem hG_of_good (Bs : Finset ℕ) (kmax v : ℕ) (N : Finset ℕ) (ν : CT) (M : ℕ) (hM : M = runBound Bs.card)
    (hg : Good Bs ν) (hm : maxEntry ν ≤ kmax) (hc : count ν ≤ M) :
    (wtopPlans v ν).length + 1 ≤ Gp Bs.card kmax ∧ (allChains ν.S N).length + 1 ≤ Gp Bs.card kmax ∧
      (attachPlans v N ν).length ≤ Gp Bs.card kmax ∧ (introPlans v N ν).length ≤ Gp Bs.card kmax := by
  subst hM
  set b := Bs.card with hb
  have hM1 := runBound_pos b
  have hAM : (2 ^ b + 1) ^ (b + 2) ≤ AM b kmax := by
    unfold AM
    have : (2 ^ b + 1) ^ (b + 2) ≤ (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hAM2 : (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤ AM b kmax := by unfold AM; omega
  have hMA : AM b kmax ≤ runBound b * AM b kmax := Nat.le_mul_of_pos_left _ hM1
  have hbS : ∀ S : Finset ℕ, S ⊆ Bs → S.card ≤ b := fun S h => Finset.card_le_card h
  cases ν with
  | node S y ks =>
    have hS : S.card ≤ b := hbS S hg.label_sub
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h1 := wtopPlans_length_le v kmax Bs hg hm
      have h2 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * count (node S y ks) - 1) ≤
          (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      have h3 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) ≤ AM b kmax := by unfold AM; omega
      unfold Gp; omega
    · have h1 := allChains_length_le (S := S) N hS
      show (allChains S N).length + 1 ≤ Gp b kmax
      unfold Gp; omega
    · have h1 := attachPlans_length_le v kmax Bs N hg hm (b := b) (t := node S y ks) hS
      unfold Gp; omega
    · have h1 := introPlans_length_le_aux v kmax Bs N (runBound b) b hbS (node S y ks) hg hm hc
      have h2 : count (node S y ks) * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * runBound b) +
          (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3)) ≤ runBound b * AM b kmax :=
        Nat.mul_le_mul_right _ hc
      unfold Gp; unfold AM at h2 ⊢; omega

/-- `M · A_M ≤ 2^(64 (b+kmax+2)^3)` (the computation inside `introPlans_length_le`) -/
theorem M_AM_le (b kmax : ℕ) : runBound b * AM b kmax ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := by
  unfold AM
  set M := runBound b with hM
  have hM1 : M ≤ 2 ^ (2 * b + 2) := by
    rw [hM]; unfold runBound
    have h1 : (b + 1) ≤ 2 ^ b := succ_le_two_pow b
    have h2 : (2 * b + 2) * (2 * b + 2) = 4 * ((b + 1) * (b + 1)) := by ring
    have h3 : (b + 1) * (b + 1) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul h1 h1
    have h4 : 2 ^ (2 * b + 2) = 4 * (2 ^ b * 2 ^ b) := by
      rw [show 2 * b + 2 = b + b + 2 by ring, pow_add, pow_add]; ring
    rw [h2, h4]
    omega
  have hK : (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ ((kmax + 2) * (2 * M)) := by
    rw [pow_mul 2 (kmax + 2) (2 * M)]
    exact Nat.pow_le_pow_left (four_mul_le kmax) _
  have hC : (2 ^ b + 1) ^ (b + 2) ≤ 2 ^ ((b + 1) * (b + 2)) := by
    have : 2 ^ b + 1 ≤ 2 ^ (b + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := b); omega
    calc (2 ^ b + 1) ^ (b + 2) ≤ (2 ^ (b + 1)) ^ (b + 2) := Nat.pow_le_pow_left this _
      _ = _ := by rw [← pow_mul]
  have h34 : 4 * kmax + 3 ≤ 2 ^ (kmax + 2) := le_trans (by omega) (four_mul_le kmax)
  set E1 := (kmax + 2) * (2 * M)
  set E2 := (b + 1) * (b + 2)
  have hA : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤
      2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1) := by
    have a1 : (4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) ≤ 2 ^ (kmax + 2) * 2 ^ E1 := Nat.mul_le_mul h34 hK
    have a2 : (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3) ≤ 2 ^ E2 * 2 ^ (kmax + 2) := Nat.mul_le_mul hC h34
    have b1 : 2 ^ E1 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have b2 : 2 ^ E2 ≤ 2 ^ (E1 + E2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (E1 + E2 + 1) = 2 * 2 ^ (E1 + E2) := by rw [pow_succ]; ring
    rw [this]
    nlinarith [Nat.mul_le_mul_left (2 ^ (kmax + 2)) b1, Nat.mul_le_mul_left (2 ^ (kmax + 2)) b2]
  calc M * ((4 * kmax + 3) * (4 * kmax + 4) ^ (2 * M) + (2 ^ b + 1) ^ (b + 2) * (4 * kmax + 3))
      ≤ 2 ^ (2 * b + 2) * (2 ^ (kmax + 2) * 2 ^ (E1 + E2 + 1)) := Nat.mul_le_mul hM1 hA
    _ = 2 ^ ((2 * b + 2) + (kmax + 2) + (E1 + E2 + 1)) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := by
      apply Nat.pow_le_pow_right (by norm_num)
      have := intro_exponent_le b kmax
      omega

theorem Gp_le (b kmax : ℕ) : Gp b kmax ≤ 2 * 2 ^ (64 * (b + kmax + 2) ^ 3) := by
  have h1 := M_AM_le b kmax
  have h2 : 1 ≤ 2 ^ (64 * (b + kmax + 2) ^ 3) := Nat.one_le_two_pow
  unfold Gp; omega

theorem Sn_le (b kmax W : ℕ) (hb : b + 1 ≤ W) (hk : kmax + 1 ≤ W) :
    runBound b ≤ 4 * W ^ 2 ∧
      (2 * runBound b + b + 4) * (2 * b + 4 * kmax + 10) ≤ 208 * W ^ 3 := by
  have hW1 : 1 ≤ W := by omega
  have hM : runBound b ≤ 4 * W ^ 2 := by
    unfold runBound
    have : 2 * b + 2 ≤ 2 * W := by omega
    have h2 := Nat.mul_le_mul this this
    nlinarith
  refine ⟨hM, ?_⟩
  have h1 : 2 * runBound b + b + 4 ≤ 13 * W ^ 2 := by
    have : W ≤ W ^ 2 := by nlinarith
    have : 1 ≤ W ^ 2 := Nat.one_le_pow _ _ hW1
    omega
  have h2 : 2 * b + 4 * kmax + 10 ≤ 16 * W := by omega
  calc (2 * runBound b + b + 4) * (2 * b + 4 * kmax + 10) ≤ (13 * W ^ 2) * (16 * W) := Nat.mul_le_mul h1 h2
    _ = 208 * W ^ 3 := by ring

theorem hΩ_of_good (Bs : Finset ℕ) (N : Finset ℕ) (ν : CT) (hg : Good Bs ν) :
    (chainCands ν.S N).length + 1 ≤ 2 ^ Bs.card + 1 := by
  cases ν with
  | node S y ks =>
    have hS : S.card ≤ Bs.card := Finset.card_le_card hg.label_sub
    show (chainCands S N).length + 1 ≤ 2 ^ Bs.card + 1
    have : (chainCands S N).length = 2 ^ (S \ N).card := by simp [chainCands, List.length_sublists]
    rw [this]
    have h2 : (S \ N).card ≤ Bs.card := le_trans (Finset.card_le_card Finset.sdiff_subset) hS
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
    omega

end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3Arith` -/

section
/-!
# WP E3 (assembly, part 2): the pure arithmetic of the final cost bound
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

theorem final_arith (W X M G Ω Sn c : ℕ) (hW : 1 ≤ W) (hX : 1 ≤ X)
    (hG : G ≤ 2 * X) (hΩ : Ω ≤ 2 * X) (hM : M ≤ 4 * W ^ 2) (hSn : Sn ≤ 208 * W ^ 3) (hc : 3 * c - 1 ≤ 3 * W) :
    (100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W) * (3 * c - 1) +
      (G * (6200 * (Sn + 1) ^ 5 + 40 * Sn + 80) + 100) ≤ 10 ^ 16 * W ^ 15 * X ^ 2 := by
  have hW2 : W ≤ W ^ 4 := by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 4 := Nat.pow_le_pow_right hW (by norm_num)
  have hW4 : W * W = W ^ 2 := by ring
  have hW2' : W ^ 2 ≤ W ^ 4 := Nat.pow_le_pow_right hW (by norm_num)
  have hX2 : X ≤ X ^ 2 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 2 := Nat.pow_le_pow_right hX (by norm_num)
  -- the pieces of Q₀
  have a1 : 100 * (1000 * W * W * (3 * M) * G) ≤ 2400000 * (W ^ 4 * X) := by
    have : W * W * M * G ≤ W * W * (4 * W ^ 2) * (2 * X) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hG
    nlinarith
  have a2 : 4 * (1000 * (W * Ω) * W * G) ≤ 16000 * (W ^ 2 * X ^ 2) := by
    have : W * Ω * W * G ≤ W * (2 * X) * W * (2 * X) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΩ) le_rfl) hG
    nlinarith
  have a3 : 500 * (W * G) ≤ 1000 * (W * X) := by nlinarith
  have hWX : W * X ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul hW2 hX2
  have hW4X : W ^ 4 * X ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have hW2X : W ^ 2 * X ^ 2 ≤ W ^ 4 * X ^ 2 := Nat.mul_le_mul_right _ hW2'
  have hQ₀ : 100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W ≤
      3000000 * (W ^ 4 * X ^ 2) := by
    have : W ≤ W ^ 4 * X ^ 2 := le_trans hW2 (Nat.le_mul_of_pos_right _ (by positivity))
    omega
  have hQc3 : (100 * (1000 * W * W * (3 * M) * G) + 4 * (1000 * (W * Ω) * W * G) + 500 * (W * G) + 1000 * W) * (3 * c - 1) ≤
      3000000 * (W ^ 4 * X ^ 2) * (3 * W) := Nat.mul_le_mul hQ₀ hc
  have hW5 : W ^ 4 * W = W ^ 5 := by ring
  have hW5' : W ^ 5 ≤ W ^ 15 := Nat.pow_le_pow_right hW (by norm_num)
  have b1 : (Sn + 1) ^ 5 ≤ (209 * W ^ 3) ^ 5 := Nat.pow_le_pow_left (by nlinarith [Nat.one_le_pow 3 W hW]) 5
  have b2 : (209 * W ^ 3) ^ 5 = 209 ^ 5 * W ^ 15 := by ring
  have hW3 : W ^ 3 ≤ W ^ 15 := Nat.pow_le_pow_right hW (by norm_num)
  have hW0 : 1 ≤ W ^ 15 := Nat.one_le_pow _ _ hW
  have c1 : 6200 * (Sn + 1) ^ 5 + 40 * Sn + 80 ≤ 3000000000000000 * W ^ 15 := by
    have : 6200 * (Sn + 1) ^ 5 ≤ 6200 * (209 ^ 5 * W ^ 15) := by rw [← b2]; exact Nat.mul_le_mul_left _ b1
    nlinarith
  have c2 : G * (6200 * (Sn + 1) ^ 5 + 40 * Sn + 80) ≤ 2 * X * (3000000000000000 * W ^ 15) := Nat.mul_le_mul hG c1
  have hXX : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX
  have e1 : 3000000 * (W ^ 4 * X ^ 2) * (3 * W) = 9000000 * (W ^ 5 * X ^ 2) := by ring
  have e2 : 2 * X * (3000000000000000 * W ^ 15) = 6000000000000000 * (W ^ 15 * X) := by ring
  have f1 : W ^ 5 * X ^ 2 ≤ W ^ 15 * X ^ 2 := Nat.mul_le_mul_right _ hW5'
  have f2 : W ^ 15 * X ≤ W ^ 15 * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have f3 : 1 ≤ W ^ 15 * X ^ 2 := le_trans hW0 (Nat.le_mul_of_pos_right _ (by positivity))
  have e3 : 10 ^ 16 * W ^ 15 * X ^ 2 = 10 ^ 16 * (W ^ 15 * X ^ 2) := by ring
  rw [e3]
  omega

end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3Final` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# WP E3 (assembly, part 3): the `Runs` theorem for `CT.introC` with the closed-form cost

`introCCost W s = 10^16 · W^15 · 2^(128 s³)` with `W = U + 1` (`U ≥` all sizes and naturals of the input) and
`s = |B| + kmax + 2`: polynomial in the size times `2^{O((|B|+kmax+2)^3)}`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3C

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- the closed-form cost bound of `introC` -/
def introCCost (W s : ℕ) : ℕ := 10 ^ 16 * W ^ 15 * 2 ^ (128 * s ^ 3)

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem introC_runs_wf (kmax v : ℕ) (N : Finset ℕ) (t : CT) (Bs : Finset ℕ) (hw : t.Wf Bs kmax)
    (U : ℕ) (hU : sz t ≤ U) (hM : mx t ≤ U) (hv : v ≤ U) (hN : N.card ≤ U) (hk : kmax ≤ U)
    (hnorm : ∀ (c : CT) (s : ℕ), sz c ≤ s → 14000 * (s + 1) ^ 5 < B →
      Runs Δ' B fNormId [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5))
    (hnsz : ∀ c : CT, sz (norm c) ≤ sz c)
    (hB : introCCost (U + 1) (Bs.card + kmax + 2) < B) :
    Runs Δ' B fIntroC [toVal kmax, toVal v, toVal N, toVal t] (toVal (introC kmax v N t))
      (introCCost (U + 1) (Bs.card + kmax + 2)) := by
  have hbU : Bs.card ≤ U := by
    have h1 := card_verts_le_sz t
    rw [hw.verts_eq] at h1
    omega
  have hX1 : 1 ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hW1 : 1 ≤ U + 1 := by omega
  have hcount : count t ≤ runBound Bs.card := hw.count_le
  have hcU : count t ≤ U := le_trans (count_le_sz t) hU
  obtain ⟨hMW, hSnW⟩ := Sn_le Bs.card kmax (U + 1) (by omega) (by omega)
  have hGX := Gp_le Bs.card kmax
  have hΩX : 2 ^ Bs.card + 1 ≤ 2 * 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := by
    have h1 : 2 ^ Bs.card ≤ 2 ^ (64 * (Bs.card + kmax + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) (by
      have : Bs.card ≤ (Bs.card + kmax + 2) ^ 3 := by
        have : Bs.card ≤ Bs.card + kmax + 2 := by omega
        calc Bs.card ≤ Bs.card + kmax + 2 := this
          _ = (Bs.card + kmax + 2) ^ 1 := (pow_one _).symm
          _ ≤ (Bs.card + kmax + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega)
    omega
  have hcost := final_arith (U + 1) (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) (runBound Bs.card) (Gp Bs.card kmax)
    (2 ^ Bs.card + 1) ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) (count t)
    hW1 hX1 hGX hΩX hMW hSnW (by omega)
  have e : introCCost (U + 1) (Bs.card + kmax + 2) = 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
    unfold introCCost
    rw [← pow_mul, show 64 * (Bs.card + kmax + 2) ^ 3 * 2 = 128 * (Bs.card + kmax + 2) ^ 3 by ring]
  rw [e] at hB ⊢
  have hBfit : 10 * U + 600 < B := by
    have : 10 * U + 600 ≤ 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
      have h1 : 1 ≤ (U + 1) ^ 15 := Nat.one_le_pow _ _ hW1
      have h2 : U + 1 ≤ (U + 1) ^ 15 := by
        calc U + 1 = (U + 1) ^ 1 := (pow_one _).symm
          _ ≤ (U + 1) ^ 15 := Nat.pow_le_pow_right hW1 (by norm_num)
      have h3 : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
      have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
          10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
      rw [h5]; omega
    omega
  have hBn : 14000 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5 < B := by
    have h1 : (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5 ≤ (209 * (U + 1) ^ 3) ^ 5 := by
      apply Nat.pow_le_pow_left
      generalize (2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10) = Sn at hSnW ⊢
      have := Nat.one_le_pow 3 (U + 1) hW1
      omega
    have h2 : (209 * (U + 1) ^ 3) ^ 5 = 209 ^ 5 * (U + 1) ^ 15 := by
      rw [mul_pow, ← pow_mul]
    have h3 : 14000 * (209 ^ 5 * (U + 1) ^ 15) ≤ 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := by
      have : 1 ≤ (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 := Nat.one_le_pow _ _ hX1
      have h4 : (U + 1) ^ 15 ≤ (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h5 : 10 ^ 16 * (U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2 =
          10 ^ 16 * ((U + 1) ^ 15 * (2 ^ (64 * (Bs.card + kmax + 2) ^ 3)) ^ 2) := by rw [mul_assoc]
      rw [h5]; norm_num; omega
    calc 14000 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5
        ≤ 14000 * (209 * (U + 1) ^ 3) ^ 5 := Nat.mul_le_mul_left _ h1
      _ = 14000 * (209 ^ 5 * (U + 1) ^ 15) := by rw [h2]
      _ < B := lt_of_le_of_lt h3 hB
  have hszx : ∀ x ∈ introPlans v N t, sz x.2.2 ≤ (2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10) := by
    intro x hx
    rw [sz_ct_eq]
    exact introPlans_vsz_le v N hw x hx
  have hmain := introC_runs hΔ B U (1000 * (U + 1) * (U + 1)) (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card))
    (Gp Bs.card kmax) (2 ^ Bs.card + 1) (1000 * ((U + 1) * (2 ^ Bs.card + 1)))
    (100 * (1000 * (U + 1) * (U + 1) * (3 * runBound Bs.card) * Gp Bs.card kmax) +
      4 * (1000 * ((U + 1) * (2 ^ Bs.card + 1)) * (U + 1) * Gp Bs.card kmax) +
      500 * ((U + 1) * Gp Bs.card kmax) + 1000 * (U + 1))
    (6200 * (((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) + 1) ^ 5)
    ((2 * runBound Bs.card + Bs.card + 4) * (2 * Bs.card + 4 * kmax + 10)) Bs kmax (runBound Bs.card) v N
    le_rfl le_rfl le_rfl le_rfl hv hN
    (fun ν hg hm hc => hG_of_good Bs kmax v N ν (runBound Bs.card) rfl hg hm hc)
    (fun ν hg => hΩ_of_good Bs N ν hg) (by omega) t hU hM hw.good hw.bounded hcount
    (fun x hx => hnorm x.2.2 _ (hszx x hx) hBn)
    (fun x hx => le_trans (hnsz _) (hszx x hx))
  refine hmain.mono ?_
  exact hcost

end proofs
end E3C
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E3` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# WP E3: the assembled interface — table `e3Tbl` (ids `256 … 332`), `Runs` / `Embeds` for `CT.introC`

The table is `e3Tbl = orElseΔ E3A.tbl (orElseΔ E3B.tbl E3C.tbl)`; `E3C.Δ` is the layered table used in the proofs and
`ext_e3 : E3C.Δ ⊑ layerΔ Lib.Δ 128 e3Tbl`.  **How the assembler uses this.**  Let `Δ'` be a table with
`hΔ : layerΔ Lib.Δ 128 e3Tbl ⊑ Δ'` (for the assembly `layerΔ Lib.Δ 128 (orElseΔ e1Tbl (orElseΔ e2Tbl e3Tbl))` obtain `hΔ` by
`Ext.layer_mono (Ext.orElse_right …)` from the disjointness fact `e3Tbl_lt : e3Tbl f = some _ → 256 ≤ f ∧ f < 333`);
then `Ext.trans ext_e3 hΔ : E3C.Δ ⊑ Δ'` is the hypothesis of every theorem of the `E3A/E3B/E3C` layers.
The function `norm` is *not* part of this table: its id is `E3C.fNormId = 166` (= `E2.fNorm`); the theorems take its
behaviour as a hypothesis (`hnorm`), discharged by `E2.norm_runs_e12` (cost `6200 (s+1)^5`), and `hnsz` by `E2.sz_norm_le`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `plus1`, `List.range'` | 256, 257 | `[y]`, `[lo, n]` | `E3A.plus1_runs`, `rangeP_runs` | `12|y|+6`, `14 n+6` |
| `CT.winPlans` | 264 | `[v, lo, t]` | `E3A.winPlans_runs` | `Q (3 count t - 1) (|out|+1)`, `Q ≥ 1000 (U+1)^2` (output-sensitive) |
| `CT.kidChoices` | 268 | `[v, ks]` | `E3A.kidChoices_runs` | `Q (3 countL ks + 1) (|out|+1)` |
| `CT.wtopPlans` | 293 | `[v, t]` | `E3B.wtopPlans_runs` | `100 P (|out|+1)`, `P ≥ Q (3 count t - 1)` |
| `CT.chainCands` | 295 | `[S, N]` | `E3B.chainCands_runs` | `500 (U+1)^2 · 2^{|S \ N|}` |
| `CT.chainsGo` | 300 | `[cands, fuel, bound, chain]` | `E3B.chainsGo_runs` | `Qc (fuel+1)(2|out|+1)`, `Qc ≥ 1000 (U+1)(|cands|+1)` |
| `CT.allChains` | 301 | `[S, N]` | `E3B.allChains_runs` | `Qc (U+1)(2|out|+2)` |
| `CT.pathSubtree` | 303 | `[v, chain, M]` | `E3B.pathSubtree_runs` | `300 (U+1)^2` |
| `CT.attachPlans` | 307 | `[v, N, t]` | `E3B.attachPlans_runs` | `2 Qc (U+1) (2|allChains|+2)` |
| `CT.introKids` | 324 | `[v, N, S, y, pre, ks]` | `E3C.introKids_runs` | `Q₀ (3 countL ks + 1)` |
| `CT.introPlans` | 325 | `[v, N, t]` | `E3C.introPlans_runs` | `Q₀ (3 count t - 1)` |
| `CT.maxEntry` | 328 | `[c]` | `E3C.maxEntry_runs` | `40 sz c` |
| `CT.introC` | 331 | `[kmax, v, N, t]` | `E3C.introC_runs`, **`E3C.introC_runs_wf`** | `introCCost (U+1) (|B|+kmax+2) = 10^16 (U+1)^15 2^{128 (|B|+kmax+2)^3}` |
| `CT.introC` (packed) | 332 | `[(kmax, v, N, t)]` | `introCUn_runs`, **`introC_embeds`** | `introCCost (sz p + mx p + 1) (|verts t|+kmax+2) + 20` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- the E3 table (ids `256 … 332`) -/
def e3Tbl : ℕ → Option Tm := orElseΔ E3A.tbl (orElseΔ E3B.tbl E3C.tbl)

theorem e3Tbl_lt {f : ℕ} {b : Tm} (h : e3Tbl f = some b) : 256 ≤ f ∧ f < 333 := by
  unfold e3Tbl orElseΔ at h
  rcases hA : E3A.tbl f with _ | a
  · rcases hB : E3B.tbl f with _ | b'
    · rcases hC : E3C.tbl f with _ | c
      · simp [hA, hB, hC] at h
      · have := E3C.tbl_lt hC; omega
    · have := E3B.tbl_lt hB; omega
  · have := E3A.tbl_lt hA; omega

theorem ext_e3 : E3C.Δ ⊑ layerΔ Lib.Δ 128 e3Tbl := by
  intro f b h
  have hA : ∀ {c}, E3A.tbl f = some c → 256 ≤ f ∧ f < 269 := fun {c} hc => E3A.tbl_lt hc
  have hB : ∀ {c}, E3B.tbl f = some c → 288 ≤ f ∧ f < 308 := fun {c} hc => E3B.tbl_lt hc
  have hC : ∀ {c}, E3C.tbl f = some c → 320 ≤ f ∧ f < 333 := fun {c} hc => E3C.tbl_lt hc
  unfold E3C.Δ layerΔ at h
  by_cases h3 : 320 ≤ f
  · rw [if_pos h3] at h
    have hA' : E3A.tbl f = none := by
      rcases hh : E3A.tbl f with _ | c
      · rfl
      · have := hA hh; omega
    have hB' : E3B.tbl f = none := by
      rcases hh : E3B.tbl f with _ | c
      · rfl
      · have := hB hh; omega
    simp [layerΔ, e3Tbl, orElseΔ, hA', hB', h, show 128 ≤ f by omega]
  · rw [if_neg h3] at h
    unfold E3B.Δ layerΔ at h
    by_cases h2 : 288 ≤ f
    · rw [if_pos h2] at h
      have hA' : E3A.tbl f = none := by
        rcases hh : E3A.tbl f with _ | c
        · rfl
        · have := hA hh; omega
      simp [layerΔ, e3Tbl, orElseΔ, hA', h, show 128 ≤ f by omega]
    · rw [if_neg h2] at h
      unfold E3A.Δ layerΔ at h
      by_cases h1 : 128 ≤ f
      · rw [if_pos h1] at h
        simp [layerΔ, e3Tbl, orElseΔ, h, h1]
      · rw [if_neg h1] at h
        simp [layerΔ, h1, h]

/-- a table containing `e3Tbl` (ids `≥ 128`) above the library extends `E3C.Δ` -/
theorem ext_e3_of {tbl' : ℕ → Option Tm} (h : e3Tbl ⊑ tbl') : E3C.Δ ⊑ layerΔ Lib.Δ 128 tbl' :=
  Ext.trans ext_e3 (Ext.layer_mono h)

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ')
include hΔ

end proofs

end E3
end Lax117284Proofs.Treewidth.Fun

end
