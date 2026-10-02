import Lax117284Proofs.Treewidth.Fun.E3DefsA

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
