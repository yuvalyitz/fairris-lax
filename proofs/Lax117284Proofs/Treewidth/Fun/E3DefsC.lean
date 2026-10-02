import Lax117284Proofs.Treewidth.Fun.E3DefsB

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

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < 333 := by
  unfold Δ layerΔ at h
  by_cases hf : 320 ≤ f
  · rw [if_pos hf] at h; exact (tbl_lt h).2
  · rw [if_neg hf] at h; have := E3B.Δ_lt h; omega

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
theorem Δ_introCUn : Δ fIntroCUn = some introCUnTm := by simp [Δ, layerΔ_ge tbl (show 320 ≤ fIntroCUn by decide)]; rfl

theorem ids_lt {B : ℕ} (h : 500 < B) :
    fSubN < B ∧ fMk1 < B ∧ fMk2 < B ∧ fKid < B ∧ fIntroKids < B ∧ fIntroPlans < B ∧ fMaxL < B ∧
      fMaxEntryL < B ∧ fMaxEntry < B ∧ fNormOf < B ∧ fLeKC < B ∧ fIntroC < B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact Nat.lt_of_le_of_lt (by decide) h

end E3C
end Lax117284Proofs.Treewidth.Fun
