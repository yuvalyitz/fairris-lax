import Lax117284Proofs.Treewidth.Fun.E5D

/-!
# WP E5 (layer W): tuple-argument wrappers and the `Embeds` statements

Ids `530 …` (the functions of `Embeds` take *one* argument, the tuple):

| id | wrapper of | argument tuple |
|---|---|---|
| 530 `fAnalyzeP` | `analyze` | `(Bd, t)` |
| 531 `fCutAtP` | `cutAt` | `(y, w, c, ns)` |
| 532 `fApplyPlanP` | `applyPlan` | `(v, N, Bd, path, p, t)` |
| 533 `fMergeRealP` | `mergeReal` | `(Bd, ta, tb, target)` |
| 534 `fRealIntroP` | `realIntro` | `(ip, kmax, v, N, Bd, t, target)` (`ip` = id of `introPlans`) |
| 535 `fRealJoinP` | `realJoin` | `(kmax, Bd, ta, tb, target)` |

Tuples are right-nested pairs, `(a, b, c) = (a, (b, c))`.  Every `embeds_*` theorem is stated for an arbitrary table
`Δ'` extending `E5W.Δ` (equivalently `e5Δ`, see `E5Tbl`) and the hypothesis records `Ext5` (norm, key, domC),
`ExtIP` (introPlans), `ExtJ` (joinC), which the assembler instantiates by the theorems of WPs E2/E3.
The costs are `κ · (S+1)^d`-shaped in the size `S` of the argument (and, for `realIntro`/`realJoin`, of the list of plans/join
options), plus the symbolic costs of the external functions; see the docstrings.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5W

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fAnalyzeP : ℕ := 530
abbrev fCutAtP : ℕ := 531
abbrev fApplyPlanP : ℕ := 532
abbrev fMergeRealP : ℕ := 533
abbrev fRealIntroP : ℕ := 534
abbrev fRealJoinP : ℕ := 535

/-! ## the terms -/

def analyzePTm : Tm := .call E5B.fAnalyze [.fst (V 0), .snd (V 0)]

def cutAtPTm : Tm :=
  .call E5C1.fCutAt [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def applyPlanPTm : Tm :=
  .call E5C3.fApplyPlan
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .fst (.snd (.snd (.snd (.snd (V 0))))), .snd (.snd (.snd (.snd (.snd (V 0)))))]

def mergeRealPTm : Tm :=
  .call E5D.fMergeReal [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def realIntroPTm : Tm :=
  .call E5R.fRealIntro
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .fst (.snd (.snd (.snd (.snd (V 0))))), .fst (.snd (.snd (.snd (.snd (.snd (V 0)))))),
     .snd (.snd (.snd (.snd (.snd (.snd (V 0))))))]

def realJoinPTm : Tm :=
  .call E5D.fRealJoin
    [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .fst (.snd (.snd (.snd (V 0)))),
     .snd (.snd (.snd (.snd (V 0))))]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 530 => some analyzePTm | 531 => some cutAtPTm | 532 => some applyPlanPTm | 533 => some mergeRealPTm
  | 534 => some realIntroPTm | 535 => some realJoinPTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5D.Δ 530 tbl

abbrev size : ℕ := 536

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 536 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h530 : 530 ≤ f := by omega
    simp only [h530, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extD : E5D.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5D.Δ_lt h; simp [E5D.size] at this; omega)
theorem extR : E5R.Δ ⊑ Δ := Ext.trans E5D.extR extD

/-! ## costs -/

/-- `analyze`: `S = sz (Bd, t)`; the second summand is the threshold for `B`. -/
def costAnalyze {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (a : Finset ℕ × RT) : ℕ :=
  E5B.cA (sz a) (E.cKey (6 * sz a)) * sz a + (20000 + 20000 * (sz a + 1) + E.cKey (6 * sz a))

def costCutAt (a : List ℕ × List ℕ × CT.Cut × List CNode) : ℕ := 100 * sz a + 400 + (20000 + 20000 * (sz a + 1))

def costApplyPlan {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (a : ℕ × Finset ℕ × Finset ℕ × List ℕ × CT.Plan × RT) : ℕ :=
  E5C3.cApplyPlan (sz a) (E.cKey (6 * sz a)) + (20000 + 20000 * (sz a + 1) + E.cKey (6 * sz a))

/-- `mergeReal`, with `L` a bound on the bag sizes of both trees. -/
def costMergeReal {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (L : ℕ) (a : Finset ℕ × RT × RT × CT) : ℕ :=
  E5D.cMergeReal (sz a) L (E.cKey (6 * sz a)) + (200000 + 100000 * (sz a + 1) ^ 2 + E.cKey (6 * sz a))

/-- the total size `S` used by `realIntro`: the argument and the list of plans -/
def sizeRI (a : ℕ × ℕ × ℕ × Finset ℕ × Finset ℕ × RT × CT) : ℕ :=
  sz a + sz (CT.introPlans a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1))

/-- `realIntro` on `(ip, kmax, v, N, Bd, t, target)`: `L = S` bounds the number of plans, `S` the size of each -/
def costRealIntro {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (X : ExtIP Δ') (a : ℕ × ℕ × ℕ × Finset ℕ × Finset ℕ × RT × CT) : ℕ :=
  E5R.cRealIntro (sizeRI a) (sizeRI a) (E.cNorm (5 * sizeRI a)) (E.cNorm (sizeRI a)) (E.cDom (sizeRI a))
      (E.cKey (6 * sizeRI a)) (X.cIP a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1)) +
    (20000 + 20000 * (sizeRI a + 1) + E.cKey (6 * sizeRI a) + E.cNorm (5 * sizeRI a) + E.cNorm (sizeRI a) +
      E.cDom (sizeRI a) + X.cIP a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1))

/-- the total size `S` used by `realJoin`: the argument and the list of join options -/
def sizeRJ (a : ℕ × Finset ℕ × RT × RT × CT) : ℕ :=
  sz a + sz (CT.joinC a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1))

/-- `realJoin` on `(kmax, Bd, ta, tb, target)` (`L` bounds the bag sizes) -/
def costRealJoin {Δ' : ℕ → Option Tm} (E : Ext5 Δ') (X : ExtJ Δ') (L : ℕ) (a : ℕ × Finset ℕ × RT × RT × CT) : ℕ :=
  E5D.cRealJoin (sizeRJ a) L (sizeRJ a) (E.cNorm (5 * sizeRJ a)) (E.cDom (sizeRJ a)) (E.cKey (6 * sizeRJ a))
      (X.cJ a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1)) +
    (200000 + 100000 * (sizeRJ a + 1) ^ 2 + E.cKey (6 * sizeRJ a) + E.cNorm (5 * sizeRJ a) + E.cDom (sizeRJ a) +
      X.cJ a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1))

/-! ## the `Embeds` statements -/

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ')
include hΔ

end embeds

end E5W
end Lax117284Proofs.Treewidth.Fun
