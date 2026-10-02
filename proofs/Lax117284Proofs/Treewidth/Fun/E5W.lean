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
theorem ext3 : E5C3.Δ ⊑ Δ := Ext.trans E5D.ext3 extD
theorem ext2 : E5C2.Δ ⊑ Δ := Ext.trans E5D.ext2 extD
theorem ext1 : E5C1.Δ ⊑ Δ := Ext.trans E5D.ext1 extD
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5D.extB extD
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5D.extA extD
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5D.extE1 extD

theorem Δ_analyzeP : Δ fAnalyzeP = some analyzePTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fAnalyzeP by decide)]; rfl
theorem Δ_cutAtP : Δ fCutAtP = some cutAtPTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fCutAtP by decide)]; rfl
theorem Δ_applyPlanP : Δ fApplyPlanP = some applyPlanPTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fApplyPlanP by decide)]; rfl
theorem Δ_mergeRealP : Δ fMergeRealP = some mergeRealPTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fMergeRealP by decide)]; rfl
theorem Δ_realIntroP : Δ fRealIntroP = some realIntroPTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fRealIntroP by decide)]; rfl
theorem Δ_realJoinP : Δ fRealJoinP = some realJoinPTm := by
  simp [Δ, layerΔ_ge tbl (show 530 ≤ fRealJoinP by decide)]; rfl

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

theorem embeds_analyze (E : Ext5 Δ') :
    Embeds Δ' fAnalyzeP (fun _ : Finset ℕ × RT => True) (fun a => analyze a.1 a.2) (costAnalyze E) := by
  intro B a _ hfit
  have hc := hfit.cost_lt
  obtain ⟨Bd, t⟩ := a
  have hs : sz (Bd, t) = sz Bd + sz t + 1 := sz_pair Bd t
  have hq : sz (Bd, t) + 1 ≤ 20000 * (sz (Bd, t) + 1) := by omega
  have h := E5B.analyze_runs (Ext.trans extB hΔ) B E Bd (sz (Bd, t)) (by omega) (by unfold costAnalyze at hc; omega) t
    (by omega)
  have hk : E5B.fAnalyze < B := by
    have : E5B.fAnalyze < 1000 := by decide
    unfold costAnalyze at hc; omega
  have ht : t.size ≤ sz (Bd, t) := le_trans (size_le_sz t) (by omega)
  have ht' : E5B.cA (sz (Bd, t)) (E.cKey (6 * sz (Bd, t))) * t.size ≤
      E5B.cA (sz (Bd, t)) (E.cKey (6 * sz (Bd, t))) * sz (Bd, t) := Nat.mul_le_mul_left _ ht
  refine Runs.mk (hΔ _ _ Δ_analyzeP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costAnalyze; omega

theorem embeds_cutAt :
    Embeds Δ' fCutAtP (fun _ : List ℕ × List ℕ × CT.Cut × List CNode => True)
      (fun a => cutAt a.1 a.2.1 a.2.2.1 a.2.2.2) costCutAt := by
  intro B a _ hfit
  have hc := hfit.cost_lt
  obtain ⟨y, w, c, ns⟩ := a
  have hs : sz (y, w, c, ns) = sz y + (sz w + (sz c + sz ns + 1) + 1) + 1 := by simp only [sz_pair]
  have hly := length_le_sz y
  have hlw := length_le_sz w
  have h := E5C1.cutAt_runs (Ext.trans ext1 hΔ) B y w c ns (sz (y, w, c, ns)) (by omega) (by omega) (by omega)
    (by unfold costCutAt at hc; omega)
  have hk : E5C1.fCutAt < B := by
    have : E5C1.fCutAt < 1000 := by decide
    unfold costCutAt at hc; omega
  refine Runs.mk (hΔ _ _ Δ_cutAtP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costCutAt; omega

theorem embeds_applyPlan (E : Ext5 Δ') :
    Embeds Δ' fApplyPlanP (fun _ : ℕ × Finset ℕ × Finset ℕ × List ℕ × CT.Plan × RT => True)
      (fun a => applyPlan a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2) (costApplyPlan E) := by
  intro B a _ hfit
  have hc := hfit.cost_lt
  obtain ⟨v, N, Bd, path, p, t⟩ := a
  have hs : sz (v, N, Bd, path, p, t) = sz v + (sz N + (sz Bd + (sz path + (sz p + sz t + 1) + 1) + 1) + 1) + 1 := by
    simp only [sz_pair]
  have hlp := length_le_sz path
  have h := E5C3.applyPlan_runs (Ext.trans ext3 hΔ) B E v N Bd path p t (sz (v, N, Bd, path, p, t))
    (by omega) (by omega) (by omega) (by omega) (by unfold costApplyPlan at hc; omega)
  have hk : E5C3.fApplyPlan < B := by
    have : E5C3.fApplyPlan < 1000 := by decide
    unfold costApplyPlan at hc; omega
  refine Runs.mk (hΔ _ _ Δ_applyPlanP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costApplyPlan; omega

theorem embeds_mergeReal (E : Ext5 Δ') (L : ℕ) :
    Embeds Δ' fMergeRealP
      (fun a : Finset ℕ × RT × RT × CT =>
        (∀ X ∈ a.2.1.bags, X.card ≤ L) ∧ (∀ X ∈ a.2.2.1.bags, X.card ≤ L) ∧ L ≤ 5 * sz a)
      (fun a => mergeReal a.1 a.2.1 a.2.2.1 a.2.2.2) (costMergeReal E L) := by
  intro B a ⟨hca, hcb, hL⟩ hfit
  have hc := hfit.cost_lt
  obtain ⟨Bd, ta, tb, tg⟩ := a
  have hs : sz (Bd, ta, tb, tg) = sz Bd + (sz ta + (sz tb + sz tg + 1) + 1) + 1 := by simp only [sz_pair]
  have h := E5D.mergeReal_runs (Ext.trans extD hΔ) B E Bd ta tb tg (sz (Bd, ta, tb, tg)) L
    (by omega) (by omega) (by omega) (by omega) hL hca hcb (by unfold costMergeReal at hc; omega)
  have hk : E5D.fMergeReal < B := by
    have : E5D.fMergeReal < 1000 := by decide
    unfold costMergeReal at hc; omega
  refine Runs.mk (hΔ _ _ Δ_mergeRealP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costMergeReal; omega

theorem embeds_realIntro (E : Ext5 Δ') (X : ExtIP Δ') :
    Embeds Δ' fRealIntroP
      (fun a : ℕ × ℕ × ℕ × Finset ℕ × Finset ℕ × RT × CT =>
        a.1 = X.ip ∧ X.PIP a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1) ∧
          ∀ r ∈ CT.introPlans a.2.2.1 a.2.2.2.1 (a.2.2.2.2.2.1.char a.2.2.2.2.1),
            E.PD (sizeRI a) (CT.norm r.2.2) a.2.2.2.2.2.2)
      (fun a => realIntro a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2) (costRealIntro E X) := by
  intro B a ⟨hip, hPIP, hPD⟩ hfit
  have hc := hfit.cost_lt
  obtain ⟨ip, kmax, v, N, Bd, t, tg⟩ := a
  simp only at hip hPIP
  subst hip
  have hs : sz (X.ip, kmax, v, N, Bd, t, tg) =
      sz X.ip + (sz kmax + (sz v + (sz N + (sz Bd + (sz t + sz tg + 1) + 1) + 1) + 1) + 1) + 1 := by
    simp only [sz_pair]
  have hSR : sizeRI (X.ip, kmax, v, N, Bd, t, tg) = sz (X.ip, kmax, v, N, Bd, t, tg) +
      sz (CT.introPlans v N (t.char Bd)) := rfl
  have hlen := length_le_sz (CT.introPlans v N (t.char Bd))
  have h := E5R.realIntro_runs (Ext.trans extR hΔ) B E X kmax v N Bd t tg (sizeRI (X.ip, kmax, v, N, Bd, t, tg))
    (sizeRI (X.ip, kmax, v, N, Bd, t, tg)) (by omega) (by omega) (by omega) hPIP (by omega)
    (fun r hr => by have := sz_le_of_mem hr; omega) hPD (by unfold costRealIntro at hc; (try dsimp only at hc); omega)
  have hk : E5R.fRealIntro < B := by
    have : E5R.fRealIntro < 1000 := by decide
    unfold costRealIntro at hc; (try dsimp only at hc); omega
  refine Runs.mk (hΔ _ _ Δ_realIntroP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costRealIntro; (try dsimp only); omega

theorem embeds_realJoin (E : Ext5 Δ') (X : ExtJ Δ') (L : ℕ) :
    Embeds Δ' fRealJoinP
      (fun a : ℕ × Finset ℕ × RT × RT × CT =>
        (∀ Y ∈ a.2.2.1.bags, Y.card ≤ L) ∧ (∀ Y ∈ a.2.2.2.1.bags, Y.card ≤ L) ∧ L ≤ 5 * sz a ∧
          X.PJ a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1) ∧
          ∀ d ∈ CT.joinC a.1 (a.2.2.1.char a.2.1) (a.2.2.2.1.char a.2.1), E.PD (sizeRJ a) d a.2.2.2.2)
      (fun a => realJoin a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) (costRealJoin E X L) := by
  intro B a ⟨hca, hcb, hL, hPJ, hPD⟩ hfit
  have hc := hfit.cost_lt
  obtain ⟨kmax, Bd, ta, tb, tg⟩ := a
  have hs : sz (kmax, Bd, ta, tb, tg) = sz kmax + (sz Bd + (sz ta + (sz tb + sz tg + 1) + 1) + 1) + 1 := by
    simp only [sz_pair]
  have hSR : sizeRJ (kmax, Bd, ta, tb, tg) = sz (kmax, Bd, ta, tb, tg) +
      sz (CT.joinC kmax (ta.char Bd) (tb.char Bd)) := rfl
  have hlen := length_le_sz (CT.joinC kmax (ta.char Bd) (tb.char Bd))
  have h := E5D.realJoin_runs (Ext.trans extD hΔ) B E X kmax Bd ta tb tg (sizeRJ (kmax, Bd, ta, tb, tg)) L
    (sizeRJ (kmax, Bd, ta, tb, tg)) (by omega) (by omega) (by omega) (by omega) (by omega)
    hca hcb hPJ (by omega) (fun d hd => by have := sz_le_of_mem hd; omega) hPD
    (by unfold costRealJoin at hc; (try dsimp only at hc); omega)
  have hk : E5D.fRealJoin < B := by
    have : E5D.fRealJoin < 1000 := by decide
    unfold costRealJoin at hc; (try dsimp only at hc); omega
  refine Runs.mk (hΔ _ _ Δ_realJoinP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · unfold costRealJoin; (try dsimp only); omega

end embeds

end E5W
end Lax117284Proofs.Treewidth.Fun
