import Lax117284Proofs.Treewidth.Fun.E5C3

/-!
# WP E5 (layer R): `realIntro`

Ids `500 …`:

| id | function | arguments |
|---|---|---|
| 500 `fEntLeY` | `decide (y.foldr max 0 ≤ kmax)` | `[kmax, y]` |
| 501 `fEntLeL` | `decide (CT.maxEntryL ks ≤ kmax)` | `[kmax, ks]` |
| 502 `fEntLe` | `decide (c.maxEntry ≤ kmax)` | `[kmax, c]` |
| 503 `fPredIntro` | the predicate of `realIntro`'s `find?` (context `(target, kmax)`) | `[ctx, r]` |
| 504 `fRealIntro` | `realIntro` (the id of `introPlans` is the first argument) | `[ip, kmax, v, N, Bd, t, target]` |
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5R

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1 E5C2 E5C3

abbrev fEntLeY : ℕ := 500
abbrev fEntLeL : ℕ := 501
abbrev fEntLe : ℕ := 502
abbrev fPredIntro : ℕ := 503
abbrev fRealIntro : ℕ := 504

/-- the predicate of `realIntro` -/
abbrev predI (kmax : ℕ) (target : CT) : List ℕ × CT.Plan × CT → Bool :=
  fun r => CT.domCB (CT.norm r.2.2) target && decide ((CT.norm r.2.2).maxEntry ≤ kmax)

/-! ## the terms -/

def entLeYTm : Tm :=
  .ite (.isNat (V 1)) (.lit 1) (.mul (E5C1.leT (.fst (V 1)) (V 0)) (.call fEntLeY [V 0, .snd (V 1)]))

def entLeLTm : Tm :=
  .ite (.isNat (V 1)) (.lit 1) (.mul (.call fEntLe [V 0, .fst (V 1)]) (.call fEntLeL [V 0, .snd (V 1)]))

def entLeTm : Tm :=
  .mul (.call fEntLeY [V 0, .fst (.snd (V 1))]) (.call fEntLeL [V 0, .snd (.snd (V 1))])

def predIntroTm : Tm :=
  .letE (.call idNorm [.snd (.snd (V 1))])
    (.mul (.call idDomC [V 0, .fst (V 1)]) (.call fEntLe [.snd (V 1), V 0]))

def realIntroTm : Tm :=
  .letE (.callv (V 0) [V 2, V 3, .call fChar [V 4, V 5]])
    (.letE (.call Lib4.fFind [.lit fPredIntro, .cons (V 7) (V 2), V 0])
      (.ite (.isNat (V 0)) (.lit 0)
        (.cons (.lit 1)
          (.call fApplyPlan [V 4, V 5, V 6, .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), V 7]))))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 500 => some entLeYTm | 501 => some entLeLTm | 502 => some entLeTm | 503 => some predIntroTm
  | 504 => some realIntroTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C3.Δ 500 tbl

abbrev size : ℕ := 505

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 505 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h500 : 500 ≤ f := by omega
    simp only [h500, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext3 : E5C3.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C3.Δ_lt h; simp [E5C3.size] at this; omega)
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C3.extB ext3
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C3.extA ext3
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C3.extE1 ext3

theorem Δ_entLeY : Δ fEntLeY = some entLeYTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLeY by decide)]; rfl
theorem Δ_entLeL : Δ fEntLeL = some entLeLTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLeL by decide)]; rfl
theorem Δ_entLe : Δ fEntLe = some entLeTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fEntLe by decide)]; rfl
theorem Δ_predIntro : Δ fPredIntro = some predIntroTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fPredIntro by decide)]; rfl
theorem Δ_realIntro : Δ fRealIntro = some realIntroTm := by
  simp [Δ, layerΔ_ge tbl (show 500 ≤ fRealIntro by decide)]; rfl

/-! ## `maxEntry ≤ kmax` -/

theorem sz_ct_ks_lt (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz ks < sz (CT.node S y ks) := by
  rw [sz_ct_node]; have := sz_pos S; have := sz_pos y; omega
theorem sz_ct_y_lt (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz y < sz (CT.node S y ks) := by
  rw [sz_ct_node]; have := sz_pos S; have := sz_pos ks; omega

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem entLeY_runs (kmax : ℕ) (hB : 1 < B) : ∀ y : List ℕ,
    Runs Δ' B fEntLeY [toVal kmax, toVal y] (toVal (decide (y.foldr max 0 ≤ kmax))) (20 * y.length + 10)
  | [] => by
    refine Runs.mk (hΔ _ _ Δ_entLeY) ?_
    simp only [List.foldr_nil, Nat.zero_le, decide_true]
    ev_start
    · ev_run
    · simp
  | a :: y => by
    have ih := entLeY_runs kmax hB y
    refine Runs.mk (hΔ _ _ Δ_entLeY) ?_
    by_cases h1 : a ≤ kmax <;> by_cases h2 : y.foldr max 0 ≤ kmax
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = true := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2, decide_true] at ih
      have h1' : ¬ kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2, decide_false] at ih
      have h1' : ¬ kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2] at ih
      have h1' : kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega
    · have e : decide ((a :: y).foldr max 0 ≤ kmax) = false := by simp [List.foldr_cons, h1, h2]
      rw [e]; simp only [h2] at ih
      have h1' : kmax < a := by omega
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h1']; done) | (simp [h1']; omega))
      · simp only [List.length_cons]; omega

mutual
theorem entLe_runs_rec (kmax : ℕ) (hB : 1 < B) (hk : fEntLe < B) : ∀ c : CT,
    Runs Δ' B fEntLe [toVal kmax, toVal c] (toVal (decide (c.maxEntry ≤ kmax))) (30 * sz c + 10)
  | .node S y ks => by
    have h1 := entLeY_runs hΔ B kmax hB y
    have h2 := entLeL_runs_rec kmax hB hk ks
    have hkl : fEntLeL < B := by
      have : fEntLeL < fEntLe := by decide
      omega
    have hky : fEntLeY < B := by
      have : fEntLeY < fEntLe := by decide
      omega
    have hy := length_le_sz y
    have hs := sz_ct_node S y ks
    have hyv := sz_pos y
    refine Runs.mk (hΔ _ _ Δ_entLe) ?_
    simp only [toVal_ct]
    have e : decide ((CT.node S y ks).maxEntry ≤ kmax) =
        (decide (y.foldr max 0 ≤ kmax) && decide (CT.maxEntryL ks ≤ kmax)) := by
      simp only [CT.maxEntry, max_le_iff, Bool.decide_and]
    rw [e]
    by_cases a1 : y.foldr max 0 ≤ kmax <;> by_cases a2 : CT.maxEntryL ks ≤ kmax
    · simp only [a1, a2, decide_true] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · have := sz_pos S; omega
theorem entLeL_runs_rec (kmax : ℕ) (hB : 1 < B) (hk : fEntLe < B) : ∀ ks : List CT,
    Runs Δ' B fEntLeL [toVal kmax, toVal ks] (toVal (decide (CT.maxEntryL ks ≤ kmax))) (30 * sz ks + 10)
  | [] => by
    refine Runs.mk (hΔ _ _ Δ_entLeL) ?_
    simp only [CT.maxEntryL, Nat.zero_le, decide_true]
    ev_start
    · ev_run
    · simp
  | k :: ks => by
    have h1 := entLe_runs_rec kmax hB hk k
    have h2 := entLeL_runs_rec kmax hB hk ks
    have hkc : fEntLeL < B := by
      have : fEntLeL < fEntLe := by decide
      omega
    refine Runs.mk (hΔ _ _ Δ_entLeL) ?_
    have e : decide (CT.maxEntryL (k :: ks) ≤ kmax) =
        (decide (k.maxEntry ≤ kmax) && decide (CT.maxEntryL ks ≤ kmax)) := by
      simp only [CT.maxEntryL, max_le_iff, Bool.decide_and]
    rw [e]
    simp only [toVal_cons, sz_cons]
    by_cases a1 : k.maxEntry ≤ kmax <;> by_cases a2 : CT.maxEntryL ks ≤ kmax
    · simp only [a1, a2, decide_true] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [a1, a2, decide_true, decide_false] at h1 h2 ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
end

end proofs

theorem entLe_runs_pair : (type_of% @entLe_runs_rec) ∧ (type_of% @entLeL_runs_rec) :=
  ⟨@entLe_runs_rec, @entLeL_runs_rec⟩

theorem entLe_runs : type_of% @entLe_runs_rec := entLe_runs_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hΔ in
theorem sz_plan_res_le (r : List ℕ × CT.Plan × CT) : sz r.2.2 ≤ sz r ∧ sz r.1 ≤ sz r ∧ sz r.2.1 ≤ sz r := by
  obtain ⟨a, b, c⟩ := r
  simp only [sz_pair]
  omega

/-- cost of the predicate of `realIntro` -/
def cPredI (cnorm cdom s : ℕ) : ℕ := cnorm + cdom + 30 * s + 100

theorem predIntro_runs (E : Ext5 Δ') (kmax : ℕ) (target : CT) (r : List ℕ × CT.Plan × CT) (s : ℕ)
    (hr : sz r ≤ s) (htg : sz target ≤ s) (hPD : E.PD s (CT.norm r.2.2) target) (hB : 1000 + 100 * (s + 1) + E.cNorm s + E.cDom s < B) :
    Runs Δ' B fPredIntro [toVal (target, kmax), toVal r] (toVal (predI kmax target r))
      (cPredI (E.cNorm s) (E.cDom s) s) := by
  have hr' := (sz_plan_res_le r).1
  have hn := E.norm B s r.2.2 (by omega) (by omega)
  have hnsz := E.norm_sz r.2.2
  have hd := E.domC B s (CT.norm r.2.2) target hPD (by omega) htg (by omega)
  have hk : fEntLe < B := by
    have : fEntLe < 1000 := by decide
    omega
  have he := entLe_runs hΔ B kmax (by omega) hk (CT.norm r.2.2)
  have hsz := sz_pos (CT.norm r.2.2)
  refine Runs.mk (hΔ _ _ Δ_predIntro) ?_
  by_cases a1 : CT.domCB (CT.norm r.2.2) target = true <;> by_cases a2 : (CT.norm r.2.2).maxEntry ≤ kmax
  · have e : predI kmax target r = true := by simp [predI, a1, a2]
    rw [e]
    simp only [a1, a2, decide_true] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [Bool.not_eq_true] at a1
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega
  · have e : predI kmax target r = false := by simp [predI, a1, a2]
    rw [e]
    simp only [Bool.not_eq_true] at a1
    simp only [a1, a2, decide_true, decide_false] at hd he
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · unfold cPredI; omega

/-- cost of `realIntro` -/
def cRealIntro (s L cnorm5 cnorm cdom ck6 cip : ℕ) : ℕ :=
  (200 * (s + 1) * s + cnorm5 + 8) + cip + (24 * L + 6 + L * cPredI cnorm cdom s) + cApplyPlan s ck6 + 100

theorem realIntro_runs (E : Ext5 Δ') (X : ExtIP Δ') (kmax v : ℕ) (N Bd : Finset ℕ) (t : RT) (target : CT)
    (s L : ℕ) (hBd : sz Bd ≤ s) (ht : sz t ≤ s) (htg : sz target ≤ s)
    (hPIP : X.PIP v N (t.char Bd)) (hLen : (CT.introPlans v N (t.char Bd)).length ≤ L)
    (hplans : ∀ r ∈ CT.introPlans v N (t.char Bd), sz r ≤ s)
    (hPD : ∀ r ∈ CT.introPlans v N (t.char Bd), E.PD s (CT.norm r.2.2) target)
    (hB : 20000 + 20000 * (s + 1) + E.cKey (6 * s) + E.cNorm (5 * s) + E.cNorm s + E.cDom s +
      X.cIP v N (t.char Bd) < B) :
    Runs Δ' B fRealIntro [Val.nat X.ip, toVal kmax, toVal v, toVal N, toVal Bd, toVal t, toVal target]
      (toVal (realIntro kmax v N Bd t target))
      (cRealIntro s L (E.cNorm (5 * s)) (E.cNorm s) (E.cDom s) (E.cKey (6 * s)) (X.cIP v N (t.char Bd))) := by
  have hE1 := Ext.trans extE1 hΔ
  have hch := E5A.char_runs (Ext.trans extA hΔ) B E Bd t s ht hBd (by omega)
  have hip := X.introPlans B v N (t.char Bd) hPIP (by omega)
  have hfind := Lib4.find_runs (l4 hE1) B fPredIntro (toVal (target, kmax)) (predI kmax target)
    (fun _ => cPredI (E.cNorm s) (E.cDom s) s) (CT.introPlans v N (t.char Bd))
    (fun r hr => predIntro_runs hΔ B E kmax target r s (hplans r hr) htg (hPD r hr) (by omega)) (by omega)
  simp only [E5.sum_map_const] at hfind
  have hmul : (CT.introPlans v N (t.char Bd)).length * cPredI (E.cNorm s) (E.cDom s) s ≤
      L * cPredI (E.cNorm s) (E.cDom s) s := Nat.mul_le_mul_right _ hLen
  have hts : 200 * (s + 1) * t.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz t) ht)
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hk1 : fChar < B := lt_of_bnd hB2 (by decide)
  have hk2 : fPredIntro < B := lt_of_bnd hB2 (by decide)
  have hk3 : fApplyPlan < B := lt_of_bnd hB2 (by decide)
  have hk4 : Lib4.fFind < B := lt_of_bnd hB2 (by decide)
  have hgoal : realIntro kmax v N Bd t target =
      ((CT.introPlans v N (t.char Bd)).find? (predI kmax target)).map (fun r => applyPlan v N Bd r.1 r.2.1 t) := rfl
  rw [hgoal]
  rcases hf : (CT.introPlans v N (t.char Bd)).find? (predI kmax target) with _ | r
  · rw [hf] at hfind
    refine Runs.mk (hΔ _ _ Δ_realIntro) ?_
    simp only [Option.map_none]
    ev_start
    · ev_run
    · unfold cRealIntro; omega
  · rw [hf] at hfind
    have hrmem : r ∈ CT.introPlans v N (t.char Bd) := List.mem_of_find?_eq_some hf
    have hr1 := hplans r hrmem
    have hs := sz_plan_res_le r
    have hpath := length_le_sz r.1
    have hap := applyPlan_runs (Ext.trans ext3 hΔ) B E v N Bd r.1 r.2.1 t s hBd ht (by omega) (by omega) (by omega)
    refine Runs.mk (hΔ _ _ Δ_realIntro) ?_
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · unfold cRealIntro; omega

end proofs
end E5R
end Lax117284Proofs.Treewidth.Fun
