import Lax117284Proofs.Treewidth.Fun.E5C1

/-!
# WP E5 (layer C2): `processRun`, `applyKids`, `applyOpt`

Ids `480 …`:

| id | function | arguments |
|---|---|---|
| 480 `fMapP1` | `Option.map (· + 1)` | `[o]` |
| 481 `fEndStep` | the `endStep` of `processRun` | `[y, wp, w, ns]` |
| 482 `fPreStep` | the `preStep` of `processRun` | `[y, wp, pre, endS]` |
| 483 `fProcessRun` | `processRun` | `[v, pre, w, r]` |
| 484 `fApplyKids` | `applyKids` | `[v, ps, ks]` |
| 485 `fApplyOpt` | `applyOpt` | `[v, p, k]` |

The Lean `let`/`match` of `processRun` is exposed as `endStepL`, `preStepL` (`processRun_eq`).
Cost: `cPR s · wn w` where `wn` counts the nodes of the region plan.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C2

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

abbrev fMapP1 : ℕ := 480
abbrev fEndStep : ℕ := 481
abbrev fPreStep : ℕ := 482
abbrev fProcessRun : ℕ := 483
abbrev fApplyKids : ℕ := 484
abbrev fApplyOpt : ℕ := 485

/-! ## the Lean side -/

def endStepL (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) : List CNode × Option ℕ :=
  match w with
  | .endAt c => ((cutAt y wp c ns).1, some (cutAt y wp c ns).2)
  | .whole _ => (ns, none)

def preStepL (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) :
    List CNode × ℕ × Option ℕ :=
  match pre with
  | none => (endS.1, 0, endS.2)
  | some c => ((cutAt y wp c endS.1).1, (cutAt y wp c endS.1).2 + 1,
      if c.isT1 then endS.2.map (· + 1) else endS.2)

theorem processRun_eq (v : ℕ) (pre : Option CT.Cut) (w : CT.WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    processRun v pre w (.run S ns ks) =
      .run S (addV v (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).2.1
        (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).2.2
        (preStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card)))
          pre (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card))) (witnesses (ns.map (fun n => n.bag.card))) w ns)).1)
        (match w with | .endAt _ => ks | .whole ps => applyKids v ps ks) := by
  cases w <;> cases pre <;> (simp only [processRun, endStepL, preStepL]; try rfl)

/-! ## the terms -/

def mapP1Tm : Tm := .ite (.isNat (V 0)) (.lit 0) (.cons (.lit 1) (.add (.snd (V 0)) (.lit 1)))

/-- `[y, wp, w, ns]` -/
def endStepTm : Tm :=
  .ite (.eq (.fst (V 2)) (.lit 1))
    (.letE (.call fCutAt [V 0, V 1, .snd (V 2), V 3])
      (.cons (.fst (V 0)) (.cons (.lit 1) (.snd (V 0)))))
    (.cons (V 3) (.lit 0))

/-- `[y, wp, pre, endS]` -/
def preStepTm : Tm :=
  .ite (.isNat (V 2))
    (.cons (.fst (V 3)) (.cons (.lit 0) (.snd (V 3))))
    (.letE (.call fCutAt [V 0, V 1, .snd (V 2), .fst (V 3)])
      (.cons (.fst (V 0))
        (.cons (.add (.snd (V 0)) (.lit 1))
          (.ite (.eq (.fst (.snd (V 3))) (.lit 1)) (.call fMapP1 [.snd (V 4)]) (.snd (V 4))))))

/-- `[v, pre, w, r]` -/
def processRunTm : Tm :=
  .letE (.call fCards [.fst (.snd (V 3))])
    (.letE (.call E1A.fTypical [V 0])
      (.letE (.call E1B.fWitnesses [V 1])
        (.letE (.call fEndStep [V 1, V 0, V 5, .fst (.snd (V 6))])
          (.letE (.call fPreStep [V 2, V 1, V 5, V 0])
            (.letE (.call fAddV [V 5, .fst (.snd (V 0)), .snd (.snd (V 0)), .fst (V 0)])
              (.cons (.fst (V 9))
                (.cons (V 0)
                  (.ite (.eq (.fst (V 8)) (.lit 1)) (.snd (.snd (V 9)))
                    (.call fApplyKids [V 6, .snd (V 8), .snd (.snd (V 9))])))))))))

/-- `[v, ps, ks]` -/
def applyKidsTm : Tm :=
  .ite (.isNat (V 1)) (V 2)
    (.ite (.isNat (V 2)) (.lit 0)
      (.cons (.call fApplyOpt [V 0, .fst (V 1), .fst (V 2)])
        (.call fApplyKids [V 0, .snd (V 1), .snd (V 2)])))

/-- `[v, p, k]` -/
def applyOptTm : Tm :=
  .ite (.isNat (V 1)) (V 2) (.call fProcessRun [V 0, .lit 0, .snd (V 1), V 2])

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 480 => some mapP1Tm | 481 => some endStepTm | 482 => some preStepTm | 483 => some processRunTm
  | 484 => some applyKidsTm | 485 => some applyOptTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C1.Δ 480 tbl

abbrev size : ℕ := 486

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 486 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h480 : 480 ≤ f := by omega
    simp only [h480, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext1 : E5C1.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C1.Δ_lt h; simp [E5C1.size] at this; omega)
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C1.extB ext1
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C1.extA ext1
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C1.extE1 ext1

theorem Δ_mapP1 : Δ fMapP1 = some mapP1Tm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fMapP1 by decide)]; rfl
theorem Δ_endStep : Δ fEndStep = some endStepTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fEndStep by decide)]; rfl
theorem Δ_preStep : Δ fPreStep = some preStepTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fPreStep by decide)]; rfl
theorem Δ_processRun : Δ fProcessRun = some processRunTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fProcessRun by decide)]; rfl
theorem Δ_applyKids : Δ fApplyKids = some applyKidsTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fApplyKids by decide)]; rfl
theorem Δ_applyOpt : Δ fApplyOpt = some applyOptTm := by
  simp [Δ, layerΔ_ge tbl (show 480 ≤ fApplyOpt by decide)]; rfl

/-! ## witnesses are small -/

theorem wpush_snd_le (L : ℕ) : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), (∀ p ∈ st, p.2 ≤ L) → j ≤ L →
    ∀ p ∈ wpush st y j, p.2 ≤ L
  | [], y, j, _, hj => by
    intro p hp; simp only [wpush, List.mem_singleton] at hp; subst hp; exact hj
  | (x, i) :: t, y, j, hst, hj => by
    intro p hp
    have hi : i ≤ L := hst (x, i) (by simp)
    have ht : ∀ q ∈ t, q.2 ≤ L := fun q hq => hst q (List.mem_cons_of_mem _ hq)
    rw [E1B.wpush_cons] at hp
    split_ifs at hp with h1 h2
    · simp only [List.mem_singleton] at hp; subst hp; exact hi
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hi
      · exact hj
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact hi
      · exact wpush_snd_le L t y j ht hj p hp

theorem witnessesAux_snd_le (L : ℕ) : ∀ (l : List ℕ) (j : ℕ) (st : List (ℕ × ℕ)),
    (∀ p ∈ st, p.2 ≤ L) → j + l.length ≤ L → ∀ p ∈ witnessesAux j st l, p.2 ≤ L
  | [], j, st, hst, _ => by simpa [witnessesAux] using hst
  | y :: l, j, st, hst, hj => by
    simp only [witnessesAux]
    simp only [List.length_cons] at hj
    exact witnessesAux_snd_le L l (j + 1) (wpush st y j) (wpush_snd_le L st y j hst (by omega)) (by omega)

theorem witnesses_le (a : List ℕ) : ∀ e ∈ witnesses a, e ≤ a.length := by
  intro e he
  unfold witnesses at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 he
  exact witnessesAux_snd_le a.length a 0 [] (by simp) (by omega) p hp

theorem cutAt_snd_le (y w : List ℕ) (L : ℕ) (hw : ∀ e ∈ w, e ≤ L) (c : CT.Cut) (ns : List CNode) :
    (cutAt y w c ns).2 ≤ L := by
  have key : ∀ f, w.getD f 0 ≤ L := by
    intro f
    by_cases hf : f < w.length
    · rw [List.getD_eq_getElem _ _ hf]; exact hw _ (List.getElem_mem hf)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  cases c with
  | t1 f => simp only [cutAt]; exact key f
  | t2 f =>
    simp only [cutAt]
    split_ifs
    · exact key f
    · have := key (f + 1); omega

/-! ## sizes of the steps -/

theorem sz_endStep_le (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) :
    sz (endStepL y wp w ns).1 ≤ 2 * sz ns + 3 := by
  cases w with
  | endAt c => simp only [endStepL]; exact sz_cutAt_le y wp c ns
  | whole ps => simp only [endStepL]; omega

theorem endStep_snd_le (y wp : List ℕ) (L : ℕ) (hw : ∀ e ∈ wp, e ≤ L) (w : CT.WPlan) (ns : List CNode) :
    ∀ e, (endStepL y wp w ns).2 = some e → e ≤ L := by
  intro e he
  cases w with
  | endAt c =>
    simp only [endStepL, Option.some.injEq] at he
    rw [← he]; exact cutAt_snd_le y wp L hw c ns
  | whole ps => simp [endStepL] at he

theorem sz_preStep_le (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) :
    sz (preStepL y wp pre endS).1 ≤ 2 * sz endS.1 + 3 := by
  cases pre with
  | none => simp only [preStepL]; omega
  | some c => simp only [preStepL]; exact sz_cutAt_le y wp c endS.1

theorem preStep_snd_le (y wp : List ℕ) (L : ℕ) (hw : ∀ e ∈ wp, e ≤ L) (pre : Option CT.Cut)
    (endS : List CNode × Option ℕ) (hE2 : ∀ e, endS.2 = some e → e ≤ L) :
    (preStepL y wp pre endS).2.1 ≤ L + 1 ∧ ∀ e, (preStepL y wp pre endS).2.2 = some e → e ≤ L + 1 := by
  cases pre with
  | none => simp only [preStepL]; exact ⟨by omega, fun e he => by have := hE2 e he; omega⟩
  | some c =>
    have h1 := cutAt_snd_le y wp L hw c endS.1
    refine ⟨by simp only [preStepL]; omega, fun e he => ?_⟩
    simp only [preStepL] at he
    split_ifs at he with hc
    · obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 he
      have := hE2 e' he'; omega
    · have := hE2 e he; omega

/-! ## region plans: size measure -/

mutual
def wn : CT.WPlan → ℕ
  | .endAt _ => 1
  | .whole ps => 1 + wnL ps
def wnL : List (Option CT.WPlan) → ℕ
  | [] => 0
  | p :: ps => wnO p + wnL ps
def wnO : Option CT.WPlan → ℕ
  | none => 1
  | some p => wn p
end

/-- the local cost bound of `processRun` -/
def cPR (s : ℕ) : ℕ := 3000 * (s + 1) ^ 3

/-! ## sizes of the results -/

theorem sz_processRun_aux (v : ℕ) (pre : Option CT.Cut) (w : CT.WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) : sz ((processRun v pre w (.run S ns ks)).chain) ≤ 8 * sz ns + 18 ∧
    (processRun v pre w (.run S ns ks)).S = S := by
  rw [processRun_eq]
  refine ⟨?_, rfl⟩
  simp only [AR.chain]
  refine le_trans (sz_addV_le _ _ _ _) ?_
  have h1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
    (witnesses (ns.map (fun n => n.bag.card))) pre
    (endStepL (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) w ns)
  have h2 := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
    (witnesses (ns.map (fun n => n.bag.card))) w ns
  omega

mutual
theorem sz_processRun_le (v : ℕ) : ∀ (pre : Option CT.Cut) (w : CT.WPlan) (r : AR),
    sz (processRun v pre w r) ≤ 8 * sz r + 18 * wn w
  | pre, .endAt c, .run S ns ks => by
    have h := sz_processRun_aux v pre (.endAt c) S ns ks
    rw [processRun_eq]
    simp only [wn, sz_ar]
    rw [processRun_eq] at h
    simp only [AR.chain] at h
    omega
  | pre, .whole ps, .run S ns ks => by
    have h := sz_processRun_aux v pre (.whole ps) S ns ks
    have hk := sz_applyKids_le v ps ks
    rw [processRun_eq]
    simp only [wn, sz_ar]
    rw [processRun_eq] at h
    simp only [AR.chain] at h
    omega
theorem sz_applyKids_le (v : ℕ) : ∀ (ps : List (Option CT.WPlan)) (ks : List AR),
    sz (applyKids v ps ks) ≤ 8 * sz ks + 18 * wnL ps
  | [], ks => by simp only [applyKids, wnL]; omega
  | p :: ps, [] => by simp [applyKids, sz_cons]; have := sz_pos ([] : List AR); omega
  | p :: ps, k :: ks => by
    have h1 := sz_applyOpt_le v p k
    have h2 := sz_applyKids_le v ps ks
    simp only [applyKids, wnL, sz_cons]
    omega
theorem sz_applyOpt_le (v : ℕ) : ∀ (p : Option CT.WPlan) (k : AR),
    sz (applyOpt v p k) ≤ 8 * sz k + 18 * wnO p
  | none, k => by simp only [applyOpt, wnO]; omega
  | some p, k => by
    have := sz_processRun_le v none p k
    simp only [applyOpt, wnO]; exact this
end

mutual
theorem wn_le_sz : ∀ w : CT.WPlan, wn w ≤ sz w
  | .endAt c => by simp [wn, sz_pos]; have := sz_pos (CT.WPlan.endAt c); omega
  | .whole ps => by
    have := wnL_le_sz ps
    have h : sz (CT.WPlan.whole ps) = sz ps + 2 := by simp only [sz, toVal_wp_whole, Val.size]; omega
    simp only [wn]; omega
theorem wnL_le_sz : ∀ ps : List (Option CT.WPlan), wnL ps ≤ sz ps
  | [] => by simp [wnL]
  | p :: ps => by
    have := wnO_le_sz p
    have := wnL_le_sz ps
    simp only [wnL, sz_cons]; omega
theorem wnO_le_sz : ∀ p : Option CT.WPlan, wnO p ≤ sz p
  | none => by simp [wnO]
  | some p => by
    have := wn_le_sz p
    simp only [wnO, sz_some]; omega
end

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem mapP1_runs (o : Option ℕ) (hB : 1 < B) (ho : ∀ e, o = some e → e + 2 < B) :
    Runs Δ' B fMapP1 [toVal o] (toVal (o.map (· + 1))) 12 := by
  refine Runs.mk (hΔ _ _ Δ_mapP1) ?_
  cases o with
  | none =>
    simp only [Option.map_none]
    ev_start
    · ev_run
    · omega
  | some e =>
    have := ho e rfl
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · omega

theorem endStep_runs (y wp : List ℕ) (w : CT.WPlan) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s)
    (hwp : wp.length ≤ s) (hns : sz ns ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fEndStep [toVal y, toVal wp, toVal w, toVal ns] (toVal (endStepL y wp w ns)) (100 * s + 440) := by
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  cases w with
  | endAt c =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp c ns s hy hwp hns (by omega)
    refine Runs.mk (hΔ _ _ Δ_endStep) ?_
    simp only [endStepL, toVal_wp_endAt, toVal_pair, toVal_some]
    ev_start
    · ev_run
    · omega
  | whole ps =>
    refine Runs.mk (hΔ _ _ Δ_endStep) ?_
    simp only [endStepL, toVal_wp_whole, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega

theorem preStep_runs (y wp : List ℕ) (pre : Option CT.Cut) (endS : List CNode × Option ℕ) (s : ℕ)
    (hy : y.length ≤ s) (hwp : wp.length ≤ s) (hL : ∀ e ∈ wp, e ≤ s) (hE : sz endS.1 ≤ s)
    (hE2 : ∀ e, endS.2 = some e → e ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fPreStep [toVal y, toVal wp, toVal pre, toVal endS] (toVal (preStepL y wp pre endS))
      (100 * s + 500) := by
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  have hkm : fMapP1 < B := lt_of_bnd hB (by decide)
  have hB1 : 1 < B := by omega
  cases pre with
  | none =>
    refine Runs.mk (hΔ _ _ Δ_preStep) ?_
    simp only [preStepL, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega
  | some c =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp c endS.1 s hy hwp hE (by omega)
    have h2 := cutAt_snd_le y wp s hL c endS.1
    have h3 := mapP1_runs hΔ B endS.2 hB1 (fun e he => by have := hE2 e he; omega)
    refine Runs.mk (hΔ _ _ Δ_preStep) ?_
    cases c with
    | t1 f =>
      simp only [preStepL, toVal_pair, toVal_some, toVal_cut_t1, CT.Cut.isT1, if_true]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    | t2 f =>
      simp only [preStepL, toVal_pair, toVal_some, toVal_cut_t2, CT.Cut.isT1, Bool.false_eq_true, if_false]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega

omit hΔ in
theorem length_witnesses_le (a : List ℕ) : (witnesses a).length ≤ a.length := by
  have := E1B.length_witAux_le a [] 0
  simpa [witnesses] using this

mutual
theorem processRun_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (pre : Option CT.Cut) (w : CT.WPlan) (r : AR), sz r ≤ s →
    Runs Δ' B fProcessRun [toVal v, toVal pre, toVal w, toVal r] (toVal (processRun v pre w r))
      (cPR s * wn w)
  | pre, .endAt c, .run S ns ks, hr => by
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hlen := length_le_sz ns
    have hc4 := sz_chain_ge ns
    have hB1 : 1 < B := by omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hB3 : 3000 + 400 * ((2 * s + 3) + 1) < B := by omega
    rw [processRun_eq]
    simp only [wn]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hL : ∀ e ∈ witnesses sizes, e ≤ s := fun e he => le_trans (witnesses_le sizes e he) (by omega)
    have hcards := cards_runs hΔA B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hend := endStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns s hy hwpl hns hB2
    have hE := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns
    have hE2 := endStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL (.endAt c) ns
    generalize hend' : endStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.endAt c) ns = endS at hend hE hE2 ⊢
    have hpre' := preStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS (2 * s + 3) (by omega) (by omega)
      (fun e he => by have := hL e he; omega) (by omega) (fun e he => by have := hE2 e he; omega) hB3
    have hS1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS
    have hS2 := preStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL pre endS hE2
    generalize hpre'' : preStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS = preS at hpre' hS1 hS2 ⊢
    have hadd := addV_runs (Ext.trans ext1 hΔ) B v preS.2.1 preS.2.2 preS.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fEndStep < B := lt_of_bnd hB2 (by decide)
    have hk3 : fPreStep < B := lt_of_bnd hB2 (by decide)
    have hk4 : fAddV < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    refine Runs.mk (hΔ _ _ Δ_processRun) ?_
    simp only [toVal_ar, toVal_wp_endAt]
    ev_start
    · ev_run
    · omega
  | pre, .whole ps, .run S ns ks, hr => by
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hks : sz ks ≤ s := by have := sz_ks_lt S ns ks; omega
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hlen := length_le_sz ns
    have hlk := length_le_sz ks
    have hc4 := sz_chain_ge ns
    have hB1 : 1 < B := by omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hB3 : 3000 + 400 * ((2 * s + 3) + 1) < B := by omega
    have hK := applyKids_runs s hB v ps ks hks
    rw [processRun_eq]
    simp only [wn]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hL : ∀ e ∈ witnesses sizes, e ≤ s := fun e he => le_trans (witnesses_le sizes e he) (by omega)
    have hcards := cards_runs hΔA B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hend := endStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns s hy hwpl hns hB2
    simp only [toVal_wp_whole] at hend
    have hE := sz_endStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns
    have hE2 := endStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL (.whole ps) ns
    generalize hend' : endStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) (.whole ps) ns = endS at hend hE hE2 ⊢
    have hpre' := preStep_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS (2 * s + 3) (by omega) (by omega)
      (fun e he => by have := hL e he; omega) (by omega) (fun e he => by have := hE2 e he; omega) hB3
    have hS1 := sz_preStep_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS
    have hS2 := preStep_snd_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) s hL pre endS hE2
    generalize hpre'' : preStepL (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) pre endS = preS at hpre' hS1 hS2 ⊢
    have hadd := addV_runs (Ext.trans ext1 hΔ) B v preS.2.1 preS.2.2 preS.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fEndStep < B := lt_of_bnd hB2 (by decide)
    have hk3 : fPreStep < B := lt_of_bnd hB2 (by decide)
    have hk4 : fAddV < B := lt_of_bnd hB2 (by decide)
    have hk5 : fApplyKids < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    have e : cPR s * (1 + wnL ps) = cPR s + cPR s * wnL ps := by ring
    refine Runs.mk (hΔ _ _ Δ_processRun) ?_
    simp only [toVal_ar, toVal_wp_whole]
    ev_start
    · ev_run
    · rw [e]; omega

theorem applyKids_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (ps : List (Option CT.WPlan)) (ks : List AR), sz ks ≤ s →
    Runs Δ' B fApplyKids [toVal v, toVal ps, toVal ks] (toVal (applyKids v ps ks))
      (cPR s * wnL ps + 60 * ks.length + 8)
  | [], ks, hks => by
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids, wnL]
    ev_start
    · ev_run
    · omega
  | p :: ps, [], hks => by
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids]
    ev_start
    · ev_run
    · omega
  | p :: ps, k :: ks, hks => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks' : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := applyOpt_runs s hB v p k hk
    have h2 := applyKids_runs s hB v ps ks hks'
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fApplyOpt < B := lt_of_bnd hB2 (by decide)
    have hk2 : fApplyKids < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyKids) ?_
    simp only [applyKids, wnL, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · have e : cPR s * (wnO p + wnL ps) = cPR s * wnO p + cPR s * wnL ps := by ring
      rw [e]; omega

theorem applyOpt_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) :
    ∀ (p : Option CT.WPlan) (k : AR), sz k ≤ s →
    Runs Δ' B fApplyOpt [toVal v, toVal p, toVal k] (toVal (applyOpt v p k)) (cPR s * wnO p + 20)
  | none, k, hk => by
    refine Runs.mk (hΔ _ _ Δ_applyOpt) ?_
    simp only [applyOpt, wnO]
    ev_start
    · ev_run
    · omega
  | some p, k, hk => by
    have h1 := processRun_runs s hB v none p k hk
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fProcessRun < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyOpt) ?_
    simp only [applyOpt, wnO, toVal_some]
    ev_start
    · ev_run
    · omega

end

end proofs
end E5C2
end Lax117284Proofs.Treewidth.Fun
