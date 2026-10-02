import Lax117284Proofs.Treewidth.Fun.E5C2

/-!
# WP E5 (layer C3): `applyAt`, `applyRun`, `applyPlan`

Ids `490 …`:

| id | function | arguments |
|---|---|---|
| 490 `fAttCut` | the cut of `applyAt` for an attach plan | `[y, wp, c, ns]` |
| 491 `fApplyAt` | `applyAt` | `[v, p, r]` |
| 492 `fModifyRun` | `modifyNth (applyRun v p rest) i` | `[v, p, rest, i, ks]` |
| 493 `fApplyRun` | `applyRun` | `[v, p, path, r]` |
| 494 `fApplyPlan` | `applyPlan` | `[v, N, Bd, path, p, t]` |

`applyPlan v N Bd path p t = (applyRun v p path (analyze Bd t)).toRT`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5C3

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1 E5C2

abbrev fAttCut : ℕ := 490
abbrev fApplyAt : ℕ := 491
abbrev fModifyRun : ℕ := 492
abbrev fApplyRun : ℕ := 493
abbrev fApplyPlan : ℕ := 494

/-! ## the Lean side -/

/-- the cut of `applyAt` for an attach plan -/
def attCut (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) : List CNode × ℕ :=
  match c with
  | none => (ns, ns.length - 1)
  | some ct => cutAt y wp ct ns

theorem applyAt_att (v : ℕ) (c : Option CT.Cut) (chain : List (Finset ℕ)) (M S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    applyAt v (.att c chain M) (.run S ns ks) =
      .run S (addJunk (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
          (witnesses (ns.map (fun n => n.bag.card))) c ns).2 (branchRT v chain M)
        (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
          (witnesses (ns.map (fun n => n.bag.card))) c ns).1) ks := by
  cases c <;> simp only [applyAt, attCut]

/-- weight of a plan -/
def wnP : CT.Plan → ℕ
  | .att _ _ _ => 1
  | .top _ w => wn w

/-- local cost of `applyAt` -/
def cAA (s : ℕ) (p : CT.Plan) : ℕ := cPR s * wnP p + 100 * (sz p + 1)

/-- size growth constant of a plan -/
def gP (p : CT.Plan) : ℕ := 18 * sz p + 11

/-! ## the terms -/

/-- `[y, wp, c, ns]` -/
def attCutTm : Tm :=
  .ite (.isNat (V 2))
    (.cons (V 3) (.sub (.call fLength [V 3]) (.lit 1)))
    (.call fCutAt [V 0, V 1, .snd (V 2), V 3])

/-- `[v, p, r]` -/
def applyAtTm : Tm :=
  .ite (.eq (.fst (V 1)) (.lit 1))
    (.letE (.call fCards [.fst (.snd (V 2))])
      (.letE (.call E1A.fTypical [V 0])
        (.letE (.call E1B.fWitnesses [V 1])
          (.letE (.call fAttCut [V 1, V 0, .fst (.snd (V 4)), .fst (.snd (V 5))])
            (.cons (.fst (V 6))
              (.cons (.call fAddJunk [.snd (V 0),
                        .call fBranchRT [V 4, .fst (.snd (.snd (V 5))), .snd (.snd (.snd (V 5)))], .fst (V 0)])
                (.snd (.snd (V 6)))))))))
    (.call fProcessRun [V 0, .fst (.snd (V 1)), .snd (.snd (V 1)), V 2])

/-- `[v, p, rest, i, ks]` -/
def modifyRunTm : Tm :=
  .ite (.isNat (V 4)) (V 4)
    (.ite (.eq (V 3) (.lit 0))
      (.cons (.call fApplyRun [V 0, V 1, V 2, .fst (V 4)]) (.snd (V 4)))
      (.cons (.fst (V 4)) (.call fModifyRun [V 0, V 1, V 2, .sub (V 3) (.lit 1), .snd (V 4)])))

/-- `[v, p, path, r]` -/
def applyRunTm : Tm :=
  .ite (.isNat (V 2)) (.call fApplyAt [V 0, V 1, V 3])
    (.cons (.fst (V 3))
      (.cons (.fst (.snd (V 3)))
        (.call fModifyRun [V 0, V 1, .snd (V 2), .fst (V 2), .snd (.snd (V 3))])))

/-- `[v, N, Bd, path, p, t]` -/
def applyPlanTm : Tm :=
  .call E5A.fToRT [.call fApplyRun [V 0, V 4, V 3, .call E5B.fAnalyze [V 2, V 5]]]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 490 => some attCutTm | 491 => some applyAtTm | 492 => some modifyRunTm | 493 => some applyRunTm
  | 494 => some applyPlanTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5C2.Δ 490 tbl

abbrev size : ℕ := 495

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 495 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h490 : 490 ≤ f := by omega
    simp only [h490, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext2 : E5C2.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5C2.Δ_lt h; simp [E5C2.size] at this; omega)
theorem ext1 : E5C1.Δ ⊑ Δ := Ext.trans E5C2.ext1 ext2
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5C2.extB ext2
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5C2.extA ext2
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5C2.extE1 ext2

theorem Δ_attCut : Δ fAttCut = some attCutTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fAttCut by decide)]; rfl
theorem Δ_applyAt : Δ fApplyAt = some applyAtTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyAt by decide)]; rfl
theorem Δ_modifyRun : Δ fModifyRun = some modifyRunTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fModifyRun by decide)]; rfl
theorem Δ_applyRun : Δ fApplyRun = some applyRunTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyRun by decide)]; rfl
theorem Δ_applyPlan : Δ fApplyPlan = some applyPlanTm := by
  simp [Δ, layerΔ_ge tbl (show 490 ≤ fApplyPlan by decide)]; rfl

/-! ## sizes -/

theorem sz_attCut_le (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) :
    sz (attCut y wp c ns).1 ≤ 2 * sz ns + 3 := by
  cases c with
  | none => simp only [attCut]; omega
  | some ct => simp only [attCut]; exact sz_cutAt_le y wp ct ns

theorem sz_applyAt_le (v : ℕ) (p : CT.Plan) (r : AR) : sz (applyAt v p r) ≤ 8 * sz r + gP p := by
  cases p with
  | att c chain M =>
    obtain ⟨S, ns, ks⟩ := r
    rw [applyAt_att]
    have h1 := sz_attCut_le (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns
    have h2 := sz_addJunk_le (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns).2 (branchRT v chain M)
      (attCut (Lax117284Proofs.Treewidth.Seq.typical (ns.map (fun n => n.bag.card)))
      (witnesses (ns.map (fun n => n.bag.card))) c ns).1
    have h3 := sz_branchRT_le v chain M
    have h4 : sz (CT.Plan.att c chain M) = sz c + sz chain + sz M + 4 := sz_plan_att c chain M
    simp only [gP, sz_ar]
    omega
  | top pre w =>
    have h1 := sz_processRun_le v pre w r
    have h2 := wn_le_sz w
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    simp only [applyAt, gP]
    omega

theorem sz_modifyNth_le (f : AR → AR) (G : ℕ) (hf : ∀ x, sz (f x) ≤ 8 * sz x + G) :
    ∀ (i : ℕ) (l : List AR), sz (modifyNth f i l) ≤ 8 * sz l + G
  | _, [] => by simp only [modifyNth]; omega
  | 0, a :: l => by
    have := hf a
    simp only [modifyNth, sz_cons]; omega
  | i + 1, a :: l => by
    have := sz_modifyNth_le f G hf i l
    simp only [modifyNth, sz_cons]; omega

theorem sz_applyRun_le (v : ℕ) (p : CT.Plan) : ∀ (path : List ℕ) (r : AR), sz (applyRun v p path r) ≤ 8 * sz r + gP p
  | [], r => by simp only [applyRun]; exact sz_applyAt_le v p r
  | i :: rest, .run S ns ks => by
    have := sz_modifyNth_le (applyRun v p rest) (gP p) (fun x => sz_applyRun_le v p rest x) i ks
    simp only [applyRun, sz_ar]
    omega

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem attCut_runs (y wp : List ℕ) (c : Option CT.Cut) (ns : List CNode) (s : ℕ) (hy : y.length ≤ s)
    (hwp : wp.length ≤ s) (hns : sz ns ≤ s) (hB : 3000 + 400 * (s + 1) < B) :
    Runs Δ' B fAttCut [toVal y, toVal wp, toVal c, toVal ns] (toVal (attCut y wp c ns)) (100 * s + 460) := by
  have hE1 := Ext.trans extE1 hΔ
  have hlen := length_le_sz ns
  have hkc : fCutAt < B := lt_of_bnd hB (by decide)
  cases c with
  | none =>
    have h1 := Lib1.length_runs (l1 hE1) B ns (by omega)
    refine Runs.mk (hΔ _ _ Δ_attCut) ?_
    simp only [attCut, toVal_pair, toVal_none]
    ev_start
    · ev_run
    · omega
  | some ct =>
    have h1 := cutAt_runs (Ext.trans ext1 hΔ) B y wp ct ns s hy hwp hns (by omega)
    refine Runs.mk (hΔ _ _ Δ_attCut) ?_
    simp only [attCut, toVal_some]
    ev_start
    · ev_run
    · omega

theorem applyAt_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) (p : CT.Plan) (r : AR)
    (hr : sz r ≤ s) (hp : sz p ≤ s) :
    Runs Δ' B fApplyAt [toVal v, toVal p, toVal r] (toVal (applyAt v p r)) (cAA s p + 20) := by
  have hE1 := Ext.trans extE1 hΔ
  have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hB1 : 1 < B := by omega
  cases p with
  | top pre w =>
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    have hw := wn_le_sz w
    have h1 := processRun_runs (Ext.trans ext2 hΔ) B s hB v pre w r hr
    have hk : fProcessRun < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyAt) ?_
    simp only [applyAt, toVal_plan_top]
    ev_start
    · ev_run
    · unfold cAA; simp only [wnP]; omega
  | att c chain M =>
    obtain ⟨S, ns, ks⟩ := r
    have hns : sz ns ≤ s := by have := sz_c_lt S ns ks; omega
    have hlen := length_le_sz ns
    have hc4 := sz_chain_ge ns
    have h4 : sz (CT.Plan.att c chain M) = sz c + sz chain + sz M + 4 := sz_plan_att c chain M
    rw [applyAt_att]
    generalize hsizes : ns.map (fun n => n.bag.card) = sizes
    have hsl : sizes.length = ns.length := by rw [← hsizes]; simp
    have hy : (Lax117284Proofs.Treewidth.Seq.typical sizes).length ≤ s := le_trans (E5.typical_length_le sizes) (by omega)
    have hwpl : (witnesses sizes).length ≤ s := le_trans (length_witnesses_le sizes) (by omega)
    have hcards := cards_runs (Ext.trans extA hΔ) B ns (by omega)
    rw [hsizes] at hcards
    have htyp := E1A.typical_runs (eA hE1) B hB1 sizes
    have hwit := E1B.witnesses_runs (eB hE1) B sizes (by omega)
    have hatt := attCut_runs hΔ B (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns s hy hwpl hns hB2
    have hSz := sz_attCut_le (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns
    generalize hat' : attCut (Lax117284Proofs.Treewidth.Seq.typical sizes) (witnesses sizes) c ns = cr at hatt hSz ⊢
    have hbr := E5C1.branchRT_runs (Ext.trans ext1 hΔ) B v chain M (by omega)
    have hadd := E5C1.addJunk_runs (Ext.trans ext1 hΔ) B cr.2 (branchRT v chain M) cr.1 (by omega)
    have hk1 : fCards < B := lt_of_bnd hB2 (by decide)
    have hk2 : fAttCut < B := lt_of_bnd hB2 (by decide)
    have hk3 : fAddJunk < B := lt_of_bnd hB2 (by decide)
    have hk4 : fBranchRT < B := lt_of_bnd hB2 (by decide)
    have hT : (sizes.length + 1) ^ 3 ≤ (s + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hT1 : s + 1 ≤ (s + 1) ^ 3 := le_pw (by omega) (by omega)
    have hcp : cPR s = 3000 * (s + 1) ^ 3 := rfl
    refine Runs.mk (hΔ _ _ Δ_applyAt) ?_
    simp only [toVal_plan_att, toVal_ar]
    ev_start
    · ev_run
    · unfold cAA; simp only [wnP]; omega

theorem applyRun_runs (s : ℕ) (hB : 3000 + 400 * (8 * s + 16) < B) (v : ℕ) (p : CT.Plan) (hp : sz p ≤ s) :
    ∀ (path : List ℕ) (r : AR), sz r ≤ s →
    Runs Δ' B fApplyRun [toVal v, toVal p, toVal path, toVal r] (toVal (applyRun v p path r))
      (path.length * (20 * s + 60) + cAA s p + 40)
  | [], r, hr => by
    have h1 := applyAt_runs hΔ B s hB v p r hr hp
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk : fApplyAt < B := lt_of_bnd hB2 (by decide)
    refine Runs.mk (hΔ _ _ Δ_applyRun) ?_
    simp only [applyRun, toVal_nil, List.length_nil]
    ev_start
    · ev_run
    · omega
  | i :: rest, .run S ns ks, hr => by
    have ih := applyRun_runs s hB v p hp rest
    have hks : sz ks ≤ s := by have := sz_ks_lt S ns ks; omega
    have hB2 : 3000 + 400 * (s + 1) < B := by omega
    have hk1 : fModifyRun < B := lt_of_bnd hB2 (by decide)
    have hk2 : fApplyRun < B := lt_of_bnd hB2 (by decide)
    have hmod : ∀ (l : List AR) (i : ℕ), sz l ≤ s →
        Runs Δ' B fModifyRun [toVal v, toVal p, toVal rest, toVal i, toVal l]
          (toVal (modifyNth (applyRun v p rest) i l))
          (20 * l.length + 20 + (rest.length * (20 * s + 60) + cAA s p + 40)) := by
      intro l
      induction l with
      | nil =>
        intro i _
        refine Runs.mk (hΔ _ _ Δ_modifyRun) ?_
        simp only [modifyNth]
        ev_start
        · ev_run
        · omega
      | cons k l ihl =>
        intro i hl
        have hk : sz k ≤ s := by have := sz_head_lt k l; omega
        have hl' : sz l ≤ s := by have := sz_tail_lt k l; omega
        refine Runs.mk (hΔ _ _ Δ_modifyRun) ?_
        cases i with
        | zero =>
          have h1 := ih k hk
          simp only [modifyNth, toVal_cons]
          ev_start
          · ev_run
          · simp only [List.length_cons]; omega
        | succ i =>
          have h1 := ihl i hl'
          simp only [modifyNth, toVal_cons]
          ev_start
          · ev_run
          · simp only [List.length_cons]; omega
    have h1 := hmod ks i hks
    have hl := length_le_sz ks
    have e : (rest.length + 1) * (20 * s + 60) = rest.length * (20 * s + 60) + (20 * s + 60) := by ring
    refine Runs.mk (hΔ _ _ Δ_applyRun) ?_
    simp only [applyRun, toVal_ar, toVal_cons, List.length_cons]
    ev_start
    · ev_run
    · rw [e]; omega

omit hΔ in
theorem wnP_le_sz (p : CT.Plan) : wnP p ≤ sz p := by
  cases p with
  | att c chain M => simp only [wnP]; have := sz_pos (CT.Plan.att c chain M); omega
  | top pre w =>
    have := wn_le_sz w
    have h4 : sz (CT.Plan.top pre w) = sz pre + sz w + 3 := sz_plan_top pre w
    simp only [wnP]; omega

/-- cost of `applyPlan` (`ck6 = E.cKey (6 s)`) -/
def cApplyPlan (s ck6 : ℕ) : ℕ :=
  E5B.cA s ck6 * s + s * (100 * s + 60) + (cPR (5 * s) * s + 100 * (s + 1) + 40) +
    100 * (58 * s + 11 + 1) * (58 * s + 11) + 100

theorem applyPlan_runs (E : Ext5 Δ') (v : ℕ) (N Bd : Finset ℕ) (path : List ℕ) (p : CT.Plan) (t : RT) (s : ℕ)
    (hBd : sz Bd ≤ s) (ht : sz t ≤ s) (hp : sz p ≤ s) (hpath : path.length ≤ s)
    (hB : 20000 + 20000 * (s + 1) + E.cKey (6 * s) < B) :
    Runs Δ' B fApplyPlan [toVal v, toVal N, toVal Bd, toVal path, toVal p, toVal t]
      (toVal (applyPlan v N Bd path p t)) (cApplyPlan s (E.cKey (6 * s))) := by
  have hana := E5B.analyze_runs (Ext.trans extB hΔ) B E Bd s hBd (by omega) t ht
  have hsa : sz (analyze Bd t) ≤ 5 * s := le_trans (E5B.sz_analyze_le Bd t) (by omega)
  have hrun := applyRun_runs hΔ B (5 * s) (by omega) v p (by omega) path (analyze Bd t) hsa
  have hszr := sz_applyRun_le v p path (analyze Bd t)
  have hszr' : sz (applyRun v p path (analyze Bd t)) ≤ 58 * s + 11 := by
    simp only [gP] at hszr; omega
  have hrt := E5A.toRT_runs (Ext.trans extA hΔ) B (58 * s + 11) (by omega) (applyRun v p path (analyze Bd t)) hszr'
  have hcnt := cnt_le_sz (applyRun v p path (analyze Bd t))
  have t1 : E5B.cA s (E.cKey (6 * s)) * t.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz t) ht)
  have t2 : path.length * (20 * (5 * s) + 60) ≤ s * (100 * s + 60) := by
    calc path.length * (20 * (5 * s) + 60) ≤ s * (20 * (5 * s) + 60) := Nat.mul_le_mul_right _ hpath
      _ = s * (100 * s + 60) := by ring
  have t3 : cAA (5 * s) p ≤ cPR (5 * s) * s + 100 * (s + 1) := by
    unfold cAA
    have := wnP_le_sz p
    have : cPR (5 * s) * wnP p ≤ cPR (5 * s) * s := Nat.mul_le_mul_left _ (by omega)
    omega
  have t4 : 100 * (58 * s + 11 + 1) * cnt (applyRun v p path (analyze Bd t)) ≤
      100 * (58 * s + 11 + 1) * (58 * s + 11) := Nat.mul_le_mul_left _ (by omega)
  have hB2 : 3000 + 400 * (s + 1) < B := by omega
  have hk1 : fApplyRun < B := lt_of_bnd hB2 (by decide)
  have hk2 : E5B.fAnalyze < B := lt_of_bnd hB2 (by decide)
  have hk3 : E5A.fToRT < B := lt_of_bnd hB2 (by decide)
  refine Runs.mk (hΔ _ _ Δ_applyPlan) ?_
  simp only [applyPlan]
  ev_start
  · ev_run
  · unfold cApplyPlan
    omega

end proofs
end E5C3
end Lax117284Proofs.Treewidth.Fun
