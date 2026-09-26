import Lax117284Proofs.Bipartite.Ram2.SymmPrefix

/-!
The symmetrized word built in `a`, second half: the fill pass — for every slot `(u, j)` the
value (the target for a left row, `u` for a right row) is written at the cursor of its
destination. After the pass `a` holds `sx x` (`ArrOK (sx x)`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The fill pass -/

/-- The invariant of the fill pass, over the slots `P` visited so far. -/
structure FillInv (x : List ℕ) (P : List (ℕ × ℕ)) (σ : Env) : Prop where
  hfixed : FixedA x σ
  hlenP : (σ.arrs "pos").length = nw x
  hpos : ∀ l < nw x, (σ.arrs "pos").getD l 0 = offS x l + (seg x l P).length
  hseg : ∀ l < nw x, ∀ k < (seg x l P).length,
    (σ.arrs "a").getD (3 + Vw x + offS x l + k) 0 = (seg x l P).getD k 0

theorem FillInv.setVar {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : FillInv x P σ) (y : String)
    (v : ℕ) : FillInv x P (σ.setVar y v) :=
  ⟨h.hfixed.congr rfl, h.hlenP, h.hpos, h.hseg⟩

/-- The segment of a slot's destination is not yet full when the slot is reached. -/
theorem seg_length_lt_deg (x : List ℕ) {P Q : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (hpre : allPairs x = P ++ [p] ++ Q) :
    (seg x (dest x p) P).length < deg x (dest x p) := by
  have hpre' : allPairs x = (P ++ [p]) ++ Q := by rw [hpre]
  have := length_seg_le x (l := dest x p) hpre'
  rw [seg_append, seg_single, if_pos rfl, List.length_append, List.length_singleton] at this
  omega

/-- **One slot placed.** -/
theorem FillInv.step {x : List ℕ} {P Q : List (ℕ × ℕ)} {σ : Env} (hw : WellFormed x)
    (h : FillInv x P σ) (p : ℕ × ℕ) (hpre : allPairs x = P ++ [p] ++ Q) (hd : dest x p < nw x) :
    FillInv x (P ++ [p])
      ((σ.setArr "a" (3 + Vw x + (offS x (dest x p) + (seg x (dest x p) P).length)) (val x p)).setArr
        "pos" (dest x p) (offS x (dest x p) + (seg x (dest x p) P).length + 1)) := by
  have hoffn := wf_offS_n hw
  have hxlen := wf_len hw
  set d := dest x p with hddef
  set k := (seg x d P).length with hkdef
  have hpre' : allPairs x = (P ++ [p]) ++ Q := by rw [hpre]
  have hpreP : allPairs x = P ++ ([p] ++ Q) := by rw [hpre, List.append_assoc]
  have hlenP' : ∀ l, (seg x l (P ++ [p])).length ≤ deg x l := fun l => length_seg_le x hpre'
  have hsegle : ∀ l, (seg x l P).length ≤ deg x l := fun l => length_seg_le x hpreP
  have hsegd : seg x d (P ++ [p]) = seg x d P ++ [val x p] := by
    rw [seg_append, seg_single, if_pos rfl]
  have hsego : ∀ l, l ≠ d → seg x l (P ++ [p]) = seg x l P := fun l hl => by
    rw [seg_append, seg_single, if_neg (Ne.symm hl), List.append_nil]
  have hk : k < deg x d := seg_length_lt_deg x hpre
  have hkE : offS x d + k < offS x (nw x) := by
    have := offS_succ_of_lt x hd; have := offS_le_n x (d + 1); omega
  have hlenA := h.hfixed.len
  have hlenP := h.hlenP
  refine ⟨?_, by simp [h.hlenP], fun l hl => ?_, fun l hl k' hk' => ?_⟩
  · refine (h.hfixed.setTgt hw (s := offS x d + k) (v := val x p) (by omega)).congr ?_
    simp
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    by_cases hld : l = d
    · subst hld
      rw [getD_set_self (by omega), hsegd, List.length_append, List.length_singleton]
      omega
    · rw [getD_set_ne (Ne.symm hld), hsego l hld]; exact h.hpos l hl
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    by_cases hld : l = d
    · subst hld
      rw [hsegd, List.length_append, List.length_singleton] at hk'
      rcases Nat.lt_or_ge k' k with hlt | hge
      · rw [getD_set_ne (by omega), hsegd, getD_app_left hlt]
        exact h.hseg d hl k' hlt
      · have : k' = k := by omega
        subst this
        have hk0 : k - (seg x d P).length = 0 := by omega
        rw [show 3 + Vw x + offS x d + k = 3 + Vw x + (offS x d + k) by omega,
          getD_set_self (by omega), hsegd, getD_app_right (by omega), hk0]
        rfl
    · rw [hsego l hld] at hk' ⊢
      have hkl : k' < deg x l := lt_of_lt_of_le hk' (hsegle l)
      have hne : 3 + Vw x + (offS x d + k) ≠ 3 + Vw x + offS x l + k' := by
        rcases Nat.lt_or_ge l d with h1 | h1
        · have := offS_succ_of_lt x hl
          have := offS_mono x (i := l + 1) (i' := d) h1
          omega
        · have h2 : d < l := lt_of_le_of_ne h1 (Ne.symm hld)
          have := offS_succ_of_lt x hd
          have := offS_mono x (i := d + 1) (i' := l) h2
          omega
      rw [getD_set_ne hne]
      exact h.hseg l hl k' hk'

/-- `tt := t[3 + V + j]; if u < n then (a[3 + V + pos[u]] := tt; pos[u]++) else
(a[3 + V + pos[tt]] := u; pos[tt]++)`. -/
def fillThen : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var "u"))) (.var "tt"))
    (.store "pos" (.var "u") (.add (.get "pos" (.var "u")) (.lit 1)))

def fillElse : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var "tt"))) (.var "u"))
    (.store "pos" (.var "tt") (.add (.get "pos" (.var "tt")) (.lit 1)))

def fillBody : Com :=
  .seq (.assign "tt" (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))))
    (.ite (.lt (.var "u") (.var "n")) fillThen fillElse)

theorem fillBody_wvars : ∀ y ∈ fillBody.wvars, y ∉ ["u", "j", "je"] := by
  intro y hy
  simp [fillBody, fillThen, fillElse, Com.wvars] at hy
  subst hy; simp

theorem fillBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) {u j : ℕ}
    (hu : u < Vw x) (hj1 : offw x u ≤ j) (hj2 : j < offw x (u + 1)) :
    Spec B (fun σ => FillInv x (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j)
      fillBody (fun _ σ' => FillInv x (pairsAt x u (j + 1)) σ' ∧ Base x σ') 40 := by
  rintro σ ⟨hI, hb, hu', hj'⟩
  have h3 := (wellFormed_iff.1 hw).1
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlenT := hb.tab.length
  have hV := hb.V
  have hn := hb.n
  have hj2E : j < 2 * x.getD 1 0 := lt_of_lt_of_le hj2 (h3.off_le hu)
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have htV : tgtw x j < Vw x := h3.tgt_lt j hj2E
  have hcross := wf_cross hw hu hj1 hj2
  have hlenA := hI.hfixed.len
  have hlenP := hI.hlenP
  set p : ℕ × ℕ := (u, j) with hp
  have hstep : pairsAt x u (j + 1) = pairsAt x u j ++ [p] := pairsAt_succ x hj1
  obtain ⟨Q, hQ⟩ := pairsAt_prefix x u (j + 1) hu hj2
  rw [hstep] at hQ
  have hd : dest x p < nw x := wf_dest_lt hw (by rw [hQ]; simp)
  -- tt := t[3 + V + j]
  have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
    rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
  have hje : (Expr.var "j").evalB B σ = some j := by
    rw [← hj']; exact RunStep.eval_var B σ "j" (by rw [hj']; omega)
  have hidx := RunStep.eval_add B σ _ _ _ _
    (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hVe (by omega)) hje (by omega)
  have r1 := RunStep.assign B σ "tt" _ _ (RunStep.eval_get B σ "t" _ _ hidx (by omega)
    (by rw [hg]; omega))
  rw [hg] at r1
  set σ₁ := σ.setVar "tt" (tgtw x j) with hσ₁
  have hI₁ : FillInv x (pairsAt x u j) σ₁ := hI.setVar "tt" _
  have hb₁ : Base x σ₁ := hb.setVar "tt" (by simp) _
  have hu₁ : σ₁.vars "u" = u := by simp [hσ₁, hu']
  have hn₁ : σ₁.vars "n" = nw x := by simp [hσ₁, hn]
  have htt₁ : σ₁.vars "tt" = tgtw x j := by simp [hσ₁]
  have hV₁ : σ₁.vars "V" = Vw x := by simp [hσ₁, hV]
  have hue : (Expr.var "u").evalB B σ₁ = some u := by
    rw [← hu₁]; exact RunStep.eval_var B σ₁ "u" (by rw [hu₁]; omega)
  have hne : (Expr.var "n").evalB B σ₁ = some (nw x) := by
    rw [← hn₁]; exact RunStep.eval_var B σ₁ "n" (by rw [hn₁]; omega)
  have htte : (Expr.var "tt").evalB B σ₁ = some (tgtw x j) := by
    rw [← htt₁]; exact RunStep.eval_var B σ₁ "tt" (by rw [htt₁]; omega)
  have hVe₁ : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
    rw [← hV₁]; exact RunStep.eval_var B σ₁ "V" (by rw [hV₁]; omega)
  have hlenA₁ : (σ₁.arrs "a").length = x.length := by simp [hσ₁, hlenA]
  have hlenP₁ : (σ₁.arrs "pos").length = nw x := by simp [hσ₁, hlenP]
  -- the two stores, for a destination `d` held in `y` and a value `v` held in `z`
  have hplace : ∀ (y z : String) (d v : ℕ), σ₁.vars y = d → σ₁.vars z = v → d < nw x → v < B →
      (seg x d (pairsAt x u j)).length < deg x d →
      Run B (.seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.get "pos" (.var y))) (.var z))
        (.store "pos" (.var y) (.add (.get "pos" (.var y)) (.lit 1)))) σ₁
        ((σ₁.setArr "a" (3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length)) v).setArr
          "pos" d (offS x d + (seg x d (pairsAt x u j)).length + 1)) 20 := by
    intro y z d v hy hz hdn hvB hkd'
    have hoff1 := offS_succ_of_lt x hdn
    have hoff2 := offS_le_n x (d + 1)
    have hposd : (σ₁.arrs "pos").getD d 0 = offS x d + (seg x d (pairsAt x u j)).length := by
      simp only [hσ₁, arrs_setVar]; exact hI.hpos d hdn
    have hkd : (seg x d (pairsAt x u j)).length ≤ deg x d := length_seg_le x (by rw [hQ, List.append_assoc])
    have hposB : offS x d + (seg x d (pairsAt x u j)).length + 1 < B := by
      have := offS_succ_of_lt x hdn; have := offS_le_n x (d + 1); omega
    have hye : (Expr.var y).evalB B σ₁ = some d := by
      rw [← hy]; exact RunStep.eval_var B σ₁ y (by rw [hy]; omega)
    have hze : (Expr.var z).evalB B σ₁ = some v := by
      rw [← hz]; exact RunStep.eval_var B σ₁ z (by rw [hz]; exact hvB)
    have hgp : (Expr.get "pos" (.var y)).evalB B σ₁ =
        some (offS x d + (seg x d (pairsAt x u j)).length) := by
      rw [← hposd]
      exact RunStep.eval_get B σ₁ "pos" _ _ hye (by omega) (by rw [hposd]; omega)
    have hidxA := RunStep.eval_add B σ₁ _ _ _ _
      (RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 3 σ₁ (by omega)) hVe₁ (by omega)) hgp
      (by omega)
    have rA := RunStep.store B σ₁ "a" _ _ _ _ hidxA hze (by
      show 3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length) < (σ₁.arrs "a").length
      have h1 := offS_succ_of_lt x hdn
      have h2 := offS_le_n x (d + 1)
      omega)
    set σ₂ := σ₁.setArr "a" (3 + Vw x + (offS x d + (seg x d (pairsAt x u j)).length)) v with hσ₂
    have hye₂ : (Expr.var y).evalB B σ₂ = some d := by simpa [hσ₂] using hye
    have hposd₂ : (σ₂.arrs "pos").getD d 0 = offS x d + (seg x d (pairsAt x u j)).length := by
      simpa [hσ₂] using hposd
    have hgp₂ : (Expr.get "pos" (.var y)).evalB B σ₂ =
        some (offS x d + (seg x d (pairsAt x u j)).length) := by
      rw [← hposd₂]
      exact RunStep.eval_get B σ₂ "pos" _ _ hye₂ (by simp [hσ₂]; omega) (by rw [hposd₂]; omega)
    have hsum := RunStep.eval_add B σ₂ _ _ _ _ hgp₂ (RunStep.eval_lit B 1 σ₂ (by omega)) hposB
    have rP := RunStep.store B σ₂ "pos" _ _ _ _ hye₂ hsum (by simp [hσ₂]; omega)
    exact (rA.seq rP).mono (by simp)
  by_cases hun : u < nw x
  · have hc := RunStep.cond_lt_true B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = u := by unfold dest; simp [hp, hun]
    have hval : val x p = tgtw x j := by unfold val; simp [hp, hun]
    have rr := hplace "u" "tt" u (tgtw x j) hu₁ htt₁ hun (by omega)
      (by have := seg_length_lt_deg x hQ; rwa [hdest] at this)
    have rite := RunStep.ite_true B _ fillThen fillElse σ₁ _ _ hc rr
    refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setArr (by decide) _ _).setArr (by decide) _ _⟩
    rw [hstep]
    have := hI₁.step hw p hQ hd
    rw [hdest, hval] at this
    exact this
  · have hc := RunStep.cond_lt_false B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = tgtw x j := by unfold dest; simp [hp, hun]
    have hval : val x p = u := by unfold val; simp [hp, hun]
    have htn : tgtw x j < nw x := by rw [hdest] at hd; exact hd
    have rr := hplace "tt" "u" (tgtw x j) u htt₁ hu₁ htn (by omega)
      (by have := seg_length_lt_deg x hQ; rwa [hdest] at this)
    have rite := RunStep.ite_false B _ fillThen fillElse σ₁ _ _ hc rr
    refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setArr (by decide) _ _).setArr (by decide) _ _⟩
    rw [hstep]
    have := hI₁.step hw p hQ hd
    rw [hdest, hval] at this
    exact this

/-- **The fill pass.** -/
def fillPass : Com := rowIter fillBody

/-- **After the fill pass, `a` holds the symmetrized word.** -/
theorem fillPass_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ FixedA x σ ∧ PosOK x σ) fillPass
      (fun _ σ' => Base x σ' ∧ ArrOK (sx x) σ')
      ((40 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have h3 := (wellFormed_iff.1 hw).1
  have hspec := rowIter_spec (Inv := FillInv x) h3 hB fillBody 40 fillBody_wvars
    (fun P σ y v _ hI => hI.setVar y v) (fun u j hu hj1 hj2 => fillBody_spec hw hB hu hj1 hj2)
  refine hspec.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hf, hlenP, hpos⟩
    exact ⟨⟨hf, hlenP, fun l hl => by rw [hpos l hl, seg_nil]; rfl,
      fun l hl k hk => by rw [seg_nil] at hk; simp at hk⟩, hb⟩
  · rintro σ σ' - ⟨hI, hb⟩
    refine ⟨hb, ?_⟩
    have hxlen := wf_len hw
    have hoffn := wf_offS_n hw
    have hlen' := wf_length_sx hw
    unfold ArrOK
    rw [hlen', ← hI.hfixed.len]
    refine List.ext_getElem (by simp) (fun t ht₁ ht₂ => ?_)
    have ht : t < x.length := by rwa [hI.hfixed.len] at ht₁
    have e1 : (σ'.arrs "a")[t] = (σ'.arrs "a").getD t 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht₁]; rfl
    have e2 : (arrOf (σ'.arrs "a").length (fun t => (sx x).getD t 0))[t] = (sx x).getD t 0 := by
      have := getD_arrOf (n := (σ'.arrs "a").length) (fun t => (sx x).getD t 0) ht₁
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht₂] at this
      exact this
    rw [e1, e2]
    -- by cases on the position
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · interval_cases t
      · rw [hI.hfixed.h0]; rfl
      · rw [hI.hfixed.h1]; rfl
    rcases Nat.lt_or_ge t (3 + Vw x) with h3' | h3'
    · have e : t = 2 + (t - 2) := by omega
      rw [e, hI.hfixed.off (t - 2) (by omega), sx_off x (by omega)]
    rcases Nat.lt_or_ge t (3 + Vw x + 2 * x.getD 1 0) with h4 | h4
    · have e : t = 3 + Vw x + (t - 3 - Vw x) := by omega
      have hs : t - 3 - Vw x < offS x (nw x) := by omega
      rw [e, sx_tgt x hs]
      obtain ⟨l, hl, hl1, hl2⟩ := exists_owner x hs
      rw [offS_succ_of_lt x hl] at hl2
      have e2 : t - 3 - Vw x = offS x l + (t - 3 - Vw x - offS x l) := by omega
      rw [e2, tgtS_seg x hl (by omega), ← Nat.add_assoc]
      exact hI.hseg l hl _ (by unfold deg at *; omega)
    · have e : t = 3 + Vw x + 2 * x.getD 1 0 := by omega
      rw [e, hI.hfixed.last, ← hoffn, sx_last]

end Lax117284Proofs.Bipartite.Ram2
