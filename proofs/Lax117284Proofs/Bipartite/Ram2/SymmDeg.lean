import Lax117284Proofs.Bipartite.Ram2.RowIter

/-!
The degree pass: for every slot `(u, j)` of the word in `t`, with target `tt`, check that the
edge crosses the split (`u < n ↔ n ≤ tt`), clearing `ok` otherwise, and count the slot for its
destination in `deg` (`u` for a left row, `tt` for a right row). After the pass `ok = 1` exactly
when every listed edge crosses the split — with the syntactic checks of `Validate.lean`, exactly
when the word is well formed — and then `deg` holds the degrees of the symmetrized word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

theorem getD_set_self {l : List ℕ} {i v : ℕ} (h : i < l.length) : (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

theorem getD_set_ne {l : List ℕ} {i j v : ℕ} (h : i ≠ j) : (l.set i v).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

/-- The slot crosses the split. -/
def Cross (x : List ℕ) (p : ℕ × ℕ) : Prop := p.1 < nw x ↔ nw x ≤ tgtw x p.2

/-- The invariant of the degree pass, over the slots `P` visited so far. -/
structure DegInv (x : List ℕ) (P : List (ℕ × ℕ)) (σ : Env) : Prop where
  okle : σ.vars "ok" ≤ 1
  okiff : σ.vars "ok" = 1 ↔ ∀ p ∈ P, Cross x p
  lenD : (σ.arrs "deg").length = nw x
  bd : ∀ l < nw x, (σ.arrs "deg").getD l 0 ≤ P.length
  deg : σ.vars "ok" = 1 → ∀ l < nw x, (σ.arrs "deg").getD l 0 = (seg x l P).length

theorem DegInv.setVar {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (y : String)
    (hy : y ≠ "ok") (v : ℕ) : DegInv x P (σ.setVar y v) := by
  have e : (σ.setVar y v).vars "ok" = σ.vars "ok" := by simp [Ne.symm hy]
  exact ⟨by rw [e]; exact h.okle, by rw [e]; exact h.okiff, h.lenD, h.bd, by rw [e]; exact h.deg⟩

/-- `tt := t[3 + V + j]; if u < n then (if tt < n then ok := 0); deg[u]++ else (if tt < n then
deg[tt]++ else ok := 0)`. -/
def degThen : Com :=
  .seq (.ite (.lt (.var "tt") (.var "n")) (.assign "ok" (.lit 0)) .skip)
    (.store "deg" (.var "u") (.add (.get "deg" (.var "u")) (.lit 1)))

def degElse : Com :=
  .ite (.lt (.var "tt") (.var "n"))
    (.store "deg" (.var "tt") (.add (.get "deg" (.var "tt")) (.lit 1)))
    (.assign "ok" (.lit 0))

def degBody : Com :=
  .seq (.assign "tt" (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))))
    (.ite (.lt (.var "u") (.var "n")) degThen degElse)

/-- Counting one slot for its destination. -/
theorem DegInv.count {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hd : dest x p < nw x) (hc : Cross x p) :
    DegInv x (P ++ [p]) (σ.setArr "deg" (dest x p) ((σ.arrs "deg").getD (dest x p) 0 + 1)) := by
  have hlen := h.lenD
  refine ⟨h.okle, ?_, by simp [hlen], fun l hl => ?_, fun hok l hl => ?_⟩
  · simp only [vars_setArr]
    rw [h.okiff]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro hall q hq
      rcases hq with hq | rfl
      · exact hall q hq
      · exact hc
    · intro hall q hq; exact hall q (Or.inl hq)
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [List.length_append, List.length_singleton]
    by_cases hld : l = dest x p
    · subst hld; rw [getD_set_self (by omega)]; have := h.bd _ hl; omega
    · rw [getD_set_ne (Ne.symm hld)]; have := h.bd l hl; omega
  · simp only [vars_setArr] at hok
    simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [seg_append, seg_single, List.length_append]
    by_cases hld : l = dest x p
    · subst hld
      rw [getD_set_self (by omega), if_pos rfl, h.deg hok _ hl]; rfl
    · rw [getD_set_ne (Ne.symm hld), if_neg (Ne.symm hld), h.deg hok l hl]; rfl

/-- Clearing the flag on a slot that does not cross. -/
theorem DegInv.fail {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hc : ¬ Cross x p) : DegInv x (P ++ [p]) (σ.setVar "ok" 0) := by
  refine ⟨by simp, ?_, h.lenD, fun l hl => ?_, fun hok => by simp at hok⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    constructor
    · intro h0; omega
    · intro hall; exact absurd (hall p (List.mem_append_right _ (List.mem_singleton_self p))) hc
  · simp only [arrs_setVar]
    rw [List.length_append]; have := h.bd l hl; omega

/-- Clearing the flag on a left-row slot that does not cross, then still counting it. -/
theorem DegInv.failCount {x : List ℕ} {P : List (ℕ × ℕ)} {σ : Env} (h : DegInv x P σ) (p : ℕ × ℕ)
    (hc : ¬ Cross x p) (hd : dest x p < nw x) :
    DegInv x (P ++ [p])
      ((σ.setVar "ok" 0).setArr "deg" (dest x p) ((σ.arrs "deg").getD (dest x p) 0 + 1)) := by
  have h1 := h.fail p hc
  have hlen := h.lenD
  refine ⟨by simp, by simpa using h1.okiff, by simp [hlen], fun l hl => ?_, fun hok => by simp at hok⟩
  simp only [arrs_setArr, arrs_setVar, String.reduceEq, ↓reduceIte]
  rw [List.length_append, List.length_singleton]
  by_cases hld : l = dest x p
  · subst hld; rw [getD_set_self (by omega)]; have := h.bd _ hl; omega
  · rw [getD_set_ne (Ne.symm hld)]; have := h.bd l hl; omega

theorem degBody_spec {x : List ℕ} (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) {u j : ℕ}
    (hu : u < Vw x) (hj1 : offw x u ≤ j) (hj2 : j < offw x (u + 1)) :
    Spec B (fun σ => DegInv x (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j)
      degBody (fun _ σ' => DegInv x (pairsAt x u (j + 1)) σ' ∧ Base x σ') 30 := by
  rintro σ ⟨hI, hb, hu', hj'⟩
  have hlen := h3.len
  have hlenT := hb.tab.length
  have hV := hb.V
  have hn := hb.n
  have hj2E : j < 2 * x.getD 1 0 := lt_of_lt_of_le hj2 (h3.off_le hu)
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have htV : tgtw x j < Vw x := h3.tgt_lt j hj2E
  have hnV := h3.nV
  have hlenD := hI.lenD
  have hPlen : (pairsAt x u j).length ≤ 2 * x.getD 1 0 := by
    obtain ⟨Q, hQ⟩ := pairsAt_prefix x u j hu (le_of_lt hj2)
    have := congrArg List.length hQ
    rw [List.length_append] at this
    have h2 : (allPairs x).length = 2 * x.getD 1 0 := by
      unfold allPairs; rw [length_pairsUpto x h3.off0 h3.mono _ le_rfl, h3.offV]
    omega
  set p : ℕ × ℕ := (u, j) with hp
  have hstep : pairsAt x u (j + 1) = pairsAt x u j ++ [p] := pairsAt_succ x hj1
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
  have hI₁ : DegInv x (pairsAt x u j) σ₁ := hI.setVar "tt" (by decide) _
  have hb₁ : Base x σ₁ := hb.setVar "tt" (by simp) _
  have hu₁ : σ₁.vars "u" = u := by simp [hσ₁, hu']
  have hn₁ : σ₁.vars "n" = nw x := by simp [hσ₁, hn]
  have htt₁ : σ₁.vars "tt" = tgtw x j := by simp [hσ₁]
  have hue : (Expr.var "u").evalB B σ₁ = some u := by
    rw [← hu₁]; exact RunStep.eval_var B σ₁ "u" (by rw [hu₁]; omega)
  have hne : (Expr.var "n").evalB B σ₁ = some (nw x) := by
    rw [← hn₁]; exact RunStep.eval_var B σ₁ "n" (by rw [hn₁]; omega)
  have htte : (Expr.var "tt").evalB B σ₁ = some (tgtw x j) := by
    rw [← htt₁]; exact RunStep.eval_var B σ₁ "tt" (by rw [htt₁]; omega)
  have hlenD₁ : (σ₁.arrs "deg").length = nw x := by simp [hσ₁, hlenD]
  have hdegB : ∀ l < nw x, (σ₁.arrs "deg").getD l 0 + 1 < B := fun l hl => by
    have := hI₁.bd l hl; omega
  -- the increment of `deg[y]`, for `y` holding `d < n`
  have hinc : ∀ (y : String) (d : ℕ), σ₁.vars y = d → d < nw x →
      Run B (.store "deg" (.var y) (.add (.get "deg" (.var y)) (.lit 1))) σ₁
        (σ₁.setArr "deg" d ((σ₁.arrs "deg").getD d 0 + 1)) 7 := by
    intro y d hy hd
    have hye : (Expr.var y).evalB B σ₁ = some d := by
      rw [← hy]; exact RunStep.eval_var B σ₁ y (by rw [hy]; omega)
    have hget := RunStep.eval_get B σ₁ "deg" _ _ hye (by omega) (by have := hdegB d hd; omega)
    have hadd := RunStep.eval_add B σ₁ _ _ _ _ hget (RunStep.eval_lit B 1 σ₁ (by omega)) (hdegB d hd)
    exact (RunStep.store B σ₁ "deg" _ _ _ _ hye hadd (by omega)).mono (by simp)
  have hcross_iff : Cross x p ↔ (u < nw x ↔ nw x ≤ tgtw x j) := Iff.rfl
  by_cases hun : u < nw x
  · -- a left row
    have hcu := RunStep.cond_lt_true B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = u := by unfold dest; simp [hp, hun]
    by_cases htn : tgtw x j < nw x
    · -- the target is a left vertex: no crossing
      have hct := RunStep.cond_lt_true B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_true B _ (.assign "ok" (.lit 0)) .skip σ₁ _ 2 hct
        (RunStep.assign B σ₁ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ₁ (by omega)))
      set σ₂ := σ₁.setVar "ok" 0 with hσ₂
      have hu₂ : σ₂.vars "u" = u := by simp [hσ₂, hu₁]
      have hlenD₂ : (σ₂.arrs "deg").length = nw x := by simp [hσ₂, hlenD₁]
      have rB : Run B (.store "deg" (.var "u") (.add (.get "deg" (.var "u")) (.lit 1))) σ₂
          (σ₂.setArr "deg" u ((σ₂.arrs "deg").getD u 0 + 1)) 7 := by
        have hye : (Expr.var "u").evalB B σ₂ = some u := by
          rw [← hu₂]; exact RunStep.eval_var B σ₂ "u" (by rw [hu₂]; omega)
        have hb2 : (σ₂.arrs "deg").getD u 0 + 1 < B := by
          simp only [hσ₂, arrs_setVar]; exact hdegB u hun
        have hget := RunStep.eval_get B σ₂ "deg" _ _ hye (by omega) (by omega)
        have hadd := RunStep.eval_add B σ₂ _ _ _ _ hget (RunStep.eval_lit B 1 σ₂ (by omega)) hb2
        exact (RunStep.store B σ₂ "deg" _ _ _ _ hye hadd (by omega)).mono (by simp)
      have rite := RunStep.ite_true B _ degThen degElse σ₁ _ _ hcu (rA.seq rB)
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, (hb₁.setVar "ok" (by simp) 0).setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.failCount p (by rw [hcross_iff]; omega) (by rw [hdest]; exact hun)
      rw [hdest] at this
      simpa [hσ₂] using this
    · -- the target is a right vertex: the slot crosses
      have hct := RunStep.cond_lt_false B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_false B _ (.assign "ok" (.lit 0)) .skip σ₁ σ₁ 2 hct
        ((RunStep.skip B σ₁).mono (by omega))
      have rB := hinc "u" u hu₁ hun
      have rite := RunStep.ite_true B _ degThen degElse σ₁ _ _ hcu (rA.seq rB)
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.count p (by rw [hdest]; exact hun) (by rw [hcross_iff]; omega)
      rw [hdest] at this
      exact this
  · -- a right row
    have hcu := RunStep.cond_lt_false B σ₁ _ _ _ _ hue hne hun
    have hdest : dest x p = tgtw x j := by unfold dest; simp [hp, hun]
    by_cases htn : tgtw x j < nw x
    · -- the target is a left vertex: the slot crosses
      have hct := RunStep.cond_lt_true B σ₁ _ _ _ _ htte hne htn
      have rB := hinc "tt" (tgtw x j) htt₁ htn
      have rA := RunStep.ite_true B _ _ (.assign "ok" (.lit 0)) σ₁ _ _ hct rB
      have rite := RunStep.ite_false B _ degThen degElse σ₁ _ _ hcu rA
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setArr (by decide) _ _⟩
      rw [hstep]
      have := hI₁.count p (by rw [hdest]; exact htn) (by rw [hcross_iff]; omega)
      rw [hdest] at this
      exact this
    · -- no crossing
      have hct := RunStep.cond_lt_false B σ₁ _ _ _ _ htte hne htn
      have rA := RunStep.ite_false B _
        (.store "deg" (.var "tt") (.add (.get "deg" (.var "tt")) (.lit 1))) _ σ₁ _ 2 hct
        (RunStep.assign B σ₁ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ₁ (by omega)))
      have rite := RunStep.ite_false B _ degThen degElse σ₁ _ _ hcu rA
      refine ⟨_, (r1.seq rite).mono (by simp), ?_, hb₁.setVar "ok" (by simp) 0⟩
      rw [hstep]
      exact hI₁.fail p (by rw [hcross_iff]; omega)

/-- **The degree pass.** -/
def degPass : Com := rowIter degBody

theorem degBody_wvars : ∀ y ∈ degBody.wvars, y ∉ ["u", "j", "je"] := by
  intro y hy
  simp [degBody, degThen, degElse, Com.wvars] at hy
  rcases hy with rfl | rfl <;> simp

/-- The crossing condition of all slots is `WellFormed.crosses`. -/
theorem cross_all_iff (x : List ℕ) :
    (∀ p ∈ allPairs x, Cross x p) ↔
      ∀ u < Vw x, ∀ j, offw x u ≤ j → j < offw x (u + 1) → (u < nw x ↔ nw x ≤ tgtw x j) := by
  constructor
  · intro h u hu j h1 h2
    exact h (u, j) ((mem_allPairs x).2 ⟨hu, h1, h2⟩)
  · rintro h ⟨u, j⟩ hp
    obtain ⟨hu, h1, h2⟩ := (mem_allPairs x).1 hp
    exact h u hu j h1 h2

/-- **After the pass**: `ok = 1` exactly when the word is well formed (given `WF3`), and then
`deg` holds the degrees. -/
theorem degPass_spec {x : List ℕ} (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1 ∧ σ.arrs "deg" = List.replicate (nw x) 0) degPass
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧ (σ'.vars "ok" = 1 ↔ Lax117284.BipartiteDecision.WellFormed x) ∧
        (σ'.vars "ok" = 1 → ∀ l < nw x, (σ'.arrs "deg").getD l 0 = deg x l) ∧
        (σ'.arrs "deg").length = nw x)
      ((30 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have hspec := rowIter_spec (Inv := DegInv x) h3 hB degBody 30 degBody_wvars
    (fun P σ y v hy hI => hI.setVar y (by simp at hy; rcases hy with rfl | rfl | rfl <;> decide) v)
    (fun u j hu hj1 hj2 => degBody_spec h3 hB hu hj1 hj2)
  refine hspec.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hok, hdeg⟩
    refine ⟨⟨by omega, by simp [hok], by simp [hdeg], fun l hl => ?_, fun _ l hl => ?_⟩, hb⟩
    · rw [hdeg, replicate_eq_arrOf, getD_arrOf _ hl]; simp
    · rw [hdeg, replicate_eq_arrOf, getD_arrOf _ hl, seg_nil]; rfl
  · rintro σ σ' - ⟨hI, hb⟩
    refine ⟨hb, hI.okle, ?_, fun hok l hl => hI.deg hok l hl, hI.lenD⟩
    rw [hI.okiff, cross_all_iff, wellFormed_iff]
    exact ⟨fun h => ⟨h3, h⟩, fun h => h.2⟩

end Lax117284Proofs.Bipartite.Ram2
