import Lax117284Proofs.Bipartite.Ram2.Validate

/-!
The generic pass over the slots of a word in `t`: for every row `u`, for every slot `j` of the
row, a body. Its specification is stated for an invariant `Inv P σ` indexed by the list `P` of
slots visited so far (`pairsAt x u j`), the body being asked to take `Inv (pairsAt x u j)` to
`Inv (pairsAt x u (j + 1))`. The cost is amortized over the slots: `Kb + 8` per slot, `22` per
row, so that the pass is linear in the word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- `u := 0; while u < V: j := t[2+u]; je := t[3+u]; while j < je: body; j := j+1; u := u+1`. -/
def rowIter (body : Com) : Com :=
  .seq (.assign "u" (.lit 0))
    (.while (.lt (.var "u") (.var "V"))
      (.seq (.assign "j" (.get "t" (.add (.lit 2) (.var "u"))))
        (.seq (.assign "je" (.get "t" (.add (.lit 3) (.var "u"))))
          (.seq (.while (.lt (.var "j") (.var "je"))
              (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
            (.assign "u" (.add (.var "u") (.lit 1)))))))

section Iter

variable {x : List ℕ} {Inv : List (ℕ × ℕ) → Env → Prop} {body : Com} {Kb : ℕ}

/-- The invariant of the inner loop, row `u`. -/
def InnerInv (x : List ℕ) (Inv : List (ℕ × ℕ) → Env → Prop) (u : ℕ) (σ : Env) : Prop :=
  Inv (pairsAt x u (σ.vars "j")) σ ∧ Base x σ ∧ σ.vars "u" = u ∧
    σ.vars "je" = offw x (u + 1) ∧ offw x u ≤ σ.vars "j" ∧ σ.vars "j" ≤ offw x (u + 1)

theorem inner_spec (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B)
    (hfr : ∀ y ∈ body.wvars, y ∉ ["u", "j", "je"])
    (hset : ∀ P σ y v, y ∈ ["u", "j", "je"] → Inv P σ → Inv P (σ.setVar y v))
    (hbody : ∀ u j, u < Vw x → offw x u ≤ j → j < offw x (u + 1) →
      Spec B (fun σ => Inv (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j) body
        (fun _ σ' => Inv (pairsAt x u (j + 1)) σ' ∧ Base x σ') Kb)
    {u : ℕ} (hu : u < Vw x) :
    Spec B (fun σ => InnerInv x Inv u σ ∧ σ.vars "j" = offw x u)
      (.while (.lt (.var "j") (.var "je")) (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
      (fun _ σ' => InnerInv x Inv u σ' ∧ σ'.vars "j" = offw x (u + 1))
      ((Kb + 8) * (offw x (u + 1) - offw x u) + 4) := by
  have hlen := h3.len
  have hoff1 : offw x (u + 1) ≤ 2 * x.getD 1 0 := h3.off_le hu
  have hjB : ∀ j ≤ offw x (u + 1), j + 1 < B := fun j hj => by omega
  refine Spec.forRange "j" "je" (InnerInv x Inv u) (offw x (u + 1)) (Kb + 4) _
    (fun σ hσ => by have := hσ.2.2.2.2.2; have := hjB _ this; omega)
    (fun σ hσ => by have := hjB _ (le_refl (offw x (u + 1))); rw [hσ.2.2.2.1]; omega)
    (fun σ hσ => hσ.2.2.2.1) (fun σ hσ => hσ.2.2.2.2.2) ?_ (fun σ hσ => hσ.1)
    (fun σ hσ => by rw [hσ.2] <;> exact le_rfl)
  rintro σ ⟨⟨hI, hb, hu', hje, hj1, hj2⟩, hlt⟩
  obtain ⟨σ', r1, ⟨hI', hb'⟩, hfv, -, -, -⟩ :=
    (hbody u (σ.vars "j") hu hj1 hlt).frame.run ⟨hI, hb, hu', rfl⟩
  have hv : ∀ y, y ∈ ["u", "j", "je"] → σ'.vars y = σ.vars y := fun y hy =>
    hfv y (fun h => hfr y h hy)
  have hj' : σ'.vars "j" = σ.vars "j" := hv "j" (by simp)
  have r2 := RunStep.assign B σ' "j" (.add (.var "j") (.lit 1)) (σ.vars "j" + 1)
    (RunStep.eval_add B σ' (.var "j") (.lit 1) _ _
      (by rw [← hj']; exact RunStep.eval_var B σ' "j" (by rw [hj']; have := hjB _ hj2; omega))
      (RunStep.eval_lit B 1 σ' (by omega)) (hjB _ hj2))
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨?_, hb'.setVar "j" (by simp) _, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    exact hset _ _ "j" _ (by simp) hI'
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]; rw [hv "u" (by simp)]; exact hu'
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]; rw [hv "je" (by simp)]; exact hje
  · simp; omega
  · simp; omega
  · simp

/-- The invariant of the outer loop. -/
def RowOuterInv (x : List ℕ) (Inv : List (ℕ × ℕ) → Env → Prop) (σ : Env) : Prop :=
  Inv (pairsUpto x (σ.vars "u")) σ ∧ Base x σ ∧ σ.vars "u" ≤ Vw x

/-- **The pass over the slots.** -/
theorem rowIter_spec (h3 : WF3 x) (hB : 8 * x.length + 40 ≤ B) (body : Com) (Kb : ℕ)
    (hfr : ∀ y ∈ body.wvars, y ∉ ["u", "j", "je"])
    (hset : ∀ P σ y v, y ∈ ["u", "j", "je"] → Inv P σ → Inv P (σ.setVar y v))
    (hbody : ∀ u j, u < Vw x → offw x u ≤ j → j < offw x (u + 1) →
      Spec B (fun σ => Inv (pairsAt x u j) σ ∧ Base x σ ∧ σ.vars "u" = u ∧ σ.vars "j" = j) body
        (fun _ σ' => Inv (pairsAt x u (j + 1)) σ' ∧ Base x σ') Kb) :
    Spec B (fun σ => Inv [] σ ∧ Base x σ) (rowIter body)
      (fun _ σ' => Inv (allPairs x) σ' ∧ Base x σ')
      ((Kb + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6) := by
  have hlen := h3.len
  have hVB : Vw x < B := by omega
  have hoffB : ∀ i ≤ Vw x, offw x i < B := fun i hi => by have := h3.off_le hi; omega
  rintro σ₀ ⟨hI₀, hb₀⟩
  have r0 := RunStep.assign B σ₀ "u" (.lit 0) 0 (RunStep.eval_lit B 0 σ₀ (by omega))
  set σ₁ := σ₀.setVar "u" 0 with hσ₁
  have hO₁ : RowOuterInv x Inv σ₁ := by
    refine ⟨?_, hb₀.setVar "u" (by simp) 0, by simp [hσ₁]⟩
    simp only [hσ₁, vars_setVar, String.reduceEq, ↓reduceIte]
    show Inv (pairsUpto x 0) _
    have h0 : pairsUpto x 0 = [] := by simp [pairsUpto]
    rw [h0]
    exact hset _ _ "u" 0 (by simp) hI₀
  have hdef : ∀ τ, RowOuterInv x Inv τ → ∃ v, (Cond.lt (.var "u") (.var "V")).evalB B τ = some v :=
    fun τ hτ => evalB_condLt_vars (by have := hτ.2.2; omega) (by rw [hτ.2.1.V]; exact hVB)
  have hstep : ∀ τ, RowOuterInv x Inv τ → (Cond.lt (.var "u") (.var "V")).evalB B τ = some true →
      ∃ τ' K, Run B (.seq (.assign "j" (.get "t" (.add (.lit 2) (.var "u"))))
        (.seq (.assign "je" (.get "t" (.add (.lit 3) (.var "u"))))
          (.seq (.while (.lt (.var "j") (.var "je"))
              (.seq body (.assign "j" (.add (.var "j") (.lit 1)))))
            (.assign "u" (.add (.var "u") (.lit 1)))))) τ τ' K ∧ RowOuterInv x Inv τ' ∧
        1 + (Cond.lt (.var "u") (.var "V")).size + K +
          ((Kb + 8) * (2 * x.getD 1 0 - offw x (τ'.vars "u")) + 22 * (Vw x - τ'.vars "u")) ≤
        (Kb + 8) * (2 * x.getD 1 0 - offw x (τ.vars "u")) + 22 * (Vw x - τ.vars "u") := by
    intro τ ⟨hI, hb, hule⟩ hcond
    have hu : τ.vars "u" < Vw x := by
      have := lt_of_condLt_true hcond; rw [hb.V] at this; exact this
    generalize hu_eq : τ.vars "u" = u at hI hule hu ⊢
    have hlenT := hb.tab.length
    have hg2 : (τ.arrs "t").getD (2 + u) 0 = offw x u := hb.tab.getD (by omega)
    have hg3 : (τ.arrs "t").getD (3 + u) 0 = offw x (u + 1) := by
      rw [hb.tab.getD (by omega)]; unfold offw; congr 1; omega
    have hmono := h3.mono u hu
    have hoff1 := h3.off_le (i := u + 1) hu
    -- j := t[2 + u]
    have hue : (Expr.var "u").evalB B τ = some u := by
      rw [← hu_eq]; exact RunStep.eval_var B τ "u" (by rw [hu_eq]; omega)
    have e2 : (Expr.add (.lit 2) (.var "u")).evalB B τ = some (2 + u) :=
      RunStep.eval_add B τ _ _ _ _ (RunStep.eval_lit B 2 τ (by omega)) hue (by omega)
    have r1 := RunStep.assign B τ "j" _ _ (RunStep.eval_get B τ "t" _ _ e2 (by omega)
      (by rw [hg2]; exact hoffB u (by omega)))
    rw [hg2] at r1
    set τ₁ := τ.setVar "j" (offw x u) with hτ₁
    -- je := t[3 + u]
    have e3 : (Expr.add (.lit 3) (.var "u")).evalB B τ₁ = some (3 + u) :=
      RunStep.eval_add B τ₁ _ _ _ _ (RunStep.eval_lit B 3 τ₁ (by omega))
        (by have : τ₁.vars "u" = u := by simp [hτ₁, hu_eq]
            rw [← this]; exact RunStep.eval_var B τ₁ "u" (by rw [this]; omega)) (by omega)
    have hg3' : (τ₁.arrs "t").getD (3 + u) 0 = offw x (u + 1) := by simpa [hτ₁] using hg3
    have r2 := RunStep.assign B τ₁ "je" _ _ (RunStep.eval_get B τ₁ "t" _ _ e3
      (by simp [hτ₁]; omega) (by rw [hg3']; exact hoffB (u + 1) hu))
    rw [hg3'] at r2
    set τ₂ := τ₁.setVar "je" (offw x (u + 1)) with hτ₂
    -- the inner loop
    obtain ⟨τ₃, r3, ⟨hI₃, hb₃, hu₃, -, -, -⟩, hj₃⟩ :=
      (inner_spec h3 hB hfr hset hbody hu).run (σ := τ₂) (by
        refine ⟨⟨?_, (hb.setVar "j" (by simp) _).setVar "je" (by simp) _, by simp [hτ₂, hτ₁, hu_eq],
          by simp [hτ₂], by simp [hτ₂, hτ₁], by simp [hτ₂, hτ₁]; exact hmono⟩, by simp [hτ₂, hτ₁]⟩
        simp only [hτ₂, hτ₁, vars_setVar, String.reduceEq, ↓reduceIte]
        rw [pairsAt_start]
        exact hset _ _ "je" _ (by simp) (hset _ _ "j" _ (by simp) hI))
    rw [hj₃, pairsAt_end] at hI₃
    -- u := u + 1
    have r4 := RunStep.assign B τ₃ "u" (.add (.var "u") (.lit 1)) (u + 1)
      (RunStep.eval_add B τ₃ (.var "u") (.lit 1) _ _
        (by rw [← hu₃]; exact RunStep.eval_var B τ₃ "u" (by rw [hu₃]; omega))
        (RunStep.eval_lit B 1 τ₃ (by omega)) (by omega))
    refine ⟨_, _, r1.seq (r2.seq (r3.seq r4)), ⟨?_, hb₃.setVar "u" (by simp) _, by simp; omega⟩, ?_⟩
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      exact hset _ _ "u" _ (by simp) hI₃
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte, size_condLt, size_var, size_get,
        size_add, size_lit, Expr.add_def, size_bin]
      have h1 : (Kb + 8) * (2 * x.getD 1 0 - offw x u) =
          (Kb + 8) * (2 * x.getD 1 0 - offw x (u + 1)) + (Kb + 8) * (offw x (u + 1) - offw x u) := by
        rw [← Nat.mul_add]; congr 1; omega
      rw [h1]
      have h2 : 22 * (Vw x - u) = 22 * (Vw x - (u + 1)) + 22 := by
        rw [show Vw x - u = (Vw x - (u + 1)) + 1 by omega, Nat.mul_add]
      rw [h2]
      omega
  obtain ⟨σ', K, hrun, ⟨hI', hb', hu'⟩, hfalse, hpay⟩ := Run.while_potential (B := B)
    (b := .lt (.var "u") (.var "V")) (RowOuterInv x Inv)
    (fun τ => (Kb + 8) * (2 * x.getD 1 0 - offw x (τ.vars "u")) + 22 * (Vw x - τ.vars "u"))
    hdef hstep hO₁
  have hueq : σ'.vars "u" = Vw x := by
    have := le_of_condLt_false hfalse
    rw [hb'.V] at this
    omega
  refine ⟨σ', (r0.seq hrun).mono ?_, ?_, hb'⟩
  · simp only [size_condLt, size_var, size_lit, hσ₁, vars_setVar, String.reduceEq, ↓reduceIte,
      h3.off0, Nat.sub_zero] at hpay ⊢
    omega
  · rw [hueq] at hI'; exact hI'

end Iter

end Lax117284Proofs.Bipartite.Ram2
