import Lax117284Proofs.Machine.TwViol

/-!
A loop that fills a stretch of an array: at position `k` of the stretch it stores `g k`, computed
by a body that reads the state and writes no array.
-/

namespace Lax117284Proofs.Machine.TwFill

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol

variable {B : ℕ}

/-- Fill `arr[bs + fc]` for `fc < fn` with the value `val` that `pre` computes. -/
def fillLoop (arr : String) (pre : Com) : Com :=
  .seq (.assign "fc" (L 0)) (.while (.lt (V "fc") (V "fn"))
    (.seq pre (.seq (.store arr (add (V "bs") (V "fc")) (V "val"))
      (.assign "fc" (add (V "fc") (L 1))))))

/-- What the fill has done after `t` steps: the array holds `g` on the first `t` positions of the
stretch and is otherwise what it was. -/
def Filled (arr : String) (g : ℕ → ℕ) (σ0 σ : Env) : Prop :=
  (σ.arrs arr).length = (σ0.arrs arr).length ∧
  ∀ k, (σ.arrs arr).getD k 0 =
    if σ0.vars "bs" ≤ k ∧ k < σ0.vars "bs" + σ.vars "fc" then g (k - σ0.vars "bs")
    else (σ0.arrs arr).getD k 0

/-- The other arrays and the scalars outside `S` are as they were. -/
def AgrA (S : List String) (arr : String) (σ0 σ : Env) : Prop :=
  (∀ y, y ∉ S → σ.vars y = σ0.vars y) ∧ ∀ a, a ≠ arr → σ.arrs a = σ0.arrs a

lemma getD_set' (l : List ℕ) (i j v : ℕ) :
    (l.set i v).getD j 0 = if j = i ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

/-- The end of a step: store the value and count. -/
def fillTail (arr : String) : Com :=
  .seq (.store arr (add (V "bs") (V "fc")) (V "val")) (.assign "fc" (add (V "fc") (L 1)))

theorem fillTail_run (arr : String) (σ : Env) (hidx : σ.vars "bs" + σ.vars "fc" < (σ.arrs arr).length)
    (hval : σ.vars "val" < B) (hb : σ.vars "bs" + σ.vars "fc" + 2 < B) :
    ∃ σ', Run B (fillTail arr) σ σ' 20 ∧
      σ' = (σ.setArr arr (σ.vars "bs" + σ.vars "fc") (σ.vars "val")).setVar "fc"
        (σ.vars "fc" + 1) := by
  unfold fillTail
  run_vcg
  all_goals try (nrm; omega)
  all_goals try omega
  all_goals first | rfl | (simp only [vars_setArr]; done) | (simp [Env.setVar])

/-- One step of the fill. -/
theorem fillStep (arr : String) (pre : Com) (g : ℕ → ℕ) (S : List String) (Kb N : ℕ) (σ0 : Env)
    (hfn : σ0.vars "fn" = N) (hNB : N + 1 < B) (harr : σ0.vars "bs" + N ≤ (σ0.arrs arr).length)
    (hg : ∀ k, g k < B) (hS : "fc" ∈ S ∧ "val" ∈ S ∧ "fn" ∉ S ∧ "bs" ∉ S)
    (hbsB : σ0.vars "bs" + N + 2 < B)
    (hpre : ∀ σ, Filled arr g σ0 σ → AgrA S arr σ0 σ → σ.vars "fc" < N →
      ∃ σ', Run B pre σ σ' Kb ∧ σ'.vars "val" = g (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
        (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.vars "fc" = σ.vars "fc" ∧ σ'.out = σ.out)
    (σ : Env) (hF : Filled arr g σ0 σ) (hA : AgrA S arr σ0 σ) (hlt : σ.vars "fc" < N)
    (ho : σ.out = σ0.out) :
    ∃ σ', Run B (.seq pre (fillTail arr)) σ σ' (Kb + 20) ∧
      Filled arr g σ0 σ' ∧ AgrA S arr σ0 σ' ∧ σ'.vars "fc" = σ.vars "fc" + 1 ∧
      σ'.out = σ0.out := by
  obtain ⟨σ1, r1, hval, harr1, hfr1, hfc1, ho1⟩ := hpre σ hF hA hlt
  have hbs : σ1.vars "bs" = σ0.vars "bs" := by
    rw [hfr1 "bs" hS.2.2.2, hA.1 "bs" hS.2.2.2]
  have hidx : σ1.vars "bs" + σ1.vars "fc" < (σ1.arrs arr).length := by
    rw [harr1, hF.1, hfc1, hbs]; omega
  have hgB := hg (σ.vars "fc")
  obtain ⟨σ2, r2, he2⟩ := fillTail_run (B := B) arr σ1 hidx (by rw [hval]; exact hgB)
    (by rw [hfc1, hbs]; omega)
  refine ⟨σ2, r1.seq r2, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [he2]; simp only [arrs_setVar, length_arrs_setArr]; rw [harr1]; exact hF.1
  · intro k
    rw [he2]
    simp only [arrs_setVar, arrs_setArr, ↓reduceIte, vars_setVar, String.reduceEq]
    rw [getD_set', hbs, hval, hfc1, harr1, hF.2 k, hF.1]
    have hl : σ0.vars "bs" + σ.vars "fc" < (σ0.arrs arr).length := by omega
    split_ifs <;> first | rfl | (congr 1; omega) | omega
  · intro y hy
    rw [he2]
    simp only [vars_setVar, vars_setArr]
    by_cases hyf : y = "fc"
    · exact absurd (hyf ▸ hS.1) hy
    · simp only [hyf, if_false]
      rw [hfr1 y hy, hA.1 y hy]
  · intro a ha
    rw [he2]
    simp only [arrs_setVar, arrs_setArr, ha, if_false]
    rw [harr1, hA.2 a ha]
  · rw [he2]; simp [hfc1]
  · rw [he2]; simp only [out_setVar, out_setArr]; rw [ho1, ho]

/-- **The fill loop.** -/
theorem fillLoop_run (arr : String) (pre : Com) (g : ℕ → ℕ) (S : List String) (Kb N : ℕ)
    (σ0 : Env)
    (hfn : σ0.vars "fn" = N) (hNB : N + 1 < B) (harr : σ0.vars "bs" + N ≤ (σ0.arrs arr).length)
    (hg : ∀ k, g k < B) (hS : "fc" ∈ S ∧ "val" ∈ S ∧ "fn" ∉ S ∧ "bs" ∉ S)
    (hbsB : σ0.vars "bs" + N + 2 < B)
    (hpre : ∀ σ, Filled arr g σ0 σ → AgrA S arr σ0 σ → σ.vars "fc" < N →
      ∃ σ', Run B pre σ σ' Kb ∧ σ'.vars "val" = g (σ.vars "fc") ∧ σ'.arrs = σ.arrs ∧
        (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.vars "fc" = σ.vars "fc" ∧ σ'.out = σ.out) :
    ∃ σ', Run B (fillLoop arr pre) σ0 σ' ((Kb + 20 + 4) * N + 6) ∧
      (σ'.arrs arr).length = (σ0.arrs arr).length ∧
      (∀ k, (σ'.arrs arr).getD k 0 =
        if σ0.vars "bs" ≤ k ∧ k < σ0.vars "bs" + N then g (k - σ0.vars "bs")
        else (σ0.arrs arr).getD k 0) ∧
      AgrA S arr σ0 σ' ∧ σ'.out = σ0.out := by
  let I : Env → Prop := fun σ => Filled arr g σ0 σ ∧ AgrA S arr σ0 σ ∧ σ.vars "fc" ≤ N ∧
    σ.vars "fn" = N ∧ σ.out = σ0.out
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "fc" < N) (.seq pre (fillTail arr))
      (fun σ σ' => I σ' ∧ σ'.vars "fc" = σ.vars "fc" + 1) (Kb + 20) := by
    rintro σ ⟨⟨hF, hA, hle, hfn', ho⟩, hlt⟩
    obtain ⟨σ', r, hF', hA', hfc', ho'⟩ := fillStep (B := B) arr pre g S Kb N σ0 hfn hNB harr hg hS
      hbsB hpre σ hF hA hlt ho
    refine ⟨σ', r, ⟨hF', hA', by omega, ?_, ho'⟩, hfc'⟩
    rw [hA'.1 "fn" hS.2.2.1]; exact hfn
  obtain ⟨σ', r, hI, hfc⟩ := (Spec.forRangeZero (B := B) (c := .seq pre (fillTail arr)) "fc" "fn" I N
    (Kb + 20) (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) hbody) σ0 (by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by simp, by simpa using hfn, by simp⟩
      · simp
      · intro k; simp [Env.setVar]
      · intro y hy
        by_cases hyf : y = "fc"
        · exact absurd (hyf ▸ hS.1) hy
        · simp [Env.setVar, hyf]
      · intro a ha; simp [Env.setVar])
  obtain ⟨hF, hA, -, -, ho⟩ := hI
  refine ⟨σ', r, hF.1, fun k => ?_, hA, ho⟩
  rw [hF.2 k, hfc]

end Lax117284Proofs.Machine.TwFill
