import Lax117284Proofs.Bipartite.Ram2.Mu
import Lax117284Proofs.Bipartite.Ram2.Word

/-!
Counting the matched right vertices at the end: `count := 0; j := 0; while j < m do (if mu[j] ≠ 0
then count := count + 1); j := j + 1`. The result is the number of right indices below `m` whose
`mu` entry is nonzero — the size of the matching.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open scoped Classical

variable {B : ℕ}

/-- One right vertex: count it if matched, move on. -/
def countBody : Com :=
  .seq (.ite (.eq (.get "mu" (.var "j")) (.lit 0)) .skip
      (.assign "count" (.add (.var "count") (.lit 1))))
    (.assign "j" (.add (.var "j") (.lit 1)))

/-- **Count the matched right vertices.** -/
def countCom : Com :=
  .seq (.assign "count" (.lit 0))
    (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "m")) countBody))

/-- The number of matched right indices below `j`. -/
noncomputable def cnt (μ : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (fun r => (μ r).isSome)).card

theorem cnt_succ (μ : ℕ → Option ℕ) (j : ℕ) :
    cnt μ (j + 1) = cnt μ j + if (μ j).isSome then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_le (μ : ℕ → Option ℕ) (j : ℕ) : cnt μ j ≤ j := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The invariant of the counting loop. -/
def CountInv (μ : ℕ → Option ℕ) (m : ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "j" ≤ m ∧ MuOK μ m σ ∧ σ.vars "count" = cnt μ (σ.vars "j")

theorem countBody_spec {μ : ℕ → Option ℕ} {m : ℕ} (hmB : m + 1 < B)
    (hμB : ∀ j l, μ j = some l → l + 1 < B) :
    Spec B (fun σ => CountInv μ m σ ∧ σ.vars "j" < m) countBody
      (fun σ σ' => CountInv μ m σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 14 := by
  rintro σ ⟨⟨hm, hjm, hmu, hc⟩, hj⟩
  have hlen : (σ.arrs "mu").length = m := hmu.1
  have hval : (σ.arrs "mu").getD (σ.vars "j") 0 =
      (match μ (σ.vars "j") with | none => 0 | some l => l + 1) := hmu.2 _ hj
  have hvalB : (σ.arrs "mu").getD (σ.vars "j") 0 < B := by
    rw [hval]
    rcases hμ : μ (σ.vars "j") with _ | l
    · show 0 < B; omega
    · show l + 1 < B; exact hμB _ _ hμ
  have hcB : σ.vars "count" < B := by rw [hc]; have := cnt_le μ (σ.vars "j"); omega
  have hc1B : σ.vars "count" + 1 < B := by rw [hc]; have := cnt_le μ (σ.vars "j"); omega
  have hsucc := cnt_succ μ (σ.vars "j")
  unfold countBody
  run_vcg
  · rename_i hz
    have hnone : μ (σ.vars "j") = none := by
      rcases hμ : μ (σ.vars "j") with _ | l
      · rfl
      · rw [hval, hμ] at hz; simp at hz
    refine ⟨⟨by simp [hm], by simp; omega, by simpa [MuOK] using hmu, ?_⟩, by simp⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hsucc, hnone, hc]; simp
  · rename_i hz
    have hsome : (μ (σ.vars "j")).isSome := by
      rcases hμ : μ (σ.vars "j") with _ | l
      · rw [hval, hμ] at hz; simp at hz
      · rfl
    refine ⟨⟨by simp [hm], by simp; omega, by simpa [MuOK] using hmu, ?_⟩, by simp⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hsucc, if_pos hsome, hc]

/-- **The count.** -/
theorem countCom_spec {μ : ℕ → Option ℕ} {m : ℕ} (hmB : m + 1 < B)
    (hμB : ∀ j l, μ j = some l → l + 1 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ MuOK μ m σ) countCom
      (fun _ σ' => σ'.vars "count" = cnt μ m) ((14 + 4) * m + 6 + 2) := by
  have hloop := Spec.forRangeZero (B := B) (c := countBody) "j" "m" (CountInv μ m) m 14
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (countBody_spec hmB hμB)
  intro σ ⟨hm, hmu⟩
  have r1 : Run B (.assign "count" (.lit 0)) σ (σ.setVar "count" 0) 2 :=
    RunStep.assign B σ "count" (.lit 0) 0 (RunStep.eval_lit B 0 σ (by omega))
  obtain ⟨σ', hr2, hI', hj⟩ := hloop.run (σ := σ.setVar "count" 0) (by
    refine ⟨by simpa using hm, by simp, by simpa [MuOK] using hmu, ?_⟩
    simp [cnt])
  refine ⟨σ', (r1.seq hr2).mono (by omega), ?_⟩
  show σ'.vars "count" = cnt μ m
  rw [hI'.2.2.2, hj]

end Lax117284Proofs.Bipartite.Ram2
