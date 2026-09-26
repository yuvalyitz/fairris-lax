import Lax117284Proofs.Bipartite.Ram2.Header
import Lax117284Proofs.Bipartite.Ram2.Outer
import Lax117284Proofs.Bipartite.Ram2.Count
import Lax117284Proofs.Bipartite.Ram2.Wrap

/-!
The IMP+ program up to its final output: read the word, the header, run one search per left
vertex, count the matched right vertices. `pre_run` runs it from the entry state of `Wrap.lean` on
any word satisfying `Good`, and leaves `count` holding the size of Kuhn's matching of the
adjacency across the split, `adjF (adjw x) n m`. The three concept programs append one output
command each (`Machine.lean`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The program without its final output. -/
def preCom : Com :=
  .seq readAll (.seq hdrCom (.seq (.assign "l0" (.lit 0)) (.seq outerLoop countCom)))

/-- The array lengths declared to the run. -/
def extOf (x : List ℕ) : String → ℕ := fun a =>
  if a = "a" then x.length
  else if a = "vis" ∨ a = "mu" then mw x
  else mw x + 1

/-- The initial abstract state: empty stacks, nothing visited. -/
def b0 : AS := ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0, fun _ => False⟩

/-- The cost of the program without its final output. -/
def preCost (x : List ℕ) : ℕ :=
  ((10 + 4) * x.length + 6) + 12 + 2 + (iterCost x * nw x + 4) + ((14 + 4) * mw x + 6 + 2)

/-- The size of Kuhn's matching of the adjacency across the split of the word. -/
noncomputable def kuhnSize (x : List ℕ) : ℕ := size (kuhn (adjF (adjw x) (nw x) (mw x)))

theorem real_init {x : List ℕ} {σ : Env} (htop : σ.vars "top" = 0) (hV : σ.vars "V" = Vw x)
    (hn : σ.vars "n" = nw x) (hm : σ.vars "m" = mw x) (harr : ArrOK x σ)
    (hvis : σ.arrs "vis" = List.replicate (mw x) 0) (hmu : σ.arrs "mu" = List.replicate (mw x) 0)
    (hL : σ.arrs "stkL" = List.replicate (mw x + 1) 0)
    (hR : σ.arrs "stkR" = List.replicate (mw x + 1) 0)
    (hX : σ.arrs "stkX" = List.replicate (mw x + 1) 0) :
    Real x (fun _ => none) b0 σ := by
  refine ⟨htop, hV, hn, hm, harr, ?_, ⟨?_, fun j hj => ?_⟩, ?_, ?_, ?_⟩
  · unfold VisOK
    rw [hvis, replicate_eq_arrOf]
    exact arrOf_congr (fun _ _ => by simp [b0])
  · rw [hmu]; simp
  · rw [hmu, replicate_eq_arrOf, getD_arrOf _ hj]
  · rw [hL, replicate_eq_arrOf]; rfl
  · rw [hR, replicate_eq_arrOf]; rfl
  · rw [hX, replicate_eq_arrOf]; rfl

/-- **The program up to its output**, on a good word: `count` is the size of Kuhn's matching, the
header scalars hold `V` and `n`, nothing has been written. -/
theorem pre_run {x : List ℕ} (hg : Good x) (hB : x.length + 8 ≤ B) :
    ∃ σ' K, Run B preCom (lenEnv (extOf x) x) σ' K ∧ K ≤ preCost x ∧
      σ'.vars "count" = kuhnSize x ∧ σ'.vars "n" = nw x ∧ σ'.vars "V" = Vw x ∧
      σ'.out = [] := by
  set σ₀ := lenEnv (extOf x) x with hσ₀
  have h0len : σ₀.vars "len" = x.length := by simp [hσ₀, lenEnv]
  have h0top : σ₀.vars "top" = 0 := by simp [hσ₀, lenEnv, initEnv]
  have h0inp : σ₀.inp = x := rfl
  have h0out : σ₀.out = [] := rfl
  have h0arr : ∀ a, σ₀.arrs a = List.replicate (extOf x a) 0 := fun a => rfl
  have hx := hg.ent_lt
  have hlB : x.length < B := by omega
  have hxB : ∀ v ∈ x, v < B := fun v hv => lt_of_lt_of_le (hx v hv) (by omega)
  -- read
  obtain ⟨σ₁, hr1, ⟨hinp1, harr1, hlen1⟩, hfv1, hfa1, -, hfo1⟩ :=
    (readAll_spec (B := B) hxB hlB).frame.run
      ⟨h0len, h0inp, by rw [h0arr, replicate_eq_arrOf]; simp [extOf]⟩
  have hv1 : ∀ y, y ≠ "rt" → y ≠ "v" → σ₁.vars y = σ₀.vars y := fun y h1 h2 =>
    hfv1 y (by simp [readAll, readBody, Com.wvars, h1, h2])
  have ha1 : ∀ a, a ≠ "a" → σ₁.arrs a = σ₀.arrs a := fun a h1 =>
    hfa1 a (by simp [readAll, readBody, Com.warrs, h1])
  have hout1 : σ₁.out = [] := by
    rw [hfo1 (by simp [readAll, readBody, Com.NoWrite]), h0out]
  -- header
  obtain ⟨σ₂, hr2, hq2⟩ := (hdr_spec (B := B) hg hB).run (σ := σ₁) ⟨harr1, hlen1⟩
  -- l0 := 0
  have hr3 : Run B (.assign "l0" (.lit 0)) σ₂ (σ₂.setVar "l0" 0) 2 :=
    RunStep.assign B σ₂ "l0" (.lit 0) 0 (RunStep.eval_lit B 0 σ₂ (by omega))
  set σ₃ := σ₂.setVar "l0" 0 with hσ₃
  have hI₃ : OuterInv x σ₃ := by
    refine ⟨by simp [hσ₃], fun _ => none, b0, ?_, ?_⟩
    · refine real_init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · rw [hσ₃, hq2]; simp; rw [hv1 _ (by decide) (by decide), h0top]
      · rw [hσ₃, hq2]; simp
      · rw [hσ₃, hq2]; simp
      · rw [hσ₃, hq2]; simp
      · refine harr1.congr ?_
        rw [hσ₃, hq2]; simp
      all_goals
        rw [hσ₃, hq2]; simp only [arrs_setVar]
        rw [ha1 _ (by decide), h0arr]; simp [extOf]
    · simp only [hσ₃, vars_setVar, ↓reduceIte]
      exact MatchInv.zero _ _ _
  -- the searches
  obtain ⟨σ₄, K₄, hr4, hI₄, hl4, hK₄⟩ := outerLoop_run hg hB hI₃
  have hl3 : σ₃.vars "l0" = 0 := by simp [hσ₃]
  rw [hl3, Nat.sub_zero] at hK₄
  obtain ⟨-, μ, b, hR₄, hM₄⟩ := hI₄
  rw [hl4] at hM₄
  have hout4 : σ₄.out = [] := by
    rw [hr4.out_eq (by decide), hσ₃, hq2]; simpa using hout1
  -- the count
  have hnB : nw x < B := by have := hg.n_lt; omega
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  obtain ⟨σ₅, hr5, hq5, hfv5, -, -, hfo5⟩ :=
    (countCom_spec (B := B) (μ := μ) (m := mw x) hmB
      (fun j l hj => by have := hM₄.hμn le_rfl j l hj; omega)).frame.run
      (σ := σ₄) ⟨hR₄.m, hR₄.mu⟩
  have hv5 : ∀ y, y ≠ "count" → y ≠ "j" → σ₅.vars y = σ₄.vars y := fun y h1 h2 =>
    hfv5 y (by simp [countCom, countBody, Com.wvars, h1, h2])
  refine ⟨σ₅, _, hr1.seq (hr2.seq (hr3.seq (hr4.seq hr5))), ?_, ?_, ?_, ?_, ?_⟩
  · unfold preCost; omega
  · rw [hq5]
    unfold kuhnSize cnt
    rw [← size_muF_eq (hM₄.hμn le_rfl), hM₄.size_eq_kuhn]
  · rw [hv5 _ (by decide) (by decide)]; exact hR₄.n
  · rw [hv5 _ (by decide) (by decide)]; exact hR₄.V
  · rw [hfo5 (by decide)]; exact hout4

end Lax117284Proofs.Bipartite.Ram2
