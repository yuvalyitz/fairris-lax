import Lax117284Proofs.Bipartite.Ram2.Total

/-!
**The total program on every word**: from the entry state of `Wrap.lean` (the word on the input
tape, its length in `len`, everything else zero), `totCom` halts within `totCost x` with the
output `saturatingAnswer x`, under the value bound `8 (|x| + max x + 1) + 40`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- The largest entry of the word. -/
def mxE (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mxE {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mxE x := by
  induction x with
  | nil => simp at h
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem mxE_cases (x : List ℕ) : mxE x = 0 ∨ mxE x ∈ x := by
  induction x with
  | nil => left; simp [mxE]
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      change max a (mxE t) = 0 ∨ max a (mxE t) ∈ a :: t
      rcases max_choice a (mxE t) with h | h
      · rw [h]; right; exact List.mem_cons_self
      · rw [h]
        rcases ih with h0 | h0
        · left; exact h0
        · right; exact List.mem_cons_of_mem _ h0

theorem getD_le_mxE (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ mxE x := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact Nat.zero_le _
  · exact le_mxE (List.mem_of_getElem? h)

/-- The value bound the program runs under. -/
def BofT (x : List ℕ) : ℕ := 8 * (x.length + 3 * mxE x + 1) + 40

theorem write_run {σ : Env} (v : ℕ) (hv : v < B) :
    Run B (.write (.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
  (Run.write (evalB_lit hv)).mono (by simp)

theorem finalC_run {σ : Env} (hcB : σ.vars "count" < B) (hnB : σ.vars "n" < B) (h1B : 1 < B) :
    Run B finalC σ { σ with out := σ.out ++ [if σ.vars "count" = σ.vars "n" then 1 else 0] } 6 := by
  have e1 := RunStep.eval_var B σ "count" hcB
  have e2 := RunStep.eval_var B σ "n" hnB
  have w1 := RunStep.write B σ (.lit 1) 1 (RunStep.eval_lit _ 1 σ h1B)
  have w0 := RunStep.write B σ (.lit 0) 0 (RunStep.eval_lit _ 0 σ (by omega))
  by_cases h : σ.vars "count" = σ.vars "n"
  · rw [if_pos h]
    exact RunStep.ite_true _ _ _ _ σ _ _ (RunStep.cond_eq_true _ σ _ _ _ _ e1 e2 h) w1
  · rw [if_neg h]
    exact RunStep.ite_false _ _ _ _ σ _ _ (RunStep.cond_eq_false _ σ _ _ _ _ e1 e2 h) w0

theorem notWellFormed_of_short {x : List ℕ} (h : x.length < 4) : ¬ WellFormed x := fun hw => by
  have := hw.length_eq; omega

theorem saturatingAnswer_of_not {x : List ℕ} (h : ¬ WellFormed x) : saturatingAnswer x = [0] := by
  unfold saturatingAnswer
  rw [if_neg (fun hh => h hh.1)]

/-- **The heavy path**, on a well-formed word. -/
theorem heavyTot_run {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) {σ : Env}
    (hb : Base x σ) (hdeg : DegOK x σ) (ha : σ.arrs "a" = List.replicate x.length 0)
    (hpos : (σ.arrs "pos").length = nw x) (hu : Untouched x σ) :
    ∃ σ' K, Run B heavyTot σ σ' K ∧
      K ≤ 200 * (x.length + 1) + 400 * ((x.length + 1) * nw x) ∧
      σ'.out = [if kuhnSize (sx x) = nw x then 1 else 0] := by
  have hxlen := wf_len hw
  have hnV := wf_nV hw
  have hg : Good (sx x) := wf_good_sx hw
  have hlen' := wf_length_sx hw
  set x' := sx x with hx'
  have hnw : nw x' = nw x := nw_sx x
  have hmw : mw x' = Vw x - nw x := by unfold mw; rw [Vw_sx, nw_sx]
  have hVw : Vw x' = Vw x := rfl
  -- the prefix sums
  obtain ⟨σ₁, r1, ⟨hb₁, hdeg₁, hf₁⟩, hfv₁, hfa₁, -, hfo₁⟩ :=
    (prefix_spec hw hB).frame.run ⟨hb, hdeg, ha⟩
  have hu₁ : Untouched x σ₁ := hu.of_run r1 frame_prefix.1 frame_prefix.2.1 frame_prefix.2.2
  have hpos₁ : (σ₁.arrs "pos").length = nw x := by rw [hfa₁ "pos" warrs_prefix]; exact hpos
  -- the cursors
  obtain ⟨σ₂, r2, ⟨hb₂, hf₂, hp₂⟩, -, -, -, -⟩ :=
    (pos_spec hw hB).frame.run ⟨hb₁, hf₁, hpos₁⟩
  have hu₂ : Untouched x σ₂ := hu₁.of_run r2 frame_pos.1 frame_pos.2.1 frame_pos.2.2
  -- the fill
  obtain ⟨σ₃, r3, ⟨hb₃, harr₃⟩, -, -, -, -⟩ := (fillPass_spec hw hB).frame.run ⟨hb₂, hf₂, hp₂⟩
  have hu₃ : Untouched x σ₃ := hu₂.of_run r3 frame_fillPass.1 frame_fillPass.2.1 frame_fillPass.2.2
  -- m := V - n; l0 := 0
  have hVB : Vw x < B := by omega
  have r4 := RunStep.assign B σ₃ "m" (.sub (.var "V") (.var "n")) (Vw x - nw x)
    (RunStep.eval_sub B σ₃ (.var "V") (.var "n") _ _
      (by rw [← hb₃.V]; exact RunStep.eval_var B σ₃ "V" (by rw [hb₃.V]; omega))
      (by rw [← hb₃.n]; exact RunStep.eval_var B σ₃ "n" (by rw [hb₃.n]; omega)) (by omega))
  set σ₄ := σ₃.setVar "m" (Vw x - nw x) with hσ₄
  have r5 := RunStep.assign B σ₄ "l0" (.lit 0) 0 (RunStep.eval_lit B 0 σ₄ (by omega))
  set σ₅ := σ₄.setVar "l0" 0 with hσ₅
  have hu₅ : Untouched x σ₅ := (hu₃.setVar "m" (by decide) _).setVar "l0" (by decide) _
  -- the search state
  have hReal : Real x' (fun _ => none) b0 σ₅ := by
    refine real_init hu₅.top ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hVw]; simp [hσ₅, hσ₄, hb₃.V]
    · rw [hnw]; simp [hσ₅, hσ₄, hb₃.n]
    · rw [hmw]; simp [hσ₅, hσ₄]
    · exact harr₃.congr (by simp [hσ₅, hσ₄])
    · rw [hmw]; exact hu₅.vis
    · rw [hmw]; exact hu₅.mu
    · rw [hmw]; exact hu₅.stkL
    · rw [hmw]; exact hu₅.stkR
    · rw [hmw]; exact hu₅.stkX
  have hI₅ : OuterInv x' σ₅ := by
    refine ⟨by rw [hnw]; simp [hσ₅], fun _ => none, b0, hReal, ?_⟩
    simp only [hσ₅, vars_setVar, ↓reduceIte]
    exact MatchInv.zero _ _ _
  have hB' : x'.length + 8 ≤ B := by rw [hlen']; omega
  obtain ⟨σ₆, K₆, r6, hI₆, hl₆, hK₆⟩ := outerLoop_run hg hB' hI₅
  have hl₅ : σ₅.vars "l0" = 0 := by simp [hσ₅]
  rw [hl₅, Nat.sub_zero, hnw] at hK₆
  obtain ⟨-, μ, b, hR₆, hM₆⟩ := hI₆
  rw [hl₆] at hM₆
  have hout₆ : σ₆.out = [] := by
    rw [r6.out_eq (by decide)]; simpa [hσ₅, hσ₄] using hu₃.out
  -- the count
  have hmB : mw x' + 1 < B := by rw [hmw]; omega
  obtain ⟨σ₇, r7, hq₇, hfv₇, -, -, hfo₇⟩ :=
    (countCom_spec (B := B) (μ := μ) (m := mw x') hmB
      (fun j l hj => by have := hM₆.hμn le_rfl j l hj; rw [hnw] at this; omega)).frame.run
      (σ := σ₆) ⟨hR₆.m, hR₆.mu⟩
  have hn₇ : σ₇.vars "n" = nw x := by
    rw [hfv₇ "n" (by simp [countCom, countBody, Com.wvars]), hR₆.n, hnw]
  have hcount : σ₇.vars "count" = kuhnSize x' := by
    rw [hq₇]
    unfold kuhnSize cnt
    rw [← size_muF_eq (hM₆.hμn le_rfl), hM₆.size_eq_kuhn]
  have hout₇ : σ₇.out = [] := by rw [hfo₇ (by decide)]; exact hout₆
  have hcB : σ₇.vars "count" < B := by
    rw [hcount]; have := Lax117284Proofs.Bipartite.Machine.kuhnSize_le x'; rw [hmw] at this; omega
  have r8 := finalC_run (B := B) (σ := σ₇) hcB (by rw [hn₇]; omega) (by omega)
  refine ⟨_, _, r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8)))))), ?_, ?_⟩
  · -- the cost
    have h1 := Lax117284Proofs.Bipartite.Machine.iterCost_le hg
    have h2 : x'.length + 1 = x.length + 1 := by rw [hlen']
    have h3 : iterCost x' ≤ 400 * (x.length + 1) := by omega
    have h4 : iterCost x' * nw x ≤ 400 * ((x.length + 1) * nw x) := by
      calc iterCost x' * nw x ≤ 400 * (x.length + 1) * nw x := Nat.mul_le_mul_right _ h3
        _ = 400 * ((x.length + 1) * nw x) := by ring
    rw [hmw] at *
    simp only [size_var, size_lit, size_bin, Expr.sub_def]
    omega
  · show σ₇.out ++ [if σ₇.vars "count" = σ₇.vars "n" then 1 else 0] = _
    rw [hout₇, hcount, hn₇]
    rfl

end Lax117284Proofs.Bipartite.Ram2
