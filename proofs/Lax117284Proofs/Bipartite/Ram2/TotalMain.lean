import Lax117284Proofs.Bipartite.Ram2.TotalRun
import Lax117284Proofs.Bipartite.Ram2.Wrap

/-!
**The total program on every word**: from the entry state of `Wrap.lean`, `totCom` halts within
`totCost x` with the output `saturatingAnswer x`, every value below `BofT x`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision Lax117284.BipartiteGraph Lax117284.BipartiteMatching Lax271696.GraphEncoding
open scoped Classical

variable {B : ℕ}

/-- What the checks keep: the header, the untouched search state, and the three arrays of the
symmetrizer still zero. -/
structure Aux (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  unt : Untouched x σ
  deg : σ.arrs "deg" = List.replicate (nw x) 0
  a : σ.arrs "a" = List.replicate x.length 0
  pos : σ.arrs "pos" = List.replicate (nw x) 0

/-- A check keeps `Aux`. -/
theorem Aux.of_run {x : List ℕ} {σ σ' : Env} {c : Com} {K : ℕ} (h : Aux x σ) (hb : Base x σ')
    (hr : Run B c σ σ' K) (htop : "top" ∉ c.wvars)
    (harr : ∀ a ∈ ["vis", "mu", "stkL", "stkR", "stkX"], a ∉ c.warrs) (hw : c.NoWrite)
    (h3 : ∀ a ∈ ["deg", "pos", "a"], a ∉ c.warrs) : Aux x σ' :=
  ⟨hb, h.unt.of_run hr htop harr hw, by rw [hr.frame_arr "deg" (h3 _ (by simp))]; exact h.deg,
    by rw [hr.frame_arr "a" (h3 _ (by simp))]; exact h.a,
    by rw [hr.frame_arr "pos" (h3 _ (by simp))]; exact h.pos⟩

theorem Aux.setVar {x : List ℕ} {σ : Env} (h : Aux x σ) (y : String)
    (hy : y ∉ ["len", "V", "E", "n", "top"]) (v : ℕ) : Aux x (σ.setVar y v) :=
  ⟨h.base.setVar y (by simp at hy; simp; tauto) v, h.unt.setVar y (by simp at hy; tauto) v,
    h.deg, h.a, h.pos⟩

/-- **The total program, run.** -/
theorem tot_run (x : List ℕ) :
    ∃ σ' K, Run (BofT x) totCom (lenEnv (extT x) x) σ' K ∧ K ≤ totCost x ∧
      σ'.out = saturatingAnswer x := by
  set B := BofT x with hBdef
  have hxB : ∀ v ∈ x, v < B := fun v hv => by have := le_mxE hv; unfold BofT at hBdef; omega
  have hB : 8 * x.length + 40 ≤ B := by unfold BofT at hBdef; omega
  have h0m := getD_le_mxE x 0
  have h1m := getD_le_mxE x 1
  have hnm := getD_le_mxE x (x.length - 1)
  have hVm : Vw x ≤ mxE x := h0m
  have hnm' : nw x ≤ mxE x := hnm
  have hBV : 8 * (x.length + Vw x + x.getD 1 0 + nw x) + 40 ≤ B := by
    have hB' : B = 8 * (x.length + 3 * mxE x + 1) + 40 := hBdef
    rw [hB']
    omega
  have hlB : x.length < B := by omega
  have h1B : 1 < B := by omega
  set σ₀ := lenEnv (extT x) x with hσ₀
  have h0len : σ₀.vars "len" = x.length := by simp [hσ₀, lenEnv]
  have h0top : σ₀.vars "top" = 0 := by simp [hσ₀, lenEnv, initEnv]
  have h0inp : σ₀.inp = x := rfl
  have h0out : σ₀.out = [] := rfl
  have h0arr : ∀ a, σ₀.arrs a = List.replicate (extT x a) 0 := fun a => rfl
  -- the read
  obtain ⟨σ₁, r1, ⟨-, htab₁, hlen₁⟩, hfv₁, hfa₁, -, hfo₁⟩ :=
    (readT_spec (B := B) hxB hlB).frame.run
      ⟨h0len, h0inp, by rw [h0arr, replicate_eq_arrOf]; simp [extT]⟩
  have hu₁ : Untouched x σ₁ := by
    have hv : σ₁.vars "top" = σ₀.vars "top" := hfv₁ "top" frame_readT.1
    refine ⟨by rw [hv]; exact h0top, ?_, ?_, ?_, ?_, ?_, by rw [hfo₁ frame_readT.2.2]; exact h0out⟩
    all_goals (rw [hfa₁ _ (frame_readT.2.1 _ (by simp)), h0arr]; simp [extT])
  have harrs₁ : σ₁.arrs "deg" = List.replicate (nw x) 0 ∧ σ₁.arrs "a" = List.replicate x.length 0 ∧
      σ₁.arrs "pos" = List.replicate (nw x) 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> (rw [hfa₁ _ (warrs_checks _ (by simp)).1, h0arr]; simp [extT])
  have hcond4 : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some (decide (x.length < 4)) := by
    rw [← hlen₁]; exact evalB_condLt (evalB_var (by omega)) (evalB_lit (by omega))
  by_cases h4 : x.length < 4
  · -- too short: not well formed
    have hc : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some true := by
      rw [hcond4, decide_eq_true h4]
    refine ⟨_, _, r1.seq (Run.ite_true hc (write_run 0 (by omega))), ?_, ?_⟩
    · simp only [size_condLt, size_var, size_lit]; unfold totCost; omega
    · show σ₁.out ++ [0] = _
      rw [hu₁.out, saturatingAnswer_of_not (notWellFormed_of_short h4)]; rfl
  have hc4 : (Cond.lt (.var "len") (.lit 4)).evalB B σ₁ = some false := by
    rw [hcond4, decide_eq_false h4]
  -- the header
  obtain ⟨σ₂, r2, hq₂⟩ := (hdrT_spec (B := B) hxB hlB (by omega)).run (σ := σ₁) ⟨htab₁, hlen₁⟩
  have hb₂ : Base x σ₂ := by
    rw [hq₂]; exact ⟨htab₁.congr rfl, by simpa using hlen₁, by simp, by simp, by simp⟩
  have hA₂ : Aux x σ₂ := by
    rw [hq₂]
    refine ⟨?_, ?_, harrs₁.1, harrs₁.2.1, harrs₁.2.2⟩
    · rw [← hq₂]; exact hb₂
    · exact ((hu₁.setVar "V" (by decide) _).setVar "E" (by decide) _).setVar "n" (by decide) _
  -- ok := 1
  have r3 := RunStep.assign B σ₂ "ok" (.lit 1) 1 (RunStep.eval_lit B 1 σ₂ h1B)
  set σ₃ := σ₂.setVar "ok" 1 with hσ₃
  have hA₃ : Aux x σ₃ := hA₂.setVar "ok" (by simp) 1
  -- check 1
  obtain ⟨σ₄, r4, ⟨hb₄, hok₄, hiff₄⟩, hfv₄, hfa₄, -, hfo₄⟩ :=
    (chk1_spec (B := B) hBV).frame.run (σ := σ₃) ⟨hA₃.base, by simp [hσ₃]⟩
  have hA₄ : Aux x σ₄ := hA₃.of_run hb₄ r4 frame_chk1.1 frame_chk1.2.1 frame_chk1.2.2
    (fun a ha => (warrs_checks a ha).2.2.1)
  -- check 2, guarded
  obtain ⟨σ₅, K₅, r5, hK₅, hok₅, hiff₅, hA₅⟩ := guarded_run (B := B) (Q' := offw x 0 = 0 ∧
      offw x (Vw x) = 2 * x.getD 1 0 ∧ ∀ i < Vw x, offw x i ≤ offw x (i + 1))
    (Kc := 16 + 16 + ((20 + 4) * Vw x + 6)) (Aux x) h1B hok₄ hiff₄ hA₄ (fun hok => by
      have hlen : x.length = 4 + Vw x + 2 * x.getD 1 0 := (hiff₄.1 hok).2
      obtain ⟨σ', r, ⟨hb', hok', hiff'⟩, -, -, -, -⟩ :=
        (chk2_spec (B := B) hxB hB hlen).frame.run (σ := σ₄) ⟨hA₄.base, hok⟩
      exact ⟨σ', _, r, le_rfl, hok', hiff', hA₄.of_run hb' r frame_chk2.1 frame_chk2.2.1
        frame_chk2.2.2 (fun a ha => (warrs_checks a ha).2.2.2.1)⟩)
  -- check 3, guarded
  obtain ⟨σ₆, K₆, r6, hK₆, hok₆, hiff₆, hA₆⟩ := guarded_run (B := B)
    (Q' := ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x)
    (Kc := 4 + ((20 + 4) * (2 * x.getD 1 0) + 6)) (Aux x) h1B hok₅ hiff₅ hA₅ (fun hok => by
      have hlen : x.length = 4 + Vw x + 2 * x.getD 1 0 := (hiff₅.1 hok).1.2
      obtain ⟨σ', r, ⟨hb', hok', hiff'⟩, -, -, -, -⟩ :=
        (chk3_spec (B := B) hxB hB hlen).frame.run (σ := σ₅) ⟨hA₅.base, hok⟩
      exact ⟨σ', _, r, le_rfl, hok', hiff', hA₅.of_run hb' r frame_chk3.1 frame_chk3.2.1
        frame_chk3.2.2 (fun a ha => (warrs_checks a ha).2.2.2.2)⟩)
  -- the degree pass, guarded: afterwards `ok = 1 ↔ WellFormed x`
  have hWF3 : σ₆.vars "ok" = 1 → WF3 x := fun hok => by
    obtain ⟨⟨⟨h1, h2⟩, h3, h4, h5⟩, h6⟩ := hiff₆.1 hok
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hokB₆ : σ₆.vars "ok" < B := by omega
  have hdegPass : ∃ σ' K, Run B (guarded degPass) σ₆ σ' K ∧
      K ≤ 5 + (if σ₆.vars "ok" = 1 then (30 + 8) * (2 * x.getD 1 0) + 22 * Vw x + 6 else 0) ∧
      σ'.vars "ok" ≤ 1 ∧
      (σ'.vars "ok" = 1 ↔ WellFormed x) ∧ Base x σ' ∧ Untouched x σ' ∧
      σ'.arrs "a" = List.replicate x.length 0 ∧ σ'.arrs "pos" = List.replicate (nw x) 0 ∧
      (σ'.vars "ok" = 1 → DegOK x σ') := by
    by_cases hok : σ₆.vars "ok" = 1
    · have h3 := hWF3 hok
      have hcond := RunStep.cond_eq_true B σ₆ (.var "ok") (.lit 1) _ _
        (RunStep.eval_var B σ₆ "ok" hokB₆) (RunStep.eval_lit B 1 σ₆ h1B) hok
      obtain ⟨σ', r, ⟨hb', hok', hiff', hdeg', hlen'⟩, -, hfa', -, -⟩ :=
        (degPass_spec (B := B) h3 hB).frame.run (σ := σ₆) ⟨hA₆.base, hok, hA₆.deg⟩
      refine ⟨σ', _, RunStep.ite_true B _ degPass .skip σ₆ σ' _ hcond r,
        by rw [if_pos hok]; simp only [size_condEq, size_var, size_lit]; omega, hok', hiff', hb',
        hA₆.unt.of_run r frame_degPass.1 frame_degPass.2.1 frame_degPass.2.2, ?_, ?_,
        fun h => ⟨hlen', hdeg' h⟩⟩
      · rw [hfa' "a" (warrs_degPass _ (by simp))]; exact hA₆.a
      · rw [hfa' "pos" (warrs_degPass _ (by simp))]; exact hA₆.pos
    · have hcond := RunStep.cond_eq_false B σ₆ (.var "ok") (.lit 1) _ _
        (RunStep.eval_var B σ₆ "ok" hokB₆) (RunStep.eval_lit B 1 σ₆ h1B) hok
      refine ⟨σ₆, _, RunStep.ite_false B _ degPass .skip σ₆ σ₆ 1 hcond (RunStep.skip B σ₆),
        by rw [if_neg hok]; simp only [size_condEq, size_var, size_lit]; omega,
        hok₆, ⟨fun h => absurd h hok, fun hw => absurd (hiff₆.2 (wellFormed_iff.1 hw |>.elim
          (fun h3 hc => ⟨⟨⟨h3.nV, h3.len⟩, h3.off0, h3.offV, h3.mono⟩, h3.tgt_lt⟩))) hok⟩,
        hA₆.base, hA₆.unt, hA₆.a, hA₆.pos, fun h => absurd h hok⟩
  obtain ⟨σ₇, K₇, r7, hK₇, hok₇, hiff₇, hb₇, hu₇, ha₇, hpos₇, hdeg₇⟩ := hdegPass
  have hokB₇ : σ₇.vars "ok" < B := by omega
  -- the answer
  by_cases hok : σ₇.vars "ok" = 1
  · have hw : WellFormed x := hiff₇.1 hok
    have hcond := RunStep.cond_eq_true B σ₇ (.var "ok") (.lit 1) _ _
      (RunStep.eval_var B σ₇ "ok" hokB₇) (RunStep.eval_lit B 1 σ₇ h1B) hok
    obtain ⟨σ₈, K₈, r8, hK₈, hout₈⟩ := heavyTot_run hw hB hb₇ (hdeg₇ hok) ha₇
      (by rw [hpos₇]; simp) hu₇
    refine ⟨σ₈, _, r1.seq (Run.ite_false hc4 (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq
      (RunStep.ite_true B _ heavyTot _ σ₇ σ₈ _ hcond r8)))))))), ?_, ?_⟩
    · have hxlen := wf_len hw
      have hVx : Vw x ≤ x.length := by omega
      have hEx : 2 * x.getD 1 0 ≤ x.length := by omega
      simp only [size_condLt, size_condEq, size_var, size_lit]
      unfold totCost
      rw [if_pos hw]
      split_ifs at hK₅ hK₆ hK₇ <;> omega
    · rw [hout₈]
      unfold saturatingAnswer
      by_cases hs : ∃ M : (wordGraph x).Subgraph, M.IsMatching ∧
          Saturates (wordGraph x) M (leftSide (vertexCount x) (leftCount x))
      · rw [if_pos (show kuhnSize (sx x) = nw x from (kuhnSize_sx_iff hw).2 hs), if_pos ⟨hw, hs⟩]
      · rw [if_neg (show ¬ kuhnSize (sx x) = nw x from fun h => hs ((kuhnSize_sx_iff hw).1 h)),
          if_neg (fun h => hs h.2)]
  · have hnw : ¬ WellFormed x := fun hw => hok (hiff₇.2 hw)
    have hcond := RunStep.cond_eq_false B σ₇ (.var "ok") (.lit 1) _ _
      (RunStep.eval_var B σ₇ "ok" hokB₇) (RunStep.eval_lit B 1 σ₇ h1B) hok
    refine ⟨_, _, r1.seq (Run.ite_false hc4 (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq
      (RunStep.ite_false B _ heavyTot _ σ₇ _ 2 hcond (write_run 0 (by omega)))))))))), ?_, ?_⟩
    · -- the cost, by whether the checks ran
      simp only [size_condLt, size_condEq, size_var, size_lit]
      unfold totCost
      rw [if_neg hnw]
      by_cases hQ1 : nw x ≤ Vw x ∧ x.length = 4 + Vw x + 2 * x.getD 1 0
      · have hVx : Vw x ≤ x.length := by omega
        have hEx : 2 * x.getD 1 0 ≤ x.length := by omega
        split_ifs at hK₅ hK₆ hK₇ <;> omega
      · -- the flag fell at the first check: every later phase was skipped
        have h4' : σ₄.vars "ok" ≠ 1 := fun h => hQ1 (hiff₄.1 h)
        have h5' : σ₅.vars "ok" ≠ 1 := fun h => hQ1 (hiff₅.1 h).1
        have h6' : σ₆.vars "ok" ≠ 1 := fun h => hQ1 (hiff₆.1 h).1.1
        rw [if_neg h4'] at hK₅
        rw [if_neg h5'] at hK₆
        rw [if_neg h6'] at hK₇
        omega
    · show σ₇.out ++ [0] = _
      rw [hu₇.out, saturatingAnswer_of_not hnw]; rfl

end Lax117284Proofs.Bipartite.Ram2
