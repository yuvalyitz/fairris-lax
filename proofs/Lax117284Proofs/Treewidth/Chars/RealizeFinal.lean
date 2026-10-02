import Lax117284Proofs.Treewidth.Chars.RealizeIR
import Lax117284Proofs.Treewidth.Chars.IntroMono
import Lax117284Proofs.Treewidth.Chars.MergeFinal
import Lax117284Proofs.Treewidth.Chars.Forget

/-!
# `applyPlan_spec`, `realIntro_spec`, `realize_intro` (work package C5)

The realisation of an introduce plan.  **Repair**: all three statements get the hypothesis
`hs : ∀ u ∈ c.under, adj u v = true → adj v u = true` (the neighbours of `v` below are read through `adj v ·` in
`NT.Good`, but the graph of the tree decomposition is the *symmetric* closure `Adj.graph`; without `hs` an edge
`{v, w}` present only as `adj w v` would need a bag containing `v` and `w ∉ c.bag`, which no realisation provides).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem applyPlan_spec {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {path : List ℕ} {p : Plan} {r : CT}
    (hr : (path, p, r) ∈ CT.introPlans v (nbrs adj v c.bag) (t.char c.bag))
    (hk : (CT.norm r).maxEntry ≤ k + 1) :
    PTD adj (.intro v c) k (applyPlan v (nbrs adj v c.bag) c.bag path p t) ∧
      DomC ((applyPlan v (nbrs adj v c.bag) c.bag path p t).char (insert v c.bag)) (CT.norm r) := by
  have hg' : v ∉ c.bag ∧ (∀ u ∈ c.under, adj v u = true → u ∈ c.bag) ∧ v ∉ c.under ∧ NT.Good adj c := hg
  obtain ⟨hvB, hclos, hvU, hgc⟩ := hg'
  set B := c.bag with hB
  set A := analyze B t with hA
  have hverts : (AR.toRT A).verts = c.under := by rw [hA, verts_toRT_analyze, h.1.verts_eq]
  have hfree : v ∉ (AR.toRT A).verts := by rw [hverts]; exact hvU
  have hx : RunOk v B A := ⟨analyze_canon B t, hfree⟩
  have hchar : t.char B = AR.charF Finset.card A := char_eq_charF B t
  have hcn : CT.Conn (AR.charF Finset.card A) := by
    rw [← hchar]
    exact conn_norm _ (RT.conn_prof B t h.1.conn)
  rw [hchar] at hr
  have hir := ir_claim v B hvB (nbrs adj v B) A hx hcn path p r hr
  unfold applyPlan
  rw [← hA]
  set x' := applyRun v p path A with hx'
  have hti := hir.ti
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- vertices
    ext z
    change z ∈ (AR.toRT x').verts ↔ z ∈ insert v c.under
    rw [Finset.mem_insert]
    constructor
    · intro hz
      rcases hti.vsub z hz with h1 | h1
      · rw [hverts] at h1; exact Or.inr h1
      · exact Or.inl h1
    · rintro (rfl | hz)
      · exact hir.vin
      · exact hti.vsup z (by rw [hverts]; exact hz)
  · -- edges
    intro u w huw hu hw
    have hu' : u ∈ insert v c.under := hu
    have hw' : w ∈ insert v c.under := hw
    have hadj : u ≠ w ∧ (adj u w = true ∨ adj w u = true) := by
      simpa [Adj.graph, SimpleGraph.fromRel_adj] using huw
    have hnbr : ∀ z ∈ c.under, adj v z = true → z ∈ nbrs adj v B := by
      intro z hz hvz
      exact Finset.mem_filter.2 ⟨hclos z hz hvz, hvz⟩
    by_cases huv : u = v
    · subst huv
      have hwU : w ∈ c.under := by
        rcases Finset.mem_insert.1 hw' with rfl | h1
        · exact absurd rfl hadj.1
        · exact h1
      have hvw : adj u w = true := by
        rcases hadj.2 with h1 | h1
        · exact h1
        · exact hs w hwU h1
      obtain ⟨Y, hY, hvY, hwY⟩ := hir.cov w (hnbr w hwU hvw)
      exact ⟨Y, hY, hvY, hwY⟩
    · by_cases hwv : w = v
      · subst hwv
        have huU : u ∈ c.under := by
          rcases Finset.mem_insert.1 hu' with rfl | h1
          · exact absurd rfl huv
          · exact h1
        have hvu : adj w u = true := by
          rcases hadj.2 with h1 | h1
          · exact hs u huU h1
          · exact h1
        obtain ⟨Y, hY, hvY, huY⟩ := hir.cov u (hnbr u huU hvu)
        exact ⟨Y, hY, huY, hvY⟩
      · have huU : u ∈ c.under := (Finset.mem_insert.1 hu').resolve_left huv
        have hwU : w ∈ c.under := (Finset.mem_insert.1 hw').resolve_left hwv
        obtain ⟨X, hX, hxu, hxw⟩ := h.1.edges u w huw huU hwU
        obtain ⟨Y, hY, hXY⟩ := hti.bsup X ((mem_bags_toRT_analyze B t X).2 hX)
        exact ⟨Y, hY, hXY hxu, hXY hxw⟩
  · -- connectedness
    rw [conn_iff_tc]
    intro u
    by_cases huv : u = v
    · subst huv; rw [hir.tcv]
    · rw [hti.tcne u huv false]
      exact (conn_iff_tc _).1 (conn_toRT_analyze B t h.1.conn) u
  · -- width
    intro Y hY
    rcases hti.bnew Y hY with hvY | ⟨X, hX, hYX⟩
    · exact (hir.wid Y hY hvY).trans hk
    · exact (Finset.card_le_card hYX).trans (width_toRT_analyze B h.2 X hX)
  · -- the characteristic
    obtain ⟨Q, hQ, hdom⟩ := hir.chr
    have : (AR.toRT x').char (insert v B) = norm (RT.prof (insert v B) (AR.toRT x')) := rfl
    show DomC (RT.char (insert v B) (AR.toRT x')) (norm r)
    unfold RT.char
    rw [hQ]
    exact norm_mono hdom

/-- **Introduce, realised.** -/
theorem realize_intro {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {c' : CT} (hc' : c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) (t.char c.bag)) :
    ∃ t', PTD adj (.intro v c) k t' ∧ DomC (t'.char (insert v c.bag)) c' := by
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hc'
  obtain ⟨path, plan, hp⟩ := IR_toPlans v _ hr
  obtain ⟨h1, h2⟩ := applyPlan_spec hg hs h hp hk
  exact ⟨_, h1, h2⟩

/-- **The introduce step of the extraction.** -/
theorem realIntro_spec {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (hs : ∀ u ∈ c.under, adj u v = true → adj v u = true)
    (h : PTD adj c k t) {ca c' : CT} (hca : DomC (t.char c.bag) ca)
    (hc' : c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) ca) :
    ∃ t', realIntro (k + 1) v (nbrs adj v c.bag) c.bag t c' = some t' ∧ PTD adj (.intro v c) k t' ∧
      DomC (t'.char (insert v c.bag)) c' := by
  obtain ⟨d, hd, hdc⟩ := introC_mono (k + 1) v (nbrs adj v c.bag) hca c' hc'
  obtain ⟨r, hr, rfl, hk⟩ := mem_introC.1 hd
  obtain ⟨path, plan, hp⟩ := IR_toPlans v _ hr
  have hsome : ((CT.introPlans v (nbrs adj v c.bag) (t.char c.bag)).find?
      (fun r => domCB (CT.norm r.2.2) c' && decide ((CT.norm r.2.2).maxEntry ≤ k + 1))).isSome = true :=
    List.find?_isSome.2 ⟨(path, plan, r), hp, by simp [domCB_iff.2 hdc, hk]⟩
  obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hr0
  have hpred := List.find?_some hr0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨hdom0, hk0⟩ := hpred
  obtain ⟨p1, p2⟩ := applyPlan_spec hg hs h hmem hk0
  refine ⟨_, ?_, p1, DomC.trans p2 (domCB_iff.1 hdom0)⟩
  unfold realIntro
  rw [hr0]; rfl

end Lax117284Proofs.Treewidth.Chars
