import Lax117284Proofs.Bipartite.Ram2.SearchLoop

/-!
Restarting the search for the next left vertex: `stkL[0] := l0; stkX[0] := a[2 + l0]; top := 1;
result := 2`, and clear the visited table (`m` stores). The postcondition is `Real` for the
abstract state `AS.restart (offw x) b l0`, exactly what `search_run_restart` asks for.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching
open scoped Classical

variable {B : ℕ}

/-- `vis[j] := 0; j := j + 1`. -/
def clearVisBody : Com :=
  .seq (.store "vis" (.var "j") (.lit 0)) (.assign "j" (.add (.var "j") (.lit 1)))

/-- Clear the visited table: `j := 0; while j < m do clearVisBody`. -/
def clearVis : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "m")) clearVisBody)

/-- The four writes of a restart: frame `0` is `l0` at the first slot of its row. -/
def restartHead : Com :=
  .seq (.store "stkL" (.lit 0) (.var "l0"))
    (.seq (.store "stkX" (.lit 0) (.get "a" (.add (.lit 2) (.var "l0"))))
      (.seq (.assign "top" (.lit 1)) (.assign "result" (.lit 2))))

/-- **Restart**: frame `0` is `l0` at its row's first slot, `top = 1`, `result = 2`, nothing
visited. -/
def restartCom : Com := .seq restartHead clearVis

/-- The invariant of the clearing loop: `m` is in place, `j ≤ m`, and the first `j` cells of
`vis` are zero, the rest as they were (`f`). -/
def ClearInv (m : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "m" = m ∧ σ.vars "j" ≤ m ∧
    σ.arrs "vis" = arrOf m (fun k => if k < σ.vars "j" then 0 else f k)

theorem clearVisBody_spec {m : ℕ} {f : ℕ → ℕ} (hmB : m + 1 < B) (h1B : 1 < B) :
    Spec B (fun σ => ClearInv m f σ ∧ σ.vars "j" < m) clearVisBody
      (fun σ σ' => ClearInv m f σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 9 := by
  rintro σ ⟨⟨hm, hjm, hvis⟩, hj⟩
  have hlen : (σ.arrs "vis").length = m := by rw [hvis]; simp
  unfold clearVisBody
  run_vcg
  all_goals (simp [ClearInv, hm, hvis]; try omega)
  refine ⟨hj, ?_⟩
  rw [set_arrOf_update]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "j"
  · subst hk; simp
  · rw [Function.update_of_ne hk]
    split_ifs <;> first | rfl | omega

theorem clearVis_spec {m : ℕ} {f : ℕ → ℕ} (hmB : m + 1 < B) (h1B : 1 < B) :
    Spec B (fun σ => σ.vars "m" = m ∧ σ.arrs "vis" = arrOf m f) clearVis
      (fun _ σ' => σ'.arrs "vis" = arrOf m (fun _ => 0)) ((9 + 4) * m + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := clearVisBody) "j" "m" (ClearInv m f) m 9
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (clearVisBody_spec hmB h1B)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hm, hv⟩
    refine ⟨by simpa using hm, by simp, ?_⟩
    simpa using hv.trans (arrOf_congr (fun k _ => by simp))
  · rintro σ σ' _ ⟨⟨_, _, hv⟩, hj⟩
    rw [hv]
    exact arrOf_congr (fun k hk => by simp [hj, hk])

section Head

variable {x : List ℕ} {μ : ℕ → Option ℕ} {l0 : ℕ} {b : AS} {σ : Env}

/-- The abstract state after the head of a restart (visited table not yet cleared). -/
def AS.head (off : ℕ → ℕ) (b : AS) (l0 : ℕ) : AS :=
  { b with Ls := Function.update b.Ls 0 l0, Xs := Function.update b.Xs 0 (off l0), top := 1 }

theorem restartHead_spec (hg : Good x) (hB : x.length + 8 ≤ B) (hl : l0 < nw x) :
    Spec B (fun σ => Real x μ b σ ∧ σ.vars "l0" = l0) restartHead
      (fun σ σ' => σ' = (((σ.setArr "stkL" 0 l0).setArr "stkX" 0 (offw x l0)).setVar "top" 1).setVar
        "result" 2) 16 := by
  rintro σ ⟨hR, hl0⟩
  have hlenL := hR.lenL
  have hlenX := hR.lenX
  have hlenA := hR.arr.length
  have hnB : nw x < B := by have := hg.n_lt; omega
  have h2pos : 2 + l0 < x.length := hg.offPos_lt (by have := hg.nV; omega)
  have hoff : (σ.arrs "a").getD (2 + l0) 0 = offw x l0 := hR.arr.getD h2pos
  have hoffB : offw x l0 < B := by
    have := hg.off_lt_len (i := l0) (by have := hg.nV; omega); omega
  rw [List.getD_eq_getElem?_getD] at hoff
  unfold restartHead
  run_vcg
  all_goals (simp [hl0, hoff]; try omega)

theorem Real.head (hR : Real x μ b σ) (l0 : ℕ) :
    Real x μ (AS.head (offw x) b l0)
      ((((σ.setArr "stkL" 0 l0).setArr "stkX" 0 (offw x l0)).setVar "top" 1).setVar "result" 2) := by
  refine ⟨by simp [AS.head], by simpa using hR.V, by simpa using hR.n, by simpa using hR.m,
    hR.arr.congr (by simp), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK
    have := hR.vis
    unfold VisOK at this
    simp only [arrs_setVar, arrs_setArr]
    simp
    exact this
  · simpa [MuOK] using hR.mu
  · simp [hR.stkL, set_arrOf_update, AS.head]
  · simpa [AS.head] using hR.stkR
  · simp [hR.stkX, set_arrOf_update, AS.head]

theorem Real.clear {a : AS} {σ' : Env} (hR : Real x μ a σ)
    (hv : σ'.arrs "vis" = arrOf (mw x) (fun _ => 0)) (ha : ∀ c, c ≠ "vis" → σ'.arrs c = σ.arrs c)
    (ht : σ'.vars "top" = σ.vars "top") (hV : σ'.vars "V" = σ.vars "V")
    (hn : σ'.vars "n" = σ.vars "n") (hm : σ'.vars "m" = σ.vars "m") :
    Real x μ { a with visB := fun _ => False } σ' := by
  refine ⟨by rw [ht]; exact hR.top, by rw [hV]; exact hR.V, by rw [hn]; exact hR.n,
    by rw [hm]; exact hR.m, hR.arr.congr (ha _ (by decide)), ?_, ?_, ?_, ?_, ?_⟩
  · unfold VisOK; rw [hv]; exact arrOf_congr (fun k _ => by simp)
  · unfold MuOK; rw [ha _ (by decide)]; exact hR.mu
  · rw [ha _ (by decide)]; exact hR.stkL
  · rw [ha _ (by decide)]; exact hR.stkR
  · rw [ha _ (by decide)]; exact hR.stkX

/-- The cost of a restart. -/
def restartCost (x : List ℕ) : ℕ := 16 + ((9 + 4) * mw x + 6)

/-- **Restart**: from any state realizing `b`, with `l0 < n` in the scalar `"l0"`, the search
state is that of `AS.restart (offw x) b l0`, `result` is `2`, and every scalar but `top`,
`result`, `j` is unchanged. -/
theorem restart_spec (hg : Good x) (hB : x.length + 8 ≤ B) (hl : l0 < nw x) :
    Spec B (fun σ => Real x μ b σ ∧ σ.vars "l0" = l0) restartCom
      (fun σ σ' => Real x μ (AS.restart (offw x) b l0) σ' ∧ σ'.vars "result" = 2 ∧
        ∀ y, y ≠ "top" → y ≠ "result" → y ≠ "j" → σ'.vars y = σ.vars y)
      (restartCost x) := by
  intro σ hσ
  have hmB : mw x + 1 < B := by have := hg.m_lt; omega
  obtain ⟨σ₁, hr1, hq1⟩ := (restartHead_spec (μ := μ) (b := b) hg hB hl).run hσ
  have hR₁ : Real x μ (AS.head (offw x) b l0) σ₁ := by rw [hq1]; exact hσ.1.head l0
  obtain ⟨σ₂, hr2, hq2, hfv, hfa, -, -⟩ :=
    (clearVis_spec (B := B) (m := mw x) (f := fun k => if b.visB k then 1 else 0) hmB
      (by omega)).frame.run ⟨hR₁.m, hR₁.vis⟩
  have hv2 : ∀ y, y ≠ "j" → σ₂.vars y = σ₁.vars y := fun y hy =>
    hfv y (by simp [clearVis, clearVisBody, Com.wvars, hy])
  have ha2 : ∀ c, c ≠ "vis" → σ₂.arrs c = σ₁.arrs c := fun c hc =>
    hfa c (by simp [clearVis, clearVisBody, Com.warrs, hc])
  refine ⟨σ₂, (hr1.seq hr2), ?_, ?_, fun y h1 h2 h3 => ?_⟩
  · exact (hR₁.clear hq2 ha2 (hv2 _ (by decide)) (hv2 _ (by decide)) (hv2 _ (by decide))
      (hv2 _ (by decide)) : _)
  · rw [hv2 _ (by decide), hq1]; simp
  · rw [hv2 y h3, hq1]; simp [h1, h2]

end Head

end Lax117284Proofs.Bipartite.Ram2
