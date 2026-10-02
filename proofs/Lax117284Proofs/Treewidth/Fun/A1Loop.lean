import Lax117284Proofs.Treewidth.Fun.A1Imp

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (3): the round loop

`loopC adj k j m t` runs the `m` rounds `j, j+1, …, j+m-1` from the nice tree `t` (of `range j`);
`decomposeC adj k (j + m) = loopC adj k j m t` when `decomposeC adj k j = some t`.

`loop_runs`: for `j + m = n` the F-function `fLoop` evaluates `[x, k, n, j, t]` to `loopC …`
within `m · cRound M k + 10` steps.  The per-round preconditions come from the math layer:
* `addEverywhere_isNiceTD` (round `j`: `range j ↦ range (j+1)`, width `k ↦ k+1`, needs `j ∉ range j`);
* `good_of_isNiceTD`, `IsNiceTD.2.2` (Width) ⇒ `ntOk`; `symmOn` on `range n` and `under = range (j+1) ⊆ range n` ⇒ `ExtOk`;
* `size_addEverywhere_le`, `sz_nt_le_size`, the invariant `size ≤ (j+2)²` (`improveC_correct`) ⇒ `sz a ≤ M`;
* `mx_nt_le_of_wf` (`Wf` from `IsNiceTD`, vertices `< n`) ⇒ `mx a ≤ n + 3`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT CT
open E4 (adjOfWord nOfWord ntOk)

/-! ## the math side -/

/-- `m` rounds starting at round `j` -/
def loopC (adj : Adj) (k : ℕ) : ℕ → ℕ → NT → Option NT
  | _, 0, t => some t
  | j, m + 1, t => (improveC adj k (NT.addEverywhere j t)).bind (fun t' => loopC adj k (j + 1) m t')

theorem decomposeC_none_add (adj : Adj) (k : ℕ) :
    ∀ m i, decomposeC adj k i = none → decomposeC adj k (i + m) = none := by
  intro m
  induction m with
  | zero => intro i h; simpa using h
  | succ m ih =>
    intro i h
    have := ih i h
    show decomposeC adj k (i + m + 1) = none
    simp [decomposeC, this]

theorem decomposeC_loop (adj : Adj) (k : ℕ) :
    ∀ m j t, decomposeC adj k j = some t → decomposeC adj k (j + m) = loopC adj k j m t := by
  intro m
  induction m with
  | zero => intro j t h; simpa [loopC] using h
  | succ m ih =>
    intro j t h
    have e : j + (m + 1) = (j + 1) + m := by omega
    rw [e]
    have hs : decomposeC adj k (j + 1) = improveC adj k (NT.addEverywhere j t) := by
      simp [decomposeC, h]
    have hl : loopC adj k j (m + 1) t = (improveC adj k (NT.addEverywhere j t)).bind
        (fun t' => loopC adj k (j + 1) m t') := rfl
    rw [hl]
    rcases hi : improveC adj k (NT.addEverywhere j t) with _ | t'
    · rw [hi] at hs
      simp [decomposeC_none_add adj k m (j + 1) hs]
    · rw [hi] at hs
      simpa using ih (j + 1) t' hs

/-- the invariant at the start of round `j` -/
def LoopInv (adj : Adj) (k j : ℕ) (t : NT) : Prop :=
  t.IsNiceTD adj.graph (Finset.range j) k ∧ t.size ≤ (j + 2) * (j + 2)

theorem loopInv_zero (adj : Adj) (k : ℕ) : LoopInv adj k 0 NT.leaf := by
  refine ⟨⟨trivial, ⟨rfl, fun u v _ hu _ => absurd hu (by simp), by simp [NT.toRT, RT.Conn, RT.ConnL]⟩,
      by intro X hX; simp [NT.toRT, RT.bags, RT.bagsL] at hX; simp [hX]⟩, by simp [NT.size]⟩

/-- after `addEverywhere j` -/
theorem round_add {adj : Adj} {k j : ℕ} {t : NT} (h : LoopInv adj k j t) :
    (NT.addEverywhere j t).IsNiceTD adj.graph (Finset.range (j + 1)) (k + 1) := by
  have := addEverywhere_isNiceTD (v := j) h.1 (by simp)
  rwa [← Finset.range_add_one] at this

/-- the step of the invariant -/
theorem round_next {adj : Adj} {W : Finset ℕ} (hs : adj.SymmOn W) {k j n : ℕ} {t : NT}
    (hj : j + 1 ≤ n) (hW : Finset.range n ⊆ W) (h : LoopInv adj k j t) {t' : NT}
    (ht' : improveC adj k (NT.addEverywhere j t) = some t') : LoopInv adj k (j + 1) t' := by
  have hadd := round_add h
  have hU : Finset.range (j + 1) ⊆ W := (Finset.range_subset_range.2 hj).trans hW
  obtain ⟨-, j2⟩ := improveC_correct hs hU hadd k
  obtain ⟨a, b⟩ := j2 t' ht'
  refine ⟨a, ?_⟩
  simpa [Finset.card_range] using b

/-- the round-`j` input tree `a = addEverywhere j t` -/
theorem round_facts {adj : Adj} {k j n : ℕ} {t : NT} (hj : j + 1 ≤ n) (h : LoopInv adj k j t) :
    (NT.addEverywhere j t).Good adj ∧ (NT.addEverywhere j t).toRT.Width (k + 1) ∧
    (NT.addEverywhere j t).under = Finset.range (j + 1) ∧
    (NT.addEverywhere j t).Wf ∧ (NT.addEverywhere j t).size ≤ 2 * ((n + 1) * (n + 1)) := by
  have hadd := round_add h
  refine ⟨good_of_isNiceTD hadd, hadd.2.2, ?_, hadd.1, ?_⟩
  · rw [NT.under_eq_vs]; exact hadd.2.1.verts_eq
  · have h1 := size_addEverywhere_le j t
    have h2 := h.2
    have h3 : (j + 2) * (j + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-! ## the run -/

/-- the per-round cost -/
def cRound (M k : ℕ) : ℕ := 30 * M + cIC M k + 30

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

/-- **the round loop**: for `j + m = n`, from a nice tree of `range j` -/
theorem loop_runs (B : ℕ) (x : List ℕ) (k n M Mv Ctot : ℕ) (hnx : n = nOfWord x)
    (hs : (adjOfWord x).SymmOn (Finset.range n)) (hxM : x.length ≤ M) (hMs : 8 * ((n + 1) * (n + 1)) ≤ M)
    (hnM : n + 3 ≤ M) (hnMv : n + 3 ≤ Mv) (hk : k + 2 < B) (hCt : n * cRound M k + 10 ≤ Ctot)
    (hB : (Mv + Ctot + 2) ^ 2 < B) :
    ∀ m j (t : NT), j + m = n → LoopInv (adjOfWord x) k j t →
      Runs Δ' B fLoop [toVal x, toVal k, toVal n, toVal j, toVal t] (toVal (loopC (adjOfWord x) k j m t))
        (m * cRound M k + 10) := by
  have hnB : n + 3 < B := by
    have : n + 3 ≤ (Mv + Ctot + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Ctot + 2)]
    omega
  intro m
  induction m with
  | zero =>
    intro j t hjm hinv
    have hj : j = n := by omega
    subst hj
    simp only [loopC, toVal_some]
    refine Runs.mk (h1 _ _ Δ_loop) ?_
    ev_start
    · ev_run
    · omega
  | succ m ih =>
    intro j t hjm hinv
    have hjn : j + 1 ≤ n := by omega
    have hne : j ≠ n := by omega
    simp only [loopC]
    obtain ⟨hg, hw, hund, hwf, hsz⟩ := round_facts hjn hinv
    set a := NT.addEverywhere j t with ha
    have hszM : sz a ≤ M := by
      have := sz_nt_le_size a
      omega
    have hmxa : mx a ≤ n + 3 := by
      refine mx_nt_le_of_wf hwf (by omega) fun v hv => ?_
      rw [hund] at hv
      have := Finset.mem_range.1 hv
      omega
    have hok : E6b.ExtOk x k a :=
      ⟨⟨hg, hw⟩, Finset.range n, hs, by rw [hund]; exact Finset.range_subset_range.2 hjn⟩
    have hcR : cRound M k ≤ n * cRound M k := by
      have : 1 ≤ n := by omega
      nlinarith [Nat.zero_le (cRound M k)]
    have hnx2 : (nOfWord x) ^ 2 < B := by
      rw [← hnx]
      have : n ^ 2 ≤ (Mv + Ctot + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hIC : cIC M k ≤ Ctot := by
      have : cIC M k ≤ cRound M k := by unfold cRound; omega
      omega
    have hBi : (Mv + cIC M k + 2) ^ 2 < B :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
    have hImp := improveC_runs hΔ h6a h1 B x k a M Mv hxM hszM (by omega) (by omega) hok hnx2 hk hBi
    have hAdd := E6a.addEv_runs h6a B j (by omega) t
    have hAdd' : Runs Δ' B E6a.fAddEv [toVal j, toVal t] (toVal a) (30 * t.size) := hAdd
    have htM : t.size ≤ M := by
      have := hinv.2
      have h3 : (j + 2) * (j + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      have : (n + 1) * (n + 1) ≤ M := by omega
      omega
    rcases hi : improveC (adjOfWord x) k a with _ | t'
    · rw [hi] at hImp
      simp only [Option.bind_none, toVal_none] at hImp ⊢
      refine Runs.mk (h1 _ _ Δ_loop) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hne]
      · have : (m + 1) * cRound M k = m * cRound M k + cRound M k := by ring
        unfold cRound at this ⊢
        omega
    · have hinv' : LoopInv (adjOfWord x) k (j + 1) t' :=
        round_next hs hjn (le_refl _) hinv hi
      have hrec := ih (j + 1) t' (by omega) hinv'
      rw [hi] at hImp
      simp only [Option.bind_some, toVal_some] at hImp ⊢
      refine Runs.mk (h1 _ _ Δ_loop) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hne]
      · have : (m + 1) * cRound M k = m * cRound M k + cRound M k := by ring
        unfold cRound at this ⊢
        omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun
