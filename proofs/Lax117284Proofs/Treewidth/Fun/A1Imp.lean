import Lax117284Proofs.Treewidth.Fun.A1Defs
import Lax117284Proofs.Treewidth.Fun.E6bFinal
import Lax117284Proofs.Treewidth.Wrap.ImproveC

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (2): `improveC` as an F-function

`improveC adj k nt = (extractFirst adj k nt).map (niceOf ∘ compress)` and the run of `fImproveC` on the input
`(x, k, nt)`; cost `cIC M k` for every `M ≥ |x|, sz nt, mx nt`.

Preconditions: `ExtOk x k nt` (Good, width `k + 1`, `adjOfWord x` symmetric on a set containing the vertices of `nt`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord ntOk)

theorem improveC_eq_map (adj : Adj) (k : ℕ) (nt : NT) :
    improveC adj k nt = (E6b.extractFirst adj k nt).map (fun t => niceOf (compress t)) := by
  unfold improveC E6b.extractFirst
  cases tables adj k nt <;> simp

/-- the size bound of the extracted tree in terms of the nice tree -/
def sBnd (k M : ℕ) : ℕ := (2 * k + 8) * (2 * k + 6) * M

/-- the cost of `improveC` -/
def cIC (M k : ℕ) : ℕ :=
  (M * E4.cnode M k + M ^ 2 * E6b.Wx M k + 30) + 400 * (2 * sBnd k M + 1) ^ 3 + 8000 * (sBnd k M + 2) ^ 5 + 40

/-- facts about the extracted tree -/
theorem extractFirst_facts {x : List ℕ} {k : ℕ} {nt : NT} (hok : E6b.ExtOk x k nt) {t' : RT}
    (h : E6b.extractFirst (adjOfWord x) k nt = some t') :
    t'.IsTD (adjOfWord x).graph nt.under ∧ t'.Width k ∧ sz t' ≤ (2 * k + 8) * (2 * k + 6) * nt.size := by
  obtain ⟨⟨hg, hw⟩, W, hs, hW⟩ := hok
  unfold E6b.extractFirst at h
  rcases hcase : tables (adjOfWord x) k nt with _ | ⟨c, T'⟩
  · rw [hcase] at h; simp at h
  · rw [hcase] at h
    have hc : c ∈ tables (adjOfWord x) k nt := by rw [hcase]; simp
    obtain ⟨t, ht, hp, -⟩ := extract_spec (k := k) hs hg hW c hc
    simp only at h
    rw [ht] at h
    cases h
    exact ⟨hp.1, hp.2, extract_sz_le hs hg hW hw c hc t' ht⟩

theorem mx_rt_le_of_isTD {t : RT} {U : Finset ℕ} {G : SimpleGraph ℕ} (h : t.IsTD G U) {M : ℕ}
    (hM : ∀ v ∈ U, v ≤ M) : mx t ≤ M :=
  (mx_rt_le_iff t).2 fun v hv => hM v (h.verts_eq ▸ hv)

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

theorem improveC_runs (B : ℕ) (x : List ℕ) (k : ℕ) (nt : NT) (M Mv : ℕ) (hxM : x.length ≤ M)
    (hsM : sz nt ≤ M) (hmM : mx nt ≤ M) (hmv : mx nt ≤ Mv) (hok : E6b.ExtOk x k nt)
    (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) (hB : (Mv + cIC M k + 2) ^ 2 < B) :
    Runs Δ' B fImproveC [toVal x, toVal k, toVal nt] (toVal (improveC (adjOfWord x) k nt)) (cIC M k) := by
  have hsize : nt.size ≤ M := E4.size_le_M hsM
  have hcn : nt.size * E4.cnode M k ≤ M * E4.cnode M k := Nat.mul_le_mul_right _ hsize
  have hwx : nt.size ^ 2 * E6b.Wx M k ≤ M ^ 2 * E6b.Wx M k :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsize 2)
  have hB1 : (nt.size * E4.cnode M k + nt.size ^ 2 * E6b.Wx M k + 30 + 2) ^ 2 < B := by
    refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
    unfold cIC; omega
  have hT := E6b.extractFirst_runs hΔ B x k nt M hxM hsM hmM hok hn hk hB1
  rw [improveC_eq_map]
  rcases hcase : E6b.extractFirst (adjOfWord x) k nt with _ | t'
  · rw [hcase] at hT
    simp only [Option.map_none, toVal_none] at hT ⊢
    refine Runs.mk (h1 _ _ Δ_improveC) ?_
    ev_start
    · ev_run
    · unfold cIC; omega
  · obtain ⟨htd, hw, hsz⟩ := extractFirst_facts hok hcase
    rw [hcase] at hT
    simp only [Option.map_some, toVal_some] at hT ⊢
    have hunder : ∀ v ∈ nt.under, v ≤ Mv := fun v hv => le_trans (under_le_mx_nt nt hv) hmv
    have hctd := compress_isTD htd
    have hmt' : mx t' ≤ Mv := mx_rt_le_of_isTD htd hunder
    have hmc : mx (compress t') ≤ Mv := mx_rt_le_of_isTD hctd hunder
    have hszc := E6a.sz_compress_le t'
    have hS : sz t' ≤ sBnd k M := by
      unfold sBnd; exact le_trans hsz (Nat.mul_le_mul_left _ hsize)
    have hc2 : 400 * (sz t' + sz (compress t') + 1) ^ 3 ≤ 400 * (2 * sBnd k M + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have hc3 : 8000 * (sz (compress t') + 2) ^ 5 ≤ 8000 * (sBnd k M + 2) ^ 5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)
    have hf2 : Fits B (toVal t') (400 * (sz t' + sz (compress t') + 1) ^ 3) := by
      unfold Fits
      refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
      show mx t' + _ + 2 ≤ _
      unfold cIC; omega
    have hf3 : Fits B (toVal (compress t')) (8000 * (sz (compress t') + 2) ^ 5) := by
      unfold Fits
      refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
      show mx (compress t') + _ + 2 ≤ _
      unfold cIC; omega
    have hcomp := E6a.embeds_compress h6a B t' trivial hf2
    have hnice := E6a.embeds_niceOf_conn h6a B (compress t') hctd.conn hf3
    beta_reduce at hcomp hnice
    refine Runs.mk (h1 _ _ Δ_improveC) ?_
    ev_start
    · ev_run
    · unfold cIC; omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun
