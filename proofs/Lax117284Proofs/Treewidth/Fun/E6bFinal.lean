import Lax117284Proofs.Treewidth.Fun.E6bRun

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (15): `E_extract` — the `Embeds` statements

* `embeds_extract`   : `fExtractUn` (packed argument `(x, k, nt, target)`) computes `extract (adjOfWord x) k nt target`
  within `nt.size² · Wx M k + 20` steps, `M = |x| + sz nt + mx nt`, `Wx M k = ((M+1) · 2^(1728 (k+2)^3))^60`.
* `E_extract`        : the form of `proofs-todo/Machine.lean`: labels `≤ |x|`, cost `(|x| + sz nt + 1)^62 · 2^(103680 (k+2)^3)`.
* `embeds_extractFirst` : `match tables … with [] => none | c :: _ => extract … c` (the extraction step of `improveC`).

Preconditions: `ntOk x k nt` (`Good`, width), `target ∈ tables`, and the two hypotheses of `extract_all` that the
Machine statement leaves implicit: `adjOfWord x` symmetric on a set `W` containing the vertices below `nt` (true for the graph
words of the wrapper: `W = range n`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord ntOk)

/-- `extract` followed by nothing: the first table entry (`improveC`'s call) -/
def extractFirst (adj : Adj) (k : ℕ) (nt : NT) : Option RT :=
  match tables adj k nt with
  | [] => none
  | c :: _ => extract adj k nt c

/-- the side conditions of the extraction: `ntOk`, a symmetric set `W` above the vertices of `nt` -/
def ExtOk (x : List ℕ) (k : ℕ) (nt : NT) : Prop :=
  ntOk x k nt ∧ ∃ W : Finset ℕ, (adjOfWord x).SymmOn W ∧ nt.under ⊆ W

/-- the closed form of the cost -/
theorem cost_closed (M k s : ℕ) : s ^ 2 * Wx M k = s ^ 2 * (M + 1) ^ 60 * 2 ^ (103680 * (k + 2) ^ 3) := by
  unfold Wx Zc Yk pX
  rw [mul_pow, ← pow_mul]
  have : 1728 * (k + 2) ^ 3 * 60 = 103680 * (k + 2) ^ 3 := by ring
  rw [this, mul_assoc]

section top
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ')
include hΔ

/-- `extractFirst`: the extraction step of `improveC` (`tables` once, then `extract` of its first entry) -/
theorem extractFirst_runs (B : ℕ) (x : List ℕ) (k : ℕ) (nt : NT) (M : ℕ) (hxM : x.length ≤ M)
    (hsM : sz nt ≤ M) (hmM : mx nt ≤ M) (hok : ExtOk x k nt)
    (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B)
    (hB : (nt.size * E4.cnode M k + nt.size ^ 2 * Wx M k + 30 + 2) ^ 2 < B) :
    Runs Δ' B fExtractFirst [toVal x, toVal k, toVal nt] (toVal (extractFirst (adjOfWord x) k nt))
      (nt.size * E4.cnode M k + nt.size ^ 2 * Wx M k + 30) := by
  obtain ⟨⟨hg, hw⟩, W, hs, hW⟩ := hok
  have hB1 : (nt.size ^ 2 * Wx M k + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have hBt : (nt.size * E4.cnode M k + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have hB1000 : 1000 < B := hB_of_sq M k _ (size_pos nt) hB1
  have hT := E4.tables_runs hΔ.e4 B x k M hxM hn hk nt hg hw hsM hmM hBt
  unfold extractFirst
  rcases hcase : tables (adjOfWord x) k nt with _ | ⟨c, T'⟩
  · rw [hcase] at hT
    refine Runs.mk (hΔ.e6 _ _ Δ_extractFirst) ?_
    simp only [toVal_nil, toVal_none]
    ev_start
    · ev_run
    · omega
  · have hc : c ∈ tables (adjOfWord x) k nt := by rw [hcase]; simp
    have hE := extract_runs hΔ B x k M hs hxM hn hk nt hg hW hw hsM hmM hB1 c hc
    rw [hcase] at hT
    refine Runs.mk (hΔ.e6 _ _ Δ_extractFirst) ?_
    simp only [toVal_cons]
    ev_start
    · ev_run
    · omega

end top

end E6b
end Lax117284Proofs.Treewidth.Fun
