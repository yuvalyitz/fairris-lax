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

theorem extractUn_runs (B : ℕ) (x : List ℕ) (k : ℕ) (nt : NT) (target : CT) (M : ℕ) (hxM : x.length ≤ M)
    (hsM : sz nt ≤ M) (hmM : mx nt ≤ M) (hok : ExtOk x k nt) (htg : target ∈ tables (adjOfWord x) k nt)
    (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) (hB : (nt.size ^ 2 * Wx M k + 20 + 2) ^ 2 < B) :
    Runs Δ' B fExtractUn [toVal (x, k, nt, target)] (toVal (extract (adjOfWord x) k nt target))
      (nt.size ^ 2 * Wx M k + 20) := by
  obtain ⟨⟨hg, hw⟩, W, hs, hW⟩ := hok
  have hB1 : (nt.size ^ 2 * Wx M k + 2) ^ 2 < B :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have h := extract_runs hΔ B x k M hs hxM hn hk nt hg hW hw hsM hmM hB1 target htg
  have hB1000 : 1000 < B := hB_of_sq M k _ (size_pos nt) hB1
  refine Runs.mk (hΔ.e6 _ _ Δ_extractUn) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- **`E_extract`** (unary `Embeds` form, cost in `M = |x| + sz nt + mx nt`). -/
theorem embeds_extract :
    Embeds Δ' fExtractUn
      (fun p : List ℕ × ℕ × NT × CT => ExtOk p.1 p.2.1 p.2.2.1 ∧ p.2.2.2 ∈ tables (adjOfWord p.1) p.2.1 p.2.2.1)
      (fun p => extract (adjOfWord p.1) p.2.1 p.2.2.1 p.2.2.2)
      (fun p => p.2.2.1.size ^ 2 * Wx (p.1.length + sz p.2.2.1 + mx p.2.2.1) p.2.1 + 20) := by
  rintro B ⟨x, k, nt, target⟩ ⟨hok, htg⟩ hfit
  simp only at hok htg hfit ⊢
  have hmxv : (toVal (x, k, nt, target)).maxNat =
      max (toVal x).maxNat (max k (max (toVal nt).maxNat (toVal target).maxNat)) := by
    simp only [toVal_pair, toVal_nat, Val.maxNat]
  have hn1 : nOfWord x ≤ mx x := E4.nOfWord_le_mx x
  have hn2 : mx x = (toVal x).maxNat := rfl
  have hkB : k + 2 < B := hfit.lt (by omega)
  have hnB : (nOfWord x) ^ 2 < B := by
    have : nOfWord x ≤ (toVal (x, k, nt, target)).maxNat +
        (nt.size ^ 2 * Wx (x.length + sz nt + mx nt) k + 20) + 2 := by omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left this 2) hfit
  have hfit' : (nt.size ^ 2 * Wx (x.length + sz nt + mx nt) k + 20 + 2) ^ 2 < B :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hfit
  exact extractUn_runs hΔ B x k nt target (x.length + sz nt + mx nt) (by omega) (by omega) (by omega) hok htg
    hnB hkB hfit'

/-- **`E_extract`** with the labels bounded by the word length (`mx nt ≤ |x|`): the cost is a polynomial in `|x| + sz nt`
times `2^(103680 (k+2)^3)`. -/
theorem E_extract :
    Embeds Δ' fExtractUn
      (fun p : List ℕ × ℕ × NT × CT => ExtOk p.1 p.2.1 p.2.2.1 ∧ mx p.2.2.1 ≤ p.1.length ∧
        p.2.2.2 ∈ tables (adjOfWord p.1) p.2.1 p.2.2.1)
      (fun p => extract (adjOfWord p.1) p.2.1 p.2.2.1 p.2.2.2)
      (fun p => (p.1.length + sz p.2.2.1 + 1) ^ 62 * 2 ^ (103680 * (p.2.1 + 2) ^ 3) + 20) := by
  rintro B ⟨x, k, nt, target⟩ ⟨hok, hmx, htg⟩ hfit
  simp only at hok hmx htg hfit ⊢
  have hcost : nt.size ^ 2 * Wx (x.length + sz nt) k + 20 ≤
      (x.length + sz nt + 1) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3) + 20 := by
    rw [cost_closed]
    have h1 : nt.size ≤ sz nt := by have := size_le_sz_nt nt; have := sz_pos nt; omega
    have h2 : nt.size ^ 2 * (x.length + sz nt + 1) ^ 60 ≤ (x.length + sz nt + 1) ^ 62 := by
      have hs : nt.size ≤ x.length + sz nt + 1 := by omega
      have h3 : nt.size ^ 2 ≤ (x.length + sz nt + 1) ^ 2 := Nat.pow_le_pow_left hs 2
      calc nt.size ^ 2 * (x.length + sz nt + 1) ^ 60 ≤ (x.length + sz nt + 1) ^ 2 * (x.length + sz nt + 1) ^ 60 :=
            Nat.mul_le_mul_right _ h3
        _ = (x.length + sz nt + 1) ^ 62 := by rw [← pow_add]
    have := Nat.mul_le_mul_right (2 ^ (103680 * (k + 2) ^ 3)) h2
    omega
  have hmxv : (toVal (x, k, nt, target)).maxNat =
      max (toVal x).maxNat (max k (max (toVal nt).maxNat (toVal target).maxNat)) := by
    simp only [toVal_pair, toVal_nat, Val.maxNat]
  have hn1 : nOfWord x ≤ mx x := E4.nOfWord_le_mx x
  have hn2 : mx x = (toVal x).maxNat := rfl
  have hfit' := hfit.mono_cost hcost
  have hkB : k + 2 < B := hfit.lt (by omega)
  have hnB : (nOfWord x) ^ 2 < B := by
    have : nOfWord x ≤ (toVal (x, k, nt, target)).maxNat +
        ((x.length + sz nt + 1) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3) + 20) + 2 := by omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left this 2) hfit
  have hfit'' : (nt.size ^ 2 * Wx (x.length + sz nt) k + 20 + 2) ^ 2 < B := by
    have : nt.size ^ 2 * Wx (x.length + sz nt) k + 20 + 2 ≤ (toVal (x, k, nt, target)).maxNat +
        ((x.length + sz nt + 1) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3) + 20) + 2 := by omega
    exact lt_of_le_of_lt (Nat.pow_le_pow_left this 2) hfit
  exact (extractUn_runs hΔ B x k nt target (x.length + sz nt) (by omega) (by omega) (by omega) hok htg
    hnB hkB hfit'').mono hcost

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
