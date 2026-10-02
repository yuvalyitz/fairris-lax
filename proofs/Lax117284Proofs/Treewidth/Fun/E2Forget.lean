import Lax117284Proofs.Treewidth.Fun.E2Norm

/-!
# WP E2 (4): `forgetC` as an F-function

`relE x c = relabel (·.erase x) c` (id 168, also the `map` callee of its own recursion) and `forgetC x c = norm (relE x c)`.
Cost `≤ 7000 (s + 1)^5` for `sz c ≤ s`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

theorem sz_erase_le (x : ℕ) (S : Finset ℕ) : sz (S.erase x) ≤ sz S := by
  rw [sz_finset, sz_finset]; have := Finset.card_erase_le (a := x) (s := S); omega

theorem sz_relabel_le (x : ℕ) : ∀ c : CT, sz (relabel (fun S => S.erase x) c) ≤ sz c := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    rw [relabel_node, sz_ct_node', sz_ct_node']
    have := sz_map_le (relabel (fun S => S.erase x)) ks ih
    have := sz_erase_le x S
    omega

section forget
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hE in
theorem relE_runs_aux (x : ℕ) (c : CT) (hB : 300 * (2 * count c) * (sz c + 1) + 300 < B) :
    Runs Δ' B fRelE [toVal x, toVal c] (toVal (relabel (fun S => S.erase x) c)) (100 * wt c * (sz c + 1)) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hcS := sz_finset_card S
    have hm : ks.length ≤ sz ks := length_le_sz ks
    have hcpos := count_ge_one (node S y ks)
    have hlit : fRelE < B := by
      show 168 < B
      have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 300) (by omega : 0 < 2 * count (node S y ks))) (by omega : 0 < sz (node S y ks) + 1)
      omega
    have hk : ∀ k ∈ ks, Runs Δ' B fRelE [toVal x, toVal k] (toVal (relabel (fun S => S.erase x) k))
        (100 * wt k * (sz k + 1)) := by
      intro k hk
      refine ih k hk ?_
      have h6 : count k ≤ count (node S y ks) := by
        have := count_le_countL_of_mem hk; rw [hcnode]; omega
      have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
      have h9 : 300 * (2 * count k) * (sz k + 1) ≤ 300 * (2 * count (node S y ks)) * (sz (node S y ks) + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)) (by omega)
      omega
    have hmap := Lib1.map_runs (ext1 hΔ) B fRelE (toVal x) (relabel (fun S => S.erase x))
      (fun k => 100 * wt k * (sz k + 1)) ks hk
    have herase := Lib3.erase_runs (ext3 hΔ) B x S
    have hts := tree_step ks (fun k => sz k + 1) 100 1 (sz (node S y ks) + 1)
      (fun k hk => by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
    simp only [pow_one] at hts
    rw [relabel_node]
    refine Runs.mk (hΔ _ _ (Δ_relE rid)) ?_
    simp only [toVal_ct]
    ev_start
    · ev_run
    · rw [hwt]
      nlinarith

theorem relE_runs (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 1300 * (s + 1) ^ 2 < B) :
    Runs Δ' B fRelE [toVal x, toVal c] (toVal (relabel (fun S => S.erase x) c)) (200 * (s + 1) ^ 2) := by
  have h1 := count_le_sz c
  have h2 : wt c ≤ 2 * count c := by unfold wt; omega
  have h3 : count c * (sz c + 1) ≤ (s + 1) * (s + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : (s + 1) * (s + 1) = (s + 1) ^ 2 := by ring
  refine (relE_runs_aux hΔ B x c ?_).mono ?_
  · nlinarith
  · nlinarith [Nat.zero_le (wt c)]

include hE in
theorem forgetC_runs (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 + 100 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) := by
  have hsq : (s + 1) ^ 2 ≤ (s + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hr := relE_runs hΔ B x c s hc (by omega)
  have hn := norm_runs hΔ hE B (relabel (fun S => S.erase x) c) s
    (le_trans (sz_relabel_le x c) hc) (by omega)
  refine Runs.mk (hΔ _ _ (Δ_forgetC rid)) ?_
  unfold forgetC
  ev_start
  · ev_run
  · omega

end forget

end E2
end Lax117284Proofs.Treewidth.Fun
