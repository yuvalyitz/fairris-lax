import Lax117284Proofs.Treewidth.Fun.E6aNice
import Lax117284Proofs.Treewidth.Fun.E6aEnc

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (5): `Embeds` for `niceOf`
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem card_vertsL_le_sz : ∀ ks : List RT, (∀ k ∈ ks, k.verts.card ≤ sz k) → (RT.vertsL ks).card ≤ sz ks
  | [], _ => by simp [RT.vertsL]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := card_vertsL_le_sz ks (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := Finset.card_union_le k.verts (RT.vertsL ks)
    rw [sz_cons]
    simp only [RT.vertsL]
    omega

/-- the number of vertices of a rooted tree is at most its cell count -/
theorem card_verts_le_sz (t : RT) : t.verts.card ≤ sz t := by
  induction t using RT.ind with
  | _ X ks ih =>
    have h1 := card_vertsL_le_sz ks ih
    have h2 := Finset.card_union_le X (RT.vertsL ks)
    have h3 : X.card ≤ sz X := by rw [sz_finset]; omega
    rw [sz_rt_node']
    show (X ∪ RT.vertsL ks).card ≤ _
    omega

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

/-- **`niceOf` on a connected tree**: the cost is a polynomial (degree 5) in `sz t` alone
(`niceOf_size_le` : `size (niceOf t) ≤ (|V|+2)(size t+1)`). -/
theorem embeds_niceOf_conn : Embeds Δ' fNiceOf (fun t : RT => t.Conn) niceOf
    (fun t => 8000 * (sz t + 2) ^ 5) := by
  intro B t hcn hfit
  have hc : 8000 * (sz t + 2) ^ 5 + 3 < B := hfit.cost_lt
  have hp1 := sz_pos t
  have hS : 3 ≤ sz t + 2 := by omega
  have hS5 : 243 ≤ (sz t + 2) ^ 5 := by
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hS 5
  have h1000 : 1000 < B := by omega
  have hV := card_verts_le_sz t
  have hsize := size_le_sz t
  have hnz := niceOf_size_le hcn
  have hnz2 : (niceOf t).size ≤ (sz t + 2) ^ 2 := by
    refine le_trans hnz ?_
    calc (t.verts.card + 2) * (t.size + 1) ≤ (sz t + 2) * (sz t + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = (sz t + 2) ^ 2 := by ring
  have hs1 : sz t ≤ (sz t + 2) ^ 2 := by nlinarith
  have h := niceOf_runs (Δ' := Δ') hΔ B h1000 ((sz t + 2) ^ 2) t hs1 hnz2
  refine h.mono ?_
  have hw := wtR_le_sz t
  show 1000 * ((sz t + 2) ^ 2 + 1) ^ 2 * wtR t ≤ 8000 * (sz t + 2) ^ 5
  have hq : (sz t + 2) ^ 2 + 1 ≤ 2 * (sz t + 2) ^ 2 := by nlinarith
  have hq2 : ((sz t + 2) ^ 2 + 1) ^ 2 ≤ 4 * (sz t + 2) ^ 4 := by
    calc ((sz t + 2) ^ 2 + 1) ^ 2 ≤ (2 * (sz t + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left hq 2
      _ = 4 * (sz t + 2) ^ 4 := by ring
  have hq3 : ((sz t + 2) ^ 2 + 1) ^ 2 * wtR t ≤ (4 * (sz t + 2) ^ 4) * (2 * (sz t + 2)) :=
    Nat.mul_le_mul hq2 (by omega)
  nlinarith

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun
