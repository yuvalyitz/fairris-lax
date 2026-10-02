import Lax117284Proofs.Treewidth.Fun.E4Steps
import Lax117284Proofs.Treewidth.Fun.E4Arith
import Lax117284Proofs.Treewidth.Fun.E4Asm

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4 (4): `tables` as an F-function (recursion over the nice tree), with the closed-form cost

`tables_runs`: for a good nice tree of width `≤ k + 1` whose size / labels are `≤ M`, on a graph word of length `≤ M`,
the function `fTables` computes `tables (adjOfWord x) k nt` within `nt.size · cnode M k` steps, where
`cnode M k = (M+1)^15 · 2^(4000 (k+2)^3)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

theorem Y_ge (k : ℕ) : 8 ≤ (k + 2) ^ 3 := by
  have : 2 ^ 3 ≤ (k + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  simpa using this

theorem X_le_Y (k : ℕ) : k + 2 ≤ (k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _

theorem cnode_ge (M k : ℕ) : 1000 ≤ cnode M k := by
  unfold cnode
  have h1 := Q_ge M
  have hY := Y_ge k
  have h2 : 1000 ≤ 2 ^ (4000 * (k + 2) ^ 3) :=
    le_trans (by norm_num : 1000 ≤ 2 ^ 10) (pw_le (by omega))
  calc 1000 ≤ 2 ^ (4000 * (k + 2) ^ 3) := h2
    _ ≤ (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3) := Nat.le_mul_of_pos_left _ h1

theorem mx_intro_le (v : ℕ) (c : NT) : mx c ≤ mx (NT.intro v c) := by
  simp only [mx, toVal_nt_intro, Val.maxNat]; omega
theorem mx_forget_le (v : ℕ) (c : NT) : mx c ≤ mx (NT.forget v c) := by
  simp only [mx, toVal_nt_forget, Val.maxNat]; omega
theorem mx_join_left_le (a b : NT) : mx a ≤ mx (NT.join a b) := by
  simp only [mx, toVal_nt_join, Val.maxNat]; omega
theorem mx_join_right_le (a b : NT) : mx b ≤ mx (NT.join a b) := by
  simp only [mx, toVal_nt_join, Val.maxNat]; omega

/-! ### isolated numerics -/

theorem b500_of {B C S : ℕ} (hC : 1000 ≤ C) (hS : 1 ≤ S) (hB : (S * C + 2) ^ 2 < B) : 500 < B := by
  have h1 : 1000 ≤ S * C := le_trans hC (Nat.le_mul_of_pos_left _ hS)
  have h2 : (1000 + 2) ^ 2 ≤ (S * C + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  omega

theorem sq_size_mono {B a b C : ℕ} (h : a ≤ b) (hB : (b * C + 2) ^ 2 < B) : (a * C + 2) ^ 2 < B :=
  sq_lt_of_le (Nat.mul_le_mul_right _ h) hB

theorem sq_cost_le {B c C S : ℕ} (hc : c ≤ C) (hS : 1 ≤ S) (hB : (S * C + 2) ^ 2 < B) : (c + 2) ^ 2 < B :=
  sq_lt_of_le (le_trans hc (Nat.le_mul_of_pos_left _ hS)) hB

theorem cost_forget (s C F : ℕ) (h : 200 + F ≤ C) : 60 + s * C + F ≤ (s + 1) * C := by
  have : (s + 1) * C = s * C + C := by ring
  omega

theorem cost_join (a b C F : ℕ) (h : 200 + F ≤ C) : 100 + a * C + b * C + F ≤ (a + b + 1) * C := by
  have : (a + b + 1) * C = a * C + b * C + C := by ring
  omega

theorem cost_intro (s C Cbag Cnb CI M X : ℕ) (h : 200 + 60 * M ^ 2 + X * (28 * M + 120) + CI ≤ C)
    (hbag : Cbag ≤ 60 * M ^ 2) (hnb : Cnb ≤ X * (28 * M + 120) + 60) :
    100 + s * C + Cbag + Cnb + CI ≤ (s + 1) * C := by
  have : (s + 1) * C = s * C + C := by ring
  omega

theorem sz_sq_le {s M : ℕ} (h : s ≤ M) : 60 * s ^ 2 ≤ 60 * M ^ 2 :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)

theorem nbrs_cost_le {c X L M : ℕ} (hc : c ≤ X) (hL : L ≤ M) : c * (28 * L + 120) + 60 ≤ X * (28 * M + 120) + 60 := by
  have := Nat.mul_le_mul hc (show 28 * L + 120 ≤ 28 * M + 120 by omega)
  omega

section tables
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

theorem tables_runs (x : List ℕ) (k M : ℕ) (hxM : x.length ≤ M) (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) :
    ∀ nt : NT, nt.Good (adjOfWord x) → nt.toRT.Width (k + 1) → sz nt ≤ M → mx nt ≤ M →
      (nt.size * cnode M k + 2) ^ 2 < B →
      Runs Δ' B fTables [toVal x, toVal k, toVal nt] (toVal (tables (adjOfWord x) k nt))
        (nt.size * cnode M k) := by
  intro nt
  induction nt with
  | leaf =>
    intro hg hw hs hm hB
    have hc := cnode_ge M k
    have hsz : NT.size NT.leaf = 1 := rfl
    rw [hsz] at hB ⊢
    have hB500 : 500 < B := b500_of hc le_rfl hB
    have e : toVal (tables (adjOfWord x) k NT.leaf) =
        Val.cons (Val.cons (.nat 0) (.cons (.cons (.nat 0) (.nat 0)) (.nat 0))) (.nat 0) := by
      simp only [tables, CT.start, toVal_cons, toVal_ct, toVal_empty_finset, toVal_nil, toVal_nat]
    rw [e]
    refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
    simp only [toVal_nt_leaf]
    ev_start
    · ev_run
    · omega
  | forget y c ih =>
    intro hg hw hs hm hB
    have hgc : c.Good (adjOfWord x) := hg.2
    have hwc : c.toRT.Width (k + 1) := NT.width_forget hw
    have hsc : sz c ≤ M := by have := sz_nt_forget y c; omega
    have hmc : mx c ≤ M := le_trans (mx_forget_le y c) hm
    have hcn := cnode_ge M k
    have hsize : (NT.forget y c).size = c.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBc : (c.size * cnode M k + 2) ^ 2 < B := sq_size_mono (Nat.le_succ _) hB'
    have hfn : 200 + forgetCostF (128 * (k + 2) ^ 3) (2 ^ (96 * (k + 2) ^ 3)) ≤ cnode M k :=
      forget_node' ((k + 2) ^ 3) M (Y_ge k)
    have IH := ih hgc hwc hsc hmc hBc
    have hF := forgetTable_runs hΔ B y (tables (adjOfWord x) k c) (128 * (k + 2) ^ 3) (2 ^ (96 * (k + 2) ^ 3))
      (tables_sz_le hgc hwc) (tables_length_le_pow hgc hwc)
      (sq_cost_le (S := (NT.forget y c).size) (by omega) (by rw [hsize]; omega) hB)
    have e : tables (adjOfWord x) k (NT.forget y c) = forgetTable y (tables (adjOfWord x) k c) := rfl
    rw [e]
    refine forget_assemble hΔ B x k y c _ _ _ _ _ hB500 IH hF ?_
    rw [hsize]
    exact cost_forget _ _ _ hfn
  | join a b iha ihb =>
    intro hg hw hs hm hB
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good (adjOfWord x) a ∧ NT.Good (adjOfWord x) b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adjOfWord x u v = true ∨ adjOfWord x v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
    have hwb : b.toRT.Width (k + 1) := NT.width_join_right hw
    have hsab := sz_nt_join a b
    have hsa : sz a ≤ M := by omega
    have hsb : sz b ≤ M := by omega
    have hma : mx a ≤ M := le_trans (mx_join_left_le a b) hm
    have hmb : mx b ≤ M := le_trans (mx_join_right_le a b) hm
    have hcn := cnode_ge M k
    have hsize : (NT.join a b).size = a.size + b.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBa : (a.size * cnode M k + 2) ^ 2 < B := sq_size_mono (by omega) hB'
    have hBb : (b.size * cnode M k + 2) ^ 2 < B := sq_size_mono (by omega) hB'
    have IHa := iha hga hwa hsa hma hBa
    have IHb := ihb hgb hwb hsb hmb hBb
    have hjn : 200 + joinCostF (14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3))
        (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (432 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) ≤
        cnode M k := join_node' ((k + 2) ^ 3) M (Y_ge k)
    have hcard : a.bag.card ≤ k + 2 := bag_card_le_of_width hwa
    have hs3 : a.bag.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have hs33 : (a.bag.card + (k + 1) + 2) ^ 3 ≤ 27 * (k + 2) ^ 3 := by
      calc (a.bag.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left hs3 3
        _ = 27 * (k + 2) ^ 3 := by ring
    have hCj : 14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (48 * (a.bag.card + (k + 1) + 2) ^ 3) ≤
        14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3) :=
      Nat.mul_le_mul_left _ (pw_le (by omega))
    have hwfa : ∀ c ∈ tables (adjOfWord x) k a, c.Wf a.bag (k + 1) := fun c hc => tables_wf hga c hc
    have hwfb : ∀ c ∈ tables (adjOfWord x) k b, c.Wf a.bag (k + 1) := fun c hc => by
      rw [hab]; exact tables_wf hgb c hc
    have hmem : ∀ e, e ∈ (tables (adjOfWord x) k a).flatMap
        (fun ca => (tables (adjOfWord x) k b).flatMap (fun cb => joinC (k + 1) ca cb)) →
        e ∈ tables (adjOfWord x) k (NT.join a b) := by
      intro e he
      show e ∈ joinTable (k + 1) (tables (adjOfWord x) k a) (tables (adjOfWord x) k b)
      simp only [joinTable, List.mem_dedup]
      exact he
    have hJ := joinTable_runs hΔ B (k + 1) a.bag (tables (adjOfWord x) k a) (tables (adjOfWord x) k b)
      (128 * (k + 2) ^ 3) (14000 * (128 * (k + 2) ^ 3 + 1) * 2 ^ (1296 * (k + 2) ^ 3))
      (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (2 ^ (432 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3)
      hwfa hwfb (tables_sz_le hga hwa) (tables_sz_le hgb hwb) hCj
      (fun a' ha' b' hb' => joinC_length_le_k hcard (hwfa a' ha') (hwfb b' hb'))
      (tables_length_le_pow hga hwa) (tables_length_le_pow hgb hwb) Nat.one_le_two_pow Nat.one_le_two_pow
      (fun e he => tables_sz_le hg hw e (hmem e he))
      (sq_cost_le (S := (NT.join a b).size) (by omega) (by rw [hsize]; omega) hB)
    have e : tables (adjOfWord x) k (NT.join a b) =
        joinTable (k + 1) (tables (adjOfWord x) k a) (tables (adjOfWord x) k b) := rfl
    rw [e]
    have hk1 : k + 1 < B := by omega
    refine join_assemble hΔ B x k a b _ _ _ _ _ _ _ hB500 hk1 IHa IHb hJ ?_
    rw [hsize]
    exact cost_join _ _ _ _ hjn
  | intro v c ih =>
    intro hg hw hs hm hB
    have hgfull := hg
    obtain ⟨hvB, -, -, hgc⟩ := hg
    have hwc : c.toRT.Width (k + 1) := NT.width_intro hw
    have hsc : sz c ≤ M := by have := sz_nt_intro v c; omega
    have hmc : mx c ≤ M := le_trans (mx_intro_le v c) hm
    have hvM : v ≤ M := le_trans (le_mx_nt (NT.intro v c) (by simp [NT.mentioned])) hm
    have hbagM : ∀ u ∈ c.bag, u ≤ M := fun u hu => le_trans (le_mx_nt c (bag_subset_mentioned c hu)) hmc
    have hcn := cnode_ge M k
    have hsize : (NT.intro v c).size = c.size + 1 := rfl
    have hB500 : 500 < B := b500_of hcn (by omega) hB
    have hB' := hB
    rw [hsize] at hB'
    have hBc : (c.size * cnode M k + 2) ^ 2 < B := sq_size_mono (Nat.le_succ _) hB'
    have IH := ih hgc hwc hsc hmc hBc
    have hin : 200 + 60 * M ^ 2 + (k + 2) * (28 * M + 120) +
        introCostF (10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3))
          (2 ^ (1728 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) (2 ^ (1824 * (k + 2) ^ 3)) ≤
        cnode M k := intro_node' ((k + 2) ^ 3) M (k + 2) (Y_ge k) (X_le_Y k)
    have hcard : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
    have hs3 : c.bag.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have hs33 : (c.bag.card + (k + 1) + 2) ^ 3 ≤ 27 * (k + 2) ^ 3 := by
      calc (c.bag.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left hs3 3
        _ = 27 * (k + 2) ^ 3 := by ring
    have hCi : E3C.introCCost (128 * (k + 2) ^ 3 + M + 1) (c.bag.card + (k + 1) + 2) ≤
        10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3) := by
      unfold E3C.introCCost
      exact Nat.mul_le_mul_left _ (pw_le (by omega))
    have hwf : ∀ t ∈ tables (adjOfWord x) k c, t.Wf c.bag (k + 1) := fun t ht => tables_wf hgc t ht
    have hYk := X_le_Y k
    have hmem : ∀ e, e ∈ (tables (adjOfWord x) k c).flatMap (introC (k + 1) v (nbrs (adjOfWord x) v c.bag)) →
        e ∈ tables (adjOfWord x) k (NT.intro v c) := by
      intro e he
      show e ∈ introTable (k + 1) v (nbrs (adjOfWord x) v c.bag) (tables (adjOfWord x) k c)
      simp only [introTable, List.mem_dedup]
      exact he
    have hNc : (nbrs (adjOfWord x) v c.bag).card ≤ 128 * (k + 2) ^ 3 + M := by
      have h1 : nbrs (adjOfWord x) v c.bag ⊆ c.bag := Finset.filter_subset _ _
      have := Finset.card_le_card h1
      omega
    have hI := introTable_runs hΔ B (k + 1) v (nbrs (adjOfWord x) v c.bag) c.bag (tables (adjOfWord x) k c)
      (128 * (k + 2) ^ 3 + M) (10 ^ 16 * (128 * (k + 2) ^ 3 + M + 1) ^ 15 * 2 ^ (3456 * (k + 2) ^ 3))
      (2 ^ (1728 * (k + 2) ^ 3)) (2 ^ (96 * (k + 2) ^ 3)) (128 * (k + 2) ^ 3) (2 ^ (1824 * (k + 2) ^ 3))
      hwf (fun t ht => le_trans (tables_sz_le hgc hwc t ht) (Nat.le_add_right _ _))
      (fun t ht => mx_ct_le_of_wf (hwf t ht) (fun u hu => le_trans (hbagM u hu) (Nat.le_add_left _ _))
        (by omega))
      (by omega) hNc (by omega) hCi
      (fun t ht => introC_length_le hcard (hwf t ht)) (tables_length_le_pow hgc hwc)
      (fun e he => tables_sz_le hgfull hw e (hmem e he)) (introTable_pre_le hgc hwc _)
      (sq_cost_le (S := (NT.intro v c).size) (by omega) (by rw [hsize]; omega) hB)
    have hbag := ntBag_runs hΔ B hB500 c
    have hnb := nbrs_runs hΔ B x v c.bag hB500 hn
    have e : tables (adjOfWord x) k (NT.intro v c) =
        introTable (k + 1) v (nbrs (adjOfWord x) v c.bag) (tables (adjOfWord x) k c) := rfl
    rw [e]
    have hk1 : k + 1 < B := by omega
    refine intro_assemble hΔ B x k v c _ _ _ _ _ _ _ _ hB500 hk1 IH hbag hnb hI ?_
    rw [hsize]
    exact cost_intro _ _ _ _ _ M (k + 2) hin (sz_sq_le hsc) (nbrs_cost_le hcard hxM)

end tables

end E4
end Lax117284Proofs.Treewidth.Fun
