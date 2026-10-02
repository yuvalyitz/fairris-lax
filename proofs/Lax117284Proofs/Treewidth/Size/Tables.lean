import Lax117284Proofs.Treewidth.Size.Plans
import Lax117284Proofs.Treewidth.Size.Join
import Lax117284Proofs.Treewidth.Chars.Tables

/-!
# Size bounds (WP P1), part 4: table sizes, with the intermediate (pre-`dedup`) lists

`x := k + 2`.  For a good nice tree `nt` all of whose bags have at most `k + 2` vertices:

* `tables_length_le_pow`  : `|tables adj k nt| ≤ 2^(96 x^3)` (`tables` is duplicate-free, so this is the counting bound);
* `introC_length_le`     : `|introC (k+1) v N t| ≤ 2^(64 (b + k + 3)^3)` for `t ∈ tables adj k c`, `b = |c.bag|`;
* `forgetTable_pre_le`, `introTable_pre_le`, `joinTable_pre_le` : the lists *before* `dedup` are at most `2^(2000 x^3)`
  (the quadratic `dedup` then costs at most `2^(4000 x^3)` comparisons).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem pow_mul_pow_le' {a b d : ℕ} (h : a + b ≤ d) : 2 ^ a * 2 ^ b ≤ 2 ^ d := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- Width hereditary along the children. -/
theorem NT.width_intro {v : ℕ} {c : NT} {w : ℕ} (h : (NT.intro v c).toRT.Width w) : c.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_forget {v : ℕ} {c : NT} {w : ℕ} (h : (NT.forget v c).toRT.Width w) : c.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_join_left {a b : NT} {w : ℕ} (h : (NT.join a b).toRT.Width w) : a.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem NT.width_join_right {a b : NT} {w : ℕ} (h : (NT.join a b).toRT.Width w) : b.toRT.Width w := by
  intro X hX
  exact h X (by simp [NT.toRT, RT.bags, RT.bagsL, hX])

theorem introC_length_le_plans (kmax v : ℕ) (N : Finset ℕ) (t : CT) :
    (introC kmax v N t).length ≤ (introPlans v N t).length := by
  unfold introC
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem exp_le_96 (k : ℕ) : 16 * (k + 2 + 1) ^ 2 * (k + 2 + (k + 1) + 2) ≤ 96 * (k + 2) ^ 3 := by
  nlinarith [sq_nonneg k, Nat.zero_le k]

theorem charBound_tables_le (k : ℕ) : charBound (k + 2) (k + 1) ≤ 2 ^ (96 * (k + 2) ^ 3) := by
  unfold charBound
  exact Nat.pow_le_pow_right (by norm_num) (exp_le_96 k)

theorem tables_length_le_pow {adj : Adj} {k : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width (k + 1)) :
    (tables adj k nt).length ≤ 2 ^ (96 * (k + 2) ^ 3) := by
  have := tables_length_le_of_width' (k := k) hg hw
  exact le_trans this (charBound_tables_le k)

theorem introC_length_le {k v : ℕ} {N B : Finset ℕ} {t : CT} (hB : B.card ≤ k + 2) (hw : t.Wf B (k + 1)) :
    (introC (k + 1) v N t).length ≤ 2 ^ (1728 * (k + 2) ^ 3) := by
  refine le_trans (introC_length_le_plans _ _ _ _) (le_trans (introPlans_length_le hw) ?_)
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : B.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (B.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 64 * (B.card + (k + 1) + 2) ^ 3 ≤ 64 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 1728 * (k + 2) ^ 3 := by ring

theorem joinC_length_le_k {k : ℕ} {B : Finset ℕ} {a b : CT} (hB : B.card ≤ k + 2) (ha : a.Wf B (k + 1))
    (hb : b.Wf B (k + 1)) : (joinC (k + 1) a b).length ≤ 2 ^ (432 * (k + 2) ^ 3) := by
  refine le_trans (joinC_length_le ha hb) (Nat.pow_le_pow_right (by norm_num) ?_)
  have h1 : B.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
  have h2 : (B.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
  calc 16 * (B.card + (k + 1) + 2) ^ 3 ≤ 16 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
    _ = 432 * (k + 2) ^ 3 := by ring

/-- The introduce step before `dedup`. -/
theorem introTable_pre_le {adj : Adj} {k v : ℕ} {c : NT} (hg : c.Good adj) (hw : c.toRT.Width (k + 1))
    (N : Finset ℕ) :
    ((tables adj k c).flatMap (CT.introC (k + 1) v N)).length ≤ 2 ^ (1824 * (k + 2) ^ 3) := by
  have hB : c.bag.card ≤ k + 2 := bag_card_le_of_width hw
  have h1 := tables_length_le_pow hg hw
  refine le_trans (length_flatMap_le (n := 2 ^ (1728 * (k + 2) ^ 3)) ?_) ?_
  · intro t ht
    exact introC_length_le hB (tables_wf hg t ht)
  · refine le_trans (Nat.mul_le_mul_right _ h1) ?_
    exact pow_mul_pow_le' (by omega)

end Lax117284Proofs.Treewidth.Chars
