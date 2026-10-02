import Lax117284Proofs.Treewidth.Chars.CountCard

/-!
# Counting characteristics (3): table sizes and the closed form of `charBound`

* `charBound_le : charBound (l+1) (k+1) ≤ 2^(720 l³)` for `k < l`, `1 ≤ l` (the exponent is
  `16 (l+2)² (l+k+4) ≤ 16 · 9 l² · 5 l`);
* `tables_length_le`, `tables_length_le_of_width`: every table has at most `charBound (l+1) (k+1)` entries, because it is
  duplicate-free and consists of well-formed characteristics.  The latter fact (`tables_wf`, preservation of `CT.Wf` by
  `forgetC`/`joinC`/`introC`) is proved elsewhere; here it is the explicit hypothesis `TablesWf`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-! ## `charBound` -/

theorem charBound_mono {b b' : ℕ} (k : ℕ) (h : b ≤ b') : charBound b k ≤ charBound b' k := by
  unfold charBound
  apply Nat.pow_le_pow_right (by norm_num)
  have h1 : (b + 1) ^ 2 ≤ (b' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : b + k + 2 ≤ b' + k + 2 := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 h1) h2

/-! ## tables -/

theorem tables_nodup (adj : Adj) (k : ℕ) (nt : NT) : (tables adj k nt).Nodup := by
  cases nt <;> simp [tables, forgetTable, introTable, joinTable, List.nodup_dedup]

/-- The one fact about tables that the counting needs (`tables_wf` of `proofs-todo/Statements.lean`: `Wf` is
preserved by `forgetC`, `joinC`, `introC`). -/
def TablesWf : Prop :=
  ∀ {adj : Adj} {k : ℕ} {nt : NT}, nt.Good adj → ∀ c ∈ tables adj k nt, CT.Wf nt.bag (k + 1) c

/-- Every table has at most `charBound (ℓ+1) (k+1)` entries (as the lists are duplicate-free). -/
theorem tables_length_le (tables_wf : TablesWf) {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj)
    (hb : nt.bag.card ≤ l + 1) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) := by
  have h1 : (tables adj k nt).length = (tables adj k nt).toFinset.card :=
    (List.toFinset_card_of_nodup (tables_nodup adj k nt)).symm
  have h2 : ((tables adj k nt).toFinset : Set CT) ⊆ {t : CT | CT.Wf nt.bag (k + 1) t} := by
    intro c hc
    exact tables_wf hg c (List.mem_toFinset.1 hc)
  have h3 : (tables adj k nt).toFinset.card ≤ {t : CT | CT.Wf nt.bag (k + 1) t}.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard h2 (wf_finite _ _)
  exact le_trans (h1 ▸ h3) (le_trans (card_wf_le nt.bag (k + 1)) (charBound_mono (k + 1) hb))

theorem bag_card_le_of_width {nt : NT} {l : ℕ} (hw : nt.toRT.Width l) : nt.bag.card ≤ l + 1 :=
  hw nt.bag (by cases nt <;> simp [NT.toRT, RT.bags, NT.bag])

/-- (blueprint `tables_all_length_le`, with the vacuous hypotheses removed) if a nice tree has width `≤ l`, every
table of it is small. -/
theorem tables_length_le_of_width (tables_wf : TablesWf) {adj : Adj} {k l : ℕ} {nt : NT} (hg : nt.Good adj)
    (hw : nt.toRT.Width l) :
    (tables adj k nt).length ≤ charBound (l + 1) (k + 1) :=
  tables_length_le tables_wf hg (bag_card_le_of_width hw)

end Lax117284Proofs.Treewidth.Chars
