import Lax117284Proofs.Treewidth.Size.RealD
import Lax117284Proofs.Treewidth.Size.Tables

/-!
# Size bounds (WP P1), part 11: `extract_size_le`

For a good nice tree `nt` whose bags have at most `k + 2` vertices (`nt.toRT.Width (k + 1)`), every real tree returned by
`extract adj k nt c` has at most `(2k + 8) · |nt|` nodes: a leaf gives 1 node, a forget node none, an introduce node at
most `leaves + b + 3 ≤ 2k + 8` (region cuts + new branch), a join node adds the sizes (`mergeReal_size_le`).

**Repair of `Machine.lean`'s `extract_size_le`**: the hypothesis `nt.toRT.Width (k + 1)` is needed (otherwise the bags,
hence `b`, are unbounded); the constant `4 * (k + 3)` is kept as a corollary (`extract_size_le`) since `2k + 8 ≤ 4(k+3)`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem extract_size_aux {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → nt.toRT.Width (k + 1) → ∀ c ∈ tables adj k nt,
      ∀ t, extract adj k nt c = some t → t.size ≤ (2 * k + 8) * nt.size
  | .leaf, _, _, _, c, hc, t, ht => by
    simp only [extract, Option.some.injEq] at ht
    subst ht
    simp [size_node', NT.size]
  | .forget x c, hg, hW, hw, q, hq, t, ht => by
    simp only [extract] at ht
    obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
    by_cases he : CT.forgetC x q1 = q
    · simp only [he, if_true] at hf
      have := extract_size_aux hs hg.2 hW (NT.width_forget hw) q1 hq1 t hf
      simp only [NT.size]
      nlinarith
    · simp [he] at hf
  | .join a b, hg, hW, hw, q, hq, t, ht => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    simp only [extract] at ht
    obtain ⟨ca, hca, hf⟩ := findSome_sound ht
    obtain ⟨cb, hcb, hf'⟩ := findSome_sound hf
    by_cases he : q ∈ CT.joinC (k + 1) ca cb
    · simp only [he, if_true] at hf'
      rcases hea : extract adj k a ca with _ | ta
      · simp [hea] at hf'
      rcases heb : extract adj k b cb with _ | tb
      · simp [hea, heb] at hf'
      simp only [hea, heb, Option.bind_some] at hf'
      have h1 := extract_size_aux hs hga hWa (NT.width_join_left hw) ca hca ta hea
      have h2 := extract_size_aux hs hgb hWb (NT.width_join_right hw) cb hcb tb heb
      have h3 := realJoin_size_le hf'
      simp only [NT.size]
      nlinarith
    · simp [he] at hf'
  | .intro v c, hg, hW, hw, q, hq, t, ht => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hwc := NT.width_intro hw
    have hB : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
    simp only [extract] at ht
    obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
    by_cases he : q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q1
    · simp only [he, if_true] at hf
      rcases hea : extract adj k c q1 with _ | t0
      · simp [hea] at hf
      simp only [hea, Option.bind_some] at hf
      have ih := extract_size_aux hs hgc hWc hwc q1 hq1 t0 hea
      obtain ⟨-, hsp⟩ := extract_all hs hgc hWc q1 hq1
      obtain ⟨-, d0⟩ := hsp t0 hea
      have hwf := tables_wf hgc q1 hq1
      have hLB : LB c.bag.card (t0.char c.bag) :=
        (DomC.LB_iff d0).2 (LB.of_good hwf.good)
      have hl : leaves (t0.char c.bag) ≤ c.bag.card + 1 := by
        rw [d0.leaves_eq]; exact hwf.leaves_le
      have h3 := realIntro_size_le hLB hf
      simp only [NT.size]
      nlinarith
    · simp [he] at hf

/-- **`extract_size_le`** (WP P1 (c)). -/
theorem extract_size_le' {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) (hw : nt.toRT.Width (k + 1)) : ∀ c ∈ tables adj k nt, ∀ t, extract adj k nt c = some t →
      t.size ≤ 4 * (k + 3) * nt.size := by
  intro c hc t ht
  have := extract_size_aux hs hg hW hw c hc t ht
  refine le_trans this (Nat.mul_le_mul_right _ (by omega))

end Lax117284Proofs.Treewidth.Chars
