import Lax117284Proofs.Treewidth.Size.RealE

/-!
# Size bounds (WP P1), part 13: cell sizes of real trees, and the final `extract` bounds

`rvsz` is the number of cells of the cons-tree view of a real tree
(`encRT (node X ks) = cons (list X) (list of kids)`); if all bags have at most `β` vertices,
`vsz t + 1 ≤ size t · (2β + 4)` (`rvsz_le`).  Combined with `extract_size_aux` and the width `≤ k` of the extracted
trees (`extract_all`), `extract_vsz_le` bounds the cell size of `extract`'s result by
`(2k + 8)(2k + 6) · |nt|`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

mutual
/-- Number of cells of the cons-tree view of a real tree. -/
def rvsz : RT → ℕ
  | .node X ks => (2 * X.card + 1) + rvszL ks + 1
def rvszL : List RT → ℕ
  | [] => 1
  | k :: ks => rvsz k + rvszL ks + 1
end

theorem rvszL_eq : ∀ ks : List RT, rvszL ks = 1 + (ks.map (fun k => rvsz k + 1)).sum
  | [] => by simp [rvszL]
  | k :: ks => by simp [rvszL, rvszL_eq ks]; omega

theorem rvsz_le {β : ℕ} : ∀ t : RT, (∀ X ∈ t.bags, X.card ≤ β) → rvsz t + 1 ≤ t.size * (2 * β + 4) := by
  intro t
  induction t using RT.ind with
  | h X ks ih =>
    intro hb
    have hX : X.card ≤ β := hb X (by simp [RT.bags])
    have hk : ∀ k ∈ ks, rvsz k + 1 ≤ k.size * (2 * β + 4) := by
      intro k hk
      refine ih k hk (fun Y hY => hb Y ?_)
      have : ∃ (pre : List (Finset ℕ)), True := ⟨[], trivial⟩
      simp only [RT.bags, List.mem_cons]
      right
      have hall : ∀ ks' : List RT, k ∈ ks' → ∀ Y ∈ k.bags, Y ∈ RT.bagsL ks' := by
        intro ks'
        induction ks' with
        | nil => intro h; simp at h
        | cons a l ihl =>
          intro h Y hY
          simp only [RT.bagsL, List.mem_append]
          rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hY
          · exact Or.inr (ihl h Y hY)
      exact hall ks hk Y hY
    have hsum : ((ks.map (fun k => rvsz k + 1)).sum) ≤ (ks.map (fun k => k.size * (2 * β + 4))).sum := by
      apply List.sum_le_sum
      intro k0 hk0
      have := hk k0 hk0
      omega
    have hsz : (ks.map (fun k => k.size * (2 * β + 4))).sum = (ks.map RT.size).sum * (2 * β + 4) :=
      List.sum_map_mul_right ..
    have hv : rvsz (RT.node X ks) = 2 * X.card + 2 + rvszL ks := by simp [rvsz]; omega
    rw [hv, rvszL_eq, size_node']
    nlinarith

/-- The cell size of the tree returned by `extract`. -/
theorem extract_vsz_le {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) (hw : nt.toRT.Width (k + 1)) : ∀ c ∈ tables adj k nt, ∀ t, extract adj k nt c = some t →
      rvsz t ≤ (2 * k + 8) * (2 * k + 6) * nt.size := by
  intro c hc t ht
  have hsz := extract_size_aux hs hg hW hw c hc t ht
  obtain ⟨-, hsp⟩ := extract_all hs hg hW c hc
  obtain ⟨hp, -⟩ := hsp t ht
  have hb : ∀ X ∈ t.bags, X.card ≤ k + 1 := hp.2
  have := rvsz_le (β := k + 1) t hb
  calc rvsz t ≤ t.size * (2 * (k + 1) + 4) := by omega
    _ ≤ ((2 * k + 8) * nt.size) * (2 * (k + 1) + 4) := Nat.mul_le_mul_right _ hsz
    _ = (2 * k + 8) * (2 * k + 6) * nt.size := by ring

end Lax117284Proofs.Treewidth.Chars
