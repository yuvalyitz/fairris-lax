import Lax117284Proofs.Machine.TwNum10
import Lax117284.Bodlaender

/-!
The decomposition step run on the graph of a word: what the cited theorem gives, in the numbers of
the main program.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)

/-- **The cited theorem**, for the program `prog` and the constant `ca`. -/
def AxStmt (prog : Program) (ca : ℕ) : Prop :=
  ∀ (W w : ℕ) (g : List ℕ) (I : Instance), EncodesGraph g I →
    (∀ v ∈ g ++ [w], ca * 2 ^ (ca * w ^ 3) * ((g ++ [w]).length + v + 1) ^ ca ≤ 2 ^ W) →
    ∃ (out : List ℕ) (t : ℕ), t ≤ ca * 2 ^ (ca * w ^ 3) * (g.length + 2) ^ ca ∧
      RunsTo W prog (g ++ [w]) out t ∧
      (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) w ∨
        ∃ D, out = 1 :: D ∧ NiceDecomposition I w D)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem core_key (hax : AxStmt prog ca) (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hpl : ca ≤ plit)
    (hx : Dm x) {I : Instance} {y0 : List ℕ} {k : ℕ} (hxe : x = y0 ++ [k])
    (hy : EncodesInstance y0 I) (hn : nx x = I.clients) (hm : mx x = I.days) :
    ∃ (z : List ℕ) (t : ℕ), t ≤ Tbx ca cc x ∧
      (gdx cc x → RunsTo (Wpx cc plit x) prog (TwGraph.gwList x (nx x) (mx x) ++ [wx cc x]) z t ∧
        (z = [0] ∨ ∃ D, z = 1 :: D)) ∧
      (gdx cc x → ∀ D, z = 1 :: D → NiceDecomposition I (wx cc x) D ∧ D.length + 1 ≤ t) ∧
      (gdx cc x → z = [0] → ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)) ∧
      (¬ gdx cc x → z = [0]) := by
  by_cases hg : gdx cc x
  · have gd := hx.gd hca hcc hg
    have hnL := hx.nL hg.2
    have hXy : ∀ j < y0.length, x.getD j 0 = y0.getD j 0 := by
      intro j hj
      rw [hxe, List.getD_append _ _ _ _ hj]
    have hEG : EncodesGraph (TwGraph.gwList x (nx x) (mx x)) I := by
      rw [hn, hm]; exact TwGraph.encodesGraph_gwList hy hXy
    have hlen : (TwGraph.gwList x (nx x) (mx x) ++ [wx cc x]).length = nx x * nx x + 2 := by
      simp [TwGraph.gwList_length]; omega
    have hwL : wx cc x ≤ x.length := by have := gd.wlg; have := gd.lgL; omega
    obtain ⟨out, t, ht, hrun, hcase⟩ := hax (Wpx cc plit x) (wx cc x)
      (TwGraph.gwList x (nx x) (mx x)) I hEG (by
        intro v hv
        rw [hlen]
        have hvL : v ≤ x.length := by
          rcases List.mem_append.mp hv with hv | hv
          · rcases Machine.TwNum.mem_gwList hv with rfl | h1
            · exact hnL
            · have := gd.hL; omega
          · have : v = wx cc x := by simpa using hv
            omega
        exact gd.ax hnL hvL hpl)
    have ht' : t ≤ Tbx ca cc x := by
      refine le_trans ht (le_of_eq ?_)
      unfold Tbx
      rw [TwGraph.gwList_length]
      congr 2; ring
    refine ⟨out, t, ht', fun _ => ⟨hrun, ?_⟩, fun _ D hD => ?_, fun _ h0 => ?_, fun h => absurd hg h⟩
    · rcases hcase with ⟨h, -⟩ | ⟨D, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨D, h⟩
    · rcases hcase with ⟨h, -⟩ | ⟨D', h, hN⟩
      · rw [h] at hD; simp at hD
      · rw [h] at hD
        have hDD : D' = D := by simpa using hD
        subst hDD
        refine ⟨hN, ?_⟩
        have := TwSetup.RunsTo.out_length_le hrun
        rw [h] at this; simpa using this
    · rcases hcase with ⟨-, h⟩ | ⟨D, h, -⟩
      · exact h
      · rw [h] at h0; simp at h0
  · exact ⟨[0], 0, Nat.zero_le _, fun h => absurd h hg, fun h => absurd h hg,
      fun h => absurd h hg, fun _ => rfl⟩

end Lax117284Proofs.Machine.TwNum
