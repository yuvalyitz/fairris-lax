import Lax117284Proofs.Treewidth.Fun.A2Corr

/-!
# WP A2 (2): `niceDecomposition_computable` from `DecompRun`

`niceDecomposition_computable_of h` is the exact statement of the concept axiom
`Lax117284.BodlaenderGeneral.niceDecomposition_computable`, proved from the functional run `h : DecompRun` through the compiler
(`Load.compile_computes`): the program is the compiled one, the constant `c` dominates the compiler's constant `c₀` and
`10 κ (C + 1) + 1`, and the set of admissible inputs handed to the compiler is the singleton `{g ++ [k]}` (the concept's guard
is per input, the compiler's is per set).
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal Lax808846.Ram Lax808846.RamComputes

open Classical in
theorem niceDecomposition_computable_of (h : DecompRun) :
    ∃ (prog : Program) (c : ℕ), ∀ (W k n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ),
      EncodesGraph g G →
      (∀ v ∈ g ++ [k], c * 2 ^ (c * k ^ 3) * ((g ++ [k]).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * k ^ 3) * (g.length + 2) ^ c ∧
        RunsTo W prog (g ++ [k]) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D, out = 1 :: D ∧ NiceDecomposition G k D) := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := h
  obtain ⟨prog, c₀, H⟩ := compile_computes Δ hN main Fmt.graphK (pC C) hC hC (le_refl 1)
  refine ⟨prog, max c₀ (max C (10 * kappa Δ N main (pC C) * (C + 1) + 1)), ?_⟩
  intro W k n G g henc hg
  set c := max c₀ (max C (10 * kappa Δ N main (pC C) * (C + 1) + 1)) with hcdef
  have hc0 : c₀ ≤ c := le_max_left _ _
  have hcC : C ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcK : 10 * kappa Δ N main (pC C) * (C + 1) + 1 ≤ c := le_trans (le_max_right _ _) (le_max_right _ _)
  set x := g ++ [k] with hx
  have hD2 : x ∈ D2 := mem_D2 henc k
  have hkw : Fmt.graphK.kw x = k := kw_graphK henc k
  have hlen : x.length = g.length + 1 := by rw [hx, List.length_append]; simp
  obtain ⟨hr, hl⟩ := hrun x hD2
  have hcomp := H {x} outWord (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact fmtLen_graphK henc k)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hr)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hl) W
    (fun y hy v hv => by
      rw [Set.mem_singleton_iff.1 hy] at hv ⊢
      rw [hkw]
      exact guard_mono hc0 (by omega) (hg v hv))
  obtain ⟨t, ht, hrt⟩ := hcomp x rfl
  refine ⟨outWord x, t, ?_, hrt, ?_⟩
  · refine le_trans ht ?_
    have hK : Kx (pC C) Fmt.graphK x = C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C := by
      unfold Kx
      rw [hkw]
      show C * 2 ^ (C * k ^ 3) * (x.length + 1) ^ C = _
      rw [hlen]
    have := time_arith (κ := kappa Δ N main (pC C)) (C₀ := C) (C₁ := C) (C₃ := C) (e := k) (X := g.length + 2)
      (X' := g.length + 2) (c := c) (by omega) le_rfl hC hcC hcC hcK
    show 10 * kappa Δ N main (pC C) * (Kx (pC C) Fmt.graphK x + x.length + 1) + 1 ≤ _
    rw [hK, hlen]
    have e : C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C + (g.length + 1) + 1
        = C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C + (g.length + 2) := by ring
    rw [e]
    exact this
  · exact outWord_correct henc k

end Lax117284Proofs.Treewidth.Fun.A2

/-- the statement proved is exactly the concept's -/
example (h : Lax117284Proofs.Treewidth.Fun.A2.DecompRun) : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  Lax117284Proofs.Treewidth.Fun.A2.niceDecomposition_computable_of h
