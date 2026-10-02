import Lax117284Proofs.Treewidth.Fun.A3Run
import Lax117284Proofs.Treewidth.Fun.A2Main
import Lax117284.BodlaenderKloks

/-!
# WP A3 (5): `improveDecomposition` from `DecompRun`

* `NiceDecomposition.mono_width` : a nice decomposition of width `l ≤ k` is one of width `k`;
* `improveDecomposition_of h` : the exact statement of the concept axiom `Lax117284.BodlaenderKloks.improveDecomposition`, from
  `improveRun_of h` (the dispatcher) through the compiler `Load.compile_computes` with the format `graphKLD` (parameter entry `l`).

**Glue (TODO until A1 lands `decompose_run : A2.DecompRun`)**: in a last file importing `Fun.A1Main`,
`theorem niceDecomposition_computable_final : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable := A2.niceDecomposition_computable_of decompose_run`
and `theorem improveDecomposition_final : type_of% @Lax117284.BodlaenderKloks.improveDecomposition := A3.improveDecomposition_of decompose_run`,
each with the docstring `---\nconclusion: <Concept.name>\n---` and an `example : type_of% @<Concept.name> := ..._final`.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal Lax808846.Ram Lax808846.RamComputes

theorem NiceDecomposition.mono_width {n : ℕ} {G : SimpleGraph (Fin n)} {l k : ℕ} {D : List ℕ} (h : NiceDecomposition G l D)
    (hlk : l ≤ k) : NiceDecomposition G k D :=
  { length_eq := h.length_eq
    nonempty := h.nonempty
    shape := h.shape
    parent := h.parent
    isTree := h.isTree
    covers := h.covers
    edges := h.edges
    connected := h.connected
    width := fun i hi => le_trans (h.width i hi) (by omega) }

open Classical in
theorem improveDecomposition_of (h : A2.DecompRun) :
    ∃ (prog : Program) (c : ℕ), ∀ (W k l : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (g D : List ℕ),
      EncodesGraph g G → NiceDecomposition G l D →
      (∀ v ∈ g ++ [k, l] ++ D,
        c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + 2) ^ c ∧
        RunsTo W prog (g ++ [k, l] ++ D) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D', out = 1 :: D' ∧ NiceDecomposition G k D') := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := improveRun_of h
  obtain ⟨prog, c₀, H⟩ := compile_computes Δ hN main Fmt.graphKLD (pC1 C) (by simp [pC1]) hC (le_refl 1)
  refine ⟨prog, max c₀ (max (C + 100) (10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1)), ?_⟩
  intro W k l n G g D henc hnice hg
  set c := max c₀ (max (C + 100) (10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1)) with hcdef
  have hc0 : c₀ ≤ c := le_max_left _ _
  have hcC : C + 100 ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcK : 10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1 ≤ c := le_trans (le_max_right _ _) (le_max_right _ _)
  set x := g ++ [k, l] ++ D with hx
  have hD1 : x ∈ D1 := ⟨n, G, g, k, l, D, rfl, henc, hnice.length_eq⟩
  have hkw : Fmt.graphKLD.kw x = l := facts_kw henc k l D
  obtain ⟨hr, hl⟩ := hrun x hD1
  have hcomp := H {x} outWord1 (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact facts_fmtLen henc k l D hnice.length_eq)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hr)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hl) W
    (fun y hy v hv => by
      rw [Set.mem_singleton_iff.1 hy] at hv ⊢
      rw [hkw]
      exact A2.guard_mono hc0 (by omega) (hg v hv))
  obtain ⟨t, ht, hrt⟩ := hcomp x rfl
  refine ⟨outWord1 x, t, ?_, hrt, ?_⟩
  · refine le_trans ht ?_
    have hK : Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := Kx_eq hkw
    have := A2.time_arith (κ := kappa Δ N main (pC1 C)) (C₀ := C + 100) (C₁ := C) (C₃ := C) (e := l) (X := x.length + 1)
      (X' := x.length + 2) (c := c) (by omega) (by omega) hC (by omega) (by omega) hcK
    show 10 * kappa Δ N main (pC1 C) * (Kx (pC1 C) Fmt.graphKLD x + x.length + 1) + 1 ≤ _
    rw [hK]
    have e : (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C + x.length + 1
        = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C + (x.length + 1) := by ring
    rw [e]
    exact this
  · rw [hx, outWord1_eq henc k l D]
    by_cases hle : l ≤ k
    · rw [if_pos hle]
      exact Or.inr ⟨D, rfl, NiceDecomposition.mono_width hnice hle⟩
    · rw [if_neg hle]
      exact A2.outWord_correct henc k

end Lax117284Proofs.Treewidth.Fun.A3

/-- the statement proved is exactly the concept's -/
example (h : Lax117284Proofs.Treewidth.Fun.A2.DecompRun) : type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  Lax117284Proofs.Treewidth.Fun.A3.improveDecomposition_of h
