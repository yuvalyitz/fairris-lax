import Lax117284Proofs.McisHard.Defs

/-!
# WP1: the copy reduction is regular and normal (proved versions of the `Defs` statements)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284.MulticolouredIndepSet Lax117284Proofs.Lemma14Graph
open Lax117284Proofs.McisHard

open Classical in
/-- The neighbour list of the vertex numbered `num v` has as many entries as `v` has neighbours. -/
theorem nbrs_length_num (G : Instance) (v : Fin G.colours × Fin G.size) :
    (G.nbrs (num G v)).length = (Finset.univ.filter (G.graph.Adj v)).card := by
  classical
  have hnd := nbrs_nodup G (num G v)
  rw [← List.toFinset_card_of_nodup hnd]
  have : (G.nbrs (num G v)).toFinset = (Finset.univ.filter (G.graph.Adj v)).image (num G) := by
    ext w'
    simp only [List.mem_toFinset, mem_nbrs, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hw', hadj⟩
      obtain ⟨u, rfl⟩ := exists_num G hw'
      exact ⟨u, (adjAt_num G v u).1 hadj, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨num_lt G u, (adjAt_num G v u).2 hu⟩
  rw [this, Finset.card_image_of_injective _ (num_injective G)]

open Classical in
theorem copy_card {k n r : ℕ} (G : SimpleGraph (Fin n))
    (hG : ∀ u, (Finset.univ.filter (G.Adj u)).card = r) (v : Fin k × Fin n) :
    (Finset.univ.filter ((copyGraph k G).Adj v)).card = (k - 1) * (r + 1) := by
  classical
  have h1 : (Finset.univ.filter ((copyGraph k G).Adj v)) =
      (Finset.univ.filter (fun j : Fin k => j ≠ v.1)) ×ˢ
        (insert v.2 (Finset.univ.filter (G.Adj v.2))) := by
    ext ⟨j, y⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_filter]
    simp only [true_and, Finset.mem_univ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 e.symm, h2.elim (fun e => Or.inl e.symm) Or.inr⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun e => h1 e.symm, h2.elim (fun e => Or.inl e.symm) Or.inr⟩
  rw [h1, Finset.card_product]
  have h2 : (Finset.univ.filter (fun j : Fin k => j ≠ v.1)).card = k - 1 := by
    rw [Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
  have h3 : (insert v.2 (Finset.univ.filter (G.Adj v.2))).card = r + 1 := by
    rw [Finset.card_insert_of_notMem, hG]
    simp
  rw [h2, h3]

open Classical in
theorem copyInst_regular (k : ℕ) {n r : ℕ} (G : SimpleGraph (Fin n))
    (hG : ∀ u, (Finset.univ.filter (G.Adj u)).card = r) :
    (copyInst k G).Regular ((k - 1) * (r + 1)) := by
  intro w hw
  obtain ⟨v, rfl⟩ := exists_num (copyInst k G) hw
  rw [nbrs_length_num]
  exact copy_card G hG v

open Classical in
theorem copyInst_normal (k : ℕ) {n r : ℕ} (G : SimpleGraph (Fin n))
    (hG : ∀ u, (Finset.univ.filter (G.Adj u)).card = r)
    (hk : 2 ≤ k) (hn : 4 ≤ n) (h4 : 4 ∣ k * n * ((k - 1) * (r + 1))) :
    (copyInst k G).Normal := by
  have hreg := copyInst_regular k G hG
  refine ⟨⟨(k - 1) * (r + 1), ?_, hreg⟩, hn, ?_⟩
  · exact Nat.mul_pos (by omega) (by omega)
  · have hh := handshake (copyInst k G) hreg
    have hv : (copyInst k G).vertices = k * n := rfl
    rw [hv] at hh
    omega

open Classical in
theorem H0_normal : H0.Normal := by
  have hG : ∀ u : Fin 4, (Finset.univ.filter ((⊥ : SimpleGraph (Fin 4)).Adj u)).card = 0 := by
    intro u; simp
  exact copyInst_normal (r := 0) 2 (⊥ : SimpleGraph (Fin 4)) (fun u => by convert hG u) (le_refl _) (le_refl _) (by norm_num)

theorem H0_hasIndepSet : H0.HasIndepSet := by
  refine (copyInst_hasIndepSet_iff 2 (⊥ : SimpleGraph (Fin 4))).2
    ⟨{0, 1}, ?_, by decide⟩
  intro a _ b _ _
  simp

end Lax117284Proofs.McisHard.Proved
