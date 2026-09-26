import Lax117284Proofs.ParentTree
import Lax117284.Lemma15
import Lax117284.ConflictGraph

/-!
Lemma 15's construction raises the treewidth by at most two. The two new clients are put
into every bag of a decomposition of the original graph, and that is a decomposition of the
new one: on an original day two original clients conflict exactly as they did, on an
additional day they never conflict at all — their unit jobs end at distinct times — and
every other pair of clients has a new client in it.
-/

namespace Lax117284Proofs.Lemma15Treewidth

open Lax117284.Scheduling Lax117284.Lemma15
open Lax117284.ConflictGraph Lax228581.Treewidth

variable (J : Instance) (k : Fin J.clients → ℕ)

/-! ### The jobs of the original clients -/

theorem pAt_orig {i u : ℕ} (hi : i < J.days) (hu : u < J.clients) :
    (inst J k).pAt i u = J.pAt i u := by
  have hi2 : i < 2 * J.days := by omega
  have hu2 : u < J.clients + 2 := by omega
  simp [Instance.pAt, inst, hi, hu, hi2, hu2]

theorem dAt_orig {i u : ℕ} (hi : i < J.days) (hu : u < J.clients) :
    (inst J k).dAt i u = J.dAt i u := by
  have hi2 : i < 2 * J.days := by omega
  have hu2 : u < J.clients + 2 := by omega
  simp [Instance.dAt, inst, hi, hu, hi2, hu2]

theorem pAt_extra {i u : ℕ} (hi : J.days ≤ i) (hi2 : i < 2 * J.days) (hu : u < J.clients) :
    (inst J k).pAt i u = 1 := by
  have hu2 : u < J.clients + 2 := by omega
  have hi3 : ¬ i < J.days := by omega
  simp [Instance.pAt, inst, hi2, hu, hu2, hi3]

theorem dAt_extra {i u : ℕ} (hi : J.days ≤ i) (hi2 : i < 2 * J.days) (hu : u < J.clients) :
    ((inst J k).dAt i u = dmax J + (u + 1)) ∨
      ((inst J k).dAt i u = dmax J + span J + (u + 1)) := by
  have hu2 : u < J.clients + 2 := by omega
  have hi3 : ¬ i < J.days := by omega
  simp only [Instance.dAt, inst, dif_pos hi2, dif_pos hu2, dif_pos hu, if_neg hi3]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Two original clients conflict in the new instance only if they did in the old one.** -/
theorem conflict_orig {i u v : ℕ} (hi : i < 2 * J.days) (hu : u < J.clients)
    (hv : v < J.clients) (hne : u ≠ v) (h : (inst J k).ConflictAt i u v) :
    ∃ hd : i < J.days, J.ConflictAt i u v := by
  by_cases hd : i < J.days
  · refine ⟨hd, ?_⟩
    simpa only [Instance.ConflictAt, pAt_orig J k hd hu, pAt_orig J k hd hv,
      dAt_orig J k hd hu, dAt_orig J k hd hv] using h
  · exfalso
    have hd' : J.days ≤ i := by omega
    simp only [Instance.ConflictAt, pAt_extra J k hd' hi hu, pAt_extra J k hd' hi hv] at h
    have hs : span J = J.clients + 1 := rfl
    rcases dAt_extra J k hd' hi hu with h1 | h1 <;> rcases dAt_extra J k hd' hi hv with h2 | h2 <;>
      rw [h1, h2] at h <;> omega

/-! ### Adding two clients to every bag of a decomposition

The step is stated for any graph `H` on two more vertices than `G` whose edges among the
first vertices are edges of `G`. -/

section Extend

variable {n : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin (n + 2))}

/-- The bag of the extended decomposition: the old bag together with the two new vertices. -/
def extBag (b : Finset (Fin n)) : Finset (Fin (n + 2)) :=
  b.map ⟨Fin.castAdd 2, Fin.castAdd_injective n 2⟩ ∪ Finset.univ.filter fun c => n ≤ (c : ℕ)

theorem mem_extBag_of_lt {b : Finset (Fin n)} {c : Fin (n + 2)} (hc : (c : ℕ) < n) :
    c ∈ extBag b ↔ (⟨c, hc⟩ : Fin n) ∈ b := by
  simp only [extBag, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨a, ha, rfl⟩ | h)
    · exact ha
    · omega
  · intro h
    exact Or.inl ⟨⟨c, hc⟩, h, rfl⟩

theorem mem_extBag_of_ge {b : Finset (Fin n)} {c : Fin (n + 2)} (hc : n ≤ (c : ℕ)) :
    c ∈ extBag b := by
  simp only [extBag, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr hc

theorem card_extBag_le (b : Finset (Fin n)) : (extBag b).card ≤ b.card + 2 := by
  refine le_trans (Finset.card_union_le _ _) ?_
  rw [Finset.card_map]
  have : (Finset.univ.filter fun c : Fin (n + 2) => n ≤ (c : ℕ)).card ≤ 2 := by
    have h : (Finset.univ.filter fun c : Fin (n + 2) => n ≤ (c : ℕ)).card
        ≤ (Finset.range 2).card := by
      refine Finset.card_le_card_of_injOn (fun c => (c : ℕ) - n) (fun c hc => ?_)
        (fun a ha b hb hab => ?_)
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        simp only [Finset.mem_coe, Finset.mem_range]
        have := c.isLt
        omega
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
        have hab' : (a : ℕ) - n = (b : ℕ) - n := hab
        exact Fin.ext (by omega)
    simpa using h
  omega

/-- **The extension of a tree decomposition by two vertices in every bag.** -/
noncomputable def extend (D : TreeDecomposition G)
    (hadj : ∀ u v : Fin (n + 2), ∀ (hu : (u : ℕ) < n) (hv : (v : ℕ) < n), H.Adj u v →
      G.Adj ⟨u, hu⟩ ⟨v, hv⟩) : TreeDecomposition H where
  Node := D.Node
  nodeFintype := D.nodeFintype
  tree := D.tree
  isTree := D.isTree
  bag i := extBag (D.bag i)
  vertex_mem_bag c := by
    by_cases hc : (c : ℕ) < n
    · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨c, hc⟩
      exact ⟨i, (mem_extBag_of_lt hc).2 hi⟩
    · obtain ⟨i⟩ : Nonempty D.Node := D.isTree.connected.nonempty
      exact ⟨i, mem_extBag_of_ge (by omega)⟩
  edge_mem_bag := by
    intro u v huv
    by_cases hu : (u : ℕ) < n
    · by_cases hv : (v : ℕ) < n
      · obtain ⟨i, h1, h2⟩ := D.edge_mem_bag (hadj u v hu hv huv)
        exact ⟨i, (mem_extBag_of_lt hu).2 h1, (mem_extBag_of_lt hv).2 h2⟩
      · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨u, hu⟩
        exact ⟨i, (mem_extBag_of_lt hu).2 hi, mem_extBag_of_ge (by omega)⟩
    · by_cases hv : (v : ℕ) < n
      · obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨v, hv⟩
        exact ⟨i, mem_extBag_of_ge (by omega), (mem_extBag_of_lt hv).2 hi⟩
      · obtain ⟨i⟩ : Nonempty D.Node := D.isTree.connected.nonempty
        exact ⟨i, mem_extBag_of_ge (by omega), mem_extBag_of_ge (by omega)⟩
  bag_indices_connected c := by
    by_cases hc : (c : ℕ) < n
    · have hset : {i : D.Node | c ∈ extBag (D.bag i)} = {i | (⟨c, hc⟩ : Fin n) ∈ D.bag i} := by
        ext i
        exact mem_extBag_of_lt hc
      rw [hset]
      exact D.bag_indices_connected ⟨c, hc⟩
    · have hset : {i : D.Node | c ∈ extBag (D.bag i)} = Set.univ := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact mem_extBag_of_ge (by omega)
      rw [hset]
      exact (SimpleGraph.induceUnivIso D.tree).connected_iff.2 D.isTree.connected

theorem hasTreewidthAtMost_extend {w : ℕ} (D : TreeDecomposition G)
    (hD : ∀ i, (D.bag i).card ≤ w + 1)
    (hadj : ∀ u v : Fin (n + 2), ∀ (hu : (u : ℕ) < n) (hv : (v : ℕ) < n), H.Adj u v →
      G.Adj ⟨u, hu⟩ ⟨v, hv⟩) : HasTreewidthAtMost H (w + 2) :=
  ⟨extend D hadj, fun i => by
    have := card_extBag_le (D.bag i)
    have := hD i
    show (extBag (D.bag i)).card ≤ w + 2 + 1
    omega⟩

end Extend

/-- A single node holding every vertex is a tree decomposition. -/
noncomputable def single {n : ℕ} (G : SimpleGraph (Fin n)) : TreeDecomposition G where
  Node := Unit
  tree := ⊥
  isTree := SimpleGraph.IsTree.of_subsingleton
  bag _ := Finset.univ
  vertex_mem_bag v := ⟨(), Finset.mem_univ v⟩
  edge_mem_bag u v _ := ⟨(), Finset.mem_univ u, Finset.mem_univ v⟩
  bag_indices_connected v := by
    have : Nonempty {i : Unit | v ∈ (Finset.univ : Finset (Fin n))} := ⟨⟨(), Finset.mem_univ v⟩⟩
    exact ⟨fun a b => by rw [Subsingleton.elim a b]⟩

/-- **The treewidth is attained.** -/
theorem hasTreewidthAtMost_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) :
    HasTreewidthAtMost G (treewidth G) := by
  have hne : {w | HasTreewidthAtMost G w}.Nonempty :=
    ⟨n, single G, fun _ => by
      show (Finset.univ : Finset (Fin n)).card ≤ n + 1
      simp⟩
  exact Nat.sInf_mem hne

/--
---
conclusion: Lax117284.Lemma15.treewidth_le
---
On an original day two original clients conflict exactly as they did before, on an additional
day they never conflict since their unit jobs end at distinct times, and every remaining pair
of clients has one of the two new clients in it — so putting both new clients into every bag
of a decomposition of the old graph gives a decomposition of the new one, at the price of two
in the width.
-/
theorem treewidth_le : treewidth (overallGraph (inst J k)) ≤ treewidth (overallGraph J) + 2 := by
  obtain ⟨D, hD⟩ := hasTreewidthAtMost_treewidth (overallGraph J)
  have hext : HasTreewidthAtMost (overallGraph (inst J k)) (treewidth (overallGraph J) + 2) := by
    refine hasTreewidthAtMost_extend (H := overallGraph (inst J k)) D hD ?_
    intro u v hu hv huv
    obtain ⟨hne, i, hci⟩ := huv
    have hc : (inst J k).ConflictAt (i : ℕ) (u : ℕ) (v : ℕ) :=
      ((inst J k).conflictAt_iff i u v).2 hci
    obtain ⟨hd, hcJ⟩ := conflict_orig J k i.isLt hu hv (fun h => hne (Fin.ext h)) hc
    refine ⟨fun h => hne (Fin.ext (Fin.mk.inj h)), ⟨i, hd⟩, ?_⟩
    exact (J.conflictAt_iff ⟨i, hd⟩ ⟨u, hu⟩ ⟨v, hv⟩).1 hcJ
  exact Nat.sInf_le hext

end Lax117284Proofs.Lemma15Treewidth
