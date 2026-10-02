import Lax117284Proofs.Treewidth.Trees.WordConn

/-!
# The word tree as a `SimpleGraph` (T2)

* `Lay.isTree`: `treeGraph D` is a tree (each node but the last has one parent, which is later; count the edges);
* `Lay.connected_iff`: connectedness of an induced subgraph of `treeGraph D` is `ConnOn`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma treeGraph_adj (a b : Fin (nodeCount D)) :
    (treeGraph D).Adj a b ↔ a ≠ b ∧ Adj' D a.val b.val := Iff.rfl

/-- Every node reaches the last one. -/
lemma Lay.reachable_last (L : Lay n D) (x : Fin (nodeCount D)) :
    (treeGraph D).Reachable x ⟨nodeCount D - 1, by have := L.nonempty; omega⟩ := by
  have hN := L.nonempty
  obtain ⟨x, hx⟩ := x
  obtain ⟨k, hk⟩ : ∃ k, nodeCount D - 1 - x = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases hxl : x = nodeCount D - 1
    · subst hxl; exact SimpleGraph.Reachable.refl _
    · have hx1 : x + 1 < nodeCount D := by omega
      obtain ⟨p, hp, -⟩ := L.parent x hx1
      have hlt := L.isChild_lt hp
      have hr := ih (nodeCount D - 1 - p) (by omega) p hlt.2 rfl
      have hadj : (treeGraph D).Adj ⟨x, hx⟩ ⟨p, hlt.2⟩ :=
        ⟨fun h => by have := Fin.mk.inj h; omega, Or.inl hp⟩
      exact hadj.reachable.trans hr

lemma Lay.isTree (L : Lay n D) : (treeGraph D).IsTree := by
  classical
  have hN := L.nonempty
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hconn : (treeGraph D).Connected := by
    have : Nonempty (Fin (nodeCount D)) := ⟨⟨0, hN⟩⟩
    exact SimpleGraph.Connected.mk (fun x y => (L.reachable_last x).trans (L.reachable_last y).symm)
  refine ⟨hconn, le_antisymm ?_ ?_⟩
  · -- at most `N - 1` edges: every edge is `{c, parent c}`
    have hpar : ∀ c : Fin (nodeCount D - 1), ∃ p : Fin (nodeCount D), IsChild D c.val p.val := by
      intro c
      obtain ⟨p, hp, -⟩ := L.parent c.val (by omega)
      exact ⟨⟨p, (L.isChild_lt hp).2⟩, hp⟩
    choose par hpar using hpar
    have hsub : (treeGraph D).edgeSet ⊆
        (fun c : Fin (nodeCount D - 1) => s(((⟨c.val, by omega⟩ : Fin (nodeCount D))), par c)) '' Set.univ := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        obtain ⟨-, h | h⟩ := he
        · have hlt := L.isChild_lt h
          refine ⟨⟨a.val, by omega⟩, Set.mem_univ _, ?_⟩
          have := L.parent_unique (hpar ⟨a.val, by omega⟩) h
          have hb : par ⟨a.val, by omega⟩ = b := Fin.ext this
          simp [hb]
        · have hlt := L.isChild_lt h
          refine ⟨⟨b.val, by omega⟩, Set.mem_univ _, ?_⟩
          have := L.parent_unique (hpar ⟨b.val, by omega⟩) h
          have hb : par ⟨b.val, by omega⟩ = a := Fin.ext this
          simp [hb, Sym2.eq_swap]
    have h1 : Set.ncard (treeGraph D).edgeSet ≤ nodeCount D - 1 := by
      calc Set.ncard (treeGraph D).edgeSet
          ≤ Set.ncard ((fun c : Fin (nodeCount D - 1) =>
              s(((⟨c.val, by omega⟩ : Fin (nodeCount D))), par c)) '' Set.univ) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ Set.ncard (Set.univ : Set (Fin (nodeCount D - 1))) := Set.ncard_image_le (Set.toFinite _)
        _ = nodeCount D - 1 := by simp
    have : Nat.card (treeGraph D).edgeSet = Set.ncard (treeGraph D).edgeSet := rfl
    rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  · have := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card (α := Fin (nodeCount D)), Fintype.card_fin] at this
    simpa using this

lemma mem_bagN_fin {D : List ℕ} {i : ℕ} (v : Fin n) : v.val ∈ bagN n D i ↔ v ∈ bagAt n D i := by
  rw [mem_bagN]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

lemma Lay.connected_iff (L : Lay n D) (S : Set ℕ) (hS : ∀ j ∈ S, j < nodeCount D) :
    ((treeGraph D).induce {i : Fin (nodeCount D) | i.val ∈ S}).Connected ↔ ConnOn D S := by
  constructor
  · intro h
    refine ⟨?_, fun x hx y hy => ?_⟩
    · obtain ⟨⟨i, hi⟩⟩ := h.nonempty
      exact ⟨i.val, hi⟩
    · have hr := h.preconnected ⟨⟨x, hS x hx⟩, hx⟩ ⟨⟨y, hS y hy⟩, hy⟩
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      exact Relation.ReflTransGen.lift (fun a : {i : Fin (nodeCount D) // i.val ∈ S} => a.1.val)
        (fun a b hab => ⟨a.2, b.2, ((treeGraph_adj a.1 b.1).1 hab).2⟩) _ _ hr
  · rintro ⟨⟨x0, hx0⟩, hc⟩
    have : Nonempty ↥{i : Fin (nodeCount D) | i.val ∈ S} := ⟨⟨⟨x0, hS x0 hx0⟩, hx0⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨⟨x, hxN⟩, hxS⟩ ⟨⟨y, hyN⟩, hyS⟩
    have hpath := hc x hxS y hyS
    have key : ∀ b, Relation.ReflTransGen (RelOn D S) x b →
        ∃ hb : b ∈ S, (SimpleGraph.induce {i : Fin (nodeCount D) | i.val ∈ S} (treeGraph D)).Reachable
          ⟨⟨x, hxN⟩, hxS⟩ ⟨⟨b, hS b hb⟩, hb⟩ := by
      intro b hb
      induction hb with
      | refl => exact ⟨hxS, SimpleGraph.Reachable.refl _⟩
      | tail hab hbc ih =>
        rename_i b c
        obtain ⟨hb, hreach⟩ := ih
        have hne : (⟨b, hS b hb⟩ : Fin (nodeCount D)) ≠ ⟨c, hS c hbc.2.1⟩ := by
          intro h
          have := Fin.mk.inj h
          rcases hbc.2.2 with h' | h' <;> have := (L.isChild_lt h').1 <;> omega
        have hadj : (SimpleGraph.induce {i : Fin (nodeCount D) | i.val ∈ S} (treeGraph D)).Adj
            ⟨⟨b, hS b hb⟩, hb⟩ ⟨⟨c, hS c hbc.2.1⟩, hbc.2.1⟩ := ⟨hne, hbc.2.2⟩
        exact ⟨hbc.2.1, hreach.trans hadj.reachable⟩
    exact (key y hpath).2

lemma Lay.connected_bagAt_iff (L : Lay n D) (v : Fin n) :
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt n D i}).Connected ↔
      ConnOn D (Sv n D v.val) := by
  have hset : {i : Fin (nodeCount D) | v ∈ bagAt n D i} =
      {i : Fin (nodeCount D) | i.val ∈ Sv n D v.val} := by
    ext i
    simp [Sv, mem_bagN_fin]
  rw [hset]
  exact L.connected_iff _ (fun j hj => hj.1)

end Word

end Lax117284Proofs.Treewidth.Trees
