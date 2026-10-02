import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt
import Lax117284Proofs.Treewidth.Trees.Bridge1Root

/-!
# Bridge 1, direction (→): an abstract tree decomposition folds into an `RT`

A rooted tree given by a parent function (`Rooted`) with bags whose occurrence sets are connected folds into an
`RT` with `Conn`; then the concept's `TreeDecomposition` is rooted (`exists_rooting`) and folded.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Trees.RootedTree Lax228581.Treewidth

section fold

variable {V : Type} [Fintype V] {r : V} {par : V → V} {d : V → ℕ}

/-- Folding: the subtree below `v`. -/
theorem exists_rt_sub (hR : Rooted r par d) (bag : V → Finset ℕ)
    (hconn : ∀ x a b (ha : x ∈ bag a) (hb : x ∈ bag b),
      ((rgraph par).induce {i | x ∈ bag i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∀ v : V, ∃ t : RT, t.rootBag = bag v ∧ t.Conn ∧ (∀ X ∈ t.bags, ∃ u, Desc r par v u ∧ bag u = X) ∧
      (∀ u, Desc r par v u → bag u ∈ t.bags) := by
  classical
  have : Inhabited RT := ⟨.node ∅ []⟩
  intro v
  induction hn : (Finset.univ.filter (Desc r par v)).card using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    have hkid_d : ∀ w, w ≠ r → par w = v → d w = d v + 1 := by
      intro w hw hp
      have := hR.d_par w hw
      rw [hp] at this
      omega
    have ih' : ∀ w, w ≠ r → par w = v → ∃ t : RT, t.rootBag = bag w ∧ t.Conn ∧
        (∀ X ∈ t.bags, ∃ u, Desc r par w u ∧ bag u = X) ∧ (∀ u, Desc r par w u → bag u ∈ t.bags) := by
      intro w hw hp
      refine ih _ ?_ w rfl
      rw [← hn]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨v, by simp [Desc.refl], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hv
        have := Desc.d_le hR hv
        have := hkid_d w hw hp
        omega
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact (Desc.child hw hp).trans hu
    choose! f hf using ih'
    let kids : Finset V := Finset.univ.filter (fun w => w ≠ r ∧ par w = v)
    have hkids : ∀ w, w ∈ kids ↔ w ≠ r ∧ par w = v := by
      intro w; simp [kids]
    refine ⟨.node (bag v) (kids.toList.map f), rfl, ?_, ?_, ?_⟩
    · rw [RT.conn_node_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        exact (hf w hw.1 hw.2).2.1
      · intro k hk x hxv hxk
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        obtain ⟨hw1, hw2⟩ := hw
        obtain ⟨hr1, hc, hb, hb2⟩ := hf w hw1 hw2
        rw [hr1]
        obtain ⟨X, hX, hxX⟩ := (RT.mem_verts_iff _ _).1 hxk
        obtain ⟨u, hu, rfl⟩ := hb X hX
        by_contra hxw
        have hreach := hconn x u v hxX hxv
        obtain ⟨x', hx'S, hx'A, hx'r, hpS, hpA⟩ :=
          exit (S := {i | x ∈ bag i}) (A := {y | Desc r par w y}) hR
            (fun c hc hp => Desc.tail hp hc rfl) hxX hu hxv
            (by
              intro hv
              have := Desc.d_le hR hv
              have := hkid_d w hw1 hw2
              simp only [Set.mem_ofPred_eq] at hv
              omega) hreach
        have := Desc.eq_of_par_not hx'A hpA
        subst this
        exact hxw hx'S
      · rw [List.pairwise_map]
        apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList kids)
        intro w1 hw1 w2 hw2 hne x hx1 hx2
        rw [Finset.mem_toList, hkids] at hw1 hw2
        obtain ⟨X1, hX1, hxX1⟩ := (RT.mem_verts_iff _ _).1 hx1
        obtain ⟨X2, hX2, hxX2⟩ := (RT.mem_verts_iff _ _).1 hx2
        obtain ⟨u1, hu1, rfl⟩ := (hf w1 hw1.1 hw1.2).2.2.1 X1 hX1
        obtain ⟨u2, hu2, rfl⟩ := (hf w2 hw2.1 hw2.2).2.2.1 X2 hX2
        have hreach := hconn x u1 u2 hxX1 hxX2
        have hd1 := hkid_d w1 hw1.1 hw1.2
        have hd2 := hkid_d w2 hw2.1 hw2.2
        obtain ⟨x', hx'S, hx'A, hx'r, hpS, hpA⟩ :=
          exit (S := {i | x ∈ bag i}) (A := {y | Desc r par w1 y}) hR
            (fun c hc hp => Desc.tail hp hc rfl) hxX1 hu1 hxX2
            (by
              intro hv
              simp only [Set.mem_ofPred_eq] at hv
              rcases Desc.comparable hv hu2 with h | h
              · have := Desc.d_lt hR h hne
                omega
              · have := Desc.d_lt hR h (Ne.symm hne)
                omega) hreach
        have := Desc.eq_of_par_not hx'A hpA
        subst this
        rw [hw1.2] at hpS
        exact hpS
    · intro X hX
      rw [RT.bags_node] at hX
      rcases hX with rfl | ⟨k, hk, hX⟩
      · exact ⟨v, Desc.refl _, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        obtain ⟨u, hu, e⟩ := (hf w hw.1 hw.2).2.2.1 X hX
        exact ⟨u, (Desc.child hw.1 hw.2).trans hu, e⟩
    · intro u hu
      rw [RT.bags_node]
      by_cases huv : v = u
      · subst huv; exact Or.inl rfl
      · obtain ⟨w, hw1, hw2, hwu⟩ := Desc.exists_kid hu huv
        right
        refine ⟨f w, List.mem_map.2 ⟨w, ?_, rfl⟩, (hf w hw1 hw2).2.2.2 u hwu⟩
        rw [Finset.mem_toList, hkids]
        exact ⟨hw1, hw2⟩

/-- Folding at the root. -/
theorem exists_rt (hR : Rooted r par d) (bag : V → Finset ℕ)
    (hconn : ∀ x a b (ha : x ∈ bag a) (hb : x ∈ bag b),
      ((rgraph par).induce {i | x ∈ bag i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ t : RT, t.rootBag = bag r ∧ t.Conn ∧ (∀ X ∈ t.bags, ∃ i, bag i = X) ∧ (∀ i, bag i ∈ t.bags) := by
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_rt_sub hR bag hconn r
  exact ⟨t, h1, h2, fun X hX => let ⟨u, _, e⟩ := h3 X hX; ⟨u, e⟩, fun i => h4 i (Desc.root hR i)⟩

end fold

theorem reachable_congr {V : Type} {T T' : SimpleGraph V} (hT : T = T') {S S' : Set V} (hS : S = S')
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (h : (T.induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    (T'.induce S').Reachable ⟨a, hS ▸ ha⟩ ⟨b, hS ▸ hb⟩ := by
  subst hT; subst hS; exact h

/-- **Bridge 1, (→).** -/
theorem rt_of_hasTreewidthAtMost {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ}
    (h : HasTreewidthAtMost G w) :
    ∃ t : RT, t.IsTD (liftGraph G) (Finset.range n) ∧ t.Width w := by
  obtain ⟨D, hD⟩ := h
  have := D.nodeFintype
  have hne : Nonempty D.Node := D.isTree.connected.nonempty
  obtain ⟨r⟩ := hne
  obtain ⟨par, d, hR, heq⟩ := exists_rooting D.isTree r
  let bag' : D.Node → Finset ℕ := fun i => (D.bag i).map Fin.valEmbedding
  have hmem : ∀ x i, x ∈ bag' i ↔ ∃ y : Fin n, y ∈ D.bag i ∧ y.val = x := by
    intro x i; simp [bag']
  have hconn : ∀ x a b (ha : x ∈ bag' a) (hb : x ∈ bag' b),
      ((rgraph par).induce {i | x ∈ bag' i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro x a b ha hb
    obtain ⟨y, hya, rfl⟩ := (hmem x a).1 ha
    obtain ⟨y', hyb, hy'⟩ := (hmem _ b).1 hb
    have hyy : y' = y := Fin.ext hy'
    subst hyy
    have hS : {i | y'.val ∈ bag' i} = {i | y' ∈ D.bag i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      rw [hmem]
      constructor
      · rintro ⟨z, hz, hzy⟩
        rwa [Fin.ext hzy] at hz
      · intro hy; exact ⟨y', hy, rfl⟩
    have := reachable_congr heq hS.symm (a := a) (b := b) hya hyb
      ((D.bag_indices_connected y').preconnected ⟨a, hya⟩ ⟨b, hyb⟩)
    exact this
  obtain ⟨t, hroot, hconn', hb1, hb2⟩ := exists_rt hR bag' hconn
  refine ⟨t, ⟨?_, ?_, hconn'⟩, ?_⟩
  · ext x
    rw [RT.mem_verts_iff, Finset.mem_range]
    constructor
    · rintro ⟨X, hX, hx⟩
      obtain ⟨i, rfl⟩ := hb1 X hX
      obtain ⟨y, _, rfl⟩ := (hmem x i).1 hx
      exact y.2
    · intro hx
      obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨x, hx⟩
      exact ⟨bag' i, hb2 i, (hmem x i).2 ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro u v huv _ _
    obtain ⟨u', v', hadj, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 huv
    obtain ⟨i, hui, hvi⟩ := D.edge_mem_bag hadj
    exact ⟨bag' i, hb2 i, (hmem _ i).2 ⟨u', hui, rfl⟩, (hmem _ i).2 ⟨v', hvi, rfl⟩⟩
  · intro X hX
    obtain ⟨i, rfl⟩ := hb1 X hX
    simpa [bag'] using hD i


end Lax117284Proofs.Treewidth.Trees
