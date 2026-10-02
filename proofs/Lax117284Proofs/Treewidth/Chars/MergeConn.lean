import Lax117284Proofs.Treewidth.Chars.MergeSide

/-!
# `Conn` of a merged chain (C3)

The interface `MergeI KM KA KB` says that the tree `KM` is a merge of `KA` and `KB`: it is connected, its vertices and
root bag are the unions, and every bag of `KA`, `KB` is contained in a bag of `KM`.  `MergeCtx` collects the
hypotheses on the two chains and the merged kid trees; `chain_claim` proves the interface for the merged chain by
induction along the lattice path.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

structure MergeI (KM KA KB : RT) : Prop where
  conn : KM.Conn
  verts : KM.verts = KA.verts ∪ KB.verts
  root : KM.rootBag = KA.rootBag ∪ KB.rootBag
  bagsA : ∀ X ∈ KA.bags, ∃ Y ∈ KM.bags, X ⊆ Y
  bagsB : ∀ X ∈ KB.bags, ∃ Y ∈ KM.bags, X ⊆ Y

structure MergeCtx (B Ua Ub S : Finset ℕ) (nA nB : List CNode) (kAT kBT kMT : List RT) : Prop where
  hU : Ua ∩ Ub = B
  Abag : ∀ x ∈ nA, x.bag ⊆ Ua ∧ x.bag ∩ B = S
  Bbag : ∀ x ∈ nB, x.bag ⊆ Ub ∧ x.bag ∩ B = S
  Ajunk : ∀ x ∈ nA, ∀ J ∈ x.junk, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S
  Bjunk : ∀ x ∈ nB, ∀ J ∈ x.junk, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S
  Akid : ∀ K ∈ kAT, K.verts ⊆ Ua
  Bkid : ∀ K ∈ kBT, K.verts ⊆ Ub
  Aconn : (AR.chainToRT nA kAT).Conn
  Bconn : (AR.chainToRT nB kBT).Conn
  kids : F3 (fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B) kMT kAT kBT

/-! ## small helpers -/

theorem sub_ite {α : Type} (b : Bool) (l : List α) : (if b = true then l else []).Sublist l := by
  cases b <;> simp

theorem mem_vertsL_ite (b : Bool) (l : List RT) (x : ℕ) :
    x ∈ RT.vertsL (if b = true then l else []) ↔ b = true ∧ x ∈ RT.vertsL l := by
  cases b <;> simp [RT.mem_vertsL_iff]

theorem vertsL_kids {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) (x : ℕ) :
    x ∈ RT.vertsL kMT ↔ x ∈ RT.vertsL kAT ∨ x ∈ RT.vertsL kBT := by
  rw [mem_vertsL, mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨K, hK, hx⟩
    obtain ⟨a, ha, b, hb, hI, _⟩ := F3.mem_mid ctx.kids K hK
    rw [hI.verts] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl ⟨a, ha, hx⟩
    · exact Or.inr ⟨b, hb, hx⟩
  · rintro (⟨a, ha, hx⟩ | ⟨b, hb, hx⟩)
    · obtain ⟨m, hm, b, hb, hI, _⟩ := F3.mem_left ctx.kids a ha
      exact ⟨m, hm, by rw [hI.verts]; exact Finset.mem_union_left _ hx⟩
    · obtain ⟨m, hm, a, ha, hI, _⟩ := F3.mem_right ctx.kids b hb
      exact ⟨m, hm, by rw [hI.verts]; exact Finset.mem_union_right _ hx⟩

theorem kids_agree {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) (x : ℕ) (hx : x ∈ B) :
    x ∈ RT.vertsL kAT ↔ x ∈ RT.vertsL kBT := by
  rw [mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨a, ha, hxa⟩
    obtain ⟨m, hm, b, hb, hI, hag⟩ := F3.mem_left ctx.kids a ha
    have : x ∈ a.verts ∩ B := Finset.mem_inter.2 ⟨hxa, hx⟩
    rw [hag] at this
    exact ⟨b, hb, (Finset.mem_inter.1 this).1⟩
  · rintro ⟨b, hb, hxb⟩
    obtain ⟨m, hm, a, ha, hI, hag⟩ := F3.mem_right ctx.kids b hb
    have : x ∈ b.verts ∩ B := Finset.mem_inter.2 ⟨hxb, hx⟩
    rw [← hag] at this
    exact ⟨a, ha, (Finset.mem_inter.1 this).1⟩

/-- A `B`-vertex below a node on one side is below (the same-indexed node of) the other. -/
theorem PA_cross {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ} (hi : i < nA.length) (hj : j < nB.length)
    (b1 b2 : Bool) : ∀ x ∈ B, x ∈ PA nB kBT j b2 → x ∈ PA nA kAT i b1 := by
  intro x hxB hx
  rcases PA_inter_B (fun x hx => (ctx.Bbag x hx).2) (fun x hx J hJ => (ctx.Bjunk x hx J hJ).2) hj b2 x hx hxB with h | h
  · exact S_sub_PA (fun x hx => (ctx.Abag x hx).2) hi b1 h
  · exact vertsL_sub_PA hi b1 x ((kids_agree ctx x hxB).2 h)

theorem PB_cross {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ} (hi : i < nA.length) (hj : j < nB.length)
    (b1 b2 : Bool) : ∀ x ∈ B, x ∈ PA nA kAT i b1 → x ∈ PA nB kBT j b2 := by
  intro x hxB hx
  rcases PA_inter_B (fun x hx => (ctx.Abag x hx).2) (fun x hx J hJ => (ctx.Ajunk x hx J hJ).2) hi b1 x hx hxB with h | h
  · exact S_sub_PA (fun x hx => (ctx.Bbag x hx).2) hj b2 h
  · exact vertsL_sub_PA hj b2 x ((kids_agree ctx x hxB).1 h)

theorem mem_vertsL_append {l1 l2 : List RT} {x : ℕ} :
    x ∈ RT.vertsL (l1 ++ l2) ↔ x ∈ RT.vertsL l1 ∨ x ∈ RT.vertsL l2 := by
  rw [mem_vertsL, mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact Or.inl ⟨k, hk, hx⟩
    · exact Or.inr ⟨k, hk, hx⟩
  · rintro (⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
    · exact ⟨k, List.mem_append_left _ hk, hx⟩
    · exact ⟨k, List.mem_append_right _ hk, hx⟩

theorem kid_verts_A {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) {m a b : RT} (hI : MergeI m a b)
    (hag : a.verts ∩ B = b.verts ∩ B) (hbU : b.verts ⊆ Ub) {v : ℕ} (hv : v ∈ Ua) (hvm : v ∈ m.verts) :
    v ∈ a.verts := by
  rw [hI.verts] at hvm
  rcases Finset.mem_union.1 hvm with h | h
  · exact h
  · have hvB : v ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨hv, hbU h⟩
    have : v ∈ b.verts ∩ B := Finset.mem_inter.2 ⟨h, hvB⟩
    rw [← hag] at this
    exact (Finset.mem_inter.1 this).1

theorem kid_verts_B {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) {m a b : RT} (hI : MergeI m a b)
    (hag : a.verts ∩ B = b.verts ∩ B) (haU : a.verts ⊆ Ua) {v : ℕ} (hv : v ∈ Ub) (hvm : v ∈ m.verts) :
    v ∈ b.verts := by
  rw [hI.verts] at hvm
  rcases Finset.mem_union.1 hvm with h | h
  · have hvB : v ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨haU h, hv⟩
    have : v ∈ a.verts ∩ B := Finset.mem_inter.2 ⟨h, hvB⟩
    rw [hag] at this
    exact (Finset.mem_inter.1 this).1
  · exact h

/-- The last node of a merged chain. -/
theorem claim_last {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ}
    (hi : i < nA.length) (hj : j < nB.length) (hil : ¬ (i + 1 < nA.length)) (hjl : ¬ (j + 1 < nB.length))
    (b1 b2 : Bool) {T : RT}
    (hT : T = RT.node (cbag nA i ∪ cbag nB j)
        ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ kMT)) :
    T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
    (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i b1 ∨ x ∈ PA nB kBT j b2) ∧
    (∀ X, (X = cbag nA i ∨ (b1 = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨ ∃ K ∈ succL nA kAT i, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) ∧
    (∀ X, (X = cbag nB j ∨ (b2 = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨ ∃ K ∈ succL nB kBT j, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) := by
  subst hT
  obtain ⟨hAc, hAk, hAr, hAp⟩ := local_facts hi (conn_drop ctx.Aconn i hi)
  obtain ⟨hBc, hBk, hBr, hBp⟩ := local_facts hj (conn_drop ctx.Bconn j hj)
  have hsA : succL nA kAT i = kAT := succL_of_last hil
  have hsB : succL nB kBT j = kBT := succL_of_last hjl
  rw [hsA] at hAk hAr hAp
  rw [hsB] at hBk hBr hBp
  have hmA : nA[i] ∈ nA := List.getElem_mem hi
  have hmB : nB[j] ∈ nB := List.getElem_mem hj
  have hXA : cbag nA i ⊆ Ua := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).1
  have hAB : cbag nA i ∩ B = S := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).2
  have hXB : cbag nB j ⊆ Ub := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).1
  have hBB : cbag nB j ∩ B = S := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).2
  have hjA : ∀ J ∈ cjunk nA i, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hi]; exact fun J hJ => ctx.Ajunk _ hmA J hJ
  have hjB : ∀ J ∈ cjunk nB j, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hj]; exact fun J hJ => ctx.Bjunk _ hmB J hJ
  have hcisub : (if b1 = true then cjunk nA i else []).Sublist (cjunk nA i) := sub_ite b1 _
  have hcjsub : (if b2 = true then cjunk nB j else []).Sublist (cjunk nB j) := sub_ite b2 _
  have hSA : S ⊆ cbag nA i := by rw [← hAB]; exact Finset.inter_subset_left
  have hSB : S ⊆ cbag nB j := by rw [← hBB]; exact Finset.inter_subset_left
  have hconn : (RT.node (cbag nA i ∪ cbag nB j)
      ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ kMT)).Conn := by
    apply conn_merged_node (B := B) (Ua := Ua) (Ub := Ub) (S := S) ctx.hU hXA hXB hAB hBB
    · exact fun J hJ => hAc J (hcisub.subset hJ)
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).1
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).2
    · exact fun J hJ => hAr J (List.mem_append_left _ (hcisub.subset hJ))
    · exact List.Pairwise.sublist hcisub (List.pairwise_append.1 hAp).1
    · exact fun J hJ => hBc J (hcjsub.subset hJ)
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).1
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).2
    · exact fun J hJ => hBr J (List.mem_append_left _ (hcjsub.subset hJ))
    · exact List.Pairwise.sublist hcjsub (List.pairwise_append.1 hBp).1
    · -- successors are connected
      intro K hK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      exact hP.1.conn
    · intro K hK v hv hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hva := kid_verts_A ctx.hU hP.1 hP.2 (ctx.Bkid b hb) (hXA hv) hvK
      have := hAr a (List.mem_append_right _ ha) v hv hva
      rw [hP.1.root]; exact Finset.mem_union_left _ this
    · intro K hK v hv hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hvb := kid_verts_B ctx.hU hP.1 hP.2 (ctx.Akid a ha) (hXB hv) hvK
      have := hBr b (List.mem_append_right _ hb) v hv hvb
      rw [hP.1.root]; exact Finset.mem_union_right _ this
    · intro J hJ K hK v hvJ hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hJ' := hcisub.subset hJ
      by_cases hvUa : v ∈ Ua
      · have hva := kid_verts_A ctx.hU hP.1 hP.2 (ctx.Bkid b hb) hvUa hvK
        exact (List.pairwise_append.1 hAp).2.2 J hJ' a ha v hvJ hva
      · exact absurd ((hjA J hJ').1 hvJ) hvUa
    · intro J hJ K hK v hvJ hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hJ' := hcjsub.subset hJ
      have hvUb := (hjB J hJ').1 hvJ
      have hvb := kid_verts_B ctx.hU hP.1 hP.2 (ctx.Akid a ha) hvUb hvK
      exact (List.pairwise_append.1 hBp).2.2 J hJ' b hb v hvJ hvb
    · -- pairwise successors
      apply F3.pairwise (P := fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B)
        (RA := fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag nA i)
        (RB := fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag nB j) ctx.kids _
        (List.pairwise_append.1 hAp).2.1 (List.pairwise_append.1 hBp).2.1
      intro m1 hm1 a1 ha1 b1 hb1 m2 hm2 a2 ha2 b2 hb2 P1 P2 R1 R2 v hv1 hv2
      have hs1 : v ∈ Ua ∨ v ∈ Ub := by
        rw [P1.1.verts] at hv1
        rcases Finset.mem_union.1 hv1 with h | h
        · exact Or.inl (ctx.Akid a1 ha1 h)
        · exact Or.inr (ctx.Bkid b1 hb1 h)
      rcases hs1 with hUa | hUb
      · have h1 := kid_verts_A ctx.hU P1.1 P1.2 (ctx.Bkid b1 hb1) hUa hv1
        have h2 := kid_verts_A ctx.hU P2.1 P2.2 (ctx.Bkid b2 hb2) hUa hv2
        exact Finset.mem_union_left _ (R1 v h1 h2)
      · have h1 := kid_verts_B ctx.hU P1.1 P1.2 (ctx.Akid a1 ha1) hUb hv1
        have h2 := kid_verts_B ctx.hU P2.1 P2.2 (ctx.Akid a2 ha2) hUb hv2
        exact Finset.mem_union_right _ (R2 v h1 h2)
  refine ⟨hconn, rfl, ?_, ?_, ?_⟩
  · intro x
    rw [RT.verts_node, ← mem_vertsL, mem_vertsL_append, mem_vertsL_append, mem_vertsL_ite, mem_vertsL_ite,
      vertsL_kids ctx, mem_PA, mem_PA, hsA, hsB]
    simp only [Finset.mem_union]
    tauto
  · intro X hX
    rcases hX with hX | ⟨hb1, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_left
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb1, if_true, List.mem_append]
      exact Or.inl (Or.inl hJ)
    · rw [hsA] at hK
      obtain ⟨m, hm, b, hb, hP⟩ := F3.mem_left ctx.kids K hK
      obtain ⟨Y, hY, hXY⟩ := hP.1.bagsA X hX
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨m, List.mem_append_right _ hm, hY⟩), hXY⟩
  · intro X hX
    rcases hX with hX | ⟨hb2, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_right
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb2, if_true, List.mem_append]
      exact Or.inl (Or.inr hJ)
    · rw [hsB] at hK
      obtain ⟨m, hm, a, ha, hP⟩ := F3.mem_right ctx.kids K hK
      obtain ⟨Y, hY, hXY⟩ := hP.1.bagsB X hX
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨m, List.mem_append_right _ hm, hY⟩), hXY⟩

theorem mem_ite_empty (b : Bool) (s : Finset ℕ) (x : ℕ) : x ∈ (if b = true then s else ∅) ↔ b = true ∧ x ∈ s := by
  cases b <;> simp

theorem logic_step (p1 p2 q1 q2 a b : Prop) :
    ((p1 ∨ p2) ∨ (q1 ∨ q2) ∨ a ∨ b) ↔ (((p1 ∨ q1) ∨ a) ∨ ((p2 ∨ q2) ∨ b)) := by tauto

/-- An inner node of a merged chain. -/
theorem claim_step {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j i' j' : ℕ}
    (hi : i < nA.length) (hj : j < nB.length) (hi' : i' < nA.length) (hj' : j' < nB.length)
    (hst : LStep (i, j) (i', j')) (b1 b2 : Bool) {T T' : RT}
    (hC' : T'.Conn) (hR' : T'.rootBag = cbag nA i' ∪ cbag nB j')
    (hV' : ∀ x, x ∈ T'.verts ↔ x ∈ PA nA kAT i' (decide (i ≠ i')) ∨ x ∈ PA nB kBT j' (decide (j ≠ j')))
    (hCA' : ∀ X, (X = cbag nA i' ∨ (decide (i ≠ i') = true ∧ ∃ J ∈ cjunk nA i', X ∈ J.bags) ∨
      ∃ K ∈ succL nA kAT i', X ∈ K.bags) → ∃ Y ∈ T'.bags, X ⊆ Y)
    (hCB' : ∀ X, (X = cbag nB j' ∨ (decide (j ≠ j') = true ∧ ∃ J ∈ cjunk nB j', X ∈ J.bags) ∨
      ∃ K ∈ succL nB kBT j', X ∈ K.bags) → ∃ Y ∈ T'.bags, X ⊆ Y)
    (hT : T = RT.node (cbag nA i ∪ cbag nB j)
        ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ [T'])) :
    T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
    (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i b1 ∨ x ∈ PA nB kBT j b2) ∧
    (∀ X, (X = cbag nA i ∨ (b1 = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨ ∃ K ∈ succL nA kAT i, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) ∧
    (∀ X, (X = cbag nB j ∨ (b2 = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨ ∃ K ∈ succL nB kBT j, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) := by
  subst hT
  have hAi : i' = i ∨ i' = i + 1 := by
    rcases hst with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only at h1 <;> omega
  have hBj : j' = j ∨ j' = j + 1 := by
    rcases hst with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp only at h2 <;> omega
  obtain ⟨hAc, hAk, hAr, hAp⟩ := local_facts hi (conn_drop ctx.Aconn i hi)
  obtain ⟨hBc, hBk, hBr, hBp⟩ := local_facts hj (conn_drop ctx.Bconn j hj)
  obtain ⟨hSA1, hSA2⟩ := side_conn hi hi' hAi hAr hAp
  obtain ⟨hSB1, hSB2⟩ := side_conn hj hj' hBj hBr hBp
  have hmA : nA[i] ∈ nA := List.getElem_mem hi
  have hmB : nB[j] ∈ nB := List.getElem_mem hj
  have hXA : cbag nA i ⊆ Ua := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).1
  have hAB : cbag nA i ∩ B = S := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).2
  have hXB : cbag nB j ⊆ Ub := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).1
  have hBB : cbag nB j ∩ B = S := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).2
  have hjA : ∀ J ∈ cjunk nA i, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hi]; exact fun J hJ => ctx.Ajunk _ hmA J hJ
  have hjB : ∀ J ∈ cjunk nB j, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hj]; exact fun J hJ => ctx.Bjunk _ hmB J hJ
  have hcisub : (if b1 = true then cjunk nA i else []).Sublist (cjunk nA i) := sub_ite b1 _
  have hcjsub : (if b2 = true then cjunk nB j else []).Sublist (cjunk nB j) := sub_ite b2 _
  have hPAsub : PA nA kAT i' (decide (i ≠ i')) ⊆ Ua :=
    PA_sub_U (fun x hx => (ctx.Abag x hx).1) (fun x hx J hJ => (ctx.Ajunk x hx J hJ).1) ctx.Akid hi' _
  have hPBsub : PA nB kBT j' (decide (j ≠ j')) ⊆ Ub :=
    PA_sub_U (fun x hx => (ctx.Bbag x hx).1) (fun x hx J hJ => (ctx.Bjunk x hx J hJ).1) ctx.Bkid hj' _
  -- a vertex of `T'` in `Ua` lies in the `A`-part, one in `Ub` lies in the `B`-part
  have hToA : ∀ v ∈ Ua, v ∈ T'.verts → v ∈ PA nA kAT i' (decide (i ≠ i')) := by
    intro v hv hvT
    rcases (hV' v).1 hvT with h | h
    · exact h
    · have hvB : v ∈ B := by rw [← ctx.hU]; exact Finset.mem_inter.2 ⟨hv, hPBsub h⟩
      exact PA_cross ctx hi' hj' _ _ v hvB h
  have hToB : ∀ v ∈ Ub, v ∈ T'.verts → v ∈ PA nB kBT j' (decide (j ≠ j')) := by
    intro v hv hvT
    rcases (hV' v).1 hvT with h | h
    · have hvB : v ∈ B := by rw [← ctx.hU]; exact Finset.mem_inter.2 ⟨hPAsub h, hv⟩
      exact PB_cross ctx hi' hj' _ _ v hvB h
    · exact h
  have hconn : (RT.node (cbag nA i ∪ cbag nB j)
      ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ [T'])).Conn := by
    apply conn_merged_node (B := B) (Ua := Ua) (Ub := Ub) (S := S) ctx.hU hXA hXB hAB hBB
    · exact fun J hJ => hAc J (hcisub.subset hJ)
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).1
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).2
    · exact fun J hJ => hAr J (List.mem_append_left _ (hcisub.subset hJ))
    · exact List.Pairwise.sublist hcisub (List.pairwise_append.1 hAp).1
    · exact fun J hJ => hBc J (hcjsub.subset hJ)
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).1
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).2
    · exact fun J hJ => hBr J (List.mem_append_left _ (hcjsub.subset hJ))
    · exact List.Pairwise.sublist hcjsub (List.pairwise_append.1 hBp).1
    · intro K hK; rw [List.mem_singleton] at hK; subst hK; exact hC'
    · intro K hK v hv hvK
      rw [List.mem_singleton] at hK; subst hK
      have := hSA1 v hv (hToA v (hXA hv) hvK)
      rw [hR']; exact Finset.mem_union_left _ this
    · intro K hK v hv hvK
      rw [List.mem_singleton] at hK; subst hK
      have := hSB1 v hv (hToB v (hXB hv) hvK)
      rw [hR']; exact Finset.mem_union_right _ this
    · intro J hJ K hK v hvJ hvK
      rw [List.mem_singleton] at hK; subst hK
      have hJ' := hcisub.subset hJ
      exact hSA2 J hJ' v hvJ (hToA v ((hjA J hJ').1 hvJ) hvK)
    · intro J hJ K hK v hvJ hvK
      rw [List.mem_singleton] at hK; subst hK
      have hJ' := hcjsub.subset hJ
      exact hSB2 J hJ' v hvJ (hToB v ((hjB J hJ').1 hvJ) hvK)
    · exact List.pairwise_singleton _ _
  refine ⟨hconn, rfl, ?_, ?_, ?_⟩
  · intro x
    rw [RT.verts_node, ← mem_vertsL, mem_vertsL_append, mem_vertsL_append, mem_vertsL_ite, mem_vertsL_ite,
      PA_step hi' hAi b1, PA_step hj' hBj b2]
    simp only [mem_vertsL, List.mem_singleton, exists_eq_left, Finset.mem_union, mem_ite_empty]
    rw [hV' x]
    exact logic_step _ _ _ _ _ _
  · intro X hX
    rcases hX with hX | ⟨hb1, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_left
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb1, if_true, List.mem_append]
      exact Or.inl (Or.inl hJ)
    · obtain ⟨Y, hY, hXY⟩ := hCA' X (side_bags hi hi' hAi K hK X hX)
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨T', by simp, hY⟩), hXY⟩
  · intro X hX
    rcases hX with hX | ⟨hb2, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_right
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb2, if_true, List.mem_append]
      exact Or.inl (Or.inr hJ)
    · obtain ⟨Y, hY, hXY⟩ := hCB' X (side_bags hj hj' hBj K hK X hX)
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨T', by simp, hY⟩), hXY⟩

/-! ## the induction along the path -/

def nw1 (prev : Option (ℕ × ℕ)) (i : ℕ) : Bool := prev.elim true (fun p => decide (p.1 ≠ i))
def nw2 (prev : Option (ℕ × ℕ)) (j : ℕ) : Bool := prev.elim true (fun p => decide (p.2 ≠ j))

theorem mergeChain_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (rest : List (ℕ × ℕ)) :
    mergeChain na nb prev ((i, j) :: rest) =
      ⟨cbag na i ∪ cbag nb j, (if nw1 prev i = true then cjunk na i else []) ++
        (if nw2 prev j = true then cjunk nb j else [])⟩ :: mergeChain na nb (some (i, j)) rest := rfl

theorem chainToRT_merge_last (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (K : List RT) :
    AR.chainToRT (mergeChain na nb prev [(i, j)]) K =
      RT.node (cbag na i ∪ cbag nb j)
        ((if nw1 prev i = true then cjunk na i else []) ++ (if nw2 prev j = true then cjunk nb j else []) ++ K) := by
  rw [mergeChain_cons]
  rfl

theorem chainToRT_merge_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j i' j' : ℕ)
    (rest : List (ℕ × ℕ)) (K : List RT) :
    AR.chainToRT (mergeChain na nb prev ((i, j) :: (i', j') :: rest)) K =
      RT.node (cbag na i ∪ cbag nb j)
        ((if nw1 prev i = true then cjunk na i else []) ++ (if nw2 prev j = true then cjunk nb j else []) ++
          [AR.chainToRT (mergeChain na nb (some (i, j)) ((i', j') :: rest)) K]) := by
  rw [mergeChain_cons na nb prev i j ((i', j') :: rest), mergeChain_cons na nb (some (i, j)) i' j' rest]
  rfl

theorem chain_claim {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) :
    ∀ (Q : List (ℕ × ℕ)) (i j : ℕ) (prev : Option (ℕ × ℕ)),
      Q.head? = some (i, j) → Q.getLast? = some (nA.length - 1, nB.length - 1) → Q.IsChain LStep →
      (∀ p, prev = some p → LStep p (i, j)) → i < nA.length → j < nB.length →
      ∀ T, T = AR.chainToRT (mergeChain nA nB prev Q) kMT →
        T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
        (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i (nw1 prev i) ∨ x ∈ PA nB kBT j (nw2 prev j)) ∧
        (∀ X, (X = cbag nA i ∨ (nw1 prev i = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨
          ∃ K ∈ succL nA kAT i, X ∈ K.bags) → ∃ Y ∈ T.bags, X ⊆ Y) ∧
        (∀ X, (X = cbag nB j ∨ (nw2 prev j = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨
          ∃ K ∈ succL nB kBT j, X ∈ K.bags) → ∃ Y ∈ T.bags, X ⊆ Y) := by
  intro Q
  induction Q with
  | nil => intro i j prev h; simp at h
  | cons q rest ih =>
    intro i j prev hh hl hc hp hi hj T hT
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at hl
      rw [chainToRT_merge_last] at hT
      exact claim_last ctx hi hj (by omega) (by omega) _ _ hT
    | cons q' rest' =>
      obtain ⟨i', j'⟩ := q'
      rw [List.isChain_cons_cons] at hc
      rw [List.getLast?_cons_cons] at hl
      have hlast := chain_le_last rest' (i', j') hc.2 _ (by rw [hl]; rfl)
      simp only at hlast
      have hi' : i' < nA.length := by omega
      have hj' : j' < nB.length := by omega
      rw [chainToRT_merge_cons] at hT
      have IH := ih i' j' (some (i, j)) rfl hl hc.2 (by intro p hp; simp only [Option.some.injEq] at hp; subst hp; exact hc.1)
        hi' hj' _ rfl
      obtain ⟨hC', hR', hV', hCA', hCB'⟩ := IH
      have e1 : nw1 (some (i, j)) i' = decide (i ≠ i') := rfl
      have e2 : nw2 (some (i, j)) j' = decide (j ≠ j') := rfl
      rw [e1, e2] at hV'
      rw [e1] at hCA'
      rw [e2] at hCB'
      exact claim_step ctx hi hj hi' hj' hc.1 _ _ hC' hR' hV' hCA' hCB' hT

end Lax117284Proofs.Treewidth.Chars
