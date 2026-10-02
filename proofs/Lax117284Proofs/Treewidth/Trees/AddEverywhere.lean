import Lax117284Proofs.Treewidth.Trees.NiceLemmas

/-!
# Adding a vertex to every bag of a nice tree (T2, BP2 part 1)

`NT.addEverywhere v` puts an introduce node above every leaf.  Everything is proved by induction on `NT`,
through the local characterisation of `RT.Conn` (`NT.NConn`).

Statement audit note: BP2 states `bag_addEverywhere` without hypotheses.  That is false (`t = forget v (intro v leaf)`);
the correct hypotheses are `t.Wf` and `v ∉ t.vs` (`v` occurs nowhere), which is what `addEverywhere_isNiceTD` has.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace NT

lemma not_mem_vs_intro {v u : ℕ} {c : NT} (h : v ∉ vs (intro u c)) : v ∉ vs c ∧ v ≠ u := by
  simp only [vs_intro, Finset.mem_union, not_or, bag_intro, Finset.mem_insert] at h
  tauto

lemma not_mem_vs_forget {v u : ℕ} {c : NT} (h : v ∉ vs (forget u c)) : v ∉ vs c := by
  simp only [vs_forget, Finset.mem_union, not_or] at h
  exact h.2

lemma not_mem_vs_join {v : ℕ} {a b : NT} (h : v ∉ vs (join a b)) : v ∉ vs a ∧ v ∉ vs b := by
  simp only [vs_join, Finset.mem_union, not_or] at h
  exact ⟨h.2.1, h.2.2⟩

/-- The bag of the root after adding `v` everywhere. -/
theorem bag_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) :
    (addEverywhere v t).bag = insert v t.bag := by
  induction t with
  | leaf => simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp [addEverywhere, ih hc hv', Finset.insert_comm u v]
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bag_forget, ih hc hv']
    exact Finset.erase_insert_of_ne this
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp [addEverywhere, ih₁ ha hva]

theorem size_addEverywhere_le (v : ℕ) (t : NT) : (addEverywhere v t).size ≤ 2 * t.size := by
  induction t with
  | leaf => simp [addEverywhere, size]
  | intro u c ih => simp only [addEverywhere, size]; omega
  | forget u c ih => simp only [addEverywhere, size]; omega
  | join a b ih₁ ih₂ => simp only [addEverywhere, size]; omega

theorem wf_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) : (addEverywhere v t).Wf := by
  induction t with
  | leaf => simp [addEverywhere, Wf]
  | intro u c ih =>
    obtain ⟨hu, hc⟩ := hw
    obtain ⟨hv', hne⟩ := not_mem_vs_intro hv
    refine ⟨?_, ih hc hv'⟩
    rw [bag_addEverywhere v c hc hv']
    simp [Ne.symm hne, hu]
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    refine ⟨?_, ih hc hv'⟩
    rw [bag_addEverywhere v c hc hv']
    exact Finset.mem_insert_of_mem hu
  | join a b ih₁ ih₂ =>
    obtain ⟨hab, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    refine ⟨?_, ih₁ ha hva, ih₂ hb hvb⟩
    rw [bag_addEverywhere v a ha hva, bag_addEverywhere v b hb hvb, hab]

theorem vs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) :
    (addEverywhere v t).vs = insert v t.vs := by
  induction t with
  | leaf => simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, vs_intro, bag_intro]
    rw [bag_addEverywhere v c hc hv', ih hc hv']
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  | forget u c ih =>
    obtain ⟨-, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    simp only [addEverywhere, vs_forget, bag_forget]
    rw [bag_addEverywhere v c hc hv', ih hc hv']
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]; tauto
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, vs_join]
    rw [bag_addEverywhere v a ha hva, ih₁ ha hva, ih₂ hb hvb]
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto

/-- Every bag of the new tree is `∅` (a new leaf) or an old bag plus `v`. -/
theorem mem_bs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) {X : Finset ℕ}
    (hX : X ∈ bs (addEverywhere v t)) : X = ∅ ∨ ∃ Y ∈ bs t, X = insert v Y := by
  induction t with
  | leaf =>
    simp only [addEverywhere, bs_intro, bs_leaf, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · right; exact ⟨∅, by simp, by simp⟩
    · left; rfl
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, bs_intro, List.mem_cons] at hX
    rcases hX with hX | hX
    · right
      refine ⟨(intro u c).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_intro, bag_intro, bag_addEverywhere v c hc hv']; simp [Finset.insert_comm u v]
    · rcases ih hc hv' hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have hne : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bs_forget, List.mem_cons] at hX
    rcases hX with hX | hX
    · right
      refine ⟨(forget u c).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_forget, bag_forget, bag_addEverywhere v c hc hv']; simp [Finset.erase_insert_of_ne hne]
    · rcases ih hc hv' hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, bs_join, List.mem_cons, List.mem_append] at hX
    rcases hX with hX | hX | hX
    · right
      refine ⟨(join a b).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_join, bag_addEverywhere v a ha hva]
    · rcases ih₁ ha hva hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
    · rcases ih₂ hb hvb hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩

/-- Every old bag plus `v` is a bag of the new tree. -/
theorem insert_mem_bs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) {Y : Finset ℕ}
    (hY : Y ∈ bs t) : insert v Y ∈ bs (addEverywhere v t) := by
  induction t with
  | leaf =>
    simp only [bs_leaf, List.mem_singleton] at hY
    subst hY
    simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, bs_intro, List.mem_cons] at hY ⊢
    rcases hY with hY | hY
    · left; rw [hY, bag_intro, bag_intro, bag_addEverywhere v c hc hv']; simp [Finset.insert_comm u v]
    · exact Or.inr (ih hc hv' hY)
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have hne : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bs_forget, List.mem_cons] at hY ⊢
    rcases hY with hY | hY
    · left; rw [hY, bag_forget, bag_forget, bag_addEverywhere v c hc hv']; simp [Finset.erase_insert_of_ne hne]
    · exact Or.inr (ih hc hv' hY)
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, bs_join, List.mem_cons, List.mem_append] at hY ⊢
    rcases hY with hY | hY | hY
    · left; rw [hY, bag_addEverywhere v a ha hva]
    · exact Or.inr (Or.inl (ih₁ ha hva hY))
    · exact Or.inr (Or.inr (ih₂ hb hvb hY))

theorem nconn_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) (hn : NConn t) :
    NConn (addEverywhere v t) := by
  induction t with
  | leaf => simp [addEverywhere, NConn]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    obtain ⟨hu, hnc⟩ := hn
    refine ⟨?_, ih hc hv' hnc⟩
    rw [vs_addEverywhere v c hc hv']
    have hne : u ≠ v := by
      intro h; subst h
      exact hv (by simp)
    simp [hne, hu]
  | forget u c ih =>
    obtain ⟨-, hc⟩ := hw
    exact ih hc (not_mem_vs_forget hv) hn
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    obtain ⟨hj, hna, hnb⟩ := hn
    refine ⟨?_, ih₁ ha hva hna, ih₂ hb hvb hnb⟩
    intro x hxa hxb
    rw [vs_addEverywhere v a ha hva] at hxa
    rw [vs_addEverywhere v b hb hvb] at hxb
    rw [bag_addEverywhere v a ha hva]
    rcases Finset.mem_insert.1 hxa with rfl | hxa
    · simp
    · rcases Finset.mem_insert.1 hxb with rfl | hxb
      · simp
      · exact Finset.mem_insert_of_mem (hj x hxa hxb)

/-- **The wrapper's step.**  Adding `v` (with arbitrary neighbours among the existing vertices `U`) to every bag of a
nice decomposition of `G[U]` of width `≤ k` gives a nice decomposition of `G[U ∪ {v}]` of width `≤ k + 1`. -/
theorem addEverywhere_isNiceTD {G : SimpleGraph ℕ} {U : Finset ℕ} {t : NT} {k v : ℕ}
    (h : t.IsNiceTD G U k) (hv : v ∉ U) :
    (addEverywhere v t).IsNiceTD G (insert v U) (k + 1) := by
  obtain ⟨hw, hTD, hwd⟩ := h
  have hU : t.vs = U := hTD.verts_eq
  have hv' : v ∉ t.vs := hU ▸ hv
  refine ⟨wf_addEverywhere v t hw hv', ⟨?_, ?_, ?_⟩, ?_⟩
  · show (addEverywhere v t).vs = _
    rw [vs_addEverywhere v t hw hv', hU]
  · intro a b hab ha hb
    have inU : ∀ x, x ∈ U → ∃ X ∈ bs t, x ∈ X := fun x hx => (mem_vs_iff t x).1 (hU ▸ hx)
    rcases Finset.mem_insert.1 ha with h1 | ha'
    · rcases Finset.mem_insert.1 hb with h2 | hb'
      · exact absurd (h1.trans h2.symm ▸ hab) (G.loopless.irrefl _)
      · obtain ⟨X, hX, hbX⟩ := inU b hb'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, h1 ▸ Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem hbX⟩
    · rcases Finset.mem_insert.1 hb with h2 | hb'
      · obtain ⟨X, hX, haX⟩ := inU a ha'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, Finset.mem_insert_of_mem haX,
          h2 ▸ Finset.mem_insert_self _ _⟩
      · obtain ⟨X, hX, haX, hbX⟩ := hTD.edges a b hab ha' hb'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, Finset.mem_insert_of_mem haX,
          Finset.mem_insert_of_mem hbX⟩
  · exact (conn_toRT_iff (wf_addEverywhere v t hw hv')).2
      (nconn_addEverywhere v t hw hv' ((conn_toRT_iff hw).1 hTD.conn))
  · intro X hX
    rcases mem_bs_addEverywhere v t hw hv' hX with rfl | ⟨Y, hY, rfl⟩
    · simp
    · have hYU : Y ⊆ U := hU ▸ vs_subset_of_mem_bs hY
      have hvY : v ∉ Y := fun h => hv (hYU h)
      rw [Finset.card_insert_of_notMem hvY]
      have := hwd Y hY
      omega

end NT

end Lax117284Proofs.Treewidth.Trees
