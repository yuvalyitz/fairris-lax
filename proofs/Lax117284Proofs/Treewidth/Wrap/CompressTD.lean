import Lax117284Proofs.Treewidth.Wrap.CompressDefs

/-!
# `compress` preserves tree decompositions and widths, and produces a compressed, connected tree (WP P0)

* `verts_compress`, `bags_compress_sub`, `bags_compress_cover` : vertex set unchanged, bags only lose,
  every lost bag was inside a surviving one;
* `compress_conn_comp` : `t.Conn → (compress t).Conn ∧ Comp (compress t)`;
* `compress_isTD`, `compress_width`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

theorem verts_compress : ∀ t : RT, (compress t).verts = t.verts := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    ext x
    rw [compress_node, verts_node, verts_node, mem_verts_flat]
    simp only [List.mem_map, exists_exists_and_eq_and]
    constructor
    · rintro (h | ⟨k, hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, by rwa [← ih k hk]⟩
    · rintro (h | ⟨k, hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, by rwa [ih k hk]⟩

theorem bags_compress_sub : ∀ t : RT, ∀ B ∈ (compress t).bags, B ∈ t.bags := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro B hB
    rw [compress_node, bags_node] at hB
    rw [bags_node]
    rcases hB with rfl | ⟨e, he, hBe⟩
    · exact Or.inl rfl
    · have := bagsL_flat_sub X (ks.map compress) B ((mem_bagsL_iff _ _).2 ⟨e, he, hBe⟩)
      rw [mem_bagsL_iff] at this
      obtain ⟨c, hc, hBc⟩ := this
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
      exact Or.inr ⟨k, hk, ih k hk B hBc⟩

theorem bags_compress_cover : ∀ t : RT, ∀ B ∈ t.bags, ∃ B' ∈ (compress t).bags, B ⊆ B' := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro B hB
    rw [bags_node] at hB
    rcases hB with rfl | ⟨k, hk, hBk⟩
    · exact ⟨B, by rw [compress_node, bags_node]; exact Or.inl rfl, subset_rfl⟩
    · obtain ⟨B', hB', hBB'⟩ := ih k hk B hBk
      have h1 : B' ∈ bagsL (ks.map compress) :=
        (mem_bagsL_iff _ _).2 ⟨compress k, List.mem_map_of_mem hk, hB'⟩
      rcases mem_bagsL_flat X (ks.map compress) B' h1 with h | h
      · exact ⟨X, by rw [compress_node, bags_node]; exact Or.inl rfl, hBB'.trans h⟩
      · exact ⟨B', by rw [compress_node, bags_node]; exact Or.inr ((mem_bagsL_iff _ _).1 h), hBB'⟩

/-! ### connectedness and compressedness -/

/-- The `X`-level clauses of `Conn`, for a list of kids. -/
def Lvl (X : Finset ℕ) (L : List RT) : Prop :=
  (∀ k ∈ L, ∀ v ∈ X, v ∈ verts k → v ∈ rootBag k) ∧
    L.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ X)

theorem flat_verts_sub (X : Finset ℕ) (L : List RT) :
    ∀ e ∈ flatKids X L, ∃ c ∈ L, e.verts ⊆ c.verts := by
  intro e he
  obtain ⟨Y, ls, h1, h2⟩ := (mem_flatKids_iff X L e).1 he
  refine ⟨_, h1, ?_⟩
  rcases h2 with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact subset_rfl
  · exact sub_verts h

theorem flat_pairwise (X : Finset ℕ) : ∀ L : List RT, (∀ c ∈ L, Conn c) →
    L.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ X) →
    (flatKids X L).Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ X)
  | [], _, _ => by simp [flatKids]
  | .node Y ls :: rest, hconn, hp => by
    rw [List.pairwise_cons] at hp
    have hconn' : ∀ c ∈ rest, Conn c := fun c hc => hconn c (List.mem_cons_of_mem _ hc)
    have ih := flat_pairwise X rest hconn' hp.2
    have hc := (conn_node_iff Y ls).1 (hconn _ (List.mem_cons_self))
    have cross : ∀ (a : RT), (∃ c ∈ (RT.node Y ls :: rest), a.verts ⊆ c.verts) → ∀ b ∈ flatKids X rest,
        (RT.node Y ls).verts ⊆ (RT.node Y ls).verts → a.verts ⊆ (RT.node Y ls).verts →
        ∀ v, v ∈ verts a → v ∈ verts b → v ∈ X := by
      intro a _ b hb _ hav v hva hvb
      obtain ⟨c', hc', hbc⟩ := flat_verts_sub X rest b hb
      exact hp.1 c' hc' v (hav hva) (hbc hvb)
    rw [flatKids]
    by_cases hY : Y ⊆ X
    · rw [if_pos hY, List.pairwise_append]
      refine ⟨hc.2.2.imp (fun h v h1 h2 => hY (h v h1 h2)), ih, ?_⟩
      intro a ha b hb
      exact cross a ⟨_, List.mem_cons_self, sub_verts ha⟩ b hb subset_rfl (sub_verts ha)
    · rw [if_neg hY, List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro b hb
      exact cross _ ⟨_, List.mem_cons_self, subset_rfl⟩ b hb subset_rfl subset_rfl

theorem flat_conn_comp (X : Finset ℕ) (L : List RT) (hL : ∀ c ∈ L, Conn c ∧ Comp c) (hlv : Lvl X L) :
    Conn (.node X (flatKids X L)) ∧ Comp (.node X (flatKids X L)) := by
  obtain ⟨hC2, hC3⟩ := hlv
  have hE : ∀ e ∈ flatKids X L, Conn e ∧ Comp e ∧ ¬ e.rootBag ⊆ X ∧
      (∀ v ∈ X, v ∈ verts e → v ∈ rootBag e) := by
    intro e he
    obtain ⟨Y, ls, h1, h2⟩ := (mem_flatKids_iff X L e).1 he
    obtain ⟨hc, hcomp⟩ := hL _ h1
    have hc' := (conn_node_iff Y ls).1 hc
    have hcomp' := (comp_node_iff Y ls).1 hcomp
    rcases h2 with ⟨hY, rfl⟩ | ⟨hY, h⟩
    · exact ⟨hc, hcomp, hY, hC2 _ h1⟩
    · obtain ⟨hck, hcomp2⟩ := hcomp' e h
      have hev : e.verts ⊆ (RT.node Y ls).verts := sub_verts h
      have hin : ∀ v ∈ X, v ∈ e.verts → v ∈ Y := fun v hv hve => hC2 _ h1 v hv (hev hve)
      refine ⟨hc'.1 e h, hcomp2, fun hs => hck fun v hv => hin v (hs hv) (rootBag_sub_verts e hv),
        fun v hv hve => hc'.2.1 e h v (hin v hv hve) hve⟩
  rw [conn_node_iff, comp_node_iff]
  refine ⟨⟨fun e he => (hE e he).1, fun e he => (hE e he).2.2.2,
    flat_pairwise X L (fun c hc => (hL c hc).1) hC3⟩, fun e he => ⟨(hE e he).2.2.1, (hE e he).2.1⟩⟩

theorem compress_conn_comp : ∀ t : RT, Conn t → Conn (compress t) ∧ Comp (compress t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := (conn_node_iff X ks).1 h
    rw [compress_node]
    apply flat_conn_comp
    · intro c hc
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
      exact ih k hk (h1 k hk)
    · refine ⟨?_, ?_⟩
      · intro c hc v hv hvc
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hc
        rw [verts_compress] at hvc
        rw [rootBag_compress]
        exact h2 k hk v hv hvc
      · rw [List.pairwise_map]
        exact h3.imp (fun h v hv1 hv2 => h v (by rwa [verts_compress] at hv1) (by rwa [verts_compress] at hv2))
end RT

end Lax117284Proofs.Treewidth.Trees
