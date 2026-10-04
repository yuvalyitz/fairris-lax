import Lax117284Proofs.Treewidth.Trees.Bridge1Rt
import Lax117284Proofs.Treewidth.Wrap.NiceSize
import Lax117284Proofs.Treewidth.Wrap.NiceSizeConn

/-! ### `Lax117284Proofs.Treewidth.Wrap.CompressDefs` -/

section
/-!
# `compress` (work package P0): definitions and the two structural facts about `flatKids`

`compress t` dissolves every kid whose bag is contained in its parent's bag, moving its kids up (bottom-up).
It is the missing step between `extract` and `niceOf` that keeps the nice trees of the wrapper polynomial
(without it the nice tree grows by a factor ~2.2 per round; see `PLAN-machine.md` §0).

* `flatKids X L` : the kids `L`, with each kid whose root bag is `⊆ X` replaced by its kids;
* `compress`     : `node X ks ↦ node X (flatKids X (compress ks))`;
* `Comp t`       : *compressedness*, no non-root node has its bag inside its parent's bag.
-/

namespace Lax117284Proofs.Treewidth.Trees

/-- Dissolve the kids whose bag is inside the parent's bag (their kids move up). -/
def flatKids (X : Finset ℕ) : List RT → List RT
  | [] => []
  | .node Y ls :: rest => if Y ⊆ X then ls ++ flatKids X rest else .node Y ls :: flatKids X rest

mutual
/-- Dissolve, bottom-up, every node whose bag is contained in its parent's bag. -/
def compress : RT → RT
  | .node X ks => .node X (flatKids X (compressL ks))
def compressL : List RT → List RT
  | [] => []
  | k :: ks => compress k :: compressL ks
end

mutual
/-- *Compressed*: no kid's bag is contained in its parent's bag, recursively. -/
def Comp : RT → Prop
  | .node X ks => CompL X ks
def CompL (X : Finset ℕ) : List RT → Prop
  | [] => True
  | k :: ks => ¬ k.rootBag ⊆ X ∧ Comp k ∧ CompL X ks
end

namespace RT

theorem compressL_eq : ∀ ks : List RT, compressL ks = ks.map compress
  | [] => rfl
  | k :: ks => by simp [compressL, compressL_eq ks]

theorem compL_iff (X : Finset ℕ) : ∀ ks : List RT, CompL X ks ↔ ∀ k ∈ ks, ¬ k.rootBag ⊆ X ∧ Comp k
  | [] => by simp [CompL]
  | k :: ks => by
    simp only [CompL, List.mem_cons, forall_eq_or_imp]
    rw [compL_iff X ks, and_assoc]

theorem comp_node_iff (X : Finset ℕ) (ks : List RT) :
    Comp (.node X ks) ↔ ∀ k ∈ ks, ¬ k.rootBag ⊆ X ∧ Comp k := by
  rw [Comp, compL_iff]

theorem compress_node (X : Finset ℕ) (ks : List RT) :
    compress (.node X ks) = .node X (flatKids X (ks.map compress)) := by
  rw [compress, compressL_eq]

theorem rootBag_compress (t : RT) : (compress t).rootBag = t.rootBag := by
  cases t; simp [compress, rootBag]

/-- Membership in `flatKids`. -/
theorem mem_flatKids_iff (X : Finset ℕ) : ∀ (L : List RT) (e : RT), e ∈ flatKids X L ↔
    ∃ Y ls, RT.node Y ls ∈ L ∧ ((¬ Y ⊆ X ∧ e = .node Y ls) ∨ (Y ⊆ X ∧ e ∈ ls))
  | [], e => by simp [flatKids]
  | .node Y ls :: rest, e => by
    rw [flatKids]
    by_cases hY : Y ⊆ X
    · simp only [hY, if_true, List.mem_append, mem_flatKids_iff X rest e, List.mem_cons]
      constructor
      · rintro (h | ⟨Y', ls', h1, h2⟩)
        · exact ⟨Y, ls, Or.inl rfl, Or.inr ⟨hY, h⟩⟩
        · exact ⟨Y', ls', Or.inr h1, h2⟩
      · rintro ⟨Y', ls', h1 | h1, h2⟩
        · cases h1
          rcases h2 with ⟨h, _⟩ | ⟨_, h⟩
          · exact absurd hY h
          · exact Or.inl h
        · exact Or.inr ⟨Y', ls', h1, h2⟩
    · simp only [hY, if_false, List.mem_cons, mem_flatKids_iff X rest e]
      constructor
      · rintro (h | ⟨Y', ls', h1, h2⟩)
        · exact ⟨Y, ls, Or.inl rfl, Or.inl ⟨hY, h⟩⟩
        · exact ⟨Y', ls', Or.inr h1, h2⟩
      · rintro ⟨Y', ls', h1 | h1, h2⟩
        · cases h1
          rcases h2 with ⟨_, h⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exact absurd h hY
        · exact Or.inr ⟨Y', ls', h1, h2⟩

/-- Every vertex of `X ∪ (kids)` survives `flatKids` (dissolved bags are inside `X`). -/
theorem mem_verts_flat (X : Finset ℕ) (L : List RT) (x : ℕ) :
    (x ∈ X ∨ ∃ e ∈ flatKids X L, x ∈ e.verts) ↔ (x ∈ X ∨ ∃ k ∈ L, x ∈ k.verts) := by
  simp only [mem_flatKids_iff]
  constructor
  · rintro (h | ⟨e, ⟨Y, ls, h1, h2⟩, hx⟩)
    · exact Or.inl h
    · rcases h2 with ⟨_, rfl⟩ | ⟨_, h⟩
      · exact Or.inr ⟨_, h1, hx⟩
      · exact Or.inr ⟨_, h1, (verts_node Y ls).2 (Or.inr ⟨e, h, hx⟩)⟩
  · rintro (h | ⟨k, hk, hx⟩)
    · exact Or.inl h
    · obtain ⟨Y, ls⟩ := k
      by_cases hY : Y ⊆ X
      · rcases (verts_node Y ls).1 hx with h | ⟨e, he, hxe⟩
        · exact Or.inl (hY h)
        · exact Or.inr ⟨e, ⟨Y, ls, hk, Or.inr ⟨hY, he⟩⟩, hxe⟩
      · exact Or.inr ⟨_, ⟨Y, ls, hk, Or.inl ⟨hY, rfl⟩⟩, hx⟩

/-- Bags of the flattened list: contained in those of the original, and every original bag is inside `X`
or survives. -/
theorem bagsL_flat_sub (X : Finset ℕ) (L : List RT) (B : Finset ℕ) :
    B ∈ bagsL (flatKids X L) → B ∈ bagsL L := by
  simp only [mem_bagsL_iff, mem_flatKids_iff]
  rintro ⟨e, ⟨Y, ls, h1, h2⟩, hB⟩
  rcases h2 with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact ⟨_, h1, hB⟩
  · exact ⟨_, h1, (bags_node Y ls).2 (Or.inr ⟨e, h, hB⟩)⟩

theorem mem_bagsL_flat (X : Finset ℕ) (L : List RT) (B : Finset ℕ) :
    B ∈ bagsL L → B ⊆ X ∨ B ∈ bagsL (flatKids X L) := by
  simp only [mem_bagsL_iff, mem_flatKids_iff]
  rintro ⟨k, hk, hB⟩
  obtain ⟨Y, ls⟩ := k
  by_cases hY : Y ⊆ X
  · rcases (bags_node Y ls).1 hB with rfl | ⟨e, he, hBe⟩
    · exact Or.inl hY
    · exact Or.inr ⟨e, ⟨Y, ls, hk, Or.inr ⟨hY, he⟩⟩, hBe⟩
  · exact Or.inr ⟨_, ⟨Y, ls, hk, Or.inl ⟨hY, rfl⟩⟩, hB⟩

end RT

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Wrap.CompressTD` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Wrap.CompressSize` -/

section
/-!
# `compress`: the decomposition facts and the size bound (WP P0)

* `compress_isTD`, `compress_width` ;
* `size_le_of_comp` : a connected, compressed tree has at most `1 + |V \ root bag|` nodes (every non-root node owns
  the vertices of its bag that are not in its parent's bag; connectedness makes these sets disjoint);
* `compress_size_le` : `(compress t).size ≤ |V(t)| + 1` for a connected `t`.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Chars

theorem compress_isTD {G : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : t.IsTD G U) : (compress t).IsTD G U := by
  refine ⟨by rw [RT.verts_compress]; exact h.verts_eq, ?_, (RT.compress_conn_comp t h.conn).1⟩
  intro u v huv hu hv
  obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hu hv
  obtain ⟨X', hX', hXX'⟩ := RT.bags_compress_cover t X hX
  exact ⟨X', hX', hXX' hxu, hXX' hxv⟩

theorem compress_width {t : RT} {w : ℕ} (h : t.Width w) : (compress t).Width w :=
  fun X hX => h X (RT.bags_compress_sub t X hX)

namespace RT

theorem size_le_of_comp : ∀ t : RT, Conn t → Comp t → t.size ≤ 1 + (t.verts \ t.rootBag).card := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc hcomp
    obtain ⟨h1, h2, h3⟩ := (conn_node_iff X ks).1 hc
    have hk := (comp_node_iff X ks).1 hcomp
    have hkid : ∀ k ∈ ks, k.size ≤ (k.verts \ X).card := by
      intro k hk'
      obtain ⟨hnot, hcompk⟩ := hk k hk'
      have i1 := ih k hk' (h1 k hk') hcompk
      have i2 := conn_kid_card (rootBag_sub_verts k) (h2 k hk')
      have i3 : 0 < (k.rootBag \ X).card := by
        apply Finset.card_pos.2
        by_contra hne
        exact hnot (Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hne))
      omega
    have hsum : (ks.map (fun k => (k.verts \ X).card)).sum ≤ ((RT.node X ks).verts \ X).card := by
      apply sum_card_le ks h3
      intro k hk' v hv
      have := Finset.mem_sdiff.1 hv
      exact Finset.mem_sdiff.2 ⟨sub_verts hk' this.1, this.2⟩
    have hle : (ks.map size).sum ≤ (ks.map (fun k => (k.verts \ X).card)).sum :=
      List.sum_le_sum (fun k hk' => by simpa using hkid k (by simpa using hk'))
    rw [size_node]
    simp only [rootBag]
    omega

end RT

theorem compress_size_le {t : RT} (h : t.Conn) : (compress t).size ≤ t.verts.card + 1 := by
  obtain ⟨hc, hcomp⟩ := RT.compress_conn_comp t h
  have := RT.size_le_of_comp _ hc hcomp
  rw [RT.verts_compress] at this
  have h2 := Finset.card_le_card (Finset.sdiff_subset (s := t.verts) (t := (compress t).rootBag))
  omega

end Lax117284Proofs.Treewidth.Trees

end
