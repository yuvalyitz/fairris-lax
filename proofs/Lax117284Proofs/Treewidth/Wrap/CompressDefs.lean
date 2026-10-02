import Lax117284Proofs.Treewidth.Trees.Bridge1Rt
import Lax117284Proofs.Treewidth.Wrap.NiceSize

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
