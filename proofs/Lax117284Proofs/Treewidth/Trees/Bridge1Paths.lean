import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt

/-!
# Nodes of an `RT` as paths

`paths t` is the (finite) set of paths (child indices from the root) of an `RT`; `bagAt t p` the bag at a path.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
/-- The set of nodes of the tree, as paths of child indices. -/
def paths : RT → Finset (List ℕ)
  | .node _ ks => insert [] (pathsL ks 0)
/-- Paths into a list of trees whose first index is `j`. -/
def pathsL : List RT → ℕ → Finset (List ℕ)
  | [], _ => ∅
  | k :: ks, j => (paths k).image (List.cons j) ∪ pathsL ks (j + 1)
end

mutual
/-- The bag at a path (empty for a non-path). -/
def bagAt : RT → List ℕ → Finset ℕ
  | .node b _, [] => b
  | .node _ ks, i :: p => bagAtL ks i p
/-- The bag below the `i`-th tree of the list. -/
def bagAtL : List RT → ℕ → List ℕ → Finset ℕ
  | [], _, _ => ∅
  | k :: _, 0, p => bagAt k p
  | _ :: ks, i + 1, p => bagAtL ks i p
end

theorem mem_pathsL (ks : List RT) (j : ℕ) (q : List ℕ) :
    q ∈ pathsL ks j ↔ ∃ i k q', ks[i]? = some k ∧ q' ∈ paths k ∧ q = (j + i) :: q' := by
  induction ks generalizing j with
  | nil => simp [pathsL]
  | cons k ks ih =>
    simp only [pathsL, Finset.mem_union, Finset.mem_image, ih]
    constructor
    · rintro (⟨q', hq', rfl⟩ | ⟨i, k', q', h1, h2, rfl⟩)
      · exact ⟨0, k, q', by simp, hq', by simp⟩
      · exact ⟨i + 1, k', q', by simpa using h1, h2, by congr 1; omega⟩
    · rintro ⟨i, k', q', h1, h2, rfl⟩
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        exact Or.inl ⟨q', h2, by simp⟩
      · simp only [List.getElem?_cons_succ] at h1
        exact Or.inr ⟨i, k', q', h1, h2, by congr 1; omega⟩

theorem mem_paths_node (b : Finset ℕ) (ks : List RT) (p : List ℕ) :
    p ∈ paths (.node b ks) ↔ p = [] ∨ ∃ i k q', ks[i]? = some k ∧ q' ∈ paths k ∧ p = i :: q' := by
  simp only [paths, Finset.mem_insert, mem_pathsL, zero_add]

theorem bagAtL_of_getElem? : ∀ (ks : List RT) (i : ℕ) (k : RT) (p : List ℕ),
    ks[i]? = some k → bagAtL ks i p = bagAt k p
  | [], i, k, p, h => by simp at h
  | k' :: ks, 0, k, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [bagAtL]
  | k' :: ks, i + 1, k, p, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [bagAtL, bagAtL_of_getElem? ks i k p h]

theorem bagAtL_of_getElem?_none : ∀ (ks : List RT) (i : ℕ) (p : List ℕ),
    ks[i]? = none → bagAtL ks i p = ∅
  | [], i, p, h => by cases i <;> simp [bagAtL]
  | k' :: ks, 0, p, h => by simp at h
  | k' :: ks, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [bagAtL, bagAtL_of_getElem?_none ks i p h]

theorem bagAt_nil (b : Finset ℕ) (ks : List RT) : bagAt (.node b ks) [] = b := by simp [bagAt]

theorem bagAt_cons (b : Finset ℕ) (ks : List RT) (i : ℕ) (k : RT) (p : List ℕ) (h : ks[i]? = some k) :
    bagAt (.node b ks) (i :: p) = bagAt k p := by
  simp only [bagAt]; exact bagAtL_of_getElem? ks i k p h

theorem nil_mem_paths (t : RT) : ([] : List ℕ) ∈ paths t := by
  cases t; simp [paths]

/-- Paths are closed under removing the last step. -/
theorem dropLast_mem_paths (t : RT) : ∀ p ∈ paths t, p.dropLast ∈ paths t := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro p hp
    rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
    · simpa using nil_mem_paths _
    · rcases q' with _ | ⟨a, q''⟩
      · simpa using nil_mem_paths _
      · have := ih k (List.mem_of_getElem? hk) _ hq'
        rw [List.dropLast_cons_of_ne_nil (by simp)]
        exact (mem_paths_node b ks _).2 (Or.inr ⟨i, k, _, hk, this, rfl⟩)

/-- Every bag of the tree is the bag at some path. -/
theorem exists_path_of_mem_bags (t : RT) : ∀ X ∈ t.bags, ∃ p ∈ paths t, bagAt t p = X := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro X hX
    rcases (bags_node b ks).1 hX with rfl | ⟨k, hk, hXk⟩
    · exact ⟨[], nil_mem_paths _, bagAt_nil _ _⟩
    · obtain ⟨p, hp, hpX⟩ := ih k hk X hXk
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
      exact ⟨i :: p, (mem_paths_node b ks _).2 (Or.inr ⟨i, k, p, hi, hp, rfl⟩),
        by rw [bagAt_cons b ks i k p hi, hpX]⟩

/-- The bag at any path is a bag of the tree. -/
theorem bagAt_mem_bags (t : RT) : ∀ p ∈ paths t, bagAt t p ∈ t.bags := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro p hp
    rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
    · rw [bagAt_nil]; exact (bags_node b ks).2 (Or.inl rfl)
    · rw [bagAt_cons b ks i k q' hk]
      exact (bags_node b ks).2 (Or.inr ⟨k, List.mem_of_getElem? hk, ih k (List.mem_of_getElem? hk) q' hq'⟩)

theorem bagAt_nil_eq (t : RT) : bagAt t [] = t.rootBag := by cases t; simp [bagAt, rootBag]

theorem mem_verts_of_bagAt {t : RT} {q : List ℕ} (hq : q ∈ paths t) {x : ℕ} (h : x ∈ bagAt t q) :
    x ∈ t.verts :=
  (mem_verts_iff _ _).2 ⟨_, bagAt_mem_bags t q hq, h⟩

/-- **Top of an occurrence set.**  In a tree with `Conn`, the paths whose bag contains `x` form a connected
set with a top element: all its other members have their parent in the set. -/
theorem top_exists : ∀ t : RT, t.Conn → ∀ x : ℕ, (∃ p ∈ paths t, x ∈ bagAt t p) →
    ∃ p₀ ∈ paths t, x ∈ bagAt t p₀ ∧
      ∀ q ∈ paths t, x ∈ bagAt t q → q ≠ p₀ → q ≠ [] ∧ x ∈ bagAt t q.dropLast := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro hc x hx
    obtain ⟨hks, h2, h3⟩ := (conn_node_iff b ks).1 hc
    by_cases hxb : x ∈ b
    · refine ⟨[], nil_mem_paths _, by rwa [bagAt_nil], ?_⟩
      intro q hq hxq hne
      rcases (mem_paths_node b ks q).1 hq with rfl | ⟨i, k, q', hk, hq', rfl⟩
      · exact absurd rfl hne
      · refine ⟨by simp, ?_⟩
        rw [bagAt_cons b ks i k q' hk] at hxq
        have hkm := List.mem_of_getElem? hk
        have hxv := mem_verts_of_bagAt hq' hxq
        have hroot := h2 k hkm x hxb hxv
        obtain ⟨p₀, hp₀, hxp₀, htop⟩ := ih k hkm (hks k hkm) x ⟨q', hq', hxq⟩
        have hp₀nil : p₀ = [] := by
          by_contra hne'
          have := (htop [] (nil_mem_paths k) (by rw [bagAt_nil_eq]; exact hroot) (Ne.symm hne')).1
          exact absurd rfl this
        subst hp₀nil
        rcases q' with _ | ⟨a, q''⟩
        · simpa [bagAt_nil] using hxb
        · have := (htop (a :: q'') hq' hxq (List.cons_ne_nil _ _)).2
          rw [List.dropLast_cons_of_ne_nil (by simp), bagAt_cons b ks i k _ hk]
          exact this
    · obtain ⟨p, hp, hxp⟩ := hx
      rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
      · rw [bagAt_nil] at hxp; exact absurd hxp hxb
      · rw [bagAt_cons b ks i k q' hk] at hxp
        have hkm := List.mem_of_getElem? hk
        obtain ⟨p₀, hp₀, hxp₀, htop⟩ := ih k hkm (hks k hkm) x ⟨q', hq', hxp⟩
        refine ⟨i :: p₀, (mem_paths_node b ks _).2 (Or.inr ⟨i, k, p₀, hk, hp₀, rfl⟩),
          by rw [bagAt_cons b ks i k p₀ hk]; exact hxp₀, ?_⟩
        intro q hq hxq hne
        rcases (mem_paths_node b ks q).1 hq with rfl | ⟨j, k', q'', hk', hq'', rfl⟩
        · rw [bagAt_nil] at hxq; exact absurd hxq hxb
        · rw [bagAt_cons b ks j k' q'' hk'] at hxq
          have hji : j = i := by
            by_contra hji
            have hxv1 := mem_verts_of_bagAt hq' hxp
            have hxv2 := mem_verts_of_bagAt hq'' hxq
            rw [List.pairwise_iff_getElem] at h3
            obtain ⟨hi1, hk1⟩ := List.getElem?_eq_some_iff.1 hk
            obtain ⟨hj1, hk2⟩ := List.getElem?_eq_some_iff.1 hk'
            rcases lt_or_gt_of_ne hji with h | h
            · exact hxb (h3 j i hj1 hi1 h x (by rw [hk2]; exact hxv2) (by rw [hk1]; exact hxv1))
            · exact hxb (h3 i j hi1 hj1 h x (by rw [hk1]; exact hxv1) (by rw [hk2]; exact hxv2))
          subst hji
          rw [hk] at hk'
          have hkk : k = k' := Option.some.inj hk'
          subst hkk
          have hq_ne : q'' ≠ p₀ := fun e => hne (by rw [e])
          obtain ⟨hne0, hd⟩ := htop q'' hq'' hxq hq_ne
          refine ⟨by simp, ?_⟩
          obtain ⟨a, q3, rfl⟩ := List.exists_cons_of_ne_nil hne0
          rw [List.dropLast_cons_of_ne_nil (by simp), bagAt_cons b ks j k _ hk]
          exact hd

end RT

end Lax117284Proofs.Treewidth.Trees
