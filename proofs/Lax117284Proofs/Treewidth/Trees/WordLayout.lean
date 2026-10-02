import Lax117284Proofs.Treewidth.Trees.NiceLemmas

/-!
# Nice-decomposition words in arbitrary layout (T2)

`GraphWords.NiceDecomposition` allows *any* topological layout of the nodes (the first child of a node is the node just
before it; the second child of a join is an arbitrary earlier node) and arbitrary junk in the unused fields of a record.
`NT.encode` produces only one canonical layout.  So the word format is read by `ofWord`, which ignores the junk and the
layout, and everything in this file is proved for an *arbitrary* word `D` satisfying `Lay n D` (the graph-independent
half of `NiceDecomposition`).

Notation: `N = nodeCount D`; `bagN n D i` is `bagAt n D i` with vertices as naturals; `ofWord D i` is the nice tree
rooted at node `i`; `desc D i` the set of nodes of that subtree.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

/-! ## bags as sets of naturals -/

/-- `bagAt` with the vertices as natural numbers. -/
def bagN (n : ℕ) (D : List ℕ) (i : ℕ) : Finset ℕ := (bagAt n D i).map Fin.valEmbedding

lemma mem_bagN {n : ℕ} {D : List ℕ} {i u : ℕ} :
    u ∈ bagN n D i ↔ ∃ h : u < n, (⟨u, h⟩ : Fin n) ∈ bagAt n D i := by
  unfold bagN
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hu⟩; exact ⟨⟨u, h⟩, hu, rfl⟩

lemma lt_of_mem_bagN {n : ℕ} {D : List ℕ} {i u : ℕ} (h : u ∈ bagN n D i) : u < n :=
  (mem_bagN.1 h).1

lemma bagN_zero (n : ℕ) (D : List ℕ) : bagN n D 0 = ∅ := by simp [bagN, bagAt]

lemma bagN_succ_intro {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 1) (hv : vertex D (i + 1) < n) :
    bagN n D (i + 1) = insert (vertex D (i + 1)) (bagN n D i) := by
  simp [bagN, bagAt, hk, hv, Finset.map_insert]

lemma bagN_succ_forget {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 2) (hv : vertex D (i + 1) < n) :
    bagN n D (i + 1) = (bagN n D i).erase (vertex D (i + 1)) := by
  simp [bagN, bagAt, hk, hv, Finset.map_erase]

lemma bagN_succ_join {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 3) :
    bagN n D (i + 1) = bagN n D i := by
  simp [bagN, bagAt, hk]

lemma bagN_succ_leaf {n : ℕ} {D : List ℕ} {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2)
    (h3 : kind D (i + 1) ≠ 3) : bagN n D (i + 1) = ∅ := by
  simp [bagN, bagAt, h1, h2, h3]

/-! ## the layout conditions -/

/-- The graph-independent half of `NiceDecomposition`: the word is `N` records, every record has the right shape, and
every non-last node has exactly one parent.  (The tree condition follows, `Lay.isTree`.) -/
structure Lay (n : ℕ) (D : List ℕ) : Prop where
  length_eq : D.length = 1 + 3 * nodeCount D
  nonempty : 0 < nodeCount D
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt n D (other D i) = bagAt n D (i - 1))
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p

variable {n : ℕ} {D : List ℕ}

/-- Introduce nodes. -/
lemma Lay.intro_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 1) :
    0 < i ∧ vertex D i < n ∧ vertex D i ∉ bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · refine ⟨h0, hv, fun hm => ?_⟩
    obtain ⟨h, hm⟩ := mem_bagN.1 hm
    exact hb h hm
  · omega
  · omega

/-- Forget nodes. -/
lemma Lay.forget_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 2) :
    0 < i ∧ vertex D i < n ∧ vertex D i ∈ bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · omega
  · exact ⟨h0, hv, mem_bagN.2 ⟨hv, hb hv⟩⟩
  · omega

/-- Join nodes. -/
lemma Lay.join_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 3) :
    0 < i ∧ other D i + 1 < i ∧ bagN n D (other D i) = bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · omega
  · omega
  · exact ⟨h0, hv, by simp only [bagN, hb]⟩

/-- Every kind is at most `3`, and a leaf is `0`. -/
lemma Lay.kind_le (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) : kind D i ≤ 3 := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ <;> omega

/-- The node after `i` has a parent iff it's not the last. -/
lemma Lay.isChild_lt (L : Lay n D) {c p : ℕ} (h : IsChild D c p) : c < p ∧ p < nodeCount D := by
  obtain ⟨hp, h⟩ := h
  refine ⟨?_, hp⟩
  rcases h with ⟨-, h⟩ | ⟨hk, h | h⟩
  · omega
  · omega
  · have := (L.join_data hp hk).2.1; omega

/-! ## the tree read off a word -/

/-- The nice tree rooted at node `i` (junk fields and the layout are ignored). -/
def ofWord (D : List ℕ) : ℕ → NT
  | 0 => .leaf
  | i + 1 =>
    if kind D (i + 1) = 1 then .intro (vertex D (i + 1)) (ofWord D i)
    else if kind D (i + 1) = 2 then .forget (vertex D (i + 1)) (ofWord D i)
    else if kind D (i + 1) = 3 then
      (if h : other D (i + 1) < i then .join (ofWord D i) (ofWord D (other D (i + 1))) else .leaf)
    else .leaf
termination_by i => i
decreasing_by all_goals omega

/-- The nodes of the subtree rooted at `i`. -/
def desc (D : List ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | i + 1 =>
    if kind D (i + 1) = 1 ∨ kind D (i + 1) = 2 then insert (i + 1) (desc D i)
    else if kind D (i + 1) = 3 then
      (if h : other D (i + 1) < i then insert (i + 1) (desc D i ∪ desc D (other D (i + 1))) else {i + 1})
    else {i + 1}
termination_by i => i
decreasing_by all_goals omega

lemma ofWord_zero : ofWord D 0 = .leaf := by rw [ofWord]

lemma ofWord_intro {i : ℕ} (h : kind D (i + 1) = 1) :
    ofWord D (i + 1) = .intro (vertex D (i + 1)) (ofWord D i) := by
  rw [ofWord]; simp [h]

lemma ofWord_forget {i : ℕ} (h : kind D (i + 1) = 2) :
    ofWord D (i + 1) = .forget (vertex D (i + 1)) (ofWord D i) := by
  rw [ofWord]; simp [h]

lemma ofWord_join {i : ℕ} (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) :
    ofWord D (i + 1) = .join (ofWord D i) (ofWord D (other D (i + 1))) := by
  rw [ofWord]; simp [h, ho]

lemma ofWord_leaf {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) :
    ofWord D (i + 1) = .leaf := by
  rw [ofWord]; simp [h1, h2, h3]

lemma desc_zero : desc D 0 = {0} := by rw [desc]

lemma desc_intro {i : ℕ} (h : kind D (i + 1) = 1) : desc D (i + 1) = insert (i + 1) (desc D i) := by
  rw [desc]; simp [h]

lemma desc_forget {i : ℕ} (h : kind D (i + 1) = 2) : desc D (i + 1) = insert (i + 1) (desc D i) := by
  rw [desc]; simp [h]

lemma desc_join {i : ℕ} (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) :
    desc D (i + 1) = insert (i + 1) (desc D i ∪ desc D (other D (i + 1))) := by
  rw [desc]; simp [h, ho]

lemma desc_leaf {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) :
    desc D (i + 1) = {i + 1} := by
  rw [desc]; simp [h1, h2, h3]

/-- The case analysis at node `i + 1`. -/
inductive Node (n : ℕ) (D : List ℕ) (i : ℕ) : Prop
  | leaf (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3)
  | intro (h : kind D (i + 1) = 1) (hv : vertex D (i + 1) < n) (hn : vertex D (i + 1) ∉ bagN n D i)
  | forget (h : kind D (i + 1) = 2) (hv : vertex D (i + 1) < n) (hn : vertex D (i + 1) ∈ bagN n D i)
  | join (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) (hb : bagN n D (other D (i + 1)) = bagN n D i)

lemma Lay.node (L : Lay n D) {i : ℕ} (hi : i + 1 < nodeCount D) : Node n D i := by
  by_cases h1 : kind D (i + 1) = 1
  · obtain ⟨-, hv, hn⟩ := L.intro_data hi h1
    exact .intro h1 hv (by simpa using hn)
  by_cases h2 : kind D (i + 1) = 2
  · obtain ⟨-, hv, hn⟩ := L.forget_data hi h2
    exact .forget h2 hv (by simpa using hn)
  by_cases h3 : kind D (i + 1) = 3
  · obtain ⟨-, ho, hb⟩ := L.join_data hi h3
    exact .join h3 (by omega) (by simpa using hb)
  exact .leaf h1 h2 h3

end Word

end Lax117284Proofs.Treewidth.Trees
