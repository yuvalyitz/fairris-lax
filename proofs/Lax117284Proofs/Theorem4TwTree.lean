import Lax117284Proofs.Treewidth
import Lax117284Proofs.Bridge
import Lax117284.Bodlaender

/-!
# From the Word of a Nice Tree Decomposition to a `NiceTree`

The cited decomposition program returns a word (`Bodlaender.NiceDecomposition`), which describes an
unrooted tree by parent pointers and states the connectedness of the bags through the archive's
`Connected`. The dynamic program of `Theorem4TreewidthDP.lean` runs on the rooted inductive
`NiceTree`. This file builds the `NiceTree` of a node of the word and shows that the word being a
nice decomposition of the conflict graph makes the tree one (`IsNice`): the two separation
properties the dynamic program needs are exactly what connectedness says once a root is fixed.
-/

namespace Lax117284Proofs.TwTree

open Lax117284.Bodlaender Lax117284.Scheduling Lax117284Proofs.Model

/-- The rooted tree of node `i` of the word `D`, on the vertices `0 … n - 1`. -/
def toTree (n : ℕ) (D : List ℕ) : ℕ → NiceTree (Fin n)
  | 0 => .leaf ∅
  | i + 1 =>
      if kind D (i + 1) = 1 then
        if h : vertex D (i + 1) < n then .intro ⟨vertex D (i + 1), h⟩ (toTree n D i)
        else toTree n D i
      else if kind D (i + 1) = 2 then
        if h : vertex D (i + 1) < n then .forget ⟨vertex D (i + 1), h⟩ (toTree n D i)
        else toTree n D i
      else if kind D (i + 1) = 3 then
        if h : other D (i + 1) < i + 1 then .join (toTree n D (other D (i + 1))) (toTree n D i)
        else toTree n D i
      else .leaf ∅
termination_by i => i
decreasing_by
  all_goals (try simp_wf)
  all_goals first | omega | assumption


section Basic

variable {I : Lax117284.Scheduling.Instance} {w : ℕ} {D : List ℕ}

/-- Node `x` lies below node `p`: a chain of children leads from `x` to `p`. -/
def Anc (D : List ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen (IsChild D)

lemma isChild_lt (hD : NiceDecomposition I w D) {c p : ℕ}
    (h : IsChild D c p) : c < p := by
  obtain ⟨hp, h⟩ := h
  rcases hD.shape p hp with h0 | ⟨h1, hk, -⟩ | ⟨h1, hk, -⟩ | ⟨h1, hk, ho, -⟩
  · rcases h with ⟨hk, -⟩ | ⟨hk, -⟩ <;> omega
  · rcases h with ⟨-, h⟩ | ⟨hk', -⟩ <;> omega
  · rcases h with ⟨-, h⟩ | ⟨hk', -⟩ <;> omega
  · rcases h with ⟨hk', -⟩ | ⟨-, h | h⟩
    · omega
    · omega
    · omega

lemma isChild_unique (hD : NiceDecomposition I w D) {c p q : ℕ}
    (hp : IsChild D c p) (hq : IsChild D c q) : p = q := by
  have hlt := isChild_lt hD hp
  have hN : c + 1 < nodeCount D := by have := hp.1; omega
  exact (hD.parent c hN).unique hp hq

lemma anc_le (hD : NiceDecomposition I w D) {c p : ℕ} (h : Anc D c p) :
    c ≤ p := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (isChild_lt hD hs).le

/-- Below `i + 1`: itself, or below one of its children. -/
lemma anc_succ_iff {i x : ℕ} :
    Anc D x (i + 1) ↔ x = i + 1 ∨ ∃ c, Anc D x c ∧ IsChild D c (i + 1) := by
  unfold Anc
  rw [Relation.ReflTransGen.cases_tail_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

lemma isChild_succ_iff {i c : ℕ} :
    IsChild D c (i + 1) ↔ i + 1 < nodeCount D ∧
      (((kind D (i + 1) = 1 ∨ kind D (i + 1) = 2) ∧ c = i) ∨
        (kind D (i + 1) = 3 ∧ (c = i ∨ c = other D (i + 1)))) := by
  unfold IsChild
  constructor
  · rintro ⟨h, ⟨hk, h2⟩ | ⟨hk, h2 | h2⟩⟩
    · exact ⟨h, Or.inl ⟨hk, by omega⟩⟩
    · exact ⟨h, Or.inr ⟨hk, Or.inl (by omega)⟩⟩
    · exact ⟨h, Or.inr ⟨hk, Or.inr h2⟩⟩
  · rintro ⟨h, ⟨hk, h2⟩ | ⟨hk, h2 | h2⟩⟩
    · exact ⟨h, Or.inl ⟨hk, by omega⟩⟩
    · exact ⟨h, Or.inr ⟨hk, Or.inl (by omega)⟩⟩
    · exact ⟨h, Or.inr ⟨hk, Or.inr h2⟩⟩

/-- **The bag of the tree of a node is the bag of the node.** -/
lemma bag_toTree (hD : NiceDecomposition I w D) : ∀ i, i < nodeCount D →
    (toTree I.clients D i).bag = bagAt I.clients D i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [toTree, bagAt]
    | succ i =>
      have hshape := hD.shape (i + 1) hi
      rw [toTree, bagAt]
      rcases hshape with h0 | ⟨_, hk, hv, _⟩ | ⟨_, hk, hv, _⟩ | ⟨_, hk, ho, hb⟩
      · simp [h0]
      · have hih := ih i (by omega) (by omega)
        simp [hk, hv, hih]
      · have hih := ih i (by omega) (by omega)
        simp [hk, hv, hih]
      · have hih := ih i (by omega) (by omega)
        have hoi : other D (i + 1) < i + 1 := by omega
        have hio := ih (other D (i + 1)) hoi (by omega)
        have hb' : bagAt I.clients D (other D (i + 1)) = bagAt I.clients D i := by
          simpa using hb
        simp [hk, hoi, hio, hb']

lemma anc_succ_unary {i x : ℕ} (hi : i + 1 < nodeCount D)
    (hk : kind D (i + 1) = 1 ∨ kind D (i + 1) = 2) :
    Anc D x (i + 1) ↔ x = i + 1 ∨ Anc D x i := by
  rw [anc_succ_iff]
  constructor
  · rintro (h | ⟨c, hc, hch⟩)
    · exact Or.inl h
    · rw [isChild_succ_iff] at hch
      rcases hch with ⟨-, ⟨-, rfl⟩ | ⟨hk3, -⟩⟩
      · exact Or.inr hc
      · omega
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨i, h, isChild_succ_iff.2 ⟨hi, Or.inl ⟨hk, rfl⟩⟩⟩

lemma anc_succ_join {i x : ℕ} (hi : i + 1 < nodeCount D) (hk : kind D (i + 1) = 3) :
    Anc D x (i + 1) ↔ x = i + 1 ∨ Anc D x i ∨ Anc D x (other D (i + 1)) := by
  rw [anc_succ_iff]
  constructor
  · rintro (h | ⟨c, hc, hch⟩)
    · exact Or.inl h
    · rw [isChild_succ_iff] at hch
      rcases hch with ⟨-, ⟨hk', -⟩ | ⟨-, rfl | rfl⟩⟩
      · omega
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr ⟨i, h, isChild_succ_iff.2 ⟨hi, Or.inr ⟨hk, Or.inl rfl⟩⟩⟩
    · exact Or.inr ⟨_, h, isChild_succ_iff.2 ⟨hi, Or.inr ⟨hk, Or.inr rfl⟩⟩⟩

lemma anc_zero {x : ℕ} (hD : NiceDecomposition I w D) (h : Anc D x 0) : x = 0 := by
  have := anc_le hD h; omega

lemma anc_succ_leaf {i x : ℕ} (hk : kind D (i + 1) = 0) : Anc D x (i + 1) ↔ x = i + 1 := by
  rw [anc_succ_iff]
  constructor
  · rintro (h | ⟨c, -, hch⟩)
    · exact h
    · rw [isChild_succ_iff] at hch; omega
  · exact Or.inl

lemma bagAt_succ_intro {n : ℕ} {i : ℕ} (hk : kind D (i + 1) = 1) (hv : vertex D (i + 1) < n) :
    bagAt n D (i + 1) = insert ⟨vertex D (i + 1), hv⟩ (bagAt n D i) := by
  simp [bagAt, hk, hv]

lemma bagAt_succ_forget {n : ℕ} {i : ℕ} (hk : kind D (i + 1) = 2) (hv : vertex D (i + 1) < n) :
    bagAt n D (i + 1) = (bagAt n D i).erase ⟨vertex D (i + 1), hv⟩ := by
  simp [bagAt, hk, hv]

lemma bagAt_succ_join {n : ℕ} {i : ℕ} (hk : kind D (i + 1) = 3) :
    bagAt n D (i + 1) = bagAt n D i := by
  simp [bagAt, hk]

lemma bagAt_succ_leaf {n : ℕ} {i : ℕ} (hk : kind D (i + 1) = 0) :
    bagAt n D (i + 1) = ∅ := by
  simp [bagAt, hk]

/-- **The vertices of the tree of a node** are the vertices of the bags below it. -/
lemma mem_verts_toTree (hD : NiceDecomposition I w D) : ∀ i, i < nodeCount D →
    ∀ v : Fin I.clients, v ∈ (toTree I.clients D i).verts ↔
      ∃ x, Anc D x i ∧ v ∈ bagAt I.clients D x := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi v
    cases i with
    | zero =>
      simp only [toTree, NiceTree.verts_leaf, Finset.notMem_empty, false_iff, not_exists]
      intro x ⟨hx, hv⟩
      have := anc_zero hD hx
      subst this
      simp [bagAt] at hv
    | succ i =>
      have hshape := hD.shape (i + 1) hi
      rw [toTree]
      rcases hshape with h0 | ⟨_, hk, hv', _⟩ | ⟨_, hk, hv', _⟩ | ⟨_, hk, ho, hb⟩
      · simp only [h0, Nat.reduceEqDiff, if_false, NiceTree.verts_leaf, Finset.notMem_empty,
          false_iff, not_exists]
        rintro x ⟨hx, hvx⟩
        rw [anc_succ_leaf h0] at hx
        subst hx
        simp [bagAt_succ_leaf h0] at hvx
      · have hih := ih i (by omega) (by omega) v
        simp only [hk, ↓reduceIte, dif_pos hv', NiceTree.verts_intro, Finset.mem_insert, hih]
        constructor
        · rintro (rfl | ⟨x, hx, hvx⟩)
          · exact ⟨i + 1, Relation.ReflTransGen.refl, by rw [bagAt_succ_intro hk hv']; simp⟩
          · exact ⟨x, (anc_succ_unary (by omega) (Or.inl hk)).2 (Or.inr hx), hvx⟩
        · rintro ⟨x, hx, hvx⟩
          rcases (anc_succ_unary (by omega) (Or.inl hk)).1 hx with rfl | hx
          · rw [bagAt_succ_intro hk hv'] at hvx
            rcases Finset.mem_insert.1 hvx with h | hvx
            · exact Or.inl h
            · exact Or.inr ⟨i, Relation.ReflTransGen.refl, hvx⟩
          · exact Or.inr ⟨x, hx, hvx⟩
      · have hih := ih i (by omega) (by omega) v
        simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hv', NiceTree.verts_forget, hih]
        constructor
        · rintro ⟨x, hx, hvx⟩
          exact ⟨x, (anc_succ_unary (by omega) (Or.inr hk)).2 (Or.inr hx), hvx⟩
        · rintro ⟨x, hx, hvx⟩
          rcases (anc_succ_unary (by omega) (Or.inr hk)).1 hx with rfl | hx
          · rw [bagAt_succ_forget hk hv'] at hvx
            exact ⟨i, Relation.ReflTransGen.refl, Finset.mem_of_mem_erase hvx⟩
          · exact ⟨x, hx, hvx⟩
      · have hoi : other D (i + 1) < i + 1 := by omega
        have hih := ih i (by omega) (by omega) v
        have hio := ih (other D (i + 1)) hoi (by omega) v
        simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hoi, NiceTree.verts_join,
          Finset.mem_union, hih, hio]
        constructor
        · rintro (⟨x, hx, hvx⟩ | ⟨x, hx, hvx⟩)
          · exact ⟨x, (anc_succ_join (by omega) hk).2 (Or.inr (Or.inr hx)), hvx⟩
          · exact ⟨x, (anc_succ_join (by omega) hk).2 (Or.inr (Or.inl hx)), hvx⟩
        · rintro ⟨x, hx, hvx⟩
          rcases (anc_succ_join (by omega) hk).1 hx with rfl | hx | hx
          · rw [bagAt_succ_join hk] at hvx
            exact Or.inr ⟨i, Relation.ReflTransGen.refl, hvx⟩
          · exact Or.inr ⟨x, hx, hvx⟩
          · exact Or.inl ⟨x, hx, hvx⟩

/-- Every bag below a node is a bag of the tree of the node. -/
lemma hasBag_of_anc (hD : NiceDecomposition I w D) : ∀ i, i < nodeCount D → ∀ x,
    Anc D x i → (toTree I.clients D i).HasBag (bagAt I.clients D x) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi x hx
    cases i with
    | zero =>
      have := anc_zero hD hx
      subst this
      simp [toTree, NiceTree.hasBag_leaf_iff, bagAt]
    | succ i =>
      have hshape := hD.shape (i + 1) hi
      rw [toTree]
      rcases hshape with h0 | ⟨_, hk, hv', _⟩ | ⟨_, hk, hv', _⟩ | ⟨_, hk, ho, hb⟩
      · rw [anc_succ_leaf h0] at hx
        subst hx
        simp [h0, NiceTree.hasBag_leaf_iff, bagAt_succ_leaf h0]
      · simp only [hk, ↓reduceIte, dif_pos hv', NiceTree.hasBag_intro_iff]
        rcases (anc_succ_unary (by omega) (Or.inl hk)).1 hx with rfl | hx
        · left; rw [bagAt_succ_intro hk hv', bag_toTree hD i (by omega)]
        · right; exact ih i (by omega) (by omega) x hx
      · simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hv', NiceTree.hasBag_forget_iff]
        rcases (anc_succ_unary (by omega) (Or.inr hk)).1 hx with rfl | hx
        · left; rw [bagAt_succ_forget hk hv', bag_toTree hD i (by omega)]
        · right; exact ih i (by omega) (by omega) x hx
      · have hoi : other D (i + 1) < i + 1 := by omega
        have hb' : bagAt I.clients D (other D (i + 1)) = bagAt I.clients D i := by simpa using hb
        simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hoi, NiceTree.hasBag_join_iff]
        rcases (anc_succ_join (by omega) hk).1 hx with rfl | hx | hx
        · left; rw [bagAt_succ_join hk, bag_toTree hD _ (by omega), hb']
        · right; right; exact ih i (by omega) (by omega) x hx
        · right; left; exact ih _ hoi (by omega) x hx

/-- **Every node lies below the last one.** -/
lemma anc_root (hD : NiceDecomposition I w D) :
    ∀ d x, x < nodeCount D → nodeCount D - 1 - x = d → Anc D x (nodeCount D - 1) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hx hd
    by_cases hlast : x + 1 = nodeCount D
    · have : x = nodeCount D - 1 := by omega
      rw [this]; exact Relation.ReflTransGen.refl
    · obtain ⟨p, hp, -⟩ := hD.parent x (by omega)
      have hlt := isChild_lt hD hp
      have hpN := hp.1
      exact Relation.ReflTransGen.head hp (ih (nodeCount D - 1 - p) (by omega) p hpN rfl)

/-- Two chains from a node upwards: one is part of the other. -/
lemma anc_total (hD : NiceDecomposition I w D) {x a b : ℕ} (ha : Anc D x a) (hb : Anc D x b) :
    Anc D a b ∨ Anc D b a := by
  induction ha using Relation.ReflTransGen.head_induction_on generalizing b with
  | refl => exact Or.inl hb
  | head hxc hca ih =>
    rename_i x' c
    rcases Relation.ReflTransGen.cases_head hb with h | ⟨z, hz, hzb⟩
    · exact Or.inr (h ▸ Relation.ReflTransGen.head hxc hca)
    · have := isChild_unique hD hxc hz
      subst this
      exact ih hzb

/-- The parent of a proper descendant of `c` is again below `c`. -/
lemma parent_anc (hD : NiceDecomposition I w D) {x c y : ℕ} (hx : Anc D x c) (hxc : x ≠ c)
    (hy : IsChild D x y) : Anc D y c := by
  rcases Relation.ReflTransGen.cases_head hx with h | ⟨z, hz, hzc⟩
  · exact absurd h hxc
  · have := isChild_unique hD hy hz
    subst this
    exact hzc

/-- **Leaving the tree of a node**: a step of the tree graph from below `c` to a node not below
`c` starts at `c` and goes to its parent. -/
lemma exit_desc (hD : NiceDecomposition I w D) {c x y : ℕ} (hx : Anc D x c) (hy : ¬ Anc D y c)
    (hadj : IsChild D x y ∨ IsChild D y x) : x = c ∧ IsChild D c y := by
  rcases hadj with h | h
  · by_cases hxc : x = c
    · subst hxc; exact ⟨rfl, h⟩
    · exact absurd (parent_anc hD hx hxc h) hy
  · exact absurd (Relation.ReflTransGen.head h hx) hy

/-- A connected induced subgraph that contains a vertex inside `A` and one outside `A` has an
edge leaving `A`. -/
lemma exists_exit {α : Type} (G : SimpleGraph α) (S A : Set α) (hconn : (G.induce S).Connected)
    {a b : α} (ha : a ∈ S) (hb : b ∈ S) (haA : a ∈ A) (hbA : b ∉ A) :
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ∈ A ∧ y ∉ A ∧ G.Adj x y := by
  have hr := hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ v : S, Relation.ReflTransGen (G.induce S).Adj ⟨a, ha⟩ v →
      v.1 ∈ A ∨ ∃ x y, x ∈ S ∧ y ∈ S ∧ x ∈ A ∧ y ∉ A ∧ G.Adj x y := by
    intro v hv
    induction hv with
    | refl => exact Or.inl haA
    | @tail v' v'' _ hs ih =>
      rcases ih with h | h
      · by_cases h' : v''.1 ∈ A
        · exact Or.inl h'
        · exact Or.inr ⟨v'.1, v''.1, v'.2, v''.2, h, h', hs⟩
      · exact Or.inr h
  rcases key ⟨b, hb⟩ hr with h | h
  · exact absurd h hbA
  · exact h

/-- **Introduce nodes separate**, from connectedness: the introduced vertex occurs nowhere below
the child. -/
lemma intro_not_mem (hD : NiceDecomposition I w D) {i : ℕ} (hi : i + 1 < nodeCount D)
    (hk : kind D (i + 1) = 1) (hv' : vertex D (i + 1) < I.clients) :
    (⟨vertex D (i + 1), hv'⟩ : Fin I.clients) ∉ (toTree I.clients D i).verts := by
  intro hmem
  rw [mem_verts_toTree hD i (by omega)] at hmem
  obtain ⟨x, hx, hvx⟩ := hmem
  have hnot : (⟨vertex D (i + 1), hv'⟩ : Fin I.clients) ∉ bagAt I.clients D i := by
    rcases hD.shape (i + 1) hi with h0 | ⟨_, _, _, hn⟩ | ⟨_, hk2, _⟩ | ⟨_, hk3, _⟩
    · omega
    · simpa using hn hv'
    · omega
    · omega
  have hvi : (⟨vertex D (i + 1), hv'⟩ : Fin I.clients) ∈ bagAt I.clients D (i + 1) := by
    rw [bagAt_succ_intro hk hv']; simp
  have hxN : x < nodeCount D := by have := anc_le hD hx; omega
  obtain ⟨x', y', hx'S, hy'S, hx'A, hy'A, hadj⟩ := exists_exit (treeGraph D)
    {j : Fin (nodeCount D) | (⟨vertex D (i + 1), hv'⟩ : Fin I.clients) ∈ bagAt I.clients D j}
    {j : Fin (nodeCount D) | Anc D j i} (hD.connected _)
    (a := ⟨x, hxN⟩) (b := ⟨i + 1, hi⟩) hvx hvi hx (fun h => by
      have := anc_le hD h; simp at this)
  obtain ⟨heq, -⟩ := exit_desc hD hx'A hy'A hadj.2
  exact hnot (heq ▸ hx'S)

/-- **Join nodes separate**, from connectedness. -/
lemma join_inter (hD : NiceDecomposition I w D) {i : ℕ} (hi : i + 1 < nodeCount D)
    (hk : kind D (i + 1) = 3) (ho : other D (i + 1) + 1 < i + 1) :
    (toTree I.clients D (other D (i + 1))).verts ∩ (toTree I.clients D i).verts ⊆
      bagAt I.clients D (i + 1) := by
  intro v hv
  rw [Finset.mem_inter, mem_verts_toTree hD _ (by omega), mem_verts_toTree hD i (by omega)] at hv
  obtain ⟨⟨x, hx, hvx⟩, ⟨x', hx', hvx'⟩⟩ := hv
  by_contra hnot
  have hxN : x < nodeCount D := by have := anc_le hD hx; omega
  have hx'N : x' < nodeCount D := by have := anc_le hD hx'; omega
  have hpar : IsChild D (other D (i + 1)) (i + 1) :=
    isChild_succ_iff.2 ⟨hi, Or.inr ⟨hk, Or.inr rfl⟩⟩
  have hdis : ¬ Anc D x' (other D (i + 1)) := by
    intro h
    have hpar' : IsChild D i (i + 1) := isChild_succ_iff.2 ⟨hi, Or.inr ⟨hk, Or.inl rfl⟩⟩
    rcases anc_total hD hx' h with h1 | h1
    · -- `i` is below `other`, so `other ≥ i`
      have := anc_le hD h1; omega
    · -- `other` is below `i`
      rcases Relation.ReflTransGen.cases_head h1 with h2 | ⟨z, hz, hzi⟩
      · omega
      · have := isChild_unique hD hz hpar
        subst this
        have := anc_le hD hzi; omega
  obtain ⟨x'', y'', hx''S, hy''S, hx''A, hy''A, hadj⟩ := exists_exit (treeGraph D)
    {j : Fin (nodeCount D) | v ∈ bagAt I.clients D j}
    {j : Fin (nodeCount D) | Anc D j (other D (i + 1))} (hD.connected _)
    (a := ⟨x, hxN⟩) (b := ⟨x', hx'N⟩) hvx hvx' hx hdis
  obtain ⟨heq, hch⟩ := exit_desc hD hx''A hy''A hadj.2
  have := isChild_unique hD hch hpar
  apply hnot
  have h3 : v ∈ bagAt I.clients D y''.1 := hy''S
  rw [this] at h3
  exact h3

/-- **The tree of every node is coherent.** -/
lemma coherent_toTree (hD : NiceDecomposition I w D) : ∀ i, i < nodeCount D →
    (toTree I.clients D i).Coherent := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [toTree, NiceTree.coherent_leaf_iff]
    | succ i =>
      have hshape := hD.shape (i + 1) hi
      rw [toTree]
      rcases hshape with h0 | ⟨_, hk, hv', _⟩ | ⟨_, hk, hv', hin⟩ | ⟨_, hk, ho, hb⟩
      · simp [h0, NiceTree.coherent_leaf_iff]
      · simp only [hk, ↓reduceIte, dif_pos hv', NiceTree.coherent_intro_iff]
        exact ⟨intro_not_mem hD hi hk hv', ih i (by omega) (by omega)⟩
      · simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hv', NiceTree.coherent_forget_iff]
        refine ⟨?_, ih i (by omega) (by omega)⟩
        rw [bag_toTree hD i (by omega)]
        simpa using hin hv'
      · have hoi : other D (i + 1) < i + 1 := by omega
        have hb' : bagAt I.clients D (other D (i + 1)) = bagAt I.clients D i := by simpa using hb
        simp only [hk, Nat.reduceEqDiff, ↓reduceIte, dif_pos hoi, NiceTree.coherent_join_iff]
        refine ⟨?_, ?_, ih _ hoi (by omega), ih i (by omega) (by omega)⟩
        · rw [bag_toTree hD _ (by omega), bag_toTree hD i (by omega), hb']
        · rw [bag_toTree hD _ (by omega), hb', ← bagAt_succ_join hk]
          exact join_inter hD hi hk ho

/-- **The tree of the last node is a nice tree decomposition of the conflict graph.** -/
theorem isNice_toTree (hD : NiceDecomposition I w D) :
    NiceTree.IsNice (Lax117284.ConflictGraph.overallGraph I)
      (toTree I.clients D (nodeCount D - 1)) := by
  have hN := hD.nonempty
  refine ⟨?_, ?_, coherent_toTree hD _ (by omega)⟩
  · intro v
    obtain ⟨i, hi, hv⟩ := hD.covers v
    rw [mem_verts_toTree hD _ (by omega)]
    exact ⟨i, anc_root hD _ i hi rfl, hv⟩
  · intro u v huv
    obtain ⟨i, hi, hu, hv⟩ := hD.edges u v huv
    exact ⟨bagAt I.clients D i, hasBag_of_anc hD _ (by omega) i (anc_root hD _ i hi rfl), hu, hv⟩

end Basic

end Lax117284Proofs.TwTree
