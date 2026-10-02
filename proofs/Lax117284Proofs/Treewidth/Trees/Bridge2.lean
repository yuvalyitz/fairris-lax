import Lax117284Proofs.Treewidth.Trees.EncodeReads

/-!
# Bridge 2: nice trees and `GraphWords.NiceDecomposition` (T2)
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma recAt_eq {D : List ℕ} {i k v o : ℕ} (h : recAt D i = (k, v, o)) :
    kind D i = k ∧ vertex D i = v ∧ other D i = o := by
  simp only [recAt, Prod.mk.injEq] at h; exact h

/-- The bag at the root of the block of `t` is the bag of `t`. -/
lemma bagN_root {n : ℕ} {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → t.Wf →
    (∀ u ∈ t.vs, u < n) → bagN n D (b + t.size - 1) = t.bag := by
  intro t
  induction t with
  | leaf =>
    intro b h _ _
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    simp only [NT.size, NT.bag_leaf]
    cases b with
    | zero => simp [bagN_zero]
    | succ b =>
      have : b + 1 + 1 - 1 = b + 1 := by omega
      rw [this]
      exact bagN_succ_leaf (by omega) (by omega) (by omega)
  | intro v c ih =>
    intro b h hw hlt
    obtain ⟨hc, hrec⟩ := h.intro
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hvn : v < n := hlt v (by simp [NT.vs_intro])
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_intro, hu])
    have := ih b hc hw.2 hcl
    have hidx : b + (NT.intro v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_intro hk (hv ▸ hvn), this, hv, NT.bag_intro]
  | forget v c ih =>
    intro b h hw hlt
    obtain ⟨hc, hrec⟩ := h.forget
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hvn : v < n := hlt v (by
      have := hw.1
      have := NT.bag_subset_vs c this
      simp [NT.vs_forget, this])
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_forget, hu])
    have := ih b hc hw.2 hcl
    have hidx : b + (NT.forget v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_forget hk (hv ▸ hvn), this, hv, NT.bag_forget]
  | join x y ihx ihy =>
    intro b h hw hlt
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    obtain ⟨i, hi⟩ : ∃ i, b + y.size + x.size = i + 1 := ⟨b + y.size + x.size - 1, by omega⟩
    rw [hi] at hrec
    obtain ⟨hk, -, -⟩ := recAt_eq hrec
    have hxl : ∀ u ∈ x.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    have := ihx (b + y.size) hx hw.2.1 hxl
    have hidx : b + (NT.join x y).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + y.size + x.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_join hk, this, NT.bag_join]

/-- The shape condition at node `i` (as in `NiceDecomposition.shape`). -/
abbrev ShapeAt (n : ℕ) (D : List ℕ) (i : ℕ) : Prop :=
  kind D i = 0 ∨
  (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
    ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
  (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
    ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
  (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
    bagAt n D (other D i) = bagAt n D (i - 1))

lemma fin_mem_bagAt {D : List ℕ} {i u : ℕ} (h : u < n) :
    (⟨u, h⟩ : Fin n) ∈ bagAt n D i ↔ u ∈ bagN n D i := (mem_bagN_fin (⟨u, h⟩ : Fin n)).symm

lemma bagAt_eq_of_bagN_eq {D : List ℕ} {i j : ℕ} (h : bagN n D i = bagN n D j) :
    bagAt n D i = bagAt n D j :=
  Finset.map_injective Fin.valEmbedding h

lemma shape_of_reads {n : ℕ} {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → t.Wf →
    (∀ u ∈ t.vs, u < n) → ∀ j, b ≤ j → j < b + t.size → ShapeAt n D j := by
  intro t
  induction t with
  | leaf =>
    intro b h _ _ j hj1 hj2
    have hjb : j = b := by simp [NT.size] at hj2; omega
    subst hjb
    exact Or.inl (recAt_eq h.leaf).1
  | intro v c ih =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hc, hrec⟩ := h.intro
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_intro, hu])
    simp only [NT.size] at hj2
    by_cases hjc : j < b + c.size
    · exact ih b hc hw.2 hcl j hj1 hjc
    · have hjeq : j = b + c.size := by omega
      subst hjeq
      obtain ⟨hk, hv, -⟩ := recAt_eq hrec
      have hvn : v < n := hlt v (by simp [NT.vs_intro])
      have hroot := bagN_root c b hc hw.2 hcl
      right; left
      refine ⟨by have := size_pos c; omega, hk, hv ▸ hvn, fun h hmem => ?_⟩
      rw [fin_mem_bagAt h, hv] at hmem
      rw [hroot] at hmem
      exact hw.1 hmem
  | forget v c ih =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hc, hrec⟩ := h.forget
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_forget, hu])
    simp only [NT.size] at hj2
    by_cases hjc : j < b + c.size
    · exact ih b hc hw.2 hcl j hj1 hjc
    · have hjeq : j = b + c.size := by omega
      subst hjeq
      obtain ⟨hk, hv, -⟩ := recAt_eq hrec
      have hvn : v < n := hcl v (NT.bag_subset_vs c hw.1)
      have hroot := bagN_root c b hc hw.2 hcl
      right; right; left
      refine ⟨by have := size_pos c; omega, hk, hv ▸ hvn, fun h => ?_⟩
      rw [fin_mem_bagAt h, hv, hroot]
      exact hw.1
  | join x y ihx ihy =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    have hxl : ∀ u ∈ x.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    have hyl : ∀ u ∈ y.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    simp only [NT.size] at hj2
    by_cases hjy : j < b + y.size
    · exact ihy b hy hw.2.2 hyl j hj1 hjy
    · by_cases hjx : j < b + y.size + x.size
      · exact ihx (b + y.size) hx hw.2.1 hxl j (by omega) hjx
      · have hjeq : j = b + y.size + x.size := by omega
        subst hjeq
        obtain ⟨hk, -, ho⟩ := recAt_eq hrec
        have hrx := bagN_root x (b + y.size) hx hw.2.1 hxl
        have hry := bagN_root y b hy hw.2.2 hyl
        right; right; right
        refine ⟨by omega, hk, by omega, ?_⟩
        apply bagAt_eq_of_bagN_eq
        rw [ho, hry, show b + y.size + x.size - 1 = (b + y.size) + x.size - 1 by omega, hrx]
        exact hw.1.symm

/-! ### parents in the canonical layout -/

/-- The parent relation of the block of `t` placed at `b` (child, parent). -/
def PC : ℕ → NT → ℕ → ℕ → Prop
  | _, NT.leaf, _, _ => False
  | b, NT.intro _ c, x, p => PC b c x p ∨ (p = b + c.size ∧ x + 1 = p)
  | b, NT.forget _ c, x, p => PC b c x p ∨ (p = b + c.size ∧ x + 1 = p)
  | b, NT.join x y, c, p => PC b y c p ∨ PC (b + y.size) x c p ∨
      (p = b + y.size + x.size ∧ (c + 1 = p ∨ c = b + y.size - 1))

lemma PC_bounds : ∀ (t : NT) (b c p : ℕ), PC b t c p → b ≤ c ∧ c < p ∧ p < b + t.size := by
  intro t
  induction t with
  | leaf => intro b c p h; exact h.elim
  | intro v c' ih =>
    intro b c p h
    have := size_pos c'
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | ⟨h1, h2⟩
    · have := ih b c p h; omega
    · omega
  | forget v c' ih =>
    intro b c p h
    have := size_pos c'
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | ⟨h1, h2⟩
    · have := ih b c p h; omega
    · omega
  | join x y ihx ihy =>
    intro b c p h
    have := size_pos x
    have := size_pos y
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | h | ⟨h1, h2 | h2⟩
    · have := ihy b c p h; omega
    · have := ihx (b + y.size) c p h; omega
    · omega
    · omega

lemma PC_existsUnique : ∀ (t : NT) (b c : ℕ), b ≤ c → c + 1 < b + t.size → ∃! p, PC b t c p := by
  intro t
  induction t with
  | leaf => intro b c h1 h2; simp [NT.size] at h2; omega
  | intro v c' ih =>
    intro b c h1 h2
    have := size_pos c'
    simp only [NT.size] at h2
    by_cases hc : c + 1 < b + c'.size
    · obtain ⟨p, hp, hu⟩ := ih b c h1 hc
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, hq2⟩
      · exact hu q hq
      · omega
    · refine ⟨b + c'.size, Or.inr ⟨rfl, by omega⟩, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, -⟩
      · have := PC_bounds c' b c q hq; omega
      · exact hq1
  | forget v c' ih =>
    intro b c h1 h2
    have := size_pos c'
    simp only [NT.size] at h2
    by_cases hc : c + 1 < b + c'.size
    · obtain ⟨p, hp, hu⟩ := ih b c h1 hc
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, hq2⟩
      · exact hu q hq
      · omega
    · refine ⟨b + c'.size, Or.inr ⟨rfl, by omega⟩, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, -⟩
      · have := PC_bounds c' b c q hq; omega
      · exact hq1
  | join x y ihx ihy =>
    intro b c h1 h2
    have hxs := size_pos x
    have hys := size_pos y
    simp only [NT.size] at h2
    by_cases hcy : c + 1 < b + y.size
    · obtain ⟨p, hp, hu⟩ := ihy b c h1 hcy
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | hq | ⟨hq1, hq2 | hq2⟩
      · exact hu q hq
      · have := PC_bounds x (b + y.size) c q hq; omega
      · omega
      · omega
    · by_cases hcx : c + 1 < b + y.size + x.size
      · by_cases hcy' : c + 1 = b + y.size
        · refine ⟨b + y.size + x.size, Or.inr (Or.inr ⟨rfl, Or.inr (by omega)⟩), fun q hq => ?_⟩
          rcases hq with hq | hq | ⟨hq1, -⟩
          · have := PC_bounds y b c q hq; omega
          · have := PC_bounds x (b + y.size) c q hq; omega
          · exact hq1
        · obtain ⟨p, hp, hu⟩ := ihx (b + y.size) c (by omega) (by omega)
          refine ⟨p, Or.inr (Or.inl hp), fun q hq => ?_⟩
          rcases hq with hq | hq | ⟨hq1, hq2 | hq2⟩
          · have := PC_bounds y b c q hq; omega
          · exact hu q hq
          · omega
          · omega
      · refine ⟨b + y.size + x.size, Or.inr (Or.inr ⟨rfl, Or.inl (by omega)⟩), fun q hq => ?_⟩
        rcases hq with hq | hq | ⟨hq1, -⟩
        · have := PC_bounds y b c q hq; omega
        · have := PC_bounds x (b + y.size) c q hq; omega
        · exact hq1

lemma isChild_iff_PC {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → b + t.size ≤ nodeCount D →
    ∀ c p, b ≤ p → p < b + t.size → (IsChild D c p ↔ PC b t c p) := by
  intro t
  induction t with
  | leaf =>
    intro b h hN c p hp1 hp2
    have hpb : p = b := by simp [NT.size] at hp2; omega
    subst hpb
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    simp only [PC, iff_false]
    rintro ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ <;> omega
  | intro v c' ih =>
    intro b h hN c p hp1 hp2
    obtain ⟨hc, hrec⟩ := h.intro
    have hs := size_pos c'
    simp only [NT.size] at hp2 hN
    by_cases hpc : p < b + c'.size
    · rw [ih b hc (by omega) c p hp1 hpc]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · have hpeq : p = b + c'.size := by omega
      subst hpeq
      obtain ⟨hk, -, -⟩ := recAt_eq hrec
      rw [PC]
      constructor
      · rintro ⟨-, ⟨-, h'⟩ | ⟨h', -⟩⟩
        · exact Or.inr ⟨rfl, h'⟩
        · omega
      · rintro (h' | ⟨-, h'⟩)
        · have := (PC_bounds c' b c _ h'); omega
        · exact ⟨by omega, Or.inl ⟨Or.inl hk, h'⟩⟩
  | forget v c' ih =>
    intro b h hN c p hp1 hp2
    obtain ⟨hc, hrec⟩ := h.forget
    have hs := size_pos c'
    simp only [NT.size] at hp2 hN
    by_cases hpc : p < b + c'.size
    · rw [ih b hc (by omega) c p hp1 hpc]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · have hpeq : p = b + c'.size := by omega
      subst hpeq
      obtain ⟨hk, -, -⟩ := recAt_eq hrec
      rw [PC]
      constructor
      · rintro ⟨-, ⟨-, h'⟩ | ⟨h', -⟩⟩
        · exact Or.inr ⟨rfl, h'⟩
        · omega
      · rintro (h' | ⟨-, h'⟩)
        · have := (PC_bounds c' b c _ h'); omega
        · exact ⟨by omega, Or.inl ⟨Or.inr hk, h'⟩⟩
  | join x y ihx ihy =>
    intro b h hN c p hp1 hp2
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    simp only [NT.size] at hp2 hN
    by_cases hpy : p < b + y.size
    · rw [ihy b hy (by omega) c p hp1 hpy]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | h' | ⟨h', -⟩)
        · exact h'
        · have := PC_bounds x (b + y.size) c p h'; omega
        · omega
    · by_cases hpx : p < b + y.size + x.size
      · rw [ihx (b + y.size) hx (by omega) c p (by omega) hpx]
        rw [PC]
        constructor
        · exact fun h' => Or.inr (Or.inl h')
        · rintro (h' | h' | ⟨h', -⟩)
          · have := PC_bounds y b c p h'; omega
          · exact h'
          · omega
      · have hpeq : p = b + y.size + x.size := by omega
        subst hpeq
        obtain ⟨hk, -, ho⟩ := recAt_eq hrec
        rw [PC]
        constructor
        · rintro ⟨-, ⟨h', -⟩ | ⟨-, h'⟩⟩
          · omega
          · exact Or.inr (Or.inr ⟨rfl, by rw [ho] at h'; exact h'⟩)
        · rintro (h' | h' | ⟨-, h'⟩)
          · have := PC_bounds y b c _ h'; omega
          · have := PC_bounds x (b + y.size) c _ h'; omega
          · exact ⟨by omega, Or.inr ⟨hk, by rw [ho]; exact h'⟩⟩

/-- Reading the canonical layout back gives the tree. -/
lemma ofWord_of_reads {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → ofWord D (b + t.size - 1) = t := by
  intro t
  induction t with
  | leaf =>
    intro b h
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    cases b with
    | zero => simp [NT.size, ofWord_zero]
    | succ b =>
      have : b + 1 + NT.leaf.size - 1 = b + 1 := by simp [NT.size]
      rw [this]
      exact ofWord_leaf (by omega) (by omega) (by omega)
  | intro v c ih =>
    intro b h
    obtain ⟨hc, hrec⟩ := h.intro
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hidx : b + (NT.intro v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    have := ih b hc
    rw [hi'] at this
    rw [hidx, ofWord_intro hk, hv, this]
  | forget v c ih =>
    intro b h
    obtain ⟨hc, hrec⟩ := h.forget
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hidx : b + (NT.forget v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    have := ih b hc
    rw [hi'] at this
    rw [hidx, ofWord_forget hk, hv, this]
  | join x y ihx ihy =>
    intro b h
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    obtain ⟨i, hi⟩ : ∃ i, b + y.size + x.size = i + 1 := ⟨b + y.size + x.size - 1, by omega⟩
    rw [hi] at hrec
    obtain ⟨hk, -, ho⟩ := recAt_eq hrec
    have hidx : b + (NT.join x y).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + y.size + x.size - 1 = i := by omega
    have h1 := ihx (b + y.size) hx
    rw [hi'] at h1
    have h2 := ihy b hy
    rw [hidx, ofWord_join hk (by omega), ho, h1, h2]

/-- The layout half of `NiceDecomposition` for the canonical word. -/
theorem lay_encode {n : ℕ} {t : NT} (hw : t.Wf) (hlt : ∀ u ∈ t.vs, u < n) : Lay n t.encode where
  length_eq := by rw [nodeCount_encode]; exact length_encode t
  nonempty := by rw [nodeCount_encode]; exact size_pos t
  shape := fun i hi => by
    rw [nodeCount_encode] at hi
    exact shape_of_reads t 0 (reads_encode t) hw hlt i (Nat.zero_le _) (by omega)
  parent := fun c hc => by
    rw [nodeCount_encode] at hc
    obtain ⟨p, hp, hu⟩ := PC_existsUnique t 0 c (Nat.zero_le _) (by omega)
    have hN : 0 + t.size ≤ nodeCount t.encode := by rw [nodeCount_encode]; omega
    have hpb := PC_bounds t 0 c p hp
    refine ⟨p, (isChild_iff_PC t 0 (reads_encode t) hN c p (Nat.zero_le _) hpb.2.2).2 hp, fun q hq => ?_⟩
    have hqN := hq.1
    rw [nodeCount_encode] at hqN
    exact hu q ((isChild_iff_PC t 0 (reads_encode t) hN c q (Nat.zero_le _) (by omega)).1 hq)

theorem ofWord_encode (t : NT) : ofWord t.encode (nodeCount t.encode - 1) = t := by
  rw [nodeCount_encode]
  simpa using ofWord_of_reads t 0 (reads_encode t)

/-- Every `NiceDecomposition` word satisfies the layout conditions. -/
theorem lay_of_niceDecomposition {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {D : List ℕ}
    (h : NiceDecomposition G w D) : Lay n D :=
  ⟨h.length_eq, h.nonempty, h.shape, h.parent⟩

end Word

open Word Lax117284.GraphWords in
/-- **Bridge 2 (word side), encode.**  A nice tree decomposition of `G` of width `≤ w` is written as a
`NiceDecomposition` word.  (Used for the *output* of the algorithm.) -/
theorem niceDecomposition_encode {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {t : NT}
    (h : t.IsNiceTD (liftGraph G) (Finset.range n) w) : NiceDecomposition G w t.encode := by
  have hlt : ∀ u ∈ t.vs, u < n := fun u hu => by
    have : t.vs = Finset.range n := h.2.1.verts_eq
    rw [this] at hu; exact Finset.mem_range.1 hu
  have L := lay_encode h.1 hlt
  refine L.niceDecomposition_of_isNiceTD ?_
  rw [ofWord_encode]
  exact h

open Word Lax117284.GraphWords in
/-- **Bridge 2 (word side), parse — corrected.**  `BP2` claimed `t.encode = D`; that is false: a
`NiceDecomposition` word may list the nodes in any topological order (only the first child of a node is forced to be the
node just before it) and may carry arbitrary junk in the unused fields of a record.  What is true, and what the
consumers of the word use, is that the tree `ofWord D (N-1)` read off the word is a nice tree decomposition of `G` of
width `≤ w` with exactly `N` nodes. -/
theorem niceDecomposition_parse {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {D : List ℕ}
    (h : NiceDecomposition G w D) :
    ∃ t : NT, t = ofWord D (nodeCount D - 1) ∧ t.size = nodeCount D ∧
      t.IsNiceTD (liftGraph G) (Finset.range n) w :=
  ⟨_, rfl, (lay_of_niceDecomposition h).size_ofWord_last,
    (lay_of_niceDecomposition h).isNiceTD_ofWord h.covers h.edges h.connected h.width⟩

end Lax117284Proofs.Treewidth.Trees
