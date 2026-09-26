import Lax117284.MulticolouredIndepSet
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

/-!
The numbered graph of Multicoloured Independent Set, read as the graph the development of
Lemma 14 consumes: a vertex is a pair, its number is `in + a`, the neighbours of a vertex
are listed without repetition in increasing order, and an edge appears in the list of edges
exactly once, oriented from the smaller number — that is, from the smaller class.
-/

namespace Lax117284Proofs.Lemma14Graph

open Lax117284.MulticolouredIndepSet

variable (G : Instance)

/-! ### Vertices and their numbers -/

/-- The number of the vertex `(i, a)`. -/
def num (v : Fin G.colours × Fin G.size) : ℕ := (v.1 : ℕ) * G.size + (v.2 : ℕ)

theorem size_pos_of_vtx (v : Fin G.colours × Fin G.size) : 0 < G.size :=
  lt_of_le_of_lt (Nat.zero_le _) v.2.isLt

theorem num_lt (v : Fin G.colours × Fin G.size) : num G v < G.vertices := by
  have h1 : ((v.1 : ℕ) + 1) * G.size ≤ G.colours * G.size :=
    Nat.mul_le_mul_right _ v.1.isLt
  have h2 : ((v.1 : ℕ) + 1) * G.size = (v.1 : ℕ) * G.size + G.size := by ring
  have h3 := v.2.isLt
  have h4 : G.vertices = G.colours * G.size := rfl
  simp only [num]
  omega

@[simp] theorem classOf_num (v : Fin G.colours × Fin G.size) :
    G.classOf (num G v) = (v.1 : ℕ) := by
  have hs := size_pos_of_vtx G v
  simp only [Instance.classOf, num]
  rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt v.2.isLt, Nat.add_zero]

@[simp] theorem indexOf_num (v : Fin G.colours × Fin G.size) :
    G.indexOf (num G v) = (v.2 : ℕ) := by
  simp only [Instance.indexOf, num]
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.2.isLt]

theorem num_injective : Function.Injective (num G) := by
  intro v u h
  have h1 : (v.1 : ℕ) = (u.1 : ℕ) := by
    have := congrArg G.classOf h; simpa using this
  have h2 : (v.2 : ℕ) = (u.2 : ℕ) := by
    have := congrArg G.indexOf h; simpa using this
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- Every number below `ℓn` is the number of a vertex. -/
theorem exists_num {w : ℕ} (hw : w < G.vertices) : ∃ v, num G v = w := by
  have hs : 0 < G.size := by
    rcases Nat.eq_zero_or_pos G.size with h0 | h0
    · exfalso
      have : G.vertices = G.colours * G.size := rfl
      rw [h0, Nat.mul_zero] at this
      omega
    · exact h0
  have hv : G.vertices = G.colours * G.size := rfl
  have hdiv : w / G.size < G.colours := (Nat.div_lt_iff_lt_mul hs).2 (by omega)
  refine ⟨(⟨w / G.size, hdiv⟩, ⟨w % G.size, Nat.mod_lt _ hs⟩), ?_⟩
  simp only [num]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod w G.size

/-! ### Adjacency, read off the numbers -/

theorem adjAt_num (v u : Fin G.colours × Fin G.size) :
    G.adjAt (num G v) (num G u) = true ↔ G.graph.Adj v u := by
  classical
  have hv := num_lt G v
  have hu := num_lt G u
  simp only [Instance.adjAt, dif_pos (And.intro hv hu), decide_eq_true_eq]
  have key : ∀ a b : Fin G.colours × Fin G.size, a = v → b = u →
      (G.graph.Adj a b ↔ G.graph.Adj v u) := by rintro a b rfl rfl; exact Iff.rfl
  refine key _ _ ?_ ?_
  · exact Prod.ext (Fin.ext (classOf_num G v)) (Fin.ext (indexOf_num G v))
  · exact Prod.ext (Fin.ext (classOf_num G u)) (Fin.ext (indexOf_num G u))

theorem adjAt_eq_false_of_ge {w w' : ℕ} (h : ¬ (w < G.vertices ∧ w' < G.vertices)) :
    G.adjAt w w' = false := by
  classical
  simp only [Instance.adjAt, dif_neg h]

theorem adjAt_lt {w w' : ℕ} (h : G.adjAt w w' = true) : w < G.vertices ∧ w' < G.vertices := by
  by_contra hc
  rw [adjAt_eq_false_of_ge G hc] at h
  exact Bool.noConfusion h

theorem adjAt_symm {w w' : ℕ} (h : G.adjAt w w' = true) : G.adjAt w' w = true := by
  obtain ⟨hw, hw'⟩ := adjAt_lt G h
  obtain ⟨v, rfl⟩ := exists_num G hw
  obtain ⟨u, rfl⟩ := exists_num G hw'
  exact (adjAt_num G u v).2 ((adjAt_num G v u).1 h).symm

theorem adjAt_irrefl (w : ℕ) : G.adjAt w w = false := by
  by_contra hc
  have h : G.adjAt w w = true := by
    cases hb : G.adjAt w w
    · exact absurd hb hc
    · rfl
  obtain ⟨hw, -⟩ := adjAt_lt G h
  obtain ⟨v, rfl⟩ := exists_num G hw
  exact G.graph.irrefl ((adjAt_num G v v).1 h)

/-- Adjacent vertices lie in different classes, hence have different numbers. -/
theorem classOf_ne_of_adjAt {w w' : ℕ} (h : G.adjAt w w' = true) :
    G.classOf w ≠ G.classOf w' := by
  obtain ⟨hw, hw'⟩ := adjAt_lt G h
  obtain ⟨v, rfl⟩ := exists_num G hw
  obtain ⟨u, rfl⟩ := exists_num G hw'
  have := G.adj_colour_ne _ _ ((adjAt_num G v u).1 h)
  simpa using fun hc => this (Fin.ext hc)

/-! ### The list of neighbours -/

theorem mem_nbrs {w w' : ℕ} : w' ∈ G.nbrs w ↔ w' < G.vertices ∧ G.adjAt w w' = true := by
  classical
  simp [Instance.nbrs, List.mem_filter, List.mem_range]

theorem nbrs_nodup (w : ℕ) : (G.nbrs w).Nodup := by
  classical
  exact (List.nodup_range).filter _

theorem mem_nbrs_symm {w w' : ℕ} (h : w' ∈ G.nbrs w) : w ∈ G.nbrs w' := by
  obtain ⟨-, hadj⟩ := (mem_nbrs G).1 h
  exact (mem_nbrs G).2 ⟨(adjAt_lt G hadj).1, adjAt_symm G hadj⟩

theorem not_mem_nbrs_self (w : ℕ) : w ∉ G.nbrs w := by
  intro h
  have := ((mem_nbrs G).1 h).2
  rw [adjAt_irrefl G w] at this
  exact Bool.noConfusion this

/-! ### The list of edges -/

theorem mem_edgeList {e : ℕ × ℕ} :
    e ∈ G.edgeList ↔ e.1 < G.vertices ∧ e.2 ∈ G.nbrs e.1 ∧ e.1 < e.2 := by
  classical
  simp only [Instance.edgeList, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, w', ⟨hw', hlt⟩, rfl⟩
    exact ⟨hw, hw', hlt⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨e.1, h1, e.2, ⟨h2, h3⟩, rfl⟩

theorem edgeList_nodup : G.edgeList.Nodup := by
  classical
  refine List.nodup_flatMap.2 ⟨fun w _ => ?_, ?_⟩
  · exact List.Nodup.map (fun a b h => by simpa using h) ((nbrs_nodup G w).filter _)
  · refine List.Pairwise.imp (fun {a b} (hab : a ≠ b) => ?_) List.nodup_range
    intro x hxa hxb
    simp only [List.mem_map] at hxa hxb
    obtain ⟨p, -, rfl⟩ := hxa
    obtain ⟨q, -, hq⟩ := hxb
    exact hab (congrArg Prod.fst hq).symm

/-- The `k`'th edge. -/
noncomputable def edgeAt (k : ℕ) : ℕ × ℕ := G.edgeList.getD k (0, 0)

theorem edgeAt_eq_getElem {k : ℕ} (hk : k < G.edgeCount) :
    edgeAt G k = G.edgeList[k]'hk := by
  simp only [edgeAt]
  rw [List.getD_eq_getElem _ _ hk]

theorem edgeAt_mem {k : ℕ} (hk : k < G.edgeCount) : edgeAt G k ∈ G.edgeList := by
  rw [edgeAt_eq_getElem G hk]
  exact List.getElem_mem hk

theorem edgeAt_lt {k : ℕ} (hk : k < G.edgeCount) : (edgeAt G k).1 < (edgeAt G k).2 :=
  ((mem_edgeList G).1 (edgeAt_mem G hk)).2.2

theorem edgeAt_mem_nbrs {k : ℕ} (hk : k < G.edgeCount) :
    (edgeAt G k).2 ∈ G.nbrs (edgeAt G k).1 :=
  ((mem_edgeList G).1 (edgeAt_mem G hk)).2.1

theorem edgeAt_fst_lt {k : ℕ} (hk : k < G.edgeCount) : (edgeAt G k).1 < G.vertices :=
  ((mem_edgeList G).1 (edgeAt_mem G hk)).1

/-! ### The numbering orders the classes

An edge of the numbered graph runs from the smaller number to the larger exactly when it
runs from the smaller class to the larger, which is the orientation the source fixes. -/

theorem size_pos_of_lt_vertices {w : ℕ} (hw : w < G.vertices) : 0 < G.size := by
  rcases Nat.eq_zero_or_pos G.size with h0 | h0
  · exfalso
    have hv : G.vertices = G.colours * G.size := rfl
    rw [h0, Nat.mul_zero] at hv
    omega
  · exact h0

theorem lt_of_classOf_lt {w w' : ℕ} (hw : w < G.vertices) (hw' : w' < G.vertices)
    (h : G.classOf w < G.classOf w') : w < w' := by
  have hs := size_pos_of_lt_vertices G hw
  have e1 := Nat.div_add_mod w G.size
  have e2 := Nat.div_add_mod w' G.size
  have hm : w % G.size < G.size := Nat.mod_lt _ hs
  simp only [Instance.classOf] at h
  have hle : (w / G.size + 1) * G.size ≤ w' / G.size * G.size := Nat.mul_le_mul_right _ h
  have hexp : (w / G.size + 1) * G.size = G.size * (w / G.size) + G.size := by ring
  have hexp2 : w' / G.size * G.size = G.size * (w' / G.size) := by ring
  omega

theorem lt_iff_classOf_lt {w w' : ℕ} (h : G.adjAt w w' = true) :
    w < w' ↔ G.classOf w < G.classOf w' := by
  obtain ⟨hw, hw'⟩ := adjAt_lt G h
  have hne := classOf_ne_of_adjAt G h
  refine ⟨fun hlt => ?_, fun h1 => lt_of_classOf_lt G hw hw' h1⟩
  rcases Nat.lt_trichotomy (G.classOf w) (G.classOf w') with h1 | h1 | h1
  · exact h1
  · exact absurd h1 hne
  · exact absurd (lt_of_classOf_lt G hw' hw h1) (by omega)

/-! ### The handshake count

Each edge is one of the two ordered incidences that carry it, and on a regular graph the
ordered incidences number `ℓn · r`. The source leaves the resulting bound `ℓr ≤ |E|/2`
implicit; it is what makes the incidence check of Lemma 14 possible, and it is where four
vertices per class enter. -/

/-- Every ordered incidence: a vertex together with one of its neighbours. -/
noncomputable def incList : List (ℕ × ℕ) :=
  (List.range G.vertices).flatMap fun w => (G.nbrs w).map (w, ·)

theorem mem_incList {e : ℕ × ℕ} :
    e ∈ incList G ↔ e.1 < G.vertices ∧ e.2 ∈ G.nbrs e.1 := by
  simp only [incList, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨w, hw, w', hw', rfl⟩
    exact ⟨hw, hw'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.1, h1, e.2, h2, rfl⟩

theorem incList_nodup : (incList G).Nodup := by
  refine List.nodup_flatMap.2 ⟨fun w _ => ?_, ?_⟩
  · exact List.Nodup.map (fun a b h => by simpa using h) (nbrs_nodup G w)
  · refine List.Pairwise.imp (fun {a b} (hab : a ≠ b) => ?_) List.nodup_range
    intro x hxa hxb
    simp only [List.mem_map] at hxa hxb
    obtain ⟨p, -, rfl⟩ := hxa
    obtain ⟨q, -, hq⟩ := hxb
    exact hab (congrArg Prod.fst hq).symm

theorem incList_length {r : ℕ} (hreg : G.Regular r) :
    (incList G).length = G.vertices * r := by
  have h : ∀ w ∈ List.range G.vertices, ((G.nbrs w).map (w, ·)).length = r := by
    intro w hw
    rw [List.length_map]
    exact hreg w (List.mem_range.1 hw)
  rw [incList, List.length_flatMap, List.map_congr_left h, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

/-- The incidences oriented from the smaller number are the edges. -/
theorem up_length : ((incList G).filter fun e => decide (e.1 < e.2)).length = G.edgeCount := by
  refine Nat.le_antisymm ?_ ?_
  · refine (((incList_nodup G).filter _).subperm (fun e he => ?_)).length_le
    rw [List.mem_filter] at he
    obtain ⟨h1, h2⟩ := he
    rw [decide_eq_true_eq] at h2
    exact (mem_edgeList G).2 ⟨((mem_incList G).1 h1).1, ((mem_incList G).1 h1).2, h2⟩
  · refine ((edgeList_nodup G).subperm (fun e he => ?_)).length_le
    obtain ⟨h1, h2, h3⟩ := (mem_edgeList G).1 he
    rw [List.mem_filter]
    exact ⟨(mem_incList G).2 ⟨h1, h2⟩, by simpa using h3⟩

/-- …and so are those oriented from the larger, once swapped. -/
theorem down_length :
    ((incList G).filter fun e => !decide (e.1 < e.2)).length = G.edgeCount := by
  have hmap : (((incList G).filter fun e => !decide (e.1 < e.2)).map Prod.swap).length
      = ((incList G).filter fun e => !decide (e.1 < e.2)).length := List.length_map _
  rw [← hmap]
  refine Nat.le_antisymm ?_ ?_
  · refine ((List.Nodup.map Prod.swap_injective ((incList_nodup G).filter _)).subperm
      (fun x hx => ?_)).length_le
    rw [List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [List.mem_filter] at he
    obtain ⟨h1, h2⟩ := he
    obtain ⟨hv, hn⟩ := (mem_incList G).1 h1
    have hne : e.2 ≠ e.1 := fun hc => not_mem_nbrs_self G e.1 (hc ▸ hn)
    have hlt : e.2 < e.1 := by
      have : ¬ (e.1 < e.2) := by simpa using h2
      omega
    exact (mem_edgeList G).2
      ⟨((mem_nbrs G).1 hn).1, mem_nbrs_symm G hn, hlt⟩
  · refine ((edgeList_nodup G).subperm (fun x hx => ?_)).length_le
    obtain ⟨h1, h2, h3⟩ := (mem_edgeList G).1 hx
    refine List.mem_map.2 ⟨x.swap, ?_, Prod.swap_swap x⟩
    rw [List.mem_filter]
    refine ⟨(mem_incList G).2 ⟨((mem_nbrs G).1 h2).1, mem_nbrs_symm G h2⟩, ?_⟩
    simp only [Prod.fst_swap, Prod.snd_swap, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not]
    omega

/-- **The handshake count**: twice the number of edges is the number of ordered
incidences. -/
theorem handshake {r : ℕ} (hreg : G.Regular r) :
    2 * G.edgeCount = G.vertices * r := by
  have h := List.length_eq_length_filter_add (l := incList G) (fun e => decide (e.1 < e.2))
  rw [incList_length G hreg, up_length G, down_length G] at h
  omega

/-- **The bound the source leaves implicit**: with four vertices per class the edge days
incident to a multicoloured independent set do not exhaust one interaction client. -/
theorem balance {r : ℕ} (hreg : G.Regular r) (hsize : 4 ≤ G.size) :
    G.colours * r ≤ G.edgeCount / 2 := by
  have hh := handshake G hreg
  have hv : G.vertices = G.colours * G.size := rfl
  rw [hv] at hh
  have h1 : G.colours * 4 ≤ G.colours * G.size := Nat.mul_le_mul_left _ hsize
  have h2 : G.colours * 4 * r ≤ G.colours * G.size * r :=
    Nat.mul_le_mul_right _ h1
  have h3 : G.colours * 4 * r = 4 * (G.colours * r) := by ring
  omega

end Lax117284Proofs.Lemma14Graph
