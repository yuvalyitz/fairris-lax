import Lax117284Proofs.Lemma14Graph
import Lax117284Proofs.Lemma14_MIS
import Lax117284.Lemma14

/-!
The graph the development of Lemma 14 consumes, built from a numbered instance of
Multicoloured Independent Set in normal form: the `q`'th neighbour of a vertex is the
`q`'th entry of its list of neighbours, and the back-index is the place the vertex occupies
in that neighbour's own list. Regularity is what makes every index below the degree name a
neighbour, and the lists carry no repetition, so the two indices undo each other.
-/

namespace Lax117284Proofs.Lemma14Build

open Lax117284.MulticolouredIndepSet Lax117284.Lemma14 Lax117284Proofs.Lemma14Graph

/-! ### Reading a list at the place of one of its entries -/

theorem getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {a d : α} (h : a ∈ l) :
    l.getD (l.idxOf a) d = a := by
  have hlt := List.idxOf_lt_length_iff.2 h
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

theorem idxOf_getD {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {d : α} (hn : l.Nodup)
    {k : ℕ} (hk : k < l.length) : l.idxOf (l.getD k d) = k := by
  rw [List.getD_eq_getElem _ _ hk]
  exact hn.idxOf_getElem k hk

variable (G : Instance)

/-! ### The neighbour of a number at an index, and the index back -/

/-- The number of the `k`'th neighbour of the vertex numbered `w`. -/
noncomputable def nbrNum (w k : ℕ) : ℕ := (G.nbrs w).getD k 0

/-- The place the vertex numbered `w` occupies in the list of neighbours of its `k`'th
neighbour. -/
noncomputable def revNum (w k : ℕ) : ℕ := (G.nbrs (nbrNum G w k)).idxOf w

theorem nbrNum_mem (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : nbrNum G w k ∈ G.nbrs w := by
  have hlen : k < (G.nbrs w).length := by rw [hreg w hw]; exact hk
  simp only [nbrNum]
  rw [List.getD_eq_getElem _ _ hlen]
  exact List.getElem_mem _

theorem nbrNum_lt (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : nbrNum G w k < G.vertices :=
  ((mem_nbrs G).1 (nbrNum_mem G hreg hw hk)).1

theorem mem_nbrs_nbrNum (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : w ∈ G.nbrs (nbrNum G w k) :=
  mem_nbrs_symm G (nbrNum_mem G hreg hw hk)

theorem revNum_lt (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : revNum G w k < deg G := by
  have hmem := mem_nbrs_nbrNum G hreg hw hk
  have hlt := List.idxOf_lt_length_iff.2 hmem
  rw [hreg _ (nbrNum_lt G hreg hw hk)] at hlt
  exact hlt

theorem nbrNum_revNum (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : nbrNum G (nbrNum G w k) (revNum G w k) = w :=
  getD_idxOf (mem_nbrs_nbrNum G hreg hw hk)

theorem revNum_revNum (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : revNum G (nbrNum G w k) (revNum G w k) = k := by
  have h1 := nbrNum_revNum G hreg hw hk
  have hlen : k < (G.nbrs w).length := by rw [hreg w hw]; exact hk
  show (G.nbrs (nbrNum G (nbrNum G w k) (revNum G w k))).idxOf (nbrNum G w k) = k
  rw [h1]
  exact idxOf_getD (nbrs_nodup G w) hlen

theorem adjAt_nbrNum (hreg : G.Regular (deg G)) {w k : ℕ} (hw : w < G.vertices)
    (hk : k < deg G) : G.adjAt w (nbrNum G w k) = true :=
  ((mem_nbrs G).1 (nbrNum_mem G hreg hw hk)).2

/-! ### The graph of the development -/

/-- The vertex carrying a given number, and a default for numbers naming no vertex. -/
noncomputable def vtxOf (v₀ : Fin G.colours × Fin G.size) (w : ℕ) :
    Fin G.colours × Fin G.size :=
  if h : ∃ u, num G u = w then h.choose else v₀

theorem num_vtxOf (v₀ : Fin G.colours × Fin G.size) {w : ℕ} (h : ∃ u, num G u = w) :
    num G (vtxOf G v₀ w) = w := by
  simp only [vtxOf, dif_pos h]
  exact h.choose_spec

/-- The `q`'th neighbour of `v`. -/
noncomputable def nbr (v : Fin G.colours × Fin G.size) (q : Fin (deg G)) :
    Fin G.colours × Fin G.size := vtxOf G v (nbrNum G (num G v) (q : ℕ))

theorem num_nbr (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) : num G (nbr G v q) = nbrNum G (num G v) (q : ℕ) :=
  num_vtxOf G v (exists_num G (nbrNum_lt G hreg (num_lt G v) q.isLt))

theorem revNum_lt' (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) : revNum G (num G v) (q : ℕ) < deg G :=
  revNum_lt G hreg (num_lt G v) q.isLt

theorem nbr_rev (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) :
    nbr G (nbr G v q) ⟨revNum G (num G v) (q : ℕ), revNum_lt' G hreg v q⟩ = v := by
  refine num_injective G ?_
  rw [num_nbr G hreg, num_nbr G hreg]
  exact nbrNum_revNum G hreg (num_lt G v) q.isLt

theorem revq_rev (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) :
    revNum G (num G (nbr G v q)) (revNum G (num G v) (q : ℕ)) = (q : ℕ) := by
  rw [num_nbr G hreg]
  exact revNum_revNum G hreg (num_lt G v) q.isLt

theorem colour_ne (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) : (nbr G v q).1 ≠ v.1 := by
  have hadj := adjAt_nbrNum G hreg (num_lt G v) q.isLt
  have hne := classOf_ne_of_adjAt G hadj
  rw [classOf_num] at hne
  intro hc
  exact hne (by rw [← num_nbr G hreg v q, classOf_num, hc])

/-- **The graph of Lemma 14's development**, read off a numbered instance in normal
form. -/
noncomputable def mis (hreg : G.Regular (deg G)) : Model.Lemma14.MIS where
  ℓ := G.colours
  n := G.size
  r := deg G
  r_pos := one_le_deg G
  nbr v q := nbr G v q
  revq v q := ⟨revNum G (num G v) (q : ℕ), revNum_lt' G hreg v q⟩
  nbr_rev v q := nbr_rev G hreg v q
  revq_rev v q := Fin.ext (revq_rev G hreg v q)
  colour_ne v q := colour_ne G hreg v q

/-- The adjacency of the development is the adjacency of the graph. -/
theorem mis_adj_iff (hreg : G.Regular (deg G)) (v u : Fin G.colours × Fin G.size) :
    (mis G hreg).Adj v u ↔ G.graph.Adj v u := by
  constructor
  · rintro ⟨q, hq⟩
    refine (adjAt_num G v u).1 ?_
    have : num G u = nbrNum G (num G v) (q : ℕ) := by
      rw [← hq]; exact num_nbr G hreg v q
    rw [this]
    exact adjAt_nbrNum G hreg (num_lt G v) q.isLt
  · intro h
    have hmem : num G u ∈ G.nbrs (num G v) :=
      (mem_nbrs G).2 ⟨num_lt G u, (adjAt_num G v u).2 h⟩
    have hlt := List.idxOf_lt_length_iff.2 hmem
    rw [hreg _ (num_lt G v)] at hlt
    refine ⟨⟨(G.nbrs (num G v)).idxOf (num G u), hlt⟩, ?_⟩
    refine num_injective G ?_
    show num G (nbr G v ⟨(G.nbrs (num G v)).idxOf (num G u), hlt⟩) = num G u
    rw [num_nbr G hreg]
    exact getD_idxOf hmem

/-- **The two questions agree.** -/
theorem mis_hasIndepSet_iff (hreg : G.Regular (deg G)) :
    (mis G hreg).HasIndepSet ↔ G.HasIndepSet := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun i i' h => hf i i' ((mis_adj_iff G hreg _ _).2 h)⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, fun i i' h => hf i i' ((mis_adj_iff G hreg _ _).1 h)⟩

/-! ### The edges, and their places in the list of edges -/

theorem nbr_inj (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    {q q' : Fin (deg G)} (h : nbr G v q = nbr G v q') : q = q' := by
  have h1 : (G.nbrs (num G v)).getD (q : ℕ) 0 = (G.nbrs (num G v)).getD (q' : ℕ) 0 := by
    have hh := congrArg (num G) h
    rw [num_nbr G hreg, num_nbr G hreg] at hh
    exact hh
  have hq : (q : ℕ) < (G.nbrs (num G v)).length := by
    rw [hreg _ (num_lt G v)]; exact q.isLt
  have hq' : (q' : ℕ) < (G.nbrs (num G v)).length := by
    rw [hreg _ (num_lt G v)]; exact q'.isLt
  refine Fin.ext ?_
  rw [← idxOf_getD (d := 0) (nbrs_nodup G (num G v)) hq, h1,
    idxOf_getD (d := 0) (nbrs_nodup G (num G v)) hq']

/-- The pair of numbers an incidence names. -/
noncomputable def incPair (v : Fin G.colours × Fin G.size) (q : Fin (deg G)) : ℕ × ℕ :=
  (num G v, num G (nbr G v q))

theorem incPair_adjAt (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) : G.adjAt (incPair G v q).1 (incPair G v q).2 = true := by
  show G.adjAt (num G v) (num G (nbr G v q)) = true
  rw [num_nbr G hreg]
  exact adjAt_nbrNum G hreg (num_lt G v) q.isLt

theorem incPair_lt_iff (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size)
    (q : Fin (deg G)) :
    (incPair G v q).1 < (incPair G v q).2 ↔ v.1 < (nbr G v q).1 := by
  rw [lt_iff_classOf_lt G (incPair_adjAt G hreg v q)]
  show G.classOf (num G v) < G.classOf (num G (nbr G v q)) ↔ _
  rw [classOf_num, classOf_num]
  exact Fin.lt_def.symm

theorem tail_iff (hreg : G.Regular (deg G)) (x : (mis G hreg).Inc) :
    (mis G hreg).Tail x ↔ (incPair G x.1 x.2).1 < (incPair G x.1 x.2).2 :=
  (incPair_lt_iff G hreg x.1 x.2).symm

theorem incPair_mem (hreg : G.Regular (deg G)) {v : Fin G.colours × Fin G.size}
    {q : Fin (deg G)} (h : (incPair G v q).1 < (incPair G v q).2) :
    incPair G v q ∈ G.edgeList := by
  have hadj := incPair_adjAt G hreg v q
  exact (mem_edgeList G).2
    ⟨(adjAt_lt G hadj).1, (mem_nbrs G).2 ⟨(adjAt_lt G hadj).2, hadj⟩, h⟩

/-- The place an edge occupies in the list of edges. -/
noncomputable def eIdx (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) : ℕ :=
  G.edgeList.idxOf (incPair G e.1.1 e.1.2)

theorem eIdx_lt (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    eIdx G hreg e < G.edgeCount :=
  List.idxOf_lt_length_iff.2 (incPair_mem G hreg ((tail_iff G hreg e.1).1 e.2))

theorem edgeAt_eIdx (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    edgeAt G (eIdx G hreg e) = incPair G e.1.1 e.1.2 :=
  getD_idxOf (incPair_mem G hreg ((tail_iff G hreg e.1).1 e.2))

theorem eIdx_injective (hreg : G.Regular (deg G)) :
    Function.Injective (eIdx G hreg) := by
  intro e e' h
  have hp : incPair G e.1.1 e.1.2 = incPair G e'.1.1 e'.1.2 := by
    rw [← edgeAt_eIdx G hreg e, ← edgeAt_eIdx G hreg e', h]
  have h1 : e.1.1 = e'.1.1 := num_injective G (congrArg Prod.fst hp)
  have h2 : nbr G e.1.1 e.1.2 = nbr G e'.1.1 e'.1.2 :=
    num_injective G (congrArg Prod.snd hp)
  rw [h1] at h2
  exact Subtype.ext (Prod.ext h1 (nbr_inj G hreg _ h2))

theorem eIdx_surjective (hreg : G.Regular (deg G)) {k : ℕ} (hk : k < G.edgeCount) :
    ∃ e : (mis G hreg).Edge, eIdx G hreg e = k := by
  obtain ⟨v, hv⟩ := exists_num G (edgeAt_fst_lt G hk)
  have hmem : (edgeAt G k).2 ∈ G.nbrs (num G v) := by
    rw [hv]; exact edgeAt_mem_nbrs G hk
  have hq : (G.nbrs (num G v)).idxOf (edgeAt G k).2 < deg G := by
    have hh := List.idxOf_lt_length_iff.2 hmem
    rwa [hreg _ (num_lt G v)] at hh
  have hsnd : num G (nbr G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩)
      = (edgeAt G k).2 := by
    rw [num_nbr G hreg]
    exact getD_idxOf hmem
  have hpair : incPair G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩ = edgeAt G k := by
    show (num G v, num G (nbr G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩))
      = edgeAt G k
    rw [hsnd]
    exact Prod.ext hv rfl
  have htail : (mis G hreg).Tail
      (v, ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩) := by
    refine (tail_iff G hreg _).2 ?_
    show (incPair G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩).1
      < (incPair G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩).2
    rw [hpair]
    exact edgeAt_lt G hk
  refine ⟨⟨(v, ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩), htail⟩, ?_⟩
  show G.edgeList.idxOf (incPair G v ⟨(G.nbrs (num G v)).idxOf (edgeAt G k).2, hq⟩) = k
  rw [hpair]
  exact idxOf_getD (edgeList_nodup G) hk

/-- **The edges of the development are the edges of the list**, numbered by their places
in it. -/
noncomputable def edgeEquiv (hreg : G.Regular (deg G)) :
    (mis G hreg).Edge ≃ Fin G.edgeCount :=
  Equiv.ofBijective (fun e => ⟨eIdx G hreg e, eIdx_lt G hreg e⟩)
    ⟨fun e e' h => eIdx_injective G hreg (congrArg Fin.val h),
      fun k => by
        obtain ⟨e, he⟩ := eIdx_surjective G hreg k.isLt
        exact ⟨e, Fin.ext he⟩⟩

theorem card_edge (hreg : G.Regular (deg G)) :
    Fintype.card (mis G hreg).Edge = G.edgeCount := by
  rw [Fintype.card_congr (edgeEquiv G hreg), Fintype.card_fin]

/-! ### The clients and the days of the construction, numbered

The days come in colour blocks of `n` vertex days and a validation day, then the edge days
in the order the edges are listed; the clients are the dummy, the two interaction clients,
one per colour, one per vertex and one per incidence, in that order. -/

@[simp] theorem mis_r (hreg : G.Regular (deg G)) : (mis G hreg).r = deg G := Eq.trans rfl rfl

theorem vtx_fst_lt (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    (v.1 : ℕ) < G.colours := v.1.isLt

theorem vtx_snd_lt (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    (v.2 : ℕ) < G.size := v.2.isLt

theorem col_lt (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ) :
    (i : ℕ) < G.colours := i.isLt

theorem inc_snd_lt (hreg : G.Regular (deg G)) (x : (mis G hreg).Inc) :
    (x.2 : ℕ) < deg G := x.2.isLt

theorem inc_fst_lt (hreg : G.Regular (deg G)) (x : (mis G hreg).Inc) :
    num G x.1 < G.vertices := num_lt G x.1

/-- Reading a number as a place inside a block and the block it lies in. -/
theorem block_ext {s i a i' a' : ℕ} (ha : a < s) (ha' : a' < s)
    (h : i * s + a = i' * s + a') : i = i' ∧ a = a' := by
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) ha
  have h1 : (i * s + a) / s = i := by
    rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt ha, Nat.add_zero]
  have h2 : (i' * s + a') / s = i' := by
    rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt ha', Nat.add_zero]
  have hi : i = i' := by rw [← h1, ← h2, h]
  refine ⟨hi, ?_⟩
  rw [hi] at h
  omega

theorem block_lt {s i a c : ℕ} (ha : a < s) (hi : i < c) : i * s + a < c * s := by
  have h1 : (i + 1) * s ≤ c * s := Nat.mul_le_mul_right _ hi
  have h2 : (i + 1) * s = i * s + s := by ring
  omega

/-! #### The days -/

/-- The number of a day. -/
noncomputable def dayNum (hreg : G.Regular (deg G)) : (mis G hreg).Day → ℕ
  | Sum.inl v => (v.1 : ℕ) * (G.size + 1) + (v.2 : ℕ)
  | Sum.inr (Sum.inl i) => (i : ℕ) * (G.size + 1) + G.size
  | Sum.inr (Sum.inr e) => G.colours * (G.size + 1) + eIdx G hreg e

theorem dV_lt (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    dayNum G hreg (Sum.inl v) < G.colours * (G.size + 1) := by
  have h1 := vtx_fst_lt G hreg v
  have h2 := vtx_snd_lt G hreg v
  exact block_lt (by omega) h1

theorem dW_lt (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ) :
    dayNum G hreg (Sum.inr (Sum.inl i)) < G.colours * (G.size + 1) :=
  block_lt (by omega) (col_lt G hreg i)

theorem dE_ge (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    G.colours * (G.size + 1) ≤ dayNum G hreg (Sum.inr (Sum.inr e)) := by
  simp only [dayNum]; omega

theorem dE_lt (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    dayNum G hreg (Sum.inr (Sum.inr e)) < dayCount G := by
  have h := eIdx_lt G hreg e
  have hd : dayCount G = G.colours * (G.size + 1) + G.edgeCount := rfl
  simp only [dayNum]
  omega

theorem dayNum_lt (hreg : G.Regular (deg G)) (i : (mis G hreg).Day) :
    dayNum G hreg i < dayCount G := by
  have hd : dayCount G = G.colours * (G.size + 1) + G.edgeCount := rfl
  rcases i with v | i | e
  · have := dV_lt G hreg v; omega
  · have := dW_lt G hreg i; omega
  · exact dE_lt G hreg e

theorem dayNum_injective (hreg : G.Regular (deg G)) :
    Function.Injective (dayNum G hreg) := by
  rintro (v | i | e) (v' | i' | e') h
  · simp only [dayNum] at h
    obtain ⟨h1, h2⟩ := block_ext (by have := vtx_snd_lt G hreg v; omega)
      (by have := vtx_snd_lt G hreg v'; omega) h
    exact congrArg Sum.inl (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · exfalso
    simp only [dayNum] at h
    obtain ⟨-, h2⟩ := block_ext (by have := vtx_snd_lt G hreg v; omega) (by omega) h
    have := vtx_snd_lt G hreg v
    omega
  · exfalso
    have := dV_lt G hreg v
    have := dE_ge G hreg e'
    omega
  · exfalso
    simp only [dayNum] at h
    obtain ⟨-, h2⟩ := block_ext (by omega) (by have := vtx_snd_lt G hreg v'; omega) h
    have := vtx_snd_lt G hreg v'
    omega
  · simp only [dayNum] at h
    obtain ⟨h1, -⟩ := block_ext (by omega) (by omega) h
    exact congrArg (fun a => Sum.inr (Sum.inl a)) (Fin.ext h1)
  · exfalso
    have := dW_lt G hreg i
    have := dE_ge G hreg e'
    omega
  · exfalso
    have := dV_lt G hreg v'
    have := dE_ge G hreg e
    omega
  · exfalso
    have := dW_lt G hreg i'
    have := dE_ge G hreg e
    omega
  · simp only [dayNum] at h
    exact congrArg (fun a => Sum.inr (Sum.inr a)) (eIdx_injective G hreg (by omega))

theorem card_day (hreg : G.Regular (deg G)) :
    Fintype.card (mis G hreg).Day = dayCount G := by
  have hd : dayCount G = G.colours * (G.size + 1) + G.edgeCount := rfl
  have hexp : G.colours * (G.size + 1) = G.colours * G.size + G.colours := by ring
  have h1 : Fintype.card (mis G hreg).Day
      = Fintype.card (mis G hreg).Vtx
        + (Fintype.card (Fin (mis G hreg).ℓ) + Fintype.card (mis G hreg).Edge) := by
    rw [Fintype.card_sum, Fintype.card_sum]
  have h2 : Fintype.card (mis G hreg).Vtx = G.colours * G.size := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; rfl
  have h3 : Fintype.card (Fin (mis G hreg).ℓ) = G.colours := by
    rw [Fintype.card_fin]; rfl
  rw [h1, h2, h3, card_edge G hreg]
  omega

/-- **The days of the development are the numbered days.** -/
noncomputable def dayEquiv (hreg : G.Regular (deg G)) :
    (mis G hreg).Day ≃ Fin (dayCount G) :=
  Equiv.ofBijective (fun i => ⟨dayNum G hreg i, dayNum_lt G hreg i⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => dayNum_injective G hreg (congrArg Fin.val h),
        by rw [card_day G hreg, Fintype.card_fin]⟩)

/-! #### The clients -/

/-- The number of a client. -/
noncomputable def clientNum (hreg : G.Regular (deg G)) : (mis G hreg).Client → ℕ
  | Sum.inl v => vtxId G (num G v)
  | Sum.inr (Sum.inl i) => selId (i : ℕ)
  | Sum.inr (Sum.inr (Sum.inl x)) => incId G (num G x.1) (x.2 : ℕ)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl b))) => if b then 1 else 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 0

theorem cv_range (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    3 + G.colours ≤ clientNum G hreg (Sum.inl v) ∧
      clientNum G hreg (Sum.inl v) < 3 + G.colours + G.vertices := by
  have := num_lt G v
  simp only [clientNum, vtxId]
  omega

theorem cs_range (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ) :
    3 ≤ clientNum G hreg (Sum.inr (Sum.inl i)) ∧
      clientNum G hreg (Sum.inr (Sum.inl i)) < 3 + G.colours := by
  have := col_lt G hreg i
  simp only [clientNum, selId]
  omega

theorem ce_range (hreg : G.Regular (deg G)) (x : (mis G hreg).Inc) :
    3 + G.colours + G.vertices ≤ clientNum G hreg (Sum.inr (Sum.inr (Sum.inl x))) ∧
      clientNum G hreg (Sum.inr (Sum.inr (Sum.inl x))) < clientCount G := by
  have hc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  have := block_lt (s := deg G) (i := num G x.1) (a := (x.2 : ℕ)) (c := G.vertices)
    (inc_snd_lt G hreg x) (inc_fst_lt G hreg x)
  simp only [clientNum, incId]
  omega

theorem ci_range (hreg : G.Regular (deg G)) (b : Bool) :
    1 ≤ clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inl b)))) ∧
      clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inl b)))) ≤ 2 := by
  cases b <;> simp [clientNum]

theorem c0_eq (hreg : G.Regular (deg G)) (u : Unit) :
    clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))) = 0 := rfl

theorem clientNum_lt (hreg : G.Regular (deg G)) (c : (mis G hreg).Client) :
    clientNum G hreg c < clientCount G := by
  have hc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  rcases c with v | i | x | b | u
  · have := (cv_range G hreg v).2
    have := Nat.zero_le (G.vertices * deg G)
    omega
  · have := (cs_range G hreg i).2
    have := Nat.zero_le (G.vertices * deg G)
    omega
  · exact (ce_range G hreg x).2
  · have := (ci_range G hreg b).2
    omega
  · rw [c0_eq]
    omega

theorem clientNum_injective (hreg : G.Regular (deg G)) :
    Function.Injective (clientNum G hreg) := by
  rintro (v | i | x | b | u) (v' | i' | x' | b' | u') h
  · simp only [clientNum, vtxId] at h
    exact congrArg Sum.inl (num_injective G (by omega))
  · exfalso; have := (cv_range G hreg v).1; have := (cs_range G hreg i').2; omega
  · exfalso; have := (cv_range G hreg v).2; have := (ce_range G hreg x').1; omega
  · exfalso; have := (cv_range G hreg v).1; have := (ci_range G hreg b').2; omega
  · exfalso; have := (cv_range G hreg v).1; rw [c0_eq] at h; omega
  · exfalso; have := (cs_range G hreg i).2; have := (cv_range G hreg v').1; omega
  · simp only [clientNum, selId] at h
    exact congrArg (fun a => Sum.inr (Sum.inl a)) (Fin.ext (by omega))
  · exfalso; have := (cs_range G hreg i).2; have := (ce_range G hreg x').1
    have := Nat.zero_le G.vertices; omega
  · exfalso; have := (cs_range G hreg i).1; have := (ci_range G hreg b').2; omega
  · exfalso; have := (cs_range G hreg i).1; rw [c0_eq] at h; omega
  · exfalso; have := (ce_range G hreg x).1; have := (cv_range G hreg v').2; omega
  · exfalso; have := (ce_range G hreg x).1; have := (cs_range G hreg i').2
    have := Nat.zero_le G.vertices; omega
  · simp only [clientNum, incId] at h
    obtain ⟨h1, h2⟩ := block_ext (s := deg G) (i := num G x.1) (a := (x.2 : ℕ))
      (i' := num G x'.1) (a' := (x'.2 : ℕ)) (inc_snd_lt G hreg x) (inc_snd_lt G hreg x')
      (by omega)
    exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inl a)))
      (Prod.ext (num_injective G h1) (Fin.ext h2))
  · exfalso; have := (ce_range G hreg x).1; have := (ci_range G hreg b').2
    have := Nat.zero_le G.vertices; have := Nat.zero_le G.colours; omega
  · exfalso; have := (ce_range G hreg x).1; rw [c0_eq] at h; omega
  · exfalso; have := (ci_range G hreg b).2; have := (cv_range G hreg v').1; omega
  · exfalso; have := (ci_range G hreg b).2; have := (cs_range G hreg i').1; omega
  · exfalso; have := (ci_range G hreg b).2; have := (ce_range G hreg x').1
    have := Nat.zero_le G.vertices; have := Nat.zero_le G.colours; omega
  · simp only [clientNum] at h
    refine congrArg (fun a => Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) ?_
    revert h; cases b <;> cases b' <;> simp
  · exfalso; have := (ci_range G hreg b).1; rw [c0_eq] at h; omega
  · exfalso; have := (cv_range G hreg v').1; rw [c0_eq] at h; omega
  · exfalso; have := (cs_range G hreg i').1; rw [c0_eq] at h; omega
  · exfalso; have := (ce_range G hreg x').1; rw [c0_eq] at h; omega
  · exfalso; have := (ci_range G hreg b').1; rw [c0_eq] at h; omega
  · exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inr (Sum.inr a))))
      (Subsingleton.elim u u')

theorem card_client (hreg : G.Regular (deg G)) :
    Fintype.card (mis G hreg).Client = clientCount G := by
  have hc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  have hv : G.vertices = G.colours * G.size := rfl
  rw [hv] at hc
  have h1 : Fintype.card (mis G hreg).Client
      = Fintype.card (mis G hreg).Vtx
        + (Fintype.card (Fin (mis G hreg).ℓ)
          + (Fintype.card (mis G hreg).Inc
            + (Fintype.card Bool + Fintype.card Unit))) := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_sum]
  have h2 : Fintype.card (mis G hreg).Vtx = G.colours * G.size := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; rfl
  have h3 : Fintype.card (Fin (mis G hreg).ℓ) = G.colours := by
    rw [Fintype.card_fin]; rfl
  have h4 : Fintype.card (mis G hreg).Inc = G.colours * G.size * deg G := by
    rw [Fintype.card_prod, h2, Fintype.card_fin]; rfl
  rw [h1, h2, h3, h4, Fintype.card_bool, Fintype.card_unit]
  omega

/-- **The clients of the development are the numbered clients.** -/
noncomputable def clientEquiv (hreg : G.Regular (deg G)) :
    (mis G hreg).Client ≃ Fin (clientCount G) :=
  Equiv.ofBijective (fun c => ⟨clientNum G hreg c, clientNum_lt G hreg c⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => clientNum_injective G hreg (congrArg Fin.val h),
        by rw [card_client G hreg, Fintype.card_fin]⟩)

end Lax117284Proofs.Lemma14Build
