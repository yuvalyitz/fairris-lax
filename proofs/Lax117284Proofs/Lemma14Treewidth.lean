import Lax117284Proofs.ParentTree
import Lax117284Proofs.Lemma14Layout
import Lax117284Proofs.Lemma14Build
import Lax117284.Lemma14

/-!
The overall conflict graph of Lemma 14's instance has treewidth at most four, whatever the
graph it was built from. The decomposition is the source's: a root bag `{c₀, c⁺, c⁻}`, a bag
with the selection client of a colour below it, a bag with a vertex client and the selection
client of its colour below that, and a bag with a vertex client and one of its incidence
clients below that. Everything the conflicts of the instance can be is read off the layout:
the dummy client and the two interaction clients meet every client, and apart from those two
kinds of edge the only conflicts are between a vertex client and the selection client of its
colour, and between a vertex client and one of its own incidence clients.
-/

namespace Lax117284Proofs.Lemma14Treewidth

open Lax117284.MulticolouredIndepSet Lax117284.Lemma14 Lax117284Proofs.Lemma14Layout
open Lax117284Proofs.Lemma14Graph

variable (G : Instance)

/-! ### The nodes of the decomposition -/

/-- The root, one node per colour, one per vertex, and one per vertex together with a
neighbour index. -/
abbrev Node : Type :=
  Unit ⊕ (Fin G.colours ⊕ (Fin G.vertices ⊕ (Fin G.vertices × Fin (deg G))))

theorem size_pos_of_vertex (w : Fin G.vertices) : 0 < G.size :=
  size_pos_of_lt_vertices G w.isLt

theorem classOf_lt (w : Fin G.vertices) : G.classOf w < G.colours := by
  have hs := size_pos_of_vertex G w
  have hw := w.isLt
  simp only [Instance.classOf]
  exact (Nat.div_lt_iff_lt_mul hs).2 hw

/-- The node above a node. -/
def par : Node G → Node G
  | Sum.inl _ => Sum.inl ()
  | Sum.inr (Sum.inl _) => Sum.inl ()
  | Sum.inr (Sum.inr (Sum.inl w)) => Sum.inr (Sum.inl ⟨G.classOf w, classOf_lt G w⟩)
  | Sum.inr (Sum.inr (Sum.inr (w, _))) => Sum.inr (Sum.inr (Sum.inl w))

/-- The depth of a node. -/
def depth : Node G → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

theorem depth_par (v : Node G) (hv : v ≠ Sum.inl ()) : depth G (par G v) < depth G v := by
  rcases v with u | i | w | ⟨w, q⟩
  · exact absurd rfl hv
  · simp [par, depth]
  · simp [par, depth]
  · simp [par, depth]

theorem isTree : (ParentTree.graph (Sum.inl () : Node G) (par G)).IsTree :=
  ParentTree.isTree (depth := depth G) (depth_par G)

/-! ### The bags, as sets of client numbers -/

/-- The client numbers in a node's bag. -/
noncomputable def own : Node G → Finset ℕ
  | Sum.inl _ => {0, 1, 2}
  | Sum.inr (Sum.inl i) => {0, 1, 2, selId (i : ℕ)}
  | Sum.inr (Sum.inr (Sum.inl w)) => {0, 1, 2, vtxId G (w : ℕ), selId (G.classOf w)}
  | Sum.inr (Sum.inr (Sum.inr (w, q))) => {0, 1, 2, vtxId G (w : ℕ), incId G (w : ℕ) (q : ℕ)}

theorem card_own_le (n : Node G) : (own G n).card ≤ 5 := by
  rcases n with u | i | w | ⟨w, q⟩ <;> simp only [own]
  · exact le_trans (Finset.card_le_three) (by omega)
  · exact le_trans (Finset.card_le_four) (by omega)
  · exact Finset.card_le_five
  · exact Finset.card_le_five

theorem small_mem_own (n : Node G) {c : ℕ} (hc : c < 3) : c ∈ own G n := by
  have : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases n with u | i | w | ⟨w, q⟩ <;> simp only [own] <;> rcases this with rfl | rfl | rfl <;> simp

/-- The bag of a node, as a set of clients. -/
noncomputable def bag (n : Node G) : Finset (Fin (clientCount G)) :=
  Finset.univ.filter fun c => (c : ℕ) ∈ own G n

theorem mem_bag {n : Node G} {c : Fin (clientCount G)} : c ∈ bag G n ↔ (c : ℕ) ∈ own G n := by
  simp [bag]

theorem card_bag_le (n : Node G) : (bag G n).card ≤ 4 + 1 := by
  have h : (bag G n).card ≤ (own G n).card := by
    refine Finset.card_le_card_of_injOn (fun c => (c : ℕ)) (fun c hc => ?_)
      (fun a _ b _ h => Fin.ext h)
    exact (mem_bag G).1 hc
  have := card_own_le G n
  omega

/-! ### Membership in a bag, node by node -/

theorem mem_own_root {c : ℕ} : c ∈ own G (Sum.inl ()) ↔ c = 0 ∨ c = 1 ∨ c = 2 := by
  simp [own]

theorem mem_own_colour (i : Fin G.colours) {c : ℕ} :
    c ∈ own G (Sum.inr (Sum.inl i)) ↔ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = selId (i : ℕ) := by
  simp [own]

theorem mem_own_vertex (w : Fin G.vertices) {c : ℕ} :
    c ∈ own G (Sum.inr (Sum.inr (Sum.inl w))) ↔
      c = 0 ∨ c = 1 ∨ c = 2 ∨ c = vtxId G (w : ℕ) ∨ c = selId (G.classOf w) := by
  simp [own]

theorem mem_own_slot (w : Fin G.vertices) (q : Fin (deg G)) {c : ℕ} :
    c ∈ own G (Sum.inr (Sum.inr (Sum.inr (w, q)))) ↔
      c = 0 ∨ c = 1 ∨ c = 2 ∨ c = vtxId G (w : ℕ) ∨ c = incId G (w : ℕ) (q : ℕ) := by
  simp [own]

/-- A client number of the last kind, read as a vertex and a neighbour index. -/
theorem decode_inc {c : ℕ} (hc : c < clientCount G) (h : 3 + G.colours + G.vertices ≤ c) :
    ∃ (w : Fin G.vertices) (q : Fin (deg G)), incId G (w : ℕ) (q : ℕ) = c := by
  have hd : 0 < deg G := one_le_deg G
  have hcc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  have hlt : (c - (3 + G.colours + G.vertices)) / deg G < G.vertices :=
    (Nat.div_lt_iff_lt_mul hd).2 (by omega)
  refine ⟨⟨(c - (3 + G.colours + G.vertices)) / deg G, hlt⟩,
    ⟨(c - (3 + G.colours + G.vertices)) % deg G, Nat.mod_lt _ hd⟩, ?_⟩
  have := Nat.div_add_mod (c - (3 + G.colours + G.vertices)) (deg G)
  simp only [incId]
  rw [Nat.mul_comm] at this
  omega

theorem exists_own {c : ℕ} (hc : c < clientCount G) : ∃ n : Node G, c ∈ own G n := by
  have hcc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  by_cases h1 : c < 3
  · exact ⟨Sum.inl (), small_mem_own G _ h1⟩
  by_cases h2 : c < 3 + G.colours
  · refine ⟨Sum.inr (Sum.inl ⟨c - 3, by omega⟩), (mem_own_colour G _).2 ?_⟩
    simp only [selId]; omega
  by_cases h3 : c < 3 + G.colours + G.vertices
  · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨c - (3 + G.colours), by omega⟩)),
      (mem_own_vertex G _).2 (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    simp only [vtxId]; omega
  · obtain ⟨w, q, hwq⟩ := decode_inc G hc (by omega)
    exact ⟨Sum.inr (Sum.inr (Sum.inr (w, q))),
      (mem_own_slot G _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr hwq.symm))))⟩

/-! ### The nodes whose bag holds a client form a connected subtree -/

theorem bag_connected (c : Fin (clientCount G)) :
    ((ParentTree.graph (Sum.inl () : Node G) (par G)).induce
      {n | c ∈ bag G n}).Connected := by
  have hcc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  have hk : (c : ℕ) < clientCount G := c.isLt
  have hd : 0 < deg G := one_le_deg G
  have hdp := depth_par G
  simp only [ParentTree.graph] at *
  by_cases h1 : (c : ℕ) < 3
  · refine ParentTree.induce_connected (depth := depth G) hdp
      (t := Sum.inl ()) ?_ ?_
    · exact (mem_bag G).2 (small_mem_own G _ h1)
    · intro s _ hs
      exact ⟨hs, (mem_bag G).2 (small_mem_own G _ h1)⟩
  by_cases h2 : (c : ℕ) < 3 + G.colours
  · have hi : (c : ℕ) - 3 < G.colours := by omega
    refine ParentTree.induce_connected (depth := depth G) hdp
      (t := Sum.inr (Sum.inl ⟨(c : ℕ) - 3, hi⟩)) ?_ ?_
    · refine (mem_bag G).2 ((mem_own_colour G _).2 (Or.inr (Or.inr (Or.inr ?_))))
      simp only [selId]; omega
    · intro s hs hst
      have hs' := (mem_bag G).1 hs
      rcases s with u | j | w | ⟨w, q⟩
      · rw [mem_own_root] at hs'; omega
      · rw [mem_own_colour] at hs'
        exfalso; apply hst
        have : (j : ℕ) = (c : ℕ) - 3 := by
          rcases hs' with h | h | h | h <;> (try simp only [selId] at h) <;> omega
        exact congrArg (fun a => Sum.inr (Sum.inl a)) (Fin.ext this)
      · rw [mem_own_vertex] at hs'
        refine ⟨by simp, ?_⟩
        refine (mem_bag G).2 ?_
        have hsel : (c : ℕ) = selId (G.classOf w) := by
          rcases hs' with h | h | h | h | h <;> (try simp only [selId, vtxId] at h ⊢) <;> omega
        show (c : ℕ) ∈ own G (Sum.inr (Sum.inl ⟨G.classOf w, classOf_lt G w⟩))
        rw [mem_own_colour]
        exact Or.inr (Or.inr (Or.inr hsel))
      · rw [mem_own_slot] at hs'
        exfalso
        have := w.isLt
        rcases hs' with h | h | h | h | h <;> (try simp only [vtxId, incId] at h) <;> omega
  by_cases h3 : (c : ℕ) < 3 + G.colours + G.vertices
  · have hw : (c : ℕ) - (3 + G.colours) < G.vertices := by omega
    refine ParentTree.induce_connected (depth := depth G) hdp
      (t := Sum.inr (Sum.inr (Sum.inl ⟨(c : ℕ) - (3 + G.colours), hw⟩))) ?_ ?_
    · refine (mem_bag G).2 ((mem_own_vertex G _).2 (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
      simp only [vtxId]; omega
    · intro s hs hst
      have hs' := (mem_bag G).1 hs
      rcases s with u | j | w | ⟨w, q⟩
      · rw [mem_own_root] at hs'; omega
      · rw [mem_own_colour] at hs'
        exfalso
        have := j.isLt
        rcases hs' with h | h | h | h <;> (try simp only [selId] at h) <;> omega
      · rw [mem_own_vertex] at hs'
        exfalso; apply hst
        have hw' : (w : ℕ) = (c : ℕ) - (3 + G.colours) := by
          rcases hs' with h | h | h | h | h <;> (try simp only [selId, vtxId] at h) <;>
            first | omega | (have := classOf_lt G w; omega)
        exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inl a))) (Fin.ext hw')
      · rw [mem_own_slot] at hs'
        have hw' : (w : ℕ) = (c : ℕ) - (3 + G.colours) := by
          have := w.isLt
          rcases hs' with h | h | h | h | h <;> (try simp only [vtxId, incId] at h) <;> omega
        refine ⟨by simp, (mem_bag G).2 ?_⟩
        show (c : ℕ) ∈ own G (Sum.inr (Sum.inr (Sum.inl w)))
        rw [mem_own_vertex]
        exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only [vtxId]; omega))))
  · obtain ⟨w0, q0, hwq⟩ := decode_inc G hk (by omega)
    refine ParentTree.induce_connected (depth := depth G) hdp
      (t := Sum.inr (Sum.inr (Sum.inr (w0, q0)))) ?_ ?_
    · exact (mem_bag G).2 ((mem_own_slot G _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr hwq.symm)))))
    · intro s hs hst
      have hs' := (mem_bag G).1 hs
      rcases s with u | j | w | ⟨w, q⟩
      · rw [mem_own_root] at hs'; omega
      · rw [mem_own_colour] at hs'
        exfalso
        have := j.isLt
        rcases hs' with h | h | h | h <;> (try simp only [selId] at h) <;> omega
      · rw [mem_own_vertex] at hs'
        exfalso
        have := w.isLt
        have := classOf_lt G w
        rcases hs' with h | h | h | h | h <;> (try simp only [selId, vtxId] at h) <;> omega
      · rw [mem_own_slot] at hs'
        exfalso; apply hst
        have hwl := w.isLt
        have hql := q.isLt
        have hwl0 := w0.isLt
        have hql0 := q0.isLt
        have hinc : incId G (w : ℕ) (q : ℕ) = incId G (w0 : ℕ) (q0 : ℕ) := by
          rcases hs' with h | h | h | h | h
          · omega
          · omega
          · omega
          · simp only [vtxId] at h; omega
          · exact h.symm.trans hwq.symm
        simp only [incId] at hinc
        obtain ⟨h1, h2⟩ := Lax117284Proofs.Lemma14Build.block_ext (s := deg G)
          (i := (w : ℕ)) (a := (q : ℕ)) (i' := (w0 : ℕ)) (a' := (q0 : ℕ)) hql hql0
          (by omega)
        exact congrArg (fun a => Sum.inr (Sum.inr (Sum.inr a)))
          (Prod.ext (Fin.ext h1) (Fin.ext h2))

/-! ### Every conflict lies in a bag

Apart from the dummy client and the two interaction clients, which every client meets, the
only pairs of clients that conflict on some day are a vertex client with the selection
client of its colour, and a vertex client with one of its own incidence clients. -/

theorem cover_vertexDay {i u v : ℕ} (hi : i < dayCount G) (hu : u < clientCount G)
    (hv : v < clientCount G) (hne : u ≠ v) (h3u : 3 ≤ u) (h3v : 3 ≤ v)
    (hd : IsVertexDay G i) (hc : (inst G).ConflictAt i u v) :
    ∃ n : Node G, u ∈ own G n ∧ v ∈ own G n := by
  by_cases hnu : Named G i u
  · by_cases hnv : Named G i v
    · rw [named_vertexDay G hd] at hnu hnv
      have hw0 := dayVertex_lt G hd
      refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨dayVertex G i, hw0⟩)), ?_, ?_⟩ <;>
        rw [mem_own_vertex]
      · rcases hnu with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · rcases hnv with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · exact absurd hc (fun hh => not_conflict_parked_named G hi hv hu (by omega) hnv hnu
        (conflictAt_symm hh))
  · by_cases hnv : Named G i v
    · exact absurd hc (not_conflict_parked_named G hi hu hv (by omega) hnu hnv)
    · exact absurd hc (not_conflict_parked_parked G hi hu hv (by omega) (by omega) hne hnu hnv)

theorem cover_validationDay {i u v : ℕ} (hi : i < dayCount G) (hu : u < clientCount G)
    (hv : v < clientCount G) (hne : u ≠ v) (h3u : 3 ≤ u) (h3v : 3 ≤ v)
    (hd : IsValidationDay G i) (hc : (inst G).ConflictAt i u v) :
    ∃ n : Node G, u ∈ own G n ∧ v ∈ own G n := by
  have hcc : clientCount G = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
  have hdg : 0 < deg G := one_le_deg G
  by_cases hnu : Named G i u
  · by_cases hnv : Named G i v
    · rw [named_validationDay G hd] at hnu hnv
      -- a vertex client of the day's colour, or an incidence client of it
      have key : ∀ (a b : ℕ), a < clientCount G → b < clientCount G → a ≠ b →
          (inst G).ConflictAt i a b →
          ((3 + G.colours ≤ a ∧ a < 3 + G.colours + G.vertices ∧
              G.classOf (a - (3 + G.colours)) = dayColour G i) ∨
            (3 + G.colours + G.vertices ≤ a ∧
              G.classOf ((a - (3 + G.colours + G.vertices)) / deg G) = dayColour G i)) →
          ((3 + G.colours ≤ b ∧ b < 3 + G.colours + G.vertices ∧
              G.classOf (b - (3 + G.colours)) = dayColour G i) ∨
            (3 + G.colours + G.vertices ≤ b ∧
              G.classOf ((b - (3 + G.colours + G.vertices)) / deg G) = dayColour G i)) →
          3 + G.colours ≤ a ∧ a < 3 + G.colours + G.vertices →
          ∃ n : Node G, a ∈ own G n ∧ b ∈ own G n := by
        intro a b ha hb hab hcab hna hnb hvtx
        obtain ⟨hw1, hw2⟩ := hvtx
        have hwa : a - (3 + G.colours) < G.vertices := by omega
        have hva : vtxId G (a - (3 + G.colours)) = a := by simp only [vtxId]; omega
        rcases hnb with ⟨hb1, hb2, hb3⟩ | ⟨hb1, hb3⟩
        · -- vertex client against vertex client
          have hwb : b - (3 + G.colours) < G.vertices := by omega
          have hca : G.classOf (a - (3 + G.colours)) = dayColour G i := by
            rcases hna with ⟨-, -, h⟩ | ⟨h, -⟩
            · exact h
            · omega
          by_cases hww : a - (3 + G.colours) = b - (3 + G.colours)
          · exact absurd (by omega) hab
          · exact absurd hcab (not_conflict_validationDay_vtx_vtx hi hd hwa hwb hca hb3 hww
              |> fun h => by
                have hva' : vtxId G (a - (3 + G.colours)) = a := hva
                have hvb' : vtxId G (b - (3 + G.colours)) = b := by simp only [vtxId]; omega
                rw [← hva', ← hvb']
                exact h)
        · -- vertex client against incidence client
          obtain ⟨w, q, hwq⟩ := decode_inc G hb (by omega)
          have hca : G.classOf (a - (3 + G.colours)) = dayColour G i := by
            rcases hna with ⟨-, -, h⟩ | ⟨h, -⟩
            · exact h
            · omega
          have hdiv : (b - (3 + G.colours + G.vertices)) / deg G = (w : ℕ) := by
            have := w.isLt
            have hq := q.isLt
            have : b - (3 + G.colours + G.vertices) = (w : ℕ) * deg G + (q : ℕ) := by
              rw [← hwq]; simp only [incId]; omega
            rw [this, Nat.mul_comm, Nat.mul_add_div hdg, Nat.div_eq_of_lt hq, Nat.add_zero]
          by_cases hww : a - (3 + G.colours) = (w : ℕ)
          · refine ⟨Sum.inr (Sum.inr (Sum.inr (w, q))), ?_, ?_⟩
            · rw [mem_own_slot]
              exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← hww]; exact hva.symm))))
            · rw [mem_own_slot]
              exact Or.inr (Or.inr (Or.inr (Or.inr hwq.symm)))
          · exfalso
            have hcw : G.classOf (w : ℕ) = dayColour G i := by rw [← hdiv]; exact hb3
            have hcc' := not_conflict_validationDay_vtx_inc (q := (q : ℕ)) hi hd hwa w.isLt
              q.isLt hca hcw hww
            rw [← hwq] at hcab
            rw [← hva] at hcab
            exact hcc' hcab
      -- dispatch on the kinds of the two clients
      by_cases hua : 3 + G.colours ≤ u ∧ u < 3 + G.colours + G.vertices
      · exact key u v hu hv hne hc hnu hnv hua
      · by_cases hva : 3 + G.colours ≤ v ∧ v < 3 + G.colours + G.vertices
        · obtain ⟨n, h1, h2⟩ := key v u hv hu (Ne.symm hne) (conflictAt_symm hc) hnv hnu hva
          exact ⟨n, h2, h1⟩
        · -- two incidence clients
          have hiu : 3 + G.colours + G.vertices ≤ u := by
            rcases hnu with ⟨h1, h2, -⟩ | ⟨h1, -⟩
            · exact absurd ⟨h1, h2⟩ hua
            · exact h1
          have hiv : 3 + G.colours + G.vertices ≤ v := by
            rcases hnv with ⟨h1, h2, -⟩ | ⟨h1, -⟩
            · exact absurd ⟨h1, h2⟩ hva
            · exact h1
          obtain ⟨w, q, hwq⟩ := decode_inc G hu hiu
          obtain ⟨w', q', hwq'⟩ := decode_inc G hv hiv
          have hcl : ∀ (w : Fin G.vertices) (q : Fin (deg G)) (c : ℕ),
              incId G (w : ℕ) (q : ℕ) = c → 3 + G.colours + G.vertices ≤ c →
              (G.classOf ((c - (3 + G.colours + G.vertices)) / deg G) = dayColour G i) →
              G.classOf (w : ℕ) = dayColour G i := by
            intro w q c hwq _ h
            have hq := q.isLt
            have : c - (3 + G.colours + G.vertices) = (w : ℕ) * deg G + (q : ℕ) := by
              rw [← hwq]; simp only [incId]; omega
            rw [this, Nat.mul_comm, Nat.mul_add_div hdg, Nat.div_eq_of_lt hq,
              Nat.add_zero] at h
            exact h
          have hcu : G.classOf (w : ℕ) = dayColour G i := by
            rcases hnu with ⟨h1, h2, -⟩ | ⟨-, h⟩
            · omega
            · exact hcl w q u hwq hiu h
          have hcv : G.classOf (w' : ℕ) = dayColour G i := by
            rcases hnv with ⟨h1, h2, -⟩ | ⟨-, h⟩
            · omega
            · exact hcl w' q' v hwq' hiv h
          exfalso
          have hne' : incId G (w : ℕ) (q : ℕ) ≠ incId G (w' : ℕ) (q' : ℕ) := by
            rw [hwq, hwq']; exact hne
          have := not_conflict_validationDay_inc_inc (q := (q : ℕ)) (q' := (q' : ℕ)) hi hd
            w.isLt w'.isLt q.isLt q'.isLt hcu hcv hne'
          rw [hwq, hwq'] at this
          exact this hc
    · exact absurd hc (fun hh => not_conflict_parked_named G hi hv hu (by omega) hnv hnu
        (conflictAt_symm hh))
  · by_cases hnv : Named G i v
    · exact absurd hc (not_conflict_parked_named G hi hu hv (by omega) hnu hnv)
    · exact absurd hc (not_conflict_parked_parked G hi hu hv (by omega) (by omega) hne hnu hnv)

theorem cover_edgeDay {i u v : ℕ} (hi : i < dayCount G) (hu : u < clientCount G)
    (hv : v < clientCount G) (hne : u ≠ v) (h3u : 3 ≤ u) (h3v : 3 ≤ v)
    (hd : IsEdgeDay G i) (hc : (inst G).ConflictAt i u v) :
    ∃ n : Node G, u ∈ own G n ∧ v ∈ own G n := by
  exfalso
  by_cases hnu : Named G i u
  · by_cases hnv : Named G i v
    · rw [named_edgeDay G hd] at hnu hnv
      have hT : 3 ≤ edgeTail G i := by simp only [edgeTail, incId]; omega
      have hH : 3 ≤ edgeHead G i := by simp only [edgeHead, incId]; omega
      rcases hnu with h | h | h | h <;> rcases hnv with h' | h' | h' | h'
      all_goals first
        | omega
        | (subst_vars; exact hne rfl)
        | skip
      -- the remaining cases are the tail against the head
      · rw [h, h'] at hc
        exact not_conflict_edgeDay_tail_head hi hd (h ▸ hu) (h' ▸ hv)
          (fun hh => hne (by rw [h, h']; exact hh.symm)) hc
      · rw [h, h'] at hc
        exact not_conflict_edgeDay_tail_head hi hd (h' ▸ hv) (h ▸ hu)
          (fun hh => hne (by rw [h, h']; exact hh)) (conflictAt_symm hc)
    · exact (fun hh => not_conflict_parked_named G hi hv hu (by omega) hnv hnu
        (conflictAt_symm hh)) hc
  · by_cases hnv : Named G i v
    · exact not_conflict_parked_named G hi hu hv (by omega) hnu hnv hc
    · exact not_conflict_parked_parked G hi hu hv (by omega) (by omega) hne hnu hnv hc

/-- **Every conflict between two clients lies in a bag.** -/
theorem exists_bag_of_conflict {i u v : ℕ} (hi : i < dayCount G) (hu : u < clientCount G)
    (hv : v < clientCount G) (hne : u ≠ v) (hc : (inst G).ConflictAt i u v) :
    ∃ n : Node G, u ∈ own G n ∧ v ∈ own G n := by
  by_cases h3u : 3 ≤ u
  · by_cases h3v : 3 ≤ v
    · rcases day_trichotomy G i with hd | hd | hd
      · exact cover_vertexDay G hi hu hv hne h3u h3v hd hc
      · exact cover_validationDay G hi hu hv hne h3u h3v hd hc
      · exact cover_edgeDay G hi hu hv hne h3u h3v hd hc
    · obtain ⟨n, hn⟩ := exists_own G hu
      exact ⟨n, hn, small_mem_own G n (by omega)⟩
  · obtain ⟨n, hn⟩ := exists_own G hv
    exact ⟨n, small_mem_own G n (by omega), hn⟩

/-! ### The decomposition -/

/-- **The tree decomposition of the overall conflict graph**, as the archive states it. -/
noncomputable def decomp :
    Lax228581.Treewidth.TreeDecomposition (Lax117284.ConflictGraph.overallGraph (inst G)) where
  Node := Node G
  tree := ParentTree.graph (Sum.inl () : Node G) (par G)
  isTree := isTree G
  bag := bag G
  vertex_mem_bag c := by
    obtain ⟨n, hn⟩ := exists_own G c.isLt
    exact ⟨n, (mem_bag G).2 hn⟩
  edge_mem_bag := by
    intro u v huv
    obtain ⟨hne, i, hci⟩ := huv
    have hc : (inst G).ConflictAt (i : ℕ) (u : ℕ) (v : ℕ) :=
      ((inst G).conflictAt_iff i u v).2 hci
    obtain ⟨n, h1, h2⟩ := exists_bag_of_conflict G i.isLt u.isLt v.isLt
      (fun h => hne (Fin.ext h)) hc
    exact ⟨n, (mem_bag G).2 h1, (mem_bag G).2 h2⟩
  bag_indices_connected := bag_connected G

/--
---
conclusion: Lax117284.Lemma14.treewidth_le
---
The overall conflict graph of the constructed instance has a tree decomposition of width
four: on every day the dummy client conflicts with the clients that take no part in the
gadget and with none that does, so apart from the dummy and the two interaction clients,
which every bag holds, the conflicts that remain are those inside a day's gadget — a vertex
client with the selection client of its colour, and a vertex client with one of its own
incidence clients.
-/
theorem treewidth_le : Lax117284.ConflictGraph.treewidth (inst G) ≤ 4 := by
  have h : Lax228581.Treewidth.HasTreewidthAtMost (Lax117284.ConflictGraph.overallGraph (inst G)) 4 :=
    ⟨decomp G, card_bag_le G⟩
  exact Nat.sInf_le h

end Lax117284Proofs.Lemma14Treewidth


