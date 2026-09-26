import Lax117284Proofs.Machine.MisFormat
import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.SourceInjectivity
import Lax117284.Lemma14

/-!
The reduction of Lemma 14 on the numbers of a stream: the check that the stream is the adjacency
matrix of an instance in normal form, the graph it describes, and the numbers of the instance it is
sent to.
-/

namespace Lax117284Proofs.Machine.MisSem

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.MisFormat Lax117284Proofs.Machine.Lists
open Lax117284.MulticolouredIndepSet

/-! ### The matrix of a stream -/

/-- The number of colour classes. -/
def lN (ns : List ℕ) : ℕ := ns.getD 0 0

/-- The number of vertices per class. -/
def nN (ns : List ℕ) : ℕ := ns.getD 1 0

lemma VM_eq (ns : List ℕ) : VM ns = lN ns * nN ns := rfl

/-- The entry of the matrix at row `w` and column `w'`. -/
def mat (ns : List ℕ) (w w' : ℕ) : ℕ := ns.getD (2 + (w * VM ns + w')) 0

/-- The number of ones in row `w`. -/
def rowSum (ns : List ℕ) (w : ℕ) : ℕ :=
  (List.range (VM ns)).countP fun w' => decide (mat ns w w' = 1)

/-- The cell `t` is the entry of an edge from a smaller number to a larger. -/
def qualE (ns : List ℕ) (t : ℕ) : Bool :=
  decide (ns.getD (2 + t) 0 = 1 ∧ t / VM ns < t % VM ns)

/-- The number of edges. -/
def edgeN (ns : List ℕ) : ℕ := (List.range (VM ns * VM ns)).countP (qualE ns)

/-- The cell `t` is symmetric, is not on the diagonal unless empty, and does not join two
vertices of the same class unless empty. -/
def PassM (ns : List ℕ) (t : ℕ) : Prop :=
  ns.getD (2 + t) 0 = ns.getD (2 + (t % VM ns * VM ns + t / VM ns)) 0 ∧
  (t / VM ns = t % VM ns → ns.getD (2 + t) 0 = 0) ∧
  (t / VM ns / nN ns = t % VM ns / nN ns → ns.getD (2 + t) 0 = 0)

/-- The graph is regular of a positive degree, or has no vertex. -/
def RegM (ns : List ℕ) : Prop :=
  VM ns = 0 ∨ (0 < rowSum ns 0 ∧ ∀ w < VM ns, rowSum ns w = rowSum ns 0)

/-- **What the check asks of a stream**: the normal form of the source. -/
def CondM (ns : List ℕ) : Prop :=
  4 ≤ nN ns ∧ (∀ t < VM ns * VM ns, PassM ns t) ∧ RegM ns ∧ edgeN ns % 2 = 0

lemma cell_div (ns : List ℕ) {w w' : ℕ} (hw' : w' < VM ns) : (w * VM ns + w') / VM ns = w := by
  have hV : 0 < VM ns := by omega
  rw [Nat.mul_comm, Nat.mul_add_div hV, Nat.div_eq_of_lt hw', Nat.add_zero]

lemma cell_mod (ns : List ℕ) {w w' : ℕ} (hw' : w' < VM ns) : (w * VM ns + w') % VM ns = w' := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hw']

lemma cell_lt (ns : List ℕ) {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) :
    w * VM ns + w' < VM ns * VM ns := by
  have : w * VM ns + w' < (w + 1) * VM ns := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (w + 1) * VM ns ≤ VM ns * VM ns := Nat.mul_le_mul_right _ (by omega)
  omega

lemma cell_split (ns : List ℕ) (t : ℕ) (ht : t < VM ns * VM ns) :
    t = (t / VM ns) * VM ns + t % VM ns ∧ t / VM ns < VM ns ∧ t % VM ns < VM ns := by
  have hV : 0 < VM ns := by
    rcases Nat.eq_zero_or_pos (VM ns) with h | h
    · rw [h] at ht; simp at ht
    · exact h
  refine ⟨?_, (Nat.div_lt_iff_lt_mul hV).2 ht, Nat.mod_lt _ hV⟩
  have := Nat.div_add_mod t (VM ns)
  rw [Nat.mul_comm] at this
  omega

/-- The entry at a cell, in terms of row and column. -/
lemma getD_cell (ns : List ℕ) (t : ℕ) (ht : t < VM ns * VM ns) :
    ns.getD (2 + t) 0 = mat ns (t / VM ns) (t % VM ns) := by
  obtain ⟨h1, -, -⟩ := cell_split ns t ht
  unfold mat
  rw [← h1]

lemma passM_iff (ns : List ℕ) (w w' : ℕ) (hw : w < VM ns) (hw' : w' < VM ns) :
    PassM ns (w * VM ns + w') ↔
      (mat ns w w' = mat ns w' w ∧ (w = w' → mat ns w w' = 0) ∧
        (w / nN ns = w' / nN ns → mat ns w w' = 0)) := by
  have hlt := cell_lt ns hw hw'
  unfold PassM
  rw [cell_div ns hw', cell_mod ns hw']
  unfold mat
  rfl

/-! ### The graph of a stream that passes the check -/

section Graph

variable (ns : List ℕ)

/-- The number of a vertex given as a pair. -/
def numV (u : Fin (lN ns) × Fin (nN ns)) : ℕ := (u.1 : ℕ) * nN ns + (u.2 : ℕ)

lemma numV_lt (u : Fin (lN ns) × Fin (nN ns)) : numV ns u < VM ns := by
  unfold numV
  rw [VM_eq]
  have h1 := u.1.isLt
  have h2 := u.2.isLt
  have : (u.1 : ℕ) * nN ns + (u.2 : ℕ) < ((u.1 : ℕ) + 1) * nN ns := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h3 : ((u.1 : ℕ) + 1) * nN ns ≤ lN ns * nN ns := Nat.mul_le_mul_right _ h1
  omega

lemma numV_div (u : Fin (lN ns) × Fin (nN ns)) : numV ns u / nN ns = u.1 := by
  have hn : 0 < nN ns := by have := u.2.isLt; omega
  unfold numV
  rw [Nat.mul_comm, Nat.mul_add_div hn, Nat.div_eq_of_lt u.2.isLt, Nat.add_zero]

lemma passM_at (hc : CondM ns) {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) :
    mat ns w w' = mat ns w' w ∧ (w = w' → mat ns w w' = 0) ∧
      (w / nN ns = w' / nN ns → mat ns w w' = 0) :=
  (passM_iff ns w w' hw hw').1 (hc.2.1 _ (cell_lt ns hw hw'))

/-- **The graph of a stream that passes the check**: two vertices are adjacent when the matrix has
a one at either of their cells. -/
noncomputable def graphOf (hc : CondM ns) : Instance where
  colours := lN ns
  size := nN ns
  graph := SimpleGraph.fromRel fun u v => mat ns (numV ns u) (numV ns v) = 1
  adj_colour_ne := by
    intro u v h hcol
    rw [SimpleGraph.fromRel_adj] at h
    have hcls : numV ns u / nN ns = numV ns v / nN ns := by
      rw [numV_div, numV_div, hcol]
    have h1 := (passM_at ns hc (numV_lt ns u) (numV_lt ns v)).2.2 hcls
    have h2 := (passM_at ns hc (numV_lt ns u) (numV_lt ns v)).1
    rcases h.2 with h3 | h3
    · omega
    · omega

theorem adjAt_graphOf (hc : CondM ns) {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) :
    (graphOf ns hc).adjAt w w' = decide (mat ns w w' = 1) := by
  have hn : 0 < nN ns := by
    have := hc.1; omega
  have hV : 0 < VM ns := by omega
  have hsz : (graphOf ns hc).size = nN ns := rfl
  have e1 : ∀ x : ℕ, x / nN ns * nN ns + x % nN ns = x := fun x => by
    have := Nat.div_add_mod x (nN ns)
    rw [Nat.mul_comm] at this; omega
  have hp := passM_at ns hc hw hw'
  unfold Instance.adjAt
  rw [dif_pos (And.intro (show w < (graphOf ns hc).vertices from hw)
    (show w' < (graphOf ns hc).vertices from hw'))]
  rw [decide_eq_decide]
  refine (SimpleGraph.fromRel_adj _ _ _).trans ?_
  simp only [numV, Fin.val_mk, hsz, e1]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact h
    · rw [hp.1]; exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    have h1 := congrArg (fun p : Fin (lN ns) × Fin (nN ns) => (p.1 : ℕ) * nN ns + p.2) heq
    simp only [hsz, e1] at h1
    have h0 := hp.2.1 h1
    omega

lemma flatMap_single {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem code_toksM {ns : List ℕ} (hs : ShapeM ns) :
    code (toksM ns) = encodeNat (ns.getD 0 0) ++ encodeNat (ns.getD 1 0) ++
      (List.range (VM ns * VM ns)).map (fun t => decide (ns.getD (2 + t) 0 ≠ 0)) := by
  obtain ⟨h2, hl, hsg⟩ := hs
  unfold code toksM
  rw [hl, List.range_add, List.map_append, List.flatMap_append, List.map_map, List.flatMap_map]
  congr 1
  · simp [List.range_succ, tokAtM, Tok.code]
  · rw [List.flatMap_map]
    have : ∀ t, ((tokAtM ns ∘ fun x => 2 + x) t).code = [decide (ns.getD (2 + t) 0 ≠ 0)] := by
      intro t
      have h : ¬ (2 + t < 2) := by omega
      simp only [Function.comp, tokAtM, if_neg h, Tok.code]
    simp only [this]
    exact flatMap_single _ _

theorem encode_graphOf (hc : CondM ns) (hs : ShapeM ns) :
    Lax117284.MulticolouredIndepSet.encodeInstance (graphOf ns hc) = code (toksM ns) := by
  have hsg := hs.2.2
  rw [code_toksM hs]
  unfold Lax117284.MulticolouredIndepSet.encodeInstance
  show encodeNat (lN ns) ++ encodeNat (nN ns) ++ (List.range (VM ns)).flatMap (fun w =>
      (List.range (VM ns)).map fun w' => (graphOf ns hc).adjAt w w') = _
  have hV : ∀ t, t < VM ns * VM ns → (graphOf ns hc).adjAt (t / VM ns) (t % VM ns) =
      decide (ns.getD (2 + t) 0 ≠ 0) := by
    intro t ht
    obtain ⟨-, h1, h2⟩ := cell_split ns t ht
    rw [adjAt_graphOf ns hc h1 h2, ← getD_cell ns t ht]
    have hlen := hs.2.1
    have hlt : 2 + t < ns.length := by rw [hlen]; omega
    have := hsg (2 + t) (by omega) hlt
    by_cases h0 : ns.getD (2 + t) 0 = 0
    · rw [h0]; rfl
    · have h1' : ns.getD (2 + t) 0 = 1 := by omega
      rw [h1']; rfl
  congr 1
  rw [← flatMap_single (List.range (VM ns * VM ns)) (fun t => decide (ns.getD (2 + t) 0 ≠ 0)),
    ← flatMap_rows (fun t => [decide (ns.getD (2 + t) 0 ≠ 0)]) (VM ns) (VM ns)]
  refine List.flatMap_congr fun w hw => ?_
  rw [← flatMap_single (List.range (VM ns)) (fun w' => (graphOf ns hc).adjAt w w')]
  refine List.flatMap_congr fun b hb => ?_
  have hw' := List.mem_range.mp hw
  have hb' := List.mem_range.mp hb
  have := hV (w * VM ns + b) (cell_lt ns hw' hb')
  rw [cell_div ns hb', cell_mod ns hb'] at this
  rw [this]

end Graph

/-! ### The neighbours and the edges of a graph whose adjacency is a matrix -/

lemma filter_map_eq_flatMap {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter p).map f = l.flatMap (fun x => if p x = true then [f x] else [])
  | [] => rfl
  | x :: t => by
    rw [List.filter_cons, List.flatMap_cons]
    by_cases h : p x = true
    · rw [if_pos h, if_pos h, List.map_cons, filter_map_eq_flatMap p f t]; rfl
    · rw [if_neg h, if_neg h, filter_map_eq_flatMap p f t]; simp

/-- The pairs of endpoints of the edges, from the cells of the matrix. -/
def edgeCellsN (ns : List ℕ) : List (ℕ × ℕ) :=
  ((List.range (VM ns * VM ns)).filter (qualE ns)).map fun t => (t / VM ns, t % VM ns)

section Struct

variable (G : Instance) (ns : List ℕ) (hV : VM ns = G.vertices)
  (hadj : ∀ w w', w < VM ns → w' < VM ns → G.adjAt w w' = decide (mat ns w w' = 1))
include hV hadj

lemma nbrs_eq {w : ℕ} (hw : w < VM ns) :
    G.nbrs w = (List.range (VM ns)).filter (fun w' => decide (mat ns w w' = 1)) := by
  unfold Instance.nbrs
  rw [← hV]
  exact List.filter_congr (fun w' hw' => hadj w w' hw (List.mem_range.mp hw'))

lemma nbrs_length {w : ℕ} (hw : w < VM ns) : (G.nbrs w).length = rowSum ns w := by
  rw [nbrs_eq G ns hV hadj hw]
  unfold rowSum
  rw [List.countP_eq_length_filter]

lemma degree_eq : G.degree = rowSum ns 0 := by
  unfold Instance.degree
  by_cases h : 0 < VM ns
  · exact nbrs_length G ns hV hadj h
  · have h0 : VM ns = 0 := by omega
    have h1 : G.vertices = 0 := by rw [← hV]; exact h0
    unfold Instance.nbrs
    rw [h1]
    simp [rowSum, h0]

theorem edgeList_eq : G.edgeList = edgeCellsN ns := by
  unfold Instance.edgeList edgeCellsN
  rw [← hV, filter_map_eq_flatMap]
  have hV0 : ∀ w b, b < VM ns → (w * VM ns + b) / VM ns = w := fun w b hb => cell_div ns hb
  have hV1 : ∀ w b, b < VM ns → (w * VM ns + b) % VM ns = b := fun w b hb => cell_mod ns hb
  rw [← flatMap_rows (fun t => if qualE ns t = true then [(t / VM ns, t % VM ns)] else [])
    (VM ns) (VM ns)]
  refine List.flatMap_congr fun w hw => ?_
  have hw' := List.mem_range.mp hw
  rw [nbrs_eq G ns hV hadj hw', List.filter_filter, filter_map_eq_flatMap]
  refine List.flatMap_congr fun b hb => ?_
  have hb' := List.mem_range.mp hb
  have hq : qualE ns (w * VM ns + b) = (decide (mat ns w b = 1) && decide (w < b)) := by
    unfold qualE
    rw [hV0 w b hb', hV1 w b hb']
    have := getD_cell ns (w * VM ns + b) (cell_lt ns hw' hb')
    rw [hV0 w b hb', hV1 w b hb'] at this
    rw [this]
    simp [Bool.decide_and]
  rw [hq, hV0 w b hb', hV1 w b hb', Bool.and_comm (decide (w < b))]

/-- The number of neighbours of `w` that come before `w'`, which is the position of `w'` among
the neighbours of `w` when it is one. -/
def idxN (ns : List ℕ) (w w' : ℕ) : ℕ :=
  (List.range w').countP fun x => decide (mat ns w x = 1)

lemma idxOf_nbrs {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) (hm : mat ns w w' = 1) :
    (G.nbrs w).idxOf w' = idxN ns w w' := by
  rw [nbrs_eq G ns hV hadj hw]
  obtain ⟨k, hk⟩ : ∃ k, VM ns = w' + 1 + k := ⟨VM ns - w' - 1, by omega⟩
  rw [hk, List.range_add, List.range_succ, List.filter_append, List.filter_append]
  have hp : (fun w'' => decide (mat ns w w'' = 1)) w' = true := by simp [hm]
  have hf : (List.filter (fun w'' => decide (mat ns w w'' = 1)) [w']) = [w'] := by
    simp [List.filter_cons, hm]
  rw [hf, List.append_assoc, List.singleton_append]
  have hnot : w' ∉ List.filter (fun w'' => decide (mat ns w w'' = 1)) (List.range w') := by
    intro h
    have := List.mem_range.mp (List.mem_of_mem_filter h)
    omega
  rw [List.idxOf_append_of_notMem hnot, List.idxOf_cons_self]
  unfold idxN
  rw [List.countP_eq_length_filter]
  simp

theorem edgeCount_eq : G.edgeCount = edgeN ns := by
  unfold Instance.edgeCount edgeN
  rw [edgeList_eq G ns hV hadj]
  unfold edgeCellsN
  rw [List.length_map, List.countP_eq_length_filter]

end Struct

/-! ### The gate of the reduction, on streams -/

section Gate

lemma cdiv' (V w b : ℕ) (hb : b < V) : (w * V + b) / V = w := by
  have hV : 0 < V := by omega
  rw [Nat.mul_comm, Nat.mul_add_div hV, Nat.div_eq_of_lt hb, Nat.add_zero]

lemma cmod' (V w b : ℕ) (hb : b < V) : (w * V + b) % V = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

variable (G : Instance)

lemma encodeInstance_cells :
    Lax117284.MulticolouredIndepSet.encodeInstance G = encodeNat G.colours ++ encodeNat G.size ++
      (List.range (G.vertices * G.vertices)).map (fun t => G.adjAt (t / G.vertices) (t % G.vertices)) := by
  unfold Lax117284.MulticolouredIndepSet.encodeInstance
  congr 1
  rw [← flatMap_single (List.range (G.vertices * G.vertices)) (fun t =>
      G.adjAt (t / G.vertices) (t % G.vertices)),
    ← flatMap_rows (fun t => [G.adjAt (t / G.vertices) (t % G.vertices)]) G.vertices G.vertices]
  refine List.flatMap_congr fun w hw => ?_
  rw [← flatMap_single (List.range G.vertices) (fun w' => G.adjAt w w')]
  refine List.flatMap_congr fun b hb => ?_
  have hb' := List.mem_range.mp hb
  rw [cdiv' _ _ _ hb', cmod' _ _ _ hb']

/-- The numbers of an instance: the counts and the adjacency matrix as zeros and ones. -/
noncomputable def valsG : List ℕ :=
  [G.colours, G.size] ++ (List.range (G.vertices * G.vertices)).map
    (fun t => if G.adjAt (t / G.vertices) (t % G.vertices) = true then 1 else 0)

lemma valsG_getD_cell {t : ℕ} (ht : t < G.vertices * G.vertices) :
    (valsG G).getD (2 + t) 0 = if G.adjAt (t / G.vertices) (t % G.vertices) = true then 1 else 0 := by
  unfold valsG
  rw [List.getD_append_right _ _ _ _ (by simp), show 2 + t - [G.colours, G.size].length = t by simp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
  simp

lemma valsG_VM : VM (valsG G) = G.vertices := by
  unfold VM valsG; simp [Instance.vertices]

lemma valsG_lN : lN (valsG G) = G.colours := by unfold lN valsG; simp
lemma valsG_nN : nN (valsG G) = G.size := by unfold nN valsG; simp

lemma valsG_length : (valsG G).length = 2 + G.vertices * G.vertices := by
  unfold valsG; simp; omega

theorem shape_valsG : ShapeM (valsG G) := by
  refine ⟨by rw [valsG_length]; omega, by rw [valsG_length, valsG_VM], fun k hk2 hk => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t, k = 2 + t := ⟨k - 2, by omega⟩
  rw [valsG_length] at hk
  rw [valsG_getD_cell G (by omega)]
  split <;> omega

theorem mat_valsG {w w' : ℕ} (hw : w < G.vertices) (hw' : w' < G.vertices) :
    mat (valsG G) w w' = if G.adjAt w w' = true then 1 else 0 := by
  unfold mat
  rw [valsG_VM]
  have hV : 0 < G.vertices := by omega
  have := valsG_getD_cell G (t := w * G.vertices + w') (by
    have := cell_lt (valsG G) (w := w) (w' := w') (by rw [valsG_VM]; exact hw)
      (by rw [valsG_VM]; exact hw')
    rw [valsG_VM] at this; exact this)
  rw [this, cdiv' _ _ _ hw', cmod' _ _ _ hw']

theorem adj_valsG : ∀ w w', w < VM (valsG G) → w' < VM (valsG G) →
    G.adjAt w w' = decide (mat (valsG G) w w' = 1) := by
  intro w w' hw hw'
  rw [valsG_VM] at hw hw'
  rw [mat_valsG G hw hw']
  by_cases h : G.adjAt w w' = true <;> simp [h]

theorem code_valsG : code (toksM (valsG G)) = Lax117284.MulticolouredIndepSet.encodeInstance G := by
  rw [code_toksM (shape_valsG G), encodeInstance_cells]
  have h0 : (valsG G).getD 0 0 = G.colours := valsG_lN G
  have h1 : (valsG G).getD 1 0 = G.size := valsG_nN G
  rw [h0, h1, valsG_VM]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [valsG_getD_cell G (List.mem_range.mp ht)]
  by_cases h : G.adjAt (t / G.vertices) (t % G.vertices) = true <;> simp [h]

open Classical in
lemma adjAt_unfold {w w' : ℕ} (hw : w < G.vertices) (hw' : w' < G.vertices) :
    ∃ (hs : 0 < G.size) (h1 : w / G.size < G.colours) (h2 : w' / G.size < G.colours),
      G.adjAt w w' = decide (G.graph.Adj
        (⟨w / G.size, h1⟩, ⟨w % G.size, Nat.mod_lt _ hs⟩)
        (⟨w' / G.size, h2⟩, ⟨w' % G.size, Nat.mod_lt _ hs⟩)) := by
  have hs : 0 < G.size := by
    by_contra h0
    have hz : G.size = 0 := by omega
    unfold Instance.vertices at hw
    rw [hz, Nat.mul_zero] at hw
    omega
  exact ⟨hs, (Nat.div_lt_iff_lt_mul hs).2 hw, (Nat.div_lt_iff_lt_mul hs).2 hw', by
    unfold Instance.adjAt
    rw [dif_pos ⟨hw, hw'⟩]⟩

open Classical in
lemma adjAt_symm {w w' : ℕ} (hw : w < G.vertices) (hw' : w' < G.vertices) :
    G.adjAt w w' = G.adjAt w' w := by
  obtain ⟨hs, h1, h2, e1⟩ := adjAt_unfold G hw hw'
  obtain ⟨_, _, _, e2⟩ := adjAt_unfold G hw' hw
  rw [e1, e2]
  exact decide_eq_decide.mpr (SimpleGraph.adj_comm _ _ _)

open Classical in
lemma adjAt_irrefl {w : ℕ} (hw : w < G.vertices) : G.adjAt w w = false := by
  obtain ⟨_, _, _, e1⟩ := adjAt_unfold G hw hw
  rw [e1]
  exact decide_eq_false (G.graph.loopless.irrefl _)

open Classical in
lemma adjAt_class {w w' : ℕ} (hw : w < G.vertices) (hw' : w' < G.vertices)
    (h : G.adjAt w w' = true) : w / G.size ≠ w' / G.size := by
  obtain ⟨hs, h1, h2, e1⟩ := adjAt_unfold G hw hw'
  rw [e1] at h
  have := G.adj_colour_ne _ _ (of_decide_eq_true h)
  intro heq
  exact this (Fin.ext heq)

theorem condM_valsG (hN : G.Normal) : CondM (valsG G) := by
  have hV := valsG_VM G
  have hadj := adj_valsG G
  refine ⟨by rw [valsG_nN]; exact hN.2.1, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, w', hw, hw', rfl⟩ : ∃ w w', w < VM (valsG G) ∧ w' < VM (valsG G) ∧
        t = w * VM (valsG G) + w' :=
      ⟨t / VM (valsG G), t % VM (valsG G), (cell_split _ t ht).2.1, (cell_split _ t ht).2.2,
        (cell_split _ t ht).1⟩
    rw [passM_iff _ w w' hw hw']
    rw [valsG_VM] at hw hw'
    refine ⟨?_, ?_, ?_⟩
    · rw [mat_valsG G hw hw', mat_valsG G hw' hw, adjAt_symm G hw hw']
    · intro h
      subst h
      rw [mat_valsG G hw hw, adjAt_irrefl G hw]; rfl
    · intro h
      rw [valsG_nN] at h
      rw [mat_valsG G hw hw']
      by_cases hh : G.adjAt w w' = true
      · exact absurd h (adjAt_class G hw hw' hh)
      · simp [hh]
  · obtain ⟨r, hr, hreg⟩ := hN.1
    by_cases h0 : VM (valsG G) = 0
    · exact Or.inl h0
    · right
      have h0' : 0 < VM (valsG G) := by omega
      have e := fun w (hw : w < VM (valsG G)) =>
        (nbrs_length G (valsG G) hV.symm hadj hw).symm.trans (hreg w (by rw [← hV]; exact hw))
      exact ⟨by rw [e 0 h0']; exact hr, fun w hw => by rw [e w hw, e 0 h0']⟩
  · have := edgeCount_eq G (valsG G) hV.symm hadj
    have h2 := hN.2.2
    omega

theorem normal_graphOf (ns : List ℕ) (hc : CondM ns) : (graphOf ns hc).Normal := by
  have hV : VM ns = (graphOf ns hc).vertices := rfl
  have hadj : ∀ w w', w < VM ns → w' < VM ns →
      (graphOf ns hc).adjAt w w' = decide (mat ns w w' = 1) :=
    fun w w' hw hw' => adjAt_graphOf ns hc hw hw'
  refine ⟨?_, hc.1, ?_⟩
  · by_cases h0 : VM ns = 0
    · exact ⟨1, by omega, fun w hw => by rw [← hV] at hw; omega⟩
    · have hreg : 0 < rowSum ns 0 ∧ ∀ w < VM ns, rowSum ns w = rowSum ns 0 := by
        rcases hc.2.2.1 with h | h
        · exact absurd h h0
        · exact h
      exact ⟨rowSum ns 0, hreg.1, fun w hw => by
        rw [← hV] at hw
        rw [nbrs_length _ ns hV hadj hw]
        exact hreg.2 w hw⟩
  · have := edgeCount_eq (graphOf ns hc) ns hV hadj
    have h2 := hc.2.2.2
    omega

/-- **The gate of the reduction, on streams.** -/
theorem mis_gate (w : Word) :
    (∃ G : Instance, Lax117284.MulticolouredIndepSet.encodeInstance G = w ∧ G.Normal) ↔
      ∃ ts : List Tok, w = code ts ∧ Conforms EM ts ∧
        CondM (ts.map Lax117284Proofs.Machine.TokProg.Tok.val) := by
  constructor
  · rintro ⟨G, rfl, hN⟩
    refine ⟨toksM (valsG G), (code_valsG G).symm, conforms_of_shape (shape_valsG G), ?_⟩
    rw [vals_toksM (shape_valsG G)]
    exact condM_valsG G hN
  · rintro ⟨ts, rfl, hconf, hcond⟩
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    refine ⟨graphOf _ hcond, ?_, normal_graphOf _ hcond⟩
    rw [encode_graphOf _ hcond hshape, ← hts]

end Gate

/-! ### The image -/

/-- The degree, raised to `1`. -/
def degN (ns : List ℕ) : ℕ := max 1 (rowSum ns 0)

/-- The number of clients other than the dummy client. -/
def spanN (ns : List ℕ) : ℕ := 2 + lN ns + VM ns + VM ns * degN ns

/-- The number of clients. -/
def clN (ns : List ℕ) : ℕ := 3 + lN ns + VM ns + VM ns * degN ns

/-- The number of days. -/
def daysN (ns : List ℕ) : ℕ := lN ns * (nN ns + 1) + edgeN ns

/-- The number of the edge client of the vertex `w` and its neighbour number `q`. -/
def incIdN (ns : List ℕ) (w q : ℕ) : ℕ := 3 + lN ns + VM ns + w * degN ns + q

/-- The processing time and the due date of client `c` on the vertex day of the vertex `w₀`. -/
def vertexDayN (ns : List ℕ) (w₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (spanN ns, degN ns + spanN ns)
  else if c = 3 + lN ns + w₀ ∨ c = 3 + w₀ / nN ns then (degN ns, degN ns)
  else (1, degN ns + c)

/-- The processing time and the due date of client `c` on the validation day of colour `i₀`. -/
def validationDayN (ns : List ℕ) (i₀ c : ℕ) : ℕ × ℕ :=
  if c = 0 then (spanN ns, degN ns * nN ns + spanN ns)
  else if 3 + lN ns ≤ c ∧ c < 3 + lN ns + VM ns ∧ (c - (3 + lN ns)) / nN ns = i₀ then
    (degN ns, degN ns * ((c - (3 + lN ns)) % nN ns + 1))
  else if 3 + lN ns + VM ns ≤ c ∧
      ((c - (3 + lN ns + VM ns)) / degN ns) / nN ns = i₀ then
    (1, degN ns * (((c - (3 + lN ns + VM ns)) / degN ns) % nN ns)
      + (c - (3 + lN ns + VM ns)) % degN ns + 1)
  else (1, degN ns * nN ns + c)

/-- The processing time and the due date of client `c` on the edge day of the edge from `w` to
`w'`. -/
def edgeDayN (ns : List ℕ) (w w' c : ℕ) : ℕ × ℕ :=
  if c = 0 then (spanN ns, 3 + spanN ns)
  else if c = 2 then (2, 2)
  else if c = 1 then (2, 3)
  else if c = incIdN ns w (idxN ns w w') then (1, 3)
  else if c = incIdN ns w' (idxN ns w' w) then (1, 1)
  else (1, 3 + c)

/-- The processing time and the due date of client `c` on day `i`. -/
def jobN (ns : List ℕ) (i c : ℕ) : ℕ × ℕ :=
  if i < lN ns * (nN ns + 1) then
    (if i % (nN ns + 1) < nN ns then
      vertexDayN ns ((i / (nN ns + 1)) * nN ns + i % (nN ns + 1)) c
    else validationDayN ns (i / (nN ns + 1)) c)
  else
    edgeDayN ns ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).1
      ((edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0)).2 c

/-- The fairness parameter of client `c`. -/
def kvN (ns : List ℕ) (c : ℕ) : ℕ :=
  if c = 0 then daysN ns else if c = 1 ∨ c = 2 then edgeN ns / 2 else 1

/-- The numbers of the image: the counts, the processing time and the due date of every job day
by day, and the fairness parameter of every client. -/
def outM (ns : List ℕ) : List ℕ :=
  [clN ns, daysN ns] ++ (List.range (daysN ns * clN ns)).flatMap (fun t =>
    [(jobN ns (t / clN ns) (t % clN ns)).1, (jobN ns (t / clN ns) (t % clN ns)).2]) ++
    (List.range (clN ns)).map (kvN ns)

section Image

variable (ns : List ℕ) (hc : CondM ns)

theorem deg_graphOf : Lax117284.Lemma14.deg (graphOf ns hc) = degN ns := by
  have hV : VM ns = (graphOf ns hc).vertices := rfl
  have hadj : ∀ w w', w < VM ns → w' < VM ns →
      (graphOf ns hc).adjAt w w' = decide (mat ns w w' = 1) :=
    fun w w' hw hw' => adjAt_graphOf ns hc hw hw'
  unfold Lax117284.Lemma14.deg degN
  rw [degree_eq _ ns hV hadj]

theorem span_graphOf : Lax117284.Lemma14.span (graphOf ns hc) = spanN ns := by
  unfold Lax117284.Lemma14.span spanN
  rw [deg_graphOf ns hc]; rfl

theorem clientCount_graphOf : Lax117284.Lemma14.clientCount (graphOf ns hc) = clN ns := by
  unfold Lax117284.Lemma14.clientCount clN
  rw [deg_graphOf ns hc]; rfl

theorem edgeCount_graphOf : (graphOf ns hc).edgeCount = edgeN ns :=
  edgeCount_eq _ ns rfl (fun w w' hw hw' => adjAt_graphOf ns hc hw hw')

theorem dayCount_graphOf : Lax117284.Lemma14.dayCount (graphOf ns hc) = daysN ns := by
  unfold Lax117284.Lemma14.dayCount daysN
  rw [edgeCount_graphOf ns hc]; rfl

theorem vertexDay_graphOf (w₀ c : ℕ) :
    Lax117284.Lemma14.vertexDay (graphOf ns hc) w₀ c = vertexDayN ns w₀ c := by
  unfold Lax117284.Lemma14.vertexDay vertexDayN
  rw [deg_graphOf ns hc, span_graphOf ns hc]
  rfl

theorem validationDay_graphOf (i₀ c : ℕ) :
    Lax117284.Lemma14.validationDay (graphOf ns hc) i₀ c = validationDayN ns i₀ c := by
  unfold Lax117284.Lemma14.validationDay validationDayN
  rw [deg_graphOf ns hc, span_graphOf ns hc]
  rfl

theorem edgeDay_graphOf (w w' c : ℕ) (hw : w < VM ns) (hw' : w' < VM ns) (hm : mat ns w w' = 1) :
    Lax117284.Lemma14.edgeDay (graphOf ns hc) w w' c = edgeDayN ns w w' c := by
  have hV : VM ns = (graphOf ns hc).vertices := rfl
  have hadj : ∀ w w', w < VM ns → w' < VM ns →
      (graphOf ns hc).adjAt w w' = decide (mat ns w w' = 1) :=
    fun w w' hw hw' => adjAt_graphOf ns hc hw hw'
  have hm' : mat ns w' w = 1 := by rw [← (passM_at ns hc hw hw').1]; exact hm
  have hinc : ∀ x q, Lax117284.Lemma14.incId (graphOf ns hc) x q = incIdN ns x q := by
    intro x q
    unfold Lax117284.Lemma14.incId incIdN
    rw [deg_graphOf ns hc]; rfl
  unfold Lax117284.Lemma14.edgeDay edgeDayN
  rw [span_graphOf ns hc, hinc, hinc, idxOf_nbrs _ ns hV hadj hw hw' hm,
    idxOf_nbrs _ ns hV hadj hw' hw hm']

theorem job_graphOf (i c : ℕ) (hi : i < daysN ns) :
    Lax117284.Lemma14.job (graphOf ns hc) i c = jobN ns i c := by
  unfold Lax117284.Lemma14.job jobN
  simp only [show (graphOf ns hc).colours = lN ns from rfl,
    show (graphOf ns hc).size = nN ns from rfl]
  by_cases h1 : i < lN ns * (nN ns + 1)
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : i % (nN ns + 1) < nN ns
    · rw [if_pos h2, if_pos h2, vertexDay_graphOf]
    · rw [if_neg h2, if_neg h2, validationDay_graphOf]
  · rw [if_neg h1, if_neg h1]
    have hV : VM ns = (graphOf ns hc).vertices := rfl
    have hadj : ∀ w w', w < VM ns → w' < VM ns →
        (graphOf ns hc).adjAt w w' = decide (mat ns w w' = 1) :=
      fun w w' hw hw' => adjAt_graphOf ns hc hw hw'
    rw [edgeList_eq _ ns hV hadj]
    have he : i - lN ns * (nN ns + 1) < (edgeCellsN ns).length := by
      have : (edgeCellsN ns).length = edgeN ns := by
        unfold edgeCellsN edgeN
        rw [List.length_map, List.countP_eq_length_filter]
      unfold daysN at hi
      omega
    have hmem := List.getElem_mem he
    rw [← List.getD_eq_getElem _ (0, 0) he] at hmem
    generalize (edgeCellsN ns).getD (i - lN ns * (nN ns + 1)) (0, 0) = q at hmem ⊢
    have hmem2 : q ∈ ((List.range (VM ns * VM ns)).filter (qualE ns)).map
        (fun t => (t / VM ns, t % VM ns)) := hmem
    obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hmem2
    obtain ⟨ht1, ht2⟩ := List.mem_filter.mp ht
    have htl := List.mem_range.mp ht1
    unfold qualE at ht2
    obtain ⟨hq1, hq2⟩ := of_decide_eq_true ht2
    obtain ⟨-, hw, hw'⟩ := cell_split ns t htl
    have hm : mat ns (t / VM ns) (t % VM ns) = 1 := by rw [← getD_cell ns t htl]; exact hq1
    rw [← hteq]
    exact edgeDay_graphOf ns hc _ _ c hw hw' hm

theorem inst_clients : (Lax117284.Lemma14.inst (graphOf ns hc)).clients = clN ns :=
  clientCount_graphOf ns hc

theorem inst_days : (Lax117284.Lemma14.inst (graphOf ns hc)).days = daysN ns :=
  dayCount_graphOf ns hc

theorem instToks_graphOf :
    InstSem.instToks (Lax117284.Lemma14.inst (graphOf ns hc)) = [clN ns, daysN ns] ++
      (List.range (daysN ns * clN ns)).flatMap (fun t =>
        [(jobN ns (t / clN ns) (t % clN ns)).1, (jobN ns (t / clN ns) (t % clN ns)).2]) := by
  have hC : 0 < clN ns := by unfold clN; omega
  unfold InstSem.instToks
  rw [inst_clients ns hc, inst_days ns hc]
  congr 1
  refine List.flatMap_congr fun t ht => ?_
  have ht' := List.mem_range.mp ht
  have hlt : t / clN ns < daysN ns := (Nat.div_lt_iff_lt_mul hC).2 ht'
  have hlt2 : t % clN ns < clN ns := Nat.mod_lt _ hC
  have h1 := Lax117284.Scheduling.Instance.pAt_coe (Lax117284.Lemma14.inst (graphOf ns hc))
    ⟨t / clN ns, by rw [inst_days ns hc]; exact hlt⟩ ⟨t % clN ns, by rw [inst_clients ns hc]; exact hlt2⟩
  have h2 := Lax117284.Scheduling.Instance.dAt_coe (Lax117284.Lemma14.inst (graphOf ns hc))
    ⟨t / clN ns, by rw [inst_days ns hc]; exact hlt⟩ ⟨t % clN ns, by rw [inst_clients ns hc]; exact hlt2⟩
  simp only [Fin.val_mk] at h1 h2
  have hj := job_graphOf ns hc (t / clN ns) (t % clN ns) hlt
  rw [h1, h2]
  show [(Lax117284.Lemma14.job (graphOf ns hc) (t / clN ns) (t % clN ns)).1,
    (Lax117284.Lemma14.job (graphOf ns hc) (t / clN ns) (t % clN ns)).2] = _
  rw [hj]

theorem kv_graphOf :
    (List.finRange (Lax117284.Lemma14.inst (graphOf ns hc)).clients).flatMap
      (fun j => encodeNat (Lax117284.Lemma14.kvec (graphOf ns hc) j)) =
      numCode ((List.range (clN ns)).map (kvN ns)) := by
  rw [flatMap_finRange]
  have : ((List.range (Lax117284.Lemma14.inst (graphOf ns hc)).clients).flatMap fun i =>
      if h : i < (Lax117284.Lemma14.inst (graphOf ns hc)).clients then
        encodeNat (Lax117284.Lemma14.kvec (graphOf ns hc) ⟨i, h⟩) else []) =
      (List.range (Lax117284.Lemma14.inst (graphOf ns hc)).clients).flatMap
        (fun c => encodeNat (kvN ns c)) := by
    refine List.flatMap_congr fun c hc' => ?_
    have := List.mem_range.mp hc'
    rw [dif_pos this]
    unfold Lax117284.Lemma14.kvec kvN
    rw [dayCount_graphOf ns hc, edgeCount_graphOf ns hc]
  rw [this, inst_clients ns hc]
  simp only [numCode, List.flatMap_map]

theorem out_graphOf :
    encodePerClient (Lax117284.Lemma14.inst (graphOf ns hc)) (Lax117284.Lemma14.kvec (graphOf ns hc))
      = numCode (outM ns) := by
  unfold encodePerClient
  rw [InstSem.encodeInstance_eq, instToks_graphOf, kv_graphOf]
  unfold outM
  rw [numCode_append, numCode_append, numCode_append]

end Image

/-- **The reduction writes the numbers of the constructed instance.** -/
theorem t14_eq (ts : List Tok) (hconf : Conforms EM ts)
    (hcond : CondM (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    Lax117284.Lemma14.reduce (code ts) =
      numCode (outM (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) := by
  classical
  obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
  have hg := (mis_gate (code ts)).2 ⟨ts, rfl, hconf, hcond⟩
  unfold Lax117284.Lemma14.reduce
  rw [dif_pos hg]
  have hG : graphOf _ hcond = hg.choose := by
    apply Lax117284Proofs.SourceInjectivity.mis_encode_inj
    rw [encode_graphOf _ hcond hshape, ← hts]
    exact hg.choose_spec.1.symm
  rw [← hG]
  exact out_graphOf _ hcond

/-- **A word that is not the code of an admissible stream is rejected.** -/
theorem t14_rej (w : Word)
    (h : ¬ ∃ ts : List Tok, w = code ts ∧ Conforms EM ts ∧
      CondM (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    Lax117284.Lemma14.reduce w = rejectedPerClient := by
  classical
  unfold Lax117284.Lemma14.reduce
  rw [dif_neg (fun hg => h ((mis_gate w).1 hg))]

theorem rejectedPerClient_eq : rejectedPerClient = rejected := by
  unfold rejectedPerClient rejected encodePerClient encodeUniform
  congr 1

end Lax117284Proofs.Machine.MisSem
