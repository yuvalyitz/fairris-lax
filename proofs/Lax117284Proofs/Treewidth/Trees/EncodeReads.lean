import Mathlib.Data.List.GetD
import Lax117284Proofs.Treewidth.Trees.WordBridge

/-!
# The canonical word `NT.encode` (T2)

`Reads D b t`: the records of `D` from node `b` on are `NT.recs b t`.  `NT.encode t` reads `t` at `0`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

/-- The record of node `i`. -/
def recAt (D : List ℕ) (i : ℕ) : ℕ × ℕ × ℕ := (kind D i, vertex D i, other D i)

/-- The records of `D` from node `b` on are those of `t`. -/
def Reads (D : List ℕ) (b : ℕ) (t : NT) : Prop :=
  ∀ j, j < t.size → recAt D (b + j) = (NT.recs b t).getD j (0, 0, 0)

lemma length_recs (t : NT) : ∀ b, (NT.recs b t).length = t.size := by
  induction t with
  | leaf => intro b; simp [NT.recs, NT.size]
  | intro v c ih => intro b; simp [NT.recs, NT.size, ih]
  | forget v c ih => intro b; simp [NT.recs, NT.size, ih]
  | join x y ihx ihy => intro b; simp [NT.recs, NT.size, ihx, ihy]; omega

lemma recs_join (b : ℕ) (x y : NT) :
    NT.recs b (NT.join x y) = NT.recs b y ++ NT.recs (b + y.size) x ++ [(3, 0, b + y.size - 1)] := by
  simp only [NT.recs, length_recs]

lemma size_pos (t : NT) : 0 < t.size := by
  cases t <;> simp [NT.size]

lemma Reads.leaf {D : List ℕ} {b : ℕ} (h : Reads D b NT.leaf) : recAt D b = (0, 0, 0) := by
  simpa [NT.recs, NT.size] using h 0 (by simp [NT.size])

lemma Reads.intro {D : List ℕ} {b v : ℕ} {c : NT} (h : Reads D b (NT.intro v c)) :
    Reads D b c ∧ recAt D (b + c.size) = (1, v, 0) := by
  constructor
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append _ _ _ _ (by rw [length_recs]; exact hj)]
  · have := h c.size (by simp [NT.size])
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append_right _ _ _ _ (by rw [length_recs])]
    simp [length_recs]

lemma Reads.forget {D : List ℕ} {b v : ℕ} {c : NT} (h : Reads D b (NT.forget v c)) :
    Reads D b c ∧ recAt D (b + c.size) = (2, v, 0) := by
  constructor
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append _ _ _ _ (by rw [length_recs]; exact hj)]
  · have := h c.size (by simp [NT.size])
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append_right _ _ _ _ (by rw [length_recs])]
    simp [length_recs]

lemma Reads.join {D : List ℕ} {b : ℕ} {x y : NT} (h : Reads D b (NT.join x y)) :
    Reads D b y ∧ Reads D (b + y.size) x ∧
      recAt D (b + y.size + x.size) = (3, 0, b + y.size - 1) := by
  have hx := size_pos x
  have hy := size_pos y
  have hly := length_recs y b
  have hlx := length_recs x (b + y.size)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this, recs_join, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  · intro j hj
    have := h (y.size + j) (by simp [NT.size]; omega)
    rw [← Nat.add_assoc] at this
    rw [this, recs_join, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega)]
    congr 2
    omega
  · have := h (y.size + x.size) (by simp [NT.size]; omega)
    rw [← Nat.add_assoc] at this
    rw [this, recs_join, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have : y.size + x.size - (NT.recs b y).length - (NT.recs (b + y.size) x).length = 0 := by omega
    rw [this]; rfl

lemma flat_get (rs : List (ℕ × ℕ × ℕ)) : ∀ i, i < rs.length →
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i) 0 = (rs.getD i (0, 0, 0)).1 ∧
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i + 1) 0 = (rs.getD i (0, 0, 0)).2.1 ∧
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i + 2) 0 = (rs.getD i (0, 0, 0)).2.2 := by
  induction rs with
  | nil => intro i hi; simp at hi
  | cons r rs ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      have := ih i (by simpa using hi)
      have e0 : 3 * (i + 1) = (3 * i) + 1 + 1 + 1 := by omega
      simp only [List.flatMap_cons, e0, List.cons_append, List.nil_append,
        Nat.add_assoc, List.getD_eq_getElem?_getD] at this ⊢
      simpa [Nat.add_assoc] using this

lemma nodeCount_encode (t : NT) : nodeCount t.encode = t.size := by
  simp [nodeCount, NT.encode, length_recs]

lemma length_encode (t : NT) : t.encode.length = 1 + 3 * t.size := by
  simp [NT.encode, length_recs]; omega

lemma reads_encode (t : NT) : Reads t.encode 0 t := by
  intro j hj
  have hlen : j < (NT.recs 0 t).length := by rw [length_recs]; exact hj
  obtain ⟨h0, h1, h2⟩ := flat_get (NT.recs 0 t) j hlen
  simp only [recAt, kind, vertex, other, NT.encode, Nat.zero_add]
  have e1 : 1 + 3 * j = 3 * j + 1 := by omega
  have e2 : 2 + 3 * j = 3 * j + 1 + 1 := by omega
  have e3 : 3 + 3 * j = 3 * j + 1 + 1 + 1 := by omega
  rw [e1, e2, e3]
  simp only [List.getD_cons_succ]
  rw [h0, h1, h2]

end Word

end Lax117284Proofs.Treewidth.Trees
