import Lax808846Proofs.Reasoning
import Lax808846Proofs.Tactic

/-!
The word as the machine sees it.

An admissible word is a compressed sparse row block followed by the number `n` of left vertices
(`Lax117284.BipartiteGraph.EncodesBipartite`). The machine reads the whole word into one array
`"a"` and addresses it by position: `V = a[0]`, `n = a[len - 1]`, the offsets `a[2 + i]`, the
targets `a[3 + V + s]`. This file names those positions (`Vw`, `nw`, `offw`, `tgtw`), the
adjacency across the split they define (`adjOff`, `adjw`), and `Good x` — the handful of
arithmetic facts about an admissible word the program's proofs use, which `Bridge.lean` derives
from `EncodesBipartite`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The number of vertices: the first entry. -/
def Vw (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of left vertices: the last entry. -/
def nw (x : List ℕ) : ℕ := x.getD (x.length - 1) 0

/-- The number of right vertices. -/
def mw (x : List ℕ) : ℕ := Vw x - nw x

/-- The `i`-th offset. -/
def offw (x : List ℕ) (i : ℕ) : ℕ := x.getD (2 + i) 0

/-- The `s`-th target. -/
def tgtw (x : List ℕ) (s : ℕ) : ℕ := x.getD (3 + Vw x + s) 0

/-- The length of the row of a left vertex. -/
def rowlen (off : ℕ → ℕ) (l : ℕ) : ℕ := off (l + 1) - off l

/-- The adjacency across the split of a CSR word with offsets `off`, targets `tgt` and `n` left
vertices: left vertex `l` is adjacent to right index `j` when its row lists the vertex `n + j`. -/
def adjOff (off tgt : ℕ → ℕ) (n : ℕ) (l j : ℕ) : Prop :=
  ∃ s, off l ≤ s ∧ s < off (l + 1) ∧ tgt s = n + j

/-- The adjacency across the split of a word. -/
def adjw (x : List ℕ) : ℕ → ℕ → Prop := adjOff (offw x) (tgtw x) (nw x)

/-- **What the machine needs of a word**: `n ≤ V`, nondecreasing offsets, the length as declared,
the second entry consistent with the last offset, every target a vertex, and every target of a
left row a right vertex. -/
structure Good (x : List ℕ) : Prop where
  nV : nw x ≤ Vw x
  mono : ∀ i < Vw x, offw x i ≤ offw x (i + 1)
  len : x.length = 4 + Vw x + offw x (Vw x)
  e2 : 2 * x.getD 1 0 = offw x (Vw x)
  tgt_lt : ∀ s < offw x (Vw x), tgtw x s < Vw x
  rows : ∀ l < nw x, ∀ s, offw x l ≤ s → s < offw x (l + 1) → nw x ≤ tgtw x s

namespace Good

variable {x : List ℕ} (h : Good x)
include h

theorem off_le_last : ∀ i ≤ Vw x, offw x i ≤ offw x (Vw x) := by
  have key : ∀ k i, i + k ≤ Vw x → offw x i ≤ offw x (i + k) := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := h.mono (i + k) (by omega)
      calc offw x i ≤ offw x (i + k) := h1
        _ ≤ offw x (i + k + 1) := h2
        _ = offw x (i + (k + 1)) := by rw [Nat.add_assoc]
  intro i hi
  have := key (Vw x - i) i (by omega)
  rwa [Nat.add_sub_cancel' hi] at this

theorem four_le : 4 ≤ x.length := by have := h.len; omega

theorem getD_lt (p : ℕ) (hp : p < x.length) : x.getD p 0 < x.length := by
  have hlen := h.len
  have hlast := h.off_le_last
  rcases Nat.lt_or_ge p 2 with h2 | h2
  · interval_cases p
    · show Vw x < x.length; omega
    · have := h.e2; omega
  rcases Nat.lt_or_ge p (3 + Vw x) with h3 | h3
  · have e : x.getD p 0 = offw x (p - 2) := by unfold offw; congr 1; omega
    rw [e]; have := hlast (p - 2) (by omega); omega
  rcases Nat.lt_or_ge p (3 + Vw x + offw x (Vw x)) with h4 | h4
  · have e : x.getD p 0 = tgtw x (p - 3 - Vw x) := by unfold tgtw; congr 1; omega
    rw [e]; have := h.tgt_lt (p - 3 - Vw x) (by omega); omega
  · have e : p = x.length - 1 := by omega
    rw [e]; show nw x < x.length; have := h.nV; omega

theorem ent_lt : ∀ v ∈ x, v < x.length := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
  have := h.getD_lt i hi
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this

theorem V_lt : Vw x < x.length := h.getD_lt 0 (by have := h.four_le; omega)

theorem off_lt_len {i : ℕ} (hi : i ≤ Vw x) : offw x i < x.length := by
  have := h.off_le_last i hi; have := h.len; omega

/-- The position of an offset is inside the word. -/
theorem offPos_lt {i : ℕ} (hi : i ≤ Vw x) : 2 + i < x.length := by have := h.len; omega

/-- The position of a slot is inside the word. -/
theorem tgtPos_lt {s : ℕ} (hs : s < offw x (Vw x)) : 3 + Vw x + s < x.length := by
  have := h.len; omega

/-- A slot of a left row is a slot of the target array. -/
theorem slot_lt {l s : ℕ} (hl : l < nw x) (hs : s < offw x (l + 1)) : s < offw x (Vw x) := by
  have := h.off_le_last (l + 1) (by have := h.nV; omega); omega

/-- The candidate a slot of a left row names is a right index. -/
theorem cand_lt {l s : ℕ} (hl : l < nw x) (hs1 : offw x l ≤ s) (hs2 : s < offw x (l + 1)) :
    tgtw x s - nw x < mw x := by
  have h1 := h.rows l hl s hs1 hs2
  have h2 := h.tgt_lt s (h.slot_lt hl hs2)
  unfold mw; omega

theorem cand_eq {l s : ℕ} (hl : l < nw x) (hs1 : offw x l ≤ s) (hs2 : s < offw x (l + 1)) :
    tgtw x s = nw x + (tgtw x s - nw x) := by
  have h1 := h.rows l hl s hs1 hs2
  omega

theorem rowlen_le {l : ℕ} (hl : l < nw x) : rowlen (offw x) l ≤ offw x (Vw x) := by
  unfold rowlen
  have := h.off_le_last (l + 1) (by have := h.nV; omega); omega

theorem m_lt : mw x < x.length := by
  have := h.V_lt; unfold mw; omega

theorem n_lt : nw x < x.length := by
  have := h.V_lt; have := h.nV; omega

end Good

theorem nw_eq_getLastD (x : List ℕ) : nw x = x.getLastD 0 := by
  unfold nw
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-! ### The word in the array `"a"` -/

/-- The array `"a"` holds the word. -/
def ArrOK (x : List ℕ) (σ : Env) : Prop := σ.arrs "a" = arrOf x.length (fun t => x.getD t 0)

theorem ArrOK.length {x : List ℕ} {σ : Env} (h : ArrOK x σ) : (σ.arrs "a").length = x.length := by
  rw [h]; simp

theorem ArrOK.getD {x : List ℕ} {σ : Env} (h : ArrOK x σ) {p : ℕ} (hp : p < x.length) :
    (σ.arrs "a").getD p 0 = x.getD p 0 := by
  rw [h]; exact getD_arrOf _ hp

theorem ArrOK.getD_tgtw {x : List ℕ} {σ : Env} (h : ArrOK x σ) (hg : Good x) {s : ℕ}
    (hs : s < offw x (Vw x)) : (σ.arrs "a").getD (3 + Vw x + s) 0 = tgtw x s :=
  h.getD (hg.tgtPos_lt hs)

theorem ArrOK.congr {x : List ℕ} {σ σ' : Env} (h : ArrOK x σ) (ha : σ'.arrs "a" = σ.arrs "a") :
    ArrOK x σ' := by unfold ArrOK; rw [ha]; exact h

end Lax117284Proofs.Bipartite.Ram2
