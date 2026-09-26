import Lax117284Proofs.UnitPGraph
import Lax808846Proofs.Tactic

/-!
The conversion, guarded, of the table words of `UnitPGraph` to the bipartite words of
`lax-817977`: a word `[R, C] ++ table` is converted to the compressed sparse row word `csrOf x`
of its bipartite graph (left vertices `0 .. R - 1`, right vertices `R .. R + C - 1`, the row of
a left vertex listing the columns of its nonzero entries, each twice, so that the target array
has the even length the encoding demands; the rows of the right vertices are empty), on which
the cited decider of `lax-817977` decides whether a matching saturates the left side. The guards
answer a fixed word at once when the table is shorter than its header claims, so that the whole
program runs in time polynomial in the bit size of the word on *every* word; on the words that
are tables — every image of the reduction of `USem` — the cited decider then answers as the
function `gfun` says (`MatchWord`).

This file: the guard predicate `Heavy`, the function `gfun` the two stages compute together and
the function `conv` the conversion computes; the CSR word `csrP x R C` and its arithmetic; the
IMP+ programs reading the word into `t` and converting it into `a`, with their specifications.
`MatchWord.lean` reads the word with the accessors of the cited encoding, and `MatchRam.lean`
adds the guards, the printing of `a`, the layout and the transfer to the machine.
-/

namespace Lax117284Proofs.Machine.MatchGuard

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284Proofs.UnitPGraph (Yes decodeAdj)
open scoped Classical

variable {B : ℕ}

/-- The words on which the search runs. -/
def Heavy (x : List ℕ) : Prop :=
  1 ≤ x.getD 0 0 ∧ 1 ≤ x.getD 1 0 ∧ (x.getD 0 0 - 1) * x.getD 1 0 < x.length - 2 ∧
    x.getD 1 0 ≤ x.length

/-- What the two stages, the conversion and the cited decider, compute together. -/
noncomputable def gfun (x : List ℕ) : List ℕ :=
  if Heavy x then [if Yes x then 1 else 0] else if x.getD 0 0 = 0 then [1] else [0]

/-! ### The compressed sparse row word of a table -/

/-- The entry of the table in row `r`, column `c`. -/
def tab (x : List ℕ) (C r c : ℕ) : ℕ := x.getD (2 + r * C + c) 0

/-- The first `c` columns of row `r`, as targets `R + c'` of the nonzero entries, each listed
twice: the target array then has an even length, as the encoding demands, without padding. -/
def rowPre (x : List ℕ) (R C r c : ℕ) : List ℕ :=
  ((List.range c).filter (fun c' => tab x C r c' ≠ 0)).flatMap (fun c' => [R + c', R + c'])

/-- The row of a left vertex. -/
def row (x : List ℕ) (R C r : ℕ) : List ℕ := rowPre x R C r C

/-- The rows `0 .. r - 1`, laid end to end. -/
def pre (x : List ℕ) (R C r : ℕ) : List ℕ := (List.range r).flatMap (row x R C)

/-- The offset of row `r`. -/
def off (x : List ℕ) (R C r : ℕ) : ℕ := (pre x R C r).length

/-- The length of the target array. -/
def E (x : List ℕ) (R C : ℕ) : ℕ := off x R C R

/-- The offsets of the word: those of the left rows, then the end for every right vertex. -/
def off' (x : List ℕ) (R C i : ℕ) : ℕ := if i ≤ R then off x R C i else E x R C

/-- The target at slot `s`. -/
def tgt (x : List ℕ) (R C s : ℕ) : ℕ := (pre x R C R).getD s 0

/-- **The CSR word** of the table word with `R` rows and `C` columns: the number of vertices,
the number of edges (half the length of the target array), the offsets, the targets, and the
number of left vertices. -/
def csrP (x : List ℕ) (R C : ℕ) : List ℕ :=
  (R + C) :: (E x R C / 2) ::
    (arrOf (R + C + 1) (off' x R C) ++ (arrOf (E x R C) (tgt x R C) ++ [R]))

/-- The CSR word of a table word. -/
def csrOf (x : List ℕ) : List ℕ := csrP x (x.getD 0 0) (x.getD 1 0)

/-- The word answered when there is no left vertex: the empty graph, whose empty left side is
saturated by the empty matching. -/
def W1 : List ℕ := [0, 0, 0, 0]

/-- The word answered when the table is not searched: one isolated left vertex, which no
matching saturates. -/
def W0 : List ℕ := [1, 0, 0, 0, 1]

/-- **What the guarded conversion computes**: the CSR word of a table, the fixed words
otherwise. -/
noncomputable def conv (x : List ℕ) : List ℕ :=
  if Heavy x then csrOf x else if x.getD 0 0 = 0 then W1 else W0

section Rows

variable (x : List ℕ) (R C : ℕ)

theorem rowPre_zero (r : ℕ) : rowPre x R C r 0 = [] := by simp [rowPre]

theorem rowPre_succ (r c : ℕ) :
    rowPre x R C r (c + 1) =
      rowPre x R C r c ++ (if tab x C r c ≠ 0 then [R + c, R + c] else []) := by
  unfold rowPre
  rw [List.range_succ, List.filter_append, List.flatMap_append]
  congr 1
  by_cases h : tab x C r c ≠ 0 <;> simp [h]

theorem length_rowPre_le (r c : ℕ) : (rowPre x R C r c).length ≤ 2 * c := by
  induction c with
  | zero => simp [rowPre_zero]
  | succ c ih =>
    rw [rowPre_succ, List.length_append]
    split_ifs <;> simp <;> omega

theorem length_rowPre_even (r c : ℕ) : (rowPre x R C r c).length % 2 = 0 := by
  induction c with
  | zero => simp [rowPre_zero]
  | succ c ih =>
    rw [rowPre_succ, List.length_append]
    split_ifs <;> simp <;> omega

theorem rowPre_prefix (r c : ℕ) (hc : c ≤ C) : ∃ l, row x R C r = rowPre x R C r c ++ l := by
  have key : ∀ k, ∃ l, rowPre x R C r (c + k) = rowPre x R C r c ++ l := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp⟩
    | succ k ih =>
      obtain ⟨l, hl⟩ := ih
      rw [← Nat.add_assoc, rowPre_succ, hl, List.append_assoc]
      exact ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := key (C - c)
  rw [Nat.add_sub_cancel' hc] at hl
  exact ⟨l, hl⟩

theorem mem_row {r v : ℕ} : v ∈ row x R C r ↔ ∃ c < C, tab x C r c ≠ 0 ∧ v = R + c := by
  unfold row rowPre
  simp only [List.mem_flatMap, List.mem_filter, List.mem_range, decide_eq_true_eq,
    List.mem_cons, List.not_mem_nil, or_false, or_self]
  constructor
  · rintro ⟨c, ⟨hc, ht⟩, rfl⟩; exact ⟨c, hc, ht, rfl⟩
  · rintro ⟨c, hc, ht, rfl⟩; exact ⟨c, ⟨hc, ht⟩, rfl⟩

theorem pre_succ (r : ℕ) : pre x R C (r + 1) = pre x R C r ++ row x R C r := by
  unfold pre
  rw [List.range_succ, List.flatMap_append]
  simp

theorem off_zero : off x R C 0 = 0 := by simp [off, pre]

theorem off_succ (r : ℕ) : off x R C (r + 1) = off x R C r + (row x R C r).length := by
  unfold off
  rw [pre_succ, List.length_append]

theorem off_le_mul (r : ℕ) : off x R C r ≤ 2 * (r * C) := by
  induction r with
  | zero => simp [off_zero]
  | succ r ih =>
    rw [off_succ]
    have h : (row x R C r).length ≤ 2 * C := length_rowPre_le x R C r C
    have e : 2 * ((r + 1) * C) = 2 * (r * C) + 2 * C := by ring
    omega

theorem off_even (r : ℕ) : off x R C r % 2 = 0 := by
  induction r with
  | zero => simp [off_zero]
  | succ r ih =>
    rw [off_succ]
    have h := length_rowPre_even x R C r C
    unfold row at h ⊢
    omega

theorem pre_prefix {r : ℕ} (hr : r ≤ R) : ∃ l, pre x R C R = pre x R C r ++ l := by
  have key : ∀ k, ∃ l, pre x R C (r + k) = pre x R C r ++ l := by
    intro k
    induction k with
    | zero => exact ⟨[], by simp⟩
    | succ k ih =>
      obtain ⟨l, hl⟩ := ih
      rw [← Nat.add_assoc, pre_succ, hl, List.append_assoc]
      exact ⟨_, rfl⟩
  obtain ⟨l, hl⟩ := key (R - r)
  rw [Nat.add_sub_cancel' hr] at hl
  exact ⟨l, hl⟩

theorem off_mono {r r' : ℕ} (h : r ≤ r') : off x R C r ≤ off x R C r' := by
  obtain ⟨k, rfl⟩ : ∃ k, r' = r + k := ⟨r' - r, by omega⟩
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [← Nat.add_assoc, off_succ]; omega

theorem mem_pre {v : ℕ} (h : v ∈ pre x R C R) : ∃ c < C, v = R + c := by
  unfold pre at h
  obtain ⟨r, -, hv⟩ := List.mem_flatMap.1 h
  obtain ⟨c, hc, -, rfl⟩ := (mem_row x R C).1 hv
  exact ⟨c, hc, rfl⟩

theorem getD_app_left {a b : List ℕ} {s : ℕ} (h : s < a.length) : (a ++ b).getD s 0 = a.getD s 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {a b : List ℕ} {s : ℕ} (h : a.length ≤ s) :
    (a ++ b).getD s 0 = b.getD (s - a.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_of_length_le {a : List ℕ} {s : ℕ} (h : a.length ≤ s) : a.getD s 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The target of slot `off r + k` is entry `k` of row `r`. -/
theorem tgt_row {r k : ℕ} (hr : r < R) (hk : k < (row x R C r).length) :
    tgt x R C (off x R C r + k) = (row x R C r).getD k 0 := by
  obtain ⟨l, hl⟩ := pre_prefix x R C (r := r + 1) hr
  unfold tgt
  rw [hl, pre_succ, List.append_assoc, getD_app_right (by unfold off; omega)]
  unfold off
  rw [Nat.add_sub_cancel_left, getD_app_left hk]

theorem tgt_lt_V {s : ℕ} (hs : s < E x R C) : tgt x R C s < R + C := by
  have hmem : tgt x R C s ∈ pre x R C R := by
    unfold tgt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
    exact List.getElem_mem _
  obtain ⟨c, hc, he⟩ := mem_pre x R C hmem
  omega

theorem R_le_tgt {s : ℕ} (hs : s < E x R C) : R ≤ tgt x R C s := by
  have hmem : tgt x R C s ∈ pre x R C R := by
    unfold tgt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
    exact List.getElem_mem _
  obtain ⟨c, hc, he⟩ := mem_pre x R C hmem
  omega

theorem E_le : E x R C ≤ 2 * (R * C) := off_le_mul x R C R

theorem E_even : 2 * (E x R C / 2) = E x R C := by
  have := off_even x R C R
  unfold E; omega

/-- The end is the offset at `V`, in either case. -/
theorem off'_V : off' x R C (R + C) = E x R C := by
  unfold off'
  split_ifs with h
  · have hC : C = 0 := by omega
    subst hC
    rfl
  · rfl

theorem off'_of_le {i : ℕ} (hi : i ≤ R) : off' x R C i = off x R C i := if_pos hi

theorem off'_of_lt {i : ℕ} (hi : R < i) : off' x R C i = E x R C := if_neg (by omega)

theorem off'_le_E (i : ℕ) : off' x R C i ≤ E x R C := by
  unfold off'
  split_ifs with h
  · exact off_mono x R C h
  · exact le_rfl

theorem off'_mono (i : ℕ) : off' x R C i ≤ off' x R C (i + 1) := by
  unfold off'
  split_ifs with h1 h2 h2
  · exact off_mono x R C (by omega)
  · exact off_mono x R C h1
  · omega
  · exact le_rfl

end Rows

/-! ### Reading the CSR word -/

section Read

variable (x : List ℕ) (R C : ℕ)

theorem length_csrP : (csrP x R C).length = 4 + (R + C) + E x R C := by
  simp [csrP]; omega

theorem getD_cons2 (a b : ℕ) (l : List ℕ) (i : ℕ) : (a :: b :: l).getD (2 + i) 0 = l.getD i 0 := by
  rw [show 2 + i = i + 1 + 1 by omega]
  rfl

theorem csrP_zero : (csrP x R C).getD 0 0 = R + C := rfl

theorem csrP_one : (csrP x R C).getD 1 0 = E x R C / 2 := rfl

theorem csrP_off {i : ℕ} (hi : i ≤ R + C) : (csrP x R C).getD (2 + i) 0 = off' x R C i := by
  unfold csrP
  rw [getD_cons2, getD_app_left (by simp; omega), getD_arrOf _ (by omega)]

theorem csrP_tgt {s : ℕ} (hs : s < E x R C) :
    (csrP x R C).getD (3 + (R + C) + s) 0 = tgt x R C s := by
  unfold csrP
  rw [show 3 + (R + C) + s = 2 + (R + C + 1 + s) by omega, getD_cons2,
    getD_app_right (by simp), length_arrOf, Nat.add_sub_cancel_left, getD_app_left (by simpa),
    getD_arrOf _ hs]

theorem csrP_last : (csrP x R C).getD (3 + (R + C) + E x R C) 0 = R := by
  unfold csrP
  rw [show 3 + (R + C) + E x R C = 2 + (R + C + 1 + E x R C) by omega, getD_cons2,
    getD_app_right (by simp), length_arrOf, Nat.add_sub_cancel_left,
    getD_app_right (by simp), length_arrOf, Nat.sub_self]
  rfl

/-- The last entry of the word is the number of left vertices. -/
theorem csrP_getLastD : (csrP x R C).getLastD 0 = R := by
  unfold csrP
  rw [show (R + C) :: (E x R C / 2) :: (arrOf (R + C + 1) (off' x R C) ++
      (arrOf (E x R C) (tgt x R C) ++ [R])) =
      ((R + C) :: (E x R C / 2) :: (arrOf (R + C + 1) (off' x R C) ++
        arrOf (E x R C) (tgt x R C))) ++ [R] by simp]
  exact List.getLastD_concat

/-- Every entry of the word is small. -/
theorem mem_csrP_le {v : ℕ} (hv : v ∈ csrP x R C) : v ≤ R + C + E x R C := by
  unfold csrP arrOf at hv
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | ⟨i, -, rfl⟩ | ⟨s, hs, rfl⟩ | rfl
  · omega
  · omega
  · have := off'_le_E x R C i; omega
  · have := tgt_lt_V x R C hs; omega
  · omega

end Read

/-! ### The machine: the word in `t` -/

/-- The word is in the array `t` (of some length at least the word's; the cells beyond read
`0`, as `getD` does). -/
def TabOK (x : List ℕ) (Lt : ℕ) (σ : Env) : Prop :=
  σ.arrs "t" = arrOf Lt (fun i => x.getD i 0)

theorem TabOK.length {x : List ℕ} {Lt : ℕ} {σ : Env} (h : TabOK x Lt σ) :
    (σ.arrs "t").length = Lt := by rw [h]; simp

theorem TabOK.getD {x : List ℕ} {Lt : ℕ} {σ : Env} (h : TabOK x Lt σ) {i : ℕ} (hi : i < Lt) :
    (σ.arrs "t").getD i 0 = x.getD i 0 := by rw [h]; exact getD_arrOf _ hi

theorem TabOK.congr {x : List ℕ} {Lt : ℕ} {σ σ' : Env} (h : TabOK x Lt σ)
    (ha : σ'.arrs "t" = σ.arrs "t") : TabOK x Lt σ' := by unfold TabOK; rw [ha]; exact h

theorem getD_lt_of_mem {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 0 < B) (i : ℕ) :
    x.getD i 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact hB
  · exact hx v (List.mem_of_getElem? h)

/-- One entry: read it, store it, advance. -/
def readTBody : Com :=
  .seq (.read "v")
    (.seq (.store "t" (.var "rt") (.var "v")) (.assign "rt" (.add (.var "rt") (.lit 1))))

/-- Read the whole word into `t`: `rt := 0; while rt < len do readTBody`. -/
def readT : Com :=
  .seq (.assign "rt" (.lit 0)) (.while (.lt (.var "rt") (.var "len")) readTBody)

/-- Invariant of the read: `rt` entries consumed and stored. -/
def ReadInv (x : List ℕ) (Lt : ℕ) (σ : Env) : Prop :=
  σ.vars "len" = x.length ∧ σ.vars "rt" ≤ x.length ∧ σ.inp = x.drop (σ.vars "rt") ∧
    σ.arrs "t" = arrOf Lt (fun i => if i < σ.vars "rt" then x.getD i 0 else 0)

theorem readTBody_spec {x : List ℕ} {Lt : ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B)
    (hLt : x.length ≤ Lt) :
    Spec B (fun σ => ReadInv x Lt σ ∧ σ.vars "rt" < x.length) readTBody
      (fun σ σ' => ReadInv x Lt σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 10 := by
  rintro σ ⟨⟨hl, hrt, hinp, ha⟩, hlt⟩
  have hlen : (σ.arrs "t").length = Lt := by rw [ha]; simp
  have hdrop : σ.inp = x[σ.vars "rt"]'hlt :: x.drop (σ.vars "rt" + 1) := by
    rw [hinp, List.drop_eq_getElem_cons hlt]
  have hgetE : x[σ.vars "rt"]?.getD 0 = x[σ.vars "rt"]'hlt := by
    rw [List.getElem?_eq_getElem hlt]; rfl
  have htail : σ.inp.tail = x.drop (σ.vars "rt" + 1) := by rw [hdrop]; rfl
  have hne : σ.inp ≠ [] := by rw [hdrop]; exact List.cons_ne_nil _ _
  have hhead' : σ.inp.head?.getD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv' : σ.inp.head?.getD 0 < B := by rw [hhead']; exact hx _ (List.getElem_mem hlt)
  have hhead : σ.inp.headD 0 = x[σ.vars "rt"]'hlt := by rw [hdrop]; rfl
  have hv : σ.inp.headD 0 < B := by rw [hhead]; exact hx _ (List.getElem_mem hlt)
  unfold readTBody
  run_vcg
  all_goals (simp [ReadInv, hl, htail]; try omega)
  refine ⟨hlt, ?_⟩
  rw [ha, set_arrOf]
  refine arrOf_congr (fun k _ => ?_)
  by_cases hk : k = σ.vars "rt"
  · subst hk; simp [hhead', hgetE]
  · simp only [hk, if_false]
    split_ifs <;> first | rfl | omega

/-- **The read leaves the word in `t`.** -/
theorem readT_spec {x : List ℕ} {Lt : ℕ} (hx : ∀ v ∈ x, v < B) (hlB : x.length < B)
    (hLt : x.length ≤ Lt) :
    Spec B (fun σ => σ.vars "len" = x.length ∧ σ.inp = x ∧ σ.arrs "t" = arrOf Lt (fun _ => 0))
      readT (fun _ σ' => σ'.inp = [] ∧ TabOK x Lt σ' ∧ σ'.vars "len" = x.length)
      ((10 + 4) * x.length + 6) := by
  have hloop := Spec.forRangeZero (B := B) (c := readTBody) "rt" "len" (ReadInv x Lt) x.length 10
    hlB (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1) (readTBody_spec hx hlB hLt)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hl, hinp, ha⟩
    refine ⟨by simpa using hl, by simp, by simpa using hinp, ?_⟩
    simpa using ha
  · rintro σ σ' _ ⟨⟨hl, -, hinp, ha⟩, hrt⟩
    rw [hrt] at hinp ha
    refine ⟨?_, ?_, hl⟩
    · rw [hinp]; exact List.drop_eq_nil_of_le le_rfl
    · unfold TabOK
      rw [ha]
      refine arrOf_congr (fun k _ => ?_)
      by_cases hk : k < x.length
      · simp [hk]
      · simp only [hk, if_false]
        exact (getD_of_length_le (by omega)).symm

/-! ### The machine: the table converted to its CSR word -/

/-- The heavy words, in the numbers the machine holds. -/
structure HC (x : List ℕ) (R C : ℕ) : Prop where
  R1 : 1 ≤ R
  C1 : 1 ≤ C
  RC : R * C ≤ 2 * x.length
  Rle : R ≤ x.length
  Cle : C ≤ x.length

theorem HC.of_heavy {x : List ℕ} (h : Heavy x) : HC x (x.getD 0 0) (x.getD 1 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : x.getD 0 0 * x.getD 1 0 = (x.getD 0 0 - 1) * x.getD 1 0 + x.getD 1 0 := by
    obtain ⟨k, hk⟩ : ∃ k, x.getD 0 0 = k + 1 := ⟨x.getD 0 0 - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.succ_mul]
  have h5 : x.getD 0 0 - 1 ≤ (x.getD 0 0 - 1) * x.getD 1 0 := Nat.le_mul_of_pos_right _ h2
  exact ⟨h1, h2, by omega, by omega, h4⟩

/-- The length of the CSR word. -/
def Lc (x : List ℕ) (R C : ℕ) : ℕ := 4 + (R + C) + E x R C

theorem Lc_eq (x : List ℕ) (R C : ℕ) : (csrP x R C).length = Lc x R C := length_csrP x R C

theorem HC.hE {x : List ℕ} {R C : ℕ} (h : HC x R C) : E x R C ≤ 4 * x.length := by
  have := E_le x R C; have := h.RC; omega

theorem HC.hLc {x : List ℕ} {R C : ℕ} (h : HC x R C) : Lc x R C ≤ 6 * x.length + 5 := by
  have := h.hE; have := h.Rle; have := h.Cle
  unfold Lc; omega

/-- The array `a` during the conversion: `k` offsets written (positions `3 .. 2 + k`), `P`
targets written. -/
def AF (x : List ℕ) (R C k P t : ℕ) : ℕ :=
  if t = 0 then R + C
  else if 3 ≤ t ∧ t ≤ 2 + k then off x R C (t - 2)
  else if 3 + (R + C) ≤ t ∧ t < 3 + (R + C) + P then tgt x R C (t - 3 - (R + C))
  else 0

/-- The array `a` after the rows, with `i` right vertices' offsets written. -/
def AT (x : List ℕ) (R C i t : ℕ) : ℕ :=
  if 2 + R < t ∧ t ≤ 2 + R + i then E x R C else AF x R C R (E x R C) t

/-- The array `a` at the end of the conversion. -/
def AFin (x : List ℕ) (R C t : ℕ) : ℕ :=
  if t = 1 then E x R C / 2 else if t = 3 + (R + C) + E x R C then R else AT x R C C t

section ArrFun

variable (x : List ℕ) (R C : ℕ)

theorem AF_succ_of_ne {k P t : ℕ} (h : t ≠ 3 + (R + C) + P) :
    AF x R C k (P + 1) t = AF x R C k P t := by
  unfold AF
  split_ifs <;> first | rfl | omega

theorem AF_at {k P : ℕ} (hk : k ≤ R) :
    AF x R C k (P + 1) (3 + (R + C) + P) = tgt x R C P := by
  unfold AF
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem AF_row_of_ne {r P t : ℕ} (h : t ≠ 3 + r) :
    AF x R C (r + 1) P t = AF x R C r P t := by
  unfold AF
  split_ifs <;> first | rfl | omega

theorem AF_row_at (r P : ℕ) :
    AF x R C (r + 1) P (3 + r) = off x R C (r + 1) := by
  unfold AF
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem AT_zero (t : ℕ) : AT x R C 0 t = AF x R C R (E x R C) t := by
  unfold AT
  rw [if_neg (by omega)]

theorem AT_succ_of_ne {i t : ℕ} (h : t ≠ 3 + R + i) : AT x R C (i + 1) t = AT x R C i t := by
  unfold AT
  split_ifs <;> first | rfl | omega

theorem AT_at (i : ℕ) : AT x R C (i + 1) (3 + R + i) = E x R C := by
  unfold AT
  rw [if_pos (by omega)]

theorem AF_init (t : ℕ) : AF x R C 0 0 t = if t = 0 then R + C else 0 := by
  unfold AF
  split_ifs <;> first | rfl | omega

/-- **The final array is the CSR word.** -/
theorem AFin_eq {t : ℕ} (ht : t < Lc x R C) : AFin x R C t = (csrP x R C).getD t 0 := by
  unfold Lc at ht
  unfold AFin
  by_cases h1 : t = 1
  · subst h1; rw [if_pos rfl, csrP_one]
  rw [if_neg h1]
  by_cases h2 : t = 3 + (R + C) + E x R C
  · subst h2; rw [if_pos rfl, csrP_last]
  rw [if_neg h2]
  unfold AT AF
  by_cases h0 : t = 0
  · subst h0; rw [if_neg (by omega), if_pos rfl, csrP_zero]
  rcases Nat.lt_or_ge t (3 + (R + C)) with h3 | h3
  · -- an offset
    have e : t = 2 + (t - 2) := by omega
    rw [e, csrP_off x R C (by omega), ← e]
    by_cases h4 : 2 + R < t
    · rw [if_pos ⟨h4, by omega⟩, off'_of_lt x R C (by omega)]
    · rw [if_neg (by omega), if_neg h0, off'_of_le x R C (by omega)]
      by_cases h5 : 3 ≤ t
      · rw [if_pos ⟨h5, by omega⟩]
      · have : t = 2 := by omega
        subst this
        rw [if_neg (by omega), if_neg (by omega)]
        exact (off_zero x R C).symm
  · -- a target
    have e : t = 3 + (R + C) + (t - 3 - (R + C)) := by omega
    rw [e, csrP_tgt x R C (by omega), ← e]
    rw [if_neg (by omega), if_neg h0, if_neg (by omega), if_pos ⟨h3, by omega⟩]

end ArrFun

/-! ### The conversion program -/

/-- Append the target `R + c` of a nonzero cell, twice. -/
def colThen : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "V")) (.var "p")) (.add (.var "R") (.var "c")))
    (.seq (.store "a" (.add (.add (.add (.lit 3) (.var "V")) (.var "p")) (.lit 1))
        (.add (.var "R") (.var "c")))
      (.assign "p" (.add (.var "p") (.lit 2))))

/-- One column: if the cell is nonzero, append the target `R + c`; move on. -/
def colBody : Com :=
  .seq (.ite (.eq (.get "t" (.var "q")) (.lit 0)) .skip colThen)
    (.seq (.assign "q" (.add (.var "q") (.lit 1))) (.assign "c" (.add (.var "c") (.lit 1))))

/-- One row: its columns, then its end offset. -/
def rowBody : Com :=
  .seq (.seq (.assign "c" (.lit 0)) (.while (.lt (.var "c") (.var "C")) colBody))
    (.seq (.store "a" (.add (.lit 3) (.var "r")) (.var "p"))
      (.assign "r" (.add (.var "r") (.lit 1))))

/-- The rows. -/
def rowLoop : Com := .seq (.assign "r" (.lit 0)) (.while (.lt (.var "r") (.var "R")) rowBody)

/-- One right vertex: its offset is the end. -/
def tailBody : Com :=
  .seq (.store "a" (.add (.add (.lit 3) (.var "R")) (.var "i2")) (.var "p"))
    (.assign "i2" (.add (.var "i2") (.lit 1)))

/-- The right vertices. -/
def tailLoop : Com :=
  .seq (.assign "i2" (.lit 0)) (.while (.lt (.var "i2") (.var "C")) tailBody)

/-- **The conversion**: the table in `t`, with `R` and `C` in their scalars, becomes the CSR
word in `a`. -/
def convCom : Com :=
  .seq (.assign "V" (.add (.var "R") (.var "C")))
    (.seq (.store "a" (.lit 0) (.var "V"))
      (.seq (.assign "p" (.lit 0))
        (.seq (.assign "q" (.lit 2))
          (.seq rowLoop
            (.seq tailLoop
              (.seq (.store "a" (.lit 1) (.div (.var "p") (.lit 2)))
                (.store "a" (.add (.add (.lit 3) (.var "V")) (.var "p")) (.var "R"))))))))

/-- What every phase of the conversion keeps. -/
structure ConvBase (x : List ℕ) (R C Lt : ℕ) (σ : Env) : Prop where
  hR : σ.vars "R" = R
  hC : σ.vars "C" = C
  hV : σ.vars "V" = R + C
  htab : TabOK x Lt σ

theorem ConvBase.setVar {x : List ℕ} {R C Lt : ℕ} {σ : Env} (h : ConvBase x R C Lt σ)
    (y : String) (hy : y ∉ ["R", "C", "V"]) (v : ℕ) : ConvBase x R C Lt (σ.setVar y v) := by
  refine ⟨?_, ?_, ?_, h.htab.congr rfl⟩
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.hR
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.hC
  · simp only [vars_setVar]; rw [if_neg (by rintro rfl; simp at hy)]; exact h.hV

theorem ConvBase.setArr {x : List ℕ} {R C Lt : ℕ} {σ : Env} (h : ConvBase x R C Lt σ)
    (i v : ℕ) : ConvBase x R C Lt (σ.setArr "a" i v) :=
  ⟨h.hR, h.hC, h.hV, h.htab.congr (by simp)⟩

/-- The invariant of the row loop. -/
structure RowInv (x : List ℕ) (R C Lt : ℕ) (σ : Env) : Prop where
  base : ConvBase x R C Lt σ
  r_le : σ.vars "r" ≤ R
  p : σ.vars "p" = off x R C (σ.vars "r")
  q : σ.vars "q" = 2 + σ.vars "r" * C
  a : σ.arrs "a" = arrOf (Lc x R C) (AF x R C (σ.vars "r") (σ.vars "p"))

/-- The invariant of the column loop. -/
structure ColInv (x : List ℕ) (R C Lt : ℕ) (σ : Env) : Prop where
  base : ConvBase x R C Lt σ
  r_lt : σ.vars "r" < R
  c_le : σ.vars "c" ≤ C
  p : σ.vars "p" = off x R C (σ.vars "r") + (rowPre x R C (σ.vars "r") (σ.vars "c")).length
  q : σ.vars "q" = 2 + σ.vars "r" * C + σ.vars "c"
  a : σ.arrs "a" = arrOf (Lc x R C) (AF x R C (σ.vars "r") (σ.vars "p"))

section Conv

variable {x : List ℕ} {R C Lt : ℕ}

/-- The row's next two targets, when the cell is nonzero. -/
theorem row_next {r c : ℕ} (hcC : c < C) (ht : tab x C r c ≠ 0) :
    (rowPre x R C r c).length + 1 < (row x R C r).length ∧
      (row x R C r).getD (rowPre x R C r c).length 0 = R + c ∧
      (row x R C r).getD ((rowPre x R C r c).length + 1) 0 = R + c := by
  obtain ⟨l, hl⟩ := rowPre_prefix x R C r (c + 1) hcC
  rw [rowPre_succ, if_pos ht, List.append_assoc] at hl
  refine ⟨by rw [hl, List.length_append]; simp, ?_, ?_⟩
  · rw [hl, getD_app_right le_rfl, Nat.sub_self]
    rfl
  · rw [hl, getD_app_right (by omega), Nat.add_sub_cancel_left]
    rfl

theorem colBody_run (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B) (hx : ∀ v ∈ x, v < B)
    (hLt : 2 + R * C ≤ Lt) {σ : Env} (hI : ColInv x R C Lt σ) (hlt : σ.vars "c" < C) :
    ∃ σ', Run B colBody σ σ' 40 ∧ ColInv x R C Lt σ' ∧ σ'.vars "c" = σ.vars "c" + 1 := by
  obtain ⟨⟨hR, hC, hV, htab⟩, hr, hcle, hp, hq, ha⟩ := hI
  have hRC := hc.RC
  have hRle := hc.Rle
  have hCle := hc.Cle
  generalize hr_eq : σ.vars "r" = r at hr hp hq ha
  generalize hc_eq : σ.vars "c" = c at hcle hp hq hlt
  generalize hp_eq : σ.vars "p" = p at hp ha
  have hpair : r * C + c < R * C := Lax117284Proofs.UnitPGraph.pair_lt hr hlt
  have hqLt : σ.vars "q" < Lt := by omega
  have hqB : σ.vars "q" < B := by have := hc.RC; omega
  have hlenT := htab.length
  have hread : (σ.arrs "t").getD (σ.vars "q") 0 = tab x C r c := by
    rw [htab.getD hqLt, hq]; rfl
  have htabB : tab x C r c < B := getD_lt_of_mem hx (by omega) _
  have hoff : off x R C r ≤ 2 * (r * C) := off_le_mul x R C r
  have hrowlen : (rowPre x R C r c).length ≤ 2 * c := length_rowPre_le x R C r c
  have hpB : p + 2 < B := by have := hc.RC; omega
  have hVB : R + C < B := by have := hc.Rle; have := hc.Cle; omega
  have hlenA : (σ.arrs "a").length = Lc x R C := by rw [ha]; simp
  have hLcle := hc.hLc
  have hE := hc.hE
  -- the condition
  have eq_ : (Expr.var "q").evalB B σ = some (σ.vars "q") := RunStep.eval_var B σ "q" hqB
  have eget : (Expr.get "t" (.var "q")).evalB B σ = some ((σ.arrs "t").getD (σ.vars "q") 0) :=
    RunStep.eval_get B σ "t" _ _ eq_ (by omega) (by rw [hread]; exact htabB)
  have e0 := RunStep.eval_lit B 0 σ (by omega)
  -- the two increments
  have einc : ∀ (τ : Env) (y : String), τ.vars y + 1 < B →
      (Expr.add (.var y) (.lit 1)).evalB B τ = some (τ.vars y + 1) := fun τ y hy =>
    RunStep.eval_add B τ (.var y) (.lit 1) _ _ (RunStep.eval_var B τ y (by omega))
      (RunStep.eval_lit B 1 τ (by omega)) hy
  by_cases ht : tab x C r c = 0
  · -- a zero cell: nothing to append
    have hcond : (Cond.eq (.get "t" (.var "q")) (.lit 0)).evalB B σ = some true :=
      RunStep.cond_eq_true B σ _ _ _ 0 eget e0 (by rw [hread, ht])
    have r1 := RunStep.ite_true B _ .skip colThen σ σ 1 hcond (RunStep.skip B σ)
    have r2 := RunStep.assign B σ "q" _ _ (einc σ "q" (by omega))
    set σ₂ := σ.setVar "q" (σ.vars "q" + 1) with hσ₂
    have r3 := RunStep.assign B σ₂ "c" _ _ (einc σ₂ "c" (by simp [hσ₂, hr_eq, hc_eq, hp_eq]; omega))
    refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ?_, by simp [hσ₂, hr_eq, hc_eq, hp_eq]⟩
    refine ⟨((⟨hR, hC, hV, htab⟩ : ConvBase x R C Lt σ).setVar "q" (by simp) _).setVar "c"
      (by simp) _, by simp [hσ₂, hr_eq, hc_eq, hp_eq]; exact hr, by simp [hσ₂, hr_eq, hc_eq, hp_eq]; omega, ?_, by simp [hσ₂, hr_eq, hc_eq, hp_eq]; omega, ?_⟩
    · simp only [hσ₂, vars_setVar, String.reduceEq, ↓reduceIte, hr_eq, hc_eq, hp_eq]
      rw [rowPre_succ, if_neg (by simpa using ht), List.append_nil]
      exact hp
    · simp only [hσ₂, arrs_setVar, vars_setVar, String.reduceEq, ↓reduceIte, hr_eq, hc_eq, hp_eq]
      exact ha
  · -- a nonzero cell: append `R + c` twice
    have hcond : (Cond.eq (.get "t" (.var "q")) (.lit 0)).evalB B σ = some false :=
      RunStep.cond_eq_false B σ _ _ _ 0 eget e0 (by rw [hread]; exact ht)
    obtain ⟨hklt, hkval, hkval'⟩ := row_next (x := x) (R := R) hlt ht
    have hklt0 : (rowPre x R C r c).length < (row x R C r).length := by omega
    have hoffs : off x R C (r + 1) ≤ E x R C := off_mono x R C hr
    rw [off_succ] at hoffs
    have hposLt : 3 + (R + C) + p + 1 < Lc x R C := by unfold Lc; omega
    have hVe : (Expr.var "V").evalB B σ = some (R + C) := by
      rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
    have hpe : (Expr.var "p").evalB B σ = some p := by
      rw [← hp_eq]; exact RunStep.eval_var B σ "p" (by rw [hp_eq]; omega)
    have h3 := RunStep.eval_lit B 3 σ (by omega)
    have h4 := RunStep.eval_add B σ _ _ _ _ h3 hVe (by omega)
    have hidx : (Expr.add (.add (.lit 3) (.var "V")) (.var "p")).evalB B σ =
        some (3 + (R + C) + p) :=
      RunStep.eval_add B σ _ _ _ _ h4 hpe (by omega)
    have hidx' : (Expr.add (.add (.add (.lit 3) (.var "V")) (.var "p")) (.lit 1)).evalB B σ =
        some (3 + (R + C) + p + 1) :=
      RunStep.eval_add B σ _ _ _ _ hidx (RunStep.eval_lit B 1 σ (by omega)) (by omega)
    have hval : (Expr.add (.var "R") (.var "c")).evalB B σ = some (R + c) := by
      have hRe : (Expr.var "R").evalB B σ = some R := by
        rw [← hR]; exact RunStep.eval_var B σ "R" (by omega)
      have hce : (Expr.var "c").evalB B σ = some c := by
        rw [← hc_eq]; exact RunStep.eval_var B σ "c" (by rw [hc_eq]; omega)
      exact RunStep.eval_add B σ _ _ _ _ hRe hce (by omega)
    have rs := RunStep.store B σ "a" _ _ _ _ hidx hval (by omega)
    set σ₁ := σ.setArr "a" (3 + (R + C) + p) (R + c) with hσ₁
    -- the second store evaluates the same expressions: the scalars are unchanged
    have hidx'₁ : (Expr.add (.add (.add (.lit 3) (.var "V")) (.var "p")) (.lit 1)).evalB B σ₁ =
        some (3 + (R + C) + p + 1) := by
      have hVe₁ : (Expr.var "V").evalB B σ₁ = some (R + C) := by
        have : σ₁.vars "V" = R + C := by simp [hσ₁, hV]
        rw [← this]; exact RunStep.eval_var B σ₁ "V" (by rw [this]; omega)
      have hpe₁ : (Expr.var "p").evalB B σ₁ = some p := by
        have : σ₁.vars "p" = p := by simp [hσ₁, hp_eq]
        rw [← this]; exact RunStep.eval_var B σ₁ "p" (by rw [this]; omega)
      have h3₁ := RunStep.eval_lit B 3 σ₁ (by omega)
      have h4₁ := RunStep.eval_add B σ₁ _ _ _ _ h3₁ hVe₁ (by omega)
      have h5₁ := RunStep.eval_add B σ₁ _ _ _ _ h4₁ hpe₁ (by omega)
      exact RunStep.eval_add B σ₁ _ _ _ _ h5₁ (RunStep.eval_lit B 1 σ₁ (by omega)) (by omega)
    have hval₁ : (Expr.add (.var "R") (.var "c")).evalB B σ₁ = some (R + c) := by
      have hRe : (Expr.var "R").evalB B σ₁ = some R := by
        have : σ₁.vars "R" = R := by simp [hσ₁, hR]
        rw [← this]; exact RunStep.eval_var B σ₁ "R" (by rw [this]; omega)
      have hce : (Expr.var "c").evalB B σ₁ = some c := by
        have : σ₁.vars "c" = c := by simp [hσ₁, hc_eq]
        rw [← this]; exact RunStep.eval_var B σ₁ "c" (by rw [this]; omega)
      exact RunStep.eval_add B σ₁ _ _ _ _ hRe hce (by omega)
    have hlenA₁ : (σ₁.arrs "a").length = Lc x R C := by simp [hσ₁, hlenA]
    have rs' := RunStep.store B σ₁ "a" _ _ _ _ hidx'₁ hval₁ (by rw [hlenA₁]; exact hposLt)
    set σ₁' := σ₁.setArr "a" (3 + (R + C) + p + 1) (R + c) with hσ₁'
    have einc2 : (Expr.add (.var "p") (.lit 2)).evalB B σ₁' = some (p + 2) := by
      have : σ₁'.vars "p" = p := by simp [hσ₁', hσ₁, hp_eq]
      rw [← this]
      exact RunStep.eval_add B σ₁' (.var "p") (.lit 2) _ _
        (RunStep.eval_var B σ₁' "p" (by rw [this]; omega)) (RunStep.eval_lit B 2 σ₁' (by omega))
        (by rw [this]; omega)
    have rp := RunStep.assign B σ₁' "p" _ _ einc2
    set σ₁'' := σ₁'.setVar "p" (p + 2) with hσ₁''
    have r1 := RunStep.ite_false B _ .skip colThen σ σ₁'' _ hcond (rs.seq (rs'.seq rp))
    have r2 := RunStep.assign B σ₁'' "q" _ _
      (einc σ₁'' "q" (by simp [hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]; omega))
    set σ₂ := σ₁''.setVar "q" (σ₁''.vars "q" + 1) with hσ₂
    have r3 := RunStep.assign B σ₂ "c" _ _
      (einc σ₂ "c" (by simp [hσ₂, hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]; omega))
    refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp), ?_,
      by simp [hσ₂, hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]⟩
    have hbase : ConvBase x R C Lt σ₁' :=
      ((⟨hR, hC, hV, htab⟩ : ConvBase x R C Lt σ).setArr _ _).setArr _ _
    refine ⟨((hbase.setVar "p" (by simp) _).setVar "q" (by simp) _).setVar "c" (by simp) _,
      by simp [hσ₂, hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]; exact hr,
      by simp [hσ₂, hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]; omega, ?_,
      by simp [hσ₂, hσ₁'', hσ₁', hσ₁, hr_eq, hc_eq, hp_eq]; omega, ?_⟩
    · simp only [hσ₂, hσ₁'', hσ₁', hσ₁, vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte,
        hr_eq, hc_eq, hp_eq]
      rw [rowPre_succ, if_pos (by simpa using ht), List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
    · simp only [hσ₂, hσ₁'', hσ₁', hσ₁, arrs_setVar, vars_setVar, vars_setArr, arrs_setArr,
        String.reduceEq, ↓reduceIte, hr_eq, hc_eq, hp_eq]
      rw [ha, set_arrOf, set_arrOf]
      refine arrOf_congr (fun t' _ => ?_)
      have e1 : p + 1 = off x R C r + ((rowPre x R C r c).length + 1) := by omega
      by_cases htp1 : t' = 3 + (R + C) + p + 1
      · subst htp1
        rw [if_pos rfl, show 3 + (R + C) + p + 1 = 3 + (R + C) + (p + 1) by omega,
          AF_at x R C (le_of_lt hr), e1, tgt_row x R C hr hklt, hkval']
      · rw [if_neg htp1]
        by_cases htp : t' = 3 + (R + C) + p
        · subst htp
          rw [if_pos rfl, AF_succ_of_ne x R C (P := p + 1) (by omega),
            AF_at x R C (le_of_lt hr), hp, tgt_row x R C hr hklt0, hkval]
        · rw [if_neg htp, AF_succ_of_ne x R C (P := p + 1) (by omega), AF_succ_of_ne x R C htp]

theorem colBody_spec (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B) (hx : ∀ v ∈ x, v < B)
    (hLt : 2 + R * C ≤ Lt) :
    Spec B (fun σ => ColInv x R C Lt σ ∧ σ.vars "c" < C) colBody
      (fun σ σ' => ColInv x R C Lt σ' ∧ σ'.vars "c" = σ.vars "c" + 1) 40 := by
  rintro σ ⟨hI, hlt⟩
  obtain ⟨σ', hr, hI', hc'⟩ := colBody_run hc hB hx hLt hI hlt
  exact ⟨σ', hr, hI', hc'⟩

theorem rowBody_spec (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B) (hx : ∀ v ∈ x, v < B)
    (hLt : 2 + R * C ≤ Lt) :
    Spec B (fun σ => RowInv x R C Lt σ ∧ σ.vars "r" < R) rowBody
      (fun σ σ' => RowInv x R C Lt σ' ∧ σ'.vars "r" = σ.vars "r" + 1) ((40 + 4) * C + 6 + 10) := by
  have hCB : C < B := by have := hc.Cle; omega
  have hloop := Spec.forRangeZero (B := B) (c := colBody) "c" "C" (ColInv x R C Lt) C 40 hCB
    (fun σ hσ => hσ.c_le) (fun σ hσ => hσ.base.hC) (colBody_spec hc hB hx hLt)
  rintro σ ⟨hI, hlt⟩
  obtain ⟨⟨hR, hC, hV, htab⟩, hr, hp, hq, ha⟩ := hI
  -- the columns
  obtain ⟨σ₁, hr1, hI₁, hc₁⟩ := hloop.run (σ := σ) (by
    refine ⟨(⟨hR, hC, hV, htab⟩ : ConvBase x R C Lt σ).setVar "c" (by simp) _,
      by simpa using hlt, by simp, ?_, by simp [hq], by simpa using ha⟩
    simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [rowPre_zero]; simpa using hp)
  obtain ⟨⟨hR₁, hC₁, hV₁, htab₁⟩, hr₁, -, hp₁, hq₁, ha₁⟩ := hI₁
  rw [hc₁] at hp₁ hq₁
  have hp₁' : σ₁.vars "p" = off x R C (σ₁.vars "r" + 1) := by rw [hp₁, off_succ]; rfl
  -- the row's end offset
  have hoffs : off x R C (σ₁.vars "r" + 1) ≤ E x R C := off_mono x R C hr₁
  have hE := hc.hE
  have hRle := hc.Rle
  have hlenA : (σ₁.arrs "a").length = Lc x R C := by rw [ha₁]; simp
  have hLc := hc.hLc
  have hidx : (Expr.add (.lit 3) (.var "r")).evalB B σ₁ = some (3 + σ₁.vars "r") :=
    RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 3 σ₁ (by omega))
      (RunStep.eval_var B σ₁ "r" (by omega)) (by omega)
  have hval : (Expr.var "p").evalB B σ₁ = some (σ₁.vars "p") :=
    RunStep.eval_var B σ₁ "p" (by omega)
  have rs := RunStep.store B σ₁ "a" _ _ _ _ hidx hval (by rw [hlenA]; unfold Lc; omega)
  set σ₂ := σ₁.setArr "a" (3 + σ₁.vars "r") (σ₁.vars "p") with hσ₂
  have rr := RunStep.assign B σ₂ "r" _ _ (RunStep.eval_add B σ₂ (.var "r") (.lit 1) _ _
    (RunStep.eval_var B σ₂ "r" (by simp [hσ₂]; omega)) (RunStep.eval_lit B 1 σ₂ (by omega))
    (by simp [hσ₂]; omega))
  have hr' : σ₁.vars "r" = σ.vars "r" := by
    have := hr1.frame_var "r" (by
      simp [colBody, colThen, Com.wvars])
    simpa using this
  refine ⟨_, (hr1.seq (rs.seq rr)).mono (by simp), ?_, by simp [hσ₂, hr']⟩
  have hbase : ConvBase x R C Lt σ₂ := (⟨hR₁, hC₁, hV₁, htab₁⟩ : ConvBase x R C Lt σ₁).setArr _ _
  refine ⟨hbase.setVar "r" (by simp) _, by simp [hσ₂]; omega, ?_, ?_, ?_⟩
  · simp only [hσ₂, vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte]
    exact hp₁'
  · simp only [hσ₂, vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte]
    rw [hq₁, Nat.succ_mul]; omega
  · simp only [hσ₂, arrs_setVar, vars_setVar, vars_setArr, arrs_setArr, String.reduceEq,
      ↓reduceIte]
    rw [ha₁, set_arrOf]
    refine arrOf_congr (fun t' _ => ?_)
    by_cases htp : t' = 3 + σ₁.vars "r"
    · subst htp
      rw [if_pos rfl, AF_row_at x R C _ _, hp₁']
    · rw [if_neg htp, AF_row_of_ne x R C htp]

/-- The invariant of the tail loop. -/
structure TailInv (x : List ℕ) (R C Lt : ℕ) (σ : Env) : Prop where
  base : ConvBase x R C Lt σ
  i_le : σ.vars "i2" ≤ C
  p : σ.vars "p" = E x R C
  a : σ.arrs "a" = arrOf (Lc x R C) (AT x R C (σ.vars "i2"))

theorem tailBody_spec (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => TailInv x R C Lt σ ∧ σ.vars "i2" < C) tailBody
      (fun σ σ' => TailInv x R C Lt σ' ∧ σ'.vars "i2" = σ.vars "i2" + 1) 12 := by
  rintro σ ⟨⟨⟨hR, hC, hV, htab⟩, hi, hp, ha⟩, hlt⟩
  have hRle := hc.Rle
  have hCle := hc.Cle
  have hE := hc.hE
  have hlenA : (σ.arrs "a").length = Lc x R C := by rw [ha]; simp
  have hidx : (Expr.add (.add (.lit 3) (.var "R")) (.var "i2")).evalB B σ =
      some (3 + R + σ.vars "i2") := by
    have hRe : (Expr.var "R").evalB B σ = some R := by
      rw [← hR]; exact RunStep.eval_var B σ "R" (by omega)
    have h3 := RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hRe (by omega)
    exact RunStep.eval_add B σ _ _ _ _ h3 (RunStep.eval_var B σ "i2" (by omega)) (by omega)
  have hval : (Expr.var "p").evalB B σ = some (σ.vars "p") := RunStep.eval_var B σ "p" (by omega)
  have rs := RunStep.store B σ "a" _ _ _ _ hidx hval (by rw [hlenA]; unfold Lc; omega)
  set σ₁ := σ.setArr "a" (3 + R + σ.vars "i2") (σ.vars "p") with hσ₁
  have ri := RunStep.assign B σ₁ "i2" _ _ (RunStep.eval_add B σ₁ (.var "i2") (.lit 1) _ _
    (RunStep.eval_var B σ₁ "i2" (by simp [hσ₁]; omega)) (RunStep.eval_lit B 1 σ₁ (by omega))
    (by simp [hσ₁]; omega))
  refine ⟨_, (rs.seq ri).mono (by simp), ?_, by simp [hσ₁]⟩
  have hbase : ConvBase x R C Lt σ₁ := (⟨hR, hC, hV, htab⟩ : ConvBase x R C Lt σ).setArr _ _
  refine ⟨hbase.setVar "i2" (by simp) _, by simp [hσ₁]; omega, by simp [hσ₁]; exact hp, ?_⟩
  simp only [hσ₁, arrs_setVar, vars_setVar, vars_setArr, arrs_setArr, ↓reduceIte]
  rw [ha, set_arrOf]
  refine arrOf_congr (fun t' _ => ?_)
  by_cases htp : t' = 3 + R + σ.vars "i2"
  · subst htp
    rw [if_pos rfl, AT_at, hp]
  · rw [if_neg htp, AT_succ_of_ne x R C htp]

/-- The cost of the conversion. -/
def convCost (x : List ℕ) (R C : ℕ) : ℕ := 50 * (R * C) + 20 * R + 20 * C + 60

/-- **The conversion**, from a state holding the table in `t`, `R`, `C`, and a zero `a` of the
CSR word's length: `a` holds the CSR word, `V` holds `R + C`, `p` the length of the target
array, and `t`, `R`, `C` are unchanged. -/
theorem conv_spec (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B) (hx : ∀ v ∈ x, v < B)
    (hLt : 2 + R * C ≤ Lt) :
    Spec B (fun σ => σ.vars "R" = R ∧ σ.vars "C" = C ∧ TabOK x Lt σ ∧
        σ.arrs "a" = List.replicate (Lc x R C) 0)
      convCom
      (fun _ σ' => σ'.vars "R" = R ∧ σ'.vars "C" = C ∧ σ'.vars "V" = R + C ∧
        σ'.vars "p" = E x R C ∧ TabOK x Lt σ' ∧
        σ'.arrs "a" = arrOf (Lc x R C) (AFin x R C))
      (convCost x R C) := by
  rintro σ ⟨hR, hC, htab, ha⟩
  have hRle := hc.Rle
  have hCle := hc.Cle
  have hRC := hc.RC
  have hE := hc.hE
  have hLc := hc.hLc
  have hRB : R < B := by omega
  have hCB : C < B := by omega
  -- V := R + C
  have r1 := RunStep.assign B σ "V" _ _ (RunStep.eval_add B σ (.var "R") (.var "C") R C
    (by rw [← hR]; exact RunStep.eval_var B σ "R" (by omega))
    (by rw [← hC]; exact RunStep.eval_var B σ "C" (by omega)) (by omega))
  set σ₁ := σ.setVar "V" (R + C) with hσ₁
  -- a[0] := V
  have hlenA₁ : (σ₁.arrs "a").length = Lc x R C := by simp [hσ₁, ha]
  have hV₁ : σ₁.vars "V" = R + C := by simp [hσ₁]
  have hVe₁ : (Expr.var "V").evalB B σ₁ = some (R + C) := by
    rw [← hV₁]; exact RunStep.eval_var B σ₁ "V" (by rw [hV₁]; omega)
  have r2 := RunStep.store B σ₁ "a" (.lit 0) (.var "V") 0 (R + C)
    (RunStep.eval_lit B 0 σ₁ (by omega)) hVe₁ (by rw [hlenA₁]; unfold Lc; omega)
  set σ₂ := σ₁.setArr "a" 0 (R + C) with hσ₂
  -- p := 0; q := 2
  have r3 := RunStep.assign B σ₂ "p" (.lit 0) 0 (RunStep.eval_lit B 0 σ₂ (by omega))
  set σ₃ := σ₂.setVar "p" 0 with hσ₃
  have r4 := RunStep.assign B σ₃ "q" (.lit 2) 2 (RunStep.eval_lit B 2 σ₃ (by omega))
  set σ₄ := σ₃.setVar "q" 2 with hσ₄
  have hbase₄ : ConvBase x R C Lt σ₄ :=
    ⟨by simp [hσ₄, hσ₃, hσ₂, hσ₁, hR], by simp [hσ₄, hσ₃, hσ₂, hσ₁, hC], by simp [hσ₄, hσ₃, hσ₂, hσ₁],
      htab.congr (by simp [hσ₄, hσ₃, hσ₂, hσ₁])⟩
  -- the rows
  have hrows := Spec.forRangeZero (B := B) (c := rowBody) "r" "R" (RowInv x R C Lt) R
    ((40 + 4) * C + 6 + 10) hRB (fun σ hσ => hσ.r_le) (fun σ hσ => hσ.base.hR)
    (rowBody_spec hc hB hx hLt)
  obtain ⟨σ₅, r5, hI₅, hr₅⟩ := hrows.run (σ := σ₄) (by
    refine ⟨hbase₄.setVar "r" (by simp) _, by simp, ?_, ?_, ?_⟩
    · simp [hσ₄, hσ₃, off_zero]
    · simp [hσ₄, hσ₃]
    · simp only [arrs_setVar, vars_setVar, String.reduceEq, ↓reduceIte, hσ₄, hσ₃, hσ₂, hσ₁,
        arrs_setArr]
      rw [ha, replicate_eq_arrOf, set_arrOf]
      exact arrOf_congr (fun t _ => by simp [AF_init]))
  obtain ⟨hbase₅, -, hp₅, -, ha₅⟩ := hI₅
  rw [hr₅] at hp₅ ha₅
  have hp₅' : σ₅.vars "p" = E x R C := hp₅
  -- the tail
  have htail := Spec.forRangeZero (B := B) (c := tailBody) "i2" "C" (TailInv x R C Lt) C 12 hCB
    (fun σ hσ => hσ.i_le) (fun σ hσ => hσ.base.hC) (tailBody_spec (Lt := Lt) hc hB)
  obtain ⟨σ₈, r8, hI₈, hi₈⟩ := htail.run (σ := σ₅) (by
    refine ⟨hbase₅.setVar "i2" (by simp) _, by simp, by simpa using hp₅', ?_⟩
    simp only [arrs_setVar, vars_setVar, String.reduceEq, ↓reduceIte]
    rw [ha₅, hp₅']
    exact arrOf_congr (fun t _ => (AT_zero x R C t).symm))
  obtain ⟨hbase₈, -, hp₈, ha₈⟩ := hI₈
  rw [hi₈] at ha₈
  -- a[1] := p / 2
  have hlenA₈ : (σ₈.arrs "a").length = Lc x R C := by rw [ha₈]; simp
  have hp₈B : σ₈.vars "p" < B := by rw [hp₈]; omega
  have r9 := RunStep.store B σ₈ "a" (.lit 1) (.div (.var "p") (.lit 2)) 1 (σ₈.vars "p" / 2)
    (RunStep.eval_lit B 1 σ₈ (by omega))
    (RunStep.eval_div B σ₈ _ _ _ _ (RunStep.eval_var B σ₈ "p" hp₈B)
      (RunStep.eval_lit B 2 σ₈ (by omega)) (by omega)) (by rw [hlenA₈]; unfold Lc; omega)
  set σ₉ := σ₈.setArr "a" 1 (σ₈.vars "p" / 2) with hσ₉
  -- a[3 + V + p] := R
  have hV₉ : σ₉.vars "V" = R + C := by simp [hσ₉, hbase₈.hV]
  have hidx : (Expr.add (.add (.lit 3) (.var "V")) (.var "p")).evalB B σ₉ =
      some (3 + (R + C) + E x R C) := by
    have hVe : (Expr.var "V").evalB B σ₉ = some (R + C) := by
      rw [← hV₉]; exact RunStep.eval_var B σ₉ "V" (by rw [hV₉]; omega)
    have hpe : (Expr.var "p").evalB B σ₉ = some (E x R C) := by
      have : σ₉.vars "p" = E x R C := by simp [hσ₉, hp₈]
      rw [← this]; exact RunStep.eval_var B σ₉ "p" (by rw [this]; omega)
    have h3 := RunStep.eval_add B σ₉ _ _ _ _ (RunStep.eval_lit B 3 σ₉ (by omega)) hVe (by omega)
    exact RunStep.eval_add B σ₉ _ _ _ _ h3 hpe (by unfold Lc at hLc; omega)
  have hRe₉ : (Expr.var "R").evalB B σ₉ = some R := by
    have : σ₉.vars "R" = R := by simp [hσ₉, hbase₈.hR]
    rw [← this]; exact RunStep.eval_var B σ₉ "R" (by rw [this]; omega)
  have r10 := RunStep.store B σ₉ "a" _ _ _ _ hidx hRe₉ (by simp [hσ₉, hlenA₈]; unfold Lc; omega)
  refine ⟨σ₉.setArr "a" (3 + (R + C) + E x R C) R, ?_, ?_⟩
  · refine (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r8.seq (r9.seq r10))))))).mono ?_
    simp only [size_lit, size_var, size_add, size_div, size_bin, Expr.add_def, Expr.div_def]
    unfold convCost
    nlinarith
  · refine ⟨by simp [hσ₉, hbase₈.hR], by simp [hσ₉, hbase₈.hC], by simp [hσ₉, hbase₈.hV],
      by simp [hσ₉, hp₈], hbase₈.htab.congr (by simp [hσ₉]), ?_⟩
    simp only [hσ₉, arrs_setArr, String.reduceEq, ↓reduceIte, vars_setArr]
    rw [ha₈, hp₈, set_arrOf, set_arrOf]
    refine arrOf_congr (fun t _ => ?_)
    unfold AFin
    by_cases h2 : t = 3 + (R + C) + E x R C
    · rw [if_pos h2, if_neg (by omega), if_pos h2]
    · rw [if_neg h2]
      by_cases h1 : t = 1
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_neg h2]

end Conv

end Lax117284Proofs.Machine.MatchGuard
