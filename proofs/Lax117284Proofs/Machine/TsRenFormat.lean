import Lax117284Proofs.Machine.TokProg
import Lax117284Proofs.Machine.Lists

/-!
The format of a 2-CNF formula of the scheduling submission: the number of variables, the number
of clauses, and then a variable (a number) and a sign (a bit) for each of the two literals of
every clause.
-/

namespace Lax117284Proofs.Machine.TsRenFormat

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokProg

/-- What is expected after the two counts and `j` further tokens: a variable and a sign
alternately, until both literals of every clause have been read. -/
def kindR (C j : ℕ) : Kind :=
  if j < 4 * C then (if j % 2 = 0 then .num else .bit) else .done

/-- The format. -/
def ER : Format := fun ts =>
  if ts.length < 2 then .num else kindR (Tok.val (ts.getD 1 (.num 0))) (ts.length - 2)

/-- The number of positions of the formula whose number of clauses is the entry `1`. -/
def PosN (ns : List ℕ) : ℕ := 2 * ns.getD 1 0

/-- The numbers of a stream of the format: two counts, and a variable and a sign, which is `0`
or `1`, for every position. -/
def ShapeR (ns : List ℕ) : Prop :=
  2 ≤ ns.length ∧ ns.length = 2 + 2 * PosN ns ∧ ∀ o < PosN ns, ns.getD (3 + 2 * o) 0 ≤ 1

/-- The token at a position: the counts and the variables are numbers, the signs bits. -/
def tokAt (ns : List ℕ) (k : ℕ) : Tok :=
  if k < 2 ∨ k % 2 = 0 then .num (ns.getD k 0) else .bit (decide (ns.getD k 0 ≠ 0))

/-- The tokens of a stream of numbers. -/
def toksR (ns : List ℕ) : List Tok := (List.range ns.length).map (tokAt ns)

lemma length_toksR (ns : List ℕ) : (toksR ns).length = ns.length := by simp [toksR]

lemma getD_toksR (ns : List ℕ) {k : ℕ} (hk : k < ns.length) (d : Tok) :
    (toksR ns).getD k d = tokAt ns k := by
  simp [toksR, List.getD_eq_getElem?_getD, hk]

lemma take_toksR (ns : List ℕ) (k : ℕ) (hk : k ≤ ns.length) :
    (toksR ns).take k = (List.range k).map (tokAt ns) := by
  unfold toksR
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

lemma vals_toksR {ns : List ℕ} (h : ShapeR ns) : (toksR ns).map Tok.val = ns := by
  obtain ⟨h2, hl, hs⟩ := h
  apply List.ext_getElem
  · simp [toksR]
  · intro k h1 h2
    have hk : k < ns.length := h2
    simp only [toksR, List.getElem_map, List.getElem_range, tokAt]
    split_ifs with h
    · simp [Tok.val, List.getElem?_eq_getElem hk]
    · have hk3 : 2 ≤ k := by omega
      obtain ⟨o, rfl⟩ : ∃ o, k = 3 + 2 * o := ⟨(k - 3) / 2, by omega⟩
      have ho : o < PosN ns := by omega
      have := hs o ho
      rw [List.getD_eq_getElem _ _ hk] at this ⊢
      by_cases h0 : ns[3 + 2 * o] = 0
      · simp [Tok.val, h0]
      · have : ns[3 + 2 * o] = 1 := by omega
        simp [Tok.val, this]

lemma kind_tokAt (ns : List ℕ) (k : ℕ) :
    (tokAt ns k).kind = if k < 2 then .num else if k % 2 = 0 then .num else .bit := by
  unfold tokAt; split_ifs <;> simp_all [Tok.kind]

theorem conforms_of_shape {ns : List ℕ} (h : ShapeR ns) : Conforms ER (toksR ns) := by
  have hv := vals_toksR h
  obtain ⟨h2, hl, hs⟩ := h
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [length_toksR] at hk
    rw [getD_toksR ns hk, kind_tokAt, take_toksR ns k hk.le]
    simp only [ER, List.length_map, List.length_range]
    by_cases hk2 : k < 2
    · simp [hk2]
    · rw [if_neg hk2]
      have g1 : ((List.range k).map (tokAt ns)).getD 1 (.num 0) = .num (ns.getD 1 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [tokAt]
      rw [g1]
      have hlt : k - 2 < 2 * PosN ns := by unfold PosN at *; omega
      have e : kindR (Tok.val (Tok.num (ns.getD 1 0))) (k - 2) = kindR (ns.getD 1 0) (k - 2) := rfl
      rw [e]
      unfold kindR
      have hlt' : k - 2 < 4 * ns.getD 1 0 := by unfold PosN at hlt; omega
      rw [if_pos hlt', if_neg hk2]
      split_ifs <;> first | rfl | omega
  · have hlen : (toksR ns).length = 2 + 2 * PosN ns := by rw [length_toksR, hl]
    have g1 : (toksR ns).getD 1 (.num 0) = .num (ns.getD 1 0) := by
      rw [getD_toksR ns (by omega)]; simp [tokAt]
    unfold ER
    rw [hlen, if_neg (by omega), g1]
    have e : kindR (Tok.val (Tok.num (ns.getD 1 0))) (2 + 2 * PosN ns - 2) =
        kindR (ns.getD 1 0) (2 + 2 * PosN ns - 2) := rfl
    rw [e]
    unfold kindR
    have : ¬ (2 + 2 * PosN ns - 2 < 4 * ns.getD 1 0) := by unfold PosN; omega
    rw [if_neg this]

lemma getD_map_val (ts : List Tok) (k : ℕ) :
    (ts.map Tok.val).getD k 0 = Tok.val (ts.getD k (.num 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[k]? <;> simp [Tok.val]

lemma kind_ne_done (t : Tok) : t.kind ≠ .done := by cases t <;> simp [Tok.kind]

lemma exists_num {t : Tok} (h : t.kind = .num) : ∃ v, t = .num v := by
  cases t with
  | num v => exact ⟨v, rfl⟩
  | bit b => simp [Tok.kind] at h

lemma exists_bit {t : Tok} (h : t.kind = .bit) : ∃ b, t = .bit b := by
  cases t with
  | num v => simp [Tok.kind] at h
  | bit b => exact ⟨b, rfl⟩

/-- What conformance says, in terms of the count `C`. -/
lemma conforms_facts {ts : List Tok} (h : Conforms ER ts) :
    2 ≤ ts.length ∧ ER ts = .done ∧
    ∀ k < ts.length, (ts.getD k (.bit false)).kind =
      (if k < 2 then .num else kindR (Tok.val (ts.getD 1 (.num 0))) (k - 2)) := by
  obtain ⟨hf, hd⟩ := h
  refine ⟨?_, hd, ?_⟩
  · by_contra hlt
    unfold ER at hd
    rw [if_pos (by omega)] at hd
    exact absurd hd (by decide)
  · intro k hk
    rw [hf k hk]
    unfold ER
    rw [List.length_take, Nat.min_eq_left hk.le]
    by_cases hk2 : k < 2
    · rw [if_pos hk2, if_pos hk2]
    · rw [if_neg hk2, if_neg hk2]
      have e1 : (ts.take k).getD 1 (.num 0) = ts.getD 1 (.num 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_take_of_lt (by omega)]
      rw [e1]

theorem shape_of_conforms {ts : List Tok} (h : Conforms ER ts) :
    ShapeR (ts.map Tok.val) ∧ ts = toksR (ts.map Tok.val) := by
  obtain ⟨hT2, hd, hkind⟩ := conforms_facts h
  have hS : PosN (ts.map Tok.val) = 2 * Tok.val (ts.getD 1 (.num 0)) := by
    unfold PosN; rw [getD_map_val]
  have hd' : ¬ (ts.length - 2 < 2 * PosN (ts.map Tok.val)) := by
    intro hlt'
    unfold ER at hd
    rw [if_neg (by omega)] at hd
    unfold kindR at hd
    rw [hS] at hlt'
    rw [if_pos (by omega)] at hd
    split_ifs at hd
  have hlt : ∀ k, 2 ≤ k → k < ts.length → k - 2 < 2 * PosN (ts.map Tok.val) := by
    intro k hk2 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    by_contra hge
    rw [hS] at hge
    unfold kindR at this
    rw [if_neg (by omega)] at this
    exact kind_ne_done _ this
  have hlen : ts.length = 2 + 2 * PosN (ts.map Tok.val) := by
    by_cases h4 : ts.length = 2
    · omega
    · have := hlt (ts.length - 1) (by omega) (by omega)
      omega
  have hkind' : ∀ k, 2 ≤ k → k < ts.length →
      (ts.getD k (.bit false)).kind = if (k - 2) % 2 = 0 then .num else .bit := by
    intro k hk2 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    rw [this]
    have h2 := hlt k hk2 hk
    rw [hS] at h2
    unfold kindR
    rw [if_pos (by omega)]
  have hshape : ShapeR (ts.map Tok.val) := by
    refine ⟨by simpa using hT2, by rw [← hlen]; simp, fun o ho => ?_⟩
    have hk : 3 + 2 * o < ts.length := by omega
    rw [getD_map_val]
    have hkd := hkind' (3 + 2 * o) (by omega) hk
    rw [if_neg (by omega)] at hkd
    obtain ⟨bb, hbb⟩ := exists_bit (t := ts.getD (3 + 2 * o) (.bit false)) (by
      rw [List.getD_eq_getElem _ _ hk] at hkd ⊢; exact hkd)
    rw [List.getD_eq_getElem _ _ hk] at hbb
    rw [List.getD_eq_getElem _ _ hk, hbb]
    cases bb <;> simp [Tok.val]
  refine ⟨hshape, ?_⟩
  apply List.ext_getElem
  · rw [length_toksR]; simp
  · intro k h1 h2
    have hk : k < ts.length := h1
    have hg : (toksR (ts.map Tok.val))[k]'h2 = tokAt (ts.map Tok.val) k := by
      have := getD_toksR (ts.map Tok.val) (k := k) (by simpa using hk) (.bit false)
      rwa [List.getD_eq_getElem _ _ h2] at this
    rw [hg]
    have hv : (ts.map Tok.val).getD k 0 = Tok.val ts[k] := by
      rw [getD_map_val, List.getD_eq_getElem _ _ hk]
    have hkd := hkind k hk
    rw [List.getD_eq_getElem _ _ hk] at hkd
    unfold tokAt
    rw [hv]
    by_cases hk2 : k < 2
    · rw [if_pos hk2] at hkd
      obtain ⟨v, hvv⟩ := exists_num hkd
      rw [if_pos (Or.inl hk2), hvv]; rfl
    · have hkd' := hkind' k (by omega) hk
      rw [List.getD_eq_getElem _ _ hk] at hkd'
      by_cases hpar : k % 2 = 0
      · rw [if_pos (by omega)] at hkd'
        obtain ⟨v, hvv⟩ := exists_num hkd'
        rw [if_pos (Or.inr hpar), hvv]; rfl
      · rw [if_neg (by omega)] at hkd'
        obtain ⟨bb, hbb⟩ := exists_bit hkd'
        rw [if_neg (by omega), hbb]
        cases bb <;> simp [Tok.val]

end Lax117284Proofs.Machine.TsRenFormat
