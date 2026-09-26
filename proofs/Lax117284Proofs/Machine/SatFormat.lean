import Lax117284Proofs.Machine.TokProg
import Lax117284Proofs.Machine.Lists
import Lax117284Proofs.Theorem7Slots

/-!
The format of a [2,3]-bounded 3-SAT formula: the number of variables, the numbers of clauses of
two and of three literals, and then a variable (a number) and a sign (a bit) for every position.
-/

namespace Lax117284Proofs.Machine.SatFormat

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokProg

/-- What is expected after the three counts and `j` further tokens: a variable and a sign
alternately, until every position of the formula has been read. -/
def kindF (a b j : ℕ) : Kind :=
  if j < 2 * (2 * a + 3 * b) then (if j % 2 = 0 then .num else .bit) else .done

/-- The format. -/
def EF : Format := fun ts =>
  if ts.length < 3 then .num
  else kindF (Tok.val (ts.getD 1 (.num 0))) (Tok.val (ts.getD 2 (.num 0))) (ts.length - 3)

/-- The number of positions of the formula whose counts are the entries `1` and `2`. -/
def SlotsN (ns : List ℕ) : ℕ := 2 * ns.getD 1 0 + 3 * ns.getD 2 0

/-- The numbers of a stream of the format: three counts, and a variable and a sign, which is `0`
or `1`, for every position. -/
def ShapeF (ns : List ℕ) : Prop :=
  3 ≤ ns.length ∧ ns.length = 3 + 2 * SlotsN ns ∧ ∀ o < SlotsN ns, ns.getD (4 + 2 * o) 0 ≤ 1

/-- The token at a position: the counts and the variables are numbers, the signs bits. -/
def tokAt (ns : List ℕ) (k : ℕ) : Tok :=
  if k < 3 ∨ k % 2 = 1 then .num (ns.getD k 0) else .bit (decide (ns.getD k 0 ≠ 0))

/-- The tokens of a stream of numbers. -/
def toksF (ns : List ℕ) : List Tok := (List.range ns.length).map (tokAt ns)

lemma length_toksF (ns : List ℕ) : (toksF ns).length = ns.length := by simp [toksF]

lemma getD_toksF (ns : List ℕ) {k : ℕ} (hk : k < ns.length) (d : Tok) :
    (toksF ns).getD k d = tokAt ns k := by
  simp [toksF, List.getD_eq_getElem?_getD, hk]

lemma take_toksF (ns : List ℕ) (k : ℕ) (hk : k ≤ ns.length) :
    (toksF ns).take k = (List.range k).map (tokAt ns) := by
  unfold toksF
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

lemma vals_toksF {ns : List ℕ} (h : ShapeF ns) : (toksF ns).map Tok.val = ns := by
  obtain ⟨h3, hl, hs⟩ := h
  apply List.ext_getElem
  · simp [toksF]
  · intro k h1 h2
    have hk : k < ns.length := h2
    simp only [toksF, List.getElem_map, List.getElem_range, tokAt]
    split_ifs with h
    · simp [Tok.val, List.getD_eq_getElem _ _ hk, List.getElem?_eq_getElem hk]
    · have hk3 : 3 ≤ k := by omega
      obtain ⟨o, rfl⟩ : ∃ o, k = 4 + 2 * o := ⟨(k - 4) / 2, by omega⟩
      have ho : o < SlotsN ns := by omega
      have := hs o ho
      rw [List.getD_eq_getElem _ _ hk] at this ⊢
      by_cases h0 : ns[4 + 2 * o] = 0
      · simp [Tok.val, h0]
      · have : ns[4 + 2 * o] = 1 := by omega
        simp [Tok.val, this]

lemma kind_tokAt (ns : List ℕ) (k : ℕ) :
    (tokAt ns k).kind = if k < 3 then .num else if k % 2 = 1 then .num else .bit := by
  unfold tokAt; split_ifs <;> simp_all [Tok.kind]

theorem conforms_of_shape {ns : List ℕ} (h : ShapeF ns) : Conforms EF (toksF ns) := by
  have hv := vals_toksF h
  obtain ⟨h3, hl, hs⟩ := h
  have h1 : ns.getD 1 0 = ns[1]'(by omega) := List.getD_eq_getElem _ _ _
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [length_toksF] at hk
    rw [getD_toksF ns hk, kind_tokAt, take_toksF ns k hk.le]
    simp only [EF, List.length_map, List.length_range]
    by_cases hk3 : k < 3
    · simp [hk3]
    · rw [if_neg hk3]
      have g1 : ((List.range k).map (tokAt ns)).getD 1 (.num 0) = .num (ns.getD 1 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [tokAt]
      have g2 : ((List.range k).map (tokAt ns)).getD 2 (.num 0) = .num (ns.getD 2 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [tokAt]
      rw [g1, g2]
      have hlt : k - 3 < 2 * SlotsN ns := by unfold SlotsN at *; omega
      have e : kindF (Tok.val (Tok.num (ns.getD 1 0))) (Tok.val (Tok.num (ns.getD 2 0))) (k - 3)
          = kindF (ns.getD 1 0) (ns.getD 2 0) (k - 3) := rfl
      rw [e]
      unfold kindF
      unfold SlotsN at hlt
      rw [if_pos hlt, if_neg hk3]
      split_ifs <;> first | rfl | omega
  · have hlen : (toksF ns).length = 3 + 2 * SlotsN ns := by rw [length_toksF, hl]
    have g1 : (toksF ns).getD 1 (.num 0) = .num (ns.getD 1 0) := by
      rw [getD_toksF ns (by omega)]; simp [tokAt]
    have g2 : (toksF ns).getD 2 (.num 0) = .num (ns.getD 2 0) := by
      rw [getD_toksF ns (by omega)]; simp [tokAt]
    unfold EF
    rw [hlen, if_neg (by omega), g1, g2]
    have e : kindF (Tok.val (Tok.num (ns.getD 1 0))) (Tok.val (Tok.num (ns.getD 2 0)))
        (3 + 2 * SlotsN ns - 3) = kindF (ns.getD 1 0) (ns.getD 2 0) (3 + 2 * SlotsN ns - 3) := rfl
    rw [e]
    unfold kindF
    have : ¬ (3 + 2 * SlotsN ns - 3 < 2 * (2 * ns.getD 1 0 + 3 * ns.getD 2 0)) := by
      unfold SlotsN; omega
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

/-- What conformance says, in terms of the counts `a` and `b`. -/
lemma conforms_facts {ts : List Tok} (h : Conforms EF ts) :
    3 ≤ ts.length ∧ EF ts = .done ∧
    ∀ k < ts.length, (ts.getD k (.bit false)).kind =
      (if k < 3 then .num
        else kindF (Tok.val (ts.getD 1 (.num 0))) (Tok.val (ts.getD 2 (.num 0))) (k - 3)) := by
  obtain ⟨hf, hd⟩ := h
  refine ⟨?_, hd, ?_⟩
  · by_contra hlt
    unfold EF at hd
    rw [if_pos (by omega)] at hd
    exact absurd hd (by decide)
  · intro k hk
    rw [hf k hk]
    unfold EF
    rw [List.length_take, Nat.min_eq_left hk.le]
    by_cases hk3 : k < 3
    · rw [if_pos hk3, if_pos hk3]
    · rw [if_neg hk3, if_neg hk3]
      have e1 : (ts.take k).getD 1 (.num 0) = ts.getD 1 (.num 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_take_of_lt (by omega)]
      have e2 : (ts.take k).getD 2 (.num 0) = ts.getD 2 (.num 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_take_of_lt (by omega)]
      rw [e1, e2]

theorem shape_of_conforms {ts : List Tok} (h : Conforms EF ts) :
    ShapeF (ts.map Tok.val) ∧ ts = toksF (ts.map Tok.val) := by
  obtain ⟨hT3, hd, hkind⟩ := conforms_facts h
  have hS : SlotsN (ts.map Tok.val) =
      2 * Tok.val (ts.getD 1 (.num 0)) + 3 * Tok.val (ts.getD 2 (.num 0)) := by
    unfold SlotsN; rw [getD_map_val, getD_map_val]
  have hd' : ¬ (ts.length - 3 < 2 * SlotsN (ts.map Tok.val)) := by
    intro hlt'
    unfold EF at hd
    rw [if_neg (by omega)] at hd
    unfold kindF at hd
    rw [hS] at hlt'
    rw [if_pos hlt'] at hd
    split_ifs at hd <;> exact absurd hd (by decide)
  have hlt : ∀ k, 3 ≤ k → k < ts.length → k - 3 < 2 * SlotsN (ts.map Tok.val) := by
    intro k hk3 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    by_contra hge
    rw [hS] at hge
    unfold kindF at this
    rw [if_neg hge] at this
    exact kind_ne_done _ this
  have hlen : ts.length = 3 + 2 * SlotsN (ts.map Tok.val) := by
    by_cases h4 : ts.length = 3
    · omega
    · have := hlt (ts.length - 1) (by omega) (by omega)
      omega
  have hkind' : ∀ k, 3 ≤ k → k < ts.length →
      (ts.getD k (.bit false)).kind = if (k - 3) % 2 = 0 then .num else .bit := by
    intro k hk3 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    rw [this]
    have h2 := hlt k hk3 hk
    rw [hS] at h2
    unfold kindF
    rw [if_pos h2]
  have hshape : ShapeF (ts.map Tok.val) := by
    refine ⟨by simpa using hT3, by rw [← hlen]; simp, fun o ho => ?_⟩
    have hk : 4 + 2 * o < ts.length := by omega
    rw [getD_map_val]
    have hkd := hkind' (4 + 2 * o) (by omega) hk
    rw [if_neg (by omega)] at hkd
    obtain ⟨bb, hbb⟩ := exists_bit (t := ts.getD (4 + 2 * o) (.bit false)) (by
      rw [List.getD_eq_getElem _ _ hk] at hkd ⊢; exact hkd)
    rw [List.getD_eq_getElem _ _ hk] at hbb
    rw [List.getD_eq_getElem _ _ hk, hbb]
    cases bb <;> simp [Tok.val]
  refine ⟨hshape, ?_⟩
  apply List.ext_getElem
  · rw [length_toksF]; simp
  · intro k h1 h2
    have hk : k < ts.length := h1
    have hg : (toksF (ts.map Tok.val))[k]'h2 = tokAt (ts.map Tok.val) k := by
      have := getD_toksF (ts.map Tok.val) (k := k) (by simpa using hk) (.bit false)
      rwa [List.getD_eq_getElem _ _ h2] at this
    rw [hg]
    have hv : (ts.map Tok.val).getD k 0 = Tok.val ts[k] := by
      rw [getD_map_val, List.getD_eq_getElem _ _ hk]
    have hkd := hkind k hk
    rw [List.getD_eq_getElem _ _ hk] at hkd
    unfold tokAt
    rw [hv]
    by_cases hk3 : k < 3
    · rw [if_pos hk3] at hkd
      obtain ⟨v, hvv⟩ := exists_num hkd
      rw [if_pos (Or.inl hk3), hvv]; rfl
    · have hkd' := hkind' k (by omega) hk
      rw [List.getD_eq_getElem _ _ hk] at hkd'
      by_cases hpar : k % 2 = 1
      · rw [if_pos (by omega)] at hkd'
        obtain ⟨v, hvv⟩ := exists_num hkd'
        rw [if_pos (Or.inr hpar), hvv]; rfl
      · rw [if_neg (by omega)] at hkd'
        obtain ⟨bb, hbb⟩ := exists_bit hkd'
        rw [if_neg (by omega), hbb]
        cases bb <;> simp [Tok.val]

end Lax117284Proofs.Machine.SatFormat
