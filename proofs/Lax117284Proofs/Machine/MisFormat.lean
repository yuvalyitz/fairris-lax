import Lax117284Proofs.Machine.TokProg
import Lax117284Proofs.Machine.Lists

/-!
The format of an instance of Multicoloured Independent Set: the number of colour classes, the number
of vertices per class, and then the adjacency matrix, one bit per ordered pair of vertices.
-/

namespace Lax117284Proofs.Machine.MisFormat

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokProg

/-- What is expected after the two counts and `j` further tokens: a bit of the matrix as long as
it has not been read. -/
def kindM (l n j : ℕ) : Kind := if j < (l * n) * (l * n) then .bit else .done

/-- The format. -/
def EM : Format := fun ts =>
  if ts.length < 2 then .num
  else kindM (Tok.val (ts.getD 0 (.num 0))) (Tok.val (ts.getD 1 (.num 0))) (ts.length - 2)

/-- The number of vertices, read off the counts. -/
def VM (ns : List ℕ) : ℕ := ns.getD 0 0 * ns.getD 1 0

/-- The numbers of a stream of the format: two counts and the bits of the matrix. -/
def ShapeM (ns : List ℕ) : Prop :=
  2 ≤ ns.length ∧ ns.length = 2 + VM ns * VM ns ∧ ∀ k, 2 ≤ k → k < ns.length → ns.getD k 0 ≤ 1

/-- The token at a position. -/
def tokAtM (ns : List ℕ) (k : ℕ) : Tok :=
  if k < 2 then .num (ns.getD k 0) else .bit (decide (ns.getD k 0 ≠ 0))

/-- The tokens of a stream of numbers. -/
def toksM (ns : List ℕ) : List Tok := (List.range ns.length).map (tokAtM ns)

lemma length_toksM (ns : List ℕ) : (toksM ns).length = ns.length := by simp [toksM]

lemma getD_toksM (ns : List ℕ) {k : ℕ} (hk : k < ns.length) (d : Tok) :
    (toksM ns).getD k d = tokAtM ns k := by
  simp [toksM, List.getD_eq_getElem?_getD, hk]

lemma take_toksM (ns : List ℕ) (k : ℕ) (hk : k ≤ ns.length) :
    (toksM ns).take k = (List.range k).map (tokAtM ns) := by
  unfold toksM
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

lemma vals_toksM {ns : List ℕ} (h : ShapeM ns) : (toksM ns).map Tok.val = ns := by
  obtain ⟨h2, hl, hs⟩ := h
  apply List.ext_getElem
  · simp [toksM]
  · intro k h1 h2'
    have hk : k < ns.length := h2'
    simp only [toksM, List.getElem_map, List.getElem_range, tokAtM]
    split_ifs with h
    · simp [Tok.val, List.getD_eq_getElem _ _ hk, List.getElem?_eq_getElem hk]
    · have := hs k (by omega) hk
      rw [List.getD_eq_getElem _ _ hk] at this ⊢
      by_cases h0 : ns[k] = 0
      · simp [Tok.val, h0]
      · have : ns[k] = 1 := by omega
        simp [Tok.val, this]

lemma kind_tokAtM (ns : List ℕ) (k : ℕ) :
    (tokAtM ns k).kind = if k < 2 then .num else .bit := by
  unfold tokAtM; split_ifs <;> simp_all [Tok.kind]

theorem conforms_of_shape {ns : List ℕ} (h : ShapeM ns) : Conforms EM (toksM ns) := by
  have hv := vals_toksM h
  obtain ⟨h2, hl, hs⟩ := h
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [length_toksM] at hk
    rw [getD_toksM ns hk, kind_tokAtM, take_toksM ns k hk.le]
    simp only [EM, List.length_map, List.length_range]
    by_cases hk2 : k < 2
    · simp [hk2]
    · rw [if_neg hk2]
      have g0 : ((List.range k).map (tokAtM ns)).getD 0 (.num 0) = .num (ns.getD 0 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [tokAtM]
      have g1 : ((List.range k).map (tokAtM ns)).getD 1 (.num 0) = .num (ns.getD 1 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp [tokAtM]
      rw [g0, g1]
      have hlt : k - 2 < VM ns * VM ns := by omega
      have e : kindM (Tok.val (Tok.num (ns.getD 0 0))) (Tok.val (Tok.num (ns.getD 1 0))) (k - 2)
          = kindM (ns.getD 0 0) (ns.getD 1 0) (k - 2) := rfl
      rw [e]
      unfold kindM
      unfold VM at hlt
      rw [if_pos hlt, if_neg hk2]
  · have hlen : (toksM ns).length = 2 + VM ns * VM ns := by rw [length_toksM, hl]
    have g0 : (toksM ns).getD 0 (.num 0) = .num (ns.getD 0 0) := by
      rw [getD_toksM ns (by omega)]; simp [tokAtM]
    have g1 : (toksM ns).getD 1 (.num 0) = .num (ns.getD 1 0) := by
      rw [getD_toksM ns (by omega)]; simp [tokAtM]
    unfold EM
    rw [hlen, if_neg (by omega), g0, g1]
    have e : kindM (Tok.val (Tok.num (ns.getD 0 0))) (Tok.val (Tok.num (ns.getD 1 0)))
        (2 + VM ns * VM ns - 2) = kindM (ns.getD 0 0) (ns.getD 1 0) (2 + VM ns * VM ns - 2) := rfl
    rw [e]
    unfold kindM
    rw [Nat.add_sub_cancel_left]
    have hh : ¬ (VM ns * VM ns < ns.getD 0 0 * ns.getD 1 0 * (ns.getD 0 0 * ns.getD 1 0)) :=
      Nat.lt_irrefl _
    rw [if_neg hh]

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

/-- What conformance says. -/
lemma conforms_facts {ts : List Tok} (h : Conforms EM ts) :
    2 ≤ ts.length ∧ EM ts = .done ∧
    ∀ k < ts.length, (ts.getD k (.bit false)).kind =
      (if k < 2 then .num
        else kindM (Tok.val (ts.getD 0 (.num 0))) (Tok.val (ts.getD 1 (.num 0))) (k - 2)) := by
  obtain ⟨hf, hd⟩ := h
  refine ⟨?_, hd, ?_⟩
  · by_contra hlt
    unfold EM at hd
    rw [if_pos (by omega)] at hd
    exact absurd hd (by decide)
  · intro k hk
    rw [hf k hk]
    unfold EM
    rw [List.length_take, Nat.min_eq_left hk.le]
    by_cases hk2 : k < 2
    · rw [if_pos hk2, if_pos hk2]
    · rw [if_neg hk2, if_neg hk2]
      have e0 : (ts.take k).getD 0 (.num 0) = ts.getD 0 (.num 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_take_of_lt (by omega)]
      have e1 : (ts.take k).getD 1 (.num 0) = ts.getD 1 (.num 0) := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_take_of_lt (by omega)]
      rw [e0, e1]

theorem shape_of_conforms {ts : List Tok} (h : Conforms EM ts) :
    ShapeM (ts.map Tok.val) ∧ ts = toksM (ts.map Tok.val) := by
  obtain ⟨hT2, hd, hkind⟩ := conforms_facts h
  have hV : VM (ts.map Tok.val) = Tok.val (ts.getD 0 (.num 0)) * Tok.val (ts.getD 1 (.num 0)) := by
    unfold VM; rw [getD_map_val, getD_map_val]
  have hd' : ¬ (ts.length - 2 < VM (ts.map Tok.val) * VM (ts.map Tok.val)) := by
    intro hlt'
    unfold EM at hd
    rw [if_neg (by omega)] at hd
    unfold kindM at hd
    rw [hV] at hlt'
    rw [if_pos hlt'] at hd
    exact absurd hd (by decide)
  have hlt : ∀ k, 2 ≤ k → k < ts.length → k - 2 < VM (ts.map Tok.val) * VM (ts.map Tok.val) := by
    intro k hk2 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    by_contra hge
    rw [hV] at hge
    unfold kindM at this
    rw [if_neg hge] at this
    exact kind_ne_done _ this
  have hlen : ts.length = 2 + VM (ts.map Tok.val) * VM (ts.map Tok.val) := by
    by_cases h4 : ts.length = 2
    · omega
    · have := hlt (ts.length - 1) (by omega) (by omega)
      omega
  have hkind' : ∀ k, 2 ≤ k → k < ts.length → (ts.getD k (.bit false)).kind = .bit := by
    intro k hk2 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    rw [this]
    have h2 := hlt k hk2 hk
    rw [hV] at h2
    unfold kindM
    rw [if_pos h2]
  have hshape : ShapeM (ts.map Tok.val) := by
    refine ⟨by simpa using hT2, by rw [← hlen]; simp, fun k hk2 hk => ?_⟩
    have hk' : k < ts.length := by simpa using hk
    rw [getD_map_val]
    have hkd := hkind' k hk2 hk'
    obtain ⟨bb, hbb⟩ := exists_bit (t := ts.getD k (.bit false)) hkd
    rw [List.getD_eq_getElem _ _ hk'] at hbb
    rw [List.getD_eq_getElem _ _ hk', hbb]
    cases bb <;> simp [Tok.val]
  refine ⟨hshape, ?_⟩
  apply List.ext_getElem
  · rw [length_toksM]; simp
  · intro k h1 h2
    have hk : k < ts.length := h1
    have hg : (toksM (ts.map Tok.val))[k]'h2 = tokAtM (ts.map Tok.val) k := by
      have := getD_toksM (ts.map Tok.val) (k := k) (by simpa using hk) (.bit false)
      rwa [List.getD_eq_getElem _ _ h2] at this
    rw [hg]
    have hv : (ts.map Tok.val).getD k 0 = Tok.val ts[k] := by
      rw [getD_map_val, List.getD_eq_getElem _ _ hk]
    have hkd := hkind k hk
    rw [List.getD_eq_getElem _ _ hk] at hkd
    unfold tokAtM
    rw [hv]
    by_cases hk2 : k < 2
    · rw [if_pos hk2] at hkd
      obtain ⟨v, hvv⟩ := exists_num hkd
      rw [if_pos hk2, hvv]; rfl
    · have hkd' := hkind' k (by omega) hk
      rw [List.getD_eq_getElem _ _ hk] at hkd'
      obtain ⟨bb, hbb⟩ := exists_bit hkd'
      rw [if_neg hk2, hbb]
      cases bb <;> simp [Tok.val]

end Lax117284Proofs.Machine.MisFormat
