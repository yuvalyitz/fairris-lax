import Lax117284Proofs.Machine.MisFormat

/-!
The format of an instance of interval scheduling with eligible machine sets: the number of jobs
`n`, the number of machines `m`, the processing times, the deadlines and the weights of the `n`
jobs, and then the eligibility matrix, one bit per pair of a job and a machine.
-/

namespace Lax117284Proofs.Machine.JitHardFormat

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.MisFormat (getD_map_val kind_ne_done exists_num exists_bit)

/-- What is expected after the two counts and `j` further tokens: `3 n` numbers, then a bit of
the matrix as long as it has not been read. -/
def kindH (n m j : ℕ) : Kind :=
  if j < 3 * n then .num else if j - 3 * n < n * m then .bit else .done

/-- The format. -/
def EH : Format := fun ts =>
  if ts.length < 2 then .num
  else kindH (Tok.val (ts.getD 0 (.num 0))) (Tok.val (ts.getD 1 (.num 0))) (ts.length - 2)

/-- The number of jobs, read off the counts. -/
abbrev nH (ns : List ℕ) : ℕ := ns.getD 0 0

/-- The number of machines, read off the counts. -/
abbrev mH (ns : List ℕ) : ℕ := ns.getD 1 0

/-- The numbers of a stream of the format. -/
def ShapeH (ns : List ℕ) : Prop :=
  2 ≤ ns.length ∧ ns.length = 2 + 3 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 ∧
    ∀ k, 2 + 3 * ns.getD 0 0 ≤ k → k < ns.length → ns.getD k 0 ≤ 1

/-- The token at a position. -/
def tokAtH (ns : List ℕ) (k : ℕ) : Tok :=
  if k < 2 + 3 * ns.getD 0 0 then .num (ns.getD k 0) else .bit (decide (ns.getD k 0 ≠ 0))

/-- The tokens of a stream of numbers. -/
def toksH (ns : List ℕ) : List Tok := (List.range ns.length).map (tokAtH ns)

lemma length_toksH (ns : List ℕ) : (toksH ns).length = ns.length := by simp [toksH]

lemma getD_toksH (ns : List ℕ) {k : ℕ} (hk : k < ns.length) (d : Tok) :
    (toksH ns).getD k d = tokAtH ns k := by
  simp [toksH, List.getD_eq_getElem?_getD, hk]

lemma take_toksH (ns : List ℕ) (k : ℕ) (hk : k ≤ ns.length) :
    (toksH ns).take k = (List.range k).map (tokAtH ns) := by
  unfold toksH
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

lemma vals_toksH {ns : List ℕ} (h : ShapeH ns) : (toksH ns).map Tok.val = ns := by
  obtain ⟨h2, hl, hs⟩ := h
  apply List.ext_getElem
  · simp [toksH]
  · intro k h1 h2'
    have hk : k < ns.length := h2'
    simp only [toksH, List.getElem_map, List.getElem_range, tokAtH]
    split_ifs with h
    · simp [Tok.val, List.getElem?_eq_getElem hk]
    · have := hs k (by omega) hk
      rw [List.getD_eq_getElem _ _ hk] at this ⊢
      by_cases h0 : ns[k] = 0
      · simp [Tok.val, h0]
      · have : ns[k] = 1 := by omega
        simp [Tok.val, this]

lemma kind_tokAtH (ns : List ℕ) (k : ℕ) :
    (tokAtH ns k).kind = if k < 2 + 3 * ns.getD 0 0 then .num else .bit := by
  unfold tokAtH; split_ifs <;> simp_all [Tok.kind]

theorem conforms_of_shape {ns : List ℕ} (h : ShapeH ns) : Conforms EH (toksH ns) := by
  obtain ⟨h2, hl, hs⟩ := h
  have g0 : ∀ k, 2 ≤ k → ((List.range k).map (tokAtH ns)).getD 0 (.num 0) =
      .num (ns.getD 0 0) := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    have : (0 : ℕ) < 2 + 3 * ns.getD 0 0 := by omega
    show tokAtH ns 0 = _; unfold tokAtH; rw [if_pos this]
  have g1 : ∀ k, 2 ≤ k → ((List.range k).map (tokAtH ns)).getD 1 (.num 0) =
      .num (ns.getD 1 0) := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    have : (1 : ℕ) < 2 + 3 * ns.getD 0 0 := by omega
    show tokAtH ns 1 = _; unfold tokAtH; rw [if_pos this]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [length_toksH] at hk
    rw [getD_toksH ns hk, kind_tokAtH, take_toksH ns k hk.le]
    simp only [EH, List.length_map, List.length_range]
    by_cases hk2 : k < 2
    · rw [if_pos hk2, if_pos (by omega)]
    · rw [if_neg hk2, g0 k (by omega), g1 k (by omega)]
      show _ = kindH (ns.getD 0 0) (ns.getD 1 0) (k - 2)
      unfold kindH
      by_cases hk3 : k < 2 + 3 * ns.getD 0 0
      · rw [if_pos hk3, if_pos (by omega)]
      · have : k - 2 - 3 * ns.getD 0 0 < ns.getD 0 0 * ns.getD 1 0 := by omega
        rw [if_neg hk3, if_neg (by omega), if_pos this]
  · have hlen : (toksH ns).length = 2 + 3 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 := by
      rw [length_toksH, hl]
    have e0 : (toksH ns).getD 0 (.num 0) = .num (ns.getD 0 0) := by
      rw [getD_toksH ns (by omega)]
      have : (0 : ℕ) < 2 + 3 * ns.getD 0 0 := by omega
      unfold tokAtH; rw [if_pos this]
    have e1 : (toksH ns).getD 1 (.num 0) = .num (ns.getD 1 0) := by
      rw [getD_toksH ns (by omega)]
      have : (1 : ℕ) < 2 + 3 * ns.getD 0 0 := by omega
      unfold tokAtH; rw [if_pos this]
    unfold EH
    rw [hlen, if_neg (by omega), e0, e1]
    show kindH (ns.getD 0 0) (ns.getD 1 0) (2 + 3 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 - 2)
      = .done
    unfold kindH
    have : 2 + 3 * ns.getD 0 0 + ns.getD 0 0 * ns.getD 1 0 - 2 - 3 * ns.getD 0 0
        = ns.getD 0 0 * ns.getD 1 0 := by omega
    rw [if_neg (by omega), this, if_neg (Nat.lt_irrefl _)]

/-- What conformance says. -/
lemma conforms_facts {ts : List Tok} (h : Conforms EH ts) :
    2 ≤ ts.length ∧
      kindH (Tok.val (ts.getD 0 (.num 0))) (Tok.val (ts.getD 1 (.num 0))) (ts.length - 2) = .done ∧
    ∀ k < ts.length, (ts.getD k (.bit false)).kind =
      (if k < 2 then .num
        else kindH (Tok.val (ts.getD 0 (.num 0))) (Tok.val (ts.getD 1 (.num 0))) (k - 2)) := by
  obtain ⟨hf, hd⟩ := h
  have hT2 : 2 ≤ ts.length := by
    by_contra hlt
    unfold EH at hd
    rw [if_pos (by omega)] at hd
    exact absurd hd (by decide)
  refine ⟨hT2, ?_, ?_⟩
  · unfold EH at hd
    rwa [if_neg (by omega)] at hd
  · intro k hk
    rw [hf k hk]
    unfold EH
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

theorem shape_of_conforms {ts : List Tok} (h : Conforms EH ts) :
    ShapeH (ts.map Tok.val) ∧ ts = toksH (ts.map Tok.val) := by
  obtain ⟨hT2, hd, hkind⟩ := conforms_facts h
  have hnH : (ts.map Tok.val).getD 0 0 = Tok.val (ts.getD 0 (.num 0)) := getD_map_val ts 0
  have hmH : (ts.map Tok.val).getD 1 0 = Tok.val (ts.getD 1 (.num 0)) := getD_map_val ts 1
  generalize Tok.val (ts.getD 0 (.num 0)) = n at hkind hd hnH
  generalize Tok.val (ts.getD 1 (.num 0)) = m at hkind hd hmH
  have hlen1 : ¬ (ts.length - 2 < 3 * n) ∧ ¬ (ts.length - 2 - 3 * n < n * m) := by
    unfold kindH at hd
    split_ifs at hd <;> first | exact absurd hd (by decide) | omega
  -- every token but the last has kind num or bit
  have hnd : ∀ k, 2 ≤ k → k < ts.length → (k - 2 < 3 * n ∨ k - 2 - 3 * n < n * m) := by
    intro k hk2 hk
    have := hkind k hk
    rw [if_neg (by omega)] at this
    by_contra hcon
    push Not at hcon
    unfold kindH at this
    rw [if_neg (by omega), if_neg (by omega)] at this
    exact kind_ne_done _ this
  have hlen : ts.length = 2 + 3 * n + n * m := by
    by_cases h2 : ts.length = 2
    · omega
    · have := hnd (ts.length - 1) (by omega) (by omega)
      omega
  have hnum : ∀ k, k < ts.length → k < 2 + 3 * n → (ts.getD k (.bit false)).kind = .num := by
    intro k hk hk3
    rw [hkind k hk]
    by_cases hk2 : k < 2
    · rw [if_pos hk2]
    · rw [if_neg hk2]
      unfold kindH
      rw [if_pos (by omega)]
  have hbit : ∀ k, k < ts.length → 2 + 3 * n ≤ k → (ts.getD k (.bit false)).kind = .bit := by
    intro k hk hk3
    rw [hkind k hk, if_neg (by omega)]
    unfold kindH
    rw [if_neg (by omega), if_pos (by omega)]
  have hshape : ShapeH (ts.map Tok.val) := by
    unfold ShapeH
    rw [hnH, hmH]
    refine ⟨by simpa using hT2, by simpa using hlen, fun k hk2 hk => ?_⟩
    have hk' : k < ts.length := by simpa using hk
    rw [getD_map_val]
    have hkd := hbit k hk' hk2
    obtain ⟨bb, hbb⟩ := exists_bit (t := ts.getD k (.bit false)) hkd
    rw [List.getD_eq_getElem _ _ hk'] at hbb
    rw [List.getD_eq_getElem _ _ hk', hbb]
    cases bb <;> simp [Tok.val]
  refine ⟨hshape, ?_⟩
  apply List.ext_getElem
  · rw [length_toksH]; simp
  · intro k h1 h2
    have hk : k < ts.length := h1
    have hg : (toksH (ts.map Tok.val))[k]'h2 = tokAtH (ts.map Tok.val) k := by
      have := getD_toksH (ts.map Tok.val) (k := k) (by simpa using hk) (.bit false)
      rwa [List.getD_eq_getElem _ _ h2] at this
    rw [hg]
    have hv : (ts.map Tok.val).getD k 0 = Tok.val ts[k] := by
      rw [getD_map_val, List.getD_eq_getElem _ _ hk]
    unfold tokAtH
    rw [hv, hnH]
    by_cases hk3 : k < 2 + 3 * n
    · have hkd := hnum k hk hk3
      rw [List.getD_eq_getElem _ _ hk] at hkd
      obtain ⟨v, hvv⟩ := exists_num hkd
      rw [if_pos hk3, hvv]; rfl
    · have hkd := hbit k hk (by omega)
      rw [List.getD_eq_getElem _ _ hk] at hkd
      obtain ⟨bb, hbb⟩ := exists_bit hkd
      rw [if_neg hk3, hbb]
      cases bb <;> simp [Tok.val]

end Lax117284Proofs.Machine.JitHardFormat
