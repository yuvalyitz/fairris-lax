import Lax117284Proofs.Machine.TokProg
import Lax117284Proofs.Machine.Lists
import Lax117284Proofs.Machine.SatSem
import Lax117284Proofs.TwoSatRename
import Lax117284Proofs.Machine.SatOps
import Lax117284Proofs.Machine.UEmit
import Lax117284Proofs.Machine.SatCheck
import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.WrapTFinal

/-! ### `Lax117284Proofs.Machine.TsRenFormat` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.TsRenSem` -/

section
/-!
The renaming reduction on the numbers of a stream: the check that every position names a
variable of the formula, the word of a formula as a stream of the format, the formula of a
stream that passes the check, and the zeros and ones the machine writes.
-/

namespace Lax117284Proofs.Machine.TsRenSem

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TsRenFormat
open Lax117284Proofs.Machine.TokProg (Tok.val)
open Lax117284Proofs.TwoSatRename Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.SatSem (pairs_length pairs_getD flatMap_two)

/-! ### The numbers of a formula -/

/-- The numbers of a formula: the two counts, and the variable and the sign, `0` or `1`, of
every position. -/
def valsOf (φ : SF) : List ℕ :=
  [φ.vars, φ.clauses] ++ (List.range (2 * φ.clauses)).flatMap fun o => [idxF φ o, sgNat (sgF φ o)]

section Vals

variable (φ : SF)

lemma valsOf_length : (valsOf φ).length = 2 + 2 * (2 * φ.clauses) := by
  unfold valsOf
  rw [List.length_append, pairs_length (fun o => idxF φ o) (fun o => sgNat (sgF φ o))]
  simp

lemma valsOf_zero : (valsOf φ).getD 0 0 = φ.vars := by simp [valsOf]
lemma valsOf_one : (valsOf φ).getD 1 0 = φ.clauses := by simp [valsOf]

lemma valsOf_pos : PosN (valsOf φ) = 2 * φ.clauses := by
  unfold PosN; rw [valsOf_one]

lemma valsOf_idx {o : ℕ} (h : o < 2 * φ.clauses) : (valsOf φ).getD (2 + 2 * o) 0 = idxF φ o := by
  unfold valsOf
  have := (pairs_getD (fun o => idxF φ o) (fun o => sgNat (sgF φ o)) (2 * φ.clauses) o h).1
  rw [List.getD_append_right _ _ _ _ (by simp), show (2 + 2 * o) - [φ.vars, φ.clauses].length
    = 2 * o by simp]
  exact this

lemma valsOf_sign {o : ℕ} (h : o < 2 * φ.clauses) :
    (valsOf φ).getD (3 + 2 * o) 0 = sgNat (sgF φ o) := by
  unfold valsOf
  have := (pairs_getD (fun o => idxF φ o) (fun o => sgNat (sgF φ o)) (2 * φ.clauses) o h).2
  have e : (3 + 2 * o) - [φ.vars, φ.clauses].length = 2 * o + 1 := by simp; omega
  rw [List.getD_append_right _ _ _ _ (by simp; omega), e]
  exact this

theorem shape_valsOf : ShapeR (valsOf φ) := by
  refine ⟨by rw [valsOf_length]; omega, by rw [valsOf_length, valsOf_pos], fun o ho => ?_⟩
  rw [valsOf_pos] at ho
  rw [valsOf_sign φ ho]
  unfold sgNat
  split <;> omega

end Vals

/-! ### What the check asks -/

/-- The position `o` names a variable of the formula. -/
def PassR (ns : List ℕ) (o : ℕ) : Prop := ns.getD (2 + 2 * o) 0 < ns.getD 0 0

instance (ns : List ℕ) : DecidablePred (PassR ns) := fun o => by unfold PassR; infer_instance

/-- **What the check asks of a stream**: every position passes. -/
def CondR (ns : List ℕ) : Prop := ∀ o < PosN ns, PassR ns o

theorem condR_valsOf (φ : SF) : CondR (valsOf φ) := by
  intro o ho
  rw [valsOf_pos] at ho
  unfold PassR
  rw [valsOf_idx φ ho, valsOf_zero]
  exact idxF_lt φ ho

/-! ### The word of a formula -/

section Word

variable (φ : SF)

/-- The word of the position `o`: its variable and its sign. -/
def posWord (o : ℕ) : Word := encodeNat (idxF φ o) ++ [sgF φ o]

lemma lits_eq :
    ((List.finRange φ.clauses).flatMap fun c => (List.finRange 2).flatMap fun α =>
        encodeNat (φ.lit c α).1 ++ [(φ.lit c α).2]) =
    (List.range (2 * φ.clauses)).flatMap (posWord φ) := by
  have hH : ∀ (c : Fin φ.clauses) (α : Fin 2), posWord φ (2 * (c : ℕ) + (α : ℕ)) =
      encodeNat (φ.lit c α).1 ++ [(φ.lit c α).2] := by
    intro c α
    unfold posWord
    rw [idxF_eq, sgF_eq]
  rw [flatMap_two, flatMap_finRange]
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.mp hc
  rw [dif_pos hc']
  have e2 : (List.finRange 2).flatMap (fun α => encodeNat (φ.lit ⟨c, hc'⟩ α).1 ++
      [(φ.lit ⟨c, hc'⟩ α).2]) = (encodeNat (φ.lit ⟨c, hc'⟩ 0).1 ++ [(φ.lit ⟨c, hc'⟩ 0).2]) ++
        (encodeNat (φ.lit ⟨c, hc'⟩ 1).1 ++ [(φ.lit ⟨c, hc'⟩ 1).2]) := by
    simp [List.finRange_succ]
  rw [e2, ← hH ⟨c, hc'⟩ 0, ← hH ⟨c, hc'⟩ 1]
  rfl

theorem code_toksR : code (toksR (valsOf φ)) = Lax117284.TwoSatisfiability.encodeFormula φ := by
  have hL : (valsOf φ).length = 2 + 2 * (2 * φ.clauses) := valsOf_length φ
  have hpos : ∀ o, o < 2 * φ.clauses → Tok.code (tokAt (valsOf φ) (2 + (2 * o))) =
      encodeNat (idxF φ o) ∧ Tok.code (tokAt (valsOf φ) (2 + (2 * o + 1))) = [sgF φ o] := by
    intro o ho
    refine ⟨?_, ?_⟩
    · unfold tokAt
      rw [if_pos (Or.inr (by omega))]
      simp only [TokModel.Tok.code]
      rw [valsOf_idx φ ho]
    · unfold tokAt
      rw [if_neg (by omega), show 2 + (2 * o + 1) = 3 + 2 * o by ring, valsOf_sign φ ho]
      simp only [TokModel.Tok.code]
      unfold sgNat
      split <;> simp_all
  unfold toksR code Lax117284.TwoSatisfiability.encodeFormula
  rw [hL, List.range_add, List.map_append, List.flatMap_append, List.map_map, List.flatMap_map,
    List.append_assoc, lits_eq φ]
  rw [List.flatMap_map]
  have h2 : (List.range 2).flatMap (fun a => (tokAt (valsOf φ) a).code) =
      encodeNat φ.vars ++ encodeNat φ.clauses := by
    simp [List.range_succ, tokAt, Lax117284Proofs.Machine.TokModel.Tok.code, valsOf]
  rw [h2, List.append_assoc]
  congr 2
  rw [flatMap_two (fun a => ((tokAt (valsOf φ) ∘ fun x => 2 + x) a).code)]
  refine List.flatMap_congr fun o ho => ?_
  have h := hpos o (List.mem_range.mp ho)
  unfold posWord
  simp only [Function.comp]
  rw [h.1, h.2]

end Word

/-! ### A formula from a stream that passes the check -/

section Build

variable (ns : List ℕ)

/-- **The formula of a stream that passes the check.** -/
def formulaOf (hc : CondR ns) : SF where
  vars := ns.getD 0 0
  clauses := ns.getD 1 0
  lit c α :=
    (⟨ns.getD (2 + 2 * (2 * (c : ℕ) + (α : ℕ))) 0, hc _ (by
        have := c.isLt; have := α.isLt; unfold PosN; omega)⟩,
      decide (ns.getD (3 + 2 * (2 * (c : ℕ) + (α : ℕ))) 0 ≠ 0))

lemma clauses_formulaOf (hc : CondR ns) : (formulaOf ns hc).clauses = ns.getD 1 0 := rfl

lemma idxF_formulaOf (hc : CondR ns) {o : ℕ} (ho : o < PosN ns) :
    idxF (formulaOf ns hc) o = ns.getD (2 + 2 * o) 0 := by
  have h : o < 2 * (formulaOf ns hc).clauses := ho
  unfold idxF
  rw [dif_pos h]
  show ns.getD (2 + 2 * (2 * (o / 2) + o % 2)) 0 = _
  rw [Nat.div_add_mod]

lemma sgF_formulaOf (hc : CondR ns) {o : ℕ} (ho : o < PosN ns) :
    sgF (formulaOf ns hc) o = decide (ns.getD (3 + 2 * o) 0 ≠ 0) := by
  have h : o < 2 * (formulaOf ns hc).clauses := ho
  unfold sgF
  rw [dif_pos h]
  show decide (ns.getD (3 + 2 * (2 * (o / 2) + o % 2)) 0 ≠ 0) = _
  rw [Nat.div_add_mod]

theorem valsOf_formulaOf (hc : CondR ns) (hs : ShapeR ns) : valsOf (formulaOf ns hc) = ns := by
  obtain ⟨h2, hl, hsg⟩ := hs
  have hS : 2 * (formulaOf ns hc).clauses = PosN ns := rfl
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, ns = a :: b :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  unfold valsOf
  rw [hS]
  have hpairs : (List.range (PosN (a :: b :: rest))).flatMap (fun o =>
      [idxF (formulaOf (a :: b :: rest) hc) o, sgNat (sgF (formulaOf (a :: b :: rest) hc) o)]) =
      rest := by
    have := flatMap_pairs (a :: b :: rest) 2 (PosN (a :: b :: rest)) (by omega)
    simp only [List.drop_succ_cons, List.drop_zero] at this
    have hlen : 2 * PosN (a :: b :: rest) = rest.length := by
      simp only [List.length_cons] at hl; omega
    rw [hlen, List.take_length] at this
    refine Eq.trans (List.flatMap_congr fun o ho => ?_) this
    have ho' := List.mem_range.mp ho
    rw [idxF_formulaOf (a :: b :: rest) hc ho', sgF_formulaOf (a :: b :: rest) hc ho']
    have hsig := hsg o ho'
    rw [show 2 + 2 * o + 1 = 3 + 2 * o by omega]
    congr 2
    unfold sgNat
    generalize (a :: b :: rest).getD (3 + 2 * o) 0 = x at *
    by_cases hx : x = 0 <;> simp_all
    omega
  rw [hpairs]
  rfl

end Build

/-! ### The reduction, on streams -/

/-- The index of the position `o` of an array of numbers. -/
def idxA (arr : List ℕ) (o : ℕ) : ℕ := arr.getD (2 + 2 * o) 0

/-- The sign of the position `o`, as a number. -/
def sgA (arr : List ℕ) (o : ℕ) : ℕ := arr.getD (3 + 2 * o) 0

/-- The sign of the position `o`, as a Boolean. -/
def sgnA (arr : List ℕ) (o : ℕ) : Bool := decide (arr.getD (3 + 2 * o) 0 ≠ 0)

/-- The image of a stream, as a word. -/
noncomputable def outW (ns : List ℕ) : Word :=
  Lax429075.Encoding.encodeCNF (cnfOf (ns.getD 1 0) (idxA ns) (sgnA ns))

/-- **The gate of the reduction, on streams.** -/
theorem ren_gate (w : Word) :
    (∃ φ : SF, Lax117284.TwoSatisfiability.encodeFormula φ = w) ↔
      ∃ ts : List Tok, w = code ts ∧ Conforms ER ts ∧ CondR (ts.map Tok.val) := by
  constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨toksR (valsOf φ), (code_toksR φ).symm, conforms_of_shape (shape_valsOf φ), ?_⟩
    rw [vals_toksR (shape_valsOf φ)]
    exact condR_valsOf φ
  · rintro ⟨ts, rfl, hconf, hcond⟩
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    refine ⟨formulaOf _ hcond, ?_⟩
    have := code_toksR (formulaOf _ hcond)
    rw [valsOf_formulaOf _ hcond hshape] at this
    rw [← this, ← hts]

/-- **The reduction writes the code of the renamed formula.** -/
theorem ren_eq (ts : List Tok) (hconf : Conforms ER ts) (hcond : CondR (ts.map Tok.val)) :
    reduceR (code ts) = outW (ts.map Tok.val) := by
  obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
  have h1 := code_toksR (formulaOf _ hcond)
  rw [valsOf_formulaOf _ hcond hshape] at h1
  have hw : code ts = Lax117284.TwoSatisfiability.encodeFormula (formulaOf _ hcond) := by
    rw [← h1, ← hts]
  rw [hw, reduceR_encode]
  unfold outW toCNF
  congr 1
  rw [clauses_formulaOf]
  refine cnfOf_congr _ (fun p hp => ?_) (fun p hp => ?_)
  · rw [idxF_formulaOf _ hcond hp]; rfl
  · rw [sgF_formulaOf _ hcond hp]; rfl

/-- **A word that is not the code of an admissible stream is rejected.** -/
theorem ren_rej (w : Word)
    (h : ¬ ∃ ts : List Tok, w = code ts ∧ Conforms ER ts ∧ CondR (ts.map Tok.val)) :
    reduceR w = rejW :=
  reduceR_rej w (fun hg => h ((ren_gate w).1 hg))

/-! ### The zeros and ones the machine writes -/

/-- The zeros and ones of the image, read off an array of numbers with `C` clauses. -/
noncomputable def outBits (arr : List ℕ) (C : ℕ) : List ℕ :=
  (List.range C).flatMap (fun c => clauseBits (fo (idxA arr) (2 * c)) (sgA arr (2 * c))
    (fo (idxA arr) (2 * c + 1)) (sgA arr (2 * c + 1))) ++ [0]

lemma sgNat_sgnA (arr : List ℕ) (o : ℕ) (h : arr.getD (3 + 2 * o) 0 ≤ 1) :
    sgNat (sgnA arr o) = sgA arr o := by
  unfold sgNat sgnA sgA
  generalize arr.getD (3 + 2 * o) 0 = x at *
  by_cases hx : x = 0 <;> simp_all
  omega

/-- **The zeros and ones of the image of a stream.** -/
theorem natBits_outW (ns : List ℕ) (hs : ShapeR ns) :
    natBits (outW ns) = outBits ns (ns.getD 1 0) := by
  unfold outW outBits
  rw [natBits_encodeCNF_cnfOf]
  congr 1
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.mp hc
  have h1 := hs.2.2 (2 * c) (by unfold PosN; omega)
  have h2 := hs.2.2 (2 * c + 1) (by unfold PosN; omega)
  rw [sgNat_sgnA ns _ h1, sgNat_sgnA ns _ h2]

/-- The image depends on the numbers of the stream only. -/
theorem outBits_congr (arr ns : List ℕ) (C : ℕ)
    (h : ∀ k < 2 + 4 * C, arr.getD k 0 = ns.getD k 0) : outBits arr C = outBits ns C := by
  unfold outBits
  congr 1
  refine List.flatMap_congr fun c hc => ?_
  have hc' := List.mem_range.mp hc
  have hfo : ∀ p < 2 * C, fo (idxA arr) p = fo (idxA ns) p := fun p hp =>
    fo_congr fun j hj => by unfold idxA; exact h _ (by omega)
  have hsg : ∀ p < 2 * C, sgA arr p = sgA ns p := fun p hp => by
    unfold sgA; exact h _ (by omega)
  rw [hfo _ (by omega), hfo _ (by omega), hsg _ (by omega), hsg _ (by omega)]

end Lax117284Proofs.Machine.TsRenSem

end

/-! ### `Lax117284Proofs.Machine.TsRenFo` -/

section
/-!
The first occurrence of the variable of a position: a loop over the earlier positions that
remembers the first one carrying the same variable.
-/

namespace Lax117284Proofs.Machine.TsRenFo

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.TwoSatRename Lax117284Proofs.Machine.TsRenSem

variable {B : ℕ}

abbrev bumpS (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

/-- The body of the loop: compare the earlier position `j` with the given one, and remember
`j` if it is the first to agree. -/
def foBody : Com :=
  .seq (.assign "vj" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "j")))))
  (.seq (.ite (.eq (V "vj") (V "vp")) (.ite (.eq (V "r") (V "p")) (.assign "r" (V "j")) .skip) .skip)
    (bumpS "j"))

def foLoop : Com := .seq (.assign "j" (.lit 0)) (.while (.lt (V "j") (V "p")) foBody)

/-- The scalars the loop assigns. -/
def AF : List String := ["j", "vj", "r"]

structure FInv (arr : List ℕ) (p : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  hp : σ.vars "p" = p
  hvp : σ.vars "vp" = arr.getD (2 + 2 * p) 0
  hj : σ.vars "j" ≤ p
  hr : σ.vars "r" = if fo (idxA arr) p < σ.vars "j" then fo (idxA arr) p else p
  fr : ∀ y, y ∉ AF → σ.vars y = σ0.vars y

lemma finv_step (arr : List ℕ) (p : ℕ) (σ0 σ σ' : Env) (hI : FInv arr p σ0 σ)
    (hlt : σ.vars "j" < p) (hv : ∀ y, y ∉ AF → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (_hj : σ'.vars "j" = σ.vars "j")
    (hr : σ'.vars "r" = if fo (idxA arr) p < σ.vars "j" + 1 then fo (idxA arr) p else p) :
    FInv arr p σ0 (σ'.setVar "j" (σ.vars "j" + 1)) ∧
      (σ'.setVar "j" (σ.vars "j" + 1)).vars "j" = σ.vars "j" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hpv := hI.hp
  have hvpv := hI.hvp
  have hjle := hI.hj
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "p" (by simp [AF]), hpv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "vp" (by simp [AF]), hvpv]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar]; rw [if_neg (by decide), if_true, hr]
  · have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
    simp only [Env.setVar, if_neg hyj]
    rw [hv y hy, hfr y hy]

set_option maxHeartbeats 1600000 in
theorem foBody_spec (arr : List ℕ) (p : ℕ) (σ0 : Env)
    (hE : ∀ k ≤ p, arr.getD (2 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * p ≤ arr.length) (hpB : 2 * p + 16 < B) :
    Spec B (fun σ => FInv arr p σ0 σ ∧ σ.vars "j" < p) foBody
      (fun σ σ' => FInv arr p σ0 σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 40 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hpv, hvpv, hjle, hrv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  set j := σ.vars "j" with hjdef
  have hjv : σ.vars "j" = j := rfl
  have hfle := fo_le (idxA arr) p
  have hrB : σ.vars "r" < B := by rw [hrv]; split <;> omega
  have e1 := hE j (by omega)
  have e2 := hE p le_rfl
  have s1 := asg_idx (B := B) "vj" 2 2 "j" σ arr j hA rfl (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vj" (arr.getD (2 + 2 * j) 0) with hσ1
  have hvj : σ1.vars "vj" = arr.getD (2 + 2 * j) 0 := by simp [hσ1, Env.setVar]
  have hvp1 : σ1.vars "vp" = arr.getD (2 + 2 * p) 0 := by simp [hσ1, Env.setVar, hvpv]
  have hr1 : σ1.vars "r" = σ.vars "r" := by simp [hσ1, Env.setVar]
  have hp1 : σ1.vars "p" = p := by simp [hσ1, Env.setVar, hpv]
  have hj1 : σ1.vars "j" = j := by simp [hσ1, Env.setVar, hjv]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AF → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "vj" := fun h => hy (by simp [AF, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_eqv (B := B) "vj" "vp" σ1 _ _ hvj hvp1 (by omega) (by omega)
  have c2 := cond_eqv (B := B) "r" "p" σ1 _ _ hr1 hp1 hrB (by omega)
  have rI : ∀ σ' : Env, σ'.vars "j" = j →
      Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ' (σ'.setVar "j" (j + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "j" (.bin .add (V "j") (.lit 1))) σ'
          (σ'.setVar "j" (σ'.vars "j" + 1)) (1 + (Expr.bin .add (V "j") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  have hidx : idxA arr j = arr.getD (2 + 2 * j) 0 := rfl
  have hidxp : idxA arr p = arr.getD (2 + 2 * p) 0 := rfl
  by_cases hm : arr.getD (2 + 2 * j) 0 = arr.getD (2 + 2 * p) 0
  · have hT1 : (Cond.eq (V "vj") (V "vp")).evalB B σ1 = some true := by
      rw [c1, hm]; simp
    have hfo : fo (idxA arr) p ≤ j := fo_le_of_eq (idxA arr) p (by rw [hidx, hidxp, hm])
    by_cases hrp : σ.vars "r" = p
    · have hT2 : (Cond.eq (V "r") (V "p")).evalB B σ1 = some true := by
        rw [c2, hrp]; simp
      have hfoj : fo (idxA arr) p = j := by
        rw [hrv] at hrp
        by_contra hne
        have : fo (idxA arr) p < j := by omega
        rw [if_pos this] at hrp
        omega
      have s3 : Run B (.assign "r" (V "j")) σ1 (σ1.setVar "r" j) 2 := by
        have := Run.assign (B := B) (σ := σ1) (x := "r") (e := V "j") (v := j)
          (by have := evalB_var (B := B) (x := "j") (σ := σ1) (by omega); rwa [hj1] at this)
        exact this.mono (by simp [Expr.size])
      obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ (σ1.setVar "r" j) hI' hlt
        (fun y hy => by
          have : y ≠ "r" := fun h => hy (by simp [AF, h])
          simp only [Env.setVar, if_neg this]; exact hfr1 y hy)
        (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by simp [Env.setVar, hj1, hjdef])
        (by
          simp only [Env.setVar, if_true]
          rw [if_pos (by omega), hfoj])
      exact ⟨_, (s1.seq ((Run.ite_true hT1 (Run.ite_true hT2 s3)).seq
        (rI _ (by simp [Env.setVar, hj1])))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
    · have hF2 : (Cond.eq (V "r") (V "p")).evalB B σ1 = some false := by
        rw [c2]; simp only [beq_eq_false_iff_ne.mpr hrp]
      have hfoj : fo (idxA arr) p < j := by
        rw [hrv] at hrp
        by_contra hne
        rw [if_neg hne] at hrp
        exact hrp rfl
      obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ σ1 hI' hlt hfr1 ha1 ho1 hj1
        (by rw [hr1, hrv, if_pos hfoj, if_pos (by omega)])
      exact ⟨_, (s1.seq ((Run.ite_true hT1 (Run.ite_false hF2 Run.skip)).seq
        (rI _ hj1))).mono (by simp [Cond.size, Expr.size]), hJ, hJi⟩
  · have hF1 : (Cond.eq (V "vj") (V "vp")).evalB B σ1 = some false := by
      rw [c1]; simp only [beq_eq_false_iff_ne.mpr hm]
    have hne : fo (idxA arr) p ≠ j := fun h => by
      have := idx_fo (idxA arr) p
      rw [h, hidx, hidxp] at this
      exact hm this
    obtain ⟨hJ, hJi⟩ := finv_step arr p σ0 σ σ1 hI' hlt hfr1 ha1 ho1 hj1
      (by
        rw [hr1, hrv]
        by_cases hlt' : fo (idxA arr) p < j
        · rw [if_pos hlt', if_pos (by omega)]
        · rw [if_neg hlt', if_neg (by omega)])
    exact ⟨_, (s1.seq ((Run.ite_false hF1 Run.skip).seq (rI _ hj1))).mono
      (by simp [Cond.size, Expr.size]), hJ, hJi⟩

/-- **The loop finds the first occurrence.** -/
theorem foLoop_spec (arr : List ℕ) (p : ℕ) (σ : Env)
    (hE : ∀ k ≤ p, arr.getD (2 + 2 * k) 0 + 8 < B)
    (hlen : 3 + 2 * p ≤ arr.length) (hpB : 2 * p + 16 < B)
    (hA : σ.arrs "TK" = arr) (hpv : σ.vars "p" = p)
    (hvp : σ.vars "vp" = arr.getD (2 + 2 * p) 0) (hr : σ.vars "r" = p) :
    ∃ σ', Run B foLoop σ σ' ((40 + 4) * p + 6) ∧
      σ'.vars "r" = fo (idxA arr) p ∧ σ'.arrs = σ.arrs ∧
      σ'.out = σ.out ∧ ∀ y, y ∉ AF → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := foBody) "j" "p"
    (FInv arr p σ) p 40 (by omega) (fun _ h => h.hj) (fun _ h => h.hp)
    (foBody_spec arr p σ hE hlen hpB)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hpv],
      by simp [Env.setVar, hvp], by simp [Env.setVar], by
        simp [Env.setVar, hr], fun y hy => by
      have hyj : y ≠ "j" := fun h => hy (by simp [AF, h])
      simp [Env.setVar, hyj]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp), hI.out.trans (by simp), ?_⟩
  · rw [hI.hr, hi]
    have := fo_le (idxA arr) p
    by_cases h : fo (idxA arr) p < p
    · rw [if_pos h]
    · rw [if_neg h]; omega
  · intro y hy
    rw [hI.fr y hy]

end Lax117284Proofs.Machine.TsRenFo

end

/-! ### `Lax117284Proofs.Machine.TsRenLit` -/

section
/-!
Writing the image: a literal is a one, the first occurrence of its variable in unary, a zero
and its sign; a clause is a one, its two literals and a zero; the formula is its clauses and
a final zero.
-/

namespace Lax117284Proofs.Machine.TsRenLit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops
open Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.UEmit
open Lax117284Proofs.TwoSatRename Lax117284Proofs.Machine.TsRenSem Lax117284Proofs.Machine.TsRenFo

variable {B : ℕ}

/-- The literal of the position held by `p`. -/
def litCom : Com :=
  .seq (.write (.lit 1))
  (.seq (.assign "vp" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "p")))))
  (.seq (.assign "r" (V "p"))
  (.seq foLoop
  (.seq (emitRep 1 (V "r"))
  (.seq (.write (.lit 0))
  (.seq (.assign "sg" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "p")))))
    (.write (V "sg"))))))))

/-- The scalars a literal assigns. -/
def AL : List String := ["vp", "r", "j", "vj", "cn", "cc", "sg"]

/-- The cost of a literal at a position below `S`. -/
def Klit (S : ℕ) : ℕ := 2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2

/-- The bounds the positions below `S` of the array satisfy. -/
structure Bnd (B : ℕ) (arr : List ℕ) (S : ℕ) : Prop where
  hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B
  hEs : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B
  hlen : 2 + 2 * S ≤ arr.length
  hSB : 2 * S + 16 < B

/-- **One literal.** -/
theorem litCom_run (arr : List ℕ) (S p : ℕ) (σ : Env) (hb : Bnd B arr S) (hp : p < S)
    (hA : σ.arrs "TK" = arr) (hpv : σ.vars "p" = p) :
    ∃ σ', Run B litCom σ σ' (Klit S) ∧
      σ'.out = σ.out ++ litBits (fo (idxA arr) p) (sgA arr p) ∧ σ'.arrs = σ.arrs ∧
      ∀ y, y ∉ AL → σ'.vars y = σ.vars y := by
  have hEv := hb.hEv
  have hEs := hb.hEs
  have hlen := hb.hlen
  have hSB := hb.hSB
  have e1 := hEv p hp
  have e2 := hEs p hp
  have hfle := fo_le (idxA arr) p
  -- write 1
  have w1 := write_bit (B := B) 1 (by omega) σ
  set σ1 : Env := { σ with out := σ.out ++ [1] } with hσ1
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, hA]
  have hp1 : σ1.vars "p" = p := by simp [hσ1, hpv]
  -- vp := TK[2 + 2 p]
  have s2 := asg_idx (B := B) "vp" 2 2 "p" σ1 arr p hA1 hp1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "vp" (arr.getD (2 + 2 * p) 0) with hσ2
  have hp2 : σ2.vars "p" = p := by simp [hσ2, hp1]
  -- r := p
  have s3 : Run B (.assign "r" (V "p")) σ2 (σ2.setVar "r" p) 2 := by
    have := Run.assign (B := B) (σ := σ2) (x := "r") (e := V "p") (v := p)
      (by have := evalB_var (B := B) (x := "p") (σ := σ2) (by omega); rwa [hp2] at this)
    exact this.mono (by simp [Expr.size])
  set σ3 := σ2.setVar "r" p with hσ3
  -- the first occurrence
  obtain ⟨σ4, r4, hr4, ha4, ho4, hf4⟩ := foLoop_spec (B := B) arr p σ3
    (fun k hk => hEv k (by omega)) (by omega) (by omega)
    (by simp [hσ3, hσ2, Env.setVar, hA1]) (by simp [hσ3, hσ2, Env.setVar, hp1])
    (by simp [hσ3, hσ2, Env.setVar]) (by simp [hσ3, Env.setVar])
  -- the unary run
  obtain ⟨σ5, r5, ho5, ha5, -, hf5⟩ := emitRep_run (B := B) 1 (V "r") (fo (idxA arr) p) σ4
    (by omega) (by omega)
    (by have := evalB_var (B := B) (x := "r") (σ := σ4) (by rw [hr4]; omega); rwa [hr4] at this)
  -- write 0
  have w6 := write_bit (B := B) 0 (by omega) σ5
  set σ6 : Env := { σ5 with out := σ5.out ++ [0] } with hσ6
  have hA6 : σ6.arrs "TK" = arr := by
    simp only [hσ6]
    rw [ha5, ha4]; simp [hσ3, hσ2, Env.setVar, hA1]
  have hp6 : σ6.vars "p" = p := by
    simp only [hσ6]
    rw [hf5 "p" (by decide) (by decide), hf4 "p" (by simp [AF])]
    simp [hσ3, hσ2, Env.setVar, hp1]
  -- sg := TK[3 + 2 p]
  have s7 := asg_idx (B := B) "sg" 3 2 "p" σ6 arr p hA6 hp6 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ7 := σ6.setVar "sg" (arr.getD (3 + 2 * p) 0) with hσ7
  have hsg7 : σ7.vars "sg" = arr.getD (3 + 2 * p) 0 := by simp [hσ7, Env.setVar]
  -- write sg
  have w8 : Run B (.write (V "sg")) σ7 { σ7 with out := σ7.out ++ [arr.getD (3 + 2 * p) 0] } 2 := by
    have := Run.write (B := B) (σ := σ7) (e := V "sg")
      (evalB_var (B := B) (x := "sg") (σ := σ7) (by rw [hsg7]; omega))
    rw [hsg7] at this
    exact this.mono (by simp [Expr.size])
  refine ⟨_, (w1.seq (s2.seq (s3.seq (r4.seq (r5.seq (w6.seq (s7.seq w8))))))).mono ?_, ?_, ?_,
    fun y hy => ?_⟩
  · unfold Klit
    have h1 : (40 + 4) * p + 6 ≤ (40 + 4) * S + 6 := by omega
    have h2 : (6 + 4) * fo (idxA arr) p + 6 ≤ (6 + 4) * S + 6 := by omega
    simp only [Expr.size]
    omega
  · simp only [hσ7, Env.setVar, hσ6]
    rw [ho5, ho4]
    simp only [hσ3, hσ2, Env.setVar, hσ1]
    simp [litBits, sgA, List.append_assoc]
  · simp only [hσ7, Env.setVar, hσ6]
    rw [ha5, ha4]
    simp [hσ3, hσ2, hσ1, Env.setVar]
  · have g1 : y ≠ "sg" := fun h => hy (by simp [AL, h])
    have g2 : y ≠ "cc" := fun h => hy (by simp [AL, h])
    have g3 : y ≠ "cn" := fun h => hy (by simp [AL, h])
    have g4 : y ∉ AF := fun h => hy (by
      simp only [AF, AL, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have g5 : y ≠ "r" := fun h => hy (by simp [AL, h])
    have g6 : y ≠ "vp" := fun h => hy (by simp [AL, h])
    simp only [hσ7, Env.setVar, if_neg g1, hσ6]
    rw [hf5 y g2 g3, hf4 y g4]
    simp [hσ3, hσ2, hσ1, Env.setVar, g5, g6]

/-- The clause `i`: a one, its two literals, a zero. -/
def clauseBody : Com :=
  .seq (.write (.lit 1))
  (.seq (.assign "p" (.bin .mul (V "i") (.lit 2)))
  (.seq litCom
  (.seq (.assign "p" (add (.lit 1) (mul (.lit 2) (V "i"))))
  (.seq litCom (.write (.lit 0))))))

/-- The scalars a clause assigns. -/
def SC : List String := "i" :: "p" :: AL

/-- The cost of a clause. -/
def Kcl (S : ℕ) : ℕ := 2 + 4 + Klit S + 12 + Klit S + 2

/-- The bits of the clause `c`. -/
noncomputable def clauseOut (arr : List ℕ) (c : ℕ) : List ℕ :=
  clauseBits (fo (idxA arr) (2 * c)) (sgA arr (2 * c)) (fo (idxA arr) (2 * c + 1))
    (sgA arr (2 * c + 1))

/-- **One clause.** -/
theorem clauseBody_run (arr : List ℕ) (S : ℕ) (σ0 σ : Env) (hb : Bnd B arr S)
    (hAg : Agr SC σ0 σ) (hA : σ0.arrs "TK" = arr) (hlt : 2 * σ.vars "i" + 1 < S) :
    ∃ σ', Run B clauseBody σ σ' (Kcl S) ∧ σ'.out = σ.out ++ clauseOut arr (σ.vars "i") ∧
      Agr SC σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  have hSB := hb.hSB
  obtain ⟨i, hi⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hi] at hlt
  rw [hi]
  have hAσ : σ.arrs "TK" = arr := by rw [hAg.1, hA]
  -- write 1
  have w1 := write_bit (B := B) 1 (by omega) σ
  set σ1 : Env := { σ with out := σ.out ++ [1] } with hσ1
  have hi1 : σ1.vars "i" = i := by simp [hσ1, hi]
  -- p := 2 i
  have s2 := asg_binr (B := B) .mul "i" 2 "p" σ1 i hi1 (by simp; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s2
  set σ2 := σ1.setVar "p" (i * 2) with hσ2
  obtain ⟨σ3, r3, ho3, ha3, hf3⟩ := litCom_run (B := B) arr S (i * 2) σ2 hb (by omega)
    (by simp [hσ2, hσ1, Env.setVar, hAσ]) (by simp [hσ2, Env.setVar])
  have hi3 : σ3.vars "i" = i := by
    rw [hf3 "i" (by decide)]; simp [hσ2, hσ1, Env.setVar, hi]
  -- p := 1 + 2 i
  have s4 := asg_linl (B := B) "p" 1 2 "i" σ3 i hi3 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  set σ4 := σ3.setVar "p" (1 + 2 * i) with hσ4
  have hA4 : σ4.arrs "TK" = arr := by
    simp only [hσ4, Env.setVar]; rw [ha3]; simp [hσ2, hσ1, Env.setVar, hAσ]
  obtain ⟨σ5, r5, ho5, ha5, hf5⟩ := litCom_run (B := B) arr S (1 + 2 * i) σ4 hb (by omega) hA4
    (by simp [hσ4, Env.setVar])
  -- write 0
  have w6 := write_bit (B := B) 0 (by omega) σ5
  have hout : σ5.out ++ [0] = σ.out ++ clauseOut arr i := by
    rw [ho5]
    simp only [hσ4, Env.setVar]
    rw [ho3]
    simp only [hσ2, Env.setVar, hσ1, clauseOut, clauseBits]
    rw [show 1 + 2 * i = 2 * i + 1 by omega, show i * 2 = 2 * i by omega]
    simp [List.append_assoc]
  have harr : σ5.arrs = σ0.arrs := by
    rw [ha5]; simp only [hσ4, Env.setVar]; rw [ha3]; simp only [hσ2, Env.setVar, hσ1]
    exact hAg.1
  have hfr : ∀ y, y ∉ SC → σ5.vars y = σ0.vars y := by
    intro y hy
    have g1 : y ∉ AL := fun h => hy (by simp [SC, h])
    have g2 : y ≠ "p" := fun h => hy (by simp [SC, h])
    rw [hf5 y g1]
    simp only [hσ4, Env.setVar, if_neg g2]
    rw [hf3 y g1]
    simp only [hσ2, Env.setVar, if_neg g2, hσ1]
    exact hAg.2 y hy
  have hi5 : σ5.vars "i" = i := by
    rw [hf5 "i" (by decide)]
    simp only [hσ4, Env.setVar, if_neg (by decide : "i" ≠ "p")]
    exact hi3
  refine ⟨_, (w1.seq (s2.seq (r3.seq (s4.seq (r5.seq w6))))).mono ?_, hout, ⟨harr, hfr⟩, hi5⟩
  unfold Kcl; omega

/-- Write the whole image: the clauses, then a zero. -/
def printR : Com := .seq (outLoop "C" clauseBody) (.write (.lit 0))

/-- The cost of writing the image of `C` clauses. -/
def Kprint (S C : ℕ) : ℕ := (Kcl S + 10 + 4) * C + 6 + 2

/-- **Writing the image.** -/
theorem printR_run (arr : List ℕ) (C : ℕ) (σ : Env) (hb : Bnd B arr (2 * C))
    (hA : σ.arrs "TK" = arr) (hC : σ.vars "C" = C) (hCB : C + 1 < B) :
    ∃ σ', Run B printR σ σ' (Kprint (2 * C) C) ∧ σ'.out = σ.out ++ outBits arr C := by
  obtain ⟨σ1, r1, o1, -⟩ := eLoop (B := B) "C" clauseBody SC (clauseOut arr) (Kcl (2 * C)) C σ
    (by simp [SC]) (by decide) hC hCB (by
      intro τ hAg hlt
      exact clauseBody_run (B := B) arr (2 * C) σ τ hb hAg hA (by omega))
  have w2 := write_bit (B := B) 0 (by omega) σ1
  refine ⟨_, (r1.seq w2).mono (by unfold Kprint; omega), ?_⟩
  simp only
  rw [o1]
  unfold outBits clauseOut
  simp [List.append_assoc]

end Lax117284Proofs.Machine.TsRenLit

end

/-! ### `Lax117284Proofs.Machine.TsRenAccept` -/

section
/-!
The whole of the renaming reduction after the tokenizer has accepted: read the counts off the
array, check that every position names a variable of the formula, and write either the image
or the rejected word.
-/

namespace Lax117284Proofs.Machine.TsRenAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatCheck (flag_fail flag_pass)
open Lax117284Proofs.Machine.TsRenFormat Lax117284Proofs.Machine.TsRenSem
open Lax117284Proofs.Machine.TsRenLit
open Lax117284Proofs.Machine.TsRenFo (bumpS)

variable {B : ℕ}

/-! ### The counts -/

/-- Read the counts off the array: the number of variables, the number of clauses, the number
of positions; and raise the flag. -/
def prepR : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "C" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (.bin .mul (V "C") (.lit 2)))
    (.assign "ok" (.lit 1))))

/-- The scalars the preparation assigns. -/
def AP : List String := ["n", "C", "N", "ok"]

theorem prepR_run (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr) (h2 : 2 ≤ arr.length)
    (hE : ∀ k < 2, arr.getD k 0 + 8 < B) (hN : 2 * arr.getD 1 0 + 8 < B) :
    ∃ σ', Run B prepR σ σ' 14 ∧ σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "C" = arr.getD 1 0 ∧
      σ'.vars "N" = PosN arr ∧ σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AP → σ'.vars y = σ.vars y := by
  have e0 := hE 0 (by omega)
  have e1 := hE 1 (by omega)
  have s0 := asg_tkl (B := B) "n" 0 σ arr hA (by omega) (by omega) (by omega)
  set σ0 := σ.setVar "n" (arr.getD 0 0) with h0
  have A0 : σ0.arrs "TK" = arr := by simp [h0, Env.setVar, hA]
  have s1 := asg_tkl (B := B) "C" 1 σ0 arr A0 (by omega) (by omega) (by omega)
  set σ1 := σ0.setVar "C" (arr.getD 1 0) with h1
  have vC : σ1.vars "C" = arr.getD 1 0 := by simp [h1, Env.setVar]
  have s2 := asg_binr (B := B) .mul "C" 2 "N" σ1 (arr.getD 1 0) vC
    (by simp only [Bop.apply_mul]; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s2
  set σ2 := σ1.setVar "N" (arr.getD 1 0 * 2) with h2'
  have s3 := asg_lit (B := B) "ok" 1 σ2 (by omega)
  refine ⟨_, (s0.seq (s1.seq (s2.seq s3))).mono (by omega), ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · simp [h2', h1, h0, Env.setVar]
  · simp [h2', h1, Env.setVar]
  · simp [h2', Env.setVar, PosN]; omega
  · simp [Env.setVar]
  · simp [h2', h1, h0, Env.setVar]
  · simp [h2', h1, h0, Env.setVar]
  · have g1 : y ≠ "n" := fun h => hy (by simp [AP, h])
    have g2 : y ≠ "C" := fun h => hy (by simp [AP, h])
    have g3 : y ≠ "N" := fun h => hy (by simp [AP, h])
    have g4 : y ≠ "ok" := fun h => hy (by simp [AP, h])
    simp [h2', h1, h0, Env.setVar, g1, g2, g3, g4]

/-! ### The check -/

/-- The check of the position `i`: its variable is below the number of variables. -/
def chkBody : Com :=
  .seq (.assign "vp" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "i")))))
  (.seq (.ite (.lt (V "vp") (V "n")) .skip (.assign "ok" (.lit 0)))
    (bumpS "i"))

def chkLoop : Com := .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) chkBody)

/-- The scalars the pass assigns. -/
def AC : List String := ["vp", "ok", "i"]

structure CInv (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vN : σ.vars "N" = S
  vn : σ.vars "n" = n
  hi : σ.vars "i" ≤ S
  hok : σ.vars "ok" = flagTo (PassR arr) ok0 (σ.vars "i")
  fr : ∀ y, y ∉ AC → σ.vars y = σ0.vars y

lemma cinv_step (arr : List ℕ) (S n ok0 : ℕ) (σ0 σ σ' : Env) (hI : CInv arr S n ok0 σ0 σ)
    (hlt : σ.vars "i" < S) (hv : ∀ y, y ∉ AC → σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) (ho : σ'.out = σ.out) (_hi : σ'.vars "i" = σ.vars "i")
    (hok : σ'.vars "ok" = flagTo (PassR arr) ok0 (σ.vars "i" + 1)) :
    CInv arr S n ok0 σ0 (σ'.setVar "i" (σ.vars "i" + 1)) ∧
      (σ'.setVar "i" (σ.vars "i" + 1)).vars "i" = σ.vars "i" + 1 := by
  have hsa := hI.arrs
  have hso := hI.out
  have hA0 := hI.hA
  have hNv := hI.vN
  have hnv := hI.vn
  have hfr := hI.fr
  clear hI
  refine ⟨⟨?_, ?_, hA0, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, by simp [Env.setVar]⟩
  · simp only [Env.setVar]; rw [ha, hsa]
  · simp only [Env.setVar]; rw [ho, hso]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "N" (by simp [AC]), hNv]
  · simp only [Env.setVar]; rw [if_neg (by decide), hv "n" (by simp [AC]), hnv]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hok]
  · have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
    simp only [Env.setVar, if_neg hyi]
    rw [hv y hy, hfr y hy]

theorem chkBody_spec (arr : List ℕ) (S n ok0 : ℕ) (σ0 : Env) (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B) (hlen : 2 + 2 * S ≤ arr.length)
    (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => CInv arr S n ok0 σ0 σ ∧ σ.vars "i" < S) chkBody
      (fun σ σ' => CInv arr S n ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 30 := by
  rintro σ ⟨hI, hlt⟩
  have hI' := hI
  obtain ⟨hsa, hso, hA0, hNv, hnv, hile, hokv, hfr⟩ := hI
  have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
  obtain ⟨k, hk⟩ : ∃ k, σ.vars "i" = k := ⟨_, rfl⟩
  rw [hk] at hlt hokv
  have e1 := hEv k hlt
  have s1 := asg_idx (B := B) "vp" 2 2 "i" σ arr k hA hk (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ1 := σ.setVar "vp" (arr.getD (2 + 2 * k) 0) with hσ1
  have hvp1 : σ1.vars "vp" = arr.getD (2 + 2 * k) 0 := by simp [hσ1, Env.setVar]
  have hn1 : σ1.vars "n" = n := by simp [hσ1, Env.setVar, hnv]
  have hk1 : σ1.vars "i" = k := by simp [hσ1, Env.setVar, hk]
  have ha1 : σ1.arrs = σ.arrs := by simp [hσ1, Env.setVar]
  have ho1 : σ1.out = σ.out := by simp [hσ1, Env.setVar]
  have hfr1 : ∀ y, y ∉ AC → σ1.vars y = σ.vars y := by
    intro y hy
    have g1 : y ≠ "vp" := fun h => hy (by simp [AC, h])
    simp [hσ1, Env.setVar, g1]
  have c1 := cond_ltv (B := B) "vp" "n" σ1 _ _ hvp1 hn1 (by omega) (by omega)
  have rI : ∀ σ' : Env, σ'.vars "i" = k → Run B (bumpS "i") σ' (σ'.setVar "i" (k + 1)) 5 :=
    fun σ' hi' => by
      have r : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ'
          (σ'.setVar "i" (σ'.vars "i" + 1)) (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
        Run.assign (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
      rw [hi'] at r
      exact r.mono (by simp [Expr.size])
  by_cases hp : arr.getD (2 + 2 * k) 0 < n
  · have hT : (Cond.lt (V "vp") (V "n")).evalB B σ1 = some true := by
      rw [c1]; exact congrArg some (decide_eq_true hp)
    have hpass : PassR arr k := by unfold PassR; rw [← hn]; exact hp
    obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ σ1 hI' (by rw [hk]; exact hlt) hfr1 ha1 ho1
      (by rw [hk1, hk]) (by
        rw [hσ1]; simp only [Env.setVar, if_neg (by decide : "ok" ≠ "vp")]
        rw [hokv, hk, flag_pass (PassR arr) ok0 k hpass hok0])
    exact ⟨_, (s1.seq ((Run.ite_true hT Run.skip).seq (rI _ hk1))).mono
      (by simp [Cond.size, Expr.size]), by rw [hk] at hJ; exact hJ, by rw [hk] at hJi ⊢; exact hJi⟩
  · have hF : (Cond.lt (V "vp") (V "n")).evalB B σ1 = some false := by
      rw [c1]; exact congrArg some (decide_eq_false hp)
    have hfail : ¬ PassR arr k := fun h => hp (by unfold PassR at h; rwa [← hn] at h)
    have hrok : Run B (.assign "ok" (.lit 0)) σ1 (σ1.setVar "ok" 0) 2 :=
      (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
    have hi2 : (σ1.setVar "ok" 0).vars "i" = k := by simp [Env.setVar, hk1]
    obtain ⟨hJ, hJi⟩ := cinv_step arr S n ok0 σ0 σ (σ1.setVar "ok" 0) hI' (by rw [hk]; exact hlt)
      (fun y hy => by
        have hyo : y ≠ "ok" := fun h => hy (by simp [AC, h])
        simp only [Env.setVar, if_neg hyo]; exact hfr1 y hy)
      (by simp [Env.setVar, ha1]) (by simp [Env.setVar, ho1]) (by rw [hi2, hk])
      (by simp [Env.setVar, hk]; exact (flag_fail (PassR arr) ok0 _ hfail).symm)
    exact ⟨_, (s1.seq ((Run.ite_false hF hrok).seq (rI _ hi2))).mono
      (by simp [Cond.size, Expr.size]), by rw [hk] at hJ; exact hJ, by rw [hk] at hJi ⊢; exact hJi⟩

/-- **The pass.** -/
theorem chkLoop_run (arr : List ℕ) (S n ok0 : ℕ) (σ : Env) (hn : n = arr.getD 0 0)
    (hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B) (hlen : 2 + 2 * S ≤ arr.length)
    (hSB : 2 * S + 16 < B) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = S) (hnv : σ.vars "n" = n)
    (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B chkLoop σ σ' ((30 + 4) * S + 6) ∧
      σ'.vars "ok" = flagTo (PassR arr) ok0 S ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AC → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := chkBody) "i" "N"
    (CInv arr S n ok0 σ) S 30 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (chkBody_spec arr S n ok0 σ hn hEv hlen hSB hnB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hNv],
      by simp [Env.setVar, hnv], by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassR arr) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AC, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp), hI.out.trans (by simp), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

/-! ### The whole of the accepting phase -/

/-- Write the rejected word: one empty clause. -/
def rejR : Com := .seq (.write (.lit 1)) (.seq (.write (.lit 0)) (.write (.lit 0)))

theorem rejR_run (σ : Env) (hB : 2 < B) :
    ∃ σ', Run B rejR σ σ' 6 ∧ σ'.out = σ.out ++ [1, 0, 0] := by
  have w1 := write_bit (B := B) 1 (by omega) σ
  have w2 := write_bit (B := B) 0 (by omega) { σ with out := σ.out ++ [1] }
  have w3 := write_bit (B := B) 0 (by omega) { σ with out := σ.out ++ [1] ++ [0] }
  exact ⟨_, w1.seq (w2.seq w3), by simp⟩

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptR : Com :=
  .seq prepR (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printR rejR))

/-- The cost of the accepting phase, on an input of `l` tokens. -/
def KaccR (l : ℕ) : ℕ := 14 + ((30 + 4) * l + 6) + 4 + Kprint l l + 6

lemma Kprint_mono (S S' C C' : ℕ) (h1 : S ≤ S') (h2 : C ≤ C') :
    Kprint S C ≤ Kprint S' C' := by
  unfold Kprint Kcl Klit
  have : (2 + 4 + (2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2) + 12 +
      (2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2) + 2 + 10 + 4) * C ≤
      (2 + 4 + (2 + 12 + 2 + ((40 + 4) * S' + 6) + (2 + ((6 + 4) * S' + 6)) + 2 + 12 + 2) + 12 +
      (2 + 12 + 2 + ((40 + 4) * S' + 6) + (2 + ((6 + 4) * S' + 6)) + 2 + 12 + 2) + 2 + 10 + 4) * C' :=
    Nat.mul_le_mul (by omega) h2
  omega

lemma KaccR_mono (a b : ℕ) (h : a ≤ b) : KaccR a ≤ KaccR b := by
  unfold KaccR
  have := Kprint_mono a b a b h h
  omega

open scoped Classical in
/-- **The accepting phase.** -/
theorem acceptR_run (l : ℕ) (arr : List ℕ) (σ : Env) (hA : σ.arrs "TK" = arr)
    (hlen : 2 + 2 * PosN arr ≤ arr.length)
    (hE : ∀ k < 2 + 2 * PosN arr, arr.getD k 0 + 8 < B) (hl : PosN arr ≤ l)
    (hB : 2 * PosN arr + 20 < B) :
    ∃ σ', Run B acceptR σ σ' (KaccR l) ∧
      σ'.out = σ.out ++ (if CondR arr then outBits arr (arr.getD 1 0) else [1, 0, 0]) := by
  obtain ⟨S, hSdef⟩ : ∃ S, PosN arr = S := ⟨_, rfl⟩
  have hS2 : S = 2 * arr.getD 1 0 := by rw [← hSdef]; rfl
  rw [hSdef] at hlen hE hl hB
  have hn0 := hE 0 (by omega)
  have hn1 := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1C, e1N, e1ok, e1a, e1o, e1f⟩ :=
    prepR_run (B := B) arr σ hA (by omega) (fun k hk => hE k (by omega)) (by omega)
  rw [hSdef] at e1N
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_run (B := B) arr S (arr.getD 0 0) 1 σ1 rfl
    (fun k hk => hE _ (by omega)) hlen (by omega) hn0 le_rfl A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hC2 : σ2.vars "C" = arr.getD 1 0 := by rw [e2f "C" (by decide)]; exact e1C
  have hcond : σ2.vars "ok" = 1 ↔ CondR arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondR
    rw [hSdef]
    exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassR arr) 1 S; omega
  have hb : Bnd B arr (2 * arr.getD 1 0) :=
    ⟨fun k hk => hE _ (by omega), fun k hk => hE _ (by omega), by omega, by omega⟩
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := printR_run (B := B) arr (arr.getD 1 0) σ2 hb A2 hC2 (by omega)
    have hK := Kprint_mono (2 * arr.getD 1 0) l (arr.getD 1 0) l (by omega) (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true hcondT r3))).mono ?_, ?_⟩
    · unfold KaccR
      have h1 : (30 + 4) * S ≤ (30 + 4) * l := Nat.mul_le_mul_left _ hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_pos hc]
  · have hno : ¬ CondR arr := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    obtain ⟨σ3, r3, o3⟩ := rejR_run (B := B) σ2 (by omega)
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false hcondF r3))).mono ?_, ?_⟩
    · unfold KaccR
      have h1 : (30 + 4) * S ≤ (30 + 4) * l := Nat.mul_le_mul_left _ hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o3, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.TsRenAccept

end

/-! ### `Lax117284Proofs.Machine.TsRenNk` -/

section
/-!
What the format of a 2-CNF formula expects next, as a command: a number for each of the two
counts, and then a number and a bit alternately until every position has been read.
-/

namespace Lax117284Proofs.Machine.TsRenNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.TsRenFormat

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev div (e f : Expr) : Expr := .bin .div e f

/-- What the format expects, the number of clauses being `TK[1]`. -/
def nkR : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.lit 4) (.get "TK" (.lit 1))))
        (.ite (.lt (V "j") (V "n3"))
          (.assign "kind" (sub (V "j") (mul (div (V "j") (.lit 2)) (.lit 2))))
          (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the number of clauses being `C`. -/
def kindCodeR (Tn C : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindR C (Tn - 2))

variable {B : ℕ}

theorem nkR_flat (Tn C : ℕ) (hB : 4 * C + Tn + C + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 1 0 = C ∧
        (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkR
      (fun σ σ' => σ'.vars "kind" = kindCodeR Tn C ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 80 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = C›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k1 : kcode .bit = 1 := rfl
    have k2 : kcode .done = 2 := rfl
    unfold kindCodeR kindR
    split_ifs <;> simp_all [k0, k1, k2] <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]

/-- **The command meets the contract of the tokenizer.** -/
theorem nkR_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt ER cap nkR 80 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · have hE : ER toks = .num := by unfold ER; rw [if_pos h2]
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have h3 : 2 ≤ toks.length := by omega
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have hg : ∀ k, k < 2 → (σ.arrs "TK").getD k 0 = Tok.val (toks.getD k (.num 0)) := fun k hk => by
      have h1 : (σ.arrs "TK").getD k 0 = ((σ.arrs "TK").take toks.length).getD k 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega)]
      rw [h1, hTK, TsRenFormat.getD_map_val]
    have hb : ∀ k, k < 2 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 1 (by omega)
    have hBt : 10 * Bt ≤ 2 * (Bt * Bt) + 2 * Bt + 12 := by
      rcases Nat.lt_or_ge Bt 5 with h | h
      · interval_cases Bt <;> omega
      · nlinarith
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkR_flat (B := B) toks.length
      (Tok.val (toks.getD 1 (.num 0))) (by omega) σ
      ⟨hT, hg 1 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeR ER
    rw [if_neg h2, if_neg h2]

end Lax117284Proofs.Machine.TsRenNk

end

/-! ### `Lax117284Proofs.Machine.TsRenFinal` -/

section
/-!
The renaming reduction from the 2-CNF formulas of the scheduling submission into the 2-SAT of
`lax-429075` is polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.TsRenFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax434930.PolynomialTime
open Lax117284Proofs.Machine.TsRenFormat Lax117284Proofs.Machine.TsRenSem
open Lax117284Proofs.Machine.TsRenAccept Lax117284Proofs.Machine.TsRenLit
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)
open Lax117284Proofs.TwoSatRename

open scoped Classical

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := ER
  nk := TsRenNk.nkR
  Knk := 80
  hnk := fun B Bt cap hB => TsRenNk.nkR_spec (B := B) Bt cap hB
  red := reduceR
  cond := fun ts => CondR (ts.map Tok.val)
  outW := fun ts => outW (ts.map Tok.val)
  sem_acc := fun ts hc hcond => ren_eq ts hc hcond
  rejW := rejW
  sem_rej := fun w h => ren_rej w h
  rej := rejR
  Krej := fun _ => 6
  rejRun := fun B _ σ _ hB => by
    obtain ⟨σ', r, o⟩ := rejR_run (B := B) σ (by omega)
    exact ⟨σ', r, by rw [o, natBits_rejW]⟩
  acc := acceptR
  Kacc := fun _ l => KaccR l
  Kmono := fun _ a b h => KaccR_mono a b h
  accRun := fun B _ L ts arr σ hconf harr hA hlenL hvals hB _ => by
    obtain ⟨hshape, -⟩ := shape_of_conforms hconf
    obtain ⟨h2, hl, hsg⟩ := hshape
    have hlenns : (ts.map Tok.val).length = ts.length := by simp
    have harr' : arr.take (ts.map Tok.val).length = ts.map Tok.val := by rw [hlenns]; exact harr
    have hg : ∀ k < (ts.map Tok.val).length, arr.getD k 0 = (ts.map Tok.val).getD k 0 := by
      intro k hk
      conv_rhs => rw [← harr']
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
    have hval : ∀ k < (ts.map Tok.val).length, (ts.map Tok.val).getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk)
      rw [← e]
      exact hvals t ht
    obtain ⟨S, hS⟩ : ∃ S, PosN (ts.map Tok.val) = S := ⟨_, rfl⟩
    rw [hS] at hl hsg
    have hPa : PosN arr = S := by
      unfold PosN at hS ⊢; rw [hg 1 (by omega)]; exact hS
    have hlenA : 2 + 2 * S ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hpow : (2 : ℕ) ^ (L + 1) ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
    have hE : ∀ k < 2 + 2 * S, arr.getD k 0 + 8 < B := fun k hk => by
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hSL : S < L := by rw [hlenns] at hl; omega
    have h64 : 8 * L + 64 ≤ B := by have := Nat.zero_le (2 ^ (2 * L + 4)); omega
    obtain ⟨σ', r, o⟩ := acceptR_run (B := B) ts.length arr σ hA (by rw [hPa]; exact hlenA)
      (by rw [hPa]; exact hE) (by rw [hPa, ← hlenns]; omega) (by rw [hPa]; omega)
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    show _ = if CondR (ts.map Tok.val) then natBits (outW (ts.map Tok.val)) else natBits rejW
    have hcongr : CondR arr ↔ CondR (ts.map Tok.val) := by
      unfold CondR PassR
      rw [hPa, hS, hg 0 (by omega)]
      refine forall_congr' fun o => imp_congr_right fun ho => ?_
      rw [hg (2 + 2 * o) (by omega)]
    have hC : arr.getD 1 0 = (ts.map Tok.val).getD 1 0 := hg 1 (by omega)
    by_cases hc : CondR (ts.map Tok.val)
    · rw [if_pos hc, if_pos (hcongr.2 hc), natBits_outW _ ⟨h2, by rw [hl, hS], by rw [hS]; exact hsg⟩, hC,
        outBits_congr arr (ts.map Tok.val) _ (fun k hk => hg k (by
          have : 2 * (ts.map Tok.val).getD 1 0 = S := hS
          omega))]
    · rw [if_neg hc, if_neg (fun h => hc (hcongr.1 h)), natBits_rejW]

/-- The scalars and the arrays of the program. -/
def layoutR : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv",
    "n", "C", "N", "ok", "vp", "r", "vj", "sg", "cn", "cc"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutR W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, TsRenNk.nkR,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptR, prepR, chkLoop, chkBody, printR, rejR, Out.outLoop, clauseBody, litCom,
    TsRenFo.foLoop, TsRenFo.foBody, UEmit.emitRep, UEmit.repLoop, UEmit.repBody, layoutR,
    Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 300 * (Sz + 1) * (l + 1) ^ 2 := by
  intro Sz l
  show KaccR l ≤ _
  unfold KaccR Kprint Kcl Klit
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l), Nat.zero_le (Sz * l * l),
    Nat.zero_le (l * l)]

/-- **The renaming reduction is polynomial-time computable.** The program reads the word,
tokenizes it against the format of a 2-CNF formula — the number of variables, the number of
clauses, and a variable and a sign for each literal of every clause —, checks that every
literal names one of the formula's variables, and then writes, for every literal, the position
of the first occurrence of its variable in unary together with its sign, in the code of
`lax-429075`. The first occurrence is found by a loop over the earlier positions, so the phase
is quadratic in the number of tokens. -/
theorem reduceR_polyTime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceR) :=
  WrapTFinal.polyTimeE W layoutR com_ok rfl (by simp [layoutR]) 300 2 (by omega) Kpoly
    (fun Sz => by
      show 6 ≤ 300 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.TsRenFinal

end
