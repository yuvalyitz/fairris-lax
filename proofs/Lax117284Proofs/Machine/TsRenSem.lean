import Lax117284Proofs.Machine.TsRenFormat
import Lax117284Proofs.Machine.SatSem
import Lax117284Proofs.TwoSatRename

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
