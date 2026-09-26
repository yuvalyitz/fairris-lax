import Lax117284.TwoSatisfiability
import Lax117284.TwoSatCNF
import Lax429075.EncodingCorrect
import Lax117284Proofs.SourceInjectivity
import Lax117284Proofs.Machine.Bits
import Mathlib.Data.Nat.Find

/-!
The renaming of a 2-CNF formula of the scheduling submission into a formula of `lax-429075`:
every occurrence of a variable is renamed to the position of the first occurrence of that
variable, so that the indices of the image are bounded by the number of positions and the
unary code of `lax-429075` stays polynomial. The renaming preserves satisfiability, and the
map on words, defined here mathematically, is correct.
-/

namespace Lax117284Proofs.TwoSatRename

open Lax434930.PolynomialTime Lax429075.CNF Lax117284.TwoSatCNF
open Lax117284Proofs.Machine.Bits
open scoped Classical

/-! ### The first occurrence -/

/-- The first position carrying the same index as the position `p`. -/
noncomputable def fo (idx : ℕ → ℕ) (p : ℕ) : ℕ := Nat.find (⟨p, rfl⟩ : ∃ j, idx j = idx p)

lemma idx_fo (idx : ℕ → ℕ) (p : ℕ) : idx (fo idx p) = idx p :=
  Nat.find_spec (⟨p, rfl⟩ : ∃ j, idx j = idx p)

lemma fo_le (idx : ℕ → ℕ) (p : ℕ) : fo idx p ≤ p :=
  Nat.find_min' (⟨p, rfl⟩ : ∃ j, idx j = idx p) rfl

lemma fo_min (idx : ℕ → ℕ) (p : ℕ) {j : ℕ} (hj : j < fo idx p) : idx j ≠ idx p :=
  Nat.find_min (⟨p, rfl⟩ : ∃ j, idx j = idx p) hj

lemma fo_le_of_eq (idx : ℕ → ℕ) (p : ℕ) {j : ℕ} (hj : idx j = idx p) : fo idx p ≤ j :=
  Nat.find_min' (⟨p, rfl⟩ : ∃ j, idx j = idx p) hj

lemma fo_eq_of_idx_eq {idx : ℕ → ℕ} {p q : ℕ} (h : idx p = idx q) : fo idx p = fo idx q := by
  apply le_antisymm
  · exact fo_le_of_eq idx p (by rw [idx_fo idx q, h])
  · exact fo_le_of_eq idx q (by rw [idx_fo idx p, h])

/-- **Two positions get the same name exactly when they carry the same index.** -/
lemma fo_eq_iff (idx : ℕ → ℕ) (p q : ℕ) : fo idx p = fo idx q ↔ idx p = idx q := by
  refine ⟨fun h => ?_, fo_eq_of_idx_eq⟩
  rw [← idx_fo idx p, h, idx_fo idx q]

/-- The first occurrence lies before `j` exactly when some earlier position carries the index. -/
lemma fo_lt_iff (idx : ℕ → ℕ) (p j : ℕ) : fo idx p < j ↔ ∃ i < j, idx i = idx p := by
  constructor
  · intro h
    exact ⟨fo idx p, h, idx_fo idx p⟩
  · rintro ⟨i, hi, hie⟩
    exact lt_of_le_of_lt (fo_le_of_eq idx p hie) hi

/-- The first occurrence depends on the indices up to `p` only. -/
lemma fo_congr {idx idx' : ℕ → ℕ} {p : ℕ} (h : ∀ j ≤ p, idx j = idx' j) :
    fo idx p = fo idx' p := by
  have h1 : ∀ j ≤ p, idx' j = idx j := fun j hj => (h j hj).symm
  apply le_antisymm
  · exact fo_le_of_eq idx p (by
      rw [h _ (fo_le idx' p), idx_fo idx' p, h p le_rfl])
  · exact fo_le_of_eq idx' p (by
      rw [h1 _ (fo_le idx p), idx_fo idx p, h1 p le_rfl])

/-! ### The renamed formula -/

/-- The literal of the position `p`: the first occurrence of its index, with its sign. -/
noncomputable def litAt (idx : ℕ → ℕ) (sgn : ℕ → Bool) (p : ℕ) : Literal := ⟨fo idx p, sgn p⟩

/-- The formula of `C` clauses whose position `2 c + α` carries the index `idx (2 c + α)` and
the sign `sgn (2 c + α)`, renamed. -/
noncomputable def cnfOf (C : ℕ) (idx : ℕ → ℕ) (sgn : ℕ → Bool) : Formula :=
  (List.range C).map fun c => [litAt idx sgn (2 * c), litAt idx sgn (2 * c + 1)]

/-- The renamed formula depends on the indices and signs of its positions only. -/
theorem cnfOf_congr (C : ℕ) {idx idx' : ℕ → ℕ} {sgn sgn' : ℕ → Bool}
    (h1 : ∀ p < 2 * C, idx p = idx' p) (h2 : ∀ p < 2 * C, sgn p = sgn' p) :
    cnfOf C idx sgn = cnfOf C idx' sgn' := by
  unfold cnfOf
  refine List.map_congr_left fun c hc => ?_
  have hc' := List.mem_range.mp hc
  unfold litAt
  rw [fo_congr (fun j hj => h1 j (by omega)), fo_congr (fun j hj => h1 j (by omega)),
    h2 _ (by omega), h2 _ (by omega)]

theorem isTwoCNF_cnfOf (C : ℕ) (idx : ℕ → ℕ) (sgn : ℕ → Bool) : IsTwoCNF (cnfOf C idx sgn) := by
  intro K hK
  simp only [cnfOf, List.mem_map, List.mem_range] at hK
  obtain ⟨c, -, rfl⟩ := hK
  simp

lemma lit_eval_iff (r : ℕ) (s : Bool) (ρ : Assignment) :
    Literal.eval ⟨r, s⟩ ρ = true ↔ ρ r = s := by
  cases s <;> simp [Literal.eval]

theorem eval_cnfOf (C : ℕ) (idx : ℕ → ℕ) (sgn : ℕ → Bool) (ρ : Assignment) :
    eval (cnfOf C idx sgn) ρ = true ↔
      ∀ c < C, ρ (fo idx (2 * c)) = sgn (2 * c) ∨ ρ (fo idx (2 * c + 1)) = sgn (2 * c + 1) := by
  simp only [eval, cnfOf, List.all_eq_true, List.mem_map, List.mem_range, List.any_eq_true,
    List.mem_cons, List.not_mem_nil, or_false, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, litAt]
  constructor
  · intro h c hc
    obtain ⟨l, hl, he⟩ := h c hc
    rcases hl with rfl | rfl
    · exact Or.inl ((lit_eval_iff _ _ ρ).1 he)
    · exact Or.inr ((lit_eval_iff _ _ ρ).1 he)
  · intro h c hc
    rcases h c hc with h1 | h1
    · exact ⟨_, Or.inl rfl, (lit_eval_iff _ _ ρ).2 h1⟩
    · exact ⟨_, Or.inr rfl, (lit_eval_iff _ _ ρ).2 h1⟩

/-! ### The formulas of the scheduling submission -/

/-- The formulas of the scheduling submission. -/
abbrev SF := Lax117284.TwoSatisfiability.Formula

/-- The index of the position `2 c + α` of `φ`: the variable of its literal `α` of clause `c`. -/
def idxF (φ : SF) (p : ℕ) : ℕ :=
  if h : p < 2 * φ.clauses then ((φ.lit ⟨p / 2, by omega⟩ ⟨p % 2, by omega⟩).1 : ℕ) else 0

/-- The sign of the position `2 c + α` of `φ`. -/
def sgF (φ : SF) (p : ℕ) : Bool :=
  if h : p < 2 * φ.clauses then (φ.lit ⟨p / 2, by omega⟩ ⟨p % 2, by omega⟩).2 else false

lemma idxF_eq (φ : SF) (c : Fin φ.clauses) (α : Fin 2) :
    idxF φ (2 * c + α) = (φ.lit c α).1 := by
  have hc := c.isLt
  have hα := α.isLt
  have h : 2 * (c : ℕ) + α < 2 * φ.clauses := by omega
  unfold idxF
  rw [dif_pos h]
  have e1 : (⟨(2 * (c : ℕ) + α) / 2, by omega⟩ : Fin φ.clauses) = c := Fin.ext (by simp; omega)
  have e2 : (⟨(2 * (c : ℕ) + α) % 2, by omega⟩ : Fin 2) = α := Fin.ext (by simp; omega)
  rw [e1, e2]

lemma sgF_eq (φ : SF) (c : Fin φ.clauses) (α : Fin 2) :
    sgF φ (2 * c + α) = (φ.lit c α).2 := by
  have hc := c.isLt
  have hα := α.isLt
  have h : 2 * (c : ℕ) + α < 2 * φ.clauses := by omega
  unfold sgF
  rw [dif_pos h]
  have e1 : (⟨(2 * (c : ℕ) + α) / 2, by omega⟩ : Fin φ.clauses) = c := Fin.ext (by simp; omega)
  have e2 : (⟨(2 * (c : ℕ) + α) % 2, by omega⟩ : Fin 2) = α := Fin.ext (by simp; omega)
  rw [e1, e2]

lemma idxF_lt (φ : SF) {p : ℕ} (hp : p < 2 * φ.clauses) : idxF φ p < φ.vars := by
  unfold idxF
  rw [dif_pos hp]
  exact Fin.isLt _

/-- **The renamed formula of `φ`.** -/
noncomputable def toCNF (φ : SF) : Formula := cnfOf φ.clauses (idxF φ) (sgF φ)

theorem isTwoCNF_toCNF (φ : SF) : IsTwoCNF (toCNF φ) := isTwoCNF_cnfOf _ _ _

/-- A position of `φ` as a clause and a literal. -/
lemma pos_cases (φ : SF) (c : ℕ) (hc : c < φ.clauses) (α : ℕ) (hα : α < 2) :
    ∃ (c' : Fin φ.clauses) (α' : Fin 2), 2 * c + α = 2 * c' + α' :=
  ⟨⟨c, hc⟩, ⟨α, hα⟩, rfl⟩

/-- **Renaming preserves satisfiability.** -/
theorem satisfiable_iff (φ : SF) : φ.Satisfiable ↔ Satisfiable (toCNF φ) := by
  constructor
  · rintro ⟨a, ha⟩
    let a' : ℕ → Bool := fun v => if h : v < φ.vars then a ⟨v, h⟩ else false
    refine ⟨fun r => a' (idxF φ r), ?_⟩
    rw [toCNF, eval_cnfOf]
    intro c hc
    obtain ⟨α, hα⟩ := ha ⟨c, hc⟩
    have key : ∀ β : Fin 2, a' (idxF φ (fo (idxF φ) (2 * c + β))) = a (φ.lit ⟨c, hc⟩ β).1 := by
      intro β
      rw [idx_fo (idxF φ) (2 * c + β)]
      have e := idxF_eq φ ⟨c, hc⟩ β
      rw [e]
      simp only [a', dif_pos (Fin.isLt _)]
    have hs : ∀ β : Fin 2, sgF φ (2 * c + β) = (φ.lit ⟨c, hc⟩ β).2 := fun β => by
      have := sgF_eq φ ⟨c, hc⟩ β
      simpa using this
    rcases (by omega : (α : ℕ) = 0 ∨ (α : ℕ) = 1) with h0 | h1
    · left
      have e : α = 0 := Fin.ext h0
      subst e
      have := key 0
      simp only [Fin.val_zero, Nat.add_zero] at this
      rw [this, hα]
      have := hs 0
      simp only [Fin.val_zero, Nat.add_zero] at this
      rw [this]
    · right
      have e : α = 1 := Fin.ext h1
      subst e
      have := key 1
      simp only [Fin.val_one] at this
      rw [this, hα]
      have := hs 1
      simp only [Fin.val_one] at this
      rw [this]
  · rintro ⟨ρ, hρ⟩
    rw [toCNF, eval_cnfOf] at hρ
    let a : φ.Assignment := fun v =>
      if h : ∃ p, p < 2 * φ.clauses ∧ idxF φ p = v then ρ (fo (idxF φ) h.choose) else false
    refine ⟨a, fun c => ?_⟩
    have key : ∀ β : Fin 2, a (φ.lit c β).1 = ρ (fo (idxF φ) (2 * c + β)) := by
      intro β
      have hp : 2 * (c : ℕ) + β < 2 * φ.clauses := by have := c.isLt; have := β.isLt; omega
      have hex : ∃ p, p < 2 * φ.clauses ∧ idxF φ p = (φ.lit c β).1 :=
        ⟨2 * c + β, hp, idxF_eq φ c β⟩
      simp only [a, dif_pos hex]
      congr 1
      apply fo_eq_of_idx_eq
      rw [hex.choose_spec.2, idxF_eq]
    have hs : ∀ β : Fin 2, sgF φ (2 * c + β) = (φ.lit c β).2 := sgF_eq φ c
    rcases hρ c c.isLt with h | h
    · refine ⟨0, ?_⟩
      have k := key 0
      have s := hs 0
      simp only [Fin.val_zero, Nat.add_zero] at k s
      rw [k, h, s]
    · refine ⟨1, ?_⟩
      have k := key 1
      have s := hs 1
      simp only [Fin.val_one] at k s
      rw [k, h, s]

/-! ### The words -/

open Lax429075.Encoding in
lemma encodeList_eq {α : Type} (e : α → Word) (l : List α) :
    encodeList e l = l.flatMap (fun a => true :: e a) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [encodeList, ih]

/-- The zeros and ones of the code of a literal renamed to `r` with the sign `s`. -/
def litBits (r s : ℕ) : List ℕ := [1] ++ List.replicate r 1 ++ [0, s]

/-- The zeros and ones of the code of a clause. -/
def clauseBits (r0 s0 r1 s1 : ℕ) : List ℕ := [1] ++ litBits r0 s0 ++ litBits r1 s1 ++ [0]

/-- The sign as a number. -/
def sgNat (b : Bool) : ℕ := if b then 1 else 0

open Lax429075.Encoding in
/-- **The zeros and ones of the code of the renamed formula.** -/
theorem natBits_encodeCNF_cnfOf (C : ℕ) (idx : ℕ → ℕ) (sgn : ℕ → Bool) :
    natBits (encodeCNF (cnfOf C idx sgn)) =
      (List.range C).flatMap (fun c => clauseBits (fo idx (2 * c)) (sgNat (sgn (2 * c)))
        (fo idx (2 * c + 1)) (sgNat (sgn (2 * c + 1)))) ++ [0] := by
  unfold encodeCNF cnfOf
  rw [encodeList_eq, List.flatMap_map]
  simp only [natBits, List.map_append, List.map_cons, List.map_nil, List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun c _ => ?_
  simp only [encodeClause, encodeList, encodeLiteral, encodeNat, litAt, List.map_cons,
    List.map_append, List.map_replicate, List.map_nil, clauseBits, litBits, sgNat]
  cases sgn (2 * c) <;> cases sgn (2 * c + 1) <;> simp

/-- The word every rejected word is sent to: the formula of one empty clause. -/
def rejW : Word := Lax429075.Encoding.encodeCNF [[]]

lemma natBits_rejW : natBits rejW = [1, 0, 0] := rfl

/-- **A code word lies in 2-SAT exactly when the formula is a satisfiable 2-CNF formula.** -/
theorem encodeCNF_mem_iff (F : Formula) :
    Lax429075.Encoding.encodeCNF F ∈ TwoSAT ↔ IsTwoCNF F ∧ Satisfiable F := by
  constructor
  · rintro ⟨F', hF', h2, hs⟩
    have h1 := Lax429075.EncodingCorrect.roundtrip F'
    rw [hF', Lax429075.EncodingCorrect.roundtrip F] at h1
    obtain rfl := Option.some.inj h1
    exact ⟨h2, hs⟩
  · rintro ⟨h2, hs⟩
    exact ⟨F, rfl, h2, hs⟩

theorem rejW_notMem : rejW ∉ TwoSAT := by
  rw [rejW, encodeCNF_mem_iff]
  rintro ⟨-, ρ, hρ⟩
  simp [eval] at hρ

/-- **The reduction, as a map on words**: the code of a formula goes to the code of its
renaming, every other word to the rejected word. -/
noncomputable def reduceR (w : Word) : Word :=
  if h : ∃ φ : SF, Lax117284.TwoSatisfiability.encodeFormula φ = w then
    Lax429075.Encoding.encodeCNF (toCNF h.choose)
  else rejW

theorem reduceR_encode (φ : SF) :
    reduceR (Lax117284.TwoSatisfiability.encodeFormula φ) =
      Lax429075.Encoding.encodeCNF (toCNF φ) := by
  have hg : ∃ φ' : SF, Lax117284.TwoSatisfiability.encodeFormula φ' =
      Lax117284.TwoSatisfiability.encodeFormula φ := ⟨φ, rfl⟩
  unfold reduceR
  rw [dif_pos hg]
  have := Lax117284Proofs.SourceInjectivity.twoSat_encode_inj hg.choose_spec
  rw [this]

theorem reduceR_rej (w : Word) (h : ¬ ∃ φ : SF, Lax117284.TwoSatisfiability.encodeFormula φ = w) :
    reduceR w = rejW := by
  unfold reduceR
  rw [dif_neg h]

/-- **The reduction is correct.** -/
theorem reduceR_correct (w : Word) :
    w ∈ Lax117284.TwoSatisfiability.TwoSat ↔ reduceR w ∈ TwoSAT := by
  by_cases h : ∃ φ : SF, Lax117284.TwoSatisfiability.encodeFormula φ = w
  · obtain ⟨φ, rfl⟩ := h
    rw [reduceR_encode, encodeCNF_mem_iff]
    constructor
    · rintro ⟨φ', hφ', hs⟩
      have e := Lax117284Proofs.SourceInjectivity.twoSat_encode_inj hφ'
      subst e
      exact ⟨isTwoCNF_toCNF _, (satisfiable_iff _).1 hs⟩
    · rintro ⟨-, hs⟩
      exact ⟨φ, rfl, (satisfiable_iff φ).2 hs⟩
  · rw [reduceR_rej w h]
    constructor
    · rintro ⟨φ, hφ, -⟩
      exact absurd ⟨φ, hφ⟩ h
    · intro hm
      exact absurd hm rejW_notMem

end Lax117284Proofs.TwoSatRename
