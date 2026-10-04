import Lax117284Proofs.Machine.TokProg
import Lax117284Proofs.Machine.Lists
import Lax117284Proofs.Theorem7Slots
import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.SourceInjectivity
import Lax117284.Theorem7

/-! ### `Lax117284Proofs.Machine.SatFormat` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.SatSem` -/

section
/-!
The reduction of Theorem 7 on the numbers of a stream: the check that the stream is a formula with
no more variables than positions, in which every literal occurs at most twice, and the word of the
instance written cell by cell, the due date of each cell being a function of the numbers.
-/

namespace Lax117284Proofs.Machine.SatSem

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.SatFormat
open Lax117284.BoundedSat Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.InstSem (instToks encodeInstance_eq)
open Lax117284.Scheduling

/-! ### Pairs of numbers, read back -/

section Pairs

variable (f g : ℕ → ℕ)

lemma pairs_length (N : ℕ) : ((List.range N).flatMap fun o => [f o, g o]).length = 2 * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp; ring

lemma pairs_getD (N o : ℕ) (h : o < N) :
    ((List.range N).flatMap fun o => [f o, g o]).getD (2 * o) 0 = f o ∧
    ((List.range N).flatMap fun o => [f o, g o]).getD (2 * o + 1) 0 = g o := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hN : o < N
    · obtain ⟨h1, h2⟩ := ih hN
      have hl := pairs_length f g N
      refine ⟨?_, ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h2
    · have hoN : o = N := by omega
      subst hoN
      have hl := pairs_length f g o
      refine ⟨?_, ?_⟩
      · rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [hl]
      · rw [List.getD_append_right _ _ _ _ (by omega)]
        simp [hl]

end Pairs

/-! ### The numbers of a formula -/

/-- The numbers of a formula: the three counts, and the variable and the sign, `0` or `1`, of
every position. -/
def valsOf (φ : Formula) : List ℕ :=
  [φ.vars, φ.twoClauses, φ.threeClauses] ++ (List.range (slots φ)).flatMap fun o =>
    [(litOfSlot φ o).1, if (litOfSlot φ o).2 then 1 else 0]

section Vals

variable (φ : Formula)

lemma valsOf_length : (valsOf φ).length = 3 + 2 * slots φ := by
  unfold valsOf
  rw [List.length_append, pairs_length (fun o => (litOfSlot φ o).1)
    (fun o => if (litOfSlot φ o).2 then 1 else 0)]
  simp

lemma valsOf_zero : (valsOf φ).getD 0 0 = φ.vars := by simp [valsOf]
lemma valsOf_one : (valsOf φ).getD 1 0 = φ.twoClauses := by simp [valsOf]
lemma valsOf_two : (valsOf φ).getD 2 0 = φ.threeClauses := by simp [valsOf]

lemma valsOf_slots : SlotsN (valsOf φ) = slots φ := by
  unfold SlotsN; rw [valsOf_one, valsOf_two]; rfl

lemma valsOf_var {o : ℕ} (h : o < slots φ) : (valsOf φ).getD (3 + 2 * o) 0 = (litOfSlot φ o).1 := by
  unfold valsOf
  have := (pairs_getD (fun o => (litOfSlot φ o).1)
    (fun o => if (litOfSlot φ o).2 then 1 else 0) (slots φ) o h).1
  rw [List.getD_append_right _ _ _ _ (by simp), show (3 + 2 * o) - [φ.vars, φ.twoClauses,
    φ.threeClauses].length = 2 * o by simp]
  exact this

lemma valsOf_sign {o : ℕ} (h : o < slots φ) :
    (valsOf φ).getD (4 + 2 * o) 0 = if (litOfSlot φ o).2 then 1 else 0 := by
  unfold valsOf
  have := (pairs_getD (fun o => (litOfSlot φ o).1)
    (fun o => if (litOfSlot φ o).2 then 1 else 0) (slots φ) o h).2
  have e : (4 + 2 * o) - [φ.vars, φ.twoClauses, φ.threeClauses].length = 2 * o + 1 := by
    simp; omega
  rw [List.getD_append_right _ _ _ _ (by simp; omega), e]
  exact this

theorem shape_valsOf : ShapeF (valsOf φ) := by
  refine ⟨by rw [valsOf_length]; omega, by rw [valsOf_length, valsOf_slots], fun o ho => ?_⟩
  rw [valsOf_slots] at ho
  rw [valsOf_sign φ ho]
  split <;> omega

end Vals

/-! ### What the check asks -/

/-- Which of the occurrences of its own literal a position is, read off the numbers: the number
of earlier positions with the same variable and sign. -/
def rankN (ns : List ℕ) (o : ℕ) : ℕ :=
  (List.range o).countP fun o' =>
    decide (ns.getD (3 + 2 * o') 0 = ns.getD (3 + 2 * o) 0 ∧
      ns.getD (4 + 2 * o') 0 = ns.getD (4 + 2 * o) 0)

/-- The position `o` names a variable of the formula and is the first or the second occurrence
of its literal. -/
def PassS (ns : List ℕ) (o : ℕ) : Prop :=
  ns.getD (3 + 2 * o) 0 < ns.getD 0 0 ∧ rankN ns o ≤ 1

instance (ns : List ℕ) : DecidablePred (PassS ns) := fun o => by unfold PassS; infer_instance

/-- **What the check asks of a stream**: no more variables than positions, and every position
passes. -/
def CondN (ns : List ℕ) : Prop :=
  ns.getD 0 0 ≤ SlotsN ns ∧ ∀ o < SlotsN ns, PassS ns o

section Check

variable (φ : Formula)

lemma rank_valsOf {o : ℕ} (h : o < slots φ) : rankN (valsOf φ) o = slotRank φ o := by
  unfold rankN slotRank
  refine List.countP_congr fun o' ho' => ?_
  have h' : o' < slots φ := by have := List.mem_range.mp ho'; omega
  rw [valsOf_var φ h', valsOf_var φ h, valsOf_sign φ h', valsOf_sign φ h]
  obtain ⟨v', s'⟩ := litOfSlot φ o'
  obtain ⟨v, s⟩ := litOfSlot φ o
  simp only [decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq]
  cases s' <;> cases s <;> simp

lemma var_lt (o : ℕ) (h : o < slots φ) : (litOfSlot φ o).1 < φ.vars := by
  obtain ⟨occ, rfl⟩ := Lax117284Proofs.Theorem7Slots.exists_slotNum φ h
  rw [Lax117284Proofs.Theorem7Slots.litOfSlot_slotNum]
  exact (φ.litAt occ).1.isLt

theorem condN_valsOf (hv : φ.vars ≤ slots φ) : CondN (valsOf φ) := by
  refine ⟨by rw [valsOf_zero, valsOf_slots]; exact hv, fun o ho => ?_⟩
  rw [valsOf_slots] at ho
  refine ⟨by rw [valsOf_var φ ho, valsOf_zero]; exact var_lt φ o ho, ?_⟩
  rw [rank_valsOf φ ho]
  obtain ⟨occ, hocc⟩ := Lax117284Proofs.Theorem7Slots.exists_slotNum φ ho
  rw [← hocc]
  exact Lax117284Proofs.Theorem7Slots.slotRank_le_one φ occ

end Check

/-! ### The image -/

/-- The number of clients of the constructed instance. -/
def clientsN (ns : List ℕ) : ℕ := 3 + 2 * ns.getD 0 0 + SlotsN ns

/-- The due date of client `c` on day `i`, read off the numbers. -/
def dueN (ns : List ℕ) (i c : ℕ) : ℕ :=
  if c < 3 then 2
  else if c < 3 + 2 * ns.getD 0 0 then
    (if i = 0 then 2 * ((c - 3) / 2) + 5
     else if i = 1 then 2
     else if (c - 3) % 2 = 0 then 10 * ((c - 3) / 2) + 6 else 10 * ((c - 3) / 2) + 11)
  else
    if i = 2 then
      (if ns.getD (4 + 2 * (c - 3 - 2 * ns.getD 0 0)) 0 ≠ 0 then
        10 * ns.getD (3 + 2 * (c - 3 - 2 * ns.getD 0 0)) 0 + 5 +
          2 * rankN ns (c - 3 - 2 * ns.getD 0 0)
      else 10 * ns.getD (3 + 2 * (c - 3 - 2 * ns.getD 0 0)) 0 + 10 +
          2 * rankN ns (c - 3 - 2 * ns.getD 0 0))
    else if c - 3 - 2 * ns.getD 0 0 < 2 * ns.getD 1 0 then
      (if i = 0 then 2 * ns.getD 0 0 + 2 * ((c - 3 - 2 * ns.getD 0 0) / 2) + 7 else 2)
    else
      (if i = 0 then
        2 * ns.getD 0 0 + 2 * ns.getD 1 0 + 2 * ((c - 3 - 2 * ns.getD 0 0 - 2 * ns.getD 1 0) / 3) + 9
      else 3 * ((c - 3 - 2 * ns.getD 0 0 - 2 * ns.getD 1 0) / 3) + 6)

/-- The numbers of the image: the counts, the processing time and the due date of every job day
by day, and the parameter `1`. -/
def outNums (ns : List ℕ) : List ℕ :=
  [clientsN ns, 3] ++ (List.range 3).flatMap (fun i => (List.range (clientsN ns)).flatMap fun c =>
    [2, dueN ns i c]) ++ [1]

section Image

variable (φ : Formula)

theorem due_valsOf (i c : ℕ) (hc : c < Lax117284.Theorem7.clients φ) :
    dueN (valsOf φ) i c = Lax117284.Theorem7.due φ i c := by
  unfold dueN Lax117284.Theorem7.due
  rw [valsOf_zero, valsOf_one]
  by_cases h1 : c < 3
  · simp [h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : c < 3 + 2 * φ.vars
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      have ho : c - 3 - 2 * φ.vars < slots φ := by
        unfold Lax117284.Theorem7.clients at hc; omega
      dsimp only
      rw [valsOf_var φ ho, valsOf_sign φ ho, rank_valsOf φ ho]
      by_cases hs : (litOfSlot φ (c - 3 - 2 * φ.vars)).2 = true
      · simp only [hs, if_true]
        split_ifs <;> first | rfl | omega
      · have hs' : (litOfSlot φ (c - 3 - 2 * φ.vars)).2 = false := by simpa using hs
        simp only [hs', Bool.false_eq_true, if_false]
        split_ifs <;> first | rfl | omega

theorem clientsN_valsOf : clientsN (valsOf φ) = Lax117284.Theorem7.clients φ := by
  unfold clientsN Lax117284.Theorem7.clients
  rw [valsOf_zero, valsOf_slots]

theorem out_valsOf :
    numCode (outNums (valsOf φ)) = encodeUniform (Lax117284.Theorem7.inst φ) 1 := by
  have hcl : (Lax117284.Theorem7.inst φ).clients = clientsN (valsOf φ) := by
    rw [clientsN_valsOf]; rfl
  have hC : 0 < clientsN (valsOf φ) := by unfold clientsN; omega
  have hpt : ∀ a b, a < 3 → b < clientsN (valsOf φ) →
      (Lax117284.Theorem7.inst φ).pAt a b = 2 ∧
        (Lax117284.Theorem7.inst φ).dAt a b = dueN (valsOf φ) a b := by
    intro a b ha hb
    have ha' : a < (Lax117284.Theorem7.inst φ).days := ha
    have hb' : b < (Lax117284.Theorem7.inst φ).clients := by rw [hcl]; exact hb
    have h1 := Instance.pAt_coe (Lax117284.Theorem7.inst φ) ⟨a, ha'⟩ ⟨b, hb'⟩
    have h2 := Instance.dAt_coe (Lax117284.Theorem7.inst φ) ⟨a, ha'⟩ ⟨b, hb'⟩
    simp only [Fin.val_mk] at h1 h2
    rw [h1, h2]
    exact ⟨rfl, (due_valsOf φ a b (by rw [← clientsN_valsOf]; exact hb)).symm⟩
  have hI : instToks (Lax117284.Theorem7.inst φ) = [clientsN (valsOf φ), 3] ++
      (List.range 3).flatMap (fun i => (List.range (clientsN (valsOf φ))).flatMap fun c =>
        [2, dueN (valsOf φ) i c]) := by
    unfold instToks
    have hd : (Lax117284.Theorem7.inst φ).days = 3 := rfl
    rw [hd, hcl]
    congr 1
    rw [← flatMap_rows (fun t => [(Lax117284.Theorem7.inst φ).pAt (t / clientsN (valsOf φ))
      (t % clientsN (valsOf φ)), (Lax117284.Theorem7.inst φ).dAt (t / clientsN (valsOf φ))
      (t % clientsN (valsOf φ))]) (clientsN (valsOf φ)) 3]
    refine List.flatMap_congr fun a ha => List.flatMap_congr fun b hb => ?_
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    have e1 : (a * clientsN (valsOf φ) + b) / clientsN (valsOf φ) = a := by
      rw [Nat.mul_comm, Nat.mul_add_div hC, Nat.div_eq_of_lt hb', Nat.add_zero]
    have e2 : (a * clientsN (valsOf φ) + b) % clientsN (valsOf φ) = b := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
    rw [e1, e2, (hpt a b ha' hb').1, (hpt a b ha' hb').2]
  unfold encodeUniform
  rw [encodeInstance_eq, hI]
  unfold outNums
  rw [numCode_append]
  simp [numCode]

end Image

/-! ### The word of a formula -/

lemma flatMap_two {α : Type} (g : ℕ → List α) :
    ∀ N, (List.range (2 * N)).flatMap g =
      (List.range N).flatMap (fun o => g (2 * o) ++ g (2 * o + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.flatMap_append, List.flatMap_append, flatMap_two g N, List.range_succ (n := N),
      List.flatMap_append]
    simp [List.append_assoc]

lemma flatMap_three {α : Type} (g : ℕ → List α) :
    ∀ N, (List.range (3 * N)).flatMap g =
      (List.range N).flatMap (fun o => g (3 * o) ++ g (3 * o + 1) ++ g (3 * o + 2))
  | 0 => by simp
  | N + 1 => by
    rw [show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.range_succ, List.flatMap_append, List.flatMap_append, List.flatMap_append,
      flatMap_three g N, List.range_succ (n := N), List.flatMap_append]
    simp [List.append_assoc]

section Word

variable (φ : Formula)

/-- The word of the position `o`: its variable and its sign. -/
def posWord (o : ℕ) : Word := encodeNat (litOfSlot φ o).1 ++ [(litOfSlot φ o).2]

lemma lits_eq :
    ((List.finRange φ.twoClauses).flatMap fun c => (List.finRange 2).flatMap fun α =>
        encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2]) ++
      ((List.finRange φ.threeClauses).flatMap fun c => (List.finRange 3).flatMap fun α =>
        encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2]) =
    (List.range (slots φ)).flatMap (posWord φ) := by
  have hH2 : ∀ (c : Fin φ.twoClauses) (α : Fin 2), posWord φ (2 * (c : ℕ) + (α : ℕ)) =
      encodeNat (φ.aLit c α).1 ++ [(φ.aLit c α).2] := by
    intro c α
    have := Lax117284Proofs.Theorem7Slots.litOfSlot_slotNum φ (Sum.inl (c, α))
    have e : Lax117284Proofs.Theorem7Slots.slotNum φ (Sum.inl (c, α)) = 2 * (c : ℕ) + (α : ℕ) := rfl
    rw [e] at this
    unfold posWord
    rw [this]; rfl
  have hH3 : ∀ (c : Fin φ.threeClauses) (α : Fin 3),
      posWord φ (2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ)) =
      encodeNat (φ.bLit c α).1 ++ [(φ.bLit c α).2] := by
    intro c α
    have := Lax117284Proofs.Theorem7Slots.litOfSlot_slotNum φ (Sum.inr (c, α))
    have e : Lax117284Proofs.Theorem7Slots.slotNum φ (Sum.inr (c, α)) =
        2 * φ.twoClauses + 3 * (c : ℕ) + (α : ℕ) := rfl
    rw [e] at this
    unfold posWord
    rw [this]; rfl
  unfold slots
  rw [List.range_add, List.flatMap_append, flatMap_two, List.flatMap_map, flatMap_three,
    flatMap_finRange, flatMap_finRange]
  congr 1
  · refine List.flatMap_congr fun c hc => ?_
    have hc' := List.mem_range.mp hc
    rw [dif_pos hc']
    have e2 : (List.finRange 2).flatMap (fun α => encodeNat (φ.aLit ⟨c, hc'⟩ α).1 ++
        [(φ.aLit ⟨c, hc'⟩ α).2]) = (encodeNat (φ.aLit ⟨c, hc'⟩ 0).1 ++ [(φ.aLit ⟨c, hc'⟩ 0).2]) ++
          (encodeNat (φ.aLit ⟨c, hc'⟩ 1).1 ++ [(φ.aLit ⟨c, hc'⟩ 1).2]) := by
      simp [List.finRange_succ]
    rw [e2, ← hH2 ⟨c, hc'⟩ 0, ← hH2 ⟨c, hc'⟩ 1]
    rfl
  · refine List.flatMap_congr fun c hc => ?_
    have hc' := List.mem_range.mp hc
    rw [dif_pos hc']
    have e3 : (List.finRange 3).flatMap (fun α => encodeNat (φ.bLit ⟨c, hc'⟩ α).1 ++
        [(φ.bLit ⟨c, hc'⟩ α).2]) = (encodeNat (φ.bLit ⟨c, hc'⟩ 0).1 ++ [(φ.bLit ⟨c, hc'⟩ 0).2]) ++
          (encodeNat (φ.bLit ⟨c, hc'⟩ 1).1 ++ [(φ.bLit ⟨c, hc'⟩ 1).2]) ++
          (encodeNat (φ.bLit ⟨c, hc'⟩ 2).1 ++ [(φ.bLit ⟨c, hc'⟩ 2).2]) := by
      simp [List.finRange_succ]
    rw [e3, ← hH3 ⟨c, hc'⟩ 0, ← hH3 ⟨c, hc'⟩ 1, ← hH3 ⟨c, hc'⟩ 2]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.add_zero, List.append_assoc]
    rfl

theorem code_toksF : code (toksF (valsOf φ)) = encodeFormula φ := by
  have hL : (valsOf φ).length = 3 + 2 * slots φ := valsOf_length φ
  have hpos : ∀ o, o < slots φ → Tok.code (tokAt (valsOf φ) (3 + (2 * o))) =
      encodeNat (litOfSlot φ o).1 ∧ Tok.code (tokAt (valsOf φ) (3 + (2 * o + 1))) =
      [(litOfSlot φ o).2] := by
    intro o ho
    refine ⟨?_, ?_⟩
    · unfold tokAt
      rw [if_pos (Or.inr (by omega))]
      simp only [Lax117284Proofs.Machine.TokProg.Tok.val, TokModel.Tok.code]
      rw [show 3 + 2 * o = 3 + 2 * o from rfl, valsOf_var φ ho]
    · unfold tokAt
      rw [if_neg (by omega), show 3 + (2 * o + 1) = 4 + 2 * o by ring, valsOf_sign φ ho]
      simp only [TokModel.Tok.code]
      split <;> simp_all
  unfold toksF code encodeFormula
  rw [hL, List.range_add, List.map_append, List.flatMap_append, List.map_map, List.flatMap_map,
    List.append_assoc, lits_eq φ]
  rw [List.flatMap_map]
  have h3 : (List.range 3).flatMap (fun a => (tokAt (valsOf φ) a).code) =
      encodeNat φ.vars ++ encodeNat φ.twoClauses ++ encodeNat φ.threeClauses := by
    simp [List.range_succ, tokAt, Lax117284Proofs.Machine.TokModel.Tok.code, valsOf]
  rw [h3, List.append_assoc, ← List.append_assoc]
  congr 1
  rw [flatMap_two (fun a => ((tokAt (valsOf φ) ∘ fun x => 3 + x) a).code)]
  refine List.flatMap_congr fun o ho => ?_
  have h := hpos o (List.mem_range.mp ho)
  unfold posWord
  simp only [Function.comp]
  rw [h.1, h.2]

end Word

/-! ### A formula from a stream that passes the check -/

section Build

variable (ns : List ℕ)

lemma sign_eq_iff (hs : ShapeF ns) {o o' : ℕ} (ho : o < SlotsN ns) (ho' : o' < SlotsN ns) :
    ns.getD (4 + 2 * o') 0 = ns.getD (4 + 2 * o) 0 ↔
      decide (ns.getD (4 + 2 * o') 0 ≠ 0) = decide (ns.getD (4 + 2 * o) 0 ≠ 0) := by
  have h1 := hs.2.2 o ho
  have h2 := hs.2.2 o' ho'
  generalize ns.getD (4 + 2 * o') 0 = x at *
  generalize ns.getD (4 + 2 * o) 0 = y at *
  constructor
  · intro h; rw [h]
  · intro h
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all <;> omega

/-- **Every literal has at most two of the first `N` positions**, if every position is the
first or the second of its literal. -/
lemma count_le_two (hs : ShapeF ns) (hr : ∀ o < SlotsN ns, rankN ns o ≤ 1) (v : ℕ) (b : Bool) :
    ∀ N, N ≤ SlotsN ns →
      (List.range N).countP (fun o => decide (ns.getD (3 + 2 * o) 0 = v ∧
        decide (ns.getD (4 + 2 * o) 0 ≠ 0) = b)) ≤ 2
  | 0, _ => by simp
  | N + 1, hN => by
    have ih := count_le_two hs hr v b N (by omega)
    rw [List.range_succ, List.countP_append]
    by_cases hP : ns.getD (3 + 2 * N) 0 = v ∧ decide (ns.getD (4 + 2 * N) 0 ≠ 0) = b
    · have hrk := hr N (by omega)
      have hcong : (List.range N).countP (fun o => decide (ns.getD (3 + 2 * o) 0 = v ∧
          decide (ns.getD (4 + 2 * o) 0 ≠ 0) = b)) = rankN ns N := by
        unfold rankN
        refine List.countP_congr fun o ho => ?_
        have ho' : o < N := List.mem_range.mp ho
        simp only [decide_eq_true_eq]
        rw [sign_eq_iff ns hs (by omega) (by omega)]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by rw [h1, hP.1], by rw [h2, hP.2]⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by rw [h1, hP.1], by rw [h2, hP.2]⟩
      have : [N].countP (fun o => decide (ns.getD (3 + 2 * o) 0 = v ∧
          decide (ns.getD (4 + 2 * o) 0 ≠ 0) = b)) = 1 := by
        rw [List.countP_cons_of_pos (by simp only [decide_eq_true_eq]; exact hP)]; rfl
      omega
    · have : [N].countP (fun o => decide (ns.getD (3 + 2 * o) 0 = v ∧
          decide (ns.getD (4 + 2 * o) 0 ≠ 0) = b)) = 0 := by
        rw [List.countP_cons_of_neg (by simp only [decide_eq_true_eq]; exact hP)]; rfl
      omega

end Build

lemma card_filter_range (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((Finset.range N).filter P).card = (List.range N).countP (fun o => decide (P o)) := by
  rw [List.countP_eq_length_filter]
  rw [← Multiset.coe_card, ← Multiset.filter_coe (p := P)]
  simp [Finset.card, Finset.filter, Finset.range, Multiset.range]

section Build2

variable (ns : List ℕ)

lemma pos_lt (hc : CondN ns) {o : ℕ} (ho : o < SlotsN ns) : ns.getD (3 + 2 * o) 0 < ns.getD 0 0 :=
  (hc.2 o ho).1

/-- The literal of the position `2 c + α` of a clause of two literals. -/
def aLitOf (hc : CondN ns) (c : Fin (ns.getD 1 0)) (α : Fin 2) : Fin (ns.getD 0 0) × Bool :=
  (⟨ns.getD (3 + 2 * (2 * (c : ℕ) + (α : ℕ))) 0, pos_lt ns hc (by
      have := c.isLt; have := α.isLt; unfold SlotsN; omega)⟩,
    decide (ns.getD (4 + 2 * (2 * (c : ℕ) + (α : ℕ))) 0 ≠ 0))

/-- The literal of the position `2 a + 3 c + α` of a clause of three literals. -/
def bLitOf (hc : CondN ns) (c : Fin (ns.getD 2 0)) (α : Fin 3) : Fin (ns.getD 0 0) × Bool :=
  (⟨ns.getD (3 + 2 * (2 * ns.getD 1 0 + 3 * (c : ℕ) + (α : ℕ))) 0, pos_lt ns hc (by
      have := c.isLt; have := α.isLt; unfold SlotsN; omega)⟩,
    decide (ns.getD (4 + 2 * (2 * ns.getD 1 0 + 3 * (c : ℕ) + (α : ℕ))) 0 ≠ 0))

theorem occ_aux (hc : CondN ns) (hs : ShapeF ns) (l : Fin (ns.getD 0 0) × Bool) :
    (Finset.univ.filter fun o : (Fin (ns.getD 1 0) × Fin 2) ⊕ (Fin (ns.getD 2 0) × Fin 3) =>
      Sum.elim (fun q => aLitOf ns hc q.1 q.2) (fun q => bLitOf ns hc q.1 q.2) o = l).card
        ≤ 2 := by
  classical
  let num : (Fin (ns.getD 1 0) × Fin 2) ⊕ (Fin (ns.getD 2 0) × Fin 3) → ℕ :=
    Sum.elim (fun q => 2 * (q.1 : ℕ) + (q.2 : ℕ))
      (fun q => 2 * ns.getD 1 0 + 3 * (q.1 : ℕ) + (q.2 : ℕ))
  have hnum_lt : ∀ o, num o < SlotsN ns := by
    rintro (⟨c, α⟩ | ⟨c, α⟩)
    · have := c.isLt; have := α.isLt; simp only [num, Sum.elim_inl]; unfold SlotsN; omega
    · have := c.isLt; have := α.isLt; simp only [num, Sum.elim_inr]; unfold SlotsN; omega
  have hnum_inj : Function.Injective num := by
    rintro (⟨c, α⟩ | ⟨c, α⟩) (⟨c', α'⟩ | ⟨c', α'⟩) h
    · have := α.isLt; have := α'.isLt
      simp only [num, Sum.elim_inl] at h
      have hc' : (c : ℕ) = c' := by omega
      have ha' : (α : ℕ) = α' := by omega
      exact congrArg Sum.inl (Prod.ext (Fin.ext hc') (Fin.ext ha'))
    · have := c.isLt; have := α.isLt; have := α'.isLt
      simp only [num, Sum.elim_inl, Sum.elim_inr] at h; omega
    · have := c'.isLt; have := α.isLt; have := α'.isLt
      simp only [num, Sum.elim_inl, Sum.elim_inr] at h; omega
    · have := α.isLt; have := α'.isLt
      simp only [num, Sum.elim_inr] at h
      have hc' : (c : ℕ) = c' := by omega
      have ha' : (α : ℕ) = α' := by omega
      exact congrArg Sum.inr (Prod.ext (Fin.ext hc') (Fin.ext ha'))
  have hT := count_le_two ns hs (fun o ho => (hc.2 o ho).2) l.1 l.2 (SlotsN ns) le_rfl
  rw [← card_filter_range (fun o => ns.getD (3 + 2 * o) 0 = (l.1 : ℕ) ∧
    decide (ns.getD (4 + 2 * o) 0 ≠ 0) = l.2)] at hT
  refine le_trans (Finset.card_le_card_of_injOn num (fun o ho => ?_) (fun a _ b _ h => hnum_inj h)) hT
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ho
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
  refine ⟨hnum_lt o, ?_⟩
  rcases o with ⟨c, α⟩ | ⟨c, α⟩
  · simp only [Sum.elim_inl, aLitOf] at ho
    have h1 := congrArg (fun x => (x.1 : ℕ)) ho
    have h2 := congrArg Prod.snd ho
    simp only [num, Sum.elim_inl] at h1 h2 ⊢
    exact ⟨h1, h2⟩
  · simp only [Sum.elim_inr, bLitOf] at ho
    have h1 := congrArg (fun x => (x.1 : ℕ)) ho
    have h2 := congrArg Prod.snd ho
    simp only [num, Sum.elim_inr] at h1 h2 ⊢
    exact ⟨h1, h2⟩

/-- **The formula of a stream that passes the check.** -/
def formulaOf (hc : CondN ns) (hs : ShapeF ns) : Formula where
  vars := ns.getD 0 0
  twoClauses := ns.getD 1 0
  threeClauses := ns.getD 2 0
  aLit := aLitOf ns hc
  bLit := bLitOf ns hc
  occ_le_two := occ_aux ns hc hs

theorem litOfSlot_formulaOf (hc : CondN ns) (hs : ShapeF ns) {o : ℕ} (ho : o < SlotsN ns) :
    litOfSlot (formulaOf ns hc hs) o =
      (ns.getD (3 + 2 * o) 0, decide (ns.getD (4 + 2 * o) 0 ≠ 0)) := by
  have htw : (formulaOf ns hc hs).twoClauses = ns.getD 1 0 := rfl
  have hth : (formulaOf ns hc hs).threeClauses = ns.getD 2 0 := rfl
  have hSN : SlotsN ns = 2 * ns.getD 1 0 + 3 * ns.getD 2 0 := rfl
  unfold litOfSlot
  by_cases h1 : o < 2 * (formulaOf ns hc hs).twoClauses
  · have h2 : o / 2 < (formulaOf ns hc hs).twoClauses := by omega
    rw [if_pos h1, dif_pos h2]
    show (ns.getD (3 + 2 * (2 * (o / 2) + o % 2)) 0,
      decide (ns.getD (4 + 2 * (2 * (o / 2) + o % 2)) 0 ≠ 0)) = _
    rw [Nat.div_add_mod]
  · have h2 : (o - 2 * (formulaOf ns hc hs).twoClauses) / 3 <
        (formulaOf ns hc hs).threeClauses := by omega
    rw [if_neg h1, dif_pos h2]
    show (ns.getD (3 + 2 * (2 * ns.getD 1 0 + 3 * ((o - 2 * (formulaOf ns hc hs).twoClauses) / 3)
        + (o - 2 * (formulaOf ns hc hs).twoClauses) % 3)) 0,
      decide (ns.getD (4 + 2 * (2 * ns.getD 1 0 + 3 * ((o - 2 * (formulaOf ns hc hs).twoClauses) / 3)
        + (o - 2 * (formulaOf ns hc hs).twoClauses) % 3)) 0 ≠ 0)) = _
    have : 2 * ns.getD 1 0 + 3 * ((o - 2 * (formulaOf ns hc hs).twoClauses) / 3)
        + (o - 2 * (formulaOf ns hc hs).twoClauses) % 3 = o := by omega
    rw [this]

theorem valsOf_formulaOf (hc : CondN ns) (hs : ShapeF ns) : valsOf (formulaOf ns hc hs) = ns := by
  obtain ⟨h3, hl, hsg⟩ := hs
  have hS : slots (formulaOf ns hc ⟨h3, hl, hsg⟩) = SlotsN ns := rfl
  obtain ⟨a, b, c, rest, rfl⟩ : ∃ a b c rest, ns = a :: b :: c :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp at h3
    exact ⟨a, b, c, rest, rfl⟩
  unfold valsOf
  rw [hS]
  have hpairs : (List.range (SlotsN (a :: b :: c :: rest))).flatMap (fun o =>
      [(litOfSlot (formulaOf (a :: b :: c :: rest) hc ⟨h3, hl, hsg⟩) o).1,
        if (litOfSlot (formulaOf (a :: b :: c :: rest) hc ⟨h3, hl, hsg⟩) o).2 then 1 else 0]) =
      rest := by
    have := flatMap_pairs (a :: b :: c :: rest) 3 (SlotsN (a :: b :: c :: rest)) (by omega)
    simp only [List.drop_succ_cons, List.drop_zero] at this
    have hlen : 2 * SlotsN (a :: b :: c :: rest) = rest.length := by
      simp only [List.length_cons] at hl; omega
    rw [hlen, List.take_length] at this
    refine Eq.trans (List.flatMap_congr fun o ho => ?_) this
    have ho' := List.mem_range.mp ho
    rw [litOfSlot_formulaOf (a :: b :: c :: rest) hc ⟨h3, hl, hsg⟩ ho']
    have hsig := hsg o ho'
    simp only []
    rw [show 3 + 2 * o + 1 = 4 + 2 * o by omega]
    congr 1
    congr 1
    generalize (a :: b :: c :: rest).getD (4 + 2 * o) 0 = x at *
    by_cases hx : x = 0 <;> simp_all
    omega
  rw [hpairs]
  rfl

end Build2

/-! ### The reduction, on streams -/

/-- **The gate of the reduction, on streams.** -/
theorem sat_gate (w : Word) :
    (∃ φ : Formula, encodeFormula φ = w ∧ φ.vars ≤ slots φ) ↔
      ∃ ts : List Tok, w = code ts ∧ Conforms EF ts ∧ CondN (ts.map Lax117284Proofs.Machine.TokProg.Tok.val) := by
  constructor
  · rintro ⟨φ, rfl, hv⟩
    refine ⟨toksF (valsOf φ), (code_toksF φ).symm, conforms_of_shape (shape_valsOf φ), ?_⟩
    rw [vals_toksF (shape_valsOf φ)]
    exact condN_valsOf φ hv
  · rintro ⟨ts, rfl, hconf, hcond⟩
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    refine ⟨formulaOf _ hcond hshape, ?_, hcond.1⟩
    have := code_toksF (formulaOf _ hcond hshape)
    rw [valsOf_formulaOf] at this
    rw [← this, ← hts]

/-- **The reduction writes the numbers of the constructed instance.** -/
theorem t7_eq (ts : List Tok) (hconf : Conforms EF ts)
    (hcond : CondN (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    Lax117284.Theorem7.reduce (code ts) =
      numCode (outNums (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) := by
  classical
  obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
  have hg := (sat_gate (code ts)).2 ⟨ts, rfl, hconf, hcond⟩
  unfold Lax117284.Theorem7.reduce
  rw [dif_pos hg]
  have hφ : formulaOf _ hcond hshape = hg.choose := by
    apply Lax117284Proofs.SourceInjectivity.boundedSat_encode_inj
    have h1 := code_toksF (formulaOf _ hcond hshape)
    rw [valsOf_formulaOf] at h1
    rw [hg.choose_spec.1, ← h1, ← hts]
  rw [← hφ, ← out_valsOf, valsOf_formulaOf]

/-- **A word that is not the code of an admissible stream is rejected.** -/
theorem t7_rej (w : Word)
    (h : ¬ ∃ ts : List Tok, w = code ts ∧ Conforms EF ts ∧
      CondN (ts.map Lax117284Proofs.Machine.TokProg.Tok.val)) :
    Lax117284.Theorem7.reduce w = rejected := by
  classical
  unfold Lax117284.Theorem7.reduce
  rw [dif_neg (fun hg => h ((sat_gate w).1 hg))]

end Lax117284Proofs.Machine.SatSem

end
