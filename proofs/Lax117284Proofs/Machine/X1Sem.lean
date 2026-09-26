import Lax117284Proofs.Machine.T9Sem
import Lax117284Proofs.X1Word

/-!
The reduction of the three tractable parameters on the numbers of a stream: the word of the
formula of the case an instance is in, clause by clause.
-/

namespace Lax117284Proofs.Machine.X1Sem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime Lax117284.TwoSatisfiability
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.BlockSem Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.X1Word

/-- The streams that are mapped to a formula. -/
def condX (ns : List ℕ) : Prop :=
  Valid ns ∧ (paramOf ns = 0 ∨ paramOf ns + 1 = ns.getD 1 0 ∨ paramOf ns = ns.getD 1 0)

/-- The word of the formula for the parameter equal to the number of days. -/
def outU (arr : List ℕ) (n m : ℕ) : Word :=
  encodeNat (m * n + 1) ++ encodeNat (m * n * n + m * n) ++
    ((List.range (m * n * n)).flatMap (clW arr n m) ++
      (List.range (m * n)).flatMap fun v => encodeNat v ++ [true] ++ encodeNat v ++ [true])

/-- The word of the formula of the case a stream is in. -/
def outX (ns : List ℕ) : Word :=
  if paramOf ns + 1 = ns.getD 1 0 then outT9 ns (ns.getD 0 0) (ns.getD 1 0)
  else if paramOf ns = ns.getD 1 0 then outU ns (ns.getD 0 0) (ns.getD 1 0)
  else encodeNat 1 ++ encodeNat 0

/-- **The numbers of the instances are the valid streams.** -/
theorem uniform_iff' (w : Word) :
    (∃ (I : Instance) (k : ℕ), encodeUniform I k = w) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ Valid ns := by
  constructor
  · rintro ⟨I, k, hw⟩
    refine ⟨instToks I ++ [k], ?_, ?_, ?_⟩
    · rw [← hw, encodeUniform, encodeInstance_eq, numCode_append]
      simp
    · have hl := instToks_length I
      have h0 : (instToks I ++ [k]).getD 0 0 = I.clients := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).1
      have h1 : (instToks I ++ [k]).getD 1 0 = I.days := by
        rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).2
      refine ⟨by simp; omega, ?_⟩
      rw [h0, h1]
      simp only [List.length_append, List.length_singleton, eU, hl]
    · intro t ht
      have h0 : (instToks I ++ [k]).getD 0 0 = I.clients := by
        rw [List.getD_append _ _ _ _ (by have := instToks_length I; omega)]
        exact (instToks_getD_head I).1
      have h1 : (instToks I ++ [k]).getD 1 0 = I.days := by
        rw [List.getD_append _ _ _ _ (by have := instToks_length I; omega)]
        exact (instToks_getD_head I).2
      rw [h0, h1] at ht
      have ht' : t < I.days * I.clients := ht
      have hl := instToks_length I
      have hp := instToks_getD_cell I ht'
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hp.1, hp.2]
      exact ⟨I.pAt_pos _ _, I.pAt_le_dAt _ _⟩
  · rintro ⟨ns, hw, hs, hv⟩
    refine ⟨instOf ns hv, paramOf ns, ?_⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]

section Formula

variable (ns : List ℕ) (hv : Valid ns)

/-- **The word of the formula for the parameter equal to the number of days.** -/
theorem encodeFormula_eqU :
    encodeFormula (formulaU (instOf ns hv)) = outU ns (ns.getD 0 0) (ns.getD 1 0) := by
  unfold encodeFormula outU
  show encodeNat (ns.getD 1 0 * ns.getD 0 0 + 1) ++
      encodeNat (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + ns.getD 1 0 * ns.getD 0 0) ++
      (List.finRange (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 +
        ns.getD 1 0 * ns.getD 0 0)).flatMap (fun c =>
      (List.finRange 2).flatMap fun α =>
        encodeNat ((formulaU (instOf ns hv)).lit c α).1 ++
          [((formulaU (instOf ns hv)).lit c α).2]) = _
  congr 1
  refine (flatMap_finRange _ _).trans ?_
  have hrange : List.range (formulaU (instOf ns hv)).clauses =
      List.range (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) ++
        (List.range (ns.getD 1 0 * ns.getD 0 0)).map
          (fun c => ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c) := List.range_add ..
  rw [hrange, List.flatMap_append, List.flatMap_map]
  congr 1
  · refine List.flatMap_congr fun c hc => ?_
    have hc' := List.mem_range.mp hc
    have hc2 : c < (formulaU (instOf ns hv)).clauses := by
      show c < ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + ns.getD 1 0 * ns.getD 0 0
      omega
    rw [dif_pos hc2]
    have hl : ∀ α : Fin 2, (formulaU (instOf ns hv)).lit ⟨c, hc2⟩ α =
        Lax117284.Theorem9.clauseLit (instOf ns hv) c α := fun α => dif_pos hc'
    have hf2 : List.finRange 2 = [0, 1] := by decide
    rw [hf2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hl]
    have hct : c < ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 +
        ns.getD 0 0 * ns.getD 1 0 * ns.getD 1 0 := by omega
    obtain ⟨a0, b0⟩ := lit_val ns hv 0 hct
    obtain ⟨a1, b1⟩ := lit_val ns hv 1 hct
    show encodeNat ((Lax117284.Theorem9.clauseLit (instOf ns hv) c 0).1 : ℕ) ++
        [(Lax117284.Theorem9.clauseLit (instOf ns hv) c 0).2] ++
        (encodeNat ((Lax117284.Theorem9.clauseLit (instOf ns hv) c 1).1 : ℕ) ++
        [(Lax117284.Theorem9.clauseLit (instOf ns hv) c 1).2]) = _
    rw [a0, b0, a1, b1]
    simp [clW]
  · refine List.flatMap_congr fun c hc => ?_
    have hc' := List.mem_range.mp hc
    have hc2 : ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c <
        (formulaU (instOf ns hv)).clauses := by
      show _ < ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + ns.getD 1 0 * ns.getD 0 0
      omega
    try simp only [Function.comp_apply]
    rw [dif_pos hc2]
    have hnot : ¬ (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c <
        ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0) := by omega
    have hnot' : ¬ (ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c <
        (instOf ns hv).days * (instOf ns hv).clients * (instOf ns hv).clients) := hnot
    have hl : ∀ α : Fin 2, ((formulaU (instOf ns hv)).lit
        ⟨ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c, hc2⟩ α).1.val = c ∧
        ((formulaU (instOf ns hv)).lit
        ⟨ns.getD 1 0 * ns.getD 0 0 * ns.getD 0 0 + c, hc2⟩ α).2 = true := fun α => by
      refine ⟨?_, ?_⟩
      · unfold formulaU; dsimp only; rw [dif_neg hnot']; exact Nat.add_sub_cancel_left _ _
      · unfold formulaU; dsimp only; rw [dif_neg hnot']
    have hf2 : List.finRange 2 = [0, 1] := by decide
    rw [hf2]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [(hl 0).1, (hl 0).2, (hl 1).1, (hl 1).2]
    simp

end Formula

/-- **The gate of the reduction, on streams.** -/
theorem tX_gate (w : Word) :
    (∃ (I : Instance) (k : ℕ), encodeUniform I k = w ∧ extremeC I k) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ condX ns := by
  constructor
  · rintro ⟨I, k, hw, hk⟩
    obtain ⟨ns, hw', hs, hv⟩ := (uniform_iff' w).1 ⟨I, k, hw⟩
    refine ⟨ns, hw', hs, hv, ?_⟩
    have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
      rw [encodeUniform, encodeInstance_eq]
      conv_rhs => rw [← instToks_instOf ns hv hs]
      rw [numCode_append]
      simp [numCode]
    have := Injectivity.encodeUniform_inj (I := instOf ns hv) (I' := I) (k := paramOf ns)
      (k' := k) (hI.trans (hw'.symm.trans hw.symm))
    obtain ⟨rfl, rfl⟩ := this
    exact hk
  · rintro ⟨ns, hw, hs, hv, hk⟩
    refine ⟨instOf ns hv, paramOf ns, ?_, hk⟩
    rw [hw, encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]

/-- **The reduction writes the word of the formula of the case.** -/
theorem tX_eq (ns : List ℕ) (hv : Valid ns) (hs : Shape eU ns)
    (hk : paramOf ns = 0 ∨ paramOf ns + 1 = ns.getD 1 0 ∨ paramOf ns = ns.getD 1 0) :
    reduceX (numCode ns) = outX ns := by
  classical
  have hI : encodeUniform (instOf ns hv) (paramOf ns) = numCode ns := by
    rw [encodeUniform, encodeInstance_eq]
    conv_rhs => rw [← instToks_instOf ns hv hs]
    rw [numCode_append]
    simp [numCode]
  rw [← hI, reduceX_code _ _ (show extremeC (instOf ns hv) (paramOf ns) from hk)]
  unfold caseFormula outX
  have hd : (instOf ns hv).days = ns.getD 1 0 := rfl
  rw [hd]
  by_cases h1 : paramOf ns + 1 = ns.getD 1 0
  · rw [if_pos h1, if_pos h1]
    exact encodeFormula_eq ns hv
  · by_cases h2 : paramOf ns = ns.getD 1 0
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]
      exact encodeFormula_eqU ns hv
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]
      simp [encodeFormula, satF]

/-- **A word that is not the code of an accepted stream goes to the unsatisfiable formula.** -/
theorem tX_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ Shape eU ns ∧ condX ns) :
    reduceX w = encodeFormula unsatisfiable := by
  classical
  unfold reduceX
  rw [dif_neg (fun hg => h ((tX_gate w).1 hg))]

end Lax117284Proofs.Machine.X1Sem
