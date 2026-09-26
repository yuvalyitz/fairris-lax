import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.UNk

/-!
What the whole reduction computes, on the zeros and ones of its input: the bridge between what
the tokenizer accepts and the reduction as a map on words.
-/

namespace Lax117284Proofs.Machine.FreeMain

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck
open Lax117284Proofs.Machine.Bits

lemma code_map_num (ns : List ℕ) : code (ns.map Tok.num) = numCode ns := by
  induction ns with
  | nil => rfl
  | cons a t ih => simp [code, Tok.code, numCode] at ih ⊢; rw [ih]

lemma rejected_eq : rejected = numCode [1, 0, 1] := by
  have : instToks blocked = [1, 0] := rfl
  rw [rejected, encodeUniform, encodeInstance_eq, this]
  simp [numCode]

lemma natBits_rejected : natBits rejected = numBits [1, 0, 1] := by
  rw [rejected_eq, natBits_numCode]

lemma take_drop_map (arr : List ℕ) (K : ℕ) (h : 2 + K ≤ arr.length) :
    (arr.drop 2).take K = (List.range K).map (fun i => arr.getD (2 + i) 0) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    simp only [List.length_take, List.length_drop] at h1
    rw [List.getD_eq_getElem _ _ (by omega)]

lemma runMax_congr (arr ns : List ℕ) (n : ℕ)
    (h : ∀ j < n, arr.getD (2 + 2 * j) 0 = ns.getD (2 + 2 * j) 0) : runMax arr n = runMax ns n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runMax_succ, runMax_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

/-- The table of the array is the table of the stream, when they agree on its length. -/
lemma outFree_congr (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns)
    (hm : 0 < ns.getD 1 0) : outFree arr = outFree ns := by
  have hlenA : ns.length ≤ arr.length := by
    have := congrArg List.length h
    rw [List.length_take] at this; omega
  have hg : ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
    conv_rhs => rw [← h]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  have hnm : ns.getD 0 0 ≤ ns.getD 1 0 * ns.getD 0 0 := Nat.le_mul_of_pos_left _ hm
  have hgap : gapOf arr = gapOf ns := by
    unfold gapOf
    rw [h0]
    exact runMax_congr arr ns _ (fun j hj => hg _ (by omega))
  have hpar : paramOf arr = paramOf ns := by
    unfold paramOf
    rw [h0, h1]
    exact hg _ (by omega)
  have htab : (arr.drop 2).take (2 * (ns.getD 1 0 * ns.getD 0 0))
      = (ns.drop 2).take (2 * (ns.getD 1 0 * ns.getD 0 0)) := by
    rw [take_drop_map arr _ (by omega), take_drop_map ns _ (by omega)]
    refine List.map_congr_left fun i hi => ?_
    exact hg _ (by have := List.mem_range.mp hi; omega)
  unfold outFree
  rw [h0, h1, htab, hgap, hpar]
  have hnew : (List.range (ns.getD 0 0)).flatMap (fun j => [arr.getD (2 + 2 * j) 0, (j + 1) * gapOf ns])
      = (List.range (ns.getD 0 0)).flatMap (fun j => [ns.getD (2 + 2 * j) 0, (j + 1) * gapOf ns]) :=
    List.flatMap_congr fun j hj => by rw [hg _ (by have := List.mem_range.mp hj; omega)]
  rw [hnew]

/-- **A word the tokenizer accepts is the numbers of a stream of the format.** -/
theorem accepted_stream (y : List ℕ)
    (hacc : Accepts (EI eU) (run (EI eU) init (bitsOf y))) :
    ∃ ns : List ℕ, bitsOf y = numCode ns ∧ Shape eU ns ∧
      (run (EI eU) init (bitsOf y)).toks = ns.map Tok.num := by
  obtain ⟨hcode, hconf⟩ := accept_sound (EI eU) hacc
  obtain ⟨ns, hns, hsh⟩ := shape_of_conforms eU hconf
  refine ⟨ns, ?_, hsh, hns⟩
  rw [← hcode, hns, code_map_num]

theorem cond_iff (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eU ns) :
    (0 < arr.getD 1 0 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ↔
      (0 < ns.getD 1 0 ∧ Valid ns) := by
  have hg : ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
    conv_rhs => rw [← h]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  rw [h0, h1]
  constructor
  · rintro ⟨hm, hp⟩
    refine ⟨hm, fun t ht => ?_⟩
    have := hp t ht
    unfold Pass at this
    rw [hg _ (by omega), hg _ (by omega)] at this
    exact this
  · rintro ⟨hm, hv⟩
    refine ⟨hm, fun t ht => ?_⟩
    have := hv t ht
    unfold Pass
    rw [hg _ (by omega), hg _ (by omega)]
    exact this

/-- **What the reduction writes, when the tokenizer accepts.** -/
theorem bits_accept (y : List ℕ) (arr : List ℕ)
    (hacc : Accepts (EI eU) (run (EI eU) init (bitsOf y)))
    (harr : arr.take (run (EI eU) init (bitsOf y)).toks.length =
      (run (EI eU) init (bitsOf y)).toks.map Tok.val) :
    natBits (Lax117284.Corollary8.reduceFreeDay (bitsOf y)) =
      (if 0 < arr.getD 1 0 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t
        then numBits (outFree arr) else numBits [1, 0, 1]) := by
  obtain ⟨ns, hw, hsh, hns⟩ := accepted_stream y hacc
  have hval : (run (EI eU) init (bitsOf y)).toks.map Tok.val = ns := by
    rw [hns]; simp [List.map_map, Function.comp_def, Tok.val]
  have hlen : (run (EI eU) init (bitsOf y)).toks.length = ns.length := by rw [hns]; simp
  rw [hlen, hval] at harr
  by_cases hc : 0 < arr.getD 1 0 ∧ ∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t
  · have hc' := (cond_iff arr ns harr hsh).1 hc
    rw [if_pos hc, hw, free_eq ns hc'.2 hsh hc'.1, natBits_numCode,
      outFree_congr arr ns harr hsh hc'.1]
  · rw [if_neg hc, hw, free_rej (numCode ns), natBits_rejected]
    rintro ⟨ns', hw', hs', hv', hp'⟩
    have hnn : ns' = ns := (numCode_inj hw').symm
    subst hnn
    exact hc ((cond_iff arr ns' harr hsh).2 ⟨hp', hv'⟩)

/-- **What the reduction writes, when the tokenizer rejects.** -/
theorem bits_reject (y : List ℕ)
    (hn : ¬ Accepts (EI eU) (run (EI eU) init (bitsOf y))) :
    natBits (Lax117284.Corollary8.reduceFreeDay (bitsOf y)) = numBits [1, 0, 1] := by
  rw [free_rej (bitsOf y), natBits_rejected]
  rintro ⟨ns', hw', hs', -, -⟩
  apply hn
  have := (accept_complete (EI eU) (ns'.map Tok.num) (conforms_of_shape eU hs')).1
  rwa [code_map_num, ← hw'] at this

end Lax117284Proofs.Machine.FreeMain
