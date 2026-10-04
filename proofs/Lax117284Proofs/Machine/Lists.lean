import Mathlib.Data.List.Range
import Mathlib.Data.List.GetD
import Lax117284Proofs.Codes
import Lax117284Proofs.Machine.Bits

/-! ### `Lax117284Proofs.Machine.RecList` -/

section
/-!
Lists made of records of a fixed length.
-/

namespace Lax117284Proofs.Machine.RecList

variable {α : Type}

lemma length_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N : ℕ) :
    ((List.range N).flatMap f).length = c * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [hf, Nat.mul_succ]

lemma getD_flatMap_const (f : ℕ → List α) (c : ℕ) (hf : ∀ k, (f k).length = c) (N k r : ℕ)
    (hk : k < N) (hr : r < c) (d : α) :
    ((List.range N).flatMap f).getD (c * k + r) d = (f k).getD r d := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen := length_flatMap_const f c hf N
    rcases Nat.lt_or_ge k N with h | h
    · have hlt : c * k + r < c * N := by
        have := Nat.mul_le_mul_left c (show k + 1 ≤ N by omega)
        rw [Nat.mul_succ] at this; omega
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      exact ih h
    · have : k = N := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
      simp

end Lax117284Proofs.Machine.RecList

end

/-! ### `Lax117284Proofs.Machine.Lists` -/

section
/-!
Lists of numbers, and their codes: the code of a list of numbers, blocks of a fixed length read
off a flat list, and a double loop over rows and columns read as one loop.
-/

namespace Lax117284Proofs.Machine.Lists

open Lax117284.Problems Lax434930.PolynomialTime Lax117284Proofs.Codes
open Lax117284Proofs.Machine.Bits

/-- The code of a list of numbers: the codes of the numbers, one after the other. -/
def numCode (l : List ℕ) : Word := l.flatMap encodeNat

@[simp] lemma numCode_nil : numCode [] = [] := Eq.trans rfl rfl
@[simp] lemma numCode_cons (a : ℕ) (l : List ℕ) : numCode (a :: l) = encodeNat a ++ numCode l := by
  simp [numCode]
lemma numCode_append (l l' : List ℕ) : numCode (l ++ l') = numCode l ++ numCode l' := by
  simp [numCode]

/-- **A list of numbers is determined by its code.** -/
theorem numCode_inj : ∀ {l l' : List ℕ}, numCode l = numCode l' → l = l'
  | [], [], _ => rfl
  | [], b :: l', h => by
      exfalso
      have := congrArg List.length h
      simp only [numCode_nil, numCode_cons, List.length_nil, List.length_append] at this
      have h1 : 0 < (encodeNat b).length := by simp [encodeNat]
      omega
  | a :: l, [], h => by
      exfalso
      have := congrArg List.length h
      simp only [numCode_nil, numCode_cons, List.length_nil, List.length_append] at this
      have h1 : 0 < (encodeNat a).length := by simp [encodeNat]
      omega
  | a :: l, b :: l', h => by
      simp only [numCode_cons] at h
      obtain ⟨hab, hl⟩ := encodeNat_prefixFree _ _ _ _ h
      rw [hab, numCode_inj hl]

/-- The bits of a list of numbers' code, as numbers. -/
def numBits (l : List ℕ) : List ℕ := l.flatMap bitsNat

lemma natBits_numCode (l : List ℕ) : natBits (numCode l) = numBits l := by
  simp only [numCode, numBits, natBits, List.map_flatMap]
  refine List.flatMap_congr fun a _ => ?_
  exact natBits_encodeNat a

@[simp] lemma numBits_nil : numBits [] = [] := Eq.trans rfl rfl
@[simp] lemma numBits_cons (a : ℕ) (l : List ℕ) : numBits (a :: l) = bitsNat a ++ numBits l := by
  simp [numBits]
lemma numBits_append (l l' : List ℕ) : numBits (l ++ l') = numBits l ++ numBits l' := by
  simp [numBits]

/-! ### Loops over a range -/

lemma flatMap_finRange {α : Type} : ∀ (n : ℕ) (f : Fin n → List α),
    (List.finRange n).flatMap f =
      (List.range n).flatMap fun i => if h : i < n then f ⟨i, h⟩ else []
  | 0, _ => by simp
  | n + 1, f => by
    rw [List.finRange_succ_last, List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_map, flatMap_finRange n]
    congr 1
    · refine List.flatMap_congr fun i hi => ?_
      have hi' : i < n := List.mem_range.mp hi
      simp [hi', Nat.lt_succ_of_lt hi']
    · simp; rfl

/-- A loop over rows of a loop over columns is one loop over the cells. -/
lemma flatMap_rows {α : Type} (H : ℕ → List α) (n : ℕ) :
    ∀ m : ℕ, (List.range m).flatMap (fun a => (List.range n).flatMap fun b => H (a * n + b))
      = (List.range (m * n)).flatMap H
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_rows H n m, show (m + 1) * n = m * n + n by
      ring, List.range_add, List.flatMap_append, List.flatMap_map]
    simp [Nat.mul_comm]

/-- The blocks of two numbers read off a list, in order. -/
lemma flatMap_pairs (ns : List ℕ) (a : ℕ) :
    ∀ N : ℕ, a + 2 * N ≤ ns.length →
      (List.range N).flatMap (fun t => [ns.getD (a + 2 * t) 0, ns.getD (a + 2 * t + 1) 0])
        = (ns.drop a).take (2 * N)
  | 0, _ => by simp
  | N + 1, h => by
    rw [List.range_succ, List.flatMap_append, flatMap_pairs ns a N (by omega),
      show 2 * (N + 1) = 2 * N + 2 by ring, List.take_add]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_take,
      List.length_drop]
    have e : (List.drop (2 * N) (List.drop a ns)).take 2
        = [ns.getD (a + 2 * N) 0, ns.getD (a + 2 * N + 1) 0] := by
      apply List.ext_getElem?
      intro i
      rcases i with _ | _ | i
      · simp [List.getElem?_take, List.getElem?_drop, List.getD_eq_getElem?_getD]
        rw [show a + 2 * N = 2 * N + a by ring]
        rcases h1 : ns[2 * N + a]? with _ | v
        · exfalso
          have := (List.getElem?_eq_none_iff).1 h1
          omega
        · rfl
      · simp [List.getElem?_take, List.getElem?_drop, List.getD_eq_getElem?_getD]
        rw [show a + 2 * N + 1 = 2 * N + 1 + a by ring]
        rcases h1 : ns[2 * N + 1 + a]? with _ | v
        · exfalso
          have := (List.getElem?_eq_none_iff).1 h1
          omega
        · rfl
      · simp [List.getElem?_take, List.getElem?_drop]
    rw [e]

end Lax117284Proofs.Machine.Lists

end
