import Lax117284.Problems
import Mathlib.Data.Nat.Bits

/-!
The binary codes of the submission are prefix-free, so a word determines what it encodes.
A code is *prefix-free* when a code word followed by anything determines both the thing
and the rest; a number is a run of ones, a zero, and then its digits, which is such a code.
-/

namespace Lax117284Proofs.Codes

open Lax117284.Problems Lax434930.PolynomialTime

/-- A code is prefix-free: a code word followed by anything determines both. -/
def PrefixFree {α : Type} (e : α → Word) : Prop :=
  ∀ a b x y, e a ++ x = e b ++ y → a = b ∧ x = y

def ofBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

lemma ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, List.foldr_cons] at ih ⊢
    rw [ih]

lemma bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← ofBits_bits a, ← ofBits_bits b, h]

lemma replicate_true_inj (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih b h
      exact ⟨by omega, h2⟩

lemma encodeNat_prefixFree : PrefixFree encodeNat := by
  intro a b x y h
  simp only [encodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hl, hr⟩ := replicate_true_inj _ _ _ _ h
  obtain ⟨hb, hxy⟩ := List.append_inj hr hl
  exact ⟨bits_injective hb, hxy⟩

lemma encodeNat_injective : Function.Injective encodeNat := fun a b h => by
  have := encodeNat_prefixFree a b [] [] (by simpa using h)
  exact this.1

/-- Two prefix-free codes in sequence are prefix-free. -/
lemma PrefixFree.pair {α β : Type} {e : α → Word} {f : β → Word} (he : PrefixFree e)
    (hf : PrefixFree f) : PrefixFree fun ab : α × β => e ab.1 ++ f ab.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ x y h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h2⟩ := he _ _ _ _ h
  obtain ⟨h3, h4⟩ := hf _ _ _ _ h2
  exact ⟨by rw [h1, h3], h4⟩

lemma bool_prefixFree : PrefixFree fun b : Bool => [b] := by
  intro a b x y h
  simpa using h

/-- A sequence of `n` code words of a prefix-free code determines its entries. -/
lemma flatMap_inj {α : Type} {e : α → Word} (he : PrefixFree e) :
    ∀ (n : ℕ) (f g : Fin n → α) (x y : Word),
      (List.finRange n).flatMap (fun i => e (f i)) ++ x =
        (List.finRange n).flatMap (fun i => e (g i)) ++ y → f = g ∧ x = y := by
  intro n
  induction n with
  | zero => intro f g x y h; exact ⟨funext fun i => i.elim0, by simpa using h⟩
  | succ n ih =>
    intro f g x y h
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map, List.append_assoc] at h
    obtain ⟨h0, hrest⟩ := he _ _ _ _ h
    obtain ⟨hfg, hxy⟩ := ih (fun i => f i.succ) (fun i => g i.succ) x y hrest
    refine ⟨funext fun i => ?_, hxy⟩
    refine Fin.cases h0 (fun j => ?_) i
    exact congrFun hfg j

/-- A fixed-length sequence of code words is itself a prefix-free code. -/
lemma PrefixFree.fin {α : Type} {e : α → Word} (he : PrefixFree e) (n : ℕ) :
    PrefixFree fun f : Fin n → α => (List.finRange n).flatMap fun i => e (f i) :=
  fun f g x y h => flatMap_inj he n f g x y h

/-- The code of a number followed by a sign or digit. -/
lemma natBool_prefixFree : PrefixFree fun nb : ℕ × Bool => encodeNat nb.1 ++ [nb.2] :=
  encodeNat_prefixFree.pair bool_prefixFree

lemma natPair_prefixFree : PrefixFree fun nb : ℕ × ℕ => encodeNat nb.1 ++ encodeNat nb.2 :=
  encodeNat_prefixFree.pair encodeNat_prefixFree

end Lax117284Proofs.Codes
