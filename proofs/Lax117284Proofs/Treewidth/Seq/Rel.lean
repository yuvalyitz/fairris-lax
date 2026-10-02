import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Common

/-!
# Entrywise order on sequences

`List.Forall₂ (· ≤ ·) a b` is "`a ≤ b`" of the paper (same length, `a_i ≤ b_i`).  Small helper
lemmas about it.
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- `a ≤ b` for sequences of the same length (Section 3 preliminaries). -/
abbrev LeSeq (a b : List ℕ) : Prop := List.Forall₂ (· ≤ ·) a b

theorem LeSeq.refl (a : List ℕ) : LeSeq a a := by
  induction a with
  | nil => exact List.Forall₂.nil
  | cons x a ih => exact List.Forall₂.cons (Nat.le_refl x) ih

theorem LeSeq.trans {a b c : List ℕ} (h1 : LeSeq a b) (h2 : LeSeq b c) : LeSeq a c := by
  induction h1 generalizing c with
  | nil => cases h2; exact List.Forall₂.nil
  | cons hab _ ih =>
    cases h2 with
    | cons hbc h2' => exact List.Forall₂.cons (Nat.le_trans hab hbc) (ih h2')

theorem LeSeq.length_eq {a b : List ℕ} (h : LeSeq a b) : a.length = b.length :=
  List.Forall₂.length_eq h

theorem LeSeq.append {a b c d : List ℕ} (h1 : LeSeq a b) (h2 : LeSeq c d) :
    LeSeq (a ++ c) (b ++ d) := by
  induction h1 with
  | nil => simpa using h2
  | cons hab _ ih => exact List.Forall₂.cons hab ih

theorem LeSeq.zipWith_add {a b c d : List ℕ} (h1 : LeSeq a b) (h2 : LeSeq c d) :
    LeSeq (List.zipWith (· + ·) a c) (List.zipWith (· + ·) b d) := by
  induction h1 generalizing c d with
  | nil => simp
  | cons hab _ ih =>
    cases h2 with
    | nil => simp
    | cons hcd h2' =>
      simp only [List.zipWith_cons_cons]
      exact List.Forall₂.cons (Nat.add_le_add hab hcd) (ih h2')

theorem leSeq_replicate_left {x : ℕ} {m : List ℕ} (h : ∀ z ∈ m, x ≤ z) :
    LeSeq (List.replicate m.length x) m := by
  induction m with
  | nil => exact List.Forall₂.nil
  | cons z m ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h z (by simp)) (ih fun w hw => h w (by simp [hw]))

theorem leSeq_replicate_right {x : ℕ} {m : List ℕ} (h : ∀ z ∈ m, z ≤ x) :
    LeSeq m (List.replicate m.length x) := by
  induction m with
  | nil => exact List.Forall₂.nil
  | cons z m ih =>
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons (h z (by simp)) (ih fun w hw => h w (by simp [hw]))

theorem LeSeq.flip {a b : List ℕ} (h : List.Forall₂ (fun p q => q ≤ p) a b) : LeSeq b a := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

theorem LeSeq.flip' {a b : List ℕ} (h : LeSeq a b) : List.Forall₂ (fun p q => q ≤ p) b a := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons hab ih

end Lax117284Proofs.Treewidth.Seq
