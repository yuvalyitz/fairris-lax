import Lax117284Proofs.Treewidth.Fun.Lib1
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort

/-!
# WP F1, layer 2: `foldr`, `reverse`, `dedup`, insertion sort (= `List.mergeSort` on total preorders)

Ids `32 …`.  Extends `Lib1.Δ` through `layerΔ`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib2

open ToVal Lib1

abbrev fFoldr : ℕ := 32
abbrev fRevAux : ℕ := 33
abbrev fReverse : ℕ := 34
abbrev fDedup : ℕ := 35
abbrev fIns : ℕ := 36
abbrev fISort : ℕ := 37

/-- `foldr f ctx z xs`: `f ctx x acc` -/
def foldrTm : Tm :=
  .ite (.isNat (V 3)) (V 2)
    (.callv (V 0) [V 1, .fst (V 3), .call fFoldr [V 0, V 1, V 2, .snd (V 3)]])
/-- `revAux xs acc` -/
def revAuxTm : Tm :=
  .ite (.isNat (V 0)) (V 1) (.call fRevAux [.snd (V 0), .cons (.fst (V 0)) (V 1)])
def reverseTm : Tm := .call fRevAux [V 0, .lit 0]
/-- `dedup l` (Lean's `List.dedup`: keeps the last occurrence) -/
def dedupTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.letE (.call fDedup [.snd (V 0)])
      (.ite (.call fMem [.fst (V 1), V 0]) (V 0) (.cons (.fst (V 1)) (V 0))))
/-- `ins f ctx a l`: `orderedInsert` -/
def insTm : Tm :=
  .ite (.isNat (V 3)) (.cons (V 2) (V 3))
    (.ite (.callv (V 0) [V 1, V 2, .fst (V 3)]) (.cons (V 2) (V 3))
      (.cons (.fst (V 3)) (.call fIns [V 0, V 1, V 2, .snd (V 3)])))
/-- `isort f ctx l`: insertion sort -/
def isortTm : Tm :=
  .ite (.isNat (V 2)) (V 2) (.call fIns [V 0, V 1, .fst (V 2), .call fISort [V 0, V 1, .snd (V 2)]])

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 32 => some foldrTm | 33 => some revAuxTm | 34 => some reverseTm | 35 => some dedupTm
  | 36 => some insTm | 37 => some isortTm | _ => none

/-- The layer-2 table. -/
def Δ : ℕ → Option Tm := layerΔ Lib1.Δ 32 tbl

abbrev size : ℕ := 38

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 38 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have : ¬ 32 ≤ f → Lib1.Δ f = none := fun h32 => by omega
    by_cases h32 : 32 ≤ f
    · simp only [h32, if_true]; unfold tbl; split <;> first | rfl | omega
    · omega
  rw [this] at h; cases h

theorem ext1 : Lib1.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := Lib1.Δ_lt h; simp [Lib1.size] at this; omega)

theorem Δ_foldr : Δ fFoldr = some foldrTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fFoldr by decide)]; rfl
theorem Δ_revAux : Δ fRevAux = some revAuxTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fRevAux by decide)]; rfl
theorem Δ_reverse : Δ fReverse = some reverseTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fReverse by decide)]; rfl
theorem Δ_dedup : Δ fDedup = some dedupTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fDedup by decide)]; rfl
theorem Δ_ins : Δ fIns = some insTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fIns by decide)]; rfl
theorem Δ_isort : Δ fISort = some isortTm := by simp [Δ, layerΔ_ge tbl (show 32 ≤ fISort by decide)]; rfl

/-- the relation of a Boolean comparator -/
abbrev rOf {α : Type} (le : α → α → Bool) : α → α → Prop := fun a b => le a b = true

/-- `List.mergeSort` on a total preorder is the insertion sort. -/
theorem mergeSort_eq_insertionSort {α : Type} (le : α → α → Bool)
    (trans : ∀ (a b c : α), le a b → le b c → le a c) (total : ∀ (a b : α), le a b || le b a) :
    ∀ l : List α, l.mergeSort le = l.insertionSort (rOf le)
  | [] => by simp
  | a :: l => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons trans total a l
    have ih := mergeSort_eq_insertionSort le trans total l
    have hs := List.pairwise_mergeSort trans total (a :: l)
    rw [h1] at hs
    rw [List.insertionSort_cons, ← ih, h2, h1]
    clear h1 h2 ih
    have key : ∀ l₁ : List α, List.Pairwise (fun a b => le a b = true) (l₁ ++ a :: l₂) →
        (∀ b ∈ l₁, (!le a b) = true) → (l₁ ++ l₂).orderedInsert (rOf le) a = l₁ ++ a :: l₂ := by
      intro l₁
      induction l₁ with
      | nil =>
        intro hs _
        cases l₂ with
        | nil => simp
        | cons c l₂ =>
          have : le a c = true := (List.pairwise_cons.mp hs).1 c (by simp)
          simp [List.orderedInsert_cons, rOf, this]
      | cons b l₁ ih =>
        intro hs h3
        have hb : ¬ rOf le a b := by simpa [rOf] using h3 b (by simp)
        have := ih (List.pairwise_cons.mp hs).2 (fun x hx => h3 x (List.mem_cons_of_mem _ hx))
        simp only [List.cons_append, List.orderedInsert_cons, hb, if_false, this]
    exact (key l₁ hs h3).symm

/-- total cost of the calls made by a right fold. -/
def foldrCost {α β : Type} (g : α → β → β) (cf : α → β → ℕ) (z : β) : List α → ℕ
  | [] => 0
  | a :: l => cf a (l.foldr g z) + foldrCost g cf z l

theorem foldr_inv {α β : Type} (g : α → β → β) (P : β → Prop) (z : β) (hP : P z) :
    ∀ l : List α, (∀ a b, a ∈ l → P b → P (g a b)) → P (l.foldr g z)
  | [], _ => hP
  | a :: l, h => h a _ (by simp) (foldr_inv g P z hP l (fun a' b ha' hb => h a' b (List.mem_cons_of_mem _ ha') hb))

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

theorem foldr_runs (fid : ℕ) (ctx : Val) (g : α → β → β) (cf : α → β → ℕ) (P : β → Prop) (z : β)
    (l : List α) (hP : P z) (hstep : ∀ a b, a ∈ l → P b → P (g a b))
    (hf : ∀ a b, a ∈ l → P b → Runs Δ' B fid [ctx, toVal a, toVal b] (toVal (g a b)) (cf a b)) :
    Runs Δ' B fFoldr [.nat fid, ctx, toVal z, toVal l] (toVal (l.foldr g z))
      (14 * l.length + 6 + foldrCost g cf z l) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_foldr) ?_
    ev_start
    · ev_run
    · simp [foldrCost]
  | cons a l ih =>
    have ih := ih (fun a' b ha' hb => hstep a' b (List.mem_cons_of_mem _ ha') hb)
      (fun a' b ha' hb => hf a' b (List.mem_cons_of_mem _ ha') hb)
    have hP' : P (l.foldr g z) :=
      foldr_inv g P z hP l (fun a' b ha' hb => hstep a' b (List.mem_cons_of_mem _ ha') hb)
    have h1 := hf a (l.foldr g z) (List.mem_cons_self ..) hP'
    refine Runs.mk (hΔ _ _ Δ_foldr) ?_
    ev_start
    · ev_run
    · simp [foldrCost]; omega

theorem revAux_runs (xs acc : List α) :
    Runs Δ' B fRevAux [toVal xs, toVal acc] (toVal (xs.reverse ++ acc)) (12 * xs.length + 4) := by
  induction xs generalizing acc with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_revAux) ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    have ih := ih (a :: acc)
    refine Runs.mk (hΔ _ _ Δ_revAux) ?_
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    ev_start
    · ev_run
    · simp; omega

theorem reverse_runs (xs : List α) (hB : 0 < B) :
    Runs Δ' B fReverse [toVal xs] (toVal xs.reverse) (12 * xs.length + 10) := by
  have h := revAux_runs hΔ B xs ([] : List α)
  simp only [List.append_nil] at h
  refine Runs.mk (hΔ _ _ Δ_reverse) ?_
  ev_start
  · ev_run
  · simp; omega

theorem dedup_runs [DecidableEq α] (hB : 1 < B) (s : ℕ) : ∀ l : List α, (∀ a ∈ l, sz a ≤ s) →
    Runs Δ' B fDedup [toVal l] (toVal l.dedup) (60 * (s + 1) * (l.length + 1) ^ 2) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine Runs.mk (hΔ _ _ Δ_dedup) ?_
    ev_start
    · ev_run
    · simp; nlinarith [Nat.zero_le s]
  | cons a l ih =>
    intro hs
    have ih := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    have hsa := hs a (List.mem_cons_self ..)
    have hlen : (l.dedup).length ≤ l.length := (List.dedup_sublist l).length_le
    have hm : (30 * sz a + 24) * (l.dedup.length + 1) ≤ (30 * s + 24) * (l.length + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine Runs.mk (hΔ _ _ Δ_dedup) ?_
    by_cases ha : a ∈ l
    · have h2 := Lib1.mem_runs (Ext.trans ext1 hΔ) B hB a l.dedup true (by simp [ha])
      rw [List.dedup_cons_of_mem ha]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le (s * l.length), Nat.zero_le s, Nat.zero_le l.length]
    · have h2 := Lib1.mem_runs (Ext.trans ext1 hΔ) B hB a l.dedup false (by simp [ha])
      rw [List.dedup_cons_of_notMem ha]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le (s * l.length), Nat.zero_le s, Nat.zero_le l.length]

theorem ins_runs (fid : ℕ) (ctx : Val) (le : α → α → Bool) (cf : ℕ) (a : α) (l : List α)
    (hf : ∀ x ∈ l, Runs Δ' B fid [ctx, toVal a, toVal x] (toVal (le a x)) cf) :
    Runs Δ' B fIns [.nat fid, ctx, toVal a, toVal l] (toVal (l.orderedInsert (rOf le) a))
      ((cf + 20) * (l.length + 1) + 8) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_ins) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    have ih := ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    have h1 := hf x (List.mem_cons_self ..)
    refine Runs.mk (hΔ _ _ Δ_ins) ?_
    rcases Bool.eq_false_or_eq_true (le a x) with hp | hp
    · simp only [hp] at h1
      simp only [List.orderedInsert_cons, rOf, hp, if_true]
      ev_start
      · ev_run
      · simp only [List.length_cons]; nlinarith [Nat.zero_le cf, Nat.zero_le l.length]
    · simp only [hp] at h1
      simp only [List.orderedInsert_cons, rOf, hp, if_false, Bool.false_eq_true]
      ev_start
      · ev_run
      · simp only [List.length_cons]; nlinarith [Nat.zero_le cf, Nat.zero_le l.length]

theorem isort_runs (fid : ℕ) (ctx : Val) (le : α → α → Bool) (cf : ℕ) (l : List α)
    (hf : ∀ x ∈ l, ∀ y ∈ l, Runs Δ' B fid [ctx, toVal x, toVal y] (toVal (le x y)) cf) :
    Runs Δ' B fISort [.nat fid, ctx, toVal l] (toVal (l.insertionSort (rOf le)))
      ((cf + 60) * (l.length + 1) ^ 2 + 8) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_isort) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    have h2 := ins_runs hΔ B fid ctx le cf a (l.insertionSort (rOf le)) (fun x hx =>
      hf a (List.mem_cons_self ..) x (List.mem_cons_of_mem _ ((List.mem_insertionSort _).mp hx)))
    rw [List.length_insertionSort] at h2
    refine Runs.mk (hΔ _ _ Δ_isort) ?_
    rw [List.insertionSort_cons]
    ev_start
    · ev_run
    · simp only [List.length_cons]
      nlinarith [Nat.zero_le cf, Nat.zero_le l.length, Nat.zero_le (cf * l.length)]

/-- Lean's `List.mergeSort` (a stable merge sort) on a total preorder, computed by insertion sort. -/
theorem mergeSort_runs (fid : ℕ) (ctx : Val) (le : α → α → Bool) (cf : ℕ)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a) (l : List α)
    (hf : ∀ x ∈ l, ∀ y ∈ l, Runs Δ' B fid [ctx, toVal x, toVal y] (toVal (le x y)) cf) :
    Runs Δ' B fISort [.nat fid, ctx, toVal l] (toVal (l.mergeSort le))
      ((cf + 60) * (l.length + 1) ^ 2 + 8) := by
  rw [mergeSort_eq_insertionSort le trans total]
  exact isort_runs hΔ B fid ctx le cf l hf

end proofs
end Lib2
end Lax117284Proofs.Treewidth.Fun
