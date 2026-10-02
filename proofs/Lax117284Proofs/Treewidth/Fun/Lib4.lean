import Lax117284Proofs.Treewidth.Fun.Lib3
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists

/-!
# WP F1, layer 4: `find?`, `findSome?`, `filterMap`, `sum`, `head?`, `toFinset`, `sublists`, `card`

Ids `64 …`.  `Option`: `none = nat 0`, `some a = cons (nat 1) (toVal a)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib4

open ToVal Lib1

abbrev fFind : ℕ := 64
abbrev fFindSome : ℕ := 65
abbrev fFilterMap : ℕ := 66
abbrev fSum : ℕ := 67
abbrev fHead : ℕ := 68
abbrev fToFinset : ℕ := 69
abbrev fSublists : ℕ := 70
abbrev fPairUp : ℕ := 71

/-- `find? p ctx xs` -/
def findTm : Tm :=
  .ite (.isNat (V 2)) (.lit 0)
    (.ite (.callv (V 0) [V 1, .fst (V 2)]) (.cons (.lit 1) (.fst (V 2))) (.call fFind [V 0, V 1, .snd (V 2)]))
/-- `findSome? f ctx xs` -/
def findSomeTm : Tm :=
  .ite (.isNat (V 2)) (.lit 0)
    (.letE (.callv (V 0) [V 1, .fst (V 2)])
      (.ite (.isNat (V 0)) (.call fFindSome [V 1, V 2, .snd (V 3)]) (V 0)))
/-- `filterMap f ctx xs` -/
def filterMapTm : Tm :=
  .ite (.isNat (V 2)) (V 2)
    (.letE (.callv (V 0) [V 1, .fst (V 2)])
      (.ite (.isNat (V 0)) (.call fFilterMap [V 1, V 2, .snd (V 3)])
        (.cons (.snd (V 0)) (.call fFilterMap [V 1, V 2, .snd (V 3)]))))
/-- sum of a list of naturals -/
def sumTm : Tm := .ite (.isNat (V 0)) (.lit 0) (.add (.fst (V 0)) (.call fSum [.snd (V 0)]))
def headTm : Tm := .ite (.isNat (V 0)) (.lit 0) (.cons (.lit 1) (.fst (V 0)))
/-- `List.toFinset` on naturals, as the sorted list -/
def toFinsetTm : Tm := .ite (.isNat (V 0)) (V 0) (.call Lib3.fInsertS [.fst (V 0), .call fToFinset [.snd (V 0)]])
/-- `[x, a :: x]` with `a` the context -/
def pairUpTm : Tm := .cons (V 1) (.cons (.cons (V 0) (V 1)) (.lit 0))
/-- `List.sublists` (needs `fPairUp < B`) -/
def sublistsTm : Tm :=
  .ite (.isNat (V 0)) (.cons (.lit 0) (.lit 0))
    (.call Lib1.fFlatMap [.lit fPairUp, .fst (V 0), .call fSublists [.snd (V 0)]])

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 64 => some findTm | 65 => some findSomeTm | 66 => some filterMapTm | 67 => some sumTm
  | 68 => some headTm | 69 => some toFinsetTm | 70 => some sublistsTm | 71 => some pairUpTm | _ => none

/-- The layer-4 table. -/
def Δ : ℕ → Option Tm := layerΔ Lib3.Δ 64 tbl

abbrev size : ℕ := 72

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 72 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h64 : 64 ≤ f := by omega
    simp only [h64, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext3 : Lib3.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := Lib3.Δ_lt h; simp [Lib3.size] at this; omega)
theorem ext2 : Lib2.Δ ⊑ Δ := Ext.trans Lib3.ext2 ext3
theorem ext1 : Lib1.Δ ⊑ Δ := Ext.trans Lib3.ext1 ext3

theorem Δ_find : Δ fFind = some findTm := by simp [Δ, layerΔ_ge tbl (show 64 ≤ fFind by decide)]; rfl
theorem Δ_findSome : Δ fFindSome = some findSomeTm := by simp [Δ, layerΔ_ge tbl (show 64 ≤ fFindSome by decide)]; rfl
theorem Δ_toFinset : Δ fToFinset = some toFinsetTm := by simp [Δ, layerΔ_ge tbl (show 64 ≤ fToFinset by decide)]; rfl
theorem Δ_sublists : Δ fSublists = some sublistsTm := by simp [Δ, layerΔ_ge tbl (show 64 ≤ fSublists by decide)]; rfl
theorem Δ_pairUp : Δ fPairUp = some pairUpTm := by simp [Δ, layerΔ_ge tbl (show 64 ≤ fPairUp by decide)]; rfl

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

theorem find_runs (fid : ℕ) (ctx : Val) (p : α → Bool) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (p a)) (cf a)) (hB : 1 < B) :
    Runs Δ' B fFind [.nat fid, ctx, toVal l] (toVal (l.find? p)) (24 * l.length + 6 + (l.map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_find) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf a (List.mem_cons_self ..)
    refine Runs.mk (hΔ _ _ Δ_find) ?_
    rcases Bool.eq_false_or_eq_true (p a) with hp | hp
    · simp only [hp] at h1
      simp only [List.find?_cons, hp]
      ev_start
      · ev_run
      · simp; omega
    · simp only [hp] at h1
      simp only [List.find?_cons, hp]
      ev_start
      · ev_run
      · simp; omega

theorem toFinset_runs (l : List ℕ) :
    Runs Δ' B fToFinset [toVal l] (toVal l.toFinset) (60 * (l.length + 1) ^ 2) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_toFinset) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have h2 := Lib3.insert_runs (Ext.trans ext3 hΔ) B a l.toFinset
    have hc : l.toFinset.card ≤ l.length := List.toFinset_card_le l
    refine Runs.mk (hΔ _ _ Δ_toFinset) ?_
    rw [List.toFinset_cons]
    ev_start
    · ev_run
    · simp only [List.length_cons]
      nlinarith [Nat.zero_le l.length]

theorem pairUp_runs (a : α) (x : List α) (hB : 0 < B) :
    Runs Δ' B fPairUp [toVal a, toVal x] (toVal [x, a :: x]) 12 := by
  refine Runs.mk (hΔ _ _ Δ_pairUp) ?_
  ev_start
  · ev_run
  · simp

theorem sublists_runs (hB : 72 < B) (l : List α) :
    Runs Δ' B fSublists [toVal l] (toVal l.sublists) (100 * 2 ^ l.length) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_sublists) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have h2 := Lib1.flatMap_runs (Ext.trans ext1 hΔ) B fPairUp (toVal a) (fun x : List α => [x, a :: x])
      (fun _ => 12) l.sublists (fun x _ => pairUp_runs hΔ B a x (by omega))
    have hl : l.sublists.length = 2 ^ l.length := List.length_sublists l
    have hsum : (l.sublists.map (fun x => 12 + 10 * ([x, a :: x] : List (List α)).length + 20)).sum
        = 52 * 2 ^ l.length := by
      have : ∀ (m : List (List α)), (m.map (fun x => 12 + 10 * ([x, a :: x] : List (List α)).length + 20)).sum = 52 * m.length := by
        intro m; induction m with
        | nil => simp
        | cons x m ih => simp [ih]; omega
      rw [this, hl]
    rw [hsum] at h2
    have hp : (List.sublists (a :: l)) = l.sublists.flatMap (fun x => [x, a :: x]) := rfl
    have hpu : fPairUp < B := by show 71 < B; omega
    refine Runs.mk (hΔ _ _ Δ_sublists) ?_
    rw [hp]
    ev_start
    · ev_run
    · simp only [List.length_cons, Nat.pow_succ]
      have := Nat.one_le_two_pow (n := l.length)
      nlinarith
theorem card_runs (S : Finset ℕ) (hB : 8 * S.card + 8 < B) :
    Runs Δ' B Lib1.fLength [toVal S] (toVal S.card) (8 * S.card + 5) := by
  have h := Lib1.length_runs (Ext.trans ext1 hΔ) B (S.sort (· ≤ ·)) (by rw [Finset.length_sort]; exact hB)
  rw [Finset.length_sort] at h
  exact h

end proofs
end Lib4
end Lax117284Proofs.Treewidth.Fun
