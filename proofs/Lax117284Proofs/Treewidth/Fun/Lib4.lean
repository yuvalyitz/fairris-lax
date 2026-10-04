import Lax117284Proofs.Treewidth.Fun.Lib2
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sublists

/-! ### `Lax117284Proofs.Treewidth.Fun.Lib3` -/

section
/-!
# WP F1, layer 3: `Finset ℕ` as strictly sorted lists — membership, insert, erase, union, inter, diff, subset

Ids `48 …`.  The functions run on raw lists (`unionL`, …, no sortedness needed for the *cost*); on strictly sorted lists
they implement the `Finset` operations (`toVal (S ∪ T)` etc.).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib3

open ToVal Lib1

abbrev fMemS : ℕ := 48
abbrev fInsertS : ℕ := 49
abbrev fEraseS : ℕ := 50
abbrev fUnionS : ℕ := 51
abbrev fInterS : ℕ := 52
abbrev fDiffS : ℕ := 53
abbrev fSubsetS : ℕ := 54

/-- `memS a xs` on a sorted list (stops early) -/
def memSTm : Tm :=
  .ite (.isNat (V 1)) (.lit 0)
    (.ite (.lt (V 0) (.fst (V 1))) (.lit 0)
      (.ite (.eq (V 0) (.fst (V 1))) (.lit 1) (.call fMemS [V 0, .snd (V 1)])))
def insertSTm : Tm :=
  .ite (.isNat (V 1)) (.cons (V 0) (V 1))
    (.ite (.lt (V 0) (.fst (V 1))) (.cons (V 0) (V 1))
      (.ite (.eq (V 0) (.fst (V 1))) (V 1) (.cons (.fst (V 1)) (.call fInsertS [V 0, .snd (V 1)]))))
def eraseSTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.lt (V 0) (.fst (V 1))) (V 1)
      (.ite (.eq (V 0) (.fst (V 1))) (.snd (V 1)) (.cons (.fst (V 1)) (.call fEraseS [V 0, .snd (V 1)]))))
def unionSTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.ite (.isNat (V 1)) (V 0)
      (.ite (.lt (.fst (V 0)) (.fst (V 1))) (.cons (.fst (V 0)) (.call fUnionS [.snd (V 0), V 1]))
        (.ite (.lt (.fst (V 1)) (.fst (V 0))) (.cons (.fst (V 1)) (.call fUnionS [V 0, .snd (V 1)]))
          (.cons (.fst (V 0)) (.call fUnionS [.snd (V 0), .snd (V 1)])))))
def interSTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.ite (.isNat (V 1)) (V 1)
      (.ite (.lt (.fst (V 0)) (.fst (V 1))) (.call fInterS [.snd (V 0), V 1])
        (.ite (.lt (.fst (V 1)) (.fst (V 0))) (.call fInterS [V 0, .snd (V 1)])
          (.cons (.fst (V 0)) (.call fInterS [.snd (V 0), .snd (V 1)])))))
def diffSTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.ite (.isNat (V 1)) (V 0)
      (.ite (.lt (.fst (V 0)) (.fst (V 1))) (.cons (.fst (V 0)) (.call fDiffS [.snd (V 0), V 1]))
        (.ite (.lt (.fst (V 1)) (.fst (V 0))) (.call fDiffS [V 0, .snd (V 1)])
          (.call fDiffS [.snd (V 0), .snd (V 1)]))))
def subsetSTm : Tm :=
  .ite (.isNat (V 0)) (.lit 1)
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.lt (.fst (V 0)) (.fst (V 1))) (.lit 0)
        (.ite (.lt (.fst (V 1)) (.fst (V 0))) (.call fSubsetS [V 0, .snd (V 1)])
          (.call fSubsetS [.snd (V 0), .snd (V 1)]))))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 48 => some memSTm | 49 => some insertSTm | 50 => some eraseSTm | 51 => some unionSTm
  | 52 => some interSTm | 53 => some diffSTm | 54 => some subsetSTm | _ => none

/-- The layer-3 table. -/
def Δ : ℕ → Option Tm := layerΔ Lib2.Δ 48 tbl

abbrev size : ℕ := 55

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 55 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h48 : 48 ≤ f := by omega
    simp only [h48, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem ext2 : Lib2.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := Lib2.Δ_lt h; simp [Lib2.size] at this; omega)
theorem ext1 : Lib1.Δ ⊑ Δ := Ext.trans Lib2.ext1 ext2

theorem Δ_insertS : Δ fInsertS = some insertSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fInsertS by decide)]; rfl
theorem Δ_eraseS : Δ fEraseS = some eraseSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fEraseS by decide)]; rfl
theorem Δ_unionS : Δ fUnionS = some unionSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fUnionS by decide)]; rfl
theorem Δ_interS : Δ fInterS = some interSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fInterS by decide)]; rfl
theorem Δ_diffS : Δ fDiffS = some diffSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fDiffS by decide)]; rfl
theorem Δ_subsetS : Δ fSubsetS = some subsetSTm := by simp [Δ, layerΔ_ge tbl (show 48 ≤ fSubsetS by decide)]; rfl

/-! ### the list-level functions (same recursion as the F bodies) -/

/-- `a ∈ xs`, scanning a sorted list only up to the first element `≥ a`. -/
def memL (a : ℕ) : List ℕ → Bool
  | [] => false
  | x :: xs => if a < x then false else if a = x then true else memL a xs

def insertL (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | x :: xs => if a < x then a :: x :: xs else if a = x then x :: xs else x :: insertL a xs

def eraseL (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if a < x then x :: xs else if a = x then xs else x :: eraseL a xs

def unionL : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x < y then x :: unionL xs (y :: ys) else if y < x then y :: unionL (x :: xs) ys else x :: unionL xs ys
termination_by xs ys => xs.length + ys.length

def interL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: ys =>
    if x < y then interL xs (y :: ys) else if y < x then interL (x :: xs) ys else x :: interL xs ys
termination_by xs ys => xs.length + ys.length

def diffL : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    if x < y then x :: diffL xs (y :: ys) else if y < x then diffL (x :: xs) ys else diffL xs ys
termination_by xs ys => xs.length + ys.length

def subsetL : List ℕ → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if x < y then false else if y < x then subsetL (x :: xs) ys else subsetL xs ys
termination_by xs ys => xs.length + ys.length

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem unionL_runs (xs ys : List ℕ) :
    Runs Δ' B fUnionS [toVal xs, toVal ys] (toVal (unionL xs ys)) (60 * (xs.length + ys.length) + 20) := by
  fun_induction unionL xs ys with
  | case1 ys =>
    refine Runs.mk (hΔ _ _ Δ_unionS) ?_
    ev_start
    · ev_run
    · simp
  | case2 x xs =>
    refine Runs.mk (hΔ _ _ Δ_unionS) ?_
    ev_start
    · ev_run
    · simp
  | case3 x xs y ys hxy ih =>
    refine Runs.mk (hΔ _ _ Δ_unionS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case4 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_unionS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case5 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_unionS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem interL_runs (xs ys : List ℕ) :
    Runs Δ' B fInterS [toVal xs, toVal ys] (toVal (interL xs ys)) (60 * (xs.length + ys.length) + 20) := by
  fun_induction interL xs ys with
  | case1 ys =>
    refine Runs.mk (hΔ _ _ Δ_interS) ?_
    ev_start
    · ev_run
    · simp
  | case2 x xs =>
    refine Runs.mk (hΔ _ _ Δ_interS) ?_
    ev_start
    · ev_run
    · simp
  | case3 x xs y ys hxy ih =>
    refine Runs.mk (hΔ _ _ Δ_interS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case4 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_interS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case5 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_interS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem diffL_runs (xs ys : List ℕ) :
    Runs Δ' B fDiffS [toVal xs, toVal ys] (toVal (diffL xs ys)) (60 * (xs.length + ys.length) + 20) := by
  fun_induction diffL xs ys with
  | case1 ys =>
    refine Runs.mk (hΔ _ _ Δ_diffS) ?_
    ev_start
    · ev_run
    · simp
  | case2 x xs =>
    refine Runs.mk (hΔ _ _ Δ_diffS) ?_
    ev_start
    · ev_run
    · simp
  | case3 x xs y ys hxy ih =>
    refine Runs.mk (hΔ _ _ Δ_diffS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case4 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_diffS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case5 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_diffS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem subsetL_runs (hB : 1 < B) (xs ys : List ℕ) :
    Runs Δ' B fSubsetS [toVal xs, toVal ys] (toVal (subsetL xs ys)) (60 * (xs.length + ys.length) + 20) := by
  fun_induction subsetL xs ys with
  | case1 ys =>
    refine Runs.mk (hΔ _ _ Δ_subsetS) ?_
    ev_start
    · ev_run
    · simp
  | case2 x xs =>
    refine Runs.mk (hΔ _ _ Δ_subsetS) ?_
    ev_start
    · ev_run
    · simp
  | case3 x xs y ys hxy =>
    refine Runs.mk (hΔ _ _ Δ_subsetS) ?_
    ev_start
    · ev_run
    · simp
  | case4 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_subsetS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega
  | case5 x xs y ys hxy hyx ih =>
    refine Runs.mk (hΔ _ _ Δ_subsetS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem insertL_runs (a : ℕ) (xs : List ℕ) :
    Runs Δ' B fInsertS [toVal a, toVal xs] (toVal (insertL a xs)) (40 * xs.length + 20) := by
  fun_induction insertL a xs with
  | case1 =>
    refine Runs.mk (hΔ _ _ Δ_insertS) ?_
    ev_start
    · ev_run
    · simp
  | case2 =>
    refine Runs.mk (hΔ _ _ Δ_insertS) ?_
    ev_start
    · ev_run
    · simp
  | case3 =>
    refine Runs.mk (hΔ _ _ Δ_insertS) ?_
    ev_start
    · ev_run
    · simp
  | case4 =>
    refine Runs.mk (hΔ _ _ Δ_insertS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

theorem eraseL_runs (a : ℕ) (xs : List ℕ) :
    Runs Δ' B fEraseS [toVal a, toVal xs] (toVal (eraseL a xs)) (40 * xs.length + 20) := by
  fun_induction eraseL a xs with
  | case1 =>
    refine Runs.mk (hΔ _ _ Δ_eraseS) ?_
    ev_start
    · ev_run
    · simp
  | case2 =>
    refine Runs.mk (hΔ _ _ Δ_eraseS) ?_
    ev_start
    · ev_run
    · simp
  | case3 =>
    refine Runs.mk (hΔ _ _ Δ_eraseS) ?_
    ev_start
    · ev_run
    · simp
  | case4 =>
    refine Runs.mk (hΔ _ _ Δ_eraseS) ?_
    ev_start
    · ev_run
    · simp only [List.length_cons]; omega

end proofs

theorem mem_unionL (xs ys : List ℕ) (a : ℕ) : a ∈ unionL xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  fun_induction unionL xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih => simp [ih]; tauto
  | case4 x xs y ys hxy hyx ih => simp [ih]; tauto
  | case5 x xs y ys hxy hyx ih =>
    have : x = y := by omega
    subst this
    simp [ih]; tauto

theorem sorted_unionL (xs ys : List ℕ) (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) :
    (unionL xs ys).Pairwise (· < ·) := by
  fun_induction unionL xs ys with
  | case1 ys => simpa using hy
  | case2 x xs => simpa using hx
  | case3 x xs y ys hxy ih =>
    rw [List.pairwise_cons] at hx ⊢
    refine ⟨fun a ha => ?_, ih hx.2 hy⟩
    rw [mem_unionL] at ha
    rcases ha with ha | ha
    · exact hx.1 a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hxy
      · exact lt_trans hxy ((List.pairwise_cons.mp hy).1 a ha)
  | case4 x xs y ys hxy hyx ih =>
    rw [List.pairwise_cons] at hy ⊢
    refine ⟨fun a ha => ?_, ih hx hy.2⟩
    rw [mem_unionL] at ha
    rcases ha with ha | ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact hyx
      · exact lt_trans hyx ((List.pairwise_cons.mp hx).1 a ha)
    · exact hy.1 a ha
  | case5 x xs y ys hxy hyx ih =>
    have : x = y := by omega
    subst this
    rw [List.pairwise_cons] at hx hy ⊢
    refine ⟨fun a ha => ?_, ih hx.2 hy.2⟩
    rw [mem_unionL] at ha
    rcases ha with ha | ha
    · exact hx.1 a ha
    · exact hy.1 a ha

theorem interL_sublist (xs ys : List ℕ) : (interL xs ys).Sublist xs := by
  fun_induction interL xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih => exact ih.trans (List.sublist_cons_self _ _)
  | case4 x xs y ys hxy hyx ih => exact ih
  | case5 x xs y ys hxy hyx ih => exact ih.cons_cons _

theorem mem_interL (xs ys : List ℕ) (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) (a : ℕ) :
    a ∈ interL xs ys ↔ a ∈ xs ∧ a ∈ ys := by
  fun_induction interL xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih =>
    have hx' := List.pairwise_cons.mp hx
    rw [ih hx'.2 hy]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases List.mem_cons.mp h1 with rfl | h1
      · exfalso
        rcases List.mem_cons.mp h2 with rfl | h2
        · omega
        · have := (List.pairwise_cons.mp hy).1 a h2; omega
      · exact ⟨h1, h2⟩
  | case4 x xs y ys hxy hyx ih =>
    have hy' := List.pairwise_cons.mp hy
    rw [ih hx hy'.2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, List.mem_cons_of_mem _ h2⟩
    · rintro ⟨h1, h2⟩
      rcases List.mem_cons.mp h2 with rfl | h2
      · exfalso
        rcases List.mem_cons.mp h1 with rfl | h1
        · omega
        · have := (List.pairwise_cons.mp hx).1 a h1; omega
      · exact ⟨h1, h2⟩
  | case5 x xs y ys hxy hyx ih =>
    have : x = y := by omega
    subst this
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    rw [List.mem_cons, ih hx'.2 hy'.2]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨List.mem_cons_self .., List.mem_cons_self ..⟩
      · exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
    · rintro ⟨h1, h2⟩
      rcases List.mem_cons.mp h1 with e1 | h1'
      · exact Or.inl e1
      · rcases List.mem_cons.mp h2 with e2 | h2'
        · exfalso; have := hx'.1 _ h1'; omega
        · exact Or.inr ⟨h1', h2'⟩


theorem diffL_sublist (xs ys : List ℕ) : (diffL xs ys).Sublist xs := by
  fun_induction diffL xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih => exact ih.cons_cons _
  | case4 x xs y ys hxy hyx ih => exact ih
  | case5 x xs y ys hxy hyx ih => exact ih.trans (List.sublist_cons_self _ _)

theorem mem_diffL (xs ys : List ℕ) (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) (a : ℕ) :
    a ∈ diffL xs ys ↔ a ∈ xs ∧ a ∉ ys := by
  fun_induction diffL xs ys with
  | case1 ys => simp
  | case2 x xs => simp
  | case3 x xs y ys hxy ih =>
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    rw [List.mem_cons, ih hx'.2 hy]
    have h1 := hx'.1 a
    have h2 := hy'.1 a
    simp only [List.mem_cons, not_or]
    by_cases hA : a ∈ xs <;> by_cases hB : a ∈ ys <;> simp [hA, hB] <;> first | omega | (have := h1 hA; omega) | (have := h2 hB; omega)
  | case4 x xs y ys hxy hyx ih =>
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    rw [ih hx hy'.2]
    have h1 := hx'.1 a
    have h2 := hy'.1 a
    simp only [List.mem_cons, not_or]
    by_cases hA : a ∈ xs <;> by_cases hB : a ∈ ys <;> simp [hA, hB] <;> first | omega | (have := h1 hA; omega) | (have := h2 hB; omega)
  | case5 x xs y ys hxy hyx ih =>
    have : x = y := by omega
    subst this
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    rw [ih hx'.2 hy'.2]
    have h1 := hx'.1 a
    have h2 := hy'.1 a
    simp only [List.mem_cons, not_or]
    by_cases hA : a ∈ xs <;> by_cases hB : a ∈ ys <;> simp [hA, hB] <;> first | omega | (have := h1 hA; omega) | (have := h2 hB; omega)

theorem subsetL_iff (xs ys : List ℕ) (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·)) :
    subsetL xs ys = true ↔ ∀ a ∈ xs, a ∈ ys := by
  fun_induction subsetL xs ys with
  | case1 ys => simp
  | case2 x xs =>
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd (h x (by simp)) (by simp)
  | case3 x xs y ys hxy =>
    have hy' := List.pairwise_cons.mp hy
    simp only [Bool.false_eq_true, false_iff, not_forall]
    refine ⟨x, List.mem_cons_self .., fun h => ?_⟩
    rcases List.mem_cons.mp h with h | h
    · omega
    · have := hy'.1 x h; omega
  | case4 x xs y ys hxy hyx ih =>
    have hy' := List.pairwise_cons.mp hy
    rw [ih hx hy'.2]
    constructor
    · intro h a ha; exact List.mem_cons_of_mem _ (h a ha)
    · intro h a ha
      rcases List.mem_cons.mp (h a ha) with e | h'
      · exfalso
        rcases List.mem_cons.mp ha with e' | ha'
        · omega
        · have := (List.pairwise_cons.mp hx).1 a ha'; omega
      · exact h'
  | case5 x xs y ys hxy hyx ih =>
    have : x = y := by omega
    subst this
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    rw [ih hx'.2 hy'.2]
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with e | ha'
      · subst e; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h a ha')
    · intro h a ha
      rcases List.mem_cons.mp (h a (List.mem_cons_of_mem _ ha)) with e | h'
      · exfalso; have := hx'.1 a ha; omega
      · exact h'

theorem mem_insertL (a : ℕ) (xs : List ℕ) (b : ℕ) : b ∈ insertL a xs ↔ b = a ∨ b ∈ xs := by
  fun_induction insertL a xs with
  | case1 => simp
  | case2 x xs h => simp
  | case3 => simp
  | case4 x xs h1 h2 ih => simp [ih]; tauto

theorem sorted_insertL (a : ℕ) (xs : List ℕ) (hx : xs.Pairwise (· < ·)) : (insertL a xs).Pairwise (· < ·) := by
  fun_induction insertL a xs with
  | case1 => simp
  | case2 x xs h =>
    have hx' := List.pairwise_cons.mp hx
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, hx⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h
    · have := hx'.1 b hb; omega
  | case3 => simpa using hx
  | case4 x xs h1 h2 ih =>
    have hx' := List.pairwise_cons.mp hx
    have := ih hx'.2
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, this⟩
    have hb' : b = a ∨ b ∈ xs := (mem_insertL a xs b).mp hb
    rcases hb' with rfl | hb'
    · omega
    · exact hx'.1 b hb'


theorem eraseL_sublist (a : ℕ) (xs : List ℕ) : (eraseL a xs).Sublist xs := by
  fun_induction eraseL a xs with
  | case1 => simp
  | case2 x xs h => exact List.Sublist.refl _
  | case3 => exact List.sublist_cons_self _ _
  | case4 x xs h1 h2 ih => exact ih.cons_cons _

theorem mem_eraseL (a : ℕ) (xs : List ℕ) (hx : xs.Pairwise (· < ·)) (b : ℕ) :
    b ∈ eraseL a xs ↔ b ∈ xs ∧ b ≠ a := by
  fun_induction eraseL a xs with
  | case1 => simp
  | case2 x xs h =>
    have hx' := List.pairwise_cons.mp hx
    simp only [List.mem_cons]
    constructor
    · intro hb; refine ⟨hb, ?_⟩
      rcases hb with rfl | hb
      · omega
      · have := hx'.1 b hb; omega
    · exact fun h => h.1
  | case3 =>
    have hx' := List.pairwise_cons.mp hx
    simp only [List.mem_cons]
    constructor
    · intro hb; exact ⟨Or.inr hb, fun e => by subst e; exact absurd (hx'.1 _ hb) (lt_irrefl _)⟩
    · rintro ⟨h | h, hne⟩
      · exact absurd h hne
      · exact h
  | case4 x xs h1 h2 ih =>
    have hx' := List.pairwise_cons.mp hx
    rw [List.mem_cons, ih hx'.2, List.mem_cons]
    constructor
    · rintro (rfl | ⟨h, hne⟩)
      · exact ⟨Or.inl rfl, fun e => h2 e.symm⟩
      · exact ⟨Or.inr h, hne⟩
    · rintro ⟨h | h, hne⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, hne⟩


/-! ### the `Finset` operations -/

theorem sorted_sort (S : Finset ℕ) : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
  have h1 := Finset.pairwise_sort S (· ≤ ·)
  have h2 := Finset.sort_nodup S (· ≤ ·)
  have := (List.pairwise_and_iff.mpr ⟨h1, List.nodup_iff_pairwise_ne.mp h2⟩)
  exact this.imp (fun ⟨a, b⟩ => lt_of_le_of_ne a b)

/-- a strictly sorted list with the members of `S` is the view of `S`. -/
theorem toVal_finset_of_sorted {S : Finset ℕ} {l : List ℕ} (hl : l.Pairwise (· < ·)) (h : ∀ a, a ∈ S ↔ a ∈ l) :
    toVal S = toVal l := by
  have hS : S = l.toFinset := by ext a; simp [h]
  have hnd : l.Nodup := hl.imp (fun h => ne_of_lt h)
  have hs : S.sort (· ≤ ·) = l := by
    rw [hS]; exact (List.toFinset_sort (· ≤ ·) hnd).mpr (hl.imp (fun h => le_of_lt h))
  rw [toVal_finset, hs]

theorem toVal_sort_mem (S : Finset ℕ) (a : ℕ) : a ∈ S.sort (· ≤ ·) ↔ a ∈ S := Finset.mem_sort _

section proofs2
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem union_runs (S T : Finset ℕ) :
    Runs Δ' B fUnionS [toVal S, toVal T] (toVal (S ∪ T)) (60 * (S.card + T.card) + 20) := by
  have h := unionL_runs hΔ B (S.sort (· ≤ ·)) (T.sort (· ≤ ·))
  rw [Finset.length_sort, Finset.length_sort] at h
  have e : toVal (S ∪ T) = toVal (unionL (S.sort (· ≤ ·)) (T.sort (· ≤ ·))) :=
    toVal_finset_of_sorted (sorted_unionL _ _ (sorted_sort S) (sorted_sort T))
      (fun a => by simp [mem_unionL])
  rw [e]; exact h

theorem inter_runs (S T : Finset ℕ) :
    Runs Δ' B fInterS [toVal S, toVal T] (toVal (S ∩ T)) (60 * (S.card + T.card) + 20) := by
  have h := interL_runs hΔ B (S.sort (· ≤ ·)) (T.sort (· ≤ ·))
  rw [Finset.length_sort, Finset.length_sort] at h
  have e : toVal (S ∩ T) = toVal (interL (S.sort (· ≤ ·)) (T.sort (· ≤ ·))) :=
    toVal_finset_of_sorted ((sorted_sort S).sublist (interL_sublist _ _))
      (fun a => by simp [mem_interL _ _ (sorted_sort S) (sorted_sort T)])
  rw [e]; exact h

theorem sdiff_runs (S T : Finset ℕ) :
    Runs Δ' B fDiffS [toVal S, toVal T] (toVal (S \ T)) (60 * (S.card + T.card) + 20) := by
  have h := diffL_runs hΔ B (S.sort (· ≤ ·)) (T.sort (· ≤ ·))
  rw [Finset.length_sort, Finset.length_sort] at h
  have e : toVal (S \ T) = toVal (diffL (S.sort (· ≤ ·)) (T.sort (· ≤ ·))) :=
    toVal_finset_of_sorted ((sorted_sort S).sublist (diffL_sublist _ _))
      (fun a => by simp [mem_diffL _ _ (sorted_sort S) (sorted_sort T)])
  rw [e]; exact h

theorem subset_runs (hB : 1 < B) (S T : Finset ℕ) (b : Bool) (hb : b = true ↔ S ⊆ T) :
    Runs Δ' B fSubsetS [toVal S, toVal T] (toVal b) (60 * (S.card + T.card) + 20) := by
  have h := subsetL_runs hΔ B hB (S.sort (· ≤ ·)) (T.sort (· ≤ ·))
  rw [Finset.length_sort, Finset.length_sort] at h
  have e : subsetL (S.sort (· ≤ ·)) (T.sort (· ≤ ·)) = b := by
    have h1 := subsetL_iff _ _ (sorted_sort S) (sorted_sort T)
    simp only [toVal_sort_mem] at h1
    exact Bool.eq_iff_iff.mpr (h1.trans (by rw [hb, Finset.subset_iff]))
  rw [e] at h; exact h

theorem insert_runs (a : ℕ) (S : Finset ℕ) :
    Runs Δ' B fInsertS [toVal a, toVal S] (toVal (insert a S)) (40 * S.card + 20) := by
  have h := insertL_runs hΔ B a (S.sort (· ≤ ·))
  rw [Finset.length_sort] at h
  have e : toVal (insert a S) = toVal (insertL a (S.sort (· ≤ ·))) :=
    toVal_finset_of_sorted (sorted_insertL _ _ (sorted_sort S))
      (fun b => by simp [mem_insertL])
  rw [e]; exact h

theorem erase_runs (a : ℕ) (S : Finset ℕ) :
    Runs Δ' B fEraseS [toVal a, toVal S] (toVal (S.erase a)) (40 * S.card + 20) := by
  have h := eraseL_runs hΔ B a (S.sort (· ≤ ·))
  rw [Finset.length_sort] at h
  have e : toVal (S.erase a) = toVal (eraseL a (S.sort (· ≤ ·))) :=
    toVal_finset_of_sorted ((sorted_sort S).sublist (eraseL_sublist _ _))
      (fun b => by simp [mem_eraseL _ _ (sorted_sort S), and_comm])
  rw [e]; exact h

end proofs2

end Lib3
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.Lib4` -/

section
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

end
