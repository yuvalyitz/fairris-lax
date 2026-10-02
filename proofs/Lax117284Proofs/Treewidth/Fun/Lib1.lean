import Lax117284Proofs.Treewidth.Fun.Kit
import Mathlib.Tactic.Linarith

/-!
# WP F1, layer 1: first-order list combinators as F-functions

Function ids `0 … 63` are reserved for the library (layer 1: `0 … 31`).  Every function is a `Tm` body over the
argument list (de Bruijn: `var 0` is the first argument).  Lemmas are stated for every table `Δ` extending
`Lib1.Δ` (`Lib1.Δ ⊑ Δ`).  Costs are upper bounds on the number of constructs evaluated by the *body*
(the `Runs` convention).  Naturals produced must be `< B`; the hypotheses say how large `B` must be.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace Lib1

open ToVal

/-- variable `i` -/
abbrev V (i : ℕ) : Tm := .var i

abbrev fAppend : ℕ := 0
abbrev fLength : ℕ := 1
abbrev fNth : ℕ := 2
abbrev fTake : ℕ := 3
abbrev fDrop : ℕ := 4
abbrev fMap : ℕ := 5
abbrev fFilter : ℕ := 6
abbrev fFoldl : ℕ := 7
abbrev fFlatMap : ℕ := 8
abbrev fAny : ℕ := 9
abbrev fAll : ℕ := 10
abbrev fRangeAux : ℕ := 11
abbrev fRange : ℕ := 12
abbrev fZip : ℕ := 13
abbrev fEqV : ℕ := 14
abbrev fMem : ℕ := 15
abbrev fMin : ℕ := 16
abbrev fMax : ℕ := 17

/-- `append xs ys` -/
def appendTm : Tm := .ite (.isNat (V 0)) (V 1) (.cons (.fst (V 0)) (.call fAppend [.snd (V 0), V 1]))
/-- `length xs` -/
def lengthTm : Tm := .ite (.isNat (V 0)) (.lit 0) (.add (.call fLength [.snd (V 0)]) (.lit 1))
/-- `nth xs i` (`nat 0` when out of range) -/
def nthTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.eq (V 1) (.lit 0)) (.fst (V 0)) (.call fNth [.snd (V 0), .sub (V 1) (.lit 1)]))
/-- `take n xs` -/
def takeTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (.lit 0) (.cons (.fst (V 1)) (.call fTake [.sub (V 0) (.lit 1), .snd (V 1)])))
/-- `drop n xs` -/
def dropTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (V 1) (.call fDrop [.sub (V 0) (.lit 1), .snd (V 1)]))
/-- `map f ctx xs`: calls `f ctx x` -/
def mapTm : Tm :=
  .ite (.isNat (V 2)) (V 2) (.cons (.callv (V 0) [V 1, .fst (V 2)]) (.call fMap [V 0, V 1, .snd (V 2)]))
/-- `filter f ctx xs`: keeps `x` with `f ctx x ≠ 0` -/
def filterTm : Tm :=
  .ite (.isNat (V 2)) (V 2)
    (.ite (.callv (V 0) [V 1, .fst (V 2)]) (.cons (.fst (V 2)) (.call fFilter [V 0, V 1, .snd (V 2)]))
      (.call fFilter [V 0, V 1, .snd (V 2)]))
/-- `foldl f ctx acc xs`: `acc := f ctx acc x` -/
def foldlTm : Tm :=
  .ite (.isNat (V 3)) (V 2)
    (.call fFoldl [V 0, V 1, .callv (V 0) [V 1, V 2, .fst (V 3)], .snd (V 3)])
/-- `flatMap f ctx xs` -/
def flatMapTm : Tm :=
  .ite (.isNat (V 2)) (V 2)
    (.call fAppend [.callv (V 0) [V 1, .fst (V 2)], .call fFlatMap [V 0, V 1, .snd (V 2)]])
/-- `any f ctx xs` -/
def anyTm : Tm :=
  .ite (.isNat (V 2)) (.lit 0)
    (.ite (.callv (V 0) [V 1, .fst (V 2)]) (.lit 1) (.call fAny [V 0, V 1, .snd (V 2)]))
/-- `all f ctx xs` -/
def allTm : Tm :=
  .ite (.isNat (V 2)) (.lit 1)
    (.ite (.callv (V 0) [V 1, .fst (V 2)]) (.call fAll [V 0, V 1, .snd (V 2)]) (.lit 0))
/-- `rangeAux i n = [i, …, n-1]` -/
def rangeAuxTm : Tm :=
  .ite (.lt (V 0) (V 1)) (.cons (V 0) (.call fRangeAux [.add (V 0) (.lit 1), V 1])) (.lit 0)
/-- `range n = [0, …, n-1]` -/
def rangeTm : Tm := .call fRangeAux [.lit 0, V 0]
/-- `zip xs ys` -/
def zipTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.ite (.isNat (V 1)) (V 1) (.cons (.cons (.fst (V 0)) (.fst (V 1))) (.call fZip [.snd (V 0), .snd (V 1)])))
/-- structural equality `eqV u v` (`nat 1` / `nat 0`) -/
def eqVTm : Tm :=
  .ite (.isNat (V 0)) (.ite (.isNat (V 1)) (.eq (V 0) (V 1)) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.call fEqV [.fst (V 0), .fst (V 1)]) (.call fEqV [.snd (V 0), .snd (V 1)]) (.lit 0)))
/-- `mem a xs` by structural equality -/
def memTm : Tm :=
  .ite (.isNat (V 1)) (.lit 0)
    (.ite (.call fEqV [V 0, .fst (V 1)]) (.lit 1) (.call fMem [V 0, .snd (V 1)]))
def minTm : Tm := .ite (.lt (V 0) (V 1)) (V 0) (V 1)
def maxTm : Tm := .ite (.lt (V 0) (V 1)) (V 1) (V 0)

/-- The layer-1 function table. -/
def Δ : ℕ → Option Tm := fun f =>
  match f with
  | 0 => some appendTm | 1 => some lengthTm | 2 => some nthTm | 3 => some takeTm | 4 => some dropTm
  | 5 => some mapTm | 6 => some filterTm | 7 => some foldlTm | 8 => some flatMapTm | 9 => some anyTm
  | 10 => some allTm | 11 => some rangeAuxTm | 12 => some rangeTm | 13 => some zipTm | 14 => some eqVTm
  | 15 => some memTm | 16 => some minTm | 17 => some maxTm
  | _ => none

/-- the layer occupies exactly the ids below `size`. -/
abbrev size : ℕ := 18

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 18 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ; split <;> first | rfl | omega
  rw [this] at h; cases h

variable {Δ' : ℕ → Option Tm}

theorem Δ_append : Δ fAppend = some appendTm := rfl
theorem Δ_length : Δ fLength = some lengthTm := rfl
theorem Δ_nth : Δ fNth = some nthTm := rfl
theorem Δ_take : Δ fTake = some takeTm := rfl
theorem Δ_drop : Δ fDrop = some dropTm := rfl
theorem Δ_map : Δ fMap = some mapTm := rfl
theorem Δ_filter : Δ fFilter = some filterTm := rfl
theorem Δ_foldl : Δ fFoldl = some foldlTm := rfl
theorem Δ_flatMap : Δ fFlatMap = some flatMapTm := rfl
theorem Δ_all : Δ fAll = some allTm := rfl
theorem Δ_rangeAux : Δ fRangeAux = some rangeAuxTm := rfl
theorem Δ_range : Δ fRange = some rangeTm := rfl
theorem Δ_eqV : Δ fEqV = some eqVTm := rfl
theorem Δ_mem : Δ fMem = some memTm := rfl
theorem Δ_max : Δ fMax = some maxTm := rfl

/-- total cost of the calls made by a left fold. -/
def foldCost {α β : Type} (g : β → α → β) (cf : β → α → ℕ) : β → List α → ℕ
  | _, [] => 0
  | b, a :: l => cf b a + foldCost g cf (g b a) l

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ) {α β : Type} [ToVal α] [ToVal β]
include hΔ

theorem append_runs (xs ys : List α) :
    Runs Δ' B fAppend [toVal xs, toVal ys] (toVal (xs ++ ys)) (10 * xs.length + 4) := by
  induction xs with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_append) ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk (hΔ _ _ Δ_append) ?_
    ev_start
    · ev_run
    · simp; omega

theorem length_runs (xs : List α) (hB : 8 * xs.length + 8 < B) :
    Runs Δ' B fLength [toVal xs] (toVal xs.length) (8 * xs.length + 5) := by
  induction xs with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_length) ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    simp only [List.length_cons] at hB
    have ih := ih (by omega)
    refine Runs.mk (hΔ _ _ Δ_length) ?_
    ev_start
    · ev_run
    · simp; omega

theorem take_runs (n : ℕ) (xs : List α) (hB : 1 < B) :
    Runs Δ' B fTake [toVal n, toVal xs] (toVal (xs.take n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_take) ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk (hΔ _ _ Δ_take) ?_
    cases n with
    | zero =>
      ev_start
      · ev_run
      · simp
    | succ n =>
      have ih := ih n
      ev_start
      · ev_run
      · simp; omega

theorem drop_runs (n : ℕ) (xs : List α) (hB : 1 < B) :
    Runs Δ' B fDrop [toVal n, toVal xs] (toVal (xs.drop n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_drop) ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk (hΔ _ _ Δ_drop) ?_
    cases n with
    | zero =>
      ev_start
      · ev_run
      · simp
    | succ n =>
      have ih := ih n
      ev_start
      · ev_run
      · simp; omega

theorem map_runs (fid : ℕ) (ctx : Val) (g : α → β) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (g a)) (cf a)) :
    Runs Δ' B fMap [.nat fid, ctx, toVal l] (toVal (l.map g)) (20 * l.length + 6 + (l.map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_map) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf a (List.mem_cons_self ..)
    refine Runs.mk (hΔ _ _ Δ_map) ?_
    ev_start
    · ev_run
    · simp; omega

theorem filter_runs (fid : ℕ) (ctx : Val) (p : α → Bool) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (p a)) (cf a)) :
    Runs Δ' B fFilter [.nat fid, ctx, toVal l] (toVal (l.filter p)) (24 * l.length + 6 + (l.map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_filter) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf a (List.mem_cons_self ..)
    refine Runs.mk (hΔ _ _ Δ_filter) ?_
    rcases Bool.eq_false_or_eq_true (p a) with hp | hp
    · simp only [hp] at h1
      simp only [List.filter_cons, hp, if_true]
      ev_start
      · ev_run
      · simp; omega
    · simp only [hp] at h1
      simp only [List.filter_cons, hp]
      ev_start
      · ev_run
      · simp; omega

theorem foldl_runs (fid : ℕ) (ctx : Val) (g : β → α → β) (cf : β → α → ℕ) (P : β → Prop) (b : β)
    (l : List α) (hP : P b) (hstep : ∀ b' a, P b' → a ∈ l → P (g b' a))
    (hf : ∀ b' a, P b' → a ∈ l → Runs Δ' B fid [ctx, toVal b', toVal a] (toVal (g b' a)) (cf b' a)) :
    Runs Δ' B fFoldl [.nat fid, ctx, toVal b, toVal l] (toVal (l.foldl g b))
      (18 * l.length + 6 + foldCost g cf b l) := by
  induction l generalizing b with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_foldl) ?_
    ev_start
    · ev_run
    · simp [foldCost]
  | cons a l ih =>
    have h1 := hf b a hP (List.mem_cons_self ..)
    have ih := ih (g b a) (hstep b a hP (List.mem_cons_self ..))
      (fun b' x hb hx => hstep b' x hb (List.mem_cons_of_mem _ hx))
      (fun b' x hb hx => hf b' x hb (List.mem_cons_of_mem _ hx))
    refine Runs.mk (hΔ _ _ Δ_foldl) ?_
    ev_start
    · ev_run
    · simp [foldCost]; omega

theorem flatMap_runs (fid : ℕ) (ctx : Val) (g : α → List β) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (g a)) (cf a)) :
    Runs Δ' B fFlatMap [.nat fid, ctx, toVal l] (toVal (l.flatMap g))
      ((l.map (fun a => cf a + 10 * (g a).length + 20)).sum + 8) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_flatMap) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf a (List.mem_cons_self ..)
    have h2 := append_runs hΔ B (g a) (l.flatMap g)
    refine Runs.mk (hΔ _ _ Δ_flatMap) ?_
    ev_start
    · ev_run
    · simp; omega

theorem all_runs (fid : ℕ) (ctx : Val) (p : α → Bool) (cf : α → ℕ) (l : List α)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (p a)) (cf a)) (hB : 1 < B) :
    Runs Δ' B fAll [.nat fid, ctx, toVal l] (toVal (l.all p)) (24 * l.length + 6 + (l.map cf).sum) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_all) ?_
    ev_start
    · ev_run
    · simp
  | cons a l ih =>
    have ih := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf a (List.mem_cons_self ..)
    refine Runs.mk (hΔ _ _ Δ_all) ?_
    rcases Bool.eq_false_or_eq_true (p a) with hp | hp
    · simp only [hp] at h1
      simp only [List.all_cons, hp, Bool.true_and]
      ev_start
      · ev_run
      · simp; omega
    · simp only [hp] at h1
      simp only [List.all_cons, hp, Bool.false_and]
      ev_start
      · ev_run
      · simp; omega

theorem rangeAux_runs (k : ℕ) : ∀ (i : ℕ), i + k + 2 < B →
    Runs Δ' B fRangeAux [toVal i, toVal (i + k)] (toVal (List.range' i k)) (24 * k + 10) := by
  induction k with
  | zero =>
    intro i hB
    refine Runs.mk (hΔ _ _ Δ_rangeAux) ?_
    ev_start
    · ev_run
    · simp
  | succ k ih =>
    intro i hB
    have ih := ih (i + 1) (by omega)
    rw [show i + 1 + k = i + (k + 1) by omega] at ih
    refine Runs.mk (hΔ _ _ Δ_rangeAux) ?_
    rw [List.range'_succ]
    ev_start
    · ev_run
    · simp; omega

theorem range_runs (n : ℕ) (hB : n + 2 < B) :
    Runs Δ' B fRange [toVal n] (toVal (List.range n)) (24 * n + 16) := by
  have h := rangeAux_runs hΔ B n 0 (by omega)
  simp only [Nat.zero_add] at h
  rw [List.range_eq_range']
  refine Runs.mk (hΔ _ _ Δ_range) ?_
  ev_start
  · ev_run
  · omega

theorem max_runs (a b : ℕ) : Runs Δ' B fMax [toVal a, toVal b] (toVal (max a b)) 8 := by
  refine Runs.mk (hΔ _ _ Δ_max) ?_
  by_cases h : a < b
  · have : max a b = b := max_eq_right h.le
    rw [this]
    ev_start
    · ev_run
    · simp
  · have : max a b = a := max_eq_left (by omega)
    rw [this]
    ev_start
    · ev_run
    · simp

/-- structural equality of values, for any Boolean `b` recording the answer. -/
theorem eqV_runs (hB : 1 < B) (u : Val) : ∀ (v : Val) (b : Bool), (b = true ↔ u = v) →
    Runs Δ' B fEqV [u, v] (toVal b) (30 * min u.size v.size) := by
  induction u with
  | nat m =>
    intro v b hb
    refine Runs.mk (hΔ _ _ Δ_eqV) ?_
    cases v with
    | nat n =>
      cases b with
      | true =>
        have : m = n := by simpa using hb.1 rfl
        subst this
        ev_start
        · ev_run
        · simp [Val.size]
      | false =>
        have : m ≠ n := fun h => by simpa using hb.2 (by rw [h])
        ev_start
        · ev_run
        · simp [Val.size]
    | cons c d =>
      cases b with
      | true => exact absurd (hb.1 rfl) (by simp)
      | false =>
        ev_start
        · ev_run
        · simp [Val.size]
  | cons a b iha ihb =>
    intro v bb hb
    refine Runs.mk (hΔ _ _ Δ_eqV) ?_
    cases v with
    | nat n =>
      cases bb with
      | true => exact absurd (hb.1 rfl) (by simp)
      | false =>
        ev_start
        · ev_run
        · simp [Val.size]
    | cons c d =>
      classical
      by_cases hac : a = c
      · subst hac
        have h1 := iha a true (by simp)
        have h2 := ihb d bb (by simpa using hb)
        ev_start
        · ev_run
        · simp [Val.size]; omega
      · have hbb : bb = false := by
          cases bb
          · rfl
          · exact absurd (Val.cons.inj (hb.1 rfl)).1 hac
        subst hbb
        have h1 := iha c false (by simpa using hac)
        ev_start
        · ev_run
        · simp [Val.size]; omega

theorem eqV_runs_typed (hB : 1 < B) (a b : α) (bb : Bool) (hb : bb = true ↔ a = b) :
    Runs Δ' B fEqV [toVal a, toVal b] (toVal bb) (30 * min (sz a) (sz b)) :=
  eqV_runs hΔ B hB (toVal a) (toVal b) bb (by rw [hb]; exact ⟨fun h => h ▸ rfl, fun h => ToVal.inj h⟩)

theorem mem_runs (hB : 1 < B) (a : α) (l : List α) (b : Bool) (hb : b = true ↔ a ∈ l) :
    Runs Δ' B fMem [toVal a, toVal l] (toVal b) ((30 * sz a + 24) * (l.length + 1) + 8) := by
  induction l generalizing b with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_mem) ?_
    have : b = false := by cases b <;> simp_all
    subst this
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    refine Runs.mk (hΔ _ _ Δ_mem) ?_
    by_cases hax : a = x
    · subst hax
      have h1 := eqV_runs_typed hΔ B hB a a true (by simp)
      have : b = true := hb.2 (by simp)
      subst this
      ev_start
      · ev_run
      · simp only [List.length_cons]
        have := min_le_left (sz a) (sz a)
        nlinarith
    · have h1 := eqV_runs_typed hΔ B hB a x false (by simpa using hax)
      have ih := ih b (by simpa [hax] using hb)
      ev_start
      · ev_run
      · simp only [List.length_cons]
        have := min_le_left (sz a) (sz x)
        nlinarith

end proofs

end Lib1
end Lax117284Proofs.Treewidth.Fun
