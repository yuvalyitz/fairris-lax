import Lax117284Proofs.Treewidth.Fun.LibEmbeds
import Lax117284Proofs.Treewidth.Seq.Stack
import Lax117284Proofs.Treewidth.Seq.Dom

/-!
# WP E1 (layer A): the typical-sequence stack algorithm and `domB` as F-functions

Ids `128 …`.  `inR`, `allInR`, `cut`, `push`, `typical`, `domB` (the lattice-path recursion, exponential in the length
exactly as the Lean function).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E1A

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq

abbrev fInR : ℕ := 128
abbrev fAllInR : ℕ := 129
abbrev fCut : ℕ := 130
abbrev fPush : ℕ := 131
abbrev fPushC : ℕ := 132
abbrev fTypAux : ℕ := 133
abbrev fTypical : ℕ := 134
abbrev fDomB : ℕ := 135
abbrev fDomBP : ℕ := 136

/-- `a ≤ b` as a term (`1 - (b < a)`); no natural above `1` is produced. -/
abbrev leT (a b : Tm) : Tm := .sub (.lit 1) (.lt b a)

/-- `inR z x y` : `z` lies between `x` and `y` -/
def inRTm : Tm :=
  .ite (.lt (V 1) (V 2))
    (.ite (leT (V 1) (V 0)) (leT (V 0) (V 2)) (.lit 0))
    (.ite (leT (V 2) (V 0)) (leT (V 0) (V 1)) (.lit 0))

/-- `allInR l x y` : every entry of `l` lies between `x` and `y` -/
def allInRTm : Tm :=
  .ite (.isNat (V 0)) (.lit 1)
    (.ite (.call fInR [.fst (V 0), V 1, V 2]) (.call fAllInR [.snd (V 0), V 1, V 2]) (.lit 0))

/-- `Seq.cut t y` -/
def cutTm : Tm :=
  .ite (.isNat (V 0)) (V 0)
    (.ite (.call fAllInR [.snd (V 0), .fst (V 0), V 1])
      (.ite (.isNat (.snd (V 0))) (.ite (.eq (.fst (V 0)) (V 1)) (.lit 0) (.cons (.fst (V 0)) (.lit 0)))
        (.cons (.fst (V 0)) (.lit 0)))
      (.cons (.fst (V 0)) (.call fCut [.snd (V 0), V 1])))

/-- `Seq.push t y` -/
def pushTm : Tm := .call fAppend [.call fCut [V 0, V 1], .cons (V 1) (.lit 0)]

/-- `push` with a (dummy) context, the calling convention of `foldl` -/
def pushCTm : Tm := .call fPush [V 1, V 2]

/-- `typAux acc l = l.foldl push acc` -/
def typAuxTm : Tm :=
  .ite (.isNat (V 1)) (V 0) (.call fTypAux [.call fPush [V 0, .fst (V 1)], .snd (V 1)])

/-- `Seq.typical a` -/
def typicalTm : Tm := .call fTypAux [.lit 0, V 0]

/-- `Seq.domB a b` (lazy `||`, so the cost is that of the Lean recursion) -/
def domBRest : Tm :=
  .ite (.call fDomB [.snd (V 0), V 1]) (.lit 1)
    (.ite (.call fDomB [V 0, .snd (V 1)]) (.lit 1) (.call fDomB [.snd (V 0), .snd (V 1)]))

def domBTm : Tm :=
  .ite (.isNat (V 0)) (.ite (.isNat (V 1)) (.lit 1) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (leT (.fst (V 0)) (.fst (V 1)))
        (.ite (.mul (.isNat (.snd (V 0))) (.isNat (.snd (V 1)))) (.lit 1) domBRest)
        (.lit 0)))

/-- `domB` on a pair (the unary calling convention of `Embeds`) -/
def domBPTm : Tm := .call fDomB [.fst (V 0), .snd (V 0)]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 128 => some inRTm | 129 => some allInRTm | 130 => some cutTm | 131 => some pushTm
  | 132 => some pushCTm | 133 => some typAuxTm | 134 => some typicalTm | 135 => some domBTm | 136 => some domBPTm | _ => none

/-- layer A of the E1 table -/
def Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 tbl

abbrev size : ℕ := 137

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 137 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h128 : 128 ≤ f := by omega
    simp only [h128, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extLib : Lib.Δ ⊑ Δ := Ext.layer tbl (fun f b h => Lib.Δ_lt h)

theorem Δ_inR : Δ fInR = some inRTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fInR by decide)]; rfl
theorem Δ_allInR : Δ fAllInR = some allInRTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fAllInR by decide)]; rfl
theorem Δ_cut : Δ fCut = some cutTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fCut by decide)]; rfl
theorem Δ_push : Δ fPush = some pushTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fPush by decide)]; rfl
theorem Δ_typAux : Δ fTypAux = some typAuxTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fTypAux by decide)]; rfl
theorem Δ_typical : Δ fTypical = some typicalTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fTypical by decide)]; rfl
theorem Δ_domB : Δ fDomB = some domBTm := by simp [Δ, layerΔ_ge tbl (show 128 ≤ fDomB by decide)]; rfl

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem inR_runs (hB : 1 < B) (z x y : ℕ) :
    Runs Δ' B fInR [toVal z, toVal x, toVal y] (toVal (decide (InR z x y))) 40 := by
  refine Runs.mk (hΔ _ _ Δ_inR) ?_
  by_cases hxy : x < y <;> by_cases h1 : z < x <;> by_cases h2 : y < z <;>
    by_cases h3 : z < y <;> by_cases h4 : x < z <;>
    rcases (by tauto : InR z x y ∨ ¬ InR z x y) with hI | hI <;>
    first
    | (exfalso; omega)
    | (exfalso; unfold InR at hI; omega)
    | (simp only [hI, decide_true, decide_false]
       ev_start
       · ev_run
       · omega)

theorem allInR_runs (hB : 1 < B) (x y : ℕ) (l : List ℕ) :
    Runs Δ' B fAllInR [toVal l, toVal x, toVal y] (toVal (l.all (fun z => decide (InR z x y))))
      (60 * l.length + 6) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_allInR) ?_
    ev_start
    · ev_run
    · simp
  | cons z l ih =>
    have h1 := inR_runs hΔ B hB z x y
    refine Runs.mk (hΔ _ _ Δ_allInR) ?_
    by_cases hz : InR z x y
    · simp only [hz, decide_true] at h1
      simp only [List.all_cons, hz, decide_true, Bool.true_and]
      ev_start
      · ev_run
      · simp only [List.length_cons]; omega
    · simp only [hz, decide_false] at h1
      simp only [List.all_cons, hz, decide_false, Bool.false_and]
      ev_start
      · ev_run
      · simp only [List.length_cons]; omega

omit hΔ in
theorem length_cut_le : ∀ (t : List ℕ) (y : ℕ), (cut t y).length ≤ t.length
  | [], _ => by simp [cut]
  | x :: t, y => by
    unfold cut
    split_ifs with h1 h2
    · simp
    · simp
    · have := length_cut_le t y
      simp only [List.length_cons]; omega

theorem cut_runs (hB : 1 < B) (y : ℕ) (t : List ℕ) :
    Runs Δ' B fCut [toVal t, toVal y] (toVal (cut t y)) (60 * (t.length + 1) ^ 2) := by
  induction t with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_cut) ?_
    ev_start
    · ev_run
    · simp [cut]
  | cons x t ih =>
    have h1 := allInR_runs hΔ B hB x y t
    refine Runs.mk (hΔ _ _ Δ_cut) ?_
    by_cases hall : ∀ z ∈ t, InR z x y
    · have hall' : t.all (fun z => decide (InR z x y)) = true := by simpa using hall
      simp only [hall'] at h1
      by_cases hc : t = [] ∧ x = y
      · obtain ⟨rfl, rfl⟩ := hc
        have hcut : cut [x] x = [] := by simp [cut]
        rw [hcut]
        ev_start
        · ev_run
        · simp
      · have hc' : ¬ (t = [] ∧ x = y) := hc
        have hcut : cut (x :: t) y = [x] := by
          simp only [cut]; rw [if_pos hall, if_neg hc']
        rw [hcut]
        by_cases ht : t = []
        · subst ht
          have hxy : ¬ x = y := fun h => hc ⟨rfl, h⟩
          ev_start
          · ev_run
          · simp
        · obtain ⟨w, t', rfl⟩ := List.exists_cons_of_ne_nil ht
          ev_start
          · ev_run
          · simp only [List.length_cons]; nlinarith [Nat.zero_le t'.length]
    · have hall' : t.all (fun z => decide (InR z x y)) = false := by
        simpa using hall
      simp only [hall'] at h1
      have hcut : cut (x :: t) y = x :: cut t y := by
        simp only [cut]; rw [if_neg hall]
      rw [hcut]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le t.length]

theorem ext1' : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans extLib hΔ)

theorem push_runs (hB : 1 < B) (y : ℕ) (t : List ℕ) :
    Runs Δ' B fPush [toVal t, toVal y] (toVal (push t y)) (80 * (t.length + 1) ^ 2) := by
  have h1 := cut_runs hΔ B hB y t
  have h2 := append_runs (ext1' hΔ) B (cut t y) [y]
  have hl := length_cut_le t y
  refine Runs.mk (hΔ _ _ Δ_push) ?_
  show EvLe Δ' B _ pushTm (toVal (cut t y ++ [y])) _
  ev_start
  · ev_run
  · nlinarith [Nat.zero_le t.length]

theorem typAux_runs (hB : 1 < B) : ∀ (l acc : List ℕ) (k : ℕ), acc.length ≤ k →
    Runs Δ' B fTypAux [toVal acc, toVal l] (toVal (l.foldl push acc))
      (100 * (l.length + 1) * (k + l.length + 1) ^ 2) := by
  intro l
  induction l with
  | nil =>
    intro acc k _
    refine Runs.mk (hΔ _ _ Δ_typAux) ?_
    ev_start
    · ev_run
    · simp only [List.length_nil]; nlinarith [Nat.zero_le k]
  | cons y l ih =>
    intro acc k hk
    have h1 := push_runs hΔ B hB y acc
    have hl : (push acc y).length ≤ acc.length + 1 := by
      simp only [push, List.length_append, List.length_singleton]
      have := length_cut_le acc y; omega
    have h2 := ih (push acc y) (k + 1) (by omega)
    refine Runs.mk (hΔ _ _ Δ_typAux) ?_
    simp only [List.foldl_cons]
    ev_start
    · ev_run
    · simp only [List.length_cons]
      have h3 : (acc.length + 1) ^ 2 ≤ (k + (l.length + 1) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h4 : (k + 1 + l.length + 1) = (k + (l.length + 1) + 1) := by omega
      rw [h4] at h2
      nlinarith [Nat.zero_le l.length, Nat.zero_le k, Nat.zero_le (l.length * (k + (l.length + 1) + 1) ^ 2)]

theorem typical_runs (hB : 1 < B) (a : List ℕ) :
    Runs Δ' B fTypical [toVal a] (toVal (typical a)) (110 * (a.length + 1) ^ 3) := by
  have h := typAux_runs hΔ B hB a [] 0 (by simp)
  refine Runs.mk (hΔ _ _ Δ_typical) ?_
  ev_start
  · ev_run
  · simp only [zero_add] at h
    nlinarith [Nat.zero_le a.length]

theorem domBRest_ev (hB : 1 < B) (x y : ℕ) (a b : List ℕ) (dA dB dC : Bool) (cA cB cC : ℕ)
    (hA : Runs Δ' B fDomB [toVal a, toVal (y :: b)] (toVal dA) cA)
    (hB' : Runs Δ' B fDomB [toVal (x :: a), toVal b] (toVal dB) cB)
    (hC : Runs Δ' B fDomB [toVal a, toVal b] (toVal dC) cC) :
    EvLe Δ' B [toVal (x :: a), toVal (y :: b)] domBRest (toVal (dA || dB || dC))
      (cA + cB + cC + 20) := by
  cases dA <;> cases dB <;> cases dC <;>
  · simp only [Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or] at *
    unfold domBRest
    ev_start
    · ev_run
    · omega

theorem domB_runs (hB : 1 < B) : ∀ (n : ℕ) (a b : List ℕ), a.length + b.length = n →
    Runs Δ' B fDomB [toVal a, toVal b] (toVal (domB a b)) (60 * 3 ^ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn
    have hp : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by omega)
    refine Runs.mk (hΔ _ _ Δ_domB) ?_
    cases a with
    | nil =>
      cases b with
      | nil =>
        simp only [domB]
        ev_start
        · ev_run
        · omega
      | cons y b =>
        simp only [domB]
        ev_start
        · ev_run
        · omega
    | cons x a =>
      cases b with
      | nil =>
        simp only [domB]
        ev_start
        · ev_run
        · omega
      | cons y b =>
        simp only [List.length_cons] at hn
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨a.length + b.length, by omega⟩
        have hA := ih (m + 1) (by omega) a (y :: b) (by simp; omega)
        have hB' := ih (m + 1) (by omega) (x :: a) b (by simp; omega)
        have hC := ih m (by omega) a b (by omega)
        have hpm : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by omega)
        have e1 : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ]; ring
        have e2 : 3 ^ (m + 2) = 9 * 3 ^ m := by rw [pow_succ, pow_succ]; ring
        rw [e1] at hA hB'
        rw [e2]
        have hrest := domBRest_ev hΔ B hB x y a b _ _ _ _ _ _ hA hB' hC
        clear ih hA hB' hC
        by_cases hxy : x ≤ y
        · have hxy' : ¬ y < x := by omega
          rw [domB_cons_cons]
          by_cases hab : a = [] ∧ b = []
          · obtain ⟨rfl, rfl⟩ := hab
            simp only [hxy, decide_true, List.isEmpty_nil, Bool.and_self, Bool.true_or, Bool.true_and]
            ev_start
            · ev_run
            · omega
          · have hab' : (a.isEmpty && b.isEmpty) = false := by
              cases a <;> cases b <;> simp_all
            simp only [hxy, decide_true, hab', Bool.false_or, Bool.true_and]
            rcases a with _ | ⟨w, a'⟩ <;> rcases b with _ | ⟨u, b'⟩
            · exact absurd ⟨rfl, rfl⟩ hab
            all_goals
              ev_start
              · ev_run
                all_goals first | exact hrest | skip
              · omega
        · have hxy' : y < x := by omega
          simp only [domB_cons_cons, hxy, decide_false, Bool.false_and]
          ev_start
          · ev_run
          · omega

end proofs
end E1A
end Lax117284Proofs.Treewidth.Fun
