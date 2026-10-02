import Lax117284Proofs.Treewidth.Fun.E1Seq
import Lax117284Proofs.Treewidth.Chars.Alg

/-!
# WP E1 (layer B): `witnesses` (the witness positions of the typical sequence)

Ids `137 …`: `allInRP`, `wpush`, `witnessesAux`, `sndF`, `witnesses`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E1B

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars E1A

abbrev fAllInRP : ℕ := 137
abbrev fWpush : ℕ := 138
abbrev fWitAux : ℕ := 139
abbrev fSndF : ℕ := 140
abbrev fWitnesses : ℕ := 141

/-- `allInRP l x y`: the first components of the pairs of `l` all lie between `x` and `y` -/
def allInRPTm : Tm :=
  .ite (.isNat (V 0)) (.lit 1)
    (.ite (.call fInR [.fst (.fst (V 0)), V 1, V 2]) (.call fAllInRP [.snd (V 0), V 1, V 2]) (.lit 0))

/-- `wpush st y j` -/
def wpushTm : Tm :=
  .ite (.isNat (V 0)) (.cons (.cons (V 1) (V 2)) (.lit 0))
    (.ite (.call fAllInRP [.snd (V 0), .fst (.fst (V 0)), V 1])
      (.ite (.mul (.isNat (.snd (V 0))) (.eq (.fst (.fst (V 0))) (V 1)))
        (.cons (.fst (V 0)) (.lit 0))
        (.cons (.fst (V 0)) (.cons (.cons (V 1) (V 2)) (.lit 0))))
      (.cons (.fst (V 0)) (.call fWpush [.snd (V 0), V 1, V 2])))

/-- `witnessesAux j st l` -/
def witAuxTm : Tm :=
  .ite (.isNat (V 2)) (V 1)
    (.call fWitAux [.add (V 0) (.lit 1), .call fWpush [V 1, .fst (V 2), V 0], .snd (V 2)])

/-- `map snd` step -/
def sndFTm : Tm := .snd (V 1)

/-- `witnesses a` -/
def witnessesTm : Tm :=
  .call fMap [.lit fSndF, .lit 0, .call fWitAux [.lit 0, .lit 0, V 0]]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 137 => some allInRPTm | 138 => some wpushTm | 139 => some witAuxTm | 140 => some sndFTm
  | 141 => some witnessesTm | _ => none

/-- layer B of the E1 table -/
def Δ : ℕ → Option Tm := layerΔ E1A.Δ 137 tbl

abbrev size : ℕ := 142

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 142 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h137 : 137 ≤ f := by omega
    simp only [h137, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extA : E1A.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E1A.Δ_lt h; simp [E1A.size] at this; omega)
theorem extLib : Lib.Δ ⊑ Δ := Ext.trans E1A.extLib extA

theorem Δ_allInRP : Δ fAllInRP = some allInRPTm := by simp [Δ, layerΔ_ge tbl (show 137 ≤ fAllInRP by decide)]; rfl
theorem Δ_wpush : Δ fWpush = some wpushTm := by simp [Δ, layerΔ_ge tbl (show 137 ≤ fWpush by decide)]; rfl
theorem Δ_witAux : Δ fWitAux = some witAuxTm := by simp [Δ, layerΔ_ge tbl (show 137 ≤ fWitAux by decide)]; rfl
theorem Δ_sndF : Δ fSndF = some sndFTm := by simp [Δ, layerΔ_ge tbl (show 137 ≤ fSndF by decide)]; rfl
theorem Δ_witnesses : Δ fWitnesses = some witnessesTm := by
  simp [Δ, layerΔ_ge tbl (show 137 ≤ fWitnesses by decide)]; rfl

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem allInRP_runs (hB : 1 < B) (x y : ℕ) (l : List (ℕ × ℕ)) :
    Runs Δ' B fAllInRP [toVal l, toVal x, toVal y] (toVal (l.all (fun z => decide (InR z.1 x y))))
      (60 * l.length + 6) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_allInRP) ?_
    ev_start
    · ev_run
    · simp
  | cons z l ih =>
    have h1 := E1A.inR_runs (Ext.trans extA hΔ) B hB z.1 x y
    refine Runs.mk (hΔ _ _ Δ_allInRP) ?_
    by_cases hz : InR z.1 x y
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
theorem wpush_cons (x i : ℕ) (t : List (ℕ × ℕ)) (y j : ℕ) : wpush ((x, i) :: t) y j =
    if t.all (fun z => decide (InR z.1 x y)) then
      (if t.isEmpty && decide (x = y) then [(x, i)] else [(x, i), (y, j)])
    else (x, i) :: wpush t y j := by rw [wpush]

omit hΔ in
theorem length_wpush_le : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), (wpush st y j).length ≤ st.length + 1
  | [], y, j => by simp [wpush]
  | (x, i) :: t, y, j => by
    unfold wpush
    split_ifs with h1 h2
    · simp
    · simp
    · have := length_wpush_le t y j
      simp only [List.length_cons]; omega

theorem wpush_runs (hB : 1 < B) (y j : ℕ) (st : List (ℕ × ℕ)) :
    Runs Δ' B fWpush [toVal st, toVal y, toVal j] (toVal (wpush st y j)) (70 * (st.length + 1) ^ 2) := by
  induction st with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_wpush) ?_
    ev_start
    · ev_run
    · simp [wpush]
  | cons p t ih =>
    obtain ⟨x, i⟩ := p
    have h1 := allInRP_runs hΔ B hB x y t
    refine Runs.mk (hΔ _ _ Δ_wpush) ?_
    by_cases hall : t.all (fun z => decide (InR z.1 x y)) = true
    · simp only [hall] at h1
      by_cases hc : t = [] ∧ x = y
      · obtain ⟨rfl, rfl⟩ := hc
        have hw : wpush [(x, i)] x j = [(x, i)] := by rw [wpush_cons]; simp
        rw [hw]
        ev_start
        · ev_run
        · simp
      · have hc' : (t.isEmpty && decide (x = y)) = false := by
          cases t <;> simp_all
        have hw : wpush ((x, i) :: t) y j = [(x, i), (y, j)] := by
          rw [wpush_cons, if_pos hall, hc']; simp
        rw [hw]
        by_cases ht : t = []
        · subst ht
          have hxy : ¬ x = y := fun h => hc ⟨rfl, h⟩
          have hB0 : 0 < B := by omega
          ev_start
          · ev_run
          · simp
        · obtain ⟨w, t', rfl⟩ := List.exists_cons_of_ne_nil ht
          ev_start
          · ev_run
          · simp only [List.length_cons]; nlinarith [Nat.zero_le t'.length]
    · have hall' : t.all (fun z => decide (InR z.1 x y)) = false := by simpa using hall
      simp only [hall'] at h1
      have hw : wpush ((x, i) :: t) y j = (x, i) :: wpush t y j := by
        rw [wpush_cons, if_neg hall]
      rw [hw]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le t.length]

theorem witAux_runs (hB : 1 < B) : ∀ (l : List ℕ) (st : List (ℕ × ℕ)) (j k : ℕ), st.length ≤ k →
    j + l.length + 2 < B →
    Runs Δ' B fWitAux [toVal j, toVal st, toVal l] (toVal (witnessesAux j st l))
      (100 * (l.length + 1) * (k + l.length + 1) ^ 2) := by
  intro l
  induction l with
  | nil =>
    intro st j k _ _
    refine Runs.mk (hΔ _ _ Δ_witAux) ?_
    ev_start
    · ev_run
    · simp only [List.length_nil]; nlinarith [Nat.zero_le k]
  | cons y l ih =>
    intro st j k hk hjB
    have h1 := wpush_runs hΔ B hB y j st
    have hl := length_wpush_le st y j
    have h2 := ih (wpush st y j) (j + 1) (k + 1) (by omega) (by simp only [List.length_cons] at hjB; omega)
    refine Runs.mk (hΔ _ _ Δ_witAux) ?_
    simp only [witnessesAux]
    have hjB' : j + 1 < B := by simp only [List.length_cons] at hjB; omega
    ev_start
    · ev_run
    · simp only [List.length_cons]
      have h3 : (st.length + 1) ^ 2 ≤ (k + (l.length + 1) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h4 : (k + 1 + l.length + 1) = (k + (l.length + 1) + 1) := by omega
      rw [h4] at h2
      nlinarith [Nat.zero_le l.length, Nat.zero_le k, Nat.zero_le (l.length * (k + (l.length + 1) + 1) ^ 2)]

omit hΔ in
theorem length_witAux_le : ∀ (l : List ℕ) (st : List (ℕ × ℕ)) (j : ℕ),
    (witnessesAux j st l).length ≤ st.length + l.length
  | [], st, j => by simp [witnessesAux]
  | y :: l, st, j => by
    simp only [witnessesAux, List.length_cons]
    have h1 := length_witAux_le l (wpush st y j) (j + 1)
    have h2 := length_wpush_le st y j
    omega

theorem sndF_runs (hB : 1 < B) (ctx : Val) (p : ℕ × ℕ) :
    Runs Δ' B fSndF [ctx, toVal p] (toVal p.2) 3 := by
  refine Runs.mk (hΔ _ _ Δ_sndF) ?_
  ev_start
  · ev_run
  · omega

theorem witnesses_runs (a : List ℕ) (hj : a.length + 150 < B) :
    Runs Δ' B fWitnesses [toVal a] (toVal (witnesses a)) (150 * (a.length + 1) ^ 3) := by
  have hB : 1 < B := by omega
  have h1 := witAux_runs hΔ B hB a [] 0 0 (by simp) (by omega)
  have hl := length_witAux_le a [] 0
  simp only [List.length_nil, zero_add] at hl
  have h2 := Lib1.map_runs (Ext.trans Lib.ext1 (Ext.trans extLib hΔ)) B fSndF (Val.nat 0) Prod.snd (fun _ => 3)
    (witnessesAux 0 [] a) (fun p _ => sndF_runs hΔ B hB _ p)
  have hs : ((witnessesAux 0 [] a).map (fun _ => 3)).sum = 3 * (witnessesAux 0 [] a).length := by
    generalize witnessesAux 0 [] a = m
    induction m with
    | nil => simp
    | cons x m ih => simp [ih]; omega
  rw [hs] at h2
  have hsB : fSndF < B := by show 140 < B; omega
  refine Runs.mk (hΔ _ _ Δ_witnesses) ?_
  show EvLe Δ' B _ witnessesTm (toVal ((witnessesAux 0 [] a).map Prod.snd)) _
  simp only [zero_add, List.length_nil] at h1
  have e : 100 * (a.length + 1) * (a.length + 1) ^ 2 = 100 * (a.length + 1) ^ 3 := by ring
  rw [e] at h1
  ev_start
  · ev_run
  · have : a.length + 1 ≤ (a.length + 1) ^ 3 := by
      calc a.length + 1 = (a.length + 1) ^ 1 := by simp
        _ ≤ (a.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- unary `Embeds` form: `witnesses`. -/
theorem embeds_witnesses : Embeds Δ' fWitnesses (fun _ : List ℕ => True) witnesses
    (fun a => 150 * (a.length + 1) ^ 3) := by
  intro B a _ hfit
  have : 150 * (a.length + 1) ^ 3 + 3 < B := hfit.cost_lt
  have h1 : a.length + 1 ≤ (a.length + 1) ^ 3 := by
    calc a.length + 1 = (a.length + 1) ^ 1 := by simp
      _ ≤ (a.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  exact witnesses_runs hΔ B a (by omega)

theorem embeds_witnesses_os : Embeds Δ' fWitnesses (fun _ : List ℕ => True) witnesses (osCost 3 witnesses) := by
  refine Embeds.mono_cost (embeds_witnesses hΔ) (fun a _ => ?_)
  have h1 : sz a = 2 * a.length + 1 := sz_list_nat a
  have h2 : 1 ≤ sz (witnesses a) := sz_pos _
  have h3 : (2 * a.length + 2) ^ 3 ≤ (sz a + sz (witnesses a) + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h4 : (2 * a.length + 2) ^ 3 = 8 * (a.length + 1) ^ 3 := by ring
  unfold osCost
  omega

end proofs
end E1B
end Lax117284Proofs.Treewidth.Fun
