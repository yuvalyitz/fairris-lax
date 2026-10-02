import Lax117284Proofs.Treewidth.Fun.E1Lat

/-!
# WP E1 (layer D): `findPath`

Ids `154 …`: `subC`, `predDom`, `findPath`, and the pair-argument form `findPathP`.
`findPath sa sb c want` = the first state of `latticeStates sa sb` (in DP order) whose `τ`-sum, minus `c`, is dominated by
`want` (`domB`), returning its lattice path.  Cost: the lattice DP plus (number of states) × (a `domB` run, exponential in
the length of the state's sequence plus `|want|`, exactly as in Lean).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E1D

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Chars.CT E1A E1B E1C

abbrev fSubC : ℕ := 154
abbrev fPredDom : ℕ := 155
abbrev fFindPath : ℕ := 156
abbrev fFindPathP : ℕ := 157

/-- `map (· - c)` step, `c` the context -/
def subCTm : Tm := .sub (V 1) (V 0)

/-- predicate of the `find?`: context `(c, want)` -/
def predDomTm : Tm :=
  .call fDomB [.call fMap [.lit fSubC, .fst (V 0), .fst (V 1)], .snd (V 0)]

/-- `findPath sa sb c want` -/
def findPathTm : Tm :=
  .letE (.call Lib4.fFind [.lit fPredDom, .cons (V 2) (V 3), .call fLatticeStates [V 0, V 1]])
    (.ite (.isNat (V 0)) (V 0) (.cons (.lit 1) (.call Lib2.fReverse [.snd (.snd (V 0))])))

/-- `findPath` on a 4-tuple `(sa, sb, c, want)` -/
def findPathPTm : Tm :=
  .call fFindPath [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 154 => some subCTm | 155 => some predDomTm | 156 => some findPathTm | 157 => some findPathPTm | _ => none

/-- layer D (= the whole E1 table, ids `128 … 157`) -/
def Δ : ℕ → Option Tm := layerΔ E1C.Δ 154 tbl

abbrev size : ℕ := 158

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 158 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h154 : 154 ≤ f := by omega
    simp only [h154, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extC : E1C.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E1C.Δ_lt h; simp [E1C.size] at this; omega)
theorem extB : E1B.Δ ⊑ Δ := Ext.trans E1C.extB extC
theorem extA : E1A.Δ ⊑ Δ := Ext.trans E1C.extA extC
theorem extLib : Lib.Δ ⊑ Δ := Ext.trans E1C.extLib extC

theorem Δ_subC : Δ fSubC = some subCTm := by simp [Δ, layerΔ_ge tbl (show 154 ≤ fSubC by decide)]; rfl
theorem Δ_predDom : Δ fPredDom = some predDomTm := by simp [Δ, layerΔ_ge tbl (show 154 ≤ fPredDom by decide)]; rfl
theorem Δ_findPath : Δ fFindPath = some findPathTm := by simp [Δ, layerΔ_ge tbl (show 154 ≤ fFindPath by decide)]; rfl
theorem Δ_findPathP : Δ fFindPathP = some findPathPTm := by
  simp [Δ, layerΔ_ge tbl (show 154 ≤ fFindPathP by decide)]; rfl

theorem pathTo_length_le : ∀ (n i j : ℕ) (P : List (ℕ × ℕ)), i + j = n → PathTo i j P → P.length ≤ i + j + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j P hn hP
    rcases hP.split with ⟨rfl, rfl, rfl⟩ | ⟨P', p, rfl, hp, hstep⟩
    · simp
    · have hlt : p.1 + p.2 < n := by
        simp only [LStep] at hstep
        omega
      have := ih (p.1 + p.2) hlt p.1 p.2 P' rfl hp
      simp only [List.length_append, List.length_singleton]
      simp only [LStep] at hstep
      omega

theorem latticeStates_path_length {a b : List ℕ} {s : LState} (h : s ∈ latticeStates a b) :
    s.2.length ≤ a.length + b.length := by
  obtain ⟨hp, -⟩ := latticeStates_sound h
  have := pathTo_length_le _ _ _ _ rfl hp
  simp only [List.length_reverse] at this
  have ha : a ≠ [] := by rintro rfl; simp at h
  have hb : b ≠ [] := by rintro rfl; simp at h
  have h1 : 0 < a.length := List.length_pos_iff.mpr ha
  have h2 : 0 < b.length := List.length_pos_iff.mpr hb
  omega

theorem latB_le (na nb L₁ L₂ : ℕ) :
    na * (rowB L₁ L₂ nb + 100) + 8 + 12 * nb + 8 + 30 ≤
      6000 * (na + 1) * (nb + 1) * (4 ^ (L₁ + L₂ + 1) + 1) ^ 2 * (2 * (L₁ + L₂) + 1 + 2) ^ 2 := by
  have h := ringArith na nb (4 ^ (L₁ + L₂ + 1)) (2 * (L₁ + L₂) + 1)
  exact le_trans (le_trans (Nat.le_add_right _ (23 * 4 ^ (L₁ + L₂ + 1) + 6)) (Nat.le_add_right _ 30)) h

theorem key_le (N T Lb : ℕ) (hN : 1 ≤ N) :
    N * (60 * T + 24 * Lb + 40) + 24 * N ≤ N * (100 * T + 100 * Lb + 100) := by
  nlinarith [Nat.zero_le (N * T), Nat.zero_le (N * Lb)]

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem subC_runs (ctx : ℕ) (x : ℕ) : Runs Δ' B fSubC [toVal ctx, toVal x] (toVal (x - ctx)) 4 := by
  refine Runs.mk (hΔ _ _ Δ_subC) ?_
  ev_start
  · ev_run
  · omega

theorem predDom_runs (hB : 200 < B) (c : ℕ) (want : List ℕ) (s : LState) :
    Runs Δ' B fPredDom [toVal (c, want), toVal s] (toVal (domB (s.1.map (· - c)) want))
      (60 * 3 ^ (s.1.length + want.length) + 24 * s.1.length + 40) := by
  have hB1 : 1 < B := by omega
  have hmap := Lib1.map_runs (Ext.trans Lib.ext1 (Ext.trans extLib hΔ)) B fSubC (Val.nat c) (fun x : ℕ => x - c)
    (fun _ => 4) s.1 (fun x _ => subC_runs hΔ B c x)
  have hs : (s.1.map (fun _ => 4)).sum = 4 * s.1.length := by
    generalize s.1 = m
    induction m with
    | nil => simp
    | cons x m ih => simp; omega
  rw [hs] at hmap
  have hdom := E1A.domB_runs (Ext.trans extA hΔ) B hB1 (s.1.length + want.length) (s.1.map (· - c)) want
    (by simp)
  have hsB : fSubC < B := by show 154 < B; omega
  refine Runs.mk (hΔ _ _ Δ_predDom) ?_
  ev_start
  · ev_run
  · omega

/-- `findPath`: the lattice DP, then a `find?` with one `domB` per state. -/
theorem findPath_runs (hB : 200 < B) (a b : List ℕ) (c : ℕ) (want : List ℕ) (L₁ L₂ : ℕ)
    (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) (hBB : L₁ + L₂ + a.length + b.length + 8 < B) :
    Runs Δ' B fFindPath [toVal a, toVal b, toVal c, toVal want] (toVal (findPath a b c want))
      (6000 * (a.length + 1) * (b.length + 1) * (4 ^ (L₁ + L₂ + 1) + 1) ^ 2 * (2 * (L₁ + L₂) + 1 + 2) ^ 2 +
        4 ^ (L₁ + L₂ + 1) * (100 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 100 * (2 * (L₁ + L₂) + 1) + 100) +
        12 * (a.length + b.length) + 200) := by
  have hB1 : 1 < B := by omega
  have hlat := latticeStates_runs (Ext.trans extC hΔ) B hB a b L₁ L₂ ha hb hBB
  have hlen := latticeStates_length_le ha hb
  -- every state is small
  have hgood : ∀ s ∈ latticeStates a b, s.1.length ≤ 2 * (L₁ + L₂) + 1 ∧ s.2.length ≤ a.length + b.length := by
    intro s hs
    have ha' : a ≠ [] := by rintro rfl; simp at hs
    have hb' : b ≠ [] := by rintro rfl; simp at hs
    exact ⟨(good_of_cell ha hb (latticeStates_cell ha' hb')).2 s hs, latticeStates_path_length hs⟩
  have hpd : ∀ s ∈ latticeStates a b, Runs Δ' B fPredDom [toVal (c, want), toVal s]
      (toVal (domB (s.1.map (· - c)) want))
      (60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40) := by
    intro s hs
    refine (predDom_runs hΔ B hB c want s).mono ?_
    have h1 := (hgood s hs).1
    have h2 : 3 ^ (s.1.length + want.length) ≤ 3 ^ (2 * (L₁ + L₂) + 1 + want.length) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hfind := Lib4.find_runs (Ext.trans Lib.ext4 (Ext.trans extLib hΔ)) B fPredDom (toVal (c, want))
    (fun s : LState => domB (s.1.map (· - c)) want)
    (fun _ => 60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40)
    (latticeStates a b) hpd hB1
  have hsum : ((latticeStates a b).map
      (fun _ => 60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40)).sum =
      (latticeStates a b).length * (60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40) := by
    generalize latticeStates a b = m
    induction m with
    | nil => simp
    | cons x m ih => simp [ih]; ring
  rw [hsum] at hfind
  have hfP : fPredDom < B := by show 155 < B; omega
  have hA := ringArith a.length b.length (4 ^ (L₁ + L₂ + 1)) (2 * (L₁ + L₂) + 1)
  have hp3 : 1 ≤ 3 ^ (2 * (L₁ + L₂) + 1 + want.length) := Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ 4 ^ (L₁ + L₂ + 1) := Nat.one_le_pow _ _ (by omega)
  have hprod : (latticeStates a b).length *
      (60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40) ≤
      4 ^ (L₁ + L₂ + 1) * (60 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 24 * (2 * (L₁ + L₂) + 1) + 40) :=
    Nat.mul_le_mul_right _ hlen
  have hf2 : 24 * (latticeStates a b).length ≤ 24 * 4 ^ (L₁ + L₂ + 1) := by omega
  have hlat' := latB_le a.length b.length L₁ L₂
  have hkey := key_le (4 ^ (L₁ + L₂ + 1)) (3 ^ (2 * (L₁ + L₂) + 1 + want.length)) (2 * (L₁ + L₂) + 1) hN1
  refine Runs.mk (hΔ _ _ Δ_findPath) ?_
  show EvLe Δ' B _ findPathTm (toVal ((latticeStates a b).find? (fun s => domB (s.1.map (· - c)) want) |>.map
    (fun s => s.2.reverse))) _
  have hfl : fPredDom < B := hfP
  rcases hfd : (latticeStates a b).find? (fun s => domB (s.1.map (· - c)) want) with _ | s
  · rw [hfd] at hfind
    rw [hfd, Option.map_none]
    ev_start
    · ev_run
    · omega
  · rw [hfd] at hfind
    have hmem := List.mem_of_find?_eq_some hfd
    have hs2 := (hgood s hmem).2
    have hr := Lib2.reverse_runs (Ext.trans Lib.ext2 (Ext.trans extLib hΔ)) B s.2 (by omega)
    rw [hfd, Option.map_some]
    ev_start
    · ev_run
    · omega

/-- cost of `findPath sa sb c want` (`L₁, L₂` the maxima of `sa`, `sb`) -/
def findPathCost (p : List ℕ × List ℕ × ℕ × List ℕ) : ℕ :=
  6000 * (p.1.length + 1) * (p.2.1.length + 1) * (4 ^ (maxOf p.1 + maxOf p.2.1 + 1) + 1) ^ 2 *
      (2 * (maxOf p.1 + maxOf p.2.1) + 1 + 2) ^ 2 +
    4 ^ (maxOf p.1 + maxOf p.2.1 + 1) *
      (100 * 3 ^ (2 * (maxOf p.1 + maxOf p.2.1) + 1 + p.2.2.2.length) +
        100 * (2 * (maxOf p.1 + maxOf p.2.1) + 1) + 100) +
    12 * (p.1.length + p.2.1.length) + 220

theorem findPathP_runs (hB : 200 < B) (a b : List ℕ) (c : ℕ) (want : List ℕ) (L₁ L₂ : ℕ)
    (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) (hBB : L₁ + L₂ + a.length + b.length + 8 < B) :
    Runs Δ' B fFindPathP [toVal (a, b, c, want)] (toVal (findPath a b c want))
      (6000 * (a.length + 1) * (b.length + 1) * (4 ^ (L₁ + L₂ + 1) + 1) ^ 2 * (2 * (L₁ + L₂) + 1 + 2) ^ 2 +
        4 ^ (L₁ + L₂ + 1) * (100 * 3 ^ (2 * (L₁ + L₂) + 1 + want.length) + 100 * (2 * (L₁ + L₂) + 1) + 100) +
        12 * (a.length + b.length) + 220) := by
  have h := findPath_runs hΔ B hB a b c want L₁ L₂ ha hb hBB
  refine Runs.mk (hΔ _ _ Δ_findPathP) ?_
  ev_start
  · ev_run
  · omega

omit hΔ in
theorem findPathCost_ge (p : List ℕ × List ℕ × ℕ × List ℕ) :
    maxOf p.1 + maxOf p.2.1 + p.1.length + p.2.1.length + 8 + 3 ≤ findPathCost p ∧ 200 ≤ findPathCost p := by
  have h1 := ringCost_ge (p.1, p.2.1)
  have h2 := ringCost_ge200 (p.1, p.2.1)
  unfold ringCost at h1 h2
  unfold findPathCost
  simp only [] at h1 h2
  omega

/-- unary `Embeds` form: `findPath` on the tuple `(sa, sb, c, want)`. -/
theorem embeds_findPath : Embeds Δ' fFindPathP (fun _ : List ℕ × List ℕ × ℕ × List ℕ => True)
    (fun p => findPath p.1 p.2.1 p.2.2.1 p.2.2.2) findPathCost := by
  intro B p _ hfit
  have h1 := hfit.cost_lt
  obtain ⟨h2, h3⟩ := findPathCost_ge p
  exact findPathP_runs hΔ B (by omega) p.1 p.2.1 p.2.2.1 p.2.2.2 (maxOf p.1) (maxOf p.2.1)
    (fun x hx => le_maxOf hx) (fun x hx => le_maxOf hx) (by omega)

end proofs
end E1D
end Lax117284Proofs.Treewidth.Fun
