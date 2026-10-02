import Lax117284Proofs.Treewidth.Fun.E1Wit
import Lax117284Proofs.Treewidth.Chars.Lattice
import Lax117284Proofs.Treewidth.Size.Lattice

/-!
# WP E1 (layer C): the lattice dynamic programme `latticeStates` / `ringTypList`

Ids `142 …`.  The functions are the Lean ones (`dedupKey`, `cellOf`, `rowCells`, `latticeRows`, `latticeStates`,
`ringTypList`); the cost is stated in terms of the bounds `4^(L₁+L₂+1)` (number of states of a cell,
`Size/Lattice.lean`) and `2(L₁+L₂)+1` (length of a state's typical sequence), `L₁, L₂` bounding the entries of `a`, `b`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Lax117284Proofs.Treewidth.Fun
namespace E1C

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Chars.CT E1A E1B

abbrev fHasKey : ℕ := 142
abbrev fDedupAux : ℕ := 143
abbrev fDedupKey : ℕ := 144
abbrev fMkState : ℕ := 145
abbrev fCellOf : ℕ := 146
abbrev fRowCells : ℕ := 147
abbrev fLatRows : ℕ := 148
abbrev fLastD : ℕ := 149
abbrev fLatticeStates : ℕ := 150
abbrev fFstF : ℕ := 151
abbrev fRingTypList : ℕ := 152
abbrev fRingTypListP : ℕ := 153

/-- `hasKey acc s`: some state of `acc` has the key of `s` -/
def hasKeyTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.call fEqV [.fst (.fst (V 0)), .fst (V 1)]) (.lit 1) (.call fHasKey [.snd (V 0), V 1]))

/-- `dedupAux acc l = l.foldl step acc` (the step of `dedupKey`) -/
def dedupAuxTm : Tm :=
  .ite (.isNat (V 1)) (V 0)
    (.call fDedupAux
      [.ite (.call fHasKey [V 0, .fst (V 1)]) (V 0) (.call fAppend [V 0, .cons (.fst (V 1)) (.lit 0)]),
       .snd (V 1)])

/-- `dedupKey l` -/
def dedupKeyTm : Tm := .call fDedupAux [.lit 0, V 0]

/-- `mkState (z,(i,j)) s = (push s.1 z, (i,j) :: s.2)` -/
def mkStateTm : Tm :=
  .cons (.call fPush [.fst (V 1), .fst (V 0)])
    (.cons (.cons (.fst (.snd (V 0))) (.snd (.snd (V 0)))) (.snd (V 1)))

/-- `cellOf i j z up left diag` -/
def cellOfTm : Tm :=
  .call fDedupKey
    [.call fMap [.lit fMkState, .cons (V 2) (.cons (V 0) (V 1)),
      .call fAppend [.call fAppend [V 3, V 4], V 5]]]

/-- `ups.headD []` -/
abbrev headDT (u : Tm) : Tm := .ite (.isNat u) (.lit 0) (.fst u)
/-- `ups.tail` -/
abbrev tailT (u : Tm) : Tm := .ite (.isNat u) (.lit 0) (.snd u)

/-- `rowCells i x bl j ups diag left` -/
def rowCellsTm : Tm :=
  .ite (.isNat (V 2)) (.lit 0)
    (.letE (.call fCellOf [V 0, V 3, .add (V 1) (.fst (V 2)), headDT (V 4), V 6, V 5])
      (.cons (V 0)
        (.call fRowCells [V 1, V 2, .snd (V 3), .add (V 4) (.lit 1), tailT (V 5), headDT (V 5), V 0])))

/-- `latticeRows b i al prev` -/
def latRowsTm : Tm :=
  .ite (.isNat (V 2)) (V 3)
    (.call fLatRows [V 0, .add (V 1) (.lit 1), .snd (V 2),
      .call fRowCells [V 1, .fst (V 2), V 0, .lit 0, V 3,
        .ite (.eq (V 1) (.lit 0)) (.cons (.cons (.lit 0) (.lit 0)) (.lit 0)) (.lit 0), .lit 0]])

/-- `l.getLast?.getD []` -/
def lastDTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0) (.ite (.isNat (.snd (V 0))) (.fst (V 0)) (.call fLastD [.snd (V 0)]))

/-- `latticeStates a b` -/
def latticeStatesTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.isNat (V 1)) (.lit 0) (.call fLastD [.call fLatRows [V 1, .lit 0, V 0, .lit 0]]))

/-- `map fst` step -/
def fstFTm : Tm := .fst (V 1)

/-- `ringTypList a b` -/
def ringTypListTm : Tm := .call fMap [.lit fFstF, .lit 0, .call fLatticeStates [V 0, V 1]]

/-- `ringTypList` on a pair (unary calling convention) -/
def ringTypListPTm : Tm := .call fRingTypList [.fst (V 0), .snd (V 0)]

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 142 => some hasKeyTm | 143 => some dedupAuxTm | 144 => some dedupKeyTm | 145 => some mkStateTm
  | 146 => some cellOfTm | 147 => some rowCellsTm | 148 => some latRowsTm | 149 => some lastDTm
  | 150 => some latticeStatesTm | 151 => some fstFTm | 152 => some ringTypListTm
  | 153 => some ringTypListPTm | _ => none

/-- layer C of the E1 table -/
def Δ : ℕ → Option Tm := layerΔ E1B.Δ 142 tbl

abbrev size : ℕ := 154

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 154 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h142 : 142 ≤ f := by omega
    simp only [h142, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extB : E1B.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E1B.Δ_lt h; simp [E1B.size] at this; omega)
theorem extA : E1A.Δ ⊑ Δ := Ext.trans E1B.extA extB
theorem extLib : Lib.Δ ⊑ Δ := Ext.trans E1A.extLib extA

theorem Δ_hasKey : Δ fHasKey = some hasKeyTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fHasKey by decide)]; rfl
theorem Δ_dedupAux : Δ fDedupAux = some dedupAuxTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fDedupAux by decide)]; rfl
theorem Δ_dedupKey : Δ fDedupKey = some dedupKeyTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fDedupKey by decide)]; rfl
theorem Δ_mkState : Δ fMkState = some mkStateTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fMkState by decide)]; rfl
theorem Δ_cellOf : Δ fCellOf = some cellOfTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fCellOf by decide)]; rfl
theorem Δ_rowCells : Δ fRowCells = some rowCellsTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fRowCells by decide)]; rfl
theorem Δ_latRows : Δ fLatRows = some latRowsTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fLatRows by decide)]; rfl
theorem Δ_lastD : Δ fLastD = some lastDTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fLastD by decide)]; rfl
theorem Δ_latticeStates : Δ fLatticeStates = some latticeStatesTm := by
  simp [Δ, layerΔ_ge tbl (show 142 ≤ fLatticeStates by decide)]; rfl
theorem Δ_fstF : Δ fFstF = some fstFTm := by simp [Δ, layerΔ_ge tbl (show 142 ≤ fFstF by decide)]; rfl
theorem Δ_ringTypList : Δ fRingTypList = some ringTypListTm := by
  simp [Δ, layerΔ_ge tbl (show 142 ≤ fRingTypList by decide)]; rfl

/-- the size bounds carried by a state list of the lattice DP -/
def Good (N Lt : ℕ) (C : List LState) : Prop := C.length ≤ N ∧ ∀ s ∈ C, s.1.length ≤ Lt

theorem good_nil (N Lt : ℕ) : Good N Lt [] := ⟨by simp, by simp⟩

/-! ### the size bounds of the cells of the DP (from `Size/Lattice.lean`) -/

/-- number of states of a cell and length of the typical sequences, as bounds in `L₁ + L₂` -/
abbrev NB (L₁ L₂ : ℕ) : ℕ := 4 ^ (L₁ + L₂ + 1)
abbrev LB (L₁ L₂ : ℕ) : ℕ := 2 * (L₁ + L₂) + 1

theorem good_of_cell {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) {i j : ℕ}
    {C : List LState} (hC : Cell a b i j C) : Good (NB L₁ L₂) (LB L₁ L₂) C := by
  refine ⟨cell_length_le ha hb hC, fun s hs => ?_⟩
  obtain ⟨-, he⟩ := hC.1 s hs
  rw [he]
  exact typical_length_le' (pathSum_le ha hb _)

theorem good_of_upOk {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) {i j : ℕ}
    {C : List LState} (hC : UpOk a b i j C) : Good (NB L₁ L₂) (LB L₁ L₂) C := by
  cases i with
  | zero => rw [hC.1 rfl]; exact good_nil _ _
  | succ i' => exact good_of_cell ha hb (hC.2 i' rfl)

theorem good_of_leftOk {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) {i j : ℕ}
    {C : List LState} (hC : LeftOk a b i j C) : Good (NB L₁ L₂) (LB L₁ L₂) C := by
  cases j with
  | zero => rw [hC.1 rfl]; exact good_nil _ _
  | succ j' => exact good_of_cell ha hb (hC.2 j' rfl)

theorem good_of_diagOk {a b : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂) {i j : ℕ}
    {C : List LState} (hC : DiagOk a b i j C) : Good (NB L₁ L₂) (LB L₁ L₂) C := by
  by_cases h0 : i = 0 ∧ j = 0
  · rw [hC.1 h0]
    refine ⟨?_, ?_⟩
    · simp only [List.length_singleton]; exact Nat.one_le_pow _ _ (by omega)
    · intro s hs; simp at hs; subst hs; simp
  · by_cases h1 : i = 0 ∨ j = 0
    · rw [hC.2.1 h1 h0]; exact good_nil _ _
    · push Not at h1
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact good_of_cell ha hb (hC.2.2 i' j' rfl rfl)

theorem ringArith (na nb N Lb : ℕ) :
    na * (nb * (500 * (3 * N + 1) ^ 2 * (Lb + 2) ^ 2 + 100) + 8 + 100) + 8 + 12 * nb + 8 + 30
      + (23 * N + 6) + 30 ≤ 6000 * (na + 1) * (nb + 1) * (N + 1) ^ 2 * (Lb + 2) ^ 2 := by
  set X := (N + 1) ^ 2 * (Lb + 2) ^ 2 with hX
  have hX4 : 4 ≤ X := by
    have h1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : 4 ≤ (Lb + 2) ^ 2 := by
      have := Nat.pow_le_pow_left (show 2 ≤ Lb + 2 by omega) 2
      simpa using this
    rw [hX]; nlinarith
  have hNX : N ≤ X := by
    have h1 : N ≤ (N + 1) ^ 2 := by nlinarith
    have h2 : 1 ≤ (Lb + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [hX]; nlinarith
  have hc : 500 * (3 * N + 1) ^ 2 * (Lb + 2) ^ 2 ≤ 4500 * X := by
    have : (3 * N + 1) ^ 2 ≤ 9 * (N + 1) ^ 2 := by nlinarith
    have h2 : (3 * N + 1) ^ 2 * (Lb + 2) ^ 2 ≤ 9 * (N + 1) ^ 2 * (Lb + 2) ^ 2 := Nat.mul_le_mul_right _ this
    rw [hX]; nlinarith
  have e : 6000 * (na + 1) * (nb + 1) * (N + 1) ^ 2 * (Lb + 2) ^ 2 = 6000 * ((na + 1) * (nb + 1)) * X := by
    rw [hX]; ring
  rw [e]
  have h3a : nb * (500 * (3 * N + 1) ^ 2 * (Lb + 2) ^ 2 + 100) ≤ nb * (4500 * X + 100) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : na * (nb * (500 * (3 * N + 1) ^ 2 * (Lb + 2) ^ 2 + 100) + 8 + 100) ≤ na * (nb * (4500 * X + 100) + 108) :=
    Nat.mul_le_mul_left na (by omega)
  nlinarith [Nat.zero_le (na * nb), Nat.zero_le (na * nb * X), Nat.zero_le (na * X), Nat.zero_le (nb * X),
    Nat.zero_le na, Nat.zero_le nb, Nat.zero_le X, Nat.mul_le_mul_left na hX4, Nat.mul_le_mul_left nb hX4]

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem ext1' : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans extLib hΔ)

theorem hasKey_runs (hB : 1 < B) (s : LState) (acc : List LState) :
    Runs Δ' B fHasKey [toVal acc, toVal s] (toVal (acc.any (fun t => decide (t.1 = s.1))))
      ((30 * sz s.1 + 30) * acc.length + 6) := by
  induction acc with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_hasKey) ?_
    ev_start
    · ev_run
    · simp
  | cons t acc ih =>
    refine Runs.mk (hΔ _ _ Δ_hasKey) ?_
    by_cases hts : t.1 = s.1
    · have h1 := Lib1.eqV_runs_typed (ext1' hΔ) B hB t.1 s.1 true (by simp [hts])
      simp only [List.any_cons, hts, decide_true, Bool.true_or]
      ev_start
      · ev_run
      · have : min (sz t.1) (sz s.1) ≤ sz s.1 := min_le_right _ _
        simp only [List.length_cons]; nlinarith [Nat.zero_le acc.length]
    · have h1 := Lib1.eqV_runs_typed (ext1' hΔ) B hB t.1 s.1 false (by simp [hts])
      simp only [List.any_cons, hts, decide_false, Bool.false_or]
      ev_start
      · ev_run
      · have : min (sz t.1) (sz s.1) ≤ sz s.1 := min_le_right _ _
        simp only [List.length_cons]; nlinarith [Nat.zero_le acc.length]

theorem dedupAux_runs (hB : 1 < B) (S : ℕ) : ∀ (l acc : List LState) (k : ℕ), acc.length ≤ k →
    (∀ s ∈ l, sz s.1 ≤ S) →
    Runs Δ' B fDedupAux [toVal acc, toVal l]
      (toVal (l.foldl (fun acc s => if acc.any (fun t => decide (t.1 = s.1)) then acc else acc ++ [s]) acc))
      (l.length * ((30 * S + 40) * (k + l.length) + 40) + 8) := by
  intro l
  induction l with
  | nil =>
    intro acc k _ _
    refine Runs.mk (hΔ _ _ Δ_dedupAux) ?_
    ev_start
    · ev_run
    · simp
  | cons s l ih =>
    intro acc k hk hS
    have hsS := hS s (List.mem_cons_self ..)
    have h1 := hasKey_runs hΔ B hB s acc
    have h1' : (30 * sz s.1 + 30) * acc.length ≤ (30 * S + 30) * k := Nat.mul_le_mul (by omega) hk
    refine Runs.mk (hΔ _ _ Δ_dedupAux) ?_
    simp only [List.foldl_cons]
    by_cases hany : acc.any (fun t => decide (t.1 = s.1)) = true
    · simp only [hany] at h1
      have h2 := ih acc (k + 1) (by omega) (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      simp only [hany, if_true]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le l.length, Nat.zero_le k, Nat.zero_le S, Nat.zero_le (S * k),
          Nat.zero_le (S * l.length), Nat.zero_le (l.length * k), Nat.zero_le (l.length * l.length),
          Nat.zero_le (S * l.length * l.length), Nat.zero_le (S * l.length * k)]
    · have hany' : acc.any (fun t => decide (t.1 = s.1)) = false := Bool.eq_false_iff.2 hany
      simp only [hany'] at h1
      have h2 := ih (acc ++ [s]) (k + 1) (by simp; omega) (fun x hx => hS x (List.mem_cons_of_mem _ hx))
      have h3 := append_runs (ext1' hΔ) B acc [s]
      simp only [hany', Bool.false_eq_true, if_false]
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le l.length, Nat.zero_le k, Nat.zero_le S, Nat.zero_le (S * k),
          Nat.zero_le (S * l.length), Nat.zero_le (l.length * k), Nat.zero_le (l.length * l.length),
          Nat.zero_le (S * l.length * l.length), Nat.zero_le (S * l.length * k)]

theorem dedupKey_runs (hB : 1 < B) (S : ℕ) (l : List LState) (hS : ∀ s ∈ l, sz s.1 ≤ S) :
    Runs Δ' B fDedupKey [toVal l] (toVal (dedupKey l))
      (l.length * ((30 * S + 40) * l.length + 40) + 16) := by
  have h := dedupAux_runs hΔ B hB S l [] 0 (by simp) hS
  simp only [zero_add] at h
  refine Runs.mk (hΔ _ _ Δ_dedupKey) ?_
  show EvLe Δ' B _ dedupKeyTm (toVal (l.foldl _ [])) _
  ev_start
  · ev_run
  · omega

theorem mkState_runs (hB : 1 < B) (z i j : ℕ) (s : LState) :
    Runs Δ' B fMkState [toVal (z, (i, j)), toVal s] (toVal (push s.1 z, (i, j) :: s.2))
      (80 * (s.1.length + 1) ^ 2 + 40) := by
  have h := E1A.push_runs (Ext.trans extA hΔ) B hB z s.1
  refine Runs.mk (hΔ _ _ Δ_mkState) ?_
  obtain ⟨u, v⟩ := s
  ev_start
  · ev_run
  · simp only []; omega

omit hΔ in
theorem length_push_le (t : List ℕ) (y : ℕ) : (push t y).length ≤ t.length + 1 := by
  simp only [push, List.length_append, List.length_singleton]
  have := length_cut_le t y; omega

theorem cellOf_runs (hB : 200 < B) (M Lt : ℕ) (i j z : ℕ) (up left diag : List LState)
    (hM : up.length + left.length + diag.length ≤ M)
    (hLt : ∀ s ∈ up ++ left ++ diag, s.1.length ≤ Lt) :
    Runs Δ' B fCellOf [toVal i, toVal j, toVal z, toVal up, toVal left, toVal diag]
      (toVal (cellOf i j z up left diag)) (500 * (M + 1) ^ 2 * (Lt + 2) ^ 2) := by
  have hB1 : 1 < B := by omega
  have hmk : ∀ s ∈ up ++ left ++ diag, Runs Δ' B fMkState [toVal (z, (i, j)), toVal s]
      (toVal (push s.1 z, (i, j) :: s.2)) (80 * (Lt + 1) ^ 2 + 40) := by
    intro s hs
    refine (mkState_runs hΔ B hB1 z i j s).mono ?_
    have := hLt s hs
    have : (s.1.length + 1) ^ 2 ≤ (Lt + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hmap := Lib1.map_runs (ext1' hΔ) B fMkState (toVal (z, (i, j)))
    (fun s : LState => ((push s.1 z, (i, j) :: s.2) : LState)) (fun _ => 80 * (Lt + 1) ^ 2 + 40)
    (up ++ left ++ diag) hmk
  have hsum : ((up ++ left ++ diag).map (fun _ => 80 * (Lt + 1) ^ 2 + 40)).sum =
      (up ++ left ++ diag).length * (80 * (Lt + 1) ^ 2 + 40) := by
    generalize up ++ left ++ diag = m
    induction m with
    | nil => simp
    | cons x m ih => simp [ih]; ring
  rw [hsum] at hmap
  have hlen : (up ++ left ++ diag).length = up.length + left.length + diag.length := by simp; omega
  have hS : ∀ s ∈ (up ++ left ++ diag).map (fun s : LState => ((push s.1 z, (i, j) :: s.2) : LState)),
      sz s.1 ≤ 2 * Lt + 3 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    have h1 := length_push_le t.1 z
    have h2 := hLt t ht
    show sz (push t.1 z) ≤ _
    rw [sz_list_nat]; omega
  have hdk := dedupKey_runs hΔ B hB1 (2 * Lt + 3) _ hS
  rw [List.length_map, hlen] at hdk
  have h4 := append_runs (ext1' hΔ) B up left
  have h5 := append_runs (ext1' hΔ) B (up ++ left) diag
  simp only [List.length_append] at h5
  rw [hlen] at hmap
  have hfm : fMkState < B := by show 145 < B; omega
  refine Runs.mk (hΔ _ _ Δ_cellOf) ?_
  show EvLe Δ' B _ cellOfTm (toVal (dedupKey ((up ++ left ++ diag).map _))) _
  ev_start
  · ev_run
  · have hu : up.length ≤ up.length + left.length + diag.length := by omega
    have hul : up.length + left.length ≤ up.length + left.length + diag.length := by omega
    generalize up.length + left.length + diag.length = n at *
    have f2 : n * n ≤ M * M := Nat.mul_le_mul hM hM
    have f3 : n * Lt ≤ M * Lt := Nat.mul_le_mul_right Lt hM
    have f4 : n * n * Lt ≤ M * M * Lt := Nat.mul_le_mul_right Lt f2
    have f5 : n * Lt * Lt ≤ M * Lt * Lt := Nat.mul_le_mul_right Lt f3
    nlinarith [Nat.zero_le M, Nat.zero_le Lt, Nat.zero_le (M * Lt), Nat.zero_le (M * M),
      Nat.zero_le (M * M * Lt), Nat.zero_le (M * Lt * Lt), Nat.zero_le (M * M * Lt * Lt),
      Nat.zero_le (Lt * Lt), Nat.zero_le n, Nat.zero_le (n * Lt)]

theorem rowCells_runs_abs (hB : 200 < B) (N Lt i x : ℕ) :
    ∀ (bl : List ℕ) (j : ℕ) (ups : List (List LState)) (diag left : List LState),
    (∀ y ∈ bl, x + y < B) → j + bl.length + 2 < B →
    (∀ m < bl.length, Good N Lt (ups.getD m [])) → Good N Lt diag → Good N Lt left →
    (∀ m < bl.length, Good N Lt ((rowCells i x bl j ups diag left).getD m [])) →
    Runs Δ' B fRowCells [toVal i, toVal x, toVal bl, toVal j, toVal ups, toVal diag, toVal left]
      (toVal (rowCells i x bl j ups diag left))
      (bl.length * (500 * (3 * N + 1) ^ 2 * (Lt + 2) ^ 2 + 100) + 8) := by
  intro bl
  induction bl with
  | nil =>
    intro j ups diag left _ _ _ _ _ _
    refine Runs.mk (hΔ _ _ Δ_rowCells) ?_
    ev_start
    · ev_run
    · simp [rowCells]
  | cons y b ih =>
    intro j ups diag left hxy hj hups hdiag hleft hout
    have hB1 : 1 < B := by omega
    have hc0 : Good N Lt (ups.headD []) := by rw [headD_eq]; exact hups 0 (by simp)
    have hcell := cellOf_runs hΔ B hB (3 * N) Lt i j (x + y) (ups.headD []) left diag
      (by have := hc0.1; have := hleft.1; have := hdiag.1; omega)
      (by
        intro s hs
        simp only [List.mem_append] at hs
        rcases hs with (hs | hs) | hs
        · exact hc0.2 s hs
        · exact hleft.2 s hs
        · exact hdiag.2 s hs)
    have hgc : Good N Lt (cellOf i j (x + y) (ups.headD []) left diag) := by
      have := hout 0 (by simp)
      simpa [rowCells] using this
    have hrec := ih (j + 1) ups.tail (ups.headD []) (cellOf i j (x + y) (ups.headD []) left diag)
      (fun y' hy' => hxy y' (List.mem_cons_of_mem _ hy'))
      (by simp only [List.length_cons] at hj; omega)
      (by
        intro m hm
        rw [tail_getD]
        exact hups (m + 1) (by simp only [List.length_cons]; omega))
      hc0 hgc
      (by
        intro m hm
        have := hout (m + 1) (by simp only [List.length_cons]; omega)
        simpa [rowCells] using this)
    have hxy0 := hxy y (List.mem_cons_self ..)
    have hj1 : j + 1 < B := by simp only [List.length_cons] at hj; omega
    clear ih hout hups hdiag hleft hxy hc0 hgc
    refine Runs.mk (hΔ _ _ Δ_rowCells) ?_
    simp only [rowCells]
    rcases ups with _ | ⟨u, us⟩
    · simp only [List.headD_nil, List.tail_nil] at hcell hrec
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le b.length]
    · simp only [List.headD_cons, List.tail_cons] at hcell hrec
      ev_start
      · ev_run
      · simp only [List.length_cons]
        nlinarith [Nat.zero_le b.length]

theorem rowCells_runs (hB : 200 < B) (a b : List ℕ) (L₁ L₂ : ℕ) (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂)
    (i : ℕ) (bl : List ℕ) (j : ℕ) (ups : List (List LState)) (diag left : List LState) (hbl : bl = b.drop j)
    (hup : ∀ m, m < bl.length → UpOk a b i (j + m) (ups.getD m []))
    (hdiag : DiagOk a b i j diag) (hleft : LeftOk a b i j left)
    (hxB : L₁ + L₂ < B) (hjB : j + bl.length + 2 < B) :
    Runs Δ' B fRowCells [toVal i, toVal (a.getD i 0), toVal bl, toVal j, toVal ups, toVal diag, toVal left]
      (toVal (rowCells i (a.getD i 0) bl j ups diag left))
      (bl.length * (500 * (3 * NB L₁ L₂ + 1) ^ 2 * (LB L₁ L₂ + 2) ^ 2 + 100) + 8) := by
  have hok := rowCells_ok a b i bl j ups diag left hbl hup hdiag hleft
  refine rowCells_runs_abs hΔ B hB (NB L₁ L₂) (LB L₁ L₂) i (a.getD i 0) bl j ups diag left ?_ hjB
    (fun m hm => good_of_upOk ha hb (hup m hm)) (good_of_diagOk ha hb hdiag) (good_of_leftOk ha hb hleft)
    (fun m hm => good_of_cell ha hb (hok.2 m hm))
  intro y hy
  have hy' : y ∈ b := by rw [hbl] at hy; exact List.mem_of_mem_drop hy
  have := getD_le_of_all ha i
  have := hb y hy'
  omega

/-- cost of one cell / one row of the DP -/
abbrev cellB (L₁ L₂ : ℕ) : ℕ := 500 * (3 * NB L₁ L₂ + 1) ^ 2 * (LB L₁ L₂ + 2) ^ 2
abbrev rowB (L₁ L₂ nb : ℕ) : ℕ := nb * (cellB L₁ L₂ + 100) + 8

theorem latRows_runs (hB : 200 < B) (a b : List ℕ) (L₁ L₂ : ℕ) (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂)
    (hBB : L₁ + L₂ + a.length + b.length + 8 < B) :
    ∀ (al : List ℕ) (i : ℕ) (prev : List (List LState)), al = a.drop i →
    (al ≠ [] → ∀ m, m < b.length → UpOk a b i m (prev.getD m [])) →
    Runs Δ' B fLatRows [toVal b, toVal i, toVal al, toVal prev] (toVal (latticeRows b i al prev))
      (al.length * (rowB L₁ L₂ b.length + 100) + 8) := by
  intro al
  induction al with
  | nil =>
    intro i prev _ _
    refine Runs.mk (hΔ _ _ Δ_latRows) ?_
    ev_start
    · ev_run
    · simp [latticeRows]
  | cons x al' ih =>
    intro i prev hal hup'
    have hup := hup' (by simp)
    have hi : i < a.length := by
      by_contra hcon
      rw [List.drop_of_length_le (by omega)] at hal
      exact absurd hal (by simp)
    have hx : a.getD i 0 = x := by
      have : (a.drop i)[0]? = some x := by rw [← hal]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at this
      simp [List.getD_eq_getElem?_getD, this]
    have hal' : al' = a.drop (i + 1) := by
      have h1 : (a.drop i).drop 1 = al' := by rw [← hal]; rfl
      rw [List.drop_drop] at h1
      rw [← h1, Nat.add_comm]
    have hrow := rowCells_ok a b i b 0 prev (if i = 0 then [([], [])] else []) [] (by simp)
      (by simpa using hup)
      ⟨fun h => by simp [h.1], fun h1 h2 => by
          rcases h1 with h1 | h1
          · exact absurd ⟨h1, rfl⟩ h2
          · have hne : i ≠ 0 := fun h => h2 ⟨h, rfl⟩
            simp [hne], fun i' j' _ h => by omega⟩
      ⟨fun _ => rfl, fun j' h => by omega⟩
    have hrun := rowCells_runs hΔ B hB a b L₁ L₂ ha hb i b 0 prev (if i = 0 then [([], [])] else []) []
      rfl (by simpa using hup)
      ⟨fun h => by simp [h.1], fun h1 h2 => by
          rcases h1 with h1 | h1
          · exact absurd ⟨h1, rfl⟩ h2
          · have hne : i ≠ 0 := fun h => h2 ⟨h, rfl⟩
            simp [hne], fun i' j' _ h => by omega⟩
      ⟨fun _ => rfl, fun j' h => by omega⟩ (by omega) (by omega)
    rw [hx] at hrun hrow
    have hih := ih (i + 1)
      (rowCells i x b 0 prev (if i = 0 then [([], [])] else []) []) hal' (by
        intro _ m hm
        refine ⟨fun h => by omega, fun i' hi' => ?_⟩
        have : i' = i := by omega
        subst this
        simpa using hrow.2 m hm)
    have hi1 : i + 1 < B := by omega
    have hxB : x ≤ L₁ := by rw [← hx]; exact getD_le_of_all ha i
    refine Runs.mk (hΔ _ _ Δ_latRows) ?_
    simp only [latticeRows]
    clear ih hup' hup hrow
    by_cases hi0 : i = 0
    · subst hi0
      simp only [if_true] at hrun hih ⊢
      ev_start
      · ev_run
      · simp only [List.length_cons]; nlinarith
    · simp only [hi0, if_false] at hrun hih ⊢
      ev_start
      · ev_run
      · simp only [List.length_cons]; nlinarith

theorem lastD_runs (hB : 1 < B) (l : List (List LState)) :
    Runs Δ' B fLastD [toVal l] (toVal (l.getLast?.getD [])) (12 * l.length + 8) := by
  induction l with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_lastD) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    refine Runs.mk (hΔ _ _ Δ_lastD) ?_
    cases l with
    | nil =>
      ev_start
      · ev_run
      · simp
    | cons y l =>
      have hg : (x :: y :: l).getLast?.getD [] = (y :: l).getLast?.getD [] := by
        simp [List.getLast?_cons_cons]
      rw [hg]
      ev_start
      · ev_run
      · simp only [List.length_cons] at *; omega

theorem latticeStates_runs (hB : 200 < B) (a b : List ℕ) (L₁ L₂ : ℕ) (ha : ∀ x ∈ a, x ≤ L₁)
    (hb : ∀ x ∈ b, x ≤ L₂) (hBB : L₁ + L₂ + a.length + b.length + 8 < B) :
    Runs Δ' B fLatticeStates [toVal a, toVal b] (toVal (latticeStates a b))
      (a.length * (rowB L₁ L₂ b.length + 100) + 8 + 12 * b.length + 8 + 30) := by
  have hB1 : 1 < B := by omega
  by_cases ha' : a = []
  · subst ha'
    refine Runs.mk (hΔ _ _ Δ_latticeStates) ?_
    ev_start
    · ev_run
    · simp
  by_cases hb' : b = []
  · subst hb'
    obtain ⟨x, a', rfl⟩ := List.exists_cons_of_ne_nil ha'
    refine Runs.mk (hΔ _ _ Δ_latticeStates) ?_
    ev_start
    · ev_run
    · simp
  obtain ⟨x, a', rfl⟩ := List.exists_cons_of_ne_nil ha'
  obtain ⟨y, b', rfl⟩ := List.exists_cons_of_ne_nil hb'
  have hrows := latticeRows_ok (x :: a') (y :: b') (x :: a') 0 [] (by simp) (by simp)
    (by intro m hm; exact ⟨fun _ => by simp, fun i' h => by omega⟩)
  have h1 := latRows_runs hΔ B hB (x :: a') (y :: b') L₁ L₂ ha hb hBB (x :: a') 0 [] (by simp)
    (fun _ m hm => ⟨fun _ => by simp, fun i' h => by omega⟩)
  have h2 := lastD_runs hΔ B hB1 (latticeRows (y :: b') 0 (x :: a') [])
  rw [hrows.1] at h2
  have hls : latticeStates (x :: a') (y :: b') = (latticeRows (y :: b') 0 (x :: a') []).getLast?.getD [] := rfl
  rw [hls]
  refine Runs.mk (hΔ _ _ Δ_latticeStates) ?_
  ev_start
  · ev_run
  · omega

theorem fstF_runs (ctx : Val) (s : LState) : Runs Δ' B fFstF [ctx, toVal s] (toVal s.1) 3 := by
  refine Runs.mk (hΔ _ _ Δ_fstF) ?_
  ev_start
  · ev_run
  · omega

/-- **`ringTypList`**: cost `6000 (|a|+1)(|b|+1) (4^(L₁+L₂+1)+1)^2 (2(L₁+L₂)+3)^2` for entries `≤ L₁`, `≤ L₂`. -/
theorem ringTypList_runs (hB : 200 < B) (a b : List ℕ) (L₁ L₂ : ℕ) (ha : ∀ x ∈ a, x ≤ L₁)
    (hb : ∀ x ∈ b, x ≤ L₂) (hBB : L₁ + L₂ + a.length + b.length + 8 < B) :
    Runs Δ' B fRingTypList [toVal a, toVal b] (toVal (ringTypList a b))
      (6000 * (a.length + 1) * (b.length + 1) * (4 ^ (L₁ + L₂ + 1) + 1) ^ 2 * (2 * (L₁ + L₂) + 1 + 2) ^ 2) := by
  have h1 := latticeStates_runs hΔ B hB a b L₁ L₂ ha hb hBB
  have hlen := latticeStates_length_le ha hb
  have h2 := Lib1.map_runs (ext1' hΔ) B fFstF (Val.nat 0) Prod.fst (fun _ => 3) (latticeStates a b)
    (fun s _ => fstF_runs hΔ B (Val.nat 0) s)
  have hs : ((latticeStates a b).map (fun _ => 3)).sum = 3 * (latticeStates a b).length := by
    generalize latticeStates a b = m
    induction m with
    | nil => simp
    | cons x m ih => simp; omega
  rw [hs] at h2
  have hfF : fFstF < B := by show 151 < B; omega
  have hA := ringArith a.length b.length (4 ^ (L₁ + L₂ + 1)) (2 * (L₁ + L₂) + 1)
  refine Runs.mk (hΔ _ _ Δ_ringTypList) ?_
  show EvLe Δ' B _ ringTypListTm (toVal ((latticeStates a b).map Prod.fst)) _
  ev_start
  · ev_run
  · simp only [rowB, cellB, NB, LB] at *
    omega

/-- the cost of `ringTypList a b` in the entries' maxima -/
def ringCost (p : List ℕ × List ℕ) : ℕ :=
  6000 * (p.1.length + 1) * (p.2.length + 1) * (4 ^ (maxOf p.1 + maxOf p.2 + 1) + 1) ^ 2 *
    (2 * (maxOf p.1 + maxOf p.2) + 1 + 2) ^ 2 + 8

end proofs
end E1C
end Lax117284Proofs.Treewidth.Fun
