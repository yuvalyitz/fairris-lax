import Lax117284Proofs.Treewidth.Fun.E2
import Lax117284Proofs.Treewidth.Fun.E3Assembly

/-!
# WP E4 (1): the table `e4Tbl` (ids `384 … 447`) — `nbrs`, `forgetTable`, `introTable`, `joinTable`, `tables`

`Adj` (a function) is not a value, so every function that reads adjacency takes the graph word `x : List ℕ` and reads
`adjOfWord x u v` (`= decide (u < n ∧ v < n ∧ x[1 + u n + v] = 1)`, `n = x[0]`, out of range `= 0`) with the library's `nth`.

| id | function | arguments |
|---|---|---|
| 384 `fAdjW` | `adjOfWord x u v` (a Boolean) | `[x, u, v]` |
| 385 `fNbrPred` | `w ↦ adjOfWord x v w` (`filter` callee, context `(x, v)`) | `[(x, v), w]` |
| 386 `fNbrs` | `nbrs (adjOfWord x) v B` | `[x, v, B]` |
| 387 `fNtBag` | `NT.bag nt` | `[nt]` |
| 388 `fForgetTable` | `forgetTable x T` | `[x, T]` |
| 389 `fIntroCb` | `t ↦ introC kmax v N t` (`flatMap` callee, context `(kmax, v, N)`) | `[(kmax, v, N), t]` |
| 390 `fIntroTable` | `introTable kmax v N T` | `[kmax, v, N, T]` |
| 391 `fJoinInner` | `cb ↦ joinC kmax ca cb` (context `(kmax, ca)`) | `[(kmax, ca), cb]` |
| 392 `fJoinOuter` | `ca ↦ Tb.flatMap (joinC kmax ca ·)` (context `(kmax, Tb)`) | `[(kmax, Tb), ca]` |
| 393 `fJoinTable` | `joinTable kmax Ta Tb` | `[kmax, Ta, Tb]` |
| 394 `fTables` | `tables (adjOfWord x) k nt` | `[x, k, nt]` |
| 395 `fTablesUn` | the same on the packed argument `(x, k, nt)` | `[p]` |
| 396 `fTablesFirst` | `(tables (adjOfWord x) k nt).head?` | `[x, k, nt]` |

`forgetTable`, `introTable`, `joinTable` are exactly the Lean definitions (`dedup` of a `map` / `flatMap`), so the
value of a run is *literally* the Lean function; only the cost needs the size bounds of P1.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open Lib1

/-- the number of vertices of a graph word -/
def nOfWord (x : List ℕ) : ℕ := x.getD 0 0

/-- the adjacency relation of a graph word (identical to `MachineTodo.adjOfWord` of `proofs-todo/Machine.lean`) -/
def adjOfWord (x : List ℕ) : Lax117284Proofs.Treewidth.Chars.Adj :=
  fun u v => decide (u < nOfWord x ∧ v < nOfWord x ∧ x.getD (1 + u * nOfWord x + v) 0 = 1)

abbrev fAdjW : ℕ := 384
abbrev fNbrPred : ℕ := 385
abbrev fNbrs : ℕ := 386
abbrev fNtBag : ℕ := 387
abbrev fForgetTable : ℕ := 388
abbrev fIntroCb : ℕ := 389
abbrev fIntroTable : ℕ := 390
abbrev fJoinInner : ℕ := 391
abbrev fJoinOuter : ℕ := 392
abbrev fJoinTable : ℕ := 393
abbrev fTables : ℕ := 394
abbrev fTablesUn : ℕ := 395
abbrev fTablesFirst : ℕ := 396

/-- `adjOfWord x u v`: `n := x[0]`; `u < n ∧ v < n ∧ x[1 + u n + v] = 1` (the multiplication only happens when `u < n`). -/
def adjWTm : Tm :=
  .letE (.call fNth [V 0, .lit 0])
    (.ite (.lt (V 2) (V 0))
      (.ite (.lt (V 3) (V 0))
        (.eq (.call fNth [V 1, .add (.add (.lit 1) (.mul (V 2) (V 0))) (V 3)]) (.lit 1))
        (.lit 0))
      (.lit 0))

def nbrPredTm : Tm := .call fAdjW [.fst (V 0), .snd (V 0), V 1]

def nbrsTm : Tm := .call fFilter [.lit fNbrPred, .cons (V 0) (V 1), V 2]

def ntBagTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.eq (.fst (V 0)) (.lit 1))
      (.call Lib3.fInsertS [.fst (.snd (V 0)), .call fNtBag [.snd (.snd (V 0))]])
      (.ite (.eq (.fst (V 0)) (.lit 2))
        (.call Lib3.fEraseS [.fst (.snd (V 0)), .call fNtBag [.snd (.snd (V 0))]])
        (.call fNtBag [.fst (.snd (V 0))])))

def forgetTableTm : Tm := .call Lib2.fDedup [.call fMap [.lit E2.fForgetC, V 0, V 1]]

def introCbTm : Tm := .call E3C.fIntroC [.fst (V 0), .fst (.snd (V 0)), .snd (.snd (V 0)), V 1]

def introTableTm : Tm :=
  .call Lib2.fDedup [.call fFlatMap [.lit fIntroCb, .cons (V 0) (.cons (V 1) (V 2)), V 3]]

def joinInnerTm : Tm := .call E2.fJoinC [.fst (V 0), .snd (V 0), V 1]

def joinOuterTm : Tm := .call fFlatMap [.lit fJoinInner, .cons (.fst (V 0)) (V 1), .snd (V 0)]

def joinTableTm : Tm :=
  .call Lib2.fDedup [.call fFlatMap [.lit fJoinOuter, .cons (V 0) (V 2), V 1]]

/-- the value of `CT.start = node ∅ [0] []` -/
def startTm : Tm := .cons (.lit 0) (.cons (.cons (.lit 0) (.lit 0)) (.lit 0))

/-- `tables`: environment `[x, k, nt]`; the `letE` environment is `[T, x, k, nt]`. -/
def tablesTm : Tm :=
  .ite (.isNat (V 2))
    (.cons startTm (.lit 0))
    (.ite (.eq (.fst (V 2)) (.lit 1))
      (.letE (.call fTables [V 0, V 1, .snd (.snd (V 2))])
        (.call fIntroTable [.add (V 2) (.lit 1), .fst (.snd (V 3)),
          .call fNbrs [V 1, .fst (.snd (V 3)), .call fNtBag [.snd (.snd (V 3))]], V 0]))
      (.ite (.eq (.fst (V 2)) (.lit 2))
        (.call fForgetTable [.fst (.snd (V 2)), .call fTables [V 0, V 1, .snd (.snd (V 2))]])
        (.call fJoinTable [.add (V 1) (.lit 1), .call fTables [V 0, V 1, .fst (.snd (V 2))],
          .call fTables [V 0, V 1, .snd (.snd (V 2))]])))

def tablesUnTm : Tm := .call fTables [.fst (V 0), .fst (.snd (V 0)), .snd (.snd (V 0))]

def tablesFirstTm : Tm := .call Lib4.fHead [.call fTables [V 0, V 1, V 2]]

/-- the functions of WP E4: ids `384 … 396` -/
def e4Tbl : ℕ → Option Tm := fun f =>
  match f with
  | 384 => some adjWTm | 385 => some nbrPredTm | 386 => some nbrsTm | 387 => some ntBagTm
  | 388 => some forgetTableTm | 389 => some introCbTm | 390 => some introTableTm
  | 391 => some joinInnerTm | 392 => some joinOuterTm | 393 => some joinTableTm
  | 394 => some tablesTm | 395 => some tablesUnTm | 396 => some tablesFirstTm
  | _ => none

/-- the E4 layer on top of the library (ids `≥ 128`) -/
def e4Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 e4Tbl

theorem e4Tbl_lt {f : ℕ} {b : Tm} (h : e4Tbl f = some b) : 384 ≤ f ∧ f < 448 := by
  unfold e4Tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem ext_lib : Lib.Δ ⊑ e4Δ := Ext.layer e4Tbl (fun _ _ h => Lib.Δ_lt h)

theorem Δ_adjW : e4Δ fAdjW = some adjWTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fAdjW by decide)]; rfl
theorem Δ_nbrPred : e4Δ fNbrPred = some nbrPredTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fNbrPred by decide)]; rfl
theorem Δ_nbrs : e4Δ fNbrs = some nbrsTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fNbrs by decide)]; rfl
theorem Δ_ntBag : e4Δ fNtBag = some ntBagTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fNtBag by decide)]; rfl
theorem Δ_forgetTable : e4Δ fForgetTable = some forgetTableTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fForgetTable by decide)]; rfl
theorem Δ_introCb : e4Δ fIntroCb = some introCbTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fIntroCb by decide)]; rfl
theorem Δ_introTable : e4Δ fIntroTable = some introTableTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fIntroTable by decide)]; rfl
theorem Δ_joinInner : e4Δ fJoinInner = some joinInnerTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fJoinInner by decide)]; rfl
theorem Δ_joinOuter : e4Δ fJoinOuter = some joinOuterTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fJoinOuter by decide)]; rfl
theorem Δ_joinTable : e4Δ fJoinTable = some joinTableTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fJoinTable by decide)]; rfl
theorem Δ_tables : e4Δ fTables = some tablesTm := by
  simp [e4Δ, layerΔ_ge e4Tbl (show 128 ≤ fTables by decide)]; rfl

/-- The hypotheses on a table `Δ'` used by every theorem of WP E4: it contains the tables of E1, E2 (with
`ringTypList` at `E1C.fRingTypList = 152`), E3 and the E4 layer. -/
structure Ext4 (Δ' : ℕ → Option Tm) : Prop where
  e1 : E1.e1Δ ⊑ Δ'
  e2 : E2.e2Δ E1C.fRingTypList ⊑ Δ'
  e3 : E3C.Δ ⊑ Δ'
  e4 : e4Δ ⊑ Δ'

namespace Ext4
variable {Δ' : ℕ → Option Tm} (h : Ext4 Δ')
include h

theorem lib : Lib.Δ ⊑ Δ' := Ext.trans ext_lib h.e4
theorem l1 : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 h.lib
theorem l2 : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 h.lib
theorem l3 : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 h.lib
theorem l4 : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 h.lib

end Ext4

end E4
end Lax117284Proofs.Treewidth.Fun
