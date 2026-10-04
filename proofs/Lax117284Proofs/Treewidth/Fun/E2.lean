import Lax117284Proofs.Treewidth.Fun.LibEmbeds
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Fun.E1Seq
import Lax117284Proofs.Treewidth.Size.Statements
import Lax117284Proofs.Treewidth.Size.Lattice
import Lax117284Proofs.Treewidth.Fun.E1

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Defs` -/

section
/-!
# WP E2: the table `e2Tbl` (ids `160 … 255`) — `norm`, `forgetC`, `joinC`, `domCB` as F-functions

Ids:

| id | function | arguments |
|---|---|---|
| 160 `fVerts` | `CT.verts` | `[c]` |
| 161 `fVertsL` | `CT.vertsL` | `[ks]` |
| 162 `fKeyLe` | `decide (key S a ≤ key S b)` | `[S, a, b]` |
| 163 `fSortKids` | `CT.sortKids` | `[S, ks]` |
| 164 `fKeep` | `CT.keep` | `[S, k]` |
| 165 `fNormNode` | `CT.normF`-shaped `normNode` on the *filtered/normalised* kids | `[S, y, ks]` |
| 166 `fNorm` | `CT.norm` | `[c]` |
| 167 `fNormC` | `norm` with a dummy context (calling convention of `map`) | `[ctx, c]` |
| 168 `fRelE` | `CT.relabel (·.erase x)` (also usable as a `map` callee) | `[x, c]` |
| 169 `fForgetC` | `CT.forgetC` | `[x, c]` |
| 170 `fSubC` | `e - c` (`map` callee) | `[c, e]` |
| 171 `fSubMap` | `d.map (· - c)` (`map` callee) | `[c, d]` |
| 172 `fLeK` | `decide (e ≤ kmax)` | `[kmax, e]` |
| 173 `fAllLe` | `d.all (· ≤ kmax)` | `[kmax, d]` |
| 174 `fJoinYs` | the list `ys` of `joinC` | `[S, kmax, y, y']` |
| 175 `fMkNode` | `node S d kk` (`map` callee, context `(S, kk)`) | `[(S, kk), d]` |
| 176 `fMapKK` | `ys.map (node S · kk)` (`flatMap` callee, context `(S, ys)`) | `[(S, ys), kk]` |
| 177 `fJoinC` | `CT.joinC` | `[kmax, a, b]` |
| 178 `fJoinKids` | `CT.joinKids` | `[kmax, ks, ks']` |
| 179 `fConsTo` | `c :: l` | `[c, l]` |
| 180 `fConsAll` | `rest.map (c :: ·)` (`flatMap` callee, context `rest`) | `[rest, c]` |
| 181 `fDomC` | `CT.domCB` | `[a, b]` |
| 182 `fDomCL` | `CT.domCBL` | `[ks, ks']` |

The function `ringTypList` (WP E1) is called through an id `rid` that the assembler chooses (`e2Tbl rid`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open Lib1

abbrev fVerts : ℕ := 160
abbrev fVertsL : ℕ := 161
abbrev fKeyLe : ℕ := 162
abbrev fSortKids : ℕ := 163
abbrev fKeep : ℕ := 164
abbrev fNormNode : ℕ := 165
abbrev fNorm : ℕ := 166
abbrev fNormC : ℕ := 167
abbrev fRelE : ℕ := 168
abbrev fForgetC : ℕ := 169
abbrev fSubC : ℕ := 170
abbrev fSubMap : ℕ := 171
abbrev fLeK : ℕ := 172
abbrev fAllLe : ℕ := 173
abbrev fJoinYs : ℕ := 174
abbrev fMkNode : ℕ := 175
abbrev fMapKK : ℕ := 176
abbrev fJoinC : ℕ := 177
abbrev fJoinKids : ℕ := 178
abbrev fConsTo : ℕ := 179
abbrev fConsAll : ℕ := 180
abbrev fDomC : ℕ := 181
abbrev fDomCL : ℕ := 182

/-- `a ≤ b` as a term (`1 - (b < a)`). -/
abbrev leT (a b : Tm) : Tm := .sub (.lit 1) (.lt b a)

-- accessors of a characteristic `node S y ks = cons S (cons y ks)`
abbrev cS (t : Tm) : Tm := .fst t
abbrev cY (t : Tm) : Tm := .fst (.snd t)
abbrev cK (t : Tm) : Tm := .snd (.snd t)

def vertsTm : Tm := .call Lib3.fUnionS [cS (V 0), .call fVertsL [cK (V 0)]]
def vertsLTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0) (.call Lib3.fUnionS [.call fVerts [.fst (V 0)], .call fVertsL [.snd (V 0)]])

def keyLeTm : Tm :=
  .letE (.call Lib3.fDiffS [.call fVerts [V 1], V 0])
    (.letE (.call Lib3.fDiffS [.call fVerts [V 3], V 1])
      (.ite (.isNat (V 0)) (.lit 1) (.ite (.isNat (V 1)) (.lit 0) (leT (.fst (V 1)) (.fst (V 0))))))

def sortKidsTm : Tm := .call Lib2.fISort [.lit fKeyLe, V 0, V 1]

def keepTm : Tm :=
  .sub (.lit 1) (.mul (.isNat (cK (V 1))) (.call Lib3.fSubsetS [cS (V 1), V 0]))

def normNodeTm : Tm :=
  .letE (.call fFilter [.lit fKeep, V 0, V 2])
    (.ite (.isNat (V 0))
      (.cons (V 1) (.cons (.call fTake [.lit 1, V 2]) (.lit 0)))
      (.ite (.isNat (.snd (V 0)))
        (.ite (.call fEqV [cS (.fst (V 0)), V 1])
          (.cons (V 1) (.cons (.call E1A.fTypical [.call fAppend [V 2, cY (.fst (V 0))]]) (cK (.fst (V 0)))))
          (.cons (V 1) (.cons (V 2) (.cons (.fst (V 0)) (.lit 0)))))
        (.cons (V 1) (.cons (V 2) (.call fSortKids [V 1, V 0])))))

def normTm : Tm :=
  .call fNormNode [cS (V 0), cY (V 0), .call fMap [.lit fNormC, .lit 0, cK (V 0)]]

def normCTm : Tm := .call fNorm [V 1]

def relETm : Tm :=
  .cons (.call Lib3.fEraseS [V 0, cS (V 1)]) (.cons (cY (V 1)) (.call fMap [.lit fRelE, V 0, cK (V 1)]))

def forgetCTm : Tm := .call fNorm [.call fRelE [V 0, V 1]]

def subCTm : Tm := .sub (V 1) (V 0)
def subMapTm : Tm := .call fMap [.lit fSubC, V 0, V 1]
def leKTm : Tm := leT (V 1) (V 0)
def allLeTm : Tm := .call fAll [.lit fLeK, V 0, V 1]

/-- `ys` of `joinC`, given the id `rid` of `ringTypList`. -/
def joinYsTm (rid : ℕ) : Tm :=
  .call fFilter [.lit fAllLe, V 1,
    .call Lib2.fDedup [.call fMap [.lit fSubMap, .call fLength [V 0], .call rid [V 2, V 3]]]]

def mkNodeTm : Tm := .cons (.fst (V 0)) (.cons (V 1) (.snd (V 0)))
def mapKKTm : Tm := .call fMap [.lit fMkNode, .cons (.fst (V 0)) (V 1), .snd (V 0)]

def joinCTm : Tm :=
  .ite (.call fEqV [cS (V 1), cS (V 2)])
    (.ite (.eq (.call fLength [cK (V 1)]) (.call fLength [cK (V 2)]))
      (.letE (.call fJoinYs [cS (V 1), V 0, cY (V 1), cY (V 2)])
        (.letE (.call fJoinKids [V 1, cK (V 2), cK (V 3)])
          (.call fFlatMap [.lit fMapKK, .cons (.fst (V 3)) (V 1), V 0])))
      (.lit 0))
    (.lit 0)

def consToTm : Tm := .cons (V 0) (V 1)
def consAllTm : Tm := .call fMap [.lit fConsTo, V 1, V 0]

def joinKidsTm : Tm :=
  .ite (.isNat (V 1))
    (.ite (.isNat (V 2)) (.cons (.lit 0) (.lit 0)) (.lit 0))
    (.ite (.isNat (V 2)) (.lit 0)
      (.letE (.call fJoinKids [V 0, .snd (V 1), .snd (V 2)])
        (.call fFlatMap [.lit fConsAll, V 0, .call fJoinC [V 1, .fst (V 2), .fst (V 3)]])))

def domCTm : Tm :=
  .ite (.call fEqV [cS (V 0), cS (V 1)])
    (.ite (.call E1A.fDomB [cY (V 0), cY (V 1)]) (.call fDomCL [cK (V 0), cK (V 1)]) (.lit 0))
    (.lit 0)

def domCLTm : Tm :=
  .ite (.isNat (V 0)) (.ite (.isNat (V 1)) (.lit 1) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.call fDomC [.fst (V 0), .fst (V 1)]) (.call fDomCL [.snd (V 0), .snd (V 1)]) (.lit 0)))

/-- the table of WP E2 (ids `160 … 182`); `rid` is the id of `ringTypList` in the assembled table. -/
def e2Tbl (rid : ℕ) : ℕ → Option Tm := fun f =>
  match f with
  | 160 => some vertsTm | 161 => some vertsLTm | 162 => some keyLeTm | 163 => some sortKidsTm
  | 164 => some keepTm | 165 => some normNodeTm | 166 => some normTm | 167 => some normCTm
  | 168 => some relETm | 169 => some forgetCTm | 170 => some subCTm | 171 => some subMapTm
  | 172 => some leKTm | 173 => some allLeTm | 174 => some (joinYsTm rid) | 175 => some mkNodeTm
  | 176 => some mapKKTm | 177 => some joinCTm | 178 => some joinKidsTm | 179 => some consToTm
  | 180 => some consAllTm | 181 => some domCTm | 182 => some domCLTm
  | _ => none

/-- the E2 layer on top of the library -/
def e2Δ (rid : ℕ) : ℕ → Option Tm := layerΔ Lib.Δ 128 (e2Tbl rid)

theorem e2Tbl_lt (rid : ℕ) {f : ℕ} {b : Tm} (h : e2Tbl rid f = some b) : 160 ≤ f ∧ f < 183 := by
  unfold e2Tbl at h
  split at h <;> first | (simp at h; done) | omega

theorem ext_lib (rid : ℕ) : Lib.Δ ⊑ e2Δ rid := Ext.layer (e2Tbl rid) (fun _ _ h => Lib.Δ_lt h)

theorem Δ_verts (rid : ℕ) : e2Δ rid fVerts = some vertsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fVerts by decide)]; rfl
theorem Δ_vertsL (rid : ℕ) : e2Δ rid fVertsL = some vertsLTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fVertsL by decide)]; rfl
theorem Δ_keyLe (rid : ℕ) : e2Δ rid fKeyLe = some keyLeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fKeyLe by decide)]; rfl
theorem Δ_sortKids (rid : ℕ) : e2Δ rid fSortKids = some sortKidsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSortKids by decide)]; rfl
theorem Δ_keep (rid : ℕ) : e2Δ rid fKeep = some keepTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fKeep by decide)]; rfl
theorem Δ_normNode (rid : ℕ) : e2Δ rid fNormNode = some normNodeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNormNode by decide)]; rfl
theorem Δ_norm (rid : ℕ) : e2Δ rid fNorm = some normTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNorm by decide)]; rfl
theorem Δ_normC (rid : ℕ) : e2Δ rid fNormC = some normCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fNormC by decide)]; rfl
theorem Δ_relE (rid : ℕ) : e2Δ rid fRelE = some relETm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fRelE by decide)]; rfl
theorem Δ_forgetC (rid : ℕ) : e2Δ rid fForgetC = some forgetCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fForgetC by decide)]; rfl
theorem Δ_subC (rid : ℕ) : e2Δ rid fSubC = some subCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSubC by decide)]; rfl
theorem Δ_subMap (rid : ℕ) : e2Δ rid fSubMap = some subMapTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fSubMap by decide)]; rfl
theorem Δ_leK (rid : ℕ) : e2Δ rid fLeK = some leKTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fLeK by decide)]; rfl
theorem Δ_allLe (rid : ℕ) : e2Δ rid fAllLe = some allLeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fAllLe by decide)]; rfl
theorem Δ_joinYs (rid : ℕ) : e2Δ rid fJoinYs = some (joinYsTm rid) := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinYs by decide)]; rfl
theorem Δ_mkNode (rid : ℕ) : e2Δ rid fMkNode = some mkNodeTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fMkNode by decide)]; rfl
theorem Δ_mapKK (rid : ℕ) : e2Δ rid fMapKK = some mapKKTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fMapKK by decide)]; rfl
theorem Δ_joinC (rid : ℕ) : e2Δ rid fJoinC = some joinCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinC by decide)]; rfl
theorem Δ_joinKids (rid : ℕ) : e2Δ rid fJoinKids = some joinKidsTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fJoinKids by decide)]; rfl
theorem Δ_consTo (rid : ℕ) : e2Δ rid fConsTo = some consToTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fConsTo by decide)]; rfl
theorem Δ_consAll (rid : ℕ) : e2Δ rid fConsAll = some consAllTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fConsAll by decide)]; rfl
theorem Δ_domC (rid : ℕ) : e2Δ rid fDomC = some domCTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fDomC by decide)]; rfl
theorem Δ_domCL (rid : ℕ) : e2Δ rid fDomCL = some domCLTm := by
  simp [e2Δ, layerΔ_ge (e2Tbl rid) (show 128 ≤ fDomCL by decide)]; rfl

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Base` -/

section
/-!
# WP E2 (1): arithmetic of tree recursions, size lemmas, `verts`, `keyLe`, `sortKids`

* `wt c = 2·count c - 1`; `tree_step` : the potential argument that turns a per-node cost `C·(m+1)·s^e`
  (`m` = number of kids) into the whole-tree bound `C·wt c·s^e ≤ 2C·count·s^e`;
* `card_verts_le : |verts c| ≤ sz c`, `sz_relE_le`, `sz_norm_le`;
* `verts_runs`, `keyLe_runs`, `sortKids_runs`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1

/-! ## potentials -/

def wt (c : CT) : ℕ := 2 * c.count - 1

theorem count_ge_one (c : CT) : 1 ≤ c.count := by cases c; simp only [count]; omega

theorem wt_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) : wt (node S y ks) = 2 * countL ks + 1 := by
  simp [wt, count]; omega

theorem sum_wt : ∀ ks : List CT, (ks.map wt).sum + ks.length = 2 * countL ks
  | [] => by simp [countL]
  | k :: ks => by
    have h := sum_wt ks
    have h1 := count_ge_one k
    simp only [List.map_cons, List.sum_cons, List.length_cons, countL, wt]
    omega

theorem sum_le_aux {α : Type} (l : List α) (u : α → ℕ) (C e sc : ℕ) (wf : α → ℕ)
    (h : ∀ a ∈ l, u a ≤ sc) :
    (l.map (fun a => C * wf a * (u a) ^ e)).sum ≤ C * sc ^ e * (l.map wf).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 : u a ^ e ≤ sc ^ e := Nat.pow_le_pow_left (h a (List.mem_cons_self ..)) e
    simp only [List.map_cons, List.sum_cons]
    have h3 : C * wf a * u a ^ e ≤ C * sc ^ e * wf a := by
      calc C * wf a * u a ^ e = C * (wf a) * u a ^ e := rfl
        _ ≤ C * wf a * sc ^ e := Nat.mul_le_mul_left _ h2
        _ = C * sc ^ e * wf a := by ring
    nlinarith

/-- The potential argument: kids' bounds `C·wt k·(u k)^e` plus the local `C·(m+1)·sc^e` fit in `C·wt c·sc^e`. -/
theorem tree_step (ks : List CT) (u : CT → ℕ) (C e sc : ℕ) (h : ∀ k ∈ ks, u k ≤ sc) :
    (ks.map (fun k => C * wt k * (u k) ^ e)).sum + C * (ks.length + 1) * sc ^ e ≤
      C * (2 * countL ks + 1) * sc ^ e := by
  have h1 := sum_le_aux ks u C e sc wt h
  have h2 := sum_wt ks
  have h3 : C * sc ^ e * (ks.map wt).sum + C * (ks.length + 1) * sc ^ e = C * (2 * countL ks + 1) * sc ^ e := by
    rw [← h2]; ring
  omega

/-! ## sizes -/

theorem sz_finset_card (S : Finset ℕ) : S.card ≤ sz S := by rw [sz_finset]; omega

theorem sz_ct_node' (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    sz (node S y ks) = sz S + sz y + sz ks + 2 := by rw [sz_ct_node]; omega

theorem card_vertsL_le (ks : List CT) (h : ∀ k ∈ ks, (verts k).card ≤ sz k) : (vertsL ks).card ≤ sz ks := by
  induction ks with
  | nil => simp [vertsL]
  | cons k ks ih =>
    have h1 := h k (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [sz_cons]
    simp only [vertsL]
    have := Finset.card_union_le (verts k) (vertsL ks)
    omega

theorem card_verts_le (c : CT) : (verts c).card ≤ sz c := by
  induction c using CT.ind with
  | h S y ks ih =>
    have h1 := card_vertsL_le ks ih
    have h2 := Finset.card_union_le S (vertsL ks)
    have h3 := sz_finset_card S
    rw [sz_ct_node']
    have : verts (node S y ks) = S ∪ vertsL ks := rfl
    rw [this]
    have := sz_pos y
    omega

theorem card_vertsL_le' (ks : List CT) : (vertsL ks).card ≤ sz ks :=
  card_vertsL_le ks (fun k _ => card_verts_le k)

theorem sz_le_of_mem_kids {k : CT} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : k ∈ ks) :
    sz k < sz (node S y ks) := by
  have := sz_le_of_mem h
  rw [sz_ct_node']
  have := sz_pos S; have := sz_pos y
  omega

theorem sz_S_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz S < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos y; have := sz_pos ks; omega

theorem sz_y_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz y < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos S; have := sz_pos ks; omega

theorem sz_ks_le (S : Finset ℕ) (y : List ℕ) (ks : List CT) : sz ks < sz (node S y ks) := by
  rw [sz_ct_node']; have := sz_pos S; have := sz_pos y; omega

/-! ## `Ext` plumbing -/

section ext
variable {rid : ℕ} {Δ' : ℕ → Option Tm}

theorem ext1 (hΔ : e2Δ rid ⊑ Δ') : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans (ext_lib rid) hΔ)
theorem ext2 (hΔ : e2Δ rid ⊑ Δ') : Lib2.Δ ⊑ Δ' := Ext.trans Lib.ext2 (Ext.trans (ext_lib rid) hΔ)
theorem ext3 (hΔ : e2Δ rid ⊑ Δ') : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans (ext_lib rid) hΔ)
theorem ext4 (hΔ : e2Δ rid ⊑ Δ') : Lib4.Δ ⊑ Δ' := Ext.trans Lib.ext4 (Ext.trans (ext_lib rid) hΔ)
end ext

/-! ## `verts` -/

section verts
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem vertsL_runs (ks : List CT) (cv : CT → ℕ) (s : ℕ) (hs : (vertsL ks).card ≤ s)
    (hB : (ks.map cv).sum + ks.length * (120 * s + 40) + 10 + 8 * s + 8 < B)
    (hf : ∀ k ∈ ks, Runs Δ' B fVerts [toVal k] (toVal (verts k)) (cv k)) :
    Runs Δ' B fVertsL [toVal ks] (toVal (vertsL ks)) ((ks.map cv).sum + ks.length * (120 * s + 40) + 10) := by
  induction ks with
  | nil =>
    refine Runs.mk (hΔ _ _ (Δ_vertsL rid)) ?_
    simp only [vertsL, toVal_empty_finset]
    ev_start
    · ev_run
    · simp
  | cons k ks ih =>
    have hsub : vertsL ks ⊆ vertsL (k :: ks) := Finset.subset_union_right
    have hsub' : verts k ⊆ vertsL (k :: ks) := Finset.subset_union_left
    have hs1 : (vertsL ks).card ≤ s := le_trans (Finset.card_le_card hsub) hs
    have hs2 : (verts k).card ≤ s := le_trans (Finset.card_le_card hsub') hs
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hB
    have ih := ih hs1 (by nlinarith [Nat.zero_le (ks.length * (120 * s + 40))])
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have h1 := hf k (List.mem_cons_self ..)
    have h2 := Lib3.union_runs (ext3 hΔ) B (verts k) (vertsL ks)
    refine Runs.mk (hΔ _ _ (Δ_vertsL rid)) ?_
    simp only [vertsL]
    ev_start
    · ev_run
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith [Nat.zero_le (ks.length * (120 * s + 40))]

theorem verts_runs (c : CT) (hB : 300 * (2 * count c) * sz c + 300 < B) :
    Runs Δ' B fVerts [toVal c] (toVal (verts c)) (220 * wt c * sz c) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcs := card_vertsL_le' ks
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hcard := card_verts_le (node S y ks)
    have hcnt := count_ge_one (node S y ks)
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hvl := vertsL_runs hΔ B ks (fun k => 220 * wt k * sz k) (sz ks) hcs (by
        have := tree_step ks sz 220 1 (sz (node S y ks)) (fun k hk => (sz_le_of_mem_kids hk).le)
        simp only [pow_one] at this
        have h4 : ks.length ≤ sz ks := length_le_sz ks
        have h5 := sz_pos ks
        nlinarith [Nat.zero_le (ks.length * sz ks), Nat.zero_le (countL ks)])
      (fun k hk => ih k hk (by
        have h6 : count k ≤ count (node S y ks) := by
          have := count_le_countL_of_mem hk; rw [hcnode]; omega
        have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
        nlinarith [Nat.zero_le (count k), Nat.zero_le (sz k)]))
    have h2 := Lib3.union_runs (ext3 hΔ) B S (vertsL ks)
    refine Runs.mk (hΔ _ _ (Δ_verts rid)) ?_
    have hv : verts (node S y ks) = S ∪ vertsL ks := rfl
    rw [hv]
    simp only [toVal_ct]
    ev_start
    · ev_run
    · have hts := tree_step ks sz 220 1 (sz (node S y ks)) (fun k hk => (sz_le_of_mem_kids hk).le)
      simp only [pow_one] at hts
      have h5 : ks.length * (120 * sz ks + 40) ≤ ks.length * (120 * sz (node S y ks)) :=
        Nat.mul_le_mul_left _ (by omega)
      have h6 := sz_finset_card S
      rw [hwt]
      nlinarith

end verts

/-! ## `keyLe`, `sortKids` -/

theorem finset_shape (T : Finset ℕ) :
    (T = ∅ ∧ toVal T = Val.nat 0 ∧ T.min = ⊤) ∨
    (∃ m r, toVal T = Val.cons (Val.nat m) r ∧ T.min = (m : WithTop ℕ)) := by
  by_cases h : T = ∅
  · subst h; left; simp
  · right
    have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 h
    have hcard : 0 < (T.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; exact Finset.card_pos.2 hne
    have h0 := @Finset.min'_eq_sorted_zero _ _ T hne
    have h1 := Finset.coe_min' hne
    generalize hs : T.sort (· ≤ ·) = l at hcard
    cases l with
    | nil => simp at hcard
    | cons m r =>
      refine ⟨m, toVal r, ?_, ?_⟩
      · rw [toVal_finset, hs]; rfl
      · rw [← h1, h0]
        simp [hs]

section key
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem verts_runs_le (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 1000 * (s + 1) ^ 2 < B) :
    Runs Δ' B fVerts [toVal c] (toVal (verts c)) (440 * (s + 1) ^ 2) := by
  have h1 := count_le_sz c
  have h2 : wt c ≤ 2 * count c := by unfold wt; omega
  have h3 : 220 * wt c * sz c ≤ 440 * (s + 1) ^ 2 := by
    have : count c * sz c ≤ (s + 1) ^ 2 := by nlinarith [Nat.zero_le (sz c)]
    nlinarith [Nat.zero_le (wt c), Nat.zero_le (sz c)]
  refine (verts_runs hΔ B c ?_).mono h3
  have : count c * sz c ≤ (s + 1) ^ 2 := by nlinarith [Nat.zero_le (sz c)]
  nlinarith

theorem keyLe_runs (S : Finset ℕ) (a b : CT) (s : ℕ) (hS : sz S ≤ s) (ha : sz a ≤ s) (hb : sz b ≤ s)
    (hB : 1000 * (s + 1) ^ 2 + 100 < B) :
    Runs Δ' B fKeyLe [toVal S, toVal a, toVal b] (toVal (decide (key S a ≤ key S b))) (1000 * (s + 1) ^ 2) := by
  have hsq : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hva := verts_runs_le hΔ B a s ha (by omega)
  have hvb := verts_runs_le hΔ B b s hb (by omega)
  have hda := Lib3.sdiff_runs (ext3 hΔ) B (verts a) S
  have hdb := Lib3.sdiff_runs (ext3 hΔ) B (verts b) S
  have ca := card_verts_le a
  have cb := card_verts_le b
  have cS := sz_finset_card S
  have hda' : Runs Δ' B Lib3.fDiffS [toVal (verts a), toVal S] (toVal (verts a \ S)) (60 * (2 * s) + 20) :=
    hda.mono (by omega)
  have hdb' : Runs Δ' B Lib3.fDiffS [toVal (verts b), toVal S] (toVal (verts b \ S)) (60 * (2 * s) + 20) :=
    hdb.mono (by omega)
  clear hda hdb
  refine Runs.mk (hΔ _ _ (Δ_keyLe rid)) ?_
  rcases finset_shape (verts a \ S) with ⟨he1, hv1, hm1⟩ | ⟨m1, r1, hv1, hm1⟩ <;>
  rcases finset_shape (verts b \ S) with ⟨he2, hv2, hm2⟩ | ⟨m2, r2, hv2, hm2⟩ <;>
  rw [hv1] at hda' <;> rw [hv2] at hdb'
  · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · have : decide (key S a ≤ key S b) = false := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2]
    rw [this]
    ev_start
    · ev_run
    · nlinarith
  · by_cases hle : m1 ≤ m2
    · have : decide (key S a ≤ key S b) = true := by simp [key, hm1, hm2, hle]
      rw [this]
      have h' : ¬ m2 < m1 := by omega
      ev_start
      · ev_run
      · nlinarith
    · have : decide (key S a ≤ key S b) = false := by simp [key, hm1, hm2, hle]
      rw [this]
      have h' : m2 < m1 := by omega
      ev_start
      · ev_run
      · nlinarith

theorem sortKids_runs (S : Finset ℕ) (ks : List CT) (s : ℕ) (hS : sz S ≤ s) (hks : sz ks ≤ s)
    (hB : 1200 * (s + 1) ^ 4 < B) :
    Runs Δ' B fSortKids [toVal S, toVal ks] (toVal (sortKids S ks)) (1100 * (s + 1) ^ 4) := by
  have hsq : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hs4 : (s + 1) ^ 4 = (s + 1) ^ 2 * (s + 1) ^ 2 := by ring
  have hf : ∀ x ∈ ks, ∀ y ∈ ks, Runs Δ' B fKeyLe [toVal S, toVal x, toVal y]
      (toVal (decide (key S x ≤ key S y))) (1000 * (s + 1) ^ 2) := fun x hx y hy =>
    keyLe_runs hΔ B S x y s hS (le_trans (sz_le_of_mem hx) hks) (le_trans (sz_le_of_mem hy) hks) (by nlinarith)
  have h := Lib2.mergeSort_runs (ext2 hΔ) B fKeyLe (toVal S) (fun a b => decide (key S a ≤ key S b)) (1000 * (s + 1) ^ 2)
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact le_trans h1 h2)
    (by intro a b; simpa using le_total (key S a) (key S b)) ks hf
  have hl : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have hl2 : (ks.length + 1) ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlt : fKeyLe < B := by
    show 162 < B
    nlinarith
  refine Runs.mk (hΔ _ _ (Δ_sortKids rid)) ?_
  unfold sortKids
  ev_start
  · ev_run
  · nlinarith

end key

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Sz` -/

section
/-!
# WP E2 (2): sizes never grow under `norm`, `relabel (erase ·)`, `filter`, `sort`, `typical`

`sz_norm_le : sz (norm c) ≤ sz c` and the same for `forgetC`.  These make the cost of `norm` and `forgetC` bounds in terms of
the *input* size only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lax117284Proofs.Treewidth.Seq

theorem sz_filter_le {α : Type} [ToVal α] (p : α → Bool) : ∀ l : List α, sz (l.filter p) ≤ sz l
  | [] => by simp
  | a :: l => by
    have ih := sz_filter_le p l
    rw [List.filter_cons]
    split_ifs
    · rw [sz_cons, sz_cons]; omega
    · rw [sz_cons]; omega

theorem sz_map_le {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_perm {α : Type} [ToVal α] {l l' : List α} (h : l.Perm l') : sz l = sz l' := by
  rw [sz_list, sz_list, h.length_eq, (h.map sz).sum_eq]

theorem sz_take_le {α : Type} [ToVal α] (n : ℕ) : ∀ l : List α, sz (l.take n) ≤ sz l
  | [] => by simp
  | a :: l => by
    cases n with
    | zero => simp; have := sz_pos (a :: l); omega
    | succ n =>
      have ih := sz_take_le n l
      rw [List.take_succ_cons, sz_cons, sz_cons]; omega

theorem typical_length_le_length_aux (t : List ℕ) : ∀ (a : List ℕ),
    (a.foldl push t).length ≤ t.length + a.length
  | [] => by simp
  | y :: a => by
    have h := typical_length_le_length_aux (push t y) a
    have h2 : (push t y).length ≤ t.length + 1 := by
      simp only [push, List.length_append, List.length_singleton]
      have := E1A.length_cut_le t y; omega
    simp only [List.foldl_cons, List.length_cons]; omega

theorem typical_length_le_length (a : List ℕ) : (typical a).length ≤ a.length := by
  have := typical_length_le_length_aux [] a
  simpa [typical] using this

theorem sz_typical_le (a : List ℕ) : sz (typical a) ≤ sz a := by
  rw [sz_list_nat, sz_list_nat]
  have := typical_length_le_length a
  omega

theorem sz_mem_add_two {α : Type} [ToVal α] {a : α} {l : List α} (h : a ∈ l) : sz a + 2 ≤ sz l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [sz_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have := sz_pos l; omega
    · have := ih h; have := sz_pos b; omega

theorem sz_norm_le : ∀ c : CT, sz (norm c) ≤ sz c := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    have hmap : sz (ks.map norm) ≤ sz ks := sz_map_le norm ks ih
    rw [norm_node']
    have hFsz := sz_filter_le (keep S) (ks.map norm)
    have hFmem : ∀ k ∈ (ks.map norm).filter (keep S), sz k + 2 ≤ sz ks := by
      intro k hk
      have hk' := (List.mem_filter.1 hk).1
      obtain ⟨k', hk'', rfl⟩ := List.mem_map.1 hk'
      have := sz_mem_add_two hk''
      have := ih k' hk''
      omega
    generalize (ks.map norm).filter (keep S) = F at hFsz hFmem
    have hy := sz_take_le 1 y
    have hp1 := sz_pos ks
    rw [sz_ct_node' S y ks]
    cases F with
    | nil =>
      rw [normF_nil, sz_ct_node']
      have : sz ([] : List CT) = 1 := rfl
      omega
    | cons k F' =>
      cases F' with
      | nil =>
        have hk := hFmem k (by simp)
        rw [normF_single]
        split_ifs with hS
        · obtain ⟨kS, ky, kks⟩ := k
          simp only [CT.S, CT.y, CT.kids]
          rw [sz_ct_node']
          have h1 := sz_typical_le (y ++ ky)
          have h2 := sz_append y ky
          rw [sz_ct_node'] at hk
          omega
        · rw [sz_ct_node']
          have : sz [k] = sz k + 2 := by rw [sz_cons]; rfl
          omega
      | cons k2 F'' =>
        rw [normF_ge2, sz_ct_node', sz_perm (sortKids_perm S _)]
        omega

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Norm` -/

section
/-!
# WP E2 (3): `keep`, `normNode`, `norm` as F-functions

* `keep_runs`, `normNode_runs` (cost `3000 (m+1) (s+1)^4`, `m` = number of kids);
* `norm_runs_aux` : `Runs fNorm [toVal c] (toVal (norm c)) (3100 · wt c · (sz c + 1)^4)`, `wt c = 2 count c - 1`
  (the per-node local cost is charged through the potential `tree_step` of `E2Base`);
* `norm_runs` : cost `6200 (s + 1)^5` for `sz c ≤ s`, hypothesis `14000 (s+1)^5 < B`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

theorem length_le_countL : ∀ ks : List CT, ks.length ≤ countL ks
  | [] => by simp [countL]
  | k :: ks => by
    have := length_le_countL ks; have := count_ge_one k
    simp only [List.length_cons, countL]; omega

theorem sum_map_add_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

section norm
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hE in
theorem keep_runs (S : Finset ℕ) (k : CT) (s : ℕ) (hS : sz S ≤ s) (hk : sz k ≤ s) (hB : 200 * (s + 1) < B) :
    Runs Δ' B fKeep [toVal S, toVal k] (toVal (keep S k)) (130 * (s + 1)) := by
  obtain ⟨kS, ky, kks⟩ := k
  have hSk : sz kS ≤ s := by have := sz_S_le kS ky kks; omega
  have hB1 : 1 < B := by omega
  have h1 := sz_finset_card S
  have h2 := sz_finset_card kS
  have hsub := Lib3.subset_runs (ext3 hΔ) B (by omega) kS S (decide (kS ⊆ S)) (by simp)
  have hsub' : Runs Δ' B Lib3.fSubsetS [toVal kS, toVal S] (toVal (decide (kS ⊆ S))) (120 * s + 20) :=
    hsub.mono (by omega)
  clear hsub
  refine Runs.mk (hΔ _ _ (Δ_keep rid)) ?_
  simp only [toVal_ct]
  cases kks with
  | nil =>
    by_cases hs : kS ⊆ S
    · have : keep S (node kS ky []) = false := by simp [keep, isLeaf, CT.kids, CT.S, hs]
      rw [this]
      simp only [hs, decide_true] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · have : keep S (node kS ky []) = true := by simp [keep, isLeaf, CT.kids, CT.S, hs]
      rw [this]
      simp only [hs, decide_false] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
  | cons k ks =>
    have : keep S (node kS ky (k :: ks)) = true := by simp [keep, isLeaf, CT.kids]
    rw [this]
    ev_start
    · ev_run
    · omega

include hE in
theorem normNode_runs (S : Finset ℕ) (y : List ℕ) (ks : List CT) (s : ℕ)
    (hS : sz S ≤ s) (hy : sz y ≤ s) (hks : sz ks ≤ s) (hB : 4000 * (ks.length + 1) * (s + 1) ^ 4 < B) :
    Runs Δ' B fNormNode [toVal S, toVal y, toVal ks] (toVal (normNode S y ks))
      (3000 * (ks.length + 1) * (s + 1) ^ 4) := by
  have hm : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have h1 : s + 1 ≤ (s + 1) ^ 4 := by
    calc s + 1 = (s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (s + 1) ^ 3 ≤ (s + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h0 : 1 ≤ (s + 1) ^ 4 := le_trans (by omega) h1
  have hQ1 : (ks.length + 1) * (s + 1) ≤ (ks.length + 1) * (s + 1) ^ 4 := Nat.mul_le_mul_left _ h1
  have hQ2 : (s + 1) ^ 4 ≤ (ks.length + 1) * (s + 1) ^ 4 := by nlinarith
  have hB1 : 1 < B := by nlinarith
  have hkeep : fKeep < B := by show 164 < B; nlinarith
  have hfilt := Lib1.filter_runs (ext1 hΔ) B fKeep (toVal S) (keep S) (fun _ => 130 * (s + 1)) ks
    (fun k hk => keep_runs hΔ B S k s hS (le_trans (sz_le_of_mem hk) hks) (by nlinarith))
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hfilt
  have hfilt' : Runs Δ' B fFilter [.nat fKeep, toVal S, toVal ks] (toVal (ks.filter (keep S)))
      (200 * ((ks.length + 1) * (s + 1) ^ 4)) := hfilt.mono (by nlinarith)
  clear hfilt
  have hFsz := sz_filter_le (keep S) ks
  rw [normNode_eq]
  refine Runs.mk (hΔ _ _ (Δ_normNode rid)) ?_
  generalize hF : ks.filter (keep S) = F at hfilt' hFsz ⊢
  cases F with
  | nil =>
    have htake := Lib1.take_runs (ext1 hΔ) B 1 y hB1
    rw [normF_nil]
    simp only [toVal_ct]
    ev_start
    · ev_run
    · have := min_le_left 1 y.length
      nlinarith
  | cons k F' =>
    cases F' with
    | nil =>
      have hk1 : sz [k] ≤ s := le_trans hFsz hks
      have hk2 : sz k + 2 ≤ sz [k] := sz_mem_add_two (List.mem_singleton_self k)
      obtain ⟨kS, ky, kks⟩ := k
      have hn := sz_ct_node' kS ky kks
      have hkS : sz kS ≤ s := by omega
      have hky : sz ky ≤ s := by omega
      have hkks : sz kks ≤ s := by omega
      have hly : y.length ≤ s := le_trans (length_le_sz y) hy
      have hlky : ky.length ≤ s := le_trans (length_le_sz ky) hky
      have hlt : ((y ++ ky).length + 1) ^ 3 ≤ 8 * (s + 1) ^ 3 := by
        have : (y ++ ky).length + 1 ≤ 2 * (s + 1) := by simp only [List.length_append]; omega
        calc ((y ++ ky).length + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := Nat.pow_le_pow_left this 3
          _ = 8 * (s + 1) ^ 3 := by ring
      have happ := Lib1.append_runs (ext1 hΔ) B y ky
      have htyp := E1A.typical_runs hE B hB1 (y ++ ky)
      have hmin : ∀ a b : ℕ, min a b ≤ a := fun a b => min_le_left a b
      by_cases hSk : kS = S
      · have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 kS S true (by simp [hSk])
        have hcond : (node kS ky kks).S = S := hSk
        rw [normF_single, if_pos hcond]
        simp only [CT.y, CT.kids]
        simp only [toVal_ct]
        simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' ⊢
        ev_start
        · ev_run
        · have := hmin (sz kS) (sz S)
          have := min_le_left (30 * min (sz kS) (sz S)) 0
          nlinarith
      · have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 kS S false (by simp [hSk])
        have hcond : ¬ (node kS ky kks).S = S := hSk
        rw [normF_single, if_neg hcond]
        simp only [toVal_ct]
        simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' ⊢
        ev_start
        · ev_run
        · have := hmin (sz kS) (sz S)
          nlinarith
    | cons k2 F'' =>
      have hsort := sortKids_runs hΔ B S (k :: k2 :: F'') s hS (le_trans hFsz hks) (by nlinarith)
      have hsrt : fSortKids < B := by show 163 < B; nlinarith
      rw [normF_ge2]
      simp only [toVal_ct]
      simp only [toVal_cons, toVal_nil, toVal_ct] at hfilt' hsort ⊢
      ev_start
      · ev_run
      · nlinarith

include hE in
theorem norm_runs_aux (c : CT) (hB : 7000 * (2 * count c) * (sz c + 1) ^ 4 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (3100 * wt c * (sz c + 1) ^ 4) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hyz := sz_y_le S y ks
    set T := (sz (node S y ks) + 1) ^ 4 with hT
    have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
    have hm : ks.length ≤ sz ks := length_le_sz ks
    have hcpos := count_ge_one (node S y ks)
    have hcm : ks.length + 1 ≤ count (node S y ks) := by
      have := length_le_countL ks; rw [hcnode]; omega
    have hB' : 4000 * (ks.length + 1) * T < B := by nlinarith
    have hnn := normNode_runs hΔ hE B S y (ks.map norm) (sz (node S y ks)) (by omega) (by omega)
      (by have := sz_map_le norm ks (fun k hk => sz_norm_le k); omega) (by rw [List.length_map]; exact hB')
    have hnormC : ∀ k ∈ ks, Runs Δ' B fNormC [Val.nat 0, toVal k] (toVal (norm k))
        (3100 * wt k * (sz k + 1) ^ 4 + 3) := by
      intro k hk
      have hk1 := ih k hk (by
        have h6 : count k ≤ count (node S y ks) := by
          have := count_le_countL_of_mem hk; rw [hcnode]; omega
        have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
        have h8 : (sz k + 1) ^ 4 ≤ T := Nat.pow_le_pow_left (by omega) 4
        have h9 : 7000 * (2 * count k) * (sz k + 1) ^ 4 ≤ 7000 * (2 * count (node S y ks)) * T :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)) h8
        exact lt_of_le_of_lt h9 hB)
      refine Runs.mk (hΔ _ _ (Δ_normC rid)) ?_
      ev_start
      · ev_run
      · omega
    have hmap := Lib1.map_runs (ext1 hΔ) B fNormC (Val.nat 0) norm (fun k => 3100 * wt k * (sz k + 1) ^ 4 + 3) ks hnormC
    have hlit : fNormC < B := by show 167 < B; nlinarith
    have hts := tree_step ks (fun k => sz k + 1) 3100 4 (sz (node S y ks) + 1)
      (fun k hk => by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
    rw [sum_map_add_const] at hmap
    simp only [List.length_map] at hnn
    rw [← hT] at hts hnn
    rw [norm_node, normL_eq_map]
    refine Runs.mk (hΔ _ _ (Δ_norm rid)) ?_
    simp only [toVal_ct]
    ev_start
    · ev_run
    · rw [hwt]
      have := Nat.mul_le_mul_left (ks.length + 1) hT1
      nlinarith

include hE in
theorem norm_runs (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5) := by
  have h1 := count_le_sz c
  have hT : (sz c + 1) ^ 5 ≤ (s + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hp4 : (s + 1) ^ 4 * (s + 1) = (s + 1) ^ 5 := by ring
  have hp4' : (sz c + 1) ^ 4 ≤ (s + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h2 : 2 * count c * (sz c + 1) ^ 4 ≤ 2 * (s + 1) ^ 5 := by
    have : count c ≤ s + 1 := by omega
    calc 2 * count c * (sz c + 1) ^ 4 ≤ 2 * (s + 1) * (s + 1) ^ 4 :=
          Nat.mul_le_mul (by omega) hp4'
      _ = 2 * (s + 1) ^ 5 := by rw [← hp4]; ring
  refine (norm_runs_aux hΔ hE B c (by nlinarith)).mono ?_
  have h3 : wt c ≤ 2 * count c := by unfold wt; omega
  calc 3100 * wt c * (sz c + 1) ^ 4 ≤ 3100 * (2 * count c) * (sz c + 1) ^ 4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = 3100 * (2 * count c * (sz c + 1) ^ 4) := by ring
    _ ≤ 3100 * (2 * (s + 1) ^ 5) := Nat.mul_le_mul_left _ h2
    _ = 6200 * (s + 1) ^ 5 := by ring

end norm

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Forget` -/

section
/-!
# WP E2 (4): `forgetC` as an F-function

`relE x c = relabel (·.erase x) c` (id 168, also the `map` callee of its own recursion) and `forgetC x c = norm (relE x c)`.
Cost `≤ 7000 (s + 1)^5` for `sz c ≤ s`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

theorem sz_erase_le (x : ℕ) (S : Finset ℕ) : sz (S.erase x) ≤ sz S := by
  rw [sz_finset, sz_finset]; have := Finset.card_erase_le (a := x) (s := S); omega

theorem sz_relabel_le (x : ℕ) : ∀ c : CT, sz (relabel (fun S => S.erase x) c) ≤ sz c := by
  intro c
  induction c using CT.ind with
  | h S y ks ih =>
    rw [relabel_node, sz_ct_node', sz_ct_node']
    have := sz_map_le (relabel (fun S => S.erase x)) ks ih
    have := sz_erase_le x S
    omega

section forget
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ

omit hE in
theorem relE_runs_aux (x : ℕ) (c : CT) (hB : 300 * (2 * count c) * (sz c + 1) + 300 < B) :
    Runs Δ' B fRelE [toVal x, toVal c] (toVal (relabel (fun S => S.erase x) c)) (100 * wt c * (sz c + 1)) := by
  induction c using CT.ind with
  | h S y ks ih =>
    have hwt := wt_node S y ks
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hsz := sz_ks_le S y ks
    have hSz := sz_S_le S y ks
    have hcS := sz_finset_card S
    have hm : ks.length ≤ sz ks := length_le_sz ks
    have hcpos := count_ge_one (node S y ks)
    have hlit : fRelE < B := by
      show 168 < B
      have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 300) (by omega : 0 < 2 * count (node S y ks))) (by omega : 0 < sz (node S y ks) + 1)
      omega
    have hk : ∀ k ∈ ks, Runs Δ' B fRelE [toVal x, toVal k] (toVal (relabel (fun S => S.erase x) k))
        (100 * wt k * (sz k + 1)) := by
      intro k hk
      refine ih k hk ?_
      have h6 : count k ≤ count (node S y ks) := by
        have := count_le_countL_of_mem hk; rw [hcnode]; omega
      have h7 := sz_le_of_mem_kids (S := S) (y := y) hk
      have h9 : 300 * (2 * count k) * (sz k + 1) ≤ 300 * (2 * count (node S y ks)) * (sz (node S y ks) + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)) (by omega)
      omega
    have hmap := Lib1.map_runs (ext1 hΔ) B fRelE (toVal x) (relabel (fun S => S.erase x))
      (fun k => 100 * wt k * (sz k + 1)) ks hk
    have herase := Lib3.erase_runs (ext3 hΔ) B x S
    have hts := tree_step ks (fun k => sz k + 1) 100 1 (sz (node S y ks) + 1)
      (fun k hk => by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
    simp only [pow_one] at hts
    rw [relabel_node]
    refine Runs.mk (hΔ _ _ (Δ_relE rid)) ?_
    simp only [toVal_ct]
    ev_start
    · ev_run
    · rw [hwt]
      nlinarith

theorem relE_runs (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 1300 * (s + 1) ^ 2 < B) :
    Runs Δ' B fRelE [toVal x, toVal c] (toVal (relabel (fun S => S.erase x) c)) (200 * (s + 1) ^ 2) := by
  have h1 := count_le_sz c
  have h2 : wt c ≤ 2 * count c := by unfold wt; omega
  have h3 : count c * (sz c + 1) ≤ (s + 1) * (s + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : (s + 1) * (s + 1) = (s + 1) ^ 2 := by ring
  refine (relE_runs_aux hΔ B x c ?_).mono ?_
  · nlinarith
  · nlinarith [Nat.zero_le (wt c)]

include hE in
theorem forgetC_runs (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 + 100 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) := by
  have hsq : (s + 1) ^ 2 ≤ (s + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hone : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hr := relE_runs hΔ B x c s hc (by omega)
  have hn := norm_runs hΔ hE B (relabel (fun S => S.erase x) c) s
    (le_trans (sz_relabel_le x c) hc) (by omega)
  refine Runs.mk (hΔ _ _ (Δ_forgetC rid)) ?_
  unfold forgetC
  ev_start
  · ev_run
  · omega

end forget

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Join1` -/

section
/-!
# WP E2 (5): `joinC`, part 1 — Lean-level facts and the helpers (`subMap`, `allLe`, `joinYs`, `mapKK`, `consAll`)

Notation: `xb nb k = cbound nb k 1 = 2^(4(nb+k+2))` (so `cbound nb k m = (xb nb k)^m`);  `4^(2k+1) ≤ xb`, `k+1 ≤ xb`, `256 ≤ xb`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-! ## Lean-level facts -/

/-- `ys` of `joinC`. -/
def joinYsL (c kmax : ℕ) (y y' : List ℕ) : List (List ℕ) :=
  (((ringTypList y y').map (fun d => d.map (· - c))).dedup).filter (fun d => d.all (· ≤ kmax))

theorem cbound_eq_pow (b k m : ℕ) : cbound b k m = (cbound b k 1) ^ m := by
  unfold cbound; rw [← pow_mul]; congr 1; ring

abbrev xb (nb k : ℕ) : ℕ := cbound nb k 1

theorem xb_ge (nb k : ℕ) : 256 ≤ xb nb k := by
  unfold xb cbound
  calc 256 = 2 ^ 8 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem xb_ring (nb k : ℕ) : 4 ^ (2 * k + 1) ≤ xb nb k := by
  unfold xb cbound
  calc 4 ^ (2 * k + 1) = 2 ^ (2 * (2 * k + 1)) := by rw [pow_mul]; norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem xb_k (nb k : ℕ) : k + 1 ≤ xb nb k := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  unfold xb cbound
  have : 2 ^ k ≤ 2 ^ ((2 * nb + 2 * k + 4) * (2 * 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem ringTypList_mem_length_le {a b d : List ℕ} {L₁ L₂ : ℕ} (ha : ∀ x ∈ a, x ≤ L₁) (hb : ∀ x ∈ b, x ≤ L₂)
    (hd : d ∈ ringTypList a b) : d.length ≤ 2 * (L₁ + L₂) + 1 := by
  unfold ringTypList at hd
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hd
  obtain ⟨-, hty⟩ := latticeStates_sound hs
  rw [hty]
  exact typical_length_le' (pathSum_le ha hb _)

theorem countL_eq_sum : ∀ ks : List CT, countL ks = (ks.map count).sum
  | [] => by simp [countL]
  | k :: ks => by simp [countL, countL_eq_sum ks]

theorem sum_pow_le {Z : ℕ} (hZ : 2 ≤ Z) : ∀ l : List ℕ, (∀ c ∈ l, 1 ≤ c) → (l.map (fun c => Z ^ c)).sum ≤ Z ^ l.sum
  | [], _ => by simp
  | c :: l, h => by
    have hc := h c (by simp)
    have ih := sum_pow_le hZ l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, pow_add]
    by_cases hl : l = []
    · subst hl; simp
    · have hs : 1 ≤ l.sum := by
        obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil hl
        have := h x (by simp); simp only [List.sum_cons]; omega
      have h1 : 2 ≤ Z ^ c := le_trans hZ (by calc Z = Z ^ 1 := (pow_one Z).symm
                                                  _ ≤ Z ^ c := Nat.pow_le_pow_right (by omega) hc)
      have h2 : 2 ≤ Z ^ l.sum := le_trans hZ (by calc Z = Z ^ 1 := (pow_one Z).symm
                                                    _ ≤ Z ^ l.sum := Nat.pow_le_pow_right (by omega) hs)
      nlinarith

theorem sum_count_pow_le {Z : ℕ} (hZ : 2 ≤ Z) (ks : List CT) :
    (ks.map (fun k => Z ^ count k)).sum ≤ Z ^ countL ks := by
  have := sum_pow_le hZ (ks.map count) (by intro c hc; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc; exact count_ge_one k)
  rw [countL_eq_sum]
  simpa [List.map_map, Function.comp_def] using this

theorem sum_count_mul (ks : List CT) (R : ℕ) : (ks.map (fun k => count k * R)).sum = countL ks * R := by
  induction ks with
  | nil => simp [countL]
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, countL, ih]; ring

theorem sum_map_const_mul {α : Type} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  simp [List.map_const', List.sum_replicate]

theorem sum_map_le_card {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) (h : ∀ a ∈ l, f a ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  have := List.sum_le_card_nsmul (l.map f) c (by
    intro x hx; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx; exact h a ha)
  simpa using this

/-! ## `Runs` helpers -/

section helpers
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem flatMap_runs_le {α β : Type} [ToVal α] [ToVal β] (fid : ℕ) (ctx : Val) (g : α → List β) (cf : α → ℕ)
    (l : List α) (n c : ℕ) (hn : ∀ a ∈ l, (g a).length ≤ n) (hc : ∀ a ∈ l, cf a ≤ c)
    (hf : ∀ a ∈ l, Runs Δ' B fid [ctx, toVal a] (toVal (g a)) (cf a)) :
    Runs Δ' B fFlatMap [.nat fid, ctx, toVal l] (toVal (l.flatMap g)) (l.length * (c + 10 * n + 20) + 8) := by
  refine (Lib1.flatMap_runs (ext1 hΔ) B fid ctx g cf l hf).mono ?_
  have := sum_map_le_card l (fun a => cf a + 10 * (g a).length + 20) (c + 10 * n + 20)
    (fun a ha => by have := hc a ha; have := hn a ha; omega)
  omega

theorem subC_runs (c e : ℕ) : Runs Δ' B fSubC [toVal c, toVal e] (toVal (e - c)) 4 := by
  refine Runs.mk (hΔ _ _ (Δ_subC rid)) ?_
  ev_start
  · ev_run
  · omega

theorem subMap_runs (c : ℕ) (d : List ℕ) (hB : 1000 + 30 * d.length < B) :
    Runs Δ' B fSubMap [toVal c, toVal d] (toVal (d.map (· - c))) (30 * d.length + 20) := by
  have h := Lib1.map_runs (ext1 hΔ) B fSubC (toVal c) (fun e => e - c) (fun _ => 4) d
    (fun e _ => subC_runs hΔ B c e)
  rw [sum_map_const_mul] at h
  have hl : fSubC < B := by show 170 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_subMap rid)) ?_
  ev_start
  · ev_run
  · omega

theorem leK_runs (kmax e : ℕ) (hB : 1 < B) : Runs Δ' B fLeK [toVal kmax, toVal e] (toVal (decide (e ≤ kmax))) 8 := by
  refine Runs.mk (hΔ _ _ (Δ_leK rid)) ?_
  by_cases h : e ≤ kmax
  · have h' : ¬ kmax < e := by omega
    simp only [h, decide_true, toVal_true]
    ev_start
    · ev_run
    · omega
  · have h' : kmax < e := by omega
    simp only [h, decide_false, toVal_false]
    ev_start
    · ev_run
    · omega

theorem allLe_runs (kmax : ℕ) (d : List ℕ) (hB : 1000 + 30 * d.length < B) :
    Runs Δ' B fAllLe [toVal kmax, toVal d] (toVal (d.all (· ≤ kmax))) (30 * d.length + 20 + 8 * d.length) := by
  have h := Lib1.all_runs (ext1 hΔ) B fLeK (toVal kmax) (fun e => decide (e ≤ kmax)) (fun _ => 8) d
    (fun e _ => leK_runs hΔ B kmax e (by omega)) (by omega)
  rw [sum_map_const_mul] at h
  have hl : fLeK < B := by show 172 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_allLe rid)) ?_
  ev_start
  · ev_run
  · omega

theorem joinYs_runs (S : Finset ℕ) (k : ℕ) (y y' : List ℕ) (R0 X : ℕ)
    (hy : ∀ x ∈ y, x ≤ k) (hy' : ∀ x ∈ y', x ≤ k)
    (hX : 4 ^ (2 * k + 1) ≤ X) (hkX : k + 1 ≤ X) (hX8 : 8 ≤ X)
    (hring : Runs Δ' B rid [toVal y, toVal y'] (toVal (ringTypList y y')) R0)
    (hB : R0 + 8 * S.card + 4000 * X ^ 3 + 1000 < B) :
    Runs Δ' B fJoinYs [toVal S, toVal k, toVal y, toVal y'] (toVal (joinYsL S.card k y y'))
      (R0 + 8 * S.card + 4000 * X ^ 3) := by
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hrl : (ringTypList y y').length ≤ X := by
    have := ringTypList_length_le hy hy'
    have h2 : 4 ^ (k + k + 1) = 4 ^ (2 * k + 1) := by congr 1; omega
    omega
  have hd : ∀ d ∈ ringTypList y y', d.length ≤ 4 * k + 1 := fun d hd' => by
    have := ringTypList_mem_length_le hy hy' hd'; omega
  have hB1 : 1 < B := by omega
  have hcard := Lib4.card_runs (ext4 hΔ) B S (by omega)
  have hmap := Lib1.map_runs (ext1 hΔ) B fSubMap (toVal S.card) (fun d => d.map (· - S.card))
    (fun _ => 120 * k + 50) (ringTypList y y') (fun d hd' =>
      (subMap_runs hΔ B S.card d (by have := hd d hd'; omega)).mono (by have := hd d hd'; omega))
  rw [sum_map_const_mul] at hmap
  have hl2 : ((ringTypList y y').map (fun d => d.map (· - S.card))).length = (ringTypList y y').length := by simp
  have hs2 : ∀ a ∈ (ringTypList y y').map (fun d => d.map (· - S.card)), sz a ≤ 8 * k + 3 := by
    intro a ha
    obtain ⟨d, hd', rfl⟩ := List.mem_map.1 ha
    rw [sz_list_nat, List.length_map]
    have := hd d hd'; omega
  have hdd := Lib2.dedup_runs (ext2 hΔ) B hB1 (8 * k + 3) _ hs2
  have hddl : (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup).length ≤ (ringTypList y y').length := by
    have := (List.dedup_sublist ((ringTypList y y').map (fun d => d.map (· - S.card)))).length_le
    omega
  have hfilt := Lib1.filter_runs (ext1 hΔ) B fAllLe (toVal k) (fun d => d.all (· ≤ k))
    (fun _ => 152 * k + 58) (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup) (fun d hd' => by
      have hd2 := List.mem_dedup.1 hd'
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd2
      have := hd d0 hd0
      refine (allLe_runs hΔ B k _ (by rw [List.length_map]; omega)).mono ?_
      rw [List.length_map]; omega)
  rw [sum_map_const_mul] at hfilt
  have hlA : fAllLe < B := by show 173 < B; omega
  have hlS : fSubMap < B := by show 171 < B; omega
  unfold joinYsL
  refine Runs.mk (hΔ _ _ (Δ_joinYs rid)) ?_
  rw [hl2] at hdd
  ev_start
  · ev_run
  · set n := (ringTypList y y').length with hn
    set m := (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup).length with hm
    have h1 : n * (k + 1) ≤ X * X := Nat.mul_le_mul hrl hkX
    have h2 : m * (k + 1) ≤ X * X := Nat.mul_le_mul (le_trans hddl hrl) hkX
    have h3 : (k + 1) * (n + 1) ^ 2 ≤ X * (2 * X) ^ 2 := by
      apply Nat.mul_le_mul hkX
      exact Nat.pow_le_pow_left (by omega) 2
    have h4 : m ≤ X := le_trans hddl hrl
    nlinarith

end helpers

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Join2` -/

section
/-!
# WP E2 (6): `joinC` and `joinKids` as F-functions

Cost of `joinC kmax a b` for `Good B0 a`, `Good B0 b`, entries `≤ kmax`, `sz ≤ s`:

    Hb X R0 s a = 8000 (s+1) (X^3)^(count a) + count a · R0,     X = cbound |B0| kmax 1 = 2^(4(|B0|+kmax+2)),

where `R0` bounds the cost of one call of `ringTypList` on entries `≤ kmax` and length `≤ 2 kmax + 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-- the cost bound of `joinC` -/
def Hb (X R0 s : ℕ) (c : CT) : ℕ := 8000 * (s + 1) * (X ^ 3) ^ count c + count c * R0

/-- `R0` bounds the cost of `ringTypList` on the run sequences of characteristics with entries `≤ kmax`. -/
def RingOK (Δ' : ℕ → Option Tm) (B rid R0 kmax : ℕ) : Prop :=
  ∀ y y' : List ℕ, (∀ x ∈ y, x ≤ kmax) → (∀ x ∈ y', x ≤ kmax) → y.length ≤ 2 * kmax + 1 → y'.length ≤ 2 * kmax + 1 →
    Runs Δ' B rid [toVal y, toVal y'] (toVal (ringTypList y y')) R0

theorem Hb_mono {X R0 s : ℕ} (hX : 1 ≤ X) {c c' : CT} (h : count c ≤ count c') : Hb X R0 s c ≤ Hb X R0 s c' := by
  unfold Hb
  have h1 : (X ^ 3) ^ count c ≤ (X ^ 3) ^ count c' := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) h
  have := Nat.mul_le_mul_left (8000 * (s + 1)) h1
  have := Nat.mul_le_mul_right R0 h
  nlinarith

theorem jk_step_arith (Jl r j ρ Q Hk Sr m : ℕ) (hJ : Jl ≤ j) (hr : r ≤ ρ) (hQ : Q = j * ρ) (hj : j ≤ Q)
    (hρQ : ρ ≤ Q) (hQ256 : 256 ≤ Q) :
    1 + 1 + (1 + 1 + (1 + (1 + 1 + (1 + 1 + 0)) + (Sr + m * (100 * ρ + 40) + 10) + 1 +
      (1 + (1 + (1 + (1 + 1 + (1 + 1 + 0)) + Hk + 1 + 0)) + (Jl * (30 * r + 30 + 10 * r + 20) + 8) + 1) + 1) + 1) + 1 ≤
    Hk + Sr + (m + 1) * (100 * Q + 40) + 10 := by
  have h1 : Jl * (30 * r + 30 + 10 * r + 20) ≤ j * (40 * ρ + 50) := Nat.mul_le_mul hJ (by omega)
  have h2 : j * (40 * ρ + 50) ≤ 90 * Q := by nlinarith
  have h3 : m * (100 * ρ + 40) ≤ m * (100 * Q + 40) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

theorem jc_arith (t Z X W A cL R0 Sc m1 m2 Yl J Sg mn : ℕ) (hXZ : X ≤ Z) (hZ8 : 8 ≤ Z) (hWA : W ≤ A)
    (hA1 : 1 ≤ A) (ht : 1 ≤ t) (hm1 : m1 ≤ t) (hm2 : m2 ≤ t) (hSc : Sc ≤ t) (hmn : mn ≤ t) (hYl : Yl ≤ X)
    (hJ : J ≤ W) (hSg : Sg ≤ 8000 * t * A + cL * R0) :
    1 + 1 + (1 + 1 + 0) + 30 * mn + 1 +
      (1 + 1 + 1 + 0 + (8 * m1 + 5) + 1 + (1 + 1 + 1 + 0 + (8 * m2 + 5) + 1) + 1 +
        (1 + 1 + (1 + (1 + 1 + 1 + (1 + 1 + 1 + 0))) + (R0 + 8 * Sc + 4000 * Z) + 1 +
          (1 + (1 + 1 + 1 + (1 + 1 + 1 + 0)) + (Sg + m1 * (100 * W + 40) + 10) + 1 +
            (1 + (1 + 1 + 1 + 1 + (1 + 0)) + (J * (30 * Yl + 30 + 10 * Yl + 20) + 8) + 1) + 1) + 1) + 1) + 1 ≤
    8000 * t * (A * Z) + (1 + cL) * R0 := by
  have h1 : m1 * (100 * W + 40) ≤ t * (100 * A + 40) := Nat.mul_le_mul hm1 (by omega)
  have h2 : J * (30 * Yl + 30 + 10 * Yl + 20) ≤ A * (40 * Z + 50) :=
    Nat.mul_le_mul (le_trans hJ hWA) (by omega)
  have hP1 : 8 * (t * A) ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP2 : A * Z ≤ t * A * Z := by
    have : A * Z * 1 ≤ A * Z * t := Nat.mul_le_mul_left _ ht
    nlinarith
  have hP3 : t ≤ t * A * Z := by nlinarith [Nat.zero_le t]
  have hP4 : A ≤ t * A * Z := by nlinarith [Nat.zero_le A]
  have hP5 : Z ≤ t * A * Z := by nlinarith [Nat.zero_le Z]
  have hP6 : t * A ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP7 : 1 ≤ t * A * Z := by nlinarith
  nlinarith

theorem sum_Hb_le {X R0 s : ℕ} (hX : 2 ≤ X ^ 3) (ks : List CT) :
    (ks.map (Hb X R0 s)).sum ≤ 8000 * (s + 1) * (X ^ 3) ^ countL ks + countL ks * R0 := by
  have e : (ks.map (Hb X R0 s)).sum =
      8000 * (s + 1) * (ks.map (fun k => (X ^ 3) ^ count k)).sum + (ks.map (fun k => count k * R0)).sum := by
    induction ks with
    | nil => simp
    | cons k ks ih => simp only [List.map_cons, List.sum_cons, Hb] at ih ⊢; rw [ih]; ring
  have h1 := sum_count_pow_le hX ks
  have h2 := sum_count_mul ks R0
  rw [e, h2]
  nlinarith

theorem hb_ge {X R0 s : ℕ} (c : CT) (hX : 1 ≤ X) : R0 + 8 * s + 4000 * X ^ 3 ≤ Hb X R0 s c := by
  unfold Hb
  have hc := count_ge_one c
  have h3 : X ^ 3 ≤ (X ^ 3) ^ count c := by
    calc X ^ 3 = (X ^ 3) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) hc
  have h4 := Nat.mul_le_mul_left (8000 * (s + 1)) h3
  have h5 : R0 ≤ count c * R0 := Nat.le_mul_of_pos_left _ (by omega)
  have h6 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h7 := Nat.mul_le_mul_left s h6
  nlinarith

theorem jkb_arith (t Z W A cL R0 m Sg : ℕ) (hZ8 : 8 ≤ Z) (hWA : W ≤ A) (hA1 : 1 ≤ A) (ht : 1 ≤ t) (hm : m ≤ t)
    (hSg : Sg ≤ 8000 * t * A + cL * R0) : Sg + m * (100 * W + 40) + 10 ≤ 8000 * t * (A * Z) + (1 + cL) * R0 := by
  have h1 : m * (100 * W + 40) ≤ t * (100 * A + 40) := Nat.mul_le_mul hm (by omega)
  have hP1 : 8 * (t * A) ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP3 : t ≤ t * A * Z := by nlinarith [Nat.zero_le t]
  have hP7 : 1 ≤ t * A * Z := by nlinarith
  nlinarith

section joinC
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem mapKK_runs (S : Finset ℕ) (ys : List (List ℕ)) (kk : List CT) (hB : 1000 + 30 * ys.length < B) :
    Runs Δ' B fMapKK [Val.cons (toVal S) (toVal ys), toVal kk] (toVal (ys.map (fun d => node S d kk)))
      (30 * ys.length + 30) := by
  have h := Lib1.map_runs (ext1 hΔ) B fMkNode (Val.cons (toVal S) (toVal kk)) (fun d => node S d kk)
    (fun _ => 8) ys (fun d _ => by
      refine Runs.mk (hΔ _ _ (Δ_mkNode rid)) ?_
      simp only [toVal_ct]
      ev_start
      · ev_run
      · omega)
  rw [sum_map_const_mul] at h
  have hl : fMkNode < B := by show 175 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_mapKK rid)) ?_
  ev_start
  · ev_run
  · omega

theorem consAll_runs (rest : List (List CT)) (c : CT) (hB : 1000 + 30 * rest.length < B) :
    Runs Δ' B fConsAll [toVal rest, toVal c] (toVal (rest.map (c :: ·))) (30 * rest.length + 30) := by
  have h := Lib1.map_runs (ext1 hΔ) B fConsTo (toVal c) (fun l => c :: l) (fun _ => 6) rest (fun l _ => by
      refine Runs.mk (hΔ _ _ (Δ_consTo rid)) ?_
      ev_start
      · ev_run
      · omega)
  rw [sum_map_const_mul] at h
  have hl : fConsTo < B := by show 179 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_consAll rid)) ?_
  ev_start
  · ev_run
  · omega

set_option maxHeartbeats 1000000 in
theorem joinKids_runs_aux (B0 : Finset ℕ) (kmax R0 s X : ℕ) (hXdef : X = xb B0.card kmax) (ks : List CT) :
    ∀ ks' : List CT, (∀ k ∈ ks, Good B0 k) → (∀ k' ∈ ks', Good B0 k') →
    (∀ k ∈ ks, ∀ k' ∈ ks', Runs Δ' B fJoinC [toVal kmax, toVal k, toVal k'] (toVal (joinC kmax k k'))
      (Hb X R0 s k)) →
    (ks.map (Hb X R0 s)).sum + ks.length * (100 * X ^ countL ks + 40) + 10 + 1000 < B →
    Runs Δ' B fJoinKids [toVal kmax, toVal ks, toVal ks'] (toVal (joinKids kmax ks ks'))
      ((ks.map (Hb X R0 s)).sum + ks.length * (100 * X ^ countL ks + 40) + 10) := by
  have hX256 : 256 ≤ X := hXdef ▸ xb_ge _ _
  induction ks with
  | nil =>
    intro ks' _ _ _ hB
    refine Runs.mk (hΔ _ _ (Δ_joinKids rid)) ?_
    cases ks' with
    | nil =>
      have : joinKids kmax [] [] = [[]] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil, List.map_nil, List.sum_nil, List.length_nil, countL]
      ev_start
      · ev_run
      · omega
    | cons k' ks' =>
      have : joinKids kmax [] (k' :: ks') = [] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil, List.map_nil, List.sum_nil, List.length_nil, countL]
      ev_start
      · ev_run
      · omega
  | cons k ks ih =>
    intro ks' hgk hgk' hf hB
    refine Runs.mk (hΔ _ _ (Δ_joinKids rid)) ?_
    cases ks' with
    | nil =>
      have : joinKids kmax (k :: ks) [] = [] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil]
      ev_start
      · ev_run
      · omega
    | cons k' ks' =>
      have hgk1 : Good B0 k := hgk k (by simp)
      have hgk1' : Good B0 k' := hgk' k' (by simp)
      have hgL : GoodL B0 ks := GoodL_iff.2 (fun x hx => hgk x (List.mem_cons_of_mem _ hx))
      have hgL' : GoodL B0 ks' := GoodL_iff.2 (fun x hx => hgk' x (List.mem_cons_of_mem _ hx))
      have hlj : (joinC kmax k k').length ≤ X ^ count k := by
        have := joinC_length_le_good (kmax := kmax) hgk1 hgk1'
        rw [hXdef, ← cbound_eq_pow]; exact this
      have hlr : (joinKids kmax ks ks').length ≤ X ^ countL ks := by
        have := joinKids_length_le_good (kmax := kmax) ks ks' hgL hgL'
        rw [hXdef, ← cbound_eq_pow]; exact this
      have hcL : countL (k :: ks) = count k + countL ks := rfl
      have hQ : X ^ countL (k :: ks) = X ^ count k * X ^ countL ks := by rw [hcL, pow_add]
      have hr1 : 1 ≤ X ^ countL ks := Nat.one_le_pow _ _ (by omega)
      have hcnt := count_ge_one k
      have hj1 : X ≤ X ^ count k := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ count k := Nat.pow_le_pow_right (by omega) hcnt
      have hrQ : X ^ countL ks ≤ X ^ countL (k :: ks) := by
        rw [hQ]; exact Nat.le_mul_of_pos_left _ (by omega)
      have hjQ : X ^ count k ≤ X ^ countL (k :: ks) := by
        rw [hQ]; exact Nat.le_mul_of_pos_right _ (by omega)
      have hQ256 : 256 ≤ X ^ countL (k :: ks) := le_trans hX256 (le_trans hj1 hjQ)
      simp only [List.map_cons, List.sum_cons, List.length_cons] at hB
      have hBm : 100 * X ^ countL (k :: ks) + 40 ≤ (ks.length + 1) * (100 * X ^ countL (k :: ks) + 40) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hrest := ih ks' (fun x hx => hgk x (List.mem_cons_of_mem _ hx))
        (fun x hx => hgk' x (List.mem_cons_of_mem _ hx))
        (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        (by nlinarith [Nat.zero_le (ks.length * (100 * X ^ countL ks + 40)), Nat.zero_le (ks.length * X ^ countL ks)])
      have hJ := hf k (by simp) k' (by simp)
      have hcons : ∀ c ∈ joinC kmax k k', Runs Δ' B fConsAll [toVal (joinKids kmax ks ks'), toVal c]
          (toVal ((joinKids kmax ks ks').map (c :: ·))) (30 * (joinKids kmax ks ks').length + 30) := by
        intro c _
        exact consAll_runs hΔ B _ c (by omega)
      have hfm := flatMap_runs_le hΔ B fConsAll (toVal (joinKids kmax ks ks'))
        (fun c => (joinKids kmax ks ks').map (c :: ·)) (fun _ => 30 * (joinKids kmax ks ks').length + 30)
        (joinC kmax k k') (joinKids kmax ks ks').length (30 * (joinKids kmax ks ks').length + 30)
        (fun c _ => by simp) (fun _ _ => le_refl _) hcons
      have hlit : fConsAll < B := by show 180 < B; omega
      have hJK : joinKids kmax (k :: ks) (k' :: ks') =
          (joinC kmax k k').flatMap (fun c => (joinKids kmax ks ks').map (c :: ·)) := rfl
      rw [hJK]
      simp only [toVal_cons]
      ev_start
      · ev_run
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        exact jk_step_arith (Jl := (joinC kmax k k').length) (r := (joinKids kmax ks ks').length)
          (j := X ^ count k) (ρ := X ^ countL ks) (Q := X ^ countL (k :: ks)) (Hk := Hb X R0 s k)
          (Sr := (ks.map (Hb X R0 s)).sum) (m := ks.length) hlj hlr hQ hjQ hrQ hQ256

set_option maxHeartbeats 2000000 in
theorem joinC_runs_aux (B0 : Finset ℕ) (kmax R0 s X : ℕ) (hXdef : X = xb B0.card kmax)
    (hring : RingOK Δ' B rid R0 kmax) (a : CT) :
    ∀ b : CT, Good B0 a → Good B0 b → maxEntry a ≤ kmax → maxEntry b ≤ kmax → sz a ≤ s → sz b ≤ s →
    Hb X R0 s a + 1000 * (s + 1) + 1000 < B →
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b)) (Hb X R0 s a) := by
  have hX256 : 256 ≤ X := hXdef ▸ xb_ge _ _
  induction a using CT.ind with
  | h S y ks ih =>
    intro b hga hgb hma hmb hsa hsb hB
    obtain ⟨S', y', ks'⟩ := b
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hZ : 1 ≤ (X ^ 3) ^ count (node S y ks) := Nat.one_le_pow _ _ (by positivity)
    have hHb1 : 8000 * (s + 1) ≤ Hb X R0 s (node S y ks) := by
      unfold Hb; nlinarith [Nat.zero_le (count (node S y ks) * R0)]
    have hB1 : 1 < B := by omega
    have hsS := sz_S_le S y ks
    have hsks := sz_ks_le S y ks
    have hcardS := sz_finset_card S
    have hm : ks.length ≤ s := by
      have := length_le_sz ks; omega
    have hjc : joinC kmax (node S y ks) (node S' y' ks') =
        if S = S' ∧ ks.length = ks'.length then
          (joinKids kmax ks ks').flatMap (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk))
        else [] := rfl
    by_cases hS : S = S'
    · by_cases hlen : ks.length = ks'.length
      · subst hS
        have hs' : sz ks' < sz (node S y' ks') := sz_ks_le S y' ks'
        have hm' : ks'.length ≤ s := by have := length_le_sz ks'; omega
        obtain ⟨hgk, hmk⟩ := kids_good hga hma
        obtain ⟨hgk', hmk'⟩ := kids_good hgb hmb
        have hy : ∀ x ∈ y, x ≤ kmax := ((maxEntry_le_iff).1 hma).1
        have hy' : ∀ x ∈ y', x ≤ kmax := ((maxEntry_le_iff).1 hmb).1
        have hly := y_length_le hga hma
        have hly' := y_length_le hgb hmb
        have hgL : GoodL B0 ks := GoodL_iff.2 hgk
        have hgL' : GoodL B0 ks' := GoodL_iff.2 hgk'
        have hv : joinC kmax (node S y ks) (node S y' ks') =
            (joinKids kmax ks ks').flatMap (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk)) := by
          rw [hjc, if_pos ⟨rfl, hlen⟩]
        have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S true (by simp)
        have hl1 := Lib1.length_runs (ext1 hΔ) B ks (by omega)
        have hl2 := Lib1.length_runs (ext1 hΔ) B ks' (by omega)
        have hXk : 4 ^ (2 * kmax + 1) ≤ X := hXdef ▸ xb_ring _ _
        have hXk' : kmax + 1 ≤ X := hXdef ▸ xb_k _ _
        have hX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
        have hX38 : 8 ≤ X ^ 3 := by omega
        have hHb2 := hb_ge (X := X) (R0 := R0) (s := s) (node S y ks) (by omega)
        have hys := joinYs_runs hΔ B S kmax y y' R0 X hy hy' hXk hXk' (by omega) (hring y y' hy hy' hly hly')
          (by omega)
        have hysl : (joinYsL S.card kmax y y').length ≤ X := by
          have := joinYs_length_le (a := y) (b := y') (c := S.card) (kmax := kmax) (L₁ := kmax) (L₂ := kmax) hy hy'
          have h2 : 4 ^ (kmax + kmax + 1) = 4 ^ (2 * kmax + 1) := by congr 1; omega
          unfold joinYsL; omega
        have hjkl : (joinKids kmax ks ks').length ≤ X ^ countL ks := by
          have := joinKids_length_le_good (kmax := kmax) ks ks' hgL hgL'
          rw [hXdef, ← cbound_eq_pow]; exact this
        have hjk := joinKids_runs_aux hΔ B B0 kmax R0 s X hXdef ks ks' hgk hgk'
          (fun k hk k' hk' => ih k hk k' (hgk k hk) (hgk' k' hk') (hmk k hk) (hmk' k' hk')
            (by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
            (by have := sz_le_of_mem_kids (S := S) (y := y') hk'; omega)
            (by
              have h6 : count k ≤ count (node S y ks) := by
                have := count_le_countL_of_mem hk; rw [hcnode]; omega
              have := Hb_mono (X := X) (R0 := R0) (s := s) (by omega) h6
              exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right this _) _) hB))
          (by
            have hsum := sum_Hb_le (X := X) (R0 := R0) (s := s) (by omega) ks
            have hkb := jkb_arith (s + 1) (X ^ 3) (X ^ countL ks) ((X ^ 3) ^ countL ks) (countL ks) R0 ks.length
              ((ks.map (Hb X R0 s)).sum) hX38 (Nat.pow_le_pow_left hX3 _)
              (Nat.one_le_pow _ _ (by omega)) (by omega) (by omega) hsum
            have hHbeq : Hb X R0 s (node S y ks) =
                8000 * (s + 1) * ((X ^ 3) ^ countL ks * X ^ 3) + (1 + countL ks) * R0 := by
              unfold Hb; rw [hcnode, pow_add]; ring
            rw [hHbeq] at hB
            linarith)
        have hmk1 := fun kk (_ : kk ∈ joinKids kmax ks ks') =>
          mapKK_runs hΔ B S (joinYsL S.card kmax y y') kk (by linarith)
        have hfm := flatMap_runs_le hΔ B fMapKK (Val.cons (toVal S) (toVal (joinYsL S.card kmax y y')))
          (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk))
          (fun _ => 30 * (joinYsL S.card kmax y y').length + 30) (joinKids kmax ks ks')
          (joinYsL S.card kmax y y').length (30 * (joinYsL S.card kmax y y').length + 30)
          (fun kk _ => by simp) (fun _ _ => le_refl _) hmk1
        have hlit : fMapKK < B := by show 176 < B; omega
        refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
        rw [hv]
        simp only [toVal_ct]
        ev_start
        · ev_run
        · have hHbeq : Hb X R0 s (node S y ks) =
              8000 * (s + 1) * ((X ^ 3) ^ countL ks * X ^ 3) + (1 + countL ks) * R0 := by
            unfold Hb; rw [hcnode, pow_add]; ring
          rw [hHbeq]
          exact jc_arith (s + 1) (X ^ 3) X (X ^ countL ks) ((X ^ 3) ^ countL ks) (countL ks) R0 S.card ks.length
            ks'.length (joinYsL S.card kmax y y').length (joinKids kmax ks ks').length
            ((ks.map (Hb X R0 s)).sum) (min (sz S) (sz S)) hX3 hX38 (Nat.pow_le_pow_left hX3 _)
            (Nat.one_le_pow _ _ (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) hysl hjkl
            (sum_Hb_le (X := X) (R0 := R0) (s := s) (by omega) ks)
      · have hv : joinC kmax (node S y ks) (node S' y' ks') = [] := by
          rw [hjc, if_neg (by simp [hlen])]
        have hm' : ks'.length ≤ s := by
          have := sz_ks_le S' y' ks'; have := length_le_sz ks'; omega
        have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S' true (by simp [hS])
        have hl1 := Lib1.length_runs (ext1 hΔ) B ks (by omega)
        have hl2 := Lib1.length_runs (ext1 hΔ) B ks' (by omega)
        refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
        rw [hv]
        simp only [toVal_ct, toVal_nil]
        ev_start
        · ev_run
        · have := min_le_left (sz S) (sz S')
          omega
    · have hv : joinC kmax (node S y ks) (node S' y' ks') = [] := by
        rw [hjc, if_neg (by simp [hS])]
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S' false (by simp [hS])
      refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
      rw [hv]
      simp only [toVal_ct, toVal_nil]
      ev_start
      · ev_run
      · have := min_le_left (sz S) (sz S')
        omega

omit hΔ in
theorem Hb_le_wf {B0 : Finset ℕ} {kmax : ℕ} {a : CT} (ha : a.Wf B0 kmax) (R0 s : ℕ) :
    Hb (xb B0.card kmax) R0 s a ≤ 8000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0 := by
  have hc : count a ≤ (2 * B0.card + 2) ^ 2 := by
    have := ha.count_le; unfold runBound at this; nlinarith
  have hX : xb B0.card kmax = 2 ^ (4 * (B0.card + kmax + 2)) := by
    unfold xb cbound; congr 1; ring
  have hN : B0.card + 1 ≤ B0.card + kmax + 2 := by omega
  have h2 : (2 * B0.card + 2) ^ 2 ≤ 4 * (B0.card + kmax + 2) ^ 2 := by
    have := Nat.pow_le_pow_left hN 2
    calc (2 * B0.card + 2) ^ 2 = 4 * (B0.card + 1) ^ 2 := by ring
      _ ≤ 4 * (B0.card + kmax + 2) ^ 2 := Nat.mul_le_mul_left _ this
  have h1 : ((xb B0.card kmax) ^ 3) ^ count a ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := by
    rw [hX, ← pow_mul, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    calc 4 * (B0.card + kmax + 2) * (3 * count a) = (12 * (B0.card + kmax + 2)) * count a := by ring
      _ ≤ (12 * (B0.card + kmax + 2)) * (4 * (B0.card + kmax + 2) ^ 2) :=
          Nat.mul_le_mul_left _ (le_trans hc h2)
      _ = 48 * (B0.card + kmax + 2) ^ 3 := by ring
  unfold Hb
  have h3 := Nat.mul_le_mul_left (8000 * (s + 1)) h1
  have h4 := Nat.mul_le_mul_right R0 hc
  omega

/-- **`joinC` as an F-function**, for well-formed characteristics on the boundary `B0` (entries `≤ kmax`).
`R0` bounds one call of `ringTypList`; `s` bounds the sizes of the inputs.  The cost is
`8000 (s+1) 2^(48 (|B0|+kmax+2)^3) + (2|B0|+2)^2 · R0`. -/
theorem joinC_runs {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (R0 s : ℕ)
    (hring : RingOK Δ' B rid R0 kmax) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : 16000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0 + 2000 * (s + 1) + 2000 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (8000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0) := by
  have hle := Hb_le_wf ha R0 s
  have h := joinC_runs_aux hΔ B B0 kmax R0 s (xb B0.card kmax) rfl hring a b ha.good hb.good ha.bounded hb.bounded
    hsa hsb (by
      have hpos := Nat.zero_le ((s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3))
      nlinarith)
  exact h.mono hle

end joinC

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2Dom` -/

section
/-!
# WP E2 (7): `domCB` as an F-function (used by `realIntro` / `realJoin`)

`domCB a b` (`DomC`-decision).  Cost `C · wt a` with `C = 60·3^(2L) + 60 s + 300` when every run sequence of `a`, `b` has length `≤ L`
(`CT.RB s L`) and `sz ≤ s`; the exponential factor is `E1A.domB`'s (`60·3^(|y|+|y'|)`, as the Lean recursion).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

section dom
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ hE

theorem domCL_runs_aux (Cc : ℕ) (hB1 : 1 < B) (ks : List CT) : ∀ ks' : List CT,
    (∀ k ∈ ks, ∀ k' ∈ ks', Runs Δ' B fDomC [toVal k, toVal k'] (toVal (domCB k k')) (Cc * wt k)) →
    Runs Δ' B fDomCL [toVal ks, toVal ks'] (toVal (domCBL ks ks'))
      ((ks.map (fun k => Cc * wt k)).sum + 20 * (ks.length + 1) + 10) := by
  induction ks with
  | nil =>
    intro ks' _
    refine Runs.mk (hΔ _ _ (Δ_domCL rid)) ?_
    cases ks' with
    | nil =>
      have : domCBL [] [] = true := rfl
      rw [this]
      simp only [toVal_nil, toVal_true]
      ev_start
      · ev_run
      · simp
    | cons k' ks' =>
      have : domCBL [] (k' :: ks') = false := rfl
      rw [this]
      simp only [toVal_nil, toVal_cons, toVal_false]
      ev_start
      · ev_run
      · simp
  | cons k ks ih =>
    intro ks' hf
    refine Runs.mk (hΔ _ _ (Δ_domCL rid)) ?_
    cases ks' with
    | nil =>
      have : domCBL (k :: ks) [] = false := rfl
      rw [this]
      simp only [toVal_nil, toVal_cons, toVal_false]
      ev_start
      · ev_run
      · simp
    | cons k' ks' =>
      have h1 := hf k (by simp) k' (by simp)
      have h2 := ih ks' (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      by_cases hd : domCB k k' = true
      · have : domCBL (k :: ks) (k' :: ks') = domCBL ks ks' := by simp [domCBL, hd]
        rw [this]
        simp only [hd] at h1
        simp only [toVal_cons]
        ev_start
        · ev_run
        · simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith
      · have hd' : domCB k k' = false := by simpa using hd
        have : domCBL (k :: ks) (k' :: ks') = false := by simp [domCBL, hd']
        rw [this]
        simp only [hd'] at h1
        simp only [toVal_cons]
        ev_start
        · ev_run
        · simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith [Nat.zero_le (List.map (fun k => Cc * wt k) ks).sum]

theorem domC_runs_aux (Cc D0 L s : ℕ) (hC : 30 * s + D0 + 100 ≤ Cc) (hB1 : 1000 < B)
    (hdom : ∀ y y' : List ℕ, y.length ≤ L → y'.length ≤ L →
      Runs Δ' B E1A.fDomB [toVal y, toVal y'] (toVal (domB y y')) D0) (a : CT) :
    ∀ b : CT, RB s L a → RB s L b → sz a ≤ s → sz b ≤ s →
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) (Cc * wt a) := by
  induction a using CT.ind with
  | h S y ks ih =>
    intro b hra hrb hsa hsb
    obtain ⟨S', y', ks'⟩ := b
    have hts := tree_step ks (fun _ => 0) Cc 0 0 (fun _ _ => le_refl _)
    simp only [pow_zero, mul_one] at hts
    have hwt := wt_node S y ks
    have hsS := sz_S_le S y ks
    have hm : ks.length ≤ s := by have := sz_ks_le S y ks; have := length_le_sz ks; omega
    have hlt : fDomCL < B := by show 182 < B; omega
    have hlt2 : E1A.fDomB < B := by show 135 < B; omega
    refine Runs.mk (hΔ _ _ (Δ_domC rid)) ?_
    by_cases hS : S = S'
    · subst hS
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B (by omega) S S true (by simp)
      have hmin := min_le_left (sz S) (sz S)
      have hd := hdom y y' hra.2.1 hrb.2.1
      cases hb : domB y y' with
      | false =>
        have : domCB (node S y ks) (node S y' ks') = false := by simp [domCB, hb]
        rw [this]
        rw [hb] at hd
        simp only [toVal_ct, toVal_false]
        ev_start
        · ev_run
        · rw [hwt]; nlinarith
      | true =>
        rw [hb] at hd
        have hL := domCL_runs_aux hΔ hE B Cc (by omega) ks ks' (fun k hk k' hk' =>
          ih k hk k' (RB.kids hra k hk) (RB.kids hrb k' hk')
            (by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
            (by have := sz_le_of_mem_kids (S := S) (y := y') hk'; omega))
        have : domCB (node S y ks) (node S y' ks') = domCBL ks ks' := by simp [domCB, hb]
        rw [this]
        simp only [toVal_ct, toVal_true] at *
        ev_start
        · ev_run
        · rw [hwt]; nlinarith
    · have : domCB (node S y ks) (node S' y' ks') = false := by simp [domCB, hS]
      rw [this]
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B (by omega) S S' false (by simp [hS])
      have hmin := min_le_left (sz S) (sz S')
      simp only [toVal_ct, toVal_false]
      ev_start
      · ev_run
      · rw [hwt]; nlinarith

/-- **`domCB` as an F-function**: cost `(30 s + 60·3^(2L) + 100) · 2 count a`, where `L` bounds the run sequences of both
characteristics (`CT.RB s L`, e.g. `RB.of_good` with `L = 2 kmax + 1`) and `sz ≤ s`. -/
theorem domC_runs (L s : ℕ) (a b : CT) (hla : RB s L a) (hlb : RB s L b) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) + 1000 < B) :
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) ((30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a)) := by
  have hcnt := count_ge_one a
  have hP : 1 ≤ 3 ^ (2 * L) := Nat.one_le_pow _ _ (by omega)
  have hB1 : 1000 < B := by
    have : 100 ≤ (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) := by nlinarith
    omega
  have h := domC_runs_aux hΔ hE B (30 * s + 60 * 3 ^ (2 * L) + 100) (60 * 3 ^ (2 * L)) L s le_rfl hB1
    (fun y y' hy hy' => (E1A.domB_runs hE B (by omega) (y.length + y'.length) y y' rfl).mono
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))) a b hla hlb hsa hsb
  refine h.mono ?_
  have : wt a ≤ 2 * count a := by unfold wt; omega
  exact Nat.mul_le_mul_left _ this

end dom

end E2
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E2` -/

section
/-!
# WP E2: the assembled interface — table `e2Tbl` (ids 160…182), concrete cost bounds with the E1 functions

`e2Tbl rid` (E2Defs) has the E2 functions; `rid` is the id of `ringTypList` in the assembled table.  With WP E1's table
(`E1.e1Tbl`, ids `128 … 157`, `ringTypList` at `E1C.fRingTypList = 152`) the combined table is `e12Tbl`.

**How the assembler uses this.**  Every theorem below is stated for an arbitrary table `Δ'` with `hΔ : e2Δ 152 ⊑ Δ'` and
`hE1 : E1.e1Δ ⊑ Δ'` (for the assembly `layerΔ Lib.Δ 128 (orElseΔ e1Tbl (orElseΔ (e2Tbl 152) e3Tbl))`, obtain both by
`Ext.layer_mono (Ext.orElse_left …)` / `Ext.layer_mono (Ext.orElse_right (disj) …)`; `e2Tbl_disj_e1` is the disjointness fact).
The ids are `E2.fNorm = 166`, `E2.fForgetC = 169`, `E2.fJoinC = 177`, `E2.fJoinKids = 178`, `E2.fDomC = 181`, `E2.fKeyLe`, `E2.fSortKids`, `E2.fVerts`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `CT.norm` | `fNorm` | `[c]` | `norm_runs_e12` | `6200 (s+1)^5`, `sz c ≤ s` |
| `CT.forgetC` | `fForgetC` | `[x, c]` | `forgetC_runs_e12` | `7000 (s+1)^5` |
| `CT.joinC` | `fJoinC` | `[kmax, a, b]` | `joinC_runs_e12` | `14000 (s+1) 2^(48 (|B|+kmax+2)^3)` for `Wf B kmax a, b`, `sz ≤ s` |
| `CT.domCB` | `fDomC` | `[a, b]` | `domC_runs_e12` | `(30 s + 60·3^(2L) + 100)·2 count a`, run sequences `≤ L` |
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-- the E2 table is disjoint from the E1 table -/
theorem e2Tbl_disj_e1 (rid : ℕ) : ∀ f b, e2Tbl rid f = some b → E1.e1Tbl f = none := by
  intro f b h
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have h1 := E1.e1Tbl_lt hc
  have h2 := (e2Tbl_lt rid h).1
  omega

/-- the combined E1 + E2 table -/
def e12Tbl : ℕ → Option Tm := orElseΔ E1.e1Tbl (e2Tbl E1C.fRingTypList)
def e12Δ : ℕ → Option Tm := Lib.extend e12Tbl

/-! ## the interface with `ringTypList` -/

/-- the cost of one call of `ringTypList` on run sequences with entries `≤ k` and length `≤ 2k + 1` -/
def R0k (k : ℕ) : ℕ := 6000 * (2 * k + 2) ^ 2 * (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2

theorem R0k_ge (k : ℕ) : 6000 * (2 * k + 2) ≤ R0k k := by
  unfold R0k
  have h1 : 0 < (4 ^ (2 * k + 1) + 1) ^ 2 := by positivity
  have h2 : 0 < (4 * k + 3) ^ 2 := by positivity
  have h3 : 1 ≤ (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2 := Nat.mul_pos h1 h2
  have h4 : 2 * k + 2 ≤ (2 * k + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  generalize (4 ^ (2 * k + 1) + 1) ^ 2 = P at *
  generalize (4 * k + 3) ^ 2 = Q at *
  generalize (2 * k + 2) ^ 2 = R at *
  calc 6000 * (2 * k + 2) ≤ 6000 * R := Nat.mul_le_mul_left _ h4
    _ = 6000 * R * 1 := by ring
    _ ≤ 6000 * R * (P * Q) := Nat.mul_le_mul_left _ h3
    _ = 6000 * R * P * Q := by ring

theorem ringOK_e1 {Δ' : ℕ → Option Tm} (hE : E1C.Δ ⊑ Δ') (B kmax : ℕ) (hB : R0k kmax + 1000 < B) :
    RingOK Δ' B E1C.fRingTypList (R0k kmax) kmax := by
  intro y y' hy hy' hly hly'
  have h0 := R0k_ge kmax
  have h := E1C.ringTypList_runs hE B (by linarith) y y' kmax kmax hy hy' (by linarith)
  refine h.mono ?_
  unfold R0k
  have e1 : kmax + kmax + 1 = 2 * kmax + 1 := by omega
  have e2 : 2 * (kmax + kmax) + 1 + 2 = 4 * kmax + 3 := by omega
  rw [e1, e2]
  have h1 : y.length + 1 ≤ 2 * kmax + 2 := by omega
  have h2 : y'.length + 1 ≤ 2 * kmax + 2 := by omega
  have h3 : (y.length + 1) * (y'.length + 1) ≤ (2 * kmax + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul h1 h2
  have e : 6000 * (y.length + 1) * (y'.length + 1) = 6000 * ((y.length + 1) * (y'.length + 1)) := by ring
  rw [e]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3))

/-! ## the pure-arithmetic bound on the `ringTypList` contribution -/

theorem sq_le_pow2 (m : ℕ) : (m + 1) ^ 2 ≤ 2 ^ (2 * m) := by
  have h : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc (m + 1) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]

theorem f_lin (m : ℕ) : (2 * m + 2) ^ 2 ≤ 2 ^ (2 * m + 2) := by
  calc (2 * m + 2) ^ 2 = 4 * (m + 1) ^ 2 := by ring
    _ ≤ 4 * 2 ^ (2 * m) := Nat.mul_le_mul_left _ (sq_le_pow2 m)
    _ = 2 ^ (2 * m + 2) := by rw [pow_add]; ring

theorem f_four (k : ℕ) : (4 ^ (2 * k + 1) + 1) ^ 2 ≤ 2 ^ (8 * k + 6) := by
  have e : 4 ^ (2 * k + 1) = 2 ^ (4 * k + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; ring
  have h1 : 4 ^ (2 * k + 1) + 1 ≤ 2 ^ (4 * k + 3) := by
    have hA : 1 ≤ 4 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
    calc 4 ^ (2 * k + 1) + 1 ≤ 2 * 4 ^ (2 * k + 1) := by linarith
      _ = 2 ^ (4 * k + 3) := by rw [e, ← pow_succ']
  calc (4 ^ (2 * k + 1) + 1) ^ 2 ≤ (2 ^ (4 * k + 3)) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (8 * k + 6) := by rw [← pow_mul]; congr 1; ring

theorem f_lin2 (k : ℕ) : (4 * k + 3) ^ 2 ≤ 2 ^ (2 * k + 4) := by
  have h1 : 4 * k + 3 ≤ 4 * 2 ^ k := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  calc (4 * k + 3) ^ 2 ≤ (4 * 2 ^ k) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (2 * k + 4) := by
      rw [mul_pow, ← pow_mul, show (4 : ℕ) ^ 2 = 2 ^ 4 by norm_num, ← pow_add]; congr 1; ring

theorem arr4 (A X1 X2 X3 : ℕ) : A * (6000 * X1 * X2 * X3) = 6000 * (A * X1 * X2 * X3) := by ring

theorem join_R0_bound (nb k : ℕ) : (2 * nb + 2) ^ 2 * R0k k ≤ 6000 * 2 ^ (48 * (nb + k + 2) ^ 3) := by
  have f1 := f_lin nb
  have f2 := f_lin k
  have f3 := f_four k
  have f4 := f_lin2 k
  unfold R0k
  rw [arr4]
  have h5 : (2 * nb + 2) ^ 2 * (2 * k + 2) ^ 2 * (4 ^ (2 * k + 1) + 1) ^ 2 * (4 * k + 3) ^ 2 ≤
      2 ^ (2 * nb + 2) * 2 ^ (2 * k + 2) * 2 ^ (8 * k + 6) * 2 ^ (2 * k + 4) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul f1 f2) f3) f4
  have h6 : 2 ^ (2 * nb + 2) * 2 ^ (2 * k + 2) * 2 ^ (8 * k + 6) * 2 ^ (2 * k + 4) = 2 ^ (2 * nb + 12 * k + 14) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  have h7 : 2 * nb + 12 * k + 14 ≤ 48 * (nb + k + 2) ^ 3 := by
    have : nb + k + 2 ≤ (nb + k + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have h8 : 2 ^ (2 * nb + 12 * k + 14) ≤ 2 ^ (48 * (nb + k + 2) ^ 3) := Nat.pow_le_pow_right (by norm_num) h7
  have h9 := le_trans (le_trans h5 (le_of_eq h6)) h8
  exact Nat.mul_le_mul_left 6000 h9

theorem join_fit_arith (s E R : ℕ) (hE : 1 ≤ E) (hR : R ≤ 6000 * E) :
    28000 * (s + 1) * E + 2000 * (s + 1) + 2000 + R + 1000 ≤ (14000 * (s + 1) * E + 2) ^ 2 := by
  have h1 : 1 ≤ (s + 1) * E := Nat.mul_pos (by omega) hE
  nlinarith [Nat.zero_le ((s + 1) * E), Nat.zero_le (s + 1)]

/-! ## the concrete statements -/

section concrete
variable {Δ' : ℕ → Option Tm} (hΔ : e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') (B : ℕ)
include hΔ hE1

theorem norm_runs_e12 (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 < B) :
    Runs Δ' B fNorm [toVal c] (toVal (norm c)) (6200 * (s + 1) ^ 5) :=
  norm_runs hΔ (Ext.trans E1.extA hE1) B c s hc hB

theorem forgetC_runs_e12 (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hB : 14000 * (s + 1) ^ 5 + 100 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) :=
  forgetC_runs hΔ (Ext.trans E1.extA hE1) B x c s hc hB

/-- **`joinC`**: for `a, b` well-formed over the boundary `B0` with entries `≤ kmax` and sizes `≤ s`, cost
`14000 (s+1) 2^(48 (|B0| + kmax + 2)^3)` (the constant is symbolic; never evaluate it). -/
theorem joinC_runs_e12 {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (s : ℕ)
    (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : 28000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + 2000 * (s + 1) + 2000 + R0k kmax + 1000 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3)) := by
  have hR := join_R0_bound B0.card kmax
  have hpos := Nat.zero_le ((s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3))
  have hE : 1 ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  have hring := ringOK_e1 (Ext.trans E1.extC hE1) B kmax (by nlinarith)
  have h := joinC_runs hΔ B ha hb (R0k kmax) s hring hsa hsb (by nlinarith)
  refine h.mono ?_
  nlinarith

theorem domC_runs_e12 (L s : ℕ) (a b : CT) (hla : RB s L a) (hlb : RB s L b) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) + 1000 < B) :
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) ((30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a)) :=
  domC_runs hΔ (Ext.trans E1.extA hE1) B L s a b hla hlb hsa hsb hB

/-! ### the `Fits` forms: the hypothesis on `B` is `(cost + 2)^2 < B` (what `Fits B v cost` provides) -/

theorem forgetC_runs_fits (x : ℕ) (c : CT) (s : ℕ) (hc : sz c ≤ s) (hfit : (7000 * (s + 1) ^ 5 + 2) ^ 2 < B) :
    Runs Δ' B fForgetC [toVal x, toVal c] (toVal (forgetC x c)) (7000 * (s + 1) ^ 5) := by
  have h1 : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  refine forgetC_runs_e12 hΔ hE1 B x c s hc (lt_of_le_of_lt ?_ hfit)
  nlinarith

theorem joinC_runs_fits {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (s : ℕ)
    (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hfit : (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + 2) ^ 2 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (14000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3)) := by
  have hR := join_R0_bound B0.card kmax
  have hR1 : R0k kmax ≤ 6000 * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) :=
    le_trans (Nat.le_mul_of_pos_left (R0k kmax) (Nat.pow_pos (by omega : 0 < 2 * B0.card + 2))) hR
  have hE : 1 ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := Nat.one_le_two_pow
  exact joinC_runs_e12 hΔ hE1 B ha hb s hsa hsb (lt_of_le_of_lt (join_fit_arith s _ _ hE hR1) hfit)

end concrete

end E2
end Lax117284Proofs.Treewidth.Fun

end
