import Lax117284Proofs.Treewidth.Fun.E6bRun
import Lax117284Proofs.Treewidth.Fun.Lib
import Lax117284Proofs.Treewidth.Fun.ToValAlgSize
import Lax117284Proofs.Treewidth.Wrap.CompressSize
import Lax117284Proofs.Treewidth.Wrap.NiceSizeConn
import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Wrap.ImproveC
import Lax117284Proofs.Treewidth.Fun.VMSolveGuard
import Lax117284Proofs.Treewidth.Fun.E4Defs
import Lax117284.GraphWords
import Lax117284.BodlaenderGeneral
import Lax117284Proofs.Treewidth.Fun.Kit
import Lax117284.BodlaenderKloks

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bFinal` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (15): `E_extract` — the `Embeds` statements

* `embeds_extract`   : `fExtractUn` (packed argument `(x, k, nt, target)`) computes `extract (adjOfWord x) k nt target`
  within `nt.size² · Wx M k + 20` steps, `M = |x| + sz nt + mx nt`, `Wx M k = ((M+1) · 2^(1728 (k+2)^3))^60`.
* `E_extract`        : the form of `proofs-todo/Machine.lean`: labels `≤ |x|`, cost `(|x| + sz nt + 1)^62 · 2^(103680 (k+2)^3)`.
* `embeds_extractFirst` : `match tables … with [] => none | c :: _ => extract … c` (the extraction step of `improveC`).

Preconditions: `ntOk x k nt` (`Good`, width), `target ∈ tables`, and the two hypotheses of `extract_all` that the
Machine statement leaves implicit: `adjOfWord x` symmetric on a set `W` containing the vertices below `nt` (true for the graph
words of the wrapper: `W = range n`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord ntOk)

/-- `extract` followed by nothing: the first table entry (`improveC`'s call) -/
def extractFirst (adj : Adj) (k : ℕ) (nt : NT) : Option RT :=
  match tables adj k nt with
  | [] => none
  | c :: _ => extract adj k nt c

/-- the side conditions of the extraction: `ntOk`, a symmetric set `W` above the vertices of `nt` -/
def ExtOk (x : List ℕ) (k : ℕ) (nt : NT) : Prop :=
  ntOk x k nt ∧ ∃ W : Finset ℕ, (adjOfWord x).SymmOn W ∧ nt.under ⊆ W

/-- the closed form of the cost -/
theorem cost_closed (M k s : ℕ) : s ^ 2 * Wx M k = s ^ 2 * (M + 1) ^ 60 * 2 ^ (103680 * (k + 2) ^ 3) := by
  unfold Wx Zc Yk pX
  rw [mul_pow, ← pow_mul]
  have : 1728 * (k + 2) ^ 3 * 60 = 103680 * (k + 2) ^ 3 := by ring
  rw [this, mul_assoc]

section top
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ')
include hΔ

/-- `extractFirst`: the extraction step of `improveC` (`tables` once, then `extract` of its first entry) -/
theorem extractFirst_runs (B : ℕ) (x : List ℕ) (k : ℕ) (nt : NT) (M : ℕ) (hxM : x.length ≤ M)
    (hsM : sz nt ≤ M) (hmM : mx nt ≤ M) (hok : ExtOk x k nt)
    (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B)
    (hB : (nt.size * E4.cnode M k + nt.size ^ 2 * Wx M k + 30 + 2) ^ 2 < B) :
    Runs Δ' B fExtractFirst [toVal x, toVal k, toVal nt] (toVal (extractFirst (adjOfWord x) k nt))
      (nt.size * E4.cnode M k + nt.size ^ 2 * Wx M k + 30) := by
  obtain ⟨⟨hg, hw⟩, W, hs, hW⟩ := hok
  have hB1 : (nt.size ^ 2 * Wx M k + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have hBt : (nt.size * E4.cnode M k + 2) ^ 2 < B := lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
  have hB1000 : 1000 < B := hB_of_sq M k _ (size_pos nt) hB1
  have hT := E4.tables_runs hΔ.e4 B x k M hxM hn hk nt hg hw hsM hmM hBt
  unfold extractFirst
  rcases hcase : tables (adjOfWord x) k nt with _ | ⟨c, T'⟩
  · rw [hcase] at hT
    refine Runs.mk (hΔ.e6 _ _ Δ_extractFirst) ?_
    simp only [toVal_nil, toVal_none]
    ev_start
    · ev_run
    · omega
  · have hc : c ∈ tables (adjOfWord x) k nt := by rw [hcase]; simp
    have hE := extract_runs hΔ B x k M hs hxM hn hk nt hg hW hw hsM hmM hB1 c hc
    rw [hcase] at hT
    refine Runs.mk (hΔ.e6 _ _ Δ_extractFirst) ?_
    simp only [toVal_cons]
    ev_start
    · ev_run
    · omega

end top

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6bAssembly` -/

section
set_option linter.unusedSectionVars false

/-!
# WP E6b (16): the worked assembly with E1 + E2 + E3 + E4 + E5 + E6b — `extract` in the union table

`asm6Tbl = e1Tbl ∪ e2Tbl 152 ∪ e3Tbl ∪ e4Tbl ∪ e5Tbl ∪ e6bTbl` (ids `128 … 157`, `160 … 182`, `256 … 332`, `384 … 396`,
`448 … 535`, `704 … 710`), `asm6Δ = layerΔ Lib.Δ 128 asm6Tbl`.

**How the assembler references the table.**  It needs, for its own table `T` (e.g. the union that also contains E6a's
`640 … 703`), the four inclusions `E3.asmTbl ⊑ T`, `E4.e4Tbl ⊑ T`, `E5Tbl.e5Tbl ⊑ T`, `E6b.e6bTbl ⊑ T`; then
`Ext6.of_tbl … : Ext6 (layerΔ Lib.Δ 128 T)` and every theorem of `E6bFinal` (`embeds_extract`, `E_extract`,
`extractFirst_runs`) applies to `Δ' := layerΔ Lib.Δ 128 T`.  The entry points are `fExtractUn = 709` (packed argument) and
`fExtract = 704`, `fExtractFirst = 710`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

theorem asm4Tbl_lt {f : ℕ} {b : Tm} (h : E4.asm4Tbl f = some b) : f < 448 := by
  unfold E4.asm4Tbl orElseΔ at h
  rcases h1 : E3.asmTbl f with _ | c
  · rw [h1] at h
    have := (E4.e4Tbl_lt (by simpa using h)).2; omega
  · have := E5Inst.asmTbl_lt h1; omega

theorem e5Tbl_disj_asm4 : ∀ f b, E5Tbl.e5Tbl f = some b → E4.asm4Tbl f = none := by
  intro f b h
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have := asm4Tbl_lt hc
  have := E5Tbl.e5Tbl_ge h
  omega

/-- the union of E1–E6b -/
def asm6Tbl : ℕ → Option Tm := orElseΔ (orElseΔ E4.asm4Tbl E5Tbl.e5Tbl) e6bTbl

/-- the assembled table -/
def asm6Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm6Tbl

theorem e6bTbl_disj : ∀ f b, e6bTbl f = some b → (orElseΔ E4.asm4Tbl E5Tbl.e5Tbl) f = none := by
  intro f b h
  have h6 := (e6bTbl_lt h).1
  unfold orElseΔ
  rcases h1 : E4.asm4Tbl f with _ | c
  · rcases h2 : E5Tbl.e5Tbl f with _ | c'
    · simp
    · have := E5Tbl.e5Tbl_lt h2; omega
  · have := asm4Tbl_lt h1; omega

/-- any table containing the E1–E3 union, `e4Tbl`, `e5Tbl` and `e6bTbl` gives the hypotheses of every E6b theorem -/
theorem Ext6.of_tbl {T : ℕ → Option Tm} (ha : E3.asmTbl ⊑ T) (h4 : E4.e4Tbl ⊑ T) (h5 : E5Tbl.e5Tbl ⊑ T)
    (h6 : e6bTbl ⊑ T) : Ext6 (layerΔ Lib.Δ 128 T) :=
  ⟨E4.Ext4.of_tbl ha h4,
    Ext.trans E5Tbl.ext (E5Tbl.ext_asm T (Ext.trans (Ext.orElse_left E1.e1Tbl _ : E1.e1Tbl ⊑ E3.asmTbl) ha) h5),
    Ext.layer_mono h6⟩

end E6b
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aDefs` -/

section
/-!
# WP E6a (1): the table `e6aTbl` (ids `640 … 703`) — `compress`, `niceOf`, `NT.addEverywhere`, `NT.encode` as F-functions

The functions use only the library (`Lib.Δ`); `e6aΔ = layerΔ Lib.Δ 128 e6aTbl` and every theorem is stated for an arbitrary
`Δ'` with `e6aΔ ⊑ Δ'`.

| id | function | arguments |
|---|---|---|
| 640 `fFlatKids` | `flatKids` | `[X, L]` |
| 641 `fCompress` | `compress` | `[t]` |
| 642 `fCompressC` | `compress` (`map` callee) | `[ctx, t]` |
| 643 `fBagNT` | `NT.bag` | `[nt]` |
| 644 `fIntroMany` | `introMany` | `[l, t]` |
| 645 `fForgetMany` | `forgetMany` | `[l, t]` |
| 646 `fConv` | `conv` | `[X, t]` |
| 647 `fConvNice` | `conv X (niceOf k)` (`map` callee) | `[X, k]` |
| 648 `fJoinFold` | `ts.foldl NT.join t` | `[ts, t]` |
| 649 `fNiceOf` | `niceOf` | `[t]` |
| 650 `fAddEv` | `NT.addEverywhere` | `[v, nt]` |
| 651 `fAddEvP` | `NT.addEverywhere` (tuple argument) | `[(v, nt)]` |
| 652 `fRecs` | `NT.recs` | `[b, nt]` |
| 653 `fTriple` | `[r.1, r.2.1, r.2.2]` (`flatMap` callee) | `[ctx, r]` |
| 654 `fEncode` | `NT.encode` | `[nt]` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open Lib1

abbrev fFlatKids : ℕ := 640
abbrev fCompress : ℕ := 641
abbrev fCompressC : ℕ := 642
abbrev fBagNT : ℕ := 643
abbrev fIntroMany : ℕ := 644
abbrev fForgetMany : ℕ := 645
abbrev fConv : ℕ := 646
abbrev fConvNice : ℕ := 647
abbrev fJoinFold : ℕ := 648
abbrev fNiceOf : ℕ := 649
abbrev fAddEv : ℕ := 650
abbrev fAddEvP : ℕ := 651
abbrev fRecs : ℕ := 652
abbrev fTriple : ℕ := 653
abbrev fEncode : ℕ := 654

/-- `flatKids X L`, on `[X, L]`; a kid `node Y ls` is `cons Y ls`. -/
def flatKidsTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.letE (.fst (V 1))
      (.ite (.call Lib3.fSubsetS [.fst (V 0), V 1])
        (.call fAppend [.snd (V 0), .call fFlatKids [V 1, .snd (V 2)]])
        (.cons (V 0) (.call fFlatKids [V 1, .snd (V 2)]))))

def compressTm : Tm :=
  .cons (.fst (V 0)) (.call fFlatKids [.fst (V 0), .call fMap [.lit fCompressC, .lit 0, .snd (V 0)]])

def compressCTm : Tm := .call fCompress [V 1]

/-- `NT.bag`; the nice tree `intro v c = (1, (v, c))`, `forget v c = (2, (v, c))`, `join a b = (3, (a, b))`. -/
def bagNTTm : Tm :=
  .ite (.isNat (V 0)) (.lit 0)
    (.ite (.eq (.fst (V 0)) (.lit 1))
      (.call Lib3.fInsertS [.fst (.snd (V 0)), .call fBagNT [.snd (.snd (V 0))]])
      (.ite (.eq (.fst (V 0)) (.lit 2))
        (.call Lib3.fEraseS [.fst (.snd (V 0)), .call fBagNT [.snd (.snd (V 0))]])
        (.call fBagNT [.fst (.snd (V 0))])))

def introManyTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fIntroMany [.snd (V 0), .cons (.lit 1) (.cons (.fst (V 0)) (V 1))])

def forgetManyTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fForgetMany [.snd (V 0), .cons (.lit 2) (.cons (.fst (V 0)) (V 1))])

/-- `conv X t = introMany (X \ bag t) (forgetMany (bag t \ X) t)`; environment `[b, X, t]` under the `let`. -/
def convTm : Tm :=
  .letE (.call fBagNT [V 1])
    (.call fIntroMany [.call Lib3.fDiffS [V 1, V 0], .call fForgetMany [.call Lib3.fDiffS [V 0, V 1], V 2]])

def convNiceTm : Tm := .call fConv [V 0, .call fNiceOf [V 1]]

def joinFoldTm : Tm :=
  .ite (.isNat (V 0)) (V 1)
    (.call fJoinFold [.snd (V 0), .cons (.lit 3) (.cons (V 1) (.fst (V 0)))])

def niceOfTm : Tm :=
  .letE (.call fMap [.lit fConvNice, .fst (V 0), .snd (V 0)])
    (.ite (.isNat (V 0)) (.call fIntroMany [.fst (V 1), .lit 0])
      (.call fJoinFold [.snd (V 0), .fst (V 0)]))

def addEvTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.lit 1) (.cons (V 0) (.lit 0)))
    (.ite (.eq (.fst (V 1)) (.lit 3))
      (.cons (.lit 3) (.cons (.call fAddEv [V 0, .fst (.snd (V 1))]) (.call fAddEv [V 0, .snd (.snd (V 1))])))
      (.cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.call fAddEv [V 0, .snd (.snd (V 1))]))))

def addEvPTm : Tm := .call fAddEv [.fst (V 0), .snd (V 0)]

/-- `NT.recs b t` (records `(kind, (vertex, other))`); for a join the second child is numbered first. -/
def recsTm : Tm :=
  .ite (.isNat (V 1)) (.cons (.cons (.lit 0) (.cons (.lit 0) (.lit 0))) (.lit 0))
    (.ite (.eq (.fst (V 1)) (.lit 3))
      (.letE (.call fRecs [V 0, .snd (.snd (V 1))])
        (.letE (.call fRecs [.add (V 1) (.call fLength [V 0]), .fst (.snd (V 2))])
          (.call fAppend [V 1, .call fAppend [V 0,
            .cons (.cons (.lit 3) (.cons (.lit 0) (.sub (.add (V 2) (.call fLength [V 1])) (.lit 1)))) (.lit 0)]])))
      (.call fAppend [.call fRecs [V 0, .snd (.snd (V 1))],
        .cons (.cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.lit 0))) (.lit 0)]))

def tripleTm : Tm :=
  .cons (.fst (V 1)) (.cons (.fst (.snd (V 1))) (.cons (.snd (.snd (V 1))) (.lit 0)))

def encodeTm : Tm :=
  .letE (.call fRecs [.lit 0, V 0])
    (.cons (.call fLength [V 0]) (.call fFlatMap [.lit fTriple, .lit 0, V 0]))

/-- the table of WP E6a (ids `640 … 654`) -/
def e6aTbl : ℕ → Option Tm := fun f =>
  match f with
  | 640 => some flatKidsTm | 641 => some compressTm | 642 => some compressCTm | 643 => some bagNTTm
  | 644 => some introManyTm | 645 => some forgetManyTm | 646 => some convTm | 647 => some convNiceTm
  | 648 => some joinFoldTm | 649 => some niceOfTm | 650 => some addEvTm | 651 => some addEvPTm
  | 652 => some recsTm | 653 => some tripleTm | 654 => some encodeTm
  | _ => none

/-- the E6a layer on top of the library -/
def e6aΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 e6aTbl

theorem e6aTbl_lt {f : ℕ} {b : Tm} (h : e6aTbl f = some b) : 640 ≤ f ∧ f < 655 := by
  unfold e6aTbl at h
  split at h <;> first | (simp at h; done) | omega

theorem ext_lib : Lib.Δ ⊑ e6aΔ := Ext.layer e6aTbl (fun _ _ h => Lib.Δ_lt h)

theorem ext1 {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') : Lib1.Δ ⊑ Δ' := Ext.trans Lib.ext1 (Ext.trans ext_lib hΔ)
theorem ext3 {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') : Lib3.Δ ⊑ Δ' := Ext.trans Lib.ext3 (Ext.trans ext_lib hΔ)

theorem Δ_flatKids : e6aΔ fFlatKids = some flatKidsTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fFlatKids by decide)]; rfl
theorem Δ_compress : e6aΔ fCompress = some compressTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fCompress by decide)]; rfl
theorem Δ_compressC : e6aΔ fCompressC = some compressCTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fCompressC by decide)]; rfl
theorem Δ_bagNT : e6aΔ fBagNT = some bagNTTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fBagNT by decide)]; rfl
theorem Δ_introMany : e6aΔ fIntroMany = some introManyTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fIntroMany by decide)]; rfl
theorem Δ_forgetMany : e6aΔ fForgetMany = some forgetManyTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fForgetMany by decide)]; rfl
theorem Δ_conv : e6aΔ fConv = some convTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fConv by decide)]; rfl
theorem Δ_convNice : e6aΔ fConvNice = some convNiceTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fConvNice by decide)]; rfl
theorem Δ_joinFold : e6aΔ fJoinFold = some joinFoldTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fJoinFold by decide)]; rfl
theorem Δ_niceOf : e6aΔ fNiceOf = some niceOfTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fNiceOf by decide)]; rfl
theorem Δ_addEv : e6aΔ fAddEv = some addEvTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fAddEv by decide)]; rfl
theorem Δ_recs : e6aΔ fRecs = some recsTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fRecs by decide)]; rfl
theorem Δ_triple : e6aΔ fTriple = some tripleTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fTriple by decide)]; rfl
theorem Δ_encode : e6aΔ fEncode = some encodeTm := by
  simp [e6aΔ, layerΔ_ge e6aTbl (show 128 ≤ fEncode by decide)]; rfl

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aCompress` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (3): `compress` (with `flatKids`)

* `flatKids_runs` : cost `100 (s+1) · sz L` for `sz X ≤ s`;
* `compress_runs` : cost `200 (s+1)² · wt t` (`wt t = 2 size t − 1`) for `sz t ≤ s`;
* `embeds_compress` : `Embeds … fCompress … compress (400 (sz t + sz (compress t) + 1)³)`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

/-! ## sizes -/

theorem sz_rt_node' (X : Finset ℕ) (ks : List RT) : sz (RT.node X ks) = sz X + sz ks + 1 := by
  simp only [sz, toVal_rt, Val.size]

theorem sz_map_le6 {α β : Type} [ToVal α] [ToVal β] (f : α → β) : ∀ l : List α,
    (∀ a ∈ l, sz (f a) ≤ sz a) → sz (l.map f) ≤ sz l
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have ih := sz_map_le6 f l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.map_cons, sz_cons, sz_cons]; omega

theorem sz_flatKids_le (X : Finset ℕ) : ∀ L : List RT, sz (flatKids X L) ≤ sz L
  | [] => by simp [flatKids]
  | .node Y ls :: rest => by
    have ih := sz_flatKids_le X rest
    rw [flatKids]
    by_cases hY : Y ⊆ X
    · simp only [hY, if_true]
      have := sz_append ls (flatKids X rest)
      rw [sz_cons, sz_rt_node']
      have := sz_pos Y
      omega
    · simp only [hY, if_false]
      rw [sz_cons, sz_cons, sz_rt_node']
      omega

theorem sz_compress_le : ∀ t : RT, sz (compress t) ≤ sz t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [RT.compress_node, sz_rt_node', sz_rt_node']
    have h1 := sz_flatKids_le X (ks.map compress)
    have h2 := sz_map_le6 compress ks ih
    omega

/-! ## the potential `wt t = 2 · size t − 1` -/

def wtR (t : RT) : ℕ := 2 * t.size - 1

theorem wtR_node (X : Finset ℕ) (ks : List RT) : wtR (.node X ks) = 2 * (ks.map RT.size).sum + 1 := by
  simp [wtR, RT.size_node]; omega

theorem sum_wtR : ∀ ks : List RT, (ks.map wtR).sum + ks.length = 2 * (ks.map RT.size).sum
  | [] => by simp
  | k :: ks => by
    have h := sum_wtR ks
    have h1 := RT.size_pos k
    simp only [List.map_cons, List.sum_cons, List.length_cons, wtR]
    omega

theorem sum_le_wtR : ∀ (ks : List RT) (cf : RT → ℕ) (C : ℕ),
    (∀ k ∈ ks, cf k ≤ C * wtR k + 3) → (ks.map cf).sum ≤ C * (ks.map wtR).sum + 3 * ks.length
  | [], _, _, _ => by simp
  | k :: ks, cf, C, h => by
    have h1 := h k (by simp)
    have ih := sum_le_wtR ks cf C (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-! ## `flatKids` -/

section flat
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem flatKids_runs (X : Finset ℕ) (s : ℕ) (hX : sz X ≤ s) (hB : 1000 < B) :
    ∀ L : List RT, Runs Δ' B fFlatKids [toVal X, toVal L] (toVal (flatKids X L)) (100 * (s + 1) * sz L) := by
  have hXc : X.card ≤ s := le_trans (by rw [sz_finset]; omega) hX
  intro L
  induction L with
  | nil =>
    refine Runs.mk (hΔ _ _ Δ_flatKids) ?_
    ev_start
    · ev_run
    · simp; nlinarith
  | cons k rest ih =>
    obtain ⟨Y, ls⟩ := k
    have hYc : Y.card ≤ sz Y := by rw [sz_finset]; omega
    have hlsl : ls.length ≤ sz ls := length_le_sz ls
    have hsub := Lib3.subset_runs (ext3 hΔ) B (by omega) Y X (decide (Y ⊆ X)) (by simp)
    have happ := append_runs (ext1 hΔ) B ls (flatKids X rest)
    have hsl : sz (RT.node Y ls :: rest) = sz Y + sz ls + sz rest + 2 := by
      rw [sz_cons, sz_rt_node']; omega
    have hlsl' : ls.length ≤ sz ls := length_le_sz ls
    refine Runs.mk (hΔ _ _ Δ_flatKids) ?_
    rw [flatKids]
    simp only [toVal_cons, toVal_rt]
    by_cases hY : Y ⊆ X
    · simp only [hY, if_true, decide_true, toVal_true] at hsub ⊢
      ev_start
      · ev_run
        apply EvLe.iteT
        · ev_sub
        · ev_side
        · ev_run
      · rw [hsl]
        nlinarith
    · simp only [hY, if_false, decide_false, toVal_false] at hsub ⊢
      ev_start
      · ev_run
        apply EvLe.iteF
        · case hc => ev_sub
        · ev_side
        · ev_run
      · rw [hsl]
        nlinarith

theorem compress_runs (hB : 1000 < B) (s : ℕ) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fCompress [toVal t] (toVal (compress t)) (200 * (s + 1) ^ 2 * wtR t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hs
    rw [sz_rt_node'] at hs
    have hXs : sz X ≤ s := by omega
    have hks : sz ks ≤ s := by omega
    have hkid : ∀ k ∈ ks, sz k ≤ s := fun k hk => le_trans (sz_le_of_mem hk) hks
    have hc642 : fCompressC < B := by show 642 < B; omega
    have hf : ∀ k ∈ ks, Runs Δ' B fCompressC [.nat 0, toVal k] (toVal (compress k))
        (200 * (s + 1) ^ 2 * wtR k + 3) := by
      intro k hk
      have h1 := ih k hk (hkid k hk)
      refine Runs.mk (hΔ _ _ Δ_compressC) ?_
      ev_start
      · ev_run
      · omega
    have hmap := map_runs (ext1 hΔ) B fCompressC (.nat 0) compress (fun k => 200 * (s + 1) ^ 2 * wtR k + 3) ks hf
    have hsum := sum_le_wtR ks (fun k => 200 * (s + 1) ^ 2 * wtR k + 3) (200 * (s + 1) ^ 2) (fun k _ => le_refl _)
    have hsk : sz (ks.map compress) ≤ s :=
      le_trans (sz_map_le6 compress ks (fun k _ => sz_compress_le k)) hks
    have hflat := flatKids_runs hΔ B X s hXs hB (ks.map compress)
    have hlen := length_le_sz ks
    have hw := sum_wtR ks
    have hwn := wtR_node X ks
    have hP : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hP2 : (s + 1) * s ≤ (s + 1) ^ 2 := by nlinarith
    refine Runs.mk (hΔ _ _ Δ_compress) ?_
    rw [RT.compress_node]
    simp only [toVal_rt]
    ev_start
    · ev_run
    · rw [hwn]
      nlinarith

end flat

theorem wtR_le_sz (t : RT) : wtR t ≤ 2 * sz t := by
  have := size_le_sz t; unfold wtR; omega

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

/-- **`compress`** (`fCompress`, argument `t`), unconditionally; output-sensitive cost of degree 3. -/
theorem embeds_compress : Embeds Δ' fCompress (fun _ : RT => True) compress
    (fun t => 400 * (sz t + sz (compress t) + 1) ^ 3) := by
  intro B t _ hfit
  have hc : 400 * (sz t + sz (compress t) + 1) ^ 3 + 3 < B := hfit.cost_lt
  have hp1 := sz_pos t
  have hp2 := sz_pos (compress t)
  have hS : 3 ≤ sz t + sz (compress t) + 1 := by omega
  have hS3 : 27 ≤ (sz t + sz (compress t) + 1) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hS 3
  have h1000 : 1000 < B := by omega
  have h := compress_runs (Δ' := Δ') hΔ B h1000 (sz t) t le_rfl
  refine h.mono ?_
  have hw := wtR_le_sz t
  have hsq : (sz t + 1) ^ 2 ≤ (sz t + sz (compress t) + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : (sz t + sz (compress t) + 1) ^ 3 = (sz t + sz (compress t) + 1) ^ 2 * (sz t + sz (compress t) + 1) := by ring
  show 200 * (sz t + 1) ^ 2 * wtR t ≤ 400 * (sz t + sz (compress t) + 1) ^ 3
  rw [h3]
  have : (sz t + 1) ^ 2 * wtR t ≤ (sz t + sz (compress t) + 1) ^ 2 * (2 * (sz t + sz (compress t) + 1)) :=
    Nat.mul_le_mul hsq (by omega)
  nlinarith

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aNice` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (4): the building blocks of `niceOf` — `NT.bag`, `introMany`, `forgetMany`, `conv`, the join fold
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem card_bag_le_inner : ∀ nt : NT, nt.bag.card ≤ nt.inner
  | .leaf => by simp [NT.bag, NT.inner]
  | .intro v c => by
    have h := card_bag_le_inner c
    have := Finset.card_insert_le v c.bag
    simp only [NT.bag, NT.inner]; omega
  | .forget v c => by
    have h := card_bag_le_inner c
    have := Finset.card_erase_le (a := v) (s := c.bag)
    simp only [NT.bag, NT.inner]; omega
  | .join a b => by
    have h := card_bag_le_inner a
    simp only [NT.bag, NT.inner]; omega

theorem sum_le_wtR' : ∀ (ks : List RT) (cf : RT → ℕ) (C D : ℕ),
    (∀ k ∈ ks, cf k ≤ C * wtR k + D) → (ks.map cf).sum ≤ C * (ks.map wtR).sum + D * ks.length
  | [], _, _, _, _ => by simp
  | k :: ks, cf, C, D, h => by
    have h1 := h k (by simp)
    have ih := sum_le_wtR' ks cf C D (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- a kid's nice tree is no larger than the nice tree of the node -/
theorem niceOf_kid_size {X : Finset ℕ} {ks : List RT} {k : RT} (hk : k ∈ ks) :
    (niceOf k).size ≤ (niceOf (.node X ks)).size := by
  rcases ks with _ | ⟨k0, ks'⟩
  · simp at hk
  · have h1 := niceOf_size_cons X k0 ks'
    have h2 : (conv X (niceOf k)).size + 1 ≤ ((k0 :: ks').map (fun k' => (conv X (niceOf k')).size + 1)).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun k' => (conv X (niceOf k')).size + 1) hk)
    have h3 := conv_size_kid X k
    omega

section niceOf
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem bag_runs (hB : 1000 < B) : ∀ nt : NT,
    Runs Δ' B fBagNT [toVal nt] (toVal nt.bag) (100 * (nt.inner + 1) ^ 2) := by
  intro nt
  induction nt with
  | leaf =>
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    ev_start
    · ev_run
    · simp [NT.inner, NT.bag]
  | intro v c ih =>
    have h1 := Lib3.insert_runs (ext3 hΔ) B v c.bag
    have hc := card_bag_le_inner c
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_intro]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith
  | forget v c ih =>
    have h1 := Lib3.erase_runs (ext3 hΔ) B v c.bag
    have hc := card_bag_le_inner c
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_forget]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith
  | join a b iha ihb =>
    refine Runs.mk (hΔ _ _ Δ_bagNT) ?_
    simp only [NT.bag, toVal_nt_join]
    have h3 : (a.inner + 1) ^ 2 + 3 ≤ (a.inner + b.inner + 1 + 1) ^ 2 := by
      nlinarith [Nat.zero_le a.inner, Nat.zero_le b.inner]
    ev_start
    · ev_run
    · simp only [NT.inner]; nlinarith

theorem introMany_runs (hB : 1000 < B) : ∀ (l : List ℕ) (t : NT),
    Runs Δ' B fIntroMany [toVal l, toVal t] (toVal (introMany l t)) (40 * l.length + 10) := by
  intro l
  induction l with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_introMany) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    intro t
    have h1 := ih (NT.intro x t)
    refine Runs.mk (hΔ _ _ Δ_introMany) ?_
    rw [introMany_cons]
    ev_start
    · ev_run
    · simp; omega

theorem forgetMany_runs (hB : 1000 < B) : ∀ (l : List ℕ) (t : NT),
    Runs Δ' B fForgetMany [toVal l, toVal t] (toVal (forgetMany l t)) (40 * l.length + 10) := by
  intro l
  induction l with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_forgetMany) ?_
    ev_start
    · ev_run
    · simp
  | cons x l ih =>
    intro t
    have h1 := ih (NT.forget x t)
    refine Runs.mk (hΔ _ _ Δ_forgetMany) ?_
    rw [forgetMany_cons]
    ev_start
    · ev_run
    · simp; omega

theorem joinFold_runs (hB : 1000 < B) : ∀ (ts : List NT) (t : NT),
    Runs Δ' B fJoinFold [toVal ts, toVal t] (toVal (ts.foldl NT.join t)) (40 * ts.length + 10) := by
  intro ts
  induction ts with
  | nil =>
    intro t
    refine Runs.mk (hΔ _ _ Δ_joinFold) ?_
    ev_start
    · ev_run
    · simp
  | cons x ts ih =>
    intro t
    have h1 := ih (NT.join t x)
    refine Runs.mk (hΔ _ _ Δ_joinFold) ?_
    rw [List.foldl_cons]
    ev_start
    · ev_run
    · simp; omega

theorem conv_runs (hB : 1000 < B) (X : Finset ℕ) (t : NT) (s : ℕ) (hX : X.card ≤ s) (ht : t.inner ≤ s) :
    Runs Δ' B fConv [toVal X, toVal t] (toVal (conv X t)) (500 * (s + 1) ^ 2) := by
  have hb := bag_runs hΔ B hB t
  have hbc := card_bag_le_inner t
  have hc1 : (X \ t.bag).card ≤ s := le_trans (Finset.card_le_card Finset.sdiff_subset) hX
  have hc2 : (t.bag \ X).card ≤ s := le_trans (Finset.card_le_card Finset.sdiff_subset) (le_trans hbc ht)
  have hd1 : Runs Δ' B Lib3.fDiffS [toVal X, toVal t.bag] (toVal ((X \ t.bag).sort (· ≤ ·)))
      (60 * (X.card + t.bag.card) + 20) := Lib3.sdiff_runs (ext3 hΔ) B X t.bag
  have hd2 : Runs Δ' B Lib3.fDiffS [toVal t.bag, toVal X] (toVal ((t.bag \ X).sort (· ≤ ·)))
      (60 * (t.bag.card + X.card) + 20) := Lib3.sdiff_runs (ext3 hΔ) B t.bag X
  have hf := forgetMany_runs hΔ B hB ((t.bag \ X).sort (· ≤ ·)) t
  rw [Finset.length_sort] at hf
  have hi := introMany_runs hΔ B hB ((X \ t.bag).sort (· ≤ ·)) (forgetMany ((t.bag \ X).sort (· ≤ ·)) t)
  rw [Finset.length_sort] at hi
  refine Runs.mk (hΔ _ _ Δ_conv) ?_
  unfold conv
  ev_start
  · ev_run
  · nlinarith

theorem niceOf_runs (hB : 1000 < B) (s : ℕ) : ∀ t : RT, sz t ≤ s → (niceOf t).size ≤ s →
    Runs Δ' B fNiceOf [toVal t] (toVal (niceOf t)) (1000 * (s + 1) ^ 2 * wtR t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hs hn
    rw [sz_rt_node'] at hs
    have hXs : sz X ≤ s := by omega
    have hXc : X.card ≤ s := le_trans (by rw [sz_finset]; omega) hXs
    have hks : sz ks ≤ s := by omega
    have hkid : ∀ k ∈ ks, sz k ≤ s := fun k hk => le_trans (sz_le_of_mem hk) hks
    have hkn : ∀ k ∈ ks, (niceOf k).size ≤ s := fun k hk => le_trans (niceOf_kid_size hk) hn
    have hc647 : fConvNice < B := by show 647 < B; omega
    have hP : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hf : ∀ k ∈ ks, Runs Δ' B fConvNice [toVal X, toVal k] (toVal (conv X (niceOf k)))
        (1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10)) := by
      intro k hk
      have h1 := ih k hk (hkid k hk) (hkn k hk)
      have hin : (niceOf k).inner ≤ s := by
        have := (inner_lt_size (niceOf k)).1; have := hkn k hk; omega
      have h2 := conv_runs hΔ B hB X (niceOf k) s hXc hin
      refine Runs.mk (hΔ _ _ Δ_convNice) ?_
      ev_start
      · ev_run
      · omega
    have hmap := map_runs (ext1 hΔ) B fConvNice (toVal X) (fun k => conv X (niceOf k))
      (fun k => 1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10)) ks hf
    have hsum := sum_le_wtR' ks (fun k => 1000 * (s + 1) ^ 2 * wtR k + (500 * (s + 1) ^ 2 + 10))
      (1000 * (s + 1) ^ 2) (500 * (s + 1) ^ 2 + 10) (fun k _ => le_refl _)
    have hlen := length_le_sz ks
    have hw := sum_wtR ks
    have hwn := wtR_node X ks
    rcases ks with _ | ⟨k, ks'⟩
    · have hi : Runs Δ' B fIntroMany [toVal X, toVal NT.leaf] (toVal (introMany (X.sort (· ≤ ·)) NT.leaf))
          (40 * X.card + 10) := by
        have := introMany_runs hΔ B hB (X.sort (· ≤ ·)) NT.leaf
        rw [Finset.length_sort] at this
        exact this
      refine Runs.mk (hΔ _ _ Δ_niceOf) ?_
      rw [niceOf_node]
      simp only [List.map_nil, toVal_rt] at hmap ⊢
      ev_start
      · ev_run
      · rw [hwn]
        simp only [List.map_nil, List.sum_nil, List.length_nil] at *
        nlinarith
    · have hj := joinFold_runs hΔ B hB (ks'.map (fun k' => conv X (niceOf k'))) (conv X (niceOf k))
      rw [List.length_map] at hj
      refine Runs.mk (hΔ _ _ Δ_niceOf) ?_
      rw [niceOf_node]
      simp only [List.map_cons, toVal_rt] at hmap ⊢
      ev_start
      · ev_run
      · rw [hwn]
        simp only [List.map_cons, List.sum_cons, List.length_cons] at hsum hmap hw hlen hs ⊢
        nlinarith

end niceOf

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aEnc` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem NT.size_pos_aux (t : NT) : 1 ≤ t.size := by cases t <;> simp [NT.size] <;> omega

section addEv
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem addEv_runs (v : ℕ) (hB : 4 < B) : ∀ nt : NT,
    Runs Δ' B fAddEv [toVal v, toVal nt] (toVal (NT.addEverywhere v nt)) (30 * nt.size) := by
  intro nt
  induction nt with
  | leaf =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]
  | intro u c ih =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega
  | forget u c ih =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega
  | join a b iha ihb =>
    refine Runs.mk (hΔ _ _ Δ_addEv) ?_
    ev_start
    · ev_run
    · simp [NT.size]; omega

end addEv

theorem recs_length : ∀ (nt : NT) (b : ℕ), (NT.recs b nt).length = nt.size
  | .leaf, b => by simp [NT.recs, NT.size]
  | .intro v c, b => by simp [NT.recs, NT.size, recs_length c b]
  | .forget v c, b => by simp [NT.recs, NT.size, recs_length c b]
  | .join x y, b => by
    simp [NT.recs, NT.size, recs_length x, recs_length y]; omega

section recs
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ') (B : ℕ)
include hΔ

theorem recs_runs : ∀ (nt : NT) (b : ℕ), 8 * (b + nt.size) + 40 < B →
    Runs Δ' B fRecs [toVal b, toVal nt] (toVal (NT.recs b nt)) (60 * nt.size ^ 2) := by
  intro nt
  induction nt with
  | leaf =>
    intro b hB
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    ev_start
    · ev_run
    · simp [NT.size]
  | intro u c ih =>
    intro b hB
    simp only [NT.size] at hB
    have h1 := ih b (by omega)
    have h2 := append_runs (ext1 hΔ) B (NT.recs b c) [((1 : ℕ), (u, (0 : ℕ)))]
    rw [recs_length] at h2
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith
  | forget u c ih =>
    intro b hB
    simp only [NT.size] at hB
    have h1 := ih b (by omega)
    have h2 := append_runs (ext1 hΔ) B (NT.recs b c) [((2 : ℕ), (u, (0 : ℕ)))]
    rw [recs_length] at h2
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith
  | join x y ihx ihy =>
    intro b hB
    simp only [NT.size] at hB
    have hx1 := NT.size_pos_aux x
    have h1 := ihy b (by omega)
    have h2 := ihx (b + y.size) (by omega)
    have hl := length_runs (ext1 hΔ) B (NT.recs b y) (by rw [recs_length]; omega)
    rw [recs_length] at hl
    have h3 := append_runs (ext1 hΔ) B (NT.recs (b + y.size) x) [((3 : ℕ), ((0 : ℕ), b + y.size - 1))]
    rw [recs_length] at h3
    have h4 := append_runs (ext1 hΔ) B (NT.recs b y)
      (NT.recs (b + y.size) x ++ [((3 : ℕ), ((0 : ℕ), b + y.size - 1))])
    rw [recs_length] at h4
    refine Runs.mk (hΔ _ _ Δ_recs) ?_
    simp only [NT.recs, recs_length, List.append_assoc]
    ev_start
    · ev_run
    · simp [NT.size]; nlinarith

theorem triple_runs (ctx : Val) (r : ℕ × ℕ × ℕ) (hB : 0 < B) :
    Runs Δ' B fTriple [ctx, toVal r] (toVal [r.1, r.2.1, r.2.2]) 20 := by
  obtain ⟨a, b, c⟩ := r
  refine Runs.mk (hΔ _ _ Δ_triple) ?_
  ev_start
  · ev_run
  · omega

theorem encode_runs (nt : NT) (hB : 8 * nt.size + 1000 < B) :
    Runs Δ' B fEncode [toVal nt] (toVal nt.encode) (200 * nt.size ^ 2) := by
  have hp := NT.size_pos_aux nt
  have hT : fTriple < B := by show 653 < B; omega
  have h1 := recs_runs hΔ B nt 0 (by omega)
  have hl : Runs Δ' B fLength [toVal (NT.recs 0 nt)] (toVal (NT.recs 0 nt).length) (8 * nt.size + 5) :=
    (length_runs (ext1 hΔ) B (NT.recs 0 nt) (by rw [recs_length]; omega)).mono (by rw [recs_length])
  have hf := flatMap_runs (ext1 hΔ) B fTriple (.nat 0) (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2]) (fun _ => 20)
    (NT.recs 0 nt) (fun r _ => triple_runs hΔ B _ r (by omega))
  have hsum : ((NT.recs 0 nt).map (fun a : ℕ × ℕ × ℕ => 20 + 10 * [a.1, a.2.1, a.2.2].length + 20)).sum
      = nt.size * 70 := by
    have : ∀ l : List (ℕ × ℕ × ℕ), (l.map (fun a : ℕ × ℕ × ℕ => 20 + 10 * [a.1, a.2.1, a.2.2].length + 20)).sum
        = l.length * 70 := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; simp; ring
    rw [this, recs_length]
  rw [hsum] at hf
  have hv : toVal nt.encode = Val.cons (Val.nat (NT.recs 0 nt).length)
      (toVal ((NT.recs 0 nt).flatMap (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2]))) := rfl
  refine Runs.mk (hΔ _ _ Δ_encode) ?_
  rw [hv]
  ev_start
  · ev_run
  · nlinarith

end recs

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aTop` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E6a (5): `Embeds` for `niceOf`
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lib1

theorem card_vertsL_le_sz : ∀ ks : List RT, (∀ k ∈ ks, k.verts.card ≤ sz k) → (RT.vertsL ks).card ≤ sz ks
  | [], _ => by simp [RT.vertsL]
  | k :: ks, h => by
    have h1 := h k (by simp)
    have h2 := card_vertsL_le_sz ks (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := Finset.card_union_le k.verts (RT.vertsL ks)
    rw [sz_cons]
    simp only [RT.vertsL]
    omega

/-- the number of vertices of a rooted tree is at most its cell count -/
theorem card_verts_le_sz (t : RT) : t.verts.card ≤ sz t := by
  induction t using RT.ind with
  | _ X ks ih =>
    have h1 := card_vertsL_le_sz ks ih
    have h2 := Finset.card_union_le X (RT.vertsL ks)
    have h3 : X.card ≤ sz X := by rw [sz_finset]; omega
    rw [sz_rt_node']
    show (X ∪ RT.vertsL ks).card ≤ _
    omega

section embeds
variable {Δ' : ℕ → Option Tm} (hΔ : e6aΔ ⊑ Δ')
include hΔ

/-- **`niceOf` on a connected tree**: the cost is a polynomial (degree 5) in `sz t` alone
(`niceOf_size_le` : `size (niceOf t) ≤ (|V|+2)(size t+1)`). -/
theorem embeds_niceOf_conn : Embeds Δ' fNiceOf (fun t : RT => t.Conn) niceOf
    (fun t => 8000 * (sz t + 2) ^ 5) := by
  intro B t hcn hfit
  have hc : 8000 * (sz t + 2) ^ 5 + 3 < B := hfit.cost_lt
  have hp1 := sz_pos t
  have hS : 3 ≤ sz t + 2 := by omega
  have hS5 : 243 ≤ (sz t + 2) ^ 5 := by
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_left hS 5
  have h1000 : 1000 < B := by omega
  have hV := card_verts_le_sz t
  have hsize := size_le_sz t
  have hnz := niceOf_size_le hcn
  have hnz2 : (niceOf t).size ≤ (sz t + 2) ^ 2 := by
    refine le_trans hnz ?_
    calc (t.verts.card + 2) * (t.size + 1) ≤ (sz t + 2) * (sz t + 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = (sz t + 2) ^ 2 := by ring
  have hs1 : sz t ≤ (sz t + 2) ^ 2 := by nlinarith
  have h := niceOf_runs (Δ' := Δ') hΔ B h1000 ((sz t + 2) ^ 2) t hs1 hnz2
  refine h.mono ?_
  have hw := wtR_le_sz t
  show 1000 * ((sz t + 2) ^ 2 + 1) ^ 2 * wtR t ≤ 8000 * (sz t + 2) ^ 5
  have hq : (sz t + 2) ^ 2 + 1 ≤ 2 * (sz t + 2) ^ 2 := by nlinarith
  have hq2 : ((sz t + 2) ^ 2 + 1) ^ 2 ≤ 4 * (sz t + 2) ^ 4 := by
    calc ((sz t + 2) ^ 2 + 1) ^ 2 ≤ (2 * (sz t + 2) ^ 2) ^ 2 := Nat.pow_le_pow_left hq 2
      _ = 4 * (sz t + 2) ^ 4 := by ring
  have hq3 : ((sz t + 2) ^ 2 + 1) ^ 2 * wtR t ≤ (4 * (sz t + 2) ^ 4) * (2 * (sz t + 2)) :=
    Nat.mul_le_mul hq2 (by omega)
  nlinarith

end embeds

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.E6aTbl` -/

section
/-!
# WP E6a (6): the assembly interface and a worked union table E1 + E2 + E3 + E5 + E6a

**How the assembler references the table.**  `E6a.e6aTbl : ℕ → Option Tm` (ids `640 … 654`, all `≥ 128`).  Let `T` be the
assembled table (`layerΔ Lib.Δ 128 T` the assembled Δ).  If `E6a.e6aTbl ⊑ T` then `E6a.e6aΔ ⊑ layerΔ Lib.Δ 128 T`
(`ext_asm`) and every theorem of E6a (stated for an arbitrary `Δ'` with `hΔ : e6aΔ ⊑ Δ'`) applies to `Δ' := layerΔ Lib.Δ 128 T`.
Disjointness with another table is `e6aTbl_range` (`640 ≤ f < 655`).  The E6a functions call **only** the library
(no E1–E5 function), so no `Ext5/ExtJ/ExtIP`-style hypotheses are needed.

The worked example is `asm6Tbl = asm5Tbl ∪ e6aTbl` (`asm5Tbl` of `E5Inst` = E1 ∪ E2 ∪ E3 ∪ E5).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6a

theorem e6aTbl_range {f : ℕ} {b : Tm} (h : e6aTbl f = some b) : 640 ≤ f ∧ f < 655 := e6aTbl_lt h

/-- **assembly**: `e6aTbl ⊑ T` implies `e6aΔ ⊑ layerΔ Lib.Δ 128 T` -/
theorem ext_asm (T : ℕ → Option Tm) (h : e6aTbl ⊑ T) : e6aΔ ⊑ layerΔ Lib.Δ 128 T := Ext.layer_mono h

/-- the union of the E1 + E2 + E3 + E5 table and the E6a table -/
def asm6Tbl : ℕ → Option Tm := orElseΔ E5Inst.asm5Tbl e6aTbl

def asm6Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm6Tbl

open Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees ToVal

end E6a
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Defs` -/

section
set_option linter.unusedSectionVars false

/-!
# WP A1 (1): the top-level table `a1Tbl` (ids `768 … 799`) and the final union table

| id | function | arguments |
|---|---|---|
| 768 `fImproveC` | `improveC (adjOfWord x) k nt` (an `Option NT`) | `[x, k, nt]` |
| 769 `fLoop` | `loopC (adjOfWord x) k j m t` for `j + m = n` (the round loop; `m = n - j` is decided by `j = n`) | `[x, k, n, j, t]` |
| 770 `fMain` | `outWord x` | `[x]` |

`finalTbl = (E1–E6b) ∪ e6aTbl ∪ a1Tbl`, `finalΔ = layerΔ Lib.Δ 128 finalTbl`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open Lib1

abbrev fImproveC : ℕ := 768
abbrev fLoop : ℕ := 769
abbrev fMain : ℕ := 770

/-- `improveC`: `extractFirst`, then `niceOf ∘ compress` on the extracted tree; environment `[x, k, nt]`. -/
def improveCTm : Tm :=
  .letE (.call E6b.fExtractFirst [V 0, V 1, V 2])
    (.ite (.isNat (V 0)) (.lit 0)
      (.cons (.lit 1) (.call E6a.fNiceOf [.call E6a.fCompress [.snd (V 0)]])))

/-- the round loop; environment `[x, k, n, j, t]`; stops when `j = n`. -/
def loopTm : Tm :=
  .ite (.eq (V 3) (V 2)) (.cons (.lit 1) (V 4))
    (.letE (.call E6a.fAddEv [V 3, V 4])
      (.letE (.call fImproveC [V 1, V 2, V 0])
        (.ite (.isNat (V 0)) (.lit 0)
          (.call fLoop [V 2, V 3, V 4, .add (V 5) (.lit 1), .snd (V 0)]))))

/-- the entry: read `n`, `k` off the word, run the rounds from the empty tree, print. -/
def mainTm : Tm :=
  .letE (.call fNth [V 0, .lit 0])
    (.letE (.call fNth [V 1, .add (.mul (V 0) (V 0)) (.lit 1)])
      (.letE (.call fLoop [V 2, V 0, V 1, .lit 0, .lit 0])
        (.ite (.isNat (V 0)) (.cons (.lit 0) (.lit 0))
          (.cons (.lit 1) (.call E6a.fEncode [.snd (V 0)])))))

/-- the table of WP A1 -/
def a1Tbl : ℕ → Option Tm := fun f =>
  match f with
  | 768 => some improveCTm | 769 => some loopTm | 770 => some mainTm
  | _ => none

theorem a1Tbl_lt {f : ℕ} {b : Tm} (h : a1Tbl f = some b) : 768 ≤ f ∧ f < 800 := by
  unfold a1Tbl at h
  split at h <;> first | (simp at h; done) | omega

def a1Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 a1Tbl

theorem Δ_improveC : a1Δ fImproveC = some improveCTm := by
  simp [a1Δ, layerΔ_ge a1Tbl (show 128 ≤ fImproveC by decide)]; rfl
theorem Δ_loop : a1Δ fLoop = some loopTm := by
  simp [a1Δ, layerΔ_ge a1Tbl (show 128 ≤ fLoop by decide)]; rfl
theorem Δ_main : a1Δ fMain = some mainTm := by
  simp [a1Δ, layerΔ_ge a1Tbl (show 128 ≤ fMain by decide)]; rfl

/-! ## the union table -/

theorem asm6Tbl_lt {f : ℕ} {b : Tm} (h : E6b.asm6Tbl f = some b) : f < 768 := by
  unfold E6b.asm6Tbl orElseΔ at h
  rcases h2 : E4.asm4Tbl f with _ | c
  · rcases h3 : E5Tbl.e5Tbl f with _ | c'
    · rcases h4 : E6b.e6bTbl f with _ | c''
      · simp [h2, h3, h4] at h
      · exact (E6b.e6bTbl_lt h4).2
    · have := E5Tbl.e5Tbl_lt h3; omega
  · have := E6b.asm4Tbl_lt h2; omega

theorem e6aTbl_disj_asm6 : ∀ f b, E6a.e6aTbl f = some b → E6b.asm6Tbl f = none := by
  intro f b h
  have h1 := (E6a.e6aTbl_range h)
  unfold E6b.asm6Tbl orElseΔ
  rcases h2 : E4.asm4Tbl f with _ | c
  · rcases h3 : E5Tbl.e5Tbl f with _ | c'
    · rcases h4 : E6b.e6bTbl f with _ | c''
      · simp
      · have := (E6b.e6bTbl_lt h4).1; omega
    · have := E5Tbl.e5Tbl_lt h3; omega
  · have := E6b.asm4Tbl_lt h2; omega

/-- `(E1–E6b) ∪ e6aTbl` -/
def finalTbl0 : ℕ → Option Tm := orElseΔ E6b.asm6Tbl E6a.e6aTbl

theorem finalTbl0_lt {f : ℕ} {b : Tm} (h : finalTbl0 f = some b) : f < 768 := by
  unfold finalTbl0 orElseΔ at h
  rcases h1 : E6b.asm6Tbl f with _ | c
  · rw [h1] at h
    have := (E6a.e6aTbl_range (by simpa using h)).2; omega
  · exact asm6Tbl_lt h1

theorem a1Tbl_disj : ∀ f b, a1Tbl f = some b → finalTbl0 f = none := by
  intro f b h
  have h1 := (a1Tbl_lt h).1
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have := finalTbl0_lt hc
  omega

/-- **the final table** -/
def finalTbl : ℕ → Option Tm := orElseΔ finalTbl0 a1Tbl

/-- **the final function table** -/
def finalΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 finalTbl

theorem finalTbl_lt {f : ℕ} {b : Tm} (h : finalTbl f = some b) : f < 800 := by
  unfold finalTbl orElseΔ at h
  rcases h1 : finalTbl0 f with _ | c
  · rw [h1] at h
    have := (a1Tbl_lt (by simpa using h)).2; omega
  · have := finalTbl0_lt h1; omega

/-- **the table is finite**: every id `≥ 800` is undefined -/
theorem finalΔ_none {f : ℕ} (hf : 800 ≤ f) : finalΔ f = none := by
  unfold finalΔ
  rw [layerΔ_ge finalTbl (show 128 ≤ f by omega)]
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have := finalTbl_lt hc
  omega

theorem asm6_le_final : E6b.asm6Tbl ⊑ finalTbl :=
  Ext.trans (Ext.orElse_left _ _) (Ext.orElse_left _ _)

theorem e6a_le_final : E6a.e6aTbl ⊑ finalTbl :=
  Ext.trans (Ext.orElse_right e6aTbl_disj_asm6) (Ext.orElse_left _ _)

theorem a1_le_final : a1Tbl ⊑ finalTbl := Ext.orElse_right a1Tbl_disj

/-- the hypotheses of every E6b theorem hold in the final table -/
theorem ext6_final : E6b.Ext6 finalΔ :=
  E6b.Ext6.of_tbl
    (Ext.trans (Ext.trans (Ext.orElse_left _ _) (Ext.trans (Ext.orElse_left _ _) (Ext.orElse_left _ _)))
      asm6_le_final)
    (Ext.trans (Ext.trans (Ext.orElse_right E4.e4Tbl_disj_asm)
      (Ext.trans (Ext.orElse_left _ _) (Ext.orElse_left _ _))) asm6_le_final)
    (Ext.trans (Ext.trans (Ext.orElse_right E6b.e5Tbl_disj_asm4) (Ext.orElse_left _ _)) asm6_le_final)
    (Ext.trans (Ext.orElse_right E6b.e6bTbl_disj) asm6_le_final)

theorem ext6a_final : E6a.e6aΔ ⊑ finalΔ := E6a.ext_asm _ e6a_le_final

theorem ext_a1_final : a1Δ ⊑ finalΔ := Ext.layer_mono a1_le_final

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Imp` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (2): `improveC` as an F-function

`improveC adj k nt = (extractFirst adj k nt).map (niceOf ∘ compress)` and the run of `fImproveC` on the input
`(x, k, nt)`; cost `cIC M k` for every `M ≥ |x|, sz nt, mx nt`.

Preconditions: `ExtOk x k nt` (Good, width `k + 1`, `adjOfWord x` symmetric on a set containing the vertices of `nt`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord ntOk)

theorem improveC_eq_map (adj : Adj) (k : ℕ) (nt : NT) :
    improveC adj k nt = (E6b.extractFirst adj k nt).map (fun t => niceOf (compress t)) := by
  unfold improveC E6b.extractFirst
  cases tables adj k nt <;> simp

/-- the size bound of the extracted tree in terms of the nice tree -/
def sBnd (k M : ℕ) : ℕ := (2 * k + 8) * (2 * k + 6) * M

/-- the cost of `improveC` -/
def cIC (M k : ℕ) : ℕ :=
  (M * E4.cnode M k + M ^ 2 * E6b.Wx M k + 30) + 400 * (2 * sBnd k M + 1) ^ 3 + 8000 * (sBnd k M + 2) ^ 5 + 40

/-- facts about the extracted tree -/
theorem extractFirst_facts {x : List ℕ} {k : ℕ} {nt : NT} (hok : E6b.ExtOk x k nt) {t' : RT}
    (h : E6b.extractFirst (adjOfWord x) k nt = some t') :
    t'.IsTD (adjOfWord x).graph nt.under ∧ t'.Width k ∧ sz t' ≤ (2 * k + 8) * (2 * k + 6) * nt.size := by
  obtain ⟨⟨hg, hw⟩, W, hs, hW⟩ := hok
  unfold E6b.extractFirst at h
  rcases hcase : tables (adjOfWord x) k nt with _ | ⟨c, T'⟩
  · rw [hcase] at h; simp at h
  · rw [hcase] at h
    have hc : c ∈ tables (adjOfWord x) k nt := by rw [hcase]; simp
    obtain ⟨t, ht, hp, -⟩ := extract_spec (k := k) hs hg hW c hc
    simp only at h
    rw [ht] at h
    cases h
    exact ⟨hp.1, hp.2, extract_sz_le hs hg hW hw c hc t' ht⟩

theorem mx_rt_le_of_isTD {t : RT} {U : Finset ℕ} {G : SimpleGraph ℕ} (h : t.IsTD G U) {M : ℕ}
    (hM : ∀ v ∈ U, v ≤ M) : mx t ≤ M :=
  (mx_rt_le_iff t).2 fun v hv => hM v (h.verts_eq ▸ hv)

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

theorem improveC_runs (B : ℕ) (x : List ℕ) (k : ℕ) (nt : NT) (M Mv : ℕ) (hxM : x.length ≤ M)
    (hsM : sz nt ≤ M) (hmM : mx nt ≤ M) (hmv : mx nt ≤ Mv) (hok : E6b.ExtOk x k nt)
    (hn : (nOfWord x) ^ 2 < B) (hk : k + 2 < B) (hB : (Mv + cIC M k + 2) ^ 2 < B) :
    Runs Δ' B fImproveC [toVal x, toVal k, toVal nt] (toVal (improveC (adjOfWord x) k nt)) (cIC M k) := by
  have hsize : nt.size ≤ M := E4.size_le_M hsM
  have hcn : nt.size * E4.cnode M k ≤ M * E4.cnode M k := Nat.mul_le_mul_right _ hsize
  have hwx : nt.size ^ 2 * E6b.Wx M k ≤ M ^ 2 * E6b.Wx M k :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hsize 2)
  have hB1 : (nt.size * E4.cnode M k + nt.size ^ 2 * E6b.Wx M k + 30 + 2) ^ 2 < B := by
    refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
    unfold cIC; omega
  have hT := E6b.extractFirst_runs hΔ B x k nt M hxM hsM hmM hok hn hk hB1
  rw [improveC_eq_map]
  rcases hcase : E6b.extractFirst (adjOfWord x) k nt with _ | t'
  · rw [hcase] at hT
    simp only [Option.map_none, toVal_none] at hT ⊢
    refine Runs.mk (h1 _ _ Δ_improveC) ?_
    ev_start
    · ev_run
    · unfold cIC; omega
  · obtain ⟨htd, hw, hsz⟩ := extractFirst_facts hok hcase
    rw [hcase] at hT
    simp only [Option.map_some, toVal_some] at hT ⊢
    have hunder : ∀ v ∈ nt.under, v ≤ Mv := fun v hv => le_trans (under_le_mx_nt nt hv) hmv
    have hctd := compress_isTD htd
    have hmt' : mx t' ≤ Mv := mx_rt_le_of_isTD htd hunder
    have hmc : mx (compress t') ≤ Mv := mx_rt_le_of_isTD hctd hunder
    have hszc := E6a.sz_compress_le t'
    have hS : sz t' ≤ sBnd k M := by
      unfold sBnd; exact le_trans hsz (Nat.mul_le_mul_left _ hsize)
    have hc2 : 400 * (sz t' + sz (compress t') + 1) ^ 3 ≤ 400 * (2 * sBnd k M + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have hc3 : 8000 * (sz (compress t') + 2) ^ 5 ≤ 8000 * (sBnd k M + 2) ^ 5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)
    have hf2 : Fits B (toVal t') (400 * (sz t' + sz (compress t') + 1) ^ 3) := by
      unfold Fits
      refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
      show mx t' + _ + 2 ≤ _
      unfold cIC; omega
    have hf3 : Fits B (toVal (compress t')) (8000 * (sz (compress t') + 2) ^ 5) := by
      unfold Fits
      refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) hB
      show mx (compress t') + _ + 2 ≤ _
      unfold cIC; omega
    have hcomp := E6a.embeds_compress h6a B t' trivial hf2
    have hnice := E6a.embeds_niceOf_conn h6a B (compress t') hctd.conn hf3
    beta_reduce at hcomp hnice
    refine Runs.mk (h1 _ _ Δ_improveC) ?_
    ev_start
    · ev_run
    · unfold cIC; omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Loop` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (3): the round loop

`loopC adj k j m t` runs the `m` rounds `j, j+1, …, j+m-1` from the nice tree `t` (of `range j`);
`decomposeC adj k (j + m) = loopC adj k j m t` when `decomposeC adj k j = some t`.

`loop_runs`: for `j + m = n` the F-function `fLoop` evaluates `[x, k, n, j, t]` to `loopC …`
within `m · cRound M k + 10` steps.  The per-round preconditions come from the math layer:
* `addEverywhere_isNiceTD` (round `j`: `range j ↦ range (j+1)`, width `k ↦ k+1`, needs `j ∉ range j`);
* `good_of_isNiceTD`, `IsNiceTD.2.2` (Width) ⇒ `ntOk`; `symmOn` on `range n` and `under = range (j+1) ⊆ range n` ⇒ `ExtOk`;
* `size_addEverywhere_le`, `sz_nt_le_size`, the invariant `size ≤ (j+2)²` (`improveC_correct`) ⇒ `sz a ≤ M`;
* `mx_nt_le_of_wf` (`Wf` from `IsNiceTD`, vertices `< n`) ⇒ `mx a ≤ n + 3`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT CT
open E4 (adjOfWord nOfWord ntOk)

/-! ## the math side -/

/-- `m` rounds starting at round `j` -/
def loopC (adj : Adj) (k : ℕ) : ℕ → ℕ → NT → Option NT
  | _, 0, t => some t
  | j, m + 1, t => (improveC adj k (NT.addEverywhere j t)).bind (fun t' => loopC adj k (j + 1) m t')

theorem decomposeC_none_add (adj : Adj) (k : ℕ) :
    ∀ m i, decomposeC adj k i = none → decomposeC adj k (i + m) = none := by
  intro m
  induction m with
  | zero => intro i h; simpa using h
  | succ m ih =>
    intro i h
    have := ih i h
    show decomposeC adj k (i + m + 1) = none
    simp [decomposeC, this]

theorem decomposeC_loop (adj : Adj) (k : ℕ) :
    ∀ m j t, decomposeC adj k j = some t → decomposeC adj k (j + m) = loopC adj k j m t := by
  intro m
  induction m with
  | zero => intro j t h; simpa [loopC] using h
  | succ m ih =>
    intro j t h
    have e : j + (m + 1) = (j + 1) + m := by omega
    rw [e]
    have hs : decomposeC adj k (j + 1) = improveC adj k (NT.addEverywhere j t) := by
      simp [decomposeC, h]
    have hl : loopC adj k j (m + 1) t = (improveC adj k (NT.addEverywhere j t)).bind
        (fun t' => loopC adj k (j + 1) m t') := rfl
    rw [hl]
    rcases hi : improveC adj k (NT.addEverywhere j t) with _ | t'
    · rw [hi] at hs
      simp [decomposeC_none_add adj k m (j + 1) hs]
    · rw [hi] at hs
      simpa using ih (j + 1) t' hs

/-- the invariant at the start of round `j` -/
def LoopInv (adj : Adj) (k j : ℕ) (t : NT) : Prop :=
  t.IsNiceTD adj.graph (Finset.range j) k ∧ t.size ≤ (j + 2) * (j + 2)

theorem loopInv_zero (adj : Adj) (k : ℕ) : LoopInv adj k 0 NT.leaf := by
  refine ⟨⟨trivial, ⟨rfl, fun u v _ hu _ => absurd hu (by simp), by simp [NT.toRT, RT.Conn, RT.ConnL]⟩,
      by intro X hX; simp [NT.toRT, RT.bags, RT.bagsL] at hX; simp [hX]⟩, by simp [NT.size]⟩

/-- after `addEverywhere j` -/
theorem round_add {adj : Adj} {k j : ℕ} {t : NT} (h : LoopInv adj k j t) :
    (NT.addEverywhere j t).IsNiceTD adj.graph (Finset.range (j + 1)) (k + 1) := by
  have := addEverywhere_isNiceTD (v := j) h.1 (by simp)
  rwa [← Finset.range_add_one] at this

/-- the step of the invariant -/
theorem round_next {adj : Adj} {W : Finset ℕ} (hs : adj.SymmOn W) {k j n : ℕ} {t : NT}
    (hj : j + 1 ≤ n) (hW : Finset.range n ⊆ W) (h : LoopInv adj k j t) {t' : NT}
    (ht' : improveC adj k (NT.addEverywhere j t) = some t') : LoopInv adj k (j + 1) t' := by
  have hadd := round_add h
  have hU : Finset.range (j + 1) ⊆ W := (Finset.range_subset_range.2 hj).trans hW
  obtain ⟨-, j2⟩ := improveC_correct hs hU hadd k
  obtain ⟨a, b⟩ := j2 t' ht'
  refine ⟨a, ?_⟩
  simpa [Finset.card_range] using b

/-- the round-`j` input tree `a = addEverywhere j t` -/
theorem round_facts {adj : Adj} {k j n : ℕ} {t : NT} (hj : j + 1 ≤ n) (h : LoopInv adj k j t) :
    (NT.addEverywhere j t).Good adj ∧ (NT.addEverywhere j t).toRT.Width (k + 1) ∧
    (NT.addEverywhere j t).under = Finset.range (j + 1) ∧
    (NT.addEverywhere j t).Wf ∧ (NT.addEverywhere j t).size ≤ 2 * ((n + 1) * (n + 1)) := by
  have hadd := round_add h
  refine ⟨good_of_isNiceTD hadd, hadd.2.2, ?_, hadd.1, ?_⟩
  · rw [NT.under_eq_vs]; exact hadd.2.1.verts_eq
  · have h1 := size_addEverywhere_le j t
    have h2 := h.2
    have h3 : (j + 2) * (j + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-! ## the run -/

/-- the per-round cost -/
def cRound (M k : ℕ) : ℕ := 30 * M + cIC M k + 30

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

/-- **the round loop**: for `j + m = n`, from a nice tree of `range j` -/
theorem loop_runs (B : ℕ) (x : List ℕ) (k n M Mv Ctot : ℕ) (hnx : n = nOfWord x)
    (hs : (adjOfWord x).SymmOn (Finset.range n)) (hxM : x.length ≤ M) (hMs : 8 * ((n + 1) * (n + 1)) ≤ M)
    (hnM : n + 3 ≤ M) (hnMv : n + 3 ≤ Mv) (hk : k + 2 < B) (hCt : n * cRound M k + 10 ≤ Ctot)
    (hB : (Mv + Ctot + 2) ^ 2 < B) :
    ∀ m j (t : NT), j + m = n → LoopInv (adjOfWord x) k j t →
      Runs Δ' B fLoop [toVal x, toVal k, toVal n, toVal j, toVal t] (toVal (loopC (adjOfWord x) k j m t))
        (m * cRound M k + 10) := by
  have hnB : n + 3 < B := by
    have : n + 3 ≤ (Mv + Ctot + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Ctot + 2)]
    omega
  intro m
  induction m with
  | zero =>
    intro j t hjm hinv
    have hj : j = n := by omega
    subst hj
    simp only [loopC, toVal_some]
    refine Runs.mk (h1 _ _ Δ_loop) ?_
    ev_start
    · ev_run
    · omega
  | succ m ih =>
    intro j t hjm hinv
    have hjn : j + 1 ≤ n := by omega
    have hne : j ≠ n := by omega
    simp only [loopC]
    obtain ⟨hg, hw, hund, hwf, hsz⟩ := round_facts hjn hinv
    set a := NT.addEverywhere j t with ha
    have hszM : sz a ≤ M := by
      have := sz_nt_le_size a
      omega
    have hmxa : mx a ≤ n + 3 := by
      refine mx_nt_le_of_wf hwf (by omega) fun v hv => ?_
      rw [hund] at hv
      have := Finset.mem_range.1 hv
      omega
    have hok : E6b.ExtOk x k a :=
      ⟨⟨hg, hw⟩, Finset.range n, hs, by rw [hund]; exact Finset.range_subset_range.2 hjn⟩
    have hcR : cRound M k ≤ n * cRound M k := by
      have : 1 ≤ n := by omega
      nlinarith [Nat.zero_le (cRound M k)]
    have hnx2 : (nOfWord x) ^ 2 < B := by
      rw [← hnx]
      have : n ^ 2 ≤ (Mv + Ctot + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hIC : cIC M k ≤ Ctot := by
      have : cIC M k ≤ cRound M k := by unfold cRound; omega
      omega
    have hBi : (Mv + cIC M k + 2) ^ 2 < B :=
      lt_of_le_of_lt (Nat.pow_le_pow_left (by omega) 2) hB
    have hImp := improveC_runs hΔ h6a h1 B x k a M Mv hxM hszM (by omega) (by omega) hok hnx2 hk hBi
    have hAdd := E6a.addEv_runs h6a B j (by omega) t
    have hAdd' : Runs Δ' B E6a.fAddEv [toVal j, toVal t] (toVal a) (30 * t.size) := hAdd
    have htM : t.size ≤ M := by
      have := hinv.2
      have h3 : (j + 2) * (j + 2) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      have : (n + 1) * (n + 1) ≤ M := by omega
      omega
    rcases hi : improveC (adjOfWord x) k a with _ | t'
    · rw [hi] at hImp
      simp only [Option.bind_none, toVal_none] at hImp ⊢
      refine Runs.mk (h1 _ _ Δ_loop) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hne]
      · have : (m + 1) * cRound M k = m * cRound M k + cRound M k := by ring
        unfold cRound at this ⊢
        omega
    · have hinv' : LoopInv (adjOfWord x) k (j + 1) t' :=
        round_next hs hjn (le_refl _) hinv hi
      have hrec := ih (j + 1) t' (by omega) hinv'
      rw [hi] at hImp
      simp only [Option.bind_some, toVal_some] at hImp ⊢
      refine Runs.mk (h1 _ _ Δ_loop) ?_
      ev_start
      · ev_run
        all_goals first | omega | simp [hne]
      · have : (m + 1) * cRound M k = m * cRound M k + cRound M k := by ring
        unfold cRound at this ⊢
        omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A2Stmt` -/

section
/-!
# The shared statement between the assembly A1 and the concept statements A2/A3

`DecompRun` is what the top-level functional program must deliver (A1 proves it); the two concept statements
`niceDecomposition_computable` and `improveDecomposition` are derived from it through the compiler
(`Load.compile_computes`) by A2 and A3 without looking at the program.
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The output word of the exact algorithm on the input word `g ++ [k]` (P0's `decomposeC` with the
adjacency read off the word). -/
def outWord (x : List ℕ) : List ℕ :=
  match Lax117284Proofs.Treewidth.Chars.decomposeC (E4.adjOfWord x) (Fmt.graphK.kw x) (x.getD 0 0) with
  | none => [0]
  | some t => 1 :: t.encode

/-- The admissible inputs: the word of a graph followed by `k`. -/
def D2 : Set (List ℕ) :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ) (k : ℕ), x = g ++ [k] ∧ EncodesGraph g G}

/-- The cost parameters of the top-level run: `K x = C · 2^(C·k³) · (|x|+1)^C`. -/
def pC (C : ℕ) : KP := ⟨C, C, 1, C⟩

/-- **What A1 proves.**  One function table `Δ` (finite: ids `< N`), one entry `main` and one constant `C` such that on every
admissible input the entry evaluates `[toVal x]` to `toVal (outWord x)` within `K x` steps at the tag bound `Bx`,
and the output is no longer than `K x`. -/
def DecompRun : Prop :=
  ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
    ∀ x ∈ D2, Runs Δ (Bx (pC C) Fmt.graphK x) main [toVal x] (toVal (outWord x)) (Kx (pC C) Fmt.graphK x) ∧
      (outWord x).length ≤ Kx (pC C) Fmt.graphK x

end Lax117284Proofs.Treewidth.Fun.A2

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Main` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (4): the entry `fMain`

`fMain [x] = outWord x` : read `n = x[0]`, `k = x[n²+1]`, run the `n` rounds from the empty tree, print `1 :: encode t` or `[0]`.
The correctness of the output (`outWord`) is *by definition* the value of `decomposeC` (the math layer proves that this
is a nice decomposition); this file only proves that the machine computes that value.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT CT
open E4 (adjOfWord nOfWord ntOk)

theorem flat3_length : ∀ l : List (ℕ × ℕ × ℕ), (l.flatMap (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2])).length
    = 3 * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp; ring

theorem encode_length (t : NT) : (NT.encode t).length = 3 * t.size + 1 := by
  unfold NT.encode
  simp only [List.length_cons, flat3_length, E6a.recs_length]

/-- the cost of the whole run -/
def cMain (n xlen M k : ℕ) : ℕ := 28 * xlen + n * cRound M k + 200 * ((n + 2) * (n + 2)) ^ 2 + 2000

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

theorem main_runs (B : ℕ) (x : List ℕ) (k M Mv Cm : ℕ) (hkx : k = Load.Fmt.graphK.kw x)
    (hs : (adjOfWord x).SymmOn (Finset.range (nOfWord x))) (hxM : x.length ≤ M)
    (hMs : 8 * ((nOfWord x + 1) * (nOfWord x + 1)) ≤ M) (hnM : nOfWord x + 3 ≤ M) (hnMv : nOfWord x + 3 ≤ Mv)
    (hkB : k + 2 < B) (hnn : nOfWord x * nOfWord x + 1 < B)
    (hCm : cMain (nOfWord x) x.length M k ≤ Cm) (hB : (Mv + Cm + 2) ^ 2 < B) :
    Runs Δ' B fMain [toVal x] (toVal (A2.outWord x)) Cm := by
  set n := nOfWord x with hn
  have hkeq : k = x.getD (n * n + 1) 0 := by
    rw [hkx]; simp [Load.Fmt.kw, Load.Fmt.off, hn, nOfWord]
  have hCm' := hCm
  unfold cMain at hCm'
  have hB1 : 1 < B := by
    have : 2 ≤ (Mv + Cm + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Cm + 2)]
    omega
  have hn0 : Runs Δ' B Lib1.fNth [toVal x, toVal 0] (toVal n) (14 * x.length + 9) :=
    E4.nth0_runs hΔ.e4 B x 0 hB1
  have hn1 : Runs Δ' B Lib1.fNth [toVal x, toVal (n * n + 1)] (toVal k) (14 * x.length + 9) := by
    rw [hkeq]; exact E4.nth0_runs hΔ.e4 B x (n * n + 1) hB1
  have hd := decomposeC_loop (adjOfWord x) k n 0 NT.leaf rfl
  simp only [Nat.zero_add] at hd
  have hloop := loop_runs hΔ h6a h1 B x k n M Mv Cm rfl hs hxM hMs hnM hnMv hkB
    (by omega) hB n 0 NT.leaf (by omega) (loopInv_zero (adjOfWord x) k)
  have hout : A2.outWord x = match loopC (adjOfWord x) k 0 n NT.leaf with
      | none => [0] | some t => 1 :: t.encode := by
    unfold A2.outWord
    rw [← hkx]
    have e : x.getD 0 0 = n := rfl
    rw [e, hd]
    try rfl
  rw [hout]
  have hnt0 : toVal (x.getD 0 0) = Val.nat n := rfl
  rcases hr : loopC (adjOfWord x) k 0 n NT.leaf with _ | t
  · rw [hr] at hloop
    simp only [toVal_none, toVal_cons, toVal_nat] at hloop ⊢
    refine Runs.mk (h1 _ _ Δ_main) ?_
    ev_start
    · ev_run
      all_goals first | omega | simp
    · omega
  · rw [hr] at hloop
    have hcor := (decomposeC_correct_final (adjOfWord x) (Finset.range n) hs k n (Finset.Subset.refl _)).2 t
      (by rw [hd, hr])
    have hsize : t.size ≤ (n + 2) * (n + 2) := hcor.2
    have hE : 200 * t.size ^ 2 ≤ 200 * ((n + 2) * (n + 2)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
    have hpos := E6a.NT.size_pos_aux t
    have hBe : 8 * t.size + 1000 < B := by
      have : 8 * t.size + 1000 ≤ Cm := by
        have : t.size ≤ t.size ^ 2 := by nlinarith
        omega
      have : Cm ≤ (Mv + Cm + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Cm + 2)]
      omega
    have hEnc := E6a.encode_runs h6a B t hBe
    simp only [toVal_some, toVal_cons, toVal_nat] at hloop ⊢
    refine Runs.mk (h1 _ _ Δ_main) ?_
    ev_start
    · ev_run
      all_goals first | omega | simp
    · omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Arith` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (5): the arithmetic of the total cost

All constants are treated symbolically: `C = 2^E` with `E` an arbitrary natural `≥ 829723`; nothing is ever evaluated.

* `cIC_le`    : `cIC M k ≤ 2^33 · (M+2)^62 · 2^(103680 (k+2)^3)`;
* `cMain_le`  : for `M = 8 (|x|+1)²`, `|x| = n² + 2`: `cMain n |x| M k + 3 ≤ K x` with `K x = C · 2^(C k³) · (|x|+1)^C`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

/-- `2^(a e) ≤ 2^(b e)` for `a ≤ b` -/
theorem pw_mono (a b e : ℕ) (h : a ≤ b) : 2 ^ (a * e) ≤ 2 ^ (b * e) :=
  Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)

theorem cIC_le (M k : ℕ) : cIC M k ≤ 2 ^ 33 * ((M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  have hcn : E4.cnode M k = (M + 1) ^ 15 * 2 ^ (4000 * (k + 2) ^ 3) := rfl
  have hwx := E6b.cost_closed M k M
  have he8 := E4.Y_ge k
  obtain ⟨e, he⟩ : ∃ e, e = (k + 2) ^ 3 := ⟨_, rfl⟩
  rw [← he] at hcn hwx he8 ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = M + 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ (103680 * e) := ⟨_, rfl⟩
  rw [← hP, ← hZ]
  have hP2 : 2 ≤ P := by omega
  have hP1 : 1 ≤ P := by omega
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_two_pow
  have hMP : M + 1 ≤ P := by omega
  have hMP' : M ≤ P := by omega
  -- Y = 2^e and its powers
  have hYe : e < 2 ^ e := Nat.lt_two_pow_self
  have hk2 : (k + 2) ^ 2 ≤ e := by
    rw [he]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hY1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hY3 : (2 ^ e) ^ 3 ≤ Z := by
    rw [hZ, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hY5 : (2 ^ e) ^ 5 ≤ Z := by
    rw [hZ, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4000 : 2 ^ (4000 * e) ≤ Z := by rw [hZ]; exact pw_mono 4000 103680 e (by norm_num)
  -- the size bound S
  have hS : sBnd k M ≤ 12 * (2 ^ e * P) := by
    unfold sBnd
    have h1 : (2 * k + 8) * (2 * k + 6) ≤ 12 * (k + 2) ^ 2 := by nlinarith [Nat.zero_le k]
    calc (2 * k + 8) * (2 * k + 6) * M ≤ (12 * (k + 2) ^ 2) * P := Nat.mul_le_mul h1 hMP'
      _ ≤ (12 * 2 ^ e) * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
      _ = 12 * (2 ^ e * P) := by ring
  have hYP : 1 ≤ 2 ^ e * P := Nat.mul_le_mul hY1 hP1
  have hS1 : 2 * sBnd k M + 1 ≤ 25 * (2 ^ e * P) := by omega
  have hS2 : sBnd k M + 2 ≤ 14 * (2 ^ e * P) := by omega
  have hP62 : ∀ j, j ≤ 62 → P ^ j ≤ P ^ 62 := fun j hj => Nat.pow_le_pow_right hP1 hj
  -- T1
  have hT1 : M * E4.cnode M k ≤ P ^ 62 * Z := by
    rw [hcn]
    calc M * ((M + 1) ^ 15 * 2 ^ (4000 * e)) ≤ P * (P ^ 15 * Z) :=
          Nat.mul_le_mul hMP' (Nat.mul_le_mul (Nat.pow_le_pow_left hMP 15) h4000)
      _ = P ^ 16 * Z := by ring
      _ ≤ P ^ 62 * Z := Nat.mul_le_mul_right _ (hP62 16 (by norm_num))
  -- T2
  have hT2 : M ^ 2 * E6b.Wx M k ≤ P ^ 62 * Z := by
    rw [hwx, hZ]
    calc M ^ 2 * (M + 1) ^ 60 * 2 ^ (103680 * e) ≤ P ^ 2 * P ^ 60 * 2 ^ (103680 * e) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.pow_le_pow_left hMP' 2) (Nat.pow_le_pow_left hMP 60))
      _ = P ^ 62 * 2 ^ (103680 * e) := by rw [← pow_add]
  -- T4
  have hT4 : 400 * (2 * sBnd k M + 1) ^ 3 ≤ 6250000 * (P ^ 62 * Z) := by
    calc 400 * (2 * sBnd k M + 1) ^ 3 ≤ 400 * (25 * (2 ^ e * P)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS1 3)
      _ = 6250000 * (((2 ^ e) ^ 3) * P ^ 3) := by ring
      _ ≤ 6250000 * (Z * P ^ 62) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hY3 (hP62 3 (by norm_num)))
      _ = 6250000 * (P ^ 62 * Z) := by ring
  -- T6
  have hT6 : 8000 * (sBnd k M + 2) ^ 5 ≤ 4302592000 * (P ^ 62 * Z) := by
    calc 8000 * (sBnd k M + 2) ^ 5 ≤ 8000 * (14 * (2 ^ e * P)) ^ 5 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS2 5)
      _ = 4302592000 * (((2 ^ e) ^ 5) * P ^ 5) := by ring
      _ ≤ 4302592000 * (Z * P ^ 62) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hY5 (hP62 5 (by norm_num)))
      _ = 4302592000 * (P ^ 62 * Z) := by ring
  have hW : 1 ≤ P ^ 62 * Z := Nat.mul_le_mul (Nat.one_le_pow _ _ hP1) hZ1
  unfold cIC
  omega


theorem cRound_le (M k : ℕ) : cRound M k ≤ 2 ^ 34 * ((M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  have h := cIC_le M k
  have hP1 : 1 ≤ M + 2 := by omega
  have hZ1 : 1 ≤ 2 ^ (103680 * (k + 2) ^ 3) := Nat.one_le_two_pow
  have hP62 : M + 2 ≤ (M + 2) ^ 62 := Nat.le_self_pow (by norm_num) _
  have hW : (M + 2) ^ 62 ≤ (M + 2) ^ 62 * 2 ^ (103680 * (k + 2) ^ 3) := Nat.le_mul_of_pos_right _ hZ1
  unfold cRound
  omega

/-- the polynomial part: `n · R + …` in terms of `Q = |x| + 1` -/
theorem poly_part (n xlen k : ℕ) (hn : n ≤ xlen) :
    cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3 ≤
      2 ^ 283 * ((xlen + 1) ^ 125 * 2 ^ (103680 * (k + 2) ^ 3)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = xlen + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 2 ^ (103680 * (k + 2) ^ 3) := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact Nat.one_le_two_pow
  have hR := cRound_le (8 * (Q * Q)) k
  rw [← hZ] at hR
  have hM : 8 * ((xlen + 1) * (xlen + 1)) = 8 * (Q * Q) := by rw [hQ]
  rw [hM, ← hZ, ← hQ]
  have hQ1 : 1 ≤ Q := by omega
  have hP : 8 * (Q * Q) + 2 ≤ 16 * Q ^ 2 := by nlinarith
  have hP62 : (8 * (Q * Q) + 2) ^ 62 ≤ 2 ^ 248 * Q ^ 124 := by
    calc (8 * (Q * Q) + 2) ^ 62 ≤ (16 * Q ^ 2) ^ 62 := Nat.pow_le_pow_left hP 62
      _ = 2 ^ 248 * Q ^ 124 := by
          rw [mul_pow, ← pow_mul]
          have : (16 : ℕ) = 2 ^ 4 := by norm_num
          rw [this, ← pow_mul]
  have hR2 : cRound (8 * (Q * Q)) k ≤ 2 ^ 34 * ((2 ^ 248 * Q ^ 124) * Z) :=
    le_trans hR (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hP62))
  have hnQ : n ≤ Q := by omega
  have hnR : n * cRound (8 * (Q * Q)) k ≤ 2 ^ 282 * (Q ^ 125 * Z) := by
    calc n * cRound (8 * (Q * Q)) k ≤ Q * (2 ^ 34 * ((2 ^ 248 * Q ^ 124) * Z)) := Nat.mul_le_mul hnQ hR2
      _ = (2 ^ 34 * 2 ^ 248) * (Q ^ 125 * Z) := by
          generalize 2 ^ 34 = a; generalize 2 ^ 248 = b; ring
      _ = 2 ^ 282 * (Q ^ 125 * Z) := by rw [← pow_add]
  have hQ4 : Q ^ 4 ≤ Q ^ 125 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have hQ4' : Q ≤ Q ^ 4 := Nat.le_self_pow (by norm_num) _
  have hn2 : (n + 2) * (n + 2) ≤ 4 * (Q * Q) := by nlinarith
  have hsq : ((n + 2) * (n + 2)) ^ 2 ≤ 16 * Q ^ 4 := by
    calc ((n + 2) * (n + 2)) ^ 2 ≤ (4 * (Q * Q)) ^ 2 := Nat.pow_le_pow_left hn2 2
      _ = 16 * Q ^ 4 := by ring
  have hQZ : Q ^ 4 ≤ Q ^ 125 * Z := le_trans hQ4 (Nat.le_mul_of_pos_right _ hZ1)
  have hQZ' : Q ≤ Q ^ 125 * Z := le_trans hQ4' hQZ
  unfold cMain
  omega

/-- the exponent comparison `(k+2)³ ≤ 8 + 27 k³` -/
theorem cube_le (k : ℕ) : (k + 2) ^ 3 ≤ 8 + 27 * k ^ 3 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · have h1 : k + 2 ≤ 3 * k := by omega
    have h2 : (k + 2) ^ 3 ≤ (3 * k) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : (3 * k) ^ 3 = 27 * k ^ 3 := by ring
    omega

/-- **the total cost is within `K x`**: `C = 2^E`, `E ≥ 829723` -/
theorem cMain_le (E n xlen k : ℕ) (hE : 829723 ≤ E) (hn : n ≤ xlen) :
    cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3 ≤ 2 ^ E * 2 ^ (2 ^ E * k ^ 3) * (xlen + 1) ^ (2 ^ E) := by
  have h1 := poly_part n xlen k hn
  obtain ⟨C, hC⟩ : ∃ C, C = 2 ^ E := ⟨_, rfl⟩
  rw [← hC]
  have hC1 : 2799360 ≤ C := by
    rw [hC]
    calc 2799360 ≤ 2 ^ 22 := by norm_num
      _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hC2 : 125 ≤ C := by omega
  have hC3 : 2 ^ (283 + 829440) ≤ C := by
    rw [hC]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcube := cube_le k
  have hZ : 2 ^ (103680 * (k + 2) ^ 3) ≤ 2 ^ 829440 * 2 ^ (C * k ^ 3) := by
    rw [← pow_add]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 2799360 * k ^ 3 ≤ C * k ^ 3 := Nat.mul_le_mul_right _ hC1
    omega
  have hQ : (xlen + 1) ^ 125 ≤ (xlen + 1) ^ C := Nat.pow_le_pow_right (by omega) hC2
  calc cMain n xlen (8 * ((xlen + 1) * (xlen + 1))) k + 3
      ≤ 2 ^ 283 * ((xlen + 1) ^ 125 * 2 ^ (103680 * (k + 2) ^ 3)) := h1
    _ ≤ 2 ^ 283 * ((xlen + 1) ^ C * (2 ^ 829440 * 2 ^ (C * k ^ 3))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hZ)
    _ = (2 ^ 283 * 2 ^ 829440) * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := by
        generalize 2 ^ 283 = a; generalize 2 ^ 829440 = b
        generalize 2 ^ (C * k ^ 3) = c; generalize (xlen + 1) ^ C = d
        ring
    _ = 2 ^ (283 + 829440) * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := by rw [pow_add]
    _ ≤ C * (2 ^ (C * k ^ 3) * (xlen + 1) ^ C) := Nat.mul_le_mul_right _ hC3
    _ = C * 2 ^ (C * k ^ 3) * (xlen + 1) ^ C := by rw [mul_assoc]

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A1Final` -/

section
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (6): `decompose_run : A2.DecompRun`

The table `finalΔ` (ids `< 800`, `A1Defs`), the entry `fMain = 770` and `C = 2^E` (`E` an abstract natural `≥ 829723`).
For `x = g ++ [k]` with `g` the word of a graph on `Fin n`: `|x| = n² + 2`, `x[0] = n`, `x[n²+1] = k`, the adjacency read
off the word is the graph's (symmetric on `range n`), and `main_runs` (A1Main) with `M = 8 (|x|+1)²`, `Mv = maxEntry x + 3`
gives the run within `cMain`, which `cMain_le` (A1Arith) bounds by `K x - 3`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284.GraphWords
open Lax117284Proofs.Treewidth.Fun.Load (Fmt Kx Bx maxEntry)
open Lax117284Proofs.Treewidth.Fun.VM.Ram (KP)
open E4 (adjOfWord nOfWord)

/-! ## the admissible inputs -/

theorem d2_len {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    (g ++ [k]).length = n * n + 2 := by
  simp [h.length_eq]; ring

theorem d2_n {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    nOfWord (g ++ [k]) = n := by
  have h1 := h.head_eq
  have hl : 0 < g.length := by rw [h.length_eq]; omega
  unfold nOfWord
  rw [List.getD_append _ _ _ _ hl]
  exact h1

theorem d2_k {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    Fmt.graphK.kw (g ++ [k]) = k := by
  have hn := d2_n (k := k) h
  have h1 : (g ++ [k]).getD 0 0 = n := hn
  unfold Fmt.kw Fmt.off
  rw [h1]
  simp only
  rw [List.getD_eq_getElem?_getD]
  have : (n * n + 1) = g.length := by rw [h.length_eq]; ring
  rw [this]
  simp

theorem d2_adj {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ} {k : ℕ} (h : EncodesGraph g G) :
    ∀ u v : Fin n, adjOfWord (g ++ [k]) u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u := by
  intro u v
  have hn := d2_n (k := k) h
  have hidx : 1 + u.val * n + v.val < g.length := by
    rw [h.length_eq]
    have hu := u.2
    have hv := v.2
    have : (u.val + 1) * n ≤ n * n := Nat.mul_le_mul_right _ hu
    nlinarith
  have hget : (g ++ [k]).getD (1 + u.val * n + v.val) 0 = g.getD (1 + u.val * n + v.val) 0 :=
    List.getD_append _ _ _ _ hidx
  have hadj := h.adj_eq u v
  unfold adjOfWord
  rw [hn, hget, hadj]
  by_cases hA : G.Adj u v
  · simp [hA, u.2, v.2]
  · have : G.Adj u v ↔ G.Adj v u := ⟨fun h => h.symm, fun h => h.symm⟩
    simp [hA, u.2, v.2]
    exact fun hh => hA (this.2 hh)

theorem le_maxEntry {x : List ℕ} {a : ℕ} (h : a ∈ x) : a ≤ maxEntry x :=
  (mx_foldr_max_le (y := x) (M := maxEntry x)).1 le_rfl a h

/-! ## the theorem -/

theorem decompose_run_E (E : ℕ) (hE : 829723 ≤ E) :
    ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
      ∀ x ∈ A2.D2, Runs Δ (Bx (A2.pC C) Fmt.graphK x) main [toVal x] (toVal (A2.outWord x))
          (Kx (A2.pC C) Fmt.graphK x) ∧
        (A2.outWord x).length ≤ Kx (A2.pC C) Fmt.graphK x := by
  refine ⟨finalΔ, 800, fMain, 2 ^ E, Nat.one_le_two_pow, fun f hf => finalΔ_none hf, ?_⟩
  rintro x ⟨n, G, g, k, rfl, henc⟩
  have hxl := d2_len (k := k) henc
  have hnw := d2_n (k := k) henc
  have hkw := d2_k (k := k) henc
  have hadj := d2_adj (k := k) henc
  have hs : (adjOfWord (g ++ [k])).SymmOn (Finset.range (nOfWord (g ++ [k]))) := by
    rw [hnw]; exact symmOn_of_encodes hadj
  set x := g ++ [k] with hx
  have hnn : n ≤ x.length := by rw [hxl]; nlinarith
  -- the numbers
  have hK : Kx (A2.pC (2 ^ E)) Fmt.graphK x = 2 ^ E * 2 ^ (2 ^ E * k ^ 3) * (x.length + 1) ^ (2 ^ E) := by
    unfold Kx A2.pC KP.k
    rw [hkw]
  have hBx : Bx (A2.pC (2 ^ E)) Fmt.graphK x =
      (maxEntry x + Kx (A2.pC (2 ^ E)) Fmt.graphK x + 2) ^ 2 + 1 := rfl
  set K := Kx (A2.pC (2 ^ E)) Fmt.graphK x with hKdef
  set M := 8 * ((x.length + 1) * (x.length + 1)) with hM
  set Cm := cMain n x.length M k with hCm
  have hCmK : Cm + 3 ≤ K := by rw [hK]; exact cMain_le E n x.length k hE hnn
  have hCm28 : 28 * x.length ≤ Cm := by rw [hCm]; unfold cMain; omega
  have hmem_n : n ≤ maxEntry x := by
    have : n ∈ x := by
      have h0 : x.getD 0 0 = n := hnw
      have : 0 < x.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this] at h0
      simp only [Option.getD_some] at h0
      rw [← h0]; exact List.getElem_mem _
    exact le_maxEntry this
  have hmem_k : k ≤ maxEntry x := le_maxEntry (by simp [hx])
  have hxM : x.length ≤ M := by rw [hM]; nlinarith
  have hMs : 8 * ((nOfWord x + 1) * (nOfWord x + 1)) ≤ M := by
    rw [hnw, hM]
    have : (n + 1) * (n + 1) ≤ (x.length + 1) * (x.length + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hnM : nOfWord x + 3 ≤ M := by
    rw [hnw, hM]; nlinarith
  have hkB : k + 2 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : maxEntry x + K + 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hnnB : nOfWord x * nOfWord x + 1 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : maxEntry x + K + 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    rw [hnw]; nlinarith
  have hBfit : (maxEntry x + 3 + Cm + 2) ^ 2 < (maxEntry x + K + 2) ^ 2 + 1 := by
    have : (maxEntry x + 3 + Cm + 2) ^ 2 ≤ (maxEntry x + K + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hCm' : cMain (nOfWord x) x.length M k ≤ Cm := by rw [hnw]
  have hmain := main_runs ext6_final ext6a_final ext_a1_final ((maxEntry x + K + 2) ^ 2 + 1) x k M
    (maxEntry x + 3) Cm hkw.symm hs hxM hMs hnM (by rw [hnw]; omega) hkB hnnB hCm' hBfit
  refine ⟨?_, ?_⟩
  · rw [hBx]
    exact hmain.mono (by omega)
  · -- the length of the output
    unfold A2.outWord
    rw [hkw]
    have hd := (decomposeC_correct_final (adjOfWord x) (Finset.range n) (by rw [hnw] at hs; exact hs) k n
      (Finset.Subset.refl _)).2
    have hnx : x.getD 0 0 = n := hnw
    rw [hnx]
    have hsq : 200 * ((n + 2) * (n + 2)) ^ 2 + 2000 ≤ Cm := by rw [hCm]; unfold cMain; omega
    rcases hr : decomposeC (adjOfWord x) k n with _ | t
    · simp only [List.length_cons, List.length_nil]; omega
    · have hsize := (hd t hr).2
      simp only [List.length_cons, encode_length]
      have h1 : t.size * t.size ≤ (n + 2) * (n + 2) * ((n + 2) * (n + 2)) := Nat.mul_le_mul hsize hsize
      have h2 : ((n + 2) * (n + 2)) ^ 2 = (n + 2) * (n + 2) * ((n + 2) * (n + 2)) := by ring
      have h3 : t.size ≤ t.size * t.size := Nat.le_mul_self t.size
      omega

/-- **`decompose_run`**: the top-level functional program computes `outWord` within `K x` steps at the tag bound `Bx`. -/
theorem decompose_run : A2.DecompRun := by
  obtain ⟨E, hE⟩ : ∃ E, 829723 ≤ E := ⟨_, le_refl _⟩
  exact decompose_run_E E hE

end A1
end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A2Corr` -/

section
/-!
# WP A2 (1): correctness and arithmetic for `niceDecomposition_computable`

* `outWord_correct`  : the output word of the exact algorithm (`decomposeC`) on `g ++ [k]` is `[0]` when the graph has no tree
  decomposition of width `k` and `1 :: D` with `NiceDecomposition G k D` otherwise (`Wrap/ImproveC.decomposeC_words_final`);
* `kw_graphK`, `fmtLen_graphK` : the format facts about `x = g ++ [k]`;
* `guard_mono`, `time_arith` : the constant chase between the compiler's guard/time (`c₀`, `κ`) and the concept's (`c`).
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal

section format

variable {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ}

theorem head_getD (henc : EncodesGraph g G) (k : ℕ) : (g ++ [k]).getD 0 0 = n := by
  have h0 : 0 < g.length := by rw [henc.length_eq]; omega
  rw [List.getD_append _ _ _ _ h0]
  exact henc.head_eq

theorem getD_g (henc : EncodesGraph g G) (k i : ℕ) (hi : i < 1 + n * n) : (g ++ [k]).getD i 0 = g.getD i 0 := by
  apply List.getD_append
  rw [henc.length_eq]; exact hi

theorem kw_graphK (henc : EncodesGraph g G) (k : ℕ) : Fmt.graphK.kw (g ++ [k]) = k := by
  unfold Fmt.kw
  rw [head_getD henc k]
  have : (g ++ [k]).getD (n * n + Fmt.graphK.off) 0 = k := by
    show (g ++ [k]).getD (n * n + 1) 0 = k
    rw [List.getD_append_right _ _ _ _ (by rw [henc.length_eq]; omega)]
    rw [henc.length_eq]
    have : n * n + 1 - (1 + n * n) = 0 := by omega
    rw [this]; rfl
  exact this

theorem fmtLen_graphK (henc : EncodesGraph g G) (k : ℕ) : fmtLen Fmt.graphK (g ++ [k]) = (g ++ [k]).length := by
  show nOfWord (g ++ [k]) * nOfWord (g ++ [k]) + 2 = _
  have : nOfWord (g ++ [k]) = n := head_getD henc k
  rw [this, List.length_append, henc.length_eq]
  simp; omega

theorem mem_D2 (henc : EncodesGraph g G) (k : ℕ) : g ++ [k] ∈ D2 := ⟨n, G, g, k, rfl, henc⟩

open Classical in
theorem hadj_of_encodes (henc : EncodesGraph g G) (k : ℕ) :
    ∀ u v : Fin n, E4.adjOfWord (g ++ [k]) u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u := by
  intro u v
  have hu := u.isLt
  have hv := v.isLt
  have hlt : 1 + u.val * n + v.val < 1 + n * n := by
    have : u.val * n + v.val < n * n := by
      have h1 : u.val * n + n ≤ n * n := by nlinarith
      omega
    omega
  have hn : E4.nOfWord (g ++ [k]) = n := head_getD henc k
  have e := henc.adj_eq u v
  have e2 : (g ++ [k]).getD (1 + u.val * n + v.val) 0 = if G.Adj u v then 1 else 0 := by
    rw [getD_g henc k _ hlt]; exact e
  simp only [E4.adjOfWord, hn, decide_eq_true_eq]
  rw [e2]
  constructor
  · rintro ⟨-, -, h⟩
    by_cases hA : G.Adj u v
    · exact Or.inl hA
    · simp [hA] at h
  · rintro (h | h)
    · exact ⟨hu, hv, by simp [h]⟩
    · exact ⟨hu, hv, by simp [h.symm]⟩

/-- **Correctness of the output word.** -/
theorem outWord_correct (henc : EncodesGraph g G) (k : ℕ) :
    (outWord (g ++ [k]) = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k) ∨
      ∃ D, outWord (g ++ [k]) = 1 :: D ∧ NiceDecomposition G k D := by
  have hadj := hadj_of_encodes henc k
  obtain ⟨h1, h2⟩ := Lax117284Proofs.Treewidth.Chars.decomposeC_words_final G (E4.adjOfWord (g ++ [k])) hadj k
  unfold outWord
  rw [kw_graphK henc k, head_getD henc k]
  cases hd : Lax117284Proofs.Treewidth.Chars.decomposeC (E4.adjOfWord (g ++ [k])) k n with
  | none =>
    left
    exact ⟨rfl, h1.1 hd⟩
  | some t =>
    right
    exact ⟨t.encode, rfl, h2 t hd⟩

end format

section arith

/-- the compiler's guard follows from the concept's when `c₀ ≤ c`. -/
theorem guard_mono {c₀ c e Y W : ℕ} (hc : c₀ ≤ c) (hY : 1 ≤ Y)
    (h : c * 2 ^ (c * e ^ 3) * Y ^ c ≤ 2 ^ W) : c₀ * 2 ^ (c₀ * e ^ 3) * Y ^ c₀ ≤ 2 ^ W := by
  refine le_trans ?_ h
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc)))
    (Nat.pow_le_pow_right hY hc)

/-- the compiler's time bound `10 κ (K + |x| + 1) + 1` is below the concept's, `K = C₀ · 2^(C₁ e³) · X^C₃`. -/
theorem time_arith {κ C₀ C₁ C₃ e X X' c : ℕ} (hX : 1 ≤ X) (hXX : X ≤ X') (h3 : 1 ≤ C₃) (h1 : C₁ ≤ c) (h3c : C₃ ≤ c)
    (hc : 10 * κ * (C₀ + 1) + 1 ≤ c) :
    10 * κ * (C₀ * 2 ^ (C₁ * e ^ 3) * X ^ C₃ + X) + 1 ≤ c * 2 ^ (c * e ^ 3) * X' ^ c := by
  set S := 2 ^ (C₁ * e ^ 3) * X ^ C₃ with hS
  have hXS : X ≤ S := by
    have h1' : 1 ≤ 2 ^ (C₁ * e ^ 3) := Nat.one_le_two_pow
    calc X ≤ X ^ C₃ := Nat.le_self_pow (by omega) X
      _ = 1 * X ^ C₃ := by ring
      _ ≤ S := Nat.mul_le_mul_right _ h1'
  have hS1 : 1 ≤ S := le_trans hX hXS
  have e1 : C₀ * 2 ^ (C₁ * e ^ 3) * X ^ C₃ = C₀ * S := by rw [hS]; ring
  rw [e1]
  have e2 : 10 * κ * (C₀ * S + X) + 1 ≤ (10 * κ * (C₀ + 1) + 1) * S := by
    have : 10 * κ * (C₀ * S + X) ≤ 10 * κ * ((C₀ + 1) * S) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith
  have e3 : S ≤ 2 ^ (c * e ^ 3) * X' ^ c :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h1))
      (le_trans (Nat.pow_le_pow_left hXX _) (Nat.pow_le_pow_right (by omega) h3c))
  calc 10 * κ * (C₀ * S + X) + 1 ≤ (10 * κ * (C₀ + 1) + 1) * S := e2
    _ ≤ c * S := Nat.mul_le_mul_right _ hc
    _ ≤ c * (2 ^ (c * e ^ 3) * X' ^ c) := Nat.mul_le_mul_left _ e3
    _ = c * 2 ^ (c * e ^ 3) * X' ^ c := by ring

end arith

end Lax117284Proofs.Treewidth.Fun.A2

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A3Defs` -/

section
/-!
# WP A3 (1): the statement `ImproveRun` (the analogue of `A2.DecompRun` for the improvement stage)

The input word of `improveDecomposition` is `x = g ++ [k, l] ++ D` (`g = n :: n²` entries, `D = d :: 3d` entries); it is read off
`x` by the header `n = x[0]`: `k = x[n²+1]`, `l = x[n²+2]`, `D = drop (n²+3) x`.

* `outWord1 x` = `1 :: D` when `l ≤ k` (the decomposition already has width `≤ k`), else `outWord (g ++ [k])`;
* `D1`  : the structurally admissible inputs (a graph word, `k`, `l`, and a word `D` whose length is `1 + 3 · D[0]`);
* `pC1 C` : the cost parameters of the top-level run, `K x = (C + 100) · 2^(C·l³) · (|x|+1)^C`, `l` = the parameter entry.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The output word of the improvement stage on `g ++ [k, l] ++ D`. -/
def outWord1 (x : List ℕ) : List ℕ :=
  if x.getD (x.getD 0 0 * x.getD 0 0 + 2) 0 ≤ x.getD (x.getD 0 0 * x.getD 0 0 + 1) 0 then
    1 :: x.drop (x.getD 0 0 * x.getD 0 0 + 3)
  else A2.outWord (x.take (x.getD 0 0 * x.getD 0 0 + 2))

/-- The structurally admissible inputs. -/
def D1 : Set (List ℕ) :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ) (k l : ℕ) (D : List ℕ),
    x = g ++ [k, l] ++ D ∧ EncodesGraph g G ∧ D.length = 1 + 3 * D.getD 0 0}

/-- The cost parameters of the top-level run (`c₀ = C + 100`, `c₁ = C`, `c₂ = 1`, `c₃ = C`). -/
def pC1 (C : ℕ) : KP := ⟨C + 100, C, 1, C⟩

/-- **What `improveRun_of` proves.**  One function table (ids `< N`), one entry `main`, one constant `C`, such that on every
admissible input the entry evaluates `[toVal x]` to `toVal (outWord1 x)` within `K x` steps at the tag bound `Bx`, and the output
is no longer than `K x`. -/
def ImproveRun : Prop :=
  ∃ (Δ : ℕ → Option Tm) (N main C : ℕ), 1 ≤ C ∧ (∀ f, N ≤ f → Δ f = none) ∧
    ∀ x ∈ D1, Runs Δ (Bx (pC1 C) Fmt.graphKLD x) main [toVal x] (toVal (outWord1 x)) (Kx (pC1 C) Fmt.graphKLD x) ∧
      (outWord1 x).length ≤ Kx (pC1 C) Fmt.graphKLD x

end Lax117284Proofs.Treewidth.Fun.A3

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A3Disp` -/

section
/-!
# WP A3 (2): the dispatcher term

The table `Δ` delivered by `DecompRun` is abstract (it need not contain the library), so the dispatcher brings its own `take`, `drop`
at fresh ids (`tk`, `dr`), copies of `Lib1.takeTm/dropTm` with the recursive id replaced.

`dispTm tk dr mn` (environment `[x]`):

    n := x[0];  m := n·n + 1;  r := drop m x   (= k :: l :: D);
    if k < l then mn (take (m+1) x) else 1 :: D          (D = tail (tail r))
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun ToVal

abbrev V (i : ℕ) : Tm := .var i

def takeTmAt (f : ℕ) : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (.lit 0) (.cons (.fst (V 1)) (.call f [.sub (V 0) (.lit 1), .snd (V 1)])))

def dropTmAt (f : ℕ) : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.ite (.eq (V 0) (.lit 0)) (V 1) (.call f [.sub (V 0) (.lit 1), .snd (V 1)]))

def dispTm (tk dr mn : ℕ) : Tm :=
  .letE (.fst (V 0))
    (.letE (.add (.mul (V 0) (V 0)) (.lit 1))
      (.letE (.call dr [V 0, V 2])
        (.ite (.lt (.fst (V 0)) (.fst (.snd (V 0))))
          (.call mn [.call tk [.add (V 1) (.lit 1), V 3]])
          (.cons (.lit 1) (.snd (.snd (V 0)))))))

section runs
variable {Δ' : ℕ → Option Tm} {B : ℕ}

theorem takeAt_runs {f : ℕ} (hf : Δ' f = some (takeTmAt f)) (n : ℕ) (xs : List ℕ) (hB : 1 < B) :
    Runs Δ' B f [toVal n, toVal xs] (toVal (xs.take n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk hf ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk hf ?_
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

theorem dropAt_runs {f : ℕ} (hf : Δ' f = some (dropTmAt f)) (n : ℕ) (xs : List ℕ) (hB : 1 < B) :
    Runs Δ' B f [toVal n, toVal xs] (toVal (xs.drop n)) (20 * min n xs.length + 12) := by
  induction xs generalizing n with
  | nil =>
    refine Runs.mk hf ?_
    ev_start
    · ev_run
    · simp
  | cons a xs ih =>
    refine Runs.mk hf ?_
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

theorem drop_two (x : List ℕ) (m : ℕ) (h : m + 2 ≤ x.length) :
    x.drop m = x.getD m 0 :: x.getD (m + 1) 0 :: x.drop (m + 2) := by
  have h1 : m < x.length := by omega
  have h2 : m + 1 < x.length := by omega
  rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]

variable {tk dr mn d : ℕ}

/-- **The dispatcher, case `l ≤ k`.** -/
theorem disp_runs_true (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr)) (n : ℕ) (xs : List ℕ)
    (hlen : n * n + 3 ≤ (n :: xs).length) (hB : n * n + 2 < B)
    (hle : (n :: xs).getD (n * n + 2) 0 ≤ (n :: xs).getD (n * n + 1) 0) :
    Runs Δ' B d [toVal (n :: xs)] (toVal (1 :: (n :: xs).drop (n * n + 3))) (20 * (n :: xs).length + 60) := by
  have hdrop := dropAt_runs (B := B) hdr (n * n + 1) (n :: xs) (by omega)
  rw [drop_two (n :: xs) (n * n + 1) (by omega)] at hdrop
  have hnot : ¬ (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 1 + 1) 0 := by
    have : n * n + 1 + 1 = n * n + 2 := by ring
    rw [this]; omega
  have e3 : n * n + 1 + 2 = n * n + 3 := by ring
  rw [e3] at hdrop
  refine Runs.mk hd ?_
  ev_start
  · ev_run
    · ev_call hdrop
      ev_run
    apply EvLe.iteF
    case hc =>
      apply EvLe.lt
      case ha => ev_sub
      case hb => ev_sub
      case hv => rw [if_neg hnot]
    case hn => rfl
    case he => ev_run
  · omega

/-- **The dispatcher, case `k < l`.** -/
theorem disp_runs_false (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr))
    (htk : Δ' tk = some (takeTmAt tk)) (n : ℕ) (xs : List ℕ)
    (hlen : n * n + 3 ≤ (n :: xs).length) (hB : n * n + 2 < B)
    (hlt : (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 2) 0) {v : Val} {cm : ℕ}
    (hmain : Runs Δ' B mn [toVal ((n :: xs).take (n * n + 1 + 1))] v cm) :
    Runs Δ' B d [toVal (n :: xs)] v (cm + 40 * (n :: xs).length + 100) := by
  have hdrop := dropAt_runs (B := B) hdr (n * n + 1) (n :: xs) (by omega)
  rw [drop_two (n :: xs) (n * n + 1) (by omega)] at hdrop
  have htake := takeAt_runs (B := B) htk (n * n + 1 + 1) (n :: xs) (by omega)
  have hlt' : (n :: xs).getD (n * n + 1) 0 < (n :: xs).getD (n * n + 1 + 1) 0 := hlt
  refine Runs.mk hd ?_
  ev_start
  · ev_run
    · ev_call hdrop
      ev_run
    apply EvLe.iteT
    case hc =>
      apply EvLe.lt
      case ha => ev_sub
      case hb => ev_sub
      case hv => rw [if_pos hlt']
    case hn => simp
    case ht =>
      ev_run
  · have := min_le_right (n * n + 1) (n :: xs).length
    have := min_le_right (n * n + 1 + 1) (n :: xs).length
    omega

end runs

end Lax117284Proofs.Treewidth.Fun.A3

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A3Facts` -/

section
/-!
# WP A3 (3): the words `x = g ++ [k, l] ++ D`, the output word, and the numeric facts

`facts_*` read `n, k, l, D, g ++ [k]` off `x`; `outWord1_eq` evaluates `outWord1`; `maxEntry_*` and the `Kx`-monotonicity lemmas
compare the two runs (`Bx (pC C) graphK y` of the exact algorithm against `Bx (pC1 C) graphKLD x` of the dispatcher).
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

section words

variable {n : ℕ} {G : SimpleGraph (Fin n)} {g : List ℕ}

theorem facts_head (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD 0 0 = n := by
  have h0 : 0 < g.length := by rw [henc.length_eq]; omega
  rw [List.append_assoc, List.getD_append _ _ _ _ h0]
  exact henc.head_eq

theorem facts_k (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD (n * n + 1) 0 = k := by
  have hg := henc.length_eq
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
  have : n * n + 1 - (1 + n * n) = 0 := by omega
  rw [this]; rfl

theorem facts_l (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).getD (n * n + 2) 0 = l := by
  have hg := henc.length_eq
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
  have : n * n + 2 - (1 + n * n) = 1 := by omega
  rw [this]; rfl

theorem facts_drop (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).drop (n * n + 3) = D := by
  have hg := henc.length_eq
  apply List.drop_left'
  simp [hg]; omega

theorem facts_take (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : (g ++ [k, l] ++ D).take (n * n + 2) = g ++ [k] := by
  have hg := henc.length_eq
  have : g ++ [k, l] ++ D = (g ++ [k]) ++ ([l] ++ D) := by simp
  rw [this]
  apply List.take_left'
  simp [hg]; omega

theorem facts_length (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) :
    (g ++ [k, l] ++ D).length = n * n + 3 + D.length := by
  have hg := henc.length_eq
  simp [hg]; omega

theorem outWord1_eq (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) :
    outWord1 (g ++ [k, l] ++ D) = if l ≤ k then 1 :: D else A2.outWord (g ++ [k]) := by
  unfold outWord1
  rw [facts_head henc, facts_k henc, facts_l henc, facts_drop henc, facts_take henc]

theorem facts_kw (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) : Fmt.graphKLD.kw (g ++ [k, l] ++ D) = l := by
  unfold Fmt.kw
  rw [facts_head henc]
  exact facts_l henc k l D

theorem facts_fmtLen (henc : EncodesGraph g G) (k l : ℕ) (D : List ℕ) (hD : D.length = 1 + 3 * D.getD 0 0) :
    fmtLen Fmt.graphKLD (g ++ [k, l] ++ D) = (g ++ [k, l] ++ D).length := by
  have hg := henc.length_eq
  have h1 : nOfWord (g ++ [k, l] ++ D) = n := facts_head henc k l D
  have h2 : (g ++ [k, l] ++ D).getD (1 + n * n + 2) 0 = D.getD 0 0 := by
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hg]
    have : 1 + n * n + 2 - (1 + n * n) = 2 := by omega
    rw [this]
    simp [List.getD_cons_succ]
  show 1 + nOfWord (g ++ [k, l] ++ D) * nOfWord (g ++ [k, l] ++ D) + 2 + 1
      + 3 * (g ++ [k, l] ++ D).getD (1 + nOfWord (g ++ [k, l] ++ D) * nOfWord (g ++ [k, l] ++ D) + 2) 0 = _
  rw [h1, h2, facts_length henc k l D]
  omega

end words

/-! ### maximal entries -/

theorem le_maxEntry {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ maxEntry x := by
  induction x with
  | nil => simp at h
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem maxEntry_le {y : List ℕ} {M : ℕ} (h : ∀ v ∈ y, v ≤ M) : maxEntry y ≤ M := by
  induction y with
  | nil => simp [maxEntry]
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons]
    exact max_le (h a (List.mem_cons_self ..)) (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

theorem Bx_le {p p' : KP} {fmt fmt' : Fmt} {y x : List ℕ} (hM : ∀ v ∈ y, v ≤ maxEntry x)
    (hK : Kx p fmt y ≤ Kx p' fmt' x) : Bx p fmt y ≤ Bx p' fmt' x := by
  unfold Bx bexp
  have := maxEntry_le hM
  have h2 : maxEntry y + Kx p fmt y + 2 ≤ maxEntry x + Kx p' fmt' x + 2 := by omega
  have := Nat.pow_le_pow_left h2 2
  omega

/-- `Kx` of the dispatcher: `(C + 100) · 2^(C·l³) · (|x| + 1)^C`. -/
theorem Kx_eq {x : List ℕ} {l C : ℕ} (hkw : Fmt.graphKLD.kw x = l) :
    Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := by
  unfold Kx pC1 KP.k
  rw [hkw]

theorem S_ge {C l m : ℕ} (hC : 1 ≤ C) : m + 1 ≤ 2 ^ (C * l ^ 3) * (m + 1) ^ C := by
  have h1 : 1 ≤ 2 ^ (C * l ^ 3) := Nat.one_le_two_pow
  calc m + 1 ≤ (m + 1) ^ C := Nat.le_self_pow (by omega) _
    _ = 1 * (m + 1) ^ C := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h1

/-- the exact algorithm's cost bound on the prefix `g ++ [k]` is below the dispatcher's, plus `100 (|x| + 1)`. -/
theorem Ky_add {C k l ly lx : ℕ} (hkl : k ≤ l) (hl : ly ≤ lx) (hC : 1 ≤ C) :
    C * 2 ^ (C * k ^ 3) * (ly + 1) ^ C + 100 * (lx + 1) ≤ (C + 100) * 2 ^ (C * l ^ 3) * (lx + 1) ^ C := by
  set S := 2 ^ (C * l ^ 3) * (lx + 1) ^ C with hS
  have h1 : C * 2 ^ (C * k ^ 3) * (ly + 1) ^ C ≤ C * S := by
    rw [hS, ← mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hkl 3))))
      (Nat.pow_le_pow_left (by omega) _)
  have h2 : lx + 1 ≤ S := S_ge hC
  have : (C + 100) * 2 ^ (C * l ^ 3) * (lx + 1) ^ C = (C + 100) * S := by rw [hS]; ring
  rw [this]
  nlinarith

end Lax117284Proofs.Treewidth.Fun.A3

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A3Run` -/

section
/-!
# WP A3 (4): `improveRun_of` — the dispatcher over the exact algorithm's table

`extΔ Δ N main` adds three functions at the fresh ids `N` (dispatcher), `N + 1` (take), `N + 2` (drop) to the table of `DecompRun`
(ids `< N`), and `improveRun_of h : ImproveRun` runs the dispatcher: for `l ≤ k` it answers `1 :: D`, otherwise it calls the
old `main` on the prefix `g ++ [k]` (`take (n² + 2) x`), weakened to the larger tag bound `Bx (pC1 C) graphKLD x`.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284Proofs.Treewidth.Fun.VM.Ram Lax117284.GraphWords ToVal

/-- The extended table. -/
def extΔ (Δ : ℕ → Option Tm) (N main : ℕ) : ℕ → Option Tm := fun f =>
  if f = N then some (dispTm (N + 1) (N + 2) main)
  else if f = N + 1 then some (takeTmAt (N + 1))
  else if f = N + 2 then some (dropTmAt (N + 2))
  else Δ f

theorem extΔ_ext {Δ : ℕ → Option Tm} {N : ℕ} (main : ℕ) (hN : ∀ f, N ≤ f → Δ f = none) : Ext Δ (extΔ Δ N main) := by
  intro f b hf
  have hf' : f < N := by
    by_contra hc
    rw [hN f (by omega)] at hf
    cases hf
  unfold extΔ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hf

theorem extΔ_none {Δ : ℕ → Option Tm} {N : ℕ} (main : ℕ) (hN : ∀ f, N ≤ f → Δ f = none) :
    ∀ f, N + 3 ≤ f → extΔ Δ N main f = none := by
  intro f hf
  unfold extΔ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hN f (by omega)

theorem extΔ_d (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main N = some (dispTm (N + 1) (N + 2) main) := by
  simp [extΔ]

theorem extΔ_tk (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main (N + 1) = some (takeTmAt (N + 1)) := by
  simp [extΔ]

theorem extΔ_dr (Δ : ℕ → Option Tm) (N main : ℕ) : extΔ Δ N main (N + 2) = some (dropTmAt (N + 2)) := by
  simp [extΔ]

section wrappers
variable {Δ' : ℕ → Option Tm} {B tk dr mn d : ℕ}

theorem disp_true_x (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr)) {x : List ℕ} {n : ℕ}
    {xs : List ℕ} (hx : x = n :: xs) (hlen : n * n + 3 ≤ x.length) (hB : n * n + 2 < B)
    (hle : x.getD (n * n + 2) 0 ≤ x.getD (n * n + 1) 0) :
    Runs Δ' B d [toVal x] (toVal (1 :: x.drop (n * n + 3))) (20 * x.length + 60) := by
  subst hx
  exact disp_runs_true hd hdr n xs hlen hB hle

theorem disp_false_x (hd : Δ' d = some (dispTm tk dr mn)) (hdr : Δ' dr = some (dropTmAt dr))
    (htk : Δ' tk = some (takeTmAt tk)) {x : List ℕ} {n : ℕ} {xs : List ℕ} (hx : x = n :: xs)
    (hlen : n * n + 3 ≤ x.length) (hB : n * n + 2 < B)
    (hlt : x.getD (n * n + 1) 0 < x.getD (n * n + 2) 0) {v : Val} {cm : ℕ}
    (hmain : Runs Δ' B mn [toVal (x.take (n * n + 2))] v cm) :
    Runs Δ' B d [toVal x] v (cm + 40 * x.length + 100) := by
  subst hx
  exact disp_runs_false hd hdr htk n xs hlen hB hlt hmain

end wrappers

theorem improveRun_of (h : A2.DecompRun) : ImproveRun := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := h
  refine ⟨extΔ Δ N main, N + 3, N, C, hC, extΔ_none main hN, ?_⟩
  rintro x ⟨n, G, g, k, l, D, rfl, henc, hD⟩
  have hd := extΔ_d Δ N main
  have htk := extΔ_tk Δ N main
  have hdr := extΔ_dr Δ N main
  set x := g ++ [k, l] ++ D with hx
  have hlenx : x.length = n * n + 3 + D.length := facts_length henc k l D
  have hkw := facts_kw henc k l D
  have hK : Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := Kx_eq hkw
  have hS := S_ge (C := C) (l := l) (m := x.length) hC
  have hS' : (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C
      = (C + 100) * (2 ^ (C * l ^ 3) * (x.length + 1) ^ C) := by ring
  obtain ⟨xs, hxs⟩ : ∃ xs, x = n :: xs := by
    have h0 : 0 < g.length := by rw [henc.length_eq]; omega
    obtain ⟨a, gs, hg⟩ : ∃ a gs, g = a :: gs := by
      cases g with
      | nil => simp at h0
      | cons a gs => exact ⟨a, gs, rfl⟩
    refine ⟨gs ++ [k, l] ++ D, ?_⟩
    have := henc.head_eq
    rw [hg] at this
    simp only [List.getD_cons_zero] at this
    rw [hx, hg, this]
    simp
  have hhead : x.getD 0 0 = n := facts_head henc k l D
  set K := Kx (pC1 C) Fmt.graphKLD x with hKdef
  set B := Bx (pC1 C) Fmt.graphKLD x with hBdef
  have hnM : n ≤ maxEntry x := by
    apply le_maxEntry
    rw [hxs]; simp
  have hB2 : n * n + 2 < B := by
    rw [hBdef]; unfold Bx bexp
    have h1 : n * n ≤ maxEntry x * maxEntry x := Nat.mul_le_mul hnM hnM
    nlinarith [Nat.zero_le K, Nat.zero_le (maxEntry x)]
  have hlen3 : n * n + 3 ≤ x.length := by omega
  have hxK : x.length + 1 ≤ K := by rw [hK, hS']; nlinarith
  rw [outWord1_eq henc k l D]
  by_cases hle : l ≤ k
  · rw [if_pos hle]
    have hle' : x.getD (n * n + 2) 0 ≤ x.getD (n * n + 1) 0 := by
      rw [facts_l henc, facts_k henc]; exact hle
    have hr := disp_true_x hd hdr hxs hlen3 hB2 hle'
    rw [facts_drop henc] at hr
    have hcost : 20 * x.length + 60 ≤ K := by rw [hK, hS']; nlinarith
    refine ⟨Runs.mono hr hcost, ?_⟩
    simp only [List.length_cons]
    omega
  · rw [if_neg hle]
    have hlt : x.getD (n * n + 1) 0 < x.getD (n * n + 2) 0 := by
      rw [facts_l henc, facts_k henc]; omega
    have hD2 : g ++ [k] ∈ A2.D2 := A2.mem_D2 henc k
    obtain ⟨hr0, hl0⟩ := hrun (g ++ [k]) hD2
    have hKy : Kx (A2.pC C) Fmt.graphK (g ++ [k]) = C * 2 ^ (C * k ^ 3) * ((g ++ [k]).length + 1) ^ C := by
      unfold Kx A2.pC KP.k
      rw [A2.kw_graphK henc k]
    have hkl : k ≤ l := by omega
    have hly : (g ++ [k]).length ≤ x.length := by
      rw [hlenx, List.length_append, henc.length_eq]; simp; omega
    have hKyle := Ky_add (C := C) hkl hly hC
    rw [← hKy, ← hK] at hKyle
    have hKB : Kx (A2.pC C) Fmt.graphK (g ++ [k]) ≤ K := by omega
    have hBB : Bx (A2.pC C) Fmt.graphK (g ++ [k]) ≤ B :=
      Bx_le (fun v hv => le_maxEntry (by rw [hx]; simp at hv ⊢; tauto)) hKB
    have hmain : Runs (extΔ Δ N main) B main [toVal (x.take (n * n + 2))]
        (toVal (A2.outWord (g ++ [k]))) (Kx (A2.pC C) Fmt.graphK (g ++ [k])) := by
      rw [hx, facts_take henc]
      exact Runs.weaken (extΔ_ext main hN) hBB hr0
    have hr := disp_false_x hd hdr htk hxs hlen3 hB2 hlt hmain
    have hcost : Kx (A2.pC C) Fmt.graphK (g ++ [k]) + 40 * x.length + 100 ≤ K := by omega
    exact ⟨Runs.mono hr hcost, le_trans hl0 hKB⟩

end Lax117284Proofs.Treewidth.Fun.A3

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A2Main` -/

section
/-!
# WP A2 (2): `niceDecomposition_computable` from `DecompRun`

`niceDecomposition_computable_of h` is the exact statement of the concept axiom
`Lax117284.BodlaenderGeneral.niceDecomposition_computable`, proved from the functional run `h : DecompRun` through the compiler
(`Load.compile_computes`): the program is the compiled one, the constant `c` dominates the compiler's constant `c₀` and
`10 κ (C + 1) + 1`, and the set of admissible inputs handed to the compiler is the singleton `{g ++ [k]}` (the concept's guard
is per input, the compiler's is per set).
-/

namespace Lax117284Proofs.Treewidth.Fun.A2

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal Lax808846.Ram Lax808846.RamComputes

open Classical in
theorem niceDecomposition_computable_of (h : DecompRun) :
    ∃ (prog : Program) (c : ℕ), ∀ (W k n : ℕ) (G : SimpleGraph (Fin n)) (g : List ℕ),
      EncodesGraph g G →
      (∀ v ∈ g ++ [k], c * 2 ^ (c * k ^ 3) * ((g ++ [k]).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * k ^ 3) * (g.length + 2) ^ c ∧
        RunsTo W prog (g ++ [k]) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D, out = 1 :: D ∧ NiceDecomposition G k D) := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := h
  obtain ⟨prog, c₀, H⟩ := compile_computes Δ hN main Fmt.graphK (pC C) hC hC (le_refl 1)
  refine ⟨prog, max c₀ (max C (10 * kappa Δ N main (pC C) * (C + 1) + 1)), ?_⟩
  intro W k n G g henc hg
  set c := max c₀ (max C (10 * kappa Δ N main (pC C) * (C + 1) + 1)) with hcdef
  have hc0 : c₀ ≤ c := le_max_left _ _
  have hcC : C ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcK : 10 * kappa Δ N main (pC C) * (C + 1) + 1 ≤ c := le_trans (le_max_right _ _) (le_max_right _ _)
  set x := g ++ [k] with hx
  have hD2 : x ∈ D2 := mem_D2 henc k
  have hkw : Fmt.graphK.kw x = k := kw_graphK henc k
  have hlen : x.length = g.length + 1 := by rw [hx, List.length_append]; simp
  obtain ⟨hr, hl⟩ := hrun x hD2
  have hcomp := H {x} outWord (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact fmtLen_graphK henc k)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hr)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hl) W
    (fun y hy v hv => by
      rw [Set.mem_singleton_iff.1 hy] at hv ⊢
      rw [hkw]
      exact guard_mono hc0 (by omega) (hg v hv))
  obtain ⟨t, ht, hrt⟩ := hcomp x rfl
  refine ⟨outWord x, t, ?_, hrt, ?_⟩
  · refine le_trans ht ?_
    have hK : Kx (pC C) Fmt.graphK x = C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C := by
      unfold Kx
      rw [hkw]
      show C * 2 ^ (C * k ^ 3) * (x.length + 1) ^ C = _
      rw [hlen]
    have := time_arith (κ := kappa Δ N main (pC C)) (C₀ := C) (C₁ := C) (C₃ := C) (e := k) (X := g.length + 2)
      (X' := g.length + 2) (c := c) (by omega) le_rfl hC hcC hcC hcK
    show 10 * kappa Δ N main (pC C) * (Kx (pC C) Fmt.graphK x + x.length + 1) + 1 ≤ _
    rw [hK, hlen]
    have e : C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C + (g.length + 1) + 1
        = C * 2 ^ (C * k ^ 3) * (g.length + 2) ^ C + (g.length + 2) := by ring
    rw [e]
    exact this
  · exact outWord_correct henc k

end Lax117284Proofs.Treewidth.Fun.A2

/-- the statement proved is exactly the concept's -/
example (h : Lax117284Proofs.Treewidth.Fun.A2.DecompRun) : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  Lax117284Proofs.Treewidth.Fun.A2.niceDecomposition_computable_of h

end

/-! ### `Lax117284Proofs.Treewidth.Fun.A3Main` -/

section
/-!
# WP A3 (5): `improveDecomposition` from `DecompRun`

* `NiceDecomposition.mono_width` : a nice decomposition of width `l ≤ k` is one of width `k`;
* `improveDecomposition_of h` : the exact statement of the concept axiom `Lax117284.BodlaenderKloks.improveDecomposition`, from
  `improveRun_of h` (the dispatcher) through the compiler `Load.compile_computes` with the format `graphKLD` (parameter entry `l`).

**Glue (TODO until A1 lands `decompose_run : A2.DecompRun`)**: in a last file importing `Fun.A1Main`,
`theorem niceDecomposition_computable_final : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable := A2.niceDecomposition_computable_of decompose_run`
and `theorem improveDecomposition_final : type_of% @Lax117284.BodlaenderKloks.improveDecomposition := A3.improveDecomposition_of decompose_run`,
each with the docstring `---\nconclusion: <Concept.name>\n---` and an `example : type_of% @<Concept.name> := ..._final`.
-/

namespace Lax117284Proofs.Treewidth.Fun.A3

open Lax117284Proofs.Treewidth.Fun Lax117284Proofs.Treewidth.Fun.Load Lax117284.GraphWords ToVal Lax808846.Ram Lax808846.RamComputes

theorem NiceDecomposition.mono_width {n : ℕ} {G : SimpleGraph (Fin n)} {l k : ℕ} {D : List ℕ} (h : NiceDecomposition G l D)
    (hlk : l ≤ k) : NiceDecomposition G k D :=
  { length_eq := h.length_eq
    nonempty := h.nonempty
    shape := h.shape
    parent := h.parent
    isTree := h.isTree
    covers := h.covers
    edges := h.edges
    connected := h.connected
    width := fun i hi => le_trans (h.width i hi) (by omega) }

open Classical in
theorem improveDecomposition_of (h : A2.DecompRun) :
    ∃ (prog : Program) (c : ℕ), ∀ (W k l : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (g D : List ℕ),
      EncodesGraph g G → NiceDecomposition G l D →
      (∀ v ∈ g ++ [k, l] ++ D,
        c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + v + 1) ^ c ≤ 2 ^ W) →
      ∃ (out : List ℕ) (t : ℕ), t ≤ c * 2 ^ (c * l ^ 3) * ((g ++ [k, l] ++ D).length + 2) ^ c ∧
        RunsTo W prog (g ++ [k, l] ++ D) out t ∧
        (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost G k ∨
          ∃ D', out = 1 :: D' ∧ NiceDecomposition G k D') := by
  obtain ⟨Δ, N, main, C, hC, hN, hrun⟩ := improveRun_of h
  obtain ⟨prog, c₀, H⟩ := compile_computes Δ hN main Fmt.graphKLD (pC1 C) (by simp [pC1]) hC (le_refl 1)
  refine ⟨prog, max c₀ (max (C + 100) (10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1)), ?_⟩
  intro W k l n G g D henc hnice hg
  set c := max c₀ (max (C + 100) (10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1)) with hcdef
  have hc0 : c₀ ≤ c := le_max_left _ _
  have hcC : C + 100 ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcK : 10 * kappa Δ N main (pC1 C) * (C + 100 + 1) + 1 ≤ c := le_trans (le_max_right _ _) (le_max_right _ _)
  set x := g ++ [k, l] ++ D with hx
  have hD1 : x ∈ D1 := ⟨n, G, g, k, l, D, rfl, henc, hnice.length_eq⟩
  have hkw : Fmt.graphKLD.kw x = l := facts_kw henc k l D
  obtain ⟨hr, hl⟩ := hrun x hD1
  have hcomp := H {x} outWord1 (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact facts_fmtLen henc k l D hnice.length_eq)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hr)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hl) W
    (fun y hy v hv => by
      rw [Set.mem_singleton_iff.1 hy] at hv ⊢
      rw [hkw]
      exact A2.guard_mono hc0 (by omega) (hg v hv))
  obtain ⟨t, ht, hrt⟩ := hcomp x rfl
  refine ⟨outWord1 x, t, ?_, hrt, ?_⟩
  · refine le_trans ht ?_
    have hK : Kx (pC1 C) Fmt.graphKLD x = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C := Kx_eq hkw
    have := A2.time_arith (κ := kappa Δ N main (pC1 C)) (C₀ := C + 100) (C₁ := C) (C₃ := C) (e := l) (X := x.length + 1)
      (X' := x.length + 2) (c := c) (by omega) (by omega) hC (by omega) (by omega) hcK
    show 10 * kappa Δ N main (pC1 C) * (Kx (pC1 C) Fmt.graphKLD x + x.length + 1) + 1 ≤ _
    rw [hK]
    have e : (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C + x.length + 1
        = (C + 100) * 2 ^ (C * l ^ 3) * (x.length + 1) ^ C + (x.length + 1) := by ring
    rw [e]
    exact this
  · rw [hx, outWord1_eq henc k l D]
    by_cases hle : l ≤ k
    · rw [if_pos hle]
      exact Or.inr ⟨D, rfl, NiceDecomposition.mono_width hnice hle⟩
    · rw [if_neg hle]
      exact A2.outWord_correct henc k

end Lax117284Proofs.Treewidth.Fun.A3

/-- the statement proved is exactly the concept's -/
example (h : Lax117284Proofs.Treewidth.Fun.A2.DecompRun) : type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  Lax117284Proofs.Treewidth.Fun.A3.improveDecomposition_of h

end

/-! ### `Lax117284Proofs.Treewidth.Fun.Final` -/

section
/-!
# The two concept statements, proved

`niceDecomposition_computable` (Bodlaender–Kloks, a nice tree decomposition of width at most `k` in time
`c·2^(c·k³)·(|g|+2)^c`) and `improveDecomposition` (Bodlaender–Kloks' improvement step, in time
`c·2^(c·ℓ³)·(|input|+2)^c`), from the exact algorithm.

The algorithm is the vertex-by-vertex wrapper `decomposeC` around Bodlaender–Kloks' dynamic programming over
characteristics of partial decompositions (typical sequences, normal form, introduce/forget/join, extraction of a decomposition
from a table entry).  Its correctness is `Wrap/ImproveC` and `Chars/*`; its running time is obtained by running the
Lean functions themselves on a verified virtual machine for a first-order functional fragment (`Fun/*`), compiled to a word RAM
program by the archive's verified pipeline; the cost analysis is in `Fun/E*` and `Fun/A1*`, the concept-level transfer in `Fun/A2*`, `Fun/A3*`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Final

/--
---
conclusion: Lax117284.BodlaenderGeneral.niceDecomposition_computable
---
Bodlaender's theorem with Kloks' niceness on a word RAM, proved by running the exact Bodlaender–Kloks algorithm (the vertex-by-vertex
wrapper around the dynamic program over characteristics) as a functional program on a verified virtual machine and compiling it.
-/
theorem niceDecomposition_computable_proved :
    type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  A2.niceDecomposition_computable_of A1.decompose_run

/--
---
conclusion: Lax117284.BodlaenderKloks.improveDecomposition
---
The improvement step of Bodlaender–Kloks on a word RAM: given a nice decomposition of width `ℓ` it returns one of width at most `k`
or `[0]`, proved by a dispatcher over the same exact algorithm (if `ℓ ≤ k` the given decomposition is returned; otherwise the main
algorithm runs on the graph and `k`).
-/
theorem improveDecomposition_proved :
    type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  A3.improveDecomposition_of A1.decompose_run

end Lax117284Proofs.Treewidth.Fun.Final

example : type_of% @Lax117284.BodlaenderGeneral.niceDecomposition_computable :=
  Lax117284Proofs.Treewidth.Fun.Final.niceDecomposition_computable_proved

example : type_of% @Lax117284.BodlaenderKloks.improveDecomposition :=
  Lax117284Proofs.Treewidth.Fun.Final.improveDecomposition_proved

end
