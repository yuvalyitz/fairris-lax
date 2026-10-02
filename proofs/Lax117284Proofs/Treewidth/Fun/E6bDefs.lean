import Lax117284Proofs.Treewidth.Fun.E4Assembly
import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Fun.E6bFind

/-!
# WP E6b (2): the table `e6bTbl` (ids `704 … 767`) — `extract`

`extract adj k nt target` (`Chars/Alg.lean`) searches with `findSome?`; here it is the recursive F-function `fExtract`.

| id | function | arguments |
|---|---|---|
| 704 `fExtract` | `extract (adjOfWord x) k nt target` (an `Option RT`) | `[x, k, nt, target]` |
| 705 `fFgCand` | forget candidate `cq ↦ if forgetC y cq = target then extract c cq else none` | `[(x,k,y,c,target), cq]` |
| 706 `fInCand` | introduce candidate (`realIntro` after a successful recursive extraction) | `[((k+1,v,N),x,k,c,bag,target), cq]` |
| 707 `fJnOuter` | join outer candidate `ca ↦ Tb.findSome? (inner ca)` | `[((x,k,a,b,bag,target), Tb), ca]` |
| 708 `fJnInner` | join inner candidate | `[(ca,x,k,a,b,bag,target), cb]` |
| 709 `fExtractUn` | packed `fExtract` | `[(x, k, nt, target)]` |
| 710 `fExtractFirst` | `match tables … with [] => none | c :: _ => extract … c` (the extraction step of `improveC`) | `[x, k, nt]` |

The tables are computed once per node (`fTables`, E4); `bag`, `nbrs` once per node; the candidates run over the table.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open Lib1

abbrev fExtract : ℕ := 704
abbrev fFgCand : ℕ := 705
abbrev fInCand : ℕ := 706
abbrev fJnOuter : ℕ := 707
abbrev fJnInner : ℕ := 708
abbrev fExtractUn : ℕ := 709
abbrev fExtractFirst : ℕ := 710

/-- `snd` applied `n` times -/
def sndN : ℕ → Tm → Tm
  | 0, t => t
  | n + 1, t => .snd (sndN n t)

/-- the `i`-th (not last) component of a right-nested tuple -/
def comp (i : ℕ) (t : Tm) : Tm := .fst (sndN i t)

/-- the option `some (RT.node ∅ [])` -/
def leafTm : Tm := .cons (.lit 1) (.cons (.lit 0) (.lit 0))

/-- forget candidate: environment `[ctx, cq]`, `ctx = (x, k, y, c, target)` -/
def fgCandTm : Tm :=
  .ite (.call fEqV [.call E2.fForgetC [comp 2 (V 0), V 1], sndN 4 (V 0)])
    (.call fExtract [comp 0 (V 0), comp 1 (V 0), comp 3 (V 0), V 1])
    (.lit 0)

/-- introduce candidate: environment `[ctx, cq]`, `ctx = ((k+1, v, N), x, k, c, bag, target)` -/
def inCandTm : Tm :=
  .ite (.call fMem [sndN 5 (V 0), .call E4.fIntroCb [comp 0 (V 0), V 1]])
    (.letE (.call fExtract [comp 1 (V 0), comp 2 (V 0), comp 3 (V 0), V 1])
      (.ite (.isNat (V 0)) (.lit 0)
        (.call E5R.fRealIntro [.lit E3C.fIntroPlans, .fst (comp 0 (V 1)), .fst (.snd (comp 0 (V 1))),
          .snd (.snd (comp 0 (V 1))), comp 4 (V 1), .snd (V 0), sndN 5 (V 1)])))
    (.lit 0)

/-- join inner candidate: environment `[ctxN, cb]`, `ctxN = (ca, x, k, a, b, bag, target)` -/
def jnInnerTm : Tm :=
  .ite (.call fMem [sndN 6 (V 0), .call E4.fJoinInner [.cons (.add (comp 2 (V 0)) (.lit 1)) (comp 0 (V 0)), V 1]])
    (.letE (.call fExtract [comp 1 (V 0), comp 2 (V 0), comp 3 (V 0), comp 0 (V 0)])
      (.ite (.isNat (V 0)) (.lit 0)
        (.letE (.call fExtract [comp 1 (V 1), comp 2 (V 1), comp 4 (V 1), V 2])
          (.ite (.isNat (V 0)) (.lit 0)
            (.call E5D.fRealJoin [.add (comp 2 (V 2)) (.lit 1), comp 5 (V 2), .snd (V 1), .snd (V 0),
              sndN 6 (V 2)])))))
    (.lit 0)

/-- join outer candidate: environment `[ctxO, ca]`, `ctxO = (ctxJ, Tb)`, `ctxJ = (x, k, a, b, bag, target)` -/
def jnOuterTm : Tm :=
  .call Lib4.fFindSome [.lit fJnInner, .cons (V 1) (.fst (V 0)), .snd (V 0)]

/-- `extract`: environment `[x, k, nt, target]` -/
def extractTm : Tm :=
  .ite (.isNat (V 2)) leafTm
    (.ite (.eq (.fst (V 2)) (.lit 1))
      (.letE (.call E4.fTables [V 0, V 1, .snd (.snd (V 2))])
        (.letE (.call E4.fNtBag [.snd (.snd (V 3))])
          (.letE (.call E4.fNbrs [V 2, .fst (.snd (V 4)), V 0])
            (.call Lib4.fFindSome [.lit fInCand,
              .cons (.cons (.add (V 4) (.lit 1)) (.cons (.fst (.snd (V 5))) (V 0)))
                (.cons (V 3) (.cons (V 4) (.cons (.snd (.snd (V 5))) (.cons (V 1) (V 6))))), V 2]))))
      (.ite (.eq (.fst (V 2)) (.lit 2))
        (.letE (.call E4.fTables [V 0, V 1, .snd (.snd (V 2))])
          (.call Lib4.fFindSome [.lit fFgCand,
            .cons (V 1) (.cons (V 2) (.cons (.fst (.snd (V 3))) (.cons (.snd (.snd (V 3))) (V 4)))), V 0]))
        (.letE (.call E4.fTables [V 0, V 1, .fst (.snd (V 2))])
          (.letE (.call E4.fTables [V 1, V 2, .snd (.snd (V 3))])
            (.letE (.call E4.fNtBag [.fst (.snd (V 4))])
              (.call Lib4.fFindSome [.lit fJnOuter,
                .cons (.cons (V 3) (.cons (V 4) (.cons (.fst (.snd (V 5))) (.cons (.snd (.snd (V 5)))
                  (.cons (V 0) (V 6)))))) (V 1), V 2]))))))

def extractUnTm : Tm :=
  .call fExtract [.fst (V 0), .fst (.snd (V 0)), .fst (.snd (.snd (V 0))), .snd (.snd (.snd (V 0)))]

def extractFirstTm : Tm :=
  .letE (.call E4.fTables [V 0, V 1, V 2])
    (.ite (.isNat (V 0)) (.lit 0) (.call fExtract [V 1, V 2, V 3, .fst (V 0)]))

/-- the functions of WP E6b: ids `704 … 767` -/
def e6bTbl : ℕ → Option Tm := fun f =>
  match f with
  | 704 => some extractTm | 705 => some fgCandTm | 706 => some inCandTm | 707 => some jnOuterTm
  | 708 => some jnInnerTm | 709 => some extractUnTm | 710 => some extractFirstTm
  | _ => none

/-- the E6b layer on top of the library (ids `≥ 128`) -/
def e6bΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 e6bTbl

theorem e6bTbl_lt {f : ℕ} {b : Tm} (h : e6bTbl f = some b) : 704 ≤ f ∧ f < 768 := by
  unfold e6bTbl at h
  split at h <;> first | (simp at h; done) | omega

theorem Δ_extract : e6bΔ fExtract = some extractTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fExtract by decide)]; rfl
theorem Δ_fgCand : e6bΔ fFgCand = some fgCandTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fFgCand by decide)]; rfl
theorem Δ_inCand : e6bΔ fInCand = some inCandTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fInCand by decide)]; rfl
theorem Δ_jnOuter : e6bΔ fJnOuter = some jnOuterTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fJnOuter by decide)]; rfl
theorem Δ_jnInner : e6bΔ fJnInner = some jnInnerTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fJnInner by decide)]; rfl
theorem Δ_extractFirst : e6bΔ fExtractFirst = some extractFirstTm := by
  simp [e6bΔ, layerΔ_ge e6bTbl (show 128 ≤ fExtractFirst by decide)]; rfl

/-- The hypotheses on a table `Δ'` used by every theorem of WP E6b: it contains E1–E4 (`Ext4`), the E5 layers
(`E5W.Δ`, which contains `analyze … realJoin`) and the E6b layer. -/
structure Ext6 (Δ' : ℕ → Option Tm) : Prop where
  e4 : E4.Ext4 Δ'
  e5 : E5W.Δ ⊑ Δ'
  e6 : e6bΔ ⊑ Δ'

end E6b
end Lax117284Proofs.Treewidth.Fun
