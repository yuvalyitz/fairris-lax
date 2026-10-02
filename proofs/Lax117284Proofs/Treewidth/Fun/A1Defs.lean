import Lax117284Proofs.Treewidth.Fun.E6bAssembly
import Lax117284Proofs.Treewidth.Fun.E6aTbl

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
