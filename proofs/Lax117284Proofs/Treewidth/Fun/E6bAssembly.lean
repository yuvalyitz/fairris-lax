import Lax117284Proofs.Treewidth.Fun.E6bFinal

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
