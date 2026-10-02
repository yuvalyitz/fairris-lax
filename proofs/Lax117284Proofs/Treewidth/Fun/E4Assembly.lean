import Lax117284Proofs.Treewidth.Fun.E4

set_option linter.unusedSectionVars false

/-!
# WP E4: the worked assembly with E1 + E2 + E3 + E4 — `tables` in the union table

`asm4Tbl = e1Tbl ∪ e2Tbl 152 ∪ e3Tbl ∪ e4Tbl` (ids `128 … 157`, `160 … 182`, `256 … 332`, `384 … 396`) and
`asm4Δ = layerΔ Lib.Δ 128 asm4Tbl`.  The assembler that also adds E5/E6 takes any table `tbl'` with
`E3.asmTbl ⊑ tbl'` and `e4Tbl ⊑ tbl'` (e.g. `orElseΔ asm4Tbl e5Tbl`) and gets `Ext4 (layerΔ Lib.Δ 128 tbl')` from
`Ext4.of_tbl`; then `E_tables` (and every other E4 theorem) holds in `layerΔ Lib.Δ 128 tbl'`.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

theorem e4Tbl_disj_asm : ∀ f b, e4Tbl f = some b → E3.asmTbl f = none := by
  intro f b h
  have h4 := (e4Tbl_lt h).1
  unfold E3.asmTbl orElseΔ
  rcases h1 : E1.e1Tbl f with _ | c1
  · rcases h2 : E2.e2Tbl E1C.fRingTypList f with _ | c2
    · rcases h3 : E3.e3Tbl f with _ | c3
      · simp
      · have := (E3.e3Tbl_lt h3).2; omega
    · have := (E2.e2Tbl_lt _ h2).2; omega
  · have := E1.e1Tbl_lt h1; omega

/-- any table containing the E1–E3 union and `e4Tbl` gives the hypotheses of every E4 theorem -/
theorem Ext4.of_tbl {tbl' : ℕ → Option Tm} (ha : E3.asmTbl ⊑ tbl') (h4 : e4Tbl ⊑ tbl') :
    Ext4 (layerΔ Lib.Δ 128 tbl') :=
  ⟨Ext.trans E3.asm_ext_e1 (Ext.layer_mono ha), Ext.trans E3.asm_ext_e2 (Ext.layer_mono ha),
    Ext.trans E3.asm_ext_e3 (Ext.layer_mono ha), Ext.layer_mono h4⟩

/-- the union of E1–E4 -/
def asm4Tbl : ℕ → Option Tm := orElseΔ E3.asmTbl e4Tbl

/-- the assembled table -/
def asm4Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm4Tbl

end E4
end Lax117284Proofs.Treewidth.Fun
