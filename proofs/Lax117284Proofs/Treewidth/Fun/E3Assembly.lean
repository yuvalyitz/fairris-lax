import Lax117284Proofs.Treewidth.Fun.E2
import Lax117284Proofs.Treewidth.Fun.E3

set_option linter.unusedSectionVars false

/-!
# WP E3: a worked assembly with E1 + E2 — `introC` is computed in the combined table

`asmTbl = e1Tbl ∪ e2Tbl ∪ e3Tbl` (ids `128 … 157`, `160 … 182`, `256 … 332`) and `asmΔ = layerΔ Lib.Δ 128 asmTbl`.
`introC_embeds_asm` is `E3.introC_embeds` with the `norm` hypotheses discharged by `E2.norm_runs_e12` / `E2.sz_norm_le`.
The final assembler adds the functions of E4–E6 to the same union.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- the union of the E1, E2, E3 tables -/
def asmTbl : ℕ → Option Tm := orElseΔ E1.e1Tbl (orElseΔ (E2.e2Tbl E1C.fRingTypList) e3Tbl)

/-- the assembled table -/
def asmΔ : ℕ → Option Tm := layerΔ Lib.Δ 128 asmTbl

theorem e3Tbl_disj_e2 : ∀ f b, e3Tbl f = some b → E2.e2Tbl E1C.fRingTypList f = none := by
  intro f b h
  rcases hh : E2.e2Tbl E1C.fRingTypList f with _ | c
  · rfl
  · have h1 := (E2.e2Tbl_lt _ hh).2
    have h2 := (e3Tbl_lt h).1
    omega

theorem e3Tbl_disj_e1 : ∀ f b, e3Tbl f = some b → E1.e1Tbl f = none := by
  intro f b h
  rcases hh : E1.e1Tbl f with _ | c
  · rfl
  · have h1 := E1.e1Tbl_lt hh
    have h2 := (e3Tbl_lt h).1
    omega

theorem e23_disj_e1 : ∀ f b, orElseΔ (E2.e2Tbl E1C.fRingTypList) e3Tbl f = some b → E1.e1Tbl f = none := by
  intro f b h
  unfold orElseΔ at h
  rcases hh : E2.e2Tbl E1C.fRingTypList f with _ | c
  · rw [hh] at h
    exact e3Tbl_disj_e1 f b (by simpa using h)
  · exact E2.e2Tbl_disj_e1 _ f c hh

theorem asm_ext_e3tbl : e3Tbl ⊑ asmTbl :=
  Ext.trans (Ext.orElse_right e3Tbl_disj_e2) (Ext.orElse_right e23_disj_e1)

theorem asm_ext_e3 : E3C.Δ ⊑ asmΔ := ext_e3_of asm_ext_e3tbl

theorem asm_ext_e1 : E1.e1Δ ⊑ asmΔ := Ext.layer_mono (Ext.orElse_left _ _)

theorem asm_ext_e2 : E2.e2Δ E1C.fRingTypList ⊑ asmΔ :=
  Ext.layer_mono (Ext.trans (Ext.orElse_left _ _) (Ext.orElse_right e23_disj_e1))

/-- **`introC` in the assembled table**, with the cost of `E_introC`. -/
theorem introC_embeds_asm :
    Embeds asmΔ E3C.fIntroCUn (fun p : ℕ × ℕ × Finset ℕ × CT => ∃ Bs : Finset ℕ, p.2.2.2.Wf Bs p.1)
      (fun p => introC p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p => E3C.introCCost (sz p + mx p + 1) (p.2.2.2.verts.card + p.1 + 2) + 20) :=
  introC_embeds asm_ext_e3
    (fun B c s hc hB => E2.norm_runs_e12 asm_ext_e2 asm_ext_e1 B c s hc hB) E2.sz_norm_le

end E3
end Lax117284Proofs.Treewidth.Fun
