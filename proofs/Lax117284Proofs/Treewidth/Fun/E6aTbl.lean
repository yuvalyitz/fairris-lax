import Lax117284Proofs.Treewidth.Fun.E5Inst
import Lax117284Proofs.Treewidth.Fun.E6aTop

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

theorem e6aTbl_disj_asm5 : ∀ f b, e6aTbl f = some b → E5Inst.asm5Tbl f = none := by
  intro f b h
  have h1 := (e6aTbl_range h).1
  unfold E5Inst.asm5Tbl orElseΔ
  rcases hh : E3.asmTbl f with _ | c
  · rcases h2 : E5Tbl.e5Tbl f with _ | c'
    · simp [hh, h2]
    · have := E5Tbl.e5Tbl_lt h2; omega
  · have := E5Inst.asmTbl_lt hh; omega

theorem asm6_ext_e6a : e6aΔ ⊑ asm6Δ := ext_asm _ (Ext.orElse_right e6aTbl_disj_asm5)

theorem asm6_ext_asm5 : E5Inst.asm5Δ ⊑ asm6Δ := Ext.layer_mono (Ext.orElse_left _ _)

theorem asm6_ext_e1 : E1.e1Δ ⊑ asm6Δ := Ext.trans E5Inst.asm5_ext_e1 asm6_ext_asm5
theorem asm6_ext_e2 : E2.e2Δ E1C.fRingTypList ⊑ asm6Δ := Ext.trans E5Inst.asm5_ext_e2 asm6_ext_asm5
theorem asm6_ext_e3 : E3C.Δ ⊑ asm6Δ := Ext.trans E5Inst.asm5_ext_e3 asm6_ext_asm5
theorem asm6_ext_e5 : E5W.Δ ⊑ asm6Δ := Ext.trans E5Inst.asm5_ext_e5 asm6_ext_asm5

open Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees ToVal

/-- **`compress`, worked example**: in the assembled table -/
theorem compress_embeds_asm6 : Embeds asm6Δ fCompress (fun _ : RT => True) compress
    (fun t => 400 * (sz t + sz (compress t) + 1) ^ 3) := embeds_compress asm6_ext_e6a

/-- **`niceOf` on connected trees, worked example** -/
theorem niceOf_embeds_asm6 : Embeds asm6Δ fNiceOf (fun t : RT => t.Conn) niceOf
    (fun t => 8000 * (sz t + 2) ^ 5) := embeds_niceOf_conn asm6_ext_e6a

theorem niceOf_out_embeds_asm6 : Embeds asm6Δ fNiceOf (fun _ : RT => True) niceOf
    (fun t => 2000 * (sz t + sz (niceOf t) + 1) ^ 3) := embeds_niceOf asm6_ext_e6a

theorem addEverywhere_embeds_asm6 : Embeds asm6Δ fAddEvP (fun _ : ℕ × NT => True)
    (fun p => NT.addEverywhere p.1 p.2) (fun p => 100 * (sz p + sz (NT.addEverywhere p.1 p.2) + 1)) :=
  embeds_addEverywhere asm6_ext_e6a

theorem encode_embeds_asm6 : Embeds asm6Δ fEncode (fun _ : NT => True) NT.encode
    (fun nt => 300 * (sz nt + sz nt.encode + 1) ^ 2) := embeds_encode asm6_ext_e6a

/-- the earlier worked example (`analyze`) still holds in the enlarged table -/
theorem analyze_embeds_asm6 (L : ℕ) :
    Embeds asm6Δ E5W.fAnalyzeP (fun _ : Finset ℕ × RT => True) (fun a => analyze a.1 a.2)
      (E5W.costAnalyze (E5Inst.ext5_e2 L asm6_ext_e2 asm6_ext_e1)) :=
  E5W.embeds_analyze asm6_ext_e5 (E5Inst.ext5_e2 L asm6_ext_e2 asm6_ext_e1)

end E6a
end Lax117284Proofs.Treewidth.Fun
