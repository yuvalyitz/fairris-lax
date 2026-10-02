import Lax117284Proofs.Treewidth.Fun.E5W

/-!
# WP E5: the table `e5Tbl` (ids `448 … 535`) and its assembly

`e5Tbl : ℕ → Option Tm` is the union of the layer tables `E5A … E5W` (disjoint ids), `e5Δ = layerΔ e1Δ 448 e5Tbl`
(the E1 functions are contained in it: E5 calls `typical`, `witnesses`, `findPath`).  `E5W.Δ = e5Δ` (`e5_eq`).

**How the assembler uses it.**  Let `T` be the assembled table (`layerΔ Lib.Δ 128 T` the assembled Δ).  If `e1Tbl ⊑ T` and
`e5Tbl ⊑ T` then `e5Δ ⊑ layerΔ Lib.Δ 128 T` (`ext_asm`; `ext_orElse_left/right` for the two usual shapes of `T`), and every
theorem `embeds_* : … Δ' …` of `E5W`, stated for `Δ' ⊒ E5W.Δ`, applies to `Δ' := layerΔ Lib.Δ 128 T`.  External functions:
`CT.norm` (id `E5.idNorm = 166`), `decide (key S a ≤ key S b)` (`E5.idKeyLe = 162`), `CT.domCB` (`E5.idDomC = 181`),
`CT.joinC` (`E5.idJoinC = 177`) come from E2, `CT.introPlans` from E3 (its id is `ExtIP.ip`); they are hypotheses
(`Ext5`, `ExtJ`, `ExtIP` of `E5Ext`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5Tbl

/-- the functions of WP E5: ids `448 … 535`. -/
def e5Tbl : ℕ → Option Tm := fun f =>
  if 530 ≤ f then E5W.tbl f else if 520 ≤ f then E5D.tbl f else if 500 ≤ f then E5R.tbl f
  else if 490 ≤ f then E5C3.tbl f else if 480 ≤ f then E5C2.tbl f else if 470 ≤ f then E5C1.tbl f
  else if 460 ≤ f then E5B.tbl f else E5A.tbl f

/-- E1's library plus the E5 functions. -/
def e5Δ : ℕ → Option Tm := layerΔ E1.e1Δ 448 e5Tbl

theorem e5_eq : E5W.Δ = e5Δ := by
  funext f
  simp only [E5W.Δ, E5D.Δ, E5R.Δ, E5C3.Δ, E5C2.Δ, E5C1.Δ, E5B.Δ, E5A.Δ, e5Δ, e5Tbl, layerΔ]
  by_cases h1 : 530 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, this]
  by_cases h2 : 520 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, this]
  by_cases h3 : 500 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, this]
  by_cases h4 : 490 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, this]
  by_cases h5 : 480 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, this]
  by_cases h6 : 470 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, h6, this]
  by_cases h7 : 460 ≤ f
  · have : 448 ≤ f := by omega
    simp [h1, h2, h3, h4, h5, h6, h7, this]
  by_cases h8 : 448 ≤ f
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]
  · simp [h1, h2, h3, h4, h5, h6, h7, h8]

/-- the last layer is the whole E5 table. -/
theorem ext : E5W.Δ ⊑ e5Δ := by rw [e5_eq]; exact Ext.refl _

theorem extE1 : E1.e1Δ ⊑ e5Δ := Ext.trans E5W.extE1 ext

/-- ids of the E5 table: `448 ≤ f < 536` -/
theorem e5Tbl_range {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : 448 ≤ f ∧ f < 536 := by
  have h' : e5Δ f = some b := by
    unfold e5Δ layerΔ
    by_cases h448 : 448 ≤ f
    · simp [h448, h]
    · exfalso
      simp only [e5Tbl] at h
      split_ifs at h <;> first | omega | (unfold E5A.tbl at h; split at h <;> first | omega | simp at h)
  rw [← e5_eq] at h'
  have := E5W.Δ_lt h'
  refine ⟨?_, by simpa [E5W.size] using this⟩
  by_contra hf
  simp only [e5Tbl] at h
  split_ifs at h <;> first | omega | (unfold E5A.tbl at h; split at h <;> first | omega | simp at h)

theorem e5Tbl_ge {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : 448 ≤ f := (e5Tbl_range h).1
theorem e5Tbl_lt {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : f < 536 := (e5Tbl_range h).2

/-- **assembly**: if the assembled table `T` contains `e1Tbl` and `e5Tbl`, `e5Δ` is contained in `layerΔ Lib.Δ 128 T`. -/
theorem ext_asm (T : ℕ → Option Tm) (h1 : E1.e1Tbl ⊑ T) (h5 : e5Tbl ⊑ T) : e5Δ ⊑ layerΔ Lib.Δ 128 T := by
  intro f b h
  unfold e5Δ layerΔ at h
  by_cases h448 : 448 ≤ f
  · simp only [h448, if_true] at h
    have := h5 f b h
    have h128 : 128 ≤ f := by omega
    simp [layerΔ, h128, this]
  · simp only [h448, if_false] at h
    unfold E1.e1Δ Lib.extend layerΔ at h
    by_cases h128 : 128 ≤ f
    · simp only [h128, if_true] at h
      simp [layerΔ, h128, h1 f b h]
    · simp only [h128, if_false] at h
      simp [layerΔ, h128, h]

/-- the assembly `layerΔ Lib.Δ 128 (orElseΔ (orElseΔ e1Tbl e5Tbl) tbl₂)` -/
theorem ext_orElse_left (tbl₂ : ℕ → Option Tm) :
    e5Δ ⊑ layerΔ Lib.Δ 128 (orElseΔ (orElseΔ E1.e1Tbl e5Tbl) tbl₂) :=
  ext_asm _ (Ext.trans (Ext.orElse_left _ _) (Ext.orElse_left _ _))
    (Ext.trans (Ext.orElse_right (fun f b h => by
      have := e5Tbl_ge h
      by_contra hne
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
      have := E1.e1Tbl_lt hc
      omega)) (Ext.orElse_left _ _))

/-- `e1Tbl` and `e5Tbl` have no id in common -/
theorem e5_e1_disjoint {f : ℕ} {b : Tm} (h : e5Tbl f = some b) : E1.e1Tbl f = none := by
  by_contra hne
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
  have := E1.e1Tbl_lt hc
  have := e5Tbl_ge h
  omega

/-- the assembly `layerΔ Lib.Δ 128 (orElseΔ tbl₁ (orElseΔ e1Tbl e5Tbl))`, `tbl₁` having no id of `e1Tbl`, `e5Tbl` -/
theorem ext_orElse_right (tbl₁ : ℕ → Option Tm) (hd1 : ∀ f b, E1.e1Tbl f = some b → tbl₁ f = none)
    (hd5 : ∀ f b, e5Tbl f = some b → tbl₁ f = none) :
    e5Δ ⊑ layerΔ Lib.Δ 128 (orElseΔ tbl₁ (orElseΔ E1.e1Tbl e5Tbl)) :=
  ext_asm _
    (fun f b h => by simp [orElseΔ, hd1 f b h, h])
    (fun f b h => by simp [orElseΔ, hd5 f b h, e5_e1_disjoint h, h])

end E5Tbl
end Lax117284Proofs.Treewidth.Fun
