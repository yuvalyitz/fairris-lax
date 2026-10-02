import Lax117284Proofs.Treewidth.Fun.E3Final

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# WP E3: the assembled interface — table `e3Tbl` (ids `256 … 332`), `Runs` / `Embeds` for `CT.introC`

The table is `e3Tbl = orElseΔ E3A.tbl (orElseΔ E3B.tbl E3C.tbl)`; `E3C.Δ` is the layered table used in the proofs and
`ext_e3 : E3C.Δ ⊑ layerΔ Lib.Δ 128 e3Tbl`.  **How the assembler uses this.**  Let `Δ'` be a table with
`hΔ : layerΔ Lib.Δ 128 e3Tbl ⊑ Δ'` (for the assembly `layerΔ Lib.Δ 128 (orElseΔ e1Tbl (orElseΔ e2Tbl e3Tbl))` obtain `hΔ` by
`Ext.layer_mono (Ext.orElse_right …)` from the disjointness fact `e3Tbl_lt : e3Tbl f = some _ → 256 ≤ f ∧ f < 333`);
then `Ext.trans ext_e3 hΔ : E3C.Δ ⊑ Δ'` is the hypothesis of every theorem of the `E3A/E3B/E3C` layers.
The function `norm` is *not* part of this table: its id is `E3C.fNormId = 166` (= `E2.fNorm`); the theorems take its
behaviour as a hypothesis (`hnorm`), discharged by `E2.norm_runs_e12` (cost `6200 (s+1)^5`), and `hnsz` by `E2.sz_norm_le`.

| Lean function | id | arguments | theorem | cost |
|---|---|---|---|---|
| `plus1`, `List.range'` | 256, 257 | `[y]`, `[lo, n]` | `E3A.plus1_runs`, `rangeP_runs` | `12|y|+6`, `14 n+6` |
| `CT.winPlans` | 264 | `[v, lo, t]` | `E3A.winPlans_runs` | `Q (3 count t - 1) (|out|+1)`, `Q ≥ 1000 (U+1)^2` (output-sensitive) |
| `CT.kidChoices` | 268 | `[v, ks]` | `E3A.kidChoices_runs` | `Q (3 countL ks + 1) (|out|+1)` |
| `CT.wtopPlans` | 293 | `[v, t]` | `E3B.wtopPlans_runs` | `100 P (|out|+1)`, `P ≥ Q (3 count t - 1)` |
| `CT.chainCands` | 295 | `[S, N]` | `E3B.chainCands_runs` | `500 (U+1)^2 · 2^{|S \ N|}` |
| `CT.chainsGo` | 300 | `[cands, fuel, bound, chain]` | `E3B.chainsGo_runs` | `Qc (fuel+1)(2|out|+1)`, `Qc ≥ 1000 (U+1)(|cands|+1)` |
| `CT.allChains` | 301 | `[S, N]` | `E3B.allChains_runs` | `Qc (U+1)(2|out|+2)` |
| `CT.pathSubtree` | 303 | `[v, chain, M]` | `E3B.pathSubtree_runs` | `300 (U+1)^2` |
| `CT.attachPlans` | 307 | `[v, N, t]` | `E3B.attachPlans_runs` | `2 Qc (U+1) (2|allChains|+2)` |
| `CT.introKids` | 324 | `[v, N, S, y, pre, ks]` | `E3C.introKids_runs` | `Q₀ (3 countL ks + 1)` |
| `CT.introPlans` | 325 | `[v, N, t]` | `E3C.introPlans_runs` | `Q₀ (3 count t - 1)` |
| `CT.maxEntry` | 328 | `[c]` | `E3C.maxEntry_runs` | `40 sz c` |
| `CT.introC` | 331 | `[kmax, v, N, t]` | `E3C.introC_runs`, **`E3C.introC_runs_wf`** | `introCCost (U+1) (|B|+kmax+2) = 10^16 (U+1)^15 2^{128 (|B|+kmax+2)^3}` |
| `CT.introC` (packed) | 332 | `[(kmax, v, N, t)]` | `introCUn_runs`, **`introC_embeds`** | `introCCost (sz p + mx p + 1) (|verts t|+kmax+2) + 20` |
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E3

open ToVal Lax117284Proofs.Treewidth.Chars CT

/-- the E3 table (ids `256 … 332`) -/
def e3Tbl : ℕ → Option Tm := orElseΔ E3A.tbl (orElseΔ E3B.tbl E3C.tbl)

theorem e3Tbl_lt {f : ℕ} {b : Tm} (h : e3Tbl f = some b) : 256 ≤ f ∧ f < 333 := by
  unfold e3Tbl orElseΔ at h
  rcases hA : E3A.tbl f with _ | a
  · rcases hB : E3B.tbl f with _ | b'
    · rcases hC : E3C.tbl f with _ | c
      · simp [hA, hB, hC] at h
      · have := E3C.tbl_lt hC; omega
    · have := E3B.tbl_lt hB; omega
  · have := E3A.tbl_lt hA; omega

theorem ext_e3 : E3C.Δ ⊑ layerΔ Lib.Δ 128 e3Tbl := by
  intro f b h
  have hA : ∀ {c}, E3A.tbl f = some c → 256 ≤ f ∧ f < 269 := fun {c} hc => E3A.tbl_lt hc
  have hB : ∀ {c}, E3B.tbl f = some c → 288 ≤ f ∧ f < 308 := fun {c} hc => E3B.tbl_lt hc
  have hC : ∀ {c}, E3C.tbl f = some c → 320 ≤ f ∧ f < 333 := fun {c} hc => E3C.tbl_lt hc
  unfold E3C.Δ layerΔ at h
  by_cases h3 : 320 ≤ f
  · rw [if_pos h3] at h
    have hA' : E3A.tbl f = none := by
      rcases hh : E3A.tbl f with _ | c
      · rfl
      · have := hA hh; omega
    have hB' : E3B.tbl f = none := by
      rcases hh : E3B.tbl f with _ | c
      · rfl
      · have := hB hh; omega
    simp [layerΔ, e3Tbl, orElseΔ, hA', hB', h, show 128 ≤ f by omega]
  · rw [if_neg h3] at h
    unfold E3B.Δ layerΔ at h
    by_cases h2 : 288 ≤ f
    · rw [if_pos h2] at h
      have hA' : E3A.tbl f = none := by
        rcases hh : E3A.tbl f with _ | c
        · rfl
        · have := hA hh; omega
      simp [layerΔ, e3Tbl, orElseΔ, hA', h, show 128 ≤ f by omega]
    · rw [if_neg h2] at h
      unfold E3A.Δ layerΔ at h
      by_cases h1 : 128 ≤ f
      · rw [if_pos h1] at h
        simp [layerΔ, e3Tbl, orElseΔ, h, h1]
      · rw [if_neg h1] at h
        simp [layerΔ, h1, h]

/-- a table containing `e3Tbl` (ids `≥ 128`) above the library extends `E3C.Δ` -/
theorem ext_e3_of {tbl' : ℕ → Option Tm} (h : e3Tbl ⊑ tbl') : E3C.Δ ⊑ layerΔ Lib.Δ 128 tbl' :=
  Ext.trans ext_e3 (Ext.layer_mono h)

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ')
include hΔ

end proofs

end E3
end Lax117284Proofs.Treewidth.Fun
