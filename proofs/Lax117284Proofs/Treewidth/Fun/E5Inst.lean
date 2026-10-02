import Lax117284Proofs.Treewidth.Fun.E5Tbl
import Lax117284Proofs.Treewidth.Fun.E2
import Lax117284Proofs.Treewidth.Fun.E3
import Lax117284Proofs.Treewidth.Fun.E3Assembly

/-!
# WP E5: discharging the external hypotheses from the theorems of E2 and E3

`E5Ext` states what E5 needs from `norm`, `key`, `domCB`, `joinC` (E2) and `introPlans` (E3) as hypothesis records.  Here they
are *instantiated* by the proved theorems `E2.norm_runs_e12`, `E2.keyLe_runs`, `E2.domC_runs_e12`, `E2.joinC_runs_e12`,
`E3C.introPlans_runs` (with abstract costs equal to the thresholds of those theorems, so that the `Runs` facts are
`Runs.mono`-weakened).  Nothing of E5 depends on this file: it is the glue for the assembler.

* `ext5_e2 L` : `Ext5 Δ'` for every `Δ'` containing `e2Δ 152` and `e1Δ`; `Ext5.PD s a b := RB s L a ∧ RB s L b`
  (run sequences of length `≤ L`).
* `extJ_e2` : `ExtJ Δ'` (`PJ kmax a b := ∃ B0, a.Wf B0 kmax ∧ b.Wf B0 kmax`).
* `extIP_e3 …` : `ExtIP Δ'` (`ip = 325`) from `E3C.introPlans_runs`, for the parameters of that theorem.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5Inst

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5

/-- costs of the E2 functions used by E5, as functions of the size bound `s` -/
def cKeyE2 (s : ℕ) : ℕ := 1000 * (s + 1) ^ 2 + 100
def cNormE2 (s : ℕ) : ℕ := 14000 * (s + 1) ^ 5
def cDomE2 (L s : ℕ) : ℕ := (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * s) + 1000

/-- `E5.Ext5` from E2: `norm` (id 166), `key` (162), `domCB` (181; run sequences of length `≤ L`). -/
def ext5_e2 (L : ℕ) {Δ' : ℕ → Option Tm} (hΔ : E2.e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') : Ext5 Δ' where
  cKey := cKeyE2
  keyLe := fun B s S a b hS ha hb hB =>
    (E2.keyLe_runs hΔ B S a b s hS ha hb (by unfold cKeyE2 at hB; omega)).mono (by unfold cKeyE2; omega)
  cNorm := cNormE2
  norm := fun B s c hc hB =>
    (E2.norm_runs_e12 hΔ hE1 B c s hc hB).mono (by
      have : 1 ≤ (s + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
      unfold cNormE2; omega)
  norm_sz := E2.sz_norm_le
  PD := fun s a b => RB s L a ∧ RB s L b
  cDom := cDomE2 L
  domC := fun B s a b hab hsa hsb hB => by
    have hcnt := count_le_sz a
    have hc : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * a.count) ≤ (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * s) :=
      Nat.mul_le_mul_left _ (by have := le_trans hcnt hsa; omega)
    have h := E2.domC_runs_e12 hΔ hE1 B L s a b hab.1 hab.2 hsa hsb (by unfold cDomE2 at hB; omega)
    exact h.mono (by unfold cDomE2; omega)

/-- `E5.ExtJ` from E2 (`joinC`, id 177): `a, b` well formed over a common boundary with entries `≤ kmax`. -/
def extJ_e2 {Δ' : ℕ → Option Tm} (hΔ : E2.e2Δ E1C.fRingTypList ⊑ Δ') (hE1 : E1.e1Δ ⊑ Δ') : ExtJ Δ' where
  PJ := fun kmax a b => ∃ B0 : Finset ℕ, a.Wf B0 kmax ∧ b.Wf B0 kmax
  cJ := fun kmax a b =>
    28000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) + 2000 * (sz a + sz b + 1) + 2000 +
      E2.R0k kmax + 1000
  joinC := fun B kmax a b hab hB => by
    obtain ⟨B0, ha, hb⟩ := hab
    have hv : a.verts = B0 := ha.verts_eq
    subst hv
    have h := E2.joinC_runs_e12 hΔ hE1 B ha hb (sz a + sz b) (by omega) (by omega) (by simpa using hB)
    refine h.mono ?_
    have hj : 14000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) ≤
        28000 * (sz a + sz b + 1) * 2 ^ (48 * (a.verts.card + kmax + 2) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- `E5.ExtIP` from `E3C.introPlans_runs` (id `325`), for the parameters of that theorem. -/
def extIP_e3 (U Q P G Ω Qc Q₀ : ℕ) (Bs : Finset ℕ) (kmax M : ℕ)
    (hQ : 1000 * (U + 1) * (U + 1) ≤ Q) (hP : Q * (3 * M) ≤ P) (hQc : 1000 * ((U + 1) * Ω) ≤ Qc)
    (hQ₀ : 100 * (P * G) + 4 * (Qc * (U + 1) * G) + 500 * ((U + 1) * G) + 1000 * (U + 1) ≤ Q₀)
    (hG : ∀ (v : ℕ) (N : Finset ℕ) (ν : CT), Good Bs ν → maxEntry ν ≤ kmax → count ν ≤ M →
      (wtopPlans v ν).length + 1 ≤ G ∧ (allChains ν.S N).length + 1 ≤ G ∧
      (attachPlans v N ν).length ≤ G ∧ (introPlans v N ν).length ≤ G)
    (hΩ : ∀ (N : Finset ℕ) (ν : CT), Good Bs ν → (chainCands ν.S N).length + 1 ≤ Ω)
    {Δ' : ℕ → Option Tm} (hΔ : E3C.Δ ⊑ Δ') : ExtIP Δ' where
  ip := E3C.fIntroPlans
  PIP := fun v N t => v ≤ U ∧ N.card ≤ U ∧ sz t ≤ U ∧ mx t ≤ U ∧ Good Bs t ∧ maxEntry t ≤ kmax ∧ count t ≤ M
  cIP := fun _ _ t => Q₀ * (3 * count t - 1) + (10 * U + 600)
  introPlans := fun B v N t ⟨hv, hN, hs, hm, hg, hk, hc⟩ hB =>
    (E3C.introPlans_runs hΔ B U Q P G Ω Qc Q₀ Bs kmax M v N hQ hP hQc hQ₀ hv hN (fun ν => hG v N ν)
      (fun ν => hΩ N ν) (by omega) t hs hm hg hk hc).mono (by omega)

/-! ## a worked assembly: E1 + E2 + E3 + E5 -/

/-- the union of the tables of E1, E2, E3 (as in `E3.Assembly`) and E5 -/
def asm5Tbl : ℕ → Option Tm := orElseΔ E3.asmTbl E5Tbl.e5Tbl

def asm5Δ : ℕ → Option Tm := layerΔ Lib.Δ 128 asm5Tbl

theorem asmTbl_lt {f : ℕ} {b : Tm} (h : E3.asmTbl f = some b) : f < 333 := by
  unfold E3.asmTbl orElseΔ at h
  rcases h1 : E1.e1Tbl f with _ | c
  · rcases h2 : E2.e2Tbl E1C.fRingTypList f with _ | c'
    · rcases h3 : E3.e3Tbl f with _ | c''
      · simp [h1, h2, h3] at h
      · have := (E3.e3Tbl_lt h3).2; omega
    · have := (E2.e2Tbl_lt _ h2).2; omega
  · have := E1.e1Tbl_lt h1; omega

end E5Inst
end Lax117284Proofs.Treewidth.Fun
