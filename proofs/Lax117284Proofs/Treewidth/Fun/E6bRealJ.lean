import Lax117284Proofs.Treewidth.Fun.E6bRealI

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (8): `realJoin` on the trees built by `extract`

`realJoin_at`: `E5D.fRealJoin` computes `realJoin (k+1) a.bag ta tb target` within `Zc^pRJ` steps, where `ta`, `tb` are
real decompositions returned by the extractions of the two children (`PTD`), by `E5D.realJoin_runs'` (the version of
`E5D.realJoin_runs` with the target-sequence length `Ly` as a separate parameter, `E6bMerge`).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT E5D

theorem cJ_le (Bs : Finset ℕ) (k : ℕ) (ca cb : CT) (hb : Bs.card ≤ k + 2) (M : ℕ) (ha : ca.Wf Bs (k + 1))
    (hbb : cb.Wf Bs (k + 1)) :
    28000 * (sz ca + sz cb + 1) * 2 ^ (48 * (ca.verts.card + (k + 1) + 2) ^ 3) + 2000 * (sz ca + sz cb + 1) + 2000 +
      E2.R0k (k + 1) + 1000 ≤ cJb M k := by
  have hsa := wf_sz_le hb ha
  have hsb := wf_sz_le hb hbb
  have hv : ca.verts = Bs := ha.verts_eq
  have hR := E2.join_R0_bound Bs.card (k + 1)
  have hpos : 0 < (2 * Bs.card + 2) ^ 2 := pow_pos (by omega) 2
  have hR1 : E2.R0k (k + 1) ≤ 6000 * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) :=
    le_trans (Nat.le_mul_of_pos_left (E2.R0k (k + 1)) hpos) hR
  have hE : 48 * (Bs.card + (k + 1) + 2) ^ 3 ≤ 1296 * Yk k := by
    unfold Yk
    have h1 : Bs.card + (k + 1) + 2 ≤ 3 * (k + 2) := by omega
    have h2 : (Bs.card + (k + 1) + 2) ^ 3 ≤ (3 * (k + 2)) ^ 3 := Nat.pow_le_pow_left h1 3
    calc 48 * (Bs.card + (k + 1) + 2) ^ 3 ≤ 48 * (3 * (k + 2)) ^ 3 := Nat.mul_le_mul_left _ h2
      _ = 1296 * (k + 2) ^ 3 := by ring
  have hP : 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤ 2 ^ (1296 * Yk k) := Nat.pow_le_pow_right (by norm_num) hE
  rw [hv]
  unfold cJb
  have h3 : sz ca + sz cb + 1 ≤ 256 * Yk k + 1 := by unfold Yk; omega
  have h4 : 28000 * (sz ca + sz cb + 1) * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤
      28000 * (256 * Yk k + 1) * 2 ^ (1296 * Yk k) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) hP
  have h5 : 2000 * (sz ca + sz cb + 1) ≤ 2000 * (256 * Yk k + 1) := Nat.mul_le_mul_left _ h3
  have h6 : 6000 * 2 ^ (48 * (Bs.card + (k + 1) + 2) ^ 3) ≤ 6000 * 2 ^ (1296 * Yk k) := Nat.mul_le_mul_left _ hP
  omega

theorem realJoin_at {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ) {adj : Adj} {k M : ℕ} {a b : NT}
    (hg : (NT.join a b).Good adj) (hw : (NT.join a b).toRT.Width (k + 1))
    {ta tb : RT} (hta : PTD adj a k ta) (htb : PTD adj b k tb) {target : CT}
    (htg : target ∈ tables adj k (NT.join a b))
    (hsza : sz ta ≤ (2 * k + 8) * (2 * k + 6) * a.size) (hszb : sz tb ≤ (2 * k + 8) * (2 * k + 6) * b.size)
    (haM : a.size ≤ M) (hbM : b.size ≤ M) (hB : (Zc M k ^ pRJ + 2) ^ 2 < B) :
    Runs Δ' B E5D.fRealJoin [toVal (k + 1), toVal a.bag, toVal ta, toVal tb, toVal target]
      (toVal (realJoin (k + 1) a.bag ta tb target)) (Zc M k ^ pRJ) := by
  have hg0 := hg
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, -, hga, hgb, -⟩ := hg'
  have hwa : a.toRT.Width (k + 1) := NT.width_join_left hw
  have hb : a.bag.card ≤ k + 2 := bag_card_le_of_width hwa
  have hcova : a.bag ⊆ ta.verts := by
    rw [hta.1.verts_eq]; intro x hx; exact NT.bag_subset_under a hx
  have hcovb : a.bag ⊆ tb.verts := by
    rw [htb.1.verts_eq, hab]; intro x hx; exact NT.bag_subset_under b hx
  have wfa : (ta.char a.bag).Wf a.bag (k + 1) := char_wf hta.1.conn hcova hta.2
  have wfb : (tb.char a.bag).Wf a.bag (k + 1) := char_wf htb.1.conn hcovb htb.2
  have wft : target.Wf a.bag (k + 1) := tables_wf hg0 target htg
  have hsI := bag_sz_num M k
  have hRBd : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag), d.Wf a.bag (k + 1) :=
    fun d hd => CT.joinC_wf wfa wfb hd
  have hcj : (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1).cJ (k + 1) (ta.char a.bag) (tb.char a.bag) ≤ cJb M k :=
    cJ_le a.bag k _ _ hb M wfa wfb
  have hBsum := numRJ_B M k _ hcj
  have hB2 : 200000 + 100000 * (sI M k + 1) ^ 2 +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cKey (6 * sI M k) +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cNorm (5 * sI M k) +
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).cDom (sI M k) +
      (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1).cJ (k + 1) (ta.char a.bag) (tb.char a.bag) < B := by
    have : Zc M k ^ pRJ < B := by nlinarith [Nat.zero_le (Zc M k ^ pRJ)]
    exact lt_of_le_of_lt hBsum this
  have hPD : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag),
      (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1).PD (sI M k) d target := by
    intro d hd
    have hwd := hRBd d hd
    refine ⟨?_, ?_⟩
    · exact (RB.of_good hwd.good hwd.bounded).mono (by omega) (by unfold LrJ; omega)
    · exact (RB.of_good wft.good wft.bounded).mono (by omega) (by unfold LrJ; omega)
  have hRB : ∀ d ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag), CT.RB (5 * sI M k) (LrJ k) d := by
    intro d hd
    have hwd := hRBd d hd
    exact (RB.of_good hwd.good hwd.bounded).mono (by omega) (by unfold LrJ; omega)
  have h := E5D.realJoin_runs' (Ext.trans E5W.extD hΔ.e5) B (E5Inst.ext5_e2 (LrJ k) hΔ.e4.e2 hΔ.e4.e1)
    (E5Inst.extJ_e2 hΔ.e4.e2 hΔ.e4.e1) (k + 1) a.bag ta tb target (sI M k) (k + 1) (LrJ k) (LenJ k)
    (by rw [sz_finset]; omega) (le_trans hsza (t0_sz_num M k _ haM))
    (le_trans hszb (t0_sz_num M k _ hbM))
    (le_trans (tables_sz_le hg0 hw target htg) (tg_sz_num M k)) (by omega)
    hta.2 htb.2 ⟨a.bag, wfa, wfb⟩
    (joinC_length_le_k hb wfa wfb)
    (fun d hd => le_trans (wf_sz_le hb (hRBd d hd)) (tg_sz_num M k)) hPD hRB hB2
  exact h.mono (numRJ_cost M k _ hcj)

end E6b
end Lax117284Proofs.Treewidth.Fun
