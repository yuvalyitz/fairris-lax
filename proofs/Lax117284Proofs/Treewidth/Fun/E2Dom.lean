import Lax117284Proofs.Treewidth.Fun.E2Join1

/-!
# WP E2 (7): `domCB` as an F-function (used by `realIntro` / `realJoin`)

`domCB a b` (`DomC`-decision).  Cost `C · wt a` with `C = 60·3^(2L) + 60 s + 300` when every run sequence of `a`, `b` has length `≤ L`
(`CT.RB s L`) and `sz ≤ s`; the exponential factor is `E1A.domB`'s (`60·3^(|y|+|y'|)`, as the Lean recursion).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

section dom
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (hE : E1A.Δ ⊑ Δ') (B : ℕ)
include hΔ hE

theorem domCL_runs_aux (Cc : ℕ) (hB1 : 1 < B) (ks : List CT) : ∀ ks' : List CT,
    (∀ k ∈ ks, ∀ k' ∈ ks', Runs Δ' B fDomC [toVal k, toVal k'] (toVal (domCB k k')) (Cc * wt k)) →
    Runs Δ' B fDomCL [toVal ks, toVal ks'] (toVal (domCBL ks ks'))
      ((ks.map (fun k => Cc * wt k)).sum + 20 * (ks.length + 1) + 10) := by
  induction ks with
  | nil =>
    intro ks' _
    refine Runs.mk (hΔ _ _ (Δ_domCL rid)) ?_
    cases ks' with
    | nil =>
      have : domCBL [] [] = true := rfl
      rw [this]
      simp only [toVal_nil, toVal_true]
      ev_start
      · ev_run
      · simp
    | cons k' ks' =>
      have : domCBL [] (k' :: ks') = false := rfl
      rw [this]
      simp only [toVal_nil, toVal_cons, toVal_false]
      ev_start
      · ev_run
      · simp
  | cons k ks ih =>
    intro ks' hf
    refine Runs.mk (hΔ _ _ (Δ_domCL rid)) ?_
    cases ks' with
    | nil =>
      have : domCBL (k :: ks) [] = false := rfl
      rw [this]
      simp only [toVal_nil, toVal_cons, toVal_false]
      ev_start
      · ev_run
      · simp
    | cons k' ks' =>
      have h1 := hf k (by simp) k' (by simp)
      have h2 := ih ks' (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      by_cases hd : domCB k k' = true
      · have : domCBL (k :: ks) (k' :: ks') = domCBL ks ks' := by simp [domCBL, hd]
        rw [this]
        simp only [hd] at h1
        simp only [toVal_cons]
        ev_start
        · ev_run
        · simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith
      · have hd' : domCB k k' = false := by simpa using hd
        have : domCBL (k :: ks) (k' :: ks') = false := by simp [domCBL, hd']
        rw [this]
        simp only [hd'] at h1
        simp only [toVal_cons]
        ev_start
        · ev_run
        · simp only [List.map_cons, List.sum_cons, List.length_cons]; nlinarith [Nat.zero_le (List.map (fun k => Cc * wt k) ks).sum]

theorem domC_runs_aux (Cc D0 L s : ℕ) (hC : 30 * s + D0 + 100 ≤ Cc) (hB1 : 1000 < B)
    (hdom : ∀ y y' : List ℕ, y.length ≤ L → y'.length ≤ L →
      Runs Δ' B E1A.fDomB [toVal y, toVal y'] (toVal (domB y y')) D0) (a : CT) :
    ∀ b : CT, RB s L a → RB s L b → sz a ≤ s → sz b ≤ s →
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) (Cc * wt a) := by
  induction a using CT.ind with
  | h S y ks ih =>
    intro b hra hrb hsa hsb
    obtain ⟨S', y', ks'⟩ := b
    have hts := tree_step ks (fun _ => 0) Cc 0 0 (fun _ _ => le_refl _)
    simp only [pow_zero, mul_one] at hts
    have hwt := wt_node S y ks
    have hsS := sz_S_le S y ks
    have hm : ks.length ≤ s := by have := sz_ks_le S y ks; have := length_le_sz ks; omega
    have hlt : fDomCL < B := by show 182 < B; omega
    have hlt2 : E1A.fDomB < B := by show 135 < B; omega
    refine Runs.mk (hΔ _ _ (Δ_domC rid)) ?_
    by_cases hS : S = S'
    · subst hS
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B (by omega) S S true (by simp)
      have hmin := min_le_left (sz S) (sz S)
      have hd := hdom y y' hra.2.1 hrb.2.1
      cases hb : domB y y' with
      | false =>
        have : domCB (node S y ks) (node S y' ks') = false := by simp [domCB, hb]
        rw [this]
        rw [hb] at hd
        simp only [toVal_ct, toVal_false]
        ev_start
        · ev_run
        · rw [hwt]; nlinarith
      | true =>
        rw [hb] at hd
        have hL := domCL_runs_aux hΔ hE B Cc (by omega) ks ks' (fun k hk k' hk' =>
          ih k hk k' (RB.kids hra k hk) (RB.kids hrb k' hk')
            (by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
            (by have := sz_le_of_mem_kids (S := S) (y := y') hk'; omega))
        have : domCB (node S y ks) (node S y' ks') = domCBL ks ks' := by simp [domCB, hb]
        rw [this]
        simp only [toVal_ct, toVal_true] at *
        ev_start
        · ev_run
        · rw [hwt]; nlinarith
    · have : domCB (node S y ks) (node S' y' ks') = false := by simp [domCB, hS]
      rw [this]
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B (by omega) S S' false (by simp [hS])
      have hmin := min_le_left (sz S) (sz S')
      simp only [toVal_ct, toVal_false]
      ev_start
      · ev_run
      · rw [hwt]; nlinarith

/-- **`domCB` as an F-function**: cost `(30 s + 60·3^(2L) + 100) · 2 count a`, where `L` bounds the run sequences of both
characteristics (`CT.RB s L`, e.g. `RB.of_good` with `L = 2 kmax + 1`) and `sz ≤ s`. -/
theorem domC_runs (L s : ℕ) (a b : CT) (hla : RB s L a) (hlb : RB s L b) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) + 1000 < B) :
    Runs Δ' B fDomC [toVal a, toVal b] (toVal (domCB a b)) ((30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a)) := by
  have hcnt := count_ge_one a
  have hP : 1 ≤ 3 ^ (2 * L) := Nat.one_le_pow _ _ (by omega)
  have hB1 : 1000 < B := by
    have : 100 ≤ (30 * s + 60 * 3 ^ (2 * L) + 100) * (2 * count a) := by nlinarith
    omega
  have h := domC_runs_aux hΔ hE B (30 * s + 60 * 3 ^ (2 * L) + 100) (60 * 3 ^ (2 * L)) L s le_rfl hB1
    (fun y y' hy hy' => (E1A.domB_runs hE B (by omega) (y.length + y'.length) y y' rfl).mono
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))) a b hla hlb hsa hsb
  refine h.mono ?_
  have : wt a ≤ 2 * count a := by unfold wt; omega
  exact Nat.mul_le_mul_left _ this

end dom

end E2
end Lax117284Proofs.Treewidth.Fun
