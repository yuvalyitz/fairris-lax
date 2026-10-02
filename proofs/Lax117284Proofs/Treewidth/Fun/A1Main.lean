import Lax117284Proofs.Treewidth.Fun.A1Loop
import Lax117284Proofs.Treewidth.Fun.A2Stmt

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-!
# WP A1 (4): the entry `fMain`

`fMain [x] = outWord x` : read `n = x[0]`, `k = x[n²+1]`, run the `n` rounds from the empty tree, print `1 :: encode t` or `[0]`.
The correctness of the output (`outWord`) is *by definition* the value of `decomposeC` (the math layer proves that this
is a nice decomposition); this file only proves that the machine computes that value.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace A1

open ToVal Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT CT
open E4 (adjOfWord nOfWord ntOk)

theorem flat3_length : ∀ l : List (ℕ × ℕ × ℕ), (l.flatMap (fun r : ℕ × ℕ × ℕ => [r.1, r.2.1, r.2.2])).length
    = 3 * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp; ring

theorem encode_length (t : NT) : (NT.encode t).length = 3 * t.size + 1 := by
  unfold NT.encode
  simp only [List.length_cons, flat3_length, E6a.recs_length]

/-- the cost of the whole run -/
def cMain (n xlen M k : ℕ) : ℕ := 28 * xlen + n * cRound M k + 200 * ((n + 2) * (n + 2)) ^ 2 + 2000

section run
variable {Δ' : ℕ → Option Tm} (hΔ : E6b.Ext6 Δ') (h6a : E6a.e6aΔ ⊑ Δ') (h1 : a1Δ ⊑ Δ')
include hΔ h6a h1

theorem main_runs (B : ℕ) (x : List ℕ) (k M Mv Cm : ℕ) (hkx : k = Load.Fmt.graphK.kw x)
    (hs : (adjOfWord x).SymmOn (Finset.range (nOfWord x))) (hxM : x.length ≤ M)
    (hMs : 8 * ((nOfWord x + 1) * (nOfWord x + 1)) ≤ M) (hnM : nOfWord x + 3 ≤ M) (hnMv : nOfWord x + 3 ≤ Mv)
    (hkB : k + 2 < B) (hnn : nOfWord x * nOfWord x + 1 < B)
    (hCm : cMain (nOfWord x) x.length M k ≤ Cm) (hB : (Mv + Cm + 2) ^ 2 < B) :
    Runs Δ' B fMain [toVal x] (toVal (A2.outWord x)) Cm := by
  set n := nOfWord x with hn
  have hkeq : k = x.getD (n * n + 1) 0 := by
    rw [hkx]; simp [Load.Fmt.kw, Load.Fmt.off, hn, nOfWord]
  have hCm' := hCm
  unfold cMain at hCm'
  have hB1 : 1 < B := by
    have : 2 ≤ (Mv + Cm + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Cm + 2)]
    omega
  have hn0 : Runs Δ' B Lib1.fNth [toVal x, toVal 0] (toVal n) (14 * x.length + 9) :=
    E4.nth0_runs hΔ.e4 B x 0 hB1
  have hn1 : Runs Δ' B Lib1.fNth [toVal x, toVal (n * n + 1)] (toVal k) (14 * x.length + 9) := by
    rw [hkeq]; exact E4.nth0_runs hΔ.e4 B x (n * n + 1) hB1
  have hd := decomposeC_loop (adjOfWord x) k n 0 NT.leaf rfl
  simp only [Nat.zero_add] at hd
  have hloop := loop_runs hΔ h6a h1 B x k n M Mv Cm rfl hs hxM hMs hnM hnMv hkB
    (by omega) hB n 0 NT.leaf (by omega) (loopInv_zero (adjOfWord x) k)
  have hout : A2.outWord x = match loopC (adjOfWord x) k 0 n NT.leaf with
      | none => [0] | some t => 1 :: t.encode := by
    unfold A2.outWord
    rw [← hkx]
    have e : x.getD 0 0 = n := rfl
    rw [e, hd]
    rfl
  rw [hout]
  have hnt0 : toVal (x.getD 0 0) = Val.nat n := rfl
  rcases hr : loopC (adjOfWord x) k 0 n NT.leaf with _ | t
  · rw [hr] at hloop
    simp only [toVal_none, toVal_cons, toVal_nat] at hloop ⊢
    refine Runs.mk (h1 _ _ Δ_main) ?_
    ev_start
    · ev_run
      all_goals first | omega | simp
    · omega
  · rw [hr] at hloop
    have hcor := (decomposeC_correct_final (adjOfWord x) (Finset.range n) hs k n (Finset.Subset.refl _)).2 t
      (by rw [hd, hr])
    have hsize : t.size ≤ (n + 2) * (n + 2) := hcor.2
    have hE : 200 * t.size ^ 2 ≤ 200 * ((n + 2) * (n + 2)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 2)
    have hpos := E6a.NT.size_pos_aux t
    have hBe : 8 * t.size + 1000 < B := by
      have : 8 * t.size + 1000 ≤ Cm := by
        have : t.size ≤ t.size ^ 2 := by nlinarith
        omega
      have : Cm ≤ (Mv + Cm + 2) ^ 2 := by nlinarith [Nat.zero_le (Mv + Cm + 2)]
      omega
    have hEnc := E6a.encode_runs h6a B t hBe
    simp only [toVal_some, toVal_cons, toVal_nat] at hloop ⊢
    refine Runs.mk (h1 _ _ Δ_main) ?_
    ev_start
    · ev_run
      all_goals first | omega | simp
    · omega

end run

end A1
end Lax117284Proofs.Treewidth.Fun
