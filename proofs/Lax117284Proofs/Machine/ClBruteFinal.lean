import Lax117284Proofs.Machine.ClBruteMain

/-!
The brute force decides whether a fair schedule exists, in time `2 ^ (m * n)` times a
polynomial.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-! ### The cost -/

lemma costBody_le (m n : ℕ) : costBody m n ≤ 1000 * (m * n + n + 2) ^ 2 := by
  have hfe : costFeas m n = 69 * (m * n) * n + 37 * (m * n) + 18 * m + 6 := by
    unfold costFeas; ring
  have hfa : costFair m n = 17 * (m * n) + 32 * n + 6 := by
    unfold costFair; ring
  have ho : costOdo m n = 24 * (m * n) + 8 := by unfold costOdo; ring
  unfold costBody costEval costFeasG
  rw [hfe, hfa, ho]
  have hm : 0 < n → m ≤ m * n := fun h => Nat.le_mul_of_pos_right m h
  generalize m * n = p at *
  by_cases hn : n = 0
  · subst hn; simp only [if_true]; nlinarith
  · have hm := hm (Nat.pos_of_ne_zero hn)
    rw [if_neg hn]
    nlinarith

theorem bruteCost_le (m n : ℕ) :
    bruteCost m n ≤ 5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2 := by
  have hb := costBody_le m n
  have hY : 1 ≤ 2 ^ (m * n) := Nat.one_le_two_pow
  unfold bruteCost costLoop
  generalize 2 ^ (m * n) = Y at *
  generalize m * n = p at *
  have hN : 4 ≤ (p + n + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (show 2 ≤ p + n + 2 by omega) 2
    simpa using this
  generalize (p + n + 2) ^ 2 = N at *
  generalize costBody m n = c at *
  nlinarith

/-! ### The correctness -/

open Classical in
theorem brute_core (hb : Bd B x I k) :
    Spec B (fun σ => σ.arrs "X" = x ∧ σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧
        σ.vars "k" = k ∧ σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0) bruteCom
      (fun _ σ' => σ'.vars "bfans" = (if I.HasKFairSchedule k then 1 else 0) ∧
        σ'.arrs "X" = x ∧ σ'.vars "n" = I.clients ∧ σ'.vars "m" = I.days ∧ σ'.vars "k" = k)
      (bruteCost I.days I.clients) := by
  intro σ ⟨hX, hn, hm, hk, hsc⟩
  have hbig := hb.big
  have hmn := hb.mnB
  have hs1 : ((V "n").mul (V "m")).size = 3 := rfl
  have hs2 : (lit 0).size = 1 := rfl
  obtain ⟨σ1, hr1, rfl⟩ := (Spec.assign (B := B) (x := "bfmn") (e := .mul (V "n") (V "m"))
    (f := fun σ => σ.vars "n" * σ.vars "m")
    (P := fun σ => σ.vars "n" = I.clients ∧ σ.vars "m" = I.days)
    (fun σ h => evalB_bin (evalB_var (by rw [h.1]; exact hb.nB)) (evalB_var (by rw [h.2]; exact hb.mB))
      (by rw [Bop.apply_mul, h.1, h.2, Nat.mul_comm]; omega))) σ ⟨hn, hm⟩
  obtain ⟨σ2, hr2, rfl⟩ := (Spec.assign (B := B) (x := "bfans") (e := lit 0) (f := fun _ => 0)
    (P := fun _ => True) (fun _ _ => evalB_lit (by omega))) (σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")) trivial
  obtain ⟨σ3, hr3, rfl⟩ := (Spec.assign (B := B) (x := "bfdn") (e := lit 0) (f := fun _ => 0)
    (P := fun _ => True) (fun _ _ => evalB_lit (by omega)))
    ((σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")).setVar "bfans" 0) trivial
  obtain ⟨σ', hrun, ⟨f', hc', hans', hdn', h0', h1'⟩, hfalse⟩ := loop_spec hb
    (((σ.setVar "bfmn" (σ.vars "n" * σ.vars "m")).setVar "bfans" 0).setVar "bfdn" 0)
    ⟨fun _ => 0, ⟨by simpa [Env.setVar] using hX, by simp [Env.setVar, hn], by simp [Env.setVar, hm],
      by simp [Env.setVar, hk], by simp [Env.setVar, hn, hm, Nat.mul_comm],
      by simp [Env.setVar, hsc, replicate_eq_arrOf], fun _ _ => Nat.zero_le _⟩,
      by simp [Env.setVar], by simp [Env.setVar], by simp [Env.setVar, enc], by simp [Env.setVar]⟩
  have hdn1 : σ'.vars "bfdn" = 1 := by have := dn_ne_of_false hfalse; omega
  have hiff : σ'.vars "bfans" = 1 ↔ I.HasKFairSchedule k := by
    rw [h1' hdn1, ← hasK_iff]
  refine ⟨σ', (hr1.seq (hr2.seq (hr3.seq hrun))).mono (le_of_eq (by simp only [hs1, hs2]; rfl)),
    ?_, hc'.hx, hc'.hn, hc'.hm, hc'.hk⟩
  split_ifs with hK
  · exact hiff.mpr hK
  · have : σ'.vars "bfans" ≠ 1 := fun h => hK (hiff.mp h)
    omega

open Classical in
/-- **The brute force decides the existence of a fair schedule.** Started on the word `x`, which
encodes the instance `I` and the fairness parameter `k`, with `bfsc` all zeros, `bruteCom` leaves
`1` in `bfans` if the instance has a `k`-fair schedule and `0` otherwise, at a cost of
`bruteCost m n`, which is at most `5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2` (`bruteCost_le`). -/
theorem brute_spec (I : Instance) (x : List ℕ) (k B : ℕ) (hdec : EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => σ.arrs "X" = x ∧ σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧
        σ.vars "k" = k ∧ σ.arrs "bfsc" = List.replicate (I.days * I.clients) 0)
      bruteCom
      (fun σ σ' => σ'.vars "bfans" = (if I.HasKFairSchedule k then 1 else 0) ∧ σ'.arrs "X" = x ∧
        σ'.vars "n" = σ.vars "n" ∧ σ'.vars "m" = σ.vars "m" ∧ σ'.vars "k" = σ.vars "k" ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (bruteCost I.days I.clients) := by
  refine ((brute_core (B := B) (x := x) (I := I) (k := k) ⟨hdec, hB, hX⟩).frame).post ?_
  rintro σ σ' ⟨-, hn, hm, hk, -⟩ ⟨⟨hans, hx, hn', hm', hk'⟩, -, -, hrd, hwr⟩
  exact ⟨hans, hx, by rw [hn', hn], by rw [hm', hm], by rw [hk', hk], hrd (by decide),
    hwr (by decide)⟩

end Lax117284Proofs.Machine.ClBrute
