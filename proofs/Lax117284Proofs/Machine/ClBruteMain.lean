import Lax117284Proofs.Machine.ClBruteBody

/-!
The whole search, and its correctness: `bfans` ends `1` exactly when a fair schedule exists.
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

variable {B k : ℕ} {x : List ℕ} {I : Instance}

/-- The cost of the loop over all vectors. -/
def costLoop (m n : ℕ) : ℕ := (1 + 3 + costBody m n) * 2 ^ (m * n) + 1 + 3

/-- **The cost of the brute force**: three initialisations and the loop. -/
def bruteCost (m n : ℕ) : ℕ := 4 + (2 + (2 + costLoop m n))

lemma dn_zero_of_true {σ : Env}
    (h : (Cond.eq (V "bfdn") (lit 0)).evalB B σ = some true) : σ.vars "bfdn" = 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

lemma dn_ne_of_false {σ : Env}
    (h : (Cond.eq (V "bfdn") (lit 0)).evalB B σ = some false) : σ.vars "bfdn" ≠ 0 := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem loop_spec (hb : Bd B x I k) :
    Spec B (fun σ => J x I k σ) (.while (.eq (V "bfdn") (lit 0)) bodyCom)
      (fun _ σ' => J x I k σ' ∧ (Cond.eq (V "bfdn") (lit 0)).evalB B σ' = some false)
      (costLoop I.days I.clients) := by
  have hsz : (Cond.eq (V "bfdn") (lit 0)).size = 3 := rfl
  refine Spec.while_count (J x I k) (Vm I) (costBody I.days I.clients) ?_
    ((body_spec hb).pre (fun σ h => ⟨h.1, dn_zero_of_true h.2⟩)) (fun σ h => h) ?_
  · rintro σ ⟨f, hctx, hans, hdn, -, -⟩
    exact ⟨_, evalB_condEq (evalB_var (by have := hb.big; omega))
      (evalB_lit (by have := hb.big; omega))⟩
  · rintro σ ⟨f, hctx, -⟩
    rw [hsz, costLoop]
    have hV : Vm I σ ≤ 2 ^ (I.days * I.clients) := by
      unfold Vm; split_ifs
      · exact Nat.sub_le _ _
      · exact Nat.zero_le _
    have := Nat.mul_le_mul_left (1 + 3 + costBody I.days I.clients) hV
    omega

end Lax117284Proofs.Machine.ClBrute
