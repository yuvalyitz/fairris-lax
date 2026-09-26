import Lax117284Proofs.Machine.TwAnswer

/-!
The answer: the correctness.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- What the answer costs. -/
def answerCost (P : Params) : ℕ := 60 + ((20 + 10 + 4) * P.tabs + 6) + 10

open Classical in
theorem answerCom_run (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs P.N σ) :
    ∃ σ', Run B answerCom σ σ' (answerCost P) ∧
      σ'.out = σ.out ++ [if P.I.HasKFairSchedule P.kk then 1 else 0] := by
  have hNpos : 0 < P.N := P.hD.nonempty
  obtain ⟨σ1, r1, e1⟩ := answerPre_run hC hN
  have hle := bagL_len_le P (j := P.N - 1) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D (P.N - 1)).length) ≤ P.tabs := pow_le_tabs P hle
  have hNt : P.N * P.tabs = (P.N - 1) * P.tabs + P.tabs := by
    have : P.N = (P.N - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  have hTBl : (σ1.arrs "TB").length = (σ.arrs "TB").length := by
    rw [show σ1.arrs = σ.arrs by rw [e1]; simp [preState]]
  have hbs1 : σ1.vars "bs" = (P.N - 1) * P.tabs := by rw [e1]; simp [preState]
  have hfn1 : σ1.vars "fn" = 2 ^ (P.m * (bagL P.D (P.N - 1)).length) := by
    rw [e1]; simp [preState]
  have hac1 : σ1.vars "ac" = 0 := by rw [e1]; simp [preState]
  have har1 : σ1.arrs = σ.arrs := by rw [e1]; simp [preState]
  have ho1 : σ1.out = σ.out := by rw [e1]; simp [preState]
  have hrowT : ∀ j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length),
      (σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0 = tbv P.I P.kk P.D (P.N - 1) j := by
    intro j hj
    rw [har1]; exact hN.tb (P.N - 1) (by omega) j (by rw [bpow]; exact hj)
  have hf := fLoop_spec (B := B) "so" "fn" "ac" orBody ["so", "ac"]
    (fun j a => if j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length) then Nat.lor a
      ((σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0) else a)
    (fun _ a => a ≤ 1) 20 (2 ^ (P.m * (bagL P.D (P.N - 1)).length)) σ1 (by simp) (by simp)
    (by decide) hfn1 (by omega) (by rw [hac1]; omega)
    (fun j a h => by
      by_cases hj : j < 2 ^ (P.m * (bagL P.D (P.N - 1)).length)
      · simp only [hj, if_true]; rw [hrowT j hj]; exact lor_le_one h tbv_le_one
      · simp only [hj, if_false]; exact h) (by
      intro τ hA hlt hQ
      have hfr : ∀ y, y ∉ ["so", "ac"] → τ.vars y = σ1.vars y := hA.2
      have e4 : τ.vars "bs" = (P.N - 1) * P.tabs := by rw [hfr "bs" (by simp), hbs1]
      have e5 : τ.arrs "TB" = σ1.arrs "TB" := by rw [hA.1]
      have hlt' : τ.vars "so" < 2 ^ (P.m * (bagL P.D (P.N - 1)).length) := hlt
      have hb : (τ.arrs "TB").getD (τ.vars "bs" + τ.vars "so") 0 = tbv P.I P.kk P.D (P.N - 1)
          (τ.vars "so") := by rw [e4, e5]; exact hrowT _ hlt'
      obtain ⟨τ', r, hv, hA', hso, ho⟩ := orBody_run (B := B) τ (by rw [e4, e5]; omega)
        (by rw [e4]; omega) hQ (by rw [hb]; exact tbv_le_one) (by omega) (by omega)
        (by rw [e4]; omega)
      refine ⟨τ', r, ?_, agr_comp (S := ["so", "ac"]) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp; tauto), hso, ho⟩
      rw [hv, hb, if_pos hlt', hrowT _ hlt'])
  obtain ⟨σ2, r2, hv2, hA2, o2⟩ := hf
  have hfold := or_fold (2 ^ (P.m * (bagL P.D (P.N - 1)).length))
    (fun j => (σ1.arrs "TB").getD ((P.N - 1) * P.tabs + j) 0)
    (fun j hj => by
      show (σ1.arrs "TB").getD _ 0 ≤ 1
      rw [hrowT j hj]; exact tbv_le_one) _ le_rfl
  have hac2 : σ2.vars "ac" ≤ 1 := by
    rw [hv2, hac1, hfold]; split_ifs <;> omega
  have r3 : Run B (.write (V "ac")) σ2
      { σ2 with out := σ2.out ++ [σ2.vars "ac"] } (1 + (V "ac").size) :=
    Run.write (evalB_var (by omega))
  refine ⟨_, (r1.seq (r2.seq r3)).mono (by simp [Expr.size]; unfold answerCost; omega), ?_⟩
  have hdp := dp_correct P.hD P.kk
  have hans : σ2.vars "ac" = if P.I.HasKFairSchedule P.kk then 1 else 0 := by
    rw [hv2, hac1, hfold]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨j, hj, hT1⟩
      rw [hrowT j hj] at hT1
      refine hdp.1 ⟨j, by rw [bpow]; exact hj, ?_⟩
      by_contra hn
      have hn' : ¬ TB P.I P.kk P.D (P.N - 1) j := hn
      rw [tbv_zero hn'] at hT1; omega
    · intro h
      obtain ⟨e, he, hTB⟩ := hdp.2 h
      rw [bpow] at he
      exact ⟨e, he, by rw [hrowT e he]; exact tbv_one (show TB P.I P.kk P.D (P.N - 1) e from hTB)⟩
  show σ2.out ++ [σ2.vars "ac"] = _
  rw [o2, ho1, hans]

end Lax117284Proofs.Machine.TwNode
