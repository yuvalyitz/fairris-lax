import Lax117284Proofs.Machine.TwLoop1

/-!
The program of a node of any kind: the dispatch on the kind.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The program of a node.** -/
def nodeCom : Com :=
  .seq (.assign "kd" (G "O" (add (L 2) (mul (L 3) (V "i")))))
    (.ite (.eq (V "kd") (L 0)) leafCom
      (.ite (.eq (V "kd") (L 1)) introCom
        (.ite (.eq (V "kd") (L 2)) forgetCom joinCom)))

/-- What a node costs. -/
def nodeCost (P : Params) : ℕ := 60 + introCost P + forgetCost P + joinCost P

lemma kd_cond (hk : σ.vars "kd" < B) {k : ℕ} (hkB : k < B) :
    (Cond.eq (V "kd") (L k)).evalB B σ = some (σ.vars "kd" == k) :=
  evalB_condEq (evalB_var hk) (evalB_lit hkB)

theorem kd_run (hC : NC P B σ) {i : ℕ} (hi : σ.vars "i" = i) (hiN : i < P.N) :
    Run B (.assign "kd" (G "O" (add (L 2) (mul (L 3) (V "i"))))) σ
      (σ.setVar "kd" (kind P.D i)) 20 := by
  have hk := kind_eq P hC hiN
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hb3 := hC.b3
  have hlenO := hC.lenO
  have hBpos : 0 < B := by omega
  have hidx : (σ.arrs "O")[2 + 3 * i]? = some (kind P.D i) := by
    rw [List.getElem?_eq_getElem (by omega)]
    have := hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hkB : kind P.D i < B := by rw [← hk]; exact hC.O_lt (by omega) (by omega)
  refine (Run.assign (v := kind P.D i) ?_).mono (by simp [Expr.size])
  refine evalB_get (k := 2 + 3 * i) ?_ hidx hkB
  have := evalB_bin (B := B) (σ := σ) (op := .add) (e := L 2) (f := mul (L 3) (V "i"))
    (m := 2) (n := 3 * i) (evalB_lit (by omega))
    (evalB_bin (op := .mul) (m := 3) (n := i) (evalB_lit (by omega))
      (by rw [evalB_var (by omega)]; exact congrArg some hi) (by simp; omega)) (by simp; omega)
  simpa using this

theorem nodeCom_run {i : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs i σ)
    (hi : σ.vars "i" = i) (hiN : i < P.N) :
    ∃ σ', Run B nodeCom σ σ' (nodeCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i + 1) σ' ∧ σ'.out = σ.out := by
  have r1 := kd_run hC hi hiN
  set σ1 := σ.setVar "kd" (kind P.D i) with hσ1
  have kk1 : Keep σ σ1 := (Keep.refl σ).setVar (by simp [SN]) _
  have hC1 : NC P B σ1 := kk1.nc hC
  have hN1 : NI P.I P.kk P.D P.wid P.tabs i σ1 := hN.of_arrs (by simp [hσ1])
  have hi1 : σ1.vars "i" = i := by simp [hσ1, hi]
  have hkd : σ1.vars "kd" = kind P.D i := by simp [hσ1]
  have hkdB : kind P.D i < B := by
    have := hC.b3; have := (P.hD.shape i hiN)
    rcases this with h | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> omega
  have hb3 := hC.b3
  have hcs := P.hD.shape i hiN
  have hc0 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 0) (by omega)
  have hc1 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 1) (by omega)
  have hc2 := kd_cond (σ := σ1) (by rw [hkd]; exact hkdB) (k := 2) (by omega)
  rw [hkd] at hc0 hc1 hc2
  have hnc : ∀ K, K ≤ 100 → 20 + (1 + (Cond.eq (V "kd") (L 0)).size + K) ≤ nodeCost P := by
    intro K hK
    simp only [Cond.size, Expr.size]
    unfold nodeCost introCost forgetCost joinCost
    omega
  rcases hcs with h0 | ⟨hpos, h1, _⟩ | ⟨hpos, h2, _⟩ | ⟨hpos, h3, _⟩
  · -- a leaf
    obtain ⟨σ', r, kk2, hN', ho⟩ := leafCom_ok (B := B) hC1 hN1 hi1 hiN (Or.inr h0)
    refine ⟨σ', (r1.seq (Run.ite_true (by rw [hc0, h0]; rfl) r)).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- an introduce node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := introCom_run (B := B) hC1 hN1 hi1 hiN h1
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h1]; rfl)
      (Run.ite_true (by rw [hc1, h1]; rfl) r))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- a forget node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := forgetCom_run (B := B) hC1 hN1 hi1 hiN h2
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h2]; rfl)
      (Run.ite_false (by rw [hc1, h2]; rfl) (Run.ite_true (by rw [hc2, h2]; rfl) r)))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩
  · -- a join node
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    obtain ⟨σ', r, kk2, hN', ho⟩ := joinCom_run (B := B) hC1 hN1 hi1 hiN h3
    refine ⟨σ', (r1.seq (Run.ite_false (by rw [hc0, h3]; rfl)
      (Run.ite_false (by rw [hc1, h3]; rfl) (Run.ite_false (by rw [hc2, h3]; rfl) r)))).mono
      (by simp only [Cond.size, Expr.size]; unfold nodeCost introCost forgetCost joinCost; omega),
      kk1.trans kk2, hN', by rw [ho]; simp [hσ1]⟩

end Lax117284Proofs.Machine.TwNode
