import Lax117284Proofs.Machine.ClMainFit
import Lax117284Proofs.Machine.ClBruteFinal
import Lax117284Proofs.ExtremeFairness

/-!
The two branches of the main program: the one that builds the integer program (after handling
the case `k > m` directly) and the brute force.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- `1` when `m < k` and `0 < n`. -/
def scE : Expr := mul (ltFl (V "m") (V "k")) (ltFl (lit 0) (V "n"))

/-- The branch for a long word: answer `0` when `k > m`, else build. -/
def fitBranch (P : Program) (c1 : ℕ) : Com := seqs [asg "sc" scE,
  .ite (.lt (lit 0) (V "sc")) (.write (lit 0)) (fitRun P c1)]

variable {B k c1 : ℕ} {I : Instance} {x : List ℕ} {P : Program}

/-- What the branches start from. -/
def F0 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
    σ.inp = [] ∧ σ.out = []

theorem scCom_spec (hn : I.clients < B) (hm : I.days < B) (hk : k < B) (h1 : 1 < B) :
    Spec B (F0 P c1 I x k) (asg "sc" scE)
      (fun _ σ' => F0 P c1 I x k σ' ∧ σ'.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0)
      20 := by
  have e1 : k - I.days - (k - I.days - 1) = if I.days < k then 1 else 0 := by
    split_ifs <;> omega
  have e2 : I.clients - 0 - (I.clients - 0 - 1) = if 0 < I.clients then 1 else 0 := by
    split_ifs <;> omega
  unfold scE
  run_vcg
  all_goals obtain ⟨⟨hX, hn', hm', hk'⟩, hZ, hi, ho⟩ := ‹F0 P c1 I x k σ›
  · refine ⟨⟨⟨by simpa [Env.setVar] using hX, by simp [Env.setVar, hn'], by simp [Env.setVar, hm'],
      by simp [Env.setVar, hk']⟩, hZ, by simp [Env.setVar, hi], by simp [Env.setVar, ho]⟩, ?_⟩
    simp only [Env.setVar, hn', hm', hk', ite_true]
    rw [e1, e2]
    split_ifs <;> simp_all
  all_goals (simp only [hn', hm', hk']; try (rw [e1, e2]; split_ifs <;> simp <;> omega))
  all_goals omega

theorem cond0_true {B : ℕ} {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some true) : 0 < σ.vars y := by
  simp only [evalB_condLt_iff, ClSim.lit, ClSim.V, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem cond0_false {B : ℕ} {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some false) : σ.vars y = 0 := by
  simp only [evalB_condLt_iff, ClSim.lit, ClSim.V, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem cond0_def {B : ℕ} {σ : Env} {y : String} (h1 : 0 < B) (h : σ.vars y < B) :
    ∃ v, (Cond.lt (lit 0) (V y)).evalB B σ = some v :=
  ⟨_, evalB_condLt (evalB_lit h1) (evalB_var h)⟩

/-- The cost of the branch that builds. -/
def Kfit (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (I : Instance) : ℕ :=
  buildCost I + (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) +
    (20 * P.length + 101 + ((c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 + 4)) + 3

open Classical Lax117284.ParameterizedComplexity in
open Lax117284.IlpClients (decodeILP ilpClients) in
theorem fitBranch_spec (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1)
    (hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t)
    (h : Bh I x k B) (hcrit : Q I.clients + 2 ≤ x.length)
    (hbB : 2 * x.length + I.days + 1 < B)
    (hw : 16 * (c1 * (2 * x.length + I.days + 1) ^ (c1 - 1)) + 32 < B) (hP : P.length < B)
    (hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (F0 P c1 I x k) (fitBranch P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) (Kfit P c' g' c1 I + 30) := by
  have hn := h.n_lt
  have hm := h.m_lt
  have hk := h.k_lt
  have hB1 : 1 < B := by have := h.hL; have := h.hzB; have := (sizes_le_zLen I.clients).2.2.2.2.2.2.2; omega
  have hsc := scCom_spec (P := P) (c1 := c1) (x := x) hn hm hk hB1
  have hT : Spec B (fun σ => (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
      (Cond.lt (lit 0) (V "sc")).evalB B σ = some true)
      (.write (lit 0)) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    have hw0 : Spec B (fun σ => σ.out = []) (.write (lit 0)) (fun _ σ' => σ'.out = [0]) 3 := by
      run_vcg
      all_goals (rename_i h1; simp [h1])
    refine Spec.post (Spec.pre hw0 (fun σ hσ => hσ.1.1.2.2.2)) ?_
    rintro σ σ' ⟨⟨hF0, hsc⟩, hc⟩ hσ'
    have hpos := cond0_true hc
    rw [hsc] at hpos
    have hcond : I.days < k ∧ 0 < I.clients := by
      by_contra hn
      rw [if_neg hn] at hpos; omega
    rw [hσ', if_neg (ExtremeFairness.not_hasKFairSchedule_of_days_lt hcond.1 hcond.2)]
  have hF : Spec B (fun σ => (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
      (Cond.lt (lit 0) (V "sc")).evalB B σ = some false)
      (fitRun P c1) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) (Kfit P c' g' c1 I) := by
    have hkm : ∀ σ, (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
        (Cond.lt (lit 0) (V "sc")).evalB B σ = some false → k ≤ I.days ∨ I.clients = 0 := by
      rintro σ ⟨⟨hF0, hsc⟩, hc⟩
      have h0 := cond0_false hc
      rw [hsc] at h0
      by_contra hn
      rw [if_pos (by omega)] at h0; omega
    intro σ hσ
    exact fitRun_spec P c' g' c1 hc1 hOr h hcrit (hkm σ hσ) hbB hw hP hLits σ hσ.1.1
  have hite := Spec.ite (P := fun σ => F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0)
    (b := Cond.lt (lit 0) (V "sc")) (c := .write (lit 0)) (d := fitRun P c1)
    (fun σ hσ => cond0_def (by omega) (by rw [hσ.2]; split_ifs <;> omega))
    (Spec.mono hT (by omega : 3 ≤ Kfit P c' g' c1 I + 3))
    (Spec.mono hF (by omega : Kfit P c' g' c1 I ≤ Kfit P c' g' c1 I + 3))
  have hsz : (Cond.lt (lit 0) (V "sc")).size = 3 := by simp [lit, V]
  unfold fitBranch
  refine Spec.mono (Spec.seq hsc hite (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)) ?_
  rw [hsz]; omega

/-- The brute force, then its answer. -/
def bruteBranch : Com := .seq ClBrute.bruteCom (.write (V "bfans"))

open Classical in
theorem bruteBranch_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (F0 P c1 I x k) bruteBranch
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (ClBrute.bruteCost I.days I.clients + 3) := by
  have hbr := ClBrute.brute_spec I x k B hdec hB hX
  have hn' : x.getD 0 0 = I.clients := ClientsWord.x0 hdec
  have hm' : x.getD 1 0 = I.days := ClientsWord.x1 hdec
  have hn'' : x[0]?.getD 0 = I.clients := by simpa [List.getD_eq_getElem?_getD] using hn'
  have hm'' : x[1]?.getD 0 = I.days := by simpa [List.getD_eq_getElem?_getD] using hm'
  have hv1 : (if I.HasKFairSchedule k then 1 else 0) < B := by split_ifs <;> omega
  have hw : Spec B (fun σ => σ.out = [] ∧ σ.vars "bfans" = if I.HasKFairSchedule k then 1 else 0)
      (.write (V "bfans")) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    run_vcg
    all_goals (rename_i h1 h2; simp [h1, h2])
  have hb' : Spec B (F0 P c1 I x k) ClBrute.bruteCom
      (fun _ σ' => σ'.out = [] ∧ σ'.vars "bfans" = if I.HasKFairSchedule k then 1 else 0)
      (ClBrute.bruteCost I.days I.clients) := by
    refine Spec.post (Spec.pre hbr ?_) ?_
    · rintro σ ⟨⟨hX', hn, hm, hk⟩, hZ, hi, ho⟩
      refine ⟨hX', hn, hm, hk, ?_⟩
      rw [hZ "bfsc" (by decide)]; simp [extF, hn'', hm'']
    · rintro σ σ' ⟨⟨hX', hn, hm, hk⟩, hZ, hi, ho⟩ ⟨hans, -, -, -, -, hi', ho'⟩
      exact ⟨by rw [ho', ho], hans⟩
  unfold bruteBranch
  exact Spec.seq hb' hw (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)

end Lax117284Proofs.Machine.ClMain
