import Lax117284Proofs.Machine.ClMainDefs
import Lax117284Proofs.IlpClientsBridge

/-!
The branch of the main program that hands the integer program to the oracle: build the word,
choose the oracle's word length, run the interpreter, print the answer.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The branch: build, choose, interpret, print. -/
def fitRun (P : Program) (c1 : ℕ) : Com :=
  seqs [buildCom, wpCom c1 (c1 - 1), simCom P, .write (V "outv")]

theorem write_spec {B v : ℕ} (hv : v < B) :
    Spec B (fun σ => σ.out = [] ∧ σ.vars "outv" = v) (.write (V "outv"))
      (fun _ σ' => σ'.out = [v]) 3 := by
  run_vcg
  all_goals (rename_i h1 h2; simp [h1, h2])

theorem pow_clog_le {t : ℕ} (h : 1 ≤ t) : 2 ^ Nat.clog 2 t ≤ 2 * t := by
  by_cases h1 : t = 1
  · subst h1; simp
  · have hc : 0 < Nat.clog 2 t := Nat.clog_pos (by norm_num) (by omega)
    have := Nat.pow_lt_of_lt_clog (b := 2) (x := t) (y := Nat.clog 2 t - 1) (by omega)
    have e : 2 ^ Nat.clog 2 t = 2 * 2 ^ (Nat.clog 2 t - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- After the builder. -/
def G1 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "z" = zList I.clients I.days k (cntN I) ∧
    (∀ a, a ∉ ["X", "cnt", "okt", "z"] → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
    σ.inp = [] ∧ σ.out = []

/-- After the choice of the word length. -/
def G2 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  G1 P c1 I x k σ ∧ σ.vars "Mp" = 2 ^ Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) ∧
    σ.vars "wpv" = Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1))

theorem mulSteps_frame (n : ℕ) : (∀ y ∈ (mulSteps n).wvars, y = "tg") ∧ (mulSteps n).warrs = [] ∧
    ¬ (mulSteps n).reads ∧ (mulSteps n).NoWrite := by
  induction n with
  | zero => simp [mulSteps, Com.wvars, Com.warrs, Com.reads, Com.NoWrite]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨fun y hy => ?_, ?_, ?_, ?_⟩
    · simp only [mulSteps, Com.wvars, asg, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact hy
      · exact h1 y hy
    · simp [mulSteps, Com.warrs, asg, h2]
    · simp [mulSteps, Com.reads, asg, h3]
    · simp [mulSteps, Com.NoWrite, asg, h4]

theorem wpCom_frame (c1 E : ℕ) : (∀ y, y ∉ ["bs", "tg", "wpv", "Mp"] → y ∉ (wpCom c1 E).wvars) ∧
    (∀ a, a ∉ (wpCom c1 E).warrs) ∧ ¬ (wpCom c1 E).reads ∧ (wpCom c1 E).NoWrite := by
  obtain ⟨h1, h2, h3, h4⟩ := mulSteps_frame E
  refine ⟨fun y hy h => ?_, fun a h => ?_, ?_, ?_⟩
  · simp only [wpCom, wpLoop, wpStep, Com.wvars, seqs, asg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h hy
    have := h1 y
    tauto
  · simp [wpCom, wpLoop, wpStep, Com.warrs, seqs, asg, h2] at h
  · simp [wpCom, wpLoop, wpStep, Com.reads, seqs, asg, h3]
  · simp [wpCom, wpLoop, wpStep, Com.NoWrite, seqs, asg, h4]

/-- The word of the program, its length, its entries. -/
theorem zList_length (I : Instance) (k : ℕ) : (zList I.clients I.days k (cntN I)).length = zLen I.clients := by
  simp [zList]

open Classical Lax117284.ParameterizedComplexity in
open Lax117284.IlpClients (decodeILP ilpClients) in
theorem fitRun_spec (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1)
    (hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t)
    (h : Bh I x k B) (hcrit : Q I.clients + 2 ≤ x.length) (hkm : k ≤ I.days ∨ I.clients = 0)
    (hbB : 2 * x.length + I.days + 1 < B)
    (hw : 16 * (c1 * (2 * x.length + I.days + 1) ^ (c1 - 1)) + 32 < B) (hP : P.length < B)
    (hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
        σ.inp = [] ∧ σ.out = [])
      (fitRun P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (buildCost I + (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) +
        (20 * P.length + 101 + ((c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 + 4)) + 3) := by
  have hc1' : 1 ≤ c1 := by omega
  have hE : c1 - 1 = c' := by omega
  have hn : x.getD 0 0 = I.clients := ClientsWord.x0 h.enc
  have hm : x.getD 1 0 = I.days := ClientsWord.x1 h.enc
  have hn' : x[0]?.getD 0 = I.clients := by simpa [List.getD_eq_getElem?_getD] using hn
  have hm' : x[1]?.getD 0 = I.days := by simpa [List.getD_eq_getElem?_getD] using hm
  have hzl : zLen I.clients ≤ x.length := by have := zLen_le I.clients; omega
  have hLB : x.length < B := h.hL
  set Z := zList I.clients I.days k (cntN I) with hZ
  have hZl : Z.length = zLen I.clients := zList_length I k
  set tgt := c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1) with htgt
  have hb1 : 1 ≤ 2 * zLen I.clients + I.days + 1 := by omega
  have htgt1 : 1 ≤ tgt := Nat.mul_pos hc1' (Nat.one_le_pow _ _ hb1)
  set wp := Nat.clog 2 tgt with hwp
  have hpw : 2 ^ wp ≤ 2 * tgt := pow_clog_le htgt1
  have hpw2 : tgt ≤ 2 ^ wp := Nat.le_pow_clog (by norm_num) tgt
  have htgtB : tgt ≤ c1 * (2 * x.length + I.days + 1) ^ (c1 - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hBnd : Bnd B wp := by unfold Bnd; omega
  have hmB : I.days < B := h.m_lt
  have hzE : ∀ v ∈ Z, v < B := by
    intro v hv
    have := mem_zList_le I k hv
    have := h.hL
    omega
  have hFits : Fits c' wp Z := by
    intro v hv
    have := mem_zList_le I k hv
    have h1 : c' * (Z.length + v + 1) ^ c' ≤ c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1) := by
      rw [hE]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by rw [hZl]; omega) _)
    omega
  have hZD : Z ∈ ilpClients.Domain := Lax117284Proofs.IlpClientsBridge.zList_mem_domain _ _ _ _
  obtain ⟨t, ht, hrun⟩ := hOr wp Z hZD hFits
  have hHS : HypS B wp P Z := by
    refine ⟨hBnd, by rw [hZl]; omega, ?_, ?_, hP, hLits⟩
    · intro i
      by_cases hi : i < Z.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hzE _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; omega
    · intro i hi; exact hzE _ (List.getElem_mem hi)
  have hb' : Spec B (fun σ => Ctx0 I x k σ ∧
      (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧ σ.inp = [] ∧ σ.out = [])
      buildCom (fun _ σ' => G1 P c1 I x k σ') (buildCost I) := by
    refine Spec.post (Spec.pre (buildCom_spec h) ?_) ?_
    · rintro σ ⟨hC, hZ0, hi, ho⟩
      refine ⟨hC, ?_, ?_, ?_⟩
      · rw [hZ0 "cnt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "okt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "z" (by decide)]; simp [extF, hn', hm']
    · rintro σ σ' ⟨hC, hZ0, hi, ho⟩ ⟨hC1, hS1, hz1, hA1, hA2, hA3, hA4⟩
      refine ⟨hC1, hS1, hz1, fun a ha => ?_, by rw [hA2, hi], by rw [hA3, ho]⟩
      rw [hA1 a (by simp [BA, CA, OA, FA]; simp at ha; tauto)]
      exact hZ0 a (by simp at ha; tauto)
  have hwpB : 2 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) < B := by omega
  have hbB' : 2 * zLen I.clients + I.days + 1 < B := by omega
  have hwp' : Spec B (G1 P c1 I x k) (wpCom c1 (c1 - 1)) (fun _ σ' => G2 P c1 I x k σ')
      (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) := by
    have hs := (wpCom_spec (B := B) (zl := zLen I.clients) (m := I.days) c1 (c1 - 1) hc1' hbB' hwpB).frame
    refine Spec.post (Spec.pre hs (fun σ hσ => ⟨hσ.2.1.zl, hσ.1.m⟩)) ?_
    rintro σ σ' ⟨hC, hS, hz, hA, hi, ho⟩ ⟨⟨hMp, -, -, hwpv⟩, hv, ha, hr, hwr⟩
    obtain ⟨fv, fa, fr, fw⟩ := wpCom_frame c1 (c1 - 1)
    have hv' : ∀ y, y ∉ ["bs", "tg", "wpv", "Mp"] → σ'.vars y = σ.vars y := fun y hy => hv y (fv y hy)
    have hA' : σ'.arrs = σ.arrs := funext fun a => ha a (fa a)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, (by rw [hMp, hwpv]), hwpv⟩
    · rw [hA']; exact hC.X
    · rw [hv' _ (by decide)]; exact hC.n
    · rw [hv' _ (by decide)]; exact hC.m
    · rw [hv' _ (by decide)]; exact hC.k
    · rw [hv' _ (by decide)]; exact hS.nn
    · rw [hv' _ (by decide)]; exact hS.T
    · rw [hv' _ (by decide)]; exact hS.Z
    · rw [hv' _ (by decide)]; exact hS.Vv
    · rw [hv' _ (by decide)]; exact hS.N
    · rw [hv' _ (by decide)]; exact hS.M
    · rw [hv' _ (by decide)]; exact hS.zl
    · rw [hA']; exact hz
    · intro a' ha'; rw [hA']; exact hA a' ha'
    · rw [hr fr, hi]
    · rw [hwr fw, ho]
  have hsim' : Spec B (G2 P c1 I x k) (simCom P)
      (fun _ σ' => σ'.out = [] ∧ σ'.vars "outv" = if (decodeILP Z).Feasible then 1 else 0)
      (20 * P.length + 101 + ((t + 1) * 604 + 4)) := by
    have hs := simCom_spec hHS t hrun
    refine Spec.post (Spec.pre hs ?_) ?_
    · rintro σ ⟨⟨hC, hS, hz, hA, hi, ho⟩, hMp, hwpv⟩
      have hrep : ∀ a, a ∉ ["X", "cnt", "okt", "z"] → σ.arrs a = List.replicate (extF P c1 x a) 0 := hA
      refine ⟨?_, ?_, ?_, ?_, ?_, hz, hwpv, ?_, ?_⟩
      · rw [hrep "ip0" (by decide)]; simp [extF]
      · rw [hrep "ip1" (by decide)]; simp [extF]
      · rw [hrep "ip2" (by decide)]; simp [extF]
      · rw [hrep "ip3" (by decide)]; simp [extF]
      · rw [hrep "om" (by decide)]; simp [extF, hn', hm', hwp, htgt]
      · exact hMp
      · rw [hS.zl, hZl]
    · rintro σ σ' ⟨⟨hC, hS, hz, hA, hi, ho⟩, hMp, hwpv⟩ ⟨-, hov, -, -, hi', ho'⟩
      exact ⟨by rw [ho', ho], hov⟩
  have hwr' : Spec B (fun σ => σ.out = [] ∧ σ.vars "outv" = if (decodeILP Z).Feasible then 1 else 0)
      (.write (V "outv")) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    have hfe : (decodeILP Z).Feasible ↔ I.HasKFairSchedule k := zList_feasible_iff I k hkm
    have hv1 : (if (decodeILP Z).Feasible then 1 else 0) < B := by
      split_ifs <;> omega
    refine Spec.post (write_spec hv1) ?_
    rintro σ σ' - hσ'
    rw [hσ']
    by_cases hK : I.HasKFairSchedule k
    · rw [if_pos hK, if_pos (hfe.mpr hK)]
    · rw [if_neg hK, if_neg (fun hh => hK (hfe.mp hh))]
  have s3 := Spec.seq hsim' hwr' (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)
  have s2 := Spec.seq hwp' s3 (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  have s1 := Spec.seq hb' s2 (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  unfold fitRun
  refine Spec.mono s1 ?_
  have : (t + 1) * 604 ≤ (c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 := by
    have h1 : t ≤ c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' := by
      have := ht
      rw [hZl] at this
      have e : Z.getD 0 0 = nN I.clients := decode_N I.clients I.days k (cntN I)
      rw [e] at this
      exact this
    omega
  first | omega | linarith | (simp only [hwp, htgt] at *; omega)

end Lax117284Proofs.Machine.ClMain
