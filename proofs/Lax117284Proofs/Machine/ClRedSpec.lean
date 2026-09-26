import Lax117284Proofs.Machine.ClRedProg

/-!
The reduction's program, whole: on the word of a uniform instance it prints the word of the
reduction, within the bound `BR` on its values and the cost `KR`.
-/

namespace Lax117284Proofs.Machine.ClRed

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg)
open Lax117284Proofs.Machine.ClBuild Lax117284Proofs.Machine.ClMain
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Lax117284.InstanceEncoding

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The cost of the inner branch: eight writes without a client, else the builder and the
printing loop. -/
def bK (I : Instance) : ℕ :=
  if I.clients = 0 then 8 else buildCost I + (11 * zLen I.clients + 6)

/-- The cost of the reduction on the word of `I`. -/
def redK (I : Instance) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (20 + (4 + (8 + (4 + bK I))))

/-- The builder and the printing loop: the word of the integer program is out. -/
theorem buildOut_spec (h : Bh I x k B) :
    Spec B (F0 [] 1 I x k) (.seq buildCom outCom)
      (fun _ σ' => σ'.out = zList I.clients I.days k (cntN I))
      (buildCost I + (11 * zLen I.clients + 6)) := by
  set Z := zList I.clients I.days k (cntN I) with hZdef
  have hZl : Z.length = zLen I.clients := zList_length I k
  have hn' : x[0]?.getD 0 = I.clients := by
    simpa [List.getD_eq_getElem?_getD] using ClientsWord.x0 h.enc
  have hm' : x[1]?.getD 0 = I.days := by
    simpa [List.getD_eq_getElem?_getD] using ClientsWord.x1 h.enc
  have hmB := h.m_lt
  have hzB := h.hzB
  have hE : ∀ v ∈ Z, v < B := fun v hv => by
    have := mem_zList_le I k hv; omega
  have hb : Spec B (F0 [] 1 I x k) buildCom
      (fun _ σ' => σ'.vars "zl" = zLen I.clients ∧ σ'.arrs "z" = Z ∧ σ'.out = []) (buildCost I) := by
    refine Spec.post (Spec.pre (buildCom_spec h) ?_) ?_
    · rintro σ ⟨hC, hZ0, hi, ho⟩
      refine ⟨hC, ?_, ?_, ?_⟩
      · rw [hZ0 "cnt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "okt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "z" (by decide)]; simp [extF, hn', hm']
    · rintro σ σ' ⟨hC, hZ0, hi, ho⟩ ⟨hC1, hS1, hz1, hA⟩
      exact ⟨hS1.zl, hz1, by rw [hA.2.2.1, ho]⟩
  have ho := outCom_spec (B := B) (Z := Z) (by rw [hZl]; exact hzB) hE
  refine Spec.mono (Spec.seq hb ho (fun _ _ _ h => ⟨by rw [h.1, hZl], h.2.1, h.2.2⟩)
    (fun _ _ _ _ _ h => h)) ?_
  rw [hZl]

/-- **The reduction's program prints the word of the reduction.** The bound `B` must admit the
word, and the word of the integer program when it is built. -/
theorem redCom_spec (hdec : EncodesUniform x I k) (hL : x.length < B) (hX : ∀ v ∈ x, v < B)
    (hzB : ¬ (I.days < k ∧ 0 < I.clients) → 0 < I.clients → zLen I.clients < B) :
    Spec B (M0 [] 1 x) redCom (fun _ σ' => σ'.out = fI I k) (redK I x) := by
  have hl := ClientsWord.len_eq hdec
  have hg : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  have hnB : I.clients < B := by rw [← ClientsWord.x0 hdec]; exact hg 0
  have hmB : I.days < B := by rw [← ClientsWord.x1 hdec]; exact hg 1
  have hkB : k < B := by rw [← ClientsWord.xk hdec]; exact hg _
  have hB1 : 1 < B := by omega
  have hr := read_spec (P := []) (c1 := 1) hdec hL hX
  have hsc := scCom_spec (P := []) (c1 := 1) (x := x) hnB hmB hkB hB1
  -- the precondition of the outer conditional
  set P1 : Env → Prop := fun σ => F0 [] 1 I x k σ ∧
    σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0 with hP1
  have hdef1 : ∀ σ, P1 σ → ∃ v, (Cond.lt (lit 0) (V "sc")).evalB B σ = some v :=
    fun σ hσ => cond0_def (by omega) (by rw [hσ.2]; split_ifs <;> omega)
  have hdef2 : ∀ σ, F0 [] 1 I x k σ → ∃ v, (Cond.lt (lit 0) (V "n")).evalB B σ = some v :=
    fun σ hσ => cond0_def (by omega) (by rw [hσ.1.n]; exact hnB)
  have hsz1 : (Cond.lt (lit 0) (V "sc")).size = 3 := by simp [lit, V]
  have hsz2 : (Cond.lt (lit 0) (V "n")).size = 3 := by simp [lit, V]
  -- the rejecting branch
  have hT : Spec B (fun σ => P1 σ ∧ (Cond.lt (lit 0) (V "sc")).evalB B σ = some true) rejCom
      (fun _ σ' => σ'.out = fI I k) (8 + (4 + bK I)) := by
    by_cases hc : I.days < k ∧ 0 < I.clients
    · refine Spec.mono (Spec.conseq (rejCom_spec [] hB1) (fun σ hσ => hσ.1.1.2.2.2) ?_ le_rfl)
        (by omega)
      intro σ σ' _ h; rw [h]; simp [fI, hc]
    · rintro σ ⟨⟨hF, hsc'⟩, hev⟩
      have := cond0_true hev
      rw [hsc', if_neg hc] at this
      exact absurd this (lt_irrefl 0)
  -- the building branch, with its own conditional on the number of clients
  have hF : Spec B (fun σ => P1 σ ∧ (Cond.lt (lit 0) (V "sc")).evalB B σ = some false)
      (.ite (.lt (lit 0) (V "n")) (.seq buildCom outCom) zeroCom)
      (fun _ σ' => σ'.out = fI I k) (4 + bK I) := by
    by_cases hc : I.days < k ∧ 0 < I.clients
    · rintro σ ⟨⟨hF, hsc'⟩, hev⟩
      have := cond0_false hev
      rw [hsc', if_pos hc] at this
      exact absurd this one_ne_zero
    · have hfI : fI I k = zList I.clients I.days k (cntN I) := by simp [fI, hc]
      refine Spec.pre ?_ (fun σ hσ => hσ.1.1)
      by_cases hn0 : I.clients = 0
      · have hbK : bK I = 8 := by simp [bK, hn0]
        rw [hbK]
        have hz : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some false) zeroCom
            (fun _ σ' => σ'.out = fI I k) 8 := by
          refine Spec.conseq (zeroCom_spec [] hB1 hmB) (fun σ hσ => ⟨hσ.1.2.2.2, hσ.1.1.m⟩) ?_ le_rfl
          intro σ σ' _ h
          rw [h, hfI, zList_zero hn0]; simp
        have hb : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some true) (.seq buildCom outCom)
            (fun _ σ' => σ'.out = fI I k) 8 := by
          rintro σ ⟨hF0, hev⟩
          have := cond0_true hev
          rw [hF0.1.n, hn0] at this
          exact absurd this (lt_irrefl 0)
        have hite := Spec.ite hdef2 hb hz
        rw [hsz2] at hite
        exact hite
      · have hbK : bK I = buildCost I + (11 * zLen I.clients + 6) := by simp [bK, hn0]
        rw [hbK]
        have hb : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some true) (.seq buildCom outCom)
            (fun _ σ' => σ'.out = fI I k) (buildCost I + (11 * zLen I.clients + 6)) := by
          refine Spec.conseq (buildOut_spec ⟨hdec, hL, hX, hzB hc (by omega)⟩)
            (fun σ hσ => hσ.1) ?_ le_rfl
          intro σ σ' _ h; rw [h, hfI]
        have hz : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some false) zeroCom
            (fun _ σ' => σ'.out = fI I k) (buildCost I + (11 * zLen I.clients + 6)) := by
          rintro σ ⟨hF0, hev⟩
          have := cond0_false hev
          rw [hF0.1.n] at this
          exact absurd this hn0
        have hite := Spec.ite hdef2 hb hz
        rw [hsz2] at hite
        exact hite
  have hite := Spec.ite (P := P1) hdef1 hT (Spec.mono hF (by omega))
  rw [hsz1] at hite
  unfold redCom
  refine Spec.mono (Spec.seq hr (Spec.seq hsc hite (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h.1) (fun _ _ _ _ _ h => h)) ?_
  unfold redK; omega

/-! ### The value bound and the cost, as functions of the word -/

/-- The bound on the values of the reduction's program: the word and its image, each with its
length and its largest entry. -/
noncomputable def BR (x : List ℕ) : ℕ :=
  (x.length + Mx x + 1) + ((fRed x).length + Mx (fRed x) + 1)

/-- The cost of the reduction's program on the word `x`. -/
noncomputable def KR (x : List ℕ) : ℕ := redK (decode x.dropLast) x

/-- **The reduction's program solves the reduction** on every word of a uniform instance. -/
theorem solves : Solves layoutR redCom UniformInstances fRed BR KR where
  ok := layoutR_ok
  inp := by
    rintro x ⟨I, k, hdec⟩ v hv
    have := le_Mx hv
    unfold BR; omega
  run := by
    rintro x ⟨I, k, hdec⟩
    have hL : x.length < BR x := by unfold BR; omega
    have hX : ∀ v ∈ x, v < BR x := fun v hv => by
      have := le_Mx hv; unfold BR; omega
    have hzB : ¬ (I.days < k ∧ 0 < I.clients) → 0 < I.clients → zLen I.clients < BR x := by
      intro hc _
      unfold BR
      rw [fRed_eq hdec]
      simp only [fI, if_neg hc, zList_length]
      omega
    refine ⟨extF [] 1 x, ?_⟩
    obtain ⟨σ', hrun, hout⟩ :=
      redCom_spec hdec hL hX hzB (initEnv (extF [] 1 x) x) ⟨rfl, rfl, fun a => rfl⟩
    refine ⟨σ', ?_, ?_⟩
    · unfold KR; rw [decode_dropLast hdec]; exact hrun
    · rw [hout, fRed_eq hdec]

end Lax117284Proofs.Machine.ClRed
