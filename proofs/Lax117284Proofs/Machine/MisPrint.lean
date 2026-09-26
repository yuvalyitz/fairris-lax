import Lax117284Proofs.Machine.MisJob
import Lax117284Proofs.Machine.Emit

/-!
Writing the image of Lemma 14: the number of clients and of days, the processing time and the due
date of every job cell by cell, and the fairness parameter of every client.
-/

namespace Lax117284Proofs.Machine.MisPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.MisBlk Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisJob (jobCom XE Kjob JCE JC JStep AJ jobCom_run Mag)
open Lax117284Proofs.Machine.MisFormat (VM)

variable {B : ℕ}

/-- Everything a cell reads. -/
structure PC (ns : List ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = ns
  vnn : σ.vars "nn" = nN ns
  vlc : σ.vars "lc" = lN ns
  vV : σ.vars "V" = VM ns
  vdg : σ.vars "dg" = degN ns
  vS2 : σ.vars "S2" = spanN ns
  vB3 : σ.vars "B3" = 3 + lN ns
  vB4 : σ.vars "B4" = 3 + lN ns + VM ns
  vdn : σ.vars "dn" = degN ns * nN ns
  vn1 : σ.vars "nn1" = nN ns + 1
  vLB : σ.vars "LB" = lN ns * (nN ns + 1)
  vVV : σ.vars "VV" = VM ns * VM ns
  vCC : σ.vars "CC" = clN ns
  vDD : σ.vars "DD" = daysN ns
  vE2 : σ.vars "E2" = edgeN ns / 2
  vDC : σ.vars "DC" = daysN ns * clN ns

/-- The cell `i` of the image: the day and the client, and the job. -/
def cellBody : Com :=
  .seq (.assign "di" (.bin .div (V "i") (V "CC")))
  (.seq (.assign "dm" (.bin .mul (V "di") (V "CC")))
  (.seq (.assign "cc" (.bin .sub (V "i") (V "dm")))
  (.seq jobCom (.seq (emitVar "pv") (emitVar "dv")))))

/-- The scalars a cell assigns. -/
def SCELL : List String := "i" :: (XE ++ ["di", "dm", "cc"] ++ SCR)

/-- The cost of a cell. -/
def Kcell (Sz V VV : ℕ) : ℕ := 100 + Kjob V VV + 2 * (48 * Sz + 50)

/-- **Every number of the image is small.** -/
lemma job_bound (ns : List ℕ) (i c : ℕ) (hn0 : 0 < nN ns) (hcl : c < clN ns) :
    (jobN ns i c).1 < Mag ns ∧ (jobN ns i c).2 < Mag ns := by
  have hspe := MisJob.span_eq ns
  have hcls := MisJob.cl_le ns
  have hdg1 : 1 ≤ degN ns := by unfold degN; omega
  have hnn_le : nN ns ≤ degN ns * nN ns := Nat.le_mul_of_pos_left _ hdg1
  have hVdg := MisJob.Vdg_le ns
  have h1 : ∀ x, degN ns * (x % nN ns + 1) ≤ degN ns * nN ns :=
    fun x => Nat.mul_le_mul_left _ (Nat.mod_lt _ hn0)
  have h2 : ∀ q m, degN ns * (q % nN ns) + m % degN ns + 1 ≤ degN ns * nN ns + degN ns := by
    intro q m
    have a := Nat.mul_le_mul_left (degN ns) (Nat.mod_lt q hn0).le
    have b := Nat.mod_lt m (show 0 < degN ns by omega)
    omega
  unfold Mag
  unfold jobN vertexDayN validationDayN edgeDayN
  split_ifs <;> simp only [] <;> first | omega | (constructor <;> first | omega | skip)
  all_goals first
    | (have := h1 (c - (3 + lN ns)); omega)
    | (have := h2 ((c - (3 + lN ns + VM ns)) / degN ns) (c - (3 + lN ns + VM ns)); omega)

lemma PC.of_agr {ns : List ℕ} {σ0 σ : Env} (h : PC ns σ0) (hAg : Agr SCELL σ0 σ) : PC ns σ := by
  have fr : ∀ y, y ∉ SCELL → σ.vars y = σ0.vars y := hAg.2
  refine ⟨by rw [hAg.1]; exact h.hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fr "nn" (by decide)]; exact h.vnn
  · rw [fr "lc" (by decide)]; exact h.vlc
  · rw [fr "V" (by decide)]; exact h.vV
  · rw [fr "dg" (by decide)]; exact h.vdg
  · rw [fr "S2" (by decide)]; exact h.vS2
  · rw [fr "B3" (by decide)]; exact h.vB3
  · rw [fr "B4" (by decide)]; exact h.vB4
  · rw [fr "dn" (by decide)]; exact h.vdn
  · rw [fr "nn1" (by decide)]; exact h.vn1
  · rw [fr "LB" (by decide)]; exact h.vLB
  · rw [fr "VV" (by decide)]; exact h.vVV
  · rw [fr "CC" (by decide)]; exact h.vCC
  · rw [fr "DD" (by decide)]; exact h.vDD
  · rw [fr "E2" (by decide)]; exact h.vE2
  · rw [fr "DC" (by decide)]; exact h.vDC

set_option maxHeartbeats 12800000 in
/-- **A cell of the image.** -/
theorem cellBody_run (Sz : ℕ) (ns : List ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hAg : Agr SCELL σ0 σ) (hpc : PC ns σ0)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns + 4 < B)
    (hn0 : 0 < nN ns) (hBP : daysN ns * clN ns + clN ns + daysN ns + 100 < B)
    (hlt : σ.vars "i" < daysN ns * clN ns) :
    ∃ σ', Run B cellBody σ σ' (Kcell Sz (VM ns) (VM ns * VM ns)) ∧
      σ'.out = σ.out ++ (bitsNat (MisSem.jobN ns (σ.vars "i" / clN ns) (σ.vars "i" % clN ns)).1 ++
        bitsNat (MisSem.jobN ns (σ.vars "i" / clN ns) (σ.vars "i" % clN ns)).2) ∧
      Agr SCELL σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  have hp := hpc.of_agr hAg
  obtain ⟨t, ht⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht] at hlt ⊢
  have hCpos : 0 < clN ns := by unfold clN; omega
  have hd_lt : t / clN ns < daysN ns := (Nat.div_lt_iff_lt_mul hCpos).2 hlt
  have hdle : t / clN ns ≤ t := Nat.div_le_self _ _
  have hmle : t / clN ns * clN ns ≤ t := Nat.div_mul_le_self _ _
  have hmod : t - t / clN ns * clN ns = t % clN ns := MisFind.mod_eq_sub t _
  have hmlt : t % clN ns < clN ns := Nat.mod_lt _ hCpos
  have s1 := asgE (B := B) "di" (.bin .div (V "i") (V "CC")) σ (by
    simp [small, den, ht, hp.vCC]; omega)
  set σ1 := σ.setVar "di" (den σ (.bin .div (V "i") (V "CC"))) with hσ1
  have hdi1 : σ1.vars "di" = t / clN ns := by simp [hσ1, den, Env.setVar, ht, hp.vCC]
  have s2 := asgE (B := B) "dm" (.bin .mul (V "di") (V "CC")) σ1 (by
    simp [small, den, hσ1, Env.setVar, ht, hp.vCC]; omega)
  set σ2 := σ1.setVar "dm" (den σ1 (.bin .mul (V "di") (V "CC"))) with hσ2
  have hdm2 : σ2.vars "dm" = t / clN ns * clN ns := by
    simp [hσ2, den, Env.setVar, hdi1, hσ1, hp.vCC, ht]
  have hi2 : σ2.vars "i" = t := by simp [hσ2, hσ1, Env.setVar, ht]
  have s3 := asgE (B := B) "cc" (.bin .sub (V "i") (V "dm")) σ2 (by
    simp [small, den, hi2, hdm2]; omega)
  set σ3 := σ2.setVar "cc" (den σ2 (.bin .sub (V "i") (V "dm"))) with hσ3
  have hcc3 : σ3.vars "cc" = t % clN ns := by simp [hσ3, den, Env.setVar, hi2, hdm2, hmod]
  have hdi3 : σ3.vars "di" = t / clN ns := by simp [hσ3, hσ2, Env.setVar, hdi1]
  have fr3 : ∀ y, y ∉ ["di", "dm", "cc"] → σ3.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ3, hσ2, hσ1, Env.setVar, hy.1, hy.2.1, hy.2.2]
  have ar3 : σ3.arrs = σ.arrs := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have ou3 : σ3.out = σ.out := by simp [hσ3, hσ2, hσ1, Env.setVar]
  have hjce : JCE ns (t / clN ns) (t % clN ns) σ3 :=
    ⟨⟨hdi3, hcc3, by rw [fr3 "nn" (by decide)]; exact hp.vnn,
      by rw [fr3 "lc" (by decide)]; exact hp.vlc,
      by rw [fr3 "V" (by decide)]; exact hp.vV,
      by rw [fr3 "dg" (by decide)]; exact hp.vdg,
      by rw [fr3 "S2" (by decide)]; exact hp.vS2,
      by rw [fr3 "B3" (by decide)]; exact hp.vB3,
      by rw [fr3 "B4" (by decide)]; exact hp.vB4,
      by rw [fr3 "dn" (by decide)]; exact hp.vdn,
      by rw [fr3 "nn1" (by decide)]; exact hp.vn1,
      by rw [fr3 "LB" (by decide)]; exact hp.vLB⟩,
      by rw [ar3]; exact hp.hA, by rw [fr3 "VV" (by decide)]; exact hp.vVV⟩
  obtain ⟨σ4, r4, hpv, hdv, hst⟩ := jobCom_run (B := B) ns (t / clN ns) (t % clN ns) σ3 hjce hE hlen
    hbig (by omega) hn0 hd_lt hmlt
  obtain ⟨hb1, hb2⟩ := job_bound ns (t / clN ns) (t % clN ns) hn0 hmlt
  obtain ⟨σ5, r5, o5, v5, a5⟩ := emitVar_spec (B := B) "pv" Sz σ4
    ⟨by rw [hpv]; omega, by rw [hpv]; exact hs _ (by omega)⟩
  have s5 : Same σ4 σ5 := same_of_frame v5 a5
  have hdv5 : σ5.vars "dv" = (jobN ns (t / clN ns) (t % clN ns)).2 := by
    rw [s5.1 "dv" (by decide)]; exact hdv
  obtain ⟨σ6, r6, o6, v6, a6⟩ := emitVar_spec (B := B) "dv" Sz σ5
    ⟨by rw [hdv5]; omega, by rw [hdv5]; exact hs _ (by omega)⟩
  have s6 : Same σ5 σ6 := same_of_frame v6 a6
  refine ⟨σ6, ?_, ?_, ?_, ?_⟩
  · refine (s1.seq (s2.seq (s3.seq (r4.seq (r5.seq r6))))).mono ?_
    unfold Kcell
    simp [Expr.size]
    omega
  · rw [o6, o5, hst.2.1, ou3, hdv5, hpv, List.append_assoc]
  · have hfr : ∀ y, y ∉ SCELL → σ6.vars y = σ0.vars y := by
      intro y hy
      have hy' : y ≠ "i" ∧ y ∉ XE ∧ y ≠ "di" ∧ y ≠ "dm" ∧ y ≠ "cc" ∧ y ∉ SCR := by
        simp only [SCELL, List.mem_cons, List.mem_append, not_or] at hy
        tauto
      rw [s6.1 y hy'.2.2.2.2.2, s5.1 y hy'.2.2.2.2.2, hst.2.2 y hy'.2.1,
        fr3 y (by simp [hy'.2.2.1, hy'.2.2.2.1, hy'.2.2.2.2.1])]
      exact hAg.2 y hy
    refine ⟨?_, hfr⟩
    rw [s6.2, s5.2, hst.1, ar3]; exact hAg.1
  · rw [s6.1 "i" (by decide), s5.1 "i" (by decide), hst.2.2 "i" (by decide),
      fr3 "i" (by decide), ht]

/-- The fairness parameter of a client. -/
def kvBody : Com :=
  .ite (.eq (V "i") (.lit 0)) (emitVar "DD")
    (.ite (.eq (V "i") (.lit 1)) (emitVar "E2")
      (.ite (.eq (V "i") (.lit 2)) (emitVar "E2") (emitLit 1)))

/-- The cost of a fairness parameter. -/
def Kkv (Sz : ℕ) : ℕ := 100 + (48 * Sz + 50)

/-- **The fairness parameter of a client.** -/
theorem kvBody_run (Sz : ℕ) (ns : List ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hAg : Agr ("i" :: SCR) σ0 σ) (hpc : PC ns σ0)
    (hDD : daysN ns + 4 < B) (hE2 : edgeN ns / 2 + 4 < B) (hlt : σ.vars "i" < clN ns)
    (hBi : clN ns + 4 < B) :
    ∃ σ', Run B kvBody σ σ' (Kkv Sz) ∧
      σ'.out = σ.out ++ bitsNat (kvN ns (σ.vars "i")) ∧
      Agr ("i" :: SCR) σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  obtain ⟨t, ht⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht] at hlt ⊢
  have hDDv : σ.vars "DD" = daysN ns := by rw [hAg.2 "DD" (by decide)]; exact hpc.vDD
  have hE2v : σ.vars "E2" = edgeN ns / 2 := by rw [hAg.2 "E2" (by decide)]; exact hpc.vE2
  have hiB : small B σ (V "i") := by simp [small, ht]; omega
  have h0B : small B σ (.lit 0) := by simp [small]; omega
  have h1B : small B σ (.lit 1) := by simp [small]; omega
  have h2B : small B σ (.lit 2) := by simp [small]; omega
  have fin : ∀ (σ' : Env), (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) → σ'.arrs = σ.arrs →
      Agr ("i" :: SCR) σ0 σ' ∧ σ'.vars "i" = t := by
    intro σ' hv ha
    refine ⟨⟨by rw [ha]; exact hAg.1, fun y hy => ?_⟩, ?_⟩
    · have hy' : y ∉ ["v", "s", "u", "i2"] ∧ y ∉ "i" :: SCR := by
        simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto
      rw [hv y hy'.1]; exact hAg.2 y hy'.2
    · rw [hv "i" (by decide), ht]
  have hK : Kkv Sz = 100 + (48 * Sz + 50) := rfl
  by_cases h0 : t = 0
  · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "DD" Sz σ
      ⟨by rw [hDDv]; omega, by rw [hDDv]; exact hs _ (by omega)⟩
    have hT : (Cond.eq (V "i") (.lit 0)).evalB B σ = some true :=
      condEq_true _ _ σ hiB h0B (by simp [den, ht, h0])
    refine ⟨σ', (Run.ite_true hT r).mono (by simp [Cond.size, Expr.size, hK] <;> omega), ?_,
      fin σ' v a⟩
    rw [o, hDDv]; simp [kvN, h0]
  · have hF : (Cond.eq (V "i") (.lit 0)).evalB B σ = some false :=
      condEq_false _ _ σ hiB h0B (by simp [den, ht, h0])
    by_cases h1 : t = 1
    · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "E2" Sz σ
        ⟨by rw [hE2v]; omega, by rw [hE2v]; exact hs _ (by omega)⟩
      have hT : (Cond.eq (V "i") (.lit 1)).evalB B σ = some true :=
        condEq_true _ _ σ hiB h1B (by simp [den, ht, h1])
      refine ⟨σ', (Run.ite_false hF (Run.ite_true hT r)).mono
        (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
      rw [o, hE2v]; simp [kvN, h1]
    · have hF1 : (Cond.eq (V "i") (.lit 1)).evalB B σ = some false :=
        condEq_false _ _ σ hiB h1B (by simp [den, ht, h1])
      by_cases h2 : t = 2
      · obtain ⟨σ', r, o, v, a⟩ := emitVar_spec (B := B) "E2" Sz σ
          ⟨by rw [hE2v]; omega, by rw [hE2v]; exact hs _ (by omega)⟩
        have hT : (Cond.eq (V "i") (.lit 2)).evalB B σ = some true :=
          condEq_true _ _ σ hiB h2B (by simp [den, ht, h2])
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_true hT r))).mono
          (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
        rw [o, hE2v]; simp [kvN, h2]
      · have hF2 : (Cond.eq (V "i") (.lit 2)).evalB B σ = some false :=
          condEq_false _ _ σ hiB h2B (by simp [den, ht, h2])
        obtain ⟨σ', r, o, v, a⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ trivial
        refine ⟨σ', (Run.ite_false hF (Run.ite_false hF1 (Run.ite_false hF2 r))).mono
          (by simp [Cond.size, Expr.size, hK] <;> omega), ?_, fin σ' v a⟩
        rw [o]; simp [kvN, h0, h1, h2]

lemma PC.of_same {ns : List ℕ} {σ σ' : Env} (h : PC ns σ) (hs : Same σ σ') : PC ns σ' :=
  have hAg : Agr SCELL σ σ' := ⟨hs.2, fun y hy => hs.1 y (fun hm => hy (by
    simp only [SCELL, List.mem_cons, List.mem_append]; tauto))⟩
  h.of_agr hAg

lemma numBits_flatMap' {α : Type} (L : List α) (f : α → List ℕ) :
    numBits (L.flatMap f) = L.flatMap (fun a => numBits (f a)) := by
  simp only [numBits, List.flatMap_assoc]

lemma numBits_map' {α : Type} (L : List α) (f : α → ℕ) :
    numBits (L.map f) = L.flatMap (fun a => bitsNat (f a)) := by
  simp [numBits, List.flatMap_map]

/-- The cost of writing the image. -/
def Kprint (Sz V VV DC CC : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + (Kcell Sz V VV + 10 + 4) * DC + 6 + (Kkv Sz + 10 + 4) * CC + 6

/-- Write the whole image. -/
def printM : Com :=
  .seq (emitVar "CC") (.seq (emitVar "DD") (.seq (outLoop "DC" cellBody) (outLoop "CC" kvBody)))

/-- **Writing the image.** -/
theorem printM_run (Sz : ℕ) (ns : List ℕ) (σ : Env) (hpc : PC ns σ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < VM ns * VM ns, ns.getD (2 + k) 0 + 8 < B) (hlen : 2 + VM ns * VM ns ≤ ns.length)
    (hbig : 2 * (VM ns * VM ns) + 2 * VM ns + 2 * lN ns + 60 < B) (hM : Mag ns + 4 < B)
    (hn0 : 0 < nN ns) (hBP : daysN ns * clN ns + clN ns + daysN ns + 100 < B)
    (hE2 : edgeN ns / 2 + 4 < B) :
    ∃ σ', Run B printM σ σ'
      (Kprint Sz (VM ns) (VM ns * VM ns) (daysN ns * clN ns) (clN ns)) ∧
      σ'.out = σ.out ++ numBits (outM ns) := by
  have hCpos : 0 < clN ns := by unfold clN; omega
  have hDle : daysN ns ≤ daysN ns * clN ns := Nat.le_mul_of_pos_right _ hCpos
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "CC" Sz σ
    ⟨by rw [hpc.vCC]; omega, by rw [hpc.vCC]; exact hs _ (by omega)⟩
  have s1 : Same σ σ1 := same_of_frame v1 a1
  have p1 := hpc.of_same s1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "DD" Sz σ1
    ⟨by rw [p1.vDD]; omega, by rw [p1.vDD]; exact hs _ (by omega)⟩
  have s2 : Same σ1 σ2 := same_of_frame v2 a2
  have p2 := p1.of_same s2
  obtain ⟨σ3, r3, o3, hAg3⟩ := eLoop (B := B) "DC" cellBody SCELL
    (fun t => bitsNat (MisSem.jobN ns (t / clN ns) (t % clN ns)).1 ++
      bitsNat (MisSem.jobN ns (t / clN ns) (t % clN ns)).2) (Kcell Sz (VM ns) (VM ns * VM ns))
    (daysN ns * clN ns) σ2 (by simp [SCELL]) (by decide) p2.vDC (by omega) (by
      intro σ' hAg hlt
      obtain ⟨σ'', r, o, a, hi⟩ := cellBody_run (B := B) Sz ns σ2 σ' hs hAg p2 hE hlen hbig hM hn0 hBP hlt
      exact ⟨σ'', r, o, a, hi⟩)
  have p3 := p2.of_agr hAg3
  obtain ⟨σ4, r4, o4, hAg4⟩ := eLoop (B := B) "CC" kvBody ("i" :: SCR)
    (fun t => bitsNat (kvN ns t)) (Kkv Sz) (clN ns) σ3 (by simp) (by decide) p3.vCC (by omega) (by
      intro σ' hAg hlt
      exact kvBody_run (B := B) Sz ns σ3 σ' hs hAg p3 (by omega) hE2 hlt (by omega))
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold Kprint; omega), ?_⟩
  rw [o4, o3, o2, o1]
  unfold outM
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc,
    numBits_flatMap', numBits_map']
  rw [hpc.vCC, p1.vDD]

end Lax117284Proofs.Machine.MisPrint
