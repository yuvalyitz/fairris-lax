import Lax117284Proofs.Machine.SatDue

/-!
Writing the image of Theorem 7: the number of clients, the number of days, the processing time and
the due date of every job day by day, and the parameter `1`.
-/

namespace Lax117284Proofs.Machine.SatPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.SatOps
open Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatDue
open Lax117284Proofs.Machine.SatFormat (SlotsN)

variable {B : ℕ}

/-- **A due date is small.** -/
lemma dueN_le (arr : List ℕ) (S c d : ℕ) (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S)
    (hpass : ∀ k < S, PassS arr k) (hcl : c < 3 + 2 * arr.getD 0 0 + S) :
    dueN arr d c ≤ 12 * S + 12 := by
  unfold dueN
  by_cases h1 : c < 3
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : c < 3 + 2 * arr.getD 0 0
    · rw [if_pos h2]
      split_ifs <;> omega
    · rw [if_neg h2]
      have hp := hpass (c - 3 - 2 * arr.getD 0 0) (by omega)
      obtain ⟨hp1, hp2⟩ := hp
      split_ifs <;> omega

/-- The cell of the image: the processing time and the due date. -/
def cellBody : Com :=
  .seq dueCom (.seq (emitLit 2) (emitVar "dv"))

/-- The scalars a cell assigns. -/
def SC : List String := "i" :: (AD ++ SCR)

/-- The cost of a cell. -/
def Kcell (Sz S : ℕ) : ℕ := 110 + 64 * S + 2 * (48 * Sz + 50) + 10

/-- **A cell of the image.** -/
theorem cellBody_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ0 σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3)
    (hAg : Agr SC σ0 σ) (hA : σ0.arrs "TK" = arr)
    (hdy : σ0.vars "dy" = d) (vV3 : σ0.vars "V3" = 3 + 2 * arr.getD 0 0)
    (vA2 : σ0.vars "A2" = 2 * arr.getD 1 0) (vK7 : σ0.vars "K7" = 7 + 2 * arr.getD 0 0)
    (vK9 : σ0.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0)
    (hlt : σ.vars "i" < 3 + 2 * arr.getD 0 0 + S) (hn : arr.getD 0 0 ≤ S)
    (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k) (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B cellBody σ σ' (Kcell Sz S) ∧
      σ'.out = σ.out ++ (bitsNat 2 ++ bitsNat (dueN arr d (σ.vars "i"))) ∧ Agr SC σ0 σ' ∧
      σ'.vars "i" = σ.vars "i" := by
  have fr : ∀ y, y ∉ SC → σ.vars y = σ0.vars y := hAg.2
  have hx : DCtx arr (σ.vars "i") d σ :=
    ⟨by rw [hAg.1]; exact hA, rfl, by rw [fr "dy" (by decide)]; exact hdy,
      by rw [fr "V3" (by decide)]; exact vV3, by rw [fr "A2" (by decide)]; exact vA2,
      by rw [fr "K7" (by decide)]; exact vK7, by rw [fr "K9" (by decide)]; exact vK9⟩
  obtain ⟨σ1, r1, e1, st1⟩ := dueCom_run (B := B) arr S (σ.vars "i") d σ hx hd hlt hn hna hpass
    hlen hEv hEs hB
  have hle := dueN_le arr S (σ.vars "i") d hn hna hpass hlt
  have hv1 : σ1.vars "dv" + 4 < B := by rw [e1]; omega
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 2 Sz (by omega) (hs _ (by omega))) σ1 trivial
  have hv2 : σ2.vars "dv" = σ1.vars "dv" := v2 "dv" (by decide)
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitVar_spec (B := B) "dv" Sz σ2
    ⟨by rw [hv2]; exact hv1, by rw [hv2]; exact hs _ hv1⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold Kcell; omega), ?_, ⟨?_, fun y hy => ?_⟩, ?_⟩
  · rw [o3, o2, hv2, e1, st1.2.1]
    simp [List.append_assoc]
  · rw [a3, a2, st1.1]; exact hAg.1
  · have hyAD : y ∉ AD := fun h => hy (by simp [SC, h])
    have hyS : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SC, SCR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v3 y hyS, v2 y hyS, st1.2.2 y hyAD, hAg.2 y hy]
  · have hyAD : "i" ∉ AD := by decide
    rw [v3 "i" (by decide), v2 "i" (by decide), st1.2.2 "i" hyAD]

/-- **The cells of a day.** -/
theorem dayLoop_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3) (hA : σ0.arrs "TK" = arr)
    (hdy : σ0.vars "dy" = d) (vV3 : σ0.vars "V3" = 3 + 2 * arr.getD 0 0)
    (vA2 : σ0.vars "A2" = 2 * arr.getD 1 0) (vK7 : σ0.vars "K7" = 7 + 2 * arr.getD 0 0)
    (vK9 : σ0.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0)
    (vC : σ0.vars "C" = 3 + 2 * arr.getD 0 0 + S) (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B (outLoop "C" cellBody) σ0 σ' ((Kcell Sz S + 10 + 4) * (3 + 2 * arr.getD 0 0 + S) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (3 + 2 * arr.getD 0 0 + S)).flatMap
        fun c => [2, dueN arr d c]) ∧ (∀ y ∉ SC, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "C" cellBody SC
    (fun c => bitsNat 2 ++ bitsNat (dueN arr d c)) (Kcell Sz S) (3 + 2 * arr.getD 0 0 + S) σ0
    (by simp [SC]) (by decide) vC hCB (by
      intro σ hAg hlt
      exact cellBody_run (B := B) Sz arr S d σ0 σ hs hd hAg hA hdy vV3 vA2 vK7 vK9 hlt hn hna hpass
        hlen hEv hEs hB)
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o]
  congr 1
  simp only [numBits, List.flatMap_assoc]
  refine List.flatMap_congr fun t _ => ?_
  simp [numBits]

/-- The day is set and the cells of the day are written. -/
def dayC (d : ℕ) : Com := .seq (.assign "dy" (.lit d)) (outLoop "C" cellBody)

/-- Write the whole image. -/
def printSat : Com :=
  .seq (emitVar "C") (.seq (emitLit 3) (.seq (dayC 0) (.seq (dayC 1) (.seq (dayC 2) (emitLit 1)))))

/-- The cost of writing the image. -/
def KprintS (Sz S N : ℕ) : ℕ := 3 * (48 * Sz + 50) + 3 * ((Kcell Sz S + 10 + 4) * N + 6 + 10)

/-- The scalars the image is written from. -/
structure PCtx (arr : List ℕ) (S : ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = arr
  vV3 : σ.vars "V3" = 3 + 2 * arr.getD 0 0
  vA2 : σ.vars "A2" = 2 * arr.getD 1 0
  vK7 : σ.vars "K7" = 7 + 2 * arr.getD 0 0
  vK9 : σ.vars "K9" = 9 + 2 * arr.getD 0 0 + 2 * arr.getD 1 0
  vC : σ.vars "C" = 3 + 2 * arr.getD 0 0 + S

lemma PCtx.of_frame {arr : List ℕ} {S : ℕ} {σ σ' : Env} (h : PCtx arr S σ)
    (ha : σ'.arrs = σ.arrs) (hf : ∀ y ∉ SC, σ'.vars y = σ.vars y) : PCtx arr S σ' :=
  ⟨by rw [ha]; exact h.hA, by rw [hf "V3" (by decide)]; exact h.vV3,
    by rw [hf "A2" (by decide)]; exact h.vA2, by rw [hf "K7" (by decide)]; exact h.vK7,
    by rw [hf "K9" (by decide)]; exact h.vK9, by rw [hf "C" (by decide)]; exact h.vC⟩

lemma PCtx.of_emit {arr : List ℕ} {S : ℕ} {σ σ' : Env} (h : PCtx arr S σ)
    (ha : σ'.arrs = σ.arrs) (hf : ∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) :
    PCtx arr S σ' :=
  h.of_frame ha (fun y hy => hf y (fun h' => hy (by
    simp only [SC, SCR, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h' ⊢
    tauto)))

lemma PCtx.setDy {arr : List ℕ} {S : ℕ} {σ : Env} (h : PCtx arr S σ) (d : ℕ) :
    PCtx arr S (σ.setVar "dy" d) :=
  ⟨by simp [Env.setVar, h.hA], by simp [Env.setVar, h.vV3], by simp [Env.setVar, h.vA2],
    by simp [Env.setVar, h.vK7], by simp [Env.setVar, h.vK9], by simp [Env.setVar, h.vC]⟩

/-- **One day: set it, and write its cells.** -/
theorem dayC_run (Sz : ℕ) (arr : List ℕ) (S d : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hd : d < 3) (hctx : PCtx arr S σ)
    (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B (dayC d) σ σ' ((Kcell Sz S + 10 + 4) * (3 + 2 * arr.getD 0 0 + S) + 6 + 10) ∧
      σ'.out = σ.out ++ numBits ((List.range (3 + 2 * arr.getD 0 0 + S)).flatMap
        fun c => [2, dueN arr d c]) ∧ PCtx arr S σ' := by
  have s0 := asg_lit (B := B) "dy" d σ (by omega)
  have h1 : PCtx arr S (σ.setVar "dy" d) := hctx.setDy d
  obtain ⟨σ', r, o, hf, ha⟩ := dayLoop_run (B := B) Sz arr S d (σ.setVar "dy" d) hs hd h1.hA
    (by simp [Env.setVar]) h1.vV3 h1.vA2 h1.vK7 h1.vK9 h1.vC hCB hn hna hpass hlen hEv hEs hB
  refine ⟨σ', (s0.seq r).mono (by omega), ?_, h1.of_frame ha hf⟩
  rw [o]; simp [Env.setVar]

/-- **Writing the image.** -/
theorem printSat_run (Sz : ℕ) (arr : List ℕ) (S : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hctx : PCtx arr S σ) (hS : SlotsN arr = S)
    (hCB : 3 + 2 * arr.getD 0 0 + S + 1 < B)
    (hn : arr.getD 0 0 ≤ S) (hna : 2 * arr.getD 1 0 ≤ S) (hpass : ∀ k < S, PassS arr k)
    (hlen : 3 + 2 * S ≤ arr.length)
    (hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B) (hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B)
    (hB : 60 * (S + 4) < B) :
    ∃ σ', Run B printSat σ σ' (KprintS Sz S (3 + 2 * arr.getD 0 0 + S)) ∧
      σ'.out = σ.out ++ numBits (outNums arr) := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "C" Sz σ
    ⟨by rw [hctx.vC]; omega, by rw [hctx.vC]; exact hs _ (by omega)⟩
  have h1 : PCtx arr S σ1 := hctx.of_emit a1 v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 3 Sz (by omega) (hs _ (by omega))) σ1 trivial
  have h2 : PCtx arr S σ2 := h1.of_emit a2 v2
  obtain ⟨σ3, r3, o3, h3⟩ := dayC_run (B := B) Sz arr S 0 σ2 hs (by omega) h2 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ4, r4, o4, h4⟩ := dayC_run (B := B) Sz arr S 1 σ3 hs (by omega) h3 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ5, r5, o5, h5⟩ := dayC_run (B := B) Sz arr S 2 σ4 hs (by omega) h4 hCB hn hna hpass hlen
    hEv hEs hB
  obtain ⟨σ6, r6, o6, v6, a6⟩ := (emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega))) σ5 trivial
  refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono (by unfold KprintS; omega), ?_⟩
  rw [o6, o5, o4, o3, o2, o1, hctx.vC]
  unfold outNums clientsN
  have hSN : SlotsN arr = S := hS
  rw [hSN]
  have hr : (List.range 3).flatMap (fun i => (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap fun c =>
      [2, dueN arr i c]) =
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 0 c]) ++
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 1 c]) ++
      (List.range (3 + 2 * arr.getD 0 0 + S)).flatMap (fun c => [2, dueN arr 2 c]) := by
    simp [List.range_succ]
  rw [hr]
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

end Lax117284Proofs.Machine.SatPrint
