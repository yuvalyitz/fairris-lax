import Lax117284Proofs.Machine.JitPass

/-!
Writing the image of Theorem 11: the two counts, the table of `(p, d)` cell by cell, and the
parameter `1`.
-/

namespace Lax117284Proofs.Machine.JitPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.JitSem Lax117284Proofs.Machine.JitCheck Lax117284Proofs.Machine.JitPass

variable {B : ℕ}

/-- The loop over the table: run the pass. -/
theorem jokLoop_spec (arr : List ℕ) (m n ok0 : ℕ) (σ : Env)
    (hn0v : σ.vars "n" = n) (ho0v : σ.vars "o" = 2 + n)
    (hE : ∀ k < 2 + n + m * n, arr.getD k 0 + 8 < B) (hL : 2 + n + m * n + 8 < B)
    (hlen : 2 + n + m * n ≤ arr.length) (hnB : n + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hNv : σ.vars "N" = m * n) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B jokLoop σ σ' ((80 + 4) * (m * n) + 6) ∧
      σ'.vars "ok" = flagTo (PassJ arr n) ok0 (m * n) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ∉ AJ → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := jokBody) "i" "N"
    (JInv arr m n ok0 σ) (m * n) 80 (by omega) (fun _ h => h.hi) (fun _ h => h.vN)
    (jokBody_spec arr m n ok0 σ hn0v ho0v hE hL hlen hnB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, by simp [Env.setVar, hNv],
      by simp [Env.setVar], by
        simp only [Env.setVar]
        simp [flagTo_zero (PassJ arr n) ok0 hok0, hok], fun y hy => by
      have hyi : y ≠ "i" := fun h => hy (by simp [AJ, h])
      simp [Env.setVar, hyi]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y hy
    rw [hI.fr y hy]

/-- Write a cell of the image. -/
def cellPrint : Com :=
  .seq cellIdx (.seq (emitAt "TK" "ip") (emitAt "TK" "ij"))

/-- Scratch scalars of a cell. -/
def SJ : List String := AI ++ SCR

/-- The cost of a cell. -/
def KcellJ (Sz : ℕ) : ℕ := 30 + 2 * (48 * Sz + 50) + 20

/-- **A cell of the image.** -/
theorem cellPrint_run (Sz : ℕ) (arr : List ℕ) (n o c : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr)
    (hi : σ.vars "i" = c) (hn : σ.vars "n" = n) (ho : σ.vars "o" = 2 + n) (hn0 : 0 < n)
    (hc : c < B) (hnB : n < B) (hoB : 2 + n + c < B)
    (hp : 2 + n + c < arr.length) (hd : 2 + (c - c / n * n) < arr.length)
    (hpB : arr.getD (2 + n + c) 0 + 4 < B) (hdB : arr.getD (2 + (c - c / n * n)) 0 + 4 < B) :
    ∃ σ', Run B cellPrint σ σ' (KcellJ Sz) ∧
      σ'.out = σ.out ++ (bitsNat (arr.getD (2 + n + c) 0) ++
        bitsNat (arr.getD (2 + (c - c / n * n)) 0)) ∧
      (∀ y ∉ SJ, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  have hq : c / n * n ≤ c := Nat.div_mul_le_self c n
  obtain ⟨σ1, r1, a1, o1, hip, hij, hfr1⟩ := cellIdx_run (B := B) n (2 + n) c σ hi hn ho hc hnB
    hn0 hoB
  have hA1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "TK" "ip" Sz (by decide) σ1
    ⟨by rw [hA1, hip]; exact hp, by rw [hip]; omega, by rw [hA1, hip]; exact hpB,
      by rw [hA1, hip]; exact hs _ hpB⟩
  have hij2 : σ2.vars "ij" = 2 + (c - c / n * n) := by rw [v2 "ij" (by decide)]; exact hij
  have hA2 : σ2.arrs "TK" = arr := by rw [a2]; exact hA1
  obtain ⟨σ3, r3, o3, v3, a3⟩ := emitAt_spec (B := B) "TK" "ij" Sz (by decide) σ2
    ⟨by rw [hA2, hij2]; exact hd, by rw [hij2]; omega, by rw [hA2, hij2]; exact hdB,
      by rw [hA2, hij2]; exact hs _ hdB⟩
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by unfold KcellJ; omega), ?_, fun y hy => ?_, ?_⟩
  · rw [o3, o2, o1, hA2, hA1, hij2, hip, List.append_assoc]
  · have hyAI : y ∉ AI := fun h => hy (List.mem_append_left _ h)
    have hyS : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SJ, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v3 y hyS, v2 y hyS, hfr1 y hyAI]
  · rw [a3, a2, a1]

end Lax117284Proofs.Machine.JitPrint
