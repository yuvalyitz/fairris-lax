import Lax117284Proofs.Machine.JitHardFormat
import Lax117284Proofs.Machine.JitHardLoop
import Lax117284Proofs.Machine.Lists

/-!
The image of interval scheduling with eligible machine sets, as a list of numbers, and the
loops that write it.
-/

namespace Lax117284Proofs.Machine.JitHardSem

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.JitHardLoop
open Lax117284Proofs.Machine.JitHardFormat

/-- The number of walls: one per machine, unless there is no job. -/
def wallsN (n m : ℕ) : ℕ := m * (n - (n - 1))

lemma wallsN_le (n m : ℕ) : wallsN n m ≤ m := by
  unfold wallsN
  calc m * (n - (n - 1)) ≤ m * 1 := Nat.mul_le_mul_left m (by omega)
    _ = m := Nat.mul_one m

lemma wallsN_pos (n m : ℕ) (h : 0 < n) : wallsN n m = m := by
  unfold wallsN
  have : n - (n - 1) = 1 := by omega
  rw [this, Nat.mul_one]

lemma wallsN_zero (m : ℕ) : wallsN 0 m = 0 := by simp [wallsN]

/-- The processing time of a job on a machine, from the bit of the matrix, the processing time
of the job and its deadline. -/
def cellV (bt pp dd : ℕ) : ℕ := bt * pp + (1 - bt) * (dd + 1)

/-- The processing time of job `j` on machine `i`, read off the numbers of the input. -/
def cellN (ns : List ℕ) (i j : ℕ) : ℕ :=
  cellV (ns.getD (2 + 3 * ns.getD 0 0 + j * ns.getD 1 0 + i) 0) (ns.getD (2 + j) 0)
    (ns.getD (2 + ns.getD 0 0 + j) 0)

/-- The deadline of job `j` plus one. -/
def dueN (ns : List ℕ) (j : ℕ) : ℕ := ns.getD (2 + ns.getD 0 0 + j) 0 + 1

/-- The image, as a list of numbers. -/
def outH (ns : List ℕ) : List ℕ :=
  [ns.getD 0 0 + wallsN (ns.getD 0 0) (ns.getD 1 0), ns.getD 1 0] ++
    (List.range (ns.getD 0 0)).map (dueN ns) ++
    List.replicate (wallsN (ns.getD 0 0) (ns.getD 1 0)) 1 ++
    (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap fun i =>
      (List.range (ns.getD 0 0)).map (cellN ns i) ++
        List.replicate (wallsN (ns.getD 0 0) (ns.getD 1 0)) 1

/-- What the accepting phase reads: the numbers of the input are at the start of the array. -/
def CellPre (ns : List ℕ) (σ : Env) : Prop :=
  (∀ k < ns.length, (σ.arrs "TK").getD k 0 = ns.getD k 0) ∧
    ns.length ≤ (σ.arrs "TK").length ∧
    σ.vars "n" = ns.getD 0 0 ∧ σ.vars "m" = ns.getD 1 0 ∧ σ.vars "o1" = 2 + ns.getD 0 0 ∧
    σ.vars "o2" = 2 + 3 * ns.getD 0 0

/-- The command that writes the processing time of job `jj` on machine `i`. -/
def cellBody : Com :=
  .seq (.assign "bt" (.get "TK" (add (add (V "o2") (mul (V "jj") (V "m"))) (V "i"))))
  (.seq (.assign "pp" (.get "TK" (add (.lit 2) (V "jj"))))
  (.seq (.assign "dd" (.get "TK" (add (V "o1") (V "jj"))))
    (emitVal (add (mul (V "bt") (V "pp")) (mul (sub (.lit 1) (V "bt")) (add (V "dd") (.lit 1)))))))

/-- The scratch scalars of a cell. -/
def SCELL : List String := ["bt", "pp", "dd"] ++ SCR

variable {B : ℕ}

/-- **A cell, on the three numbers it reads.** -/
theorem cellCore (Sz bv pv dv : ℕ) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hbv : bv ≤ 1)
    (hp : bv * pv + (1 - bv) * (dv + 1) + 4 < B) (hB : bv + pv + dv + 8 < B) :
    Spec B (fun σ =>
        σ.vars "o2" + σ.vars "jj" * σ.vars "m" + σ.vars "i" < (σ.arrs "TK").length ∧
        σ.vars "o2" + σ.vars "jj" * σ.vars "m" + σ.vars "i" < B ∧
        (σ.arrs "TK").getD (σ.vars "o2" + σ.vars "jj" * σ.vars "m" + σ.vars "i") 0 = bv ∧
        2 + σ.vars "jj" < (σ.arrs "TK").length ∧ 2 + σ.vars "jj" < B ∧
        (σ.arrs "TK").getD (2 + σ.vars "jj") 0 = pv ∧
        σ.vars "o1" + σ.vars "jj" < (σ.arrs "TK").length ∧ σ.vars "o1" + σ.vars "jj" < B ∧
        (σ.arrs "TK").getD (σ.vars "o1" + σ.vars "jj") 0 = dv ∧
        σ.vars "m" < B ∧ σ.vars "jj" < B ∧ σ.vars "i" < B ∧ σ.vars "o1" < B ∧
        σ.vars "o2" < B) cellBody
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (cellV bv pv dv) ∧
        σ'.arrs = σ.arrs ∧ ∀ y ∉ SCELL, σ'.vars y = σ.vars y) (48 * Sz + 200) := by
  unfold cellBody emitVal
  run_vcg [(EmitNat.emitNat_spec (B := B) Sz).frame]
  all_goals (
    have e1 := ‹(σ.arrs "TK").getD (σ.vars "o2" + σ.vars "jj" * σ.vars "m" + σ.vars "i") 0 = bv›
    have e2 := ‹(σ.arrs "TK").getD (2 + σ.vars "jj") 0 = pv›
    have e3 := ‹(σ.arrs "TK").getD (σ.vars "o1" + σ.vars "jj") 0 = dv›
    try simp at e1 e2 e3
    try simp [e1, e2, e3] at *
    first
    | omega
    | exact ⟨hp, hs _ hp⟩
    | (obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ EmitNat.emitNat.wvars, _) ∧ _›
       refine ⟨by rw [hout]; rfl, ?_, fun y hy => ?_⟩
       · funext b; exact hfa b (by simp [Out.warrs_emitNat])
       · simp only [SCELL, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
           not_or] at hy
         obtain ⟨h1, h2, h3, h4, hrest⟩ := hy
         have hy1 : y ∉ EmitNat.emitNat.wvars := by
           rw [Out.wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
           tauto
         rw [hfv y hy1]
         simp [h1, h2, h3, h4]))

lemma cellV_le (bv pv dv : ℕ) (h : bv ≤ 1) : cellV bv pv dv ≤ pv + dv + 1 := by
  unfold cellV
  interval_cases bv <;> simp <;> omega

lemma idx_lt (n m jj i : ℕ) (hjj : jj < n) (hi : i < m) : jj * m + i < n * m := by
  calc jj * m + i < jj * m + m := by omega
    _ = (jj + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right m (by omega)

theorem cellBody_spec (Sz : ℕ) (ns : List ℕ) (hsh : ShapeH ns)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B) (hL : 4 * ns.length + 16 < B) :
    Spec B (fun σ => CellPre ns σ ∧ σ.vars "jj" < ns.getD 0 0 ∧
        σ.vars "i" < wallsN (ns.getD 0 0) (ns.getD 1 0)) cellBody
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (cellN ns (σ.vars "i") (σ.vars "jj")) ∧
        σ'.arrs = σ.arrs ∧ ∀ y ∉ SCELL, σ'.vars y = σ.vars y) (48 * Sz + 200) := by
  intro σ ⟨⟨hA, hlen, hn, hm, ho1, ho2⟩, hjj, hi⟩
  obtain ⟨hsh2, hshl, hshb⟩ := hsh
  have hn0 : 0 < ns.getD 0 0 := by omega
  have hW : wallsN (ns.getD 0 0) (ns.getD 1 0) = ns.getD 1 0 := wallsN_pos _ _ hn0
  rw [hW] at hi
  have hidx := idx_lt (ns.getD 0 0) (ns.getD 1 0) (σ.vars "jj") (σ.vars "i") hjj hi
  have hE0 := hE 0 (by omega)
  have hE1 := hE 1 (by omega)
  have hLt : ∀ k, k < ns.length → k < B := fun k hk => by omega
  have hidxl : 2 + 3 * ns.getD 0 0 + σ.vars "jj" * ns.getD 1 0 + σ.vars "i" < ns.length := by omega
  have hEi := hE _ hidxl
  have hE2 := hE (2 + σ.vars "jj") (by omega)
  have hE3 := hE (2 + ns.getD 0 0 + σ.vars "jj") (by omega)
  have hbv := hshb _ (by omega) hidxl
  obtain ⟨σ', r, hout, harr, hfv⟩ := cellCore (B := B) Sz
    (ns.getD (2 + 3 * ns.getD 0 0 + σ.vars "jj" * ns.getD 1 0 + σ.vars "i") 0)
    (ns.getD (2 + σ.vars "jj") 0) (ns.getD (2 + ns.getD 0 0 + σ.vars "jj") 0) hs hbv
    (by
      have := cellV_le _ (ns.getD (2 + σ.vars "jj") 0) (ns.getD (2 + ns.getD 0 0 + σ.vars "jj") 0) hbv
      unfold cellV at this
      omega) (by omega) σ
    ⟨by rw [ho2, hm]; omega, by rw [ho2, hm]; omega,
      by rw [ho2, hm]; exact hA _ hidxl, by omega, by omega,
      hA _ (by omega) , by rw [ho1]; omega, by rw [ho1]; omega,
      by rw [ho1]; exact hA _ (by omega),
      by rw [hm]; omega, by omega, by omega, by rw [ho1]; omega, by rw [ho2]; omega⟩
  exact ⟨σ', r.mono (by omega), by rw [hout]; rfl, harr, hfv⟩

end Lax117284Proofs.Machine.JitHardSem
