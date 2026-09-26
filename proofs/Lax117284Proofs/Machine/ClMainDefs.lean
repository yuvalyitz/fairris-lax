import Lax117284Proofs.Machine.ClMainWp

/-!
The main program's definitions: the largest entry, the largest literal of the oracle's program,
the array lengths the machine is started with, and the bounds of the entries of the integer
program's word.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The largest entry. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases le_total a (t.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h1 | h1
      · left; exact List.mem_cons_of_mem _ h1
      · right; exact h1
    · rw [max_eq_left h]; left; exact List.mem_cons_self

/-- The largest literal of a program. -/
def PB (P : Program) : ℕ :=
  P.foldr (fun i acc => max acc (max (code i).2.1 (max (code i).2.2.1 (code i).2.2.2))) 0

lemma le_PB {P : Program} {i : Lax808846.Ram.Instr} (hi : i ∈ P) :
    (code i).2.1 ≤ PB P ∧ (code i).2.2.1 ≤ PB P ∧ (code i).2.2.2 ≤ PB P := by
  induction P with
  | nil => cases hi
  | cons a t ih =>
    simp only [PB, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hi with rfl | h
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · have := ih h; omega

/-- The lengths the machine's arrays are started with. -/
def extF (P : Program) (c1 : ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "X" then x.length
  else if a = "cnt" then nT (x.getD 0 0)
  else if a = "okt" then nV (x.getD 0 0)
  else if a = "z" then zLen (x.getD 0 0)
  else if a = "bfsc" then x.getD 1 0 * x.getD 0 0
  else if a = "om" then 2 ^ Nat.clog 2 (c1 * (2 * zLen (x.getD 0 0) + x.getD 1 0 + 1) ^ (c1 - 1))
  else if a = "ip0" ∨ a = "ip1" ∨ a = "ip2" ∨ a = "ip3" then P.length
  else 0

section entries
variable (n m k : ℕ)

theorem coefRaw_le (r c : ℕ) : coefRaw n r c ≤ 1 := by
  unfold coefRaw
  split_ifs <;> omega

theorem zFunRaw_le (cnt : ℕ → ℕ) (M : ℕ) (hcnt : ∀ r, cnt r ≤ M) (idx : ℕ) :
    zFunRaw n m k cnt idx ≤ max (zLen n) (max m M) := by
  have h1 := (sizes_le_zLen n).2.2.2.1
  have h2 := (sizes_le_zLen n).2.2.2.2.1
  have h3 := (sizes_le_zLen n).2.2.2.2.2.2.2
  unfold zFunRaw
  split_ifs
  · omega
  · omega
  · have := coefRaw_le n ((idx - 2) / nN n) ((idx - 2) % nN n); omega
  · unfold rhsRaw
    split_ifs
    · have := hcnt (idx - 2 - nM n * nN n); omega
    · omega

theorem cntN_le (I : Instance) (r : ℕ) : cntN I r ≤ I.days := by
  unfold cntN
  calc _ ≤ (range I.days).card := Finset.card_filter_le _ _
    _ = I.days := Finset.card_range _

/-- Every entry of the word of the program is at most the larger of its length and `m`. -/
theorem mem_zList_le (I : Instance) (k : ℕ) {v : ℕ} (hv : v ∈ zList I.clients I.days k (cntN I)) :
    v ≤ max (zLen I.clients) I.days := by
  unfold zList at hv
  obtain ⟨idx, -, rfl⟩ := List.mem_map.mp hv
  have := zFunRaw_le I.clients I.days k (cntN I) I.days (cntN_le I) idx
  simpa using this

end entries

end Lax117284Proofs.Machine.ClMain
