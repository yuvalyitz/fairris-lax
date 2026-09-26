import Lax117284Proofs.Machine.TwSetup1
import Lax117284Proofs.Machine.TwViol

/-!
Loading the code of the cited program into the arrays the interpreter reads.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

variable {B : ℕ}

/-- The four numbers of an instruction, stored at position `i`. -/
def storeIns (i : ℕ) (ins : Instr) : Com := seqs
  [ .store "OP" (Expr.lit i) (Expr.lit (opcode ins)),
    .store "XA" (Expr.lit i) (Expr.lit (fa ins)),
    .store "XB" (Expr.lit i) (Expr.lit (fb ins)),
    .store "XC" (Expr.lit i) (Expr.lit (fc ins)) ]

/-- The code of a list of instructions, from position `i` on. -/
def loadFrom : ℕ → List Instr → Com
  | _, [] => .skip
  | i, ins :: rest => .seq (storeIns i ins) (loadFrom (i + 1) rest)

/-- The list `l` with the entries from position `i` on replaced by `vs`. -/
def setFrom : List ℕ → ℕ → List ℕ → List ℕ
  | l, _, [] => l
  | l, i, v :: vs => setFrom (l.set i v) (i + 1) vs

lemma setFrom_length (vs : List ℕ) : ∀ (l : List ℕ) (i : ℕ), (setFrom l i vs).length = l.length := by
  induction vs with
  | nil => intro l i; rfl
  | cons v vs ih => intro l i; simp [setFrom, ih]

lemma getD_set'' (l : List ℕ) (i j v : ℕ) :
    (l.set i v).getD j 0 = if j = i ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

lemma setFrom_getD (vs : List ℕ) : ∀ (l : List ℕ) (i : ℕ), i + vs.length ≤ l.length → ∀ k,
    (setFrom l i vs).getD k 0 = if i ≤ k ∧ k < i + vs.length then vs.getD (k - i) 0 else l.getD k 0 := by
  induction vs with
  | nil => intro l i h k; simp [setFrom]
  | cons v vs ih =>
    intro l i h k
    have hlen : (v :: vs).length = vs.length + 1 := rfl
    have h' : i + 1 + vs.length ≤ l.length := by omega
    simp only [setFrom]
    rw [ih (l.set i v) (i + 1) (by rw [List.length_set]; omega) k, getD_set'', hlen]
    by_cases hk : k = i
    · subst hk
      rw [if_neg (by omega), if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
      simp
    · by_cases hk2 : i + 1 ≤ k ∧ k < i + 1 + vs.length
      · rw [if_pos hk2, if_pos (by omega)]
        have : k - i = (k - (i + 1)) + 1 := by omega
        rw [this]; simp
      · rw [if_neg hk2, if_neg (by omega), if_neg (by omega)]

/-- **Replacing all of a list of zeros.** -/
lemma setFrom_replicate (vs : List ℕ) : setFrom (List.replicate vs.length 0) 0 vs = vs := by
  apply List.ext_getElem
  · rw [setFrom_length]; simp
  · intro k h1 h2
    have := setFrom_getD vs (List.replicate vs.length 0) 0 (by simp) k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp only [Option.getD_some] at this
    rw [this, if_pos ⟨by omega, by omega⟩, Nat.sub_zero, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    simp

theorem storeIns_run (i : ℕ) (ins : Instr) (σ : Env)
    (hOP : i < (σ.arrs "OP").length) (hXA : i < (σ.arrs "XA").length)
    (hXB : i < (σ.arrs "XB").length) (hXC : i < (σ.arrs "XC").length)
    (hi : i + 3 < B) (h1 : opcode ins + 3 < B) (h2 : fa ins + 3 < B) (h3 : fb ins + 3 < B)
    (h4 : fc ins + 3 < B) :
    ∃ σ1, Run B (storeIns i ins) σ σ1 12 ∧ σ1 = (((σ.setArr "OP" i (opcode ins)).setArr "XA" i
      (fa ins)).setArr "XB" i (fb ins)).setArr "XC" i (fc ins) := by
  unfold storeIns seqs
  run_vcg
  all_goals first | omega | rfl

end Lax117284Proofs.Machine.TwSetup
