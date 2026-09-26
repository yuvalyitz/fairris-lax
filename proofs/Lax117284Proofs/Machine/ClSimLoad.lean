import Lax117284Proofs.Machine.ClSimRun

/-!
Loading the text of the program into its four arrays, and setting the constants of the word length.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The stores of one instruction at position `j`. -/
def storeInstr (j : ℕ) (i : Instr) : Com :=
  .seq (.store "ip0" (lit j) (lit (code i).1))
    (.seq (.store "ip1" (lit j) (lit (code i).2.1))
      (.seq (.store "ip2" (lit j) (lit (code i).2.2.1))
        (.store "ip3" (lit j) (lit (code i).2.2.2))))

/-- The stores of a list of instructions, from position `j`. -/
def loadFrom : ℕ → List Instr → Com
  | _, [] => .skip
  | j, i :: rest => .seq (storeInstr j i) (loadFrom (j + 1) rest)

/-- The array `A'` is `A` with the numbers `fs` written from position `j`. -/
def ArrLoad (A A' : List ℕ) (j : ℕ) (fs : List ℕ) : Prop :=
  A'.length = A.length ∧
    ∀ t, A'.getD t 0 = if j ≤ t ∧ t - j < fs.length then fs.getD (t - j) 0 else A.getD t 0

theorem ArrLoad.nil (A : List ℕ) (j : ℕ) : ArrLoad A A j [] := ⟨rfl, fun t => by simp⟩

theorem ArrLoad.cons {A A1 A' : List ℕ} {j x : ℕ} {fs : List ℕ} (hj : j < A.length)
    (h1 : A1 = A.set j x) (h : ArrLoad A1 A' (j + 1) fs) : ArrLoad A A' j (x :: fs) := by
  obtain ⟨hl, ht⟩ := h
  refine ⟨by rw [hl, h1, List.length_set], fun t => ?_⟩
  rw [ht t]
  by_cases hj1 : j + 1 ≤ t ∧ t - (j + 1) < fs.length
  · have : j ≤ t ∧ t - j < (x :: fs).length := ⟨by omega, by simp; omega⟩
    rw [if_pos hj1, if_pos this]
    have : t - j = (t - (j + 1)) + 1 := by omega
    rw [this]; simp
  · rw [if_neg hj1]
    by_cases htj : t = j
    · subst htj
      have : t ≤ t ∧ t - t < (x :: fs).length := ⟨le_rfl, by simp⟩
      rw [if_pos this, h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
    · have : ¬ (j ≤ t ∧ t - j < (x :: fs).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      rw [if_neg this, h1]
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm htj)]

/-- The effect of loading the instructions of `l` from position `j`. -/
def Loaded (j : ℕ) (l : List Instr) (σ σ' : Env) : Prop :=
  σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
  (∀ a, a ≠ "ip0" → a ≠ "ip1" → a ≠ "ip2" → a ≠ "ip3" → σ'.arrs a = σ.arrs a) ∧
  ArrLoad (σ.arrs "ip0") (σ'.arrs "ip0") j (l.map fun i => (code i).1) ∧
  ArrLoad (σ.arrs "ip1") (σ'.arrs "ip1") j (l.map fun i => (code i).2.1) ∧
  ArrLoad (σ.arrs "ip2") (σ'.arrs "ip2") j (l.map fun i => (code i).2.2.1) ∧
  ArrLoad (σ.arrs "ip3") (σ'.arrs "ip3") j (l.map fun i => (code i).2.2.2)

theorem arrLoad_single {A : List ℕ} {j x : ℕ} (hj : j < A.length) : ArrLoad A (A.set j x) j [x] :=
  ArrLoad.cons hj rfl (ArrLoad.nil _ _)

variable {B : ℕ}

theorem storeInstr_spec (j : ℕ) (i : Instr) (hjB : j < B) (hi : lits i < B) :
    Spec B (fun σ => j < (σ.arrs "ip0").length ∧ j < (σ.arrs "ip1").length ∧
        j < (σ.arrs "ip2").length ∧ j < (σ.arrs "ip3").length) (storeInstr j i)
      (fun σ σ' => Loaded j [i] σ σ') 20 := by
  have h1 := lit_le_lits i
  run_vcg
  all_goals try
    obtain ⟨hj0, hj1, hj2, hj3⟩ : j < (‹Env›.arrs "ip0").length ∧ j < (‹Env›.arrs "ip1").length ∧
      j < (‹Env›.arrs "ip2").length ∧ j < (‹Env›.arrs "ip3").length := ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro a h0 h1 h2 h3; simp [Env.setArr, h0, h1, h2, h3]
    · simpa [Env.setArr] using arrLoad_single (x := (code i).1) hj0
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.1) hj1
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.2.1) hj2
    · simpa [Env.setArr] using arrLoad_single (x := (code i).2.2.2) hj3

theorem ArrLoad.comp {A A1 A' : List ℕ} {j x : ℕ} {fs : List ℕ} (h1 : ArrLoad A A1 j [x])
    (h2 : ArrLoad A1 A' (j + 1) fs) : ArrLoad A A' j (x :: fs) := by
  obtain ⟨hl1, ht1⟩ := h1
  obtain ⟨hl2, ht2⟩ := h2
  refine ⟨by rw [hl2, hl1], fun t => ?_⟩
  rw [ht2 t]
  by_cases hin : j + 1 ≤ t ∧ t - (j + 1) < fs.length
  · have : j ≤ t ∧ t - j < (x :: fs).length := ⟨by omega, by simp; omega⟩
    rw [if_pos hin, if_pos this]
    have : t - j = (t - (j + 1)) + 1 := by omega
    rw [this]; simp
  · rw [if_neg hin]
    have := ht1 t
    by_cases htj : t = j
    · subst htj
      have hc : t ≤ t ∧ t - t < (x :: fs).length := ⟨le_rfl, by simp⟩
      rw [if_pos hc]
      simpa using this
    · have hc : ¬ (j ≤ t ∧ t - j < (x :: fs).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      have hc1 : ¬ (j ≤ t ∧ t - j < ([x] : List ℕ).length) := by
        intro ⟨h1', h2'⟩; simp at h2'; omega
      rw [if_neg hc]
      rw [if_neg hc1] at this
      exact this

theorem loadFrom_spec (l : List Instr) : ∀ j : ℕ, (∀ i ∈ l, lits i < B) → j + l.length < B →
    Spec B (fun σ => j + l.length ≤ (σ.arrs "ip0").length ∧ j + l.length ≤ (σ.arrs "ip1").length ∧
        j + l.length ≤ (σ.arrs "ip2").length ∧ j + l.length ≤ (σ.arrs "ip3").length)
      (loadFrom j l) (fun σ σ' => Loaded j l σ σ') (20 * l.length + 1) := by
  induction l with
  | nil =>
    intro j _ _
    refine Spec.mono (Spec.post Spec.skip fun σ σ' _ h => ?_) (by simp)
    subst h
    exact ⟨rfl, rfl, rfl, fun _ _ _ _ _ => rfl, ArrLoad.nil _ _, ArrLoad.nil _ _,
      ArrLoad.nil _ _, ArrLoad.nil _ _⟩
  | cons i rest ih =>
    intro j hl hjB
    have h1 := storeInstr_spec (B := B) j i (by simp at hjB; omega) (hl i (by simp))
    have h2 := ih (j + 1) (fun i' hi' => hl i' (by simp [hi'])) (by simp at hjB; omega)
    refine Spec.mono (Spec.seq (P' := fun σ => j + 1 + rest.length ≤ (σ.arrs "ip0").length ∧
        j + 1 + rest.length ≤ (σ.arrs "ip1").length ∧ j + 1 + rest.length ≤ (σ.arrs "ip2").length ∧
        j + 1 + rest.length ≤ (σ.arrs "ip3").length)
      (Spec.pre h1 fun σ h => by simp only [List.length_cons] at h; omega) h2 ?_ ?_) (by simp; omega)
    · intro σ σ1 hσ hL
      obtain ⟨-, -, -, -, ⟨l0, -⟩, ⟨l1, -⟩, ⟨l2, -⟩, ⟨l3, -⟩⟩ := hL
      simp only [List.length_cons] at hσ
      rw [l0, l1, l2, l3]
      omega
    · intro σ σ1 σ' hσ hL1 hL2
      obtain ⟨v1, i1, o1, a1, c01, c11, c21, c31⟩ := hL1
      obtain ⟨v2, i2, o2, a2, c02, c12, c22, c32⟩ := hL2
      refine ⟨v2.trans v1, i2.trans i1, o2.trans o1, fun a h0 h1 h2 h3 =>
        (a2 a h0 h1 h2 h3).trans (a1 a h0 h1 h2 h3), ?_, ?_, ?_, ?_⟩
      · exact ArrLoad.comp c01 c02
      · exact ArrLoad.comp c11 c12
      · exact ArrLoad.comp c21 c22
      · exact ArrLoad.comp c31 c32

end Lax117284Proofs.Machine.ClSim
