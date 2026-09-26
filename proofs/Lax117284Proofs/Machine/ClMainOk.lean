import Lax117284Proofs.Machine.ClMainAll

/-!
The layout of the main program: the scalars and arrays it mentions and the depth of its
expressions, computed from the syntax, and the proof that a layout that has them compiles it.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs code simCom)
open Lax117284Proofs.Machine.ClBuild

/-- The scalars an expression mentions. -/
def eS : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => eS i
  | .bin _ e f => eS e ++ eS f

/-- The arrays an expression mentions. -/
def eA : Expr → List String
  | .lit _ => []
  | .var _ => []
  | .get a i => a :: eA i
  | .bin _ e f => eA e ++ eA f

/-- The number of temporaries an expression needs. -/
def eD : Expr → ℕ
  | .lit _ => 0
  | .var _ => 0
  | .get _ i => max (eD i) 1
  | .bin _ e f => max (eD f) (eD e + 1)

/-- The scalars a command mentions. -/
def cS : Com → List String
  | .skip => []
  | .assign x e => x :: eS e
  | .store _ i e => eS i ++ eS e
  | .seq c d => cS c ++ cS d
  | .ite b c d => eS (condExpr b) ++ (cS c ++ cS d)
  | .while b c => eS (condExpr b) ++ cS c
  | .read x => [x]
  | .write e => eS e

/-- The arrays a command mentions. -/
def cA : Com → List String
  | .skip => []
  | .assign _ e => eA e
  | .store a i e => a :: (eA i ++ eA e)
  | .seq c d => cA c ++ cA d
  | .ite b c d => eA (condExpr b) ++ (cA c ++ cA d)
  | .while b c => eA (condExpr b) ++ cA c
  | .read _ => []
  | .write e => eA e

/-- The number of temporaries a command needs. -/
def cD : Com → ℕ
  | .skip => 0
  | .assign _ e => eD e
  | .store _ i e => max (max (eD i) (eD e + 1)) 1
  | .seq c d => max (cD c) (cD d)
  | .ite b c d => max (eD (condExpr b)) (max (cD c) (cD d))
  | .while b c => max (eD (condExpr b)) (cD c)
  | .read _ => 0
  | .write e => max (eD e) 1

theorem expr_ok (L : Layout) : ∀ (e : Expr) (d : ℕ), (∀ y ∈ eS e, y ∈ L.scalars) →
    (∀ a ∈ eA e, a ∈ L.arrays) → d + eD e ≤ L.temps → Expr.Ok L e d
  | .lit _, d, _, _, _ => by simp [Expr.Ok]
  | .var x, d, hs, _, _ => by simpa [Expr.Ok, eS] using hs x (by simp [eS])
  | .get a i, d, hs, ha, hd => by
    simp only [Expr.Ok]
    refine ⟨ha a (by simp [eA]), expr_ok L i d hs (fun a' h => ha a' (by simp [eA, h]))
      (by simp only [eD] at hd; omega), by simp only [eD] at hd; omega⟩
  | .bin _ e f, d, hs, ha, hd => by
    simp only [Expr.Ok]
    simp only [eD] at hd
    refine ⟨expr_ok L f d (fun y h => hs y (by simp [eS, h])) (fun a h => ha a (by simp [eA, h]))
      (by omega),
      expr_ok L e (d + 1) (fun y h => hs y (by simp [eS, h])) (fun a h => ha a (by simp [eA, h]))
      (by omega), by omega⟩

theorem com_ok (L : Layout) : ∀ (c : Com), (∀ y ∈ cS c, y ∈ L.scalars) →
    (∀ a ∈ cA c, a ∈ L.arrays) → cD c ≤ L.temps → Com.Ok L c
  | .skip, _, _, _ => by simp [Com.Ok]
  | .assign x e, hs, ha, hd => by
    simp only [Com.Ok]
    exact ⟨hs x (by simp [cS]), expr_ok L e 0 (fun y h => hs y (by simp [cS, h]))
      (fun a h => ha a (by simpa [cA] using h)) (by simpa [cD] using hd)⟩
  | .store a i e, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    refine ⟨ha a (by simp [cA]), expr_ok L i 0 (fun y h => hs y (by simp [cS, h]))
      (fun a' h => ha a' (by simp [cA, h])) (by omega),
      expr_ok L e 1 (fun y h => hs y (by simp [cS, h])) (fun a' h => ha a' (by simp [cA, h]))
      (by omega), by omega⟩
  | .seq c d, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    exact ⟨com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L d (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .ite b c d, hs, ha, hd => by
    simp only [Com.Ok, Cond.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L _ 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L d (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .while b c, hs, ha, hd => by
    simp only [Com.Ok, Cond.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L _ 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .read x, hs, _, _ => by simpa [Com.Ok, cS] using hs x (by simp [cS])
  | .write e, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L e 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), by omega⟩

/-- The arrays of the machine. -/
def arrs10 : List String := ["X", "cnt", "okt", "z", "ip0", "ip1", "ip2", "ip3", "om", "bfsc"]

theorem loadFrom_names (P : List Instr) (j : ℕ) : cS (ClSim.loadFrom j P) = [] ∧
    (∀ a ∈ cA (ClSim.loadFrom j P), a ∈ arrs10) ∧ cD (ClSim.loadFrom j P) ≤ 1 := by
  induction P generalizing j with
  | nil => simp [ClSim.loadFrom, cS, cA, cD]
  | cons i rest ih =>
    obtain ⟨h1, h2, h3⟩ := ih (j + 1)
    simp only [ClSim.loadFrom, ClSim.storeInstr, cS, cA, cD, eS, eA, eD, List.nil_append, h1,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ClSim.lit]
    refine ⟨trivial, ?_, ?_⟩
    · intro a ha
      rcases ha with (h | h | h | h) | h
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · exact h2 a h
    · omega

/-- A command fits: its arrays are the machine's and it needs at most twelve temporaries. -/
def Fine (c : Com) : Prop := (∀ a ∈ cA c, a ∈ arrs10) ∧ cD c ≤ 12

theorem fine_read : Fine readCom := by unfold Fine; decide +kernel
theorem fine_crit : Fine critCom := by unfold Fine; decide +kernel
theorem fine_build : Fine buildCom := by unfold Fine; decide +kernel
theorem fine_brute : Fine ClBrute.bruteCom := by unfold Fine; decide +kernel
theorem Fine.seq' {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_mulSteps (n : ℕ) : Fine (mulSteps n) := by
  induction n with
  | zero => unfold Fine; simp [mulSteps, cA, cD]
  | succ n ih =>
    have h0 : Fine (asg "tg" (mul (V "tg") (V "bs"))) := by unfold Fine; decide +kernel
    exact Fine.seq' h0 ih

theorem fine_wp (c1 E : ℕ) : Fine (wpCom c1 E) := by
  have h1 : Fine (asg "bs" (add (add (mul (lit 2) (V "zl")) (V "m")) (lit 1))) := by
    unfold Fine; decide +kernel
  have h2 : Fine (asg "tg" (lit c1)) := by
    unfold Fine; simp [asg, ClSim.lit, cA, cD, eA, eD]
  have h3 : Fine (asg "wpv" (lit 0)) := by unfold Fine; decide +kernel
  have h4 : Fine (asg "Mp" (lit 1)) := by unfold Fine; decide +kernel
  have h5 : Fine wpLoop := by unfold Fine; decide +kernel
  exact h1.seq' (h2.seq' ((fine_mulSteps E).seq' (h3.seq' (h4.seq' h5))))
theorem fine_simInit (P : Program) : Fine (ClSim.simInit P) := by
  have : Fine (ClSim.simInit []) := by unfold Fine; decide +kernel
  exact this
theorem fine_interp : Fine ClSim.interpLoop := by unfold Fine; decide +kernel
theorem fine_sc : Fine (asg "sc" scE) := by unfold Fine; decide +kernel
theorem fine_write_outv : Fine (Com.write (V "outv")) := by unfold Fine; decide +kernel
theorem fine_write_bfans : Fine (Com.write (V "bfans")) := by unfold Fine; decide +kernel
theorem fine_write_zero : Fine (Com.write (lit 0)) := by unfold Fine; decide +kernel
theorem eD_fit : eD (condExpr (.lt (lit 0) (V "fit"))) ≤ 12 := by decide +kernel
theorem eD_sc : eD (condExpr (.lt (lit 0) (V "sc"))) ≤ 12 := by decide +kernel

theorem Fine.seq {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem Fine.ite {b : Cond} {c d : Com} (hb : eD (condExpr b) ≤ 12) (hbA : ∀ a ∈ eA (condExpr b), a ∈ arrs10)
    (h1 : Fine c) (h2 : Fine d) : Fine (.ite b c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha | ha
    · exact hbA a ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_loadFrom (P : List Instr) (j : ℕ) : Fine (ClSim.loadFrom j P) := by
  obtain ⟨-, h2, h3⟩ := loadFrom_names P j
  exact ⟨h2, by omega⟩

theorem fine_sim (P : Program) : Fine (simCom P) :=
  ((fine_loadFrom P 0).seq (fine_simInit P)).seq fine_interp

theorem fine_fitRun (P : Program) (c1 : ℕ) : Fine (fitRun P c1) :=
  fine_build.seq ((fine_wp c1 (c1 - 1)).seq ((fine_sim P).seq fine_write_outv))

theorem fine_fitBranch (P : Program) (c1 : ℕ) : Fine (fitBranch P c1) :=
  fine_sc.seq (Fine.ite eD_sc (by decide +kernel) fine_write_zero (fine_fitRun P c1))

theorem fine_main (P : Program) (c1 : ℕ) : Fine (mainCom P c1) :=
  fine_read.seq (fine_crit.seq (Fine.ite eD_fit (by decide +kernel) (fine_fitBranch P c1)
    (fine_brute.seq fine_write_bfans)))

end Lax117284Proofs.Machine.ClMain
