import Lax117284Proofs.Machine.EmitNat
import Lax117284Proofs.Machine.Bits
import Lax808846Proofs.Transfer
import Lax808846Proofs.Tactic

/-!
Writing numbers and loops of writes: the code of a scalar, of a constant, or of an entry of an
array, and output steps that read the token array and compose, with a loop of them.
-/

namespace Lax117284Proofs.Machine.Out

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.EmitNat

abbrev V (s : String) : Expr := .var s

/-- Write the code of entry `x` of array `a`. -/
def emitAt (a x : String) : Com := .seq (.assign "v" (.get a (V x))) emitNat

lemma wvars_emitNat : emitNat.wvars = ["s", "u", "u", "s", "i2", "i2", "u", "i2", "u", "i2"] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.wvars]

lemma warrs_emitNat : emitNat.warrs = [] := by
  simp [emitNat, sizeLoop, sizeBody, onesLoop, onesBody, digLoop, digBody, Com.warrs]

variable {B : ℕ}

/-- **One number.** Everything but the scratch scalars and the output is left alone. -/
theorem emitAt_spec (a x : String) (Sz : ℕ) (hx : x ∉ ["v", "s", "u", "i2"]) :
    Spec B (fun σ => σ.vars x < (σ.arrs a).length ∧ σ.vars x < B ∧
        (σ.arrs a).getD (σ.vars x) 0 + 4 < B ∧ ((σ.arrs a).getD (σ.vars x) 0).size ≤ Sz)
      (emitAt a x)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat ((σ.arrs a).getD (σ.vars x) 0) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  · simp only [Env.setVar, if_true]
    exact ⟨‹_›, ‹_›⟩

abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f


/-- Write the code of the scalar `x`. -/
def emitVar (x : String) : Com := .seq (.assign "v" (.var x)) emitNat

theorem emitVar_spec (x : String) (Sz : ℕ) :
    Spec B (fun σ => σ.vars x + 4 < B ∧ (σ.vars x).size ≤ Sz) (emitVar x)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (σ.vars x) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  all_goals first
    | omega
    | (simp only [Env.setVar, if_true]; exact ⟨‹_›, ‹_›⟩)

/-- Write the code of the constant `n`. -/
def emitLit (n : ℕ) : Com := .seq (.assign "v" (.lit n)) emitNat

theorem emitLit_spec (n Sz : ℕ) (hn : n + 4 < B) (hs : n.size ≤ Sz) :
    Spec B (fun _ => True) (emitLit n)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat n ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (48 * Sz + 50) := by
  run_vcg [(emitNat_spec (B := B) Sz).frame]
  · obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ emitNat.wvars, _) ∧ _›
    refine ⟨by simpa [Env.setVar] using hout, fun y hy => ?_, ?_⟩
    · have h1 := hfv y (by
        rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
        tauto)
      have hyv : y ≠ "v" := fun h => hy (by simp [h])
      simpa [Env.setVar, hyv] using h1
    · funext b
      have := hfa b (by simp [warrs_emitNat])
      simpa [Env.setVar] using this
  all_goals first
    | omega
    | (simp only [Env.setVar, if_true]; exact ⟨hn, hs⟩)

/-- The scratch scalars of output steps. -/
def SCR : List String := ["v", "s", "u", "i2", "ix", "aa", "M"]

/-- Nothing but scratch scalars changed. -/
def Same (σ σ' : Env) : Prop := (∀ y ∉ SCR, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs

lemma Same.trans {σ σ' σ'' : Env} (h : Same σ σ') (h' : Same σ' σ'') : Same σ σ'' :=
  ⟨fun y hy => (h'.1 y hy).trans (h.1 y hy), h'.2.trans h.2⟩


/-- An output step: under `P` of the token array, the counter `i` and the base `b3`, the
command appends `bits` of the same three. -/
def OStep (B : ℕ) (c : Com) (P : List ℕ → ℕ → ℕ → Prop) (bits : List ℕ → ℕ → ℕ → List ℕ)
    (K : ℕ) : Prop :=
  Spec B (fun σ => P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3")) c
    (fun σ σ' => σ'.out = σ.out ++ bits (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") ∧ Same σ σ') K

lemma key_of_same {σ σ' : Env} (h : Same σ σ') :
    σ'.arrs "TK" = σ.arrs "TK" ∧ σ'.vars "i" = σ.vars "i" ∧ σ'.vars "b3" = σ.vars "b3" :=
  ⟨by rw [h.2], h.1 "i" (by decide), h.1 "b3" (by decide)⟩

/-- **Output steps compose.** -/
theorem OStep.seq {c d : Com} {P Q : List ℕ → ℕ → ℕ → Prop}
    {b e : List ℕ → ℕ → ℕ → List ℕ} {K K' : ℕ} (h : OStep B c P b K) (h' : OStep B d Q e K') :
    OStep B (.seq c d) (fun t i b3 => P t i b3 ∧ Q t i b3) (fun t i b3 => b t i b3 ++ e t i b3)
      (K + K') := by
  intro σ ⟨hP, hQ⟩
  obtain ⟨σ1, r1, o1, s1⟩ := h σ hP
  obtain ⟨k1, k2, k3⟩ := key_of_same s1
  obtain ⟨σ2, r2, o2, s2⟩ := h' σ1 (by
    show Q (σ1.arrs "TK") (σ1.vars "i") (σ1.vars "b3")
    rw [k1, k2, k3]; exact hQ)
  refine ⟨σ2, r1.seq r2, ?_, s1.trans s2⟩
  rw [o2, o1, k1, k2, k3, List.append_assoc]

theorem OStep.weaken {c : Com} {P P' : List ℕ → ℕ → ℕ → Prop}
    {b b' : List ℕ → ℕ → ℕ → List ℕ} {K K' : ℕ} (h : OStep B c P b K)
    (hP : ∀ t i b3, P' t i b3 → P t i b3) (hb : ∀ t i b3, P' t i b3 → b t i b3 = b' t i b3)
    (hK : K ≤ K') : OStep B c P' b' K' := by
  intro σ hσ
  obtain ⟨σ1, r1, o1, s1⟩ := h σ (hP _ _ _ hσ)
  exact ⟨σ1, r1.mono hK, by rw [o1, hb _ _ _ hσ], s1⟩

lemma same_of_frame {σ σ' : Env} (hv : ∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y)
    (ha : σ'.arrs = σ.arrs) : Same σ σ' :=
  ⟨fun y hy => hv y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto), ha⟩

/-- Write the code of the token at the index the expression `ie` computes. -/
def emitTK (ie : Expr) : Com := .seq (.assign "ix" ie) (emitAt "TK" "ix")

theorem oEmitTK (ie : Expr) (f : ℕ → ℕ → ℕ) (Sz : ℕ) (P : List ℕ → ℕ → ℕ → Prop)
    (hie : ∀ σ, P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") →
      ie.evalB B σ = some (f (σ.vars "i") (σ.vars "b3")))
    (hP : ∀ t i b3, P t i b3 → f i b3 < t.length ∧ f i b3 < B ∧ t.getD (f i b3) 0 + 4 < B ∧
      (t.getD (f i b3) 0).size ≤ Sz) :
    OStep B (emitTK ie) P (fun t i b3 => bitsNat (t.getD (f i b3) 0))
      (1 + ie.size + (48 * Sz + 50)) := by
  intro σ hσ
  obtain ⟨h1, h2, h3, h4⟩ := hP _ _ _ hσ
  have r1 : Run B (.assign "ix" ie) σ (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
      (1 + ie.size) := Run.assign (hie σ hσ)
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitAt_spec (B := B) "TK" "ix" Sz (by decide)
    (σ.setVar "ix" (f (σ.vars "i") (σ.vars "b3")))
    ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2,
      by simpa [Env.setVar] using h3, by simpa [Env.setVar] using h4⟩
  refine ⟨σ2, r1.seq r2, by simpa [Env.setVar] using o2, fun y hy => ?_, by
    rw [a2]; simp [Env.setVar]⟩
  have hix : y ≠ "ix" := fun h => hy (by simp [SCR, h])
  rw [v2 y (by
    simp only [SCR, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢; tauto)]
  simp [Env.setVar, hix]

/-! ### A loop of output steps -/

/-- The invariant of a loop printing rows `0, …, i - 1`. -/
def LInv (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ)
    (bits : List ℕ → ℕ → ℕ → List ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.arrs = A0 ∧ (∀ y ∉ SCR, y ≠ "i" → σ.vars y = v0 y) ∧ σ.vars "i" ≤ N ∧
    σ.out = out0 ++ (List.range (σ.vars "i")).flatMap fun i => bits (A0 "TK") i (v0 "b3")

theorem oLoop (mv : String) (c : Com) (P : List ℕ → ℕ → ℕ → Prop)
    (bits : List ℕ → ℕ → ℕ → List ℕ) (K : ℕ) (hc : OStep B c P bits K)
    (A0 : String → List ℕ) (v0 : String → ℕ) (N : ℕ) (out0 : List ℕ)
    (hmv : mv ∉ SCR) (hmi : mv ≠ "i") (hN : v0 mv = N) (hNB : N + 1 < B)
    (hP : ∀ i < N, P (A0 "TK") i (v0 "b3")) :
    Spec B (fun σ => LInv A0 v0 N bits out0 (σ.setVar "i" 0))
      (.seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var mv)) (.seq c (.assign "i" (.bin .add (V "i") (.lit 1))))))
      (fun _ σ' => LInv A0 v0 N bits out0 σ' ∧ σ'.vars "i" = N) ((K + 10 + 4) * N + 6) := by
  refine Spec.forRangeZero "i" mv (LInv A0 v0 N bits out0) N (K + 10) (by omega)
    (fun _ h => h.2.2.1) (fun σ h => (h.2.1 mv hmv hmi).trans hN) ?_
  intro σ ⟨⟨ha, hv, hle, hout⟩, hlt⟩
  have hb3 : σ.vars "b3" = v0 "b3" := hv "b3" (by decide) (by decide)
  obtain ⟨σ1, r1, o1, s1⟩ := hc σ (by
    show P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3")
    rw [ha, hb3]; exact hP _ hlt)
  obtain ⟨k1, k2, k3⟩ := key_of_same s1
  have r2 : Run B (.assign "i" (.bin .add (V "i") (.lit 1))) σ1 (σ1.setVar "i" (σ1.vars "i" + 1))
      (1 + (Expr.bin .add (V "i") (.lit 1)).size) :=
    Run.assign (evalB_bin (evalB_var (by rw [k2]; omega)) (evalB_lit (by omega))
      (by simp [k2]; omega))
  refine ⟨_, (r1.seq r2).mono (by simp [Expr.size]), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Env.setVar]; rw [s1.2, ha]
  · intro y hy hyi
    simp only [Env.setVar, if_neg hyi]
    rw [s1.1 y hy]; exact hv y hy hyi
  · simp [Env.setVar, k2]; omega
  · simp only [Env.setVar, if_true, k2]
    rw [o1, hout, List.range_succ, List.flatMap_append, ha, hb3]
    simp
  · simp [Env.setVar, k2]

/-! ### Writing the value of an expression -/

/-- Write the code of the value of `e`. -/
def emitVal (e : Expr) : Com := .seq (.assign "v" e) emitNat

theorem emitVal_spec (e : Expr) (f : Env → ℕ) (Sz : ℕ) :
    Spec B (fun σ => e.evalB B σ = some (f σ) ∧ f σ + 4 < B ∧ (f σ).size ≤ Sz) (emitVal e)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (f σ) ∧
        (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs)
      (1 + e.size + (48 * Sz + 40)) := by
  intro σ ⟨he, hB, hS⟩
  have r1 : Run B (.assign "v" e) σ (σ.setVar "v" (f σ)) (1 + e.size) := Run.assign he
  obtain ⟨σ2, r2, o2⟩ := (emitNat_spec (B := B) Sz).run (σ := σ.setVar "v" (f σ))
    (by simpa [Env.setVar] using ⟨hB, hS⟩)
  have hfr := ((emitNat_spec (B := B) Sz).frame).run (σ := σ.setVar "v" (f σ))
    (by simpa [Env.setVar] using ⟨hB, hS⟩)
  obtain ⟨σ3, r3, ⟨o3, hfv, hfa, -, -⟩⟩ := hfr
  refine ⟨σ3, (r1.seq r3).mono (by omega), by simpa [Env.setVar] using o3, fun y hy => ?_, ?_⟩
  · have h1 := hfv y (by
      rw [wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
      tauto)
    have hyv : y ≠ "v" := fun h => hy (by simp [h])
    simpa [Env.setVar, hyv] using h1
  · funext b
    have := hfa b (by simp [warrs_emitNat])
    simpa [Env.setVar] using this

/-- Write the code of the value of `e`, a function of the counter and the base. -/
theorem oEmitVal (e : Expr) (f : ℕ → ℕ → ℕ) (Sz : ℕ) (P : List ℕ → ℕ → ℕ → Prop)
    (hie : ∀ σ : Env, P (σ.arrs "TK") (σ.vars "i") (σ.vars "b3") →
      e.evalB B σ = some (f (σ.vars "i") (σ.vars "b3")))
    (hP : ∀ t i b3, P t i b3 → f i b3 + 4 < B ∧ (f i b3).size ≤ Sz) :
    OStep B (emitVal e) P (fun _ i b3 => bitsNat (f i b3)) (1 + e.size + (48 * Sz + 40)) := by
  intro σ hσ
  obtain ⟨hB, hS⟩ := hP _ _ _ hσ
  obtain ⟨σ', r, o, v, a⟩ := (emitVal_spec (B := B) e (fun σ => f (σ.vars "i") (σ.vars "b3")) Sz)
    σ ⟨hie σ hσ, hB, hS⟩
  exact ⟨σ', r, o, same_of_frame v a⟩

/-- **A loop of output steps, from a given state.** -/
def outLoop (mv : String) (c : Com) : Com :=
  .seq (.assign "i" (.lit 0))
    (.while (.lt (.var "i") (.var mv)) (.seq c (.assign "i" (.bin .add (V "i") (.lit 1)))))

theorem outLoop_spec (mv : String) (c : Com) (P : List ℕ → ℕ → ℕ → Prop)
    (bits : List ℕ → ℕ → ℕ → List ℕ) (K : ℕ) (hc : OStep B c P bits K)
    (hmv : mv ∉ SCR) (hmi : mv ≠ "i") (N : ℕ) (σ : Env) (hN : σ.vars mv = N) (hNB : N + 1 < B)
    (hP : ∀ i < N, P (σ.arrs "TK") i (σ.vars "b3")) :
    ∃ σ', Run B (outLoop mv c) σ σ' ((K + 10 + 4) * N + 6) ∧
      σ'.out = σ.out ++ (List.range N).flatMap (fun i => bits (σ.arrs "TK") i (σ.vars "b3")) ∧
      (∀ y ∉ SCR, y ≠ "i" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ', r, ⟨ha, hv, hle, ho⟩, hi⟩ := (oLoop (B := B) mv c P bits K hc σ.arrs σ.vars N
    σ.out hmv hmi hN hNB hP) σ ⟨rfl, fun y _ hyi => by simp [Env.setVar, hyi],
      by simp [Env.setVar], by simp [Env.setVar]⟩
  refine ⟨σ', r, ?_, fun y hy hyi => hv y hy hyi, ha⟩
  rw [ho, hi]

end Lax117284Proofs.Machine.Out
