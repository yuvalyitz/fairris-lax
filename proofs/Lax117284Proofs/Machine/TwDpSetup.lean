import Lax117284Proofs.Machine.TwDpRun

/-!
The setup of the dynamic program: the scalars it reads, and the proof that the context it needs
holds once they are set.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.Machine.TwViol

variable {P : Params} {B : ℕ}

/-- The scalars the dynamic program reads. -/
def dpSetup : Com := seqs
  [ .assign "kk" (V "k"),
    .assign "w1" (add (V "w") (Expr.lit 1)),
    .assign "Tm" (.bin .shiftl (Expr.lit 1) (mul (V "m") (V "w1"))),
    .assign "N" (G "O" (Expr.lit 1)) ]

/-- The state after `dpSetup`. -/
def setupState (σ : Env) (kv wv tabs : ℕ) : Env :=
  (((σ.setVar "kk" kv).setVar "w1" (wv + 1)).setVar "Tm" tabs).setVar "N"
    ((σ.arrs "O").getD 1 0)

theorem dpSetup_run (σ : Env) (kv wv m : ℕ) (hk : σ.vars "k" = kv) (hw : σ.vars "w" = wv)
    (hm : σ.vars "m" = m) (hkB : kv + 3 < B) (hwB : wv + 3 < B) (hmw : m * (wv + 1) + 3 < B)
    (hT : 2 ^ (m * (wv + 1)) + 3 < B) (hO : 1 < (σ.arrs "O").length)
    (hO1 : (σ.arrs "O").getD 1 0 < B) :
    ∃ σ1, Run B dpSetup σ σ1 60 ∧ σ1 = setupState σ kv wv (2 ^ (m * (wv + 1))) := by
  have hmm : m ≤ m * (wv + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold dpSetup seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | (simp only [hk, hw, hm, one_mul]; omega))
  all_goals (try simp only [setupState, hk, hw, hm, one_mul])

lemma tabs_eq (P : Params) : 2 ^ (P.m * (P.w + 1)) = P.tabs := by
  unfold Params.tabs Params.bs Params.wid
  rw [← pow_mul]

/-- **The context of the dynamic program holds after the setup.** -/
theorem nc_of_setup (P : Params) (σ : Env) (hn : σ.vars "n" = P.n) (hm : σ.vars "m" = P.m)
    (hmask : σ.vars "mask" = 2 ^ P.m - 1) (hbb : σ.vars "bb" = 2 ^ P.m)
    (hmn : σ.vars "mn" = P.m * P.n)
    (hX : σ.arrs "X" = P.y ++ [P.kk]) (hXB : ∀ v ∈ σ.arrs "X", v < B)
    (hO : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 = P.D.getD k 0)
    (hOB : ∀ k < P.D.length, (σ.arrs "O").getD (k + 1) 0 < B)
    (lenO : 3 * P.N + 5 ≤ (σ.arrs "O").length) (lenSZ : P.N ≤ (σ.arrs "SZ").length)
    (lenBG : P.N * P.wid ≤ (σ.arrs "BG").length)
    (lenTB : P.N * P.tabs ≤ (σ.arrs "TB").length)
    (b1 : P.N * P.tabs + P.tabs + 32 < B) (b2 : P.N * P.wid + P.wid + 32 < B)
    (b3 : 3 * P.N + 32 < B) (b4 : P.tabs * P.bs + 32 < B)
    (b5 : P.wid * (P.wid * P.m + 1) + P.wid * P.m + P.m + 32 < B)
    (b6 : (σ.arrs "X").length + 32 < B) (b7 : (σ.arrs "O").length + 32 < B)
    (b8 : P.n + P.m + P.kk + 32 < B) (b9 : P.m * (P.wid + 1) + P.wid + 32 < B)
    (b10 : 2 ^ P.m + 32 < B) :
    NC P B (setupState σ P.kk P.w P.tabs) := by
  have hDl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have harr : (setupState σ P.kk P.w P.tabs).arrs = σ.arrs := by simp [setupState, Env.setVar]
  have hN : (σ.arrs "O").getD 1 0 = P.N := by
    have := hO 0 (by omega)
    rw [show (0 : ℕ) + 1 = 1 from rfl] at this
    rw [this]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setupState, Env.setVar, hn]
  · simp [setupState, Env.setVar, hm]
  · simp [setupState, Env.setVar]
  · simp [setupState, Env.setVar, Params.wid]
  · simp [setupState, Env.setVar]
  · simp [setupState, Env.setVar, hmask]
  · simp [setupState, Env.setVar, hbb]
  · simp [setupState, Env.setVar, hmn]
  · simp only [setupState, vars_setVar, if_true, hN]
  · intro j hj; rw [harr, hX]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · rw [harr, hX]; simp
  · intro v hv; rw [harr] at hv; exact hXB v hv
  · intro k hk; rw [harr]; exact hO k hk
  · intro k hk; rw [harr]; exact hOB k hk
  · rw [harr]; exact lenO
  · rw [harr]; exact lenSZ
  · rw [harr]; exact lenBG
  · rw [harr]; exact lenTB
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · rw [harr]; exact b6
  · rw [harr]; exact b7
  · exact b8
  · exact b9
  · exact b10

end Lax117284Proofs.Machine.TwNode
