import Lax117284Proofs.Treewidth.Fun.VMRamTop

/-!
# WP V3 (1): the loaded program — a function-entry table cut off at `N`, and `vm_ram_correct` for it

`vm_ram_correct` (V2) is stated for `mkProg Δ N main k B`, whose entry table `ft f = offset Δ f` is defined for *all*
`f`.  Its `Cst` therefore asks the array `FT` to be correct on the whole range `0 … W`, and `W` is (a multiple of) the
run-time word bound, which is *not* affordable to fill.  The function ids that a run ever calls are all `< N`
(`Δ f = some _`), so nothing is lost by cutting the table: `mkProgF` is `mkProg` with `ft f = 0` for `f ≥ N`, and the
V1/V2 proofs go through verbatim (they only use `Prog.Real` and the stub).  Here the two theorems are re-stated for it.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- The IMP+ environment (`Env` alone means the VM's `Env`, in this namespace). -/
abbrev IEnv : Type := Lax808846Proofs.Imp.Env

/-- `mkProg` with the entry table cut off at `N` (`ft f = 0` for `f ≥ N`, where `Δ f = none`). -/
def mkProgF (Δ : ℕ → Option Tm) (N main k B : ℕ) : Prog :=
  { mkProg Δ N main k B with ft := fun f => if f < N then offset Δ f else 0 }

theorem mkProgF_code (Δ : ℕ → Option Tm) (N main k B : ℕ) :
    (mkProgF Δ N main k B).code = (mkProg Δ N main k B).code := rfl
theorem mkProgF_len (Δ : ℕ → Option Tm) (N main k B : ℕ) :
    (mkProgF Δ N main k B).len = (mkProg Δ N main k B).len := rfl
theorem mkProgF_B (Δ : ℕ → Option Tm) (N main k B : ℕ) : (mkProgF Δ N main k B).B = B := rfl
theorem mkProgF_ft (Δ : ℕ → Option Tm) (N main k B f : ℕ) :
    (mkProgF Δ N main k B).ft f = if f < N then offset Δ f else 0 := rfl

theorem mkProgF_real (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main k B : ℕ) :
    (mkProgF Δ N main k B).Real Δ := by
  intro f body hf
  have hfN : f < N := by
    by_contra h
    have := hN f (by omega); rw [this] at hf; simp at hf
  have hfit := mkProg_fits Δ hfN main k B
  have hcode : funCode Δ f = compile id body ++ [.ret] := by simp [funCode, hf]
  rw [hcode] at hfit
  have hft : (mkProgF Δ N main k B).ft f = offset Δ f := by rw [mkProgF_ft, if_pos hfN]
  have h1 := hfit.1
  have h2 := le_offset Δ f
  have hft' : (mkProg Δ N main k B).ft f = offset Δ f := rfl
  refine ⟨?_, ?_⟩
  · show f ≤ (mkProg Δ N main k B).len
    omega
  · rw [hft]
    rw [hft'] at hfit
    exact hfit

theorem mkProgF_stub (Δ : ℕ → Option Tm) (N main k B : ℕ) :
    FitsAt (mkProgF Δ N main k B) 0 (stub main k) := mkProg_stub Δ N main k B

/-- V1 (`vm_runs`) for any program that realizes the table and starts with the stub. -/
theorem vm_runs_gen {P : Prog} (Δ : ℕ → Option Tm) (hreal : P.Real Δ) {main : ℕ} {xs : List Val}
    (hstub : FitsAt P 0 (stub main xs.length)) (hB : 2 ≤ P.B) {y : Val} {c : ℕ}
    (h : Runs Δ P.B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL P.B H ws xs) {W : ℕ}
    (hbd : St.Bd W ⟨0, ws ++ stk₀, [], H⟩) (hL : P.len ≤ W)
    (hheap : P.B + H.length + c ≤ W) (hstk : (ws ++ stk₀).length + 3 * c ≤ W) (hret : 3 * c + 1 ≤ W) :
    ∃ n ≤ 3 * c + 3, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB P W n ⟨0, ws ++ stk₀, [], H⟩ ⟨2, w :: stk₀, [], H'⟩ ∧
        HExt H H' ∧ Rep P.B H' w y ∧ H'.length ≤ H.length + c := by
  obtain ⟨body, hΔ, c', hc', hev⟩ := h
  have hsim := ev_sim hB hreal hev
  have hpos := hev.pos
  have hlen3 : 3 ≤ P.len := by simpa [stub] using hstub.1
  have hcode0 : P.code 0 = .lit main := by simpa [stub] using hstub.head
  have hcode1 : P.code 1 = .call ws.length := by
    have := (hstub.tail).head
    simpa [stub, hrep.length_eq] using this
  have hmain : main ≤ W := Nat.le_trans (hreal main body hΔ).1 hL
  have hstep := step_lit (P := P) (s := ⟨0, ws ++ stk₀, [], H⟩) hcode0
  have hbd₁ : St.Bd W ⟨0 + 1, main :: (ws ++ stk₀), [], H⟩ :=
    hbd.setStk (by omega) (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmain
      · exact hbd.stk x hx) (by simp only [List.length_cons]; omega)
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := callee_run hreal hΔ hsim (ws := ws) (stk₀ := stk₀) (ret₀ := [])
    (H := H) (pcc := 1) hcode1 hrep hbd₁ hL (by omega) (by omega) (by omega) (by show 0 + 1 + 3 * c' ≤ W; omega)
  exact ⟨n + 1, by omega, w, H', StepsB.step hbd hstep hs, hx, hr, by omega⟩

/-- **`vm_ram_correct` for the cut table** (statement of V2 with `mkProgF`). -/
theorem vm_ram_correctF (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) {B : ℕ} (hB : 2 ≤ B)
    {main : ℕ} {xs : List Val} {y : Val} {c : ℕ} (h : Runs Δ B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL B H ws xs) {W₀ : ℕ} (hbd : St.Bd W₀ ⟨0, ws ++ stk₀, [], H⟩)
    {Bi : ℕ} {σ : Lax808846Proofs.Imp.Env}
    (hA : Abs ⟨0, ws ++ stk₀, [], H⟩ σ)
    (hC : Cst (mkProgF Δ N main xs.length B)
      (W₀ + (mkProgF Δ N main xs.length B).len + B + 3 * c + 3) Bi σ)
    (hrun : σ.vars "run" = 1) :
    ∃ (w : ℕ) (H' : List (ℕ × ℕ)) (σ' : Lax808846Proofs.Imp.Env),
      Run Bi vmLoop σ σ' (124 * (3 * c + 4)) ∧ Abs ⟨2, w :: stk₀, [], H'⟩ σ' ∧
      Cst (mkProgF Δ N main xs.length B) (W₀ + (mkProgF Δ N main xs.length B).len + B + 3 * c + 3) Bi σ' ∧
      σ'.vars "run" = 0 ∧ HExt H H' ∧ Rep B H' w y ∧ H'.length ≤ H.length + c := by
  have hreal := mkProgF_real Δ hN main xs.length B
  have hstub := mkProgF_stub Δ N main xs.length B
  have hPB : (mkProgF Δ N main xs.length B).B = B := rfl
  generalize mkProgF Δ N main xs.length B = P at hreal hstub hPB hC ⊢
  subst hPB
  have h1 : H.length ≤ W₀ := hbd.heapLen
  have h2 : (ws ++ stk₀).length ≤ W₀ := hbd.stkLen
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := vm_runs_gen Δ hreal hstub hB h hrep
    (W := W₀ + P.len + P.B + 3 * c + 3) (hbd.mono (by omega)) (by omega)
    (by omega) (by omega) (by omega)
  have hhalt : P.code 2 = .halt := by
    have := hstub.2 2 (by simp [stub])
    simpa [stub] using this
  obtain ⟨σ', hrunσ, hA', hC', hrun'⟩ := loop_run hs (by simpa using hhalt) σ hA hC hrun
  exact ⟨w, H', σ', hrunσ.mono (by omega), hA', hC', hrun', hx, hr, hh⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram
