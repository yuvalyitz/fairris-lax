import Lax117284Proofs.Machine.TwForget2

/-!
The cell of the table of a forget node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The table entry of a forget node**, as a number. -/
lemma tbv_forget {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i e : ℕ}
    (hk : kind D (i + 1) = 2) :
    tbv I kk D (i + 1) e = if ∃ S < 2 ^ I.days,
      tbv I kk D i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e) = 1 then 1 else 0 := by
  by_cases h : ∃ S < 2 ^ I.days, tbv I kk D i (insN (2 ^ I.days) (pos (bagL D i) (vertex D (i + 1))) S e) = 1
  · rw [if_pos h]
    obtain ⟨S, hS, hT⟩ := h
    refine tbv_one ((TB_forget hk).2 ⟨S, hS, ?_⟩)
    by_contra hn
    rw [tbv_zero hn] at hT; omega
  · rw [if_neg h]
    refine tbv_zero fun hTB => h ?_
    obtain ⟨S, hS, hT⟩ := (TB_forget hk).1 hTB
    exact ⟨S, hS, tbv_one hT⟩

/-- The loop over the forgotten digit: the `or` of the table entries of the child. -/
def forgetOr : Com := fLoop "so" "bb" forgetBody

/-- The scalars the loop writes. -/
def SO : List String := ["so", "ix", "ac"]

theorem forgetOr_run (σ0 : Env) (N cb : ℕ) (hbb : σ0.vars "bb" = N) (hNB : N + 1 < B)
    (hcb : σ0.vars "cbase" = cb) (hac : σ0.vars "ac" ≤ 1)
    (hidx : ∀ j < N, cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi") <
      (σ0.arrs "TB").length)
    (hixB : ∀ j < N, cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi") < B)
    (hT : ∀ j < N, (σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0 ≤ 1)
    (hB : 2 < B) (hPp : σ0.vars "Pp" < B) :
    ∃ σ', Run B forgetOr σ0 σ' ((30 + 10 + 4) * N + 6) ∧
      σ'.vars "ac" = (List.range N).foldl (fun a j => if j < N then Nat.lor a
        ((σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0) else a)
        (σ0.vars "ac") ∧ Agr SO σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "so" "bb" "ac" forgetBody SO
    (fun j a => if j < N then Nat.lor a
      ((σ0.arrs "TB").getD (cb + (σ0.vars "lo" + j * σ0.vars "Pp" + σ0.vars "hi")) 0) else a)
    (fun _ a => a ≤ 1) 30 N σ0 (by simp [SO]) (by simp [SO]) (by decide) hbb hNB hac
    (fun j a h => by
      by_cases hj : j < N
      · simp only [hj, if_true]
        exact lor_le_one h (hT j hj) 
      · simp only [hj, if_false]; exact h) (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ SO → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "lo" = σ0.vars "lo" := hfr "lo" (by simp [SO])
      have e2 : σ.vars "hi" = σ0.vars "hi" := hfr "hi" (by simp [SO])
      have e3 : σ.vars "Pp" = σ0.vars "Pp" := hfr "Pp" (by simp [SO])
      have e4 : σ.vars "cbase" = cb := by rw [hfr "cbase" (by simp [SO]), hcb]
      have e5 : σ.arrs "TB" = σ0.arrs "TB" := by rw [hA.1]
      have hlt' : σ.vars "so" < N := hlt
      obtain ⟨σ', r, hv, hA', hso, ho⟩ := forgetBody_run (B := B) σ
        (by rw [e1, e2, e3, e4, e5]; exact hidx _ hlt') (by rw [e1, e2, e3, e4]; exact hixB _ hlt')
        hQ (by rw [e1, e2, e3, e4, e5]; exact hT _ hlt') hB (by omega) (by rw [e3]; exact hPp)
      refine ⟨σ', r, ?_, agr_comp (S := SO) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp [SO]; tauto), hso, ho⟩
      rw [hv, e1, e2, e3, e4, e5, if_pos hlt'])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  exact ⟨σ', r, hv, hA, ho⟩

end Lax117284Proofs.Machine.TwNode
