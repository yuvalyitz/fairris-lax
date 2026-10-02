import Lax117284Proofs.Treewidth.Fun.VMLoadInit

/-!
# WP V3 (7): the writer — emit the output list from the final heap

After the VM has halted, `STK[0]` holds a word `w` with `Rep B H' w (listVal out)`.  The writer walks the list:
`while B - 1 < w do write HA[w - B]; w := HB[w - B]` (`B - 1 < w` is `w ≥ B`, i.e. `w` is a pointer, since `1 ≤ B`).
Its cost is linear in `|out|`; the caller must charge `|out|` (a value's tree size is not bounded by the derivation cost).
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning ToVal

def wrBody : Com :=
  .seq (.write (G "HA" (mi (V "w") (V "B")))) (.assign "w" (G "HB" (mi (V "w") (V "B"))))

def wrLoop : Com := .while (.lt (mi (V "B") (L 1)) (V "w")) wrBody

/-- `w := STK[0]` then the loop. -/
def wrCom : Com := .seq (.assign "w" (G "STK" (L 0))) wrLoop

theorem wrLoop_run {Bi B : ℕ} {H : List (ℕ × ℕ)} (hB : 1 ≤ B) (hBi : B + H.length + 1 < Bi) :
    ∀ (l : List ℕ) (w : ℕ) (σ : IEnv), Rep B H w (listVal l) → σ.vars "w" = w → σ.vars "B" = B →
      Pfx (H.map Prod.fst) (σ.arrs "HA") → Pfx (H.map Prod.snd) (σ.arrs "HB") →
      ∃ σ', Run Bi wrLoop σ σ' (16 * l.length + 6) ∧ σ'.out = σ.out ++ l := by
  intro l
  induction l with
  | nil =>
    intro w σ hr hw hb _ _
    have hw0 : w = 0 := (Rep.nat_inv (by simpa [listVal] using hr)).1
    have hcond : (Cond.lt (mi (V "B") (L 1)) (V "w")).evalB Bi σ = some false := by
      have := RunStep.cond_lt_false Bi σ (mi (V "B") (L 1)) (V "w") (B - 1) w
        (RunStep.eval_sub Bi σ _ _ B 1 (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega)) (by omega)
      exact this
    exact ⟨σ, (Run.while_false hcond).mono (by simp), by simp⟩
  | cons a l ih =>
    intro w σ hr hw hb hHA hHB
    have hr' : Rep B H w (Val.cons (Val.nat a) (listVal l)) := by simpa [listVal] using hr
    obtain ⟨p, a', b, hwp, hp, hra, hrb⟩ := hr'.cons_inv
    have ha' : a' = a := (Rep.nat_inv hra).1
    have hpl : p < H.length := (List.getElem?_eq_some_iff.mp hp).1
    have haB : a < B := (Rep.nat_inv hra).2
    rw [ha'] at hp hra
    have hcond : (Cond.lt (mi (V "B") (L 1)) (V "w")).evalB Bi σ = some true := by
      have := RunStep.cond_lt_true Bi σ (mi (V "B") (L 1)) (V "w") (B - 1) w
        (RunStep.eval_sub Bi σ _ _ B 1 (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega)) (by omega)
      exact this
    have hidx : (mi (V "w") (V "B")).evalB Bi σ = some p := by
      have := RunStep.eval_sub Bi σ (V "w") (V "B") w B
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega))
        (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega)) (by omega)
      rw [show w - B = p by omega] at this
      exact this
    have hHAp : (σ.arrs "HA")[p]? = some a := hHA.get (j := p) (x := a) (by simp [hp])
    have hHBp : (σ.arrs "HB")[p]? = some b := hHB.get (j := p) (x := b) (by simp [hp])
    have hpA : p < (σ.arrs "HA").length := (List.getElem?_eq_some_iff.mp hHAp).1
    have hpB : p < (σ.arrs "HB").length := (List.getElem?_eq_some_iff.mp hHBp).1
    have hgA : (σ.arrs "HA").getD p 0 = a := by
      rw [List.getD_eq_getElem?_getD, hHAp]; rfl
    have hgB : (σ.arrs "HB").getD p 0 = b := by
      rw [List.getD_eq_getElem?_getD, hHBp]; rfl
    have hbl : b < B + H.length := Rep.lt hrb
    -- the body
    have r1 : Run Bi (.write (G "HA" (mi (V "w") (V "B")))) σ { σ with out := σ.out ++ [a] } 5 := by
      have := Run.write (B := Bi) (σ := σ) (e := G "HA" (mi (V "w") (V "B"))) (v := a)
        (by have := RunStep.eval_get Bi σ "HA" (mi (V "w") (V "B")) p hidx hpA (by rw [hgA]; omega)
            rwa [hgA] at this)
      exact this.mono (by simp)
    set σ1 : IEnv := { σ with out := σ.out ++ [a] } with hσ1
    have hidx1 : (mi (V "w") (V "B")).evalB Bi σ1 = some p := hidx
    have r2 : Run Bi (.assign "w" (G "HB" (mi (V "w") (V "B")))) σ1 (σ1.setVar "w" b) 5 := by
      have := Run.assign (B := Bi) (σ := σ1) (x := "w") (e := G "HB" (mi (V "w") (V "B"))) (v := b)
        (by have := RunStep.eval_get Bi σ1 "HB" (mi (V "w") (V "B")) p hidx1 hpB (by rw [hgB]; omega)
            rwa [hgB] at this)
      exact this.mono (by simp)
    obtain ⟨σ', hr', hout'⟩ := ih b (σ1.setVar "w" b) hrb (by simp) (by simpa [hσ1] using hb)
      (by simpa [hσ1] using hHA) (by simpa [hσ1] using hHB)
    refine ⟨σ', ?_, ?_⟩
    · have := run_while_step hcond (r1.seq r2) hr'
      exact this.mono (by simp; omega)
    · simp [hσ1] at hout'
      simp [hout']

theorem wrCom_run {Bi B w : ℕ} {H : List (ℕ × ℕ)} {l : List ℕ} {σ : IEnv} (hB : 1 ≤ B)
    (hBi : B + H.length + 1 < Bi) (hr : Rep B H w (listVal l)) (hstk : (σ.arrs "STK")[0]? = some w)
    (hb : σ.vars "B" = B) (hHA : Pfx (H.map Prod.fst) (σ.arrs "HA"))
    (hHB : Pfx (H.map Prod.snd) (σ.arrs "HB")) :
    ∃ σ', Run Bi wrCom σ σ' (16 * l.length + 12) ∧ σ'.out = σ.out ++ l := by
  have hwl : w < B + H.length := Rep.lt hr
  have hlen : 0 < (σ.arrs "STK").length := (List.getElem?_eq_some_iff.mp hstk).1
  have hg : (σ.arrs "STK").getD 0 0 = w := by rw [List.getD_eq_getElem?_getD, hstk]; rfl
  have r1 : Run Bi (.assign "w" (G "STK" (L 0))) σ (σ.setVar "w" w) 3 := by
    have := Run.assign (B := Bi) (σ := σ) (x := "w") (e := G "STK" (L 0)) (v := w)
      (by have := RunStep.eval_get Bi σ "STK" (L 0) 0 (RunStep.eval_lit Bi 0 σ (by omega)) hlen
            (by rw [hg]; omega)
          rwa [hg] at this)
    exact this.mono (by simp)
  obtain ⟨σ', hr', ho⟩ := wrLoop_run hB hBi l w (σ.setVar "w" w) hr (by simp) (by simpa using hb)
    (by simpa using hHA) (by simpa using hHB)
  exact ⟨σ', (r1.seq hr').mono (by omega), by simpa using ho⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram
