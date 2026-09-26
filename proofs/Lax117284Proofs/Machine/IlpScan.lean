import Lax117284Proofs.Machine.IlpCtx

/-!
The counted scan, with a static context, and the zeroing of an array.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients

/-- **A counted scan** `i := 0; while i < len do body`, whose invariant `Inv k` at the counter value
`k` is separated from a static context `C` (preserved by every run of the body that leaves alone
what the body cannot touch). -/
theorem scan_spec {B : ℕ} (i len : String) (N Kb : ℕ) (body : Com) (C : Env → Prop)
    (Inv : ℕ → Env → Prop) (hC : Stable body C) (hNB : N < B) (hlen : ∀ σ, C σ → σ.vars len = N)
    (hbody : ∀ k < N, Spec B (fun σ => C σ ∧ σ.vars i = k ∧ Inv k σ) body
      (fun σ σ' => σ'.vars i = k + 1 ∧ Inv (k + 1) σ') Kb) :
    Spec B (fun σ => C (σ.setVar i 0) ∧ Inv 0 (σ.setVar i 0)) (forZ i len body)
      (fun _ σ' => C σ' ∧ Inv N σ' ∧ σ'.vars i = N) ((Kb + 4) * N + 6) := by
  have hI := Spec.forRangeZero (B := B) (c := body) i len
    (fun σ => C σ ∧ σ.vars i ≤ N ∧ Inv (σ.vars i) σ) N Kb hNB (fun σ h => h.2.1)
    (fun σ h => hlen σ h.1) ?_
  · refine (Spec.pre hI ?_).post ?_
    · intro σ ⟨h1, h2⟩
      exact ⟨h1, by simp, by simpa using h2⟩
    · intro σ σ' _ ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, by rw [h4] at h3; exact h3, h4⟩
  · intro σ ⟨⟨hCσ, hle, hinv⟩, hlt⟩
    obtain ⟨σ', hr, ⟨hi', hinv'⟩, hkp⟩ := spec_keeps (hbody (σ.vars i) hlt) σ ⟨hCσ, rfl, hinv⟩
    refine ⟨σ', hr, ⟨hC σ σ' hCσ hkp, by omega, by rw [hi']; exact hinv'⟩, hi'⟩

/-! ### Zeroing an array -/

theorem fillBody_vals {B : ℕ} (a len : String) (L : ℕ) (hB : 1 < B) :
    Spec B (fun σ => (σ.arrs a).length = L ∧ σ.vars "fi" < L ∧ L < B)
      (.seq (.store a (V "fi") (lit 0)) (bump "fi"))
      (fun σ σ' => σ'.vars "fi" = σ.vars "fi" + 1 ∧
        σ'.arrs a = (σ.arrs a).set (σ.vars "fi") 0) 7 := by
  run_vcg
  simp

theorem eq_arrOf_of_length {l : List ℕ} {L : ℕ} (h : l.length = L) :
    l = arrOf L (fun c => l.getD c 0) := by
  subst h
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  rw [List.getElem_eq_getD 0]
  simp [arrOf]

/-- **Zeroing**: the first `L` cells of `a` become `0`. -/
theorem fill_spec {B : ℕ} (a len : String) (L : ℕ) (C : Env → Prop)
    (hC : Stable (.seq (.store a (V "fi") (lit 0)) (bump "fi")) C)
    (hCi : ∀ σ, C σ → C (σ.setVar "fi" 0)) (hlen : ∀ σ, C σ → σ.vars len = L)
    (hLB : L < B) (hB : 1 < B) (hne : len ≠ "fi") :
    Spec B (fun σ => C σ ∧ (σ.arrs a).length = L) (fillCom a len)
      (fun _ σ' => C σ' ∧ σ'.arrs a = arrOf L (fun _ => 0)) ((7 + 4) * L + 6) := by
  unfold fillCom
  have hs := scan_spec (B := B) "fi" len L 7 (.seq (.store a (V "fi") (lit 0)) (bump "fi")) C
    (fun k σ => ∃ g, σ.arrs a = arrOf L g ∧ ∀ c < k, g c = 0) hC hLB hlen ?_
  · refine (Spec.pre hs ?_).post ?_
    · intro σ ⟨h1, h2⟩
      exact ⟨hCi σ h1, fun c => (σ.arrs a).getD c 0, eq_arrOf_of_length h2, fun c hc => absurd hc (by omega)⟩
    · intro σ σ' _ ⟨h1, ⟨g, hg, hc⟩, h3⟩
      exact ⟨h1, by rw [hg]; exact arrOf_congr hc⟩
  · intro k hk σ ⟨hCσ, hk', g, hg, hgk⟩
    obtain ⟨σ', hr, h1, h2⟩ := (fillBody_vals (B := B) a len L hB) σ ⟨by rw [hg]; simp, by omega, hLB⟩
    refine ⟨σ', hr, by omega, fun j => if j = σ.vars "fi" then 0 else g j, ?_, ?_⟩
    · rw [h2, hg, set_arrOf]
    · intro c hc
      by_cases h : c = σ.vars "fi"
      · simp [h]
      · simp only [h, if_false]; exact hgk c (by omega)

/-- `x := x + 1`. -/
theorem bump_spec {B : ℕ} (x : String) (hB : 1 < B) :
    Spec B (fun σ => σ.vars x + 1 < B) (bump x) (fun σ σ' => σ' = σ.setVar x (σ.vars x + 1)) 4 := by
  run_vcg
  rfl

/-- `x := c`. -/
theorem assign_lit_spec {B : ℕ} (x : String) (c : ℕ) (hc : c < B) :
    Spec B (fun _ => True) (asg x (lit c)) (fun σ σ' => σ' = σ.setVar x c) 2 :=
  Spec.mono (Spec.assign (fun _ _ => evalB_lit hc)) (by simp)

end Lax117284Proofs.Machine.Ilp
