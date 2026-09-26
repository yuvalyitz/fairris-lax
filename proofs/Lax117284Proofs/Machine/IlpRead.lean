import Lax117284Proofs.Machine.IlpSearch

/-!
Reading the word into `z`.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

theorem readBody_vals {B : ℕ} :
    Spec B (fun σ => σ.inp ≠ [] ∧ σ.inp.headD 0 < B ∧ σ.vars "q" + 2 < (σ.arrs "z").length ∧
        σ.vars "q" + 2 < B)
      readBody
      (fun σ σ' => σ'.inp = σ.inp.tail ∧ σ'.vars "q" = σ.vars "q" + 1 ∧
        σ'.arrs "z" = (σ.arrs "z").set (σ.vars "q" + 2) (σ.inp.headD 0)) 10 := by
  run_vcg
  all_goals
    have hq : σ.vars "q" + 2 < (σ.arrs "z").length := ‹σ.vars "q" + 2 < (σ.arrs "z").length›
    have hqB : σ.vars "q" + 2 < B := ‹σ.vars "q" + 2 < B›
    have hh : σ.inp.headD 0 < B := ‹σ.inp.headD 0 < B›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | exact ⟨trivial, trivial, trivial⟩ | exact hh)

theorem tail_ne_nil' {l : List ℕ} (h : 2 ≤ l.length) : l.tail ≠ [] := by
  intro h0
  have : l.tail.length = l.length - 1 := List.length_tail
  rw [h0] at this
  simp at this
  omega

theorem ne_nil' {l : List ℕ} (h : 2 ≤ l.length) : l ≠ [] := by
  intro h0; rw [h0] at h; simp at h

theorem readHead_vals {B : ℕ} :
    Spec B (fun σ => 1 < B ∧ σ.inp.length ≥ 2 ∧ σ.inp.headD 0 < B ∧ σ.inp.tail.headD 0 < B ∧
        2 ≤ (σ.arrs "z").length ∧
        σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B)
      readHead
      (fun σ σ' => σ'.vars "N" = σ.inp.headD 0 ∧ σ'.vars "M" = σ.inp.tail.headD 0 ∧
        σ'.vars "tl" = σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 ∧
        σ'.arrs "z" = ((σ.arrs "z").set 0 (σ.inp.headD 0)).set 1 (σ.inp.tail.headD 0) ∧
        σ'.inp = σ.inp.tail.tail) 30 := by
  unfold readHead
  run_vcg
  all_goals
    have hB1 : 1 < B := ‹1 < B›
    have hlen : σ.inp.length ≥ 2 := ‹σ.inp.length ≥ 2›
    have hh : σ.inp.headD 0 < B := ‹σ.inp.headD 0 < B›
    have hh2 : σ.inp.tail.headD 0 < B := ‹σ.inp.tail.headD 0 < B›
    have hz : 2 ≤ (σ.arrs "z").length := ‹2 ≤ (σ.arrs "z").length›
    have hp : σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B :=
      ‹σ.inp.tail.headD 0 * σ.inp.headD 0 + σ.inp.tail.headD 0 < B›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | exact ⟨trivial, trivial, trivial, trivial, trivial⟩ | assumption |
    exact ne_nil' hlen | exact tail_ne_nil' hlen |
    skip)

theorem list_eq_arrOf {x : List ℕ} {f : ℕ → ℕ} (h : ∀ c < x.length, f c = x.getD c 0) :
    arrOf x.length f = x := by
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [arrOf, List.getElem_map, List.getElem_range]
  rw [h k (by simpa using h1), List.getElem_eq_getD 0]

theorem headD_drop' (l : List ℕ) (m : ℕ) : (l.drop m).headD 0 = l.getD m 0 := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih => cases m <;> simp [ih]

theorem getD_one_of_cons {a b : ℕ} {rest : List ℕ} : (a :: b :: rest).getD 1 0 = b := rfl

/-- **The word is read into `z`.** -/
theorem readCom_spec {B : ℕ} (x : List ℕ) (hx : x.length = 2 + x.getD 1 0 * x.getD 0 0 + x.getD 1 0)
    (hxB : ∀ v ∈ x, v < B) (hlB : x.length + 1 < B) (h2 : 2 ≤ x.length) :
    Spec B (fun σ => σ.inp = x ∧ (σ.arrs "z").length = x.length)
      readCom
      (fun _ σ' => σ'.vars "N" = x.getD 0 0 ∧ σ'.vars "M" = x.getD 1 0 ∧ σ'.arrs "z" = x ∧
        σ'.inp = []) (30 + ((10 + 4) * (x.length - 2) + 6)) := by
  obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, x = a :: b :: rest := by
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    · exact ⟨a, b, rest, rfl⟩
  have hB1 : 1 < B := by simp at hlB; omega
  have hTL : (a :: b :: rest).length - 2 = b * a + b := by
    have := hx; simp at this ⊢; omega
  have hs := scan_spec (B := B) "q" "tl" ((a :: b :: rest).length - 2) 10 readBody
    (fun σ => σ.vars "tl" = (a :: b :: rest).length - 2 ∧
      (σ.arrs "z").length = (a :: b :: rest).length)
    (fun k σ => σ.inp = (a :: b :: rest).drop (k + 2) ∧ ∃ f, σ.arrs "z" = arrOf (a :: b :: rest).length f ∧
      ∀ c < k + 2, f c = (a :: b :: rest).getD c 0)
    (Stable.and (stable_var "tl" (fun v => v = (a :: b :: rest).length - 2) (by decide))
      (stable_len "z" (fun l => l = (a :: b :: rest).length))) (by omega) (fun σ h => h.1) ?_
  · have hH := readHead_vals (B := B)
    unfold readCom
    have hH' : Spec B (fun σ => σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length)
        readHead
        (fun σ σ' => σ'.vars "N" = a ∧ σ'.vars "M" = b ∧
          σ'.vars "tl" = (a :: b :: rest).length - 2 ∧
          σ'.arrs "z" = (((σ.arrs "z").set 0 a).set 1 b) ∧
          σ'.inp = rest) 30 := by
      refine Spec.post (Spec.pre hH ?_) ?_
      · rintro σ ⟨hin, hz⟩
        rw [hin]
        refine ⟨hB1, by simp, hxB a (by simp), hxB b (by simp), by simp at hz ⊢; omega, ?_⟩
        simp only [List.headD_cons, List.tail_cons]
        omega
      · rintro σ σ' ⟨hin, hz⟩ ⟨h1, h2, h3, h4, h5⟩
        rw [hin] at h1 h2 h3 h4 h5
        simp only [List.headD_cons, List.tail_cons] at h1 h2 h3 h4 h5
        exact ⟨h1, h2, by rw [h3, hTL], h4, h5⟩
    have hL : Spec B (fun σ => σ.vars "tl" = (a :: b :: rest).length - 2 ∧ σ.inp = rest ∧
        (∃ f, σ.arrs "z" = arrOf (a :: b :: rest).length f ∧ ∀ c < 2, f c = (a :: b :: rest).getD c 0))
        (forZ "q" "tl" readBody)
        (fun _ σ' => σ'.inp = [] ∧ σ'.arrs "z" = a :: b :: rest) ((10 + 4) * ((a :: b :: rest).length - 2) + 6) := by
      refine Spec.mono (Spec.post (Spec.pre hs ?_) ?_) (by omega)
      · rintro σ ⟨htl, hin, f, hz, hf⟩
        refine ⟨⟨by simpa using htl, by simp [hz]⟩, by simpa using hin, f, by simpa using hz, hf⟩
      · rintro σ σ' - ⟨-, ⟨hin, f, hz, hf⟩, -⟩
        refine ⟨?_, ?_⟩
        · rw [hin]; simp
        · rw [hz]; exact list_eq_arrOf fun c hc => hf c (by omega)
    have hmid : ∀ σ σ1 : Env, (σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length) →
        (σ1.vars "N" = a ∧ σ1.vars "M" = b ∧ σ1.vars "tl" = (a :: b :: rest).length - 2 ∧
          σ1.arrs "z" = (((σ.arrs "z").set 0 a).set 1 b) ∧ σ1.inp = rest) →
        (σ1.vars "tl" = (a :: b :: rest).length - 2 ∧ σ1.inp = rest ∧
          (∃ f, σ1.arrs "z" = arrOf (a :: b :: rest).length f ∧
            ∀ c < 2, f c = (a :: b :: rest).getD c 0)) := by
      rintro σ σ1 ⟨hin, hz⟩ ⟨g1, g2, g3, g4, g5⟩
      have hlen2 : 2 ≤ (σ.arrs "z").length := by rw [hz]; exact h2
      refine ⟨g3, g5, fun c => (((σ.arrs "z").set 0 a).set 1 b).getD c 0, ?_, ?_⟩
      · rw [g4]; exact eq_arrOf_of_length (by simp [hz])
      · intro c hc
        interval_cases c
        · simp [List.getD_eq_getElem?_getD, List.getElem?_set, show 0 < (σ.arrs "z").length by omega]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_set, show 1 < (σ.arrs "z").length by omega]
    have hL' := Spec.frame hL
    have hfull : Spec B (fun σ => σ.inp = a :: b :: rest ∧ (σ.arrs "z").length = (a :: b :: rest).length)
        (.seq readHead (forZ "q" "tl" readBody))
        (fun _ σ' => σ'.inp = [] ∧ σ'.arrs "z" = a :: b :: rest ∧ σ'.vars "N" = a ∧ σ'.vars "M" = b)
        (30 + ((10 + 4) * ((a :: b :: rest).length - 2) + 6)) := by
      refine Spec.seq hH' hL' hmid ?_
      rintro σ σ1 σ2 - ⟨h1, h2', -, -, -⟩ ⟨⟨hin, hz⟩, hv, -, -, -⟩
      exact ⟨hin, hz, by rw [hv "N" (by decide), h1], by rw [hv "M" (by decide), h2']⟩
    refine Spec.post hfull ?_
    rintro σ σ' - ⟨hin, hz, hN, hM⟩
    exact ⟨hN, hM, hz, hin⟩
  · intro k hk σ ⟨⟨htl, hzl⟩, hqk, hin, f, hz, hf⟩
    have hk' : k + 2 < (a :: b :: rest).length := by omega
    have hget : (a :: b :: rest).getD (k + 2) 0 ∈ (a :: b :: rest) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
      exact List.getElem_mem hk'
    have hhead : ((a :: b :: rest).drop (k + 2)).headD 0 = (a :: b :: rest).getD (k + 2) 0 :=
      headD_drop' _ _
    obtain ⟨σ', hr, h1, h2', h3⟩ := readBody_vals (B := B) σ
      ⟨by rw [hin]; intro h; have : ((a :: b :: rest).drop (k + 2)).length = (a :: b :: rest).length - (k + 2) := List.length_drop; rw [h] at this; simp at this hk'; omega,
       by rw [hin, hhead]; exact hxB _ hget, by rw [hzl, hqk]; exact hk', by rw [hqk]; omega⟩
    refine ⟨σ', hr, by omega, ?_, ?_⟩
    · rw [h1, hin, List.tail_drop]
    · refine ⟨fun c => if c = k + 2 then (a :: b :: rest).getD (k + 2) 0 else f c, ?_, ?_⟩
      · rw [h3, hz, hqk, hin, hhead, set_arrOf]
      · intro c hc
        by_cases h : c = k + 2
        · simp [h]
        · simp only [h, if_false]; exact hf c (by omega)

end

end Lax117284Proofs.Machine.Ilp
