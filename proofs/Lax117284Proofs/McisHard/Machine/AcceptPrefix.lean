import Lax117284Proofs.McisHard.Machine.PredFinal

/-!
# Running a store-free command on a longer array (WP8)

The token array `TK` the tokenizer leaves is as long as the input word, and the stream of the formula is
only a prefix of it.  A command that never stores into an array and never reads an entry past the end of
the arrays it is started on (a run on the shorter arrays exists) runs identically on longer arrays.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Prefix

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

theorem getElem?_of_prefix {l1 l2 : List ℕ} (h : l1 <+: l2) {k v : ℕ} (hu : l1[k]? = some v) :
    l2[k]? = some v := by
  obtain ⟨t, rfl⟩ := h
  have hk : k < l1.length := (List.getElem?_eq_some_iff.mp hu).1
  rw [List.getElem?_append_left hk]; exact hu

theorem evalB_prefix {B : ℕ} {σ1 σ : Env} (hv : σ.vars = σ1.vars)
    (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∀ (e : Expr) {v : ℕ}, e.evalB B σ1 = some v → e.evalB B σ = some v := by
  intro e
  induction e with
  | lit n => intro v h; simpa [Expr.evalB] using h
  | var x => intro v h; simpa [Expr.evalB, hv] using h
  | get a i ih =>
      intro v h
      simp only [Expr.evalB, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨k, hk, u, hu, hf⟩ := h
      exact ⟨k, ih hk, u, getElem?_of_prefix (ha a) hu, hf⟩
  | bin op e f ihe ihf =>
      intro v h
      simp only [Expr.evalB, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, ihe hm, n, ihf hn, hf⟩

theorem condB_prefix {B : ℕ} {σ1 σ : Env} (hv : σ.vars = σ1.vars)
    (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∀ (b : Cond) {r : Bool}, b.evalB B σ1 = some r → b.evalB B σ = some r := by
  intro b
  cases b with
  | eq e f =>
      intro r h
      simp only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, evalB_prefix hv ha e hm, n, evalB_prefix hv ha f hn, hf⟩
  | lt e f =>
      intro r h
      simp only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, evalB_prefix hv ha e hm, n, evalB_prefix hv ha f hn, hf⟩

/-- **A store-free run on shorter arrays is a run on longer arrays.** -/
theorem bigStepB_prefix {B : ℕ} {c : Com} (hw : c.warrs = []) {σ1 σ1' : Env} {k : ℕ}
    (h : BigStepB B c σ1 σ1' k) :
    ∀ σ : Env, σ.vars = σ1.vars → σ.out = σ1.out → σ.inp = σ1.inp →
      (∀ a, σ1.arrs a <+: σ.arrs a) →
      ∃ σ', BigStepB B c σ σ' k ∧ σ'.vars = σ1'.vars ∧ σ'.out = σ1'.out ∧ σ'.inp = σ1'.inp ∧
        σ'.arrs = σ.arrs ∧ σ1'.arrs = σ1.arrs := by
  induction h with
  | skip =>
      intro σ hv ho hi ha
      exact ⟨σ, .skip, hv, ho, hi, rfl, rfl⟩
  | assign he =>
      rename_i σ1 x e v
      intro σ hv ho hi ha
      refine ⟨σ.setVar x v, .assign (evalB_prefix hv ha e he), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Env.setVar, hv]
      · simp [Env.setVar, ho]
      · simp [Env.setVar, hi]
      · rfl
      · rfl
  | store hi he hk => simp [Com.warrs] at hw
  | seq h1 h2 ih1 ih2 =>
      rename_i c d σ1 σ2 σ3 k k'
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r1, v1, o1, i1, a1, e1⟩ := ih1 hw.1 σ hv ho hi ha
      obtain ⟨τ', r2, v2, o2, i2, a2, e2⟩ := ih2 hw.2 τ v1 o1 i1
        (fun a => by rw [e1, a1]; exact ha a)
      exact ⟨τ', r1.seq r2, v2, o2, i2, a2.trans a1, e2.trans e1⟩
  | ite_true hb hc ih =>
      rename_i b c d σ1 σ1' k
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r, v, o, i, a, e⟩ := ih hw.1 σ hv ho hi ha
      exact ⟨τ, .ite_true (condB_prefix hv ha b hb) r, v, o, i, a, e⟩
  | ite_false hb hd ih =>
      rename_i b c d σ1 σ1' k
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r, v, o, i, a, e⟩ := ih hw.2 σ hv ho hi ha
      exact ⟨τ, .ite_false (condB_prefix hv ha b hb) r, v, o, i, a, e⟩
  | while_true hb hc hw' ih ih' =>
      rename_i b c σ1 σ2 σ3 k k'
      simp only [Com.warrs] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r1, v1, o1, i1, a1, e1⟩ := ih hw σ hv ho hi ha
      obtain ⟨τ', r2, v2, o2, i2, a2, e2⟩ := ih' (by simpa [Com.warrs] using hw) τ v1 o1 i1
        (fun a => by rw [e1, a1]; exact ha a)
      exact ⟨τ', .while_true (condB_prefix hv ha b hb) r1 r2, v2, o2, i2, a2.trans a1,
        e2.trans e1⟩
  | while_false hb =>
      rename_i b c σ1
      intro σ hv ho hi ha
      exact ⟨σ, .while_false (condB_prefix hv ha b hb), hv, ho, hi, rfl, rfl⟩
  | read h =>
      rename_i σ1 x v rest
      intro σ hv ho hi ha
      refine ⟨{ σ.setVar x v with inp := rest }, .read (by rw [hi]; exact h), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Env.setVar, hv]
      · simp [Env.setVar, ho]
      · rfl
      · rfl
      · rfl
  | write he =>
      rename_i σ1 e v
      intro σ hv ho hi ha
      refine ⟨{ σ with out := σ.out ++ [v] }, .write (evalB_prefix hv ha e he), hv, ?_, hi, rfl,
        rfl⟩
      simp [ho]

/-- The same for `Run`. -/
theorem run_prefix {B : ℕ} {c : Com} (hw : c.warrs = []) {σ1 σ1' : Env} {K : ℕ}
    (h : Run B c σ1 σ1' K) (σ : Env) (hv : σ.vars = σ1.vars) (ho : σ.out = σ1.out)
    (hi : σ.inp = σ1.inp) (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∃ σ', Run B c σ σ' K ∧ σ'.vars = σ1'.vars ∧ σ'.out = σ1'.out ∧ σ'.inp = σ1'.inp ∧
      σ'.arrs = σ.arrs := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨σ', r, v, o, i, a, -⟩ := bigStepB_prefix hw hb σ hv ho hi ha
  exact ⟨σ', ⟨k, hk, r⟩, v, o, i, a⟩

end Lax117284Proofs.McisHard.Prefix
