import Lax117284Proofs.Machine.ClSimFinal
import Lax117284Proofs.ClientsILPEquiv
import Lax117284Proofs.ClientsILPSize
import Lax117284Proofs.ClientsWord

/-!
The builder of the integer program's word, as an IMP+ command: the definitions.

The input word is in the array `X`. The builder computes the sizes `T = 2 ^ (n*n)`, `Z = 2 ^ n`,
`V = T * Z`, `N = V + n`, `M = T + n` and `zl = 2 + M * N + M`; the table `cnt` of the number of days
of each type; the table `okt` of which pairs (type, subset) are independent; and finally the array
`z`, one entry per position, by the formula of `zFunRaw`.
-/

namespace Lax117284Proofs.Machine.ClBuild

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.ClientsILP Lax117284.Scheduling

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev add (e f : Expr) : Expr := .bin .add e f
abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev dv (e f : Expr) : Expr := .bin .div e f
/-- The smaller of two values. -/
abbrev cap (e f : Expr) : Expr := sub e (sub e f)
/-- `1` when `e < f`, `0` otherwise. -/
abbrev ltFl (e f : Expr) : Expr := cap (sub f e) (lit 1)
/-- Bit `p` of `x`: `1` or `0`. -/
abbrev bitE (x p : Expr) : Expr := .bin .and (.bin .shiftr x p) (lit 1)
/-- The power `2 ^ p`. -/
abbrev pow2 (p : Expr) : Expr := .bin .shiftl (lit 1) p

/-- The sizes of the program, from the number of clients. -/
def sizesCom : Com := seqs [
  asg "nn" (mul (V "n") (V "n")),
  asg "T" (pow2 (V "nn")), asg "Z" (pow2 (V "n")), asg "Vv" (mul (V "T") (V "Z")),
  asg "N" (add (V "Vv") (V "n")), asg "M" (add (V "T") (V "n")),
  asg "zl" (add (add (lit 2) (mul (V "M") (V "N"))) (V "M"))]

/-- What the builder knows about the word and the bounds. -/
structure Bh (I : Instance) (x : List ℕ) (k B : ℕ) : Prop where
  enc : Lax117284.InstanceEncoding.EncodesUniform x I k
  hL : x.length < B
  hX : ∀ v ∈ x, v < B
  hzB : zLen I.clients < B

/-- The scalars and the input array. -/
structure Ctx0 (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop where
  X : σ.arrs "X" = x
  n : σ.vars "n" = I.clients
  m : σ.vars "m" = I.days
  k : σ.vars "k" = k

/-- The sizes are set. -/
structure Sizes (I : Instance) (σ : Env) : Prop where
  nn : σ.vars "nn" = I.clients * I.clients
  T : σ.vars "T" = nT I.clients
  Z : σ.vars "Z" = nZ I.clients
  Vv : σ.vars "Vv" = nV I.clients
  N : σ.vars "N" = nN I.clients
  M : σ.vars "M" = nM I.clients
  zl : σ.vars "zl" = zLen I.clients

variable {B k : ℕ} {I : Instance} {x : List ℕ}

open Lax117284Proofs.Machine.ClSim (AgreeOff) in
theorem AgreeOff.trans' {L1 L2 : List String} {σ σ1 σ2 : Env} (h1 : AgreeOff L1 σ σ1)
    (h2 : AgreeOff L2 σ1 σ2) : AgreeOff (L1 ++ L2) σ σ2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun y hy => by
    rw [h2.2.2.2 y (fun h => hy (List.mem_append_right _ h)),
      h1.2.2.2 y (fun h => hy (List.mem_append_left _ h))]⟩

open Lax117284Proofs.Machine.ClSim (AgreeOff) in
theorem AgreeOff.mono' {L L' : List String} {σ σ' : Env} (h : AgreeOff L σ σ')
    (hs : ∀ y ∈ L, y ∈ L') : AgreeOff L' σ σ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun y hy => h.2.2.2 y (fun hh => hy (hs y hh))⟩

theorem Bh.n_lt (h : Bh I x k B) : I.clients < B := by
  have := ClientsWord.x0 h.enc
  rw [← this]
  by_cases hj : 0 < x.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
  · have := ClientsWord.len_eq h.enc; omega

theorem Bh.m_lt (h : Bh I x k B) : I.days < B := by
  have := ClientsWord.x1 h.enc
  rw [← this]
  have hl := ClientsWord.len_eq h.enc
  rw [List.getD_eq_getElem _ _ (by omega)]; exact h.hX _ (List.getElem_mem _)

theorem Bh.k_lt (h : Bh I x k B) : k < B := by
  have := ClientsWord.xk h.enc
  rw [← this]
  have hl := ClientsWord.len_eq h.enc
  rw [List.getD_eq_getElem _ _ (by omega)]; exact h.hX _ (List.getElem_mem _)

theorem Bh.getD_lt (h : Bh I x k B) (j : ℕ) : x.getD j 0 < B := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ hj]; exact h.hX _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; have := h.hL; omega

theorem Bh.mn_le (h : Bh I x k B) : 2 * (I.days * I.clients) + 3 = x.length := by
  have := ClientsWord.len_eq h.enc; omega

/-- `σ'` differs from `σ` only in the scalars `LV` and the arrays `LA`. -/
def AgreeA (LV LA : List String) (σ σ' : Env) : Prop :=
  (∀ a, a ∉ LA → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
    ∀ y, y ∉ LV → σ'.vars y = σ.vars y

theorem AgreeA.trans {LV LV' LA LA' : List String} {σ σ1 σ2 : Env} (h1 : AgreeA LV LA σ σ1)
    (h2 : AgreeA LV' LA' σ1 σ2) : AgreeA (LV ++ LV') (LA ++ LA') σ σ2 :=
  ⟨fun a ha => by
    rw [h2.1 a (fun h => ha (List.mem_append_right _ h)), h1.1 a (fun h => ha (List.mem_append_left _ h))],
    h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, fun y hy => by
    rw [h2.2.2.2 y (fun h => hy (List.mem_append_right _ h)),
      h1.2.2.2 y (fun h => hy (List.mem_append_left _ h))]⟩

theorem AgreeA.mono {LV LV' LA LA' : List String} {σ σ' : Env} (h : AgreeA LV LA σ σ')
    (hv : ∀ y ∈ LV, y ∈ LV') (ha : ∀ a ∈ LA, a ∈ LA') : AgreeA LV' LA' σ σ' :=
  ⟨fun a hh => h.1 a (fun h' => hh (ha a h')), h.2.1, h.2.2.1,
    fun y hy => h.2.2.2 y (fun h' => hy (hv y h'))⟩

theorem AgreeOff.toA {L : List String} {σ σ' : Env} (h : AgreeOff L σ σ') :
    AgreeA L [] σ σ' := ⟨fun a _ => by rw [h.1], h.2.1, h.2.2.1, h.2.2.2⟩

theorem agreeA_of_frame {c : Com} {LV LA : List String} (hv : ∀ y ∈ c.wvars, y ∈ LV)
    (ha : ∀ a ∈ c.warrs, a ∈ LA) (hr : ¬ c.reads) (hw : c.NoWrite) {σ σ' : Env}
    (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h3 : ¬ c.reads → σ'.inp = σ.inp) (h4 : c.NoWrite → σ'.out = σ.out) : AgreeA LV LA σ σ' :=
  ⟨fun a hh => h2 a (fun h' => hh (ha a h')), h3 hr, h4 hw, fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem agree_of_frame_gen {c : Com} {L : List String} (hv : ∀ y ∈ c.wvars, y ∈ L)
    (ha : ∀ a ∈ c.warrs, False) (hr : ¬ c.reads) (hw : c.NoWrite) {σ σ' : Env}
    (h1 : ∀ y, y ∉ c.wvars → σ'.vars y = σ.vars y) (h2 : ∀ a, a ∉ c.warrs → σ'.arrs a = σ.arrs a)
    (h3 : ¬ c.reads → σ'.inp = σ.inp) (h4 : c.NoWrite → σ'.out = σ.out) : AgreeOff L σ σ' :=
  ⟨funext fun a => h2 a (fun hh => ha a hh), h3 hr, h4 hw, fun y hy => h1 y (fun hc => hy (hv y hc))⟩

theorem Bh.dAt_lt (h : Bh I x k B) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    I.dAt i a < B := by
  rw [← ClientsWord.due_eq h.enc hi ha]; exact h.getD_lt _

theorem Bh.pAt_lt (h : Bh I x k B) {i a : ℕ} (hi : i < I.days) (ha : a < I.clients) :
    I.pAt i a < B := by
  rw [← ClientsWord.proc_eq h.enc hi ha]; exact h.getD_lt _

theorem Bh.nn_lt (h : Bh I x k B) : I.clients * I.clients < B := by
  have := (sizes_le_zLen I.clients).2.2.2.2.2.1
  have := (sizes_le_zLen I.clients).1
  have := h.hzB
  have := h.hL
  omega

theorem Bh.nT_lt (h : Bh I x k B) : nT I.clients < B := by
  have := (sizes_le_zLen I.clients).1
  have := h.hzB
  have := h.hL
  omega

theorem sizesCom_spec (h : Bh I x k B) :
    Spec B (Ctx0 I x k) sizesCom (fun σ σ' => Ctx0 I x k σ' ∧ Sizes I σ' ∧
      (∀ y, y ∉ ["nn", "T", "Z", "Vv", "N", "M", "zl"] → σ'.vars y = σ.vars y) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 100 := by
  have hz := h.hzB
  have hL := h.hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := sizes_le_zLen I.clients
  have hT : (2 : ℕ) ^ (I.clients * I.clients) = nT I.clients := rfl
  have hZ : (2 : ℕ) ^ I.clients = nZ I.clients := rfl
  have hV : nT I.clients * nZ I.clients = nV I.clients := rfl
  have hN : nV I.clients + I.clients = nN I.clients := rfl
  have hM : nT I.clients + I.clients = nM I.clients := rfl
  have hzl' : 2 + nM I.clients * nN I.clients + nM I.clients = zLen I.clients := rfl
  run_vcg
  all_goals
    obtain ⟨hX, hn, hm, hk⟩ := ‹Ctx0 I x k _›
  all_goals try
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals try simp [Env.setVar, hX, hn, hm, hk, hT, hZ, hV, hN, hM, hzl']
  all_goals try (intro y a1 a2 a3 a4 a5 a6 a7
                 simp [Env.setVar, a1, a2, a3, a4, a5, a6, a7])
  all_goals try omega

end Lax117284Proofs.Machine.ClBuild
