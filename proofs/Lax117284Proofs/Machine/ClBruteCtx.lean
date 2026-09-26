import Lax117284Proofs.Machine.ClBruteCom

/-!
The context every pass of the brute force runs in: what the word and the value bound say
(`Bd`), and the scalars and arrays no pass but the odometer changes (`Ctx`).
-/

namespace Lax117284Proofs.Machine.ClBrute

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Scheduling Lax117284.Scheduling.Instance Lax117284.InstanceEncoding

/-! ### The value bound -/

/-- The word encodes the instance, and the bound `B` is big enough for it. -/
structure Bd (B : ℕ) (x : List ℕ) (I : Instance) (k : ℕ) : Prop where
  dec : EncodesUniform x I k
  big : 4 * x.length + 64 < B
  xB : ∀ v ∈ x, v < B

variable {B k : ℕ} {x : List ℕ} {I : Instance}

namespace Bd

lemma len (h : Bd B x I k) : x.length = 3 + 2 * (I.days * I.clients) :=
  Lax117284Proofs.ClientsWord.len_eq h.dec

lemma xg (h : Bd B x I k) (j : ℕ) : x.getD j 0 < B := by
  by_cases hj : j < x.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h.xB _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    have := h.big; omega

lemma mnB (h : Bd B x I k) : I.days * I.clients + 8 < B := by
  have := h.big; have := h.len; omega

lemma nB (h : Bd B x I k) : I.clients < B := by
  have := h.xg 0; rwa [Lax117284Proofs.ClientsWord.x0 h.dec] at this

lemma mB (h : Bd B x I k) : I.days < B := by
  have := h.xg 1; rwa [Lax117284Proofs.ClientsWord.x1 h.dec] at this

lemma kB (h : Bd B x I k) : k < B := by
  have := h.xg (2 + 2 * (I.days * I.clients))
  rwa [Lax117284Proofs.ClientsWord.xk h.dec] at this

end Bd

/-! ### The context -/

/-- What no pass but the odometer changes: the word, the three parameters, the size of the
vector, and the vector itself, `m * n` bits. -/
structure Ctx (x : List ℕ) (I : Instance) (k : ℕ) (f : ℕ → ℕ) (σ : Env) : Prop where
  hx : σ.arrs "X" = x
  hn : σ.vars "n" = I.clients
  hm : σ.vars "m" = I.days
  hk : σ.vars "k" = k
  hmn : σ.vars "bfmn" = I.days * I.clients
  hsc : σ.arrs "bfsc" = arrOf (I.days * I.clients) f
  hf : ∀ r, r < I.days * I.clients → f r ≤ 1

namespace Ctx

variable {f : ℕ → ℕ} {σ : Env}

lemma scLen (h : Ctx x I k f σ) : (σ.arrs "bfsc").length = I.days * I.clients := by
  rw [h.hsc]; simp

lemma scGet (h : Ctx x I k f σ) {r : ℕ} (hr : r < I.days * I.clients) :
    (σ.arrs "bfsc").getD r 0 = f r := by
  rw [h.hsc, getD_arrOf f hr]

lemma xLen (hb : Bd B x I k) (h : Ctx x I k f σ) :
    (σ.arrs "X").length = 3 + 2 * (I.days * I.clients) := by
  rw [h.hx]; exact hb.len

lemma xGet (h : Ctx x I k f σ) (j : ℕ) : (σ.arrs "X").getD j 0 = x.getD j 0 := by
  rw [h.hx]

end Ctx

/-! ### The flags -/

/-- The value of `ltF e f`. -/
lemma ltf_eq (e f : ℕ) : 1 - (1 - (f - e)) = if e < f then 1 else 0 := by
  split_ifs <;> omega

/-- The clash of the pair, as the program computes it. -/
def cl (ba bb a b sa db sb da : ℕ) : ℕ :=
  ba * bb * (1 - (1 - (b - a))) * (1 - (1 - (db - sa))) * (1 - (1 - (da - sb)))

lemma cl_eq {ba bb : ℕ} (hba : ba ≤ 1) (hbb : bb ≤ 1) (a b sa db sb da : ℕ) :
    cl ba bb a b sa db sb da =
      if ba = 1 ∧ bb = 1 ∧ a < b ∧ sa < db ∧ sb < da then 1 else 0 := by
  rw [cl, ltf_eq, ltf_eq, ltf_eq]
  have h1 : ba = 0 ∨ ba = 1 := by omega
  have h2 : bb = 0 ∨ bb = 1 := by omega
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> split_ifs <;> simp_all

end Lax117284Proofs.Machine.ClBrute
