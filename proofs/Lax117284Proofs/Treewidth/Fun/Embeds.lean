import Lax117284Proofs.Treewidth.Fun.Kit
import Mathlib.Tactic.Linarith

/-!
# WP F0 (3): `Embeds` and its closure lemmas

`Embeds Δ fid P f cost` — the function `fid` of the table computes the Lean function `f` on the inputs satisfying
`P`, within cost `cost a`, whenever `B` is large (`Fits`).  (Same definition as `proofs-todo/Machine.lean`.)

`EmbedsE Δ t P env f cost` is the term-level version over an arbitrary environment `env a : List Val`
(`Embeds` is the case `t = body`, `env a = [toVal a]`).  Closure lemmas: `call1` (composition with a function),
`ite`, `letE`, `var`, `lit`, `cons`, monotonicity in the precondition and in the cost.
-/

set_option linter.unusedSectionVars false

namespace Lax117284Proofs.Treewidth.Fun

open ToVal

/-- `f` is computed by the function `fid` of the table, within cost `cost a`, on every `a` with `P a`. -/
def Embeds {α β : Type} [ToVal α] [ToVal β] (Δ : ℕ → Option Tm) (fid : ℕ) (P : α → Prop) (f : α → β)
    (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → Fits B (toVal a) (cost a) → Runs Δ B fid [toVal a] (toVal (f a)) (cost a)

/-- Output-sensitive polynomial cost of degree `d`. -/
def osCost {α β : Type} [ToVal α] [ToVal β] (d : ℕ) (f : α → β) (a : α) : ℕ := 64 * (sz a + sz (f a) + 1) ^ d

/-! ### `Fits` -/

theorem Fits.mono_cost {B : ℕ} {v : Val} {c c' : ℕ} (h : Fits B v c) (hc : c' ≤ c) : Fits B v c' :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by first | omega | (dsimp only; omega)) 2) h

theorem Fits.mono_val {B : ℕ} {v w : Val} {c : ℕ} (h : Fits B v c) (hv : w.maxNat ≤ v.maxNat) : Fits B w c :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by first | omega | (dsimp only; omega)) 2) h

theorem Fits.mono_B {B B' : ℕ} {v : Val} {c : ℕ} (h : Fits B v c) (hB : B ≤ B') : Fits B' v c :=
  Nat.lt_of_lt_of_le h hB

/-- every quantity `n ≤ maxNat + c + 2` is `< B` (in particular the cost). -/
theorem Fits.lt {B : ℕ} {v : Val} {c n : ℕ} (h : Fits B v c) (hn : n ≤ v.maxNat + c + 2) : n < B :=
  Nat.lt_of_le_of_lt (le_trans hn (by nlinarith [Nat.zero_le (v.maxNat + c + 2)])) h

theorem Fits.cost_lt {B : ℕ} {v : Val} {c : ℕ} (h : Fits B v c) : c + 3 < B := by
  have h1 : (v.maxNat + c + 2) ^ 2 ≥ c + 3 := by nlinarith [Nat.zero_le v.maxNat, Nat.zero_le c]
  have h' : (v.maxNat + c + 2) ^ 2 < B := h
  omega

theorem Fits.maxNat_lt {B : ℕ} {v : Val} {c : ℕ} (h : Fits B v c) : v.maxNat + 3 < B := by
  have h1 : (v.maxNat + c + 2) ^ 2 ≥ v.maxNat + 3 := by nlinarith [Nat.zero_le v.maxNat, Nat.zero_le c]
  have h' : (v.maxNat + c + 2) ^ 2 < B := h
  omega

/-- the largest natural in an environment -/
def Val.maxNatL : List Val → ℕ
  | [] => 0
  | v :: vs => max v.maxNat (Val.maxNatL vs)

/-- `Fits` for a whole environment. -/
def FitsL (B : ℕ) (ρ : List Val) (c : ℕ) : Prop := (Val.maxNatL ρ + c + 2) ^ 2 < B

theorem fitsL_single (B : ℕ) (v : Val) (c : ℕ) : FitsL B [v] c ↔ Fits B v c := by
  simp [FitsL, Fits, Val.maxNatL]

theorem FitsL.mono_cost {B : ℕ} {ρ : List Val} {c c' : ℕ} (h : FitsL B ρ c) (hc : c' ≤ c) : FitsL B ρ c' :=
  Nat.lt_of_le_of_lt (Nat.pow_le_pow_left (by first | omega | (dsimp only; omega)) 2) h

theorem FitsL.cons {B : ℕ} {u : Val} {ρ : List Val} {c : ℕ} (h : FitsL B ρ c) (hu : u.maxNat ≤ Val.maxNatL ρ) :
    FitsL B (u :: ρ) c := by
  unfold FitsL at *
  refine Nat.lt_of_le_of_lt (Nat.pow_le_pow_left ?_ 2) h
  simp only [Val.maxNatL]; omega

/-! ### term-level embeddings -/

/-- `t`, evaluated in the environment `env a`, computes `f a` within cost `cost a`. -/
def EmbedsE {α β : Type} [ToVal β] (Δ : ℕ → Option Tm) (t : Tm) (P : α → Prop) (env : α → List Val)
    (f : α → β) (cost : α → ℕ) : Prop :=
  ∀ (B : ℕ) (a : α), P a → FitsL B (env a) (cost a) → EvLe Δ B (env a) t (toVal (f a)) (cost a)

namespace EmbedsE
variable {α β γ : Type} [ToVal α] [ToVal β] [ToVal γ] {Δ : ℕ → Option Tm} {t : Tm} {P : α → Prop}
  {env : α → List Val} {f : α → β} {cost : α → ℕ}

theorem mono_cost {cost' : α → ℕ} (h : EmbedsE Δ t P env f cost) (hc : ∀ a, P a → cost a ≤ cost' a) :
    EmbedsE Δ t P env f cost' :=
  fun B a ha hfit => (h B a ha (hfit.mono_cost (hc a ha))).mono (hc a ha)

theorem mono_pre {P' : α → Prop} (h : EmbedsE Δ t P env f cost) (hP : ∀ a, P' a → P a) :
    EmbedsE Δ t P' env f cost := fun B a ha hfit => h B a (hP a ha) hfit

theorem congr {g : α → β} (h : EmbedsE Δ t P env f cost) (hg : ∀ a, P a → f a = g a) :
    EmbedsE Δ t P env g cost := fun B a ha hfit => hg a ha ▸ h B a ha hfit

theorem ext {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (h : EmbedsE Δ t P env f cost) : EmbedsE Δ' t P env f cost :=
  fun B a ha hfit => (h B a ha hfit).weaken hΔ (Nat.le_refl _)

theorem var (i : ℕ) (hv : ∀ a, P a → (env a)[i]? = some (toVal (f a))) :
    EmbedsE Δ (.var i) P env f (fun _ => 1) := fun _ a ha _ => EvLe.var (hv a ha)

theorem lit (n : ℕ) (f : α → ℕ) (hf : ∀ a, P a → f a = n) (hn : ∀ B a, P a → FitsL B (env a) 1 → n < B) :
    EmbedsE Δ (.lit n) P env f (fun _ => 1) :=
  fun B a ha hfit => EvLe.lit (hn B a ha hfit) (by simp [hf a ha])

theorem pair {tb : Tm} {ta : Tm} {g : α → β} {h : α → γ} {ca cb : α → ℕ}
    (hg : EmbedsE Δ ta P env g ca) (hh : EmbedsE Δ tb P env h cb) :
    EmbedsE Δ (.cons ta tb) P env (fun a => (g a, h a)) (fun a => ca a + cb a + 1) := by
  intro B a ha hfit
  have h1 := hg B a ha (hfit.mono_cost (by first | omega | (dsimp only; omega)))
  have h2 := hh B a ha (hfit.mono_cost (by first | omega | (dsimp only; omega)))
  exact (EvLe.cons h1 h2)

/-- composition with a function of the table (`call ff [tg]`). -/
theorem call1 {ff : ℕ} {tg : Tm} {Q : β → Prop} {f' : β → γ} {cf : β → ℕ} {g : α → β} {cg : α → ℕ}
    (hf : Embeds Δ ff Q f' cf) (hg : EmbedsE Δ tg P env g cg) (hQ : ∀ a, P a → Q (g a))
    (hfit : ∀ B a, P a → FitsL B (env a) (cg a + cf (g a) + 1) → Fits B (toVal (g a)) (cf (g a))) :
    EmbedsE Δ (.call ff [tg]) P env (fun a => f' (g a)) (fun a => cg a + cf (g a) + 1) := by
  intro B a ha hfit'
  have h1 := hg B a ha (hfit'.mono_cost (by first | omega | (dsimp only; omega)))
  have h2 := hf B (g a) (hQ a ha) (hfit B a ha hfit')
  have h3 : EvLL Δ B (env a) [tg] [toVal (g a)] (cg a) := by
    simpa using EvLL.cons h1 EvLL.nil
  exact (Runs.evle h3 h2).mono (by first | omega | (dsimp only; omega))

/-- conditional. -/
theorem ite {tc tt te : Tm} {p : α → Bool} {cc ct ce : α → ℕ}
    (hc : EmbedsE Δ tc P env p cc)
    (ht : EmbedsE Δ tt (fun a => P a ∧ p a = true) env f ct)
    (he : EmbedsE Δ te (fun a => P a ∧ p a = false) env f ce) :
    EmbedsE Δ (.ite tc tt te) P env f (fun a => cc a + (if p a then ct a else ce a) + 1) := by
  intro B a ha hfit
  have h1 := hc B a ha (hfit.mono_cost (by first | omega | (dsimp only; omega)))
  cases hp : p a with
  | true =>
    have h2 := ht B a ⟨ha, hp⟩ (hfit.mono_cost (by simp [hp] <;> omega))
    have h1' : EvLe Δ B (env a) tc (.nat 1) (cc a) := by simpa [hp] using h1
    simpa [hp] using EvLe.iteT h1' (by first | omega | (dsimp only; omega)) h2
  | false =>
    have h2 := he B a ⟨ha, hp⟩ (hfit.mono_cost (by simp [hp] <;> omega))
    have h1' : EvLe Δ B (env a) tc (.nat 0) (cc a) := by simpa [hp] using h1
    simpa [hp] using EvLe.iteF h1' rfl h2

/-- `let`: the bound value becomes variable `0` of the body's environment. -/
theorem letE {tg tb : Tm} {g : α → γ} {cg cb : α → ℕ}
    (hg : EmbedsE Δ tg P env g cg) (hb : EmbedsE Δ tb P (fun a => toVal (g a) :: env a) f cb)
    (hfit : ∀ B a, P a → FitsL B (env a) (cg a + cb a + 1) → FitsL B (toVal (g a) :: env a) (cb a)) :
    EmbedsE Δ (.letE tg tb) P env f (fun a => cg a + cb a + 1) := by
  intro B a ha hfit'
  have h1 := hg B a ha (hfit'.mono_cost (by first | omega | (dsimp only; omega)))
  have h2 := hb B a ha (hfit B a ha hfit')
  exact EvLe.letE h1 h2

end EmbedsE

theorem Embeds.of_body {α β : Type} [ToVal α] [ToVal β] {Δ : ℕ → Option Tm} {fid : ℕ} {body : Tm}
    {P : α → Prop} {f : α → β} {cost : α → ℕ} (hΔ : Δ fid = some body)
    (h : EmbedsE Δ body P (fun a => [toVal a]) f cost) : Embeds Δ fid P f cost := by
  intro B a ha hfit
  exact Runs.mk hΔ (h B a ha ((fitsL_single B _ _).mpr hfit))

theorem Embeds.mono_cost {α β : Type} [ToVal α] [ToVal β] {Δ : ℕ → Option Tm} {fid : ℕ} {P : α → Prop}
    {f : α → β} {cost cost' : α → ℕ} (h : Embeds Δ fid P f cost) (hc : ∀ a, P a → cost a ≤ cost' a) :
    Embeds Δ fid P f cost' :=
  fun B a ha hfit => (h B a ha (hfit.mono_cost (hc a ha))).mono (hc a ha)

theorem Embeds.mono_pre {α β : Type} [ToVal α] [ToVal β] {Δ : ℕ → Option Tm} {fid : ℕ} {P P' : α → Prop}
    {f : α → β} {cost : α → ℕ} (h : Embeds Δ fid P f cost) (hP : ∀ a, P' a → P a) :
    Embeds Δ fid P' f cost := fun B a ha hfit => h B a (hP a ha) hfit

theorem Embeds.ext {α β : Type} [ToVal α] [ToVal β] {Δ Δ' : ℕ → Option Tm} {fid : ℕ} {P : α → Prop}
    {f : α → β} {cost : α → ℕ} (hΔ : Δ ⊑ Δ') (h : Embeds Δ fid P f cost) : Embeds Δ' fid P f cost :=
  fun B a ha hfit => (h B a ha hfit).weaken hΔ (Nat.le_refl _)

end Lax117284Proofs.Treewidth.Fun
