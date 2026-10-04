import Lax117284Proofs.Treewidth.Fun.Defs
import Lax117284Proofs.Treewidth.Fun.ToVal

/-! ### `Lax117284Proofs.Treewidth.Fun.Meta` -/

section
/-!
# WP F0 (1): meta-theory of `Ev` / `EvL` / `Runs`

* determinism (value and cost),
* weakening in the bound `B` and in the function table `Δ` (`Δ ⊑ Δ'`),
* environment extension,
* `EvLe` (evaluation within a cost *bound*) and its constructor lemmas — the working interface of `ev_step`,
* congruence of `Runs` (`Runs.mono`, `Runs.mono_B`, `Runs.bind`, …).
-/

namespace Lax117284Proofs.Treewidth.Fun

/-- `Δ'` extends `Δ` (`Δ ⊑ Δ'`): every function of `Δ` is present with the same body. -/
def Ext (Δ Δ' : ℕ → Option Tm) : Prop := ∀ f b, Δ f = some b → Δ' f = some b

infixl:50 " ⊑ " => Ext

theorem Ext.refl (Δ : ℕ → Option Tm) : Δ ⊑ Δ := fun _ _ h => h
theorem Ext.trans {Δ₁ Δ₂ Δ₃ : ℕ → Option Tm} (h₁ : Δ₁ ⊑ Δ₂) (h₂ : Δ₂ ⊑ Δ₃) : Δ₁ ⊑ Δ₃ :=
  fun f b h => h₂ f b (h₁ f b h)

/-- Union of two tables; the left one has priority. -/
def orElseΔ (Δ₁ Δ₂ : ℕ → Option Tm) : ℕ → Option Tm := fun f => (Δ₁ f).or (Δ₂ f)

theorem Ext.orElse_left (Δ₁ Δ₂ : ℕ → Option Tm) : Δ₁ ⊑ orElseΔ Δ₁ Δ₂ := by
  intro f b h; simp [orElseΔ, h]

theorem Ext.orElse_right {Δ₁ Δ₂ : ℕ → Option Tm} (hd : ∀ f b, Δ₂ f = some b → Δ₁ f = none) :
    Δ₂ ⊑ orElseΔ Δ₁ Δ₂ := by
  intro f b h; simp [orElseΔ, hd f b h, h]

/-- A layered table: functions with id `≥ lo` come from `tbl`, all others from `base`. -/
def layerΔ (base : ℕ → Option Tm) (lo : ℕ) (tbl : ℕ → Option Tm) : ℕ → Option Tm :=
  fun f => if lo ≤ f then tbl f else base f

theorem Ext.layer {base : ℕ → Option Tm} {lo : ℕ} (tbl : ℕ → Option Tm) (h : ∀ f b, base f = some b → f < lo) :
    base ⊑ layerΔ base lo tbl := by
  intro f b hf
  have := h f b hf
  simp [layerΔ, Nat.not_le.mpr this, hf]

theorem layerΔ_ge {base : ℕ → Option Tm} {lo f : ℕ} (tbl : ℕ → Option Tm) (hf : lo ≤ f) :
    layerΔ base lo tbl f = tbl f := by simp [layerΔ, hf]

theorem Ext.layer_mono {base : ℕ → Option Tm} {lo : ℕ} {tbl tbl' : ℕ → Option Tm} (h : tbl ⊑ tbl') :
    layerΔ base lo tbl ⊑ layerΔ base lo tbl' := by
  intro f b hf
  by_cases hlo : lo ≤ f
  · simp only [layerΔ, hlo, if_true] at hf ⊢; exact h f b hf
  · simpa [layerΔ, hlo] using hf

/-- A finite table as an association list (first entry wins). -/
def lookupL : List (ℕ × Tm) → ℕ → Option Tm
  | [], _ => none
  | (i, t) :: es, f => if i = f then some t else lookupL es f

theorem lookupL_mem {es : List (ℕ × Tm)} {f : ℕ} {b : Tm} (h : lookupL es f = some b) : ∃ p ∈ es, p.1 = f := by
  induction es with
  | nil => simp [lookupL] at h
  | cons e es ih =>
    obtain ⟨i, t⟩ := e
    by_cases hi : i = f
    · exact ⟨(i, t), by simp, hi⟩
    · simp only [lookupL, hi, if_false] at h
      obtain ⟨p, hp, hpf⟩ := ih h
      exact ⟨p, List.mem_cons_of_mem _ hp, hpf⟩

theorem lookupL_lt {es : List (ℕ × Tm)} {size : ℕ} (hes : ∀ p ∈ es, p.1 < size) {f : ℕ} {b : Tm}
    (h : lookupL es f = some b) : f < size := by
  obtain ⟨p, hp, rfl⟩ := lookupL_mem h
  exact hes p hp

/-! ### weakening -/

theorem Ev.weaken {Δ Δ' : ℕ → Option Tm} {B B' : ℕ} (hΔ : Δ ⊑ Δ') (hB : B ≤ B')
    {ρ : List Val} {t : Tm} {v : Val} {c : ℕ} (h : Ev Δ B ρ t v c) : Ev Δ' B' ρ t v c := by
  induction h using Ev.rec (motive_2 := fun ρ ts vs c _ => EvL Δ' B' ρ ts vs c)
  · rename_i h; exact .lit (Nat.lt_of_lt_of_le h hB)
  · rename_i h; exact .var h
  · rename_i _ _ hm iha ihb; exact .add iha ihb (Nat.lt_of_lt_of_le hm hB)
  · rename_i _ _ iha ihb; exact .sub iha ihb
  · rename_i _ _ hm iha ihb; exact .mul iha ihb (Nat.lt_of_lt_of_le hm hB)
  · rename_i _ _ iha ihb; exact .lt iha ihb
  · rename_i _ _ iha ihb; exact .eq iha ihb
  · rename_i _ _ iha ihb; exact .cons iha ihb
  · rename_i _ iha; exact .fst iha
  · rename_i _ iha; exact .snd iha
  · rename_i _ iha; exact .isNatT iha
  · rename_i _ iha; exact .isNatF iha
  · rename_i _ hn _ ihc iht; exact .iteT ihc hn iht
  · rename_i _ _ ihc ihe; exact .iteF ihc ihe
  · rename_i _ _ iha ihb; exact .letE iha ihb
  · rename_i _ hf _ ihargs ihbody; exact .call ihargs (hΔ _ _ hf) ihbody
  · rename_i _ _ hf _ ihft ihargs ihbody; exact .callv ihft ihargs (hΔ _ _ hf) ihbody
  · exact .nil
  · rename_i _ _ iht ihts; exact .cons iht ihts

/-! ### determinism -/

/-! ### environment extension -/

/-- `ρ'` refines `ρ`: every variable bound in `ρ` is bound to the same value in `ρ'`. -/
def EnvLe (ρ ρ' : List Val) : Prop := ∀ (i : ℕ) (v : Val), ρ[i]? = some v → ρ'[i]? = some v

/-! ### evaluation within a cost bound -/

/-- `t` evaluates to `v` in at most `c` steps. -/
def EvLe (Δ : ℕ → Option Tm) (B : ℕ) (ρ : List Val) (t : Tm) (v : Val) (c : ℕ) : Prop :=
  ∃ c' ≤ c, Ev Δ B ρ t v c'

/-- The argument list evaluates to `vs` in at most `c` steps. -/
def EvLL (Δ : ℕ → Option Tm) (B : ℕ) (ρ : List Val) (ts : List Tm) (vs : List Val) (c : ℕ) : Prop :=
  ∃ c' ≤ c, EvL Δ B ρ ts vs c'

theorem Ev.le {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {t : Tm} {v : Val} {c : ℕ} (h : Ev Δ B ρ t v c) :
    EvLe Δ B ρ t v c := ⟨c, Nat.le_refl _, h⟩

theorem EvL.le {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {ts : List Tm} {vs : List Val} {c : ℕ}
    (h : EvL Δ B ρ ts vs c) : EvLL Δ B ρ ts vs c := ⟨c, Nat.le_refl _, h⟩

namespace EvLe
variable {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val}

theorem mono {t : Tm} {v : Val} {c c' : ℕ} (h : EvLe Δ B ρ t v c) (hc : c ≤ c') : EvLe Δ B ρ t v c' := by
  obtain ⟨d, hd, e⟩ := h; exact ⟨d, Nat.le_trans hd hc, e⟩

theorem lit {n : ℕ} {v : Val} (h : n < B) (hv : v = .nat n) : EvLe Δ B ρ (.lit n) v 1 := hv ▸ (Ev.lit h).le
theorem var {i : ℕ} {v : Val} (h : ρ[i]? = some v) : EvLe Δ B ρ (.var i) v 1 := (Ev.var h).le

theorem add {a b : Tm} {m n c₁ c₂ : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat m) c₁)
    (hb : EvLe Δ B ρ b (.nat n) c₂) (hm : m + n < B) (hv : v = .nat (m + n)) :
    EvLe Δ B ρ (.add a b) v (c₁ + c₂ + 1) := by
  subst hv
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .add e₁ e₂ hm⟩
theorem sub {a b : Tm} {m n c₁ c₂ : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat m) c₁)
    (hb : EvLe Δ B ρ b (.nat n) c₂) (hv : v = .nat (m - n)) :
    EvLe Δ B ρ (.sub a b) v (c₁ + c₂ + 1) := by
  subst hv
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .sub e₁ e₂⟩
theorem mul {a b : Tm} {m n c₁ c₂ : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat m) c₁)
    (hb : EvLe Δ B ρ b (.nat n) c₂) (hm : m * n < B) (hv : v = .nat (m * n)) :
    EvLe Δ B ρ (.mul a b) v (c₁ + c₂ + 1) := by
  subst hv
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .mul e₁ e₂ hm⟩
theorem lt {a b : Tm} {m n c₁ c₂ : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat m) c₁)
    (hb : EvLe Δ B ρ b (.nat n) c₂) (hv : v = .nat (if m < n then 1 else 0)) :
    EvLe Δ B ρ (.lt a b) v (c₁ + c₂ + 1) := by
  subst hv
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .lt e₁ e₂⟩
theorem eq {a b : Tm} {m n c₁ c₂ : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat m) c₁)
    (hb : EvLe Δ B ρ b (.nat n) c₂) (hv : v = .nat (if m = n then 1 else 0)) :
    EvLe Δ B ρ (.eq a b) v (c₁ + c₂ + 1) := by
  subst hv
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .eq e₁ e₂⟩
theorem cons {a b : Tm} {u v : Val} {c₁ c₂ : ℕ} (ha : EvLe Δ B ρ a u c₁) (hb : EvLe Δ B ρ b v c₂) :
    EvLe Δ B ρ (.cons a b) (.cons u v) (c₁ + c₂ + 1) := by
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .cons e₁ e₂⟩
theorem fst {a : Tm} {u v : Val} {c : ℕ} (ha : EvLe Δ B ρ a (.cons u v) c) :
    EvLe Δ B ρ (.fst a) u (c + 1) := by
  obtain ⟨d, h, e⟩ := ha; exact ⟨d + 1, by omega, .fst e⟩
theorem snd {a : Tm} {u v : Val} {c : ℕ} (ha : EvLe Δ B ρ a (.cons u v) c) :
    EvLe Δ B ρ (.snd a) v (c + 1) := by
  obtain ⟨d, h, e⟩ := ha; exact ⟨d + 1, by omega, .snd e⟩
theorem isNatT {a : Tm} {n c : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.nat n) c) (hv : v = .nat 1) :
    EvLe Δ B ρ (.isNat a) v (c + 1) := by
  subst hv
  obtain ⟨d, h, e⟩ := ha; exact ⟨d + 1, by omega, .isNatT e⟩
theorem isNatF {a : Tm} {u w : Val} {c : ℕ} {v : Val} (ha : EvLe Δ B ρ a (.cons u w) c) (hv : v = .nat 0) :
    EvLe Δ B ρ (.isNat a) v (c + 1) := by
  subst hv
  obtain ⟨d, h, e⟩ := ha; exact ⟨d + 1, by omega, .isNatF e⟩
theorem iteT {cnd t e : Tm} {n : ℕ} {v : Val} {c₁ c₂ : ℕ} (hc : EvLe Δ B ρ cnd (.nat n) c₁) (hn : n ≠ 0)
    (ht : EvLe Δ B ρ t v c₂) : EvLe Δ B ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  obtain ⟨d₁, h₁, e₁⟩ := hc; obtain ⟨d₂, h₂, e₂⟩ := ht
  exact ⟨d₁ + d₂ + 1, by omega, .iteT e₁ hn e₂⟩
theorem iteF {cnd t e : Tm} {n : ℕ} {v : Val} {c₁ c₂ : ℕ} (hc : EvLe Δ B ρ cnd (.nat n) c₁) (hn : n = 0)
    (he : EvLe Δ B ρ e v c₂) : EvLe Δ B ρ (.ite cnd t e) v (c₁ + c₂ + 1) := by
  subst hn
  obtain ⟨d₁, h₁, e₁⟩ := hc; obtain ⟨d₂, h₂, e₂⟩ := he
  exact ⟨d₁ + d₂ + 1, by omega, .iteF e₁ e₂⟩
theorem letE {a b : Tm} {u v : Val} {c₁ c₂ : ℕ} (ha : EvLe Δ B ρ a u c₁) (hb : EvLe Δ B (u :: ρ) b v c₂) :
    EvLe Δ B ρ (.letE a b) v (c₁ + c₂ + 1) := by
  obtain ⟨d₁, h₁, e₁⟩ := ha; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .letE e₁ e₂⟩
theorem call {f : ℕ} {args : List Tm} {body : Tm} {vs : List Val} {v : Val} {c₁ c₂ : ℕ}
    (hargs : EvLL Δ B ρ args vs c₁) (hf : Δ f = some body) (hb : EvLe Δ B vs body v c₂) :
    EvLe Δ B ρ (.call f args) v (c₁ + c₂ + 1) := by
  obtain ⟨d₁, h₁, e₁⟩ := hargs; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₁ + d₂ + 1, by omega, .call e₁ hf e₂⟩
theorem callv {ft : Tm} {f : ℕ} {args : List Tm} {body : Tm} {vs : List Val} {v : Val} {c₀ c₁ c₂ : ℕ}
    (hft : EvLe Δ B ρ ft (.nat f) c₀) (hargs : EvLL Δ B ρ args vs c₁) (hf : Δ f = some body)
    (hb : EvLe Δ B vs body v c₂) : EvLe Δ B ρ (.callv ft args) v (c₀ + c₁ + c₂ + 1) := by
  obtain ⟨d₀, h₀, e₀⟩ := hft; obtain ⟨d₁, h₁, e₁⟩ := hargs; obtain ⟨d₂, h₂, e₂⟩ := hb
  exact ⟨d₀ + d₁ + d₂ + 1, by omega, .callv e₀ e₁ hf e₂⟩

end EvLe

namespace EvLL
variable {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val}

theorem nil : EvLL Δ B ρ [] [] 0 := EvL.nil.le
theorem cons {t : Tm} {ts : List Tm} {v : Val} {vs : List Val} {c₁ c₂ : ℕ} (ht : EvLe Δ B ρ t v c₁)
    (hts : EvLL Δ B ρ ts vs c₂) : EvLL Δ B ρ (t :: ts) (v :: vs) (c₁ + c₂) := by
  obtain ⟨d₁, h₁, e₁⟩ := ht; obtain ⟨d₂, h₂, e₂⟩ := hts
  exact ⟨d₁ + d₂, by omega, .cons e₁ e₂⟩
end EvLL

/-! ### `Runs` -/

namespace Runs
variable {Δ : ℕ → Option Tm} {B f : ℕ} {xs : List Val} {y : Val} {c : ℕ}

theorem mk {body : Tm} (hf : Δ f = some body) (h : EvLe Δ B xs body y c) : Runs Δ B f xs y c :=
  ⟨body, hf, h⟩

theorem mono {c' : ℕ} (h : Runs Δ B f xs y c) (hc : c ≤ c') : Runs Δ B f xs y c' := by
  obtain ⟨b, hb, d, hd, e⟩ := h; exact ⟨b, hb, d, Nat.le_trans hd hc, e⟩

theorem weaken {Δ' : ℕ → Option Tm} {B' : ℕ} (hΔ : Δ ⊑ Δ') (hB : B ≤ B') (h : Runs Δ B f xs y c) :
    Runs Δ' B' f xs y c := by
  obtain ⟨b, hb, d, hd, e⟩ := h; exact ⟨b, hΔ _ _ hb, d, hd, e.weaken hΔ hB⟩

/-- the call of a function inside a term. -/
theorem evle {ρ : List Val} {args : List Tm} {c₁ : ℕ} (hargs : EvLL Δ B ρ args xs c₁) (h : Runs Δ B f xs y c) :
    EvLe Δ B ρ (.call f args) y (c₁ + c + 1) := by
  obtain ⟨b, hb, h⟩ := h; exact EvLe.call hargs hb h

theorem evle_v {ρ : List Val} {ft : Tm} {args : List Tm} {c₀ c₁ : ℕ} (hft : EvLe Δ B ρ ft (.nat f) c₀)
    (hargs : EvLL Δ B ρ args xs c₁) (h : Runs Δ B f xs y c) :
    EvLe Δ B ρ (.callv ft args) y (c₀ + c₁ + c + 1) := by
  obtain ⟨b, hb, h⟩ := h; exact EvLe.callv hft hargs hb h

end Runs

/-- variables `i, i+1, …, i+n-1` as argument terms. -/
def Tm.vars (i n : ℕ) : List Tm := (List.range n).map fun j => Tm.var (i + j)

end Lax117284Proofs.Treewidth.Fun

end

/-! ### `Lax117284Proofs.Treewidth.Fun.Kit` -/

section
/-!
# The `ev_*` tactic kit

Goals of the form `EvLe Δ B ρ t v c` (term `t` evaluates to `v` within cost `c`) are discharged by

* `ev_start` : replaces the cost bound `c` by a metavariable (the exact cost, assembled bottom-up) and leaves
  the side goal `?c ≤ c` **last** (close it with `omega`/`nlinarith` after everything else);
* `ev_step`  : one construct — `lit var add sub mul lt eq cons fst snd isNat(T/F) ite(T/F) letE`, and argument lists;
* `ev_run`   : `repeat' ev_step`, leaving only side goals (`n < B`, `ρ[i]? = some v`, `n ≠ 0`, …);
* `ev_side`  : closes the standard side goals (`rfl`, `simp`, `omega`, `decide`);
* `ev_call h`, `ev_callv h` : a call of a function whose behaviour is a `Runs` fact `h`.

`ite` needs the branch: `ev_iteT` / `ev_iteF`.
-/

namespace Lax117284Proofs.Treewidth.Fun

syntax "ev_start" : tactic
macro_rules
  | `(tactic| ev_start) => `(tactic| apply EvLe.mono)

open Lean Meta Elab Tactic in
/-- succeeds iff the main goal is a proposition that is not itself an `EvLe`/`EvLL` goal. -/
elab "ev_is_side" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  unless (← isProp ty) do throwError "ev_side: not a proposition"
  let ty ← whnfR ty
  if ty.getAppFn.isConstOf ``EvLe || ty.getAppFn.isConstOf ``EvLL then
    throwError "ev_side: an evaluation goal"

syntax "ev_side" : tactic
macro_rules
  | `(tactic| ev_side) => `(tactic| (ev_is_side; first | rfl | (simp; done) | omega | decide | (simp [*]; done) | (simp_all; done)))

syntax "ev_step" : tactic
syntax "ev_sub" : tactic
macro_rules
  | `(tactic| ev_step) => `(tactic| first
    | apply EvLe.lit
    | apply EvLe.var
    | apply EvLe.add
    | apply EvLe.sub
    | apply EvLe.mul
    | apply EvLe.lt
    | apply EvLe.eq
    | apply EvLe.cons
    | apply EvLe.fst
    | apply EvLe.snd
    | (apply EvLe.isNatT; (case ha => ev_sub))
    | (apply EvLe.isNatF; (case ha => ev_sub))
    | (apply EvLe.iteT; (case hc => ev_sub); (case hn => ev_side))
    | (apply EvLe.iteF; (case hc => ev_sub); (case hn => ev_side))
    | apply EvLe.letE
    | apply EvLL.cons
    | (apply Runs.evle ?hargs ?hrun; (case hargs => ev_sub); (case hrun => assumption))
    | (apply Runs.evle_v ?hft ?hargs ?hrun; (case hft => ev_sub); (case hargs => ev_sub); (case hrun => assumption))
    | exact EvLL.nil)
  | `(tactic| ev_sub) => `(tactic| ((all_goals (repeat' ev_step)); (all_goals try ev_side); (all_goals try ev_side); done))

/-- solve as much as possible, leaving the stuck goals (side conditions or evaluation goals). -/
syntax "ev_run" : tactic
macro_rules
  | `(tactic| ev_run) => `(tactic| ((all_goals (repeat' ev_step)); (all_goals try ev_side); (all_goals try ev_side)))

/-- choose the branch explicitly. -/
syntax "ev_iteT" : tactic
macro_rules
  | `(tactic| ev_iteT) => `(tactic| apply EvLe.iteT)
syntax "ev_iteF" : tactic
macro_rules
  | `(tactic| ev_iteF) => `(tactic| apply EvLe.iteF)

syntax "ev_call " term : tactic
macro_rules
  | `(tactic| ev_call $h) => `(tactic| apply Runs.evle _ $h)
syntax "ev_callv " term : tactic
macro_rules
  | `(tactic| ev_callv $h) => `(tactic| apply Runs.evle_v _ _ $h)

end Lax117284Proofs.Treewidth.Fun

end
