import Lax117284Proofs.Treewidth.Fun.Defs

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

theorem EvL.weaken {Δ Δ' : ℕ → Option Tm} {B B' : ℕ} (hΔ : Δ ⊑ Δ') (hB : B ≤ B')
    {ρ : List Val} {ts : List Tm} {vs : List Val} {c : ℕ} (h : EvL Δ B ρ ts vs c) :
    EvL Δ' B' ρ ts vs c := by
  induction h using EvL.rec (motive_1 := fun _ _ _ _ _ => True) <;> first
    | trivial
    | exact .nil
    | (rename_i ht _ _ ih; exact .cons (ht.weaken hΔ hB) ih)

theorem Ev.weakenB {Δ : ℕ → Option Tm} {B B' : ℕ} (hB : B ≤ B') {ρ : List Val} {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : Ev Δ B' ρ t v c := h.weaken (Ext.refl Δ) hB

theorem Ev.weakenΔ {Δ Δ' : ℕ → Option Tm} {B : ℕ} (hΔ : Δ ⊑ Δ') {ρ : List Val} {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : Ev Δ' B ρ t v c := h.weaken hΔ (Nat.le_refl _)

theorem EvL.weakenB {Δ : ℕ → Option Tm} {B B' : ℕ} (hB : B ≤ B') {ρ : List Val} {ts : List Tm}
    {vs : List Val} {c : ℕ} (h : EvL Δ B ρ ts vs c) : EvL Δ B' ρ ts vs c := EvL.weaken (Ext.refl Δ) hB h

theorem EvL.weakenΔ {Δ Δ' : ℕ → Option Tm} {B : ℕ} (hΔ : Δ ⊑ Δ') {ρ : List Val} {ts : List Tm}
    {vs : List Val} {c : ℕ} (h : EvL Δ B ρ ts vs c) : EvL Δ' B ρ ts vs c := EvL.weaken hΔ (Nat.le_refl _) h

/-! ### determinism -/

theorem Ev.det_aux {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : ∀ v' c', Ev Δ B ρ t v' c' → v = v' ∧ c = c' := by
  induction h using Ev.rec (motive_2 := fun ρ ts vs c _ => ∀ vs' c', EvL Δ B ρ ts vs' c' → vs = vs' ∧ c = c')
  · intro v' c' h'; cases h'; exact ⟨rfl, rfl⟩
  · rename_i h; intro v' c' h'; cases h' with | var h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  · rename_i _ _ _ iha ihb; intro v' c' h'; cases h' with | add ha' hb' _ =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    cases e1; cases e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ iha ihb; intro v' c' h'; cases h' with | sub ha' hb' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    cases e1; cases e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ _ iha ihb; intro v' c' h'; cases h' with | mul ha' hb' _ =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    cases e1; cases e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ iha ihb; intro v' c' h'; cases h' with | lt ha' hb' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    cases e1; cases e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ iha ihb; intro v' c' h'; cases h' with | eq ha' hb' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    cases e1; cases e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ iha ihb; intro v' c' h'; cases h' with | cons ha' hb' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; obtain ⟨e3, e4⟩ := ihb _ _ hb'
    subst e1; subst e3; subst e2; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ iha; intro v' c' h'; cases h' with | fst ha' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; cases e1; subst e2; exact ⟨rfl, rfl⟩
  · rename_i _ iha; intro v' c' h'; cases h' with | snd ha' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; cases e1; subst e2; exact ⟨rfl, rfl⟩
  · rename_i _ iha; intro v' c' h'; cases h' with
    | isNatT ha' => obtain ⟨_, e2⟩ := iha _ _ ha'; subst e2; exact ⟨rfl, rfl⟩
    | isNatF ha' => obtain ⟨e1, _⟩ := iha _ _ ha'; cases e1
  · rename_i _ iha; intro v' c' h'; cases h' with
    | isNatT ha' => obtain ⟨e1, _⟩ := iha _ _ ha'; cases e1
    | isNatF ha' => obtain ⟨_, e2⟩ := iha _ _ ha'; subst e2; exact ⟨rfl, rfl⟩
  · rename_i _ hn _ ihc iht; intro v' c' h'; cases h' with
    | iteT hc' hn' ht' =>
      obtain ⟨_, e2⟩ := ihc _ _ hc'; obtain ⟨e3, e4⟩ := iht _ _ ht'
      subst e2; subst e3; subst e4; exact ⟨rfl, rfl⟩
    | iteF hc' he' => obtain ⟨e1, _⟩ := ihc _ _ hc'; cases e1; exact absurd rfl hn
  · rename_i _ _ ihc ihe; intro v' c' h'; cases h' with
    | iteT hc' hn' ht' => obtain ⟨e1, _⟩ := ihc _ _ hc'; cases e1; exact absurd rfl hn'
    | iteF hc' he' =>
      obtain ⟨_, e2⟩ := ihc _ _ hc'; obtain ⟨e3, e4⟩ := ihe _ _ he'
      subst e2; subst e3; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ iha ihb; intro v' c' h'; cases h' with | letE ha' hb' =>
    obtain ⟨e1, e2⟩ := iha _ _ ha'; subst e1; subst e2
    obtain ⟨e3, e4⟩ := ihb _ _ hb'; subst e3; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ hf _ ihargs ihbody; intro v' c' h'; cases h' with | call hargs' hf' hbody' =>
    obtain ⟨e1, e2⟩ := ihargs _ _ hargs'; subst e1; subst e2
    rw [hf] at hf'; cases hf'
    obtain ⟨e3, e4⟩ := ihbody _ _ hbody'; subst e3; subst e4; exact ⟨rfl, rfl⟩
  · rename_i _ _ hf _ ihft ihargs ihbody; intro v' c' h'; cases h' with | callv hft' hargs' hf' hbody' =>
    obtain ⟨e0, e0'⟩ := ihft _ _ hft'; cases e0; subst e0'
    obtain ⟨e1, e2⟩ := ihargs _ _ hargs'; subst e1; subst e2
    rw [hf] at hf'; cases hf'
    obtain ⟨e3, e4⟩ := ihbody _ _ hbody'; subst e3; subst e4; exact ⟨rfl, rfl⟩
  · rename_i h'; cases h'; exact ⟨rfl, rfl⟩
  · rename_i _ _ iht ihts; intro vs' c' h'; cases h' with | cons ht' hts' =>
    obtain ⟨e1, e2⟩ := iht _ _ ht'; obtain ⟨e3, e4⟩ := ihts _ _ hts'
    subst e1; subst e2; subst e3; subst e4; exact ⟨rfl, rfl⟩

theorem Ev.det {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {t : Tm} {v v' : Val} {c c' : ℕ}
    (h : Ev Δ B ρ t v c) (h' : Ev Δ B ρ t v' c') : v = v' ∧ c = c' := h.det_aux v' c' h'

theorem EvL.det_aux {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {ts : List Tm} {vs : List Val} {c : ℕ}
    (h : EvL Δ B ρ ts vs c) : ∀ vs' c', EvL Δ B ρ ts vs' c' → vs = vs' ∧ c = c' := by
  induction h using EvL.rec (motive_1 := fun _ _ _ _ _ => True) <;> first
    | trivial
    | (intro vs' c' h'; cases h'; exact ⟨rfl, rfl⟩)
    | (rename_i ht _ _ ih; intro vs' c' h'; cases h' with | cons ht' hts' =>
        obtain ⟨e1, e2⟩ := ht.det ht'; obtain ⟨e3, e4⟩ := ih _ _ hts'
        subst e1; subst e2; subst e3; subst e4; exact ⟨rfl, rfl⟩)

theorem EvL.det {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} {ts : List Tm} {vs vs' : List Val} {c c' : ℕ}
    (h : EvL Δ B ρ ts vs c) (h' : EvL Δ B ρ ts vs' c') : vs = vs' ∧ c = c' := h.det_aux vs' c' h'

/-! ### environment extension -/

/-- `ρ'` refines `ρ`: every variable bound in `ρ` is bound to the same value in `ρ'`. -/
def EnvLe (ρ ρ' : List Val) : Prop := ∀ (i : ℕ) (v : Val), ρ[i]? = some v → ρ'[i]? = some v

theorem EnvLe.refl (ρ : List Val) : EnvLe ρ ρ := fun _ _ h => h
theorem EnvLe.append (ρ ρ' : List Val) : EnvLe ρ (ρ ++ ρ') := by
  intro i v h
  have hi : i < ρ.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi]; exact h
theorem EnvLe.cons {ρ ρ' : List Val} (h : EnvLe ρ ρ') (u : Val) : EnvLe (u :: ρ) (u :: ρ') := by
  intro i v hi
  cases i with
  | zero => simpa using hi
  | succ i => simpa using h i v (by simpa using hi)

theorem Ev.envLe {Δ : ℕ → Option Tm} {B : ℕ} {ρ ρ' : List Val} (hρ : EnvLe ρ ρ') {t : Tm} {v : Val}
    {c : ℕ} (h : Ev Δ B ρ t v c) : Ev Δ B ρ' t v c := by
  revert ρ'
  induction h using Ev.rec (motive_2 := fun ρ ts vs c _ => ∀ ρ', EnvLe ρ ρ' → EvL Δ B ρ' ts vs c)
  · rename_i h; intro ρ' _; exact .lit h
  · rename_i h; intro ρ' hρ; exact .var (hρ _ _ h)
  · rename_i _ _ hm iha ihb; intro ρ' hρ; exact .add (iha hρ) (ihb hρ) hm
  · rename_i _ _ iha ihb; intro ρ' hρ; exact .sub (iha hρ) (ihb hρ)
  · rename_i _ _ hm iha ihb; intro ρ' hρ; exact .mul (iha hρ) (ihb hρ) hm
  · rename_i _ _ iha ihb; intro ρ' hρ; exact .lt (iha hρ) (ihb hρ)
  · rename_i _ _ iha ihb; intro ρ' hρ; exact .eq (iha hρ) (ihb hρ)
  · rename_i _ _ iha ihb; intro ρ' hρ; exact .cons (iha hρ) (ihb hρ)
  · rename_i _ iha; intro ρ' hρ; exact .fst (iha hρ)
  · rename_i _ iha; intro ρ' hρ; exact .snd (iha hρ)
  · rename_i _ iha; intro ρ' hρ; exact .isNatT (iha hρ)
  · rename_i _ iha; intro ρ' hρ; exact .isNatF (iha hρ)
  · rename_i _ hn _ ihc iht; intro ρ' hρ; exact .iteT (ihc hρ) hn (iht hρ)
  · rename_i _ _ ihc ihe; intro ρ' hρ; exact .iteF (ihc hρ) (ihe hρ)
  · rename_i _ _ iha ihb; intro ρ' hρ; exact .letE (iha hρ) (ihb (hρ.cons _))
  · rename_i _ hf _ ihargs ihbody; intro ρ' hρ; exact .call (ihargs _ hρ) hf (ihbody (EnvLe.refl _))
  · rename_i _ _ hf _ ihft ihargs ihbody; intro ρ' hρ
    exact .callv (ihft hρ) (ihargs _ hρ) hf (ihbody (EnvLe.refl _))
  · exact .nil
  · rename_i _ _ iht ihts; intro ρ' hρ; exact .cons (iht hρ) (ihts _ hρ)

theorem Ev.envExt {Δ : ℕ → Option Tm} {B : ℕ} {ρ : List Val} (ρ' : List Val) {t : Tm} {v : Val} {c : ℕ}
    (h : Ev Δ B ρ t v c) : Ev Δ B (ρ ++ ρ') t v c := h.envLe (EnvLe.append ρ ρ')

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

theorem congr_val {t : Tm} {v w : Val} {c : ℕ} (h : EvLe Δ B ρ t v c) (e : v = w) : EvLe Δ B ρ t w c := e ▸ h

theorem weaken {Δ' : ℕ → Option Tm} {B' : ℕ} (hΔ : Δ ⊑ Δ') (hB : B ≤ B') {t : Tm} {v : Val} {c : ℕ}
    (h : EvLe Δ B ρ t v c) : EvLe Δ' B' ρ t v c := by
  obtain ⟨d, hd, e⟩ := h; exact ⟨d, hd, e.weaken hΔ hB⟩

theorem envLe {ρ' : List Val} (hρ : EnvLe ρ ρ') {t : Tm} {v : Val} {c : ℕ} (h : EvLe Δ B ρ t v c) :
    EvLe Δ B ρ' t v c := by
  obtain ⟨d, hd, e⟩ := h; exact ⟨d, hd, e.envLe hρ⟩

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

theorem mono {ts : List Tm} {vs : List Val} {c c' : ℕ} (h : EvLL Δ B ρ ts vs c) (hc : c ≤ c') :
    EvLL Δ B ρ ts vs c' := by
  obtain ⟨d, hd, e⟩ := h; exact ⟨d, Nat.le_trans hd hc, e⟩
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

theorem toEvLe (h : Runs Δ B f xs y c) : ∃ body, Δ f = some body ∧ EvLe Δ B xs body y c := h

theorem mono {c' : ℕ} (h : Runs Δ B f xs y c) (hc : c ≤ c') : Runs Δ B f xs y c' := by
  obtain ⟨b, hb, d, hd, e⟩ := h; exact ⟨b, hb, d, Nat.le_trans hd hc, e⟩

theorem mono_B {B' : ℕ} (hB : B ≤ B') (h : Runs Δ B f xs y c) : Runs Δ B' f xs y c := by
  obtain ⟨b, hb, d, hd, e⟩ := h; exact ⟨b, hb, d, hd, e.weakenB hB⟩

theorem weaken {Δ' : ℕ → Option Tm} {B' : ℕ} (hΔ : Δ ⊑ Δ') (hB : B ≤ B') (h : Runs Δ B f xs y c) :
    Runs Δ' B' f xs y c := by
  obtain ⟨b, hb, d, hd, e⟩ := h; exact ⟨b, hΔ _ _ hb, d, hd, e.weaken hΔ hB⟩

theorem det {y' : Val} {c' : ℕ} (h : Runs Δ B f xs y c) (h' : Runs Δ B f xs y' c') : y = y' := by
  obtain ⟨b, hb, d, _, e⟩ := h; obtain ⟨b', hb', d', _, e'⟩ := h'
  rw [hb] at hb'; cases hb'; exact (e.det e').1

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

theorem Tm.vars_length (i n : ℕ) : (Tm.vars i n).length = n := by simp [Tm.vars]

theorem Tm.vars_succ (i n : ℕ) : Tm.vars i (n + 1) = Tm.var i :: Tm.vars (i + 1) n := by
  simp [Tm.vars, List.range_succ_eq_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- the arguments `vars pre.length vs.length` read the block `vs` out of the environment `pre ++ vs ++ post`. -/
theorem EvLL.varsAt {Δ : ℕ → Option Tm} {B : ℕ} (vs : List Val) : ∀ (pre post : List Val),
    EvLL Δ B (pre ++ vs ++ post) (Tm.vars pre.length vs.length) vs vs.length := by
  induction vs with
  | nil => intro pre post; simpa [Tm.vars] using (EvLL.nil : EvLL Δ B _ [] [] 0)
  | cons v vs ih =>
    intro pre post
    have h0 : (pre ++ v :: vs ++ post)[pre.length]? = some v := by simp
    have h1 := ih (pre ++ [v]) post
    have e : pre ++ [v] ++ vs ++ post = pre ++ v :: vs ++ post := by simp
    rw [e] at h1
    simp only [List.length_append, List.length_cons] at h1 ⊢
    rw [Tm.vars_succ]
    have := EvLL.cons (EvLe.var h0) h1
    simpa [List.append_assoc] using this.mono (by omega)

/-- `h` is the composite of `g` after `f` on the first block of its arguments. -/
theorem Runs.bind {Δ : ℕ → Option Tm} {B f g h : ℕ} {xs ys : List Val} {y z : Val} {c₁ c₂ : ℕ}
    (hh : Δ h = some (.call g (.call f (Tm.vars 0 xs.length) :: Tm.vars xs.length ys.length)))
    (hf : Runs Δ B f xs y c₁) (hg : Runs Δ B g (y :: ys) z c₂) :
    Runs Δ B h (xs ++ ys) z (xs.length + ys.length + c₁ + c₂ + 2) := by
  refine Runs.mk hh ?_
  have h1 : EvLL Δ B (xs ++ ys) (Tm.vars 0 xs.length) xs xs.length := by
    simpa using EvLL.varsAt (Δ := Δ) (B := B) xs [] ys
  have h2 : EvLL Δ B (xs ++ ys) (Tm.vars xs.length ys.length) ys ys.length := by
    simpa using EvLL.varsAt (Δ := Δ) (B := B) ys xs []
  have h3 := hf.evle h1
  have h4 := EvLL.cons h3 h2
  exact (hg.evle h4).mono (by omega)

end Lax117284Proofs.Treewidth.Fun
