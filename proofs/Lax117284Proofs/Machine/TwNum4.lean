import Lax117284Proofs.Machine.TwNum3

/-!
Polynomial bounds for the numbers of a word: the length, the logarithm, the word length of the
decomposition step, the sizes of the tables and the running time of the decomposition step.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)

theorem PlOn.addL {P : List ℕ → Prop} {f g : List ℕ → ℕ} (hf : PlOn Lp P f) (hg : PlOn Lp P g) :
    PlOn Lp P (fun x => f x + g x) := PlOn.add (fun x _ => Lp_pos x) hf hg

theorem PlOn.addA {P : List ℕ → Prop} {f g : List ℕ → ℕ} (hf : PlOn Aw P f) (hg : PlOn Aw P g) :
    PlOn Aw P (fun x => f x + g x) := PlOn.add (fun x _ => Aw_pos x) hf hg

variable {P : List ℕ → Prop} {ca cc plit : ℕ}

theorem atom_len : PlOn Lp P (fun x => x.length) :=
  PlOn.base.mono (fun x _ => by unfold Lp; omega)

theorem atom_lg : PlOn Lp P lgx :=
  atom_len.mono (fun x _ => by unfold lgx; exact Nat.log_le_self 2 _)

theorem atom_Wp : PlOn Lp P (Wpx cc plit) := by
  have h : PlOn Lp P (fun x => (2 * cc + 1) * lgx x + 4 * cc + plit) :=
    (((PlOn.const _).mul atom_lg).addL (PlOn.const _)).addL (PlOn.const _)
  exact h

theorem atom_Pn (hP : ∀ x, P x → Dm x) : PlOn Lp P (fun x => 2 ^ Wpx cc plit x) := by
  have h : PlOn Lp P (fun x => 2 ^ (4 * cc + plit) * x.length ^ (2 * cc + 1)) :=
    (PlOn.const _).mul (atom_len.pow _)
  refine h.mono (fun x hx => ?_)
  have hL := (hP x hx).three
  have h1 : 2 ^ lgx x ≤ x.length := Nat.pow_log_le_self 2 (by omega)
  unfold Wpx
  have : 2 ^ ((2 * cc + 1) * lgx x + 4 * cc + plit) =
      2 ^ (4 * cc + plit) * (2 ^ lgx x) ^ (2 * cc + 1) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  rw [this]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)

/-- Under the guard. -/
theorem atom_m (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) mx := by
  refine atom_len.mono (fun x hx => ?_)
  have := (hx.1.gd hca hcc hx.2).mlg
  have := (hx.1.gd hca hcc hx.2).lgL
  omega

theorem atom_n (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) nx :=
  atom_len.mono (fun x hx => hx.1.nL hx.2.2)

theorem atom_w (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (wx cc) := by
  refine atom_len.mono (fun x hx => ?_)
  have := (hx.1.gd hca hcc hx.2).wlg
  have := (hx.1.gd hca hcc hx.2).lgL
  omega

theorem atom_pm (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ mx x) :=
  atom_len.mono (fun x hx => (hx.1.gd hca hcc hx.2).pm)

theorem atom_tabs (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (tabsx cc) :=
  atom_len.mono (fun x hx => (hx.1.gd hca hcc hx.2).tabs)

theorem atom_Tb (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x) (Tbx ca cc) := by
  have h : PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => ca * x.length * (x.length * x.length + 3) ^ ca) :=
    ((PlOn.const ca).mul atom_len).mul (((atom_len.mul atom_len).addL (PlOn.const 3)).pow ca)
  refine h.mono (fun x hx => ?_)
  have hg := hx.1.gd hca hcc hx.2
  have hn := hx.1.nL hx.2.2
  unfold Tbx
  have h1 : nx x * nx x + 3 ≤ x.length * x.length + 3 := by have := Nat.mul_le_mul hn hn; omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hg.pw) (Nat.pow_le_pow_left h1 _)

end Lax117284Proofs.Machine.TwNum
