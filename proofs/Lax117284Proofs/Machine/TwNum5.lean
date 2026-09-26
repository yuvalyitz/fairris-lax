import Lax117284Proofs.Machine.TwNum4

/-!
The bound on the values of the main program, and the facts about it that the correctness theorem
asks of it.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

/-- The largest number in the code of a program, in sum. -/
def PLit (prog : Program) : ℕ := (prog.map fun i => opcode i + fa i + fb i + fc i).sum

theorem le_PLit {prog : Program} {i : Instr} (h : i ∈ prog) :
    opcode i ≤ PLit prog ∧ fa i ≤ PLit prog ∧ fb i ≤ PLit prog ∧ fc i ≤ PLit prog := by
  unfold PLit
  induction prog with
  | nil => cases h
  | cons j rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- The part of the bound that is present whether or not the guard holds. -/
def bU (prog : Program) (cc plit : ℕ) (x : List ℕ) : ℕ :=
  4 * x.length + 64 + 3 * Mx x + TwPrep.geE cc (mx x) (lgx x) + 2 * cc + plit + Wpx cc plit x +
    2 ^ Wpx cc plit x + PLit prog + prog.length + 64

/-- The part of the bound that the guarded branch needs. -/
def bG (ca cc plit : ℕ) (x : List ℕ) : ℕ :=
  2 ^ mx x + nx x * nx x + wx cc x + 2 ^ Wpx cc plit x * 2 ^ Wpx cc plit x + 2 ^ Wpx cc plit x +
    Tbx ca cc x + Tbx ca cc x * tabsx cc x + tabsx cc x + Tbx ca cc x * (wx cc x + 1) +
    (wx cc x + 1) + 3 * Tbx ca cc x + tabsx cc x * 2 ^ mx x +
    (wx cc x + 1) * ((wx cc x + 1) * mx x + 1) + (wx cc x + 1) * mx x + mx x +
    mx x * (wx cc x + 1 + 1) + 64

open Classical in
/-- **The bound on the values of the main program.** -/
noncomputable def Bx (prog : Program) (ca cc plit : ℕ) (x : List ℕ) : ℕ :=
  bU prog cc plit x + (if gdx cc x then bG ca cc plit x else 0) + 1

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ} {P : List ℕ → Prop}

theorem Bx_pos (x : List ℕ) : 1 < Bx prog ca cc plit x := by
  unfold Bx bU; have := Nat.two_pow_pos (Wpx cc plit x); omega

/-! ### The bound is polynomial -/

theorem atom_Mx : PlOn Aw P Mx :=
  PlOn.base.mono (fun x _ => by unfold Aw; omega)

theorem atom_lenA : PlOn Aw P (fun x => x.length) :=
  PlOn.base.mono (fun x _ => by unfold Aw; omega)

theorem PlOn.toA {f : List ℕ → ℕ} (h : PlOn Lp P f) : PlOn Aw P f :=
  h.base_mono (fun x _ => Lp_le_Aw x)

theorem plon_bU (hP : ∀ x, P x → Dm x) : PlOn Aw P (bU prog cc plit) := by
  have hm : PlOn Aw P mx := atom_Mx.mono (fun x hx => (hP x hx).nMx.2)
  have hlg : PlOn Aw P lgx := atom_lg.toA
  have hge : PlOn Aw P (fun x => TwPrep.geE cc (mx x) (lgx x)) := by
    have : PlOn Aw P (fun x => cc * ((lgx x + 1) * (lgx x + 1) * (lgx x + 1)) +
        mx x * (lgx x + 1) + 2) := by
      repeat' first | exact hm | exact hlg | exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul
    exact this
  have hWp : PlOn Aw P (Wpx cc plit) := atom_Wp.toA
  have hPn : PlOn Aw P (fun x => 2 ^ Wpx cc plit x) := (atom_Pn hP).toA
  show PlOn Aw P (fun x => bU prog cc plit x)
  unfold bU
  repeat' first | exact hge | exact hWp | exact hPn | exact atom_Mx | exact atom_lenA |
    exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul

theorem plon_bG (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Aw (fun x => Dm x ∧ gdx cc x) (bG ca cc plit) := by
  have hm : PlOn Aw (fun x => Dm x ∧ gdx cc x) mx := (atom_m hca hcc).toA
  have hn : PlOn Aw (fun x => Dm x ∧ gdx cc x) nx := (atom_n hca hcc).toA
  have hw : PlOn Aw (fun x => Dm x ∧ gdx cc x) (wx cc) := (atom_w hca hcc).toA
  have hpm : PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ mx x) := (atom_pm hca hcc).toA
  have htb : PlOn Aw (fun x => Dm x ∧ gdx cc x) (Tbx ca cc) := (atom_Tb hca hcc).toA
  have hta : PlOn Aw (fun x => Dm x ∧ gdx cc x) (tabsx cc) := (atom_tabs hca hcc).toA
  have hPn : PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ Wpx cc plit x) :=
    (atom_Pn (fun x hx => hx.1)).toA
  show PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => bG ca cc plit x)
  unfold bG
  repeat' first | exact hm | exact hn | exact hw | exact hpm | exact htb | exact hta | exact hPn |
    exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul

open Classical in
theorem plon_Bx (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) : PlOn Aw Dm (Bx prog ca cc plit) := by
  have h1 : PlOn Aw Dm (bU prog cc plit) := plon_bU (fun x hx => hx)
  have h2 : PlOn Aw Dm (fun x => if gdx cc x then bG ca cc plit x else 0) :=
    PlOn.guard (plon_bG hca hcc)
  show PlOn Aw Dm (fun x => bU prog cc plit x + (if gdx cc x then bG ca cc plit x else 0) + 1)
  exact (h1.addA h2).addA (PlOn.const 1)

end Lax117284Proofs.Machine.TwNum
