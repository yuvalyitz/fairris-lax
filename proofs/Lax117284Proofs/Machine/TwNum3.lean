import Lax117284Proofs.Machine.TwMain5
import Lax117284Proofs.Machine.TwNum0
import Lax117284Proofs.Machine.TwNum2
import Lax117284Proofs.Machine.ClMainBound
import Lax117284Proofs.ClientsWord

/-!
The numbers of a word as functions of it: the guard, the width the decomposition step is run at,
the sizes of the tables, and their polynomial bounds.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284.InstanceEncoding Lax117284.Scheduling Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)

/-- The number of clients a word declares. -/
def nx (x : List ℕ) : ℕ := x.getD 0 0
/-- The number of days a word declares. -/
def mx (x : List ℕ) : ℕ := x.getD 1 0
/-- The binary logarithm of the length of a word. -/
def lgx (x : List ℕ) : ℕ := Nat.log 2 x.length
/-- The number of widths the guard admits. -/
def wcx (cc : ℕ) (x : List ℕ) : ℕ := TwPrep.wcnt cc (mx x) (lgx x)
/-- The width at which the decomposition step is run. -/
def wx (cc : ℕ) (x : List ℕ) : ℕ := wcx cc x - 1
/-- The guard: some width is admitted, and there is a day. -/
def gdx (cc : ℕ) (x : List ℕ) : Prop := 0 < wcx cc x ∧ 0 < mx x
/-- The word length of the decomposition step. -/
def Wpx (cc plit : ℕ) (x : List ℕ) : ℕ := (2 * cc + 1) * lgx x + 4 * cc + plit
/-- The bound on the running time of the decomposition step. -/
def Tbx (ca cc : ℕ) (x : List ℕ) : ℕ := ca * 2 ^ (ca * wx cc x ^ 3) * (nx x * nx x + 3) ^ ca
/-- The number of restrictions of the dynamic program. -/
def tabsx (cc : ℕ) (x : List ℕ) : ℕ := (2 ^ mx x) ^ (wx cc x + 1)
/-- The size of a word. -/
def Aw (x : List ℕ) : ℕ := x.length + Mx x + 1
/-- The size of a word for time. -/
def Lp (x : List ℕ) : ℕ := x.length + 1
/-- The words of the domain. -/
def Dm (x : List ℕ) : Prop := x ∈ UniformInstances

theorem Aw_pos (x : List ℕ) : 1 ≤ Aw x := by unfold Aw; omega
theorem Lp_pos (x : List ℕ) : 1 ≤ Lp x := by unfold Lp; omega
theorem Lp_le_Aw (x : List ℕ) : Lp x ≤ Aw x := by unfold Lp Aw; omega

variable {ca cc plit : ℕ} {x : List ℕ}

theorem Dm.len (hx : Dm x) : ∃ I k, EncodesUniform x I k ∧ x.length = 3 + 2 * (I.days * I.clients) ∧
    nx x = I.clients ∧ mx x = I.days := by
  obtain ⟨I, k, hdec⟩ := hx
  exact ⟨I, k, hdec, ClientsWord.len_eq hdec, ClientsWord.x0 hdec, ClientsWord.x1 hdec⟩

theorem Dm.three (hx : Dm x) : 3 ≤ x.length := by
  obtain ⟨I, k, -, h, -⟩ := hx.len; omega

theorem Dm.nMx (hx : Dm x) : nx x ≤ Mx x ∧ mx x ≤ Mx x := by
  obtain ⟨I, k, hdec, -⟩ := hx.len
  exact ⟨mem_x hdec 0, mem_x hdec 1⟩

theorem Dm.gd (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hx : Dm x) (hg : gdx cc x) :
    Gd ca cc x.length (lgx x) (mx x) (wx cc x) := by
  have hL0 := hx.three
  refine ⟨hca, hcc, hL0, Nat.pow_log_le_self 2 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _,
    ?_⟩
  have := (TwPrep.wcnt_spec (cc := cc) (by omega) (mx x) (lgx x)).2.1 (wcx cc x - 1)
    (by have := hg.1; unfold wcx at this ⊢; omega)
  exact this

theorem Dm.nL (hx : Dm x) (hg : 0 < mx x) : nx x ≤ x.length := by
  obtain ⟨I, k, hdec, h, hn, hm⟩ := hx.len
  have : I.clients ≤ I.days * I.clients := Nat.le_mul_of_pos_left _ (by omega)
  omega

end Lax117284Proofs.Machine.TwNum
