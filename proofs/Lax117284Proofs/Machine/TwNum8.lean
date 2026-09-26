import Lax117284Proofs.Machine.TwNum7
import Lax117284Proofs.Machine.TwTW
import Lax117284Proofs.Injectivity
import Lax117284Proofs.Machine.ClBruteFinal

/-!
The cost of the main program on a word, and its bound: a polynomial in the length, plus the cost of
the enumeration, which is only paid on a word whose length is bounded by a function of the days and
the treewidth.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284Proofs.Machine.TwMain (Kprep Kgi)

/-- The instance a word declares. -/
noncomputable def Ix (x : List ℕ) : Instance := decode x.dropLast

theorem Ix_eq {x : List ℕ} {I : Instance} {k : ℕ} (h : EncodesUniform x I k) : Ix x = I := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  unfold Ix
  rw [h1]
  exact Lax117284Proofs.Injectivity.decode_eq hy

/-- The bound on the number of instructions the program takes on a word. -/
noncomputable def Kdp (ca cc : ℕ) (x : List ℕ) : ℕ :=
  60 + dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x)

open Classical in
/-- **The cost of the main program on a word.** -/
noncomputable def Kx (prog : Program) (ca cc : ℕ) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    (if gdx cc x then
      Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + (Kdp ca cc x +
        (if Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x) then 0
          else Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3)))
    else 4 + (if 0 < mx x then Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3 else 12))))

open Classical in
/-- The polynomial part of the cost. -/
noncomputable def KP (prog : Program) (ca cc : ℕ) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    ((if gdx cc x then Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) +
      16)))

open Classical in
/-- The part of the cost that is the enumeration. -/
noncomputable def KB (cc : ℕ) (x : List ℕ) : ℕ :=
  if gdx cc x then
    (if Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x) then 0
      else Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3)
  else (if 0 < mx x then Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3 else 0)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem Kx_le : Kx prog ca cc x ≤ KP prog ca cc x + KB cc x := by
  classical
  unfold Kx KP KB
  by_cases hg : gdx cc x
  · simp only [if_pos hg]
    by_cases ht : Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x)
    · simp only [if_pos ht]; omega
    · simp only [if_neg ht]; omega
  · simp only [if_neg hg]
    by_cases hm : 0 < mx x
    · simp only [if_pos hm]; omega
    · simp only [if_neg hm]; omega

theorem plon_KP (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) : PlOn Lp Dm (KP prog ca cc) := by
  classical
  have hlen : PlOn Lp Dm (fun x => x.length) := atom_len
  have hlg : PlOn Lp Dm lgx := atom_lg
  have hK : PlOn Lp Dm (fun x => Kprep x.length (lgx x)) := by
    show PlOn Lp Dm (fun x => 40 + ((20 + 10 + 4) * x.length + 6) + 20 +
      ((40 + 10 + 4) * (lgx x + 1) + 6) + 100)
    repeat' first | exact hlen | exact hlg | exact PlOn.const _ | apply PlOn.addL | apply PlOn.mul
  have hm := atom_m (ca := ca) (cc := cc) hca hcc
  have hn := atom_n (ca := ca) (cc := cc) hca hcc
  have htb := atom_Tb (ca := ca) (cc := cc) hca hcc
  have hg : PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x)) := by
    have hgi : PlOn Lp (fun x => Dm x ∧ gdx cc x)
        (fun x => Kgi (mx x) (nx x) (Tbx ca cc x) prog.length) := by
      show PlOn Lp (fun x => Dm x ∧ gdx cc x) (fun x => 30 + ((214 * mx x + 90 + 20 + 4) *
        (nx x * nx x) + 6 + 60) + (13 * prog.length + 1 + 30 + 250 * (Tbx ca cc x + 1)))
      repeat' first | exact hm | exact hn | exact htb | exact PlOn.const _ | apply PlOn.addL |
        apply PlOn.mul
    have hdp : PlOn Lp (fun x => Dm x ∧ gdx cc x) (Kdp ca cc) := by
      show PlOn Lp (fun x => Dm x ∧ gdx cc x)
        (fun x => 60 + dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x))
      exact (PlOn.const 60).addL (plon_dpCostN hca hcc)
    exact hgi.addL ((PlOn.const 10).addL hdp)
  have hg' : PlOn Lp Dm (fun x => if gdx cc x then
      Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) :=
    PlOn.guard hg
  show PlOn Lp Dm (fun x => (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    ((if gdx cc x then Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) +
      16))))
  exact (((PlOn.const 24).mul hlen).addL (PlOn.const 60)).addL
    (hK.addL ((PlOn.const 10).addL (hg'.addL (PlOn.const 16))))

end Lax117284Proofs.Machine.TwNum
