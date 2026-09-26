import Lax117284Proofs.Machine.TwNum6

/-!
The cost of the dynamic program as a function of the sizes of its tables, and its polynomial
bound.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284Proofs.Machine.TwNode (Params vcost dpCost)

/-- **The cost of the dynamic program** for `N` nodes, `m` days, bags of `wid` clients and `tabs`
restrictions. -/
def dpCostN (N m wid tabs : ℕ) : ℕ :=
  (((60 + ((34 * wid + 130) + ((20 + 20 + 4) * wid + 6) + 100 +
        ((vcost m wid + 60 + 20 + 4) * tabs + 6)) +
      ((34 * wid + 130) + ((20 + 20 + 4) * wid + 6) + 100 +
        ((44 * 2 ^ m + 130 + 20 + 4) * tabs + 6)) +
      (100 + ((10 + 20 + 4) * wid + 6) + 100 + ((30 + 20 + 4) * tabs + 6))) + 10 + 4) * N + 6) +
    (60 + ((20 + 10 + 4) * tabs + 6) + 10)

theorem dpCost_eq (P : Params) : dpCost P = dpCostN P.N P.m P.wid P.tabs := rfl

theorem dpCostN_mono {N N' : ℕ} (h : N ≤ N') (m wid tabs : ℕ) :
    dpCostN N m wid tabs ≤ dpCostN N' m wid tabs := by
  unfold dpCostN; gcongr

variable {P : List ℕ → Prop} {ca cc plit : ℕ}

theorem plon_dpCostN (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x)) := by
  have hm := atom_m (ca := ca) (cc := cc) hca hcc
  have hw := atom_w (ca := ca) (cc := cc) hca hcc
  have hpm := atom_pm (ca := ca) (cc := cc) hca hcc
  have htb := atom_Tb (ca := ca) (cc := cc) hca hcc
  have hta := atom_tabs (ca := ca) (cc := cc) hca hcc
  show PlOn Lp (fun x => Dm x ∧ gdx cc x)
    (fun x => dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x))
  unfold dpCostN vcost
  repeat' first | exact hm | exact hw | exact hpm | exact htb | exact hta |
    exact PlOn.const _ | apply PlOn.addL | apply PlOn.mul

end Lax117284Proofs.Machine.TwNum
