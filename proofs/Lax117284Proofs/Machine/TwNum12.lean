import Lax117284Proofs.Machine.TwNum11

/-!
The main program solves the problem: on every word of the domain it runs, within the bound `Bx` on
its values and the cost `Kx`, to an output that is the answer.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)
open Lax117284Proofs.Machine.TwMain (W)
open Lax117284Proofs.Machine.TwNode (Params)

/-- What the program answers: `1` for a word whose instance block has a `k`-fair schedule. -/
noncomputable def fAnsT (x : List ℕ) : List ℕ :=
  open Classical in if (decode x.dropLast).HasKFairSchedule (parameter x) then [1] else [0]

theorem fAnsT_eq {x : List ℕ} {I : Instance} {k : ℕ} (h : EncodesUniform x I k) :
    fAnsT x = open Classical in if I.HasKFairSchedule k then [1] else [0] := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  have h2 : parameter (y ++ [k]) = k := by simp [parameter]
  unfold fAnsT
  rw [h1, h2, Lax117284Proofs.Injectivity.decode_eq hy]

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem dpCost_le {I : Instance} {y0 : List ℕ} {k : ℕ} {D : List ℕ} {w : ℕ} (hwe : w = wx cc x)
    (hy : EncodesInstance y0 I) (hD : NiceDecomposition I w D) (hm : mx x = I.days)
    (hN : nodeCount D ≤ Tbx ca cc x) :
    60 + TwNode.dpCost ⟨I, y0, k, D, w, hy, hD⟩ ≤ Kdp ca cc x := by
  subst hwe
  have e1 : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).tabs = tabsx cc x := by
    simp [Params.tabs, Params.bs, Params.wid, Params.m, tabsx, hm]
  have e2 : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).m = mx x := hm.symm
  rw [dpCost_eq, e1, e2]
  unfold Kdp
  exact Nat.add_le_add_left (dpCostN_mono hN _ _ _) 60

open Classical in
theorem Kmain_le {I : Instance} {z : List ℕ} {t : ℕ} (hI : Ix x = I) (hn : nx x = I.clients)
    (hm : mx x = I.days)
    (hgiff : (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) ↔ gdx cc x)
    (ht : t ≤ Tbx ca cc x)
    (hz : gdx cc x → z = [0] →
      ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)) :
    TwMain.Kmain x.length (Nat.log 2 x.length) I.days I.clients t prog.length (Kdp ca cc x)
      (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) (z = [0]) ≤
      Kx prog ca cc x := by
  have hK : TwMain.Kgi I.days I.clients t prog.length ≤ TwMain.Kgi I.days I.clients (Tbx ca cc x)
      prog.length := by unfold TwMain.Kgi; omega
  unfold TwMain.Kmain Kx
  rw [hI]
  simp only [hn, hm, lgx]
  by_cases hg : gdx cc x
  · simp only [if_pos (hgiff.2 hg), if_pos hg]
    by_cases hz0 : z = [0]
    · have := hz hg hz0
      simp only [if_pos hz0, if_neg this]
      omega
    · simp only [if_neg hz0]
      split_ifs <;> omega
  · simp only [if_neg (fun h => hg (hgiff.1 h)), if_neg hg]
    omega

end Lax117284Proofs.Machine.TwNum
