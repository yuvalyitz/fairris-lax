import Lax117284Proofs.McisHard.CopyProofs
import Lax117284Proofs.McisHard.SatIndepProofs
import Lax117284Proofs.McisHard.FormulaPorts
import Lax117284Proofs.McisHard.PortsBasic
import Lax117284Proofs.McisHard.PortsRegular
import Lax117284Proofs.McisHard.PortsIndep

/-!
# WP4/WP5: `Hinst_hasIndepSet_iff`, `Hinst_normal`, `encodeInstance_Hfin`

Dependencies (proved in `FormulaPorts` and `Ports*`): `isPortRel_RN`, `portGraph_regular`,
`portGraph_indep_iff`, `portGraph_adj`, `posGraph_RN`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284.MulticolouredIndepSet Lax117284Proofs.Lemma14Graph
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284.BoundedSat
open Lax117284.Problems (encodeNat)
open Lax117284Proofs.McisHard

theorem Hinst_hasIndepSet_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    (Hinst ns).HasIndepSet ↔ (formulaOf ns hc hs).Satisfiable := by
  unfold Hinst
  rw [copyInst_hasIndepSet_iff, sat_iff_indep ns hs hc]
  have hR := isPortRel_RN ns hs hc
  rw [portGraph_indep_iff hR, posGraph_RN ns hs hc]

open Classical in
theorem Hinst_normal (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (h0 : SlotsN ns ≠ 0) :
    (Hinst ns).Normal := by
  have hR := isPortRel_RN ns hs hc
  unfold Hinst
  refine copyInst_normal (r := 5) _ _ (fun u => portGraph_regular hR u) ?_ ?_ ?_
  · omega
  · omega
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (by omega) _) _

/-! ### The word of the matrix -/

/-- The adjacency bit of a copy instance, read off the numbers. -/
theorem adjAt_copyInst (k n : ℕ) (G : SimpleGraph (Fin n)) (P : ℕ → ℕ → Prop)
    (hP : ∀ u v : Fin n, G.Adj u v ↔ P u.val v.val) {w w' : ℕ}
    (hw : w < (copyInst k G).vertices) (hw' : w' < (copyInst k G).vertices) :
    (copyInst k G).adjAt w w' = true ↔
      (w / n ≠ w' / n ∧ (w % n = w' % n ∨ P (w % n) (w' % n))) := by
  obtain ⟨v, rfl⟩ := exists_num (copyInst k G) hw
  obtain ⟨u, rfl⟩ := exists_num (copyInst k G) hw'
  rw [adjAt_num]
  have h1 := classOf_num (copyInst k G) v
  have h2 := indexOf_num (copyInst k G) v
  have h3 := classOf_num (copyInst k G) u
  have h4 := indexOf_num (copyInst k G) u
  simp only [Instance.classOf, Instance.indexOf] at h1 h2 h3 h4
  change num (copyInst k G) v / n = _ at h1
  change num (copyInst k G) v % n = _ at h2
  change num (copyInst k G) u / n = _ at h3
  change num (copyInst k G) u % n = _ at h4
  rw [h1, h2, h3, h4]
  show (v.1 ≠ u.1 ∧ (v.2 = u.2 ∨ G.Adj v.2 u.2)) ↔ _
  rw [hP v.2 u.2]
  simp only [ne_eq, Fin.val_eq_val]

open Classical in
theorem encode_copyInst (k n : ℕ) (G : SimpleGraph (Fin n)) (P : ℕ → ℕ → Prop)
    (hP : ∀ u v : Fin n, G.Adj u v ↔ P u.val v.val) :
    encodeInstance (copyInst k G) = encodeNat k ++ encodeNat n ++
      (List.range (k * n)).flatMap fun w => (List.range (k * n)).map fun w' =>
        decide (w / n ≠ w' / n ∧ (w % n = w' % n ∨ P (w % n) (w' % n))) := by
  classical
  unfold encodeInstance
  have hv : (copyInst k G).vertices = k * n := rfl
  rw [hv]
  refine congrArg _ (List.flatMap_congr fun w hw => List.map_congr_left fun w' hw' => ?_)
  rw [List.mem_range] at hw hw'
  have := adjAt_copyInst k n G P hP (w := w) (w' := w') hw hw'
  cases hb : (copyInst k G).adjAt w w'
  · rw [hb] at this
    symm
    rw [decide_eq_false_iff_not]
    intro h; exact Bool.noConfusion (this.2 h)
  · rw [hb] at this
    symm
    rw [decide_eq_true_iff]
    exact this.1 rfl

open Classical in
theorem encodeInstance_Hfin (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    encodeInstance (Hfin ns) =
      encodeNat (kOf ns) ++ encodeNat (nOf ns) ++
      (List.range (kOf ns * nOf ns)).flatMap fun w =>
        (List.range (kOf ns * nOf ns)).map fun w' => decide (adjF ns w w') := by
  unfold Hfin
  by_cases h0 : SlotsN ns = 0
  · rw [if_pos h0]
    have := encode_copyInst 2 4 (⊥ : SimpleGraph (Fin 4)) (fun _ _ => False)
      (fun u v => by simp)
    unfold H0
    rw [this]
    have hk : kOf ns = 2 := by unfold kOf; rw [if_pos h0]
    have hn : nOf ns = 4 := by unfold nOf; rw [if_pos h0]
    rw [hk, hn]
    congr 1
    refine List.flatMap_congr fun w hw => List.map_congr_left fun w' hw' => ?_
    apply decide_eq_decide.2
    unfold adjF; rw [hn]
    simp [h0]
  · rw [if_neg h0]
    have hR := isPortRel_RN ns hs hc
    have := encode_copyInst (ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns) (SlotsN ns * 36)
      (portGraph (RN ns) (SlotsN ns)) (portAdjN (RN ns)) (fun u v => portGraph_adj hR u v)
    unfold Hinst
    rw [this]
    have hk : kOf ns = ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns := by unfold kOf; rw [if_neg h0]
    have hn : nOf ns = SlotsN ns * 36 := by unfold nOf; rw [if_neg h0]
    rw [hk, hn]
    congr 1
    refine List.flatMap_congr fun w hw => List.map_congr_left fun w' hw' => ?_
    apply decide_eq_decide.2
    unfold adjF; rw [hn]
    simp [h0]

end Lax117284Proofs.McisHard.Proved
