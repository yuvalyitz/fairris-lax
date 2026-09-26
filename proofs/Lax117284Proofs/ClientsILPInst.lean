import Lax117284Proofs.ClientsILPEnc
import Lax117284Proofs.Bridge
import Lax117284Proofs.Theorem4ILP
import Lax117284Proofs.Injectivity

/-!
The integer program of the numbered instance: the numbers `typeNum`, the counts `cntN`, and the
equivalence of the program's feasibility with the existence of a `k`-fair schedule.
-/

namespace Lax117284Proofs.ClientsILP

open Finset Lax117284.Scheduling

/-- Whether clients `a` and `b` conflict on day `i`, read off the numbers. -/
def confB (I : Instance) (i a b : ℕ) : Bool := decide (I.ConflictAt i a b)

/-- The number of the type of day `i`. -/
def typeNum (I : Instance) (i : ℕ) : ℕ :=
  bitsNum (fun q => confB I i (q / I.clients) (q % I.clients)) (I.clients * I.clients)

/-- The number of days of type `t`. -/
def cntN (I : Instance) (t : ℕ) : ℕ := ((range I.days).filter fun i => typeNum I i = t).card

variable (I : Instance)

theorem typeNum_lt (i : ℕ) : typeNum I i < nT I.clients := bitsNum_lt _ _

/-- The type of day `i` (its conflict relation), on `Fin n`. -/
def dtype (i : Fin I.days) : Fin I.clients → Fin I.clients → Bool :=
  fun a b => Model.Instance.dayType (Bridge.model I) i a b

theorem dtype_eq (i : Fin I.days) (a b : Fin I.clients) : dtype I i a b = confB I i a b := by
  simp only [dtype, Model.Instance.dayType, confB]
  refine decide_eq_decide.mpr ?_
  rw [I.conflictAt_iff i a b, Bridge.conflict_iff]

theorem typeNum_eq (i : Fin I.days) : typeNum I i = numOf I.clients (dtype I i) := by
  refine bitsNum_congr fun q hq => ?_
  simp only [tyBits, dif_pos hq]
  rw [dtype_eq]

theorem typeNum_iff (i : Fin I.days) {r : ℕ} (hr : r < nT I.clients) :
    typeNum I i = r ↔ dtype I i = tyOf I.clients r := by
  rw [typeNum_eq]
  constructor
  · intro h
    have := tyOf_numOf I.clients (dtype I i)
    rw [h] at this
    exact this.symm
  · intro h
    rw [h, numOf_tyOf _ hr]

theorem cntN_eq {r : ℕ} (hr : r < nT I.clients) :
    cntN I r = (Finset.univ.filter fun i : Fin I.days => dtype I i = tyOf I.clients r).card := by
  simp only [cntN, Finset.card_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun i => if typeNum I i = r then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [typeNum_iff I i hr]

theorem sum_cntN : ∑ r ∈ range (nT I.clients), cntN I r = I.days := by
  simp only [cntN]
  rw [← Finset.card_eq_sum_card_fiberwise (f := typeNum I) (t := range (nT I.clients))
    (fun i _ => Finset.mem_range.mpr (typeNum_lt I i))]
  simp

end Lax117284Proofs.ClientsILP
