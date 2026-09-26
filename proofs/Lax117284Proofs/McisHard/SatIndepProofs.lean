import Lax117284Proofs.McisHard.Defs

/-!
# WP4: the occurrence graph and satisfiability (`sat_iff_indep`)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284.MulticolouredIndepSet Lax434930.PolynomialTime
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284.BoundedSat
open Lax117284Proofs.McisHard

section
variable (ns : List ℕ)

/-- The position `o` carries a literal that holds under the assignment `ā` (on numbers). -/
def TrueAt (ā : ℕ → Bool) (o : ℕ) : Prop := ā (litV ns o) = decide (litS ns o ≠ 0)

theorem clId_lt (o : ℕ) (ho : o < SlotsN ns) : clId ns o < ns.getD 1 0 + ns.getD 2 0 := by
  unfold clId SlotsN at *
  split_ifs <;> omega

theorem clId_lt_two {o : ℕ} (h : clId ns o < ns.getD 1 0) : o < 2 * ns.getD 1 0 := by
  unfold clId at h
  split_ifs at h with h1
  · exact h1
  · omega

theorem clId_ge_two {o : ℕ} (h : ns.getD 1 0 ≤ clId ns o) : 2 * ns.getD 1 0 ≤ o := by
  unfold clId at h
  split_ifs at h with h1
  · omega
  · omega

/-- Satisfiability, in terms of positions and assignments on numbers. -/
theorem sat_iff_true (hs : ShapeF ns) (hc : CondN ns) :
    (formulaOf ns hc hs).Satisfiable ↔
      ∃ ā : ℕ → Bool, ∀ c < ns.getD 1 0 + ns.getD 2 0,
        ∃ o < SlotsN ns, clId ns o = c ∧ TrueAt ns ā o := by
  constructor
  · rintro ⟨a, ha1, ha2⟩
    refine ⟨fun x => if h : x < ns.getD 0 0 then a ⟨x, h⟩ else false, fun c hc' => ?_⟩
    by_cases hcA : c < ns.getD 1 0
    · obtain ⟨α, hα⟩ := ha1 ⟨c, hcA⟩
      have hα2 := α.isLt
      have hlt : 2 * c + (α : ℕ) < SlotsN ns := by unfold SlotsN; omega
      refine ⟨2 * c + α, hlt, ?_, ?_⟩
      · unfold clId; rw [if_pos (by omega)]; omega
      · have hp := pos_lt ns hc hlt
        show (if h : ns.getD (3 + 2 * (2 * c + (α : ℕ))) 0 < ns.getD 0 0 then
          a ⟨_, h⟩ else false) = decide (ns.getD (4 + 2 * (2 * c + (α : ℕ))) 0 ≠ 0)
        rw [dif_pos hp]
        exact hα
    · obtain ⟨c', rfl⟩ : ∃ c', c = ns.getD 1 0 + c' := ⟨c - ns.getD 1 0, by omega⟩
      have hc'B : c' < ns.getD 2 0 := by omega
      obtain ⟨α, hα⟩ := ha2 ⟨c', hc'B⟩
      have hα2 := α.isLt
      have hlt : 2 * ns.getD 1 0 + 3 * c' + (α : ℕ) < SlotsN ns := by unfold SlotsN; omega
      refine ⟨2 * ns.getD 1 0 + 3 * c' + α, hlt, ?_, ?_⟩
      · unfold clId; rw [if_neg (by omega)]; omega
      · have hp := pos_lt ns hc hlt
        show (if h : ns.getD (3 + 2 * (2 * ns.getD 1 0 + 3 * c' + (α : ℕ))) 0 < ns.getD 0 0 then
          a ⟨_, h⟩ else false) = decide (ns.getD (4 + 2 * (2 * ns.getD 1 0 + 3 * c' + (α : ℕ))) 0 ≠ 0)
        rw [dif_pos hp]
        exact hα
  · rintro ⟨ā, H⟩
    refine ⟨fun x => ā x.val, fun c => ?_, fun c => ?_⟩
    · have hcA : (c : ℕ) < ns.getD 1 0 := c.isLt
      obtain ⟨o, ho, hco, hT⟩ := H c (by omega)
      have h2 := clId_lt_two ns (o := o) (by omega)
      have e : 2 * (c : ℕ) + o % 2 = o := by
        unfold clId at hco; rw [if_pos h2] at hco; omega
      refine ⟨⟨o % 2, by omega⟩, ?_⟩
      show ā (ns.getD (3 + 2 * (2 * (c : ℕ) + o % 2)) 0) =
        decide (ns.getD (4 + 2 * (2 * (c : ℕ) + o % 2)) 0 ≠ 0)
      rw [e]; exact hT
    · have hcB : (c : ℕ) < ns.getD 2 0 := c.isLt
      obtain ⟨o, ho, hco, hT⟩ := H (ns.getD 1 0 + c) (by omega)
      have h2 := clId_ge_two ns (o := o) (by omega)
      have e : 2 * ns.getD 1 0 + 3 * (c : ℕ) + (o - 2 * ns.getD 1 0) % 3 = o := by
        unfold clId at hco; rw [if_neg (by omega)] at hco; omega
      refine ⟨⟨(o - 2 * ns.getD 1 0) % 3, by omega⟩, ?_⟩
      show ā (ns.getD (3 + 2 * (2 * ns.getD 1 0 + 3 * (c : ℕ) + (o - 2 * ns.getD 1 0) % 3)) 0) =
        decide (ns.getD (4 + 2 * (2 * ns.getD 1 0 + 3 * (c : ℕ) +
          (o - 2 * ns.getD 1 0) % 3)) 0 ≠ 0)
      rw [e]; exact hT

theorem occ_adj_iff (o o' : Fin (SlotsN ns)) :
    (occGraphN ns).Adj o o' ↔
      o ≠ o' ∧ ((clId ns o.val = clId ns o'.val ∨ compN ns o.val o'.val) ∨
        (clId ns o'.val = clId ns o.val ∨ compN ns o'.val o.val)) := by
  unfold occGraphN
  rw [SimpleGraph.fromRel_adj]

theorem trueAt_eq (hs : ShapeF ns) {ā : ℕ → Bool} {o o' : ℕ} (ho : o < SlotsN ns)
    (ho' : o' < SlotsN ns) (hv : litV ns o = litV ns o') (h : TrueAt ns ā o)
    (h' : TrueAt ns ā o') : litS ns o = litS ns o' := by
  have h1 := hs.2.2 o ho
  have h2 := hs.2.2 o' ho'
  unfold TrueAt at h h'
  rw [hv] at h
  rw [h] at h'
  unfold litS at *
  generalize ns.getD (4 + 2 * o) 0 = x at *
  generalize ns.getD (4 + 2 * o') 0 = y at *
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all <;> omega

theorem sat_iff_indep (hs : ShapeF ns) (hc : CondN ns) :
    (formulaOf ns hc hs).Satisfiable ↔
      ∃ s : Finset (Fin (SlotsN ns)), (occGraphN ns).IsIndepSet (s : Set (Fin (SlotsN ns))) ∧
        ns.getD 1 0 + ns.getD 2 0 ≤ s.card := by
  classical
  rw [sat_iff_true ns hs hc]
  set p := ns.getD 1 0 + ns.getD 2 0 with hp
  constructor
  · rintro ⟨ā, H⟩
    choose! g hgS hgc hgT using H
    let s : Finset (Fin (SlotsN ns)) := Finset.univ.filter fun o => ∃ c < p, g c = o.val
    refine ⟨s, ?_, ?_⟩
    · intro o ho o' ho' hne hadj
      simp only [s, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ho ho'
      obtain ⟨c, hc1, hc2⟩ := ho
      obtain ⟨c', hc1', hc2'⟩ := ho'
      rw [occ_adj_iff] at hadj
      have hne' : o.val ≠ o'.val := fun e => hne (Fin.ext e)
      have hcc : c ≠ c' := by
        rintro rfl; exact hne' (hc2.symm.trans hc2')
      have hT := hgT c hc1
      have hT' := hgT c' hc1'
      rw [hc2] at hT; rw [hc2'] at hT'
      have hcl := hgc c hc1
      have hcl' := hgc c' hc1'
      rw [hc2] at hcl; rw [hc2'] at hcl'
      have hcomp : ∀ x y : Fin (SlotsN ns), TrueAt ns ā x.val → TrueAt ns ā y.val →
          ¬ compN ns x.val y.val := by
        intro x y hx hy hcmp
        exact hcmp.2 (trueAt_eq ns hs x.isLt y.isLt hcmp.1 hx hy)
      rcases hadj.2 with (h | h) | (h | h)
      · exact hcc (by rw [← hcl, ← hcl', h])
      · exact hcomp o o' hT hT' h
      · exact hcc (by rw [← hcl, ← hcl', h])
      · exact hcomp o' o hT' hT h
    · have hsub : Finset.range p ⊆ s.image (fun o => clId ns o.val) := by
        intro c hc'
        rw [Finset.mem_range] at hc'
        rw [Finset.mem_image]
        have hlt := hgS c hc'
        refine ⟨⟨g c, hlt⟩, ?_, hgc c hc'⟩
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨c, hc', rfl⟩
      calc p = (Finset.range p).card := (Finset.card_range p).symm
        _ ≤ (s.image (fun o => clId ns o.val)).card := Finset.card_le_card hsub
        _ ≤ s.card := Finset.card_image_le
  · rintro ⟨s, hind, hcard⟩
    have hinj : Set.InjOn (fun o : Fin (SlotsN ns) => clId ns o.val) (s : Set _) := by
      intro o ho o' ho' h
      by_contra hne
      exact hind ho ho' hne (by
        rw [occ_adj_iff]
        exact ⟨hne, Or.inl (Or.inl h)⟩)
    have himg : s.image (fun o => clId ns o.val) = Finset.range p := by
      apply Finset.eq_of_subset_of_card_le
      · intro c hc'
        rw [Finset.mem_image] at hc'
        obtain ⟨o, -, rfl⟩ := hc'
        rw [Finset.mem_range]
        exact clId_lt ns o.val o.isLt
      · rw [Finset.card_image_of_injOn hinj, Finset.card_range]; exact hcard
    refine ⟨fun x => decide (∃ o ∈ s, litV ns o.val = x ∧ litS ns o.val ≠ 0), fun c hc' => ?_⟩
    have hcm : c ∈ s.image (fun o => clId ns o.val) := by rw [himg]; exact Finset.mem_range.2 hc'
    obtain ⟨o, hos, hoc⟩ := Finset.mem_image.1 hcm
    refine ⟨o.val, o.isLt, hoc, ?_⟩
    unfold TrueAt
    by_cases hb : litS ns o.val ≠ 0
    · rw [decide_eq_true_iff.2 hb, decide_eq_true_iff]
      exact ⟨o, hos, rfl, hb⟩
    · rw [decide_eq_false hb, decide_eq_false_iff_not]
      rintro ⟨o', ho's, hv, hb'⟩
      have hne : o ≠ o' := by
        rintro rfl; exact hb' (by simpa using hb)
      refine hind hos ho's hne ?_
      rw [occ_adj_iff]
      refine ⟨hne, Or.inl (Or.inr ⟨hv.symm, ?_⟩)⟩
      intro e; apply hb'; unfold litS at *; simp only [not_not] at hb; omega
end

end Lax117284Proofs.McisHard.Proved
