import Lax117284Proofs.McisHard.PortsRegular
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases

/-!
# WP2 (ports), part 3: independent sets of `portGraph` versus `posGraph`
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284Proofs.McisHard

section
variable {S : ℕ} {R : ℕ → ℕ → ℕ → ℕ → Prop}

theorem pos_adj_of {o o' j j' : ℕ} (hR : R o j o' j') : portAdjN R (36 * o) (36 * o') := by
  unfold portAdjN
  refine Or.inl ⟨by omega, by omega, j, j', ?_⟩
  rw [show 36 * o / 36 = o by omega, show 36 * o' / 36 = o' by omega]
  exact hR

theorem slot_adj_of {x y : ℕ} (hx : x % 36 ≠ 0) (hy : y % 36 ≠ 0) (hxy : x / 36 = y / 36)
    (hj : (x % 36 - 1) / 7 = (y % 36 - 1) / 7) (hg : gadAdj ((x % 36 - 1) % 7) ((y % 36 - 1) % 7)) :
    portAdjN R x y :=
  Or.inr (Or.inr (Or.inr ⟨hx, hy, Or.inl ⟨hxy, hj, hg⟩⟩))

theorem gadAdj_irrefl (t : ℕ) : ¬ gadAdj t t := by unfold gadAdj; omega

theorem fibre_le_two (h : IsPortRel S R) (s : Finset (Fin (S * 36)))
    (hs : (portGraph R S).IsIndepSet (s : Set (Fin (S * 36)))) (b : ℕ) :
    ((s.filter (fun v => v.val % 36 ≠ 0)).filter
      (fun v => v.val / 36 * 5 + (v.val % 36 - 1) / 7 = b)).card ≤ 2 := by
  classical
  set F := (s.filter (fun v => v.val % 36 ≠ 0)).filter
      (fun v => v.val / 36 * 5 + (v.val % 36 - 1) / 7 = b) with hF
  have hmem : ∀ x ∈ F, x ∈ s ∧ x.val % 36 ≠ 0 ∧ x.val / 36 * 5 + (x.val % 36 - 1) / 7 = b := by
    intro x hx
    simp only [hF, Finset.mem_filter] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  let g : Fin (S * 36) → ℕ := fun x => (x.val % 36 - 1) % 7
  have hsame : ∀ x ∈ F, ∀ y ∈ F, x.val / 36 = y.val / 36 ∧
      (x.val % 36 - 1) / 7 = (y.val % 36 - 1) / 7 := by
    intro x hx y hy
    obtain ⟨-, hx1, hx2⟩ := hmem x hx
    obtain ⟨-, hy1, hy2⟩ := hmem y hy
    omega
  have hinj : Set.InjOn g F := by
    intro x hx y hy hxy
    obtain ⟨-, hx1, -⟩ := hmem x hx
    obtain ⟨-, hy1, -⟩ := hmem y hy
    have := hsame x hx y hy
    simp only [g] at hxy
    exact Fin.ext (by omega)
  have hsub : F.image g ⊆ Finset.range 7 := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨x, -, rfl⟩ := ht
    simp only [g, Finset.mem_range]
    omega
  have hind : ∀ a ∈ F.image g, ∀ c ∈ F.image g, ¬ gadAdj a c := by
    intro a ha c hc
    simp only [Finset.mem_image] at ha hc
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hc
    intro hg
    by_cases hxy : x = y
    · subst hxy
      exact gadAdj_irrefl _ hg
    · obtain ⟨hxs, hx1, -⟩ := hmem x hx
      obtain ⟨hys, hy1, -⟩ := hmem y hy
      have hsm := hsame x hx y hy
      refine hs (Finset.mem_coe.2 hxs) (Finset.mem_coe.2 hys) hxy ?_
      rw [portGraph_adj h]
      exact slot_adj_of hx1 hy1 hsm.1 hsm.2 hg
  have h2 := gad_alpha _ hsub hind
  rwa [Finset.card_image_of_injOn hinj] at h2

theorem slot_part_le (h : IsPortRel S R) (s : Finset (Fin (S * 36)))
    (hs : (portGraph R S).IsIndepSet (s : Set (Fin (S * 36)))) :
    (s.filter (fun v => v.val % 36 ≠ 0)).card ≤ 10 * S := by
  classical
  have hmaps : ∀ v ∈ s.filter (fun v => v.val % 36 ≠ 0),
      (fun v : Fin (S * 36) => v.val / 36 * 5 + (v.val % 36 - 1) / 7) v ∈ Finset.range (5 * S) := by
    intro v hv
    have := v.isLt
    simp only [Finset.mem_range]
    omega
  have := Finset.card_le_mul_card_image_of_maps_to hmaps 2 (fun b _ => fibre_le_two h s hs b)
  simp only [Finset.card_range] at this
  omega

theorem pos_part_le (h : IsPortRel S R) (s : Finset (Fin (S * 36)))
    (hs : (portGraph R S).IsIndepSet (s : Set (Fin (S * 36)))) :
    ∃ P : Finset (Fin S), (posGraph R S).IsIndepSet (P : Set (Fin S)) ∧
      (s.filter (fun v => v.val % 36 = 0)).card ≤ P.card := by
  classical
  refine ⟨Finset.univ.filter (fun o : Fin S => ∃ v ∈ s, v.val = 36 * o.val), ?_, ?_⟩
  · intro a ha b hb hne hadj
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    replace ha := ha.2
    replace hb := hb.2
    obtain ⟨v, hv, hva⟩ := ha
    obtain ⟨w, hw, hwb⟩ := hb
    have hvw : v ≠ w := by
      intro e
      apply hne
      apply Fin.ext
      have := congrArg Fin.val e
      omega
    unfold posGraph at hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    obtain ⟨-, ⟨j, j', hR⟩ | ⟨j, j', hR⟩⟩ := hadj
    · refine hs (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hw) hvw ?_
      rw [portGraph_adj h, hva, hwb]
      exact pos_adj_of hR
    · refine hs (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hw) hvw ?_
      rw [portGraph_adj h, hva, hwb]
      exact portAdjN_symm h (pos_adj_of hR)
  · refine Finset.card_le_card_of_injOn (fun v => (⟨v.val / 36, by have := v.isLt; omega⟩ : Fin S))
      ?_ ?_
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, v, hv.1, by show v.val = 36 * (v.val / 36); omega⟩
    · intro v hv w hw hvw
      rw [Finset.mem_coe, Finset.mem_filter] at hv hw
      have := congrArg Fin.val hvw
      simp only at this
      exact Fin.ext (by omega)

theorem indep_of_port (h : IsPortRel S R) (q : ℕ) (s : Finset (Fin (S * 36)))
    (hs : (portGraph R S).IsIndepSet (s : Set (Fin (S * 36)))) (hq : q + 10 * S ≤ s.card) :
    ∃ s' : Finset (Fin S), (posGraph R S).IsIndepSet (s' : Set (Fin S)) ∧ q ≤ s'.card := by
  classical
  obtain ⟨P, hP, hle⟩ := pos_part_le h s hs
  have h1 := slot_part_le h s hs
  simp only [ne_eq] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun v : Fin (S * 36) => v.val % 36 = 0)
  exact ⟨P, hP, by omega⟩

theorem pos_pos_adj {o o' : ℕ} (hadj : portAdjN R (36 * o) (36 * o')) : ∃ j j', R o j o' j' := by
  rw [pos_nbr_iff] at hadj
  rcases hadj with ⟨-, j, j', hR⟩ | ⟨h1, -⟩
  · exact ⟨j, j', by rwa [show 36 * o' / 36 = o' by omega] at hR⟩
  · omega

theorem not_pos_slot {o o' j e : ℕ} (hj : j < 5) (he : e < 2) :
    ¬ portAdjN R (36 * o) (36 * o' + 1 + 7 * j + (3 + e)) := by
  rw [pos_nbr_iff]
  obtain ⟨d1, d2, d3, d4⟩ := slot_decode (o := o') hj (show 3 + e < 7 by omega)
  rw [d1, d3, d4, d2]
  omega

theorem not_slot_pos {o o' j e : ℕ} (hj : j < 5) (he : e < 2) :
    ¬ portAdjN R (36 * o' + 1 + 7 * j + (3 + e)) (36 * o) := by
  rw [slot_nbr_iff hj (show 3 + e < 7 by omega)]
  omega

theorem not_slot_slot {o o' j j' e e' : ℕ} (hj : j < 5) (hj' : j' < 5) (he : e < 2)
    (he' : e' < 2) :
    ¬ portAdjN R (36 * o + 1 + 7 * j + (3 + e)) (36 * o' + 1 + 7 * j' + (3 + e')) := by
  rw [slot_nbr_iff hj (show 3 + e < 7 by omega)]
  obtain ⟨d1, d2, d3, d4⟩ := slot_decode (o := o') hj' (show 3 + e' < 7 by omega)
  rw [d1, d3, d4, d2]
  unfold gadAdj
  omega

theorem pos_ne_slot {a b j e : ℕ} (hj : j < 5) (he : e < 2) :
    36 * a ≠ 36 * b + 1 + 7 * j + (3 + e) := by
  interval_cases j <;> interval_cases e <;> omega

def posV (o : Fin S) : Fin (S * 36) := ⟨36 * o.val, by have := o.isLt; omega⟩

def slotV (p : Fin S × Fin 5 × Fin 2) : Fin (S * 36) :=
  ⟨36 * p.1.val + 1 + 7 * p.2.1.val + (3 + p.2.2.val), by
    have := p.1.isLt; have := p.2.1.isLt; have := p.2.2.isLt; omega⟩

def phiV : Fin S ⊕ (Fin S × Fin 5 × Fin 2) → Fin (S * 36) := Sum.elim posV slotV

theorem phiV_inj : Function.Injective (phiV (S := S)) := by
  intro x y hxy
  have h := congrArg Fin.val hxy
  rcases x with o | ⟨o, j, e⟩ <;> rcases y with o' | ⟨o', j', e'⟩
  · simp only [phiV, Sum.elim_inl, posV] at h
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have := o'.isLt; have := j'.isLt; have := e'.isLt
    simp only [phiV, Sum.elim_inl, Sum.elim_inr, posV, slotV] at h
    exact absurd h (pos_ne_slot (by omega) (by omega))
  · have := o.isLt; have := j.isLt; have := e.isLt
    simp only [phiV, Sum.elim_inl, Sum.elim_inr, posV, slotV] at h
    exact absurd h.symm (pos_ne_slot (by omega) (by omega))
  · have := j.isLt; have := j'.isLt; have := e.isLt; have := e'.isLt
    simp only [phiV, Sum.elim_inr, slotV] at h
    have e1 : o = o' := Fin.ext (by omega)
    have e2 : j = j' := Fin.ext (by omega)
    have e3 : e = e' := Fin.ext (by omega)
    subst e1 e2 e3
    rfl

theorem port_of_indep (h : IsPortRel S R) (q : ℕ) (s' : Finset (Fin S))
    (hs : (posGraph R S).IsIndepSet (s' : Set (Fin S))) (hq : q ≤ s'.card) :
    ∃ s : Finset (Fin (S * 36)), (portGraph R S).IsIndepSet (s : Set (Fin (S * 36))) ∧
        q + 10 * S ≤ s.card := by
  classical
  refine ⟨(s'.disjSum (Finset.univ : Finset (Fin S × Fin 5 × Fin 2))).map ⟨phiV, phiV_inj⟩, ?_, ?_⟩
  · intro a ha b hb hne hadj
    rw [Finset.mem_coe, Finset.mem_map] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    simp only [Function.Embedding.coeFn_mk] at hne hadj
    rw [portGraph_adj h] at hadj
    rcases x with o | ⟨o, j, e⟩ <;> rcases y with o' | ⟨o', j', e'⟩
    · simp only [phiV, Sum.elim_inl, posV] at hadj
      obtain ⟨j, j', hR⟩ := pos_pos_adj hadj
      have hne' : o ≠ o' := by
        rintro rfl
        exact hne rfl
      rw [Finset.mem_disjSum] at hx hy
      obtain ⟨o0, ho0, e0⟩ := hx.resolve_right (by simp)
      obtain ⟨o1, ho1, e1⟩ := hy.resolve_right (by simp)
      simp only [Sum.inl.injEq] at e0 e1
      subst e0 e1
      refine hs (Finset.mem_coe.2 ho0) (Finset.mem_coe.2 ho1) hne' ?_
      unfold posGraph
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hne', Or.inl ⟨j, j', hR⟩⟩
    · have := j'.isLt; have := e'.isLt
      simp only [phiV, Sum.elim_inl, Sum.elim_inr, posV, slotV] at hadj
      exact not_pos_slot (by omega) (by omega) hadj
    · have := j.isLt; have := e.isLt
      simp only [phiV, Sum.elim_inl, Sum.elim_inr, posV, slotV] at hadj
      exact not_slot_pos (by omega) (by omega) hadj
    · have := j.isLt; have := j'.isLt; have := e.isLt; have := e'.isLt
      simp only [phiV, Sum.elim_inr, slotV] at hadj
      exact not_slot_slot (by omega) (by omega) (by omega) (by omega) hadj
  · rw [Finset.card_map, Finset.card_disjSum]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    omega

theorem portGraph_indep_iff {R : ℕ → ℕ → ℕ → ℕ → Prop} {S : ℕ} (h : IsPortRel S R) (q : ℕ) :
    (∃ s : Finset (Fin (S * 36)), (portGraph R S).IsIndepSet (s : Set (Fin (S * 36))) ∧
        q + 10 * S ≤ s.card) ↔
      ∃ s : Finset (Fin S), (posGraph R S).IsIndepSet (s : Set (Fin S)) ∧ q ≤ s.card :=
  ⟨fun ⟨s, hs, hq⟩ => indep_of_port h q s hs hq, fun ⟨s', hs, hq⟩ => port_of_indep h q s' hs hq⟩

end

end Lax117284Proofs.McisHard.Proved
