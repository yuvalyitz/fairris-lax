import Lax117284Proofs.McisHard.PortsBasic

/-!
# WP2 (ports), part 2: `portGraph` is 5-regular
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284Proofs.McisHard

section
variable {S : ℕ} {R : ℕ → ℕ → ℕ → ℕ → Prop}

theorem pos_nbr_iff {o v : ℕ} :
    portAdjN R (36 * o) v ↔
      (v % 36 = 0 ∧ ∃ j j', R o j (v / 36) j') ∨
      (v % 36 ≠ 0 ∧ v / 36 = o ∧ (v % 36 - 1) % 7 = 0 ∧
        ¬ ∃ o' j', R o ((v % 36 - 1) / 7) o' j') := by
  have e1 : 36 * o % 36 = 0 := by omega
  have e2 : 36 * o / 36 = o := by omega
  unfold portAdjN
  simp only [e1, e2]
  constructor
  · rintro (⟨-, h2, h3⟩ | ⟨-, h2, h3, h4, h5⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl ⟨h2, h3⟩
    · exact Or.inr ⟨h2, h3.symm, h4, h5⟩
    · exact absurd rfl h1
    · exact absurd rfl h1
  · rintro (⟨h2, h3⟩ | ⟨h2, h3, h4, h5⟩)
    · exact Or.inl ⟨trivial, h2, h3⟩
    · exact Or.inr (Or.inl ⟨trivial, h2, h3.symm, h4, h5⟩)

theorem slot_nbr_iff {o j t v : ℕ} (hj : j < 5) (ht : t < 7) :
    portAdjN R (36 * o + 1 + 7 * j + t) v ↔
      (v % 36 ≠ 0 ∧ v / 36 = o ∧ (v % 36 - 1) / 7 = j ∧ gadAdj t ((v % 36 - 1) % 7)) ∨
      (t = 0 ∧ v = 36 * o ∧ ¬ ∃ o' j', R o j o' j') ∨
      (t = 0 ∧ v % 36 ≠ 0 ∧ (v % 36 - 1) % 7 = 0 ∧ R o j (v / 36) ((v % 36 - 1) / 7)) := by
  have e1 : (36 * o + 1 + 7 * j + t) / 36 = o := by omega
  have e2 : (36 * o + 1 + 7 * j + t) % 36 = 1 + 7 * j + t := by omega
  have e3 : (1 + 7 * j + t - 1) / 7 = j := by omega
  have e4 : (1 + 7 * j + t - 1) % 7 = t := by omega
  unfold portAdjN
  simp only [e1, e2, e3, e4]
  constructor
  · rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, h3, h4, h5⟩ | ⟨-, h2, h3⟩)
    · omega
    · omega
    · refine Or.inr (Or.inl ⟨h4, ?_, ?_⟩)
      · omega
      · rw [h3]; exact h5
    · rcases h3 with ⟨a, b, c⟩ | ⟨a, b, c⟩
      · exact Or.inl ⟨h2, a.symm, b.symm, c⟩
      · exact Or.inr (Or.inr ⟨a, h2, b, c⟩)
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h1, Or.inl ⟨h2.symm, h3.symm, h4⟩⟩))
    · have : v / 36 = o := by omega
      refine Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, h1, by rw [this]; exact h3⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, h2, Or.inr ⟨h1, h3, h4⟩⟩))

open Classical in
theorem pos_card (h : IsPortRel S R) {o : ℕ} (ho : o < S) :
    ((Finset.range (S * 36)).filter (portAdjN R (36 * o))).card = 5 := by
  let g : ℕ → ℕ := fun j =>
    if hj : ∃ o' j', R o j o' j' then 36 * Classical.choose hj else 36 * o + 1 + 7 * j
  have hg : (Finset.range (S * 36)).filter (portAdjN R (36 * o)) = (Finset.range 5).image g := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, pos_nbr_iff]
    constructor
    · rintro ⟨hv, ⟨h0, j, j', hR⟩ | ⟨h0, h1, h2, h3⟩⟩
      · refine ⟨j, (h.lt hR).2.2.1, ?_⟩
        have hj : ∃ o' j', R o j o' j' := ⟨_, _, hR⟩
        simp only [g, dif_pos hj]
        obtain ⟨j'', hR2⟩ := Classical.choose_spec hj
        have := (h.func hR hR2).1
        omega
      · refine ⟨(v % 36 - 1) / 7, by omega, ?_⟩
        simp only [g, dif_neg h3]
        omega
    · rintro ⟨j, hj, rfl⟩
      by_cases hm : ∃ o' j', R o j o' j'
      · simp only [g, dif_pos hm]
        obtain ⟨j', hR⟩ := Classical.choose_spec hm
        have hc := (h.lt hR).2.1
        refine ⟨by omega, Or.inl ⟨by omega, j, j', ?_⟩⟩
        rw [show 36 * Classical.choose hm / 36 = Classical.choose hm by omega]
        exact hR
      · simp only [g, dif_neg hm]
        have e0 : (36 * o + 1 + 7 * j) % 36 = 1 + 7 * j := by omega
        have e1 : (36 * o + 1 + 7 * j) / 36 = o := by omega
        have e : (36 * o + 1 + 7 * j) % 36 - 1 = 7 * j := by omega
        refine ⟨by omega, Or.inr ⟨by omega, e1, ?_, ?_⟩⟩
        · rw [e]; omega
        · rw [e, show 7 * j / 7 = j by omega]
          exact hm
  rw [hg, Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_cases ma : ∃ o' j', R o a o' j' <;> by_cases mb : ∃ o' j', R o b o' j'
    · simp only [g, dif_pos ma, dif_pos mb] at hab
      obtain ⟨a', hRa⟩ := Classical.choose_spec ma
      obtain ⟨b', hRb⟩ := Classical.choose_spec mb
      have : Classical.choose ma = Classical.choose mb := by omega
      rw [← this] at hRb
      exact h.simple hRa hRb
    · simp only [g, dif_pos ma, dif_neg mb] at hab
      omega
    · simp only [g, dif_neg ma, dif_pos mb] at hab
      omega
    · simp only [g, dif_neg ma, dif_neg mb] at hab
      omega

theorem slot_decode {o j t : ℕ} (hj : j < 5) (ht : t < 7) :
    (36 * o + 1 + 7 * j + t) / 36 = o ∧ (36 * o + 1 + 7 * j + t) % 36 = 1 + 7 * j + t ∧
    ((36 * o + 1 + 7 * j + t) % 36 - 1) / 7 = j ∧ ((36 * o + 1 + 7 * j + t) % 36 - 1) % 7 = t := by
  have e2 : (36 * o + 1 + 7 * j + t) % 36 = 1 + 7 * j + t := by omega
  rw [e2]
  refine ⟨by omega, rfl, by omega, by omega⟩

theorem slot_D_mem {o j t v : ℕ} (hj : j < 5) :
    v ∈ ((Finset.range 7).filter (gadAdj t)).image (fun t' => 36 * o + 1 + 7 * j + t') ↔
      (v % 36 ≠ 0 ∧ v / 36 = o ∧ (v % 36 - 1) / 7 = j ∧ gadAdj t ((v % 36 - 1) % 7)) := by
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨t', ⟨ht', hg⟩, rfl⟩
    obtain ⟨d1, d2, d3, d4⟩ := slot_decode (o := o) hj ht'
    rw [d1, d3, d4, d2]
    exact ⟨by omega, rfl, rfl, hg⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(v % 36 - 1) % 7, ⟨by omega, h4⟩, by omega⟩

open Classical in
theorem slot_card (h : IsPortRel S R) {o j t : ℕ} (ho : o < S) (hj : j < 5) (ht : t < 7) :
    ((Finset.range (S * 36)).filter (portAdjN R (36 * o + 1 + 7 * j + t))).card = 5 := by
  set D : Finset ℕ := ((Finset.range 7).filter (gadAdj t)).image
    (fun t' => 36 * o + 1 + 7 * j + t') with hD
  have hDcard : D.card = if t = 0 then 4 else 5 := by
    rw [hD, Finset.card_image_of_injective _ (by intro a b hab; simpa using hab)]
    exact gad_deg t ht
  have hDmem : ∀ v, v ∈ D ↔
      (v % 36 ≠ 0 ∧ v / 36 = o ∧ (v % 36 - 1) / 7 = j ∧ gadAdj t ((v % 36 - 1) % 7)) :=
    fun v => slot_D_mem hj
  by_cases ht0 : t = 0
  · subst ht0
    by_cases hm : ∃ o' j', R o j o' j'
    · obtain ⟨o', j', hR⟩ := hm
      obtain ⟨-, ho', -, hj'⟩ := h.lt hR
      have hF : (Finset.range (S * 36)).filter (portAdjN R (36 * o + 1 + 7 * j + 0)) =
          insert (36 * o' + 1 + 7 * j') D := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, slot_nbr_iff hj ht,
          hDmem]
        constructor
        · rintro ⟨hv, h1 | ⟨-, -, h3⟩ | ⟨-, h2, h3, h4⟩⟩
          · exact Or.inr h1
          · exact absurd ⟨o', j', hR⟩ h3
          · have := h.func hR h4
            left
            omega
        · rintro (rfl | ⟨h1, h2, h3, h4⟩)
          · have d2 : (36 * o' + 1 + 7 * j') % 36 = 1 + 7 * j' := by omega
            refine ⟨by omega, Or.inr (Or.inr ⟨trivial, by omega, by rw [d2]; omega, ?_⟩)⟩
            rw [show (36 * o' + 1 + 7 * j') / 36 = o' by omega, d2,
              show (1 + 7 * j' - 1) / 7 = j' by omega]
            exact hR
          · exact ⟨by omega, Or.inl ⟨h1, h2, h3, h4⟩⟩
      have hnot : 36 * o' + 1 + 7 * j' ∉ D := by
        rw [hDmem]
        rintro ⟨-, -, -, hg⟩
        have d2 : (36 * o' + 1 + 7 * j') % 36 = 1 + 7 * j' := by omega
        rw [d2] at hg
        unfold gadAdj at hg
        omega
      rw [hF, Finset.card_insert_of_notMem hnot, hDcard]
      simp
    · have hF : (Finset.range (S * 36)).filter (portAdjN R (36 * o + 1 + 7 * j + 0)) =
          insert (36 * o) D := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, slot_nbr_iff hj ht,
          hDmem]
        constructor
        · rintro ⟨hv, h1 | ⟨-, h2, -⟩ | ⟨-, h2, h3, h4⟩⟩
          · exact Or.inr h1
          · exact Or.inl h2
          · exact absurd ⟨_, _, h4⟩ hm
        · rintro (rfl | ⟨h1, h2, h3, h4⟩)
          · exact ⟨by omega, Or.inr (Or.inl ⟨trivial, rfl, hm⟩)⟩
          · exact ⟨by omega, Or.inl ⟨h1, h2, h3, h4⟩⟩
      have hnot : 36 * o ∉ D := by
        rw [hDmem]
        rintro ⟨h1, -⟩
        omega
      rw [hF, Finset.card_insert_of_notMem hnot, hDcard]
      simp
  · have hF : (Finset.range (S * 36)).filter (portAdjN R (36 * o + 1 + 7 * j + t)) = D := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, slot_nbr_iff hj ht, hDmem]
      constructor
      · rintro ⟨hv, h1 | ⟨h1, -⟩ | ⟨h1, -⟩⟩
        · exact h1
        · exact absurd h1 ht0
        · exact absurd h1 ht0
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨by omega, Or.inl ⟨h1, h2, h3, h4⟩⟩
    rw [hF, hDcard, if_neg ht0]

open Classical in
theorem nat_card_eq (h : IsPortRel S R) (u : Fin (S * 36)) :
    (Finset.univ.filter ((portGraph R S).Adj u)).card =
      ((Finset.range (S * 36)).filter (portAdjN R u.val)).card := by
  apply Finset.card_bij (fun a _ => a.val)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at ha ⊢
    exact ⟨a.isLt, (portGraph_adj h u a).1 ha⟩
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    exact ⟨⟨v, hv.1⟩, by simpa [portGraph_adj h] using hv.2, rfl⟩

open Classical in
theorem portGraph_regular {R : ℕ → ℕ → ℕ → ℕ → Prop} {S : ℕ} (h : IsPortRel S R)
    (u : Fin (S * 36)) : (Finset.univ.filter ((portGraph R S).Adj u)).card = 5 := by
  rw [nat_card_eq h u]
  have hu := u.isLt
  generalize u.val = x at hu
  by_cases h0 : x % 36 = 0
  · have hx : x = 36 * (x / 36) := by omega
    rw [hx]
    exact pos_card h (by omega)
  · have hx : x = 36 * (x / 36) + 1 + 7 * ((x % 36 - 1) / 7) + (x % 36 - 1) % 7 := by omega
    rw [hx]
    exact slot_card h (by omega) (by omega) (by omega)

end

end Lax117284Proofs.McisHard.Proved
