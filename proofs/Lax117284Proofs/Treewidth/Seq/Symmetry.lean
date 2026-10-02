import Lax117284Proofs.Treewidth.Seq.Typical

/-!
# Symmetries of `τ` (Althaus–Ziegler (H1), (H3))

* reversal: `typical a.reverse = (typical a).reverse`;
* shift: `typical (a.map (· + c)) = (typical a).map (· + c)` (and the subtraction version).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-! ### Reversal -/

theorem Red.reverse {a b : List ℕ} (h : Red a b) : Red a.reverse b.reverse := by
  cases h with
  | dup l x r =>
    simpa [List.reverse_append] using Red.dup r.reverse x l.reverse
  | typ l x m y r hm hz =>
    have := Red.typ r.reverse y m.reverse x l.reverse (by simpa using hm)
      (fun z hz' => (hz z (by simpa using hz')).symm)
    simpa [List.reverse_append] using this

theorem Reach.reverse {a b : List ℕ} (h : Reach a b) : Reach a.reverse b.reverse := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact ih.tail hr.reverse

theorem nf_reverse {a : List ℕ} (h : NF a) : NF a.reverse := by
  intro b hb
  have := hb.reverse
  rw [List.reverse_reverse] at this
  exact h _ this

theorem nf_reverse_iff {a : List ℕ} : NF a.reverse ↔ NF a :=
  ⟨fun h => by simpa using nf_reverse h, nf_reverse⟩

/-- (H1): `τ` commutes with reversal. -/
theorem typical_reverse (a : List ℕ) : typical a.reverse = (typical a).reverse :=
  (eq_typical_of_reach_nf (reach_typical a).reverse (nf_reverse (nf_typical a))).symm

/-! ### Shifting by a constant -/

theorem ent_map_add {a : List ℕ} {c i : ℕ} (h : i < a.length) :
    ent (a.map (· + c)) i = ent a i + c := by
  rw [ent_eq_getElem (by simpa using h), ent_eq_getElem h]; simp

theorem InR.add_iff {z x y c : ℕ} : InR (z + c) (x + c) (y + c) ↔ InR z x y := by
  unfold InR; omega

theorem nf_map_add {a : List ℕ} (c : ℕ) (h : NF a) : NF (a.map (· + c)) := by
  obtain ⟨hd, hw⟩ := nf_iff.mp h
  rw [nf_iff]
  refine ⟨fun k hk => ?_, fun k j hwin => ?_⟩
  · obtain ⟨h1, h2⟩ := hk
    simp only [List.length_map] at h1
    rw [ent_map_add (by omega), ent_map_add h1] at h2
    exact hd k ⟨h1, by omega⟩
  · obtain ⟨h1, h2, h3⟩ := hwin
    simp only [List.length_map] at h2
    apply hw k j
    refine ⟨h1, h2, fun m hm1 hm2 => ?_⟩
    have := h3 m hm1 hm2
    rw [ent_map_add (by omega), ent_map_add (by omega), ent_map_add h2] at this
    exact InR.add_iff.mp this

theorem nf_map_add_iff {a : List ℕ} (c : ℕ) : NF (a.map (· + c)) ↔ NF a := by
  constructor
  · intro h
    obtain ⟨hd, hw⟩ := nf_iff.mp h
    rw [nf_iff]
    refine ⟨fun k hk => ?_, fun k j hwin => ?_⟩
    · obtain ⟨h1, h2⟩ := hk
      apply hd k ⟨by simpa using h1, ?_⟩
      rw [ent_map_add (by omega), ent_map_add h1]; omega
    · obtain ⟨h1, h2, h3⟩ := hwin
      apply hw k j
      refine ⟨h1, by simpa using h2, fun m hm1 hm2 => ?_⟩
      rw [ent_map_add (by omega), ent_map_add (by omega), ent_map_add h2]
      exact InR.add_iff.mpr (h3 m hm1 hm2)
  · exact nf_map_add c

theorem Red.map_add {a b : List ℕ} (c : ℕ) (h : Red a b) :
    Red (a.map (· + c)) (b.map (· + c)) := by
  cases h with
  | dup l x r => simpa using Red.dup (l.map (· + c)) (x + c) (r.map (· + c))
  | typ l x m y r hm hz =>
    simpa using Red.typ (l.map (· + c)) (x + c) (m.map (· + c)) (y + c) (r.map (· + c))
      (by simpa using hm) (fun z hz' => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
        exact InR.add_iff.mpr (hz w hw))

theorem Reach.map_add {a b : List ℕ} (c : ℕ) (h : Reach a b) :
    Reach (a.map (· + c)) (b.map (· + c)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih => exact ih.tail (hr.map_add c)

/-- (H3): `τ` commutes with adding a constant. -/
theorem typical_map_add (a : List ℕ) (c : ℕ) :
    typical (a.map (· + c)) = (typical a).map (· + c) :=
  (eq_typical_of_reach_nf ((reach_typical a).map_add c) (nf_map_add c (nf_typical a))).symm

/-- (H3) for subtraction, when the constant is below every entry. -/
theorem typical_map_sub (a : List ℕ) (c : ℕ) (h : ∀ x ∈ a, c ≤ x) :
    typical (a.map (· - c)) = (typical a).map (· - c) := by
  have h1 : (a.map (· - c)).map (· + c) = a := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id a]
    apply List.map_congr_left
    intro x hx; simp [Nat.sub_add_cancel (h x hx)]
  have h2 := typical_map_add (a.map (· - c)) c
  rw [h1] at h2
  have h3 : (typical a).map (· - c) = typical (a.map (· - c)) := by
    rw [h2, List.map_map]
    have : ((fun x => x - c) ∘ fun x => x + c) = id := by funext x; simp
    rw [this, List.map_id]
  exact h3.symm

end Lax117284Proofs.Treewidth.Seq
