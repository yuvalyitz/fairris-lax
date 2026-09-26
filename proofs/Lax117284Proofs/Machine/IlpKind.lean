import Lax117284Proofs.Machine.IlpSpec

/-!
The kinds of the columns, column by column: the facts about `kindOf` that the classification pass
of the machine uses (`kindOf_step`, `hlF_succ`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

open Classical

noncomputable section

section
variable {n : ℕ} {d : ℕ → ℕ}

theorem nV_le_nN' (n : ℕ) : nV n ≤ nN n := by unfold nN; omega

theorem coef_div_eq_one_iff {c : ℕ} (hc : c < nV n) : coef n (c / nZ n) c = 1 ↔ liveP n c := by
  have hlt : c / nZ n < nT n := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm]; exact hc
  rw [coef_type_row n _ c hlt]
  unfold tyOf
  by_cases hl : liveP n c
  · simp [hl]
  · simp [hl]

theorem tyOf_eq_some_iff {c t : ℕ} : tyOf n c = some t ↔ liveP n c ∧ t = c / nZ n := by
  unfold tyOf
  by_cases hl : liveP n c
  · simp only [hl, if_true, Option.some.injEq, true_and]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · simp [hl]

theorem tyOf_of_ge_V {c : ℕ} (h : nV n ≤ c) : tyOf n c = none := by
  unfold tyOf
  have : ¬ liveP n c := fun hl => by have := hl.1; omega
  simp [this]

theorem isLive_iff_of_lt_V {c : ℕ} (hc : c < nV n) : isLive n c ↔ liveP n c := by
  unfold isLive
  constructor
  · rintro ⟨-, h | h⟩
    · omega
    · exact h
  · intro h
    exact ⟨by have := nV_le_nN' n; omega, Or.inr h⟩

theorem isLive_of_ge_V {c : ℕ} (h1 : nV n ≤ c) (h2 : c < nN n) : isLive n c :=
  ⟨h2, Or.inl h1⟩

/-- Whether an earlier large column has type `t`. -/
def hlF (n : ℕ) (d : ℕ → ℕ) (t i : ℕ) : ℕ :=
  if ∃ c < i, c ∈ Lset n d ∧ tyOf n c = some t then 1 else 0

theorem hlF_zero (t : ℕ) : hlF n d t 0 = 0 := by
  unfold hlF
  rw [if_neg]
  rintro ⟨c, hc, -⟩
  omega

theorem hlF_succ (t c : ℕ) :
    hlF n d t (c + 1) = if (c ∈ Lset n d ∧ tyOf n c = some t) then 1 else hlF n d t c := by
  unfold hlF
  by_cases h : c ∈ Lset n d ∧ tyOf n c = some t
  · rw [if_pos h, if_pos ⟨c, by omega, h⟩]
  · rw [if_neg h]
    by_cases h' : ∃ c' < c, c' ∈ Lset n d ∧ tyOf n c' = some t
    · rw [if_pos h', if_pos]
      obtain ⟨c', hc', hh⟩ := h'
      exact ⟨c', by omega, hh⟩
    · rw [if_neg h', if_neg]
      rintro ⟨c', hc', hh⟩
      by_cases hcc : c' = c
      · subst hcc; exact h hh
      · exact h' ⟨c', by omega, hh⟩

theorem hlF_le_one (t i : ℕ) : hlF n d t i ≤ 1 := by
  unfold hlF; split_ifs <;> omega

/-- A large typed column: the flag of its type. -/
theorem mem_Lset_and_tyOf {c t : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    (c ∈ Lset n d ∧ tyOf n c = some t) ↔
      c < nV n ∧ coef n (c / nZ n) c = 1 ∧ d c = Kn n ∧ t = c / nZ n := by
  rw [mem_Lset_iff, tyOf_eq_some_iff]
  constructor
  · rintro ⟨⟨hl, hd⟩, hlv, ht⟩
    refine ⟨hlv.1, (coef_div_eq_one_iff hlv.1).mpr hlv, hd, ht⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hlv : liveP n c := (coef_div_eq_one_iff h1).mp h2
    exact ⟨⟨(isLive_iff_of_lt_V h1).mpr hlv, h3⟩, hlv, h4⟩

/-- **The kind of column `c`, from the tests of the machine.** -/
theorem kindOf_step {c : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    kindOf n d c =
      if c < nV n then
        (if coef n (c / nZ n) c = 1 then
          (if d c < Kn n then 3 else if hlF n d (c / nZ n) c = 0 then 1 else 2)
         else 0)
      else (if d c < Kn n then 3 else 2) := by
  by_cases hV : c < nV n
  · rw [if_pos hV]
    by_cases hcf : coef n (c / nZ n) c = 1
    · rw [if_pos hcf]
      have hlv : liveP n c := (coef_div_eq_one_iff hV).mp hcf
      have hlive : isLive n c := (isLive_iff_of_lt_V hV).mpr hlv
      by_cases hdk : d c < Kn n
      · rw [if_pos hdk]
        exact kindOf_eq_three.mpr ⟨hlive, hdk⟩
      · rw [if_neg hdk]
        have hdeq : d c = Kn n := by omega
        have hL : c ∈ Lset n d := (mem_Lset_iff n d c).mpr ⟨hlive, hdeq⟩
        have hty : tyOf n c = some (c / nZ n) := tyOf_eq_some_iff.mpr ⟨hlv, rfl⟩
        have hbase : isBase n d c ↔ hlF n d (c / nZ n) c = 0 := by
          rw [isBase_iff]
          unfold hlF
          constructor
          · rintro ⟨-, -, h⟩
            rw [if_neg]
            rintro ⟨c', hc', hL', hty'⟩
            exact h c' hc' hL' (by rw [hty, hty'])
          · intro h
            refine ⟨hL, by rw [hty]; simp, fun c' hc' hL' hne => ?_⟩
            have : ∃ c' < c, c' ∈ Lset n d ∧ tyOf n c' = some (c / nZ n) :=
              ⟨c', hc', hL', by rw [hne, hty]⟩
            rw [if_pos this] at h
            omega
        by_cases hb : isBase n d c
        · have h0 : hlF n d (c / nZ n) c = 0 := hbase.mp hb
          rw [if_pos h0]
          exact kindOf_eq_one.mpr hb
        · have h0 : ¬ hlF n d (c / nZ n) c = 0 := fun h => hb (hbase.mpr h)
          rw [if_neg h0]
          exact kindOf_eq_two.mpr ⟨hL, hb⟩
    · rw [if_neg hcf]
      have hlv : ¬ liveP n c := fun h => hcf ((coef_div_eq_one_iff hV).mpr h)
      have hlive : ¬ isLive n c := fun h => hlv ((isLive_iff_of_lt_V hV).mp h)
      unfold kindOf
      have h1 : ¬ (isLive n c ∧ d c < Kn n) := fun h => hlive h.1
      have h2 : ¬ isBase n d c := fun h => hlive ((mem_Lset_iff n d c).mp h.1).1
      have h3 : ¬ isExtra n d c := fun h => hlive ((mem_Lset_iff n d c).mp h.1).1
      rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [if_neg hV]
    have hV' : nV n ≤ c := by omega
    have hlive : isLive n c := isLive_of_ge_V hV' hc
    by_cases hdk : d c < Kn n
    · rw [if_pos hdk]
      exact kindOf_eq_three.mpr ⟨hlive, hdk⟩
    · rw [if_neg hdk]
      have hdeq : d c = Kn n := by omega
      have hL : c ∈ Lset n d := (mem_Lset_iff n d c).mpr ⟨hlive, hdeq⟩
      have hb : ¬ isBase n d c := fun h => h.2.1 (tyOf_of_ge_V hV')
      exact kindOf_eq_two.mpr ⟨hL, hb⟩

/-- The flag of the type after column `c`, from the tests of the machine. -/
theorem hlF_step {c t : ℕ} (hc : c < nN n) (hdc : d c ≤ Kn n) :
    hlF n d t (c + 1) =
      if (c < nV n ∧ coef n (c / nZ n) c = 1 ∧ ¬ d c < Kn n ∧ t = c / nZ n) then 1
      else hlF n d t c := by
  rw [hlF_succ]
  have := mem_Lset_and_tyOf (n := n) (d := d) (t := t) hc hdc
  by_cases h : c ∈ Lset n d ∧ tyOf n c = some t
  · have h' := this.mp h
    rw [if_pos h, if_pos ⟨h'.1, h'.2.1, by omega, h'.2.2.2⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨h1, h2, h3, h4⟩
    exact h (this.mpr ⟨h1, h2, by omega, h4⟩)

end

end

end Lax117284Proofs.Machine.Ilp
