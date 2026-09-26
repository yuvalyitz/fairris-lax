import Lax117284Proofs.Machine.IlpVec
import Lax117284Proofs.IlpClients.Extras

/-!
What the machine computes for one certificate, as functions of the certificate.

The passes of the machine compute, from the digits `d` of a certificate `ω`:
* `kindOf n d c`: `3` for a live column with a small digit, `1` for a base, `2` for an extra, `0`
  for the rest (the zero columns and the large digit of nothing);
* `sigma`, `Sj` (as in the math layer);
* `wvF`: the value of the extras of rank below `n`, `0` for the others;
* `esF`: the sum of `wvF` over the extras of a type;
* `xF`: the candidate solution.
All of them are defined for every certificate, and agree with `xval` of the math layer once the
guard `(Ext n d).card ≤ n` holds (`xF_eq_xval`).  The machine accepts a certificate exactly when the
guard holds and `xF` solves the program (`AccSpec`).
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax117284Proofs.IlpClients Finset

open Classical

noncomputable section

/-- The kind of a column, as the machine computes it. -/
def kindOf (n : ℕ) (d : ℕ → ℕ) (c : ℕ) : ℕ :=
  if isLive n c ∧ d c < Kn n then 3
  else if isBase n d c then 1 else if isExtra n d c then 2 else 0

/-- The value of an extra of rank below `n`; `0` for every other column. -/
def wvF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  if isExtra n ω.d c ∧ rk n ω.d c < n then wcol n cnt bb ω c else 0

/-- The sum of the values of the extras of type `t`. -/
def esF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (t : ℕ) : ℕ :=
  ∑ c ∈ range (nN n), if isExtra n ω.d c ∧ tyOf n c = some t then wvF n cnt bb ω c else 0

/-- The candidate solution, as the machine computes it. -/
def xF (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) (c : ℕ) : ℕ :=
  if kindOf n ω.d c = 3 then ω.d c
  else if kindOf n ω.d c = 2 then wvF n cnt bb ω c
  else if kindOf n ω.d c = 1 then
    cp n cnt ω.d (tyIdx n c) - esF n cnt bb ω (tyIdx n c)
  else 0

/-- The certificate is accepted: at most `n` extras, and the candidate solves the program. -/
def AccSpec (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (ω : Cert) : Prop :=
  (Ext n ω.d).card ≤ n ∧ Checks n cnt bb (xF n cnt bb ω)

/-- The number `t` is accepted: the certificate of its digits is. -/
def AccT (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) (t : ℕ) : Prop :=
  AccSpec n cnt bb (certVec n (digitsOf (Rd n) t))

section
variable {n : ℕ} {cnt : ℕ → ℕ} {bb : ℕ} {ω : Cert}

theorem isExtra_mem_Ext {c : ℕ} (h : isExtra n ω.d c) : c ∈ Ext n ω.d := by
  unfold Ext
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  have := h.1
  unfold Lset at this
  exact (Finset.mem_filter.mp this).1

theorem wvF_eq_wcol (hE : (Ext n ω.d).card ≤ n) {c : ℕ} (h : isExtra n ω.d c) :
    wvF n cnt bb ω c = wcol n cnt bb ω c := by
  unfold wvF
  rw [if_pos ⟨h, (rk_lt_card (isExtra_mem_Ext h)).trans_le hE⟩]

theorem esF_eq_extraSum (hE : (Ext n ω.d).card ≤ n) (t : ℕ) :
    esF n cnt bb ω t = extraSum n cnt bb ω t := by
  unfold esF extraSum
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : isExtra n ω.d c ∧ tyOf n c = some t
  · rw [if_pos h, if_pos h, wvF_eq_wcol hE h.1]
  · rw [if_neg h, if_neg h]

theorem kindOf_eq_three {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 3 ↔ isLive n c ∧ d c < Kn n := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    split_ifs at h <;> omega
  · intro h; rw [if_pos h]

theorem kindOf_eq_one {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 1 ↔ isBase n d c := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    split_ifs at h <;> omega
  · intro h
    have hK : ¬ (isLive n c ∧ d c < Kn n) := by
      rintro ⟨-, hlt⟩
      have := ((mem_Lset_iff n d c).mp h.1).2
      omega
    rw [if_neg hK, if_pos h]

theorem kindOf_eq_two {d : ℕ → ℕ} {c : ℕ} : kindOf n d c = 2 ↔ isExtra n d c := by
  unfold kindOf
  constructor
  · intro h
    by_contra hc
    split_ifs at h <;> omega
  · intro h
    have hK : ¬ (isLive n c ∧ d c < Kn n) := by
      rintro ⟨-, hlt⟩
      have := ((mem_Lset_iff n d c).mp h.1).2
      omega
    have hb : ¬ isBase n d c := h.2
    rw [if_neg hK, if_neg hb, if_pos h]

/-- **The candidate of the machine is the candidate of the math layer** once the guard holds. -/
theorem xF_eq_xval (hE : (Ext n ω.d).card ≤ n) (c : ℕ) : xF n cnt bb ω c = xval n cnt bb ω c := by
  unfold xF xval
  by_cases h3 : isLive n c ∧ ω.d c < Kn n
  · rw [if_pos (kindOf_eq_three.mpr h3), if_pos h3]
  · have h3' : ¬ kindOf n ω.d c = 3 := fun h => h3 (kindOf_eq_three.mp h)
    rw [if_neg h3', if_neg h3]
    by_cases h2 : isExtra n ω.d c
    · rw [if_pos (kindOf_eq_two.mpr h2), if_pos h2, wvF_eq_wcol hE h2]
    · have h2' : ¬ kindOf n ω.d c = 2 := fun h => h2 (kindOf_eq_two.mp h)
      rw [if_neg h2', if_neg h2]
      by_cases h1 : isBase n ω.d c
      · rw [if_pos (kindOf_eq_one.mpr h1), if_pos h1, esF_eq_extraSum hE]
      · have h1' : ¬ kindOf n ω.d c = 1 := fun h => h1 (kindOf_eq_one.mp h)
        rw [if_neg h1', if_neg h1]

theorem AccSpec_iff : AccSpec n cnt bb ω ↔
    (Ext n ω.d).card ≤ n ∧ Checks n cnt bb (xval n cnt bb ω) := by
  unfold AccSpec
  constructor
  · rintro ⟨hE, hc⟩
    refine ⟨hE, fun r hr => ?_⟩
    rw [← hc r hr]
    exact Finset.sum_congr rfl fun c _ => by rw [xF_eq_xval hE]
  · rintro ⟨hE, hc⟩
    refine ⟨hE, fun r hr => ?_⟩
    rw [← hc r hr]
    exact Finset.sum_congr rfl fun c _ => by rw [xF_eq_xval hE]

end

/-- **The search of the machine decides feasibility**: the program of `ilpWord n cnt bb` is feasible
if and only if one of the numbers below `Rd n ^ Dn n` is accepted. -/
theorem feasible_iff_accT (n : ℕ) (cnt : ℕ → ℕ) (bb : ℕ) :
    (decodeILP (ilpWord n cnt bb)).Feasible ↔ ∃ t < Rd n ^ Dn n, AccT n cnt bb t := by
  constructor
  · intro h
    obtain ⟨b, x, hd, hx⟩ := cert_complete_box h
    obtain ⟨t, ht, hcert⟩ := exists_digits_of_bcert b
    refine ⟨t, ht, ?_⟩
    unfold AccT
    rw [hcert]
    rw [AccSpec_iff]
    unfold decode at hd
    split_ifs at hd with hG
    · have hx' : x = xval n cnt bb b.toCert := (Option.some.inj hd).symm
      refine ⟨hG.2.1, ?_⟩
      rw [← hx']
      exact hx
  · rintro ⟨t, -, hacc⟩
    have := (AccSpec_iff).mp hacc
    exact (feasible_iff_nat n cnt bb).mpr ⟨_, this.2⟩

end

end Lax117284Proofs.Machine.Ilp
