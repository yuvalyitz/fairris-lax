import Lax117284Proofs.Machine.TwFill

/-!
The guard: how many widths of decomposition the length of the word admits. A width `w` is admitted
when the memory it needs, `2 ^ geE cc m w`, is at most the length `L` of the word, that is when
`geE cc m w ≤ ⌊log₂ L⌋`. The loops compute `⌊log₂ L⌋` and the number of admitted widths, both in time
linear in `L`.
-/

namespace Lax117284Proofs.Machine.TwPrep

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

/-! ### The arithmetic -/

/-- The exponent of the memory a width `w` needs, for `m` days. -/
def geE (cc m w : ℕ) : ℕ := cc * ((w + 1) * (w + 1) * (w + 1)) + m * (w + 1) + 2

lemma geE_mono (cc m : ℕ) {a b : ℕ} (h : a ≤ b) : geE cc m a ≤ geE cc m b := by
  unfold geE; gcongr

lemma le_geE {cc : ℕ} (hcc : 1 ≤ cc) (m w : ℕ) : w + 1 < geE cc m w := by
  unfold geE
  have h1 : (w + 1) ≤ (w + 1) * (w + 1) * (w + 1) := by
    calc w + 1 = (w + 1) * 1 * 1 := by ring
      _ ≤ (w + 1) * (w + 1) * (w + 1) := by gcongr <;> omega
  have h2 : (w + 1) * (w + 1) * (w + 1) ≤ cc * ((w + 1) * (w + 1) * (w + 1)) :=
    Nat.le_mul_of_pos_left _ hcc
  omega

/-- The number of the widths `0 … ℓ` that the guard admits. -/
def wcnt (cc m ℓ : ℕ) : ℕ := ∑ j ∈ Finset.range (ℓ + 1), if geE cc m j ≤ ℓ then 1 else 0

lemma cnt_spec (p : ℕ → Prop) [DecidablePred p] (hp : ∀ a b, a ≤ b → p b → p a) : ∀ M,
    (∑ j ∈ Finset.range M, if p j then 1 else 0) ≤ M ∧
      (∀ j < ∑ j ∈ Finset.range M, if p j then 1 else 0, p j) ∧
      ((∑ j ∈ Finset.range M, if p j then 1 else 0) < M →
        ¬ p (∑ j ∈ Finset.range M, if p j then 1 else 0))
  | 0 => by simp
  | M + 1 => by
    obtain ⟨h1, h2, h3⟩ := cnt_spec p hp M
    rw [Finset.sum_range_succ]
    by_cases hlt : (∑ j ∈ Finset.range M, if p j then 1 else 0) < M
    · have hnp : ¬ p M := fun h => h3 hlt (hp _ _ (by omega) h)
      rw [if_neg hnp, Nat.add_zero]
      exact ⟨by omega, h2, fun _ => h3 hlt⟩
    · have heq : (∑ j ∈ Finset.range M, if p j then 1 else 0) = M := by omega
      by_cases hpM : p M
      · rw [if_pos hpM, heq]
        refine ⟨le_rfl, fun j hj => ?_, fun h => by omega⟩
        by_cases hjM : j < M
        · exact h2 j (by omega)
        · have : j = M := by omega
          subst this; exact hpM
      · rw [if_neg hpM, Nat.add_zero, heq]
        exact ⟨by omega, fun j hj => h2 j (by omega), fun _ => hpM⟩

theorem wcnt_spec {cc : ℕ} (hcc : 1 ≤ cc) (m ℓ : ℕ) :
    wcnt cc m ℓ ≤ ℓ ∧ (∀ j < wcnt cc m ℓ, geE cc m j ≤ ℓ) ∧ ℓ < geE cc m (wcnt cc m ℓ) := by
  have hp : ∀ a b, a ≤ b → geE cc m b ≤ ℓ → geE cc m a ≤ ℓ :=
    fun a b hab h => le_trans (geE_mono cc m hab) h
  obtain ⟨h1, h2, h3⟩ := cnt_spec (fun j => geE cc m j ≤ ℓ) hp (ℓ + 1)
  change wcnt cc m ℓ ≤ ℓ + 1 at h1
  change ∀ j < wcnt cc m ℓ, geE cc m j ≤ ℓ at h2
  change wcnt cc m ℓ < ℓ + 1 → ¬ geE cc m (wcnt cc m ℓ) ≤ ℓ at h3
  have hlt : wcnt cc m ℓ < ℓ + 1 := by
    by_contra hn
    have heq : wcnt cc m ℓ = ℓ + 1 := by omega
    have := h2 ℓ (by omega)
    have := le_geE hcc m ℓ
    omega
  refine ⟨by omega, h2, ?_⟩
  have := h3 hlt
  omega

/-- The step of the logarithm: one more if `2 ^ (a + 1) ≤ L`. -/
def lgStep (L a : ℕ) : ℕ := a + (if 1 < L / 2 ^ a then 1 else 0)

lemma one_lt_div_iff {L a : ℕ} (hL : L ≠ 0) : 1 < L / 2 ^ a ↔ a + 1 ≤ Nat.log 2 L := by
  have h1 : 1 < L / 2 ^ a ↔ 2 ≤ L / 2 ^ a := Iff.rfl
  rw [h1, Nat.le_div_iff_mul_le (by positivity)]
  constructor
  · intro h
    exact Nat.le_log_of_pow_le (by norm_num) (by rw [pow_succ]; omega)
  · intro h
    have := Nat.pow_le_of_le_log hL h
    rw [pow_succ] at this; omega

lemma lg_iter {L : ℕ} (hL : L ≠ 0) (j : ℕ) :
    (List.range j).foldl (fun a _ => lgStep L a) 0 = min j (Nat.log 2 L) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, lgStep]
    by_cases h : j < Nat.log 2 L
    · rw [min_eq_left h.le, if_pos ((one_lt_div_iff hL).2 (by omega))]
      omega
    · rw [min_eq_right (by omega), if_neg (fun hh => by have := (one_lt_div_iff hL).1 hh; omega)]
      omega

end Lax117284Proofs.Machine.TwPrep
