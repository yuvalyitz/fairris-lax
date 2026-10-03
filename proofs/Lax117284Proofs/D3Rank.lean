import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
Sorting by rank: the position of a client in the order of due dates is the number of clients that
precede it, and this is a bijection from the clients onto the positions.
-/

namespace Lax117284Proofs.D3Rank

/-- The client `a` precedes the client `b`: earlier due date, or the same and a smaller number. -/
def Lt2 (dd : ℕ → ℕ) (a b : ℕ) : Prop := dd a < dd b ∨ (dd a = dd b ∧ a < b)

instance (dd : ℕ → ℕ) (a b : ℕ) : Decidable (Lt2 dd a b) := by unfold Lt2; infer_instance

/-- The number of clients that precede `j`. -/
def rk (dd : ℕ → ℕ) (n j : ℕ) : ℕ := (List.range n).countP fun j' => decide (Lt2 dd j' j)

variable {dd : ℕ → ℕ} {n j c : ℕ}

lemma lt2_irrefl (a : ℕ) : ¬ Lt2 dd a a := by
  unfold Lt2; omega

lemma lt2_trans {a b c : ℕ} (h1 : Lt2 dd a b) (h2 : Lt2 dd b c) : Lt2 dd a c := by
  unfold Lt2 at *; omega

lemma lt2_total {a b : ℕ} (h : a ≠ b) : Lt2 dd a b ∨ Lt2 dd b a := by
  unfold Lt2; omega

lemma countP_range_eq_sum' (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).countP (fun x => decide (p x)) = ∑ i ∈ Finset.range n, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp

lemma countP_range_eq_card' (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    (List.range n).countP (fun x => decide (p x)) =
      (Finset.univ.filter (fun x : Fin n => p x)).card := by
  rw [countP_range_eq_sum', Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if p i then 1 else 0)]

lemma rk_eq_card (j : ℕ) :
    rk dd n j = (Finset.univ.filter fun j' : Fin n => Lt2 dd j' j).card :=
  countP_range_eq_card' (fun j' => Lt2 dd j' j) n

lemma rk_lt (hj : j < n) : rk dd n j < n := by
  rw [rk_eq_card]
  calc (Finset.univ.filter fun j' : Fin n => Lt2 dd j' j).card
      < (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨⟨j, hj⟩, Finset.mem_univ _, by simp [lt2_irrefl]⟩
    _ = n := by simp

lemma rk_strictMono {a b : ℕ} (hb : b < n) (hab : Lt2 dd a b) (ha : a < n) :
    rk dd n a < rk dd n b := by
  rw [rk_eq_card, rk_eq_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨⟨a, ha⟩, by simpa using hab, by simp [lt2_irrefl]⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt2_trans hx hab

lemma rk_injOn {a b : ℕ} (ha : a < n) (hb : b < n) (h : rk dd n a = rk dd n b) : a = b := by
  by_contra hne
  rcases lt2_total (dd := dd) hne with h1 | h1
  · have := rk_strictMono hb h1 ha; omega
  · have := rk_strictMono ha h1 hb; omega

lemma rk_surj (c : ℕ) (hc : c < n) : ∃ j, j < n ∧ rk dd n j = c := by
  let g : Fin n → Fin n := fun j => ⟨rk dd n j, rk_lt j.isLt⟩
  have hinj : Function.Injective g := fun a b hab => by
    apply Fin.ext
    exact rk_injOn a.isLt b.isLt (by simpa [g] using congrArg Fin.val hab)
  obtain ⟨j, hj⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨c, hc⟩
  exact ⟨j, j.isLt, by simpa [g] using congrArg Fin.val hj⟩

/-- The client at position `c` of the order. -/
noncomputable def ordOf (dd : ℕ → ℕ) (n c : ℕ) : ℕ :=
  if h : ∃ j, j < n ∧ rk dd n j = c then h.choose else 0

lemma ordOf_spec (hc : c < n) : ordOf dd n c < n ∧ rk dd n (ordOf dd n c) = c := by
  unfold ordOf
  rw [dif_pos (rk_surj c hc)]
  exact (rk_surj c hc).choose_spec

lemma ordOf_rk (hj : j < n) : ordOf dd n (rk dd n j) = j := by
  have h := ordOf_spec (dd := dd) (n := n) (c := rk dd n j) (rk_lt (dd := dd) hj)
  exact rk_injOn h.1 hj h.2

lemma ordOf_mono {c c' : ℕ} (hc : c < n) (hc' : c' < n) (h : c ≤ c') :
    dd (ordOf dd n c) ≤ dd (ordOf dd n c') := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · by_contra hgt
    have hgt : dd (ordOf dd n c') < dd (ordOf dd n c) := not_le.1 hgt
    have h1 := ordOf_spec (dd := dd) hc
    have h2 := ordOf_spec (dd := dd) hc'
    have hl : Lt2 dd (ordOf dd n c') (ordOf dd n c) := Or.inl hgt
    have := rk_strictMono h1.1 hl h2.1
    omega

lemma ordOf_inj {c c' : ℕ} (hc : c < n) (hc' : c' < n) (h : ordOf dd n c = ordOf dd n c') :
    c = c' := by
  have h1 := ordOf_spec (dd := dd) hc
  have h2 := ordOf_spec (dd := dd) hc'
  rw [← h1.2, ← h2.2, h]

end Lax117284Proofs.D3Rank
