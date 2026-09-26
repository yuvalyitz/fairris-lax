import Lax117284Proofs.Bipartite.Ram2.SearchAbs

/-!
The potential of the search, and what each kind of turn does to it.

One turn's machine cost is paid out of `AS.pot`. It counts the scan work still to come on each
live frame (`off (Ls k + 1) - Xs k` slots, at 40 per slot), a flat charge `potD` per live frame,
and a charge per still-unvisited right vertex `j`: `40 * occLen j + potW`, where `occLen j` is
the length of the row of the left vertex currently holding `j` (zero if `j` is free). Visiting
`j` releases exactly what pushing a frame for its occupant costs — the scan of that occupant's
row — so the search's total cost is linear in `rowlen l₀ + Σ_j occLen j + m`, and the occupant
sum is at most the total row length of the left side, since the matching is injective.

The successful turn ends the loop, so its ghost successor state is the zero-potential `AS.done`;
its cost is paid out of the pending frame's scan share, the flat charges, and the released
vertex's charge, which is `pot_success`.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax117284.BipartiteKuhn Lax117284Proofs.Bipartite.Matching

/-- Flat charge per live frame. -/
def potD : ℕ := 100

/-- Flat charge per unvisited right vertex. -/
def potW : ℕ := 300

/-- The row length of the occupant of a right vertex (zero if free). -/
def occLen (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (j : ℕ) : ℕ :=
  match μ₀ j with
  | none => 0
  | some l => rowlen off l

/-- The charge of an unvisited right vertex. -/
def potJ (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (j : ℕ) : ℕ := 40 * occLen off μ₀ j + potW

open Classical in
/-- **The potential.** -/
noncomputable def AS.pot (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (m : ℕ) (a : AS) : ℕ :=
  40 * (∑ k ∈ Finset.range a.top, (off (a.Ls k + 1) - a.Xs k)) + potD * a.top +
    ∑ j ∈ (Finset.range m).filter (fun j => ¬ a.visB j), potJ off μ₀ j

section Pot

variable {off tgt : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m l₀ : ℕ} {a : AS} {s j l' : ℕ}

open Classical in
theorem AS.done_pot : (AS.done).pot off μ₀ m = 0 := by
  unfold AS.pot AS.done
  simp

/-- **Popping a frame releases its share.** -/
theorem pot_pop (a : AS) (h : 1 ≤ a.top) :
    a.pot off μ₀ m = a.pop.pot off μ₀ m + (40 * (off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1)) +
      potD) := by
  have e2 : a.pop.top = a.top - 1 := rfl
  have e3 : a.pop.Xs = a.Xs := rfl
  have e4 : a.pop.Ls = a.Ls := rfl
  have e5 : a.pop.visB = a.visB := rfl
  unfold AS.pot
  rw [e2, e3, e4, e5]
  obtain ⟨t, ht⟩ : ∃ t, a.top = t + 1 := ⟨a.top - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel, Finset.sum_range_succ]
  have hD := mul_add_one potD t
  omega

open Classical in
/-- The unvisited set after choosing `j` is the old one without `j`. -/
theorem filter_choose (a : AS) (s j : ℕ) :
    (Finset.range m).filter (fun r => ¬ (a.choose s j).visB r) =
      ((Finset.range m).filter (fun r => ¬ a.visB r)).erase j := by
  ext r
  rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
  show r < m ∧ ¬ (r = j ∨ a.visB r) ↔ r ≠ j ∧ r < m ∧ ¬ a.visB r
  constructor
  · rintro ⟨hr, h⟩
    push Not at h
    exact ⟨h.1, hr, h.2⟩
  · rintro ⟨h1, hr, h2⟩
    exact ⟨hr, fun h => h.elim h1 h2⟩

open Classical in
theorem sum_choose (a : AS) (s : ℕ) (hj : j < m) (hfresh : ¬ a.visB j) :
    ∑ r ∈ (Finset.range m).filter (fun r => ¬ a.visB r), potJ off μ₀ r =
      potJ off μ₀ j + ∑ r ∈ (Finset.range m).filter (fun r => ¬ (a.choose s j).visB r),
        potJ off μ₀ r := by
  rw [filter_choose, Finset.add_sum_erase]
  simp [hj, hfresh]

open Classical in
/-- **The successful turn is paid for**: the pending frame's scan share up to the found slot, the
flat charges, and the released vertex's charge are all in the potential. -/
theorem pot_success (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j) :
    40 * (s + 1 - a.Xs (a.top - 1)) + potD * a.top + potW ≤ a.pot off μ₀ m := by
  have hpos := hI.top_pos
  have hhi := hF.hi
  unfold AS.pot
  have h1 : off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1) ≤
      ∑ k ∈ Finset.range a.top, (off (a.Ls k + 1) - a.Xs k) :=
    Finset.single_le_sum (f := fun k => off (a.Ls k + 1) - a.Xs k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega))
  have h2 : potJ off μ₀ j ≤ ∑ r ∈ (Finset.range m).filter (fun r => ¬ a.visB r), potJ off μ₀ r :=
    Finset.single_le_sum (f := potJ off μ₀) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 hF.lt, hF.fresh⟩)
  have h3 : potW ≤ potJ off μ₀ j := by unfold potJ; omega
  have h4 : s + 1 - a.Xs (a.top - 1) ≤ off (a.Ls (a.top - 1) + 1) - a.Xs (a.top - 1) := by omega
  have h5 := Nat.mul_le_mul_left 40 (h4.trans h1)
  omega

open Classical in
/-- **Choosing a candidate and pushing a frame for its occupant** is paid for by the pending
frame's scan share up to the found slot and the released vertex's flat charge, minus the new
frame's flat charge. -/
theorem pot_push (hI : AbsInv off tgt μ₀ n m l₀ a) (hF : Found off tgt n m a s j)
    (hocc : μ₀ j = some l') :
    a.pot off μ₀ m + potD =
      ((a.choose s j).push off l').pot off μ₀ m + 40 * (s + 1 - a.Xs (a.top - 1)) + potW := by
  have hpos := hI.top_pos
  have hge := hF.ge hI
  have hhi := hF.hi
  have hsum := sum_choose (off := off) (μ₀ := μ₀) a s hF.lt hF.fresh
  have e1 : ((a.choose s j).push off l').visB = (a.choose s j).visB := rfl
  have e2 : ((a.choose s j).push off l').top = a.top + 1 := rfl
  have hJ : potJ off μ₀ j = 40 * rowlen off l' + potW := by
    unfold potJ occLen; rw [hocc]
  unfold AS.pot
  rw [e1, e2, hsum, hJ]
  obtain ⟨t, ht⟩ : ∃ t, a.top = t + 1 := ⟨a.top - 1, by omega⟩
  have hXs : ((a.choose s j).push off l').Xs =
      Function.update (Function.update a.Xs t (s + 1)) (t + 1) (off l') := by
    show Function.update (Function.update a.Xs (a.top - 1) (s + 1)) a.top (off l') = _
    rw [ht, Nat.add_sub_cancel]
  have hLs : ((a.choose s j).push off l').Ls = Function.update a.Ls (t + 1) l' := by
    show Function.update a.Ls a.top l' = _
    rw [ht]
  rw [hXs, hLs, ht]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hcongr : ∑ k ∈ Finset.range t, (off (Function.update a.Ls (t + 1) l' k + 1) -
      Function.update (Function.update a.Xs t (s + 1)) (t + 1) (off l') k) =
      ∑ k ∈ Finset.range t, (off (a.Ls k + 1) - a.Xs k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  rw [hcongr]
  simp only [Function.update_self, Function.update_of_ne (show t ≠ t + 1 by omega),
    Nat.add_sub_cancel]
  rw [ht, Nat.add_sub_cancel] at hge hhi
  have hD := mul_add_one potD (t + 1)
  have hD' := mul_add_one potD t
  unfold rowlen
  have hX : a.Xs t ≤ s + 1 := by omega
  omega

end Pot

/-! ### The potential of a restarted search -/

section Restart

variable {off : ℕ → ℕ} {μ₀ : ℕ → Option ℕ} {n m : ℕ}

open Classical in
theorem AS.restart_pot (b : AS) (l₀ : ℕ) :
    (AS.restart off b l₀).pot off μ₀ m =
      40 * rowlen off l₀ + potD + ∑ j ∈ Finset.range m, potJ off μ₀ j := by
  unfold AS.pot
  have h1 : (AS.restart off b l₀).top = 1 := rfl
  have hf : (Finset.range m).filter (fun j => ¬ (AS.restart off b l₀).visB j) = Finset.range m := by
    ext r; simp [AS.restart]
  rw [h1, hf, Finset.sum_range_one]
  simp [AS.restart, rowlen]

theorem sum_potJ (off : ℕ → ℕ) (μ₀ : ℕ → Option ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range m, potJ off μ₀ j =
      40 * ∑ j ∈ Finset.range m, occLen off μ₀ j + potW * m := by
  unfold potJ
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- **The occupants' rows are distinct rows of the left side**, so their lengths sum to at most
the total row length of the left side. -/
theorem sum_occLen_le (hinj : InjOnSupport μ₀) (hbd : ∀ j l, μ₀ j = some l → l < n) :
    ∑ j ∈ Finset.range m, occLen off μ₀ j ≤ ∑ l ∈ Finset.range n, rowlen off l := by
  classical
  set s := (Finset.range m).filter (fun j => (μ₀ j).isSome) with hs
  set g : ℕ → ℕ := fun j => (μ₀ j).getD 0 with hg
  have h1 : ∑ j ∈ Finset.range m, occLen off μ₀ j = ∑ j ∈ s, rowlen off (g j) := by
    rw [hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold occLen
    rcases hμ : μ₀ j with _ | l <;> simp [hg, hμ]
  have h2 : ∑ j ∈ s, rowlen off (g j) = ∑ l ∈ s.image g, rowlen off l := by
    rw [Finset.sum_image]
    intro j hj j' hj' he
    have hj1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2
    have hj2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hj')).2
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hj1
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 hj2
    simp only [hg, hl, hl', Option.getD_some] at he
    subst he
    exact hinj j j' l hl hl'
  have h3 : s.image g ⊆ Finset.range n := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hl
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hj).2
    simp only [hg, hl', Option.getD_some]
    exact Finset.mem_range.2 (hbd j l' hl')
  rw [h1, h2]
  exact Finset.sum_le_sum_of_subset h3

/-- The rows of the left side, laid end to end, end at `off n`. -/
theorem sum_rowlen_le (off : ℕ → ℕ) (n : ℕ) (hmono : ∀ l < n, off l ≤ off (l + 1)) :
    ∑ l ∈ Finset.range n, rowlen off l ≤ off n := by
  have key : ∀ k ≤ n, ∑ l ∈ Finset.range k, rowlen off l + off 0 = off k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 := hmono k (by omega)
      have h3 : rowlen off k = off (k + 1) - off k := rfl
      omega
  have := key n le_rfl
  omega

/-- **A restarted search's potential is linear in the row lengths and `m`.** -/
theorem restart_pot_le (b : AS) (l₀ : ℕ) (hinj : InjOnSupport μ₀)
    (hbd : ∀ j l, μ₀ j = some l → l < n) (hmono : ∀ l < n, off l ≤ off (l + 1)) {R : ℕ}
    (hR : off n ≤ R) (hl₀ : rowlen off l₀ ≤ R) :
    (AS.restart off b l₀).pot off μ₀ m ≤ 80 * R + potD + potW * m := by
  rw [AS.restart_pot, sum_potJ]
  have h1 := sum_occLen_le (off := off) (m := m) hinj hbd
  have h2 := sum_rowlen_le off n hmono
  have h3 := Nat.mul_le_mul_left 40 (h1.trans (h2.trans hR))
  have h4 := Nat.mul_le_mul_left 40 hl₀
  omega

end Restart

end Lax117284Proofs.Bipartite.Ram2
