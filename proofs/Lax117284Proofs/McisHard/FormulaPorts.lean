import Lax117284Proofs.McisHard.Defs

/-!
# WP3: the Port Relation of a Formula (`isPortRel_RN`, `rank_initial`, `unmatched_iff`, `posGraph_RN`)

Statements identical to the goal statements of `McisHard/Defs.lean`, proved in the namespace `Proved`
(the identity with the original goals was checked while the goals were still stubs).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Proved

open Lax117284Proofs.McisHard
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

section Arith

/-- clause-position arithmetic of the mate: `(t+j+1) % s`, then again with `j' = s-2-j`. -/
lemma mod_mate {s t j j' : ℕ} (hs : s = 2 ∨ s = 3) (ht : t < s) (h : j + j' + 2 = s) :
    ((t + j + 1) % s + j' + 1) % s = t := by
  rcases hs with rfl | rfl <;> omega

lemma mate_ne {s t j : ℕ} (hs : s = 2 ∨ s = 3) (ht : t < s) (hj : j + 1 < s) :
    (t + j + 1) % s ≠ t := by
  rcases hs with rfl | rfl <;> omega

lemma mate_inj {s t j j₂ : ℕ} (hs : s = 2 ∨ s = 3) (ht : t < s) (hj : j + 1 < s) (hj₂ : j₂ + 1 < s)
    (h : (t + j + 1) % s = (t + j₂ + 1) % s) : j = j₂ := by
  rcases hs with rfl | rfl <;> omega

lemma port_arith {s t x : ℕ} (hs : s = 2 ∨ s = 3) (ht : t < s) (hx : x < s) (hne : x ≠ t) :
    ∃ j, j < 2 ∧ j + 2 ≤ s ∧ (t + j + 1) % s = x := by
  rcases hs with rfl | rfl
  · exact ⟨0, by omega, by omega, by omega⟩
  · by_cases h : (t + 0 + 1) % 3 = x
    · exact ⟨0, by omega, by omega, h⟩
    · exact ⟨1, by omega, by omega, by omega⟩

end Arith

section Cl

variable (ns : List ℕ)

lemma cl_facts {o : ℕ} (ho : o < SlotsN ns) :
    (clSz ns o = 2 ∨ clSz ns o = 3) ∧ clIx ns o < clSz ns o ∧ clIx ns o ≤ o := by
  unfold clSz clIx SlotsN at *; split_ifs <;> omega

lemma posOf_facts {o x : ℕ} (ho : o < SlotsN ns) (hx : x < clSz ns o) :
    o - clIx ns o + x < SlotsN ns ∧ clSz ns (o - clIx ns o + x) = clSz ns o ∧
    clIx ns (o - clIx ns o + x) = x ∧ clId ns (o - clIx ns o + x) = clId ns o := by
  unfold clSz clIx clId SlotsN at *
  split_ifs at hx ⊢ <;> omega

lemma same_base {o o' : ℕ} (ho : o < SlotsN ns) (ho' : o' < SlotsN ns)
    (h : clId ns o = clId ns o') : o - clIx ns o = o' - clIx ns o' := by
  unfold clIx clId SlotsN at *
  split_ifs at h ⊢ <;> omega

lemma compN_comm (o o' : ℕ) : compN ns o o' ↔ compN ns o' o := by
  unfold compN
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun h => h2 h.symm⟩

end Cl

section Rank

variable (ns : List ℕ)

/-- the number of the first `N` positions with the literal `(v, s)` -/
def cnt (v s N : ℕ) : ℕ := (List.range N).countP fun o' => decide (litV ns o' = v ∧ litS ns o' = s)

lemma rankN_eq_cnt (o : ℕ) : rankN ns o = cnt ns (litV ns o) (litS ns o) o := rfl

lemma cnt_succ (v s N : ℕ) :
    cnt ns v s (N + 1) = cnt ns v s N + if litV ns N = v ∧ litS ns N = s then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.countP_append]
  by_cases h : litV ns N = v ∧ litS ns N = s
  · simp [h]
  · simp [h]

lemma cnt_mono (v s : ℕ) {a b : ℕ} (h : a ≤ b) : cnt ns v s a ≤ cnt ns v s b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => rw [cnt_succ]; omega

lemma rank_lt_of_lt {o o' : ℕ} (h : o < o') (hv : litV ns o = litV ns o')
    (hs : litS ns o = litS ns o') : rankN ns o < rankN ns o' := by
  rw [rankN_eq_cnt, rankN_eq_cnt, ← hv, ← hs]
  have h1 := cnt_succ ns (litV ns o) (litS ns o) o
  have h2 := cnt_mono ns (litV ns o) (litS ns o) (show o + 1 ≤ o' by omega)
  simp only [and_self, if_true] at h1
  omega

lemma eq_of_rank {o o' : ℕ} (hv : litV ns o = litV ns o') (hs : litS ns o = litS ns o')
    (hr : rankN ns o = rankN ns o') : o = o' := by
  rcases lt_trichotomy o o' with h | h | h
  · exact absurd hr (rank_lt_of_lt ns h hv hs).ne
  · exact h
  · exact absurd hr (rank_lt_of_lt ns h hv.symm hs.symm).ne'

lemma rank_initial_aux (v s q : ℕ) : ∀ N : ℕ,
    (∃ o' < N, litV ns o' = v ∧ litS ns o' = s ∧ rankN ns o' = q) ↔ q < cnt ns v s N
  | 0 => by simp [cnt]
  | N + 1 => by
    have ih := rank_initial_aux v s q N
    rw [cnt_succ]
    by_cases hP : litV ns N = v ∧ litS ns N = s
    · rw [if_pos hP]
      have hr : rankN ns N = cnt ns v s N := by
        rw [rankN_eq_cnt, hP.1, hP.2]
      constructor
      · rintro ⟨o', ho', h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ho' with h | h
        · have := ih.1 ⟨o', h, h1, h2, h3⟩; omega
        · subst h; omega
      · intro h
        by_cases hq : q < cnt ns v s N
        · obtain ⟨o', ho', h⟩ := ih.2 hq
          exact ⟨o', by omega, h⟩
        · exact ⟨N, by omega, hP.1, hP.2, by omega⟩
    · rw [if_neg hP]
      constructor
      · rintro ⟨o', ho', h1, h2, h3⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ho' with h | h
        · have := ih.1 ⟨o', h, h1, h2, h3⟩; omega
        · subst h; exact absurd ⟨h1, h2⟩ hP
      · intro h
        obtain ⟨o', ho', h⟩ := ih.2 (by omega)
        exact ⟨o', by omega, h⟩

theorem rank_initial (ns : List ℕ) (v s q : ℕ) :
    (∃ o' < SlotsN ns, litV ns o' = v ∧ litS ns o' = s ∧ rankN ns o' = q) ↔
      q < ((List.range (SlotsN ns)).filter fun o' =>
        decide (litV ns o' = v ∧ litS ns o' = s)).length := by
  rw [rank_initial_aux ns v s q, ← List.countP_eq_length_filter]
  rfl

end Rank

/-! ### The port relation -/

section Ports

variable {ns : List ℕ}

lemma litS_le (hs : ShapeF ns) {o : ℕ} (ho : o < SlotsN ns) : litS ns o ≤ 1 := hs.2.2 o ho

theorem isPortRel_RN (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    IsPortRel (SlotsN ns) (RN ns) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro o j o' j' ⟨ho, ho', h | h⟩ <;> omega
  · -- symm
    rintro o j o' j' ⟨ho, ho', h | h⟩
    · obtain ⟨hj, hj', hsum, hmate, hnc⟩ := h
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      have hx : (clIx ns o + j + 1) % clSz ns o < clSz ns o := Nat.mod_lt _ (by omega)
      obtain ⟨_, h2, h3, _⟩ := posOf_facts ns ho hx
      have ho'e : o' = o - clIx ns o + (clIx ns o + j + 1) % clSz ns o := hmate
      refine ⟨ho', ho, Or.inl ⟨hj', hj, by rw [ho'e, h2]; omega, ?_,
        fun h => hnc ((compN_comm ns _ _).1 h)⟩⟩
      unfold mateN
      rw [ho'e, h2, h3]
      have := mod_mate hsz hix hsum
      rw [Nat.add_sub_cancel, this]
      omega
    · obtain ⟨hj, hj4, hj', hj'4, hcomp, hr1, hr2⟩ := h
      exact ⟨ho', ho, Or.inr ⟨hj', hj'4, hj, hj4, (compN_comm ns _ _).1 hcomp, hr2, hr1⟩⟩
  · -- func
    rintro o j o' j' o'' j'' ⟨ho, ho', h1 | h1⟩ ⟨_, ho'', h2 | h2⟩
    · obtain ⟨_, _, hs1, hm1, _⟩ := h1
      obtain ⟨_, _, hs2, hm2, _⟩ := h2
      exact ⟨hm1.trans hm2.symm, by omega⟩
    · omega
    · omega
    · obtain ⟨_, _, _, _, ⟨hv1, hn1⟩, hr1, hr1'⟩ := h1
      obtain ⟨_, _, _, _, ⟨hv2, hn2⟩, hr2, hr2'⟩ := h2
      have a1 := litS_le hs ho
      have a2 := litS_le hs ho'
      have a3 := litS_le hs ho''
      have hoo : o' = o'' :=
        eq_of_rank ns (hv1.symm.trans hv2) (by omega) (by omega)
      exact ⟨hoo, by omega⟩
  · -- ne
    rintro o j o' j' ⟨ho, ho', h | h⟩
    · obtain ⟨hj, hj', hsum, hmate, hnc⟩ := h
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      have := mate_ne hsz hix (show j + 1 < clSz ns o by omega)
      intro he
      apply this
      subst he
      unfold mateN at hmate
      omega
    · rintro he
      subst he
      exact h.2.2.2.2.1.2 rfl
  · -- simple
    rintro o j o' j' j₂ j₂' ⟨ho, ho', h1 | h1⟩ ⟨_, _, h2 | h2⟩
    · obtain ⟨hj, hj', hs1, hm1, _⟩ := h1
      obtain ⟨hj₂, hj₂', hs2, hm2, _⟩ := h2
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      unfold mateN at hm1 hm2
      exact mate_inj hsz hix (by omega) (by omega) (by omega)
    · exact absurd h2.2.2.2.2.1 h1.2.2.2.2
    · exact absurd h1.2.2.2.2.1 h2.2.2.2.2
    · obtain ⟨_, _, _, _, _, hr1, _⟩ := h1
      obtain ⟨_, _, _, _, _, hr2, _⟩ := h2
      omega

/-! ### Unmatched ports -/

lemma coCount_eq (hs : ShapeF ns) {o : ℕ} (ho : o < SlotsN ns) {s' : ℕ} (hs1 : s' ≤ 1)
    (hne : s' ≠ litS ns o) :
    coCountN ns o = ((List.range (SlotsN ns)).filter fun o' =>
        decide (litV ns o' = litV ns o ∧ litS ns o' = s')).length := by
  unfold coCountN
  congr 1
  refine List.filter_congr fun o' ho' => ?_
  have h1 := litS_le hs (List.mem_range.1 ho')
  have h2 := litS_le hs ho
  simp only [decide_eq_decide]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by omega⟩

theorem unmatched_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) {o j : ℕ}
    (ho : o < SlotsN ns) (hj : j < 5) : (¬ ∃ o' j', RN ns o j o' j') ↔ unmatchedN ns o j := by
  unfold unmatchedN
  by_cases h4 : j = 4
  · subst h4
    simp only [true_or, iff_true]
    rintro ⟨o', j', -, -, h | h⟩ <;> omega
  · by_cases hj2 : j < 2
    · -- a mate port
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      have hiff : (∃ o' j', RN ns o j o' j') ↔
          (j + 1 < clSz ns o ∧ ¬ compN ns o (mateN ns o j)) := by
        constructor
        · rintro ⟨o', j', -, -, h | h⟩
          · obtain ⟨_, _, hsum, hm, hnc⟩ := h
            subst hm
            exact ⟨by omega, hnc⟩
          · omega
        · rintro ⟨hj1, hnc⟩
          have hx : (clIx ns o + j + 1) % clSz ns o < clSz ns o := Nat.mod_lt _ (by omega)
          obtain ⟨h1, _, _, _⟩ := posOf_facts ns ho hx
          exact ⟨mateN ns o j, clSz ns o - 2 - j, ho, h1,
            Or.inl ⟨hj2, by omega, by omega, rfl, hnc⟩⟩
      rw [hiff]
      constructor
      · intro h
        right; left
        refine ⟨hj2, ?_⟩
        by_contra hh
        push_neg at hh
        exact h ⟨by omega, hh.2⟩
      · rintro (h | ⟨_, h | h⟩ | ⟨h, _⟩) ⟨h1, h2⟩
        · omega
        · omega
        · exact h2 h
        · omega
    · -- a complement port
      have hj4 : 2 ≤ j ∧ j < 4 := by omega
      have hlo : ¬ (j < 2) := hj2
      have ha := litS_le hs ho
      have hiff : (∃ o' j', RN ns o j o' j') ↔ j - 2 < coCountN ns o := by
        constructor
        · rintro ⟨o', j', -, ho', h | h⟩
          · omega
          · obtain ⟨_, _, _, _, ⟨hv, hn⟩, hr, _⟩ := h
            have hb := litS_le hs ho'
            have := (rank_initial ns (litV ns o) (litS ns o') (j - 2)).1
              ⟨o', ho', hv.symm, rfl, hr⟩
            rw [coCount_eq hs ho hb (Ne.symm hn)]
            exact this
        · intro h
          rw [coCount_eq hs ho (show 1 - litS ns o ≤ 1 by omega) (by omega)] at h
          obtain ⟨o', ho', hv, hsg, hr⟩ :=
            (rank_initial ns (litV ns o) (1 - litS ns o) (j - 2)).2 h
          have hro := (hc.2 o ho).2
          exact ⟨o', rankN ns o + 2, ho, ho', Or.inr ⟨hj4.1, hj4.2, by omega, by omega,
            ⟨hv.symm, by omega⟩, by omega, by omega⟩⟩
      rw [hiff]
      simp only [h4, hlo, false_or, false_and, hj4.1, hj4.2, true_and]
      omega

/-! ### The graph of the positions -/

lemma pair_iff (hs : ShapeF ns) (hc : CondN ns) {o o' : ℕ} (ho : o < SlotsN ns)
    (ho' : o' < SlotsN ns) (hne : o ≠ o') :
    (∃ j j', RN ns o j o' j') ↔ (clId ns o = clId ns o' ∨ compN ns o o') := by
  constructor
  · rintro ⟨j, j', -, -, h | h⟩
    · left
      obtain ⟨hj, hj', hsum, hm, hnc⟩ := h
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      have hx : (clIx ns o + j + 1) % clSz ns o < clSz ns o := Nat.mod_lt _ (by omega)
      obtain ⟨_, _, _, h4⟩ := posOf_facts ns ho hx
      rw [hm]
      exact h4.symm
    · right; exact h.2.2.2.2.1
  · intro h
    by_cases hcomp : compN ns o o'
    · have hr1 := (hc.2 o ho).2
      have hr2 := (hc.2 o' ho').2
      exact ⟨rankN ns o' + 2, rankN ns o + 2, ho, ho', Or.inr ⟨by omega, by omega, by omega,
        by omega, hcomp, by omega, by omega⟩⟩
    · have hid : clId ns o = clId ns o' := h.resolve_right hcomp
      have hb := same_base ns ho ho' hid
      obtain ⟨hsz, hix, hle⟩ := cl_facts ns ho
      obtain ⟨hsz', hix', hle'⟩ := cl_facts ns ho'
      have hszeq : clSz ns o = clSz ns o' := by
        unfold clSz clId SlotsN at *
        split_ifs at hid ⊢ <;> omega
      have ho'e : o' = o - clIx ns o + clIx ns o' := by omega
      have hxt : clIx ns o' ≠ clIx ns o := by
        intro h; apply hne; omega
      obtain ⟨j, hj, hj2, hjm⟩ := port_arith hsz hix (show clIx ns o' < clSz ns o by omega) hxt
      refine ⟨j, clSz ns o - 2 - j, ho, ho', Or.inl ⟨hj, by omega, by omega, ?_, hcomp⟩⟩
      unfold mateN
      rw [hjm]
      exact ho'e

theorem posGraph_RN (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    posGraph (RN ns) (SlotsN ns) = occGraphN ns := by
  ext ⟨o, ho⟩ ⟨o', ho'⟩
  simp only [posGraph, occGraphN, SimpleGraph.fromRel_adj, ne_eq, Fin.mk.injEq]
  have k1 := pair_iff hs hc ho ho'
  have k2 := pair_iff hs hc ho' ho
  by_cases hne : o = o'
  · simp [hne]
  · simp only [hne, not_false_eq_true, true_and]
    rw [k1 hne, k2 (Ne.symm hne), compN_comm ns o' o, eq_comm (a := clId ns o')]

end Ports

end Lax117284Proofs.McisHard.Proved

/-! Statement identity with `McisHard/Defs.lean` (checked up to proof irrelevance). -/

#print axioms Lax117284Proofs.McisHard.Proved.isPortRel_RN
#print axioms Lax117284Proofs.McisHard.Proved.rank_initial
#print axioms Lax117284Proofs.McisHard.Proved.unmatched_iff
#print axioms Lax117284Proofs.McisHard.Proved.posGraph_RN
