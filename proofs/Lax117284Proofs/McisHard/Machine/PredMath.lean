import Lax117284Proofs.McisHard.Defs
import Lax117284Proofs.McisHard.FormulaPorts

/-!
# The mathematics behind the adjacency bit (WP6)

`PEP`, `portAdjM`, `adjM`: `portAdjN (RN ns)` with the two quantified pieces replaced by the predicates
the machine computes; `adjM_iff_adjF` shows they agree with `adjF`.  The only facts about `RN` that are used are
`pe_iff` (proved here) and `unmatched_iff` (the WP3 statement in `Defs`).
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

/-- The positions are different and in one clause or complementary. -/
def PEP (ns : List ℕ) (o o' : ℕ) : Prop := o ≠ o' ∧ (clId ns o = clId ns o' ∨ compN ns o o')

/-- `portAdjN (RN ns)` with `∃ j j', RN` replaced by `PEP` and `¬ ∃ o' j', RN` by `unmatchedN`, written as the case
tree the machine walks. -/
def treeP (ns : List ℕ) (u v : ℕ) : Prop :=
  if u % 36 = 0 then
    (if v % 36 = 0 then PEP ns (u / 36) (v / 36)
     else u / 36 = v / 36 ∧ (v % 36 - 1) % 7 = 0 ∧ unmatchedN ns (u / 36) ((v % 36 - 1) / 7))
  else
    (if v % 36 = 0 then
       u / 36 = v / 36 ∧ (u % 36 - 1) % 7 = 0 ∧ unmatchedN ns (v / 36) ((u % 36 - 1) / 7)
     else
       (u / 36 = v / 36 ∧ (u % 36 - 1) / 7 = (v % 36 - 1) / 7 ∧
          gadAdj ((u % 36 - 1) % 7) ((v % 36 - 1) % 7)) ∨
       ((u % 36 - 1) % 7 = 0 ∧ (v % 36 - 1) % 7 = 0 ∧
          RN ns (u / 36) ((u % 36 - 1) / 7) (v / 36) ((v % 36 - 1) / 7)))

/-- The adjacency of `H`, in the shape the machine computes it. -/
def adjM (ns : List ℕ) (w w' : ℕ) : Prop :=
  w / nOf ns ≠ w' / nOf ns ∧
    (w % nOf ns = w' % nOf ns ∨ (SlotsN ns ≠ 0 ∧ treeP ns (w % nOf ns) (w' % nOf ns)))

/-! ### `PEP` is "some ports are matched" -/

theorem rank_le_one (ns : List ℕ) (hc : CondN ns) {o : ℕ} (ho : o < SlotsN ns) : rankN ns o ≤ 1 :=
  (hc.2 o ho).2

theorem sign_le_one (ns : List ℕ) (hs : ShapeF ns) {o : ℕ} (ho : o < SlotsN ns) :
    ns.getD (4 + 2 * o) 0 ≤ 1 := hs.2.2 o ho

theorem pe_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) {o o' : ℕ} (ho : o < SlotsN ns)
    (ho' : o' < SlotsN ns) : PEP ns o o' ↔ ∃ j j', RN ns o j o' j' := by
  constructor
  · rintro ⟨hne, hcl | hcomp⟩
    · by_cases hcomp : compN ns o o'
      · refine ⟨rankN ns o' + 2, rankN ns o + 2, ho, ho', Or.inr ?_⟩
        have h1 := rank_le_one ns hc ho
        have h2 := rank_le_one ns hc ho'
        exact ⟨by omega, by omega, by omega, by omega, hcomp, by omega, by omega⟩
      · -- the same clause, not complementary: a mate port
        unfold clId at hcl
        unfold SlotsN at ho ho'
        by_cases h1 : o < 2 * ns.getD 1 0 <;> by_cases h2 : o' < 2 * ns.getD 1 0
        · rw [if_pos h1, if_pos h2] at hcl
          refine ⟨0, 0, by unfold SlotsN; omega, by unfold SlotsN; omega, Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
          · unfold clSz; rw [if_pos h1]
          · unfold mateN clIx clSz; simp only [if_pos h1]; omega
        · rw [if_pos h1, if_neg h2] at hcl; omega
        · rw [if_neg h1, if_pos h2] at hcl; omega
        · rw [if_neg h1, if_neg h2] at hcl
          by_cases hj : (o - 2 * ns.getD 1 0) % 3 + 1 = (o' - 2 * ns.getD 1 0) % 3 ∨
              ((o - 2 * ns.getD 1 0) % 3 = 2 ∧ (o' - 2 * ns.getD 1 0) % 3 = 0)
          · refine ⟨0, 1, by unfold SlotsN; omega, by unfold SlotsN; omega,
              Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
            · unfold clSz; rw [if_neg h1]
            · unfold mateN clIx clSz; simp only [if_neg h1]; omega
          · refine ⟨1, 0, by unfold SlotsN; omega, by unfold SlotsN; omega,
              Or.inl ⟨by omega, by omega, ?_, ?_, hcomp⟩⟩
            · unfold clSz; rw [if_neg h1]
            · unfold mateN clIx clSz; simp only [if_neg h1]; omega
    · refine ⟨rankN ns o' + 2, rankN ns o + 2, ho, ho', Or.inr ?_⟩
      have h1 := rank_le_one ns hc ho
      have h2 := rank_le_one ns hc ho'
      exact ⟨by omega, by omega, by omega, by omega, hcomp, by omega, by omega⟩
  · rintro ⟨j, j', -, -, ⟨hj, hj', hsz, hmate, hncomp⟩ | ⟨-, -, -, -, hcomp, -, -⟩⟩
    · refine ⟨?_, Or.inl ?_⟩
      · subst hmate
        unfold mateN clIx clSz at *
        split_ifs at * <;> omega
      · subst hmate
        unfold mateN clIx clSz clId at *
        unfold SlotsN at ho
        split_ifs at * <;> omega
    · refine ⟨?_, Or.inr hcomp⟩
      rintro rfl
      exact hcomp.2 rfl

/-! ### `treeP` and `adjM` -/

theorem treeP_iff (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) {u v : ℕ}
    (hu : u < 36 * SlotsN ns) (hv : v < 36 * SlotsN ns) :
    treeP ns u v ↔ portAdjN (RN ns) u v := by
  have hoN : u / 36 < SlotsN ns := by omega
  have hoN' : v / 36 < SlotsN ns := by omega
  unfold treeP portAdjN
  by_cases hu0 : u % 36 = 0 <;> by_cases hv0 : v % 36 = 0
  · rw [if_pos hu0, if_pos hv0]
    constructor
    · intro h; exact Or.inl ⟨hu0, hv0, (pe_iff ns hs hc hoN hoN').1 h⟩
    · rintro (⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩)
      · exact (pe_iff ns hs hc hoN hoN').2 h
      · exact absurd hv0 h
      · exact absurd hu0 h
      · exact absurd hu0 h
  · rw [if_pos hu0, if_neg hv0]
    have hj : (v % 36 - 1) / 7 < 5 := by omega
    constructor
    · rintro ⟨a, b, c⟩; exact Or.inr (Or.inl ⟨hu0, hv0, a, b, (Proved.unmatched_iff ns hs hc hoN hj).2 c⟩)
    · rintro (⟨-, h, -⟩ | ⟨-, -, a, b, c⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩)
      · exact absurd h hv0
      · exact ⟨a, b, (Proved.unmatched_iff ns hs hc hoN hj).1 c⟩
      · exact absurd hu0 h
      · exact absurd hu0 h
  · rw [if_neg hu0, if_pos hv0]
    have hj : (u % 36 - 1) / 7 < 5 := by omega
    constructor
    · rintro ⟨a, b, c⟩; exact Or.inr (Or.inr (Or.inl ⟨hu0, hv0, a, b, (Proved.unmatched_iff ns hs hc hoN' hj).2 c⟩))
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, -, a, b, c⟩ | ⟨-, h, -⟩)
      · exact absurd h hu0
      · exact absurd h hu0
      · exact ⟨a, b, (Proved.unmatched_iff ns hs hc hoN' hj).1 c⟩
      · exact absurd hv0 h
  · rw [if_neg hu0, if_neg hv0]
    constructor
    · intro h; exact Or.inr (Or.inr (Or.inr ⟨hu0, hv0, h⟩))
    · rintro (⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
      · exact absurd h hu0
      · exact absurd h hu0
      · exact absurd h hv0
      · exact h

theorem adjM_iff_adjF (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (w w' : ℕ) :
    adjM ns w w' ↔ adjF ns w w' := by
  unfold adjM adjF
  refine and_congr_right fun _ => or_congr_right (and_congr_right fun h0 => ?_)
  have hn : nOf ns = SlotsN ns * 36 := by unfold nOf; rw [if_neg h0]
  have hpos : 0 < nOf ns := by rw [hn]; omega
  have h1 := Nat.mod_lt w hpos
  have h2 := Nat.mod_lt w' hpos
  rw [hn] at h1 h2 ⊢
  exact treeP_iff ns hs hc (by omega) (by omega)

end Lax117284Proofs.McisHard.Bit
