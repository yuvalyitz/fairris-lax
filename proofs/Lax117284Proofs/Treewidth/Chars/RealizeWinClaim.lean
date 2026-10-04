import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Seq.Concat
import Lax117284Proofs.Treewidth.Seq.Structure
import Lax117284Proofs.Treewidth.Seq.Symmetry
import Lax117284Proofs.Treewidth.Chars.AnalyzeRT
import Lax117284Proofs.Treewidth.Chars.IntroSetup
import Lax117284Proofs.Treewidth.Chars.MergeIface
import Lax117284Proofs.Treewidth.Chars.MergeFinal
import Lax117284Proofs.Treewidth.Chars.IntroPlansMem

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroWitness` -/

section
/-!
# The witnesses of a typical sequence (work package C4, part 2)

`witnesses a` (`Chars/Alg.lean`) runs the stack algorithm of `Seq.push` on pairs `(value, index)`.
`witnesses_spec`: the indices are strictly increasing, in range, and read off exactly `typical a`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-- The values of `wpush` are `push` of the values. -/
theorem wpush_map_fst : ∀ (st : List (ℕ × ℕ)) (y j : ℕ),
    (wpush st y j).map Prod.fst = push (st.map Prod.fst) y := by
  intro st y j
  induction st with
  | nil => simp [wpush, push, cut]
  | cons p t ih =>
    obtain ⟨x, i⟩ := p
    simp only [wpush, List.map_cons, push, cut]
    by_cases h : t.all (fun z => decide (InR z.1 x y)) = true
    · have h' : ∀ z ∈ t.map Prod.fst, InR z x y := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
        have := List.all_eq_true.1 h p hp
        simpa using this
      rw [h, if_pos h']
      by_cases hte : t = [] ∧ x = y
      · obtain ⟨rfl, rfl⟩ := hte
        simp
      · have h2 : ¬ (t.isEmpty = true ∧ decide (x = y) = true) := by
          intro hh
          apply hte
          exact ⟨List.isEmpty_iff.1 hh.1, by simpa using hh.2⟩
        have h3 : ¬ (t.map Prod.fst = [] ∧ x = y) := by
          intro hh; apply hte
          exact ⟨by simpa using hh.1, hh.2⟩
        rw [if_neg h3]
        simp only [Bool.and_eq_true] at *
        rw [if_neg h2]
        simp
    · have h' : ¬ ∀ z ∈ t.map Prod.fst, InR z x y := by
        intro hh
        apply h
        rw [List.all_eq_true]
        intro p hp
        simpa using hh p.1 (List.mem_map.2 ⟨p, hp, rfl⟩)
      rw [if_neg h', if_neg (by simpa using h)]
      have := ih
      simp only [push] at this
      simp [this]

/-- Every pair of `wpush` is an old pair or the new one. -/
theorem mem_wpush : ∀ (st : List (ℕ × ℕ)) (y j : ℕ), ∀ p ∈ wpush st y j, p ∈ st ∨ p = (y, j) := by
  intro st y j
  induction st with
  | nil => intro p hp; simp [wpush] at hp; exact Or.inr hp
  | cons q t ih =>
    obtain ⟨x, i⟩ := q
    intro p hp
    simp only [wpush] at hp
    split_ifs at hp with h1 h2
    · simp at hp; exact Or.inl (by simp [hp])
    · simp at hp
      rcases hp with rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr rfl
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inl (by simp)
      · rcases ih p hp with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

theorem witnessesAux_map_fst : ∀ (a : List ℕ) (j : ℕ) (st : List (ℕ × ℕ)),
    (witnessesAux j st a).map Prod.fst = a.foldl push (st.map Prod.fst) := by
  intro a
  induction a with
  | nil => intro j st; simp [witnessesAux]
  | cons y a ih =>
    intro j st
    simp only [witnessesAux, List.foldl_cons]
    rw [ih, wpush_map_fst]

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeSeq` -/

section
/-!
# The witnesses cover the exact sequence (work package C5, part 1: sequences)

`witnesses a` (`Chars/Alg.lean`) runs the stack algorithm of `Seq.push` on pairs `(value, index)`.  Here we prove the
*covering property* of the final stack, which is what makes the cuts of `applyPlan` correct:

* `WInv pre st`: the stack `st` (pairs `(value, index)`) after processing `pre` has strictly increasing indices reading
  entries of `pre`, starts at index `0`, every entry of `pre` strictly between two consecutive stack indices lies in the
  interval spanned by their values, and every entry after the last stack index equals its value;
* `witnesses_cover`: the consequences for `w = witnesses a`, `y = typical a` (the three facts `F1`, `F2`, `F3` below).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## intervals -/

theorem InR_of_range {z a b x y : ℕ} (h : InR z a b) (ha : InR a x y) (hb : InR b x y) : InR z x y := by
  unfold InR at *; omega

/-! ## the invariant of the stack of pairs -/

/-- Entries strictly between two consecutive stack indices lie between their values. -/
def GapRel (pre : List ℕ) (p q : ℕ × ℕ) : Prop :=
  ∀ j, p.2 < j → j < q.2 → InR (pre.getD j 0) p.1 q.1

structure WCore (pre : List ℕ) (st : List (ℕ × ℕ)) : Prop where
  vals : ∀ p ∈ st, p.2 < pre.length ∧ pre.getD p.2 0 = p.1
  inc : (st.map Prod.snd).Pairwise (· < ·)
  gap : st.IsChain (GapRel pre)
  tail : ∀ p ∈ st.getLast?, ∀ j, p.2 < j → j < pre.length → pre.getD j 0 = p.1

theorem WCore.nil (pre : List ℕ) : WCore pre [] :=
  ⟨by simp, by simp, List.IsChain.nil, by simp⟩

/-- Everything above the head lies in the interval `[X, y]`, given that the values do. -/
theorem above_range (pre : List ℕ) {X y : ℕ} : ∀ (t : List (ℕ × ℕ)) (x i : ℕ),
    ((x, i) :: t).IsChain (GapRel pre) →
    (∀ p ∈ ((x, i) :: t).getLast?, ∀ j, p.2 < j → j < pre.length → pre.getD j 0 = p.1) →
    (∀ p ∈ t, p.2 < pre.length ∧ pre.getD p.2 0 = p.1) → InR x X y →
    (∀ z ∈ t, InR z.1 X y) → ∀ j, i < j → j < pre.length → InR (pre.getD j 0) X y := by
  intro t
  induction t with
  | nil =>
    intro x i _ htail _ hx _ j hij hjl
    have := htail (x, i) (by simp) j hij hjl
    simp only at this
    rw [this]; exact hx
  | cons q t ih =>
    obtain ⟨x1, i1⟩ := q
    intro x i hg htail hvals hx hin j hij hjl
    rw [List.isChain_cons] at hg
    obtain ⟨hg1, hg2⟩ := hg
    have hrel : GapRel pre (x, i) (x1, i1) := hg1 (x1, i1) (by simp)
    have hx1 : InR x1 X y := hin (x1, i1) (by simp)
    have hv1 := hvals (x1, i1) (by simp)
    rcases lt_trichotomy j i1 with h | h | h
    · have := hrel j hij h
      exact InR_of_range this hx hx1
    · subst h
      rw [hv1.2]; exact hx1
    · have htail' : ∀ p ∈ ((x1, i1) :: t).getLast?, ∀ j, p.2 < j → j < pre.length → pre.getD j 0 = p.1 := by
        intro p hp
        apply htail p
        simpa using hp
      exact ih x1 i1 hg2 htail' (fun p hp => hvals p (by simp [hp])) hx1
        (fun z hz => hin z (by simp [hz])) j h hjl

/-! ## `wpush` preserves the invariant -/

theorem wpush_head (t : List (ℕ × ℕ)) (x i y j : ℕ) : ∀ p ∈ (wpush ((x, i) :: t) y j).head?, p = (x, i) := by
  intro p hp
  simp only [wpush] at hp
  split_ifs at hp <;> simp_all

theorem wpush_ne (st : List (ℕ × ℕ)) (y j : ℕ) : wpush st y j ≠ [] := by
  cases st with
  | nil => simp [wpush]
  | cons q t =>
    obtain ⟨x, i⟩ := q
    simp only [wpush]
    split_ifs <;> simp

theorem getD_append_single_lt {pre : List ℕ} {y j : ℕ} (hj : j < pre.length) :
    (pre ++ [y]).getD j 0 = pre.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem getD_append_single_eq (pre : List ℕ) (y : ℕ) : (pre ++ [y]).getD pre.length 0 = y := by
  simp [List.getD_eq_getElem?_getD]

theorem WCore.push {pre : List ℕ} (y : ℕ) : ∀ {st : List (ℕ × ℕ)}, WCore pre st →
    WCore (pre ++ [y]) (wpush st y pre.length) := by
  intro st
  induction st with
  | nil =>
    intro h
    simp only [wpush]
    refine ⟨?_, by simp, List.IsChain.singleton _, ?_⟩
    · intro p hp; simp at hp; subst hp; simp [getD_append_single_eq]
    · intro p hp j hj hjl; simp at hp; subst hp; simp at hj hjl; omega
  | cons q t ih =>
    obtain ⟨x, i⟩ := q
    intro h
    have hvals := h.vals
    have hinc := h.inc
    have hgap := h.gap
    have htail := h.tail
    have hi : i < pre.length := (hvals (x, i) (by simp)).1
    have hix : pre.getD i 0 = x := (hvals (x, i) (by simp)).2
    have hlen : (pre ++ [y]).length = pre.length + 1 := by simp
    have hgetD : ∀ j, j < pre.length → (pre ++ [y]).getD j 0 = pre.getD j 0 := fun j hj =>
      getD_append_single_lt hj
    have hgetLast : (pre ++ [y]).getD pre.length 0 = y := getD_append_single_eq pre y
    simp only [wpush]
    by_cases hall : (t.all fun z => decide (InR z.1 x y)) = true
    · have hin : ∀ z ∈ t, InR z.1 x y := by
        intro z hz
        have := List.all_eq_true.1 hall z hz
        simpa using this
      have hrange : ∀ j, i < j → j < pre.length → InR (pre.getD j 0) x y :=
        above_range pre t x i hgap htail (fun p hp => hvals p (by simp [hp])) (InR.left x y) hin
      rw [if_pos hall]
      by_cases hsp : (t.isEmpty && decide (x = y)) = true
      · rw [if_pos hsp]
        have ht : t = [] := by simpa using (Bool.and_eq_true_iff.1 hsp).1
        have hxy : x = y := by simpa using (Bool.and_eq_true_iff.1 hsp).2
        subst ht; subst hxy
        refine ⟨?_, by simp, List.IsChain.singleton _, ?_⟩
        · intro p hp; simp at hp; subst hp
          exact ⟨by omega, by rw [hgetD i hi]; exact hix⟩
        · intro p hp j hj hjl
          simp at hp; subst hp
          simp only at hj
          rw [hlen] at hjl
          by_cases hj' : j < pre.length
          · rw [hgetD j hj']
            exact htail (x, i) (by simp) j hj hj'
          · have : j = pre.length := by omega
            subst this
            rw [hgetLast]
      · rw [if_neg hsp]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ⟨by omega, by rw [hgetD i hi]; exact hix⟩
          · exact ⟨by omega, hgetLast⟩
        · simp only [List.map_cons, List.map_nil, List.pairwise_cons, List.mem_singleton, forall_eq,
            List.pairwise_singleton, and_true]
          simp [hi]
        · rw [List.isChain_cons_cons]
          refine ⟨?_, List.IsChain.singleton _⟩
          intro j hij hjl
          simp only at hij hjl
          rw [hgetD j hjl]
          exact hrange j hij hjl
        · intro p hp j hj hjl
          simp at hp; subst hp
          simp at hj hjl; omega
    · rw [if_neg hall]
      have ht0 : t ≠ [] := by
        rintro rfl; simp at hall
      obtain ⟨q1, t1, rfl⟩ := List.exists_cons_of_ne_nil ht0
      obtain ⟨x1, i1⟩ := q1
      have h' : WCore pre ((x1, i1) :: t1) := by
        refine ⟨fun p hp => hvals p (by simp [hp]), ?_, (List.isChain_cons.1 hgap).2, ?_⟩
        · have hinc' : (i :: (i1 :: t1.map Prod.snd)).Pairwise (· < ·) := hinc
          exact (List.pairwise_cons.1 hinc').2
        · intro p hp
          apply htail p
          simpa [List.getLast?_cons_cons] using hp
      have IH := ih h'
      -- the new tail
      have hne := wpush_ne ((x1, i1) :: t1) y pre.length
      obtain ⟨z0, l0, hl0⟩ := List.exists_cons_of_ne_nil hne
      have hhead : z0 = (x1, i1) := by
        have := wpush_head t1 x1 i1 y pre.length z0 (by rw [hl0]; simp)
        exact this
      have hg1 : GapRel pre (x, i) (x1, i1) := ((List.isChain_cons.1 hgap).1 (x1, i1) (by simp))
      have hinc' : (i :: (i1 :: t1.map Prod.snd)).Pairwise (· < ·) := hinc
      have hi1 : i < i1 := (List.pairwise_cons.1 hinc').1 i1 (by simp)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨by omega, by rw [hgetD i hi]; exact hix⟩
        · exact IH.vals p hp
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨?_, IH.inc⟩
        intro b hb
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
        rcases mem_wpush ((x1, i1) :: t1) y pre.length p hp with h2 | h2
        · exact (List.pairwise_cons.1 hinc').1 p.2 (List.mem_map.2 ⟨p, h2, rfl⟩)
        · rw [h2]; exact hi
      · rw [List.isChain_cons]
        refine ⟨?_, IH.gap⟩
        intro z hz
        rw [hl0] at hz
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
        subst hz
        rw [hhead]
        intro j hij hjl
        simp only at hij hjl
        rw [hgetD j (by have := (hvals (x1, i1) (by simp)).1; simp only at this; omega)]
        exact hg1 j hij hjl
      · intro p hp
        have : ((x, i) :: wpush ((x1, i1) :: t1) y pre.length).getLast? =
            (wpush ((x1, i1) :: t1) y pre.length).getLast? := by
          rw [hl0]; simp [List.getLast?_cons_cons]
        rw [this] at hp
        exact IH.tail p hp

theorem WCore.witnessesAux : ∀ (a pre : List ℕ) (st : List (ℕ × ℕ)), WCore pre st →
    WCore (pre ++ a) (witnessesAux pre.length st a) := by
  intro a
  induction a with
  | nil => intro pre st h; simpa [Lax117284Proofs.Treewidth.Chars.witnessesAux] using h
  | cons y a ih =>
    intro pre st h
    have := ih (pre ++ [y]) (wpush st y pre.length) (h.push y)
    simp only [Lax117284Proofs.Treewidth.Chars.witnessesAux, List.length_append, List.length_cons, List.length_nil] at this ⊢
    simpa [List.append_assoc] using this


/-! ## blocks of the witnesses and the upper index `ub` -/

section Blocks

variable {m : ℕ} {W Y : ℕ → ℕ}

theorem exists_block (hm : 0 < m) (hW0 : W 0 = 0) (j : ℕ) :
    ∃ f, f < m ∧ W f ≤ j ∧ (f + 1 < m → j < W (f + 1)) := by
  classical
  have hf0 : W (Nat.findGreatest (fun g => W g ≤ j) (m - 1)) ≤ j :=
    Nat.findGreatest_spec (P := fun g => W g ≤ j) (Nat.zero_le _) (by simp [hW0])
  have hfle : Nat.findGreatest (fun g => W g ≤ j) (m - 1) ≤ m - 1 := Nat.findGreatest_le _
  refine ⟨Nat.findGreatest (fun g => W g ≤ j) (m - 1), by omega, hf0, fun h => ?_⟩
  by_contra hcon
  have := Nat.findGreatest_is_greatest (P := fun g => W g ≤ j) (n := m - 1)
    (k := Nat.findGreatest (fun g => W g ≤ j) (m - 1) + 1) (by omega) (by omega)
  exact this (by omega)

/-- The block of `j`: the last index `f` with `W f ≤ j`. -/
noncomputable def blk (m : ℕ) (W : ℕ → ℕ) (j : ℕ) : ℕ :=
  if h : ∃ f, f < m ∧ W f ≤ j ∧ (f + 1 < m → j < W (f + 1)) then Classical.choose h else 0

theorem block_unique (hmono : ∀ f g, f < g → g < m → W f < W g) {j f f' : ℕ}
    (h : f < m ∧ W f ≤ j ∧ (f + 1 < m → j < W (f + 1)))
    (h' : f' < m ∧ W f' ≤ j ∧ (f' + 1 < m → j < W (f' + 1))) : f = f' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.1
    have h1 := h.2.2 (by omega)
    have h3 : W (f + 1) ≤ W f' := by
      rcases Nat.eq_or_lt_of_le (show f + 1 ≤ f' by omega) with e | e
      · rw [e]
      · exact (hmono (f + 1) f' e h'.1).le
    have := h'.2.1
    omega
  · have := h.1
    have h1 := h'.2.2 (by omega)
    have h3 : W (f' + 1) ≤ W f := by
      rcases Nat.eq_or_lt_of_le (show f' + 1 ≤ f by omega) with e | e
      · rw [e]
      · exact (hmono (f' + 1) f e h.1).le
    have := h.2.1
    omega

theorem blk_spec (hm : 0 < m) (hW0 : W 0 = 0) (j : ℕ) :
    blk m W j < m ∧ W (blk m W j) ≤ j ∧ (blk m W j + 1 < m → j < W (blk m W j + 1)) := by
  have h := exists_block hm hW0 j
  unfold blk
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem blk_eq (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) {j f : ℕ}
    (h : f < m ∧ W f ≤ j ∧ (f + 1 < m → j < W (f + 1))) : blk m W j = f :=
  block_unique hmono (blk_spec hm hW0 j) h

/-- The upper index: `j` is charged to the larger of the two witnesses around it. -/
noncomputable def ub (m : ℕ) (W Y : ℕ → ℕ) (j : ℕ) : ℕ :=
  if W (blk m W j) < j ∧ blk m W j + 1 < m ∧ Y (blk m W j) < Y (blk m W j + 1) then blk m W j + 1 else blk m W j

theorem ub_lt (hm : 0 < m) (hW0 : W 0 = 0) (j : ℕ) : ub m W Y j < m := by
  have h := blk_spec hm hW0 j
  unfold ub
  split_ifs with hc
  · exact hc.2.1
  · exact h.1

theorem ub_wit (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) {f : ℕ} (hf : f < m) :
    ub m W Y (W f) = f := by
  have hb : blk m W (W f) = f := blk_eq hm hW0 hmono ⟨hf, le_rfl, fun h => hmono f (f + 1) (by omega) h⟩
  unfold ub
  rw [hb]
  split_ifs with hc
  · exact absurd hc.1 (lt_irrefl _)
  · rfl

theorem ub_gap_rise (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) {f j : ℕ}
    (hf : f + 1 < m) (h1 : W f < j) (h2 : j < W (f + 1)) (hr : Y f < Y (f + 1)) : ub m W Y j = f + 1 := by
  have hb : blk m W j = f := blk_eq hm hW0 hmono ⟨by omega, h1.le, fun _ => h2⟩
  unfold ub
  rw [hb, if_pos ⟨h1, hf, hr⟩]

theorem ub_gap_fall (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) {f j : ℕ}
    (hf : f < m) (h1 : W f ≤ j) (h2 : f + 1 < m → j < W (f + 1)) (hr : ¬ (Y f < Y (f + 1))) :
    ub m W Y j = f := by
  have hb : blk m W j = f := blk_eq hm hW0 hmono ⟨hf, h1, h2⟩
  unfold ub
  rw [hb, if_neg]
  rintro ⟨-, -, h⟩
  exact hr h

theorem ub_last (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) {j : ℕ}
    (h1 : W (m - 1) ≤ j) : ub m W Y j = m - 1 := by
  have hb : blk m W j = m - 1 := blk_eq hm hW0 hmono ⟨by omega, h1, fun h => by omega⟩
  unfold ub
  rw [hb, if_neg]
  rintro ⟨-, h, -⟩
  omega

/-- The step property of `ub`. -/
theorem ub_step (hm : 0 < m) (hW0 : W 0 = 0) (hmono : ∀ f g, f < g → g < m → W f < W g) (j : ℕ) :
    ub m W Y j ≤ ub m W Y (j + 1) ∧ ub m W Y (j + 1) ≤ ub m W Y j + 1 := by
  obtain ⟨hb1, hb2, hb3⟩ := blk_spec hm hW0 j
  set b := blk m W j with hb
  by_cases hnext : b + 1 < m ∧ W (b + 1) = j + 1
  · -- `j + 1` is a witness
    have e : ub m W Y (j + 1) = b + 1 := by
      rw [← hnext.2]; exact ub_wit hm hW0 hmono hnext.1
    rw [e]
    have : ub m W Y j ≤ b + 1 := by
      unfold ub; rw [← hb]; split_ifs <;> omega
    have : b ≤ ub m W Y j := by
      unfold ub; rw [← hb]; split_ifs <;> omega
    omega
  · -- same block
    have hb' : blk m W (j + 1) = b := by
      apply blk_eq hm hW0 hmono
      refine ⟨hb1, by omega, fun h => ?_⟩
      have := hb3 h
      by_contra hcon
      apply hnext
      exact ⟨h, by omega⟩
    have hu : ∀ i, ub m W Y i = if W (blk m W i) < i ∧ blk m W i + 1 < m ∧ Y (blk m W i) < Y (blk m W i + 1)
        then blk m W i + 1 else blk m W i := fun i => rfl
    rw [hu j, hu (j + 1), hb', ← hb]
    split_ifs <;> omega

end Blocks


/-! ## segments of `s` are dominated by the corresponding window of `y` -/

theorem slice_cons {y : List ℕ} {i n : ℕ} (hi : i < n + 1) (hn : n < y.length) :
    (y.take (n + 1)).drop i = y.getD i 0 :: (y.take (n + 1)).drop (i + 1) := by
  have h1 : i < (y.take (n + 1)).length := by simp; omega
  rw [List.drop_eq_getElem_cons h1]
  congr 1
  · rw [List.getElem_take, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

theorem ext_of_idx (y : List ℕ) (u : ℕ → ℕ) : ∀ (n p : ℕ), (∀ j, p ≤ j → j ≤ p + n → u j < y.length) →
    (∀ j, p ≤ j → j < p + n → u j ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1) →
    u p ≤ u (p + n) ∧
      Ext ((y.take (u (p + n) + 1)).drop (u p)) ((List.range' p (n + 1)).map (fun j => y.getD (u j) 0)) := by
  intro n
  induction n with
  | zero =>
    intro p hlt _
    have hp := hlt p le_rfl (by omega)
    refine ⟨le_rfl, ?_⟩
    simp only [Nat.add_zero, List.range'_one, List.map_cons, List.map_nil]
    rw [slice_cons (by omega) hp]
    have : (y.take (u p + 1)).drop (u p + 1) = [] := by simp
    rw [this]
    exact Ext.refl _
  | succ n ih =>
    intro p hlt hst
    have hstep := hst p le_rfl (by omega)
    obtain ⟨hle, hext⟩ := ih (p + 1) (fun j h1 h2 => hlt j (by omega) (by omega))
      (fun j h1 h2 => hst j (by omega) (by omega))
    have e : p + 1 + n = p + (n + 1) := by omega
    rw [e] at hle hext
    have hup : u (p + (n + 1)) < y.length := hlt _ (by omega) (by omega)
    refine ⟨by omega, ?_⟩
    rw [List.range'_succ, List.map_cons]
    have hi : u p < u (p + (n + 1)) + 1 := by omega
    rw [slice_cons hi hup]
    rw [ext_cons_cons]
    refine ⟨rfl, ?_⟩
    rcases Nat.eq_or_lt_of_le hstep.1 with h | h
    · left
      rw [← slice_cons hi hup]
      rw [h]; exact hext
    · right
      have : u (p + 1) = u p + 1 := by omega
      rw [this] at hext
      exact hext

theorem seg_eq_map (s : List ℕ) {p q : ℕ} (hpq : p ≤ q) (hq : q < s.length) :
    (s.drop p).take (q + 1 - p) = (List.range' p (q + 1 - p)).map (fun j => s.getD j 0) := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp only [List.length_take, List.length_drop, List.length_map, List.length_range'] at h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range',
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    simp [Nat.add_comm, Nat.one_mul]

theorem seg_dom (s y : List ℕ) (u : ℕ → ℕ)
    (h1 : ∀ j, j < s.length → s.getD j 0 ≤ y.getD (u j) 0 ∧ u j < y.length)
    (h2 : ∀ j, j + 1 < s.length → u j ≤ u (j + 1) ∧ u (j + 1) ≤ u j + 1) :
    ∀ p q, p ≤ q → q < s.length →
      Dom (typical ((s.drop p).take (q + 1 - p))) ((y.take (u q + 1)).drop (u p)) := by
  intro p q hpq hq
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hpq
  obtain ⟨hle, hext⟩ := ext_of_idx y u n p (fun j hj hj' => (h1 j (by omega)).2)
    (fun j hj hj' => h2 j (by omega))
  refine Dom.trans (domEquiv_typical _).1 ?_
  refine ⟨_, _, Ext.refl _, hext, ?_⟩
  rw [seg_eq_map s (by omega) hq]
  have : p + n + 1 - p = n + 1 := by omega
  rw [this]
  rw [LeSeq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  apply List.forall₂_same.2
  intro j hj
  rw [List.mem_range'_1] at hj
  exact (h1 j (by omega)).1


/-! ## the covering property of `witnesses a` -/

theorem head_witnessesAux (a : List ℕ) : ∀ (j : ℕ) (st : List (ℕ × ℕ)) (p : ℕ × ℕ), st.head? = some p →
    (witnessesAux j st a).head? = some p := by
  induction a with
  | nil => intro j st p h; simpa [Lax117284Proofs.Treewidth.Chars.witnessesAux] using h
  | cons y a ih =>
    intro j st p h
    simp only [Lax117284Proofs.Treewidth.Chars.witnessesAux]
    apply ih
    obtain ⟨q, t, rfl⟩ : ∃ q t, st = q :: t := by
      cases st with
      | nil => simp at h
      | cons q t => exact ⟨q, t, rfl⟩
    obtain ⟨x, i⟩ := q
    have := wpush_head t x i y j
    have hne := wpush_ne ((x, i) :: t) y j
    obtain ⟨z0, l0, hl0⟩ := List.exists_cons_of_ne_nil hne
    have hz : z0 = (x, i) := this z0 (by rw [hl0]; simp)
    rw [hl0, hz]
    simp at h
    simp [h]

theorem witnessesAux_zero_cons (y0 : ℕ) (a' : List ℕ) :
    witnessesAux 0 [] (y0 :: a') = witnessesAux 1 [(y0, 0)] a' := by
  simp [Lax117284Proofs.Treewidth.Chars.witnessesAux, wpush]

theorem witnessesAux_head0 (y0 : ℕ) (a' : List ℕ) :
    (witnessesAux 0 [] (y0 :: a')).head? = some (y0, 0) := by
  rw [witnessesAux_zero_cons]
  exact head_witnessesAux a' 1 [(y0, 0)] (y0, 0) (by simp)

structure WCover (a w y : List ℕ) : Prop where
  len : w.length = y.length
  pos : a ≠ [] → 0 < w.length
  wit : ∀ f, f < w.length → w.getD f 0 < a.length ∧ a.getD (w.getD f 0) 0 = y.getD f 0
  mono : ∀ f g, f < g → g < w.length → w.getD f 0 < w.getD g 0
  w0 : a ≠ [] → w.getD 0 0 = 0
  gap : ∀ f, f + 1 < w.length → ∀ j, w.getD f 0 < j → j < w.getD (f + 1) 0 →
    InR (a.getD j 0) (y.getD f 0) (y.getD (f + 1) 0)
  tail : ∀ j, w.getD (w.length - 1) 0 < j → j < a.length → a.getD j 0 = y.getD (w.length - 1) 0

theorem witnesses_cover (a : List ℕ) : WCover a (witnesses a) (typical a) := by
  set st := witnessesAux 0 [] a with hst
  have hcore : WCore ([] ++ a) st := WCore.witnessesAux a [] [] (WCore.nil [])
  simp only [List.nil_append] at hcore
  have hw : witnesses a = st.map Prod.snd := rfl
  have hy : typical a = st.map Prod.fst := by
    have := witnessesAux_map_fst a 0 []
    simp only [List.map_nil] at this
    rw [← hst] at this
    exact this.symm
  have hlen : (witnesses a).length = (typical a).length := by rw [hw, hy]; simp
  have hgetw : ∀ f (hf : f < st.length), (witnesses a).getD f 0 = (st[f]'hf).2 := by
    intro f hf
    rw [hw, List.getD_eq_getElem?_getD]
    simp [hf]
  have hgety : ∀ f (hf : f < st.length), (typical a).getD f 0 = (st[f]'hf).1 := by
    intro f hf
    rw [hy, List.getD_eq_getElem?_getD]
    simp [hf]
  have hlenst : (witnesses a).length = st.length := by rw [hw]; simp
  have hstne : a ≠ [] → st ≠ [] := by
    intro ha
    obtain ⟨y0, a', rfl⟩ := List.exists_cons_of_ne_nil ha
    have hh := witnessesAux_head0 y0 a'
    intro h
    rw [hst] at h
    rw [h] at hh; simp at hh
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ha
    rw [hlenst]; exact List.length_pos_of_ne_nil (hstne ha)
  · intro f hf
    have hf' : f < st.length := by omega
    have hv := hcore.vals (st[f]) (List.getElem_mem hf')
    rw [hgetw f hf', hgety f hf']
    exact ⟨hv.1, hv.2⟩
  · intro f g hfg hg
    have hg' : g < st.length := by omega
    have := hcore.inc
    rw [List.pairwise_iff_getElem] at this
    rw [hgetw f (by omega), hgetw g hg']
    have h := this f g (by simpa using (by omega : f < st.length)) (by simpa using hg') hfg
    rw [List.getElem_map, List.getElem_map] at h
    exact h
  · intro ha
    obtain ⟨y0, a', rfl⟩ := List.exists_cons_of_ne_nil ha
    have hh := witnessesAux_head0 y0 a'
    rw [hw]
    obtain ⟨z0, l0, hl0⟩ : ∃ z0 l0, st = z0 :: l0 := by
      cases h : st with
      | nil => rw [hst] at h; rw [h] at hh; simp at hh
      | cons z l => exact ⟨z, l, rfl⟩
    rw [hst] at hl0
    rw [hl0] at hh
    simp at hh
    subst hh
    rw [hst, hl0]
    simp
  · intro f hf j h1 h2
    have hf' : f + 1 < st.length := by omega
    have hch := hcore.gap
    rw [List.isChain_iff_getElem] at hch
    have := hch f hf' j (by rw [hgetw f (by omega)] at h1; simpa using h1)
      (by rw [hgetw (f + 1) hf'] at h2; simpa using h2)
    rw [hgety f (by omega), hgety (f + 1) hf']
    simpa using this
  · intro j h1 h2
    have ha : a ≠ [] := by rintro rfl; simp at h2
    have hne := hstne ha
    have hl : st.length - 1 < st.length := by have := List.length_pos_of_ne_nil hne; omega
    have := hcore.tail (st[st.length - 1]) (by
      simp [List.getLast?_eq_getElem?, hl])
    rw [hlenst] at h1 ⊢
    rw [hgetw _ hl] at h1
    rw [hgety _ hl]
    simpa using this j (by simpa using h1) (by simpa using h2)


/-! ## the index map of a sequence and its witnesses -/

/-- The `f`-th witness / typical entry of `a`. -/
def Wf (a : List ℕ) (f : ℕ) : ℕ := (witnesses a).getD f 0
def Yf (a : List ℕ) (f : ℕ) : ℕ := (typical a).getD f 0

/-- `ubA a j`: the (upper) index of `typical a` charged for the position `j` of `a`. -/
noncomputable def ubA (a : List ℕ) (j : ℕ) : ℕ := ub (witnesses a).length (Wf a) (Yf a) j

section UbA

variable {a : List ℕ}

theorem ubA_facts (ha : a ≠ []) :
    (∀ j, j < a.length → a.getD j 0 ≤ (typical a).getD (ubA a j) 0 ∧ ubA a j < (typical a).length) ∧
    (∀ j, j + 1 < a.length → ubA a j ≤ ubA a (j + 1) ∧ ubA a (j + 1) ≤ ubA a j + 1) := by
  have C := witnesses_cover a
  have hm := C.pos ha
  have hW0 : Wf a 0 = 0 := C.w0 ha
  have hmono : ∀ f g, f < g → g < (witnesses a).length → Wf a f < Wf a g := C.mono
  refine ⟨fun j hj => ⟨?_, ?_⟩, fun j _ => ub_step (W := Wf a) (Y := Yf a) hm hW0 hmono j⟩
  · obtain ⟨hb1, hb2, hb3⟩ := blk_spec (W := Wf a) hm hW0 j
    unfold ubA ub
    set b := blk (witnesses a).length (Wf a) j with hb
    by_cases hlt : Wf a b < j
    · by_cases hb' : b + 1 < (witnesses a).length
      · have hg := C.gap b hb' j hlt (hb3 hb')
        by_cases hr : Yf a b < Yf a (b + 1)
        · rw [if_pos ⟨hlt, hb', hr⟩]
          unfold InR at hg; unfold Yf at hr; omega
        · rw [if_neg (by rintro ⟨-, -, h⟩; exact hr h)]
          unfold InR at hg; unfold Yf at hr; omega
      · rw [if_neg (by rintro ⟨-, h, -⟩; exact hb' h)]
        have hbm : b = (witnesses a).length - 1 := by omega
        have := C.tail j (by rw [← hbm]; exact hlt) hj
        rw [hbm]; exact this.le
    · have hle : Wf a b = j := by omega
      rw [if_neg (by rintro ⟨h, -, -⟩; exact hlt h)]
      have := (C.wit b hb1).2
      rw [← hle]
      exact this.le
  · have hu := ub_lt (W := Wf a) (Y := Yf a) hm hW0 j
    unfold ubA
    rw [← C.len] at *
    exact hu

theorem ubA_zero (ha : a ≠ []) : ubA a 0 = 0 := by
  have C := witnesses_cover a
  have hm := C.pos ha
  have hW0 : Wf a 0 = 0 := C.w0 ha
  have := ub_wit (W := Wf a) (Y := Yf a) hm hW0 C.mono hm
  unfold ubA
  rw [hW0] at this; exact this

theorem ubA_wit (ha : a ≠ []) {f : ℕ} (hf : f < (witnesses a).length) : ubA a (Wf a f) = f := by
  have C := witnesses_cover a
  exact ub_wit (W := Wf a) (Y := Yf a) (C.pos ha) (C.w0 ha) C.mono hf

theorem ubA_last (ha : a ≠ []) : ubA a (a.length - 1) = (witnesses a).length - 1 := by
  have C := witnesses_cover a
  have hm := C.pos ha
  have h1 := (C.wit ((witnesses a).length - 1) (by omega)).1
  exact ub_last (W := Wf a) (Y := Yf a) hm (C.w0 ha) C.mono (by
    show Wf a _ ≤ _
    unfold Wf; omega)

/-- The position of the last entry of the left part of a cut of the second type after `f`. -/
def leftEnd2 (a : List ℕ) (f : ℕ) : ℕ :=
  if Yf a f < Yf a (f + 1) then Wf a f else Wf a (f + 1) - 1

theorem ubA_leftEnd2 (ha : a ≠ []) {f : ℕ} (hf : f + 1 < (witnesses a).length) :
    ubA a (leftEnd2 a f) = f ∧ ubA a (leftEnd2 a f + 1) = f + 1 := by
  have C := witnesses_cover a
  have hm := C.pos ha
  have hW0 : Wf a 0 = 0 := C.w0 ha
  have hmono : ∀ f g, f < g → g < (witnesses a).length → Wf a f < Wf a g := C.mono
  have hlt := hmono f (f + 1) (by omega) hf
  unfold leftEnd2
  by_cases hr : Yf a f < Yf a (f + 1)
  · rw [if_pos hr]
    refine ⟨ubA_wit ha (by omega), ?_⟩
    rcases Nat.eq_or_lt_of_le (show Wf a f + 1 ≤ Wf a (f + 1) by omega) with e | e
    · rw [e]; exact ubA_wit ha hf
    · exact ub_gap_rise (W := Wf a) (Y := Yf a) hm hW0 hmono hf (by omega) e hr
  · rw [if_neg hr]
    have hpos : 0 < Wf a (f + 1) := by omega
    constructor
    · exact ub_gap_fall (W := Wf a) (Y := Yf a) hm hW0 hmono (by omega) (by omega)
        (fun _ => by omega) hr
    · have : Wf a (f + 1) - 1 + 1 = Wf a (f + 1) := by omega
      rw [this]; exact ubA_wit ha hf

end UbA


/-! ## cuts in coordinates -/

/-- The cut is valid for `y = typical s`. -/
def CT.Cut.Valid (m : ℕ) : Cut → Prop
  | .t1 f => f < m
  | .t2 f => f + 1 < m

/-- The left part of a cut of `s` is `s.take (cA s c)`. -/
def cA (s : List ℕ) : Cut → ℕ
  | .t1 f => Wf s f + 1
  | .t2 f => leftEnd2 s f + 1

/-- The right part of a cut of `s` is `s.drop (cB s c)`. -/
def cB (s : List ℕ) : Cut → ℕ
  | .t1 f => Wf s f
  | .t2 f => leftEnd2 s f + 1

/-- The window of `y` matching the right part starts at `cLo c`. -/
def cLo : Cut → ℕ
  | .t1 f => f
  | .t2 f => f + 1

/-- The window of `y` matching the left part ends at `cHi c`. -/
def cHi : Cut → ℕ
  | .t1 f => f
  | .t2 f => f

section CutCoords

variable {s : List ℕ}

theorem Wf_lt (hs : s ≠ []) {f : ℕ} (hf : f < (witnesses s).length) : Wf s f < s.length :=
  ((witnesses_cover s).wit f hf).1

theorem cA_pos (c : Cut) : 1 ≤ cA s c := by cases c <;> simp [cA]

theorem cB_le_cA (c : Cut) : cB s c ≤ cA s c ∧ cA s c ≤ cB s c + 1 := by
  cases c <;> simp [cA, cB]

theorem leftEnd2_bounds (hs : s ≠ []) {f : ℕ} (hf : f + 1 < (witnesses s).length) :
    Wf s f ≤ leftEnd2 s f ∧ leftEnd2 s f + 1 ≤ Wf s (f + 1) := by
  have C := witnesses_cover s
  have hlt : Wf s f < Wf s (f + 1) := C.mono f (f + 1) (by omega) hf
  unfold leftEnd2
  split_ifs <;> omega

theorem cA_le (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) : cA s c ≤ s.length := by
  cases c with
  | t1 f =>
    have := Wf_lt hs (f := f) hc; simp only [cA]; omega
  | t2 f =>
    have h1 := Wf_lt hs (f := f + 1) hc
    have h2 := leftEnd2_bounds hs hc
    simp only [cA]; omega

theorem cB_lt (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) : cB s c < s.length := by
  cases c with
  | t1 f =>
    have := Wf_lt hs (f := f) hc; simp only [cB]; omega
  | t2 f =>
    have h1 := Wf_lt hs (f := f + 1) hc
    have h2 := leftEnd2_bounds hs hc
    simp only [cB]; omega

theorem ub_cB (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) : ubA s (cB s c) = cLo c := by
  cases c with
  | t1 f => exact ubA_wit hs hc
  | t2 f => exact (ubA_leftEnd2 hs hc).2

theorem ub_cA (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) : ubA s (cA s c - 1) = cHi c := by
  cases c with
  | t1 f =>
    show ubA s (Wf s f + 1 - 1) = f
    rw [Nat.add_sub_cancel]; exact ubA_wit hs hc
  | t2 f =>
    show ubA s (leftEnd2 s f + 1 - 1) = f
    rw [Nat.add_sub_cancel]; exact (ubA_leftEnd2 hs hc).1

/-- The left part of a cut. -/
theorem dom_left (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) :
    Dom (typical (s.take (cA s c))) ((typical s).take (cHi c + 1)) := by
  have hF := ubA_facts hs
  have h := seg_dom s (typical s) (ubA s) hF.1 hF.2 0 (cA s c - 1) (Nat.zero_le _)
    (by have := cA_le hs hc; have := cA_pos (s := s) c; omega)
  rw [ubA_zero hs, ub_cA hs hc] at h
  have e : cA s c - 1 + 1 - 0 = cA s c := by have := cA_pos (s := s) c; omega
  rw [e, List.drop_zero, List.drop_zero] at h
  exact h

/-- The right part of a cut. -/
theorem dom_right (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) :
    Dom (typical (s.drop (cB s c))) ((typical s).drop (cLo c)) := by
  have hF := ubA_facts hs
  have hb := cB_lt hs hc
  have h := seg_dom s (typical s) (ubA s) hF.1 hF.2 (cB s c) (s.length - 1) (by omega) (by omega)
  rw [ubA_last hs, ub_cB hs hc] at h
  have e : s.length - 1 + 1 - cB s c = s.length - cB s c := by omega
  have e2 : (witnesses s).length - 1 + 1 = (typical s).length := by
    have := (witnesses_cover s).len; have := (witnesses_cover s).pos hs; omega
  rw [e, List.take_of_length_le (by simp)] at h
  rw [e2, List.take_length] at h
  exact h

/-- The part between two cuts: the pre-cut `c1` and the end-cut `c2` (`lo(c1) ≤ hi(c2)`). -/
theorem dom_mid (hs : s ≠ []) {c1 c2 : Cut} (h1 : c1.Valid (witnesses s).length)
    (h2 : c2.Valid (witnesses s).length) (hle : cLo c1 ≤ cHi c2) :
    cB s c1 + 1 ≤ cA s c2 ∧
    Dom (typical ((s.drop (cB s c1)).take (cA s c2 - cB s c1))) (((typical s).take (cHi c2 + 1)).drop (cLo c1)) := by
  have C := witnesses_cover s
  have hF := ubA_facts hs
  have hbo : cB s c1 ≤ Wf s (cLo c1) := by
    cases c1 with
    | t1 f => simp [cB, cLo]
    | t2 f => have := leftEnd2_bounds hs h1; simp only [cB, cLo]; omega
  have hao : Wf s (cHi c2) + 1 ≤ cA s c2 := by
    cases c2 with
    | t1 f => simp [cA, cHi]
    | t2 f => have := leftEnd2_bounds hs h2; simp only [cA, cHi]; omega
  have hmon : Wf s (cLo c1) ≤ Wf s (cHi c2) := by
    rcases Nat.eq_or_lt_of_le hle with e | e
    · rw [e]
    · have hlo : cLo c1 < (witnesses s).length := by
        cases c1 <;> simp [cLo, Cut.Valid] at h1 ⊢ <;> omega
      have hhi : cHi c2 < (witnesses s).length := by
        cases c2 <;> simp [cHi, Cut.Valid] at h2 ⊢ <;> omega
      exact (C.mono _ _ e hhi).le
  have hlt : cB s c1 + 1 ≤ cA s c2 := by omega
  refine ⟨hlt, ?_⟩
  have hq : cA s c2 - 1 < s.length := by have := cA_le hs h2; omega
  have h := seg_dom s (typical s) (ubA s) hF.1 hF.2 (cB s c1) (cA s c2 - 1) (by omega) hq
  rw [ub_cB hs h1, ub_cA hs h2] at h
  have e : cA s c2 - 1 + 1 - cB s c1 = cA s c2 - cB s c1 := by omega
  rw [e] at h
  exact h

end CutCoords

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeChain` -/

section
/-!
# The chain surgery of `applyPlan`, in coordinates (work package C5, part 2)

`processRun` cuts the chain of a run (at most twice: an optional *pre-cut* and an *end-cut*), then adds `v` to the nodes
between the two cuts.  Here we compute the resulting chain in the coordinates of `RealizeSeq`:

* `DupOf ns ns'` — `ns'` arises from `ns` by inserting copies (same bag, no junk) after some nodes (`dupAfter`);
* `processRun_chain` — the new chain is `L ++ M.map av ++ R` where `L ++ M ++ R` is a `DupOf` of the old chain and the
  bag sizes of `L`, `M`, `R` are `s.take a₁`, `(s.drop b₁).take (a₂ - b₁)`, `s.drop b₂` for the coordinates of the cuts.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The bag sizes of a chain. -/
def csz (ns : List CNode) : List ℕ := ns.map (fun n => n.bag.card)

/-- Add the vertex `v` to the bag of a node. -/
def av (v : ℕ) (n : CNode) : CNode := ⟨insert v n.bag, n.junk⟩

/-! ## `dupAfter` -/

theorem dupAfter_of_lt {i : ℕ} {ns : List CNode} (hi : i < ns.length) :
    dupAfter i ns = ns.take (i + 1) ++ [⟨ns[i].bag, []⟩] ++ ns.drop (i + 1) := by
  unfold dupAfter
  rw [List.getElem?_eq_getElem hi]

theorem length_dupAfter (i : ℕ) (ns : List CNode) (hi : i < ns.length) :
    (dupAfter i ns).length = ns.length + 1 := by
  rw [dupAfter_of_lt hi]; simp; omega

theorem dupAfter_of_ge {i : ℕ} {ns : List CNode} (hi : ns.length ≤ i) : dupAfter i ns = ns := by
  unfold dupAfter
  rw [List.getElem?_eq_none hi]

theorem csz_dupAfter {i : ℕ} {ns : List CNode} (hi : i < ns.length) :
    csz (dupAfter i ns) = (csz ns).take (i + 1) ++ (csz ns).drop i := by
  unfold csz
  rw [dupAfter_of_lt hi]
  simp only [List.map_append, List.map_cons, List.map_nil, ← List.map_take, ← List.map_drop]
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.map_cons, List.singleton_append, List.append_assoc]

/-- `ns'` arises from `ns` by inserting copies. -/
inductive DupOf (ns : List CNode) : List CNode → Prop
  | refl : DupOf ns ns
  | dup {ns' : List CNode} (i : ℕ) : DupOf ns ns' → DupOf ns (dupAfter i ns')

theorem DupOf.length_ge {ns ns' : List CNode} (h : DupOf ns ns') : ns.length ≤ ns'.length := by
  induction h with
  | refl => exact le_rfl
  | @dup ns' i _ ih =>
    by_cases hi : i < ns'.length
    · rw [length_dupAfter i ns' hi]; omega
    · rw [dupAfter_of_ge (by omega)]; exact ih

/-- Every node of a duplicated chain is an old node or a junk-free copy of one. -/
theorem DupOf.mem {ns ns' : List CNode} (h : DupOf ns ns') :
    ∀ n ∈ ns', n ∈ ns ∨ ∃ n0 ∈ ns, n = ⟨n0.bag, []⟩ := by
  induction h with
  | refl => intro n hn; exact Or.inl hn
  | @dup ns' i _ ih =>
    intro n hn
    unfold dupAfter at hn
    cases hh : ns'[i]? with
    | none => rw [hh] at hn; exact ih n hn
    | some m =>
      rw [hh] at hn
      simp only [List.mem_append, List.mem_singleton] at hn
      rcases hn with (hn | rfl) | hn
      · exact ih n (List.mem_of_mem_take hn)
      · rcases ih m (List.mem_of_getElem? hh) with h1 | ⟨n0, hn0, rfl⟩
        · exact Or.inr ⟨m, h1, rfl⟩
        · exact Or.inr ⟨n0, hn0, rfl⟩
      · exact ih n (List.mem_of_mem_drop hn)

/-! ## `cutAt` -/

theorem csz_cutAt_t1 (y w : List ℕ) (f : ℕ) {ns : List CNode} (hi : w.getD f 0 < ns.length) :
    csz (cutAt y w (Cut.t1 f) ns).1 = (csz ns).take (w.getD f 0 + 1) ++ (csz ns).drop (w.getD f 0) := by
  simp only [cutAt]
  exact csz_dupAfter hi

theorem DupOf_cutAt {ns ns' : List CNode} (h : DupOf ns ns') (y w : List ℕ) (c : Cut) :
    DupOf ns (cutAt y w c ns').1 := by
  cases c with
  | t1 f => exact DupOf.dup _ h
  | t2 f => exact h

/-- Coordinates: the size list of the cut chain. -/
theorem csz_cutAt {s : List ℕ} (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) {ns : List CNode}
    (hns : s.length ≤ ns.length) :
    csz (cutAt (typical s) (witnesses s) c ns).1 = (csz ns).take (cA s c) ++ (csz ns).drop (cB s c) := by
  cases c with
  | t1 f =>
    have := Wf_lt hs (f := f) hc
    exact csz_cutAt_t1 (typical s) (witnesses s) f (by
      show Wf s f < ns.length
      omega)
  | t2 f =>
    simp only [cutAt, cA, cB]
    rw [List.take_append_drop]

/-- The index returned by a cut. -/
theorem cutAt_snd {s : List ℕ} (c : Cut) (ns : List CNode) :
    (cutAt (typical s) (witnesses s) c ns).2 + 1 = cA s c := by
  cases c with
  | t1 f => simp [cutAt, cA, Wf]
  | t2 f => simp [cutAt, cA, leftEnd2, Wf, Yf]

/-! ## `addV` -/

theorem addV_some (v : ℕ) {st e : ℕ} (ns : List CNode) (h1 : st ≤ e + 1) (h2 : e + 1 ≤ ns.length) :
    addV v st (some e) ns = ns.take st ++ ((ns.drop st).take (e + 1 - st)).map (av v) ++ ns.drop (e + 1) := by
  apply List.ext_getElem?
  intro k
  unfold addV
  rw [List.getElem?_mapIdx]
  have hlA : (ns.take st).length = st := by simp; omega
  have hlM : (((ns.drop st).take (e + 1 - st)).map (av v)).length = e + 1 - st := by simp; omega
  have hlAM : (ns.take st ++ ((ns.drop st).take (e + 1 - st)).map (av v)).length = e + 1 := by
    rw [List.length_append, hlA, hlM]; omega
  by_cases hk1 : k < st
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hk1]
    cases hh : ns[k]? with
    | none => simp
    | some n =>
      simp only [Option.map_some]
      rw [if_neg (by simp; omega)]
  · by_cases hk2 : k < e + 1
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
      rw [hlA, List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
      have : st + (k - st) = k := by omega
      rw [this]
      cases hh : ns[k]? with
      | none => simp
      | some n =>
        simp only [Option.map_some, Option.map]
        rw [if_pos (by simp; omega)]
        rfl
    · rw [List.getElem?_append_right (by omega)]
      rw [hlAM]
      rw [List.getElem?_drop]
      have : e + 1 + (k - (e + 1)) = k := by omega
      rw [this]
      cases hh : ns[k]? with
      | none => simp
      | some n =>
        simp only [Option.map_some]
        rw [if_neg (by simp; omega)]

theorem addV_none (v : ℕ) {st : ℕ} (ns : List CNode) :
    addV v st none ns = ns.take st ++ (ns.drop st).map (av v) := by
  apply List.ext_getElem?
  intro k
  unfold addV
  rw [List.getElem?_mapIdx]
  by_cases hkl : k < ns.length
  · by_cases hk1 : k < st
    · have hlA : (ns.take st).length = min st ns.length := by simp
      rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hk1,
        List.getElem?_eq_getElem hkl]
      simp only [Option.map_some]
      rw [if_neg (by simp; omega)]
    · have hlA : (ns.take st).length = min st ns.length := by simp
      have hlA' : (ns.take st).length = st := by omega
      rw [List.getElem?_append_right (by omega), hlA', List.getElem?_map, List.getElem?_drop]
      have : st + (k - st) = k := by omega
      rw [this, List.getElem?_eq_getElem hkl]
      simp only [Option.map_some, Option.map]
      rw [if_pos (by simp; omega)]
      rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp only [Option.map_none]
    symm
    rw [List.getElem?_eq_none]
    simp; omega


/-! ## `processRun`: the chain in coordinates -/

/-- Coordinates `(a₁, b₁)` of the pre-cut. -/
def preAB (s : List ℕ) : Option Cut → ℕ × ℕ
  | none => (0, 0)
  | some c => (cA s c, cB s c)

/-- Coordinates `(a₂, b₂)` of the end of the region. -/
def endAB (s : List ℕ) : WPlan → ℕ × ℕ
  | .endAt c => (cA s c, cB s c)
  | .whole _ => (s.length, s.length)

def PreOk (m : ℕ) : Option Cut → Prop
  | none => True
  | some c => c.Valid m

def WOk (m : ℕ) : WPlan → Prop
  | .endAt c => c.Valid m
  | .whole _ => True

/-- The region starts (in `y`) no later than it ends. -/
def LoHi : Option Cut → WPlan → Prop
  | some c1, .endAt c2 => cLo c1 ≤ cHi c2
  | _, _ => True

theorem comp_cuts (s : List ℕ) {a1 b1 a2 b2 : ℕ} (h1 : b1 ≤ a1) (h2 : a1 ≤ a2) (h3 : a2 ≤ s.length) :
    (s.take a2 ++ s.drop b2).take a1 ++ (s.take a2 ++ s.drop b2).drop b1 =
      s.take a1 ++ (s.drop b1).take (a2 - b1) ++ s.drop b2 := by
  have hl : (s.take a2).length = a2 := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_take, List.drop_take, Nat.min_eq_left h2]
  simp [List.append_assoc]

theorem coords_ok {s : List ℕ} (hs : s ≠ []) {pre : Option Cut} {w : WPlan}
    (hp : PreOk (witnesses s).length pre) (hw : WOk (witnesses s).length w) (hlh : LoHi pre w) :
    (preAB s pre).2 ≤ (preAB s pre).1 ∧ (preAB s pre).1 ≤ (preAB s pre).2 + 1 ∧
    (preAB s pre).2 + 1 ≤ (endAB s w).1 ∧ (preAB s pre).1 ≤ (endAB s w).1 ∧
    (endAB s w).1 ≤ s.length ∧ (endAB s w).2 ≤ s.length ∧ (endAB s w).2 ≤ (endAB s w).1 := by
  have hn : 0 < s.length := List.length_pos_of_ne_nil hs
  cases pre with
  | none =>
    cases w with
    | endAt c2 =>
      have := cA_pos (s := s) c2
      have := cA_le hs hw
      have := cB_le_cA (s := s) c2
      simp only [preAB, endAB]; omega
    | whole ps => simp only [preAB, endAB]; omega
  | some c1 =>
    have hc1 : c1.Valid (witnesses s).length := hp
    have := cB_le_cA (s := s) c1
    cases w with
    | endAt c2 =>
      have hm := dom_mid hs hc1 hw hlh
      have := cA_le hs hw
      have := cB_le_cA (s := s) c2
      simp only [preAB, endAB]; omega
    | whole ps =>
      have := cB_lt hs hc1
      have := cA_le hs hc1
      simp only [preAB, endAB]; omega

theorem csz_exists_pieces {ns : List CNode} {A M R : List ℕ} (h : csz ns = A ++ M ++ R) :
    ∃ L M' R', ns = L ++ M' ++ R' ∧ csz L = A ∧ csz M' = M ∧ csz R' = R := by
  unfold csz at h
  obtain ⟨l12, R', rfl, h12, hR⟩ := List.map_eq_append_iff.1 h
  obtain ⟨L, M', rfl, hL, hM⟩ := List.map_eq_append_iff.1 h12
  exact ⟨L, M', R', rfl, hL, hM, hR⟩


/-- The end index of the region (in the chain after both cuts), if it does not extend to the end. -/
def regionEnd (s : List ℕ) (pre : Option Cut) : WPlan → Option ℕ
  | .endAt c => some ((cA s c) + ((preAB s pre).1 - (preAB s pre).2) - 1)
  | .whole _ => none

/-- The chain computation of `processRun`, factored out. -/
def prStep (pre : Option Cut) (w : WPlan) (ns : List CNode) : List CNode × ℕ × Option ℕ :=
  let y := typical (csz ns)
  let wp := witnesses (csz ns)
  let endStep : List CNode × Option ℕ := match w with
    | .endAt c => ((cutAt y wp c ns).1, some (cutAt y wp c ns).2)
    | .whole _ => (ns, none)
  match pre with
  | none => (endStep.1, 0, endStep.2)
  | some c => ((cutAt y wp c endStep.1).1, (cutAt y wp c endStep.1).2 + 1,
      if c.isT1 then endStep.2.map (· + 1) else endStep.2)

theorem processRun_eq (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    processRun v pre w (.run S ns ks) = .run S
      (addV v (prStep pre w ns).2.1 (prStep pre w ns).2.2 (prStep pre w ns).1)
      (match w with
        | .endAt _ => ks
        | .whole ps => applyKids v ps ks) := by
  cases w <;> cases pre <;> (simp only [processRun, prStep]; try rfl)

theorem processRun_chain_eq (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    (processRun v pre w (.run S ns ks)).chain =
      addV v (prStep pre w ns).2.1 (prStep pre w ns).2.2 (prStep pre w ns).1 := by
  rw [processRun_eq]; rfl

theorem cA_sub_cB_t1 (s : List ℕ) (f : ℕ) : cA s (Cut.t1 f) - cB s (Cut.t1 f) = 1 := by simp [cA, cB]
theorem cA_sub_cB_t2 (s : List ℕ) (f : ℕ) : cA s (Cut.t2 f) - cB s (Cut.t2 f) = 0 := by simp [cA, cB]

theorem prStep_spec (pre : Option Cut) (w : WPlan) (ns : List CNode) (hne : ns ≠ [])
    (hp : PreOk (witnesses (csz ns)).length pre) (hw : WOk (witnesses (csz ns)).length w) (hlh : LoHi pre w) :
    ∃ ns2, (prStep pre w ns).1 = ns2 ∧ (prStep pre w ns).2.1 = (preAB (csz ns) pre).1 ∧
      (prStep pre w ns).2.2 = regionEnd (csz ns) pre w ∧ DupOf ns ns2 ∧
      csz ns2 = (csz ns).take (preAB (csz ns) pre).1 ++
        ((csz ns).drop (preAB (csz ns) pre).2).take ((endAB (csz ns) w).1 - (preAB (csz ns) pre).2) ++
        (csz ns).drop (endAB (csz ns) w).2 := by
  have hs : csz ns ≠ [] := by
    intro h; apply hne; unfold csz at h
    exact List.map_eq_nil_iff.1 h
  have hco := coords_ok hs hp hw hlh
  have hlen : (csz ns).length = ns.length := by simp [csz]
  cases pre with
  | none =>
    cases w with
    | endAt c2 =>
      have hc2 : c2.Valid (witnesses (csz ns)).length := hw
      have e2 := cutAt_snd (s := csz ns) c2 ns
      have h1 := cA_pos (s := csz ns) c2
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1, rfl, rfl, ?_,
        DupOf_cutAt DupOf.refl _ _ c2, ?_⟩
      · simp only [prStep, regionEnd, preAB]
        congr 1
        omega
      · rw [csz_cutAt hs hc2 (by omega)]
        simp only [preAB, endAB, List.take_zero, List.drop_zero, List.nil_append, Nat.sub_zero]
    | whole ps =>
      refine ⟨ns, rfl, rfl, rfl, DupOf.refl, ?_⟩
      simp only [preAB, endAB, List.take_zero, List.drop_zero, List.nil_append, Nat.sub_zero,
        List.take_length, List.drop_length, List.append_nil]
  | some c1 =>
    have hc1 : c1.Valid (witnesses (csz ns)).length := hp
    obtain ⟨hb1, hab1, hba, ha12, ha2, hb2, hb2a⟩ := hco
    simp only [preAB] at hb1 hab1 hba ha12
    cases w with
    | endAt c2 =>
      have hc2 : c2.Valid (witnesses (csz ns)).length := hw
      have hs1 : csz (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1 =
          (csz ns).take (cA (csz ns) c2) ++ (csz ns).drop (cB (csz ns) c2) :=
        csz_cutAt hs hc2 (by omega)
      have hlen1 : (csz ns).length ≤ (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1.length :=
        (hlen.le.trans (DupOf_cutAt DupOf.refl (typical (csz ns)) (witnesses (csz ns)) c2).length_ge)
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c1
          (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1).1, rfl, ?_, ?_,
        DupOf_cutAt (DupOf_cutAt DupOf.refl _ _ c2) _ _ c1, ?_⟩
      · have e1 := cutAt_snd (s := csz ns) c1 (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1
        simp only [prStep, preAB]
        omega
      · have e2 := cutAt_snd (s := csz ns) c2 ns
        have e1 := cutAt_snd (s := csz ns) c1 (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1
        have h1 := cA_pos (s := csz ns) c2
        have hc := cB_le_cA (s := csz ns) c1
        simp only [prStep, regionEnd, preAB]
        cases c1 with
        | t1 f =>
          simp only [Cut.isT1, if_true, Option.map_some]
          rw [cA_sub_cB_t1]
          congr 1 <;> omega
        | t2 f =>
          simp only [Cut.isT1, Bool.false_eq_true, if_false]
          rw [cA_sub_cB_t2]
          congr 1 <;> omega
      · rw [csz_cutAt hs hc1 hlen1, hs1]
        simp only [preAB, endAB]
        exact comp_cuts (csz ns) hb1 ha12 ha2
    | whole ps =>
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c1 ns).1, rfl, ?_, ?_,
        DupOf_cutAt DupOf.refl _ _ c1, ?_⟩
      · have e1 := cutAt_snd (s := csz ns) c1 ns
        simp only [prStep, preAB]
        omega
      · simp only [prStep, regionEnd, preAB]
        cases c1 <;> simp [Cut.isT1]
      · rw [csz_cutAt hs hc1 hlen.le]
        have := comp_cuts (csz ns) (a1 := cA (csz ns) c1) (b1 := cB (csz ns) c1) (a2 := (csz ns).length)
          (b2 := (csz ns).length) hb1 ha12 (le_refl _)
        simp only [preAB, endAB, List.take_length, List.drop_length, List.append_nil] at this ⊢
        simpa using this


theorem addV_pieces_some (v : ℕ) (L M R : List CNode) {e : ℕ} (h : L.length + M.length = e + 1) :
    addV v L.length (some e) (L ++ M ++ R) = L ++ M.map (av v) ++ R := by
  rw [addV_some v _ (by omega) (by simp; omega)]
  have e1 : (L ++ M ++ R).take L.length = L := by
    rw [List.append_assoc, List.take_left']; rfl
  have e2 : (L ++ M ++ R).drop L.length = M ++ R := by
    rw [List.append_assoc, List.drop_left']; rfl
  have e3 : (M ++ R).take (e + 1 - L.length) = M := by
    rw [show e + 1 - L.length = M.length by omega, List.take_left']; rfl
  have e4 : (L ++ M ++ R).drop (e + 1) = R := by
    rw [← h, ← List.length_append, List.drop_left']; rfl
  rw [e1, e2, e3, e4]

theorem addV_pieces_none (v : ℕ) (L M : List CNode) :
    addV v L.length none (L ++ M) = L ++ M.map (av v) := by
  rw [addV_none, List.take_left' rfl, List.drop_left' rfl]

theorem csz_length (ns : List CNode) : (csz ns).length = ns.length := by simp [csz]

theorem processRun_chain (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) (hne : ns ≠ []) (hp : PreOk (witnesses (csz ns)).length pre)
    (hw : WOk (witnesses (csz ns)).length w) (hlh : LoHi pre w) :
    ∃ L M R ns2 st re, DupOf ns ns2 ∧ ns2 = L ++ M ++ R ∧
      (processRun v pre w (.run S ns ks)).chain = addV v st re ns2 ∧
      (processRun v pre w (.run S ns ks)).chain = L ++ M.map (av v) ++ R ∧
      csz L = (csz ns).take (preAB (csz ns) pre).1 ∧
      csz M = ((csz ns).drop (preAB (csz ns) pre).2).take ((endAB (csz ns) w).1 - (preAB (csz ns) pre).2) ∧
      csz R = (csz ns).drop (endAB (csz ns) w).2 ∧
      M ≠ [] ∧ (pre = none → L = []) ∧ (pre ≠ none → L ≠ []) ∧
      (∀ ps, w = .whole ps → R = []) ∧ (∀ c, w = .endAt c → R ≠ []) := by
  have hs : csz ns ≠ [] := by
    intro h; apply hne; unfold csz at h
    exact List.map_eq_nil_iff.1 h
  have hco := coords_ok hs hp hw hlh
  obtain ⟨b1a1, a1b1, hba, ha12, ha2, hb2, hb2a⟩ := hco
  obtain ⟨ns2, h1, h2, h3, hdup, hcsz⟩ := prStep_spec pre w ns hne hp hw hlh
  obtain ⟨L, M, R, rfl, hL, hM, hR⟩ := csz_exists_pieces hcsz
  have hlenL : L.length = (preAB (csz ns) pre).1 := by
    rw [← csz_length L, hL]; simp; omega
  have hlenM : M.length = (endAB (csz ns) w).1 - (preAB (csz ns) pre).2 := by
    rw [← csz_length M, hM]; simp; omega
  have hlenR : R.length = (csz ns).length - (endAB (csz ns) w).2 := by
    rw [← csz_length R, hR]; simp
  refine ⟨L, M, R, L ++ M ++ R, (preAB (csz ns) pre).1, regionEnd (csz ns) pre w, hdup, rfl, ?_, ?_, hL, hM, hR,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [processRun_chain_eq, h1, h2, h3]
  · rw [processRun_chain_eq, h1, h2, h3, ← hlenL]
    cases w with
    | endAt c2 =>
      simp only [regionEnd]
      apply addV_pieces_some
      simp only [endAB] at hlenM b1a1 a1b1 hba ha12 ha2 hb2 hb2a ⊢
      omega
    | whole ps =>
      simp only [regionEnd]
      have hR0 : R = [] := by
        rw [← List.length_eq_zero_iff, hlenR]; simp [endAB]
      subst hR0
      simpa using addV_pieces_none v L M
  · rw [← List.length_pos_iff, hlenM]; omega
  · intro h; subst h
    rw [← List.length_eq_zero_iff, hlenL]; rfl
  · intro h
    rw [← List.length_pos_iff, hlenL]
    cases pre with
    | none => exact absurd rfl h
    | some c => simp only [preAB]; exact cA_pos c
  · intro ps hps; subst hps
    rw [← List.length_eq_zero_iff, hlenR]; simp [endAB]
  · intro c hc; subst hc
    rw [← List.length_pos_iff, hlenR]
    have := cB_lt hs (c := c) hw
    simp only [endAB]; omega

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeNorm` -/

section
/-!
# Normal-form algebra for the realisation of the introduce step (work package C5, part 3)

* `prof_insert_of_free` — a `v`-free tree has the same profile with respect to `B` and `insert v B`;
* `chainToRT_append` — a chain is the nesting of its two halves;
* `chain_norm` — the normal form of the profile of a chain of nodes with a common label is `normF` of that label, the
  typical sequence of the bag sizes and the normalised profiles of the kids (the junk is pruned);
* `keep_of_mem_verts`, `le_maxEntry_normF_*` — survival of a subtree containing a new vertex, and of its entries.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## profiles of `v`-free trees -/

theorem prof_insert_of_free (v : ℕ) (B : Finset ℕ) : ∀ t : RT, (∀ X ∈ t.bags, v ∉ X) →
    RT.prof (insert v B) t = RT.prof B t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro h
    rw [RT.prof_node, RT.prof_node]
    have hX : v ∉ X := h X ((RT.bags_node X ks).2 (Or.inl rfl))
    have e : X ∩ insert v B = X ∩ B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, rfl | h2⟩
        · exact absurd h1 hX
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
    rw [e]
    congr 1
    apply List.map_congr_left
    intro k hk
    exact ih k hk (fun Y hY => h Y ((RT.bags_node X ks).2 (Or.inr ⟨k, hk, hY⟩)))

/-! ## nesting of chains -/

theorem chainToRT_append (c1 c2 : List CNode) (K : List RT) (h1 : c1 ≠ []) (h2 : c2 ≠ []) :
    AR.chainToRT (c1 ++ c2) K = AR.chainToRT c1 [AR.chainToRT c2 K] := by
  induction c1 with
  | nil => exact absurd rfl h1
  | cons n r ih =>
    cases r with
    | nil =>
      obtain ⟨m, r2, rfl⟩ := List.exists_cons_of_ne_nil h2
      simp [AR.chainToRT]
    | cons m r' =>
      have := ih (by simp)
      simp only [List.cons_append] at this ⊢
      simp only [AR.chainToRT] at this ⊢
      rw [this]

/-! ## the profile of a chain -/

theorem chain_norm (B'' ℓ : Finset ℕ) : ∀ (c : List CNode) (K : List RT), c ≠ [] →
    (∀ n ∈ c, n.bag ∩ B'' = ℓ ∧ ∀ J ∈ n.junk, keep ℓ (norm (RT.prof B'' J)) = false) →
    norm (RT.prof B'' (AR.chainToRT c K)) =
      normF ℓ (typical (csz c)) (((K.map (RT.prof B'')).map norm).filter (keep ℓ)) := by
  intro c
  induction c with
  | nil => intro K h; exact absurd rfl h
  | cons n r ih =>
    intro K _ hc
    obtain ⟨hn1, hn2⟩ := hc n (by simp)
    have hjunk : (((n.junk.map (RT.prof B'')).map norm)).filter (keep ℓ) = [] := by
      rw [List.filter_eq_nil_iff]
      intro k hk
      obtain ⟨k1, hk1, rfl⟩ := List.mem_map.1 hk
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hk1
      simp [hn2 J hJ]
    cases r with
    | nil =>
      simp only [AR.chainToRT]
      rw [RT.prof_node, norm_node', hn1]
      simp only [List.map_append, List.filter_append, hjunk, List.nil_append]
      simp [csz, typical_singleton]
    | cons m r' =>
      simp only [AR.chainToRT]
      rw [RT.prof_node, norm_node', hn1]
      have hrest := ih K (by simp) (fun n' hn' => hc n' (List.mem_cons_of_mem _ hn'))
      simp only [List.map_append, List.filter_append, hjunk, List.nil_append, List.map_cons, List.map_nil]
      rw [hrest]
      have hF : ∀ k ∈ ((K.map (RT.prof B'')).map norm).filter (keep ℓ), keep ℓ k = true :=
        fun k hk => (List.mem_filter.1 hk).2
      have := normF_merge ℓ (s := [n.bag.card]) (y := typical (csz (m :: r')))
        (by simp) hF
      have e : typical ([n.bag.card] ++ typical (csz (m :: r'))) = typical (csz (n :: m :: r')) := by
        rw [← typical_append_typical_right]; simp [csz]
      rw [this, e]

/-! ## survival -/

theorem keep_of_mem_verts {σ : Finset ℕ} {p : CT} {v : ℕ} (hv : v ∈ verts p) (hσ : v ∉ σ) :
    keep σ (norm p) = true := by
  by_contra hcon
  have hf : keep σ (norm p) = false := by simpa using hcon
  have hn := (keep_norm_false_iff σ p).1 hf
  exact hσ (nested_root_sub hn (verts_nested σ p hn hv))

theorem le_maxEntry_y {q : CT} {e : ℕ} (h : e ∈ q.y) : e ≤ maxEntry q := by
  cases q with
  | node S y ks =>
    have := (maxEntry_le_iff (S := S) (y := y) (ks := ks) (n := maxEntry (node S y ks))).1 le_rfl
    exact this.1 e h

theorem maxOf_typical_le_maxEntry {q : CT} {z : List ℕ} (hz : q.y = typical z) : maxOf z ≤ maxEntry q := by
  rw [← maxOf_typical, ← hz]
  exact maxOf_le fun e he => le_maxEntry_y he

theorem le_maxEntry_normF_kid {S : Finset ℕ} {y : List ℕ} {F : List CT} {k : CT} (hk : k ∈ F) :
    maxEntry k ≤ maxEntry (normF S y F) := by
  match F, hk with
  | [], hk => simp at hk
  | [k0], hk =>
    have : k = k0 := by simpa using hk
    subst this
    rw [normF_single]
    split_ifs with hS
    · obtain ⟨Sk, yk, kk⟩ := k
      rw [maxEntry_le_iff]
      refine ⟨fun e he => ?_, fun k' hk' => ?_⟩
      · have h1 := maxOf_typical_le_maxEntry (q := node S (typical (y ++ yk)) kk) (z := y ++ yk) rfl
        exact (le_maxOf (List.mem_append_right _ he)).trans h1
      · exact maxEntry_kid_le (q := node S (typical (y ++ yk)) kk) hk'
    · exact maxEntry_kid_le (q := node S y [k]) (by simp [CT.kids])
  | a :: b :: t, hk =>
    rw [normF_ge2]
    exact maxEntry_kid_le (q := node S y (sortKids S (a :: b :: t))) (mem_sortKids.2 hk)

theorem le_maxEntry_normF_y {S : Finset ℕ} {y : List ℕ} {F : List CT} (hF : F ≠ [] ∨ y.length ≤ 1) {e : ℕ}
    (he : e ∈ y) : e ≤ maxEntry (normF S y F) := by
  match F, hF with
  | [], hF =>
    have hy : y.length ≤ 1 := by
      rcases hF with h | h
      · exact absurd rfl h
      · exact h
    rw [normF_nil]
    apply le_maxEntry_y
    simp only [CT.y]
    rw [List.take_of_length_le hy]; exact he
  | [k0], hF =>
    rw [normF_single]
    split_ifs with hS
    · have h1 := maxOf_typical_le_maxEntry (q := node S (typical (y ++ k0.y)) k0.kids) (z := y ++ k0.y) rfl
      exact (le_maxOf (List.mem_append_left _ he)).trans h1
    · exact le_maxEntry_y (q := node S y [k0]) he
  | a :: b :: t, hF =>
    rw [normF_ge2]
    exact le_maxEntry_y (q := node S y (sortKids S (a :: b :: t))) he

theorem norm_kid_le {σ : Finset ℕ} {y : List ℕ} {K : List CT} {k : CT} (hk : k ∈ K)
    (hkeep : keep σ (norm k) = true) : maxEntry (norm k) ≤ maxEntry (norm (node σ y K)) := by
  rw [norm_node']
  apply le_maxEntry_normF_kid
  exact List.mem_filter.2 ⟨List.mem_map.2 ⟨k, hk, rfl⟩, hkeep⟩

theorem norm_y_le {σ : Finset ℕ} {y : List ℕ} {K : List CT} (hF : (∃ k ∈ K, keep σ (norm k) = true) ∨ y.length ≤ 1)
    {e : ℕ} (he : e ∈ y) : e ≤ maxEntry (norm (node σ y K)) := by
  rw [norm_node']
  apply le_maxEntry_normF_y _ he
  rcases hF with ⟨k, hk, hkeep⟩ | h
  · left
    intro hnil
    have : norm k ∈ (K.map norm).filter (keep σ) := List.mem_filter.2 ⟨List.mem_map.2 ⟨k, hk, rfl⟩, hkeep⟩
    rw [hnil] at this; simp at this
  · right; exact h


/-! ## adding one to sequences -/

theorem ext_map_inj (f : ℕ → ℕ) (hf : Function.Injective f) : ∀ {a w : List ℕ}, Ext a w → Ext (a.map f) (w.map f) := by
  intro a w
  induction w generalizing a with
  | nil => intro h; rw [ext_nil_right] at h; subst h; simp
  | cons y w ih =>
    intro h
    cases a with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x a =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · simp only [List.map_cons]
        exact ext_cons_cons.mpr ⟨rfl, Or.inl (by simpa using ih h)⟩
      · simp only [List.map_cons]
        exact ext_cons_cons.mpr ⟨rfl, Or.inr (ih h)⟩

theorem leSeq_map_succ {a b : List ℕ} (h : LeSeq a b) : LeSeq (a.map (· + 1)) (b.map (· + 1)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons (by simp only []; omega) ih

theorem dom_map_succ {a b : List ℕ} (h : Dom a b) : Dom (a.map (· + 1)) (b.map (· + 1)) := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  exact ⟨a'.map (· + 1), b'.map (· + 1), ext_map_inj _ (fun x y h => by simpa using h) ha,
    ext_map_inj _ (fun x y h => by simpa using h) hb, leSeq_map_succ hle⟩

theorem typical_plus1 (a : List ℕ) : typical (a.map (· + 1)) = plus1 (typical a) := by
  unfold plus1; exact typical_map_add a 1

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeTc` -/

section
/-!
# Connectedness by counting tops (work package C5, part 4)

`tc u t p` counts the *tops* of the occurrences of `u` in `t`: the nodes containing `u` whose parent does not (`p` says
whether the parent of the root contains `u`).  `RT.Conn t` holds iff every vertex has at most one top
(`conn_iff_tc`).  Counting is additive and insensitive to the duplication of a node (same bag), which makes the
connectedness of the realised decomposition a computation.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

mutual
/-- The number of tops of the occurrences of `u` in `t`; `p` = the parent of the root contains `u`. -/
def tc (u : ℕ) : RT → Bool → ℕ
  | .node b ks, p => (if u ∈ b ∧ p = false then 1 else 0) + tcL u ks (decide (u ∈ b))
def tcL (u : ℕ) : List RT → Bool → ℕ
  | [], _ => 0
  | k :: ks, p => tc u k p + tcL u ks p
end

theorem tcL_eq_sum (u : ℕ) : ∀ (ks : List RT) (p : Bool), tcL u ks p = (ks.map (fun k => tc u k p)).sum
  | [], p => rfl
  | k :: ks, p => by simp [tcL, tcL_eq_sum u ks p]

theorem tc_node (u : ℕ) (b : Finset ℕ) (ks : List RT) (p : Bool) :
    tc u (.node b ks) p = (if u ∈ b ∧ p = false then 1 else 0) + (ks.map (fun k => tc u k (decide (u ∈ b)))).sum := by
  rw [tc, tcL_eq_sum]

/-- No vertex outside the tree: no tops. -/
theorem tc_zero_of_notin (u : ℕ) : ∀ (t : RT) (p : Bool), u ∉ t.verts → tc u t p = 0 := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro p h
    rw [RT.verts_node] at h
    push_neg at h
    rw [tc_node]
    have h1 : ¬ (u ∈ b ∧ p = false) := fun hh => h.1 hh.1
    rw [if_neg h1, zero_add, List.sum_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ih k hk _ (h.2 k hk)

theorem tc_pos (u : ℕ) : ∀ (t : RT), u ∈ t.verts → 1 ≤ tc u t false ∧ (u ∉ t.rootBag → 1 ≤ tc u t true) := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro h
    rw [RT.verts_node] at h
    by_cases hb : u ∈ b
    · refine ⟨?_, fun h' => absurd hb h'⟩
      rw [tc_node, if_pos ⟨hb, rfl⟩]; omega
    · obtain ⟨k, hk, hkv⟩ := h.resolve_left hb
      have := ih k hk hkv
      have hk1 : 1 ≤ tc u k false := this.1
      have hsum : tc u k (decide (u ∈ b)) ≤ (ks.map (fun k => tc u k (decide (u ∈ b)))).sum :=
        List.single_le_sum (fun x hx => Nat.zero_le _) _ (List.mem_map.2 ⟨k, hk, rfl⟩)
      have hdec : decide (u ∈ b) = false := by simp [hb]
      rw [hdec] at hsum
      have e1 : ¬ (u ∈ b ∧ false = false) := fun hh => hb hh.1
      have e2 : ¬ (u ∈ b ∧ true = false) := fun hh => by simp at hh
      constructor
      · rw [tc_node, if_neg (fun hh => hb hh.1), zero_add, hdec]
        omega
      · intro _
        rw [tc_node, if_neg e2, zero_add, hdec]
        omega

/-! ## the per-vertex connectedness condition -/

mutual
/-- `u` occupies a connected set of nodes of `t`. -/
def CU (u : ℕ) : RT → Prop
  | .node b ks => CUL u ks ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
      ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b)
def CUL (u : ℕ) : List RT → Prop
  | [] => True
  | k :: ks => CU u k ∧ CUL u ks
end

theorem CUL_iff (u : ℕ) : ∀ ks : List RT, CUL u ks ↔ ∀ k ∈ ks, CU u k
  | [] => by simp [CUL]
  | k :: ks => by simp [CUL, CUL_iff u ks]

theorem CU_node (u : ℕ) (b : Finset ℕ) (ks : List RT) :
    CU u (.node b ks) ↔ (∀ k ∈ ks, CU u k) ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
      ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b) := by
  rw [CU, CUL_iff]

theorem CU_of_notin (u : ℕ) : ∀ t : RT, u ∉ t.verts → CU u t := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro h
    rw [RT.verts_node] at h
    push_neg at h
    rw [CU_node]
    refine ⟨fun k hk => ih k hk (h.2 k hk), fun hb => absurd hb h.1, ?_⟩
    exact List.pairwise_iff_getElem.2 (fun i j hi hj hij hva => absurd hva (h.2 _ (List.getElem_mem _)))

theorem conn_iff_CU : ∀ t : RT, t.Conn ↔ ∀ u, CU u t := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    rw [RT.conn_node_iff]
    simp only [CU_node]
    constructor
    · rintro ⟨h1, h2, h3⟩ u
      refine ⟨fun k hk => (ih k hk).1 (h1 k hk) u, fun hu k hk hv => h2 k hk u hu hv, ?_⟩
      exact h3.imp (fun h hv1 hv2 => h u hv1 hv2)
    · intro h
      refine ⟨fun k hk => (ih k hk).2 (fun u => (h u).1 k hk), fun k hk u hu hv => (h u).2.1 hu k hk hv, ?_⟩
      -- pairwise with a universally quantified vertex
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij u hv1 hv2
      have := List.pairwise_iff_getElem.1 (h u).2.2 i j hi hj hij
      exact this hv1 hv2


/-! ## counting tops decides `CU` -/

theorem sum_le_one_iff (u : ℕ) : ∀ (ks : List RT), (∀ k ∈ ks, (tc u k false ≤ 1 ↔ CU u k)) →
    ((ks.map (fun k => tc u k false)).sum ≤ 1 ↔
      (∀ k ∈ ks, CU u k) ∧ ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → False)) := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons k ks ih =>
    intro hIH
    have hk := hIH k (by simp)
    have hks := ih (fun k' hk' => hIH k' (List.mem_cons_of_mem _ hk'))
    simp only [List.map_cons, List.sum_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have h1 : tc u k false ≤ 1 := by omega
      have h2 : (ks.map (fun k => tc u k false)).sum ≤ 1 := by omega
      obtain ⟨hc, hp⟩ := hks.1 h2
      refine ⟨⟨hk.1 h1, hc⟩, fun k' hk' hv1 hv2 => ?_, hp⟩
      have a1 := (tc_pos u k hv1).1
      have a2 := (tc_pos u k' hv2).1
      have a3 : tc u k' false ≤ (ks.map (fun k => tc u k false)).sum :=
        List.single_le_sum (fun x hx => Nat.zero_le _) _ (List.mem_map.2 ⟨k', hk', rfl⟩)
      omega
    · rintro ⟨⟨hc1, hc⟩, hp1, hp⟩
      have h1 := hk.2 hc1
      have h2 := hks.2 ⟨hc, hp⟩
      by_cases hv : u ∈ k.verts
      · have : (ks.map (fun k => tc u k false)).sum = 0 := by
          rw [List.sum_eq_zero]
          intro x hx
          obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx
          apply tc_zero_of_notin
          intro hv'
          exact hp1 k' hk' hv hv'
        omega
      · have : tc u k false = 0 := tc_zero_of_notin u k false hv
        omega

theorem CU_iff_tc (u : ℕ) : ∀ t : RT,
    (CU u t ↔ tc u t false ≤ 1) ∧ ((CU u t ∧ (u ∈ t.verts → u ∈ t.rootBag)) ↔ tc u t true = 0) := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    rw [CU_node, tc_node, tc_node]
    show _ ∧ ((_ ∧ (u ∈ (RT.node b ks).verts → u ∈ b)) ↔ _)
    by_cases hb : u ∈ b
    · have hd : decide (u ∈ b) = true := by simp [hb]
      rw [hd]
      have e1 : (if u ∈ b ∧ false = false then 1 else 0) = 1 := if_pos ⟨hb, rfl⟩
      have e2 : (if u ∈ b ∧ true = false then 1 else 0) = 0 := if_neg (by simp)
      rw [e1, e2]
      have hsum0 : ((ks.map (fun k => tc u k true)).sum = 0) ↔
          ((∀ k ∈ ks, CU u k) ∧ ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) := by
        rw [List.sum_eq_zero_iff]
        constructor
        · intro h
          have h' : ∀ k ∈ ks, CU u k ∧ (u ∈ k.verts → u ∈ k.rootBag) :=
            fun k hk => (ih k hk).2.2 (h _ (List.mem_map.2 ⟨k, hk, rfl⟩))
          exact ⟨fun k hk => (h' k hk).1, fun k hk => (h' k hk).2⟩
        · rintro ⟨h1, h2⟩ x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
          exact (ih k hk).2.1 ⟨h1 k hk, h2 k hk⟩
      have hpw : ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b) :=
        List.pairwise_iff_getElem.2 (fun i j hi hj hij _ _ => hb)
      constructor
      · constructor
        · rintro ⟨h1, h2, _⟩
          have := hsum0.2 ⟨h1, h2 hb⟩
          omega
        · intro h
          have := hsum0.1 (by omega)
          exact ⟨this.1, fun _ => this.2, hpw⟩
      · constructor
        · rintro ⟨⟨h1, h2, _⟩, _⟩
          have := hsum0.2 ⟨h1, h2 hb⟩
          omega
        · intro h
          have := hsum0.1 (by omega)
          exact ⟨⟨this.1, fun _ => this.2, hpw⟩, fun _ => hb⟩
    · have hd : decide (u ∈ b) = false := by simp [hb]
      rw [hd]
      have e1 : (if u ∈ b ∧ false = false then 1 else 0) = 0 := if_neg (fun h => hb h.1)
      have e2 : (if u ∈ b ∧ true = false then 1 else 0) = 0 := if_neg (by simp)
      rw [e1, e2]
      have hle := sum_le_one_iff u ks (fun k hk => (ih k hk).1.symm)
      have hCUpw : ((∀ k ∈ ks, CU u k) ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
          ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b)) ↔
          ((∀ k ∈ ks, CU u k) ∧ ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → False)) := by
        constructor
        · rintro ⟨h1, _, h3⟩
          exact ⟨h1, h3.imp (fun h a b => absurd (h a b) hb)⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, fun h => absurd h hb, h3.imp (fun h a b => (h a b).elim)⟩
      have hnv : u ∈ (RT.node b ks).verts ↔ ∃ k ∈ ks, u ∈ k.verts := by
        rw [RT.verts_node]; constructor
        · rintro (h | h)
          · exact absurd h hb
          · exact h
        · intro h; exact Or.inr h
      constructor
      · rw [zero_add, hCUpw]; exact hle.symm
      · have hz : ((ks.map (fun k => tc u k false)).sum = 0) ↔ ∀ k ∈ ks, u ∉ k.verts := by
          rw [List.sum_eq_zero_iff]
          constructor
          · intro h k hk hv
            have := h _ (List.mem_map.2 ⟨k, hk, rfl⟩)
            have := (tc_pos u k hv).1
            omega
          · intro h x hx
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
            exact tc_zero_of_notin u k false (h k hk)
        rw [zero_add, hz]
        constructor
        · rintro ⟨_, h2⟩ k hk hv
          exact hb (h2 (hnv.2 ⟨k, hk, hv⟩))
        · intro h
          have hn : u ∉ (RT.node b ks).verts := fun hv => by
            obtain ⟨k, hk, hk2⟩ := hnv.1 hv
            exact h k hk hk2
          refine ⟨?_, fun hv => absurd hv hn⟩
          have := CU_of_notin u _ hn
          rw [CU_node] at this
          exact this


theorem conn_iff_tc (t : RT) : t.Conn ↔ ∀ u, tc u t false ≤ 1 := by
  rw [conn_iff_CU]
  exact forall_congr' (fun u => (CU_iff_tc u t).1)

/-! ## chains -/

theorem chainToRT_cons_of_ne (n : CNode) {l : List CNode} (hl : l ≠ []) (K : List RT) :
    AR.chainToRT (n :: l) K = .node n.bag (n.junk ++ [AR.chainToRT l K]) := by
  obtain ⟨m, r, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem chainToRT_single (n : CNode) (K : List RT) : AR.chainToRT [n] K = .node n.bag (n.junk ++ K) := rfl

theorem dupAfter_cons_succ (j : ℕ) (n : CNode) (r : List CNode) : dupAfter (j + 1) (n :: r) = n :: dupAfter j r := by
  by_cases h : j < r.length
  · rw [dupAfter_of_lt (by simpa using h), dupAfter_of_lt h]
    simp [List.take_succ_cons, List.drop_succ_cons]
  · rw [dupAfter_of_ge (by simp; omega), dupAfter_of_ge (by omega)]

theorem dupAfter_zero (n : CNode) (r : List CNode) : dupAfter 0 (n :: r) = n :: ⟨n.bag, []⟩ :: r := by
  rw [dupAfter_of_lt (by simp)]
  simp

theorem tc_chain_dup (u : ℕ) : ∀ (ns : List CNode) (i : ℕ) (K : List RT) (p : Bool),
    tc u (AR.chainToRT (dupAfter i ns) K) p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro i K p; rw [dupAfter_of_ge (i := i) (ns := []) (by simp)]
  | cons n r ih =>
    intro i K p
    cases i with
    | zero =>
      rw [dupAfter_zero]
      cases r with
      | nil =>
        simp only [AR.chainToRT, tc_node, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.nil_append]
        simp
      | cons m r' =>
        simp only [AR.chainToRT, tc_node, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.nil_append]
        simp
    | succ j =>
      rw [dupAfter_cons_succ]
      cases r with
      | nil => rw [dupAfter_of_ge (i := j) (ns := []) (by simp)]
      | cons m r' =>
        have hne : dupAfter j (m :: r') ≠ [] := by
          by_cases hj : j < (m :: r').length
          · rw [dupAfter_of_lt hj]; simp
          · rw [dupAfter_of_ge (by omega)]; simp
        rw [chainToRT_cons_of_ne _ hne, chainToRT_cons_of_ne _ (by simp)]
        simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, ih j K]

theorem tc_chain_dupOf (u : ℕ) {ns ns' : List CNode} (h : DupOf ns ns') (K : List RT) (p : Bool) :
    tc u (AR.chainToRT ns' K) p = tc u (AR.chainToRT ns K) p := by
  induction h with
  | refl => rfl
  | dup i _ ih => rw [tc_chain_dup, ih]

theorem tc_chain_mapIdx (u : ℕ) : ∀ (ns : List CNode) (g : ℕ → CNode → CNode),
    (∀ i n, (u ∈ (g i n).bag ↔ u ∈ n.bag) ∧ (g i n).junk = n.junk) →
    ∀ (K : List RT) (p : Bool), tc u (AR.chainToRT (ns.mapIdx g) K) p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro g hg K p; simp
  | cons n r ih =>
    intro g hg K p
    rw [List.mapIdx_cons]
    have h0 := hg 0 n
    cases r with
    | nil =>
      simp only [List.mapIdx_nil]
      rw [chainToRT_single, chainToRT_single, tc_node, tc_node, h0.2]
      simp [h0.1]
    | cons m r' =>
      have hne : (List.mapIdx (fun i => g (i + 1)) (m :: r')) ≠ [] := by simp
      rw [chainToRT_cons_of_ne _ hne, chainToRT_cons_of_ne _ (by simp)]
      have := ih (fun i => g (i + 1)) (fun i n => hg (i + 1) n) K
      simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, h0.1, h0.2, this]

/-! ## the new vertex -/

theorem tc_chain_prefix_free (v : ℕ) : ∀ (L : List CNode) (K : List RT) (p : Bool), L ≠ [] →
    (∀ n ∈ L, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts) →
    tc v (AR.chainToRT L K) p = tcL v K false := by
  intro L
  induction L with
  | nil => intro K p h; exact absurd rfl h
  | cons n r ih =>
    intro K p _ hL
    obtain ⟨hn1, hn2⟩ := hL n (by simp)
    have hdec : decide (v ∈ n.bag) = false := by simp [hn1]
    have hjz : (n.junk.map (fun k => tc v k false)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      exact tc_zero_of_notin v J false (hn2 J hJ)
    cases r with
    | nil =>
      rw [chainToRT_single, tc_node, hdec, List.map_append, List.sum_append, hjz, if_neg (fun h => hn1 h.1),
        ← tcL_eq_sum]
      simp
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), tc_node, hdec, if_neg (fun h => hn1 h.1)]
      have := ih K false (by simp) (fun n' hn' => hL n' (List.mem_cons_of_mem _ hn'))
      simp [List.sum_append, hjz, this]

theorem tc_chain_full (v : ℕ) : ∀ (M : List CNode) (K : List RT) (p : Bool), M ≠ [] →
    (∀ n ∈ M, v ∈ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts) →
    tc v (AR.chainToRT M K) p = (if p = false then 1 else 0) + tcL v K true := by
  intro M
  induction M with
  | nil => intro K p h; exact absurd rfl h
  | cons n r ih =>
    intro K p _ hM
    obtain ⟨hn1, hn2⟩ := hM n (by simp)
    have hdec : decide (v ∈ n.bag) = true := by simp [hn1]
    have hjz : (n.junk.map (fun k => tc v k true)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      exact tc_zero_of_notin v J true (hn2 J hJ)
    have hif : (if v ∈ n.bag ∧ p = false then 1 else 0) = (if p = false then 1 else 0) := by
      by_cases hp : p = false <;> simp [hp, hn1]
    cases r with
    | nil =>
      rw [chainToRT_single, tc_node, hdec, List.map_append, List.sum_append, hjz, hif, ← tcL_eq_sum]
      simp
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), tc_node, hdec, hif]
      have := ih K true (by simp) (fun n' hn' => hM n' (List.mem_cons_of_mem _ hn'))
      simp [List.sum_append, hjz, this]

/-! ## vertices and bags of a chain -/

theorem mem_bags_chainToRT (K : List RT) : ∀ (n : List CNode), n ≠ [] → ∀ (Y : Finset ℕ),
    Y ∈ (AR.chainToRT n K).bags ↔ (∃ y ∈ n, Y = y.bag) ∨ (∃ y ∈ n, ∃ J ∈ y.junk, Y ∈ J.bags) ∨
      ∃ K' ∈ K, Y ∈ K'.bags := by
  intro n
  induction n with
  | nil => intro h; exact absurd rfl h
  | cons a r ih =>
    intro _ Y
    cases r with
    | nil =>
      rw [chainToRT_single, RT.bags_node]
      simp only [List.mem_append, List.mem_singleton, exists_eq_left]
      constructor
      · rintro (h | ⟨k, hk | hk, hY⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨k, hk, hY⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hY⟩)
      · rintro (h | ⟨k, hk, hY⟩ | ⟨k, hk, hY⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, Or.inl hk, hY⟩
        · exact Or.inr ⟨k, Or.inr hk, hY⟩
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), RT.bags_node]
      have IH := ih (by simp) Y
      constructor
      · rintro (h | ⟨k, hk, hY⟩)
        · exact Or.inl ⟨a, List.mem_cons_self, h⟩
        · rcases List.mem_append.1 hk with hk | hk
          · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, k, hk, hY⟩)
          · rw [List.mem_singleton] at hk
            subst hk
            rcases IH.1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | h
            · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hYy⟩
            · exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, J, hJ, hYJ⟩)
            · exact Or.inr (Or.inr h)
      · rintro (⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | h)
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inl hYy
          · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
              IH.2 (Or.inl ⟨y, hy, hYy⟩)⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inr ⟨J, List.mem_append_left _ hJ, hYJ⟩
          · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
              IH.2 (Or.inr (Or.inl ⟨y, hy, J, hJ, hYJ⟩))⟩
        · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
            IH.2 (Or.inr (Or.inr h))⟩

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeRun` -/

section
/-!
# The topology of the realised decomposition (work package C5, part 5)

`TI v t t'` collects what the introduction of the fresh vertex `v` does to a rooted tree `t`, turning it into `t'`
(same tree up to duplicated nodes, `v` added to a connected region, junk branches attached): vertex sets, bags, and the
number of tops of every vertex other than `v`.  We prove `TI` for a chain whose middle segment receives `v`
(`chain_region_TI`) and for a chain whose kids change (`chain_kids_TI`).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

structure TI (v : ℕ) (t t' : RT) : Prop where
  vsub : ∀ x, x ∈ t'.verts → x ∈ t.verts ∨ x = v
  vsup : ∀ x, x ∈ t.verts → x ∈ t'.verts
  bnew : ∀ Y ∈ t'.bags, v ∈ Y ∨ ∃ X ∈ t.bags, Y ⊆ X
  bsup : ∀ X ∈ t.bags, ∃ Y ∈ t'.bags, X ⊆ Y
  tcne : ∀ u, u ≠ v → ∀ p, tc u t' p = tc u t p

theorem TI.refl (v : ℕ) (t : RT) : TI v t t :=
  ⟨fun x hx => Or.inl hx, fun x hx => hx, fun Y hY => Or.inr ⟨Y, hY, subset_rfl⟩, fun X hX => ⟨X, hX, subset_rfl⟩,
    fun u _ p => rfl⟩

/-! ## lists of kids -/

theorem forall2_exists_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b := by
  intro l l' h
  induction h with
  | nil => intro b hb; simp at hb
  | @cons a b l l' hab _ ih =>
    intro b' hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact ⟨a, by simp, hab⟩
    · obtain ⟨a', ha', h'⟩ := ih b' hb'
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall2_exists_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b := by
  intro l l' h
  induction h with
  | nil => intro a ha; simp at ha
  | @cons a b l l' hab _ ih =>
    intro a' ha'
    rcases List.mem_cons.1 ha' with rfl | ha'
    · exact ⟨b, by simp, hab⟩
    · obtain ⟨b', hb', h'⟩ := ih a' ha'
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem tcL_of_forall2 {v : ℕ} {K K' : List RT} (h : List.Forall₂ (TI v) K K') {u : ℕ} (hu : u ≠ v) (p : Bool) :
    tcL u K' p = tcL u K p := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [tcL, hab.tcne u hu p, ih]

theorem tc_chain_kids (u : ℕ) : ∀ (ns : List CNode) (K K' : List RT), ns ≠ [] → (∀ p, tcL u K' p = tcL u K p) →
    ∀ p, tc u (AR.chainToRT ns K') p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro K K' h; exact absurd rfl h
  | cons n r ih =>
    intro K K' _ hK p
    cases r with
    | nil =>
      rw [chainToRT_single, chainToRT_single, tc_node, tc_node]
      simp only [List.map_append, List.sum_append, ← tcL_eq_sum, hK]
    | cons m r' =>
      rw [chainToRT_cons_of_ne n (l := m :: r') (by simp) K', chainToRT_cons_of_ne n (l := m :: r') (by simp) K]
      simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, ih K K' (by simp) hK]

/-! ## duplicated chains -/

theorem DupOf.sub {ns ns' : List CNode} (h : DupOf ns ns') : ∀ n ∈ ns, n ∈ ns' := by
  induction h with
  | refl => intro n hn; exact hn
  | @dup ns' i _ ih =>
    intro n hn
    have := ih n hn
    by_cases hi : i < ns'.length
    · rw [dupAfter_of_lt hi]
      have h2 : n ∈ ns'.take (i + 1) ++ ns'.drop (i + 1) := by rw [List.take_append_drop]; exact this
      rcases List.mem_append.1 h2 with h3 | h3
      · exact List.mem_append_left _ (List.mem_append_left _ h3)
      · exact List.mem_append_right _ h3
    · rw [dupAfter_of_ge (by omega)]; exact this

theorem DupOf.info {ns ns2 : List CNode} (h : DupOf ns ns2) :
    ∀ n ∈ ns2, ∃ n0 ∈ ns, n.bag = n0.bag ∧ ∀ J ∈ n.junk, J ∈ n0.junk := by
  intro n hn
  rcases h.mem n hn with h1 | ⟨n0, h1, rfl⟩
  · exact ⟨n, h1, rfl, fun J hJ => hJ⟩
  · exact ⟨n0, h1, rfl, fun J hJ => by simp at hJ⟩

theorem av_bag (v : ℕ) (n : CNode) : (av v n).bag = insert v n.bag := rfl

/-! ## a chain whose middle segment receives `v` -/

theorem chain_region_TI (v : ℕ) {ns L M R : List CNode} {K K' : List RT} {chain'' : List CNode} (hns : ns ≠ [])
    (hdup : DupOf ns (L ++ M ++ R)) (hne'' : chain'' ≠ [])
    (hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK : List.Forall₂ (TI v) K K')
    (hc1 : chain'' = L ++ M.map (av v) ++ R)
    (hmap : ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧
        (g i n).junk = n.junk) ∧ chain'' = (L ++ M ++ R).mapIdx g) :
    TI v (AR.chainToRT ns K) (AR.chainToRT chain'' K') := by
  have hinfo := hdup.info
  have hsub := hdup.sub
  have hb := mem_bags_chainToRT K ns hns
  have hb' := mem_bags_chainToRT K' chain'' hne''
  -- membership in the new chain
  have hmem : ∀ y ∈ chain'', y ∈ (L ++ M ++ R) ∨ (∃ n ∈ M, y = av v n) := by
    intro y hy
    rw [hc1] at hy
    simp only [List.mem_append, List.mem_map] at hy
    rcases hy with (hy | ⟨n, hn, rfl⟩) | hy
    · exact Or.inl (by simp [hy])
    · exact Or.inr ⟨n, hn, rfl⟩
    · exact Or.inl (by simp [hy])
  have hmem' : ∀ n ∈ (L ++ M ++ R), n ∈ chain'' ∨ av v n ∈ chain'' := by
    intro n hn
    rw [hc1]
    simp only [List.mem_append] at hn ⊢
    rcases hn with (hn | hn) | hn
    · exact Or.inl (Or.inl (Or.inl hn))
    · exact Or.inr (Or.inl (Or.inr (List.mem_map.2 ⟨n, hn, rfl⟩)))
    · exact Or.inl (Or.inr hn)
  -- v-freeness of the (duplicated) nodes
  have hfree2 : ∀ n ∈ (L ++ M ++ R), v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n hn
    obtain ⟨h1, h2⟩ := hfree n0 hn0
    exact ⟨by rw [hbg]; exact h1, fun J hJ => h2 J (hj J hJ)⟩
  have hMsub : ∀ n ∈ M, n ∈ (L ++ M ++ R) := fun n hn => by simp [hn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- vsub
    intro x hx
    rw [mem_verts_chainToRT] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k', hk', hxk⟩
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo y hn
        exact Or.inl (Or.inl ⟨n0, hn0, by rw [← hbg]; exact hxy⟩)
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo n (hMsub n hn)
        rw [av_bag, Finset.mem_insert] at hxy
        rcases hxy with rfl | hxy
        · exact Or.inr rfl
        · exact Or.inl (Or.inl ⟨n0, hn0, by rw [← hbg]; exact hxy⟩)
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo y hn
        exact Or.inl (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hxJ⟩))
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n (hMsub n hn)
        exact Or.inl (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hxJ⟩))
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.vsub x hxk with h | h
      · exact Or.inl (Or.inr (Or.inr ⟨k, hk, h⟩))
      · exact Or.inr h
  · -- vsup
    intro x hx
    rw [mem_verts_chainToRT] at hx ⊢
    rcases hx with ⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨k, hk, hxk⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact Or.inl ⟨y, h, hxy⟩
      · exact Or.inl ⟨av v y, h, by rw [av_bag]; exact Finset.mem_insert_of_mem hxy⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact Or.inr (Or.inl ⟨y, h, J, hJ, hxJ⟩)
      · exact Or.inr (Or.inl ⟨av v y, h, J, hJ, hxJ⟩)
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      exact Or.inr (Or.inr ⟨k', hk', hkk.vsup x hxk⟩)
  · -- bnew
    intro Y hY
    rcases (hb' Y).1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, -⟩ := hinfo y hn
        exact Or.inr ⟨n0.bag, (hb _).2 (Or.inl ⟨n0, hn0, rfl⟩), by rw [hYy, hbg]⟩
      · left
        rw [hYy, av_bag]
        exact Finset.mem_insert_self _ _
    · rcases hmem y hy with hn | ⟨n, hn, rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo y hn
        exact Or.inr ⟨Y, (hb Y).2 (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hYJ⟩)), subset_rfl⟩
      · obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n (hMsub n hn)
        exact Or.inr ⟨Y, (hb Y).2 (Or.inr (Or.inl ⟨n0, hn0, J, hj J hJ, hYJ⟩)), subset_rfl⟩
    · obtain ⟨k, hk, hkk⟩ := forall2_exists_right hK k' hk'
      rcases hkk.bnew Y hYk with h | ⟨X, hX, hYX⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, (hb X).2 (Or.inr (Or.inr ⟨k, hk, hX⟩)), hYX⟩
  · -- bsup
    intro X hX
    rcases (hb X).1 hX with ⟨y, hy, hXy⟩ | ⟨y, hy, J, hJ, hXJ⟩ | ⟨k, hk, hXk⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact ⟨y.bag, (hb' _).2 (Or.inl ⟨y, h, rfl⟩), by rw [hXy]⟩
      · exact ⟨(av v y).bag, (hb' _).2 (Or.inl ⟨av v y, h, rfl⟩),
          by rw [hXy, av_bag]; exact Finset.subset_insert _ _⟩
    · rcases hmem' y (hsub y hy) with h | h
      · exact ⟨X, (hb' _).2 (Or.inr (Or.inl ⟨y, h, J, hJ, hXJ⟩)), subset_rfl⟩
      · exact ⟨X, (hb' _).2 (Or.inr (Or.inl ⟨av v y, h, J, hJ, hXJ⟩)), subset_rfl⟩
    · obtain ⟨k', hk', hkk⟩ := forall2_exists_left hK k hk
      obtain ⟨Y, hY, hXY⟩ := hkk.bsup X hXk
      exact ⟨Y, (hb' _).2 (Or.inr (Or.inr ⟨k', hk', hY⟩)), hXY⟩
  · -- tcne
    intro u hu p
    obtain ⟨g, hg, hc2⟩ := hmap
    rw [hc2, tc_chain_mapIdx u _ g (fun i n => ⟨(hg i n).1 u hu, (hg i n).2⟩), tc_chain_dupOf u hdup]
    exact tc_chain_kids u ns K K' hns (tcL_of_forall2 hK hu) p


/-- Only the kids change. -/
theorem chain_kids_TI (v : ℕ) {ns : List CNode} {K K' : List RT} (hns : ns ≠ [])
    (hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK : List.Forall₂ (TI v) K K') :
    TI v (AR.chainToRT ns K) (AR.chainToRT ns K') := by
  have := chain_region_TI v (ns := ns) (L := ns) (M := []) (R := []) (K := K) (K' := K') (chain'' := ns) hns
    (by simpa using DupOf.refl (ns := ns)) hns hfree hK (by simp)
    ⟨fun _ n => n, fun i n => ⟨fun u _ => Iff.rfl, rfl⟩,
      by simp only [List.append_nil]; exact (List.ext_getElem (by simp) (by intro i h1 h2; simp)).symm⟩
  exact this


/-! ## the tops of the new vertex -/

theorem tc_v_MR (v : ℕ) {M R : List CNode} {K' : List RT} (hM : M ≠ [])
    (hMj : ∀ n ∈ M, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hR : ∀ n ∈ R, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0) (p : Bool) :
    tc v (AR.chainToRT (M.map (av v) ++ R) K') p = if p = false then 1 else 0 := by
  have hMfull : ∀ n ∈ M.map (av v), v ∈ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    exact ⟨by rw [av_bag]; exact Finset.mem_insert_self _ _, (hMj m hm).2⟩
  have hMne : M.map (av v) ≠ [] := by simpa using hM
  by_cases hRe : R = []
  · subst hRe
    rw [List.append_nil, tc_chain_full v _ K' p hMne hMfull, hK1 rfl]
    simp
  · rw [chainToRT_append _ _ K' hMne hRe, tc_chain_full v _ [AR.chainToRT R K'] p hMne hMfull]
    have := tc_chain_prefix_free v R K' true hRe hR
    have h2 := hK2 hRe
    simp only [tcL, this, h2]
    simp

theorem tc_v_region (v : ℕ) {L M R : List CNode} {K' : List RT} (hM : M ≠ [])
    (hL : ∀ n ∈ L, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hMj : ∀ n ∈ M, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hR : ∀ n ∈ R, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts)
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0) (p : Bool) :
    tc v (AR.chainToRT (L ++ M.map (av v) ++ R) K') p = if L = [] ∧ p = true then 0 else 1 := by
  have hMne : M.map (av v) ++ R ≠ [] := fun h => hM (List.map_eq_nil_iff.1 (List.append_eq_nil_iff.1 h).1)
  rw [List.append_assoc]
  by_cases hLe : L = []
  · subst hLe
    rw [List.nil_append, tc_v_MR v hM hMj hR hK1 hK2 p]
    by_cases hp : p = false <;> simp [hp]
  · rw [chainToRT_append _ _ K' hLe hMne, tc_chain_prefix_free v L _ p hLe hL]
    simp only [tcL]
    rw [tc_v_MR v hM hMj hR hK1 hK2 false]
    simp [hLe]

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeRegion` -/

section
/-!
# The characteristic of a chain with a region (work package C5, part 6)

`region_norm`: the normal form of the profile (with respect to `insert v B`) of a chain `L ++ M⁺ ++ R` (the middle
segment `M` with `v` added) with kids `K'` equals the normal form of the *nested* raw characteristic
`regionQ` : run `S` (sizes of `L`) above run `S ∪ {v}` (sizes of `M⁺`) above run `S` (sizes of `R`) above the kids.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem bags_free_of_verts {v : ℕ} {t : RT} (h : v ∉ t.verts) : ∀ X ∈ t.bags, v ∉ X := by
  intro X hX hv
  exact h ((RT.mem_verts_iff t v).2 ⟨X, hX, hv⟩)

/-- Junk stays prunable after adding a fresh vertex to the boundary. -/
theorem junk_keep {v : ℕ} {B S σ : Finset ℕ} {J : RT} (hJ : Jk B S J) (hv : v ∉ J.verts) (hσ : S ⊆ σ) :
    keep σ (norm (RT.prof (insert v B) J)) = false := by
  rw [prof_insert_of_free v B J (bags_free_of_verts hv)]
  have h1 : norm (RT.prof B J) = J.char B := rfl
  rw [h1, char_eq_charF, AR.keep_charF]
  obtain ⟨hleaf, hsub⟩ := hJ
  simp [hleaf, hsub.trans hσ]

/-- An unchanged kid keeps its characteristic. -/
theorem norm_prof_kid {v : ℕ} {B : Finset ℕ} {k : AR} (hk : Canon B k) (hv : v ∉ (AR.toRT k).verts) :
    norm (RT.prof (insert v B) (AR.toRT k)) = AR.charF Finset.card k := by
  rw [prof_insert_of_free v B _ (bags_free_of_verts hv)]
  have : norm (RT.prof B (AR.toRT k)) = (AR.toRT k).char B := rfl
  rw [this, char_eq_charF, analyze_toRT B k hk]

/-- The raw nested characteristic of a chain with a region. -/
def regionQ (v : ℕ) (S : Finset ℕ) (L M R : List CNode) (KQ : List CT) : CT :=
  let Rq : List CT := if R = [] then KQ else [CT.node S (typical (csz R)) KQ]
  let Mq : CT := CT.node (insert v S) (typical (csz (M.map (av v)))) Rq
  if L = [] then Mq else CT.node S (typical (csz L)) [Mq]

theorem inter_insert_of_not_mem {v : ℕ} {X B : Finset ℕ} (hv : v ∉ X) : X ∩ insert v B = X ∩ B := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨h1, rfl | h2⟩
    · exact absurd h1 hv
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩

theorem inter_insert_insert {v : ℕ} {X B : Finset ℕ} : insert v X ∩ insert v B = insert v (X ∩ B) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert]
  tauto

theorem region_norm (v : ℕ) (B S : Finset ℕ) (hvB : v ∉ B) {ns L M R : List CNode} {K' : List RT} (KQ : List CT)
    (hM : M ≠ [])
    (hinfo : ∀ n ∈ L ++ M ++ R, ∃ n0 ∈ ns, n.bag = n0.bag ∧ ∀ J ∈ n.junk, J ∈ n0.junk)
    (hbase : ∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts)
    (hKQ : KQ.map norm = (K'.map (RT.prof (insert v B))).map norm) :
    norm (RT.prof (insert v B) (AR.chainToRT (L ++ M.map (av v) ++ R) K')) = norm (regionQ v S L M R KQ) := by
  have hn0 : ∀ n ∈ L ++ M ++ R, n.bag ∩ B = S ∧ v ∉ n.bag ∧ ∀ J ∈ n.junk, Jk B S J ∧ v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hb, hj⟩ := hinfo n hn
    obtain ⟨h1, h2, h3⟩ := hbase n0 hn0
    exact ⟨by rw [hb]; exact h1, by rw [hb]; exact h2, fun J hJ => h3 J (hj J hJ)⟩
  have hL : ∀ n ∈ L, n.bag ∩ insert v B = S ∧ ∀ J ∈ n.junk, keep S (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hn0 n (by simp [hn])
    exact ⟨by rw [inter_insert_of_not_mem h2]; exact h1,
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 subset_rfl⟩
  have hR : ∀ n ∈ R, n.bag ∩ insert v B = S ∧ ∀ J ∈ n.junk, keep S (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hn0 n (by simp [hn])
    exact ⟨by rw [inter_insert_of_not_mem h2]; exact h1,
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 subset_rfl⟩
  have hMo : ∀ n ∈ M.map (av v), n.bag ∩ insert v B = insert v S ∧
      ∀ J ∈ n.junk, keep (insert v S) (norm (RT.prof (insert v B) J)) = false := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hn
    obtain ⟨h1, h2, h3⟩ := hn0 m (by simp [hm])
    exact ⟨by rw [av_bag, inter_insert_insert, h1],
      fun J hJ => junk_keep (h3 J hJ).1 (h3 J hJ).2 (Finset.subset_insert _ _)⟩
  have hMne : M.map (av v) ≠ [] := by simpa using hM
  -- generic step
  have step : ∀ (C : List CNode) (ℓ : Finset ℕ) (K : List RT) (KQ' : List CT), C ≠ [] →
      (∀ n ∈ C, n.bag ∩ insert v B = ℓ ∧ ∀ J ∈ n.junk, keep ℓ (norm (RT.prof (insert v B) J)) = false) →
      KQ'.map norm = (K.map (RT.prof (insert v B))).map norm →
      norm (RT.prof (insert v B) (AR.chainToRT C K)) = norm (CT.node ℓ (typical (csz C)) KQ') := by
    intro C ℓ K KQ' hC hok hK
    rw [chain_norm (insert v B) ℓ C K hC hok, norm_node', hK]
  have hRstep : R ≠ [] → norm (RT.prof (insert v B) (AR.chainToRT R K')) =
      norm (CT.node S (typical (csz R)) KQ) := fun hRe => step R S K' KQ hRe hR hKQ
  -- the middle part
  have hMstep : norm (RT.prof (insert v B) (AR.chainToRT (M.map (av v) ++ R) K')) =
      norm (CT.node (insert v S) (typical (csz (M.map (av v)))) (if R = [] then KQ else [CT.node S (typical (csz R)) KQ])) := by
    by_cases hRe : R = []
    · subst hRe
      rw [List.append_nil, if_pos rfl]
      exact step _ _ K' KQ hMne hMo hKQ
    · rw [if_neg hRe, chainToRT_append _ _ K' hMne hRe]
      apply step _ _ [AR.chainToRT R K'] _ hMne hMo
      simp only [List.map_cons, List.map_nil, hRstep hRe]
  have hMne' : M.map (av v) ++ R ≠ [] := fun h => hMne (List.append_eq_nil_iff.1 h).1
  by_cases hLe : L = []
  · subst hLe
    rw [List.nil_append, hMstep]
    simp [regionQ]
  · rw [List.append_assoc, chainToRT_append _ _ K' hLe hMne']
    have := step L S [AR.chainToRT (M.map (av v) ++ R) K'] [CT.node (insert v S) (typical (csz (M.map (av v))))
      (if R = [] then KQ else [CT.node S (typical (csz R)) KQ])] hLe hL (by
        simp only [List.map_cons, List.map_nil, hMstep])
    rw [this]
    simp [regionQ, hLe]


/-- Everything about a chain with a region, in one statement. -/
theorem region_PRC (v : ℕ) (B S : Finset ℕ) (hvB : v ∉ B) {ns L M R : List CNode} {ks : List AR}
    {K' : List RT} (KQ : List CT) {chain'' : List CNode} (hns : ns ≠ []) (hM : M ≠ [])
    (hbase : ∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts)
    (hdup : DupOf ns (L ++ M ++ R)) (hchain : chain'' = L ++ M.map (av v) ++ R)
    (hmap : ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧
        (g i n).junk = n.junk) ∧ chain'' = (L ++ M ++ R).mapIdx g)
    (hK : List.Forall₂ (TI v) (ks.map AR.toRT) K')
    (hK1 : R = [] → tcL v K' true = 0) (hK2 : R ≠ [] → tcL v K' false = 0)
    (hKQ : KQ.map norm = (K'.map (RT.prof (insert v B))).map norm) :
    TI v (AR.chainToRT ns (ks.map AR.toRT)) (AR.chainToRT chain'' K') ∧
    (∀ p, tc v (AR.chainToRT chain'' K') p = if L = [] ∧ p = true then 0 else 1) ∧
    norm (RT.prof (insert v B) (AR.chainToRT chain'' K')) = norm (regionQ v S L M R KQ) ∧
    (∀ Y ∈ (AR.chainToRT chain'' K').bags, v ∈ Y → (∃ m ∈ M, Y = insert v m.bag) ∨ ∃ k' ∈ K', Y ∈ k'.bags) ∧
    (∀ m ∈ M, insert v m.bag ∈ (AR.chainToRT chain'' K').bags) := by
  have hinfo := hdup.info
  have hfree : ∀ n ∈ ns, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts :=
    fun n hn => ⟨(hbase n hn).2.1, fun J hJ => ((hbase n hn).2.2 J hJ).2⟩
  have hfree2 : ∀ n ∈ (L ++ M ++ R), v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts := by
    intro n hn
    obtain ⟨n0, hn0, hbg, hj⟩ := hinfo n hn
    obtain ⟨h1, h2⟩ := hfree n0 hn0
    exact ⟨by rw [hbg]; exact h1, fun J hJ => h2 J (hj J hJ)⟩
  have hne'' : chain'' ≠ [] := by
    obtain ⟨m0, M', rfl⟩ := List.exists_cons_of_ne_nil hM
    rw [hchain]; simp
  have hb' := mem_bags_chainToRT K' chain'' hne''
  refine ⟨chain_region_TI v hns hdup hne'' hfree hK hchain hmap, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [hchain]
    exact tc_v_region v hM (fun n hn => hfree2 n (by simp [hn])) (fun n hn => hfree2 n (by simp [hn]))
      (fun n hn => hfree2 n (by simp [hn])) hK1 hK2 p
  · rw [hchain]
    exact region_norm v B S hvB KQ hM hinfo hbase hKQ
  · intro Y hY hvY
    rcases (hb' Y).1 hY with ⟨y, hy, rfl⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨k', hk', hYk⟩
    · rw [hchain] at hy
      simp only [List.mem_append, List.mem_map] at hy
      rcases hy with (hy | ⟨m, hm, rfl⟩) | hy
      · exact absurd hvY (hfree2 y (by simp [hy])).1
      · exact Or.inl ⟨m, hm, rfl⟩
      · exact absurd hvY (hfree2 y (by simp [hy])).1
    · rw [hchain] at hy
      simp only [List.mem_append, List.mem_map] at hy
      have hJv : v ∈ J.verts := (RT.mem_verts_iff J v).2 ⟨Y, hYJ, hvY⟩
      rcases hy with (hy | ⟨m, hm, rfl⟩) | hy
      · exact absurd hJv ((hfree2 y (by simp [hy])).2 J hJ)
      · exact absurd hJv ((hfree2 m (by simp [hm])).2 J hJ)
      · exact absurd hJv ((hfree2 y (by simp [hy])).2 J hJ)
    · exact Or.inr ⟨k', hk', hYk⟩
  · intro m hm
    rw [hb']
    left
    exact ⟨av v m, by rw [hchain]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm)), rfl⟩

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeWin` -/

section
/-!
# The region step `processRun` realises `winPlans` (work package C5, part 7)

Definitions of the run-level invariants (`RunOk`, `PRC`, `KC`) and the plan-level lemmas.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- A canonical analysed run, disjoint from the fresh vertex. -/
structure RunOk (v : ℕ) (B : Finset ℕ) (x : AR) : Prop where
  canon : Canon B x
  free : v ∉ (AR.toRT x).verts

theorem runOk_run {v : ℕ} {B S : Finset ℕ} {ns : List CNode} {ks : List AR} (h : RunOk v B (.run S ns ks)) :
    ns ≠ [] ∧ (∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts) ∧
    (∀ k ∈ ks, RunOk v B k) ∧ (ks = [] → ns.length = 1) ∧ (∀ k ∈ ks, prunedB S k = false) ∧ S ⊆ B ∧
    (∀ k ∈ ks, v ∉ (AR.toRT k).verts) := by
  obtain ⟨hc, hf⟩ := h
  rw [canon_run] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  rw [AR.toRT_run, mem_verts_chainToRT] at hf
  push_neg at hf
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hkf : ∀ k ∈ ks, v ∉ (AR.toRT k).verts := fun k hk => hf3 _ (List.mem_map.2 ⟨k, hk, rfl⟩)
  refine ⟨h1, fun n0 hn0 => ⟨(h2 n0 hn0).1, hf1 n0 hn0, fun J hJ => ⟨(h2 n0 hn0).2 J hJ, hf2 n0 hn0 J hJ⟩⟩,
    fun k hk => ⟨h7 k hk, hkf k hk⟩, h6, h3, ?_, hkf⟩
  obtain ⟨n0, hn0⟩ := List.exists_mem_of_ne_nil ns h1
  rw [← (h2 n0 hn0).1]; exact Finset.inter_subset_right

theorem verts_charF_sub {B : Finset ℕ} : ∀ x : AR, Canon B x → CT.verts (AR.charF Finset.card x) ⊆ B := by
  intro x
  induction x using AR.ind with
  | _ S c ks ih =>
    intro h
    rw [canon_run] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [AR.charF_run, CT.verts_node]
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨n0, hn0⟩ := List.exists_mem_of_ne_nil c h1
      have := (h2 n0 hn0).1
      rw [← this] at hy
      exact (Finset.mem_inter.1 hy).2
    · obtain ⟨k, hk, hyk⟩ := (CT.mem_vertsL).1 hy
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk
      exact ih k0 hk0 (h7 k0 hk0) hyk

theorem nested_ins {v : ℕ} {B : Finset ℕ} (hv : v ∉ B) (p : CT) (σ : Finset ℕ) (hb : CT.verts p ⊆ B)
    (h : Nested (insert v σ) p) : Nested σ p := by
  cases p with
  | node S y ks =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, h2⟩
    intro x hx
    have := h1 hx
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hb (by simp [CT.verts_node, hx])) hv
    · exact h3

/-! ## kid choices -/

theorem kidChoices_forall2 (v : ℕ) : ∀ (ks : List CT) (combo : List (Option WPlan × CT × Finset ℕ)),
    combo ∈ kidChoices v ks ↔
      List.Forall₂ (fun k o => (o.1 = none ∧ o.2.1 = k ∧ o.2.2 = ∅) ∨
        (∃ wp, o.1 = some wp ∧ (wp, o.2.1, o.2.2) ∈ winPlans v 0 k)) ks combo := by
  intro ks
  induction ks with
  | nil =>
    intro combo
    simp only [kidChoices, List.mem_singleton]
    constructor
    · rintro rfl; exact List.Forall₂.nil
    · intro h; cases h; rfl
  | cons k ks ih =>
    intro combo
    simp only [kidChoices, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨o, ho, combo', hc', rfl⟩
      refine List.Forall₂.cons ?_ ((ih combo').1 hc')
      rcases List.mem_cons.1 ho with rfl | ho
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact Or.inr ⟨p.1, rfl, hp⟩
    · intro h
      cases h with
      | cons hk hrest =>
        rename_i o combo'
        refine ⟨o, ?_, combo', (ih combo').2 hrest, rfl⟩
        rcases hk with ⟨h1, h2, h3⟩ | ⟨wp, h1, h2⟩
        · apply List.mem_cons.2; left
          obtain ⟨o1, o2, o3⟩ := o
          simp only at h1 h2 h3
          subst h1; subst h2; subst h3; rfl
        · apply List.mem_cons_of_mem
          obtain ⟨o1, o2, o3⟩ := o
          simp only at h1 h2
          subst h1
          exact List.mem_map.2 ⟨(wp, o2, o3), h2, rfl⟩


/-! ## small lemmas -/

theorem dom_maxOf_le {a b : List ℕ} (h : Dom a b) : maxOf a ≤ maxOf b := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  have key : ∀ (a' b' : List ℕ), LeSeq a' b' → ∀ x ∈ a', x ≤ maxOf b' := by
    intro a' b' hle
    induction hle with
    | nil => intro x hx; simp at hx
    | @cons x y l1 l2 hxy _ ih =>
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy.trans (le_maxOf (List.mem_cons_self))
      · exact (ih z hz).trans (by rw [maxOf_cons]; exact le_max_right _ _)
  have h1 : maxOf a ≤ maxOf a' := maxOf_le fun x hx => le_maxOf ((ha.mem).2 hx)
  have h2 : maxOf b' ≤ maxOf b := maxOf_le fun x hx => le_maxOf ((hb.mem).1 hx)
  refine h1.trans ((maxOf_le fun x hx => key a' b' hle x hx).trans h2)

theorem csz_map_av {v : ℕ} {M : List CNode} (h : ∀ n ∈ M, v ∉ n.bag) : csz (M.map (av v)) = (csz M).map (· + 1) := by
  unfold csz
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro n hn
  simp [av_bag, Finset.card_insert_of_notMem (h n hn)]

theorem mem_csz {ns : List CNode} {n : CNode} (h : n ∈ ns) : n.bag.card ∈ csz ns :=
  List.mem_map.2 ⟨n, h, rfl⟩

/-! ## the invariant of a processed run -/

/-- What `processRun` achieves on a run: topology, new vertex, coverage, characteristic, width. -/
structure PRC (v : ℕ) (B : Finset ℕ) (x x' : AR) (rep : CT) (cov : Finset ℕ) (hasPre : Bool) : Prop where
  ti : TI v (AR.toRT x) (AR.toRT x')
  tcv : ∀ p, tc v (AR.toRT x') p = if hasPre = false ∧ p = true then 0 else 1
  vin : v ∈ (AR.toRT x').verts
  cov : ∀ u ∈ cov, ∃ Y ∈ (AR.toRT x').bags, v ∈ Y ∧ u ∈ Y
  chr : ∃ Q, norm (RT.prof (insert v B) (AR.toRT x')) = norm Q ∧ DomC Q rep
  wid : ∀ Y ∈ (AR.toRT x').bags, v ∈ Y → Y.card ≤ maxEntry (norm rep)
  vrep : v ∈ CT.verts rep
  nest : hasPre = false → ∀ σ, ¬ Nested σ (AR.charF Finset.card x) → ¬ Nested (insert v σ) rep

/-- The same for a kid of a region run (processed or not). -/
structure KC (v : ℕ) (B : Finset ℕ) (k k' : AR) (rep : CT) (cov : Finset ℕ) : Prop where
  ti : TI v (AR.toRT k) (AR.toRT k')
  tcv : tc v (AR.toRT k') true = 0
  cov : ∀ u ∈ cov, ∃ Y ∈ (AR.toRT k').bags, v ∈ Y ∧ u ∈ Y
  chr : ∃ Q, norm (RT.prof (insert v B) (AR.toRT k')) = norm Q ∧ DomC Q rep
  wid : ∀ Y ∈ (AR.toRT k').bags, v ∈ Y → Y.card ≤ maxEntry (norm rep)
  nest : ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) rep

theorem PRC.kc {v : ℕ} {B : Finset ℕ} {x x' : AR} {rep : CT} {cov : Finset ℕ} (h : PRC v B x x' rep cov false) :
    KC v B x x' rep cov :=
  ⟨h.ti, by simpa using h.tcv true, h.cov, h.chr, h.wid, h.nest rfl⟩

theorem kc_unchanged {v : ℕ} {B : Finset ℕ} {k : AR} (hv : v ∉ B) (hk : RunOk v B k) :
    KC v B k k (AR.charF Finset.card k) ∅ := by
  have hn := norm_prof_kid hk.canon hk.free
  refine ⟨TI.refl v _, tc_zero_of_notin v _ true hk.free, by simp, ⟨AR.charF Finset.card k, ?_, DomC.refl _⟩,
    ?_, ?_⟩
  · rw [hn]
    have : norm (AR.charF Finset.card k) = AR.charF Finset.card k := by
      rw [← hn, norm_idem]
    rw [this]
  · intro Y hY hvY
    exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hY, hvY⟩) hk.free
  · intro σ hσ hN
    exact hσ (nested_ins hv _ σ (verts_charF_sub k hk.canon) hN)


theorem addV_map (v s : ℕ) (e : Option ℕ) (ns : List CNode) :
    ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧ (g i n).junk = n.junk) ∧
      addV v s e ns = ns.mapIdx g := by
  refine ⟨fun i n => if decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e)) then ⟨insert v n.bag, n.junk⟩ else n,
    ?_, rfl⟩
  intro i n
  dsimp only
  split_ifs
  · refine ⟨fun u hu => ?_, rfl⟩
    simp [Finset.mem_insert, hu]
  · exact ⟨fun u _ => Iff.rfl, rfl⟩

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeEnd` -/

section
/-!
# The end-case of the region step (work package C5, part 8)

`pr_end`: `processRun v pre (endAt c₂)` realises the plan `top pre (endAt c₂)`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The replacement subtree of a plan with an optional pre-cut. -/
def topRep (S : Finset ℕ) (y : List ℕ) : Option Cut → CT → CT
  | none, X => X
  | some c, X => CT.node S (y.take (cHi c + 1)) [X]

def preLo : Option Cut → ℕ
  | none => 0
  | some c => cLo c

theorem kid_keep {v : ℕ} {B S : Finset ℕ} {k : AR} (hk : RunOk v B k) (hp : prunedB S k = false) :
    keep S (norm (AR.charF Finset.card k)) = true := by
  have hn := norm_prof_kid hk.canon hk.free
  have : norm (AR.charF Finset.card k) = AR.charF Finset.card k := by rw [← hn, norm_idem]
  rw [this, AR.keep_charF]
  have : (k.isLeaf && decide (k.S ⊆ S)) = false := hp
  simp [this]

theorem processRun_endAt_eq (v : ℕ) (pre : Option Cut) (c : Cut) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    processRun v pre (.endAt c) (.run S ns ks) =
      .run S (processRun v pre (.endAt c) (.run S ns ks)).chain ks := by
  rw [processRun_chain_eq, processRun_eq]

theorem toRT_processRun_endAt (v : ℕ) (pre : Option Cut) (c : Cut) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    AR.toRT (processRun v pre (.endAt c) (.run S ns ks)) =
      AR.chainToRT (processRun v pre (.endAt c) (.run S ns ks)).chain (ks.map AR.toRT) := by
  conv_lhs => rw [processRun_endAt_eq]
  rw [AR.toRT_run]


theorem kids_norm_prof {v : ℕ} {B : Finset ℕ} {ks : List AR} (hk : ∀ k ∈ ks, RunOk v B k) :
    (ks.map (AR.charF Finset.card)).map norm = ((ks.map AR.toRT).map (RT.prof (insert v B))).map norm := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro k hkk
  have hn := norm_prof_kid (hk k hkk).canon (hk k hkk).free
  simp only [Function.comp]
  rw [← hn, norm_idem]

theorem pr_end (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) (pre : Option Cut) (c2 : Cut)
    (hpre : PreOk (typical (csz ns)).length pre) (hc2 : c2.Valid (typical (csz ns)).length)
    (hlh : LoHi pre (.endAt c2)) :
    PRC v B (.run S ns ks) (processRun v pre (.endAt c2) (.run S ns ks))
      (topRep S (typical (csz ns)) pre
        (CT.node (insert v S) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
          [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))]))
      S pre.isSome := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hs : csz ns ≠ [] := by
    intro h; apply hns; unfold csz at h; exact List.map_eq_nil_iff.1 h
  have hlenw : (witnesses (csz ns)).length = (typical (csz ns)).length := (witnesses_cover (csz ns)).len
  have hp' : PreOk (witnesses (csz ns)).length pre := by rw [hlenw]; exact hpre
  have hw' : WOk (witnesses (csz ns)).length (.endAt c2) := by
    show c2.Valid _; rw [hlenw]; exact hc2
  obtain ⟨L, M, R, ns2, st, re, hdup, hns2, hchainA, hchain, hcL, hcM, hcR, hMne, hL0, hL1, hRw, hRe⟩ :=
    processRun_chain v pre (.endAt c2) S ns ks hns hp' hw' hlh
  have hRne : R ≠ [] := hRe c2 rfl
  have hinfo := hdup.info
  have hMsub : ∀ m ∈ M, m ∈ (L ++ M ++ R) := fun n hn => by simp [hn]
  -- kids
  have hK : List.Forall₂ (TI v) (ks.map AR.toRT) (ks.map AR.toRT) := List.forall₂_same.2 (fun k _ => TI.refl v k)
  have hKQ := kids_norm_prof (v := v) (B := B) hkids
  have hK1 : R = [] → tcL v (ks.map AR.toRT) true = 0 := fun h => absurd h hRne
  have hK2 : R ≠ [] → tcL v (ks.map AR.toRT) false = 0 := by
    intro _
    rw [tcL_eq_sum, List.sum_eq_zero]
    intro x hx'
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
    exact tc_zero_of_notin v _ false (hkfree k hk)
  obtain ⟨hTI, htc, hnorm, hvb, hmb⟩ := region_PRC v B S hvB (ns := ns) (L := L) (M := M) (R := R) (ks := ks)
    (K' := ks.map AR.toRT) (ks.map (AR.charF Finset.card)) (chain'' := (processRun v pre (.endAt c2) (.run S ns ks)).chain)
    hns hMne hbase (by rw [← hns2]; exact hdup) hchain (by
      obtain ⟨g, hg, he⟩ := addV_map v st re ns2
      exact ⟨g, hg, by rw [hchainA, he, hns2]⟩) hK hK1 hK2 hKQ
  rw [hchain] at hTI htc hnorm hvb hmb
  have hxt : AR.toRT (processRun v pre (.endAt c2) (.run S ns ks)) =
      AR.chainToRT (L ++ M.map (av v) ++ R) (ks.map AR.toRT) := by
    rw [toRT_processRun_endAt, hchain]
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hMfree : ∀ m ∈ M, v ∉ m.bag := by
    intro m hm
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    rw [hb]; exact (hbase n0 hn0).2.1
  have hc2' : c2.Valid (witnesses (csz ns)).length := by rw [hlenw]; exact hc2
  -- dominance of the three pieces
  have hM : Dom (typical (csz M)) (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)) := by
    rw [hcM]
    cases pre with
    | none =>
      have := dom_left hs hc2'
      simpa [preAB, endAB, preLo] using this
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have := (dom_mid hs hc1' hc2' hlh).2
      simpa [preAB, endAB, preLo] using this
  have hR : Dom (typical (csz R)) ((typical (csz ns)).drop (cLo c2)) := by
    rw [hcR]; exact dom_right hs hc2'
  have hMq : Dom (typical (csz (M.map (av v)))) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre))) := by
    rw [csz_map_av hMfree, typical_plus1]
    unfold plus1
    exact dom_map_succ hM
  -- the region
  have hwin : DomC (CT.node (insert v S) (typical (csz (M.map (av v)))) [CT.node S (typical (csz R)) (ks.map (AR.charF Finset.card))])
      (CT.node (insert v S) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
          [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))]) :=
    ⟨rfl, hMq, ⟨⟨rfl, hR, DomCL.refl _⟩, trivial⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; exact hTI
  · intro p
    rw [hxt, htc p]
    cases pre with
    | none => simp [hL0 rfl]
    | some c1 => simp [hL1 (by simp)]
  · rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    exact (RT.mem_verts_iff _ v).2 ⟨insert v m.bag, hmb m hm, Finset.mem_insert_self _ _⟩
  · intro u hu
    rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    refine ⟨insert v m.bag, hmb m hm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
    have : u ∈ n0.bag ∩ B := by rw [(hbase n0 hn0).1]; exact hu
    rw [hb]; exact (Finset.mem_inter.1 this).1
  · -- chr
    refine ⟨regionQ v S L M R (ks.map (AR.charF Finset.card)), by rw [hxt]; exact hnorm, ?_⟩
    cases pre with
    | none =>
      simp only [regionQ, if_neg hRne, hL0 rfl, if_true, topRep]
      exact hwin
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have hL : Dom (typical (csz L)) ((typical (csz ns)).take (cHi c1 + 1)) := by
        rw [hcL]; simpa [preAB] using dom_left hs hc1'
      have hLne : L ≠ [] := hL1 (by simp)
      simp only [regionQ, if_neg hRne, if_neg hLne, topRep]
      exact ⟨rfl, hL, ⟨hwin, trivial⟩⟩
  · -- wid
    intro Y hY hvY
    rw [hxt] at hY
    have hkeep : (∃ k ∈ [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))],
        keep (insert v S) (norm k) = true) ∨
        (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre))).length ≤ 1 := by
      by_cases hka : ks = []
      · right
        have h1 : ns.length = 1 := hleaf hka
        have hy1 : (typical (csz ns)).length ≤ 1 := by
          obtain ⟨x0, hx0⟩ : ∃ x0, csz ns = [x0] := by
            have : (csz ns).length = 1 := by rw [csz_length]; exact h1
            exact List.length_eq_one_iff.1 this
          rw [hx0, typical_singleton]; simp
        simp only [plus1, List.length_map, List.length_drop, List.length_take]
        omega
      · left
        obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil ks hka
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        by_contra hcon
        have hf : keep (insert v S) (norm (CT.node S ((typical (csz ns)).drop (cLo c2))
            (ks.map (AR.charF Finset.card)))) = false := by simpa using hcon
        have hnest := (keep_norm_false_iff _ _).1 hf
        obtain ⟨-, hL⟩ := hnest
        have h1 := (nestedL_iff_keep S _).2 hL (AR.charF Finset.card k0) (List.mem_map.2 ⟨k0, hk0, rfl⟩)
        have h2 := kid_keep (hkids k0 hk0) (hkp k0 hk0)
        rw [h1] at h2
        exact absurd h2 (by simp)
    have hwidwin : Y.card ≤ maxEntry (norm (CT.node (insert v S)
        (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
        [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))])) := by
      rcases hvb Y hY hvY with ⟨m, hm, rfl⟩ | ⟨k', hk', hYk⟩
      · have h1 : (insert v m.bag).card ∈ csz (M.map (av v)) := mem_csz (List.mem_map_of_mem hm)
        have h2 := le_maxOf h1
        rw [← maxOf_typical] at h2
        refine h2.trans ((dom_maxOf_le hMq).trans (maxOf_le fun e he => norm_y_le hkeep he))
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
        exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hYk, hvY⟩) (hkfree k hk)
    cases pre with
    | none => exact hwidwin
    | some c1 =>
      refine hwidwin.trans (norm_kid_le (K := [_]) (List.mem_singleton_self _) ?_)
      exact keep_of_mem_verts (by simp [CT.verts_node]) (fun h => hvB (hSB h))
  · -- vrep
    cases pre with
    | none => simp [topRep, CT.verts_node]
    | some c1 =>
      simp only [topRep]
      exact CT.mem_verts.2 (Or.inr ⟨_, List.mem_singleton_self _,
        CT.mem_verts.2 (Or.inl (Finset.mem_insert_self _ _))⟩)
  · -- nest
    intro hpre σ hσ hN
    have hpre' : pre = none := by cases pre <;> simp_all
    subst hpre'
    simp only [topRep] at hN
    obtain ⟨h1, h2, -⟩ := hN
    apply hσ
    rw [AR.charF_run]
    refine ⟨?_, h2.2⟩
    intro z hz
    have := h1 (Finset.mem_insert_of_mem hz)
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hSB hz) hvB
    · exact h3

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeWhole` -/

section
/-!
# The whole-case of the region step (work package C5, part 9)

`kc_agg`: the aggregated invariants of a list of kids, processed or not; `pr_whole`: `processRun v pre (whole ps)`
realises the plan `top pre (whole ps)`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

section Agg

variable {v : ℕ} {B : Finset ℕ}

theorem kc_agg {ks : List AR} {combo : List (Option WPlan × CT × Finset ℕ)}
    (hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo) :
    List.Forall₂ (TI v) (ks.map AR.toRT) ((applyKids v (combo.map (·.1)) ks).map AR.toRT) ∧
    tcL v ((applyKids v (combo.map (·.1)) ks).map AR.toRT) true = 0 ∧
    (∃ Qs : List CT, Qs.map norm = (((applyKids v (combo.map (·.1)) ks).map AR.toRT).map (RT.prof (insert v B))).map norm ∧
      DomCL Qs (combo.map (·.2.1))) ∧
    (∀ Y (k' : AR), k' ∈ applyKids v (combo.map (·.1)) ks → Y ∈ (AR.toRT k').bags → v ∈ Y →
      ∃ r ∈ combo.map (·.2.1), Y.card ≤ maxEntry (norm r)) ∧
    (∀ u ∈ combo.foldl (fun a c => a ∪ c.2.2) ∅,
      ∃ k' ∈ applyKids v (combo.map (·.1)) ks, ∃ Y ∈ (AR.toRT k').bags, v ∈ Y ∧ u ∈ Y) ∧
    List.Forall₂ (fun k r => ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) r) ks (combo.map (·.2.1)) := by
  induction hkc with
  | nil =>
    simp only [List.map_nil, applyKids]
    refine ⟨List.Forall₂.nil, rfl, ⟨[], rfl, trivial⟩, ?_, ?_, List.Forall₂.nil⟩
    · intro Y k' hk'; simp at hk'
    · intro u hu; simp at hu
  | @cons k o ks combo hk hrest ih =>
    obtain ⟨ih1, ih2, ⟨Qs, ih3, ih3'⟩, ih4, ih5, ih6⟩ := ih
    simp only [List.map_cons, applyKids]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.Forall₂.cons hk.ti ih1
    · rw [tcL, hk.tcv, ih2]
    · obtain ⟨Q, hQ1, hQ2⟩ := hk.chr
      refine ⟨Q :: Qs, ?_, ⟨hQ2, ih3'⟩⟩
      simp only [List.map_cons]
      rw [hQ1, ih3]
    · intro Y k' hk' hY hvY
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨o.2.1, List.mem_cons_self, hk.wid Y hY hvY⟩
      · obtain ⟨r, hr, h⟩ := ih4 Y k' hk' hY hvY
        exact ⟨r, List.mem_cons_of_mem _ hr, h⟩
    · intro u hu
      rw [List.foldl_cons] at hu
      have hfold : ∀ (S0 : Finset ℕ) (l : List (Option WPlan × CT × Finset ℕ)),
          l.foldl (fun a c => a ∪ c.2.2) S0 = S0 ∪ l.foldl (fun a c => a ∪ c.2.2) ∅ := by
        intro S0 l
        induction l generalizing S0 with
        | nil => simp
        | cons c l ih' =>
          simp only [List.foldl_cons]
          rw [ih' (S0 ∪ c.2.2), ih' (∅ ∪ c.2.2)]
          simp [Finset.union_assoc]
      rw [hfold] at hu
      simp only [Finset.empty_union, Finset.mem_union] at hu
      rcases hu with hu | hu
      · obtain ⟨Y, hY, hvY, huY⟩ := hk.cov u hu
        exact ⟨applyOpt v o.1 k, List.mem_cons_self, Y, hY, hvY, huY⟩
      · obtain ⟨k', hk', h⟩ := ih5 u (by simpa using hu)
        exact ⟨k', List.mem_cons_of_mem _ hk', h⟩
    · exact List.Forall₂.cons hk.nest ih6

theorem nestedL_of_forall2 {S : Finset ℕ} {ks : List AR} {rs : List CT}
    (h : List.Forall₂ (fun k r => ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) r) ks rs)
    (hN : NestedL (insert v S) rs) : NestedL S (ks.map (AR.charF Finset.card)) := by
  induction h with
  | nil => trivial
  | @cons k r ks rs hkr _ ih =>
    obtain ⟨h1, h2⟩ := hN
    refine ⟨?_, ih h2⟩
    by_contra hcon
    exact hkr S hcon h1

end Agg


theorem toRT_processRun_whole (v : ℕ) (pre : Option Cut) (ps : List (Option WPlan)) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    AR.toRT (processRun v pre (.whole ps) (.run S ns ks)) =
      AR.chainToRT (processRun v pre (.whole ps) (.run S ns ks)).chain ((applyKids v ps ks).map AR.toRT) := by
  have h : processRun v pre (.whole ps) (.run S ns ks) =
      .run S (processRun v pre (.whole ps) (.run S ns ks)).chain (applyKids v ps ks) := by
    rw [processRun_chain_eq, processRun_eq]
  conv_lhs => rw [h]
  rw [AR.toRT_run]

theorem pr_whole (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) (pre : Option Cut) (combo : List (Option WPlan × CT × Finset ℕ))
    (hpre : PreOk (typical (csz ns)).length pre)
    (hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo) :
    PRC v B (.run S ns ks) (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks))
      (topRep S (typical (csz ns)) pre
        (CT.node (insert v S) (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1))))
      (combo.foldl (fun a c => a ∪ c.2.2) S) pre.isSome := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hs : csz ns ≠ [] := by
    intro h; apply hns; unfold csz at h; exact List.map_eq_nil_iff.1 h
  have hlenw : (witnesses (csz ns)).length = (typical (csz ns)).length := (witnesses_cover (csz ns)).len
  have hp' : PreOk (witnesses (csz ns)).length pre := by rw [hlenw]; exact hpre
  have hw' : WOk (witnesses (csz ns)).length (.whole (combo.map (·.1))) := trivial
  have hlh : LoHi pre (.whole (combo.map (·.1))) := by cases pre <;> exact trivial
  obtain ⟨L, M, R, ns2, st, re, hdup, hns2, hchainA, hchain, hcL, hcM, hcR, hMne, hL0, hL1, hRw, hRe⟩ :=
    processRun_chain v pre (.whole (combo.map (·.1))) S ns ks hns hp' hw' hlh
  have hR0 : R = [] := hRw _ rfl
  subst hR0
  have hinfo := hdup.info
  have hMsub : ∀ m ∈ M, m ∈ (L ++ M ++ []) := fun n hn => by simp [hn]
  obtain ⟨hA1, hA2, ⟨Qs, hA3, hA3'⟩, hA4, hA5, hA6⟩ := kc_agg hkc
  obtain ⟨hTI, htc, hnorm, hvb, hmb⟩ := region_PRC v B S hvB (ns := ns) (L := L) (M := M) (R := []) (ks := ks)
    (K' := (applyKids v (combo.map (·.1)) ks).map AR.toRT) Qs
    (chain'' := (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks)).chain)
    hns hMne hbase (by rw [← hns2]; exact hdup) hchain (by
      obtain ⟨g, hg, he⟩ := addV_map v st re ns2
      exact ⟨g, hg, by rw [hchainA, he, hns2]⟩) hA1 (fun _ => hA2) (fun h => absurd rfl h) hA3
  rw [hchain] at hTI htc hnorm hvb hmb
  have hxt : AR.toRT (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks)) =
      AR.chainToRT (L ++ M.map (av v) ++ []) ((applyKids v (combo.map (·.1)) ks).map AR.toRT) := by
    rw [toRT_processRun_whole, hchain]
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hMfree : ∀ m ∈ M, v ∉ m.bag := by
    intro m hm
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    rw [hb]; exact (hbase n0 hn0).2.1
  -- dominance of the pieces
  have hM : Dom (typical (csz M)) ((typical (csz ns)).drop (preLo pre)) := by
    rw [hcM]
    cases pre with
    | none =>
      simp only [preAB, endAB, preLo, List.drop_zero, Nat.sub_zero, List.take_length]
      exact Dom.refl _
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have := dom_right hs hc1'
      have e : (csz ns).length - cB (csz ns) c1 = ((csz ns).drop (cB (csz ns) c1)).length := by simp
      simp only [preAB, endAB, preLo]
      rw [e, List.take_length]
      exact this
  have hMq : Dom (typical (csz (M.map (av v)))) (plus1 ((typical (csz ns)).drop (preLo pre))) := by
    rw [csz_map_av hMfree, typical_plus1]
    unfold plus1
    exact dom_map_succ hM
  have hwin : DomC (CT.node (insert v S) (typical (csz (M.map (av v)))) Qs)
      (CT.node (insert v S) (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1))) :=
    ⟨rfl, hMq, hA3'⟩
  -- kept kids
  have hkeepr : ∀ r ∈ combo.map (·.2.1), keep (insert v S) (norm r) = true := by
    intro r hr
    obtain ⟨k, hk, hkr⟩ := forall2_exists_right hA6 r hr
    have hkk := kid_keep (hkids k hk) (hkp k hk)
    have hnn : ¬ Nested S (AR.charF Finset.card k) := by
      intro hN
      have := (keep_norm_false_iff S _).2 hN
      rw [this] at hkk; exact absurd hkk (by simp)
    by_contra hcon
    have hf : keep (insert v S) (norm r) = false := by simpa using hcon
    exact hkr S hnn ((keep_norm_false_iff _ _).1 hf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; simpa using hTI
  · intro p
    rw [hxt, htc p]
    cases pre with
    | none => simp [hL0 rfl]
    | some c1 => simp [hL1 (by simp)]
  · rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    exact (RT.mem_verts_iff _ v).2 ⟨insert v m.bag, by simpa using hmb m hm, Finset.mem_insert_self _ _⟩
  · intro u hu
    rw [hxt]
    have hfold : ∀ (S0 : Finset ℕ) (l : List (Option WPlan × CT × Finset ℕ)),
        l.foldl (fun a c => a ∪ c.2.2) S0 = S0 ∪ l.foldl (fun a c => a ∪ c.2.2) ∅ := by
      intro S0 l
      induction l generalizing S0 with
      | nil => simp
      | cons c l ih' =>
        simp only [List.foldl_cons]
        rw [ih' (S0 ∪ c.2.2), ih' (∅ ∪ c.2.2)]
        simp [Finset.union_assoc]
    rw [hfold, Finset.mem_union] at hu
    rcases hu with hu | hu
    · obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
      obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
      refine ⟨insert v m.bag, by simpa using hmb m hm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
      have : u ∈ n0.bag ∩ B := by rw [(hbase n0 hn0).1]; exact hu
      rw [hb]; exact (Finset.mem_inter.1 this).1
    · obtain ⟨k', hk', Y, hY, hvY, huY⟩ := hA5 u hu
      refine ⟨Y, ?_, hvY, huY⟩
      have hne'' : (L ++ M.map (av v) ++ []) ≠ [] := by
        obtain ⟨m0, M', rfl⟩ := List.exists_cons_of_ne_nil hMne
        simp
      rw [mem_bags_chainToRT _ _ hne'']
      exact Or.inr (Or.inr ⟨AR.toRT k', List.mem_map.2 ⟨k', hk', rfl⟩, hY⟩)
  · -- chr
    refine ⟨regionQ v S L M [] Qs, by rw [hxt]; exact hnorm, ?_⟩
    cases pre with
    | none =>
      simp only [regionQ, hL0 rfl, topRep]
      simpa using hwin
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have hL : Dom (typical (csz L)) ((typical (csz ns)).take (cHi c1 + 1)) := by
        rw [hcL]; simpa [preAB] using dom_left hs hc1'
      have hLne : L ≠ [] := hL1 (by simp)
      simp only [regionQ, if_neg hLne, topRep]
      simp only [if_true]
      exact ⟨rfl, hL, ⟨hwin, trivial⟩⟩
  · -- wid
    intro Y hY hvY
    rw [hxt] at hY
    have hkeep : (∃ k ∈ combo.map (·.2.1), keep (insert v S) (norm k) = true) ∨
        (plus1 ((typical (csz ns)).drop (preLo pre))).length ≤ 1 := by
      by_cases hka : ks = []
      · right
        have h1 : ns.length = 1 := hleaf hka
        have hy1 : (typical (csz ns)).length ≤ 1 := by
          obtain ⟨x0, hx0⟩ : ∃ x0, csz ns = [x0] := by
            have : (csz ns).length = 1 := by rw [csz_length]; exact h1
            exact List.length_eq_one_iff.1 this
          rw [hx0, typical_singleton]; simp
        simp only [plus1, List.length_map, List.length_drop]
        omega
      · left
        have hlen := hkc.length_eq
        have hne : combo.map (·.2.1) ≠ [] := by
          intro h
          have : combo = [] := by simpa using h
          rw [this] at hlen
          exact hka (List.length_eq_zero_iff.1 hlen)
        obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
        exact ⟨r, hr, hkeepr r hr⟩
    have hwidwin : Y.card ≤ maxEntry (norm (CT.node (insert v S)
        (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1)))) := by
      rcases hvb Y hY hvY with ⟨m, hm, rfl⟩ | ⟨k', hk', hYk⟩
      · have h1 : (insert v m.bag).card ∈ csz (M.map (av v)) := mem_csz (List.mem_map_of_mem hm)
        have h2 := le_maxOf h1
        rw [← maxOf_typical] at h2
        refine h2.trans ((dom_maxOf_le hMq).trans (maxOf_le fun e he => norm_y_le hkeep he))
      · obtain ⟨k'', hk'', rfl⟩ := List.mem_map.1 hk'
        obtain ⟨r, hr, hle⟩ := hA4 Y k'' hk'' hYk hvY
        exact hle.trans (norm_kid_le hr (hkeepr r hr))
    cases pre with
    | none => exact hwidwin
    | some c1 =>
      refine hwidwin.trans (norm_kid_le (K := [_]) (List.mem_singleton_self _) ?_)
      exact keep_of_mem_verts (by simp [CT.verts_node]) (fun h => hvB (hSB h))
  · -- vrep
    cases pre with
    | none => simp [topRep, CT.verts_node]
    | some c1 =>
      simp only [topRep]
      exact CT.mem_verts.2 (Or.inr ⟨_, List.mem_singleton_self _,
        CT.mem_verts.2 (Or.inl (Finset.mem_insert_self _ _))⟩)
  · -- nest
    intro hpre σ hσ hN
    have hpre' : pre = none := by cases pre <;> simp_all
    subst hpre'
    simp only [topRep] at hN
    obtain ⟨h1, h2⟩ := hN
    apply hσ
    rw [AR.charF_run]
    refine ⟨?_, nestedL_of_forall2 hA6 h2⟩
    intro z hz
    have := h1 (Finset.mem_insert_of_mem hz)
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hSB hz) hvB
    · exact h3

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.RealizeWinClaim` -/

section
/-!
# `winPlans` is realised by `processRun` (work package C5, part 10)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem forall2_imp_mem {α β : Type} {R R' : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (hi : ∀ a ∈ l, ∀ b, R a b → R' a b) : List.Forall₂ R' l l' := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l l' hab _ ih =>
    exact List.Forall₂.cons (hi a List.mem_cons_self b hab) (ih (fun a' ha' b' h' => hi a' (List.mem_cons_of_mem _ ha') b' h'))

theorem win_claim (v : ℕ) (B : Finset ℕ) (hvB : v ∉ B) : ∀ x : AR, RunOk v B x →
    ∀ (pre : Option Cut) (w : WPlan) (rep : CT) (cov : Finset ℕ),
      PreOk (typical (csz x.chain)).length pre →
      (w, rep, cov) ∈ winPlans v (preLo pre) (AR.charF Finset.card x) →
      PRC v B x (processRun v pre w x) (topRep x.S (typical (csz x.chain)) pre rep) cov pre.isSome := by
  intro x
  induction x using AR.ind with
  | _ S ns ks ih =>
    intro hx pre w rep cov hpre hmem
    have hc : AR.charF Finset.card (.run S ns ks) =
        CT.node S (typical (csz ns)) (ks.map (AR.charF Finset.card)) := AR.charF_run _ _ _ _
    rw [hc] at hmem
    simp only [AR.S, AR.chain] at *
    simp only [winPlans, List.mem_append, List.mem_map] at hmem
    rcases hmem with (⟨f, hf, h⟩ | ⟨f, hf, h⟩) | ⟨combo, hcombo, h⟩
    · -- end, first type
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.mem_range'_1] at hf
      have hv : (Cut.t1 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; omega
      have hlh : LoHi pre (.endAt (Cut.t1 f)) := by
        cases pre with
        | none => trivial
        | some c1 => show cLo c1 ≤ f; have : preLo (some c1) = cLo c1 := rfl; omega
      exact pr_end v B S ns ks hvB hx pre (Cut.t1 f) hpre hv hlh
    · -- end, second type
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.mem_range'_1] at hf
      have hv : (Cut.t2 f).Valid (typical (csz ns)).length := by simp only [CT.Cut.Valid]; omega
      have hlh : LoHi pre (.endAt (Cut.t2 f)) := by
        cases pre with
        | none => trivial
        | some c1 => show cLo c1 ≤ f; have : preLo (some c1) = cLo c1 := rfl; omega
      exact pr_end v B S ns ks hvB hx pre (Cut.t2 f) hpre hv hlh
    · -- whole
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hkids := (runOk_run hx).2.2.1
      have h2 := (kidChoices_forall2 v _ _).1 hcombo
      rw [List.forall₂_map_left_iff] at h2
      have hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo := by
        refine forall2_imp_mem h2 ?_
        intro k hk o ho
        rcases ho with ⟨h1, h2, h3⟩ | ⟨wp, h1, h2⟩
        · rw [h1, applyOpt, h2, h3]
          exact kc_unchanged hvB (hkids k hk)
        · rw [h1, applyOpt]
          have := ih k hk (hkids k hk) none wp o.2.1 o.2.2 (by simp [PreOk]) (by simpa [preLo] using h2)
          simpa [topRep] using this.kc
      exact pr_whole v B S ns ks hvB hx pre combo hpre hkc

end Lax117284Proofs.Treewidth.Chars

end
