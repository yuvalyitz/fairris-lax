import Lax117284Proofs.Treewidth.Chars.IntroWitness
import Lax117284Proofs.Treewidth.Seq.Concat
import Lax117284Proofs.Treewidth.Seq.Structure
import Lax117284Proofs.Treewidth.Seq.Symmetry

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
