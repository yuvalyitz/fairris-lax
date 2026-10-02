import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Seq.RingTyp
import Lax117284Proofs.Treewidth.Seq.Concat

/-!
# The lattice dynamic programme `latticeStates` (C3, part 2)

`latticeStates a b` is the state list of the final cell of the DP of `Chars/Defs.lean`: one state per typical ring
sum, with one witnessing lattice path (reversed).  We prove

* `latticeStates_sound / _complete / _nodup`;
* `mem_ringTypList` (the DP computes `ringTyp`);
* `findPath_spec`, `findPath_complete`.

The proof is by a semantic invariant `Cell a b i j C` on the state lists of the cell `(i,j)`; `cell_step` (one
cell), `rowCells_ok` (one row) and `latticeRows_ok` (the rows) establish it.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq CT

/-- A monotone lattice path from `(0,0)` to `(|a|-1,|b|-1)` (steps `(1,0)`, `(0,1)`, `(1,1)`). -/
def IsLatticePath (a b : List ℕ) (P : List (ℕ × ℕ)) : Prop :=
  P.head? = some (0, 0) ∧ P.getLast? = some (a.length - 1, b.length - 1) ∧
    P.IsChain (fun p q => (q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2 + 1) ∨
      (q.1 = p.1 + 1 ∧ q.2 = p.2 + 1))

/-- The sums along a path. -/
def pathSum (a b : List ℕ) (P : List (ℕ × ℕ)) : List ℕ := P.map (fun p => a.getD p.1 0 + b.getD p.2 0)

/-- One lattice step. -/
def LStep (p q : ℕ × ℕ) : Prop :=
  (q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2 + 1) ∨ (q.1 = p.1 + 1 ∧ q.2 = p.2 + 1)

/-- A lattice path from `(0,0)` to `(i,j)`. -/
def PathTo (i j : ℕ) (P : List (ℕ × ℕ)) : Prop :=
  P.head? = some (0, 0) ∧ P.getLast? = some (i, j) ∧ P.IsChain LStep

theorem PathTo.snoc {i j : ℕ} {P : List (ℕ × ℕ)} (h : PathTo i j P) {q : ℕ × ℕ} (hq : LStep (i, j) q) :
    PathTo q.1 q.2 (P ++ [q]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, by simp, ?_⟩
  · rcases P with _ | ⟨p, P⟩
    · simp at h1
    · simpa using h1
  · rw [List.isChain_append]
    refine ⟨h3, List.isChain_singleton _, ?_⟩
    intro x hx y hy
    rw [h2] at hx
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
    subst hx; subst hy
    exact hq

theorem pathTo_zero : PathTo 0 0 [(0, 0)] := ⟨rfl, rfl, List.isChain_singleton _⟩

theorem PathTo.split {i j : ℕ} {P : List (ℕ × ℕ)} (h : PathTo i j P) :
    (i = 0 ∧ j = 0 ∧ P = [(0, 0)]) ∨
    ∃ P' p, P = P' ++ [(i, j)] ∧ PathTo p.1 p.2 P' ∧ LStep p (i, j) := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases List.eq_nil_or_concat P with rfl | ⟨P', x, rfl⟩
  · simp at h1
  · simp only [List.concat_eq_append] at h1 h2 h3 ⊢
    have hx : x = (i, j) := by simpa using h2
    subst hx
    rcases P' with _ | ⟨p, P''⟩
    · simp at h1
      obtain ⟨rfl, rfl⟩ := h1
      left; exact ⟨rfl, rfl, rfl⟩
    · right
      have hc := (List.isChain_append.1 h3)
      have hl : (p :: P'').getLast? = some ((p :: P'').getLast (by simp)) :=
        List.getLast?_eq_some_getLast (by simp)
      refine ⟨p :: P'', (p :: P'').getLast (by simp), rfl, ⟨by simpa using h1, ?_, hc.1⟩, ?_⟩
      · rw [hl]
      · exact hc.2.2 _ (by rw [hl]; rfl) _ (by simp)

/-! ## the cell invariant -/

/-- Semantic description of the state list `C` of the cell `(i,j)`. -/
def Cell (a b : List ℕ) (i j : ℕ) (C : List LState) : Prop :=
  (∀ s ∈ C, PathTo i j s.2.reverse ∧ s.1 = typical (pathSum a b s.2.reverse)) ∧
  (∀ P, PathTo i j P → ∃ s ∈ C, s.1 = typical (pathSum a b P)) ∧
  (C.map Prod.fst).Nodup

def UpOk (a b : List ℕ) (i j : ℕ) (up : List LState) : Prop :=
  (i = 0 → up = []) ∧ ∀ i', i = i' + 1 → Cell a b i' j up

def LeftOk (a b : List ℕ) (i j : ℕ) (left : List LState) : Prop :=
  (j = 0 → left = []) ∧ ∀ j', j = j' + 1 → Cell a b i j' left

def DiagOk (a b : List ℕ) (i j : ℕ) (diag : List LState) : Prop :=
  (i = 0 ∧ j = 0 → diag = [([], [])]) ∧ ((i = 0 ∨ j = 0) → ¬ (i = 0 ∧ j = 0) → diag = []) ∧
    ∀ i' j', i = i' + 1 → j = j' + 1 → Cell a b i' j' diag

/-! ## `dedupKey` -/

theorem dedup_fold (l : List LState) :
    ∀ acc : List LState, (acc.map Prod.fst).Nodup →
      ((l.foldl (fun acc s => if acc.any (fun t => decide (t.1 = s.1)) then acc else acc ++ [s]) acc).map
          Prod.fst).Nodup ∧
      (∀ s ∈ l.foldl (fun acc s => if acc.any (fun t => decide (t.1 = s.1)) then acc else acc ++ [s]) acc,
          s ∈ acc ∨ s ∈ l) ∧
      (∀ s ∈ acc ++ l, ∃ s' ∈ l.foldl
          (fun acc s => if acc.any (fun t => decide (t.1 = s.1)) then acc else acc ++ [s]) acc, s'.1 = s.1) := by
  induction l with
  | nil =>
    intro acc h
    refine ⟨h, fun s hs => Or.inl hs, fun s hs => ⟨s, ?_, rfl⟩⟩
    simpa using hs
  | cons s l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    by_cases hany : acc.any (fun t => decide (t.1 = s.1)) = true
    · rw [if_pos hany]
      obtain ⟨h1, h2, h3⟩ := ih acc hacc
      refine ⟨h1, fun x hx => ?_, fun x hx => ?_⟩
      · rcases h2 x hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_append.1 hx with hx | hx
        · exact h3 x (List.mem_append_left _ hx)
        · rcases List.mem_cons.1 hx with rfl | hx
          · obtain ⟨t, ht, ht'⟩ := List.any_eq_true.1 hany
            obtain ⟨s', hs', e⟩ := h3 t (List.mem_append_left _ ht)
            exact ⟨s', hs', by rw [e]; simpa using ht'⟩
          · exact h3 x (List.mem_append_right _ hx)
    · rw [if_neg hany]
      have hnd : ((acc ++ [s]).map Prod.fst).Nodup := by
        rw [List.map_append, List.nodup_append]
        refine ⟨hacc, by rw [List.map_singleton]; exact List.nodup_singleton _, ?_⟩
        intro x hx y hy
        simp only [List.map_singleton, List.mem_singleton] at hy
        subst hy
        intro hxy
        apply hany
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        exact List.any_eq_true.2 ⟨t, ht, by simpa using hxy⟩
      obtain ⟨h1, h2, h3⟩ := ih (acc ++ [s]) hnd
      refine ⟨h1, fun x hx => ?_, fun x hx => ?_⟩
      · rcases h2 x hx with h | h
        · rcases List.mem_append.1 h with h | h
          · exact Or.inl h
          · exact Or.inr (by simp at h; simp [h])
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_append.1 hx with hx | hx
        · exact h3 x (List.mem_append_left _ (List.mem_append_left _ hx))
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact h3 x (List.mem_append_left _ (List.mem_append_right _ (by simp)))
          · exact h3 x (List.mem_append_right _ hx)

theorem dedupKey_nodup (l : List LState) : ((dedupKey l).map Prod.fst).Nodup :=
  (dedup_fold l [] (by simp)).1

theorem dedupKey_sub {l : List LState} {s : LState} (h : s ∈ dedupKey l) : s ∈ l := by
  rcases (dedup_fold l [] (by simp)).2.1 s h with h | h
  · simp at h
  · exact h

theorem dedupKey_cover {l : List LState} {s : LState} (h : s ∈ l) : ∃ s' ∈ dedupKey l, s'.1 = s.1 :=
  (dedup_fold l [] (by simp)).2.2 s (by simpa using h)

/-! ## `typical` along paths -/

theorem typical_snoc (l : List ℕ) (z : ℕ) : typical (l ++ [z]) = push (typical l) z := by
  simp [typical, List.foldl_append]

theorem pathSum_snoc (a b : List ℕ) (P : List (ℕ × ℕ)) (i j : ℕ) :
    pathSum a b (P ++ [(i, j)]) = pathSum a b P ++ [a.getD i 0 + b.getD j 0] := by
  simp [pathSum]

theorem typical_pathSum_snoc (a b : List ℕ) (P : List (ℕ × ℕ)) (i j : ℕ) :
    typical (pathSum a b (P ++ [(i, j)])) = push (typical (pathSum a b P)) (a.getD i 0 + b.getD j 0) := by
  rw [pathSum_snoc, typical_snoc]

/-! ## one cell -/

theorem mem_cellOf {i j z : ℕ} {up left diag : List LState} {s : LState}
    (h : s ∈ cellOf i j z up left diag) :
    ∃ t ∈ up ++ left ++ diag, s = (push t.1 z, (i, j) :: t.2) := by
  unfold cellOf at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (dedupKey_sub h)
  exact ⟨t, ht, rfl⟩

theorem cell_step {a b : List ℕ} {i j : ℕ} {up left diag : List LState}
    (hup : UpOk a b i j up) (hleft : LeftOk a b i j left) (hdiag : DiagOk a b i j diag) :
    Cell a b i j (cellOf i j (a.getD i 0 + b.getD j 0) up left diag) := by
  set z := a.getD i 0 + b.getD j 0 with hz
  refine ⟨?_, ?_, dedupKey_nodup _⟩
  · -- soundness
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_cellOf hs
    have hrev : ((push t.1 z, (i, j) :: t.2) : LState).2.reverse = t.2.reverse ++ [(i, j)] := by simp
    have hty : ∀ P : List (ℕ × ℕ), t.1 = typical (pathSum a b P) → P = t.2.reverse →
        (push t.1 z, (i, j) :: t.2).1 = typical (pathSum a b (t.2.reverse ++ [(i, j)])) := by
      intro P hP hPe
      subst hPe
      simp only
      rw [typical_pathSum_snoc, ← hP]
    rcases List.mem_append.1 ht with ht | ht
    · rcases List.mem_append.1 ht with ht | ht
      · -- up
        have hi : i ≠ 0 := by
          intro h0; rw [hup.1 h0] at ht; simp at ht
        obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
        obtain ⟨hp, hs⟩ := (hup.2 i' rfl).1 t ht
        rw [hrev]
        exact ⟨hp.snoc (Or.inl ⟨rfl, rfl⟩), hty _ hs rfl⟩
      · -- left
        have hj : j ≠ 0 := by
          intro h0; rw [hleft.1 h0] at ht; simp at ht
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
        obtain ⟨hp, hs⟩ := (hleft.2 j' rfl).1 t ht
        rw [hrev]
        exact ⟨hp.snoc (Or.inr (Or.inl ⟨rfl, rfl⟩)), hty _ hs rfl⟩
    · -- diag
      by_cases h00 : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h00
        rw [hdiag.1 ⟨rfl, rfl⟩] at ht
        simp only [List.mem_singleton] at ht
        subst ht
        rw [hrev]
        refine ⟨by simpa using pathTo_zero, ?_⟩
        simp [typical, pathSum, push_nil, hz]
      · have hne : ¬ (i = 0 ∨ j = 0) := by
          intro h0; rw [hdiag.2.1 h0 h00] at ht; simp at ht
        push Not at hne
        obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne.1
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne.2
        obtain ⟨hp, hs⟩ := (hdiag.2.2 i' j' rfl rfl).1 t ht
        rw [hrev]
        exact ⟨hp.snoc (Or.inr (Or.inr ⟨rfl, rfl⟩)), hty _ hs rfl⟩
  · -- completeness
    intro P hP
    have hcover : ∀ (P' : List (ℕ × ℕ)) (t : LState), t ∈ up ++ left ++ diag →
        t.1 = typical (pathSum a b P') →
        ∃ s ∈ cellOf i j z up left diag, s.1 = typical (pathSum a b (P' ++ [(i, j)])) := by
      intro P' t ht htt
      have hmem : ((push t.1 z, (i, j) :: t.2) : LState) ∈
          (up ++ left ++ diag).map (fun s => (push s.1 z, (i, j) :: s.2)) := List.mem_map.2 ⟨t, ht, rfl⟩
      obtain ⟨s', hs', e⟩ := dedupKey_cover hmem
      refine ⟨s', hs', ?_⟩
      rw [e]
      simp only
      rw [typical_pathSum_snoc, ← htt]
    rcases hP.split with ⟨rfl, rfl, rfl⟩ | ⟨P', p, rfl, hp, hstep⟩
    · have hd := hdiag.1 ⟨rfl, rfl⟩
      have hmem : (([], []) : LState) ∈ up ++ left ++ diag := by rw [hd]; simp
      obtain ⟨s, hs, e⟩ := hcover [] _ hmem (by simp [typical, pathSum])
      exact ⟨s, hs, by simpa using e⟩
    · obtain ⟨p1, p2⟩ := p
      simp only at hp
      rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only at h1 h2
        subst h1; subst h2
        obtain ⟨s, hs, e⟩ := (hup.2 p1 rfl).2.1 P' hp
        exact hcover P' s (List.mem_append_left _ (List.mem_append_left _ hs)) e
      · simp only at h1 h2
        subst h1; subst h2
        obtain ⟨s, hs, e⟩ := (hleft.2 p2 rfl).2.1 P' hp
        exact hcover P' s (List.mem_append_left _ (List.mem_append_right _ hs)) e
      · simp only at h1 h2
        subst h1; subst h2
        obtain ⟨s, hs, e⟩ := (hdiag.2.2 p1 p2 rfl rfl).2.1 P' hp
        exact hcover P' s (List.mem_append_right _ hs) e

/-! ## rows -/

theorem tail_getD (ups : List (List LState)) (m : ℕ) : ups.tail.getD m [] = ups.getD (m + 1) [] := by
  cases ups <;> simp

theorem headD_eq (ups : List (List LState)) : ups.headD [] = ups.getD 0 [] := by
  cases ups <;> simp

theorem rowCells_ok (a b : List ℕ) (i : ℕ) : ∀ (bl : List ℕ) (j : ℕ) (ups : List (List LState))
    (diag left : List LState), bl = b.drop j →
    (∀ m, m < bl.length → UpOk a b i (j + m) (ups.getD m [])) → DiagOk a b i j diag → LeftOk a b i j left →
    (rowCells i (a.getD i 0) bl j ups diag left).length = bl.length ∧
    ∀ m, m < bl.length → Cell a b i (j + m) ((rowCells i (a.getD i 0) bl j ups diag left).getD m []) := by
  intro bl
  induction bl with
  | nil => intro j ups diag left _ _ _ _; simp [rowCells]
  | cons y rest ih =>
    intro j ups diag left hbl hup hdiag hleft
    have hj : b.getD j 0 = y := by
      have : (b.drop j)[0]? = some y := by rw [← hbl]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at this
      simp [List.getD_eq_getElem?_getD, this]
    have hrest : rest = b.drop (j + 1) := by
      have h1 : (b.drop j).drop 1 = rest := by rw [← hbl]; rfl
      rw [List.drop_drop] at h1
      rw [← h1, Nat.add_comm]
    have hc : Cell a b i j (cellOf i j (a.getD i 0 + y) (ups.headD []) left diag) := by
      have := cell_step (a := a) (b := b) (i := i) (j := j) (up := ups.headD []) (left := left) (diag := diag)
        (by rw [headD_eq]; simpa using hup 0 (by simp)) hleft hdiag
      rwa [hj] at this
    have hrec := ih (j + 1) ups.tail (ups.headD []) (cellOf i j (a.getD i 0 + y) (ups.headD []) left diag) hrest
      (by
        intro m hm
        rw [tail_getD]
        have := hup (m + 1) (by simpa using hm)
        rwa [show j + (m + 1) = j + 1 + m by omega] at this)
      (by
        have h0 : UpOk a b i j (ups.getD 0 []) := by simpa using hup 0 (by simp)
        rw [headD_eq]
        refine ⟨by rintro ⟨_, h⟩; omega, fun h1 h2 => ?_, fun i' j' hi hj' => ?_⟩
        · rcases h1 with h1 | h1
          · exact h0.1 h1
          · omega
        · have := h0.2 i' hi
          have hjj : j = j' := by omega
          subst hjj; exact this)
      (by
        refine ⟨fun h => by omega, fun j' hj' => ?_⟩
        have : j' = j := by omega
        subst this; exact hc)
    simp only [rowCells]
    refine ⟨by rw [List.length_cons, List.length_cons, hrec.1], fun m hm => ?_⟩
    cases m with
    | zero => simpa using hc
    | succ m =>
      have := hrec.2 m (by simpa using hm)
      rw [show j + (m + 1) = j + 1 + m by omega]
      simpa using this

theorem latticeRows_ok (a b : List ℕ) : ∀ (al : List ℕ) (i : ℕ) (prev : List (List LState)),
    al = a.drop i → al ≠ [] → (∀ m, m < b.length → UpOk a b i m (prev.getD m [])) →
    (latticeRows b i al prev).length = b.length ∧
    ∀ m, m < b.length → Cell a b (a.length - 1) m ((latticeRows b i al prev).getD m []) := by
  intro al
  induction al with
  | nil => intro i prev _ h; exact absurd rfl h
  | cons x al' ih =>
    intro i prev hal _ hup
    have hi : i < a.length := by
      by_contra hcon
      rw [List.drop_of_length_le (by omega)] at hal
      exact absurd hal (by simp)
    have hx : a.getD i 0 = x := by
      have : (a.drop i)[0]? = some x := by rw [← hal]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at this
      simp [List.getD_eq_getElem?_getD, this]
    have hal' : al' = a.drop (i + 1) := by
      have h1 : (a.drop i).drop 1 = al' := by rw [← hal]; rfl
      rw [List.drop_drop] at h1
      rw [← h1, Nat.add_comm]
    have hrow := rowCells_ok a b i b 0 prev (if i = 0 then [([], [])] else []) [] (by simp)
      (by simpa using hup)
      ⟨fun h => by simp [h.1], fun h1 h2 => by
          rcases h1 with h1 | h1
          · exact absurd ⟨h1, rfl⟩ h2
          · have hne : i ≠ 0 := fun h => h2 ⟨h, rfl⟩
            simp [hne], fun i' j' _ h => by omega⟩
      ⟨fun _ => rfl, fun j' h => by omega⟩
    rw [hx] at hrow
    simp only [latticeRows]
    by_cases hnil : al' = []
    · subst hnil
      have : a.length = i + 1 := by
        have h1 : a.drop (i + 1) = [] := hal'.symm
        rw [List.drop_eq_nil_iff] at h1
        omega
      simp only [latticeRows]
      refine ⟨hrow.1, fun m hm => ?_⟩
      have e : a.length - 1 = i := by omega
      rw [e]
      simpa using hrow.2 m hm
    · exact ih (i + 1) _ hal' hnil (by
        intro m hm
        refine ⟨fun h => by omega, fun i' hi' => ?_⟩
        have : i' = i := by omega
        subst this
        simpa using hrow.2 m hm)

/-! ## the final cell -/

theorem latticeStates_cell {a b : List ℕ} (ha : a ≠ []) (hb : b ≠ []) :
    Cell a b (a.length - 1) (b.length - 1) (latticeStates a b) := by
  obtain ⟨x, a', rfl⟩ := List.exists_cons_of_ne_nil ha
  obtain ⟨y, b', rfl⟩ := List.exists_cons_of_ne_nil hb
  have hrows := latticeRows_ok (x :: a') (y :: b') (x :: a') 0 [] (by simp) (by simp)
    (by intro m hm; exact ⟨fun _ => by simp, fun i' h => by omega⟩)
  have : latticeStates (x :: a') (y :: b') =
      (latticeRows (y :: b') 0 (x :: a') []).getD ((y :: b').length - 1) [] := by
    show (latticeRows (y :: b') 0 (x :: a') []).getLast?.getD [] = _
    rw [List.getLast?_eq_getElem?, hrows.1, List.getD_eq_getElem?_getD]
  rw [this]
  exact hrows.2 _ (by simp)

@[simp] theorem latticeStates_nil_left (b : List ℕ) : latticeStates [] b = [] := by
  simp [latticeStates]

@[simp] theorem latticeStates_nil_right (a : List ℕ) : latticeStates a [] = [] := by
  cases a <;> simp [latticeStates]

/-- **NEW** soundness of `latticeStates`: every state is `τ` of the sums along its recorded path (reversed). -/
theorem latticeStates_sound {a b : List ℕ} {s : LState} (h : s ∈ latticeStates a b) :
    IsLatticePath a b s.2.reverse ∧ s.1 = typical (pathSum a b s.2.reverse) := by
  have ha : a ≠ [] := by rintro rfl; simp at h
  have hb : b ≠ [] := by rintro rfl; simp at h
  exact (latticeStates_cell ha hb).1 s h

/-- **NEW** completeness of `latticeStates`: the `τ` of the sums along every lattice path is a state. -/
theorem latticeStates_complete {a b : List ℕ} {P : List (ℕ × ℕ)} (hP : IsLatticePath a b P) (ha : a ≠ [])
    (hb : b ≠ []) : ∃ s ∈ latticeStates a b, s.1 = typical (pathSum a b P) :=
  (latticeStates_cell ha hb).2.1 P hP

/-! ## `findPath` -/

/-- **NEW** `findPath` returns a lattice path whose `τ`-sum (minus `|S|`) is dominated by `want`. -/
theorem findPath_spec {sa sb : List ℕ} {c : ℕ} {want : List ℕ} {Q : List (ℕ × ℕ)}
    (h : findPath sa sb c want = some Q) :
    IsLatticePath sa sb Q ∧ Dom ((typical (pathSum sa sb Q)).map (· - c)) want := by
  unfold findPath at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hs
  have hpred := List.find?_some hs
  obtain ⟨hpath, hty⟩ := latticeStates_sound hmem
  refine ⟨hpath, ?_⟩
  rw [← hty]
  exact dom_iff_domB.2 hpred

/-- **NEW** `findPath` succeeds when some lattice path has a dominated `τ`-sum. -/
theorem findPath_complete {sa sb : List ℕ} {c : ℕ} {want : List ℕ} {Q : List (ℕ × ℕ)}
    (hQ : IsLatticePath sa sb Q) (hd : Dom ((typical (pathSum sa sb Q)).map (· - c)) want) (ha : sa ≠ [])
    (hb : sb ≠ []) : ∃ Q', findPath sa sb c want = some Q' := by
  obtain ⟨s, hs, e⟩ := latticeStates_complete hQ ha hb
  have hp : (fun s : LState => domB (s.1.map (· - c)) want) s = true := by
    show domB (s.1.map (· - c)) want = true
    rw [e]; exact dom_iff_domB.1 hd
  have hsome : ((latticeStates sa sb).find? (fun s => domB (s.1.map (· - c)) want)).isSome = true :=
    List.find?_isSome.2 ⟨s, hs, hp⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hsome
  exact ⟨t.2.reverse, by unfold findPath; rw [ht]; rfl⟩

/-! ## lattice paths versus `pathSums` -/

theorem chain_le_last : ∀ (P : List (ℕ × ℕ)) (p : ℕ × ℕ), (p :: P).IsChain LStep →
    ∀ x ∈ (p :: P).getLast?, p.1 ≤ x.1 ∧ p.2 ≤ x.2 := by
  intro P
  induction P with
  | nil => intro p _ x hx; simp at hx; subst hx; exact ⟨le_rfl, le_rfl⟩
  | cons q P ih =>
    intro p hc x hx
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at hx
    obtain ⟨h1, h2⟩ := ih q hc.2 x hx
    rcases hc.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega

theorem mem_pathSums_of_path (a b : List ℕ) : ∀ (P : List (ℕ × ℕ)) (i j : ℕ),
    P.head? = some (i, j) → P.getLast? = some (a.length - 1, b.length - 1) → P.IsChain LStep →
    i < a.length → j < b.length → pathSum a b P ∈ pathSums (a.drop i) (b.drop j) := by
  intro P
  induction P with
  | nil => intro i j h; simp at h
  | cons p P ih =>
    intro i j h1 h2 h3 hi hj
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have hgx : a.getD i 0 = a[i] := by simp [List.getD_eq_getElem?_getD, hi]
    have hgy : b.getD j 0 = b[j] := by simp [List.getD_eq_getElem?_getD, hj]
    have hgx' : a[i]?.getD 0 = a[i] := by simp [hi]
    have hgy' : b[j]?.getD 0 = b[j] := by simp [hj]
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, mem_pathSums_cons_cons]
    cases P with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at h2
      left
      refine ⟨List.drop_of_length_le (by omega), List.drop_of_length_le (by omega), ?_⟩
      simp [pathSum, hgx', hgy']
    | cons q P' =>
      rw [List.isChain_cons_cons] at h3
      rw [List.getLast?_cons_cons] at h2
      have hlast := chain_le_last P' q h3.2 _ (by rw [h2]; rfl)
      simp only at hlast
      have hq1 : q.1 < a.length := by omega
      have hq2 : q.2 < b.length := by omega
      have hIH := ih q.1 q.2 (by simp) h2 h3.2 hq1 hq2
      right
      have hps : pathSum a b ((i, j) :: q :: P') = (a[i] + b[j]) :: pathSum a b (q :: P') := by
        simp [pathSum, hgx', hgy']
      refine ⟨pathSum a b (q :: P'), ?_, hps⟩
      rcases h3.1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · simp only at e1 e2
        rw [e1, e2] at hIH
        rw [List.drop_eq_getElem_cons hj] at hIH
        exact Or.inl hIH
      · simp only at e1 e2
        rw [e1, e2] at hIH
        rw [List.drop_eq_getElem_cons hi] at hIH
        exact Or.inr (Or.inl hIH)
      · simp only at e1 e2
        rw [e1, e2] at hIH
        exact Or.inr (Or.inr hIH)

theorem path_of_mem_pathSums (a b : List ℕ) : ∀ (n i j : ℕ) (c : List ℕ),
    (a.length - i) + (b.length - j) = n → i < a.length → j < b.length →
    c ∈ pathSums (a.drop i) (b.drop j) →
    ∃ P : List (ℕ × ℕ), P.head? = some (i, j) ∧ P.getLast? = some (a.length - 1, b.length - 1) ∧
      P.IsChain LStep ∧ c = pathSum a b P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j c hn hi hj hc
    have hgx : a.getD i 0 = a[i] := by simp [List.getD_eq_getElem?_getD, hi]
    have hgy : b.getD j 0 = b[j] := by simp [List.getD_eq_getElem?_getD, hj]
    have hgx' : a[i]?.getD 0 = a[i] := by simp [hi]
    have hgy' : b[j]?.getD 0 = b[j] := by simp [hj]
    rw [List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj, mem_pathSums_cons_cons] at hc
    rcases hc with ⟨h1, h2, rfl⟩ | ⟨p, hp, rfl⟩
    · have h1' := List.drop_eq_nil_iff.1 h1
      have h2' := List.drop_eq_nil_iff.1 h2
      refine ⟨[(i, j)], rfl, ?_, List.isChain_singleton _, ?_⟩
      · simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq]; omega
      · simp [pathSum, hgx', hgy']
    · have hnext : ∀ i' j', i < a.length → j < b.length → (i' = i + 1 ∨ i' = i) → (j' = j + 1 ∨ j' = j) →
          (i' ≠ i ∨ j' ≠ j) → p ∈ pathSums (a.drop i') (b.drop j') →
          ∃ P : List (ℕ × ℕ), P.head? = some (i, j) ∧ P.getLast? = some (a.length - 1, b.length - 1) ∧
            P.IsChain LStep ∧ (a[i] + b[j]) :: p = pathSum a b P := by
        intro i' j' _ _ hi' hj' hne hpm
        have hi2 : i' < a.length := by
          by_contra hcon
          rw [List.drop_of_length_le (l := a) (i := i') (by omega)] at hpm
          simp at hpm
        have hj2 : j' < b.length := by
          by_contra hcon
          rw [List.drop_of_length_le (l := b) (i := j') (by omega)] at hpm
          simp at hpm
        obtain ⟨P', hh, hl, hch, rfl⟩ := ih ((a.length - i') + (b.length - j')) (by omega) i' j' p rfl hi2 hj2 hpm
        cases P' with
        | nil => simp at hh
        | cons q Q =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          refine ⟨(i, j) :: (i', j') :: Q, rfl, ?_, ?_, ?_⟩
          · rw [List.getLast?_cons_cons]; exact hl
          · rw [List.isChain_cons_cons]
            refine ⟨?_, hch⟩
            unfold LStep
            simp only
            omega
          · simp [pathSum, hgx', hgy']
      rcases hp with hp | hp | hp
      · rw [← List.drop_eq_getElem_cons hj] at hp
        exact hnext (i + 1) j hi hj (Or.inl rfl) (Or.inr rfl) (Or.inl (by omega)) hp
      · rw [← List.drop_eq_getElem_cons hi] at hp
        exact hnext i (j + 1) hi hj (Or.inr rfl) (Or.inl rfl) (Or.inr (by omega)) hp
      · exact hnext (i + 1) (j + 1) hi hj (Or.inl rfl) (Or.inl rfl) (Or.inl (by omega)) hp

theorem mem_pathSums_iff {a b c : List ℕ} (ha : a ≠ []) (hb : b ≠ []) :
    c ∈ pathSums a b ↔ ∃ P, IsLatticePath a b P ∧ c = pathSum a b P := by
  have hi : 0 < a.length := List.length_pos_iff.2 ha
  have hj : 0 < b.length := List.length_pos_iff.2 hb
  constructor
  · intro h
    obtain ⟨P, h1, h2, h3, h4⟩ := path_of_mem_pathSums a b _ 0 0 c rfl hi hj (by simpa using h)
    exact ⟨P, ⟨h1, h2, h3⟩, h4⟩
  · rintro ⟨P, ⟨h1, h2, h3⟩, rfl⟩
    simpa using mem_pathSums_of_path a b P 0 0 h1 h2 h3 hi hj

/-- (BP3 `mem_ringTypList`) the lattice DP computes `ringTyp`. -/
theorem mem_ringTypList {a b d : List ℕ} : d ∈ ringTypList a b ↔ d ∈ ringTyp a b := by
  by_cases ha : a = []
  · subst ha; simp [ringTypList, ringTyp]
  by_cases hb : b = []
  · subst hb; simp [ringTypList, ringTyp]
  unfold ringTypList ringTyp
  simp only [List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨hpath, hty⟩ := latticeStates_sound hs
    exact ⟨pathSum a b s.2.reverse, (mem_pathSums_iff ha hb).2 ⟨_, hpath, rfl⟩, hty.symm⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨P, hP, rfl⟩ := (mem_pathSums_iff ha hb).1 hc
    obtain ⟨s, hs, e⟩ := latticeStates_complete hP ha hb
    exact ⟨s, hs, e⟩

end Lax117284Proofs.Treewidth.Chars
