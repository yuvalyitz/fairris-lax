import Lax117284Proofs.TwoSAT.Math.Defs

/-!
The classical criterion of Aspvall, Plass and Tarjan: a set of 2-clauses is satisfiable
exactly when no variable is contradictory, in the implication graph.


The proof of the criterion: a satisfying assignment makes every node true along the edges, so
no variable reaches its negation and back (`Edge.tr`). Conversely, one grows a set `S` of
nodes that is closed under successors and never contains a node together with its negation
(`Closed`, `Consistent`), deciding one variable at a time (`step`): a literal `l` that does
not reach its negation has the closed set `{l} ∪ reach l` as consequences. When every variable
is decided, `S` gives the assignment (`base_case`).
-/

namespace Lax117284Proofs.TwoSAT.Math



def nneg (a : ℕ) : ℕ := 2 * (a / 2) + (1 - a % 2)

/-- Negation is an involution. -/
theorem nneg_nneg (a : ℕ) : nneg (nneg a) = a := by unfold nneg; omega

/-- Negation has no fixed point. -/
theorem nneg_ne (a : ℕ) : nneg a ≠ a := by unfold nneg; omega

/-- Negation keeps the variable. -/
theorem nneg_div (a : ℕ) : nneg a / 2 = a / 2 := by unfold nneg; omega

/-- Negation of a node. -/
theorem nneg_node (x s : ℕ) (hs : s ≤ 1) : nneg (node x s) = node x (1 - s) := by
  unfold nneg node; omega

variable {m : ℕ} {ys ss : ℕ → ℕ}

/-- The graph is skew-symmetric. -/
theorem Edge.skew (hs : ∀ i < 2 * m, ss i ≤ 1) {a b : ℕ} (h : Edge m ys ss a b) :
    Edge m ys ss (nneg b) (nneg a) := by
  obtain ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · have h0 := hs (2 * c) (by omega)
    have h1 := hs (2 * c + 1) (by omega)
    refine ⟨c, hc, Or.inr ⟨nneg_node _ _ h1, ?_⟩⟩
    rw [nneg_node _ _ (by omega)]
    unfold node; omega
  · have h0 := hs (2 * c) (by omega)
    have h1 := hs (2 * c + 1) (by omega)
    refine ⟨c, hc, Or.inl ⟨nneg_node _ _ h0, ?_⟩⟩
    rw [nneg_node _ _ (by omega)]
    unfold node; omega

/-- Reachability is skew-symmetric. -/
theorem Reach.skew (hs : ∀ i < 2 * m, ss i ≤ 1) {a b : ℕ} (h : Reach m ys ss a b) :
    Reach m ys ss (nneg b) (nneg a) := by
  induction h with
  | single h => exact .single (h.skew hs)
  | tail _ h ih => exact .head (h.skew hs) ih

/-! ### Truth of nodes -/

/-- The node `n` is true under `A`: `2x+1` is the variable `x`, `2x` its negation. -/
def Tr (A : ℕ → Bool) (n : ℕ) : Prop := A (n / 2) = decide (n % 2 = 1)

/-- Truth of a node in terms of the variable and the sign. -/
theorem tr_node (A : ℕ → Bool) (x s : ℕ) (hs : s ≤ 1) :
    Tr A (node x s) ↔ A x = decide (s = 1) := by
  unfold Tr node
  have h1 : (2 * x + s) / 2 = x := by omega
  have h2 : (2 * x + s) % 2 = s := by omega
  rw [h1, h2]

/-- Truth of a literal is `Holds`. -/
theorem holds_iff_tr (A : ℕ → Bool) (i : ℕ) (hs : ss i ≤ 1) :
    Holds A ys ss i ↔ Tr A (node (ys i) (ss i)) := (tr_node A _ _ hs).symm

/-- Two variable nodes are not both true. -/
theorem not_tr_both (A : ℕ → Bool) (x : ℕ) : ¬ (Tr A (node x 1) ∧ Tr A (node x 0)) := by
  rintro ⟨h1, h0⟩
  rw [tr_node A _ _ (by omega)] at h1 h0
  rw [h1] at h0
  simp at h0

/-- An edge preserves the truth of nodes under a satisfying assignment. -/
theorem Edge.tr {A : ℕ → Bool} (hA : SatBy A m ys ss) (hs : ∀ i < 2 * m, ss i ≤ 1) {a b : ℕ}
    (h : Edge m ys ss a b) : Tr A a → Tr A b := by
  obtain ⟨c, hc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · have h0 := hs (2 * c) (by omega)
    have h1 := hs (2 * c + 1) (by omega)
    intro ha
    rw [tr_node A _ _ (by omega)] at ha
    rw [tr_node A _ _ h1]
    rcases hA c hc with hh | hh
    · unfold Holds at hh
      rw [ha] at hh
      have : (1 - ss (2 * c) = 1) ↔ (ss (2 * c) = 1) := by simpa using hh
      omega
    · exact hh
  · have h0 := hs (2 * c) (by omega)
    have h1 := hs (2 * c + 1) (by omega)
    intro ha
    rw [tr_node A _ _ (by omega)] at ha
    rw [tr_node A _ _ h0]
    rcases hA c hc with hh | hh
    · exact hh
    · unfold Holds at hh
      rw [ha] at hh
      have : (1 - ss (2 * c + 1) = 1) ↔ (ss (2 * c + 1) = 1) := by simpa using hh
      omega

/-- Reachability preserves the truth of nodes under a satisfying assignment. -/
theorem Reach.tr {A : ℕ → Bool} (hA : SatBy A m ys ss) (hs : ∀ i < 2 * m, ss i ≤ 1) {a b : ℕ}
    (h : Reach m ys ss a b) : Tr A a → Tr A b := by
  induction h with
  | single h => exact h.tr hA hs
  | tail _ h ih => exact fun ha => h.tr hA hs (ih ha)

/-- A satisfiable set of clauses has no contradictory variable. -/
theorem not_contra_of_sat {A : ℕ → Bool} (hA : SatBy A m ys ss) (hs : ∀ i < 2 * m, ss i ≤ 1)
    (x : ℕ) : ¬ Contra m ys ss x := by
  rintro ⟨h1, h0⟩
  by_cases hx : A x = true
  · have h : Tr A (node x 1) := (tr_node A _ _ le_rfl).2 (by simp [hx])
    exact not_tr_both A x ⟨h, h1.tr hA hs h⟩
  · have h : Tr A (node x 0) := (tr_node A _ _ (by omega)).2 (by simpa using hx)
    exact not_tr_both A x ⟨h0.tr hA hs h, h⟩

/-! ### Closed, consistent sets of nodes -/

/-- A set of nodes closed under the successors of the implication graph. -/
def Closed (m : ℕ) (ys ss : ℕ → ℕ) (S : Set ℕ) : Prop :=
  ∀ a b, Edge m ys ss a b → a ∈ S → b ∈ S

/-- A set of nodes that never contains a node together with its negation. -/
def Consistent (S : Set ℕ) : Prop := ∀ u ∈ S, nneg u ∉ S

/-- The variable `x` has one of its two literals in `S`. -/
def Decided (S : Set ℕ) (x : ℕ) : Prop := node x 1 ∈ S ∨ node x 0 ∈ S

/-- A closed set is closed under reachability. -/
theorem Closed.reach {S : Set ℕ} (hcl : Closed m ys ss S) {a b : ℕ} (h : Reach m ys ss a b)
    (ha : a ∈ S) : b ∈ S := by
  induction h with
  | single h => exact hcl _ _ h ha
  | tail _ h ih => exact hcl _ _ h ih

/-- Deciding more keeps decided variables decided. -/
theorem Decided.mono {S S' : Set ℕ} (h : S ⊆ S') {x : ℕ} (hx : Decided S x) : Decided S' x :=
  hx.imp (fun h1 => h h1) (fun h0 => h h0)

open Classical in
/-- The assignment read off a set of nodes: `x` is true when the node `2x+1` is in `S`. -/
noncomputable def readOff (S : Set ℕ) (x : ℕ) : Bool := decide (node x 1 ∈ S)

/-- Membership of the variable node in terms of `readOff`. -/
theorem readOff_eq_true {S : Set ℕ} {x : ℕ} : readOff S x = true ↔ node x 1 ∈ S := by
  unfold readOff; simp

/-- In the base case, the nodes of `S` are true under the assignment read off `S`. -/
theorem base_tr {S : Set ℕ} (hco : Consistent S) (u : ℕ) (hu : u ∈ S) :
    Tr (readOff S) u := by
  unfold Tr
  rcases Nat.mod_two_eq_zero_or_one u with h | h
  · have h1 : node (u / 2) 1 = nneg u := by unfold node nneg; omega
    have : node (u / 2) 1 ∉ S := by rw [h1]; exact hco u hu
    have : readOff S (u / 2) = false := by
      cases h' : readOff S (u / 2)
      · rfl
      · exact absurd (readOff_eq_true.1 h') this
    simp [this, h]
  · have h1 : node (u / 2) 1 = u := by unfold node; omega
    have : readOff S (u / 2) = true := readOff_eq_true.2 (by rw [h1]; exact hu)
    simp [this, h]

/-- A literal whose node is false has the node of its negation in `S`. -/
theorem base_key {V : ℕ} (hy : ∀ i < 2 * m, ys i < V) (hs : ∀ i < 2 * m, ss i ≤ 1)
    (S : Set ℕ) (hco : Consistent S) (hd : ∀ x < V, Decided S x) (i : ℕ) (hi : i < 2 * m)
    (hn : ¬ Holds (readOff S) ys ss i) : node (ys i) (1 - ss i) ∈ S := by
  have hdi := hd _ (hy i hi)
  have hsi := hs i hi
  by_contra hnot
  apply hn
  rw [holds_iff_tr _ i hsi]
  apply base_tr hco
  rcases (by omega : ss i = 0 ∨ ss i = 1) with e | e
  · rw [e] at hnot ⊢
    rcases hdi with h | h
    · exact absurd h hnot
    · exact h
  · rw [e] at hnot ⊢
    rcases hdi with h | h
    · exact h
    · exact absurd h hnot

/-- The base case: with every variable decided, the set `S` gives an assignment. -/
theorem base_case {V : ℕ} (hy : ∀ i < 2 * m, ys i < V) (hs : ∀ i < 2 * m, ss i ≤ 1)
    (S : Set ℕ) (hcl : Closed m ys ss S) (hco : Consistent S) (hd : ∀ x < V, Decided S x) :
    ∃ A, SatBy A m ys ss ∧ ∀ u ∈ S, Tr A u := by
  refine ⟨readOff S, fun c hc => ?_, base_tr hco⟩
  by_contra hcon
  rw [not_or] at hcon
  have k0 := base_key hy hs S hco hd (2 * c) (by omega) hcon.1
  have k1 := base_key hy hs S hco hd (2 * c + 1) (by omega) hcon.2
  have := hcl _ _ ⟨c, hc, Or.inl ⟨rfl, rfl⟩⟩ k0
  have h1 : node (ys (2 * c + 1)) (ss (2 * c + 1)) ∈ S := this
  have h1' := hs (2 * c + 1) (by omega)
  have := hco _ h1
  rw [nneg_node _ _ h1'] at this
  exact this k1

/-! ### Deciding one more variable -/

/-- The literal `l` and everything it reaches. -/
def Cone (m : ℕ) (ys ss : ℕ → ℕ) (l : ℕ) : Set ℕ := {u | u = l ∨ Reach m ys ss l u}

/-- A non-contradictory variable has a literal that does not reach its negation. -/
theorem exists_lit {j : ℕ} (hno : ¬ Contra m ys ss j) :
    ∃ l, l / 2 = j ∧ ¬ Reach m ys ss l (nneg l) := by
  unfold Contra at hno
  rw [not_and_or] at hno
  rcases hno with h | h
  · refine ⟨node j 1, by unfold node; omega, ?_⟩
    rwa [nneg_node _ _ le_rfl]
  · refine ⟨node j 0, by unfold node; omega, ?_⟩
    rwa [nneg_node _ _ (Nat.zero_le _)]

/-- The cone of a literal is closed under successors. -/
theorem Cone.closed (l : ℕ) : Closed m ys ss (Cone m ys ss l) := by
  intro a b h ha
  rcases ha with rfl | ha
  · exact Or.inr (.single h)
  · exact Or.inr (.tail ha h)

/-- The cone of `l` is consistent when `l` does not reach its negation. -/
theorem Cone.consistent (hs : ∀ i < 2 * m, ss i ≤ 1) {l : ℕ} (hl : ¬ Reach m ys ss l (nneg l)) :
    ∀ u ∈ Cone m ys ss l, nneg u ∉ Cone m ys ss l := by
  rintro u (rfl | hu) (hv | hv)
  · exact nneg_ne _ hv
  · exact hl hv
  · have : u = nneg l := by rw [← hv, nneg_nneg]
    exact hl (this ▸ hu)
  · have h2 := hv.skew hs
    rw [nneg_nneg] at h2
    exact hl (hu.trans h2)

/-- If `S` is closed and does not contain the negation of `l`, no node of `S` has its negation
in the cone of `l`. -/
theorem mixed (hs : ∀ i < 2 * m, ss i ≤ 1) {S : Set ℕ} (hcl : Closed m ys ss S) {l u : ℕ}
    (hund : nneg l ∉ S) (hu : u ∈ S) (hv : nneg u ∈ Cone m ys ss l) : False := by
  apply hund
  rcases hv with hv | hv
  · rw [← hv, nneg_nneg]; exact hu
  · have := hv.skew hs
    rw [nneg_nneg] at this
    exact hcl.reach this hu

/-- Enlarging a closed consistent set by the cone of a suitable literal decides its variable. -/
theorem step (hs : ∀ i < 2 * m, ss i ≤ 1) {S : Set ℕ} (hcl : Closed m ys ss S)
    (hco : Consistent S) {j : ℕ} (hund : ¬ Decided S j) (hno : ¬ Contra m ys ss j) :
    ∃ S', S ⊆ S' ∧ Closed m ys ss S' ∧ Consistent S' ∧ Decided S' j := by
  obtain ⟨l, hlj, hl⟩ := exists_lit hno
  have hn : nneg l ∉ S := by
    intro h
    apply hund
    have : nneg l / 2 = j := by rw [nneg_div]; exact hlj
    unfold Decided node
    rcases (by omega : nneg l = 2 * j + 1 ∨ nneg l = 2 * j + 0) with e | e
    · exact Or.inl (e ▸ h)
    · exact Or.inr (e ▸ h)
  refine ⟨S ∪ Cone m ys ss l, Set.subset_union_left, ?_, ?_, ?_⟩
  · rintro a b h (ha | ha)
    · exact Or.inl (hcl _ _ h ha)
    · exact Or.inr ((Cone.closed l) _ _ h ha)
  · rintro u (hu | hu) (hv | hv)
    · exact hco u hu hv
    · exact mixed hs hcl hn hu hv
    · exact mixed hs hcl hn hv (by rw [nneg_nneg]; exact hu)
    · exact Cone.consistent hs hl u hu hv
  · unfold Decided node
    rcases (by omega : l = 2 * j + 1 ∨ l = 2 * j + 0) with e | e
    · exact Or.inl (Or.inr (Or.inl e.symm))
    · exact Or.inr (Or.inr (Or.inl e.symm))

/-- **The main lemma.** A closed consistent set of nodes with all variables from `j` on
decided extends to a satisfying assignment making all its nodes true. -/
theorem exists_assign {V : ℕ} (hy : ∀ i < 2 * m, ys i < V) (hs : ∀ i < 2 * m, ss i ≤ 1)
    (hno : ∀ x < V, ¬ Contra m ys ss x) (j : ℕ) : ∀ S : Set ℕ, Closed m ys ss S → Consistent S →
    (∀ x, j ≤ x → x < V → Decided S x) → ∃ A, SatBy A m ys ss ∧ ∀ u ∈ S, Tr A u := by
  induction j with
  | zero => exact fun S hcl hco hd => base_case hy hs S hcl hco fun x hx => hd x (Nat.zero_le _) hx
  | succ j ih =>
    intro S hcl hco hd
    by_cases hj : j < V ∧ ¬ Decided S j
    · obtain ⟨S', hsub, hcl', hco', hd'⟩ := step hs hcl hco hj.2 (hno j hj.1)
      obtain ⟨A, hA, hT⟩ := ih S' hcl' hco' fun x hx hxV => by
        rcases Nat.eq_or_lt_of_le hx with rfl | h
        · exact hd'
        · exact (hd x h hxV).mono hsub
      exact ⟨A, hA, fun u hu => hT u (hsub hu)⟩
    · refine ih S hcl hco fun x hx hxV => ?_
      rcases Nat.eq_or_lt_of_le hx with rfl | h
      · by_contra hnd
        exact hj ⟨hxV, hnd⟩
      · exact hd x h hxV

/-- **The criterion.** Clauses whose variables are all below `V` are satisfiable exactly
when no variable below `V` is contradictory. -/
theorem sat2_iff_no_contra (V m : ℕ) (ys ss : ℕ → ℕ) (hy : ∀ i < 2 * m, ys i < V)
    (hs : ∀ i < 2 * m, ss i ≤ 1) :
    Sat2 m ys ss ↔ ∀ x < V, ¬ Contra m ys ss x := by
  constructor
  · rintro ⟨A, hA⟩ x _
    exact not_contra_of_sat hA hs x
  · intro hno
    obtain ⟨A, hA, _⟩ := exists_assign hy hs hno V ∅ (fun _ _ _ h => h.elim)
      (fun _ h => h.elim) (fun x hx hxV => absurd hxV (not_lt.2 hx))
    exact ⟨A, hA⟩

end Lax117284Proofs.TwoSAT.Math
