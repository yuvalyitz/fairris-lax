import Lax117284Proofs.Treewidth.Chars.Defs

/-!
# `allChains` enumerates exactly the nested chains (work package C4, part 1)

`mem_allChains`: `(chain, M) ∈ allChains S N` iff `chain` is a strictly decreasing sequence of subsets of `S`
containing `N` and `M` is a superset of `N` inside the last chain element (inside `S` if the chain is empty).

The enumeration `chainsGo` is a fuelled recursion; `chainsGo_iff` characterises its outputs for arbitrary fuel,
`bound` and accumulated `chain`, and the fuel `|S| + 1` of `allChains` is then shown not to cut any chain (a strictly
decreasing chain of subsets of `S` has at most `|S| + 1` elements).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## the candidates -/

theorem sort_sublist_of_subset {A B : Finset ℕ} (h : A ⊆ B) :
    (A.sort (· ≤ ·)).Sublist (B.sort (· ≤ ·)) := by
  have hf : (B.sort (· ≤ ·)).filter (fun x => decide (x ∈ A)) = A.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
    · intro a b _ _ h1 h2; exact le_antisymm h1 h2
    · exact (Finset.pairwise_sort _ _).filter _
    · exact Finset.pairwise_sort _ _
    · rw [List.perm_ext_iff_of_nodup]
      · intro x
        simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
        exact ⟨fun hx => hx.2, fun hx => ⟨h hx, hx⟩⟩
      · exact (Finset.sort_nodup _ _).filter _
      · exact Finset.sort_nodup _ _
  rw [← hf]; exact List.filter_sublist

/-- The candidates are exactly the sets between `N` and `N ∪ S`. -/
theorem mem_chainCands {S N X : Finset ℕ} : X ∈ chainCands S N ↔ N ⊆ X ∧ X ⊆ N ∪ S := by
  unfold chainCands
  rw [List.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [List.mem_sublists] at hc
    refine ⟨Finset.subset_union_left, Finset.union_subset Finset.subset_union_left ?_⟩
    intro x hx
    rw [List.mem_toFinset] at hx
    have := hc.subset hx
    rw [Finset.mem_sort, Finset.mem_sdiff] at this
    exact Finset.mem_union_right _ this.1
  · rintro ⟨h1, h2⟩
    refine ⟨(X \ N).sort (· ≤ ·), ?_, ?_⟩
    · rw [List.mem_sublists]
      apply sort_sublist_of_subset
      intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨?_, hx.2⟩
      rcases Finset.mem_union.1 (h2 hx.1) with h | h
      · exact absurd h hx.2
      · exact h
    · rw [Finset.sort_toFinset]; exact Finset.union_sdiff_of_subset h1

/-! ## the recursion `chainsGo` -/

/-- The chain conditions of an extension `l` below the bound `b`; `s` says that the first element must be strictly
inside `b` (the accumulated chain is non-empty). -/
def ChainOK (b : Finset ℕ) (s : Bool) : List (Finset ℕ) → Prop
  | [] => True
  | X :: r => X ⊆ b ∧ (s = true → X ⊂ b) ∧ ChainOK X true r

theorem chainsGo_iff (cands : List (Finset ℕ)) : ∀ (fuel : ℕ) (bound : Finset ℕ) (chain : List (Finset ℕ))
    (c : List (Finset ℕ)) (M : Finset ℕ),
    (c, M) ∈ chainsGo cands fuel bound chain ↔
      ∃ ext, c = chain ++ ext ∧ ext.length ≤ fuel ∧ (∀ X ∈ ext, X ∈ cands) ∧
        ChainOK bound (!chain.isEmpty) ext ∧ M ∈ cands ∧ M ⊆ ext.getLastD bound := by
  intro fuel
  induction fuel with
  | zero =>
    intro bound chain c M
    simp only [chainsGo, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨M', ⟨h1, h2⟩, rfl, rfl⟩
      exact ⟨[], by simp, by simp, by simp, trivial, h1, by simpa using h2⟩
    · rintro ⟨ext, rfl, hl, -, -, hM, hsub⟩
      have : ext = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨M, ⟨hM, by simpa using hsub⟩, by simp, rfl⟩
  | succ fuel ih =>
    intro bound chain c M
    simp only [chainsGo, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq,
      List.mem_flatMap, Bool.and_eq_true, Bool.or_eq_true]
    constructor
    · rintro (⟨M', ⟨h1, h2⟩, rfl, rfl⟩ | ⟨X, ⟨hX, ⟨hXb, hs⟩⟩, hm⟩)
      · exact ⟨[], by simp, by simp, by simp, trivial, h1, by simpa using h2⟩
      · obtain ⟨ext', rfl, hl, hc, hok, hM, hsub⟩ := (ih X (chain ++ [X]) c M).1 hm
        have hne : (!(chain ++ [X]).isEmpty) = true := by simp
        rw [hne] at hok
        refine ⟨X :: ext', by simp, by simp; omega, ?_, ?_, hM, by rw [List.getLastD_cons]; exact hsub⟩
        · intro Y hY
          rcases List.mem_cons.1 hY with rfl | hY
          · exact hX
          · exact hc Y hY
        · refine ⟨hXb, ?_, hok⟩
          intro hs'
          rcases hs with h | h
          · simp [List.isEmpty_iff] at h hs'
            subst h; simp at hs'
          · exact h
    · rintro ⟨ext, rfl, hl, hc, hok, hM, hsub⟩
      cases ext with
      | nil => exact Or.inl ⟨M, ⟨hM, by simpa using hsub⟩, by simp, rfl⟩
      | cons X ext' =>
        right
        obtain ⟨hXb, hXs, hok'⟩ := hok
        refine ⟨X, ⟨hc X (by simp), hXb, ?_⟩, ?_⟩
        · by_cases hch : chain = []
          · left; simp [hch]
          · right; exact hXs (by simp [hch])
        · rw [ih X (chain ++ [X])]
          have hne : (!(chain ++ [X]).isEmpty) = true := by simp
          refine ⟨ext', by simp, by simp at hl; omega, fun Y hY => hc Y (by simp [hY]), ?_, hM, ?_⟩
          · rw [hne]; exact hok'
          · rw [List.getLastD_cons] at hsub; exact hsub

/-! ## chains are short -/

theorem chain_length_le {n : ℕ} : ∀ {l : List (Finset ℕ)}, l.IsChain (fun X Y => Y ⊂ X) →
    (∀ X ∈ l, X.card ≤ n) → l.length ≤ n + 1 := by
  intro l
  induction l generalizing n with
  | nil => intro _ _; simp
  | cons X r ih =>
    intro hc hn
    cases r with
    | nil => simp
    | cons Y r' =>
      rw [List.isChain_cons_cons] at hc
      have hXn := hn X (by simp)
      have hlt : Y.card < X.card := Finset.card_lt_card hc.1
      have := ih (n := n - 1) hc.2 (by
        intro Z hZ
        have hpw : (Y :: r').Pairwise (fun X Y => Y ⊂ X) := hc.2.pairwise
        rcases List.mem_cons.1 hZ with rfl | hZ'
        · omega
        · have := (List.pairwise_cons.1 hpw).1 Z hZ'
          have := Finset.card_lt_card this
          omega)
      simp only [List.length_cons] at this ⊢
      omega

theorem chainOK_of {N : Finset ℕ} : ∀ (l : List (Finset ℕ)) (b : Finset ℕ) (s : Bool),
    l.IsChain (fun X Y => Y ⊂ X) → (∀ X ∈ l.head?, X ⊆ b ∧ (s = true → X ⊂ b)) → ChainOK b s l := by
  intro l
  induction l with
  | nil => intro b s _ _; trivial
  | cons X r ih =>
    intro b s hc hh
    obtain ⟨h1, h2⟩ := hh X rfl
    refine ⟨h1, h2, ih X true (List.isChain_cons.1 hc).2 ?_⟩
    intro Y hY
    have := (List.isChain_cons.1 hc).1 Y hY
    exact ⟨this.subset, fun _ => this⟩

theorem chainOK_sub (b : Finset ℕ) (s : Bool) : ∀ (l : List (Finset ℕ)), ChainOK b s l → ∀ X ∈ l, X ⊆ b := by
  intro l
  induction l generalizing b s with
  | nil => intro _ X hX; simp at hX
  | cons Y r ih =>
    intro h X hX
    obtain ⟨h1, h2, h3⟩ := h
    rcases List.mem_cons.1 hX with rfl | hX
    · exact h1
    · exact (ih Y true h3 X hX).trans h1

theorem chainOK_chain (b : Finset ℕ) (s : Bool) : ∀ (l : List (Finset ℕ)), ChainOK b s l →
    l.IsChain (fun X Y => Y ⊂ X) := by
  intro l
  induction l generalizing b s with
  | nil => intro _; exact List.IsChain.nil
  | cons X r ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    cases r with
    | nil => exact List.IsChain.singleton X
    | cons Y r' =>
      obtain ⟨h4, h5, h6⟩ := h3
      exact List.IsChain.cons_cons (h5 rfl) (ih X true ⟨h4, h5, h6⟩)

theorem chainOK_getLast (b : Finset ℕ) (s : Bool) : ∀ (l : List (Finset ℕ)), ChainOK b s l → l.getLastD b ⊆ b := by
  intro l
  induction l generalizing b s with
  | nil => intro _; simp
  | cons X r ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [List.getLastD_cons]
    exact (ih X true h3).trans h1

/-- **`allChains` enumerates exactly the chains described in its docstring.** -/
theorem mem_allChains {S N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ} :
    (chain, M) ∈ allChains S N ↔
      (∀ X ∈ chain, N ⊆ X ∧ X ⊆ S) ∧ chain.IsChain (fun X Y => Y ⊂ X) ∧ N ⊆ M ∧ M ⊆ chain.getLastD S := by
  unfold allChains
  rw [chainsGo_iff]
  constructor
  · rintro ⟨ext, rfl, hl, hc, hok, hM, hsub⟩
    have hsubS := chainOK_sub S (!([] : List (Finset ℕ)).isEmpty) _ hok
    refine ⟨fun X hX => ⟨(mem_chainCands.1 (hc X hX)).1, hsubS X hX⟩, chainOK_chain _ _ _ hok,
      (mem_chainCands.1 hM).1, hsub⟩
  · rintro ⟨hX, hch, hNM, hM⟩
    refine ⟨chain, by simp, ?_, ?_, ?_, ?_, hM⟩
    · apply (chain_length_le (n := S.card) hch _).trans (le_refl _)
      intro X hX'
      exact Finset.card_le_card (hX X hX').2
    · intro X hX'
      exact mem_chainCands.2 ⟨(hX X hX').1, (hX X hX').2.trans Finset.subset_union_right⟩
    · apply chainOK_of (N := N) chain S _ hch
      intro X hXh
      have hmem : X ∈ chain := List.mem_of_mem_head? hXh
      exact ⟨(hX X hmem).2, fun h => by simp at h⟩
    · have hMS : M ⊆ S := by
        refine hM.trans ?_
        -- the last element (or `S`) lies inside `S`
        cases hl : chain.getLast? with
        | none =>
          have : chain = [] := List.getLast?_eq_none_iff.1 hl
          subst this; simp
        | some Z =>
          have hZ : Z ∈ chain := List.mem_of_getLast? hl
          rw [List.getLastD_eq_getLast?, hl]; exact (hX Z hZ).2
      exact mem_chainCands.2 ⟨hNM, hMS.trans Finset.subset_union_right⟩

end Lax117284Proofs.Treewidth.Chars
