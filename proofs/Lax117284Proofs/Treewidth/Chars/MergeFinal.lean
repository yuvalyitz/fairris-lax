import Lax117284Proofs.Treewidth.Chars.MergeIface

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeCanon` -/

section
/-!
# The merged run is canonical, and its shape (C3)

`merge_canon`: the merged analysis `M` of `mergeAR A A' c = some M` is canonical (so `analyze B M.toRT = M`), has the
label of `A`, and the same vertices in its label tree.  Along the way: path bounds, `mergeChain` facts, `F4` lemmas.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## lattice paths -/

theorem path_bounds : ∀ (P : List (ℕ × ℕ)), P.IsChain LStep → ∀ x, P.getLast? = some x →
    ∀ p ∈ P, p.1 ≤ x.1 ∧ p.2 ≤ x.2 := by
  intro P
  induction P with
  | nil => intro _ x hx; simp at hx
  | cons p0 rest ih =>
    intro hc x hx p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact chain_le_last rest p hc x (by rw [hx]; rfl)
    · cases rest with
      | nil => simp at hp
      | cons q rest' =>
        rw [List.isChain_cons_cons] at hc
        rw [List.getLast?_cons_cons] at hx
        exact ih hc.2 x hx p hp

theorem path_zero {P : List (ℕ × ℕ)} (h : PathTo 0 0 P) : P = [(0, 0)] := by
  rcases h.split with ⟨_, _, hP⟩ | ⟨P', p, hP, hp, hst⟩
  · exact hP
  · exfalso
    unfold LStep at hst
    simp only at hst
    omega

/-! ## `mergeChain` -/

theorem mergeChain_length (na nb : List CNode) : ∀ (Q : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    (mergeChain na nb prev Q).length = Q.length := by
  intro Q
  induction Q with
  | nil => intro prev; rfl
  | cons q rest ih =>
    intro prev
    obtain ⟨i, j⟩ := q
    rw [mergeChain_cons]
    simp [ih]

theorem mem_mergeChain (na nb : List CNode) : ∀ (Q : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)) (n : CNode),
    n ∈ mergeChain na nb prev Q → ∃ i j, (i, j) ∈ Q ∧ n.bag = cbag na i ∪ cbag nb j ∧
      ∀ J ∈ n.junk, J ∈ cjunk na i ∨ J ∈ cjunk nb j := by
  intro Q
  induction Q with
  | nil => intro prev n h; simp [mergeChain] at h
  | cons q rest ih =>
    intro prev n h
    obtain ⟨i, j⟩ := q
    rw [mergeChain_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨i, j, List.mem_cons_self, rfl, ?_⟩
      intro J hJ
      simp only [List.mem_append] at hJ
      rcases hJ with hJ | hJ
      · left; cases hb : nw1 prev i <;> simp [hb] at hJ; exact hJ
      · right; cases hb : nw2 prev j <;> simp [hb] at hJ; exact hJ
    · obtain ⟨i', j', hmem, h1, h2⟩ := ih _ n h
      exact ⟨i', j', List.mem_cons_of_mem _ hmem, h1, h2⟩

/-! ## aligned lists (four) -/

theorem F4.mem_right {α β γ δ : Type} {P : α → β → γ → δ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds →
      ∀ d ∈ ds, ∃ a ∈ as, ∃ b ∈ bs, ∃ c ∈ cs, P a b c d
  | [], [], [], [], _, d, hd => by simp at hd
  | a0 :: as, b0 :: bs, c0 :: cs, d0 :: ds, h, d, hd => by
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨a0, by simp, b0, by simp, c0, by simp, h.1⟩
    · obtain ⟨a, ha, b, hb, c, hc, hP⟩ := F4.mem_right h.2 d hd
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, c, List.mem_cons_of_mem _ hc, hP⟩
  | [], [], [], _ :: _, h, _, _ => absurd h (by simp [F4])
  | [], [], _ :: _, _, h, _, _ => absurd h (by simp [F4])
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, [], _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, _ :: _, [], h, _, _ => absurd h (by simp [F4])

theorem F4.mem_left {α β γ δ : Type} {P : α → β → γ → δ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds →
      ∀ a ∈ as, ∃ b ∈ bs, ∃ c ∈ cs, ∃ d ∈ ds, P a b c d
  | [], [], [], [], _, a, ha => by simp at ha
  | a0 :: as, b0 :: bs, c0 :: cs, d0 :: ds, h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b0, by simp, c0, by simp, d0, by simp, h.1⟩
    · obtain ⟨b, hb, c, hc, d, hd, hP⟩ := F4.mem_left h.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, c, List.mem_cons_of_mem _ hc, d, List.mem_cons_of_mem _ hd, hP⟩
  | [], [], [], _ :: _, h, _, _ => absurd h (by simp [F4])
  | [], [], _ :: _, _, h, _, _ => absurd h (by simp [F4])
  | [], _ :: _, _, _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, [], _, _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, [], _, h, _, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, _ :: _, [], h, _, _ => absurd h (by simp [F4])

theorem F4.pairwise {α β γ δ : Type} {P : α → β → γ → δ → Prop} {RA : α → α → Prop} {RD : δ → δ → Prop}
    (hstep : ∀ a1 b1 c1 d1 a2 b2 c2 d2, P a1 b1 c1 d1 → P a2 b2 c2 d2 → RA a1 a2 → RD d1 d2) :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds →
      as.Pairwise RA → ds.Pairwise RD
  | [], [], [], [], _, _ => List.Pairwise.nil
  | a0 :: as, b0 :: bs, c0 :: cs, d0 :: ds, h, hA => by
    rw [List.pairwise_cons] at hA ⊢
    refine ⟨fun d hd => ?_, F4.pairwise hstep h.2 hA.2⟩
    obtain ⟨a, ha, b, hb, c, hc, hP⟩ := F4.mem_right h.2 d hd
    exact hstep _ _ _ _ _ _ _ _ h.1 hP (hA.1 a ha)
  | [], [], [], _ :: _, h, _ => absurd h (by simp [F4])
  | [], [], _ :: _, _, h, _ => absurd h (by simp [F4])
  | [], _ :: _, _, _, h, _ => absurd h (by simp [F4])
  | _ :: _, [], _, _, h, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, [], _, h, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, _ :: _, [], h, _ => absurd h (by simp [F4])

/-! ## `mergeAR` preserves the shape -/

theorem merge_canon {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) (kmax : ℕ) :
    ∀ (A A' : AR) (c : CT) (M : AR), Canon B A → Canon B A' → Pkg Ua A → Pkg Ub A' →
      c ∈ joinC kmax (AR.charF Finset.card A) (AR.charF Finset.card A') →
      mergeAR A A' c = some M →
      Canon B M ∧ M.S = A.S ∧ M.kids.length = A.kids.length ∧
        CT.verts (AR.charF Finset.card M) = CT.verts (AR.charF Finset.card A) := by
  intro A
  induction A using AR.ind with
  | _ S nA kA ih =>
    intro A' c M hcA hcA' hpA hpA' hc hM
    obtain ⟨S', nB, kB⟩ := A'
    obtain ⟨T, ty, tk⟩ := c
    rw [AR.charF_run, AR.charF_run] at hc
    obtain ⟨hSS, hlen, d, kk, hcd, hkk, hd⟩ := joinC_inv hc
    obtain ⟨rfl, rfl, rfl⟩ : T = S ∧ ty = d ∧ tk = kk := by
      simp only [node.injEq] at hcd; exact hcd
    subst hSS
    obtain ⟨Q, kM, hQ, hK, rfl⟩ := mergeAR_inv hM
    have hF4 := mergeKids_F4 kA kB tk kM hK
    have hF3 : F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB tk :=
      joinKids_F3 kmax (f := AR.charF Finset.card) (g := AR.charF Finset.card) kA kB tk
        (by simpa [AR.charFL_eq] using hkk)
    rw [canon_run] at hcA hcA'
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hcA
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ := hcA'
    have hpA1 := (pkg_run Ua _ _ _).1 hpA
    have hpB1 := (pkg_run Ub _ _ _).1 hpA'
    -- the kids
    have hkids : F4 (fun a b t m => Canon B m ∧ m.S = a.S ∧ m.kids.length = a.kids.length ∧
        CT.verts (AR.charF Finset.card m) = CT.verts (AR.charF Finset.card a)) kA kB tk kM := by
      have key : ∀ (kA : List AR) (kB : List AR) (kk : List CT) (kM : List AR),
          (∀ a ∈ kA, ∀ (b : AR) (t : CT) (m : AR), Canon B a → Canon B b → Pkg Ua a → Pkg Ub b →
            t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b) → mergeAR a b t = some m →
            Canon B m ∧ m.S = a.S ∧ m.kids.length = a.kids.length ∧
              CT.verts (AR.charF Finset.card m) = CT.verts (AR.charF Finset.card a)) →
          (∀ a ∈ kA, Canon B a ∧ Pkg Ua a) → (∀ b ∈ kB, Canon B b ∧ Pkg Ub b) →
          F4 (fun a b t m => mergeAR a b t = some m) kA kB kk kM →
          F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB kk →
          F4 (fun a b t m => Canon B m ∧ m.S = a.S ∧ m.kids.length = a.kids.length ∧
            CT.verts (AR.charF Finset.card m) = CT.verts (AR.charF Finset.card a)) kA kB kk kM := by
        intro kA
        induction kA with
        | nil =>
          intro kB kk kM _ _ _ h4 h3
          cases kB <;> cases kk <;> cases kM <;> simp_all [F4, F3]
        | cons a kA ih' =>
          intro kB kk kM hih hca hcb h4 h3
          cases kB with
          | nil => cases kk <;> cases kM <;> simp [F4] at h4
          | cons b kB =>
            cases kk with
            | nil => simp [F4] at h4
            | cons t kk =>
              cases kM with
              | nil => simp [F4] at h4
              | cons m kM =>
                refine ⟨hih a (by simp) b t m (hca a (by simp)).1 (hcb b (by simp)).1 (hca a (by simp)).2
                  (hcb b (by simp)).2 h3.1 h4.1, ih' kB kk kM (fun a' ha' => hih a' (List.mem_cons_of_mem _ ha'))
                  (fun a' ha' => hca a' (List.mem_cons_of_mem _ ha'))
                  (fun b' hb' => hcb b' (List.mem_cons_of_mem _ hb')) h4.2 h3.2⟩
      exact key kA kB tk kM (fun a ha b t m hca hcb hpa hpb ht hm => ih a ha b t m hca hcb hpa hpb ht hm)
        (fun a ha => ⟨hA7 a ha, hpA1.2.2 a ha⟩) (fun b hb => ⟨hB7 b hb, hpB1.2.2 b hb⟩) hF4 hF3
    have hlens := hF4.length_eq
    -- bounds of the path
    obtain ⟨hpath1, hpath2, hpath3⟩ := (findPath_spec hQ).1
    have hlenA : (nA.map (fun n => n.bag.card)).length = nA.length := List.length_map _
    have hlenB : (nB.map (fun n => n.bag.card)).length = nB.length := List.length_map _
    have hbnd := path_bounds Q hpath3 _ hpath2
    have hnA : 0 < nA.length := List.length_pos_iff.2 hA1
    have hnB : 0 < nB.length := List.length_pos_iff.2 hB1
    have hQne : Q ≠ [] := by rintro rfl; simp at hpath1
    refine ⟨?_, rfl, hlens.2.2.symm, ?_⟩
    · rw [canon_run]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h
        have := mergeChain_length nA nB Q none
        rw [h] at this
        exact hQne (List.length_eq_zero_iff.1 this.symm)
      · intro n hn
        obtain ⟨i, j, hij, hb, hj⟩ := mem_mergeChain nA nB Q none n hn
        have hb1 := hbnd (i, j) hij
        have hi : i < nA.length := by simp only [hlenA, hlenB] at hb1; omega
        have hj' : j < nB.length := by simp only [hlenA, hlenB] at hb1; omega
        have hmA : nA[i] ∈ nA := List.getElem_mem hi
        have hmB : nB[j] ∈ nB := List.getElem_mem hj'
        refine ⟨?_, ?_⟩
        · rw [hb, Finset.union_inter_distrib_right, cbag_mem hi, cbag_mem hj', (hA2 _ hmA).1, (hB2 _ hmB).1,
            Finset.union_self]
        · intro J hJ
          rcases hj J hJ with h | h
          · rw [cjunk_mem hi] at h; exact (hA2 _ hmA).2 J h
          · rw [cjunk_mem hj'] at h; exact (hB2 _ hmB).2 J h
      · intro m hm
        obtain ⟨a, ha, b, hb, t, ht, hP⟩ := F4.mem_right hkids m hm
        have := hA3 a ha
        unfold prunedB at this ⊢
        have hl := hP.2.2.1
        have hleaf : m.isLeaf = a.isLeaf := by
          unfold AR.isLeaf
          cases hm' : m.kids <;> cases ha' : a.kids <;> simp [hm', ha'] at hl ⊢
        rw [hleaf, hP.2.1]
        exact this
      · intro m hm
        have hkA : kA.length = 1 := by rw [hlens.2.2, hm]; rfl
        obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hkA
        obtain ⟨a', ha', b', hb', t', ht', hP⟩ := F4.mem_right hkids m (by rw [hm]; simp)
        simp only [List.mem_singleton] at ha'
        subst ha'
        rw [hP.2.1]
        exact hA4 a' rfl
      · exact F4.pairwise (RA := fun a1 a2 => CT.key T a1.char ≤ CT.key T a2.char)
          (RD := fun d1 d2 => CT.key T d1.char ≤ CT.key T d2.char)
          (by
            intro a1 b1 c1 d1 a2 b2 c2 d2 P1 P2 h
            have e1 : CT.key T d1.char = CT.key T a1.char := by
              unfold CT.key; rw [AR.char_eq_charF, AR.char_eq_charF, P1.2.2.2]
            have e2 : CT.key T d2.char = CT.key T a2.char := by
              unfold CT.key; rw [AR.char_eq_charF, AR.char_eq_charF, P2.2.2.2]
            rw [e1, e2]; exact h) hkids hA5
      · intro hkM
        have hkA : kA = [] := by
          have : kA.length = 0 := by rw [hlens.2.2, hkM]; rfl
          exact List.length_eq_zero_iff.1 this
        have hkB : kB = [] := by
          have : kB.length = 0 := by rw [← hlens.1, hkA]; rfl
          exact List.length_eq_zero_iff.1 this
        have h1 := hA6 hkA
        have h2 := hB6 hkB
        have hQ0 : PathTo 0 0 Q := by
          refine ⟨hpath1, ?_, hpath3⟩
          rw [hpath2]; simp only [hlenA, hlenB, h1, h2]
        rw [path_zero hQ0]
        rfl
      · intro k hk
        obtain ⟨a, ha, b, hb, t, ht, hP⟩ := F4.mem_right hkids k hk
        exact hP.1
    · ext x
      simp only [AR.charF_run, CT.mem_verts, List.mem_map]
      constructor
      · rintro (h | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
        · exact Or.inl h
        · obtain ⟨a, ha, b, hb, t, ht, hP⟩ := F4.mem_right hkids k hk
          exact Or.inr ⟨_, ⟨a, ha, rfl⟩, by rw [← hP.2.2.2]; exact hx⟩
      · rintro (h | ⟨_, ⟨a, ha, rfl⟩, hx⟩)
        · exact Or.inl h
        · obtain ⟨b, hb, t, ht, m, hm, hP⟩ := F4.mem_left hkids a ha
          exact Or.inr ⟨_, ⟨m, hm, rfl⟩, by rw [hP.2.2.2]; exact hx⟩

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeSpec` -/

section
/-!
# Sizes along the merged chain: `DomC` and the width (C3)

`merge_props`: for `mergeAR A A' c = some M`, the characteristic of `M` is dominated by the join option `c`, and if all
bags of the two analysed trees have at most `kmax` elements, so do all bags of `M.toRT`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## bags of a chain -/

theorem bags_chainToRT_mem (K : List RT) : ∀ (n : List CNode), n ≠ [] → ∀ X, X ∈ (AR.chainToRT n K).bags →
    (∃ y ∈ n, X = y.bag) ∨ (∃ y ∈ n, ∃ J ∈ y.junk, X ∈ J.bags) ∨ ∃ K' ∈ K, X ∈ K'.bags := by
  intro n
  induction n with
  | nil => intro h; exact absurd rfl h
  | cons a r ih =>
    intro _ X hX
    cases r with
    | nil =>
      rw [AR.chainToRT, RT.bags_node] at hX
      rcases hX with rfl | ⟨k, hk, hX⟩
      · exact Or.inl ⟨a, List.mem_cons_self, rfl⟩
      · rcases List.mem_append.1 hk with hk | hk
        · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, k, hk, hX⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hX⟩)
    | cons b r =>
      rw [AR.chainToRT, RT.bags_node] at hX
      rcases hX with rfl | ⟨k, hk, hX⟩
      · exact Or.inl ⟨a, List.mem_cons_self, rfl⟩
      · rcases List.mem_append.1 hk with hk | hk
        · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, k, hk, hX⟩)
        · rw [List.mem_singleton] at hk
          subst hk
          rcases ih (by simp) X hX with ⟨y, hy, hXy⟩ | ⟨y, hy, J, hJ, hXJ⟩ | h
          · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hXy⟩
          · exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, J, hJ, hXJ⟩)
          · exact Or.inr (Or.inr h)

theorem bags_chainToRT_sub (K : List RT) : ∀ (n : List CNode) X,
    ((∃ J ∈ (n.map (fun y => y.junk)).flatten, X ∈ J.bags) ∨ (∃ K' ∈ K, X ∈ K'.bags) ∨ (∃ y ∈ n, X = y.bag)) →
    X ∈ (AR.chainToRT n K).bags := by
  intro n
  induction n with
  | nil =>
    intro X h
    rcases h with ⟨J, hJ, _⟩ | ⟨K', hK', hX⟩ | ⟨y, hy, _⟩
    · simp at hJ
    · rw [AR.chainToRT, RT.bags_node]; exact Or.inr ⟨K', hK', hX⟩
    · simp at hy
  | cons a r ih =>
    intro X h
    cases r with
    | nil =>
      rw [AR.chainToRT, RT.bags_node]
      rcases h with ⟨J, hJ, hX⟩ | ⟨K', hK', hX⟩ | ⟨y, hy, hXy⟩
      · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at hJ
        exact Or.inr ⟨J, List.mem_append_left _ hJ, hX⟩
      · exact Or.inr ⟨K', List.mem_append_right _ hK', hX⟩
      · simp only [List.mem_singleton] at hy; subst hy; exact Or.inl hXy
    | cons b r =>
      rw [AR.chainToRT, RT.bags_node]
      rcases h with ⟨J, hJ, hX⟩ | ⟨K', hK', hX⟩ | ⟨y, hy, hXy⟩
      · rw [List.map_cons, List.flatten_cons, List.mem_append] at hJ
        rcases hJ with hJ | hJ
        · exact Or.inr ⟨J, List.mem_append_left _ hJ, hX⟩
        · exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ih X (Or.inl ⟨J, hJ, hX⟩)⟩
      · exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ih X (Or.inr (Or.inl ⟨K', hK', hX⟩))⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl hXy
        · exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ih X (Or.inr (Or.inr ⟨y, hy, hXy⟩))⟩

/-! ## sizes -/

theorem exists_typical_ge (a : List ℕ) {z : ℕ} (hz : z ∈ a) : ∃ w ∈ typical a, z ≤ w := by
  have hne : a ≠ [] := List.ne_nil_of_mem hz
  refine ⟨maxOf (typical a), maxOf_mem (typical_ne_nil hne), ?_⟩
  rw [maxOf_typical]; exact le_maxOf hz

theorem mergeChain_sizes (na nb : List CNode) : ∀ (Q : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    (mergeChain na nb prev Q).map (fun n => n.bag.card) =
      Q.map (fun p => (cbag na p.1 ∪ cbag nb p.2).card) := by
  intro Q
  induction Q with
  | nil => intro prev; rfl
  | cons q rest ih =>
    intro prev
    obtain ⟨i, j⟩ := q
    rw [mergeChain_cons]
    simp [ih]

theorem getD_map_card {n : List CNode} {i : ℕ} (hi : i < n.length) :
    (n.map (fun x => x.bag.card)).getD i 0 = (cbag n i).card := by
  rw [cbag_mem hi]
  simp [List.getD_eq_getElem?_getD, hi]

theorem F4_domCL {Q : AR → Prop} : ∀ {as : List AR} {bs : List AR} {cs : List CT} {ds : List AR},
    F4 (fun (_ : AR) (_ : AR) t m => DomC (AR.charF Finset.card m) t ∧ Q m) as bs cs ds →
    DomCL (ds.map (AR.charF Finset.card)) cs
  | [], [], [], [], _ => trivial
  | a :: as, b :: bs, c :: cs, d :: ds, h => ⟨h.1.1, F4_domCL h.2⟩
  | [], [], [], _ :: _, h => absurd h (by simp [F4])
  | [], [], _ :: _, _, h => absurd h (by simp [F4])
  | [], _ :: _, _, _, h => absurd h (by simp [F4])
  | _ :: _, [], _, _, h => absurd h (by simp [F4])
  | _ :: _, _ :: _, [], _, h => absurd h (by simp [F4])
  | _ :: _, _ :: _, _ :: _, [], h => absurd h (by simp [F4])

/-- **Dominance and width of the merged run.** -/
theorem merge_props {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) (kmax : ℕ) :
    ∀ (A A' : AR) (c : CT) (M : AR), Canon B A → Canon B A' → Pkg Ua A → Pkg Ub A' →
      (∀ X ∈ (AR.toRT A).bags, X.card ≤ kmax) → (∀ X ∈ (AR.toRT A').bags, X.card ≤ kmax) →
      c ∈ joinC kmax (AR.charF Finset.card A) (AR.charF Finset.card A') →
      mergeAR A A' c = some M →
      DomC (AR.charF Finset.card M) c ∧ ∀ Y ∈ (AR.toRT M).bags, Y.card ≤ kmax := by
  intro A
  induction A using AR.ind with
  | _ S nA kA ih =>
    intro A' c M hcA hcA' hpA hpA' hWA hWB hc hM
    obtain ⟨S', nB, kB⟩ := A'
    obtain ⟨T, ty, tk⟩ := c
    rw [AR.charF_run, AR.charF_run] at hc
    obtain ⟨hSS, hlen, d, kk, hcd, hkk, hd⟩ := joinC_inv hc
    obtain ⟨rfl, rfl, rfl⟩ : T = S ∧ ty = d ∧ tk = kk := by
      simp only [node.injEq] at hcd; exact hcd
    subst hSS
    obtain ⟨Q, kM, hQ, hK, rfl⟩ := mergeAR_inv hM
    have hF4 := mergeKids_F4 kA kB tk kM hK
    have hF3 : F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB tk :=
      joinKids_F3 kmax (f := AR.charF Finset.card) (g := AR.charF Finset.card) kA kB tk
        (by simpa [AR.charFL_eq] using hkk)
    rw [canon_run] at hcA hcA'
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hcA
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ := hcA'
    have hpA1 := (pkg_run Ua _ _ _).1 hpA
    have hpB1 := (pkg_run Ub _ _ _).1 hpA'
    have hlens := hF4.length_eq
    -- kids
    have hkids : F4 (fun a b t m => DomC (AR.charF Finset.card m) t ∧ ∀ Y ∈ (AR.toRT m).bags, Y.card ≤ kmax)
        kA kB tk kM := by
      have key : ∀ (kA : List AR) (kB : List AR) (kk : List CT) (kM : List AR),
          (∀ a ∈ kA, ∀ (b : AR) (t : CT) (m : AR), Canon B a → Canon B b → Pkg Ua a → Pkg Ub b →
            (∀ X ∈ (AR.toRT a).bags, X.card ≤ kmax) → (∀ X ∈ (AR.toRT b).bags, X.card ≤ kmax) →
            t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b) → mergeAR a b t = some m →
            DomC (AR.charF Finset.card m) t ∧ ∀ Y ∈ (AR.toRT m).bags, Y.card ≤ kmax) →
          (∀ a ∈ kA, Canon B a ∧ Pkg Ua a ∧ ∀ X ∈ (AR.toRT a).bags, X.card ≤ kmax) →
          (∀ b ∈ kB, Canon B b ∧ Pkg Ub b ∧ ∀ X ∈ (AR.toRT b).bags, X.card ≤ kmax) →
          F4 (fun a b t m => mergeAR a b t = some m) kA kB kk kM →
          F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB kk →
          F4 (fun a b t m => DomC (AR.charF Finset.card m) t ∧ ∀ Y ∈ (AR.toRT m).bags, Y.card ≤ kmax)
            kA kB kk kM := by
        intro kA
        induction kA with
        | nil =>
          intro kB kk kM _ _ _ h4 h3
          cases kB <;> cases kk <;> cases kM <;> simp_all [F4, F3]
        | cons a kA ih' =>
          intro kB kk kM hih hca hcb h4 h3
          cases kB with
          | nil => cases kk <;> cases kM <;> simp [F4] at h4
          | cons b kB =>
            cases kk with
            | nil => simp [F4] at h4
            | cons t kk =>
              cases kM with
              | nil => simp [F4] at h4
              | cons m kM =>
                have hca' := hca a (by simp)
                have hcb' := hcb b (by simp)
                refine ⟨hih a (by simp) b t m hca'.1 hcb'.1 hca'.2.1 hcb'.2.1 hca'.2.2 hcb'.2.2 h3.1 h4.1,
                  ih' kB kk kM (fun a' ha' => hih a' (List.mem_cons_of_mem _ ha'))
                  (fun a' ha' => hca a' (List.mem_cons_of_mem _ ha'))
                  (fun b' hb' => hcb b' (List.mem_cons_of_mem _ hb')) h4.2 h3.2⟩
      -- bags of the kids are bags of the parent
      have hbagsA : ∀ a ∈ kA, ∀ X ∈ (AR.toRT a).bags, X.card ≤ kmax := by
        intro a ha X hX
        apply hWA
        rw [AR.toRT_run]
        exact bags_chainToRT_sub _ nA X (Or.inr (Or.inl ⟨AR.toRT a, List.mem_map.2 ⟨a, ha, rfl⟩, hX⟩))
      have hbagsB : ∀ b ∈ kB, ∀ X ∈ (AR.toRT b).bags, X.card ≤ kmax := by
        intro b hb X hX
        apply hWB
        rw [AR.toRT_run]
        exact bags_chainToRT_sub _ nB X (Or.inr (Or.inl ⟨AR.toRT b, List.mem_map.2 ⟨b, hb, rfl⟩, hX⟩))
      exact key kA kB tk kM (fun a ha b t m hca hcb hpa hpb hwa hwb ht hm => ih a ha b t m hca hcb hpa hpb hwa hwb ht hm)
        (fun a ha => ⟨hA7 a ha, hpA1.2.2 a ha, hbagsA a ha⟩) (fun b hb => ⟨hB7 b hb, hpB1.2.2 b hb, hbagsB b hb⟩)
        hF4 hF3
    -- path data
    obtain ⟨hpath1, hpath2, hpath3⟩ := (findPath_spec hQ).1
    have hdom := (findPath_spec hQ).2
    have hlenA : (nA.map (fun n => n.bag.card)).length = nA.length := List.length_map _
    have hlenB : (nB.map (fun n => n.bag.card)).length = nB.length := List.length_map _
    have hbnd := path_bounds Q hpath3 _ hpath2
    have hnA : 0 < nA.length := List.length_pos_iff.2 hA1
    have hnB : 0 < nB.length := List.length_pos_iff.2 hB1
    have hfA := chainToRT_facts (kA.map AR.toRT) nA
    have hfB := chainToRT_facts (kB.map AR.toRT) nB
    rw [AR.toRT_run] at hpA1 hpB1
    -- inside the path
    have hin : ∀ p ∈ Q, p.1 < nA.length ∧ p.2 < nB.length := by
      intro p hp
      have := hbnd p hp
      simp only [hlenA, hlenB] at this
      omega
    -- the size at a path point
    have hsize : ∀ p ∈ Q, (cbag nA p.1 ∪ cbag nB p.2).card =
        (nA.map (fun n => n.bag.card)).getD p.1 0 + (nB.map (fun n => n.bag.card)).getD p.2 0 - T.card := by
      intro p hp
      obtain ⟨hi, hj⟩ := hin p hp
      have hmA : nA[p.1] ∈ nA := List.getElem_mem hi
      have hmB : nB[p.2] ∈ nB := List.getElem_mem hj
      rw [getD_map_card hi, getD_map_card hj]
      have hAB : cbag nA p.1 ∩ cbag nB p.2 = T := by
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hx
          rw [cbag_mem hi] at h1; rw [cbag_mem hj] at h2
          have hxB : x ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨(hpA1.2.1 (hfA.1 _ hmA h1)), hpB1.2.1 (hfB.1 _ hmB h2)⟩
          rw [← (hA2 _ hmA).1]; exact Finset.mem_inter.2 ⟨h1, hxB⟩
        · intro x hx
          have h1 : x ∈ nA[p.1].bag := by rw [← (hA2 _ hmA).1] at hx; exact (Finset.mem_inter.1 hx).1
          have h2 : x ∈ nB[p.2].bag := by rw [← (hB2 _ hmB).1] at hx; exact (Finset.mem_inter.1 hx).1
          rw [cbag_mem hi, cbag_mem hj]
          exact Finset.mem_inter.2 ⟨h1, h2⟩
      have := Finset.card_union_add_card_inter (cbag nA p.1) (cbag nB p.2)
      rw [hAB] at this
      omega
    have hSle : ∀ p ∈ Q, T.card ≤ (nA.map (fun n => n.bag.card)).getD p.1 0 := by
      intro p hp
      obtain ⟨hi, _⟩ := hin p hp
      have hmA : nA[p.1] ∈ nA := List.getElem_mem hi
      rw [getD_map_card hi, cbag_mem hi]
      apply Finset.card_le_card
      rw [← (hA2 _ hmA).1]; exact Finset.inter_subset_left
    have hpathSums : ∀ z ∈ pathSum (nA.map (fun n => n.bag.card)) (nB.map (fun n => n.bag.card)) Q,
        T.card ≤ z := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
      have := hSle p hp
      omega
    have hsizes : (mergeChain nA nB none Q).map (fun n => n.bag.card) =
        (pathSum (nA.map (fun n => n.bag.card)) (nB.map (fun n => n.bag.card)) Q).map (· - T.card) := by
      rw [mergeChain_sizes]
      unfold pathSum
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp]
      exact hsize p hp
    constructor
    · rw [AR.charF_run]
      refine ⟨rfl, ?_, ?_⟩
      · have : (List.map (fun n => Finset.card n.bag) (mergeChain nA nB none Q)) =
            (pathSum (nA.map (fun n => n.bag.card)) (nB.map (fun n => n.bag.card)) Q).map (· - T.card) := hsizes
        rw [this, typical_map_sub _ _ hpathSums]
        exact hdom
      · exact F4_domCL hkids
    · intro Y hY
      rw [AR.toRT_run] at hY
      have hne : mergeChain nA nB none Q ≠ [] := by
        intro h
        have := mergeChain_length nA nB Q none
        rw [h] at this
        have hQne : Q ≠ [] := by rintro rfl; simp at hpath1
        exact hQne (List.length_eq_zero_iff.1 this.symm)
      rcases bags_chainToRT_mem _ _ hne Y hY with ⟨y, hy, rfl⟩ | ⟨y, hy, J, hJ, hYJ⟩ | ⟨K', hK', hYK⟩
      · -- a merged chain bag
        have hmem : y.bag.card ∈ (mergeChain nA nB none Q).map (fun n => n.bag.card) :=
          List.mem_map.2 ⟨y, hy, rfl⟩
        rw [hsizes] at hmem
        obtain ⟨z, hz, hzeq⟩ := List.mem_map.1 hmem
        obtain ⟨w, hw, hzw⟩ := exists_typical_ge _ hz
        obtain ⟨y', hy', hwy⟩ := hdom.exists_le (List.mem_map.2 ⟨w, hw, rfl⟩)
        have hall := (List.all_eq_true.1 (List.mem_filter.1 hd).2) y' hy'
        simp only [decide_eq_true_eq] at hall
        omega
      · obtain ⟨i, j, hij, hb, hj⟩ := mem_mergeChain nA nB Q none y hy
        obtain ⟨hi, hj'⟩ := hin (i, j) hij
        simp only at hi hj'
        rcases hj J hJ with h | h
        · rw [cjunk_mem hi] at h
          apply hWA
          rw [AR.toRT_run]
          exact bags_chainToRT_sub _ nA Y (Or.inl ⟨J, List.mem_flatten.2 ⟨nA[i].junk,
            List.mem_map.2 ⟨nA[i], List.getElem_mem hi, rfl⟩, h⟩, hYJ⟩)
        · rw [cjunk_mem hj'] at h
          apply hWB
          rw [AR.toRT_run]
          exact bags_chainToRT_sub _ nB Y (Or.inl ⟨J, List.mem_flatten.2 ⟨nB[j].junk,
            List.mem_map.2 ⟨nB[j], List.getElem_mem hj', rfl⟩, h⟩, hYJ⟩)
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hK'
        obtain ⟨a, ha, b, hb, t, ht, hP⟩ := F4.mem_right hkids m hm
        exact hP.2 Y hYK

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeFinal` -/

section
/-!
# `mergeReal_spec`, `realJoin_spec`, `realize_join` (C3)

The realisation of a join option: two partial decompositions `ta`, `tb` of the two sides of a join node, and an option
`c` of the join of their characteristics, are merged by `mergeReal` into a partial decomposition of the join node
whose characteristic is dominated by `c`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem allne_analyze (B : Finset ℕ) (t : RT) : AR.All (fun _ c => c ≠ []) (analyze B t) :=
  AR.All.mono (fun _ c h => h.1) _ (analyze_all B t)

/-- `mergeReal`: for a join option `c` of the *actual* characteristics. -/
theorem mergeReal_spec {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {c : CT}
    (hc : c ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)) :
    ∃ t, mergeReal a.bag ta tb c = some t ∧ PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, hsub, -, -, hcross⟩ := hg'
  have hBa : a.bag ⊆ a.under := NT.bag_subset_under a
  have hBb : a.bag ⊆ b.under := hab ▸ NT.bag_subset_under b
  have hUab : a.under ∩ b.under = a.bag := Finset.Subset.antisymm hsub (Finset.subset_inter hBa hBb)
  set B := a.bag with hB
  set A := analyze B ta with hA
  set A' := analyze B tb with hA'
  have hcA : Canon B A := analyze_canon B ta
  have hcA' : Canon B A' := analyze_canon B tb
  have hpA : Pkg a.under A := pkg_analyze B a.under ta ha.1.conn (by rw [ha.1.verts_eq])
  have hpA' : Pkg b.under A' := pkg_analyze B b.under tb hb.1.conn (by rw [hb.1.verts_eq])
  have hc' : c ∈ joinC (k + 1) (AR.charF Finset.card A) (AR.charF Finset.card A') := by
    rw [char_eq_charF, char_eq_charF] at hc; exact hc
  obtain ⟨M, hM⟩ := mergeAR_exists (k + 1) A A' c (allne_analyze B ta) (allne_analyze B tb) hc'
  have hWA : ∀ X ∈ (AR.toRT A).bags, X.card ≤ k + 1 := width_toRT_analyze B ha.2
  have hWB : ∀ X ∈ (AR.toRT A').bags, X.card ≤ k + 1 := width_toRT_analyze B hb.2
  obtain ⟨hdom, hwidth⟩ := merge_props hUab (k + 1) A A' c M hcA hcA' hpA hpA' hWA hWB hc' hM
  have hiface := merge_interface hUab (k + 1) A A' c M hcA hcA' hpA hpA' hc' hM
  have hcanon := (merge_canon hUab (k + 1) A A' c M hcA hcA' hpA hpA' hc' hM).1
  refine ⟨AR.toRT M, ?_, ⟨⟨?_, ?_, hiface.conn⟩, hwidth⟩, ?_⟩
  · unfold mergeReal
    rw [hM]; rfl
  · -- vertices
    rw [hiface.verts, verts_toRT_analyze, verts_toRT_analyze, ha.1.verts_eq, hb.1.verts_eq]
    rfl
  · -- edges
    intro u v huv hu hv
    have hcov : ∀ {X : Finset ℕ}, X ∈ ta.bags ∨ X ∈ tb.bags → u ∈ X → v ∈ X →
        ∃ Y ∈ (AR.toRT M).bags, u ∈ Y ∧ v ∈ Y := by
      intro X hX hu' hv'
      rcases hX with hX | hX
      · obtain ⟨Y, hY, hXY⟩ := hiface.bagsA X ((mem_bags_toRT_analyze B ta X).2 hX)
        exact ⟨Y, hY, hXY hu', hXY hv'⟩
      · obtain ⟨Y, hY, hXY⟩ := hiface.bagsB X ((mem_bags_toRT_analyze B tb X).2 hX)
        exact ⟨Y, hY, hXY hu', hXY hv'⟩
    simp only [NT.under, Finset.mem_union] at hu hv
    by_cases hua : u ∈ a.under
    · by_cases hva : v ∈ a.under
      · obtain ⟨X, hX, hxu, hxv⟩ := ha.1.edges u v huv hua hva
        exact hcov (Or.inl hX) hxu hxv
      · have hvb : v ∈ b.under := hv.resolve_left hva
        by_cases hub : u ∈ b.under
        · obtain ⟨X, hX, hxu, hxv⟩ := hb.1.edges u v huv hub hvb
          exact hcov (Or.inr hX) hxu hxv
        · exfalso
          have hadj : adj u v = true ∨ adj v u = true := by
            have h := huv
            simp only [Adj.graph, SimpleGraph.fromRel_adj] at h
            exact h.2
          rcases hcross u hua v hvb hadj with h | h
          · exact hub (hBb h)
          · exact hva (hBa h)
    · have hub : u ∈ b.under := hu.resolve_left hua
      by_cases hvb : v ∈ b.under
      · obtain ⟨X, hX, hxu, hxv⟩ := hb.1.edges u v huv hub hvb
        exact hcov (Or.inr hX) hxu hxv
      · have hva : v ∈ a.under := hv.resolve_right hvb
        exfalso
        have hadj : adj v u = true ∨ adj u v = true := by
          have h := huv.symm
          simp only [Adj.graph, SimpleGraph.fromRel_adj] at h
          exact h.2
        rcases hcross v hva u hub hadj with h | h
        · exact hvb (hBb h)
        · exact hua (hBa h)
  · -- the characteristic
    rw [char_eq_charF, analyze_toRT B M hcanon]
    exact hdom

/-- Join, realised. -/
theorem realize_join {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {c : CT}
    (hc : c ∈ CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)) :
    ∃ t, PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  obtain ⟨t, -, h1, h2⟩ := mergeReal_spec hg ha hb hc
  exact ⟨t, h1, h2⟩

/-- **NEW** the join step of the extraction (uses `joinC_mono`, `mergeReal_spec`). -/
theorem realJoin_spec {adj : Adj} {a b : NT} {k : ℕ} {ta tb : RT} (hg : (NT.join a b).Good adj)
    (ha : PTD adj a k ta) (hb : PTD adj b k tb) {ca cb c : CT} (hca : DomC (ta.char a.bag) ca)
    (hcb : DomC (tb.char a.bag) cb) (hc : c ∈ CT.joinC (k + 1) ca cb) :
    ∃ t, realJoin (k + 1) a.bag ta tb c = some t ∧ PTD adj (.join a b) k t ∧ DomC (t.char a.bag) c := by
  obtain ⟨d, hd, hdc⟩ := joinC_mono (k + 1) hca hcb c hc
  have hsome : ((CT.joinC (k + 1) (ta.char a.bag) (tb.char a.bag)).find? (fun e => domCB e c)).isSome = true :=
    List.find?_isSome.2 ⟨d, hd, domCB_iff.2 hdc⟩
  obtain ⟨d0, hd0⟩ := Option.isSome_iff_exists.1 hsome
  have hmem := List.mem_of_find?_eq_some hd0
  have hpred : DomC d0 c := domCB_iff.1 (List.find?_some (p := fun e => domCB e c) hd0)
  obtain ⟨t, ht, h1, h2⟩ := mergeReal_spec hg ha hb hmem
  refine ⟨t, ?_, h1, DomC.trans h2 hpred⟩
  unfold realJoin
  rw [hd0]
  exact ht

end Lax117284Proofs.Treewidth.Chars

end
