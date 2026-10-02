import Lax117284Proofs.Treewidth.Chars.MergeIface

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
