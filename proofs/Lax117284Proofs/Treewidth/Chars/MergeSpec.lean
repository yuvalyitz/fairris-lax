import Lax117284Proofs.Treewidth.Chars.MergeCanon

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
