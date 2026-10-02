import Lax117284Proofs.Treewidth.Chars.JoinShape
import Lax117284Proofs.Treewidth.Chars.JoinSeq
import Lax117284Proofs.Treewidth.Chars.Restrict
import Lax117284Proofs.Treewidth.Chars.Dom

/-!
# The exact join layer (C3): `char_join_dom` (Lemma 3.14) and `joinC_mono` (Lemma 3.13 per run)

* `AR.All P` — a predicate on the chains of every run of an analysis (a generic invariant carrier);
* `analyze_all` — chains are non-empty, every chain node of a run with label `S` has `bag ∩ B = S` and is a bag of
  the analysed tree;
* `joinC_charF` — for one analysis `r` and three size functions with `f₃ + |S| = f₁ + f₂` on the chains, the join of
  `charF f₁` and `charF f₂` contains an element dominating `charF f₃`;
* `char_join_dom`, `joinC_mono`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## invariants on analyses -/

mutual
/-- `P` holds of (label, chain) of every run. -/
def AR.All (P : Finset ℕ → List CNode → Prop) : AR → Prop
  | .run S c ks => P S c ∧ AR.AllL P ks
def AR.AllL (P : Finset ℕ → List CNode → Prop) : List AR → Prop
  | [] => True
  | k :: ks => AR.All P k ∧ AR.AllL P ks
end

theorem AR.allL_iff (P : Finset ℕ → List CNode → Prop) : ∀ ks : List AR, AR.AllL P ks ↔ ∀ k ∈ ks, AR.All P k
  | [] => by simp [AR.AllL]
  | k :: ks => by simp [AR.AllL, AR.allL_iff P ks]

theorem AR.all_run (P : Finset ℕ → List CNode → Prop) (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    AR.All P (.run S c ks) ↔ P S c ∧ ∀ k ∈ ks, AR.All P k := by
  simp [AR.All, AR.allL_iff]

theorem AR.All.mono {P Q : Finset ℕ → List CNode → Prop} (h : ∀ S c, P S c → Q S c) :
    ∀ r : AR, AR.All P r → AR.All Q r := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    rw [AR.all_run, AR.all_run]
    rintro ⟨h1, h2⟩
    exact ⟨h S c h1, fun k hk => ih k hk (h2 k hk)⟩

theorem AR.All.kid {P : Finset ℕ → List CNode → Prop} {r : AR} (h : AR.All P r) {k : AR} (hk : k ∈ r.kids) :
    AR.All P k := by
  cases r with
  | run S c ks => exact ((AR.all_run P S c ks).1 h).2 k hk

theorem AR.All.here {P : Finset ℕ → List CNode → Prop} {r : AR} (h : AR.All P r) : P r.S r.chain := by
  cases r with
  | run S c ks => exact ((AR.all_run P S c ks).1 h).1

theorem mkNode_all (P : Finset ℕ → List CNode → Prop) (S X : Finset ℕ) (junk : List RT) (core : List AR)
    (hcore : ∀ r ∈ core, AR.All P r) (hroot : P S [⟨X, junk⟩])
    (hmerge : ∀ k ∈ core, k.S = S → P k.S k.chain → P S (⟨X, junk⟩ :: k.chain)) : AR.All P (mkNode S X junk core) := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, AR.all_run]
    exact ⟨hroot, by simp⟩
  · simp only [mkNode]
    have hk := hcore k (by simp)
    obtain ⟨S', c, ks⟩ := k
    by_cases h : S' = S
    · subst h
      have := hmerge (.run S' c ks) (by simp) rfl hk.here
      simp only [AR.S, AR.chain, AR.kids, if_true, AR.all_run] at this ⊢
      exact ⟨this, fun k' hk' => hk.kid hk'⟩
    · have : (AR.run S' c ks).S ≠ S := h
      simp only [this, if_false, AR.all_run]
      exact ⟨hroot, by simpa using hk⟩
  · simp only [mkNode, AR.all_run]
    refine ⟨hroot, fun r hr => ?_⟩
    have hr' : r ∈ k :: k2 :: t := by
      unfold sortAR at hr
      exact (List.mergeSort_perm _ _).mem_iff.1 hr
    exact hcore r hr'

theorem analyze_all (B : Finset ℕ) : ∀ t : RT,
    AR.All (fun S c => c ≠ [] ∧ ∀ n ∈ c, n.bag ∩ B = S ∧ n.bag ∈ t.bags) (analyze B t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [analyze_node, analyzeNode_eq]
    have hcore : ∀ r ∈ ((ks.map (fun k => (k, analyze B k))).filter
        (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)))).map Prod.snd,
        AR.All (fun S c => c ≠ [] ∧ ∀ n ∈ c, n.bag ∩ B = S ∧ n.bag ∈ (RT.node X ks).bags) r := by
      intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      obtain ⟨hp1, -⟩ := List.mem_filter.1 hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp1
      refine AR.All.mono ?_ _ (ih k hk)
      intro S c ⟨hne, hn⟩
      refine ⟨hne, fun n hn' => ⟨(hn n hn').1, ?_⟩⟩
      exact (RT.bags_node X ks).2 (Or.inr ⟨k, hk, (hn n hn').2⟩)
    apply mkNode_all _ _ _ _ _ hcore
    · refine ⟨by simp, fun n hn => ?_⟩
      simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨rfl, (RT.bags_node X ks).2 (Or.inl rfl)⟩
    · intro k hk hkS ⟨hne, hn⟩
      refine ⟨by simp, fun n hn' => ?_⟩
      rcases List.mem_cons.1 hn' with rfl | hn'
      · exact ⟨rfl, (RT.bags_node X ks).2 (Or.inl rfl)⟩
      · obtain ⟨h1, h2⟩ := (hcore k hk).here
        obtain ⟨h1', h2'⟩ := h2 n hn'
        exact ⟨by rw [h1', hkS], h2'⟩

/-! ## the join of one analysis -/

theorem zadd_map {α : Type} (l : List α) (g1 g2 : α → ℕ) :
    zadd (l.map g1) (l.map g2) = l.map (fun x => g1 x + g2 x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [zadd] at ih ⊢

theorem joinKids_charF (kmax : ℕ) (f1 f2 f3 : Finset ℕ → ℕ) : ∀ ks : List AR,
    (∀ k ∈ ks, ∃ c ∈ joinC kmax (AR.charF f1 k) (AR.charF f2 k), DomC c (AR.charF f3 k)) →
    ∃ kk ∈ joinKids kmax (ks.map (AR.charF f1)) (ks.map (AR.charF f2)), DomCL kk (ks.map (AR.charF f3)) := by
  intro ks
  induction ks with
  | nil => intro _; exact ⟨[], by simp [joinKids], trivial⟩
  | cons k ks ih =>
    intro h
    obtain ⟨c, hc, hdc⟩ := h k (by simp)
    obtain ⟨kk, hkk, hdk⟩ := ih (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    refine ⟨c :: kk, ?_, hdc, hdk⟩
    simp only [List.map_cons, joinKids, List.mem_flatMap, List.mem_map]
    exact ⟨c, hc, kk, hkk, rfl⟩

theorem joinC_charF (kmax : ℕ) (f1 f2 f3 : Finset ℕ → ℕ) : ∀ r : AR,
    AR.All (fun S c => c ≠ [] ∧ ∀ n ∈ c, f3 n.bag + S.card = f1 n.bag + f2 n.bag ∧ S.card ≤ f1 n.bag ∧
      f3 n.bag ≤ kmax) r →
    ∃ c ∈ joinC kmax (AR.charF f1 r) (AR.charF f2 r), DomC c (AR.charF f3 r) := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    intro h
    obtain ⟨⟨hne, hn⟩, hks⟩ := (AR.all_run _ S c ks).1 h
    obtain ⟨kk, hkk, hdk⟩ := joinKids_charF kmax f1 f2 f3 ks (fun k hk => ih k hk (hks k hk))
    have hzip : zadd (c.map (fun n => f1 n.bag)) (c.map (fun n => f2 n.bag)) =
        c.map (fun n => f1 n.bag + f2 n.bag) := zadd_map c _ _
    have he3 : (zadd (c.map (fun n => f1 n.bag)) (c.map (fun n => f2 n.bag))).map (· - S.card) =
        c.map (fun n => f3 n.bag) := by
      rw [hzip, List.map_map]
      apply List.map_congr_left
      intro n hn'
      have := (hn n hn').1
      simp only [Function.comp]
      omega
    obtain ⟨d, hd, hdom⟩ := join_seq (s := S.card) (kmax := kmax) (e1 := c.map (fun n => f1 n.bag))
      (e2 := c.map (fun n => f2 n.bag)) (by simp) (by simpa using hne)
      (by intro x hx; obtain ⟨n, hn', rfl⟩ := List.mem_map.1 hx; exact (hn n hn').2.1)
      (by
        rw [he3]
        intro x hx
        obtain ⟨n, hn', rfl⟩ := List.mem_map.1 hx
        exact (hn n hn').2.2)
    rw [he3] at hdom
    refine ⟨node S d kk, ?_, ?_⟩
    · rw [AR.charF_run, AR.charF_run]
      unfold joinC
      rw [if_pos ⟨rfl, by simp⟩]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨kk, hkk, d, hd, rfl⟩
    · rw [AR.charF_run]
      exact ⟨rfl, hdom, hdk⟩

/-! ## `char_join_dom` -/

theorem NT.bag_subset_under : ∀ t : NT, t.bag ⊆ t.under := by
  intro t
  induction t with
  | leaf => simp [NT.bag, NT.under]
  | intro v c ih =>
    intro x hx
    simp only [NT.bag, Finset.mem_insert] at hx
    simp only [NT.under, Finset.mem_insert]
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (ih hx)
  | forget v c ih =>
    intro x hx
    exact ih (Finset.mem_of_mem_erase hx)
  | join a b iha ihb =>
    intro x hx
    simp only [NT.bag] at hx
    simp only [NT.under, Finset.mem_union]
    exact Or.inl (iha hx)

theorem card_split (X Ua Ub B : Finset ℕ) (hX : X ⊆ Ua ∪ Ub) (hB : Ua ∩ Ub = B) :
    X.card + (X ∩ B).card = (X ∩ Ua).card + (X ∩ Ub).card := by
  have e1 : X ∩ Ua ∪ X ∩ Ub = X := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases Finset.mem_union.1 (hX hx) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have e2 : X ∩ Ua ∩ (X ∩ Ub) = X ∩ B := by
    rw [← hB]
    ext x
    simp only [Finset.mem_inter]
    tauto
  have := Finset.card_union_add_card_inter (X ∩ Ua) (X ∩ Ub)
  rw [e1, e2] at this
  exact this

/-- **Join** (exact layer + Lemma 3.14). -/
theorem char_join_dom {adj : Adj} {a b : NT} {k : ℕ} {t : RT} (hg : (NT.join a b).Good adj)
    (h : PTD adj (.join a b) k t) :
    ∃ c ∈ CT.joinC (k + 1) ((t.restrict a.under).char a.bag) ((t.restrict b.under).char a.bag),
      DomC c (t.char a.bag) := by
  have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
  obtain ⟨hab, hsub, -, -, -⟩ := hg'
  have hBa : a.bag ⊆ a.under := NT.bag_subset_under a
  have hBb : a.bag ⊆ b.under := hab ▸ NT.bag_subset_under b
  have hUab : a.under ∩ b.under = a.bag := Finset.Subset.antisymm hsub (Finset.subset_inter hBa hBb)
  have c1 : (t.restrict a.under).char a.bag = (analyze a.bag t).charF (fun X => (X ∩ a.under).card) := by
    unfold RT.char; rw [RT.prof_restrict hBa, norm_profF]
  have c2 : (t.restrict b.under).char a.bag = (analyze a.bag t).charF (fun X => (X ∩ b.under).card) := by
    unfold RT.char; rw [RT.prof_restrict hBb, norm_profF]
  rw [c1, c2, char_eq_charF]
  apply joinC_charF (k + 1) _ _ _ (analyze a.bag t)
  refine AR.All.mono ?_ _ (analyze_all a.bag t)
  intro S c ⟨hne, hn⟩
  refine ⟨hne, fun n hn' => ?_⟩
  obtain ⟨hl, hbag⟩ := hn n hn'
  have hX : n.bag ⊆ a.under ∪ b.under := by
    intro x hx
    have : x ∈ t.verts := (RT.mem_verts_iff t x).2 ⟨n.bag, hbag, hx⟩
    rw [h.1.verts_eq] at this
    simpa [NT.under] using this
  have hcs := card_split n.bag a.under b.under a.bag hX hUab
  refine ⟨?_, ?_, h.2 n.bag hbag⟩
  · rw [← hl]; omega
  · rw [← hl]
    exact Finset.card_le_card (Finset.inter_subset_inter_left hBa)

/-! ## `joinC_mono` -/

theorem CT.DomCL.length_eq : ∀ {a b : List CT}, DomCL a b → a.length = b.length
  | [], [], _ => rfl
  | k :: ks, k' :: ks', h => by simp [CT.DomCL.length_eq h.2]

/-- Lemma 3.13 for the run sequences of the join. -/
theorem joinSeq_mono {y y' z z' : List ℕ} {s kmax : ℕ} (hy : Dom y y') (hz : Dom z z')
    {d' : List ℕ}
    (hd' : d' ∈ (((ringTypList y' z').map (fun d => d.map (· - s))).dedup.filter (fun d => d.all (· ≤ kmax)))) :
    ∃ d ∈ (((ringTypList y z).map (fun d => d.map (· - s))).dedup.filter (fun d => d.all (· ≤ kmax))),
      Dom d d' := by
  rw [List.mem_filter, List.mem_dedup, List.mem_map] at hd'
  obtain ⟨⟨e', he', rfl⟩, hall⟩ := hd'
  have he'' := mem_ringTypList.1 he'
  have hy'ne : y' ≠ [] := by
    rintro rfl; simp [ringTyp] at he''
  obtain ⟨e0, ⟨u, v, hu, hv, hl, rfl⟩, rfl⟩ := (mem_ringTyp hy'ne).1 he''
  have h1 : Dom y u := hy.trans (domEquiv_of_ext hu).2
  have h2 : Dom z v := hz.trans (domEquiv_of_ext hv).2
  obtain ⟨y₀, hy₀, hdom⟩ := RingSum.dom_of_dom hl h1 h2
  have hyne : y ≠ [] := hy.ne_nil_left hy'ne
  have hd0 : typical y₀ ∈ ringTyp y z := (mem_ringTyp hyne).2 ⟨y₀, hy₀, rfl⟩
  have hdom' : Dom (typical y₀) (typical (zadd u v)) := dom_typical_iff.1 hdom
  refine ⟨(typical y₀).map (· - s), ?_, hdom'.map_mono (fun x y h => Nat.sub_le_sub_right h s)⟩
  rw [List.mem_filter, List.mem_dedup, List.mem_map]
  refine ⟨⟨typical y₀, mem_ringTypList.2 hd0, rfl⟩, ?_⟩
  rw [List.all_eq_true] at hall ⊢
  intro x hx
  obtain ⟨z0, hz0, rfl⟩ := List.mem_map.1 hx
  obtain ⟨w, hw, hzw⟩ := hdom'.exists_le hz0
  have := hall (w - s) (List.mem_map.2 ⟨w, hw, rfl⟩)
  simp only [decide_eq_true_eq] at this ⊢
  omega

mutual
theorem joinC_mono_aux_rec (kmax : ℕ) : ∀ (a a' b b' : CT), DomC a a' → DomC b b' →
    ∀ c' ∈ joinC kmax a' b', ∃ c ∈ joinC kmax a b, DomC c c'
  | node S y ks, node S' y' ks', node T z kt, node T' z' kt', ha, hb, c', hc => by
    obtain ⟨rfl, hy, hks⟩ := ha
    obtain ⟨rfl, hz, hkt⟩ := hb
    by_cases hcond : S = T ∧ ks'.length = kt'.length
    · unfold joinC at hc
      rw [if_pos hcond] at hc
      simp only [List.mem_flatMap, List.mem_map] at hc
      obtain ⟨kk', hkk', d', hd', rfl⟩ := hc
      obtain ⟨kk, hkk, hdkk⟩ := joinKids_mono_aux_rec kmax ks ks' kt kt' hks hkt kk' hkk'
      obtain ⟨d, hd, hdom⟩ := joinSeq_mono hy hz hd'
      refine ⟨node S d kk, ?_, rfl, hdom, hdkk⟩
      unfold joinC
      rw [if_pos ⟨hcond.1, by rw [hks.length_eq, hkt.length_eq]; exact hcond.2⟩]
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨kk, hkk, d, hd, rfl⟩
    · unfold joinC at hc
      rw [if_neg hcond] at hc
      simp at hc
theorem joinKids_mono_aux_rec (kmax : ℕ) : ∀ (ks ks' kt kt' : List CT), DomCL ks ks' → DomCL kt kt' →
    ∀ kk' ∈ joinKids kmax ks' kt', ∃ kk ∈ joinKids kmax ks kt, DomCL kk kk'
  | [], [], [], [], _, _, kk', h => by
    simp only [joinKids, List.mem_singleton] at h
    subst h
    exact ⟨[], by simp [joinKids], trivial⟩
  | k :: ks, k' :: ks', l :: kt, l' :: kt', ha, hb, kk', h => by
    simp only [joinKids, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c', hc', kk'', hkk'', rfl⟩ := h
    obtain ⟨c, hc, hdc⟩ := joinC_mono_aux_rec kmax k k' l l' ha.1 hb.1 c' hc'
    obtain ⟨kk, hkk, hdk⟩ := joinKids_mono_aux_rec kmax ks ks' kt kt' ha.2 hb.2 kk'' hkk''
    refine ⟨c :: kk, ?_, hdc, hdk⟩
    simp only [joinKids, List.mem_flatMap, List.mem_map]
    exact ⟨c, hc, kk, hkk, rfl⟩
  | [], [], _ :: _, _ :: _, _, hb, _, h => by simp [joinKids] at h
  | [], [], [], _ :: _, _, hb, _, h => by exact absurd hb (by simp [DomCL])
  | [], [], _ :: _, [], _, hb, _, h => by exact absurd hb (by simp [DomCL])
  | [], _ :: _, _, _, ha, _, _, _ => by exact absurd ha (by simp [DomCL])
  | _ :: _, [], _, _, ha, _, _, _ => by exact absurd ha (by simp [DomCL])
  | _ :: _, _ :: _, [], _ :: _, _, hb, _, _ => by exact absurd hb (by simp [DomCL])
  | _ :: _, _ :: _, _ :: _, [], _, hb, _, _ => by exact absurd hb (by simp [DomCL])
  | _ :: _, _ :: _, [], [], _, _, _, h => by simp [joinKids] at h
end

theorem joinC_mono_aux_pair : (type_of% @joinC_mono_aux_rec) ∧ (type_of% @joinKids_mono_aux_rec) :=
  ⟨@joinC_mono_aux_rec, @joinKids_mono_aux_rec⟩

theorem joinC_mono_aux : type_of% @joinC_mono_aux_rec := joinC_mono_aux_pair.1

/-- Lemma 3.13 lifted to characteristics. -/
theorem joinC_mono (kmax : ℕ) {a a' b b' : CT} (ha : DomC a a') (hb : DomC b b') :
    ∀ c' ∈ CT.joinC kmax a' b', ∃ c ∈ CT.joinC kmax a b, DomC c c' :=
  joinC_mono_aux kmax a a' b b' ha hb

end Lax117284Proofs.Treewidth.Chars
