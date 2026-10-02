import Lax117284Proofs.Treewidth.Chars.Join

/-!
# The analysis and its inverse (C3 infrastructure for `mergeReal_spec`)

* `Jk B S J` — `J` is *junk* below a node of label `S`: its analysis is a leaf run with label `⊆ S`;
* `Canon B M` — the invariants of an analysis `analyze B t` (non-empty chains, labels, junk, unpruned kids, sorted
  kids, a leaf run has a one-node chain);
* `analyze_canon : Canon B (analyze B t)` and `analyze_toRT : Canon B M → analyze B (M.toRT) = M`: reassembling a
  canonical analysis and analysing again gives it back.  Consequently `(analyze B t).toRT.char B = t.char B`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## `toRT` basics -/

theorem AR.toRTL_eq (ks : List AR) : AR.toRTL ks = ks.map AR.toRT := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [AR.toRTL, ih]

theorem AR.toRT_run (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    AR.toRT (.run S c ks) = AR.chainToRT c (ks.map AR.toRT) := by
  simp [AR.toRT, AR.toRTL_eq]

/-! ## sorting -/

theorem sortAR_pairwise (S : Finset ℕ) (l : List AR) :
    (sortAR S l).Pairwise (fun a b => CT.key S a.char ≤ CT.key S b.char) := by
  have := List.pairwise_mergeSort (le := fun a b : AR => decide (CT.key S a.char ≤ CT.key S b.char))
    (by intro a b c h1 h2; simp at *; exact le_trans h1 h2)
    (by intro a b; simp; exact le_total _ _) l
  simpa [sortAR] using this

theorem sortAR_of_pairwise {S : Finset ℕ} {l : List AR}
    (h : l.Pairwise (fun a b => CT.key S a.char ≤ CT.key S b.char)) : sortAR S l = l := by
  unfold sortAR
  exact List.mergeSort_of_pairwise (by simpa using h)

theorem mem_sortAR {S : Finset ℕ} {l : List AR} {r : AR} : r ∈ sortAR S l ↔ r ∈ l :=
  (List.mergeSort_perm _ _).mem_iff

/-! ## canonical analyses -/

/-- `J` is junk below a node with label `S`. -/
def Jk (B S : Finset ℕ) (J : RT) : Prop := (analyze B J).isLeaf = true ∧ (analyze B J).S ⊆ S

/-- A kid `k` of a run with label `S` is *pruned* (junk) iff this Boolean holds. -/
def prunedB (S : Finset ℕ) (k : AR) : Bool := k.isLeaf && decide (k.S ⊆ S)

mutual
/-- The invariants of an analysis. -/
def Canon (B : Finset ℕ) : AR → Prop
  | .run S c ks =>
    c ≠ [] ∧ (∀ n ∈ c, n.bag ∩ B = S ∧ ∀ J ∈ n.junk, Jk B S J) ∧
    (∀ k ∈ ks, prunedB S k = false) ∧ (∀ k, ks = [k] → k.S ≠ S) ∧
    ks.Pairwise (fun a b => CT.key S a.char ≤ CT.key S b.char) ∧ (ks = [] → c.length = 1) ∧ CanonL B ks
def CanonL (B : Finset ℕ) : List AR → Prop
  | [] => True
  | k :: ks => Canon B k ∧ CanonL B ks
end

theorem canonL_iff (B : Finset ℕ) : ∀ ks : List AR, CanonL B ks ↔ ∀ k ∈ ks, Canon B k
  | [] => by simp [CanonL]
  | k :: ks => by simp [CanonL, canonL_iff B ks]

theorem canon_run (B S : Finset ℕ) (c : List CNode) (ks : List AR) :
    Canon B (.run S c ks) ↔
      c ≠ [] ∧ (∀ n ∈ c, n.bag ∩ B = S ∧ ∀ J ∈ n.junk, Jk B S J) ∧
      (∀ k ∈ ks, prunedB S k = false) ∧ (∀ k, ks = [k] → k.S ≠ S) ∧
      ks.Pairwise (fun a b => CT.key S a.char ≤ CT.key S b.char) ∧ (ks = [] → c.length = 1) ∧
      ∀ k ∈ ks, Canon B k := by
  simp only [Canon, canonL_iff]

theorem prunedB_false_of_not {S : Finset ℕ} {k : AR} (h : (!(k.isLeaf && decide (k.S ⊆ S))) = true) :
    prunedB S k = false := by
  unfold prunedB
  cases hb : (k.isLeaf && decide (k.S ⊆ S)) <;> simp_all

theorem not_of_prunedB_false {S : Finset ℕ} {k : AR} (h : prunedB S k = false) :
    (!(k.isLeaf && decide (k.S ⊆ S))) = true := by
  unfold prunedB at h; simp [h]

theorem mkNode_canon (B S X : Finset ℕ) (junk : List RT) (core : List AR) (hS : X ∩ B = S)
    (hjunk : ∀ J ∈ junk, Jk B S J) (hcore : ∀ r ∈ core, Canon B r) (hunp : ∀ r ∈ core, prunedB S r = false) :
    Canon B (mkNode S X junk core) := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, canon_run]
    refine ⟨by simp, ?_, by simp, by simp, by simp, by simp, by simp⟩
    intro n hn
    simp only [List.mem_singleton] at hn
    subst hn
    exact ⟨hS, hjunk⟩
  · simp only [mkNode]
    have hk := hcore k (by simp)
    have hu := hunp k (by simp)
    obtain ⟨S', c, ks⟩ := k
    rw [canon_run] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hk
    by_cases h : S' = S
    · subst h
      simp only [AR.S, AR.chain, AR.kids, if_true, canon_run]
      refine ⟨by simp, ?_, h3, h4, h5, ?_, h7⟩
      · intro n hn
        rcases List.mem_cons.1 hn with rfl | hn
        · exact ⟨hS, hjunk⟩
        · exact h2 n hn
      · intro hks
        exfalso
        subst hks
        simp [prunedB, AR.isLeaf, AR.kids, AR.S] at hu
    · have : (AR.run S' c ks).S ≠ S := h
      simp only [this, if_false, canon_run]
      refine ⟨by simp, ?_, ?_, ?_, by simp, by simp, ?_⟩
      · intro n hn
        simp only [List.mem_singleton] at hn
        subst hn
        exact ⟨hS, hjunk⟩
      · intro k' hk'
        simp only [List.mem_singleton] at hk'
        subst hk'; exact hu
      · intro k' hk'
        simp only [List.cons.injEq, and_true] at hk'
        subst hk'; exact h
      · intro k' hk'
        simp only [List.mem_singleton] at hk'
        subst hk'; rw [canon_run]; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · simp only [mkNode, canon_run]
    have hmem : ∀ r, r ∈ sortAR S (k :: k2 :: t) ↔ r ∈ k :: k2 :: t := fun r => mem_sortAR
    refine ⟨by simp, ?_, ?_, ?_, sortAR_pairwise S _, by simp [sortAR, ← List.length_eq_zero_iff, List.length_mergeSort], ?_⟩
    · intro n hn
      simp only [List.mem_singleton] at hn
      subst hn
      exact ⟨hS, hjunk⟩
    · intro r hr; exact hunp r ((hmem r).1 hr)
    · intro k' hk'
      have hl := (List.mergeSort_perm (k :: k2 :: t)
        (fun a b => decide (CT.key S a.char ≤ CT.key S b.char))).length_eq
      have : (sortAR S (k :: k2 :: t)).length = 1 := by rw [hk']; rfl
      unfold sortAR at this
      simp at this hl
    · intro r hr; exact hcore r ((hmem r).1 hr)

theorem analyze_canon (B : Finset ℕ) : ∀ t : RT, Canon B (analyze B t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [analyze_node, analyzeNode_eq]
    apply mkNode_canon _ _ _ _ _ rfl
    · intro J hJ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hJ
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp1
      simpa [Jk, Bool.and_eq_true] using hp2
    · intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      obtain ⟨hp1, -⟩ := List.mem_filter.1 hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp1
      exact ih k hk
    · intro r hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
      exact prunedB_false_of_not hp2

/-! ## the inverse -/

theorem analyze_chainToRT (B S : Finset ℕ) (kids : List AR)
    (hinv : ∀ k ∈ kids, analyze B (AR.toRT k) = k) (hunp : ∀ k ∈ kids, prunedB S k = false)
    (hsingle : ∀ k, kids = [k] → k.S ≠ S)
    (hsort : kids.Pairwise (fun a b => CT.key S a.char ≤ CT.key S b.char)) :
    ∀ c : List CNode, c ≠ [] → (∀ n ∈ c, n.bag ∩ B = S ∧ ∀ J ∈ n.junk, Jk B S J) →
      (2 ≤ c.length → kids ≠ []) →
      analyze B (AR.chainToRT c (kids.map AR.toRT)) = .run S c kids := by
  intro c
  induction c with
  | nil => intro h; exact absurd rfl h
  | cons n r ih =>
    intro _ hc hlen
    obtain ⟨hn1, hn2⟩ := hc n (by simp)
    -- the junk part of the kid list
    have hjunkP : ∀ p ∈ n.junk.map (fun J => (J, analyze B J)), prunedB S p.2 = true := by
      intro p hp
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hp
      obtain ⟨h1, h2⟩ := hn2 J hJ
      simp [prunedB, h1, h2]
    have hkidsP : ∀ p ∈ kids.map (fun k => (AR.toRT k, analyze B (AR.toRT k))), prunedB S p.2 = false := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      simp only [hinv k hk]
      exact hunp k hk
    -- analysis of `node n.bag L` when `L` is `junk ++ tail`
    have key : ∀ tailT : List RT, ∀ tailP : List (RT × AR),
        tailP = tailT.map (fun t => (t, analyze B t)) →
        (∀ p ∈ tailP, prunedB S p.2 = false) →
        analyze B (RT.node n.bag (n.junk ++ tailT)) =
          mkNode S n.bag n.junk (tailP.map Prod.snd) := by
      intro tailT tailP hP hpr
      rw [analyze_node, analyzeNode_eq, List.map_append, ← hP, hn1]
      have e1 : ((n.junk.map (fun J => (J, analyze B J))) ++ tailP).filter
          (fun p => p.2.isLeaf && decide (p.2.S ⊆ S)) = n.junk.map (fun J => (J, analyze B J)) := by
        rw [List.filter_append]
        rw [List.filter_eq_self.2 (by intro p hp; simpa [prunedB] using hjunkP p hp)]
        rw [List.filter_eq_nil_iff.2 (by intro p hp; simpa [prunedB] using hpr p hp)]
        simp
      have e2 : ((n.junk.map (fun J => (J, analyze B J))) ++ tailP).filter
          (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ S))) = tailP := by
        rw [List.filter_append]
        rw [List.filter_eq_nil_iff.2 (by intro p hp; simpa [prunedB] using hjunkP p hp)]
        rw [List.filter_eq_self.2 (by intro p hp; exact not_of_prunedB_false (hpr p hp))]
        simp
      rw [e1, e2]
      have e3 : List.map (Prod.fst ∘ fun J => (J, analyze B J)) n.junk = n.junk := by
        simp [Function.comp_def]
      rw [List.map_map, e3]
    cases r with
    | nil =>
      simp only [AR.chainToRT]
      rw [key (kids.map AR.toRT) (kids.map (fun k => (AR.toRT k, analyze B (AR.toRT k))))
        (by rw [List.map_map]; rfl) hkidsP]
      have : (kids.map (fun k => (AR.toRT k, analyze B (AR.toRT k)))).map Prod.snd = kids := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id kids]
        exact List.map_congr_left (fun k hk => hinv k hk)
      rw [this]
      rcases kids with _ | ⟨k, _ | ⟨k2, t⟩⟩
      · simp [mkNode]
      · simp only [mkNode]
        have := hsingle k rfl
        simp only [this, if_false]
      · simp only [mkNode]
        rw [sortAR_of_pairwise hsort]
    | cons m r' =>
      simp only [AR.chainToRT]
      have hk : kids ≠ [] := hlen (by simp)
      have hsub := ih (by simp) (fun n' hn' => hc n' (List.mem_cons_of_mem _ hn'))
        (fun h => hk)
      have hne : ∀ p ∈ [(AR.chainToRT (m :: r') (kids.map AR.toRT),
          analyze B (AR.chainToRT (m :: r') (kids.map AR.toRT)))], prunedB S p.2 = false := by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        simp only [hsub, prunedB, AR.isLeaf, AR.kids]
        cases kids with
        | nil => exact absurd rfl hk
        | cons k ks => simp
      have := key [AR.chainToRT (m :: r') (kids.map AR.toRT)]
        [(AR.chainToRT (m :: r') (kids.map AR.toRT), analyze B (AR.chainToRT (m :: r') (kids.map AR.toRT)))]
        rfl hne
      rw [this]
      simp only [List.map_cons, List.map_nil, hsub, mkNode, AR.S, AR.chain, AR.kids, if_true]

theorem analyze_toRT (B : Finset ℕ) : ∀ M : AR, Canon B M → analyze B (AR.toRT M) = M := by
  intro M
  induction M using AR.ind with
  | _ S c ks ih =>
    intro h
    rw [canon_run] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [AR.toRT_run]
    apply analyze_chainToRT B S ks (fun k hk => ih k hk (h7 k hk)) h3 h4 h5 c h1 h2
    intro hl hks
    have := h6 hks
    omega

/-- The characteristic of the reassembled analysis is the characteristic (`B' = B`). -/
theorem char_toRT_analyze (B : Finset ℕ) (t : RT) : (AR.toRT (analyze B t)).char B = t.char B := by
  rw [char_eq_charF, analyze_toRT B _ (analyze_canon B t), ← char_eq_charF]

/-! ## the reassembled analysis is the same tree up to the order of the kids -/

theorem analyze_node_shape (B X : Finset ℕ) (ks : List RT) :
    analyze B (.node X ks) =
      mkNode (X ∩ B) X (ks.filter (fun k => prunedB (X ∩ B) (analyze B k)))
        ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)) := by
  rw [analyze_node, analyzeNode_eq]
  congr 1
  · rw [List.filter_map, List.map_map]
    have : (fun p : RT × AR => p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)) ∘ (fun k => (k, analyze B k)) =
        fun k => prunedB (X ∩ B) (analyze B k) := by funext k; rfl
    rw [this]
    conv_rhs => rw [← List.map_id (ks.filter _)]
    exact List.map_congr_left (fun _ _ => rfl)
  · rw [List.filter_map, List.map_map]
    have : (fun p : RT × AR => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ B))) ∘ (fun k => (k, analyze B k)) =
        fun k => !prunedB (X ∩ B) (analyze B k) := by funext k; rfl
    rw [this]
    exact List.map_congr_left (fun _ _ => rfl)

theorem toRT_mkNode (S X : Finset ℕ) (junk : List RT) (core : List AR) (hne : ∀ k ∈ core, k.chain ≠ []) :
    ∃ core' : List AR, core'.Perm core ∧ AR.toRT (mkNode S X junk core) = RT.node X (junk ++ core'.map AR.toRT) := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · exact ⟨[], List.Perm.refl _, by simp [mkNode, AR.toRT_run, AR.chainToRT]⟩
  · refine ⟨[k], List.Perm.refl _, ?_⟩
    have hk := hne k (by simp)
    obtain ⟨S', c, ks⟩ := k
    by_cases h : S' = S
    · subst h
      obtain ⟨c0, r, rfl⟩ := List.exists_cons_of_ne_nil hk
      simp [mkNode, AR.toRT_run, AR.chainToRT, AR.S, AR.chain, AR.kids]
    · have : (AR.run S' c ks).S ≠ S := h
      simp [mkNode, this, AR.toRT_run, AR.chainToRT]
  · refine ⟨sortAR S (k :: k2 :: t), (List.mergeSort_perm _ _), ?_⟩
    simp [mkNode, AR.toRT_run, AR.chainToRT]

theorem chain_ne_nil_analyze (B : Finset ℕ) (t : RT) : (analyze B t).chain ≠ [] := by
  have := (analyze_all B t).here
  exact this.1

theorem toRT_analyze_shape (B X : Finset ℕ) (ks : List RT) :
    ∃ core' : List AR, core'.Perm ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)) ∧
      AR.toRT (analyze B (.node X ks)) =
        RT.node X (ks.filter (fun k => prunedB (X ∩ B) (analyze B k)) ++ core'.map AR.toRT) := by
  rw [analyze_node_shape]
  apply toRT_mkNode
  intro r hr
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hr
  exact chain_ne_nil_analyze B k

theorem rootBag_toRT_analyze (B : Finset ℕ) (t : RT) : (AR.toRT (analyze B t)).rootBag = t.rootBag := by
  cases t with
  | node X ks =>
    obtain ⟨core', _, e⟩ := toRT_analyze_shape B X ks
    rw [e]; rfl

/-- membership of a kid of the reassembled analysis -/
theorem mem_toRT_analyze_kids (B X : Finset ℕ) (ks : List RT) {core' : List AR}
    (hp : core'.Perm ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B))) {K : RT} :
    K ∈ ks.filter (fun k => prunedB (X ∩ B) (analyze B k)) ++ core'.map AR.toRT ↔
      ∃ k ∈ ks, K = (if prunedB (X ∩ B) (analyze B k) = true then k else AR.toRT (analyze B k)) := by
  rw [List.mem_append, List.mem_filter, List.mem_map]
  constructor
  · rintro (⟨hk, hp1⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨K, hk, by simp [hp1]⟩
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((hp.mem_iff).1 hr)
      obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
      refine ⟨k, hk1, ?_⟩
      have : prunedB (X ∩ B) (analyze B k) = false := prunedB_false_of_not hk2
      simp [this]
  · rintro ⟨k, hk, rfl⟩
    by_cases h : prunedB (X ∩ B) (analyze B k) = true
    · left; exact ⟨by simpa [h] using hk, by simp [h]⟩
    · right
      have h' : prunedB (X ∩ B) (analyze B k) = false := by simpa using h
      refine ⟨analyze B k, (hp.mem_iff).2 (List.mem_map.2 ⟨k, List.mem_filter.2 ⟨hk, by simp [h']⟩, rfl⟩), ?_⟩
      simp [h']

theorem verts_toRT_analyze (B : Finset ℕ) : ∀ t : RT, (AR.toRT (analyze B t)).verts = t.verts := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    obtain ⟨core', hp, e⟩ := toRT_analyze_shape B X ks
    rw [e]
    ext x
    rw [RT.verts_node, RT.verts_node]
    apply or_congr_right
    constructor
    · rintro ⟨K, hK, hx⟩
      obtain ⟨k, hk, rfl⟩ := (mem_toRT_analyze_kids B X ks hp).1 hK
      refine ⟨k, hk, ?_⟩
      by_cases h : prunedB (X ∩ B) (analyze B k) = true
      · simpa [h] using hx
      · simpa [h, ih k hk] using hx
    · rintro ⟨k, hk, hx⟩
      refine ⟨_, (mem_toRT_analyze_kids B X ks hp).2 ⟨k, hk, rfl⟩, ?_⟩
      by_cases h : prunedB (X ∩ B) (analyze B k) = true
      · simpa [h] using hx
      · simpa [h, ih k hk] using hx

theorem mem_bags_toRT_analyze (B : Finset ℕ) : ∀ (t : RT) (Y : Finset ℕ),
    Y ∈ (AR.toRT (analyze B t)).bags ↔ Y ∈ t.bags := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro Y
    obtain ⟨core', hp, e⟩ := toRT_analyze_shape B X ks
    rw [e, RT.bags_node, RT.bags_node]
    apply or_congr_right
    constructor
    · rintro ⟨K, hK, hx⟩
      obtain ⟨k, hk, rfl⟩ := (mem_toRT_analyze_kids B X ks hp).1 hK
      refine ⟨k, hk, ?_⟩
      by_cases h : prunedB (X ∩ B) (analyze B k) = true
      · simpa [h] using hx
      · simpa [h, ih k hk] using hx
    · rintro ⟨k, hk, hx⟩
      refine ⟨_, (mem_toRT_analyze_kids B X ks hp).2 ⟨k, hk, rfl⟩, ?_⟩
      by_cases h : prunedB (X ∩ B) (analyze B k) = true
      · simpa [h] using hx
      · simpa [h, ih k hk] using hx

/-! ### `Conn` is invariant under this rearrangement -/

theorem conn_node_rearr {X : Finset ℕ} {ks L : List RT} (ψ : RT → RT)
    (hv : ∀ k ∈ ks, (ψ k).verts = k.verts) (hr : ∀ k ∈ ks, (ψ k).rootBag = k.rootBag)
    (hc : ∀ k ∈ ks, k.Conn → (ψ k).Conn) (hperm : L.Perm (ks.map ψ)) (h : (RT.node X ks).Conn) :
    (RT.node X L).Conn := by
  obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff X ks).1 h
  rw [RT.conn_node_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((hperm.mem_iff).1 hK)
    exact hc k hk (h1 k hk)
  · intro K hK v hvX hvK
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ((hperm.mem_iff).1 hK)
    rw [hv k hk] at hvK
    rw [hr k hk]
    exact h2 k hk v hvX hvK
  · have hsymm : ∀ {x y : RT}, (∀ v ∈ x.verts, v ∈ y.verts → v ∈ X) → (∀ v ∈ y.verts, v ∈ x.verts → v ∈ X) :=
      fun hxy v hy hx => hxy v hx hy
    rw [List.Perm.pairwise_iff hsymm hperm]
    rw [List.pairwise_map]
    refine (List.Pairwise.and_mem.1 h3).imp ?_
    rintro a b ⟨ha, hb, hab⟩ v hva hvb
    rw [hv a ha] at hva
    rw [hv b hb] at hvb
    exact hab v hva hvb

theorem conn_toRT_analyze (B : Finset ℕ) : ∀ t : RT, t.Conn → (AR.toRT (analyze B t)).Conn := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro h
    obtain ⟨core', hp, e⟩ := toRT_analyze_shape B X ks
    rw [e]
    let ψ : RT → RT := fun k => if prunedB (X ∩ B) (analyze B k) = true then k else AR.toRT (analyze B k)
    have hks := (RT.conn_node_iff X ks).1 h
    apply conn_node_rearr (ks := ks) ψ ?_ ?_ ?_ ?_ h
    · intro k hk
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simp [ψ, hh]
      · simp [ψ, hh, verts_toRT_analyze]
    · intro k hk
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simp [ψ, hh]
      · simp [ψ, hh, rootBag_toRT_analyze]
    · intro k hk hck
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simp [ψ, hh, hck]
      · simp only [ψ, hh]
        exact ih k hk hck
    · -- L ~ ks.map ψ
      have h1 : (ks.map ψ).Perm ((ks.filter (fun k => prunedB (X ∩ B) (analyze B k))).map ψ ++
          (ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map ψ) :=
        (((List.filter_append_perm (fun k => prunedB (X ∩ B) (analyze B k)) ks).map ψ).symm).trans
          (by rw [List.map_append])
      refine List.Perm.trans ?_ h1.symm
      have e1 : (ks.filter (fun k => prunedB (X ∩ B) (analyze B k))).map ψ =
          ks.filter (fun k => prunedB (X ∩ B) (analyze B k)) := by
        conv_rhs => rw [← List.map_id (ks.filter _)]
        apply List.map_congr_left
        intro k hk
        simp [ψ, (List.mem_filter.1 hk).2]
      have e2 : (ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map ψ =
          ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)).map AR.toRT := by
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have : prunedB (X ∩ B) (analyze B k) = false := prunedB_false_of_not (List.mem_filter.1 hk).2
        simp [ψ, this]
      rw [e1, e2]
      exact List.Perm.append_left _ (hp.map AR.toRT)

/-- The reassembled analysis is a tree decomposition of the same graph with the same width. -/
theorem isTD_toRT_analyze {G : SimpleGraph ℕ} {U : Finset ℕ} (B : Finset ℕ) {t : RT} (h : t.IsTD G U) :
    (AR.toRT (analyze B t)).IsTD G U := by
  refine ⟨by rw [verts_toRT_analyze, h.verts_eq], ?_, conn_toRT_analyze B t h.conn⟩
  intro u v huv hu hv
  obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hu hv
  exact ⟨X, (mem_bags_toRT_analyze B t X).2 hX, hxu, hxv⟩

theorem width_toRT_analyze {t : RT} {w : ℕ} (B : Finset ℕ) (h : t.Width w) : (AR.toRT (analyze B t)).Width w :=
  fun X hX => h X ((mem_bags_toRT_analyze B t X).1 hX)

end Lax117284Proofs.Treewidth.Chars
