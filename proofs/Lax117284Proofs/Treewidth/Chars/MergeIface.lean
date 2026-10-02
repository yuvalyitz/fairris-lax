import Lax117284Proofs.Treewidth.Chars.MergeConn

/-!
# The interface of a merged run (C3)

`merge_interface`: if `mergeAR A A' c = some M` for two canonical analyses `A`, `A'` of tree decompositions of graphs on
`Ua`, `Ub` with `Ua ∩ Ub = B` and `c` a join option of their characteristics, then `M.toRT` is connected, has the
union of the vertex sets and root bags, and contains (a superset of) every bag of `A.toRT` and `A'.toRT`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## vertices and bags of a chain -/

theorem verts_chainToRT_cons (a : CNode) (r : List CNode) (K : List RT) (x : ℕ) :
    x ∈ (AR.chainToRT (a :: r) K).verts ↔
      x ∈ a.bag ∨ (∃ J ∈ a.junk, x ∈ J.verts) ∨ x ∈ (AR.chainToRT r K).verts := by
  cases r with
  | nil =>
    rw [AR.chainToRT, RT.verts_node, AR.chainToRT, RT.verts_node]
    simp only [List.mem_append, Finset.notMem_empty, false_or]
    constructor
    · rintro (h | ⟨k, hk | hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, hk, hx⟩)
      · exact Or.inr (Or.inr ⟨k, hk, hx⟩)
    · rintro (h | ⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl hk, hx⟩
      · exact Or.inr ⟨k, Or.inr hk, hx⟩
  | cons b r =>
    rw [AR.chainToRT, RT.verts_node]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨k, hk | rfl, hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, hk, hx⟩)
      · exact Or.inr (Or.inr hx)
    · rintro (h | ⟨k, hk, hx⟩ | hx)
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl hk, hx⟩
      · exact Or.inr ⟨_, Or.inr rfl, hx⟩

theorem mem_verts_chainToRT (K : List RT) : ∀ (n : List CNode) (x : ℕ),
    x ∈ (AR.chainToRT n K).verts ↔ (∃ y ∈ n, x ∈ y.bag) ∨ (∃ y ∈ n, ∃ J ∈ y.junk, x ∈ J.verts) ∨
      ∃ K' ∈ K, x ∈ K'.verts := by
  intro n
  induction n with
  | nil => intro x; simp [AR.chainToRT, RT.verts_node]
  | cons a r ih =>
    intro x
    rw [verts_chainToRT_cons, ih x]
    constructor
    · rintro (h | ⟨J, hJ, hx⟩ | ⟨y, hy, hxy⟩ | ⟨y, hy, hx⟩ | h)
      · exact Or.inl ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, J, hJ, hx⟩)
      · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
      · obtain ⟨J, hJ, hxJ⟩ := hx
        exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, J, hJ, hxJ⟩)
      · exact Or.inr (Or.inr h)
    · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | h)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl hxy
        · exact Or.inr (Or.inr (Or.inl ⟨y, hy, hxy⟩))
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inr (Or.inl ⟨J, hJ, hxJ⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hy, J, hJ, hxJ⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## `B`-vertices of the profile and the analysis -/

theorem verts_prof (B : Finset ℕ) : ∀ t : RT, CT.verts (RT.prof B t) = t.verts ∩ B := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [RT.prof_node]
    ext x
    simp only [CT.mem_verts, Finset.mem_inter, RT.verts_node, List.mem_map]
    constructor
    · rintro (h | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · exact ⟨Or.inl h.1, h.2⟩
      · rw [ih k hk, Finset.mem_inter] at hx
        exact ⟨Or.inr ⟨k, hk, hx.1⟩, hx.2⟩
    · rintro ⟨h | ⟨k, hk, hx⟩, hxB⟩
      · exact Or.inl ⟨h, hxB⟩
      · exact Or.inr ⟨_, ⟨k, hk, rfl⟩, by rw [ih k hk]; exact Finset.mem_inter.2 ⟨hx, hxB⟩⟩

theorem verts_char (B : Finset ℕ) (t : RT) : CT.verts (t.char B) = t.verts ∩ B := by
  unfold RT.char; rw [verts_norm, verts_prof]

/-- Junk contains no `B`-vertex outside the label. -/
theorem verts_inter_B_of_Jk {B S : Finset ℕ} {J : RT} (h : Jk B S J) : J.verts ∩ B ⊆ S := by
  intro v hv
  have h1 : v ∈ CT.verts (J.char B) := by rw [verts_char]; exact hv
  rw [char_eq_charF] at h1
  obtain ⟨hleaf, hsub⟩ := h
  cases hA : analyze B J with
  | run S' c ks =>
    rw [hA] at hleaf hsub h1
    simp only [AR.isLeaf, AR.kids, List.isEmpty_iff] at hleaf
    subst hleaf
    simp only [AR.charF_run, List.map_nil, CT.mem_verts] at h1
    simp only [AR.S] at hsub
    rcases h1 with h1 | ⟨k, hk, _⟩
    · exact hsub h1
    · simp at hk

/-- `B`-vertices of a canonical analysis are those of its labels. -/
theorem toRT_verts_inter_B (B : Finset ℕ) (f : Finset ℕ → ℕ) : ∀ r : AR, Canon B r →
    ∀ x, (x ∈ (AR.toRT r).verts ∧ x ∈ B) ↔ x ∈ CT.verts (AR.charF f r) := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    intro h x
    rw [canon_run] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [AR.toRT_run, mem_verts_chainToRT, AR.charF_run, CT.mem_verts]
    simp only [List.mem_map]
    have hS : ∀ y ∈ c, y.bag ∩ B = S := fun y hy => (h2 y hy).1
    constructor
    · rintro ⟨(⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨K', ⟨k, hk, rfl⟩, hxk⟩), hxB⟩
      · left; rw [← hS y hy]; exact Finset.mem_inter.2 ⟨hxy, hxB⟩
      · left
        exact verts_inter_B_of_Jk ((h2 y hy).2 J hJ) (Finset.mem_inter.2 ⟨hxJ, hxB⟩)
      · right
        exact ⟨_, ⟨k, hk, rfl⟩, (ih k hk (h7 k hk) x).1 ⟨hxk, hxB⟩⟩
    · rintro (hx | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil c h1
        have : x ∈ y.bag ∩ B := by rw [hS y hy]; exact hx
        exact ⟨Or.inl ⟨y, hy, (Finset.mem_inter.1 this).1⟩, (Finset.mem_inter.1 this).2⟩
      · obtain ⟨hv, hB⟩ := (ih k hk (h7 k hk) x).2 hx
        exact ⟨Or.inr (Or.inr ⟨_, ⟨k, hk, rfl⟩, hv⟩), hB⟩

/-! ## the joined runs have the same labels -/

mutual
theorem joinC_verts_aux (kmax : ℕ) : ∀ (a b c : CT), c ∈ joinC kmax a b → CT.verts a = CT.verts b
  | node S y ks, node S' y' ks', c, h => by
    obtain ⟨rfl, hl, d, kk, rfl, hkk, hd⟩ := joinC_inv h
    have := joinKids_verts_aux kmax ks ks' kk hkk
    simp only [CT.verts, this]
theorem joinKids_verts_aux (kmax : ℕ) : ∀ (ks ks' : List CT) (kk : List CT),
    kk ∈ joinKids kmax ks ks' → CT.vertsL ks = CT.vertsL ks'
  | [], [], _, _ => rfl
  | k :: ks, k' :: ks', kk, h => by
    simp only [joinKids, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, kk', hkk', rfl⟩ := h
    have h1 := joinC_verts_aux kmax k k' c hc
    have h2 := joinKids_verts_aux kmax ks ks' kk' hkk'
    simp only [CT.vertsL, h1, h2]
  | [], _ :: _, _, h => by simp [joinKids] at h
  | _ :: _, [], _, h => by simp [joinKids] at h
end

/-! ## the package of an analysis of a tree decomposition -/

mutual
/-- `r` is connected, lives on `U`, and so do its kids. -/
def Pkg (U : Finset ℕ) : AR → Prop
  | .run S c ks => (AR.toRT (.run S c ks)).Conn ∧ (AR.toRT (.run S c ks)).verts ⊆ U ∧ PkgL U ks
def PkgL (U : Finset ℕ) : List AR → Prop
  | [] => True
  | k :: ks => Pkg U k ∧ PkgL U ks
end

theorem pkgL_iff (U : Finset ℕ) : ∀ ks : List AR, PkgL U ks ↔ ∀ k ∈ ks, Pkg U k
  | [] => by simp [PkgL]
  | k :: ks => by simp [PkgL, pkgL_iff U ks]

theorem pkg_run (U : Finset ℕ) (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    Pkg U (.run S c ks) ↔ (AR.toRT (.run S c ks)).Conn ∧ (AR.toRT (.run S c ks)).verts ⊆ U ∧ ∀ k ∈ ks, Pkg U k := by
  simp only [Pkg, pkgL_iff]

theorem pkg_kids {U : Finset ℕ} {r : AR} (h : Pkg U r) : ∀ k ∈ r.kids, Pkg U k := by
  cases r with
  | run S c ks => exact ((pkg_run U S c ks).1 h).2.2

theorem pkg_conn {U : Finset ℕ} {r : AR} (h : Pkg U r) : (AR.toRT r).Conn := by
  cases r with
  | run S c ks => exact ((pkg_run U S c ks).1 h).1

theorem pkg_verts {U : Finset ℕ} {r : AR} (h : Pkg U r) : (AR.toRT r).verts ⊆ U := by
  cases r with
  | run S c ks => exact ((pkg_run U S c ks).1 h).2.1

theorem pkg_intro {U : Finset ℕ} {r : AR} (h1 : (AR.toRT r).Conn) (h2 : (AR.toRT r).verts ⊆ U)
    (h3 : ∀ k ∈ r.kids, Pkg U k) : Pkg U r := by
  cases r with
  | run S c ks => exact (pkg_run U S c ks).2 ⟨h1, h2, h3⟩

theorem mkNode_kids_pkg {U : Finset ℕ} (S X : Finset ℕ) (junk : List RT) (core : List AR)
    (hcore : ∀ r ∈ core, Pkg U r) : ∀ k ∈ (mkNode S X junk core).kids, Pkg U k := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp [mkNode, AR.kids]
  · simp only [mkNode]
    have hk := hcore k (by simp)
    obtain ⟨S', c, ks⟩ := k
    by_cases h : S' = S
    · subst h
      simp only [AR.S, if_true, AR.kids]
      exact fun k' hk' => pkg_kids hk k' hk'
    · have : (AR.run S' c ks).S ≠ S := h
      simp only [this, if_false, AR.kids]
      intro k' hk'
      simp only [List.mem_singleton] at hk'
      subst hk'; exact hk
  · simp only [mkNode, AR.kids]
    intro k' hk'
    exact hcore k' (mem_sortAR.1 hk')

theorem pkg_analyze (B U : Finset ℕ) : ∀ t : RT, t.Conn → t.verts ⊆ U → Pkg U (analyze B t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc hv
    rw [analyze_node_shape]
    have hcore : ∀ r ∈ ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)), Pkg U r := by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      have hk1 := (List.mem_filter.1 hk).1
      obtain ⟨h1, -, -⟩ := (RT.conn_node_iff X ks).1 hc
      refine ih k hk1 (h1 k hk1) (fun x hx => hv ?_)
      rw [RT.verts_node]; exact Or.inr ⟨k, hk1, hx⟩
    have hkids := mkNode_kids_pkg (U := U) (X ∩ B) X (ks.filter (fun k => prunedB (X ∩ B) (analyze B k))) _ hcore
    refine pkg_intro ?_ ?_ hkids
    · have := conn_toRT_analyze B (.node X ks) hc
      rwa [analyze_node_shape] at this
    · have := verts_toRT_analyze B (.node X ks)
      rw [analyze_node_shape] at this
      rw [this]; exact hv

/-! ## the merged run -/

theorem chainToRT_facts (K : List RT) : ∀ n : List CNode, (∀ y ∈ n, y.bag ⊆ (AR.chainToRT n K).verts) ∧
    (∀ y ∈ n, ∀ J ∈ y.junk, J.verts ⊆ (AR.chainToRT n K).verts) ∧ (∀ K' ∈ K, K'.verts ⊆ (AR.chainToRT n K).verts) := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    rw [mem_verts_chainToRT]; exact Or.inl ⟨y, hy, hx⟩
  · intro y hy J hJ x hx
    rw [mem_verts_chainToRT]; exact Or.inr (Or.inl ⟨y, hy, J, hJ, hx⟩)
  · intro K' hK' x hx
    rw [mem_verts_chainToRT]; exact Or.inr (Or.inr ⟨K', hK', hx⟩)

theorem kids_iface {B Ua Ub : Finset ℕ} (kmax : ℕ) :
    ∀ (kA kB : List AR) (kk : List CT) (kM : List AR),
    (∀ a ∈ kA, ∀ (b : AR) (t : CT) (m : AR), Canon B a → Canon B b → Pkg Ua a → Pkg Ub b →
      t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b) → mergeAR a b t = some m →
      MergeI (AR.toRT m) (AR.toRT a) (AR.toRT b)) →
    (∀ a ∈ kA, Canon B a ∧ Pkg Ua a) → (∀ b ∈ kB, Canon B b ∧ Pkg Ub b) →
    F4 (fun a b t m => mergeAR a b t = some m) kA kB kk kM →
    F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB kk →
    F3 (fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B)
      (kM.map AR.toRT) (kA.map AR.toRT) (kB.map AR.toRT) := by
  intro kA
  induction kA with
  | nil =>
    intro kB kk kM _ _ _ h4 h3
    cases kB <;> cases kk <;> cases kM <;> simp_all [F4, F3]
  | cons a kA ih =>
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
          refine ⟨⟨?_, ?_⟩, ih kB kk kM (fun a' ha' => hih a' (List.mem_cons_of_mem _ ha'))
            (fun a' ha' => hca a' (List.mem_cons_of_mem _ ha'))
            (fun b' hb' => hcb b' (List.mem_cons_of_mem _ hb')) h4.2 h3.2⟩
          · exact hih a (by simp) b t m (hca a (by simp)).1 (hcb b (by simp)).1 (hca a (by simp)).2
              (hcb b (by simp)).2 h3.1 h4.1
          · have e1 := toRT_verts_inter_B B Finset.card a (hca a (by simp)).1
            have e2 := toRT_verts_inter_B B Finset.card b (hcb b (by simp)).1
            have e3 := joinC_verts_aux kmax _ _ t h3.1
            ext x
            simp only [Finset.mem_inter]
            rw [e1 x, e2 x, e3]

theorem bags_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) (X : Finset ℕ)
    (hX : X ∈ (AR.chainToRT n K).bags) :
    X = cbag n 0 ∨ (∃ J ∈ cjunk n 0, X ∈ J.bags) ∨ ∃ K' ∈ succL n K 0, X ∈ K'.bags := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := chainToRT_drop n K hlen
  rw [List.drop_zero] at this
  rw [this, RT.bags_node] at hX
  rcases hX with hX | ⟨J, hJ, hX⟩
  · exact Or.inl hX
  · rcases List.mem_append.1 hJ with hJ | hJ
    · exact Or.inr (Or.inl ⟨J, hJ, hX⟩)
    · exact Or.inr (Or.inr ⟨J, hJ, hX⟩)

theorem verts_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) (x : ℕ) :
    x ∈ (AR.chainToRT n K).verts ↔ x ∈ PA n K 0 true := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := verts_drop n K hlen x
  rw [List.drop_zero] at this
  rw [this, mem_PA, mem_vertsL, mem_vertsL]
  simp

theorem rootBag_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) :
    (AR.chainToRT n K).rootBag = cbag n 0 := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := rootBag_chainToRT_drop n K hlen
  rwa [List.drop_zero] at this

/-- **The interface of a merged run.** -/
theorem merge_interface {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) (kmax : ℕ) :
    ∀ (A A' : AR) (c : CT) (M : AR), Canon B A → Canon B A' → Pkg Ua A → Pkg Ub A' →
      c ∈ joinC kmax (AR.charF Finset.card A) (AR.charF Finset.card A') →
      mergeAR A A' c = some M → MergeI (AR.toRT M) (AR.toRT A) (AR.toRT A') := by
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
    have hkids := kids_iface (B := B) (Ua := Ua) (Ub := Ub) kmax kA kB tk kM
      (fun a ha b t m hca hcb hpa hpb ht hm => ih a ha b t m hca hcb hpa hpb ht hm)
      (fun a ha => ⟨hA7 a ha, hpA1.2.2 a ha⟩) (fun b hb => ⟨hB7 b hb, hpB1.2.2 b hb⟩) hF4 hF3
    rw [AR.toRT_run] at hpA1 hpB1
    have hfA := chainToRT_facts (kA.map AR.toRT) nA
    have hfB := chainToRT_facts (kB.map AR.toRT) nB
    have ctx : MergeCtx B Ua Ub T nA nB (kA.map AR.toRT) (kB.map AR.toRT) (kM.map AR.toRT) :=
      { hU := hU
        nA_ne := hA1
        nB_ne := hB1
        Abag := fun x hx => ⟨fun v hv => hpA1.2.1 (hfA.1 x hx hv), (hA2 x hx).1⟩
        Bbag := fun x hx => ⟨fun v hv => hpB1.2.1 (hfB.1 x hx hv), (hB2 x hx).1⟩
        Ajunk := fun x hx J hJ => ⟨fun v hv => hpA1.2.1 (hfA.2.1 x hx J hJ hv),
          verts_inter_B_of_Jk ((hA2 x hx).2 J hJ)⟩
        Bjunk := fun x hx J hJ => ⟨fun v hv => hpB1.2.1 (hfB.2.1 x hx J hJ hv),
          verts_inter_B_of_Jk ((hB2 x hx).2 J hJ)⟩
        Akid := fun K hK => fun v hv => hpA1.2.1 (hfA.2.2 K hK hv)
        Bkid := fun K hK => fun v hv => hpB1.2.1 (hfB.2.2 K hK hv)
        Aconn := hpA1.1
        Bconn := hpB1.1
        kids := hkids }
    obtain ⟨hpath1, hpath2, hpath3⟩ := (findPath_spec hQ).1
    have hnA : 0 < nA.length := List.length_pos_iff.2 hA1
    have hnB : 0 < nB.length := List.length_pos_iff.2 hB1
    have hclaim := chain_claim ctx Q 0 0 none (by simpa using hpath1)
      (by simpa using hpath2) hpath3 (by intro p hp; simp at hp) hnA hnB (AR.chainToRT (mergeChain nA nB none Q) (kM.map AR.toRT)) rfl
    obtain ⟨hC, hR, hV, hCA, hCB⟩ := hclaim
    have hrA : (AR.toRT (.run T nA kA)).rootBag = cbag nA 0 := by
      rw [AR.toRT_run]; exact rootBag_chain_zero hA1
    have hrB : (AR.toRT (.run T nB kB)).rootBag = cbag nB 0 := by
      rw [AR.toRT_run]; exact rootBag_chain_zero hB1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [AR.toRT_run]; exact hC
    · rw [AR.toRT_run] at *
      ext x
      rw [Finset.mem_union, hV x]
      rw [AR.toRT_run, verts_chain_zero hA1, AR.toRT_run, verts_chain_zero hB1]
      rfl
    · rw [hrA, hrB, AR.toRT_run]; exact hR
    · intro X hX
      rw [AR.toRT_run] at hX
      have hX' := bags_chain_zero hA1 X hX
      rw [AR.toRT_run]
      exact hCA X (by
        rcases hX' with h | ⟨J, hJ, h⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨rfl, J, hJ, h⟩)
        · exact Or.inr (Or.inr h))
    · intro X hX
      rw [AR.toRT_run] at hX
      have hX' := bags_chain_zero hB1 X hX
      rw [AR.toRT_run]
      exact hCB X (by
        rcases hX' with h | ⟨J, hJ, h⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨rfl, J, hJ, h⟩)
        · exact Or.inr (Or.inr h))

end Lax117284Proofs.Treewidth.Chars
