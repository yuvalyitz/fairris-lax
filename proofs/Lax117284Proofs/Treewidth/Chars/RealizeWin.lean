import Lax117284Proofs.Treewidth.Chars.RealizeRegion
import Lax117284Proofs.Treewidth.Chars.IntroPlansMem

/-!
# The region step `processRun` realises `winPlans` (work package C5, part 7)

Definitions of the run-level invariants (`RunOk`, `PRC`, `KC`) and the plan-level lemmas.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- A canonical analysed run, disjoint from the fresh vertex. -/
structure RunOk (v : ℕ) (B : Finset ℕ) (x : AR) : Prop where
  canon : Canon B x
  free : v ∉ (AR.toRT x).verts

theorem runOk_run {v : ℕ} {B S : Finset ℕ} {ns : List CNode} {ks : List AR} (h : RunOk v B (.run S ns ks)) :
    ns ≠ [] ∧ (∀ n0 ∈ ns, n0.bag ∩ B = S ∧ v ∉ n0.bag ∧ ∀ J ∈ n0.junk, Jk B S J ∧ v ∉ J.verts) ∧
    (∀ k ∈ ks, RunOk v B k) ∧ (ks = [] → ns.length = 1) ∧ (∀ k ∈ ks, prunedB S k = false) ∧ S ⊆ B ∧
    (∀ k ∈ ks, v ∉ (AR.toRT k).verts) := by
  obtain ⟨hc, hf⟩ := h
  rw [canon_run] at hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  rw [AR.toRT_run, mem_verts_chainToRT] at hf
  push_neg at hf
  obtain ⟨hf1, hf2, hf3⟩ := hf
  have hkf : ∀ k ∈ ks, v ∉ (AR.toRT k).verts := fun k hk => hf3 _ (List.mem_map.2 ⟨k, hk, rfl⟩)
  refine ⟨h1, fun n0 hn0 => ⟨(h2 n0 hn0).1, hf1 n0 hn0, fun J hJ => ⟨(h2 n0 hn0).2 J hJ, hf2 n0 hn0 J hJ⟩⟩,
    fun k hk => ⟨h7 k hk, hkf k hk⟩, h6, h3, ?_, hkf⟩
  obtain ⟨n0, hn0⟩ := List.exists_mem_of_ne_nil ns h1
  rw [← (h2 n0 hn0).1]; exact Finset.inter_subset_right

theorem verts_charF_sub {B : Finset ℕ} : ∀ x : AR, Canon B x → CT.verts (AR.charF Finset.card x) ⊆ B := by
  intro x
  induction x using AR.ind with
  | _ S c ks ih =>
    intro h
    rw [canon_run] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [AR.charF_run, CT.verts_node]
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨n0, hn0⟩ := List.exists_mem_of_ne_nil c h1
      have := (h2 n0 hn0).1
      rw [← this] at hy
      exact (Finset.mem_inter.1 hy).2
    · obtain ⟨k, hk, hyk⟩ := (CT.mem_vertsL).1 hy
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk
      exact ih k0 hk0 (h7 k0 hk0) hyk

theorem nested_ins {v : ℕ} {B : Finset ℕ} (hv : v ∉ B) (p : CT) (σ : Finset ℕ) (hb : CT.verts p ⊆ B)
    (h : Nested (insert v σ) p) : Nested σ p := by
  cases p with
  | node S y ks =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, h2⟩
    intro x hx
    have := h1 hx
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hb (by simp [CT.verts_node, hx])) hv
    · exact h3

/-! ## kid choices -/

theorem kidChoices_forall2 (v : ℕ) : ∀ (ks : List CT) (combo : List (Option WPlan × CT × Finset ℕ)),
    combo ∈ kidChoices v ks ↔
      List.Forall₂ (fun k o => (o.1 = none ∧ o.2.1 = k ∧ o.2.2 = ∅) ∨
        (∃ wp, o.1 = some wp ∧ (wp, o.2.1, o.2.2) ∈ winPlans v 0 k)) ks combo := by
  intro ks
  induction ks with
  | nil =>
    intro combo
    simp only [kidChoices, List.mem_singleton]
    constructor
    · rintro rfl; exact List.Forall₂.nil
    · intro h; cases h; rfl
  | cons k ks ih =>
    intro combo
    simp only [kidChoices, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨o, ho, combo', hc', rfl⟩
      refine List.Forall₂.cons ?_ ((ih combo').1 hc')
      rcases List.mem_cons.1 ho with rfl | ho
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
        exact Or.inr ⟨p.1, rfl, hp⟩
    · intro h
      cases h with
      | cons hk hrest =>
        rename_i o combo'
        refine ⟨o, ?_, combo', (ih combo').2 hrest, rfl⟩
        rcases hk with ⟨h1, h2, h3⟩ | ⟨wp, h1, h2⟩
        · apply List.mem_cons.2; left
          obtain ⟨o1, o2, o3⟩ := o
          simp only at h1 h2 h3
          subst h1; subst h2; subst h3; rfl
        · apply List.mem_cons_of_mem
          obtain ⟨o1, o2, o3⟩ := o
          simp only at h1 h2
          subst h1
          exact List.mem_map.2 ⟨(wp, o2, o3), h2, rfl⟩


/-! ## small lemmas -/

theorem dom_maxOf_le {a b : List ℕ} (h : Dom a b) : maxOf a ≤ maxOf b := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  have key : ∀ (a' b' : List ℕ), LeSeq a' b' → ∀ x ∈ a', x ≤ maxOf b' := by
    intro a' b' hle
    induction hle with
    | nil => intro x hx; simp at hx
    | @cons x y l1 l2 hxy _ ih =>
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hxy.trans (le_maxOf (List.mem_cons_self))
      · exact (ih z hz).trans (by rw [maxOf_cons]; exact le_max_right _ _)
  have h1 : maxOf a ≤ maxOf a' := maxOf_le fun x hx => le_maxOf ((ha.mem).2 hx)
  have h2 : maxOf b' ≤ maxOf b := maxOf_le fun x hx => le_maxOf ((hb.mem).1 hx)
  refine h1.trans ((maxOf_le fun x hx => key a' b' hle x hx).trans h2)

theorem csz_map_av {v : ℕ} {M : List CNode} (h : ∀ n ∈ M, v ∉ n.bag) : csz (M.map (av v)) = (csz M).map (· + 1) := by
  unfold csz
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro n hn
  simp [av_bag, Finset.card_insert_of_notMem (h n hn)]

theorem mem_csz {ns : List CNode} {n : CNode} (h : n ∈ ns) : n.bag.card ∈ csz ns :=
  List.mem_map.2 ⟨n, h, rfl⟩

/-! ## the invariant of a processed run -/

/-- What `processRun` achieves on a run: topology, new vertex, coverage, characteristic, width. -/
structure PRC (v : ℕ) (B : Finset ℕ) (x x' : AR) (rep : CT) (cov : Finset ℕ) (hasPre : Bool) : Prop where
  ti : TI v (AR.toRT x) (AR.toRT x')
  tcv : ∀ p, tc v (AR.toRT x') p = if hasPre = false ∧ p = true then 0 else 1
  vin : v ∈ (AR.toRT x').verts
  cov : ∀ u ∈ cov, ∃ Y ∈ (AR.toRT x').bags, v ∈ Y ∧ u ∈ Y
  chr : ∃ Q, norm (RT.prof (insert v B) (AR.toRT x')) = norm Q ∧ DomC Q rep
  wid : ∀ Y ∈ (AR.toRT x').bags, v ∈ Y → Y.card ≤ maxEntry (norm rep)
  vrep : v ∈ CT.verts rep
  nest : hasPre = false → ∀ σ, ¬ Nested σ (AR.charF Finset.card x) → ¬ Nested (insert v σ) rep

/-- The same for a kid of a region run (processed or not). -/
structure KC (v : ℕ) (B : Finset ℕ) (k k' : AR) (rep : CT) (cov : Finset ℕ) : Prop where
  ti : TI v (AR.toRT k) (AR.toRT k')
  tcv : tc v (AR.toRT k') true = 0
  cov : ∀ u ∈ cov, ∃ Y ∈ (AR.toRT k').bags, v ∈ Y ∧ u ∈ Y
  chr : ∃ Q, norm (RT.prof (insert v B) (AR.toRT k')) = norm Q ∧ DomC Q rep
  wid : ∀ Y ∈ (AR.toRT k').bags, v ∈ Y → Y.card ≤ maxEntry (norm rep)
  nest : ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) rep

theorem PRC.kc {v : ℕ} {B : Finset ℕ} {x x' : AR} {rep : CT} {cov : Finset ℕ} (h : PRC v B x x' rep cov false) :
    KC v B x x' rep cov :=
  ⟨h.ti, by simpa using h.tcv true, h.cov, h.chr, h.wid, h.nest rfl⟩

theorem kc_unchanged {v : ℕ} {B : Finset ℕ} {k : AR} (hv : v ∉ B) (hk : RunOk v B k) :
    KC v B k k (AR.charF Finset.card k) ∅ := by
  have hn := norm_prof_kid hk.canon hk.free
  refine ⟨TI.refl v _, tc_zero_of_notin v _ true hk.free, by simp, ⟨AR.charF Finset.card k, ?_, DomC.refl _⟩,
    ?_, ?_⟩
  · rw [hn]
    have : norm (AR.charF Finset.card k) = AR.charF Finset.card k := by
      rw [← hn, norm_idem]
    rw [this]
  · intro Y hY hvY
    exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hY, hvY⟩) hk.free
  · intro σ hσ hN
    exact hσ (nested_ins hv _ σ (verts_charF_sub k hk.canon) hN)


theorem addV_map (v s : ℕ) (e : Option ℕ) (ns : List CNode) :
    ∃ g : ℕ → CNode → CNode, (∀ i n, (∀ u, u ≠ v → (u ∈ (g i n).bag ↔ u ∈ n.bag)) ∧ (g i n).junk = n.junk) ∧
      addV v s e ns = ns.mapIdx g := by
  refine ⟨fun i n => if decide (s ≤ i) && e.elim true (fun e => decide (i ≤ e)) then ⟨insert v n.bag, n.junk⟩ else n,
    ?_, rfl⟩
  intro i n
  dsimp only
  split_ifs
  · refine ⟨fun u hu => ?_, rfl⟩
    simp [Finset.mem_insert, hu]
  · exact ⟨fun u _ => Iff.rfl, rfl⟩

end Lax117284Proofs.Treewidth.Chars
