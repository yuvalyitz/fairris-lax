import Lax117284Proofs.Treewidth.Trees.NiceLemmas
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Logic.Relation
import Lax117284Proofs.Treewidth.Trees.Basic
import Lax117284Proofs.Treewidth.Trees.Bridge1Rt
import Lax117284Proofs.Treewidth.Trees.Bridge1Restrict
import Mathlib.Data.List.GetD
import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Wrap.Nice

/-! ### `Lax117284Proofs.Treewidth.Trees.AddEverywhere` -/

section
/-!
# Adding a vertex to every bag of a nice tree (T2, BP2 part 1)

`NT.addEverywhere v` puts an introduce node above every leaf.  Everything is proved by induction on `NT`,
through the local characterisation of `RT.Conn` (`NT.NConn`).

Statement audit note: BP2 states `bag_addEverywhere` without hypotheses.  That is false (`t = forget v (intro v leaf)`);
the correct hypotheses are `t.Wf` and `v ∉ t.vs` (`v` occurs nowhere), which is what `addEverywhere_isNiceTD` has.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace NT

lemma not_mem_vs_intro {v u : ℕ} {c : NT} (h : v ∉ vs (intro u c)) : v ∉ vs c ∧ v ≠ u := by
  simp only [vs_intro, Finset.mem_union, not_or, bag_intro, Finset.mem_insert] at h
  tauto

lemma not_mem_vs_forget {v u : ℕ} {c : NT} (h : v ∉ vs (forget u c)) : v ∉ vs c := by
  simp only [vs_forget, Finset.mem_union, not_or] at h
  exact h.2

lemma not_mem_vs_join {v : ℕ} {a b : NT} (h : v ∉ vs (join a b)) : v ∉ vs a ∧ v ∉ vs b := by
  simp only [vs_join, Finset.mem_union, not_or] at h
  exact ⟨h.2.1, h.2.2⟩

/-- The bag of the root after adding `v` everywhere. -/
theorem bag_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) :
    (addEverywhere v t).bag = insert v t.bag := by
  induction t with
  | leaf => simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp [addEverywhere, ih hc hv', Finset.insert_comm u v]
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bag_forget, ih hc hv']
    exact Finset.erase_insert_of_ne this
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp [addEverywhere, ih₁ ha hva]

theorem size_addEverywhere_le (v : ℕ) (t : NT) : (addEverywhere v t).size ≤ 2 * t.size := by
  induction t with
  | leaf => simp [addEverywhere, size]
  | intro u c ih => simp only [addEverywhere, size]; omega
  | forget u c ih => simp only [addEverywhere, size]; omega
  | join a b ih₁ ih₂ => simp only [addEverywhere, size]; omega

theorem wf_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) : (addEverywhere v t).Wf := by
  induction t with
  | leaf => simp [addEverywhere, Wf]
  | intro u c ih =>
    obtain ⟨hu, hc⟩ := hw
    obtain ⟨hv', hne⟩ := not_mem_vs_intro hv
    refine ⟨?_, ih hc hv'⟩
    rw [bag_addEverywhere v c hc hv']
    simp [Ne.symm hne, hu]
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    refine ⟨?_, ih hc hv'⟩
    rw [bag_addEverywhere v c hc hv']
    exact Finset.mem_insert_of_mem hu
  | join a b ih₁ ih₂ =>
    obtain ⟨hab, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    refine ⟨?_, ih₁ ha hva, ih₂ hb hvb⟩
    rw [bag_addEverywhere v a ha hva, bag_addEverywhere v b hb hvb, hab]

theorem vs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) :
    (addEverywhere v t).vs = insert v t.vs := by
  induction t with
  | leaf => simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, vs_intro, bag_intro]
    rw [bag_addEverywhere v c hc hv', ih hc hv']
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  | forget u c ih =>
    obtain ⟨-, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    simp only [addEverywhere, vs_forget, bag_forget]
    rw [bag_addEverywhere v c hc hv', ih hc hv']
    ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]; tauto
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, vs_join]
    rw [bag_addEverywhere v a ha hva, ih₁ ha hva, ih₂ hb hvb]
    ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto

/-- Every bag of the new tree is `∅` (a new leaf) or an old bag plus `v`. -/
theorem mem_bs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) {X : Finset ℕ}
    (hX : X ∈ bs (addEverywhere v t)) : X = ∅ ∨ ∃ Y ∈ bs t, X = insert v Y := by
  induction t with
  | leaf =>
    simp only [addEverywhere, bs_intro, bs_leaf, List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · right; exact ⟨∅, by simp, by simp⟩
    · left; rfl
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, bs_intro, List.mem_cons] at hX
    rcases hX with hX | hX
    · right
      refine ⟨(intro u c).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_intro, bag_intro, bag_addEverywhere v c hc hv']; simp [Finset.insert_comm u v]
    · rcases ih hc hv' hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have hne : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bs_forget, List.mem_cons] at hX
    rcases hX with hX | hX
    · right
      refine ⟨(forget u c).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_forget, bag_forget, bag_addEverywhere v c hc hv']; simp [Finset.erase_insert_of_ne hne]
    · rcases ih hc hv' hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, bs_join, List.mem_cons, List.mem_append] at hX
    rcases hX with hX | hX | hX
    · right
      refine ⟨(join a b).bag, bag_mem_bs _, ?_⟩
      rw [hX, bag_join, bag_addEverywhere v a ha hva]
    · rcases ih₁ ha hva hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩
    · rcases ih₂ hb hvb hX with h | ⟨Y, hY, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨Y, by simp [hY], rfl⟩

/-- Every old bag plus `v` is a bag of the new tree. -/
theorem insert_mem_bs_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) {Y : Finset ℕ}
    (hY : Y ∈ bs t) : insert v Y ∈ bs (addEverywhere v t) := by
  induction t with
  | leaf =>
    simp only [bs_leaf, List.mem_singleton] at hY
    subst hY
    simp [addEverywhere]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    simp only [addEverywhere, bs_intro, List.mem_cons] at hY ⊢
    rcases hY with hY | hY
    · left; rw [hY, bag_intro, bag_intro, bag_addEverywhere v c hc hv']; simp [Finset.insert_comm u v]
    · exact Or.inr (ih hc hv' hY)
  | forget u c ih =>
    obtain ⟨hu, hc⟩ := hw
    have hv' := not_mem_vs_forget hv
    have hne : v ≠ u := fun h => hv' (h ▸ bag_subset_vs c hu)
    simp only [addEverywhere, bs_forget, List.mem_cons] at hY ⊢
    rcases hY with hY | hY
    · left; rw [hY, bag_forget, bag_forget, bag_addEverywhere v c hc hv']; simp [Finset.erase_insert_of_ne hne]
    · exact Or.inr (ih hc hv' hY)
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    simp only [addEverywhere, bs_join, List.mem_cons, List.mem_append] at hY ⊢
    rcases hY with hY | hY | hY
    · left; rw [hY, bag_addEverywhere v a ha hva]
    · exact Or.inr (Or.inl (ih₁ ha hva hY))
    · exact Or.inr (Or.inr (ih₂ hb hvb hY))

theorem nconn_addEverywhere (v : ℕ) (t : NT) (hw : t.Wf) (hv : v ∉ t.vs) (hn : NConn t) :
    NConn (addEverywhere v t) := by
  induction t with
  | leaf => simp [addEverywhere, NConn]
  | intro u c ih =>
    obtain ⟨-, hc⟩ := hw
    obtain ⟨hv', -⟩ := not_mem_vs_intro hv
    obtain ⟨hu, hnc⟩ := hn
    refine ⟨?_, ih hc hv' hnc⟩
    rw [vs_addEverywhere v c hc hv']
    have hne : u ≠ v := by
      intro h; subst h
      exact hv (by simp)
    simp [hne, hu]
  | forget u c ih =>
    obtain ⟨-, hc⟩ := hw
    exact ih hc (not_mem_vs_forget hv) hn
  | join a b ih₁ ih₂ =>
    obtain ⟨-, ha, hb⟩ := hw
    obtain ⟨hva, hvb⟩ := not_mem_vs_join hv
    obtain ⟨hj, hna, hnb⟩ := hn
    refine ⟨?_, ih₁ ha hva hna, ih₂ hb hvb hnb⟩
    intro x hxa hxb
    rw [vs_addEverywhere v a ha hva] at hxa
    rw [vs_addEverywhere v b hb hvb] at hxb
    rw [bag_addEverywhere v a ha hva]
    rcases Finset.mem_insert.1 hxa with rfl | hxa
    · simp
    · rcases Finset.mem_insert.1 hxb with rfl | hxb
      · simp
      · exact Finset.mem_insert_of_mem (hj x hxa hxb)

/-- **The wrapper's step.**  Adding `v` (with arbitrary neighbours among the existing vertices `U`) to every bag of a
nice decomposition of `G[U]` of width `≤ k` gives a nice decomposition of `G[U ∪ {v}]` of width `≤ k + 1`. -/
theorem addEverywhere_isNiceTD {G : SimpleGraph ℕ} {U : Finset ℕ} {t : NT} {k v : ℕ}
    (h : t.IsNiceTD G U k) (hv : v ∉ U) :
    (addEverywhere v t).IsNiceTD G (insert v U) (k + 1) := by
  obtain ⟨hw, hTD, hwd⟩ := h
  have hU : t.vs = U := hTD.verts_eq
  have hv' : v ∉ t.vs := hU ▸ hv
  refine ⟨wf_addEverywhere v t hw hv', ⟨?_, ?_, ?_⟩, ?_⟩
  · show (addEverywhere v t).vs = _
    rw [vs_addEverywhere v t hw hv', hU]
  · intro a b hab ha hb
    have inU : ∀ x, x ∈ U → ∃ X ∈ bs t, x ∈ X := fun x hx => (mem_vs_iff t x).1 (hU ▸ hx)
    rcases Finset.mem_insert.1 ha with h1 | ha'
    · rcases Finset.mem_insert.1 hb with h2 | hb'
      · exact absurd (h1.trans h2.symm ▸ hab) (G.loopless.irrefl _)
      · obtain ⟨X, hX, hbX⟩ := inU b hb'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, h1 ▸ Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem hbX⟩
    · rcases Finset.mem_insert.1 hb with h2 | hb'
      · obtain ⟨X, hX, haX⟩ := inU a ha'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, Finset.mem_insert_of_mem haX,
          h2 ▸ Finset.mem_insert_self _ _⟩
      · obtain ⟨X, hX, haX, hbX⟩ := hTD.edges a b hab ha' hb'
        exact ⟨_, insert_mem_bs_addEverywhere v t hw hv' hX, Finset.mem_insert_of_mem haX,
          Finset.mem_insert_of_mem hbX⟩
  · exact (conn_toRT_iff (wf_addEverywhere v t hw hv')).2
      (nconn_addEverywhere v t hw hv' ((conn_toRT_iff hw).1 hTD.conn))
  · intro X hX
    rcases mem_bs_addEverywhere v t hw hv' hX with rfl | ⟨Y, hY, rfl⟩
    · simp
    · have hYU : Y ⊆ U := hU ▸ vs_subset_of_mem_bs hY
      have hvY : v ∉ Y := fun h => hv (hYU h)
      rw [Finset.card_insert_of_notMem hvY]
      have := hwd Y hY
      omega

end NT

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge1Root` -/

section
/-!
# Rooted trees given by a parent function

Generic graph theory for `Trees/Bridge1`: a tree is the same thing as a finite type with a root, a parent function
`par` (with `par r = r`) and a depth `d` strictly decreasing along `par`.  This file proves

* `Rooted.isTree`     : the graph `rgraph par` of such data is a tree;
* `exists_rooting`    : every finite tree, rooted at any `r`, is of this form;
* `Desc`, `exit`      : the descendant relation and the "exit lemma" for connected vertex sets.
-/

namespace Lax117284Proofs.Treewidth.Trees.RootedTree

open SimpleGraph

variable {V : Type}

/-- Root, parent function, depth. -/
structure Rooted (r : V) (par : V → V) (d : V → ℕ) : Prop where
  par_root : par r = r
  d_par : ∀ x, x ≠ r → d (par x) + 1 = d x

/-- The graph of a parent function. -/
def rgraph (par : V → V) : SimpleGraph V := SimpleGraph.fromRel (fun a b => par a = b)

theorem rgraph_adj {par : V → V} {a b : V} :
    (rgraph par).Adj a b ↔ a ≠ b ∧ (par a = b ∨ par b = a) := by
  simp [rgraph]

namespace Rooted

variable {r : V} {par : V → V} {d : V → ℕ}

theorem ne_par (h : Rooted r par d) {x : V} (hx : x ≠ r) : par x ≠ x := by
  intro e
  have := h.d_par x hx
  rw [e] at this
  omega

theorem adj_par (h : Rooted r par d) {x : V} (hx : x ≠ r) : (rgraph par).Adj x (par x) :=
  rgraph_adj.2 ⟨(h.ne_par hx).symm, Or.inl rfl⟩

/-- Every vertex is connected to the root. -/
theorem reachable_root (h : Rooted r par d) (x : V) : (rgraph par).Reachable x r := by
  induction hn : d x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hx : x = r
    · subst hx; exact Reachable.refl _
    · have hlt := h.d_par x hx
      exact (h.adj_par hx).reachable.trans (ih (d (par x)) (by omega) (par x) rfl)

theorem connected (h : Rooted r par d) : (rgraph par).Connected := by
  have : Nonempty V := ⟨r⟩
  exact ⟨fun a b => (h.reachable_root a).trans (h.reachable_root b).symm⟩

theorem isTree [Finite V] (h : Rooted r par d) : (rgraph par).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨h.connected, ?_⟩
  let f : {x : V // x ≠ r} → (rgraph par).edgeSet := fun x => ⟨s(x.1, par x.1), h.adj_par x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ e
      have e' : s(x, par x) = s(y, par y) := congrArg Subtype.val e
      rw [Sym2.eq_iff] at e'
      rcases e' with ⟨e1, _⟩ | ⟨e1, e2⟩
      · exact Subtype.ext e1
      · exfalso
        have h1 := h.d_par x hx
        have h2 := h.d_par y hy
        rw [e2] at h1
        rw [← e1] at h2
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h a b =>
        rw [mem_edgeSet, rgraph_adj] at he
        rcases he with ⟨hab, e1 | e1⟩
        · have ha : a ≠ r := by
            rintro rfl
            rw [h.par_root] at e1
            exact hab e1
          exact ⟨⟨a, ha⟩, Subtype.ext (by simp [f, e1])⟩
        · have hb : b ≠ r := by
            rintro rfl
            rw [h.par_root] at e1
            exact hab e1.symm
          exact ⟨⟨b, hb⟩, Subtype.ext (by simp [f, e1, Sym2.eq_swap])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  have := Fintype.ofFinite V
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨r⟩
  have h2 := Fintype.card_subtype_compl (fun x : V => x = r)
  rw [Fintype.card_subtype_eq] at h2
  have h3 : Fintype.card { x // x ≠ r } = Fintype.card { x // ¬x = r } := by
    congr
  omega

end Rooted

/-- Every finite tree can be rooted at any vertex: it is the graph of a parent function. -/
theorem exists_rooting [Fintype V] {T : SimpleGraph V} (hT : T.IsTree) (r : V) :
    ∃ (par : V → V) (d : V → ℕ), Rooted r par d ∧ T = rgraph par := by
  classical
  let d : V → ℕ := fun x => T.dist r x
  have hex : ∀ x, x ≠ r → ∃ w, T.Adj x w ∧ d w + 1 = d x := by
    intro x hx
    obtain ⟨p, hp⟩ := (hT.connected x r).exists_walk_length_eq_dist
    cases p with
    | nil => exact absurd rfl hx
    | @cons _ w _ hadj q =>
      refine ⟨w, hadj, ?_⟩
      have h1 : T.dist w r ≤ q.length := dist_le q
      have h2 := hT.dist_eq_dist_add_one_of_adj r hadj
      simp only [Walk.length_cons] at hp
      have h3 : T.dist r x = T.dist x r := dist_comm
      have h4 : T.dist r w = T.dist w r := dist_comm
      show T.dist r w + 1 = T.dist r x
      omega
  have huniq : ∀ x w1 w2, T.Adj x w1 → T.Adj x w2 → d w1 + 1 = d x → d w2 + 1 = d x → w1 = w2 := by
    intro x w1 w2 h1 h2 e1 e2
    obtain ⟨p, hp, hpl⟩ := hT.connected.exists_path_of_dist r x
    have key : ∀ w, T.Adj x w → d w + 1 = d x → w = p.penultimate := by
      intro w hw ew
      obtain ⟨q, hq, hql⟩ := hT.connected.exists_path_of_dist r w
      have hxq : x ∉ q.support := by
        intro hx
        have h5 := Walk.length_takeUntil_le_length q hx
        have h6 := dist_le (q.takeUntil x hx)
        have : d x = T.dist r x := rfl
        have : d w = T.dist r w := rfl
        omega
      have hwp : w ∈ p.support :=
        hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hw hxq
      exact hT.isAcyclic.eq_penultimate_of_adj_end hp hw hwp
    rw [key w1 h1 e1, key w2 h2 e2]
  let par : V → V := fun x => if h : x = r then r else Classical.choose (hex x h)
  have hpar : ∀ x (h : x ≠ r), T.Adj x (par x) ∧ d (par x) + 1 = d x := by
    intro x h
    simp only [par, dif_neg h]
    exact Classical.choose_spec (hex x h)
  have hpr : par r = r := by simp [par]
  have hroot : Rooted r par d :=
    ⟨hpr, fun x h => (hpar x h).2⟩
  refine ⟨par, d, hroot, ?_⟩
  ext a b
  rw [rgraph_adj]
  constructor
  · intro hab
    refine ⟨hab.ne, ?_⟩
    rcases hT.dist_eq_dist_add_one_of_adj r hab with h | h
    · left
      have ha : a ≠ r := by
        rintro rfl
        simp at h
      exact huniq a _ _ (hpar a ha).1 hab (hpar a ha).2 h.symm
    · right
      have hb : b ≠ r := by
        rintro rfl
        simp at h
      exact huniq b _ _ (hpar b hb).1 hab.symm (hpar b hb).2 h.symm
  · rintro ⟨hne, h | h⟩
    · have ha : a ≠ r := by
        rintro rfl
        rw [hpr] at h
        exact hne h
      rw [← h]
      exact (hpar a ha).1
    · have hb : b ≠ r := by
        rintro rfl
        rw [hpr] at h
        exact hne h.symm
      rw [← h]
      exact (hpar b hb).1.symm

/-! ### descendants -/

/-- `b` is a child of `a`. -/
def Child (r : V) (par : V → V) (a b : V) : Prop := b ≠ r ∧ par b = a

/-- `Desc r par s u`: `u` is a descendant of `s` (possibly `s` itself). -/
def Desc (r : V) (par : V → V) (s u : V) : Prop := Relation.ReflTransGen (Child r par) s u

namespace Desc

variable {r : V} {par : V → V} {d : V → ℕ}

theorem refl (s : V) : Desc r par s s := Relation.ReflTransGen.refl

theorem trans {a b c : V} (h1 : Desc r par a b) (h2 : Desc r par b c) : Desc r par a c :=
  Relation.ReflTransGen.trans h1 h2

theorem child {a b : V} (h : b ≠ r) (e : par b = a) : Desc r par a b :=
  Relation.ReflTransGen.single ⟨h, e⟩

theorem tail {a b c : V} (h1 : Desc r par a b) (h : c ≠ r) (e : par c = b) : Desc r par a c :=
  Relation.ReflTransGen.tail h1 ⟨h, e⟩

theorem d_le (hR : Rooted r par d) {s u : V} (h : Desc r par s u) : d s ≤ d u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih =>
    have := hR.d_par _ hc.1
    rw [hc.2] at this
    omega

theorem d_lt (hR : Rooted r par d) {s u : V} (h : Desc r par s u) (hne : s ≠ u) : d s < d u := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨c, h1, hc⟩
  · exact absurd e.symm hne
  · have := hR.d_par _ hc.1
    rw [hc.2] at this
    have := d_le hR h1
    omega

/-- Every vertex descends from the root. -/
theorem root (hR : Rooted r par d) (u : V) : Desc r par r u := by
  induction hn : d u using Nat.strong_induction_on generalizing u with
  | _ n ih =>
    by_cases hu : u = r
    · subst hu; exact refl _
    · have := hR.d_par u hu
      exact (ih (d (par u)) (by omega) (par u) rfl).tail hu rfl

/-- A proper descendant descends from a child. -/
theorem exists_kid {v u : V} (h : Desc r par v u) (hne : v ≠ u) :
    ∃ w, w ≠ r ∧ par w = v ∧ Desc r par w u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd rfl hne
  | head hc hrest _ => exact ⟨_, hc.1, hc.2, hrest⟩

theorem eq_of_par_not {s a : V} (h : Desc r par s a) (hn : ¬ Desc r par s (par a)) : a = s := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨c, h1, hc⟩
  · exact e
  · exact absurd (hc.2 ▸ h1) hn

/-- The ancestors of a vertex form a chain. -/
theorem comparable {a b u : V} (ha : Desc r par a u) (hb : Desc r par b u) :
    Desc r par a b ∨ Desc r par b a := by
  induction ha with
  | refl => exact Or.inr hb
  | tail ha' hc ih =>
    rcases Relation.ReflTransGen.cases_tail hb with e | ⟨c', hb', hc'⟩
    · subst e
      exact Or.inl (Relation.ReflTransGen.tail ha' hc)
    · have : c' = _ := hc'.2.symm.trans hc.2
      subst this
      exact ih hb'

end Desc

/-! ### exit lemma and top-connectedness -/

/-- **Exit lemma.**  If a connected set `S` (connected in the induced graph) contains a point `a` of a
child-closed set `A` and a point `b` outside `A`, then it contains a vertex of `A` whose parent lies in `S` but
outside `A`. -/
theorem exit {r : V} {par : V → V} {d : V → ℕ} (hR : Rooted r par d) {S A : Set V}
    (hA : ∀ c, c ≠ r → par c ∈ A → c ∈ A) {a b : V} (ha : a ∈ S) (haA : a ∈ A) (hb : b ∈ S)
    (hbA : b ∉ A) (hr : ((rgraph par).induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ x, x ∈ S ∧ x ∈ A ∧ x ≠ r ∧ par x ∈ S ∧ par x ∉ A := by
  by_contra hne
  push Not at hne
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ y : S, Relation.ReflTransGen ((rgraph par).induce S).Adj ⟨a, ha⟩ y → y.1 ∈ A := by
    intro y hy
    induction hy with
    | refl => exact haA
    | @tail y1 y2 _ hadj ih =>
      have hadj' : (rgraph par).Adj y1.1 y2.1 := hadj
      rcases rgraph_adj.1 hadj' with ⟨hne', e | e⟩
      · have hy1r : y1.1 ≠ r := by
          intro hh
          rw [hh, hR.par_root] at e
          exact hne' (by rw [hh, e])
        have h5 := hne y1.1 y1.2 ih hy1r (by rw [e]; exact y2.2)
        rw [e] at h5
        exact h5
      · have hzr : y2.1 ≠ r := by
          intro hh
          rw [hh, hR.par_root] at e
          exact hne' (by rw [hh, ← e])
        exact hA y2.1 hzr (by rw [e]; exact ih)
  exact hbA (key _ hr)

/-- A set with a top element `t` (every other member has its parent in the set) is connected. -/
theorem reachable_of_top {r : V} {par : V → V} {d : V → ℕ} (hR : Rooted r par d) {S : Set V} {t : V}
    (ht : t ∈ S) (htop : ∀ s ∈ S, s ≠ t → s ≠ r ∧ par s ∈ S) (a : V) (ha : a ∈ S) :
    ((rgraph par).induce S).Reachable ⟨a, ha⟩ ⟨t, ht⟩ := by
  induction hn : d a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases hat : a = t
    · subst hat; exact SimpleGraph.Reachable.refl _
    · obtain ⟨har, hpa⟩ := htop a ha hat
      have hlt := hR.d_par a har
      have hadj : ((rgraph par).induce S).Adj ⟨a, ha⟩ ⟨par a, hpa⟩ := hR.adj_par har
      exact hadj.reachable.trans (ih (d (par a)) (by omega) (par a) hpa rfl)

end Lax117284Proofs.Treewidth.Trees.RootedTree

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge1To` -/

section
/-!
# Bridge 1, direction (→): an abstract tree decomposition folds into an `RT`

A rooted tree given by a parent function (`Rooted`) with bags whose occurrence sets are connected folds into an
`RT` with `Conn`; then the concept's `TreeDecomposition` is rooted (`exists_rooting`) and folded.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Trees.RootedTree Lax228581.Treewidth

section fold

variable {V : Type} [Fintype V] {r : V} {par : V → V} {d : V → ℕ}

/-- Folding: the subtree below `v`. -/
theorem exists_rt_sub (hR : Rooted r par d) (bag : V → Finset ℕ)
    (hconn : ∀ x a b (ha : x ∈ bag a) (hb : x ∈ bag b),
      ((rgraph par).induce {i | x ∈ bag i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∀ v : V, ∃ t : RT, t.rootBag = bag v ∧ t.Conn ∧ (∀ X ∈ t.bags, ∃ u, Desc r par v u ∧ bag u = X) ∧
      (∀ u, Desc r par v u → bag u ∈ t.bags) := by
  classical
  have : Inhabited RT := ⟨.node ∅ []⟩
  intro v
  induction hn : (Finset.univ.filter (Desc r par v)).card using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    have hkid_d : ∀ w, w ≠ r → par w = v → d w = d v + 1 := by
      intro w hw hp
      have := hR.d_par w hw
      rw [hp] at this
      omega
    have ih' : ∀ w, w ≠ r → par w = v → ∃ t : RT, t.rootBag = bag w ∧ t.Conn ∧
        (∀ X ∈ t.bags, ∃ u, Desc r par w u ∧ bag u = X) ∧ (∀ u, Desc r par w u → bag u ∈ t.bags) := by
      intro w hw hp
      refine ih _ ?_ w rfl
      rw [← hn]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨v, by simp [Desc.refl], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hv
        have := Desc.d_le hR hv
        have := hkid_d w hw hp
        omega
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact (Desc.child hw hp).trans hu
    choose! f hf using ih'
    let kids : Finset V := Finset.univ.filter (fun w => w ≠ r ∧ par w = v)
    have hkids : ∀ w, w ∈ kids ↔ w ≠ r ∧ par w = v := by
      intro w; simp [kids]
    refine ⟨.node (bag v) (kids.toList.map f), rfl, ?_, ?_, ?_⟩
    · rw [RT.conn_node_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        exact (hf w hw.1 hw.2).2.1
      · intro k hk x hxv hxk
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        obtain ⟨hw1, hw2⟩ := hw
        obtain ⟨hr1, hc, hb, hb2⟩ := hf w hw1 hw2
        rw [hr1]
        obtain ⟨X, hX, hxX⟩ := (RT.mem_verts_iff _ _).1 hxk
        obtain ⟨u, hu, rfl⟩ := hb X hX
        by_contra hxw
        have hreach := hconn x u v hxX hxv
        obtain ⟨x', hx'S, hx'A, hx'r, hpS, hpA⟩ :=
          exit (S := {i | x ∈ bag i}) (A := {y | Desc r par w y}) hR
            (fun c hc hp => Desc.tail hp hc rfl) hxX hu hxv
            (by
              intro hv
              have := Desc.d_le hR hv
              have := hkid_d w hw1 hw2
              simp only [Set.mem_ofPred_eq] at hv
              omega) hreach
        have := Desc.eq_of_par_not hx'A hpA
        subst this
        exact hxw hx'S
      · rw [List.pairwise_map]
        apply List.Nodup.pairwise_of_forall_ne (Finset.nodup_toList kids)
        intro w1 hw1 w2 hw2 hne x hx1 hx2
        rw [Finset.mem_toList, hkids] at hw1 hw2
        obtain ⟨X1, hX1, hxX1⟩ := (RT.mem_verts_iff _ _).1 hx1
        obtain ⟨X2, hX2, hxX2⟩ := (RT.mem_verts_iff _ _).1 hx2
        obtain ⟨u1, hu1, rfl⟩ := (hf w1 hw1.1 hw1.2).2.2.1 X1 hX1
        obtain ⟨u2, hu2, rfl⟩ := (hf w2 hw2.1 hw2.2).2.2.1 X2 hX2
        have hreach := hconn x u1 u2 hxX1 hxX2
        have hd1 := hkid_d w1 hw1.1 hw1.2
        have hd2 := hkid_d w2 hw2.1 hw2.2
        obtain ⟨x', hx'S, hx'A, hx'r, hpS, hpA⟩ :=
          exit (S := {i | x ∈ bag i}) (A := {y | Desc r par w1 y}) hR
            (fun c hc hp => Desc.tail hp hc rfl) hxX1 hu1 hxX2
            (by
              intro hv
              simp only [Set.mem_ofPred_eq] at hv
              rcases Desc.comparable hv hu2 with h | h
              · have := Desc.d_lt hR h hne
                omega
              · have := Desc.d_lt hR h (Ne.symm hne)
                omega) hreach
        have := Desc.eq_of_par_not hx'A hpA
        subst this
        rw [hw1.2] at hpS
        exact hpS
    · intro X hX
      rw [RT.bags_node] at hX
      rcases hX with rfl | ⟨k, hk, hX⟩
      · exact ⟨v, Desc.refl _, rfl⟩
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hk
        rw [Finset.mem_toList, hkids] at hw
        obtain ⟨u, hu, e⟩ := (hf w hw.1 hw.2).2.2.1 X hX
        exact ⟨u, (Desc.child hw.1 hw.2).trans hu, e⟩
    · intro u hu
      rw [RT.bags_node]
      by_cases huv : v = u
      · subst huv; exact Or.inl rfl
      · obtain ⟨w, hw1, hw2, hwu⟩ := Desc.exists_kid hu huv
        right
        refine ⟨f w, List.mem_map.2 ⟨w, ?_, rfl⟩, (hf w hw1 hw2).2.2.2 u hwu⟩
        rw [Finset.mem_toList, hkids]
        exact ⟨hw1, hw2⟩

/-- Folding at the root. -/
theorem exists_rt (hR : Rooted r par d) (bag : V → Finset ℕ)
    (hconn : ∀ x a b (ha : x ∈ bag a) (hb : x ∈ bag b),
      ((rgraph par).induce {i | x ∈ bag i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ t : RT, t.rootBag = bag r ∧ t.Conn ∧ (∀ X ∈ t.bags, ∃ i, bag i = X) ∧ (∀ i, bag i ∈ t.bags) := by
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_rt_sub hR bag hconn r
  exact ⟨t, h1, h2, fun X hX => let ⟨u, _, e⟩ := h3 X hX; ⟨u, e⟩, fun i => h4 i (Desc.root hR i)⟩

end fold

theorem reachable_congr {V : Type} {T T' : SimpleGraph V} (hT : T = T') {S S' : Set V} (hS : S = S')
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) (h : (T.induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    (T'.induce S').Reachable ⟨a, hS ▸ ha⟩ ⟨b, hS ▸ hb⟩ := by
  subst hT; subst hS; exact h

/-- **Bridge 1, (→).** -/
theorem rt_of_hasTreewidthAtMost {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ}
    (h : HasTreewidthAtMost G w) :
    ∃ t : RT, t.IsTD (liftGraph G) (Finset.range n) ∧ t.Width w := by
  obtain ⟨D, hD⟩ := h
  have := D.nodeFintype
  have hne : Nonempty D.Node := D.isTree.connected.nonempty
  obtain ⟨r⟩ := hne
  obtain ⟨par, d, hR, heq⟩ := exists_rooting D.isTree r
  let bag' : D.Node → Finset ℕ := fun i => (D.bag i).map Fin.valEmbedding
  have hmem : ∀ x i, x ∈ bag' i ↔ ∃ y : Fin n, y ∈ D.bag i ∧ y.val = x := by
    intro x i; simp [bag']
  have hconn : ∀ x a b (ha : x ∈ bag' a) (hb : x ∈ bag' b),
      ((rgraph par).induce {i | x ∈ bag' i}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro x a b ha hb
    obtain ⟨y, hya, rfl⟩ := (hmem x a).1 ha
    obtain ⟨y', hyb, hy'⟩ := (hmem _ b).1 hb
    have hyy : y' = y := Fin.ext hy'
    subst hyy
    have hS : {i | y'.val ∈ bag' i} = {i | y' ∈ D.bag i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      rw [hmem]
      constructor
      · rintro ⟨z, hz, hzy⟩
        rwa [Fin.ext hzy] at hz
      · intro hy; exact ⟨y', hy, rfl⟩
    have := reachable_congr heq hS.symm (a := a) (b := b) hya hyb
      ((D.bag_indices_connected y').preconnected ⟨a, hya⟩ ⟨b, hyb⟩)
    exact this
  obtain ⟨t, hroot, hconn', hb1, hb2⟩ := exists_rt hR bag' hconn
  refine ⟨t, ⟨?_, ?_, hconn'⟩, ?_⟩
  · ext x
    rw [RT.mem_verts_iff, Finset.mem_range]
    constructor
    · rintro ⟨X, hX, hx⟩
      obtain ⟨i, rfl⟩ := hb1 X hX
      obtain ⟨y, _, rfl⟩ := (hmem x i).1 hx
      exact y.2
    · intro hx
      obtain ⟨i, hi⟩ := D.vertex_mem_bag ⟨x, hx⟩
      exact ⟨bag' i, hb2 i, (hmem x i).2 ⟨⟨x, hx⟩, hi, rfl⟩⟩
  · intro u v huv _ _
    obtain ⟨u', v', hadj, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 huv
    obtain ⟨i, hui, hvi⟩ := D.edge_mem_bag hadj
    exact ⟨bag' i, hb2 i, (hmem _ i).2 ⟨u', hui, rfl⟩, (hmem _ i).2 ⟨v', hvi, rfl⟩⟩
  · intro X hX
    obtain ⟨i, rfl⟩ := hb1 X hX
    simpa [bag'] using hD i


end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge1Paths` -/

section
/-!
# Nodes of an `RT` as paths

`paths t` is the (finite) set of paths (child indices from the root) of an `RT`; `bagAt t p` the bag at a path.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace RT

mutual
/-- The set of nodes of the tree, as paths of child indices. -/
def paths : RT → Finset (List ℕ)
  | .node _ ks => insert [] (pathsL ks 0)
/-- Paths into a list of trees whose first index is `j`. -/
def pathsL : List RT → ℕ → Finset (List ℕ)
  | [], _ => ∅
  | k :: ks, j => (paths k).image (List.cons j) ∪ pathsL ks (j + 1)
end

mutual
/-- The bag at a path (empty for a non-path). -/
def bagAt : RT → List ℕ → Finset ℕ
  | .node b _, [] => b
  | .node _ ks, i :: p => bagAtL ks i p
/-- The bag below the `i`-th tree of the list. -/
def bagAtL : List RT → ℕ → List ℕ → Finset ℕ
  | [], _, _ => ∅
  | k :: _, 0, p => bagAt k p
  | _ :: ks, i + 1, p => bagAtL ks i p
end

theorem mem_pathsL (ks : List RT) (j : ℕ) (q : List ℕ) :
    q ∈ pathsL ks j ↔ ∃ i k q', ks[i]? = some k ∧ q' ∈ paths k ∧ q = (j + i) :: q' := by
  induction ks generalizing j with
  | nil => simp [pathsL]
  | cons k ks ih =>
    simp only [pathsL, Finset.mem_union, Finset.mem_image, ih]
    constructor
    · rintro (⟨q', hq', rfl⟩ | ⟨i, k', q', h1, h2, rfl⟩)
      · exact ⟨0, k, q', by simp, hq', by simp⟩
      · exact ⟨i + 1, k', q', by simpa using h1, h2, by congr 1; omega⟩
    · rintro ⟨i, k', q', h1, h2, rfl⟩
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
        subst h1
        exact Or.inl ⟨q', h2, by simp⟩
      · simp only [List.getElem?_cons_succ] at h1
        exact Or.inr ⟨i, k', q', h1, h2, by congr 1; omega⟩

theorem mem_paths_node (b : Finset ℕ) (ks : List RT) (p : List ℕ) :
    p ∈ paths (.node b ks) ↔ p = [] ∨ ∃ i k q', ks[i]? = some k ∧ q' ∈ paths k ∧ p = i :: q' := by
  simp only [paths, Finset.mem_insert, mem_pathsL, zero_add]

theorem bagAtL_of_getElem? : ∀ (ks : List RT) (i : ℕ) (k : RT) (p : List ℕ),
    ks[i]? = some k → bagAtL ks i p = bagAt k p
  | [], i, k, p, h => by simp at h
  | k' :: ks, 0, k, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp [bagAtL]
  | k' :: ks, i + 1, k, p, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [bagAtL, bagAtL_of_getElem? ks i k p h]

theorem bagAt_nil (b : Finset ℕ) (ks : List RT) : bagAt (.node b ks) [] = b := by simp [bagAt]

theorem bagAt_cons (b : Finset ℕ) (ks : List RT) (i : ℕ) (k : RT) (p : List ℕ) (h : ks[i]? = some k) :
    bagAt (.node b ks) (i :: p) = bagAt k p := by
  simp only [bagAt]; exact bagAtL_of_getElem? ks i k p h

theorem nil_mem_paths (t : RT) : ([] : List ℕ) ∈ paths t := by
  cases t; simp [paths]

/-- Paths are closed under removing the last step. -/
theorem dropLast_mem_paths (t : RT) : ∀ p ∈ paths t, p.dropLast ∈ paths t := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro p hp
    rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
    · simpa using nil_mem_paths _
    · rcases q' with _ | ⟨a, q''⟩
      · simpa using nil_mem_paths _
      · have := ih k (List.mem_of_getElem? hk) _ hq'
        rw [List.dropLast_cons_of_ne_nil (by simp)]
        exact (mem_paths_node b ks _).2 (Or.inr ⟨i, k, _, hk, this, rfl⟩)

/-- Every bag of the tree is the bag at some path. -/
theorem exists_path_of_mem_bags (t : RT) : ∀ X ∈ t.bags, ∃ p ∈ paths t, bagAt t p = X := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro X hX
    rcases (bags_node b ks).1 hX with rfl | ⟨k, hk, hXk⟩
    · exact ⟨[], nil_mem_paths _, bagAt_nil _ _⟩
    · obtain ⟨p, hp, hpX⟩ := ih k hk X hXk
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hk
      exact ⟨i :: p, (mem_paths_node b ks _).2 (Or.inr ⟨i, k, p, hi, hp, rfl⟩),
        by rw [bagAt_cons b ks i k p hi, hpX]⟩

/-- The bag at any path is a bag of the tree. -/
theorem bagAt_mem_bags (t : RT) : ∀ p ∈ paths t, bagAt t p ∈ t.bags := by
  induction t using RT.ind with
  | _ b ks ih =>
    intro p hp
    rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
    · rw [bagAt_nil]; exact (bags_node b ks).2 (Or.inl rfl)
    · rw [bagAt_cons b ks i k q' hk]
      exact (bags_node b ks).2 (Or.inr ⟨k, List.mem_of_getElem? hk, ih k (List.mem_of_getElem? hk) q' hq'⟩)

theorem bagAt_nil_eq (t : RT) : bagAt t [] = t.rootBag := by cases t; simp [bagAt, rootBag]

theorem mem_verts_of_bagAt {t : RT} {q : List ℕ} (hq : q ∈ paths t) {x : ℕ} (h : x ∈ bagAt t q) :
    x ∈ t.verts :=
  (mem_verts_iff _ _).2 ⟨_, bagAt_mem_bags t q hq, h⟩

/-- **Top of an occurrence set.**  In a tree with `Conn`, the paths whose bag contains `x` form a connected
set with a top element: all its other members have their parent in the set. -/
theorem top_exists : ∀ t : RT, t.Conn → ∀ x : ℕ, (∃ p ∈ paths t, x ∈ bagAt t p) →
    ∃ p₀ ∈ paths t, x ∈ bagAt t p₀ ∧
      ∀ q ∈ paths t, x ∈ bagAt t q → q ≠ p₀ → q ≠ [] ∧ x ∈ bagAt t q.dropLast := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro hc x hx
    obtain ⟨hks, h2, h3⟩ := (conn_node_iff b ks).1 hc
    by_cases hxb : x ∈ b
    · refine ⟨[], nil_mem_paths _, by rwa [bagAt_nil], ?_⟩
      intro q hq hxq hne
      rcases (mem_paths_node b ks q).1 hq with rfl | ⟨i, k, q', hk, hq', rfl⟩
      · exact absurd rfl hne
      · refine ⟨by simp, ?_⟩
        rw [bagAt_cons b ks i k q' hk] at hxq
        have hkm := List.mem_of_getElem? hk
        have hxv := mem_verts_of_bagAt hq' hxq
        have hroot := h2 k hkm x hxb hxv
        obtain ⟨p₀, hp₀, hxp₀, htop⟩ := ih k hkm (hks k hkm) x ⟨q', hq', hxq⟩
        have hp₀nil : p₀ = [] := by
          by_contra hne'
          have := (htop [] (nil_mem_paths k) (by rw [bagAt_nil_eq]; exact hroot) (Ne.symm hne')).1
          exact absurd rfl this
        subst hp₀nil
        rcases q' with _ | ⟨a, q''⟩
        · simpa [bagAt_nil] using hxb
        · have := (htop (a :: q'') hq' hxq (List.cons_ne_nil _ _)).2
          rw [List.dropLast_cons_of_ne_nil (by simp), bagAt_cons b ks i k _ hk]
          exact this
    · obtain ⟨p, hp, hxp⟩ := hx
      rcases (mem_paths_node b ks p).1 hp with rfl | ⟨i, k, q', hk, hq', rfl⟩
      · rw [bagAt_nil] at hxp; exact absurd hxp hxb
      · rw [bagAt_cons b ks i k q' hk] at hxp
        have hkm := List.mem_of_getElem? hk
        obtain ⟨p₀, hp₀, hxp₀, htop⟩ := ih k hkm (hks k hkm) x ⟨q', hq', hxp⟩
        refine ⟨i :: p₀, (mem_paths_node b ks _).2 (Or.inr ⟨i, k, p₀, hk, hp₀, rfl⟩),
          by rw [bagAt_cons b ks i k p₀ hk]; exact hxp₀, ?_⟩
        intro q hq hxq hne
        rcases (mem_paths_node b ks q).1 hq with rfl | ⟨j, k', q'', hk', hq'', rfl⟩
        · rw [bagAt_nil] at hxq; exact absurd hxq hxb
        · rw [bagAt_cons b ks j k' q'' hk'] at hxq
          have hji : j = i := by
            by_contra hji
            have hxv1 := mem_verts_of_bagAt hq' hxp
            have hxv2 := mem_verts_of_bagAt hq'' hxq
            rw [List.pairwise_iff_getElem] at h3
            obtain ⟨hi1, hk1⟩ := List.getElem?_eq_some_iff.1 hk
            obtain ⟨hj1, hk2⟩ := List.getElem?_eq_some_iff.1 hk'
            rcases lt_or_gt_of_ne hji with h | h
            · exact hxb (h3 j i hj1 hi1 h x (by rw [hk2]; exact hxv2) (by rw [hk1]; exact hxv1))
            · exact hxb (h3 i j hi1 hj1 h x (by rw [hk1]; exact hxv1) (by rw [hk2]; exact hxv2))
          subst hji
          rw [hk] at hk'
          have hkk : k = k' := Option.some.inj hk'
          subst hkk
          have hq_ne : q'' ≠ p₀ := fun e => hne (by rw [e])
          obtain ⟨hne0, hd⟩ := htop q'' hq'' hxq hq_ne
          refine ⟨by simp, ?_⟩
          obtain ⟨a, q3, rfl⟩ := List.exists_cons_of_ne_nil hne0
          rw [List.dropLast_cons_of_ne_nil (by simp), bagAt_cons b ks j k _ hk]
          exact hd

end RT

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge1From` -/

section
/-!
# Bridge 1, direction (←): an `RT` decomposition is a `TreeDecomposition`

The abstract tree lives on the nodes-as-paths of the `RT` (`RT.paths`); the parent of a path drops its last step.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax117284Proofs.Treewidth.Trees.RootedTree Lax228581.Treewidth

theorem hasTreewidthAtMost_of_rt {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {t : RT}
    (htd : t.IsTD (liftGraph G) (Finset.range n)) (hw : t.Width w) : HasTreewidthAtMost G w := by
  classical
  let N := {p : List ℕ // p ∈ t.paths}
  let r : N := ⟨[], RT.nil_mem_paths t⟩
  let par : N → N := fun p => ⟨p.1.dropLast, RT.dropLast_mem_paths t _ p.2⟩
  let dd : N → ℕ := fun p => p.1.length
  have hR : Rooted r par dd := by
    refine ⟨rfl, ?_⟩
    intro x hx
    have : x.1 ≠ [] := fun e => hx (Subtype.ext e)
    show x.1.dropLast.length + 1 = x.1.length
    rw [List.length_dropLast]
    have := List.length_pos_iff.2 this
    omega
  let bag : N → Finset (Fin n) := fun q => Finset.univ.filter (fun y => y.1 ∈ t.bagAt q.1)
  have hbag : ∀ q y, y ∈ bag q ↔ y.1 ∈ t.bagAt q.1 := by intro q y; simp [bag]
  have hocc : ∀ y : Fin n, ∃ p ∈ t.paths, y.1 ∈ t.bagAt p := by
    intro y
    have : y.1 ∈ t.verts := by rw [htd.verts_eq]; exact Finset.mem_range.2 y.2
    obtain ⟨X, hX, hyX⟩ := (RT.mem_verts_iff _ _).1 this
    obtain ⟨p, hp, rfl⟩ := RT.exists_path_of_mem_bags t X hX
    exact ⟨p, hp, hyX⟩
  refine ⟨{ Node := N, tree := rgraph par, isTree := hR.isTree, bag := bag,
            vertex_mem_bag := ?_, edge_mem_bag := ?_, bag_indices_connected := ?_ }, ?_⟩
  · intro y
    obtain ⟨p, hp, h⟩ := hocc y
    exact ⟨⟨p, hp⟩, (hbag _ _).2 h⟩
  · intro u v huv
    have hadj : (liftGraph G).Adj u.1 v.1 := (SimpleGraph.map_adj _ _ _ _).2 ⟨u, v, huv, rfl, rfl⟩
    obtain ⟨X, hX, hu, hv⟩ := htd.edges u.1 v.1 hadj (Finset.mem_range.2 u.2) (Finset.mem_range.2 v.2)
    obtain ⟨p, hp, rfl⟩ := RT.exists_path_of_mem_bags t X hX
    exact ⟨⟨p, hp⟩, (hbag _ _).2 hu, (hbag _ _).2 hv⟩
  · intro y
    obtain ⟨p, hp, h⟩ := hocc y
    obtain ⟨p₀, hp₀, hyp₀, htop⟩ := RT.top_exists t htd.conn y.1 ⟨p, hp, h⟩
    have ht₀ : (⟨p₀, hp₀⟩ : N) ∈ {i : N | y ∈ bag i} := (hbag _ _).2 hyp₀
    have htop' : ∀ s ∈ {i : N | y ∈ bag i}, s ≠ ⟨p₀, hp₀⟩ → s ≠ r ∧ par s ∈ {i : N | y ∈ bag i} := by
      intro s hs hne
      have hq : s.1 ≠ p₀ := fun e => hne (Subtype.ext e)
      obtain ⟨h1, h2⟩ := htop s.1 s.2 ((hbag _ _).1 hs) hq
      exact ⟨fun e => h1 (congrArg Subtype.val e), (hbag _ _).2 h2⟩
    have : Nonempty ↥{i : N | y ∈ bag i} := ⟨⟨_, ht₀⟩⟩
    exact ⟨fun a b => (reachable_of_top hR ht₀ htop' a.1 a.2).trans
      (reachable_of_top hR ht₀ htop' b.1 b.2).symm⟩
  · intro q
    refine le_trans ?_ (hw _ (RT.bagAt_mem_bags t q.1 q.2))
    apply Finset.card_le_card_of_injOn Fin.val
    · intro y hy
      exact (hbag _ _).1 hy
    · intro a _ b _ e
      exact Fin.ext e

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge1` -/

section
/-!
# Bridge 1: `RT ↔ Lax228581.Treewidth.TreeDecomposition`

* `hasTreewidthAtMost_iff_rt` : the concept's `HasTreewidthAtMost` in terms of `RT`.
  (→) roots the abstract tree (`exists_rooting`: parent function and depth from the distance to the root) and
  folds it into an `RT` by induction on the descendant sets (`exists_rt_sub`); `Conn` follows from the
  connectedness of the occurrence sets via the *exit lemma*.
  (←) builds the abstract tree on the nodes-as-paths of the `RT` (`RT.paths`), parent = drop the last step;
  connectedness of an occurrence set follows from its top element (`RT.top_exists`).
* `hasTreewidthAtMost_prefix` : monotonicity under induced subgraphs on initial segments, via `RT.restrict`.

Files: `Bridge1Root` (parent-function trees), `Bridge1Rt` (basic `RT` facts), `Bridge1To`, `Bridge1Paths`,
`Bridge1From`, `Bridge1Restrict`.
-/

namespace Lax117284Proofs.Treewidth.Trees

open Lax228581.Treewidth

/-- **Bridge 1 (statement side).**  `HasTreewidthAtMost` of the concept package, in terms of `RT`. -/
theorem hasTreewidthAtMost_iff_rt {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) :
    HasTreewidthAtMost G w ↔ ∃ t : RT, t.IsTD (liftGraph G) (Finset.range n) ∧ t.Width w :=
  ⟨rt_of_hasTreewidthAtMost, fun ⟨_, h1, h2⟩ => hasTreewidthAtMost_of_rt h1 h2⟩

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordLayout` -/

section
/-!
# Nice-decomposition words in arbitrary layout (T2)

`GraphWords.NiceDecomposition` allows *any* topological layout of the nodes (the first child of a node is the node just
before it; the second child of a join is an arbitrary earlier node) and arbitrary junk in the unused fields of a record.
`NT.encode` produces only one canonical layout.  So the word format is read by `ofWord`, which ignores the junk and the
layout, and everything in this file is proved for an *arbitrary* word `D` satisfying `Lay n D` (the graph-independent
half of `NiceDecomposition`).

Notation: `N = nodeCount D`; `bagN n D i` is `bagAt n D i` with vertices as naturals; `ofWord D i` is the nice tree
rooted at node `i`; `desc D i` the set of nodes of that subtree.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

/-! ## bags as sets of naturals -/

/-- `bagAt` with the vertices as natural numbers. -/
def bagN (n : ℕ) (D : List ℕ) (i : ℕ) : Finset ℕ := (bagAt n D i).map Fin.valEmbedding

lemma mem_bagN {n : ℕ} {D : List ℕ} {i u : ℕ} :
    u ∈ bagN n D i ↔ ∃ h : u < n, (⟨u, h⟩ : Fin n) ∈ bagAt n D i := by
  unfold bagN
  simp only [Finset.mem_map, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, hu⟩; exact ⟨⟨u, h⟩, hu, rfl⟩

lemma bagN_zero (n : ℕ) (D : List ℕ) : bagN n D 0 = ∅ := by simp [bagN, bagAt]

lemma bagN_succ_intro {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 1) (hv : vertex D (i + 1) < n) :
    bagN n D (i + 1) = insert (vertex D (i + 1)) (bagN n D i) := by
  simp [bagN, bagAt, hk, hv, Finset.map_insert]

lemma bagN_succ_forget {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 2) (hv : vertex D (i + 1) < n) :
    bagN n D (i + 1) = (bagN n D i).erase (vertex D (i + 1)) := by
  simp [bagN, bagAt, hk, hv, Finset.map_erase]

lemma bagN_succ_join {n : ℕ} {D : List ℕ} {i : ℕ} (hk : kind D (i + 1) = 3) :
    bagN n D (i + 1) = bagN n D i := by
  simp [bagN, bagAt, hk]

lemma bagN_succ_leaf {n : ℕ} {D : List ℕ} {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2)
    (h3 : kind D (i + 1) ≠ 3) : bagN n D (i + 1) = ∅ := by
  simp [bagN, bagAt, h1, h2, h3]

/-! ## the layout conditions -/

/-- The graph-independent half of `NiceDecomposition`: the word is `N` records, every record has the right shape, and
every non-last node has exactly one parent.  (The tree condition follows, `Lay.isTree`.) -/
structure Lay (n : ℕ) (D : List ℕ) : Prop where
  length_eq : D.length = 1 + 3 * nodeCount D
  nonempty : 0 < nodeCount D
  shape : ∀ i, i < nodeCount D →
    kind D i = 0 ∨
    (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
      ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
    (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
      bagAt n D (other D i) = bagAt n D (i - 1))
  parent : ∀ c, c + 1 < nodeCount D → ∃! p, IsChild D c p

variable {n : ℕ} {D : List ℕ}

/-- Introduce nodes. -/
lemma Lay.intro_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 1) :
    0 < i ∧ vertex D i < n ∧ vertex D i ∉ bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · refine ⟨h0, hv, fun hm => ?_⟩
    obtain ⟨h, hm⟩ := mem_bagN.1 hm
    exact hb h hm
  · omega
  · omega

/-- Forget nodes. -/
lemma Lay.forget_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 2) :
    0 < i ∧ vertex D i < n ∧ vertex D i ∈ bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · omega
  · exact ⟨h0, hv, mem_bagN.2 ⟨hv, hb hv⟩⟩
  · omega

/-- Join nodes. -/
lemma Lay.join_data (L : Lay n D) {i : ℕ} (hi : i < nodeCount D) (hk : kind D i = 3) :
    0 < i ∧ other D i + 1 < i ∧ bagN n D (other D i) = bagN n D (i - 1) := by
  rcases L.shape i hi with h | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩ | ⟨h0, h1, hv, hb⟩
  · omega
  · omega
  · omega
  · exact ⟨h0, hv, by simp only [bagN, hb]⟩

/-- The node after `i` has a parent iff it's not the last. -/
lemma Lay.isChild_lt (L : Lay n D) {c p : ℕ} (h : IsChild D c p) : c < p ∧ p < nodeCount D := by
  obtain ⟨hp, h⟩ := h
  refine ⟨?_, hp⟩
  rcases h with ⟨-, h⟩ | ⟨hk, h | h⟩
  · omega
  · omega
  · have := (L.join_data hp hk).2.1; omega

/-! ## the tree read off a word -/

/-- The nice tree rooted at node `i` (junk fields and the layout are ignored). -/
def ofWord (D : List ℕ) : ℕ → NT
  | 0 => .leaf
  | i + 1 =>
    if kind D (i + 1) = 1 then .intro (vertex D (i + 1)) (ofWord D i)
    else if kind D (i + 1) = 2 then .forget (vertex D (i + 1)) (ofWord D i)
    else if kind D (i + 1) = 3 then
      (if h : other D (i + 1) < i then .join (ofWord D i) (ofWord D (other D (i + 1))) else .leaf)
    else .leaf
termination_by i => i
decreasing_by all_goals omega

/-- The nodes of the subtree rooted at `i`. -/
def desc (D : List ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | i + 1 =>
    if kind D (i + 1) = 1 ∨ kind D (i + 1) = 2 then insert (i + 1) (desc D i)
    else if kind D (i + 1) = 3 then
      (if h : other D (i + 1) < i then insert (i + 1) (desc D i ∪ desc D (other D (i + 1))) else {i + 1})
    else {i + 1}
termination_by i => i
decreasing_by all_goals omega

lemma ofWord_zero : ofWord D 0 = .leaf := by rw [ofWord]

lemma ofWord_intro {i : ℕ} (h : kind D (i + 1) = 1) :
    ofWord D (i + 1) = .intro (vertex D (i + 1)) (ofWord D i) := by
  rw [ofWord]; simp [h]

lemma ofWord_forget {i : ℕ} (h : kind D (i + 1) = 2) :
    ofWord D (i + 1) = .forget (vertex D (i + 1)) (ofWord D i) := by
  rw [ofWord]; simp [h]

lemma ofWord_join {i : ℕ} (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) :
    ofWord D (i + 1) = .join (ofWord D i) (ofWord D (other D (i + 1))) := by
  rw [ofWord]; simp [h, ho]

lemma ofWord_leaf {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) :
    ofWord D (i + 1) = .leaf := by
  rw [ofWord]; simp [h1, h2, h3]

lemma desc_zero : desc D 0 = {0} := by rw [desc]

lemma desc_intro {i : ℕ} (h : kind D (i + 1) = 1) : desc D (i + 1) = insert (i + 1) (desc D i) := by
  rw [desc]; simp [h]

lemma desc_forget {i : ℕ} (h : kind D (i + 1) = 2) : desc D (i + 1) = insert (i + 1) (desc D i) := by
  rw [desc]; simp [h]

lemma desc_join {i : ℕ} (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) :
    desc D (i + 1) = insert (i + 1) (desc D i ∪ desc D (other D (i + 1))) := by
  rw [desc]; simp [h, ho]

lemma desc_leaf {i : ℕ} (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) :
    desc D (i + 1) = {i + 1} := by
  rw [desc]; simp [h1, h2, h3]

/-- The case analysis at node `i + 1`. -/
inductive Node (n : ℕ) (D : List ℕ) (i : ℕ) : Prop
  | leaf (h1 : kind D (i + 1) ≠ 1) (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3)
  | intro (h : kind D (i + 1) = 1) (hv : vertex D (i + 1) < n) (hn : vertex D (i + 1) ∉ bagN n D i)
  | forget (h : kind D (i + 1) = 2) (hv : vertex D (i + 1) < n) (hn : vertex D (i + 1) ∈ bagN n D i)
  | join (h : kind D (i + 1) = 3) (ho : other D (i + 1) < i) (hb : bagN n D (other D (i + 1)) = bagN n D i)

lemma Lay.node (L : Lay n D) {i : ℕ} (hi : i + 1 < nodeCount D) : Node n D i := by
  by_cases h1 : kind D (i + 1) = 1
  · obtain ⟨-, hv, hn⟩ := L.intro_data hi h1
    exact .intro h1 hv (by simpa using hn)
  by_cases h2 : kind D (i + 1) = 2
  · obtain ⟨-, hv, hn⟩ := L.forget_data hi h2
    exact .forget h2 hv (by simpa using hn)
  by_cases h3 : kind D (i + 1) = 3
  · obtain ⟨-, ho, hb⟩ := L.join_data hi h3
    exact .join h3 (by omega) (by simpa using hb)
  exact .leaf h1 h2 h3

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordDesc` -/

section
/-!
# The subtree of a node of a word in arbitrary layout (T2)

`desc D i` (the nodes below `i`) satisfies: it is closed under children, contained in `[0, i]`, transitive, its members
are linearly ordered along parent chains, the two subtrees of a join are disjoint, and `desc D (N-1)` is everything.
All from `Lay` (the unique parent).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma self_mem_desc (D : List ℕ) (i : ℕ) : i ∈ desc D i := by
  cases i with
  | zero => simp [desc_zero]
  | succ i =>
    rw [desc]
    split_ifs <;> simp

lemma desc_le (D : List ℕ) : ∀ i j, j ∈ desc D i → j ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hj
    cases i with
    | zero => simp [desc_zero] at hj; omega
    | succ i =>
      rw [desc] at hj
      split_ifs at hj with h1 h2 h3
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact le_rfl
        · exact (ih i (by omega) j hj).trans (by omega)
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact le_rfl
        · rcases Finset.mem_union.1 hj with hj | hj
          · exact (ih i (by omega) j hj).trans (by omega)
          · exact (ih _ (by omega) j hj).trans (by omega)
      · simp at hj; omega
      · simp at hj; omega

lemma kind_zero (L : Lay n D) : kind D 0 = 0 := by
  rcases L.shape 0 L.nonempty with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h
  all_goals omega

/-- Children of the node `i + 1`. -/
lemma Lay.isChild_succ_leaf (_L : Lay n D) {i c : ℕ} (_hi : i + 1 < nodeCount D) (h1 : kind D (i + 1) ≠ 1)
    (h2 : kind D (i + 1) ≠ 2) (h3 : kind D (i + 1) ≠ 3) : ¬ IsChild D c (i + 1) := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> omega

lemma Lay.isChild_succ_unary (_L : Lay n D) {i c : ℕ} (hk : kind D (i + 1) = 1 ∨ kind D (i + 1) = 2)
    (hi : i + 1 < nodeCount D) : IsChild D c (i + 1) ↔ c = i := by
  constructor
  · rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
    · omega
    · omega
  · rintro rfl; exact ⟨hi, Or.inl ⟨hk, rfl⟩⟩

lemma Lay.isChild_succ_join (_L : Lay n D) {i c : ℕ} (hk : kind D (i + 1) = 3)
    (hi : i + 1 < nodeCount D) : IsChild D c (i + 1) ↔ c = i ∨ c = other D (i + 1) := by
  constructor
  · rintro ⟨-, ⟨h, -⟩ | ⟨-, h | h⟩⟩
    · omega
    · left; omega
    · right; exact h
  · rintro (rfl | rfl)
    · exact ⟨hi, Or.inr ⟨hk, Or.inl rfl⟩⟩
    · exact ⟨hi, Or.inr ⟨hk, Or.inr rfl⟩⟩

lemma Lay.not_isChild_zero (L : Lay n D) {c : ℕ} : ¬ IsChild D c 0 := by
  rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> rw [kind_zero L] at h <;> omega

/-- Descent: a node is below `m` iff it is `m` or below a child. -/
lemma Lay.mem_desc_iff (L : Lay n D) {m x : ℕ} (hm : m < nodeCount D) :
    x ∈ desc D m ↔ x = m ∨ ∃ c, IsChild D c m ∧ x ∈ desc D c := by
  cases m with
  | zero =>
    simp only [desc_zero, Finset.mem_singleton]
    constructor
    · exact Or.inl
    · rintro (h | ⟨c, hc, -⟩)
      · exact h
      · exact absurd hc L.not_isChild_zero
  | succ i =>
    rcases L.node hm with ⟨h1, h2, h3⟩ | ⟨hkd, -, -⟩ | ⟨hkd, -, -⟩ | ⟨hkd, ho, -⟩
    · rw [desc_leaf h1 h2 h3]
      simp only [Finset.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (h | ⟨c, hc, -⟩)
        · exact h
        · exact absurd hc (L.isChild_succ_leaf hm h1 h2 h3)
    · rw [desc_intro hkd, Finset.mem_insert]
      simp only [L.isChild_succ_unary (Or.inl hkd) hm]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, rfl, h⟩
      · rintro (h | ⟨c, rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr h
    · rw [desc_forget hkd, Finset.mem_insert]
      simp only [L.isChild_succ_unary (Or.inr hkd) hm]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, rfl, h⟩
      · rintro (h | ⟨c, rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr h
    · rw [desc_join hkd ho, Finset.mem_insert, Finset.mem_union]
      simp only [L.isChild_succ_join hkd hm]
      constructor
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inr ⟨i, Or.inl rfl, h⟩
        · exact Or.inr ⟨_, Or.inr rfl, h⟩
      · rintro (h | ⟨c, rfl | rfl, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- Children have smaller indices. -/
lemma Lay.child_desc_sub (L : Lay n D) {c p : ℕ} (h : IsChild D c p) : desc D c ⊆ desc D p := by
  intro x hx
  exact (L.mem_desc_iff h.1).2 (Or.inr ⟨c, h, hx⟩)

/-- Transitivity of descent. -/
lemma Lay.desc_trans (L : Lay n D) : ∀ c a b, c < nodeCount D → a ∈ desc D b → b ∈ desc D c → a ∈ desc D c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro a b hc hab hbc
    rcases (L.mem_desc_iff hc).1 hbc with rfl | ⟨c', hc', hbc'⟩
    · exact hab
    · have hlt := L.isChild_lt hc'
      exact L.child_desc_sub hc' (ih c' hlt.1 a b (by omega) hab hbc')

lemma Lay.desc_sub_of_mem (L : Lay n D) {b c : ℕ} (hc : c < nodeCount D) (h : b ∈ desc D c) :
    desc D b ⊆ desc D c := fun _ ha => L.desc_trans c _ b hc ha h

/-- The parent, unique. -/
lemma Lay.parent_unique (L : Lay n D) {x p q : ℕ} (hp : IsChild D x p) (hq : IsChild D x q) : p = q := by
  have hx : x + 1 < nodeCount D := by
    have := L.isChild_lt hp; omega
  obtain ⟨r, -, hr⟩ := L.parent x hx
  rw [hr p hp, hr q hq]

/-- Every node is below the last one. -/
lemma Lay.desc_full (L : Lay n D) : desc D (nodeCount D - 1) = Finset.range (nodeCount D) := by
  have hN := L.nonempty
  ext x
  simp only [Finset.mem_range]
  constructor
  · intro hx; have := desc_le D _ x hx; omega
  · intro hx
    obtain ⟨k, hk⟩ : ∃ k, nodeCount D - 1 - x = k := ⟨_, rfl⟩
    induction k using Nat.strong_induction_on generalizing x with
    | _ k ih =>
      by_cases hxl : x = nodeCount D - 1
      · subst hxl; exact self_mem_desc D _
      · have hx1 : x + 1 < nodeCount D := by omega
        obtain ⟨p, hp, -⟩ := L.parent x hx1
        have hlt := L.isChild_lt hp
        have hpm : p ∈ desc D (nodeCount D - 1) := ih (nodeCount D - 1 - p) (by omega) p hlt.2 rfl
        exact L.desc_sub_of_mem (by omega) hpm ((L.mem_desc_iff hlt.2).2 (Or.inr ⟨x, hp, self_mem_desc D x⟩))

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordTree` -/

section
/-!
# The nice tree read off a word (T2)

For a word `D` with `Lay n D`, `ofWord D i` is a well-formed nice tree whose root bag is `bagAt i`, whose nodes
correspond to `desc D i`, and whose `RT.Conn` is the conjunction of the local conditions `Loc` on those nodes.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma Lay.bag_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → (ofWord D i).bag = bagN n D i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => simp [ofWord_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, -⟩ | ⟨hkd, hv, -⟩ | ⟨hkd, ho, -⟩
      · rw [ofWord_leaf h1 h2 h3, bagN_succ_leaf h1 h2 h3]; rfl
      · rw [ofWord_intro hkd, bagN_succ_intro hkd hv, NT.bag_intro, ih']
      · rw [ofWord_forget hkd, bagN_succ_forget hkd hv, NT.bag_forget, ih']
      · rw [ofWord_join hkd ho, bagN_succ_join hkd, NT.bag_join, ih']

lemma Lay.mem_vs_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → ∀ u,
    u ∈ (ofWord D i).vs ↔ ∃ j ∈ desc D i, u ∈ bagN n D j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi u
    cases i with
    | zero => simp [ofWord_zero, desc_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega) u
      have hb := L.bag_ofWord (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3] at hb ⊢
        rw [desc_leaf h1 h2 h3]
        simp only [NT.vs_leaf, Finset.notMem_empty, Finset.mem_singleton, exists_eq_left, false_iff]
        rw [← hb]; simp
      · rw [ofWord_intro hkd] at hb ⊢
        rw [desc_intro hkd]
        simp only [NT.vs_intro, Finset.mem_union, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_forget hkd] at hb ⊢
        rw [desc_forget hkd]
        simp only [NT.vs_forget, Finset.mem_union, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_join hkd ho]
        rw [desc_join hkd ho]
        have ih'' := ih (other D (i + 1)) (by omega) (by omega) u
        have hbi := L.bag_ofWord i (by omega)
        simp only [NT.vs_join, Finset.mem_union, ih', ih'', Finset.mem_insert,
          or_and_right, exists_or, exists_eq_left, hbi, ← bagN_succ_join hkd]

lemma Lay.mem_bs_ofWord (L : Lay n D) : ∀ i, i < nodeCount D → ∀ X,
    X ∈ (ofWord D i).bs ↔ ∃ j ∈ desc D i, X = bagN n D j := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X
    cases i with
    | zero => simp [ofWord_zero, desc_zero, bagN_zero]
    | succ i =>
      have ih' := ih i (by omega) (by omega) X
      have hb := L.bag_ofWord (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3] at hb ⊢
        rw [desc_leaf h1 h2 h3]
        simp only [NT.bs_leaf, List.mem_singleton, Finset.mem_singleton, exists_eq_left]
        rw [← hb]; rfl
      · rw [ofWord_intro hkd] at hb ⊢
        rw [desc_intro hkd]
        simp only [NT.bs_intro, List.mem_cons, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_forget hkd] at hb ⊢
        rw [desc_forget hkd]
        simp only [NT.bs_forget, List.mem_cons, ih', hb, Finset.mem_insert, exists_eq_or_imp]
      · rw [ofWord_join hkd ho]
        rw [desc_join hkd ho]
        have ih'' := ih (other D (i + 1)) (by omega) (by omega) X
        have hbi := L.bag_ofWord i (by omega)
        simp only [NT.bs_join, List.mem_cons, List.mem_append, ih', ih'', Finset.mem_insert,
          Finset.mem_union, or_and_right, exists_or, exists_eq_left, hbi, ← bagN_succ_join hkd]

/-- The local connectedness conditions at node `j`. -/
def Loc (n : ℕ) (D : List ℕ) (j : ℕ) : Prop :=
  (kind D j = 1 → ∀ x ∈ desc D (j - 1), vertex D j ∉ bagN n D x) ∧
  (kind D j = 3 → ∀ x ∈ desc D (j - 1), ∀ y ∈ desc D (other D j), ∀ u,
    u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D j)

lemma Lay.nconn_ofWord (L : Lay n D) : ∀ i, i < nodeCount D →
    (NT.NConn (ofWord D i) ↔ ∀ j ∈ desc D i, Loc n D j) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero =>
      have : Loc n D 0 := by simp [Loc, kind_zero L]
      simp [ofWord_zero, NT.NConn, desc_zero, this]
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      have hv := L.mem_vs_ofWord i (by omega)
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv', hn⟩ | ⟨hkd, hv', hn⟩ | ⟨hkd, ho, hbe⟩
      · rw [ofWord_leaf h1 h2 h3, desc_leaf h1 h2 h3]
        simp [NT.NConn, Loc, h1, h3]
      · have hl : Loc n D (i + 1) ↔ ∀ y ∈ desc D i, vertex D (i + 1) ∉ bagN n D y := by
          simp [Loc, hkd]
        rw [ofWord_intro hkd, desc_intro hkd, NT.NConn, Finset.forall_mem_insert, ih', hl, hv]
        simp only [not_exists, not_and]
      · have hl : Loc n D (i + 1) := by simp [Loc, hkd]
        rw [ofWord_forget hkd, desc_forget hkd, NT.NConn, Finset.forall_mem_insert, ih']
        simp [hl]
      · have ih'' := ih (other D (i + 1)) (by omega) (by omega)
        have hv2 := L.mem_vs_ofWord (other D (i + 1)) (by omega)
        have hbi := L.bag_ofWord i (by omega)
        have hl : Loc n D (i + 1) ↔ ∀ x ∈ desc D i, ∀ y ∈ desc D (other D (i + 1)), ∀ u,
            u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D i := by
          simp [Loc, hkd, bagN_succ_join hkd]
        rw [ofWord_join hkd ho, desc_join hkd ho, NT.NConn, Finset.forall_mem_insert, ih', ih'', hl]
        rw [hbi]
        have hA : (∀ u, u ∈ (ofWord D i).vs → u ∈ (ofWord D (other D (i + 1))).vs → u ∈ bagN n D i) ↔
            (∀ x ∈ desc D i, ∀ y ∈ desc D (other D (i + 1)), ∀ u,
              u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D i) := by
          constructor
          · intro h x hx y hy u hux huy
            exact h u ((hv u).2 ⟨x, hx, hux⟩) ((hv2 u).2 ⟨y, hy, huy⟩)
          · intro h u hu1 hu2
            obtain ⟨x, hx, hux⟩ := (hv u).1 hu1
            obtain ⟨y, hy, huy⟩ := (hv2 u).1 hu2
            exact h x hx y hy u hux huy
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨hA.1 h1, fun x hx => (Finset.mem_union.1 hx).elim (h2 x) (h3 x)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨hA.2 h1, fun x hx => h2 x (Finset.mem_union_left _ hx),
            fun x hx => h2 x (Finset.mem_union_right _ hx)⟩

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordConn` -/

section
/-!
# Connectedness of occurrence sets in the word tree (T2)

`ConnOn D S`: the set `S` of nodes is nonempty and any two of its members are joined by a chain of tree edges
staying in `S`.  We prove, for a word with `Lay n D`:

* `Lay.loc_of_connOn`: if all the occurrence sets are connected, the local conditions `Loc` hold (a *cut* argument:
  the subtree below a node `c` is left only through `c`);
* `Lay.connOn_of_loc`: conversely, the local conditions give connected occurrence sets (a *gluing* induction).
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

/-- Adjacency of two nodes in the tree. -/
def Adj' (D : List ℕ) (a b : ℕ) : Prop := IsChild D a b ∨ IsChild D b a

lemma Adj'.symm' {a b : ℕ} (h : Adj' D a b) : Adj' D b a := Or.symm h

/-- The tree edges inside `S`. -/
def RelOn (D : List ℕ) (S : Set ℕ) (a b : ℕ) : Prop := a ∈ S ∧ b ∈ S ∧ Adj' D a b

/-- `S` is nonempty and connected by tree edges inside `S`. -/
def ConnOn (D : List ℕ) (S : Set ℕ) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, Relation.ReflTransGen (RelOn D S) x y

/-- The occurrence set of the vertex `v`. -/
def Sv (n : ℕ) (D : List ℕ) (v : ℕ) : Set ℕ := {j | j < nodeCount D ∧ v ∈ bagN n D j}

lemma RelOn.mono {S T : Set ℕ} (h : S ⊆ T) {a b : ℕ} (hab : RelOn D S a b) : RelOn D T a b :=
  ⟨h hab.1, h hab.2.1, hab.2.2⟩

lemma ConnOn.union {A B : Set ℕ} (hA : ConnOn D A) (hB : ConnOn D B) {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B)
    (hxy : Adj' D x y) : ConnOn D (A ∪ B) := by
  have mA : ∀ {a b}, Relation.ReflTransGen (RelOn D A) a b → Relation.ReflTransGen (RelOn D (A ∪ B)) a b :=
    fun h => Relation.ReflTransGen.mono (fun _ _ hab => RelOn.mono Set.subset_union_left hab) _ _ h
  have mB : ∀ {a b}, Relation.ReflTransGen (RelOn D B) a b → Relation.ReflTransGen (RelOn D (A ∪ B)) a b :=
    fun h => Relation.ReflTransGen.mono (fun _ _ hab => RelOn.mono Set.subset_union_right hab) _ _ h
  have step : Relation.ReflTransGen (RelOn D (A ∪ B)) x y :=
    Relation.ReflTransGen.single ⟨Or.inl hx, Or.inr hy, hxy⟩
  have step' : Relation.ReflTransGen (RelOn D (A ∪ B)) y x :=
    Relation.ReflTransGen.single ⟨Or.inr hy, Or.inl hx, hxy.symm'⟩
  refine ⟨⟨x, Or.inl hx⟩, ?_⟩
  rintro p (hp | hp) q (hq | hq)
  · exact mA (hA.2 p hp q hq)
  · exact ((mA (hA.2 p hp x hx)).trans step).trans (mB (hB.2 y hy q hq))
  · exact ((mB (hB.2 p hp y hy)).trans step').trans (mA (hA.2 x hx q hq))
  · exact mB (hB.2 p hp q hq)

lemma ConnOn.singleton (x : ℕ) : ConnOn D {x} := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro p rfl q rfl
  exact Relation.ReflTransGen.refl

lemma ConnOn.insert {A : Set ℕ} (hA : ConnOn D A) {x y : ℕ} (hy : y ∈ A) (hxy : Adj' D x y) :
    ConnOn D (insert x A) := by
  have := (ConnOn.singleton (D := D) x).union hA (Set.mem_singleton x) hy hxy
  rwa [Set.singleton_union] at this

/-! ## the cut argument -/

/-! ## the gluing argument -/

/-- The occurrences of `v` below the node `m`. -/
def Av (n : ℕ) (D : List ℕ) (v m : ℕ) : Set ℕ := {j | j ∈ desc D m ∧ v ∈ bagN n D j}

/-- Empty or connected. -/
def EoC (D : List ℕ) (A : Set ℕ) : Prop := A = ∅ ∨ ConnOn D A

lemma Lay.eoc_unary (_L : Lay n D) {i v : ℕ}
    (hd : desc D (i + 1) = insert (i + 1) (desc D i))
    (hc : IsChild D i (i + 1))
    (hkey : v ∈ bagN n D (i + 1) → v ∈ bagN n D i ∨ ∀ j ∈ desc D i, v ∉ bagN n D j)
    (ih : EoC D (Av n D v i)) : EoC D (Av n D v (i + 1)) := by
  by_cases hv : v ∈ bagN n D (i + 1)
  · rcases hkey hv with hvi | hvi
    · have hA : Av n D v (i + 1) = insert (i + 1) (Av n D v i) := by
        ext j
        simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_insert_iff]
        constructor
        · rintro ⟨rfl | h, hj⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h, hj⟩
        · rintro (rfl | ⟨h, hj⟩)
          · exact ⟨Or.inl rfl, hv⟩
          · exact ⟨Or.inr h, hj⟩
      have hne : i ∈ Av n D v i := ⟨self_mem_desc D i, hvi⟩
      rcases ih with h | h
      · rw [h] at hne; exact absurd hne (Set.notMem_empty _)
      · rw [hA]; exact Or.inr (h.insert hne (Or.inr hc))
    · have hA : Av n D v (i + 1) = {i + 1} := by
        ext j
        simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | h, hj⟩
          · rfl
          · exact absurd hj (hvi j h)
        · rintro rfl; exact ⟨Or.inl rfl, hv⟩
      rw [hA]; exact Or.inr (ConnOn.singleton _)
  · have hA : Av n D v (i + 1) = Av n D v i := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨rfl | h, hj⟩
        · exact absurd hj hv
        · exact ⟨h, hj⟩
      · rintro ⟨h, hj⟩; exact ⟨Or.inr h, hj⟩
    rw [hA]; exact ih

lemma Lay.eoc_join (_L : Lay n D) {i o v : ℕ}
    (hd : desc D (i + 1) = insert (i + 1) (desc D i ∪ desc D o))
    (hci : IsChild D i (i + 1)) (hco : IsChild D o (i + 1))
    (hbo : bagN n D o = bagN n D i) (hb : bagN n D (i + 1) = bagN n D i)
    (hloc : ∀ x ∈ desc D i, ∀ y ∈ desc D o, ∀ u, u ∈ bagN n D x → u ∈ bagN n D y → u ∈ bagN n D (i + 1))
    (ih1 : EoC D (Av n D v i)) (ih2 : EoC D (Av n D v o)) : EoC D (Av n D v (i + 1)) := by
  by_cases hv : v ∈ bagN n D (i + 1)
  · have hvi : v ∈ bagN n D i := hb ▸ hv
    have hvo : v ∈ bagN n D o := hbo ▸ hvi
    have hA : Av n D v (i + 1) = insert (i + 1) (Av n D v i) ∪ Av n D v o := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Finset.mem_union, Set.mem_ofPred_eq, Set.mem_union,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | h | h, hj⟩
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ⟨h, hj⟩)
        · exact Or.inr ⟨h, hj⟩
      · rintro ((rfl | ⟨h, hj⟩) | ⟨h, hj⟩)
        · exact ⟨Or.inl rfl, hv⟩
        · exact ⟨Or.inr (Or.inl h), hj⟩
        · exact ⟨Or.inr (Or.inr h), hj⟩
    have hAi : i ∈ Av n D v i := ⟨self_mem_desc D i, hvi⟩
    have hAo : o ∈ Av n D v o := ⟨self_mem_desc D o, hvo⟩
    have c1 : ConnOn D (Av n D v i) := ih1.resolve_left (fun h => by rw [h] at hAi; exact hAi)
    have c2 : ConnOn D (Av n D v o) := ih2.resolve_left (fun h => by rw [h] at hAo; exact hAo)
    have c3 := c1.insert hAi (Or.inr hci)
    rw [hA]
    exact Or.inr (c3.union c2 (Set.mem_insert _ _) hAo (Or.inr hco))
  · have hA : Av n D v (i + 1) = Av n D v i ∪ Av n D v o := by
      ext j
      simp only [Av, hd, Finset.mem_insert, Finset.mem_union, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨rfl | h | h, hj⟩
        · exact absurd hj hv
        · exact Or.inl ⟨h, hj⟩
        · exact Or.inr ⟨h, hj⟩
      · rintro (⟨h, hj⟩ | ⟨h, hj⟩)
        · exact ⟨Or.inr (Or.inl h), hj⟩
        · exact ⟨Or.inr (Or.inr h), hj⟩
    have hor : Av n D v i = ∅ ∨ Av n D v o = ∅ := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨x, hx, hux⟩, ⟨y, hy, huy⟩⟩ := hcon
      exact hv (hloc x hx y hy v hux huy)
    rw [hA]
    rcases hor with h | h
    · rw [h, Set.empty_union]; exact ih2
    · rw [h, Set.union_empty]; exact ih1

/-- Local conditions give connected occurrence sets. -/
lemma Lay.eoc_of_loc (L : Lay n D) (hloc : ∀ j, j < nodeCount D → Loc n D j) (v : ℕ) :
    ∀ i, i < nodeCount D → EoC D (Av n D v i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero =>
      by_cases hv : v ∈ bagN n D 0
      · right
        have : Av n D v 0 = {0} := by
          ext j; simp only [Av, desc_zero, Finset.mem_singleton, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          constructor
          · exact fun h => h.1
          · rintro rfl; exact ⟨rfl, hv⟩
        rw [this]; exact ConnOn.singleton _
      · left
        ext j; simp only [Av, desc_zero, Finset.mem_singleton, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        rintro rfl; exact hv
    | succ i =>
      have ih' := ih i (by omega) (by omega)
      have hl := hloc (i + 1) hi
      rcases L.node hi with ⟨h1, h2, h3⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, hv, hn⟩ | ⟨hkd, ho, hbe⟩
      · left
        ext j
        simp only [Av, desc_leaf h1 h2 h3, Finset.mem_singleton, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro rfl; rw [bagN_succ_leaf h1 h2 h3]; simp
      · refine L.eoc_unary (desc_intro hkd) ((L.isChild_succ_unary (Or.inl hkd) hi).2 rfl) ?_ ih'
        intro hvm
        rw [bagN_succ_intro hkd hv] at hvm
        rcases Finset.mem_insert.1 hvm with rfl | h
        · right
          have := hl.1 hkd
          simpa using this
        · exact Or.inl h
      · refine L.eoc_unary (desc_forget hkd) ((L.isChild_succ_unary (Or.inr hkd) hi).2 rfl) ?_ ih'
        intro hvm
        rw [bagN_succ_forget hkd hv] at hvm
        exact Or.inl (Finset.mem_of_mem_erase hvm)
      · refine L.eoc_join (desc_join hkd ho) ((L.isChild_succ_join hkd hi).2 (Or.inl rfl))
          ((L.isChild_succ_join hkd hi).2 (Or.inr rfl)) hbe (bagN_succ_join hkd) ?_ ih'
          (ih _ (by omega) (by omega))
        intro x hx y hy u hux huy
        exact (hl.2 hkd) x (by simpa using hx) y hy u hux huy

/-- Connected occurrence sets, given the local conditions and that the vertex occurs. -/
lemma Lay.connOn_of_loc (L : Lay n D) (hloc : ∀ j, j < nodeCount D → Loc n D j) {v : ℕ}
    (hocc : ∃ j, j < nodeCount D ∧ v ∈ bagN n D j) : ConnOn D (Sv n D v) := by
  have hS : Sv n D v = Av n D v (nodeCount D - 1) := by
    ext j
    simp only [Sv, Av, Set.mem_ofPred_eq, L.desc_full, Finset.mem_range]
  rw [hS]
  rcases L.eoc_of_loc hloc v (nodeCount D - 1) (by have := L.nonempty; omega) with h | h
  · obtain ⟨j, hj, hvj⟩ := hocc
    have : j ∈ Av n D v (nodeCount D - 1) := by
      rw [← hS]; exact ⟨hj, hvj⟩
    rw [h] at this; exact absurd this (Set.notMem_empty _)
  · exact h

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordGraph` -/

section
/-!
# The word tree as a `SimpleGraph` (T2)

* `Lay.isTree`: `treeGraph D` is a tree (each node but the last has one parent, which is later; count the edges);
* `Lay.connected_iff`: connectedness of an induced subgraph of `treeGraph D` is `ConnOn`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma treeGraph_adj (a b : Fin (nodeCount D)) :
    (treeGraph D).Adj a b ↔ a ≠ b ∧ Adj' D a.val b.val := Iff.rfl

/-- Every node reaches the last one. -/
lemma Lay.reachable_last (L : Lay n D) (x : Fin (nodeCount D)) :
    (treeGraph D).Reachable x ⟨nodeCount D - 1, by have := L.nonempty; omega⟩ := by
  have hN := L.nonempty
  obtain ⟨x, hx⟩ := x
  obtain ⟨k, hk⟩ : ∃ k, nodeCount D - 1 - x = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases hxl : x = nodeCount D - 1
    · subst hxl; exact SimpleGraph.Reachable.refl _
    · have hx1 : x + 1 < nodeCount D := by omega
      obtain ⟨p, hp, -⟩ := L.parent x hx1
      have hlt := L.isChild_lt hp
      have hr := ih (nodeCount D - 1 - p) (by omega) p hlt.2 rfl
      have hadj : (treeGraph D).Adj ⟨x, hx⟩ ⟨p, hlt.2⟩ :=
        ⟨fun h => by have := Fin.mk.inj h; omega, Or.inl hp⟩
      exact hadj.reachable.trans hr

lemma Lay.isTree (L : Lay n D) : (treeGraph D).IsTree := by
  classical
  have hN := L.nonempty
  rw [SimpleGraph.isTree_iff_connected_and_card]
  have hconn : (treeGraph D).Connected := by
    have : Nonempty (Fin (nodeCount D)) := ⟨⟨0, hN⟩⟩
    exact SimpleGraph.Connected.mk (fun x y => (L.reachable_last x).trans (L.reachable_last y).symm)
  refine ⟨hconn, le_antisymm ?_ ?_⟩
  · -- at most `N - 1` edges: every edge is `{c, parent c}`
    have hpar : ∀ c : Fin (nodeCount D - 1), ∃ p : Fin (nodeCount D), IsChild D c.val p.val := by
      intro c
      obtain ⟨p, hp, -⟩ := L.parent c.val (by omega)
      exact ⟨⟨p, (L.isChild_lt hp).2⟩, hp⟩
    choose par hpar using hpar
    have hsub : (treeGraph D).edgeSet ⊆
        (fun c : Fin (nodeCount D - 1) => s(((⟨c.val, by omega⟩ : Fin (nodeCount D))), par c)) '' Set.univ := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he
        obtain ⟨-, h | h⟩ := he
        · have hlt := L.isChild_lt h
          refine ⟨⟨a.val, by omega⟩, Set.mem_univ _, ?_⟩
          have := L.parent_unique (hpar ⟨a.val, by omega⟩) h
          have hb : par ⟨a.val, by omega⟩ = b := Fin.ext this
          simp [hb]
        · have hlt := L.isChild_lt h
          refine ⟨⟨b.val, by omega⟩, Set.mem_univ _, ?_⟩
          have := L.parent_unique (hpar ⟨b.val, by omega⟩) h
          have hb : par ⟨b.val, by omega⟩ = a := Fin.ext this
          simp [hb, Sym2.eq_swap]
    have h1 : Set.ncard (treeGraph D).edgeSet ≤ nodeCount D - 1 := by
      calc Set.ncard (treeGraph D).edgeSet
          ≤ Set.ncard ((fun c : Fin (nodeCount D - 1) =>
              s(((⟨c.val, by omega⟩ : Fin (nodeCount D))), par c)) '' Set.univ) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ Set.ncard (Set.univ : Set (Fin (nodeCount D - 1))) := Set.ncard_image_le (Set.toFinite _)
        _ = nodeCount D - 1 := by simp
    have : Nat.card (treeGraph D).edgeSet = Set.ncard (treeGraph D).edgeSet := rfl
    rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  · have := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card (α := Fin (nodeCount D)), Fintype.card_fin] at this
    simpa using this

lemma mem_bagN_fin {D : List ℕ} {i : ℕ} (v : Fin n) : v.val ∈ bagN n D i ↔ v ∈ bagAt n D i := by
  rw [mem_bagN]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

lemma Lay.connected_iff (L : Lay n D) (S : Set ℕ) (hS : ∀ j ∈ S, j < nodeCount D) :
    ((treeGraph D).induce {i : Fin (nodeCount D) | i.val ∈ S}).Connected ↔ ConnOn D S := by
  constructor
  · intro h
    refine ⟨?_, fun x hx y hy => ?_⟩
    · obtain ⟨⟨i, hi⟩⟩ := h.nonempty
      exact ⟨i.val, hi⟩
    · have hr := h.preconnected ⟨⟨x, hS x hx⟩, hx⟩ ⟨⟨y, hS y hy⟩, hy⟩
      rw [SimpleGraph.reachable_iff_reflTransGen] at hr
      exact Relation.ReflTransGen.lift (fun a : {i : Fin (nodeCount D) // i.val ∈ S} => a.1.val)
        (fun a b hab => ⟨a.2, b.2, ((treeGraph_adj a.1 b.1).1 hab).2⟩) _ _ hr
  · rintro ⟨⟨x0, hx0⟩, hc⟩
    have : Nonempty ↥{i : Fin (nodeCount D) | i.val ∈ S} := ⟨⟨⟨x0, hS x0 hx0⟩, hx0⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨⟨x, hxN⟩, hxS⟩ ⟨⟨y, hyN⟩, hyS⟩
    have hpath := hc x hxS y hyS
    have key : ∀ b, Relation.ReflTransGen (RelOn D S) x b →
        ∃ hb : b ∈ S, (SimpleGraph.induce {i : Fin (nodeCount D) | i.val ∈ S} (treeGraph D)).Reachable
          ⟨⟨x, hxN⟩, hxS⟩ ⟨⟨b, hS b hb⟩, hb⟩ := by
      intro b hb
      induction hb with
      | refl => exact ⟨hxS, SimpleGraph.Reachable.refl _⟩
      | tail hab hbc ih =>
        rename_i b c
        obtain ⟨hb, hreach⟩ := ih
        have hne : (⟨b, hS b hb⟩ : Fin (nodeCount D)) ≠ ⟨c, hS c hbc.2.1⟩ := by
          intro h
          have := Fin.mk.inj h
          rcases hbc.2.2 with h' | h' <;> have := (L.isChild_lt h').1 <;> omega
        have hadj : (SimpleGraph.induce {i : Fin (nodeCount D) | i.val ∈ S} (treeGraph D)).Adj
            ⟨⟨b, hS b hb⟩, hb⟩ ⟨⟨c, hS c hbc.2.1⟩, hbc.2.1⟩ := ⟨hne, hbc.2.2⟩
        exact ⟨hbc.2.1, hreach.trans hadj.reachable⟩
    exact (key y hpath).2

lemma Lay.connected_bagAt_iff (L : Lay n D) (v : Fin n) :
    ((treeGraph D).induce {i : Fin (nodeCount D) | v ∈ bagAt n D i}).Connected ↔
      ConnOn D (Sv n D v.val) := by
  have hset : {i : Fin (nodeCount D) | v ∈ bagAt n D i} =
      {i : Fin (nodeCount D) | i.val ∈ Sv n D v.val} := by
    ext i
    simp [Sv, mem_bagN_fin]
  rw [hset]
  exact L.connected_iff _ (fun j hj => hj.1)

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.WordBridge` -/

section
/-!
# `NiceDecomposition` of a word in arbitrary layout ↔ `IsNiceTD` of the tree it reads (T2)

For a word with `Lay n D` (this is the layout half of `NiceDecomposition`), the remaining fields of
`NiceDecomposition G w D` hold iff `ofWord D (N - 1)` is a nice tree decomposition of `G` of width `≤ w`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

/-- Vertices of the tree are the vertices of the bags. -/
lemma Lay.mem_vs_iff (L : Lay n D) (u : ℕ) :
    u ∈ (ofWord D (nodeCount D - 1)).vs ↔ ∃ j, j < nodeCount D ∧ u ∈ bagN n D j := by
  have hN := L.nonempty
  rw [L.mem_vs_ofWord _ (by omega), L.desc_full]
  simp only [Finset.mem_range]

/-- The bags of the tree are the bags `bagN` of the nodes. -/
lemma Lay.mem_bs_iff (L : Lay n D) (X : Finset ℕ) :
    X ∈ (ofWord D (nodeCount D - 1)).bs ↔ ∃ j, j < nodeCount D ∧ X = bagN n D j := by
  have hN := L.nonempty
  rw [L.mem_bs_ofWord _ (by omega), L.desc_full]
  simp only [Finset.mem_range]

lemma card_bagN (n : ℕ) (D : List ℕ) (i : ℕ) : (bagN n D i).card = (bagAt n D i).card := by
  simp [bagN]

/-- **A word with the layout conditions whose tree is a nice tree decomposition is a `NiceDecomposition`.** -/
theorem Lay.niceDecomposition_of_isNiceTD (L : Lay n D) {G : SimpleGraph (Fin n)} {w : ℕ}
    (h : (ofWord D (nodeCount D - 1)).IsNiceTD (liftGraph G) (Finset.range n) w) :
    NiceDecomposition G w D := by
  have hN := L.nonempty
  obtain ⟨hwf, hTD, hwd⟩ := h
  have hverts : (ofWord D (nodeCount D - 1)).vs = Finset.range n := hTD.verts_eq
  have hcov : ∀ v : Fin n, ∃ i, i < nodeCount D ∧ v ∈ bagAt n D i := by
    intro v
    have : v.val ∈ (ofWord D (nodeCount D - 1)).vs := by rw [hverts]; exact Finset.mem_range.2 v.2
    obtain ⟨j, hj, hv⟩ := (L.mem_vs_iff _).1 this
    exact ⟨j, hj, (mem_bagN_fin v).1 hv⟩
  have hloc : ∀ j, j < nodeCount D → Loc n D j := by
    have hn := (NT.conn_toRT_iff hwf).1 hTD.conn
    rw [L.nconn_ofWord _ (by omega), L.desc_full] at hn
    exact fun j hj => hn j (Finset.mem_range.2 hj)
  refine ⟨L.length_eq, L.nonempty, L.shape, L.parent, L.isTree, hcov, ?_, ?_, ?_⟩
  · intro u v huv
    have hadj : (liftGraph (n := n) G).Adj u.val v.val :=
      ⟨fun h => G.ne_of_adj huv (Fin.ext h), u, v, huv, rfl, rfl⟩
    obtain ⟨X, hX, hu, hv⟩ := hTD.edges u.val v.val hadj (Finset.mem_range.2 u.2) (Finset.mem_range.2 v.2)
    obtain ⟨j, hj, rfl⟩ := (L.mem_bs_iff X).1 hX
    exact ⟨j, hj, (mem_bagN_fin u).1 hu, (mem_bagN_fin v).1 hv⟩
  · intro v
    obtain ⟨j, hj, hvj⟩ := hcov v
    exact (L.connected_bagAt_iff v).2
      (L.connOn_of_loc hloc ⟨j, hj, (mem_bagN_fin v).2 hvj⟩)
  · intro i hi
    have := hwd (bagN n D i) ((L.mem_bs_iff _).2 ⟨i, hi, rfl⟩)
    rwa [card_bagN] at this

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.EncodeReads` -/

section
/-!
# The canonical word `NT.encode` (T2)

`Reads D b t`: the records of `D` from node `b` on are `NT.recs b t`.  `NT.encode t` reads `t` at `0`.
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

/-- The record of node `i`. -/
def recAt (D : List ℕ) (i : ℕ) : ℕ × ℕ × ℕ := (kind D i, vertex D i, other D i)

/-- The records of `D` from node `b` on are those of `t`. -/
def Reads (D : List ℕ) (b : ℕ) (t : NT) : Prop :=
  ∀ j, j < t.size → recAt D (b + j) = (NT.recs b t).getD j (0, 0, 0)

lemma length_recs (t : NT) : ∀ b, (NT.recs b t).length = t.size := by
  induction t with
  | leaf => intro b; simp [NT.recs, NT.size]
  | intro v c ih => intro b; simp [NT.recs, NT.size, ih]
  | forget v c ih => intro b; simp [NT.recs, NT.size, ih]
  | join x y ihx ihy => intro b; simp [NT.recs, NT.size, ihx, ihy]; omega

lemma recs_join (b : ℕ) (x y : NT) :
    NT.recs b (NT.join x y) = NT.recs b y ++ NT.recs (b + y.size) x ++ [(3, 0, b + y.size - 1)] := by
  simp only [NT.recs, length_recs]

lemma size_pos (t : NT) : 0 < t.size := by
  cases t <;> simp [NT.size]

lemma Reads.leaf {D : List ℕ} {b : ℕ} (h : Reads D b NT.leaf) : recAt D b = (0, 0, 0) := by
  simpa [NT.recs, NT.size] using h 0 (by simp [NT.size])

lemma Reads.intro {D : List ℕ} {b v : ℕ} {c : NT} (h : Reads D b (NT.intro v c)) :
    Reads D b c ∧ recAt D (b + c.size) = (1, v, 0) := by
  constructor
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append _ _ _ _ (by rw [length_recs]; exact hj)]
  · have := h c.size (by simp [NT.size])
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append_right _ _ _ _ (by rw [length_recs])]
    simp [length_recs]

lemma Reads.forget {D : List ℕ} {b v : ℕ} {c : NT} (h : Reads D b (NT.forget v c)) :
    Reads D b c ∧ recAt D (b + c.size) = (2, v, 0) := by
  constructor
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append _ _ _ _ (by rw [length_recs]; exact hj)]
  · have := h c.size (by simp [NT.size])
    rw [this]
    simp only [NT.recs]
    rw [List.getD_append_right _ _ _ _ (by rw [length_recs])]
    simp [length_recs]

lemma Reads.join {D : List ℕ} {b : ℕ} {x y : NT} (h : Reads D b (NT.join x y)) :
    Reads D b y ∧ Reads D (b + y.size) x ∧
      recAt D (b + y.size + x.size) = (3, 0, b + y.size - 1) := by
  have hx := size_pos x
  have hy := size_pos y
  have hly := length_recs y b
  have hlx := length_recs x (b + y.size)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have := h j (by simp [NT.size]; omega)
    rw [this, recs_join, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  · intro j hj
    have := h (y.size + j) (by simp [NT.size]; omega)
    rw [← Nat.add_assoc] at this
    rw [this, recs_join, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega)]
    congr 2
    omega
  · have := h (y.size + x.size) (by simp [NT.size]; omega)
    rw [← Nat.add_assoc] at this
    rw [this, recs_join, List.append_assoc, List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have : y.size + x.size - (NT.recs b y).length - (NT.recs (b + y.size) x).length = 0 := by omega
    rw [this]; rfl

lemma flat_get (rs : List (ℕ × ℕ × ℕ)) : ∀ i, i < rs.length →
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i) 0 = (rs.getD i (0, 0, 0)).1 ∧
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i + 1) 0 = (rs.getD i (0, 0, 0)).2.1 ∧
    (rs.flatMap (fun r => [r.1, r.2.1, r.2.2])).getD (3 * i + 2) 0 = (rs.getD i (0, 0, 0)).2.2 := by
  induction rs with
  | nil => intro i hi; simp at hi
  | cons r rs ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      have := ih i (by simpa using hi)
      have e0 : 3 * (i + 1) = (3 * i) + 1 + 1 + 1 := by omega
      simp only [List.flatMap_cons, e0, List.cons_append, List.nil_append,
        Nat.add_assoc, List.getD_eq_getElem?_getD] at this ⊢
      simpa [Nat.add_assoc] using this

lemma nodeCount_encode (t : NT) : nodeCount t.encode = t.size := by
  simp [nodeCount, NT.encode, length_recs]

lemma length_encode (t : NT) : t.encode.length = 1 + 3 * t.size := by
  simp [NT.encode, length_recs]; omega

lemma reads_encode (t : NT) : Reads t.encode 0 t := by
  intro j hj
  have hlen : j < (NT.recs 0 t).length := by rw [length_recs]; exact hj
  obtain ⟨h0, h1, h2⟩ := flat_get (NT.recs 0 t) j hlen
  simp only [recAt, kind, vertex, other, NT.encode, Nat.zero_add]
  have e1 : 1 + 3 * j = 3 * j + 1 := by omega
  have e2 : 2 + 3 * j = 3 * j + 1 + 1 := by omega
  have e3 : 3 + 3 * j = 3 * j + 1 + 1 + 1 := by omega
  rw [e1, e2, e3]
  simp only [List.getD_cons_succ]
  rw [h0, h1, h2]

end Word

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Trees.Bridge2` -/

section
/-!
# Bridge 2: nice trees and `GraphWords.NiceDecomposition` (T2)
-/

namespace Lax117284Proofs.Treewidth.Trees

namespace Word

open Lax117284.GraphWords

variable {n : ℕ} {D : List ℕ}

lemma recAt_eq {D : List ℕ} {i k v o : ℕ} (h : recAt D i = (k, v, o)) :
    kind D i = k ∧ vertex D i = v ∧ other D i = o := by
  simp only [recAt, Prod.mk.injEq] at h; exact h

/-- The bag at the root of the block of `t` is the bag of `t`. -/
lemma bagN_root {n : ℕ} {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → t.Wf →
    (∀ u ∈ t.vs, u < n) → bagN n D (b + t.size - 1) = t.bag := by
  intro t
  induction t with
  | leaf =>
    intro b h _ _
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    simp only [NT.size, NT.bag_leaf]
    cases b with
    | zero => simp [bagN_zero]
    | succ b =>
      have : b + 1 + 1 - 1 = b + 1 := by omega
      rw [this]
      exact bagN_succ_leaf (by omega) (by omega) (by omega)
  | intro v c ih =>
    intro b h hw hlt
    obtain ⟨hc, hrec⟩ := h.intro
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hvn : v < n := hlt v (by simp [NT.vs_intro])
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_intro, hu])
    have := ih b hc hw.2 hcl
    have hidx : b + (NT.intro v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_intro hk (hv ▸ hvn), this, hv, NT.bag_intro]
  | forget v c ih =>
    intro b h hw hlt
    obtain ⟨hc, hrec⟩ := h.forget
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hvn : v < n := hlt v (by
      have := hw.1
      have := NT.bag_subset_vs c this
      simp [NT.vs_forget, this])
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_forget, hu])
    have := ih b hc hw.2 hcl
    have hidx : b + (NT.forget v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_forget hk (hv ▸ hvn), this, hv, NT.bag_forget]
  | join x y ihx ihy =>
    intro b h hw hlt
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    obtain ⟨i, hi⟩ : ∃ i, b + y.size + x.size = i + 1 := ⟨b + y.size + x.size - 1, by omega⟩
    rw [hi] at hrec
    obtain ⟨hk, -, -⟩ := recAt_eq hrec
    have hxl : ∀ u ∈ x.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    have := ihx (b + y.size) hx hw.2.1 hxl
    have hidx : b + (NT.join x y).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + y.size + x.size - 1 = i := by omega
    rw [hi'] at this
    rw [hidx, bagN_succ_join hk, this, NT.bag_join]

/-- The shape condition at node `i` (as in `NiceDecomposition.shape`). -/
abbrev ShapeAt (n : ℕ) (D : List ℕ) (i : ℕ) : Prop :=
  kind D i = 0 ∨
  (0 < i ∧ kind D i = 1 ∧ vertex D i < n ∧
    ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∉ bagAt n D (i - 1)) ∨
  (0 < i ∧ kind D i = 2 ∧ vertex D i < n ∧
    ∀ h : vertex D i < n, (⟨vertex D i, h⟩ : Fin n) ∈ bagAt n D (i - 1)) ∨
  (0 < i ∧ kind D i = 3 ∧ other D i + 1 < i ∧
    bagAt n D (other D i) = bagAt n D (i - 1))

lemma fin_mem_bagAt {D : List ℕ} {i u : ℕ} (h : u < n) :
    (⟨u, h⟩ : Fin n) ∈ bagAt n D i ↔ u ∈ bagN n D i := (mem_bagN_fin (⟨u, h⟩ : Fin n)).symm

lemma bagAt_eq_of_bagN_eq {D : List ℕ} {i j : ℕ} (h : bagN n D i = bagN n D j) :
    bagAt n D i = bagAt n D j :=
  Finset.map_injective Fin.valEmbedding h

lemma shape_of_reads {n : ℕ} {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → t.Wf →
    (∀ u ∈ t.vs, u < n) → ∀ j, b ≤ j → j < b + t.size → ShapeAt n D j := by
  intro t
  induction t with
  | leaf =>
    intro b h _ _ j hj1 hj2
    have hjb : j = b := by simp [NT.size] at hj2; omega
    subst hjb
    exact Or.inl (recAt_eq h.leaf).1
  | intro v c ih =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hc, hrec⟩ := h.intro
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_intro, hu])
    simp only [NT.size] at hj2
    by_cases hjc : j < b + c.size
    · exact ih b hc hw.2 hcl j hj1 hjc
    · have hjeq : j = b + c.size := by omega
      subst hjeq
      obtain ⟨hk, hv, -⟩ := recAt_eq hrec
      have hvn : v < n := hlt v (by simp [NT.vs_intro])
      have hroot := bagN_root c b hc hw.2 hcl
      right; left
      refine ⟨by have := size_pos c; omega, hk, hv ▸ hvn, fun h hmem => ?_⟩
      rw [fin_mem_bagAt h, hv] at hmem
      rw [hroot] at hmem
      exact hw.1 hmem
  | forget v c ih =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hc, hrec⟩ := h.forget
    have hcl : ∀ u ∈ c.vs, u < n := fun u hu => hlt u (by simp [NT.vs_forget, hu])
    simp only [NT.size] at hj2
    by_cases hjc : j < b + c.size
    · exact ih b hc hw.2 hcl j hj1 hjc
    · have hjeq : j = b + c.size := by omega
      subst hjeq
      obtain ⟨hk, hv, -⟩ := recAt_eq hrec
      have hvn : v < n := hcl v (NT.bag_subset_vs c hw.1)
      have hroot := bagN_root c b hc hw.2 hcl
      right; right; left
      refine ⟨by have := size_pos c; omega, hk, hv ▸ hvn, fun h => ?_⟩
      rw [fin_mem_bagAt h, hv, hroot]
      exact hw.1
  | join x y ihx ihy =>
    intro b h hw hlt j hj1 hj2
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    have hxl : ∀ u ∈ x.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    have hyl : ∀ u ∈ y.vs, u < n := fun u hu => hlt u (by simp [NT.vs_join, hu])
    simp only [NT.size] at hj2
    by_cases hjy : j < b + y.size
    · exact ihy b hy hw.2.2 hyl j hj1 hjy
    · by_cases hjx : j < b + y.size + x.size
      · exact ihx (b + y.size) hx hw.2.1 hxl j (by omega) hjx
      · have hjeq : j = b + y.size + x.size := by omega
        subst hjeq
        obtain ⟨hk, -, ho⟩ := recAt_eq hrec
        have hrx := bagN_root x (b + y.size) hx hw.2.1 hxl
        have hry := bagN_root y b hy hw.2.2 hyl
        right; right; right
        refine ⟨by omega, hk, by omega, ?_⟩
        apply bagAt_eq_of_bagN_eq
        rw [ho, hry, show b + y.size + x.size - 1 = (b + y.size) + x.size - 1 by omega, hrx]
        exact hw.1.symm

/-! ### parents in the canonical layout -/

/-- The parent relation of the block of `t` placed at `b` (child, parent). -/
def PC : ℕ → NT → ℕ → ℕ → Prop
  | _, NT.leaf, _, _ => False
  | b, NT.intro _ c, x, p => PC b c x p ∨ (p = b + c.size ∧ x + 1 = p)
  | b, NT.forget _ c, x, p => PC b c x p ∨ (p = b + c.size ∧ x + 1 = p)
  | b, NT.join x y, c, p => PC b y c p ∨ PC (b + y.size) x c p ∨
      (p = b + y.size + x.size ∧ (c + 1 = p ∨ c = b + y.size - 1))

lemma PC_bounds : ∀ (t : NT) (b c p : ℕ), PC b t c p → b ≤ c ∧ c < p ∧ p < b + t.size := by
  intro t
  induction t with
  | leaf => intro b c p h; exact h.elim
  | intro v c' ih =>
    intro b c p h
    have := size_pos c'
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | ⟨h1, h2⟩
    · have := ih b c p h; omega
    · omega
  | forget v c' ih =>
    intro b c p h
    have := size_pos c'
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | ⟨h1, h2⟩
    · have := ih b c p h; omega
    · omega
  | join x y ihx ihy =>
    intro b c p h
    have := size_pos x
    have := size_pos y
    simp only [PC] at h
    simp only [NT.size]
    rcases h with h | h | ⟨h1, h2 | h2⟩
    · have := ihy b c p h; omega
    · have := ihx (b + y.size) c p h; omega
    · omega
    · omega

lemma PC_existsUnique : ∀ (t : NT) (b c : ℕ), b ≤ c → c + 1 < b + t.size → ∃! p, PC b t c p := by
  intro t
  induction t with
  | leaf => intro b c h1 h2; simp [NT.size] at h2; omega
  | intro v c' ih =>
    intro b c h1 h2
    have := size_pos c'
    simp only [NT.size] at h2
    by_cases hc : c + 1 < b + c'.size
    · obtain ⟨p, hp, hu⟩ := ih b c h1 hc
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, hq2⟩
      · exact hu q hq
      · omega
    · refine ⟨b + c'.size, Or.inr ⟨rfl, by omega⟩, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, -⟩
      · have := PC_bounds c' b c q hq; omega
      · exact hq1
  | forget v c' ih =>
    intro b c h1 h2
    have := size_pos c'
    simp only [NT.size] at h2
    by_cases hc : c + 1 < b + c'.size
    · obtain ⟨p, hp, hu⟩ := ih b c h1 hc
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, hq2⟩
      · exact hu q hq
      · omega
    · refine ⟨b + c'.size, Or.inr ⟨rfl, by omega⟩, fun q hq => ?_⟩
      rcases hq with hq | ⟨hq1, -⟩
      · have := PC_bounds c' b c q hq; omega
      · exact hq1
  | join x y ihx ihy =>
    intro b c h1 h2
    have hxs := size_pos x
    have hys := size_pos y
    simp only [NT.size] at h2
    by_cases hcy : c + 1 < b + y.size
    · obtain ⟨p, hp, hu⟩ := ihy b c h1 hcy
      refine ⟨p, Or.inl hp, fun q hq => ?_⟩
      rcases hq with hq | hq | ⟨hq1, hq2 | hq2⟩
      · exact hu q hq
      · have := PC_bounds x (b + y.size) c q hq; omega
      · omega
      · omega
    · by_cases hcx : c + 1 < b + y.size + x.size
      · by_cases hcy' : c + 1 = b + y.size
        · refine ⟨b + y.size + x.size, Or.inr (Or.inr ⟨rfl, Or.inr (by omega)⟩), fun q hq => ?_⟩
          rcases hq with hq | hq | ⟨hq1, -⟩
          · have := PC_bounds y b c q hq; omega
          · have := PC_bounds x (b + y.size) c q hq; omega
          · exact hq1
        · obtain ⟨p, hp, hu⟩ := ihx (b + y.size) c (by omega) (by omega)
          refine ⟨p, Or.inr (Or.inl hp), fun q hq => ?_⟩
          rcases hq with hq | hq | ⟨hq1, hq2 | hq2⟩
          · have := PC_bounds y b c q hq; omega
          · exact hu q hq
          · omega
          · omega
      · refine ⟨b + y.size + x.size, Or.inr (Or.inr ⟨rfl, Or.inl (by omega)⟩), fun q hq => ?_⟩
        rcases hq with hq | hq | ⟨hq1, -⟩
        · have := PC_bounds y b c q hq; omega
        · have := PC_bounds x (b + y.size) c q hq; omega
        · exact hq1

lemma isChild_iff_PC {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → b + t.size ≤ nodeCount D →
    ∀ c p, b ≤ p → p < b + t.size → (IsChild D c p ↔ PC b t c p) := by
  intro t
  induction t with
  | leaf =>
    intro b h hN c p hp1 hp2
    have hpb : p = b := by simp [NT.size] at hp2; omega
    subst hpb
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    simp only [PC, iff_false]
    rintro ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ <;> omega
  | intro v c' ih =>
    intro b h hN c p hp1 hp2
    obtain ⟨hc, hrec⟩ := h.intro
    have hs := size_pos c'
    simp only [NT.size] at hp2 hN
    by_cases hpc : p < b + c'.size
    · rw [ih b hc (by omega) c p hp1 hpc]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · have hpeq : p = b + c'.size := by omega
      subst hpeq
      obtain ⟨hk, -, -⟩ := recAt_eq hrec
      rw [PC]
      constructor
      · rintro ⟨-, ⟨-, h'⟩ | ⟨h', -⟩⟩
        · exact Or.inr ⟨rfl, h'⟩
        · omega
      · rintro (h' | ⟨-, h'⟩)
        · have := (PC_bounds c' b c _ h'); omega
        · exact ⟨by omega, Or.inl ⟨Or.inl hk, h'⟩⟩
  | forget v c' ih =>
    intro b h hN c p hp1 hp2
    obtain ⟨hc, hrec⟩ := h.forget
    have hs := size_pos c'
    simp only [NT.size] at hp2 hN
    by_cases hpc : p < b + c'.size
    · rw [ih b hc (by omega) c p hp1 hpc]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | ⟨h', -⟩)
        · exact h'
        · omega
    · have hpeq : p = b + c'.size := by omega
      subst hpeq
      obtain ⟨hk, -, -⟩ := recAt_eq hrec
      rw [PC]
      constructor
      · rintro ⟨-, ⟨-, h'⟩ | ⟨h', -⟩⟩
        · exact Or.inr ⟨rfl, h'⟩
        · omega
      · rintro (h' | ⟨-, h'⟩)
        · have := (PC_bounds c' b c _ h'); omega
        · exact ⟨by omega, Or.inl ⟨Or.inr hk, h'⟩⟩
  | join x y ihx ihy =>
    intro b h hN c p hp1 hp2
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    simp only [NT.size] at hp2 hN
    by_cases hpy : p < b + y.size
    · rw [ihy b hy (by omega) c p hp1 hpy]
      rw [PC]
      constructor
      · exact Or.inl
      · rintro (h' | h' | ⟨h', -⟩)
        · exact h'
        · have := PC_bounds x (b + y.size) c p h'; omega
        · omega
    · by_cases hpx : p < b + y.size + x.size
      · rw [ihx (b + y.size) hx (by omega) c p (by omega) hpx]
        rw [PC]
        constructor
        · exact fun h' => Or.inr (Or.inl h')
        · rintro (h' | h' | ⟨h', -⟩)
          · have := PC_bounds y b c p h'; omega
          · exact h'
          · omega
      · have hpeq : p = b + y.size + x.size := by omega
        subst hpeq
        obtain ⟨hk, -, ho⟩ := recAt_eq hrec
        rw [PC]
        constructor
        · rintro ⟨-, ⟨h', -⟩ | ⟨-, h'⟩⟩
          · omega
          · exact Or.inr (Or.inr ⟨rfl, by rw [ho] at h'; exact h'⟩)
        · rintro (h' | h' | ⟨-, h'⟩)
          · have := PC_bounds y b c _ h'; omega
          · have := PC_bounds x (b + y.size) c _ h'; omega
          · exact ⟨by omega, Or.inr ⟨hk, by rw [ho]; exact h'⟩⟩

/-- Reading the canonical layout back gives the tree. -/
lemma ofWord_of_reads {D : List ℕ} : ∀ (t : NT) (b : ℕ), Reads D b t → ofWord D (b + t.size - 1) = t := by
  intro t
  induction t with
  | leaf =>
    intro b h
    obtain ⟨hk, -, -⟩ := recAt_eq h.leaf
    cases b with
    | zero => simp [NT.size, ofWord_zero]
    | succ b =>
      have : b + 1 + NT.leaf.size - 1 = b + 1 := by simp [NT.size]
      rw [this]
      exact ofWord_leaf (by omega) (by omega) (by omega)
  | intro v c ih =>
    intro b h
    obtain ⟨hc, hrec⟩ := h.intro
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hidx : b + (NT.intro v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    have := ih b hc
    rw [hi'] at this
    rw [hidx, ofWord_intro hk, hv, this]
  | forget v c ih =>
    intro b h
    obtain ⟨hc, hrec⟩ := h.forget
    obtain ⟨i, hi⟩ : ∃ i, b + c.size = i + 1 := ⟨b + c.size - 1, by have := size_pos c; omega⟩
    rw [hi] at hrec
    obtain ⟨hk, hv, -⟩ := recAt_eq hrec
    have hidx : b + (NT.forget v c).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + c.size - 1 = i := by omega
    have := ih b hc
    rw [hi'] at this
    rw [hidx, ofWord_forget hk, hv, this]
  | join x y ihx ihy =>
    intro b h
    obtain ⟨hy, hx, hrec⟩ := h.join
    have hxs := size_pos x
    have hys := size_pos y
    obtain ⟨i, hi⟩ : ∃ i, b + y.size + x.size = i + 1 := ⟨b + y.size + x.size - 1, by omega⟩
    rw [hi] at hrec
    obtain ⟨hk, -, ho⟩ := recAt_eq hrec
    have hidx : b + (NT.join x y).size - 1 = i + 1 := by simp [NT.size]; omega
    have hi' : b + y.size + x.size - 1 = i := by omega
    have h1 := ihx (b + y.size) hx
    rw [hi'] at h1
    have h2 := ihy b hy
    rw [hidx, ofWord_join hk (by omega), ho, h1, h2]

/-- The layout half of `NiceDecomposition` for the canonical word. -/
theorem lay_encode {n : ℕ} {t : NT} (hw : t.Wf) (hlt : ∀ u ∈ t.vs, u < n) : Lay n t.encode where
  length_eq := by rw [nodeCount_encode]; exact length_encode t
  nonempty := by rw [nodeCount_encode]; exact size_pos t
  shape := fun i hi => by
    rw [nodeCount_encode] at hi
    exact shape_of_reads t 0 (reads_encode t) hw hlt i (Nat.zero_le _) (by omega)
  parent := fun c hc => by
    rw [nodeCount_encode] at hc
    obtain ⟨p, hp, hu⟩ := PC_existsUnique t 0 c (Nat.zero_le _) (by omega)
    have hN : 0 + t.size ≤ nodeCount t.encode := by rw [nodeCount_encode]; omega
    have hpb := PC_bounds t 0 c p hp
    refine ⟨p, (isChild_iff_PC t 0 (reads_encode t) hN c p (Nat.zero_le _) hpb.2.2).2 hp, fun q hq => ?_⟩
    have hqN := hq.1
    rw [nodeCount_encode] at hqN
    exact hu q ((isChild_iff_PC t 0 (reads_encode t) hN c q (Nat.zero_le _) (by omega)).1 hq)

theorem ofWord_encode (t : NT) : ofWord t.encode (nodeCount t.encode - 1) = t := by
  rw [nodeCount_encode]
  simpa using ofWord_of_reads t 0 (reads_encode t)

end Word

open Word Lax117284.GraphWords in
/-- **Bridge 2 (word side), encode.**  A nice tree decomposition of `G` of width `≤ w` is written as a
`NiceDecomposition` word.  (Used for the *output* of the algorithm.) -/
theorem niceDecomposition_encode {n : ℕ} {G : SimpleGraph (Fin n)} {w : ℕ} {t : NT}
    (h : t.IsNiceTD (liftGraph G) (Finset.range n) w) : NiceDecomposition G w t.encode := by
  have hlt : ∀ u ∈ t.vs, u < n := fun u hu => by
    have : t.vs = Finset.range n := h.2.1.verts_eq
    rw [this] at hu; exact Finset.mem_range.1 hu
  have L := lay_encode h.1 hlt
  refine L.niceDecomposition_of_isNiceTD ?_
  rw [ofWord_encode]
  exact h

end Lax117284Proofs.Treewidth.Trees

end

/-! ### `Lax117284Proofs.Treewidth.Wrap.Decompose` -/

section
/-!
# The vertex-by-vertex wrapper (C8a)

* `hasTW_mono`  : `HasTW` is monotone under induced subgraphs;
* `Adj.SymmOn`  : the symmetry hypothesis on adjacency that the tables need (see `Wrap/NOTES.md`);
* `ImproveSpec adj W` : the conclusion of `improve_correct` for all vertex sets `U ⊆ W` (an explicit hypothesis, so
  that the wrapper is proved independently of the tables);
* `decompose_correct`, `decompose_words` : the wrapper's specification on `Adj` / on graphs on `Fin n`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Trees Lax117284Proofs.Treewidth.Trees.NT

/-- The adjacency function is symmetric on the vertex set `W`. -/
def Adj.SymmOn (adj : Adj) (W : Finset ℕ) : Prop := ∀ u ∈ W, ∀ v ∈ W, adj u v = adj v u

theorem hasTW_mono {adj : Adj} {U U' : Finset ℕ} {k : ℕ} (h : U' ⊆ U) : HasTW adj U k → HasTW adj U' k := by
  rintro ⟨t, htd, hw⟩
  refine ⟨t.restrict U', ?_, hw.restrict U'⟩
  have := htd.restrict U'
  rwa [Finset.inter_eq_right.2 h] at this

theorem hasTW_of_isNiceTD {adj : Adj} {U : Finset ℕ} {nt : NT} {k : ℕ} (h : nt.IsNiceTD adj.graph U k) :
    HasTW adj U k := ⟨nt.toRT, h.2.1, h.2.2⟩

theorem hasTW_empty (adj : Adj) (k : ℕ) : HasTW adj ∅ k :=
  hasTW_of_isNiceTD (nt := .leaf) (k := k)
    ⟨trivial, ⟨rfl, fun u v _ hu _ => absurd hu (by simp), by simp [NT.toRT, RT.Conn, RT.ConnL]⟩,
      by intro X hX; simp [NT.toRT, RT.bags, RT.bagsL] at hX; simp [hX]⟩

/-- The conclusion of `improve_correct`, for all vertex sets inside `W`: an explicit hypothesis of the wrapper. -/
def ImproveSpec (adj : Adj) (W : Finset ℕ) : Prop :=
  ∀ (U : Finset ℕ) (nt : NT) (l k : ℕ), U ⊆ W → nt.IsNiceTD adj.graph U l →
    (improve adj k nt = none ↔ ¬ HasTW adj U k) ∧ (∀ t', improve adj k nt = some t' → t'.IsNiceTD adj.graph U k)

/-- The graph `adj.graph` restricted to `range n` is the graph of `G` when `adj` encodes `G`. -/
theorem isTD_congr {G G' : SimpleGraph ℕ} {U : Finset ℕ} {t : RT} (h : ∀ u ∈ U, ∀ v ∈ U, G.Adj u v ↔ G'.Adj u v) :
    t.IsTD G U ↔ t.IsTD G' U :=
  ⟨fun ht => ⟨ht.verts_eq, fun u v huv hu hv => ht.edges u v ((h u hu v hv).2 huv) hu hv, ht.conn⟩,
   fun ht => ⟨ht.verts_eq, fun u v huv hu hv => ht.edges u v ((h u hu v hv).1 huv) hu hv, ht.conn⟩⟩

theorem graph_adj_of_encodes {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) {u v : ℕ} (hu : u < n) (hv : v < n) :
    adj.graph.Adj u v ↔ (liftGraph G).Adj u v := by
  rw [Adj.graph, SimpleGraph.fromRel_adj, liftGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · rcases (hadj ⟨u, hu⟩ ⟨v, hv⟩).1 h with h' | h'
      · exact ⟨_, _, h', rfl, rfl⟩
      · exact ⟨_, _, h'.symm, rfl, rfl⟩
    · rcases (hadj ⟨v, hv⟩ ⟨u, hu⟩).1 h with h' | h'
      · exact ⟨_, _, h'.symm, rfl, rfl⟩
      · exact ⟨_, _, h', rfl, rfl⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨fun e => hab.ne (Fin.ext e), Or.inl ((hadj a b).2 (Or.inl hab))⟩

/-- **The adjacency function obtained from the word of a graph is symmetric on `range n`.** -/
theorem symmOn_of_encodes {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) : adj.SymmOn (Finset.range n) := by
  intro u hu v hv
  have hu' := Finset.mem_range.1 hu
  have hv' := Finset.mem_range.1 hv
  have := hadj ⟨u, hu'⟩ ⟨v, hv'⟩
  have := hadj ⟨v, hv'⟩ ⟨u, hu'⟩
  rw [Bool.eq_iff_iff]
  simp only at *
  rw [hadj ⟨u, hu'⟩ ⟨v, hv'⟩, hadj ⟨v, hv'⟩ ⟨u, hu'⟩]
  exact or_comm

theorem hasTW_iff_hasTreewidthAtMost {n : ℕ} {G : SimpleGraph (Fin n)} {adj : Adj}
    (hadj : ∀ u v : Fin n, adj u.val v.val = true ↔ G.Adj u v ∨ G.Adj v u) (k : ℕ) :
    HasTW adj (Finset.range n) k ↔ Lax228581.Treewidth.HasTreewidthAtMost G k := by
  rw [hasTreewidthAtMost_iff_rt]
  have hcong : ∀ u ∈ Finset.range n, ∀ v ∈ Finset.range n, adj.graph.Adj u v ↔ (liftGraph G).Adj u v :=
    fun u hu v hv => graph_adj_of_encodes hadj (Finset.mem_range.1 hu) (Finset.mem_range.1 hv)
  constructor
  · rintro ⟨t, ht, hw⟩; exact ⟨t, (isTD_congr hcong).1 ht, hw⟩
  · rintro ⟨t, ht, hw⟩; exact ⟨t, (isTD_congr hcong).2 ht, hw⟩

end Lax117284Proofs.Treewidth.Chars

end
