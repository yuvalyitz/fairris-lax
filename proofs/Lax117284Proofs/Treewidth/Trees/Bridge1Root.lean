import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Logic.Relation

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
