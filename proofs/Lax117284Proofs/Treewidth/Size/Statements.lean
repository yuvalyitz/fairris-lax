import Lax117284Proofs.Treewidth.Size.RealC
import Lax117284Proofs.Treewidth.Size.Tables
import Lax117284Proofs.Treewidth.Size.PlanSize

/-! ### `Lax117284Proofs.Treewidth.Size.RealD` -/

section
/-!
# Size bounds (WP P1), part 10: sizes of real trees (3): merging, `realIntro`, `realJoin`

* `mergeChain_chsz_le` : merging two chains along a lattice path produces a chain of size `≤ chsz na + chsz nb`
  (at most `|na| + |nb| - 1` nodes, and each junk subtree is taken at most once: the first-visit indices along a
  monotone path are distinct);
* `mergeAR_nsz_le`, `mergeReal_size_le` : `(mergeReal B ta tb target).size ≤ ta.size + tb.size`;
* `realJoin_size_le`, `realIntro_size_le`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## lattice chains -/

theorem chain_len_le : ∀ (P : List (ℕ × ℕ)) (p : ℕ × ℕ), (p :: P).IsChain LStep →
    ∀ x ∈ (p :: P).getLast?, (p :: P).length + p.1 + p.2 ≤ x.1 + x.2 + 1
  | [], p, _, x, hx => by
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
    subst hx; simp; omega
  | q :: P, p, h, x, hx => by
    rw [List.isChain_cons_cons] at h
    have h1 := chain_len_le P q h.2 x (by simpa using hx)
    have h2 : p.1 + p.2 + 1 ≤ q.1 + q.2 := by
      rcases h.1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    simp only [List.length_cons] at h1 ⊢
    omega

/-- The path of an `IsLatticePath` has at most `|a| + |b|` elements (more precisely `|a|+|b|-1`). -/
theorem IsLatticePath.length_le {a b : List ℕ} {P : List (ℕ × ℕ)} (h : IsLatticePath a b P) :
    P.length ≤ (a.length - 1) + (b.length - 1) + 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  cases P with
  | nil => simp at h1
  | cons p P =>
    have hp : p = (0, 0) := by simpa using h1
    subst hp
    have := chain_len_le P (0, 0) h3 (a.length - 1, b.length - 1) h2
    simp only at this
    omega

/-! ## the junk budget along a path -/

def CNode.junkAt (ns : List CNode) (i : ℕ) : ℕ := (ns.map CNode.jsz).getD i 0

theorem jsz_getD (ns : List CNode) (i : ℕ) : (ns.getD i ⟨∅, []⟩).jsz = CNode.junkAt ns i := by
  unfold CNode.junkAt
  by_cases hi : i < ns.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [CNode.jsz]

/-- `A n = Σ_{i<n} junkAt ns i`. -/
def junkPre (ns : List CNode) (n : ℕ) : ℕ := ((ns.map CNode.jsz).take n).sum

theorem junkPre_succ (ns : List CNode) (n : ℕ) : junkPre ns (n + 1) = junkPre ns n + CNode.junkAt ns n := by
  unfold junkPre CNode.junkAt
  set l := ns.map CNode.jsz
  by_cases hn : n < l.length
  · rw [List.take_add_one, List.getElem?_eq_getElem hn]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    exact List.sum_take_succ l n hn
  · have h1 : l.take (n + 1) = l.take n := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [h1, List.getD_eq_default _ _ (by omega)]
    simp

theorem junkPre_le (ns : List CNode) (n : ℕ) : junkPre ns n ≤ (ns.map CNode.jsz).sum := by
  unfold junkPre
  have := congrArg List.sum (List.take_append_drop n (ns.map CNode.jsz))
  rw [List.sum_append] at this
  omega

theorem mergeChain_jsz (na nb : List CNode) : ∀ (P : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    (match prev with | none => P.IsChain LStep | some p => (p :: P).IsChain LStep) →
    ((mergeChain na nb prev P).map CNode.jsz).sum + junkPre na (prev.elim 0 (fun p => p.1 + 1)) +
      junkPre nb (prev.elim 0 (fun p => p.2 + 1)) ≤ (na.map CNode.jsz).sum + (nb.map CNode.jsz).sum
  | [], prev, _ => by
    have h1 := junkPre_le na (prev.elim 0 (fun p => p.1 + 1))
    have h2 := junkPre_le nb (prev.elim 0 (fun p => p.2 + 1))
    simp only [mergeChain, List.map_nil, List.sum_nil]
    omega
  | (i, j) :: rest, prev, hc => by
    have hrest : (match some (i, j) with | none => rest.IsChain LStep | some p => (p :: rest).IsChain LStep) := by
      rcases prev with _ | p
      · simpa using hc
      · simp only [] at hc ⊢
        rw [List.isChain_cons_cons] at hc
        exact hc.2
    have ih := mergeChain_jsz na nb rest (some (i, j)) hrest
    simp only [Option.elim] at ih
    have hA := junkPre_succ na i
    have hB := junkPre_succ nb j
    have hia := jsz_getD na i
    have hjb := jsz_getD nb j
    unfold CNode.jsz at hia hjb
    simp only [mergeChain, List.map_cons, List.sum_cons, CNode.jsz, List.map_append, List.sum_append]
    rcases prev with _ | ⟨p, q⟩
    · simp only [Option.elim, if_true, junkPre, List.take_zero, List.sum_nil]
      omega
    · simp only [] at hc
      rw [List.isChain_cons_cons] at hc
      have hL := hc.1
      simp only [LStep] at hL
      simp only [Option.elim]
      rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> simp at hia hjb ⊢ <;> omega

theorem mergeChain_length' (na nb : List CNode) : ∀ (P : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    (mergeChain na nb prev P).length = P.length
  | [], _ => by simp [mergeChain]
  | (i, j) :: rest, prev => by
    simp only [mergeChain, List.length_cons, mergeChain_length' na nb rest]

theorem mergeChain_chsz_le {na nb : List CNode} {P : List (ℕ × ℕ)}
    (hP : IsLatticePath (na.map fun n => n.bag.card) (nb.map fun n => n.bag.card) P) :
    chsz (mergeChain na nb none P) ≤ chsz na + chsz nb := by
  have hlen := hP.length_le
  simp only [List.length_map] at hlen
  have hne : P ≠ [] := by
    intro h; have := hP.1; simp [h] at this
  have h1 := mergeChain_jsz na nb P none (show P.IsChain LStep from hP.2.2)
  simp only [Option.elim, junkPre, List.take_zero, List.sum_nil, add_zero] at h1
  have hl : (mergeChain na nb none P).length = P.length := mergeChain_length' _ _ _ _
  have hpos : 0 < P.length := List.length_pos_iff.2 hne
  unfold chsz
  rw [hl]
  omega

mutual
theorem mergeAR_nsz_le_rec : ∀ (a b : AR) (c : CT) (r : AR), mergeAR a b c = some r → r.nsz ≤ a.nsz + b.nsz
  | .run S na ka, .run S' nb kb, .node S'' ty tk, r, h => by
    simp only [mergeAR] at h
    split at h
    · simp at h
    · rename_i path hp
      obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.1 h
      have h1 := mergeKids_nszL_le_rec ka kb tk ks hks
      have h2 := mergeChain_chsz_le (findPath_spec hp).1
      simp only [AR.nsz]
      omega
theorem mergeKids_nszL_le_rec : ∀ (ka kb : List AR) (tk : List CT) (ks : List AR),
    mergeKids ka kb tk = some ks → AR.nszL ks ≤ AR.nszL ka + AR.nszL kb
  | [], [], [], ks, h => by
    simp only [mergeKids, Option.some.injEq] at h; subst h; simp [AR.nszL]
  | a :: as, b :: bs, t :: ts, ks, h => by
    simp only [mergeKids] at h
    obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h2
    have h1 := mergeAR_nsz_le_rec a b t r hr
    have h3 := mergeKids_nszL_le_rec as bs ts l hl
    simp only [AR.nszL]
    omega
  | [], [], _ :: _, _, h => by simp [mergeKids] at h
  | [], _ :: _, _, _, h => by simp [mergeKids] at h
  | _ :: _, [], _, _, h => by simp [mergeKids] at h
  | _ :: _, _ :: _, [], _, h => by simp [mergeKids] at h
end

theorem mergeAR_nsz_le_pair : (type_of% @mergeAR_nsz_le_rec) ∧ (type_of% @mergeKids_nszL_le_rec) :=
  ⟨@mergeAR_nsz_le_rec, @mergeKids_nszL_le_rec⟩

theorem mergeAR_nsz_le : type_of% @mergeAR_nsz_le_rec := mergeAR_nsz_le_pair.1

/-- **`mergeReal` produces a tree of at most `|ta| + |tb|` nodes.** -/
theorem mergeReal_size_le {B : Finset ℕ} {ta tb t : RT} {target : CT} (h : mergeReal B ta tb target = some t) :
    t.size ≤ ta.size + tb.size := by
  unfold mergeReal at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [toRT_size]
  have h1 := mergeAR_nsz_le _ _ _ r hr
  have h2 := analyze_nsz_le B ta
  have h3 := analyze_nsz_le B tb
  omega

theorem realJoin_size_le {kmax : ℕ} {B : Finset ℕ} {ta tb t : RT} {target : CT}
    (h : realJoin kmax B ta tb target = some t) : t.size ≤ ta.size + tb.size := by
  unfold realJoin at h
  obtain ⟨d, -, hd⟩ := Option.bind_eq_some_iff.1 h
  exact mergeReal_size_le hd

/-- **`realIntro` adds at most `leaves + b + 3` nodes** (`b` bounds the labels of the characteristic of `t`). -/
theorem realIntro_size_le {kmax v : ℕ} {N B : Finset ℕ} {t t' : RT} {target : CT} {b : ℕ}
    (hb : LB b (t.char B)) (h : realIntro kmax v N B t target = some t') :
    t'.size ≤ t.size + (leaves (t.char B) + b + 3) := by
  unfold realIntro at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hr
  have h1 := applyPlan_size_le v N B r.1 r.2.1 t
  have h2 := planCost_le_of_mem_introPlans v N (b := b) (t.char B) hb r hmem
  omega

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Size.RealE` -/

section
/-!
# Size bounds (WP P1), part 11: `extract_size_le`

For a good nice tree `nt` whose bags have at most `k + 2` vertices (`nt.toRT.Width (k + 1)`), every real tree returned by
`extract adj k nt c` has at most `(2k + 8) · |nt|` nodes: a leaf gives 1 node, a forget node none, an introduce node at
most `leaves + b + 3 ≤ 2k + 8` (region cuts + new branch), a join node adds the sizes (`mergeReal_size_le`).

**Repair of `Machine.lean`'s `extract_size_le`**: the hypothesis `nt.toRT.Width (k + 1)` is needed (otherwise the bags,
hence `b`, are unbounded); the constant `4 * (k + 3)` is kept as a corollary (`extract_size_le`) since `2k + 8 ≤ 4(k+3)`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem extract_size_aux {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → nt.toRT.Width (k + 1) → ∀ c ∈ tables adj k nt,
      ∀ t, extract adj k nt c = some t → t.size ≤ (2 * k + 8) * nt.size
  | .leaf, _, _, _, c, hc, t, ht => by
    simp only [extract, Option.some.injEq] at ht
    subst ht
    simp [size_node', NT.size]
  | .forget x c, hg, hW, hw, q, hq, t, ht => by
    simp only [extract] at ht
    obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
    by_cases he : CT.forgetC x q1 = q
    · simp only [he, if_true] at hf
      have := extract_size_aux hs hg.2 hW (NT.width_forget hw) q1 hq1 t hf
      simp only [NT.size]
      nlinarith
    · simp [he] at hf
  | .join a b, hg, hW, hw, q, hq, t, ht => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    simp only [extract] at ht
    obtain ⟨ca, hca, hf⟩ := findSome_sound ht
    obtain ⟨cb, hcb, hf'⟩ := findSome_sound hf
    by_cases he : q ∈ CT.joinC (k + 1) ca cb
    · simp only [he, if_true] at hf'
      rcases hea : extract adj k a ca with _ | ta
      · simp [hea] at hf'
      rcases heb : extract adj k b cb with _ | tb
      · simp [hea, heb] at hf'
      simp only [hea, heb, Option.bind_some] at hf'
      have h1 := extract_size_aux hs hga hWa (NT.width_join_left hw) ca hca ta hea
      have h2 := extract_size_aux hs hgb hWb (NT.width_join_right hw) cb hcb tb heb
      have h3 := realJoin_size_le hf'
      simp only [NT.size]
      nlinarith
    · simp [he] at hf'
  | .intro v c, hg, hW, hw, q, hq, t, ht => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hwc := NT.width_intro hw
    have hB : c.bag.card ≤ k + 2 := bag_card_le_of_width hwc
    simp only [extract] at ht
    obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
    by_cases he : q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q1
    · simp only [he, if_true] at hf
      rcases hea : extract adj k c q1 with _ | t0
      · simp [hea] at hf
      simp only [hea, Option.bind_some] at hf
      have ih := extract_size_aux hs hgc hWc hwc q1 hq1 t0 hea
      obtain ⟨-, hsp⟩ := extract_all hs hgc hWc q1 hq1
      obtain ⟨-, d0⟩ := hsp t0 hea
      have hwf := tables_wf hgc q1 hq1
      have hLB : LB c.bag.card (t0.char c.bag) :=
        (DomC.LB_iff d0).2 (LB.of_good hwf.good)
      have hl : leaves (t0.char c.bag) ≤ c.bag.card + 1 := by
        rw [d0.leaves_eq]; exact hwf.leaves_le
      have h3 := realIntro_size_le hLB hf
      simp only [NT.size]
      nlinarith
    · simp [he] at hf

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Size.RealF` -/

section
/-!
# Size bounds (WP P1), part 13: cell sizes of real trees, and the final `extract` bounds

`rvsz` is the number of cells of the cons-tree view of a real tree
(`encRT (node X ks) = cons (list X) (list of kids)`); if all bags have at most `β` vertices,
`vsz t + 1 ≤ size t · (2β + 4)` (`rvsz_le`).  Combined with `extract_size_aux` and the width `≤ k` of the extracted
trees (`extract_all`), `extract_vsz_le` bounds the cell size of `extract`'s result by
`(2k + 8)(2k + 6) · |nt|`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

mutual
/-- Number of cells of the cons-tree view of a real tree. -/
def rvsz : RT → ℕ
  | .node X ks => (2 * X.card + 1) + rvszL ks + 1
def rvszL : List RT → ℕ
  | [] => 1
  | k :: ks => rvsz k + rvszL ks + 1
end

theorem rvszL_eq : ∀ ks : List RT, rvszL ks = 1 + (ks.map (fun k => rvsz k + 1)).sum
  | [] => by simp [rvszL]
  | k :: ks => by simp [rvszL, rvszL_eq ks]; omega

theorem rvsz_le {β : ℕ} : ∀ t : RT, (∀ X ∈ t.bags, X.card ≤ β) → rvsz t + 1 ≤ t.size * (2 * β + 4) := by
  intro t
  induction t using RT.ind with
  | h X ks ih =>
    intro hb
    have hX : X.card ≤ β := hb X (by simp [RT.bags])
    have hk : ∀ k ∈ ks, rvsz k + 1 ≤ k.size * (2 * β + 4) := by
      intro k hk
      refine ih k hk (fun Y hY => hb Y ?_)
      have : ∃ (pre : List (Finset ℕ)), True := ⟨[], trivial⟩
      simp only [RT.bags, List.mem_cons]
      right
      have hall : ∀ ks' : List RT, k ∈ ks' → ∀ Y ∈ k.bags, Y ∈ RT.bagsL ks' := by
        intro ks'
        induction ks' with
        | nil => intro h; simp at h
        | cons a l ihl =>
          intro h Y hY
          simp only [RT.bagsL, List.mem_append]
          rcases List.mem_cons.1 h with rfl | h
          · exact Or.inl hY
          · exact Or.inr (ihl h Y hY)
      exact hall ks hk Y hY
    have hsum : ((ks.map (fun k => rvsz k + 1)).sum) ≤ (ks.map (fun k => k.size * (2 * β + 4))).sum := by
      apply List.sum_le_sum
      intro k0 hk0
      have := hk k0 hk0
      omega
    have hsz : (ks.map (fun k => k.size * (2 * β + 4))).sum = (ks.map RT.size).sum * (2 * β + 4) :=
      List.sum_map_mul_right ..
    have hv : rvsz (RT.node X ks) = 2 * X.card + 2 + rvszL ks := by simp [rvsz]; omega
    rw [hv, rvszL_eq, size_node']
    nlinarith

/-- The cell size of the tree returned by `extract`. -/
theorem extract_vsz_le {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) (hw : nt.toRT.Width (k + 1)) : ∀ c ∈ tables adj k nt, ∀ t, extract adj k nt c = some t →
      rvsz t ≤ (2 * k + 8) * (2 * k + 6) * nt.size := by
  intro c hc t ht
  have hsz := extract_size_aux hs hg hW hw c hc t ht
  obtain ⟨-, hsp⟩ := extract_all hs hg hW c hc
  obtain ⟨hp, -⟩ := hsp t ht
  have hb : ∀ X ∈ t.bags, X.card ≤ k + 1 := hp.2
  have := rvsz_le (β := k + 1) t hb
  calc rvsz t ≤ t.size * (2 * (k + 1) + 4) := by omega
    _ ≤ ((2 * k + 8) * nt.size) * (2 * (k + 1) + 4) := Nat.mul_le_mul_right _ hsz
    _ = (2 * k + 8) * (2 * k + 6) * nt.size := by ring

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Size.Statements` -/

section
/-!
# Size bounds (WP P1): the statements in the shape of `proofs-todo/Machine.lean`

* `joinC_length_le_64` / `introC_length_le_64` : the typed `2^(64 (|B| + kmax + 2)^3)` bounds;
* `tables_length_le_C0`, `tables_pre_le_C0` : with the constant `C0 = 30000` of `Machine.lean` (`≤ 2^(C0 (k+2)^3)`), for
  the tables themselves and for the lists *before* `dedup` in `forgetTable`/`introTable`/`joinTable`;
* `extract_size_le` : `Machine.lean`'s statement with the extra hypothesis `nt.toRT.Width (k + 1)` (bags of at most
  `k + 2` vertices); the constant `4 * (k + 3)` is kept (the proof gives `2 * k + 8`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- `Machine.lean`'s `C0`. -/
def sizeC0 : ℕ := 30000

end Lax117284Proofs.Treewidth.Chars

end
