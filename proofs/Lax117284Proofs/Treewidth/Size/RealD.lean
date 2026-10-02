import Lax117284Proofs.Treewidth.Size.RealC

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
