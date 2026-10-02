import Lax117284Proofs.Treewidth.Chars.Extract

/-!
# Size bounds (WP P1), part 7: sizes of real trees (1): the measure `AR.nsz`

`AR.nsz` counts the nodes of `AR.toRT`: `chsz` of the chains (a chain node plus the size of its junk subtrees; an empty chain
still yields one node) plus the `w` of the kids.

* `toRT_size`      : `(AR.toRT r).size = r.nsz`;
* `analyze_w_le`   : `(analyze B t).w ≤ t.size` (so `(analyze B t).toRT.size ≤ t.size`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem sizeL_eq' : ∀ ks : List RT, RT.sizeL ks = (ks.map RT.size).sum
  | [] => rfl
  | k :: ks => by simp [RT.sizeL, sizeL_eq' ks]

theorem size_node' (X : Finset ℕ) (ks : List RT) : (RT.node X ks).size = 1 + (ks.map RT.size).sum := by
  simp [RT.size, sizeL_eq']

/-- Size of the junk of a chain node. -/
def CNode.jsz (n : CNode) : ℕ := (n.junk.map RT.size).sum

/-- Nodes contributed by a chain: one per chain node (at least one), plus the junk. -/
def chsz (ns : List CNode) : ℕ := max 1 ns.length + (ns.map CNode.jsz).sum

mutual
/-- The number of nodes of `toRT`. -/
def AR.nsz : AR → ℕ
  | .run _ c ks => chsz c + AR.nszL ks
def AR.nszL : List AR → ℕ
  | [] => 0
  | k :: ks => AR.nsz k + AR.nszL ks
end

theorem AR.nszL_eq : ∀ ks : List AR, AR.nszL ks = (ks.map AR.nsz).sum
  | [] => rfl
  | k :: ks => by simp [AR.nszL, AR.nszL_eq ks]

theorem chainToRT_size : ∀ (c : List CNode) (ks : List RT),
    (AR.chainToRT c ks).size = chsz c + (ks.map RT.size).sum
  | [], ks => by simp [AR.chainToRT, size_node', chsz]
  | [n], ks => by
    simp [AR.chainToRT, size_node', chsz, CNode.jsz, List.sum_append]
    omega
  | n :: m :: r, ks => by
    have ih := chainToRT_size (m :: r) ks
    simp only [AR.chainToRT, size_node', List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, ih] 
    simp only [chsz, List.length_cons, List.map_cons, List.sum_cons, CNode.jsz]
    omega

mutual
theorem toRT_size_rec : ∀ r : AR, r.toRT.size = r.nsz
  | .run S c ks => by
    rw [AR.toRT_run, chainToRT_size, AR.nsz, ← AR.toRTL_eq, toRTL_size_rec ks]
theorem toRTL_size_rec : ∀ ks : List AR, ((AR.toRTL ks).map RT.size).sum = AR.nszL ks
  | [] => rfl
  | k :: ks => by
    simp only [AR.toRTL, List.map_cons, List.sum_cons, AR.nszL, toRT_size_rec k, toRTL_size_rec ks]
end

theorem toRT_size_pair : (type_of% @toRT_size_rec) ∧ (type_of% @toRTL_size_rec) :=
  ⟨@toRT_size_rec, @toRTL_size_rec⟩

theorem toRT_size : type_of% @toRT_size_rec := toRT_size_pair.1

theorem sum_filter_split {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    ((l.filter p).map f).sum + ((l.filter (fun a => !p a)).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih.symm]; omega
    · simp only [Bool.not_eq_true] at h
      simp [List.filter_cons, h, ih.symm]; omega

theorem sortAR_nsz (S : Finset ℕ) (l : List AR) : ((sortAR S l).map AR.nsz).sum = (l.map AR.nsz).sum := by
  unfold sortAR
  exact ((List.mergeSort_perm _ _).map _).sum_eq

theorem analyzeNode_gen (S : Finset ℕ) (X : Finset ℕ) (kids : List (RT × AR)) (pr : RT × AR → Bool)
    (hk : ∀ p ∈ kids, p.2.nsz ≤ p.1.size) :
    (match (kids.filter (fun p => !pr p)).map Prod.snd with
      | [] => AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] []
      | [k] => if k.S = S then AR.run S (⟨X, (kids.filter pr).map Prod.fst⟩ :: k.chain) k.kids
               else AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] [k]
      | ks => AR.run S [⟨X, (kids.filter pr).map Prod.fst⟩] (sortAR S ks)).nsz ≤
      1 + (kids.map (fun p => p.1.size)).sum := by
  have hsplit := sum_filter_split kids pr (fun p => p.1.size)
  have hQ : (((kids.filter (fun p => !pr p)).map Prod.snd).map AR.nsz).sum ≤
      ((kids.filter (fun p => !pr p)).map (fun p => p.1.size)).sum := by
    rw [List.map_map]
    apply List.sum_le_sum
    intro p hp
    exact hk p (List.mem_of_mem_filter hp)
  have hJ : ((((kids.filter pr).map Prod.fst).map RT.size).sum) =
      ((kids.filter pr).map (fun p => p.1.size)).sum := by
    rw [List.map_map]; rfl
  split
  · rename_i hc
    rw [hc] at hQ
    simp only [AR.nsz, chsz, CNode.jsz, AR.nszL, List.length_singleton, List.map_singleton, List.sum_singleton,
      List.sum_nil, List.map_nil] at *
    omega
  · rename_i k hc
    rw [hc] at hQ
    simp only [List.map_singleton, List.sum_singleton] at hQ
    rcases k with ⟨S', c, ks'⟩
    simp only [AR.S, AR.chain, AR.kids]
    by_cases hS : S' = S
    · simp only [hS, ↓reduceIte]
      simp only [AR.nsz, chsz, CNode.jsz, List.length_cons, List.map_cons, List.sum_cons] at *
      omega
    · simp only [hS, ↓reduceIte]
      simp only [AR.nsz, chsz, CNode.jsz, AR.nszL, List.length_singleton, List.map_singleton,
        List.sum_singleton, add_zero] at *
      omega
  · rename_i hne hne1
    simp only [AR.nsz, chsz, CNode.jsz, List.length_singleton, List.map_singleton, List.sum_singleton,
      AR.nszL_eq, sortAR_nsz] at *
    omega

theorem analyze_nsz_le (B : Finset ℕ) : ∀ t : RT, (analyze B t).nsz ≤ t.size := by
  intro t
  induction t using RT.ind with
  | h X ks ih =>
    rw [analyze_node, size_node']
    have hk : ∀ p ∈ ks.map (fun k => (k, analyze B k)), p.2.nsz ≤ p.1.size := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      exact ih k hk
    have hks : (ks.map RT.size).sum = ((ks.map (fun k => (k, analyze B k))).map (fun p => p.1.size)).sum := by
      rw [List.map_map]; rfl
    rw [hks]
    exact analyzeNode_gen (X ∩ B) X _ (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ B)) hk

end Lax117284Proofs.Treewidth.Chars
