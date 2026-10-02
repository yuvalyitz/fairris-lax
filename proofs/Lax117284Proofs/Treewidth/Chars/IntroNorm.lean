import Lax117284Proofs.Treewidth.Chars.NormConfl
import Lax117284Proofs.Treewidth.Chars.NormConn
import Lax117284Proofs.Treewidth.Chars.NormMono
import Lax117284Proofs.Treewidth.Chars.NormGood

/-!
# Normal-form algebra for the introduce case (work package C4, part 5)

* `normF_merge` — the merge law: an already normalised run merged into a parent of the same label;
* `align` — comparison of two normal-form computations whose kid lists are permutations of each other
  (`normF_perm` with the keys of the target distinct, then `normF_mono`);
* `Nested σ p` — every label lies inside its parent's, the root inside `σ` ("junk"); it is exactly
  `keep σ (norm p) = false`, and such a tree normalises to a single leaf run.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-! ## the merge law -/

theorem normF_merge (S : Finset ℕ) {s y : List ℕ} (hs : s ≠ []) {F : List CT}
    (hF : ∀ k ∈ F, keep S k = true) :
    normF S s ([normF S y F].filter (keep S)) = normF S (typical (s ++ y)) F := by
  match F, hF with
  | [], _ =>
    rw [List.filter_cons_of_neg (by rw [keep_normF_nil]; simp), List.filter_nil, normF_nil, normF_nil,
      typical_append_take_one hs]
  | [k], hF =>
    have hkeep : keep S (normF S y [k]) = true := keep_normF_ne (by simp) hF
    rw [List.filter_cons_of_pos hkeep, List.filter_nil]
    by_cases hk : k.S = S
    · rw [normF_single S y k, if_pos hk, normF_single S s, normF_single S _ k, if_pos hk]
      simp only [CT.S, CT.y, CT.kids, if_true]
      rw [typ_assoc_l, typ_assoc_r, List.append_assoc]
    · rw [normF_single S y k, if_neg hk, normF_single S s, normF_single S _ k, if_neg hk]
      simp only [CT.S, CT.y, CT.kids, if_true]
  | a :: b :: t, hF =>
    have hkeep : keep S (normF S y (a :: b :: t)) = true := keep_normF_ne (by simp) hF
    rw [List.filter_cons_of_pos hkeep, List.filter_nil, normF_ge2 S y, normF_single S s, normF_ge2]
    simp only [CT.S, CT.y, CT.kids, if_true]

/-! ## comparison of normal-form computations up to a permutation of the kids -/

/-! ## junk: nested run trees -/

mutual
/-- Every label lies inside its parent's; the root label inside `σ`. -/
def Nested (σ : Finset ℕ) : CT → Prop
  | node S _ ks => S ⊆ σ ∧ NestedL S ks
def NestedL (σ : Finset ℕ) : List CT → Prop
  | [] => True
  | k :: ks => Nested σ k ∧ NestedL σ ks
end

theorem NestedL_iff {σ : Finset ℕ} {ks : List CT} : NestedL σ ks ↔ ∀ k ∈ ks, Nested σ k := by
  induction ks with
  | nil => simp [NestedL]
  | cons k ks ih => simp [NestedL, ih]

theorem kids_normF_ne_nil (S : Finset ℕ) (y : List ℕ) {F : List CT} (hF : ∀ k ∈ F, keep S k = true) (hne : F ≠ []) :
    (normF S y F).kids ≠ [] := by
  have := keep_normF_ne (S := S) (y := y) hne hF
  intro h
  rw [keep_eq_true_iff] at this
  exact this ⟨h, by rw [normF_S]⟩

theorem kids_norm_nil (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    (norm (node S y ks)).kids = [] ↔ ∀ k ∈ ks, keep S (norm k) = false := by
  rw [norm_node']
  generalize hF : (ks.map norm).filter (keep S) = F
  have hF' : ∀ k ∈ F, keep S k = true := by
    intro k hk; rw [← hF] at hk; exact (List.mem_filter.1 hk).2
  constructor
  · intro hk
    by_contra hne
    have hFne : F ≠ [] := by
      intro e
      apply hne
      rw [← hF, List.filter_eq_nil_iff] at e
      intro k hkm
      have := e (norm k) (List.mem_map.2 ⟨k, hkm, rfl⟩)
      simpa using this
    exact kids_normF_ne_nil S y hF' hFne hk
  · intro hn
    have hFe : F = [] := by
      rw [← hF, List.filter_eq_nil_iff]
      intro n hn'
      obtain ⟨k, hkm, rfl⟩ := List.mem_map.1 hn'
      simpa using hn k hkm
    rw [hFe]; rfl

mutual
theorem keep_norm_false_iff : ∀ (σ : Finset ℕ) (p : CT), keep σ (norm p) = false ↔ Nested σ p
  | σ, node S y ks => by
    rw [keep_eq_false_iff, S_norm, kids_norm_nil]
    simp only [CT.S, Nested]
    rw [and_comm]
    exact and_congr_right (fun _ => nestedL_iff_keep S ks)
theorem nestedL_iff_keep : ∀ (S : Finset ℕ) (ks : List CT), (∀ k ∈ ks, keep S (norm k) = false) ↔ NestedL S ks
  | S, [] => by simp [NestedL]
  | S, k :: ks => by
    have h1 := keep_norm_false_iff S k
    have h2 := nestedL_iff_keep S ks
    simp only [List.mem_cons, forall_eq_or_imp, NestedL]
    rw [h1, h2]
end

/-- A nested tree normalises to a single leaf run. -/
theorem norm_of_nested {σ : Finset ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : Nested σ (node S y ks)) :
    norm (node S y ks) = node S (y.take 1) [] := by
  have hn := nestedL_iff_keep S ks |>.2 h.2
  rw [norm_node']
  have : (ks.map norm).filter (keep S) = [] := by
    rw [List.filter_eq_nil_iff]
    intro n hn'
    obtain ⟨k, hkm, rfl⟩ := List.mem_map.1 hn'
    simpa using hn k hkm
  rw [this]; rfl

mutual
theorem verts_nested : ∀ (σ : Finset ℕ) (p : CT), Nested σ p → verts p ⊆ p.S
  | σ, node S y ks, h => by
    intro x hx
    rw [verts_node] at hx
    rcases Finset.mem_union.1 hx with h1 | h1
    · exact h1
    · obtain ⟨k, hk, hxk⟩ := mem_vertsL.1 h1
      have hkn := NestedL_iff.1 h.2 k hk
      have := verts_nested S k hkn hxk
      exact (nested_root_sub hkn) this
theorem nested_root_sub : ∀ {σ : Finset ℕ} {p : CT}, Nested σ p → p.S ⊆ σ
  | σ, node S y ks, h => h.1
end

/-! ## non-empty run sequences survive `norm` -/

theorem yne_normF {S : Finset ℕ} {y : List ℕ} (hy : y ≠ []) {F : List CT} (hF : ∀ k ∈ F, YNe k) :
    YNe (normF S y F) := by
  match F, hF with
  | [], _ =>
    rw [normF_nil]
    exact ⟨by simpa using hy, trivial⟩
  | [k], hF =>
    rw [normF_single]
    obtain ⟨Sk, yk, kk⟩ := k
    have hk := hF (node Sk yk kk) (by simp)
    split_ifs with hS
    · exact ⟨typical_ne_nil (List.append_ne_nil_of_left_ne_nil hy _), hk.2⟩
    · exact ⟨hy, by simpa [YNeL] using hk, trivial⟩
  | a :: b :: t, hF =>
    rw [normF_ge2]
    refine ⟨hy, ?_⟩
    rw [YNeL_iff]
    intro k hk
    exact hF k (mem_sortKids.1 hk)

mutual
theorem yne_norm_rec : ∀ q : CT, YNe q → YNe (norm q)
  | node S y ks, h => by
    rw [norm_node']
    apply yne_normF h.1
    intro k hk
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hk).1
    exact (YNeL_iff.1 (yneL_normL_rec ks h.2)) (norm k0) (by rw [normL_eq_map]; exact List.mem_map.2 ⟨k0, hk0, rfl⟩)
theorem yneL_normL_rec : ∀ ks : List CT, YNeL ks → YNeL (normL ks)
  | [], _ => trivial
  | k :: ks, h => ⟨yne_norm_rec k h.1, yneL_normL_rec ks h.2⟩
end

theorem yne_norm_pair : (type_of% @yne_norm_rec) ∧ (type_of% @yneL_normL_rec) :=
  ⟨@yne_norm_rec, @yneL_normL_rec⟩

theorem yne_norm : type_of% @yne_norm_rec := yne_norm_pair.1

end CT

end Lax117284Proofs.Treewidth.Chars
