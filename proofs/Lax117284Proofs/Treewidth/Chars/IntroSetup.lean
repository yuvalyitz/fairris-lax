import Lax117284Proofs.Treewidth.Chars.NormConfl
import Lax117284Proofs.Treewidth.Chars.NormConn
import Lax117284Proofs.Treewidth.Chars.NormMono
import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.IntroChains
import Lax117284Proofs.Treewidth.Seq.Transport
import Lax117284Proofs.Treewidth.Chars.IntroPlansMem
import Lax117284Proofs.Treewidth.Chars.IntroMono

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroNorm` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroFT` -/

section
/-!
# Flagged profile trees (work package C4, part 6)

The introduction of a vertex `v` changes a decomposition `t` (of `G[U ∪ {v}]`) only at the region `W` of the nodes whose
bag contains `v`: `t.restrict U` and `t` have the same tree.  A *flagged profile tree* `FT.node S e w ks` records, per
node, the label `S = X ∩ B`, the size `e = |X ∩ U|` (of the restriction) and the flag `w = [v ∈ X]`; then

* `uT P` — the profile of the restriction (label `S`, size `e`): the source `a := norm (uT P)`;
* `fT v P` — the profile of the full tree (label `S ∪ {v}` and size `e + 1` on the flagged nodes): the target
  `T := norm (fT v P)`.

`FOk v P` (well-formedness): `v ∉ S` and `|S| ≤ e` at every node, and the flags form a connected region (a flagged
node has only flagged occupied kids; an unflagged node has at most one occupied kid).

Facts (prune / flag correspondences, all consequences of `keep σ (norm p) = false ↔ Nested σ p`):
* below a flagged node, `Nested (insert v σ) (fT v K) ↔ Nested σ (uT K)` (`keep_flag`);
* an occupied subtree below an unflagged parent is never pruned (`keep_occ`).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

set_option genInjectivity false in
inductive FT where
  | node (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT)

namespace FT

def S : FT → Finset ℕ | node S _ _ _ => S
def e : FT → ℕ | node _ e _ _ => e
def w : FT → Bool | node _ _ w _ => w
def kids : FT → List FT | node _ _ _ ks => ks

mutual
/-- The profile of the restriction. -/
def uT : FT → CT
  | node S e _ ks => CT.node S [e] (uTL ks)
def uTL : List FT → List CT
  | [] => []
  | k :: ks => uT k :: uTL ks
end

theorem uTL_eq_map (ks : List FT) : uTL ks = ks.map uT := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [uTL, ih]

theorem uT_node (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    uT (node S e w ks) = CT.node S [e] (ks.map uT) := by
  simp [uT, uTL_eq_map]

mutual
/-- The profile of the full tree. -/
def fT (v : ℕ) : FT → CT
  | node S e w ks => CT.node (if w then insert v S else S) [if w then e + 1 else e] (fTL v ks)
def fTL (v : ℕ) : List FT → List CT
  | [] => []
  | k :: ks => fT v k :: fTL v ks
end

theorem fTL_eq_map (v : ℕ) (ks : List FT) : fTL v ks = ks.map (fT v) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [fTL, ih]

theorem fT_node (v : ℕ) (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    fT v (node S e w ks) = CT.node (if w then insert v S else S) [if w then e + 1 else e] (ks.map (fT v)) := by
  simp [fT, fTL_eq_map]

mutual
/-- Some node of the tree is flagged. -/
def occ : FT → Bool
  | node _ _ w ks => w || occL ks
def occL : List FT → Bool
  | [] => false
  | k :: ks => occ k || occL ks
end

theorem occL_eq_any (ks : List FT) : occL ks = ks.any occ := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [occL, ih]

theorem occ_node (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    occ (node S e w ks) = (w || ks.any occ) := by simp [occ, occL_eq_any]

mutual
/-- The labels of the flagged nodes. -/
def cov : FT → Finset ℕ
  | node S _ w ks => (if w then S else ∅) ∪ covL ks
def covL : List FT → Finset ℕ
  | [] => ∅
  | k :: ks => cov k ∪ covL ks
end

theorem mem_covL {x : ℕ} {ks : List FT} : x ∈ covL ks ↔ ∃ k ∈ ks, x ∈ cov k := by
  induction ks with
  | nil => simp [covL]
  | cons k ks ih => simp [covL, ih]

mutual
/-- Well-formedness. -/
def FOk (v : ℕ) : FT → Prop
  | node S e w ks =>
    v ∉ S ∧ S.card ≤ e ∧ (w = true → ∀ k ∈ ks, occ k = true → k.w = true) ∧
      (w = false → occL ks = false ∨
        ∃ pre k post, ks = pre ++ k :: post ∧ occ k = true ∧ occL pre = false ∧ occL post = false) ∧
      FOkL v ks
def FOkL (v : ℕ) : List FT → Prop
  | [] => True
  | k :: ks => FOk v k ∧ FOkL v ks
end

theorem FOkL_iff {v : ℕ} {ks : List FT} : FOkL v ks ↔ ∀ k ∈ ks, FOk v k := by
  induction ks with
  | nil => simp [FOkL]
  | cons k ks ih => simp [FOkL, ih]

/-! ## unflagged trees -/

mutual
theorem fT_of_not_occ_rec (v : ℕ) : ∀ K : FT, occ K = false → fT v K = uT K
  | node S e w ks, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [fT, uT, if_neg (by simp : ¬ (false = true))]
    rw [fTL_of_not_occ_rec v ks h2]
theorem fTL_of_not_occ_rec (v : ℕ) : ∀ ks : List FT, occL ks = false → fTL v ks = uTL ks
  | [], _ => rfl
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_false_iff] at h
    simp only [fTL, uTL]
    rw [fT_of_not_occ_rec v k h.1, fTL_of_not_occ_rec v ks h.2]
end

theorem fT_of_not_occ_pair : (type_of% @fT_of_not_occ_rec) ∧ (type_of% @fTL_of_not_occ_rec) :=
  ⟨@fT_of_not_occ_rec, @fTL_of_not_occ_rec⟩

theorem fT_of_not_occ : type_of% @fT_of_not_occ_rec := fT_of_not_occ_pair.1

theorem occ_of_occL_false {ks : List FT} (h : occL ks = false) : ∀ k ∈ ks, occ k = false := by
  intro k hk
  rw [occL_eq_any] at h
  have := List.any_eq_false.1 h k hk
  simpa using this

/-! ## labels and vertices -/

mutual
theorem cov_le_verts_rec : ∀ K : FT, cov K ⊆ CT.verts (uT K)
  | node S e w ks => by
    rw [uT, CT.verts_node]
    simp only [cov]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · split_ifs at h with hw
      · exact Finset.mem_union_left _ h
      · simp at h
    · exact Finset.mem_union_right _ (covL_le_vertsL_rec ks h)
theorem covL_le_vertsL_rec : ∀ ks : List FT, covL ks ⊆ CT.vertsL (uTL ks)
  | [] => by simp [covL]
  | k :: ks => by
    intro x hx
    simp only [covL, Finset.mem_union] at hx
    simp only [uTL, CT.vertsL, Finset.mem_union]
    rcases hx with h | h
    · exact Or.inl (cov_le_verts_rec k h)
    · exact Or.inr (covL_le_vertsL_rec ks h)
end

theorem cov_le_verts_pair : (type_of% @cov_le_verts_rec) ∧ (type_of% @covL_le_vertsL_rec) :=
  ⟨@cov_le_verts_rec, @covL_le_vertsL_rec⟩

theorem cov_le_verts : type_of% @cov_le_verts_rec := cov_le_verts_pair.1

mutual
theorem v_mem_verts_fT_rec (v : ℕ) : ∀ K : FT, occ K = true → v ∈ CT.verts (fT v K)
  | node S e w ks, h => by
    rw [fT, CT.verts_node]
    simp only [occ, Bool.or_eq_true] at h
    rcases h with hw | hk
    · subst hw
      exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ (v_mem_vertsL_fTL_rec v ks hk)
theorem v_mem_vertsL_fTL_rec (v : ℕ) : ∀ ks : List FT, occL ks = true → v ∈ CT.vertsL (fTL v ks)
  | [], h => by simp [occL] at h
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_true] at h
    simp only [fTL, CT.vertsL, Finset.mem_union]
    rcases h with h | h
    · exact Or.inl (v_mem_verts_fT_rec v k h)
    · exact Or.inr (v_mem_vertsL_fTL_rec v ks h)
end

theorem v_mem_verts_fT_pair : (type_of% @v_mem_verts_fT_rec) ∧ (type_of% @v_mem_vertsL_fTL_rec) :=
  ⟨@v_mem_verts_fT_rec, @v_mem_vertsL_fTL_rec⟩

theorem v_mem_verts_fT : type_of% @v_mem_verts_fT_rec := v_mem_verts_fT_pair.1

/-! ## flag correspondences -/

mutual
theorem nested_flag_rec (v : ℕ) : ∀ (K : FT), FOk v K → (K.w = true ∨ occ K = false) → ∀ σ : Finset ℕ,
    (Nested (insert v σ) (fT v K) ↔ Nested σ (uT K))
  | node S e w ks, hok, hK, σ => by
    have hvS := hok.1
    by_cases hocc : occ (node S e w ks) = false
    · rw [fT_of_not_occ v _ hocc]
      simp only [uT, Nested]
      rw [Finset.subset_insert_iff_of_notMem hvS]
    · have hw : w = true := by
        rcases hK with h | h
        · exact h
        · exact absurd h hocc
      subst hw
      simp only [fT, uT, Nested, if_true]
      rw [Finset.insert_subset_insert_iff hvS]
      refine and_congr_right (fun _ => ?_)
      have hkids := hok.2.2.1 rfl
      exact nestedL_flag_rec v ks (FOkL_iff.1 hok.2.2.2.2)
        (fun k hk => by
          by_cases hk' : occ k = true
          · exact Or.inl (hkids k hk hk')
          · exact Or.inr (by simpa using hk')) S
theorem nestedL_flag_rec (v : ℕ) : ∀ (ks : List FT), (∀ k ∈ ks, FOk v k) → (∀ k ∈ ks, k.w = true ∨ occ k = false) →
    ∀ σ : Finset ℕ, (NestedL (insert v σ) (fTL v ks) ↔ NestedL σ (uTL ks))
  | [], _, _, σ => by simp [fTL, uTL, NestedL]
  | k :: ks, hok, hK, σ => by
    have h1 := nested_flag_rec v k (hok k (by simp)) (hK k (by simp)) σ
    have h2 := nestedL_flag_rec v ks (fun k' hk' => hok k' (by simp [hk'])) (fun k' hk' => hK k' (by simp [hk'])) σ
    simp only [fTL, uTL, NestedL]
    rw [h1, h2]
end

theorem nested_flag_pair : (type_of% @nested_flag_rec) ∧ (type_of% @nestedL_flag_rec) :=
  ⟨@nested_flag_rec, @nestedL_flag_rec⟩

theorem nested_flag : type_of% @nested_flag_rec := nested_flag_pair.1

/-- Below a flagged parent (or below an unflagged one, for unoccupied subtrees) pruning is unchanged. -/
theorem keep_flag (v : ℕ) {K : FT} (hok : FOk v K) (hK : K.w = true ∨ occ K = false) (σ : Finset ℕ) :
    keep (insert v σ) (norm (fT v K)) = keep σ (norm (uT K)) := by
  have h := nested_flag v K hok hK σ
  rw [Bool.eq_iff_iff]
  have h1 := keep_norm_false_iff (insert v σ) (fT v K)
  have h2 := keep_norm_false_iff σ (uT K)
  constructor
  · intro ht
    by_contra hf
    have : keep σ (norm (uT K)) = false := by simpa using hf
    have := h.2 (h2.1 this)
    have := h1.2 this
    simp_all
  · intro ht
    by_contra hf
    have : keep (insert v σ) (norm (fT v K)) = false := by simpa using hf
    have := h.1 (h1.1 this)
    have := h2.2 this
    simp_all

/-- An occupied subtree below an unflagged parent (`v ∉ σ`) is never pruned. -/
theorem keep_occ (v : ℕ) {K : FT} (hocc : occ K = true) {σ : Finset ℕ} (hvσ : v ∉ σ) :
    keep σ (norm (fT v K)) = true := by
  by_contra hf
  have hf' : keep σ (norm (fT v K)) = false := by simpa using hf
  have hn := (keep_norm_false_iff σ (fT v K)).1 hf'
  have hv := v_mem_verts_fT v K hocc
  have h1 := verts_nested σ _ hn hv
  exact hvσ (nested_root_sub hn h1)

end FT

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroJunk` -/

section
/-!
# Case (b): the region `W` lies in a junk subtree (work package C4, part 7)

`junk_branch`: if the occupied subtree `K` is junk below a run labelled `σ` (`Nested σ (uT K)`), then `norm (fT v K)` is
a branch of strictly nested labels ending in the leaf `S_w ∪ {v}` — dominating the plan's branch `pathSubtree v chain M`
for some `(chain, M) ∈ allChains σ N`.  (The plan's runs carry the sizes of their *labels*, the real ones are larger.)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## sequences dominating a singleton -/

theorem dom_singleton_of_forall {c : ℕ} {z : List ℕ} (hz : z ≠ []) (h : ∀ x ∈ z, c ≤ x) : Dom [c] z := by
  have h1 : 1 ≤ z.length := List.length_pos_iff.2 hz
  exact ⟨List.replicate z.length c, z, ext_single_replicate h1, Ext.refl z, leSeq_replicate_left h⟩

theorem forall₂_exists_left {R : ℕ → ℕ → Prop} {a b : List ℕ} (h : List.Forall₂ R a b) :
    ∀ y ∈ b, ∃ x ∈ a, R x y := by
  induction h with
  | nil => intro y hy; simp at hy
  | @cons p q as bs hpq _ ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨p, List.mem_cons_self, hpq⟩
    · obtain ⟨x, hx, hxy⟩ := ih y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

theorem dom_singleton_le {c : ℕ} {y : List ℕ} (h : Dom [c] y) : ∀ x ∈ y, c ≤ x := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  intro x hx
  obtain ⟨p, hp, hpx⟩ := forall₂_exists_left hle x ((hb.mem).2 hx)
  have : p = c := by simpa using (ha.mem).1 hp
  omega

/-! ## induction principle for `FT` -/

mutual
theorem FT.ind_rec {P : FT → Prop} (h : ∀ S e w ks, (∀ k ∈ ks, P k) → P (FT.node S e w ks)) : ∀ K : FT, P K
  | FT.node S e w ks => h S e w ks (FT.indL_rec h ks)
theorem FT.indL_rec {P : FT → Prop} (h : ∀ S e w ks, (∀ k ∈ ks, P k) → P (FT.node S e w ks)) :
    ∀ ks : List FT, ∀ k ∈ ks, P k
  | [] => by intro k hk; simp at hk
  | k :: ks => by
    intro k' hk'
    rcases List.mem_cons.1 hk' with e | hk''
    · exact e ▸ FT.ind_rec h k
    · exact FT.indL_rec h ks k' hk''
end

theorem FT.ind_pair : (type_of% @FT.ind_rec) ∧ (type_of% @FT.indL_rec) :=
  ⟨@FT.ind_rec, @FT.indL_rec⟩

theorem FT.ind : type_of% @FT.ind_rec := FT.ind_pair.1

namespace FT

mutual
theorem cov_of_not_occ_rec : ∀ K : FT, occ K = false → cov K = ∅
  | node S e w ks, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    obtain ⟨rfl, h2⟩ := h
    simp [cov, covL_of_not_occ_rec ks h2]
theorem covL_of_not_occ_rec : ∀ ks : List FT, occL ks = false → covL ks = ∅
  | [], _ => rfl
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_false_iff] at h
    simp [covL, cov_of_not_occ_rec k h.1, covL_of_not_occ_rec ks h.2]
end

theorem cov_of_not_occ_pair : (type_of% @cov_of_not_occ_rec) ∧ (type_of% @covL_of_not_occ_rec) :=
  ⟨@cov_of_not_occ_rec, @covL_of_not_occ_rec⟩

theorem cov_of_not_occ : type_of% @cov_of_not_occ_rec := cov_of_not_occ_pair.1

end FT

open FT

/-- Membership in `allChains` is preserved when the bound grows (nonempty chain). -/
theorem mem_allChains_bound {S σ N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ} (h : (chain, M) ∈ allChains S N)
    (hSσ : S ⊆ σ) (hne : chain ≠ []) : (chain, M) ∈ allChains σ N := by
  rw [mem_allChains] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun X hX => ⟨(h1 X hX).1, (h1 X hX).2.trans hSσ⟩, h2, h3, ?_⟩
  cases chain with
  | nil => exact absurd rfl hne
  | cons X r =>
    rw [List.getLastD_cons] at h4 ⊢
    exact h4

/-- Put the label of the run on top of the chain. -/
theorem mem_allChains_cons {S σ N : Finset ℕ} {chain : List (Finset ℕ)} {M : Finset ℕ}
    (h : (chain, M) ∈ allChains S N) (hSσ : S ⊆ σ) (hhead : ∀ X ∈ chain.head?, X ≠ S) :
    (S :: chain, M) ∈ allChains σ N := by
  rw [mem_allChains] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hNS : N ⊆ S := by
    refine h3.trans (h4.trans ?_)
    cases chain with
    | nil => simp
    | cons X r =>
      -- the last element of the chain lies inside `S`
      have hall : ∀ Y ∈ X :: r, Y ⊆ S := fun Y hY => (h1 Y hY).2
      rw [List.getLastD_eq_getLast?]
      cases hl : (X :: r).getLast? with
      | none => simp at hl
      | some Z => exact hall Z (List.mem_of_getLast? hl)
  refine ⟨?_, ?_, h3, ?_⟩
  · intro Y hY
    rcases List.mem_cons.1 hY with e | hY'
    · rw [e]; exact ⟨hNS, hSσ⟩
    · exact ⟨(h1 Y hY').1, (h1 Y hY').2.trans hSσ⟩
  · cases chain with
    | nil => exact List.IsChain.singleton S
    | cons X r =>
      have hXS : X ⊆ S := (h1 X (by simp)).2
      have hne : X ≠ S := hhead X rfl
      exact List.IsChain.cons_cons (Finset.ssubset_iff_subset_ne.2 ⟨hXS, hne⟩) h2
  · rw [List.getLastD_cons]; exact h4

theorem pathSubtree_nil (v : ℕ) (M : Finset ℕ) : pathSubtree v [] M = CT.node (insert v M) [M.card + 1] [] := rfl
theorem pathSubtree_cons (v : ℕ) (X : Finset ℕ) (r : List (Finset ℕ)) (M : Finset ℕ) :
    pathSubtree v (X :: r) M = CT.node X [X.card] [pathSubtree v r M] := rfl

/-- **Lemma J.** -/
theorem junk_branch (v : ℕ) {N : Finset ℕ} : ∀ K : FT, FOk v K → occ K = true → ∀ σ : Finset ℕ, v ∉ σ →
    Nested σ (uT K) → N ⊆ cov K →
    ∃ chain M, (chain, M) ∈ allChains σ N ∧ DomC (pathSubtree v chain M) (norm (fT v K)) := by
  intro K
  induction K using FT.ind with
  | _ S e w ks ih =>
    intro hok hocc σ hvσ hnest hN
    have hvS : v ∉ S := hok.1
    have hSe : S.card ≤ e := hok.2.1
    have hnest' : Nested σ (CT.node S [e] (ks.map uT)) := by rw [← uT_node]; exact hnest
    have hSσ : S ⊆ σ := hnest'.1
    cases w with
    | true =>
      have hn : Nested (insert v σ) (fT v (FT.node S e true ks)) :=
        (nested_flag v _ hok (Or.inl rfl) σ).2 hnest
      have hN' : N ⊆ S := by
        have := verts_nested σ (CT.node S [e] (ks.map uT)) hnest'
        exact hN.trans ((cov_le_verts _).trans (by simpa [uT_node, CT.S] using this))
      simp only [fT_node, if_true] at hn ⊢
      rw [norm_of_nested hn]
      refine ⟨[], S, mem_allChains.2 ⟨by simp, List.IsChain.nil, hN', by simpa using hSσ⟩, ?_⟩
      refine ⟨rfl, ?_, trivial⟩
      exact dom_singleton_of_forall (by simp) (by
        intro x hx; simp at hx; subst hx; omega)
    | false =>
      simp only [occ, Bool.false_or] at hocc
      rcases hok.2.2.2.1 rfl with hno | ⟨pre, K0, post, hks, hK0, hpre, hpost⟩
      · rw [hno] at hocc; exact absurd hocc (by simp)
      · subst hks
        have hkidsN : ∀ k ∈ pre ++ K0 :: post, Nested S (uT k) := fun k hk =>
          NestedL_iff.1 hnest'.2 (uT k) (List.mem_map.2 ⟨k, hk, rfl⟩)
        have hkidsOk : ∀ k ∈ pre ++ K0 :: post, FOk v k := fun k hk => FOkL_iff.1 hok.2.2.2.2 k hk
        have hother : ∀ k ∈ pre ++ post, keep S (norm (fT v k)) = false := by
          intro k hk
          have hocck : occ k = false := by
            rcases List.mem_append.1 hk with h | h
            · exact occ_of_occL_false hpre k h
            · exact occ_of_occL_false hpost k h
          rw [fT_of_not_occ v k hocck]
          exact (keep_norm_false_iff S (uT k)).2 (hkidsN k (by
            rcases List.mem_append.1 hk with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)))
        have hkeep0 : keep S (norm (fT v K0)) = true := keep_occ v hK0 hvS
        have hnorm : norm (fT v (FT.node S e false (pre ++ K0 :: post))) = normF S [e] [norm (fT v K0)] := by
          simp only [fT_node, if_false, Bool.false_eq_true]
          rw [norm_node']
          congr 1
          have hk0 : keep S ((norm ∘ fT v) K0) = true := hkeep0
          rw [List.map_map, List.map_append, List.map_cons, List.filter_append, List.filter_cons_of_pos hk0]
          have h1 : (pre.map (norm ∘ fT v)).filter (keep S) = [] := by
            rw [List.filter_eq_nil_iff]
            intro n hn
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
            simpa using hother k (List.mem_append_left _ hk)
          have h2 : (post.map (norm ∘ fT v)).filter (keep S) = [] := by
            rw [List.filter_eq_nil_iff]
            intro n hn
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
            simpa using hother k (List.mem_append_right _ hk)
          rw [h1, h2]; rfl
        have hN0 : N ⊆ cov K0 := by
          intro x hx
          have hx' := hN hx
          simp [cov] at hx'
          obtain ⟨k, hk, hxk⟩ := mem_covL.1 hx'
          rcases List.mem_append.1 hk with h | h
          · rw [cov_of_not_occ k (occ_of_occL_false hpre k h)] at hxk; simp at hxk
          · rcases List.mem_cons.1 h with e | h
            · rw [e] at hxk; exact hxk
            · rw [cov_of_not_occ k (occ_of_occL_false hpost k h)] at hxk; simp at hxk
        obtain ⟨chain0, M0, hc0, hd0⟩ :=
          ih K0 (List.mem_append_right _ (List.mem_cons_self)) (hkidsOk K0 (by simp)) hK0 S hvS
            (hkidsN K0 (by simp)) hN0
        rw [hnorm]
        generalize hT0 : norm (fT v K0) = T0 at hd0 ⊢
        cases T0 with
        | node S0 y0 kk =>
          by_cases hSS : S0 = S
          · -- merge
            have hSS' : S = S0 := hSS.symm
            subst hSS'
            cases chain0 with
            | nil =>
              rw [pathSubtree_nil] at hd0
              have h1 : insert v M0 = S := hd0.1
              exact absurd (h1 ▸ Finset.mem_insert_self v M0) hvS
            | cons X1 rest =>
              rw [pathSubtree_cons] at hd0
              obtain ⟨hX1, hy0, hk0⟩ := hd0
              have hX1' : X1 = S := hX1
              subst hX1'
              refine ⟨X1 :: rest, M0, mem_allChains_bound hc0 hSσ (by simp), ?_⟩
              rw [normF_single, if_pos (show (CT.node X1 y0 kk).S = X1 from rfl), pathSubtree_cons]
              refine ⟨rfl, ?_, hk0⟩
              simp only [CT.y]
              refine dom_singleton_of_forall (typical_ne_nil (by simp)) ?_
              intro x hx
              rcases List.mem_append.1 (mem_of_mem_typical hx) with h | h
              · simp at h; subst h; exact hSe
              · exact dom_singleton_le hy0 x h
          · -- no merge
            rw [normF_single, if_neg (show ¬ (CT.node S0 y0 kk).S = S from hSS)]
            refine ⟨S :: chain0, M0, mem_allChains_cons hc0 hSσ ?_, ?_⟩
            · intro X hX hXS
              cases chain0 with
              | nil => simp at hX
              | cons X1 rest =>
                simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hX
                subst hX
                rw [pathSubtree_cons] at hd0
                exact hSS (hd0.1.symm.trans hXS |>.symm ▸ rfl)
            · rw [pathSubtree_cons]
              refine ⟨rfl, dom_singleton_of_forall (by simp) (by intro x hx; simp at hx; subst hx; exact hSe), hd0, trivial⟩
end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroPrefix` -/

section
/-!
# Prefixing a run with an exact chain (work package C4, part 8)

If the run `k = node S yk kk` has the same label as its (single non-junk) parent node of size `s`, the normal form
merges them into one run whose sequence is `typical (s ++ yk)`.  The options of `k`, and the options that end exactly at
the junction, lift *syntactically* to the options of the *exact* run `k' = node S (s ++ yk) kk` (cut indices shift by
`|s|`); `IR_mono` then moves them to the typical run.

* `winR_prefix`   — parent flagged, `W` continues into `k`  (`r ↦ preC (plus1 s) r`);
* `winR_end`      — parent flagged, `W` ends at the junction;
* `wtopR_wrap`    — parent unflagged, `W` starts at the root of `k`  (`r ↦ node S s [r]`);
* `IR_prefix`     — parent unflagged, any option of `k`;
* `attR_junction` — parent unflagged, a new branch hangs at the parent node.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- Prefix the sequence of the root run. -/
def preC (s : List ℕ) : CT → CT
  | node S y ks => node S (s ++ y) ks

theorem splits_shift {s y d1 d2 : List ℕ} (h : (d1, d2) ∈ splits y) : (s ++ d1, d2) ∈ splits (s ++ y) := by
  rw [mem_splits_iff] at h ⊢
  rcases h with ⟨f, hf, rfl, rfl⟩ | ⟨f, hf, rfl, rfl⟩
  · left
    refine ⟨s.length + f, by simp; omega, ?_, ?_⟩
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.take_length_add_append]
    · rw [List.drop_length_add_append]
  · right
    refine ⟨s.length + f, by simp; omega, ?_, ?_⟩
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.take_length_add_append]
    · rw [show s.length + f + 1 = s.length + (f + 1) by omega, List.drop_length_add_append]

theorem splits_junction {s y : List ℕ} (hs : s ≠ []) (hy : y ≠ []) : (s, y) ∈ splits (s ++ y) := by
  rw [mem_splits_iff]
  right
  have h1 : 0 < s.length := List.length_pos_iff.2 hs
  have h2 : 0 < y.length := List.length_pos_iff.2 hy
  refine ⟨s.length - 1, by simp; omega, ?_, ?_⟩
  · rw [show s.length - 1 + 1 = s.length by omega]
    simpa using (List.take_length_add_append (l₁ := s) (l₂ := y) 0).symm
  · rw [show s.length - 1 + 1 = s.length by omega]
    simpa using (List.drop_length_add_append (l₁ := s) (l₂ := y) 0).symm

theorem plus1_append (a b : List ℕ) : plus1 (a ++ b) = plus1 a ++ plus1 b := by simp [plus1]

/-- Parent flagged, `W` continues into the run. -/
theorem winR_prefix (v : ℕ) (S : Finset ℕ) (yk : List ℕ) (kk : List CT) (s : List ℕ) {r : CT} {c : Finset ℕ}
    (h : WinR v (node S yk kk) r c) :
    ∃ r', WinR v (node S (s ++ yk) kk) r' c ∧ r' = preC (plus1 s) r := by
  rcases h with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
  · exact ⟨_, Or.inl ⟨s ++ d1, d2, splits_shift hd, by rw [plus1_append], rfl⟩, by simp [preC, plus1_append]⟩
  · exact ⟨_, Or.inr ⟨kids, cv, hk, by rw [plus1_append], rfl⟩, by simp [preC, plus1_append]⟩

/-- Parent flagged, `W` ends at the junction. -/
theorem winR_end (v : ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ []) (hy : yk ≠ []) :
    WinR v (node S (s ++ yk) kk) (node (insert v S) (plus1 s) [node S yk kk]) S :=
  Or.inl ⟨s, yk, splits_junction hs hy, rfl, rfl⟩

/-- Parent unflagged, `W` starts at the root of the run. -/
theorem wtopR_wrap (v : ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ []) (hy : yk ≠ [])
    {r : CT} {c : Finset ℕ} (h : WinR v (node S yk kk) r c) :
    WtopR v (node S (s ++ yk) kk) (node S s [r]) c :=
  Or.inr ⟨s, yk, r, splits_junction hs hy, h, rfl⟩

/-- Parent unflagged, a new branch hangs at the parent node. -/
theorem attR_junction (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ [])
    (hy : yk ≠ []) {chain : List (Finset ℕ)} {M : Finset ℕ} (h : (chain, M) ∈ allChains S N) :
    AttR v N (node S (s ++ yk) kk) (node S s [pathSubtree v chain M, node S yk kk]) :=
  ⟨chain, M, h, Or.inr ⟨s, yk, splits_junction hs hy, rfl⟩⟩

/-- Parent unflagged, any option of the run lifts to the exact run. -/
theorem IR_prefix (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) {yk : List ℕ} (kk : List CT) {s : List ℕ} (hs : s ≠ [])
    (hy : yk ≠ []) {r : CT} (h : IR v N (node S yk kk) r) :
    ∃ r', IR v N (node S (s ++ yk) kk) r' ∧
      ((r.S = S ∧ r' = preC s r) ∨ (r.S = insert v S ∧ r' = node S s [r])) := by
  cases h with
  | top hw hN =>
    rename_i c
    rcases hw with hw | ⟨d1, d2, X, hd, hX, rfl⟩
    · refine ⟨node S s [r], IR.top (wtopR_wrap v S kk hs hy hw) hN, Or.inr ⟨?_, rfl⟩⟩
      rcases hw with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩ <;> rfl
    · exact ⟨node S (s ++ d1) [X], IR.top (Or.inr ⟨s ++ d1, d2, X, splits_shift hd, hX, rfl⟩) hN,
        Or.inl ⟨rfl, rfl⟩⟩
  | att hNS ha =>
    obtain ⟨chain, M, hcm, hr⟩ := ha
    rcases hr with rfl | ⟨d1, d2, hd, rfl⟩
    · exact ⟨node S (s ++ yk) (kk ++ [pathSubtree v chain M]),
        IR.att hNS ⟨chain, M, hcm, Or.inl rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨node S (s ++ d1) [pathSubtree v chain M, node S d2 kk],
        IR.att hNS ⟨chain, M, hcm, Or.inr ⟨s ++ d1, d2, splits_shift hd, rfl⟩⟩, Or.inl ⟨rfl, rfl⟩⟩
  | kid hk =>
    rename_i pre k post r1
    exact ⟨node S (s ++ yk) (pre ++ r1 :: post), IR.kid hk, Or.inl ⟨rfl, rfl⟩⟩

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.IntroSetup` -/

section
/-!
# Set-up for the main induction of `char_intro_dom` (work package C4, part 9)

The source `a = norm (uT P)` and the target `T = norm (fT v P)` of a flagged profile tree `P = node S e w ks` are both
`normF` of a list of kids obtained from the kept kids; on the source side the kept kids are sorted by key
(`order`).  Shapes of `a`: *non-merge* (`node S [e] (order.map gA)`) or *merge* (a single kept kid with the same label).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## comparing normal forms up to a permutation -/

theorem align' {S1 : Finset ℕ} {y y' : List ℕ} (hy : Dom y y') {X : Type} (τ : List X) (h1 h2 : X → CT)
    (L2 : List CT) (hperm : (τ.map h2).Perm L2) (hd : ∀ K ∈ τ, DomC (h1 K) (h2 K))
    (hkd : L2.Pairwise (fun a b => key S1 a ≠ key S1 b)) :
    DomC (normF S1 y (τ.map h1)) (normF S1 y' L2) := by
  have hL : DomCL (τ.map h1) (τ.map h2) := by
    rw [domCL_iff, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 hd
  have h := normF_mono (S := S1) hy hL
  rw [normF_perm hperm hkd] at h
  exact h

/-- The merge comparison: a run `node S' y1 kids1` dominating the kid `T1` and prefixed by the exact entry list `e'`
is dominated by the merge of `e'` with `T1`. -/
theorem merge_cmp {S' : Finset ℕ} {e' : List ℕ} (he : e' ≠ []) {y1 : List ℕ} {kids1 : List CT} {T1 : CT}
    (h : DomC (norm (CT.node S' y1 kids1)) T1) (hk : keep S' T1 = true) :
    DomC (norm (CT.node S' (e' ++ y1) kids1)) (normF S' e' [T1]) := by
  set F1 := (kids1.map norm).filter (keep S') with hF1
  have hF : ∀ k ∈ F1, keep S' k = true := fun k hk => (List.mem_filter.1 hk).2
  have h1 : norm (CT.node S' y1 kids1) = normF S' y1 F1 := norm_node' _ _ _
  have h2 : norm (CT.node S' (e' ++ y1) kids1) = normF S' (e' ++ y1) F1 := norm_node' _ _ _
  rw [h1] at h
  have hkeep : keep S' (normF S' y1 F1) = true := by rw [domC_keep S' h]; exact hk
  have hML := normF_merge S' he hF (y := y1)
  rw [List.filter_cons_of_pos hkeep, List.filter_nil] at hML
  rw [h2]
  have hA : DomC (normF S' (e' ++ y1) F1) (normF S' (typical (e' ++ y1)) F1) :=
    normF_mono (domEquiv_typical (e' ++ y1)).2 (domCL_iff.2 (List.forall₂_same.2 (fun k _ => DomC.refl k)))
  have hB : DomC (normF S' e' [normF S' y1 F1]) (normF S' e' [T1]) :=
    normF_mono (Dom.refl e') ⟨h, trivial⟩
  rw [← hML] at hA
  exact DomC.trans hA hB

theorem winR_cov_ge {v : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} {r : CT} {c : Finset ℕ}
    (h : WinR v (node S y ks) r c) : S ⊆ c := by
  rcases h with ⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩
  · exact subset_rfl
  · exact Finset.subset_union_left

theorem kidR_of_forall (v : ℕ) {X : Type} (g : X → CT) (rk : X → CT)
    (ck : X → Finset ℕ) : ∀ τ : List X,
    (∀ K ∈ τ, (rk K = g K ∧ ck K = ∅) ∨ WinR v (g K) (rk K) (ck K)) →
    ∃ cv, KidR v (τ.map g) (τ.map rk) cv ∧ ∀ K ∈ τ, ck K ⊆ cv := by
  intro τ
  induction τ with
  | nil => intro _; exact ⟨∅, ⟨rfl, rfl⟩, by simp⟩
  | cons K τ ih =>
    intro h
    obtain ⟨cv, hkid, hsub⟩ := ih (fun K' hK' => h K' (List.mem_cons_of_mem _ hK'))
    refine ⟨ck K ∪ cv, ⟨rk K, τ.map rk, ck K, cv, rfl, rfl, ?_, hkid⟩, ?_⟩
    · rcases h K List.mem_cons_self with ⟨h1, h2⟩ | h1
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · intro K' hK'
      rcases List.mem_cons.1 hK' with rfl | hK'
      · exact Finset.subset_union_left
      · exact (hsub K' hK').trans Finset.subset_union_right

namespace FT

/-- The normalised source profile of a kid. -/
def gA (K : FT) : CT := norm (uT K)
/-- The normalised target profile of a kid. -/
def fN (v : ℕ) (K : FT) : CT := norm (fT v K)
/-- The kids that survive the pruning on the source side. -/
def kept (S : Finset ℕ) (ks : List FT) : List FT := ks.filter (fun K => keep S (gA K))
/-- ... in the order of the source characteristic. -/
def order (S : Finset ℕ) (ks : List FT) : List FT :=
  (kept S ks).mergeSort (fun A B => decide (key S (gA A) ≤ key S (gA B)))
/-- The kids that survive the pruning on the target side. -/
def fkept (v : ℕ) (S1 : Finset ℕ) (ks : List FT) : List FT := ks.filter (fun K => keep S1 (fN v K))

theorem mem_kept {S : Finset ℕ} {ks : List FT} {K : FT} : K ∈ kept S ks ↔ K ∈ ks ∧ keep S (gA K) = true := by
  simp [kept]

theorem order_perm (S : Finset ℕ) (ks : List FT) : (order S ks).Perm (kept S ks) :=
  List.mergeSort_perm _ _

theorem sort_eq (S : Finset ℕ) (ks : List FT) :
    sortKids S ((kept S ks).map gA) = (order S ks).map gA := by
  unfold sortKids order
  exact (List.map_mergeSort (l := kept S ks) (f := gA)
    (r := fun A B => decide (key S (gA A) ≤ key S (gA B)))
    (s := fun a b => decide (key S a ≤ key S b)) (fun a _ b _ => rfl)).symm

theorem a_eq (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    norm (uT (node S e w ks)) = normF S [e] ((kept S ks).map gA) := by
  rw [uT_node, norm_node']
  congr 1
  rw [List.map_map]
  show (ks.map (fun K => norm (uT K))).filter (keep S) = (ks.filter (fun K => keep S (gA K))).map gA
  rw [List.filter_map]
  rfl

theorem T_eq (v : ℕ) (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    norm (fT v (node S e w ks)) =
      normF (if w then insert v S else S) [if w then e + 1 else e]
        ((fkept v (if w then insert v S else S) ks).map (fN v)) := by
  rw [fT_node, norm_node']
  congr 1
  rw [List.map_map]
  show (ks.map (fun K => norm (fT v K))).filter (keep (if w then insert v S else S)) =
    (ks.filter (fun K => keep (if w then insert v S else S) (fN v K))).map (fN v)
  rw [List.filter_map]
  rfl

theorem a_nonmerge (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT)
    (h : ∀ K1, kept S ks = [K1] → (gA K1).S ≠ S) :
    norm (uT (node S e w ks)) = CT.node S [e] ((order S ks).map gA) := by
  rw [a_eq]
  have hs := sort_eq S ks
  generalize hσ : kept S ks = σ at hs ⊢
  have hord : order S ks = σ.mergeSort (fun A B => decide (key S (gA A) ≤ key S (gA B))) := by
    rw [order, hσ]
  match σ, hσ, hord, hs with
  | [], _, hord, hs =>
    rw [hord]; simp [normF_nil]
  | [K1], hσ, hord, hs =>
    rw [hord]
    simp only [List.map_cons, List.map_nil]
    rw [normF_single, if_neg (h K1 hσ)]
    simp
  | K1 :: K2 :: rest, hσ, hord, hs =>
    simp only [List.map_cons] at hs ⊢
    rw [normF_ge2, hs]

theorem a_merge (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) {K1 : FT} (hσ : kept S ks = [K1])
    (hS : (gA K1).S = S) :
    norm (uT (node S e w ks)) = CT.node S (typical ([e] ++ (gA K1).y)) (gA K1).kids := by
  rw [a_eq, hσ]
  simp only [List.map_cons, List.map_nil]
  rw [normF_single, if_pos hS]

end FT

end Lax117284Proofs.Treewidth.Chars

end
