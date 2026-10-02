import Lax117284Proofs.Treewidth.Chars.IntroNorm

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

theorem cov_node (S : Finset ℕ) (e : ℕ) (w : Bool) (ks : List FT) :
    cov (node S e w ks) = (if w then S else ∅) ∪ ks.foldr (fun k acc => cov k ∪ acc) ∅ := by
  simp only [cov]
  congr 1
  induction ks with
  | nil => rfl
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
theorem fT_of_not_occ (v : ℕ) : ∀ K : FT, occ K = false → fT v K = uT K
  | node S e w ks, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [fT, uT, if_neg (by simp : ¬ (false = true))]
    rw [fTL_of_not_occ v ks h2]
theorem fTL_of_not_occ (v : ℕ) : ∀ ks : List FT, occL ks = false → fTL v ks = uTL ks
  | [], _ => rfl
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_false_iff] at h
    simp only [fTL, uTL]
    rw [fT_of_not_occ v k h.1, fTL_of_not_occ v ks h.2]
end

theorem occ_of_occL_false {ks : List FT} (h : occL ks = false) : ∀ k ∈ ks, occ k = false := by
  intro k hk
  rw [occL_eq_any] at h
  have := List.any_eq_false.1 h k hk
  simpa using this

/-! ## labels and vertices -/

mutual
theorem verts_uT_not_v (v : ℕ) : ∀ K : FT, FOk v K → v ∉ CT.verts (uT K)
  | node S e w ks, h => by
    rw [uT, CT.verts_node, uTL_eq_map]
    simp only [Finset.mem_union, not_or]
    refine ⟨h.1, ?_⟩
    rw [CT.mem_vertsL]
    rintro ⟨k, hk, hv⟩
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk
    exact verts_uT_not_v v k0 ((FOkL_iff.1 h.2.2.2.2) k0 hk0) hv
end

mutual
theorem cov_le_verts : ∀ K : FT, cov K ⊆ CT.verts (uT K)
  | node S e w ks => by
    rw [uT, CT.verts_node]
    simp only [cov]
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · split_ifs at h with hw
      · exact Finset.mem_union_left _ h
      · simp at h
    · exact Finset.mem_union_right _ (covL_le_vertsL ks h)
theorem covL_le_vertsL : ∀ ks : List FT, covL ks ⊆ CT.vertsL (uTL ks)
  | [] => by simp [covL]
  | k :: ks => by
    intro x hx
    simp only [covL, Finset.mem_union] at hx
    simp only [uTL, CT.vertsL, Finset.mem_union]
    rcases hx with h | h
    · exact Or.inl (cov_le_verts k h)
    · exact Or.inr (covL_le_vertsL ks h)
end

mutual
theorem v_mem_verts_fT (v : ℕ) : ∀ K : FT, occ K = true → v ∈ CT.verts (fT v K)
  | node S e w ks, h => by
    rw [fT, CT.verts_node]
    simp only [occ, Bool.or_eq_true] at h
    rcases h with hw | hk
    · subst hw
      exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ (v_mem_vertsL_fTL v ks hk)
theorem v_mem_vertsL_fTL (v : ℕ) : ∀ ks : List FT, occL ks = true → v ∈ CT.vertsL (fTL v ks)
  | [], h => by simp [occL] at h
  | k :: ks, h => by
    simp only [occL, Bool.or_eq_true] at h
    simp only [fTL, CT.vertsL, Finset.mem_union]
    rcases h with h | h
    · exact Or.inl (v_mem_verts_fT v k h)
    · exact Or.inr (v_mem_vertsL_fTL v ks h)
end

/-! ## flag correspondences -/

mutual
theorem nested_flag (v : ℕ) : ∀ (K : FT), FOk v K → (K.w = true ∨ occ K = false) → ∀ σ : Finset ℕ,
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
      exact nestedL_flag v ks (FOkL_iff.1 hok.2.2.2.2)
        (fun k hk => by
          by_cases hk' : occ k = true
          · exact Or.inl (hkids k hk hk')
          · exact Or.inr (by simpa using hk')) S
theorem nestedL_flag (v : ℕ) : ∀ (ks : List FT), (∀ k ∈ ks, FOk v k) → (∀ k ∈ ks, k.w = true ∨ occ k = false) →
    ∀ σ : Finset ℕ, (NestedL (insert v σ) (fTL v ks) ↔ NestedL σ (uTL ks))
  | [], _, _, σ => by simp [fTL, uTL, NestedL]
  | k :: ks, hok, hK, σ => by
    have h1 := nested_flag v k (hok k (by simp)) (hK k (by simp)) σ
    have h2 := nestedL_flag v ks (fun k' hk' => hok k' (by simp [hk'])) (fun k' hk' => hK k' (by simp [hk'])) σ
    simp only [fTL, uTL, NestedL]
    rw [h1, h2]
end

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
