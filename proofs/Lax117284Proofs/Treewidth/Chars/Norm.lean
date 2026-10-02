import Lax117284Proofs.Treewidth.Chars.Defs
import Lax117284Proofs.Treewidth.Seq.Concat
import Lax117284Proofs.Treewidth.Seq.Structure

/-!
# The normal form `norm`: basic API and idempotence (work package C1)

* `keep S k` — the kid `k` of a run labelled `S` is *not* junk (a leaf run whose label lies in `S` is junk);
* `normF S y F` — `normNode` as a function of the *filtered* kids (`normNode_eq` is `rfl`);
* `Nf` — the syntactic normal forms; `norm_nf : Nf (norm q)`, `nf_norm : Nf q → norm q = q`, hence `norm_idem`;
* `verts_norm : verts (norm q) = verts q`, `S_norm : (norm q).S = q.S`;
* sorting API (`sortKids` is a stable merge sort on keys).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-! ## `keep`, `normF` -/

/-- The kid survives the pruning (rule (i)). -/
def keep (S : Finset ℕ) (k : CT) : Bool := !(k.isLeaf && decide (k.S ⊆ S))

theorem keep_eq_true_iff {S : Finset ℕ} {k : CT} : keep S k = true ↔ ¬ (k.kids = [] ∧ k.S ⊆ S) := by
  simp [keep, isLeaf]
  tauto

theorem keep_eq_false_iff {S : Finset ℕ} {k : CT} : keep S k = false ↔ (k.kids = [] ∧ k.S ⊆ S) := by
  have := @keep_eq_true_iff S k
  rw [← Bool.not_eq_true, this]; tauto

/-- `normNode` as a function of the filtered kids. -/
def normF (S : Finset ℕ) (y : List ℕ) : List CT → CT
  | [] => node S (y.take 1) []
  | [k] => if k.S = S then node S (typical (y ++ k.y)) k.kids else node S y [k]
  | ks' => node S y (sortKids S ks')

theorem normNode_eq (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    normNode S y ks = normF S y (ks.filter (keep S)) := rfl

theorem normF_nil (S : Finset ℕ) (y : List ℕ) : normF S y [] = node S (y.take 1) [] := rfl
theorem normF_single (S : Finset ℕ) (y : List ℕ) (k : CT) :
    normF S y [k] = if k.S = S then node S (typical (y ++ k.y)) k.kids else node S y [k] := rfl
theorem normF_ge2 (S : Finset ℕ) (y : List ℕ) (a b : CT) (t : List CT) :
    normF S y (a :: b :: t) = node S y (sortKids S (a :: b :: t)) := rfl

theorem normL_eq_map (ks : List CT) : normL ks = ks.map norm := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [normL, ih]

theorem relabelL_eq_map (f : Finset ℕ → Finset ℕ) (ks : List CT) : relabelL f ks = ks.map (relabel f) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [relabelL, ih]

theorem norm_node' (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    norm (node S y ks) = normF S y ((ks.map norm).filter (keep S)) := by
  rw [norm_node, normL_eq_map]; rfl

theorem relabel_node (f : Finset ℕ → Finset ℕ) (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    relabel f (node S y ks) = node (f S) y (ks.map (relabel f)) := by
  simp [relabel, relabelL_eq_map]

theorem verts_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    verts (node S y ks) = S ∪ vertsL ks := rfl

theorem mem_vertsL {v : ℕ} {ks : List CT} : v ∈ vertsL ks ↔ ∃ k ∈ ks, v ∈ verts k := by
  induction ks with
  | nil => simp [vertsL]
  | cons k ks ih => simp [vertsL, ih]

theorem mem_verts {v : ℕ} {S : Finset ℕ} {y : List ℕ} {ks : List CT} :
    v ∈ verts (node S y ks) ↔ v ∈ S ∨ ∃ k ∈ ks, v ∈ verts k := by
  simp [verts_node, mem_vertsL]

theorem S_le_verts (k : CT) : k.S ⊆ verts k := by
  cases k; simp [S, verts]

theorem verts_le_of_kid {q k : CT} (h : k ∈ q.kids) : verts k ⊆ verts q := by
  cases q with
  | node S y ks =>
    intro v hv
    exact mem_verts.2 (Or.inr ⟨k, h, hv⟩)

/-! ## the sorting -/

theorem sortKids_perm (S : Finset ℕ) (l : List CT) : (sortKids S l).Perm l := List.mergeSort_perm _ _

theorem mem_sortKids {S : Finset ℕ} {l : List CT} {k : CT} : k ∈ sortKids S l ↔ k ∈ l :=
  (sortKids_perm S l).mem_iff

theorem length_sortKids (S : Finset ℕ) (l : List CT) : (sortKids S l).length = l.length :=
  (sortKids_perm S l).length_eq

theorem sortKids_pairwise (S : Finset ℕ) (l : List CT) :
    (sortKids S l).Pairwise (fun a b => key S a ≤ key S b) := by
  have := List.pairwise_mergeSort (le := fun a b : CT => decide (key S a ≤ key S b))
    (by intro a b c h1 h2; simp at *; exact le_trans h1 h2)
    (by intro a b; simp; exact le_total _ _) l
  simpa [sortKids] using this

theorem sortKids_of_pairwise {S : Finset ℕ} {l : List CT} (h : l.Pairwise (fun a b => key S a ≤ key S b)) :
    sortKids S l = l := by
  unfold sortKids
  exact List.mergeSort_of_pairwise (by simpa using h)

theorem sortKids_ne_nil {S : Finset ℕ} {l : List CT} (h : l ≠ []) : sortKids S l ≠ [] := by
  intro e; apply h
  have := length_sortKids S l; rw [e] at this
  exact List.length_eq_zero_iff.1 this.symm

theorem sortKids_idem (S : Finset ℕ) (l : List CT) : sortKids S (sortKids S l) = sortKids S l :=
  sortKids_of_pairwise (sortKids_pairwise S l)

/-! ## normal forms and idempotence -/

/-- The shape of a normalised kid list below a run labelled `S`. -/
def Shaped (S : Finset ℕ) (ks : List CT) : Prop :=
  ks ≠ [] ∧ (∀ k ∈ ks, ¬ (k.kids = [] ∧ k.S ⊆ S)) ∧ (∀ k, ks = [k] → k.S ≠ S) ∧
    (2 ≤ ks.length → sortKids S ks = ks)

mutual
/-- Syntactic normal forms. -/
def Nf : CT → Prop
  | node S y ks => NfL ks ∧ (ks = [] → y.length ≤ 1) ∧ (ks ≠ [] → Shaped S ks)
def NfL : List CT → Prop
  | [] => True
  | k :: ks => Nf k ∧ NfL ks
end

theorem NfL_iff {ks : List CT} : NfL ks ↔ ∀ k ∈ ks, Nf k := by
  induction ks with
  | nil => simp [NfL]
  | cons k ks ih => simp [NfL, ih]

theorem normNode_nf (S : Finset ℕ) (y : List ℕ) (K : List CT) (h : ∀ k ∈ K, Nf k) :
    Nf (normF S y (K.filter (keep S))) := by
  have hf : ∀ k ∈ K.filter (keep S), Nf k ∧ ¬ (k.kids = [] ∧ k.S ⊆ S) := by
    intro k hk
    rw [List.mem_filter] at hk
    exact ⟨h k hk.1, keep_eq_true_iff.1 hk.2⟩
  generalize K.filter (keep S) = F at hf
  match F, hf with
  | [], _ =>
    simp only [normF_nil, Nf]
    refine ⟨trivial, fun _ => by simp, fun h => absurd rfl h⟩
  | [k], hf =>
    rw [normF_single]
    obtain ⟨hk, hkp⟩ := hf k (by simp)
    split_ifs with hS
    · -- merge
      obtain ⟨Sk, yk, kk⟩ := k
      simp only [Nf, CT.S] at hk hS hkp
      have hkk : kk ≠ [] := by
        intro e; subst e; exact hkp ⟨rfl, by rw [hS]⟩
      subst hS
      simp only [Nf, CT.kids]
      exact ⟨hk.1, fun e => absurd e hkk, fun _ => hk.2.2 hkk⟩
    · simp only [Nf]
      refine ⟨⟨hk, trivial⟩, fun e => by simp at e, fun _ => ?_⟩
      refine ⟨by simp, by simpa using hkp, ?_, by simp⟩
      intro k' hk'
      have : k = k' := by simpa using hk'
      subst this; exact hS
  | a :: b :: t, hf =>
    rw [normF_ge2]
    simp only [Nf]
    have hne : sortKids S (a :: b :: t) ≠ [] := sortKids_ne_nil (by simp)
    refine ⟨?_, fun e => absurd e hne, fun _ => ?_⟩
    · rw [NfL_iff]; intro k hk; rw [mem_sortKids] at hk; exact (hf k hk).1
    · refine ⟨hne, ?_, ?_, ?_⟩
      · intro k hk; rw [mem_sortKids] at hk; exact (hf k hk).2
      · intro k hk; have := length_sortKids S (a :: b :: t); rw [hk] at this; simp at this
      · intro _; exact sortKids_idem S _

mutual
theorem norm_nf : ∀ q : CT, Nf (norm q)
  | node S y ks => by
    rw [norm_node']
    apply normNode_nf
    have := normL_nf ks
    rw [normL_eq_map, NfL_iff] at this
    exact this
theorem normL_nf : ∀ ks : List CT, NfL (normL ks)
  | [] => trivial
  | k :: ks => ⟨norm_nf k, normL_nf ks⟩
end

theorem norm_of_nf_node (S : Finset ℕ) (y : List ℕ) (ks : List CT)
    (h1 : ks = [] → y.length ≤ 1) (h2 : ks ≠ [] → Shaped S ks) : normNode S y ks = node S y ks := by
  rw [normNode_eq]
  by_cases hk : ks = []
  · subst hk
    simp only [List.filter_nil, normF_nil]
    rw [List.take_of_length_le (h1 rfl)]
  · obtain ⟨-, hp, hs, hsort⟩ := h2 hk
    have hf : ks.filter (keep S) = ks := by
      rw [List.filter_eq_self]
      intro k hk'; exact keep_eq_true_iff.2 (hp k hk')
    rw [hf]
    match ks, hk, hs, hsort with
    | [k], _, hs, _ => rw [normF_single, if_neg (hs k rfl)]
    | a :: b :: t, _, _, hsort => rw [normF_ge2, hsort (by simp)]

mutual
theorem nf_norm : ∀ q : CT, Nf q → norm q = q
  | node S y ks, h => by
    rw [norm_node, normL_of_nfL ks h.1]
    exact norm_of_nf_node S y ks h.2.1 h.2.2
theorem normL_of_nfL : ∀ ks : List CT, NfL ks → normL ks = ks
  | [], _ => rfl
  | k :: ks, h => by rw [normL, nf_norm k h.1, normL_of_nfL ks h.2]
end

/-- **`norm` is idempotent.** -/
theorem norm_idem (p : CT) : norm (norm p) = norm p := nf_norm _ (norm_nf p)

/-! ## `norm` keeps the vertices and the root label -/

theorem normF_S (S : Finset ℕ) (y : List ℕ) (F : List CT) : (normF S y F).S = S := by
  match F with
  | [] => rfl
  | [k] => rw [normF_single]; split_ifs <;> rfl
  | a :: b :: t => rfl

theorem S_norm (q : CT) : (norm q).S = q.S := by
  cases q with
  | node S y ks => rw [norm_node']; exact normF_S _ _ _

/-- Pruned kids lie inside the parent's label. -/
theorem verts_le_of_not_keep {S : Finset ℕ} {k : CT} (h : keep S k = false) : verts k ⊆ S := by
  obtain ⟨h1, h2⟩ := keep_eq_false_iff.1 h
  cases k with
  | node Sk yk kk =>
    simp only [CT.kids, CT.S] at h1 h2; subst h1
    simpa [verts, vertsL] using h2

theorem mem_verts_normF {S : Finset ℕ} {y : List ℕ} {K : List CT} {v : ℕ}
    (hv : v ∈ verts (normF S y (K.filter (keep S)))) : v ∈ S ∨ ∃ k ∈ K, v ∈ verts k := by
  have hf : ∀ k ∈ K.filter (keep S), k ∈ K := fun k hk => (List.mem_filter.1 hk).1
  generalize K.filter (keep S) = F at hv hf
  match F, hv, hf with
  | [], hv, _ => left; simpa [normF_nil, verts, vertsL] using hv
  | [k], hv, hf =>
    rw [normF_single] at hv
    split_ifs at hv with hS
    · rcases mem_verts.1 hv with h | ⟨k', hk', h⟩
      · left; exact h
      · right; refine ⟨k, hf k (by simp), ?_⟩
        exact verts_le_of_kid (q := k) hk' h
    · rcases mem_verts.1 hv with h | ⟨k', hk', h⟩
      · left; exact h
      · right; simp at hk'; subst hk'; exact ⟨k', hf k' (by simp), h⟩
  | a :: b :: t, hv, hf =>
    rw [normF_ge2] at hv
    rcases mem_verts.1 hv with h | ⟨k', hk', h⟩
    · left; exact h
    · right; rw [mem_sortKids] at hk'; exact ⟨k', hf k' hk', h⟩

theorem mem_verts_of_mem_verts_normF {S : Finset ℕ} {y : List ℕ} {K : List CT} {v : ℕ}
    (hv : ∃ k ∈ K, v ∈ verts k) : v ∈ verts (normF S y (K.filter (keep S))) ∨ v ∈ S := by
  obtain ⟨k, hk, hvk⟩ := hv
  by_cases hkeep : keep S k = true
  · left
    have hmem : k ∈ K.filter (keep S) := List.mem_filter.2 ⟨hk, hkeep⟩
    have hf : ∀ k' ∈ K.filter (keep S), True := fun _ _ => trivial
    generalize K.filter (keep S) = F at hmem
    match F, hmem with
    | [], hmem => simp at hmem
    | [k'], hmem =>
      have : k = k' := by simpa using hmem
      subst this
      rw [normF_single]
      split_ifs with hS
      · -- merged: `v ∈ verts k`
        cases k with
        | node Sk yk kk =>
          simp only [CT.S] at hS; subst hS
          rw [mem_verts]; rw [mem_verts] at hvk; exact hvk
      · rw [mem_verts]; right; exact ⟨k, by simp, hvk⟩
    | a :: b :: t, hmem =>
      rw [normF_ge2, mem_verts]; right
      exact ⟨k, mem_sortKids.2 hmem, hvk⟩
  · right
    rw [Bool.not_eq_true] at hkeep
    exact verts_le_of_not_keep hkeep hvk

mutual
theorem verts_norm : ∀ q : CT, verts (norm q) = verts q
  | node S y ks => by
    have ih := vertsL_normL ks
    have hK : ∀ v, (∃ k ∈ ks.map norm, v ∈ verts k) ↔ (∃ k ∈ ks, v ∈ verts k) := by
      intro v; rw [← mem_vertsL, ← mem_vertsL, ← normL_eq_map, ih]
    ext v
    rw [norm_node']
    constructor
    · intro hv
      rcases mem_verts_normF hv with h | h
      · exact mem_verts.2 (Or.inl h)
      · exact mem_verts.2 (Or.inr ((hK v).1 h))
    · intro hv
      have hSv : S ⊆ verts (normF S y ((ks.map norm).filter (keep S))) := by
        have := S_le_verts (normF S y ((ks.map norm).filter (keep S)))
        rwa [normF_S] at this
      rcases mem_verts.1 hv with h | h
      · exact hSv h
      · rcases mem_verts_of_mem_verts_normF ((hK v).2 h) with h' | h'
        · exact h'
        · exact hSv h'
theorem vertsL_normL : ∀ ks : List CT, vertsL (normL ks) = vertsL ks
  | [] => rfl
  | k :: ks => by rw [normL, vertsL, vertsL, verts_norm k, vertsL_normL ks]
end

end CT

end Lax117284Proofs.Treewidth.Chars
