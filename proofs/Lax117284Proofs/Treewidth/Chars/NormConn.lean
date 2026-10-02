import Lax117284Proofs.Treewidth.Chars.Norm

/-!
# `Conn` and `norm` (work package C1)

* `Conn_relabel_erase`, `verts_relabel_erase` — forgetting a vertex keeps connectedness;
* `collapse` — a connected run tree all of whose vertices lie in its root label normalises to one leaf run;
* `Conn_norm` — `norm` preserves connectedness;
* `survivors_keys_distinct` — the un-pruned normalised kids of a connected run have pairwise distinct keys
  (this is why the sorting of `norm` is canonical on connected trees).
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

theorem ConnL_iff {ks : List CT} : ConnL ks ↔ ∀ k ∈ ks, Conn k := by
  induction ks with
  | nil => simp [ConnL]
  | cons k ks ih => simp [ConnL, ih]

/-- The clauses of `Conn (node S y ks)`. -/
def KidsConn (S : Finset ℕ) (ks : List CT) : Prop :=
  ConnL ks ∧ (∀ k ∈ ks, ∀ v ∈ S, v ∈ verts k → v ∈ k.S) ∧
      ks.Pairwise (fun k₁ k₂ => ∀ v, v ∈ verts k₁ → v ∈ verts k₂ → v ∈ S)

theorem conn_node {S : Finset ℕ} {y : List ℕ} {ks : List CT} : Conn (node S y ks) ↔ KidsConn S ks := Iff.rfl

/-! ## forgetting a vertex -/

theorem S_relabel (f : Finset ℕ → Finset ℕ) (q : CT) : (relabel f q).S = f q.S := by
  cases q; rfl

mutual
theorem mem_verts_relabel_erase_rec (x : ℕ) : ∀ (q : CT) (v : ℕ),
    v ∈ verts (relabel (fun S => S.erase x) q) ↔ v ≠ x ∧ v ∈ verts q
  | node S y ks, v => by
    rw [relabel_node, mem_verts, mem_verts, Finset.mem_erase, ← mem_vertsL, ← mem_vertsL,
      ← relabelL_eq_map, mem_vertsL_relabelL_rec x ks v]
    tauto
theorem mem_vertsL_relabelL_rec (x : ℕ) : ∀ (ks : List CT) (v : ℕ),
    v ∈ vertsL (relabelL (fun S => S.erase x) ks) ↔ v ≠ x ∧ v ∈ vertsL ks
  | [], v => by simp [relabelL, vertsL]
  | k :: ks, v => by
    rw [relabelL, vertsL, vertsL, Finset.mem_union, Finset.mem_union, mem_verts_relabel_erase_rec x k v,
      mem_vertsL_relabelL_rec x ks v]
    tauto
end

theorem mem_verts_relabel_erase_pair : (type_of% @mem_verts_relabel_erase_rec) ∧ (type_of% @mem_vertsL_relabelL_rec) :=
  ⟨@mem_verts_relabel_erase_rec, @mem_vertsL_relabelL_rec⟩

theorem mem_verts_relabel_erase : type_of% @mem_verts_relabel_erase_rec := mem_verts_relabel_erase_pair.1

theorem verts_relabel_erase (x : ℕ) (q : CT) :
    verts (relabel (fun S => S.erase x) q) = (verts q).erase x := by
  ext v; rw [mem_verts_relabel_erase, Finset.mem_erase]

mutual
theorem conn_relabel_erase_rec (x : ℕ) : ∀ q : CT, Conn q → Conn (relabel (fun S => S.erase x) q)
  | node S y ks, h => by
    have hL := connL_relabelL_erase_rec x ks h.1
    rw [relabel_node, conn_node]
    refine ⟨?_, ?_, ?_⟩
    · rw [← relabelL_eq_map]; exact hL
    · intro k' hk' v hv hvk
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      rw [S_relabel, Finset.mem_erase]
      rw [Finset.mem_erase] at hv
      rw [mem_verts_relabel_erase] at hvk
      exact ⟨hv.1, h.2.1 k hk v hv.2 hvk.2⟩
    · rw [List.pairwise_map]
      refine h.2.2.imp ?_
      intro a b hab v hva hvb
      rw [mem_verts_relabel_erase] at hva hvb
      rw [Finset.mem_erase]
      exact ⟨hva.1, hab v hva.2 hvb.2⟩
theorem connL_relabelL_erase_rec (x : ℕ) : ∀ ks : List CT, ConnL ks → ConnL (relabelL (fun S => S.erase x) ks)
  | [], _ => trivial
  | k :: ks, h => ⟨conn_relabel_erase_rec x k h.1, connL_relabelL_erase_rec x ks h.2⟩
end

theorem conn_relabel_erase_pair : (type_of% @conn_relabel_erase_rec) ∧ (type_of% @connL_relabelL_erase_rec) :=
  ⟨@conn_relabel_erase_rec, @connL_relabelL_erase_rec⟩

theorem conn_relabel_erase : type_of% @conn_relabel_erase_rec := conn_relabel_erase_pair.1

/-! ## collapse -/

mutual
/-- A connected run tree whose vertices all lie in its root label normalises to a single leaf run. -/
theorem norm_collapse : ∀ q : CT, Conn q → verts q ⊆ q.S → norm q = node q.S (q.y.take 1) []
  | node S y ks, h, hv => by
    rw [norm_node']
    have hk : ((ks.map norm).filter (keep S)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro n hn
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
      have hvk : verts k ⊆ k.S := fun v hvv =>
        h.2.1 k hk v (hv (verts_le_of_kid (q := node S y ks) hk hvv)) hvv
      have h1 : (norm k).kids = [] := by rw [norm_collapseL ks h.1 k hk hvk]; rfl
      have h2 : (norm k).S ⊆ S := by
        rw [S_norm]
        exact (S_le_verts k).trans ((verts_le_of_kid (q := node S y ks) hk).trans hv)
      intro hkeep
      exact (keep_eq_true_iff.1 hkeep) ⟨h1, h2⟩
    rw [hk]; rfl
theorem norm_collapseL : ∀ ks : List CT, ConnL ks → ∀ k ∈ ks, verts k ⊆ k.S → norm k = node k.S (k.y.take 1) []
  | [], _, k, hk, _ => by simp at hk
  | k' :: ks, h, k, hk, hv => by
    rcases List.mem_cons.1 hk with e | hk
    · rw [e] at hv ⊢; exact norm_collapse k' h.1 hv
    · exact norm_collapseL ks h.2 k hk hv
end

theorem collapseL {ks : List CT} (h : ConnL ks) {k : CT} (hk : k ∈ ks) (hv : verts k ⊆ k.S) :
    (norm k).kids = [] := by
  rw [norm_collapseL ks h k hk hv]; rfl

/-! ## survivors have distinct keys -/

theorem key_norm (S : Finset ℕ) (k : CT) : key S (norm k) = key S k := by
  simp [key, verts_norm]

/-- A kid of a connected run that survives the pruning owns a vertex. -/
theorem owns_of_keep {S : Finset ℕ} {ks : List CT} (h : KidsConn S ks) {k : CT} (hk : k ∈ ks)
    (hkeep : keep S (norm k) = true) : (verts k \ S).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
  have hvk : verts k ⊆ k.S := fun v hv => h.2.1 k hk v (hne hv) hv
  have h1 := collapseL h.1 hk hvk
  have h2 : (norm k).S ⊆ S := by
    rw [S_norm]; exact (S_le_verts k).trans hne
  exact (keep_eq_true_iff.1 hkeep) ⟨h1, h2⟩

theorem survivors_keys_distinct {S : Finset ℕ} {ks : List CT} (h : KidsConn S ks) :
    ((ks.map norm).filter (keep S)).Pairwise (fun a b => key S a ≠ key S b) := by
  rw [List.pairwise_filter, List.pairwise_map]
  refine h.2.2.imp_of_mem ?_
  intro a b ha hb hab hka hkb hkey
  rw [key_norm, key_norm] at hkey
  have hne := owns_of_keep h ha hka
  obtain ⟨u, hu⟩ := Finset.min_of_nonempty hne
  have hu' : u ∈ verts a \ S := Finset.mem_of_min hu
  have hu'' : u ∈ verts b \ S := Finset.mem_of_min (by unfold key at hkey; rw [← hkey]; exact hu)
  exact (Finset.mem_sdiff.1 hu').2 (hab u (Finset.mem_sdiff.1 hu').1 (Finset.mem_sdiff.1 hu'').1)

/-- Sorting a list with pairwise distinct keys gives strictly increasing keys. -/
theorem sortKids_strict {S : Finset ℕ} {F : List CT} (h : F.Pairwise (fun a b => key S a ≠ key S b)) :
    (sortKids S F).Pairwise (fun a b => key S a < key S b) := by
  have h1 : (sortKids S F).Pairwise (fun a b => key S a ≠ key S b) :=
    ((sortKids_perm S F).pairwise_iff (fun {x y} hxy => Ne.symm hxy)).2 h
  have h2 := sortKids_pairwise S F
  have := h1.and h2
  exact this.imp (fun ⟨a, b⟩ => lt_of_le_of_ne b a)

/-! ## `norm` preserves `Conn` -/

theorem kidsConn_map_norm {S : Finset ℕ} {ks : List CT} (h : KidsConn S ks) :
    (∀ n ∈ ks.map norm, ∀ v ∈ S, v ∈ verts n → v ∈ n.S) ∧
    (ks.map norm).Pairwise (fun a b => ∀ v, v ∈ verts a → v ∈ verts b → v ∈ S) := by
  refine ⟨?_, ?_⟩
  · intro n hn v hv hvn
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hn
    rw [verts_norm] at hvn; rw [S_norm]; exact h.2.1 k hk v hv hvn
  · rw [List.pairwise_map]
    refine h.2.2.imp ?_
    intro a b hab v hva hvb
    rw [verts_norm] at hva hvb; exact hab v hva hvb

theorem conn_normF {S : Finset ℕ} {y : List ℕ} {ks : List CT} (h : KidsConn S ks)
    (hn : ConnL (ks.map norm)) : Conn (normF S y ((ks.map norm).filter (keep S))) := by
  obtain ⟨h2, h3⟩ := kidsConn_map_norm h
  have hcn := ConnL_iff.1 hn
  have hsub : ∀ n ∈ (ks.map norm).filter (keep S), n ∈ ks.map norm := fun n hn => (List.mem_filter.1 hn).1
  have h3' : ((ks.map norm).filter (keep S)).Pairwise
      (fun a b => ∀ v, v ∈ verts a → v ∈ verts b → v ∈ S) := h3.sublist (List.filter_sublist)
  generalize (ks.map norm).filter (keep S) = F at hsub h3'
  match F, hsub, h3' with
  | [], _, _ => simp only [normF_nil, conn_node, KidsConn]; exact ⟨trivial, by simp, by simp⟩
  | [k], hsub, _ =>
    rw [normF_single]
    have hk := hsub k (by simp)
    split_ifs with hS
    · obtain ⟨Sk, yk, kk⟩ := k
      have hc := hcn _ hk
      simp only [CT.S] at hS; subst hS
      exact hc
    · simp only [conn_node, KidsConn]
      refine ⟨⟨hcn k hk, trivial⟩, ?_, by simp⟩
      intro k' hk'
      simp at hk'; subst hk'; exact h2 k' hk
  | a :: b :: t, hsub, h3' =>
    rw [normF_ge2, conn_node]
    refine ⟨?_, ?_, ?_⟩
    · rw [ConnL_iff]; intro k hk; rw [mem_sortKids] at hk; exact hcn k (hsub k hk)
    · intro k hk; rw [mem_sortKids] at hk; exact h2 k (hsub k hk)
    · exact ((sortKids_perm S _).pairwise_iff (fun {x y} hxy v hvy hvx => hxy v hvx hvy)).2 h3'

mutual
theorem conn_norm_rec : ∀ q : CT, Conn q → Conn (norm q)
  | node S y ks, h => by
    rw [norm_node']
    apply conn_normF h
    rw [← normL_eq_map]
    exact connL_normL_rec ks h.1
theorem connL_normL_rec : ∀ ks : List CT, ConnL ks → ConnL (normL ks)
  | [], _ => trivial
  | k :: ks, h => ⟨conn_norm_rec k h.1, connL_normL_rec ks h.2⟩
end

theorem conn_norm_pair : (type_of% @conn_norm_rec) ∧ (type_of% @connL_normL_rec) :=
  ⟨@conn_norm_rec, @connL_normL_rec⟩

theorem conn_norm : type_of% @conn_norm_rec := conn_norm_pair.1

end CT

end Lax117284Proofs.Treewidth.Chars
