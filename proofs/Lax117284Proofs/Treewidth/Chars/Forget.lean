import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.NormMono

/-!
# Forget (work package C1/C2a): `forgetC_wf`, `char_forget`

* `forgetC_wf` : `Wf B kmax c → Wf (B.erase x) kmax (forgetC x c)` (**new statement**).
* `char_forget` : the characteristic of a *connected* rooted tree relative to `B.erase x` is `forgetC x` of its
  characteristic relative to `B`.  (**Repaired statement**: the hypothesis `t.Conn` is necessary — without it the
  sorting of `norm` is not canonical and the equation is false; counterexample in the module docstring of
  `NormConfl`/the delivery report.)
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-- **`forgetC` preserves well-formedness.** -/
theorem forgetC_wf {B : Finset ℕ} {kmax : ℕ} {x : ℕ} {c : CT} (h : Wf B kmax c) :
    Wf (B.erase x) kmax (forgetC x c) := by
  have hc := conn_relabel_erase x c h.conn
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold forgetC; rw [verts_norm, verts_relabel_erase, h.verts_eq]
  · exact good_norm _ (loc_relabel_erase x c (loc_of_good c h.good)) hc
  · exact conn_norm _ hc
  · exact (maxEntry_norm_le _).trans (by rw [maxEntry_relabel]; exact h.bounded)

end CT

end Lax117284Proofs.Treewidth.Chars

namespace Lax117284Proofs.Treewidth.Trees.RT

open Lax117284Proofs.Treewidth.Chars

theorem profL_eq_map (B : Finset ℕ) (ks : List RT) : profL B ks = ks.map (prof B) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [profL, ih]

theorem prof_node (B X : Finset ℕ) (ks : List RT) :
    prof B (RT.node X ks) = CT.node (X ∩ B) [X.card] (ks.map (prof B)) := by
  rw [prof, profL_eq_map]

mutual
theorem relabel_prof_erase_rec (B : Finset ℕ) (x : ℕ) : ∀ t : RT,
    CT.relabel (fun S => S.erase x) (prof B t) = prof (B.erase x) t
  | .node X ks => by
    rw [prof, prof, CT.relabel, relabelL_profL_erase_rec B x ks, Finset.inter_erase]
theorem relabelL_profL_erase_rec (B : Finset ℕ) (x : ℕ) : ∀ ks : List RT,
    CT.relabelL (fun S => S.erase x) (profL B ks) = profL (B.erase x) ks
  | [] => rfl
  | k :: ks => by
    rw [profL, profL, CT.relabelL, relabel_prof_erase_rec B x k, relabelL_profL_erase_rec B x ks]
end

theorem relabel_prof_erase_pair : (type_of% @relabel_prof_erase_rec) ∧ (type_of% @relabelL_profL_erase_rec) :=
  ⟨@relabel_prof_erase_rec, @relabelL_profL_erase_rec⟩

theorem relabel_prof_erase : type_of% @relabel_prof_erase_rec := relabel_prof_erase_pair.1

mutual
theorem mem_verts_prof_rec (B : Finset ℕ) : ∀ (t : RT) (v : ℕ), v ∈ CT.verts (prof B t) ↔ v ∈ t.verts ∧ v ∈ B
  | .node X ks, v => by
    rw [prof, CT.verts_node, RT.verts, Finset.mem_union, Finset.mem_union, Finset.mem_inter,
      mem_vertsL_profL_rec B ks v]
    tauto
theorem mem_vertsL_profL_rec (B : Finset ℕ) : ∀ (ks : List RT) (v : ℕ),
    v ∈ CT.vertsL (profL B ks) ↔ v ∈ RT.vertsL ks ∧ v ∈ B
  | [], v => by simp [profL, CT.vertsL, RT.vertsL]
  | k :: ks, v => by
    rw [profL, CT.vertsL, RT.vertsL, Finset.mem_union, Finset.mem_union, mem_verts_prof_rec B k v,
      mem_vertsL_profL_rec B ks v]
    tauto
end

theorem mem_verts_prof_pair : (type_of% @mem_verts_prof_rec) ∧ (type_of% @mem_vertsL_profL_rec) :=
  ⟨@mem_verts_prof_rec, @mem_vertsL_profL_rec⟩

theorem mem_verts_prof : type_of% @mem_verts_prof_rec := mem_verts_prof_pair.1

theorem S_prof (B : Finset ℕ) (t : RT) : (prof B t).S = t.rootBag ∩ B := by
  cases t; rfl

mutual
theorem yne_prof_rec (B : Finset ℕ) : ∀ t : RT, CT.YNe (prof B t)
  | .node X ks => by
    rw [prof, CT.YNe]
    exact ⟨by simp, yneL_profL_rec B ks⟩
theorem yneL_profL_rec (B : Finset ℕ) : ∀ ks : List RT, CT.YNeL (profL B ks)
  | [] => trivial
  | k :: ks => ⟨yne_prof_rec B k, yneL_profL_rec B ks⟩
end

theorem yne_prof_pair : (type_of% @yne_prof_rec) ∧ (type_of% @yneL_profL_rec) :=
  ⟨@yne_prof_rec, @yneL_profL_rec⟩

theorem yne_prof : type_of% @yne_prof_rec := yne_prof_pair.1

mutual
theorem conn_prof_rec (B : Finset ℕ) : ∀ t : RT, t.Conn → CT.Conn (prof B t)
  | .node X ks, h => by
    rw [prof, CT.conn_node]
    obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff X ks).1 h
    refine ⟨?_, ?_, ?_⟩
    · exact connL_profL_rec B ks h1
    · intro k hk v hv hvk
      rw [profL_eq_map] at hk
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk
      rw [Finset.mem_inter] at hv
      rw [mem_verts_prof] at hvk
      rw [S_prof, Finset.mem_inter]
      exact ⟨h2 k0 hk0 v hv.1 hvk.1, hv.2⟩
    · rw [profL_eq_map, List.pairwise_map]
      refine h3.imp ?_
      intro a b hab v hva hvb
      rw [mem_verts_prof] at hva hvb
      rw [Finset.mem_inter]
      exact ⟨hab v hva.1 hvb.1, hva.2⟩
theorem connL_profL_rec (B : Finset ℕ) : ∀ ks : List RT, (∀ k ∈ ks, k.Conn) → CT.ConnL (profL B ks)
  | [], _ => trivial
  | k :: ks, h => ⟨conn_prof_rec B k (h k (by simp)), connL_profL_rec B ks (fun j hj => h j (by simp [hj]))⟩
end

theorem conn_prof_pair : (type_of% @conn_prof_rec) ∧ (type_of% @connL_profL_rec) :=
  ⟨@conn_prof_rec, @connL_profL_rec⟩

theorem conn_prof : type_of% @conn_prof_rec := conn_prof_pair.1

end Lax117284Proofs.Treewidth.Trees.RT

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

/-- **Forget.**  The tree is unchanged, the boundary shrinks.  (Repaired statement: `t` must be connected.) -/
theorem char_forget (B : Finset ℕ) (x : ℕ) (t : RT) (ht : t.Conn) :
    t.char (B.erase x) = CT.forgetC x (t.char B) := by
  unfold RT.char CT.forgetC
  rw [CT.norm_relabel_norm x (RT.conn_prof B t ht) (RT.yne_prof B t), RT.relabel_prof_erase]

end Lax117284Proofs.Treewidth.Chars
