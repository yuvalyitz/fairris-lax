import Lax117284Proofs.Treewidth.Chars.MergeAR

/-!
# Chains of an analysis as trees: indexing, local `Conn` facts, and the generic step for a merged node (C3)

* `cbag`, `cjunk`, `succL` — the `i`-th node of a chain `n` with tail `K`: its bag, its junk, and what hangs below it;
* `chainToRT_drop` — `chainToRT (n.drop i) K = node (cbag n i) (cjunk n i ++ succL n K i)`;
* `local_facts` — the local `Conn` conditions at the `i`-th node;
* `conn_merged_node` — the *generic step*: the `Conn` condition of a node whose bag is the union of an `A`-bag and a
  `B`-bag, given the local facts of both sides and of the successors.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## indexing a chain -/

def cbag (n : List CNode) (i : ℕ) : Finset ℕ := (n.getD i ⟨∅, []⟩).bag
def cjunk (n : List CNode) (i : ℕ) : List RT := (n.getD i ⟨∅, []⟩).junk

/-- What hangs below the `i`-th node: the rest of the chain, or the tail of the chain. -/
def succL (n : List CNode) (K : List RT) (i : ℕ) : List RT :=
  if i + 1 < n.length then [AR.chainToRT (n.drop (i + 1)) K] else K

theorem getD_chain {n : List CNode} {i : ℕ} (hi : i < n.length) : n.getD i ⟨∅, []⟩ = n[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem chainToRT_drop (n : List CNode) (K : List RT) {i : ℕ} (hi : i < n.length) :
    AR.chainToRT (n.drop i) K = .node (cbag n i) (cjunk n i ++ succL n K i) := by
  have hd : n.drop i = n[i] :: n.drop (i + 1) := List.drop_eq_getElem_cons hi
  unfold cbag cjunk succL
  rw [getD_chain hi, hd]
  by_cases h : i + 1 < n.length
  · rw [if_pos h]
    cases hdr : n.drop (i + 1) with
    | nil =>
      have : (n.drop (i + 1)).length = n.length - (i + 1) := List.length_drop
      rw [hdr] at this
      simp at this; omega
    | cons m r => simp [AR.chainToRT]
  · rw [if_neg h]
    have : n.drop (i + 1) = [] := List.drop_of_length_le (by omega)
    rw [this]
    simp [AR.chainToRT]

theorem succL_of_last {n : List CNode} {K : List RT} {i : ℕ} (h : ¬ (i + 1 < n.length)) : succL n K i = K := by
  simp [succL, h]

theorem succL_of_lt {n : List CNode} {K : List RT} {i : ℕ} (h : i + 1 < n.length) :
    succL n K i = [AR.chainToRT (n.drop (i + 1)) K] := by
  simp [succL, h]

theorem rootBag_chainToRT_drop (n : List CNode) (K : List RT) {i : ℕ} (hi : i < n.length) :
    (AR.chainToRT (n.drop i) K).rootBag = cbag n i := by
  rw [chainToRT_drop n K hi]; rfl

/-! ## local `Conn` facts -/

theorem conn_drop_succ {n : List CNode} {K : List RT} {i : ℕ} (hi : i + 1 < n.length)
    (h : (AR.chainToRT (n.drop i) K).Conn) : (AR.chainToRT (n.drop (i + 1)) K).Conn := by
  rw [chainToRT_drop n K (by omega)] at h
  obtain ⟨h1, -, -⟩ := (RT.conn_node_iff _ _).1 h
  apply h1
  rw [succL_of_lt hi]
  simp

theorem conn_drop {n : List CNode} {K : List RT} (h : (AR.chainToRT n K).Conn) :
    ∀ i, i < n.length → (AR.chainToRT (n.drop i) K).Conn := by
  intro i
  induction i with
  | zero => intro _; simpa using h
  | succ i ih => intro hi; exact conn_drop_succ hi (ih (by omega))

theorem local_facts {n : List CNode} {K : List RT} {i : ℕ} (hi : i < n.length)
    (h : (AR.chainToRT (n.drop i) K).Conn) :
    (∀ J ∈ cjunk n i, J.Conn) ∧ (∀ K' ∈ succL n K i, K'.Conn) ∧
    (∀ K' ∈ cjunk n i ++ succL n K i, ∀ v ∈ cbag n i, v ∈ K'.verts → v ∈ K'.rootBag) ∧
    (cjunk n i ++ succL n K i).Pairwise
      (fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag n i) := by
  rw [chainToRT_drop n K hi] at h
  obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff _ _).1 h
  refine ⟨fun J hJ => h1 J (List.mem_append_left _ hJ), fun K' hK' => h1 K' (List.mem_append_right _ hK'),
    h2, h3⟩

/-! ## vertices along a chain -/

theorem verts_drop (n : List CNode) (K : List RT) {i : ℕ} (hi : i < n.length) (x : ℕ) :
    x ∈ (AR.chainToRT (n.drop i) K).verts ↔
      x ∈ cbag n i ∨ (∃ J ∈ cjunk n i, x ∈ J.verts) ∨ ∃ K' ∈ succL n K i, x ∈ K'.verts := by
  rw [chainToRT_drop n K hi, RT.verts_node]
  simp only [List.mem_append]
  constructor
  · rintro (h | ⟨k, hk | hk, hx⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨k, hk, hx⟩)
    · exact Or.inr (Or.inr ⟨k, hk, hx⟩)
  · rintro (h | ⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, Or.inl hk, hx⟩
    · exact Or.inr ⟨k, Or.inr hk, hx⟩

theorem mem_vertsL {l : List RT} {x : ℕ} : x ∈ RT.vertsL l ↔ ∃ k ∈ l, x ∈ k.verts := RT.mem_vertsL_iff l x

theorem vertsL_succL_lt {n : List CNode} {K : List RT} {i : ℕ} (hi : i + 1 < n.length) (x : ℕ) :
    x ∈ RT.vertsL (succL n K i) ↔
      x ∈ cbag n (i + 1) ∨ x ∈ RT.vertsL (cjunk n (i + 1)) ∨ x ∈ RT.vertsL (succL n K (i + 1)) := by
  rw [succL_of_lt hi, mem_vertsL]
  simp only [List.mem_singleton, exists_eq_left]
  rw [verts_drop n K hi, mem_vertsL, mem_vertsL]

theorem vertsL_sub_verts_chainToRT (r : List CNode) (K : List RT) :
    ∀ x ∈ RT.vertsL K, x ∈ (AR.chainToRT r K).verts := by
  intro x hx
  rw [mem_vertsL] at hx
  obtain ⟨k, hk, hxk⟩ := hx
  cases r with
  | nil =>
    rw [AR.chainToRT, RT.verts_node]
    exact Or.inr ⟨k, hk, hxk⟩
  | cons a r =>
    cases r with
    | nil =>
      rw [AR.chainToRT, RT.verts_node]
      exact Or.inr ⟨k, List.mem_append_right _ hk, hxk⟩
    | cons b r =>
      rw [AR.chainToRT, RT.verts_node]
      exact Or.inr ⟨AR.chainToRT (b :: r) K, List.mem_append_right _ (List.mem_singleton_self _),
        vertsL_sub_verts_chainToRT (b :: r) K x (mem_vertsL.2 ⟨k, hk, hxk⟩)⟩

theorem vertsL_sub_succL {n : List CNode} {K : List RT} {i : ℕ} (hi : i < n.length) :
    ∀ x ∈ RT.vertsL K, x ∈ RT.vertsL (succL n K i) := by
  intro x hx
  by_cases h : i + 1 < n.length
  · rw [succL_of_lt h, mem_vertsL]
    exact ⟨_, List.mem_singleton_self _, vertsL_sub_verts_chainToRT _ _ x hx⟩
  · rw [succL_of_last h]; exact hx

/-- The `B`-vertices below the `i`-th node are those of the label and of the tail. -/
theorem reg_succ {n : List CNode} {K : List RT} {B S : Finset ℕ}
    (hbag : ∀ x ∈ n, x.bag ∩ B = S) (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ∩ B ⊆ S) :
    ∀ d i, n.length = i + 1 + d → ∀ x ∈ RT.vertsL (succL n K i), x ∈ B → x ∈ S ∨ (x ∈ RT.vertsL K) := by
  intro d
  induction d with
  | zero =>
    intro i hi x hx hxB
    rw [succL_of_last (by omega)] at hx
    exact Or.inr hx
  | succ d ih =>
    intro i hi x hx hxB
    have hlt : i + 1 < n.length := by omega
    rw [vertsL_succL_lt hlt] at hx
    rcases hx with hx | hx | hx
    · left
      have hmem : n[i + 1] ∈ n := List.getElem_mem hlt
      have := hbag _ hmem
      have hb : cbag n (i + 1) = n[i + 1].bag := by unfold cbag; rw [getD_chain hlt]
      rw [hb] at hx
      rw [← this]; exact Finset.mem_inter.2 ⟨hx, hxB⟩
    · left
      have hmem : n[i + 1] ∈ n := List.getElem_mem hlt
      have hj' : cjunk n (i + 1) = n[i + 1].junk := by unfold cjunk; rw [getD_chain hlt]
      rw [hj', mem_vertsL] at hx
      obtain ⟨J, hJ, hxJ⟩ := hx
      exact hjunk _ hmem J hJ (Finset.mem_inter.2 ⟨hxJ, hxB⟩)
    · exact ih (i + 1) (by omega) x hx hxB

theorem reg_verts {n : List CNode} {K : List RT} {B S : Finset ℕ}
    (hbag : ∀ x ∈ n, x.bag ∩ B = S) (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ∩ B ⊆ S)
    {i : ℕ} (hi : i < n.length) : ∀ x ∈ RT.vertsL (succL n K i), x ∈ B → x ∈ S ∨ (x ∈ RT.vertsL K) :=
  reg_succ hbag hjunk (n.length - (i + 1)) i (by omega)

/-! ## the generic step for a merged node -/

theorem conn_merged_node {B Ua Ub S XA XB : Finset ℕ} {ci cj NM : List RT}
    (hU : Ua ∩ Ub = B) (hXA : XA ⊆ Ua) (hXB : XB ⊆ Ub) (hAB : XA ∩ B = S) (hBB : XB ∩ B = S)
    (hciC : ∀ J ∈ ci, J.Conn) (hciV : ∀ J ∈ ci, J.verts ⊆ Ua) (hciB : ∀ J ∈ ci, J.verts ∩ B ⊆ S)
    (hciR : ∀ J ∈ ci, ∀ v ∈ XA, v ∈ J.verts → v ∈ J.rootBag)
    (hciP : ci.Pairwise (fun J1 J2 => ∀ v, v ∈ J1.verts → v ∈ J2.verts → v ∈ XA))
    (hcjC : ∀ J ∈ cj, J.Conn) (hcjV : ∀ J ∈ cj, J.verts ⊆ Ub) (hcjB : ∀ J ∈ cj, J.verts ∩ B ⊆ S)
    (hcjR : ∀ J ∈ cj, ∀ v ∈ XB, v ∈ J.verts → v ∈ J.rootBag)
    (hcjP : cj.Pairwise (fun J1 J2 => ∀ v, v ∈ J1.verts → v ∈ J2.verts → v ∈ XB))
    (hNC : ∀ K ∈ NM, K.Conn)
    (hNA1 : ∀ K ∈ NM, ∀ v ∈ XA, v ∈ K.verts → v ∈ K.rootBag)
    (hNB1 : ∀ K ∈ NM, ∀ v ∈ XB, v ∈ K.verts → v ∈ K.rootBag)
    (hNA2 : ∀ J ∈ ci, ∀ K ∈ NM, ∀ v, v ∈ J.verts → v ∈ K.verts → v ∈ XA)
    (hNB2 : ∀ J ∈ cj, ∀ K ∈ NM, ∀ v, v ∈ J.verts → v ∈ K.verts → v ∈ XB)
    (hNP : NM.Pairwise (fun K1 K2 => ∀ v, v ∈ K1.verts → v ∈ K2.verts → v ∈ XA ∪ XB)) :
    (RT.node (XA ∪ XB) (ci ++ cj ++ NM)).Conn := by
  have hSA : S ⊆ XA := by rw [← hAB]; exact Finset.inter_subset_left
  have hSB : S ⊆ XB := by rw [← hBB]; exact Finset.inter_subset_left
  rw [RT.conn_node_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro K hK
    rcases List.mem_append.1 hK with hK | hK
    · rcases List.mem_append.1 hK with hK | hK
      · exact hciC K hK
      · exact hcjC K hK
    · exact hNC K hK
  · intro K hK v hv hvK
    rcases List.mem_append.1 hK with hK | hK
    · rcases List.mem_append.1 hK with hK | hK
      · -- junk of the A side
        rcases Finset.mem_union.1 hv with hv | hv
        · exact hciR K hK v hv hvK
        · have hvB : v ∈ B := by
            rw [← hU]; exact Finset.mem_inter.2 ⟨hciV K hK hvK, hXB hv⟩
          have : v ∈ S := by rw [← hBB]; exact Finset.mem_inter.2 ⟨hv, hvB⟩
          exact hciR K hK v (hSA this) hvK
      · rcases Finset.mem_union.1 hv with hv | hv
        · have hvB : v ∈ B := by
            rw [← hU]; exact Finset.mem_inter.2 ⟨hXA hv, hcjV K hK hvK⟩
          have : v ∈ S := by rw [← hAB]; exact Finset.mem_inter.2 ⟨hv, hvB⟩
          exact hcjR K hK v (hSB this) hvK
        · exact hcjR K hK v hv hvK
    · rcases Finset.mem_union.1 hv with hv | hv
      · exact hNA1 K hK v hv hvK
      · exact hNB1 K hK v hv hvK
  · rw [List.pairwise_append]
    refine ⟨?_, hNP, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨hciP.imp (fun {a b} h v h1 h2 => Finset.mem_union_left _ (h v h1 h2)),
        hcjP.imp (fun {a b} h v h1 h2 => Finset.mem_union_right _ (h v h1 h2)), ?_⟩
      intro J1 hJ1 J2 hJ2 v hv1 hv2
      have hvB : v ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨hciV J1 hJ1 hv1, hcjV J2 hJ2 hv2⟩
      exact Finset.mem_union_left _ (hSA (hciB J1 hJ1 (Finset.mem_inter.2 ⟨hv1, hvB⟩)))
    · intro J hJ K hK v hvJ hvK
      rcases List.mem_append.1 hJ with hJ | hJ
      · exact Finset.mem_union_left _ (hNA2 J hJ K hK v hvJ hvK)
      · exact Finset.mem_union_right _ (hNB2 J hJ K hK v hvJ hvK)

/-! ## aligned lists -/

theorem F3.mem_mid {α β γ : Type} {P : α → β → γ → Prop} :
    ∀ {ms : List α} {as : List β} {bs : List γ}, F3 P ms as bs → ∀ m ∈ ms, ∃ a ∈ as, ∃ b ∈ bs, P m a b
  | [], [], [], _, m, hm => by simp at hm
  | m0 :: ms, a0 :: as, b0 :: bs, h, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨a0, by simp, b0, by simp, h.1⟩
    · obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid h.2 m hm
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hP⟩
  | [], [], _ :: _, h, _, _ => absurd h (by simp [F3])
  | [], _ :: _, _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, [], _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, _ :: _, [], h, _, _ => absurd h (by simp [F3])

theorem F3.mem_left {α β γ : Type} {P : α → β → γ → Prop} :
    ∀ {ms : List α} {as : List β} {bs : List γ}, F3 P ms as bs → ∀ a ∈ as, ∃ m ∈ ms, ∃ b ∈ bs, P m a b
  | [], [], [], _, a, ha => by simp at ha
  | m0 :: ms, a0 :: as, b0 :: bs, h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨m0, by simp, b0, by simp, h.1⟩
    · obtain ⟨m, hm, b, hb, hP⟩ := F3.mem_left h.2 a ha
      exact ⟨m, List.mem_cons_of_mem _ hm, b, List.mem_cons_of_mem _ hb, hP⟩
  | [], [], _ :: _, h, _, _ => absurd h (by simp [F3])
  | [], _ :: _, _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, [], _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, _ :: _, [], h, _, _ => absurd h (by simp [F3])

theorem F3.mem_right {α β γ : Type} {P : α → β → γ → Prop} :
    ∀ {ms : List α} {as : List β} {bs : List γ}, F3 P ms as bs → ∀ b ∈ bs, ∃ m ∈ ms, ∃ a ∈ as, P m a b
  | [], [], [], _, b, hb => by simp at hb
  | m0 :: ms, a0 :: as, b0 :: bs, h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨m0, by simp, a0, by simp, h.1⟩
    · obtain ⟨m, hm, a, ha, hP⟩ := F3.mem_right h.2 b hb
      exact ⟨m, List.mem_cons_of_mem _ hm, a, List.mem_cons_of_mem _ ha, hP⟩
  | [], [], _ :: _, h, _, _ => absurd h (by simp [F3])
  | [], _ :: _, _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, [], _, h, _, _ => absurd h (by simp [F3])
  | _ :: _, _ :: _, [], h, _, _ => absurd h (by simp [F3])

/-- Pairwise relations transfer along aligned lists. -/
theorem F3.pairwise {α β γ : Type} {P : α → β → γ → Prop} {RA : β → β → Prop} {RB : γ → γ → Prop}
    {R : α → α → Prop} :
    ∀ {ms : List α} {as : List β} {bs : List γ}, F3 P ms as bs →
      (∀ m1 ∈ ms, ∀ a1 ∈ as, ∀ b1 ∈ bs, ∀ m2 ∈ ms, ∀ a2 ∈ as, ∀ b2 ∈ bs,
        P m1 a1 b1 → P m2 a2 b2 → RA a1 a2 → RB b1 b2 → R m1 m2) →
      as.Pairwise RA → bs.Pairwise RB → ms.Pairwise R
  | [], [], [], _, _, _, _ => List.Pairwise.nil
  | m0 :: ms, a0 :: as, b0 :: bs, h, hstep, hA, hB => by
    rw [List.pairwise_cons] at hA hB ⊢
    refine ⟨fun m hm => ?_, F3.pairwise h.2 ?_ hA.2 hB.2⟩
    · obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid h.2 m hm
      exact hstep m0 (by simp) a0 (by simp) b0 (by simp) m (List.mem_cons_of_mem _ hm)
        a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) h.1 hP (hA.1 a ha) (hB.1 b hb)
    · intro m1 hm1 a1 ha1 b1 hb1 m2 hm2 a2 ha2 b2 hb2
      exact hstep m1 (List.mem_cons_of_mem _ hm1) a1 (List.mem_cons_of_mem _ ha1) b1 (List.mem_cons_of_mem _ hb1)
        m2 (List.mem_cons_of_mem _ hm2) a2 (List.mem_cons_of_mem _ ha2) b2 (List.mem_cons_of_mem _ hb2)
  | [], [], _ :: _, h, _, _, _ => absurd h (by simp [F3])
  | [], _ :: _, _, h, _, _, _ => absurd h (by simp [F3])
  | _ :: _, [], _, h, _, _, _ => absurd h (by simp [F3])
  | _ :: _, _ :: _, [], h, _, _, _ => absurd h (by simp [F3])

end Lax117284Proofs.Treewidth.Chars
