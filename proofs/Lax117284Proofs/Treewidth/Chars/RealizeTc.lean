import Lax117284Proofs.Treewidth.Chars.RealizeNorm
import Lax117284Proofs.Treewidth.Chars.MergeIface

/-!
# Connectedness by counting tops (work package C5, part 4)

`tc u t p` counts the *tops* of the occurrences of `u` in `t`: the nodes containing `u` whose parent does not (`p` says
whether the parent of the root contains `u`).  `RT.Conn t` holds iff every vertex has at most one top
(`conn_iff_tc`).  Counting is additive and insensitive to the duplication of a node (same bag), which makes the
connectedness of the realised decomposition a computation.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

mutual
/-- The number of tops of the occurrences of `u` in `t`; `p` = the parent of the root contains `u`. -/
def tc (u : ℕ) : RT → Bool → ℕ
  | .node b ks, p => (if u ∈ b ∧ p = false then 1 else 0) + tcL u ks (decide (u ∈ b))
def tcL (u : ℕ) : List RT → Bool → ℕ
  | [], _ => 0
  | k :: ks, p => tc u k p + tcL u ks p
end

theorem tcL_eq_sum (u : ℕ) : ∀ (ks : List RT) (p : Bool), tcL u ks p = (ks.map (fun k => tc u k p)).sum
  | [], p => rfl
  | k :: ks, p => by simp [tcL, tcL_eq_sum u ks p]

theorem tc_node (u : ℕ) (b : Finset ℕ) (ks : List RT) (p : Bool) :
    tc u (.node b ks) p = (if u ∈ b ∧ p = false then 1 else 0) + (ks.map (fun k => tc u k (decide (u ∈ b)))).sum := by
  rw [tc, tcL_eq_sum]

/-- No vertex outside the tree: no tops. -/
theorem tc_zero_of_notin (u : ℕ) : ∀ (t : RT) (p : Bool), u ∉ t.verts → tc u t p = 0 := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro p h
    rw [RT.verts_node] at h
    push_neg at h
    rw [tc_node]
    have h1 : ¬ (u ∈ b ∧ p = false) := fun hh => h.1 hh.1
    rw [if_neg h1, zero_add, List.sum_eq_zero]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact ih k hk _ (h.2 k hk)

theorem tc_pos (u : ℕ) : ∀ (t : RT), u ∈ t.verts → 1 ≤ tc u t false ∧ (u ∉ t.rootBag → 1 ≤ tc u t true) := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro h
    rw [RT.verts_node] at h
    by_cases hb : u ∈ b
    · refine ⟨?_, fun h' => absurd hb h'⟩
      rw [tc_node, if_pos ⟨hb, rfl⟩]; omega
    · obtain ⟨k, hk, hkv⟩ := h.resolve_left hb
      have := ih k hk hkv
      have hk1 : 1 ≤ tc u k false := this.1
      have hsum : tc u k (decide (u ∈ b)) ≤ (ks.map (fun k => tc u k (decide (u ∈ b)))).sum :=
        List.single_le_sum (fun x hx => Nat.zero_le _) _ (List.mem_map.2 ⟨k, hk, rfl⟩)
      have hdec : decide (u ∈ b) = false := by simp [hb]
      rw [hdec] at hsum
      have e1 : ¬ (u ∈ b ∧ false = false) := fun hh => hb hh.1
      have e2 : ¬ (u ∈ b ∧ true = false) := fun hh => by simp at hh
      constructor
      · rw [tc_node, if_neg (fun hh => hb hh.1), zero_add, hdec]
        omega
      · intro _
        rw [tc_node, if_neg e2, zero_add, hdec]
        omega

/-! ## the per-vertex connectedness condition -/

mutual
/-- `u` occupies a connected set of nodes of `t`. -/
def CU (u : ℕ) : RT → Prop
  | .node b ks => CUL u ks ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
      ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b)
def CUL (u : ℕ) : List RT → Prop
  | [] => True
  | k :: ks => CU u k ∧ CUL u ks
end

theorem CUL_iff (u : ℕ) : ∀ ks : List RT, CUL u ks ↔ ∀ k ∈ ks, CU u k
  | [] => by simp [CUL]
  | k :: ks => by simp [CUL, CUL_iff u ks]

theorem CU_node (u : ℕ) (b : Finset ℕ) (ks : List RT) :
    CU u (.node b ks) ↔ (∀ k ∈ ks, CU u k) ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
      ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b) := by
  rw [CU, CUL_iff]

theorem CU_of_notin (u : ℕ) : ∀ t : RT, u ∉ t.verts → CU u t := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    intro h
    rw [RT.verts_node] at h
    push_neg at h
    rw [CU_node]
    refine ⟨fun k hk => ih k hk (h.2 k hk), fun hb => absurd hb h.1, ?_⟩
    exact List.pairwise_iff_getElem.2 (fun i j hi hj hij hva => absurd hva (h.2 _ (List.getElem_mem _)))

theorem conn_iff_CU : ∀ t : RT, t.Conn ↔ ∀ u, CU u t := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    rw [RT.conn_node_iff]
    simp only [CU_node]
    constructor
    · rintro ⟨h1, h2, h3⟩ u
      refine ⟨fun k hk => (ih k hk).1 (h1 k hk) u, fun hu k hk hv => h2 k hk u hu hv, ?_⟩
      exact h3.imp (fun h hv1 hv2 => h u hv1 hv2)
    · intro h
      refine ⟨fun k hk => (ih k hk).2 (fun u => (h u).1 k hk), fun k hk u hu hv => (h u).2.1 hu k hk hv, ?_⟩
      -- pairwise with a universally quantified vertex
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij u hv1 hv2
      have := List.pairwise_iff_getElem.1 (h u).2.2 i j hi hj hij
      exact this hv1 hv2


/-! ## counting tops decides `CU` -/

theorem sum_le_one_iff (u : ℕ) : ∀ (ks : List RT), (∀ k ∈ ks, (tc u k false ≤ 1 ↔ CU u k)) →
    ((ks.map (fun k => tc u k false)).sum ≤ 1 ↔
      (∀ k ∈ ks, CU u k) ∧ ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → False)) := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons k ks ih =>
    intro hIH
    have hk := hIH k (by simp)
    have hks := ih (fun k' hk' => hIH k' (List.mem_cons_of_mem _ hk'))
    simp only [List.map_cons, List.sum_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have h1 : tc u k false ≤ 1 := by omega
      have h2 : (ks.map (fun k => tc u k false)).sum ≤ 1 := by omega
      obtain ⟨hc, hp⟩ := hks.1 h2
      refine ⟨⟨hk.1 h1, hc⟩, fun k' hk' hv1 hv2 => ?_, hp⟩
      have a1 := (tc_pos u k hv1).1
      have a2 := (tc_pos u k' hv2).1
      have a3 : tc u k' false ≤ (ks.map (fun k => tc u k false)).sum :=
        List.single_le_sum (fun x hx => Nat.zero_le _) _ (List.mem_map.2 ⟨k', hk', rfl⟩)
      omega
    · rintro ⟨⟨hc1, hc⟩, hp1, hp⟩
      have h1 := hk.2 hc1
      have h2 := hks.2 ⟨hc, hp⟩
      by_cases hv : u ∈ k.verts
      · have : (ks.map (fun k => tc u k false)).sum = 0 := by
          rw [List.sum_eq_zero]
          intro x hx
          obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx
          apply tc_zero_of_notin
          intro hv'
          exact hp1 k' hk' hv hv'
        omega
      · have : tc u k false = 0 := tc_zero_of_notin u k false hv
        omega

theorem CU_iff_tc (u : ℕ) : ∀ t : RT,
    (CU u t ↔ tc u t false ≤ 1) ∧ ((CU u t ∧ (u ∈ t.verts → u ∈ t.rootBag)) ↔ tc u t true = 0) := by
  intro t
  induction t using RT.ind with
  | _ b ks ih =>
    rw [CU_node, tc_node, tc_node]
    show _ ∧ ((_ ∧ (u ∈ (RT.node b ks).verts → u ∈ b)) ↔ _)
    by_cases hb : u ∈ b
    · have hd : decide (u ∈ b) = true := by simp [hb]
      rw [hd]
      have e1 : (if u ∈ b ∧ false = false then 1 else 0) = 1 := if_pos ⟨hb, rfl⟩
      have e2 : (if u ∈ b ∧ true = false then 1 else 0) = 0 := if_neg (by simp)
      rw [e1, e2]
      have hsum0 : ((ks.map (fun k => tc u k true)).sum = 0) ↔
          ((∀ k ∈ ks, CU u k) ∧ ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) := by
        rw [List.sum_eq_zero_iff]
        constructor
        · intro h
          have h' : ∀ k ∈ ks, CU u k ∧ (u ∈ k.verts → u ∈ k.rootBag) :=
            fun k hk => (ih k hk).2.2 (h _ (List.mem_map.2 ⟨k, hk, rfl⟩))
          exact ⟨fun k hk => (h' k hk).1, fun k hk => (h' k hk).2⟩
        · rintro ⟨h1, h2⟩ x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
          exact (ih k hk).2.1 ⟨h1 k hk, h2 k hk⟩
      have hpw : ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b) :=
        List.pairwise_iff_getElem.2 (fun i j hi hj hij _ _ => hb)
      constructor
      · constructor
        · rintro ⟨h1, h2, _⟩
          have := hsum0.2 ⟨h1, h2 hb⟩
          omega
        · intro h
          have := hsum0.1 (by omega)
          exact ⟨this.1, fun _ => this.2, hpw⟩
      · constructor
        · rintro ⟨⟨h1, h2, _⟩, _⟩
          have := hsum0.2 ⟨h1, h2 hb⟩
          omega
        · intro h
          have := hsum0.1 (by omega)
          exact ⟨⟨this.1, fun _ => this.2, hpw⟩, fun _ => hb⟩
    · have hd : decide (u ∈ b) = false := by simp [hb]
      rw [hd]
      have e1 : (if u ∈ b ∧ false = false then 1 else 0) = 0 := if_neg (fun h => hb h.1)
      have e2 : (if u ∈ b ∧ true = false then 1 else 0) = 0 := if_neg (by simp)
      rw [e1, e2]
      have hle := sum_le_one_iff u ks (fun k hk => (ih k hk).1.symm)
      have hCUpw : ((∀ k ∈ ks, CU u k) ∧ (u ∈ b → ∀ k ∈ ks, u ∈ k.verts → u ∈ k.rootBag) ∧
          ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → u ∈ b)) ↔
          ((∀ k ∈ ks, CU u k) ∧ ks.Pairwise (fun k1 k2 => u ∈ k1.verts → u ∈ k2.verts → False)) := by
        constructor
        · rintro ⟨h1, _, h3⟩
          exact ⟨h1, h3.imp (fun h a b => absurd (h a b) hb)⟩
        · rintro ⟨h1, h3⟩
          exact ⟨h1, fun h => absurd h hb, h3.imp (fun h a b => (h a b).elim)⟩
      have hnv : u ∈ (RT.node b ks).verts ↔ ∃ k ∈ ks, u ∈ k.verts := by
        rw [RT.verts_node]; constructor
        · rintro (h | h)
          · exact absurd h hb
          · exact h
        · intro h; exact Or.inr h
      constructor
      · rw [zero_add, hCUpw]; exact hle.symm
      · have hz : ((ks.map (fun k => tc u k false)).sum = 0) ↔ ∀ k ∈ ks, u ∉ k.verts := by
          rw [List.sum_eq_zero_iff]
          constructor
          · intro h k hk hv
            have := h _ (List.mem_map.2 ⟨k, hk, rfl⟩)
            have := (tc_pos u k hv).1
            omega
          · intro h x hx
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
            exact tc_zero_of_notin u k false (h k hk)
        rw [zero_add, hz]
        constructor
        · rintro ⟨_, h2⟩ k hk hv
          exact hb (h2 (hnv.2 ⟨k, hk, hv⟩))
        · intro h
          have hn : u ∉ (RT.node b ks).verts := fun hv => by
            obtain ⟨k, hk, hk2⟩ := hnv.1 hv
            exact h k hk hk2
          refine ⟨?_, fun hv => absurd hv hn⟩
          have := CU_of_notin u _ hn
          rw [CU_node] at this
          exact this


theorem conn_iff_tc (t : RT) : t.Conn ↔ ∀ u, tc u t false ≤ 1 := by
  rw [conn_iff_CU]
  exact forall_congr' (fun u => (CU_iff_tc u t).1)

/-! ## chains -/

theorem chainToRT_cons_of_ne (n : CNode) {l : List CNode} (hl : l ≠ []) (K : List RT) :
    AR.chainToRT (n :: l) K = .node n.bag (n.junk ++ [AR.chainToRT l K]) := by
  obtain ⟨m, r, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem chainToRT_single (n : CNode) (K : List RT) : AR.chainToRT [n] K = .node n.bag (n.junk ++ K) := rfl

theorem dupAfter_cons_succ (j : ℕ) (n : CNode) (r : List CNode) : dupAfter (j + 1) (n :: r) = n :: dupAfter j r := by
  by_cases h : j < r.length
  · rw [dupAfter_of_lt (by simpa using h), dupAfter_of_lt h]
    simp [List.take_succ_cons, List.drop_succ_cons]
  · rw [dupAfter_of_ge (by simp; omega), dupAfter_of_ge (by omega)]

theorem dupAfter_zero (n : CNode) (r : List CNode) : dupAfter 0 (n :: r) = n :: ⟨n.bag, []⟩ :: r := by
  rw [dupAfter_of_lt (by simp)]
  simp

theorem tc_chain_dup (u : ℕ) : ∀ (ns : List CNode) (i : ℕ) (K : List RT) (p : Bool),
    tc u (AR.chainToRT (dupAfter i ns) K) p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro i K p; rw [dupAfter_of_ge (i := i) (ns := []) (by simp)]
  | cons n r ih =>
    intro i K p
    cases i with
    | zero =>
      rw [dupAfter_zero]
      cases r with
      | nil =>
        simp only [AR.chainToRT, tc_node, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.nil_append]
        simp
      | cons m r' =>
        simp only [AR.chainToRT, tc_node, List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.nil_append]
        simp
    | succ j =>
      rw [dupAfter_cons_succ]
      cases r with
      | nil => rw [dupAfter_of_ge (i := j) (ns := []) (by simp)]
      | cons m r' =>
        have hne : dupAfter j (m :: r') ≠ [] := by
          by_cases hj : j < (m :: r').length
          · rw [dupAfter_of_lt hj]; simp
          · rw [dupAfter_of_ge (by omega)]; simp
        rw [chainToRT_cons_of_ne _ hne, chainToRT_cons_of_ne _ (by simp)]
        simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, ih j K]

theorem tc_chain_dupOf (u : ℕ) {ns ns' : List CNode} (h : DupOf ns ns') (K : List RT) (p : Bool) :
    tc u (AR.chainToRT ns' K) p = tc u (AR.chainToRT ns K) p := by
  induction h with
  | refl => rfl
  | dup i _ ih => rw [tc_chain_dup, ih]

theorem tc_chain_mapIdx (u : ℕ) : ∀ (ns : List CNode) (g : ℕ → CNode → CNode),
    (∀ i n, (u ∈ (g i n).bag ↔ u ∈ n.bag) ∧ (g i n).junk = n.junk) →
    ∀ (K : List RT) (p : Bool), tc u (AR.chainToRT (ns.mapIdx g) K) p = tc u (AR.chainToRT ns K) p := by
  intro ns
  induction ns with
  | nil => intro g hg K p; simp
  | cons n r ih =>
    intro g hg K p
    rw [List.mapIdx_cons]
    have h0 := hg 0 n
    cases r with
    | nil =>
      simp only [List.mapIdx_nil]
      rw [chainToRT_single, chainToRT_single, tc_node, tc_node, h0.2]
      simp [h0.1]
    | cons m r' =>
      have hne : (List.mapIdx (fun i => g (i + 1)) (m :: r')) ≠ [] := by simp
      rw [chainToRT_cons_of_ne _ hne, chainToRT_cons_of_ne _ (by simp)]
      have := ih (fun i => g (i + 1)) (fun i n => hg (i + 1) n) K
      simp only [tc_node, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil, h0.1, h0.2, this]

/-! ## the new vertex -/

theorem tc_chain_prefix_free (v : ℕ) : ∀ (L : List CNode) (K : List RT) (p : Bool), L ≠ [] →
    (∀ n ∈ L, v ∉ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts) →
    tc v (AR.chainToRT L K) p = tcL v K false := by
  intro L
  induction L with
  | nil => intro K p h; exact absurd rfl h
  | cons n r ih =>
    intro K p _ hL
    obtain ⟨hn1, hn2⟩ := hL n (by simp)
    have hdec : decide (v ∈ n.bag) = false := by simp [hn1]
    have hjz : (n.junk.map (fun k => tc v k false)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      exact tc_zero_of_notin v J false (hn2 J hJ)
    cases r with
    | nil =>
      rw [chainToRT_single, tc_node, hdec, List.map_append, List.sum_append, hjz, if_neg (fun h => hn1 h.1),
        ← tcL_eq_sum]
      simp
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), tc_node, hdec, if_neg (fun h => hn1 h.1)]
      have := ih K false (by simp) (fun n' hn' => hL n' (List.mem_cons_of_mem _ hn'))
      simp [List.sum_append, hjz, this]

theorem tc_chain_full (v : ℕ) : ∀ (M : List CNode) (K : List RT) (p : Bool), M ≠ [] →
    (∀ n ∈ M, v ∈ n.bag ∧ ∀ J ∈ n.junk, v ∉ J.verts) →
    tc v (AR.chainToRT M K) p = (if p = false then 1 else 0) + tcL v K true := by
  intro M
  induction M with
  | nil => intro K p h; exact absurd rfl h
  | cons n r ih =>
    intro K p _ hM
    obtain ⟨hn1, hn2⟩ := hM n (by simp)
    have hdec : decide (v ∈ n.bag) = true := by simp [hn1]
    have hjz : (n.junk.map (fun k => tc v k true)).sum = 0 := by
      rw [List.sum_eq_zero]
      intro x hx
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
      exact tc_zero_of_notin v J true (hn2 J hJ)
    have hif : (if v ∈ n.bag ∧ p = false then 1 else 0) = (if p = false then 1 else 0) := by
      by_cases hp : p = false <;> simp [hp, hn1]
    cases r with
    | nil =>
      rw [chainToRT_single, tc_node, hdec, List.map_append, List.sum_append, hjz, hif, ← tcL_eq_sum]
      simp
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), tc_node, hdec, hif]
      have := ih K true (by simp) (fun n' hn' => hM n' (List.mem_cons_of_mem _ hn'))
      simp [List.sum_append, hjz, this]

/-! ## vertices and bags of a chain -/

theorem mem_bags_chainToRT (K : List RT) : ∀ (n : List CNode), n ≠ [] → ∀ (Y : Finset ℕ),
    Y ∈ (AR.chainToRT n K).bags ↔ (∃ y ∈ n, Y = y.bag) ∨ (∃ y ∈ n, ∃ J ∈ y.junk, Y ∈ J.bags) ∨
      ∃ K' ∈ K, Y ∈ K'.bags := by
  intro n
  induction n with
  | nil => intro h; exact absurd rfl h
  | cons a r ih =>
    intro _ Y
    cases r with
    | nil =>
      rw [chainToRT_single, RT.bags_node]
      simp only [List.mem_append, List.mem_singleton, exists_eq_left]
      constructor
      · rintro (h | ⟨k, hk | hk, hY⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨k, hk, hY⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hY⟩)
      · rintro (h | ⟨k, hk, hY⟩ | ⟨k, hk, hY⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, Or.inl hk, hY⟩
        · exact Or.inr ⟨k, Or.inr hk, hY⟩
    | cons m r' =>
      rw [chainToRT_cons_of_ne _ (by simp), RT.bags_node]
      have IH := ih (by simp) Y
      constructor
      · rintro (h | ⟨k, hk, hY⟩)
        · exact Or.inl ⟨a, List.mem_cons_self, h⟩
        · rcases List.mem_append.1 hk with hk | hk
          · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, k, hk, hY⟩)
          · rw [List.mem_singleton] at hk
            subst hk
            rcases IH.1 hY with ⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | h
            · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hYy⟩
            · exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, J, hJ, hYJ⟩)
            · exact Or.inr (Or.inr h)
      · rintro (⟨y, hy, hYy⟩ | ⟨y, hy, J, hJ, hYJ⟩ | h)
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inl hYy
          · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
              IH.2 (Or.inl ⟨y, hy, hYy⟩)⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact Or.inr ⟨J, List.mem_append_left _ hJ, hYJ⟩
          · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
              IH.2 (Or.inr (Or.inl ⟨y, hy, J, hJ, hYJ⟩))⟩
        · exact Or.inr ⟨AR.chainToRT (m :: r') K, List.mem_append_right _ (List.mem_singleton_self _),
            IH.2 (Or.inr (Or.inr h))⟩

end Lax117284Proofs.Treewidth.Chars
