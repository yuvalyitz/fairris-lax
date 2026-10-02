import Lax117284Proofs.Treewidth.Fun.ToValAlg
import Lax117284Proofs.Treewidth.Size.Statements
import Lax117284Proofs.Treewidth.Size.PlanSize

/-!
# WP E0 (2): the size bridge — `sz` and `mx` of the algorithm's data types

* **exact cell counts**: `sz c = c.vsz` (`CT`), `sz t = rvsz t` (`RT`), `sz nt = 4·nt.inner + 1` (`NT`), hence
  `2·nt.size ≤ sz nt + 1` and `sz nt + 3 ≤ 4·nt.size`; `sz w + 3 ≤ 8·CT.wsz w` for region plans;
* **lower bounds** in terms of the node counts (`count c ≤ sz c`, `t.size ≤ sz t`, `nt.size ≤ sz nt`);
* **P1 consequences in cell form** (`Wf.sz_le`, `tables_sz_le`, `sz_tables_le`, `extract_sz_le`);
* **`mx`** (largest natural in the view): `mx c ≤ M ↔ (all vertices ≤ M) ∧ maxEntry ≤ M`, `mx t ≤ M ↔ all vertices ≤ M`,
  and for `NT` the vertices mentioned by `intro`/`forget` plus the constructor tags `≤ 3`.
-/

namespace Lax117284Proofs.Treewidth.Fun

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

/-! ## generic -/

theorem sz_list_le {α : Type} [ToVal α] {l : List α} {s : ℕ} (h : ∀ a ∈ l, sz a ≤ s) :
    sz l ≤ 1 + l.length * (s + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    rw [sz_cons]
    simp only [List.length_cons]
    nlinarith

/-! ## `CT` -/

theorem sz_ct_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    sz (CT.node S y ks) = sz S + (sz y + sz ks + 1) + 1 := by
  simp only [sz, toVal_ct, Val.size]

theorem sz_ctl_of (ks : List CT) (h : ∀ k ∈ ks, sz k = k.vsz) : sz ks = CT.vszL ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [sz_cons, h k (by simp), ih (fun k hk => h k (by simp [hk]))]
    simp [CT.vszL]

/-- **`sz` of a characteristic is P1's cell count `CT.vsz`.** -/
theorem sz_ct_eq (c : CT) : sz c = c.vsz := by
  induction c using CT.ind with
  | h S y ks ih =>
    rw [sz_ct_node, sz_finset, sz_list_nat, sz_ctl_of ks ih]
    simp only [CT.vsz]

theorem count_le_sz (c : CT) : c.count ≤ sz c := by
  have hL : ∀ ks : List CT, (∀ k ∈ ks, k.count ≤ sz k) → CT.countL ks ≤ sz ks := by
    intro ks
    induction ks with
    | nil => intro _; simp [CT.countL]
    | cons k ks ih =>
      intro h
      have := h k (by simp)
      have := ih (fun k hk => h k (by simp [hk]))
      rw [sz_cons]; simp only [CT.countL]; omega
  induction c using CT.ind with
  | h S y ks ih =>
    have := hL ks ih
    rw [sz_ct_node]; simp only [CT.count]
    have := sz_pos S; have := sz_pos y
    omega

/-- Cell form of `Wf.vsz_le`. -/
theorem CT.Wf.sz_le {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : t.Wf B kmax) :
    sz t ≤ CT.runBound B.card * (2 * B.card + 2 * (2 * kmax + 1) + 6) := by
  rw [sz_ct_eq]; exact h.vsz_le

/-- Cell form of `tables_vsz_le`: every entry of every table has at most `128 (k+2)^3` cells. -/
theorem tables_sz_le {adj : Adj} {k : ℕ} {nt : NT} (hg : nt.Good adj) (hw : nt.toRT.Width (k + 1)) :
    ∀ c ∈ tables adj k nt, sz c ≤ 128 * (k + 2) ^ 3 := by
  intro c hc; rw [sz_ct_eq]; exact CT.tables_vsz_le hg hw c hc

/-! ## `RT` -/

theorem sz_rt_node (X : Finset ℕ) (ks : List RT) : sz (RT.node X ks) = sz X + sz ks + 1 := by
  simp only [sz, toVal_rt, Val.size]

theorem sz_rtl_of (ks : List RT) (h : ∀ k ∈ ks, sz k = rvsz k) : sz ks = rvszL ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [sz_cons, h k (by simp), ih (fun k hk => h k (by simp [hk]))]
    simp [rvszL]

/-- **`sz` of a real tree is P1's cell count `rvsz`.** -/
theorem sz_rt_eq (t : RT) : sz t = rvsz t := by
  induction t using RT.ind with
  | h X ks ih =>
    rw [sz_rt_node, sz_finset, sz_rtl_of ks ih]
    simp only [rvsz]

theorem size_le_sz (t : RT) : t.size ≤ sz t := by
  have hL : ∀ ks : List RT, (∀ k ∈ ks, k.size ≤ sz k) → RT.sizeL ks ≤ sz ks := by
    intro ks
    induction ks with
    | nil => intro _; simp [RT.sizeL]
    | cons k ks ih =>
      intro h
      have := h k (by simp)
      have := ih (fun k hk => h k (by simp [hk]))
      rw [sz_cons]; simp only [RT.sizeL]; omega
  induction t using RT.ind with
  | h X ks ih =>
    have := hL ks ih
    rw [sz_rt_node]; simp only [RT.size]
    have := sz_pos X
    omega

/-- Cell form of `extract_vsz_le`. -/
theorem extract_sz_le {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) (hw : nt.toRT.Width (k + 1)) : ∀ c ∈ tables adj k nt, ∀ t, extract adj k nt c = some t →
      sz t ≤ (2 * k + 8) * (2 * k + 6) * nt.size := by
  intro c hc t ht; rw [sz_rt_eq]; exact extract_vsz_le hs hg hW hw c hc t ht

/-! ## `NT` -/

/-- Number of non-leaf nodes. -/
def _root_.Lax117284Proofs.Treewidth.Trees.NT.inner : NT → ℕ
  | .leaf => 0
  | .intro _ c => c.inner + 1
  | .forget _ c => c.inner + 1
  | .join a b => a.inner + b.inner + 1

theorem sz_nt_leaf : sz NT.leaf = 1 := rfl
theorem sz_nt_intro (v : ℕ) (c : NT) : sz (NT.intro v c) = sz c + 4 := by
  simp only [sz, toVal_nt_intro, Val.size]; omega
theorem sz_nt_forget (v : ℕ) (c : NT) : sz (NT.forget v c) = sz c + 4 := by
  simp only [sz, toVal_nt_forget, Val.size]; omega
theorem sz_nt_join (a b : NT) : sz (NT.join a b) = sz a + sz b + 3 := by
  simp only [sz, toVal_nt_join, Val.size]; omega

/-- **Exact cell count of a nice tree.** -/
theorem sz_nt_eq : ∀ nt : NT, sz nt = 4 * nt.inner + 1
  | .leaf => rfl
  | .intro v c => by rw [sz_nt_intro, sz_nt_eq c]; simp only [NT.inner]; omega
  | .forget v c => by rw [sz_nt_forget, sz_nt_eq c]; simp only [NT.inner]; omega
  | .join a b => by rw [sz_nt_join, sz_nt_eq a, sz_nt_eq b]; simp only [NT.inner]; omega

theorem inner_lt_size : ∀ nt : NT, nt.inner + 1 ≤ nt.size ∧ nt.size ≤ 2 * nt.inner + 1
  | .leaf => by simp [NT.inner, NT.size]
  | .intro v c => by have := inner_lt_size c; simp only [NT.inner, NT.size]; omega
  | .forget v c => by have := inner_lt_size c; simp only [NT.inner, NT.size]; omega
  | .join a b => by have := inner_lt_size a; have := inner_lt_size b; simp only [NT.inner, NT.size]; omega

/-- `sz nt + 3 ≤ 4 · size nt`. -/
theorem sz_nt_le_size (nt : NT) : sz nt + 3 ≤ 4 * nt.size := by
  have := inner_lt_size nt; rw [sz_nt_eq]; omega

/-- `2 · size nt ≤ sz nt + 1`. -/
theorem size_le_sz_nt (nt : NT) : 2 * nt.size ≤ sz nt + 1 := by
  have := inner_lt_size nt; rw [sz_nt_eq]; omega

/-! ## region plans (`CT.wsz` of P1) -/

mutual
theorem sz_wp_le : ∀ w : CT.WPlan, sz w + 3 ≤ 8 * CT.wsz w
  | .endAt c => by
    cases c <;> simp [sz, CT.wsz, Val.size]
  | .whole ps => by
    have := sz_wpl_le ps
    have h : sz (CT.WPlan.whole ps) = sz ps + 2 := by simp only [sz, toVal_wp_whole, Val.size]; omega
    rw [h]; simp only [CT.wsz]; omega
theorem sz_wpl_le : ∀ ps : List (Option CT.WPlan), sz ps ≤ 1 + 8 * CT.wszL ps
  | [] => by simp [CT.wszL]
  | p :: ps => by
    have := sz_wpo_le p
    have := sz_wpl_le ps
    rw [sz_cons]; simp only [CT.wszL]; omega
theorem sz_wpo_le : ∀ p : Option CT.WPlan, sz p + 1 ≤ 8 * CT.wszO p
  | none => by simp [CT.wszO]
  | some p => by
    have := sz_wp_le p
    rw [sz_some]; simp only [CT.wszO]; omega
end

theorem sz_plan_att (c : Option CT.Cut) (ch : List (Finset ℕ)) (M : Finset ℕ) :
    sz (CT.Plan.att c ch M) = sz c + sz ch + sz M + 4 := by
  simp only [sz, toVal_plan_att, Val.size]; omega
theorem sz_plan_top (pre : Option CT.Cut) (w : CT.WPlan) :
    sz (CT.Plan.top pre w) = sz pre + sz w + 3 := by
  simp only [sz, toVal_plan_top, Val.size]; omega
theorem sz_cnode (b : Finset ℕ) (j : List RT) : sz (CNode.mk b j) = sz b + sz j + 1 := by
  simp only [sz, toVal_cnode, Val.size]
theorem sz_ar (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    sz (AR.run S c ks) = sz S + (sz c + sz ks + 1) + 1 := by
  simp only [sz, toVal_ar, Val.size]

/-! ## `mx` -/

theorem mx_foldr_max_le {y : List ℕ} {M : ℕ} : y.foldr max 0 ≤ M ↔ ∀ a ∈ y, a ≤ M := by
  induction y with
  | nil => simp
  | cons a y ih => simp [ih]

theorem maxEntryL_le {M : ℕ} : ∀ ks : List CT, CT.maxEntryL ks ≤ M ↔ ∀ k ∈ ks, k.maxEntry ≤ M
  | [] => by simp [CT.maxEntryL]
  | k :: ks => by simp [CT.maxEntryL, maxEntryL_le ks]

theorem mx_ct_node (S : Finset ℕ) (y : List ℕ) (ks : List CT) :
    mx (CT.node S y ks) = max (mx S) (max (mx y) (mx ks)) := by
  simp only [mx, toVal_ct, Val.maxNat]

/-- **`mx` of a characteristic**: all its vertices and all its sequence entries are `≤ M`. -/
theorem mx_ct_le_iff (c : CT) {M : ℕ} : mx c ≤ M ↔ (∀ v ∈ c.verts, v ≤ M) ∧ c.maxEntry ≤ M := by
  induction c using CT.ind with
  | h S y ks ih =>
    rw [mx_ct_node, max_le_iff, max_le_iff, mx_finset_le, mx_list_le, mx_list_le]
    simp only [CT.maxEntry, max_le_iff, mx_foldr_max_le, maxEntryL_le, CT.mem_verts_node]
    simp only [mx_nat]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun v hv => ?_, h2, fun k hk => ((ih k hk).1 (h3 k hk)).2⟩
      rcases hv with hv | ⟨k, hk, hv⟩
      · exact h1 v hv
      · exact ((ih k hk).1 (h3 k hk)).1 v hv
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun v hv => h1 v (Or.inl hv), h2, fun k hk => (ih k hk).2 ⟨fun v hv => h1 v (Or.inr ⟨k, hk, hv⟩), h3 k hk⟩⟩

/-- Natural numbers inside a well-formed characteristic over `B` with entries `≤ kmax`. -/
theorem mx_ct_le_of_wf {B : Finset ℕ} {kmax : ℕ} {t : CT} (h : t.Wf B kmax) {M : ℕ}
    (hB : ∀ v ∈ B, v ≤ M) (hk : kmax ≤ M) : mx t ≤ M :=
  (mx_ct_le_iff t).2 ⟨fun v hv => hB v (h.verts_eq ▸ hv), le_trans h.bounded hk⟩

theorem mx_rt_node (X : Finset ℕ) (ks : List RT) : mx (RT.node X ks) = max (mx X) (mx ks) := by
  simp only [mx, toVal_rt, Val.maxNat]

/-- **`mx` of a real tree**: all its vertices are `≤ M`. -/
theorem mx_rt_le_iff (t : RT) {M : ℕ} : mx t ≤ M ↔ ∀ v ∈ t.verts, v ≤ M := by
  induction t using RT.ind with
  | h X ks ih =>
    rw [mx_rt_node, max_le_iff, mx_finset_le, mx_list_le]
    simp only [RT.verts, Finset.mem_union, RT.mem_vertsL_iff]
    constructor
    · rintro ⟨h1, h2⟩ v (hv | ⟨k, hk, hv⟩)
      · exact h1 v hv
      · exact (ih k hk).1 (h2 k hk) v hv
    · intro h
      exact ⟨fun v hv => h v (Or.inl hv), fun k hk => (ih k hk).2 fun v hv => h v (Or.inr ⟨k, hk, hv⟩)⟩

/-- The vertices named by `intro`/`forget` constructors of a nice tree. -/
def _root_.Lax117284Proofs.Treewidth.Trees.NT.mentioned : NT → Finset ℕ
  | .leaf => ∅
  | .intro v c => insert v c.mentioned
  | .forget v c => insert v c.mentioned
  | .join a b => a.mentioned ∪ b.mentioned

/-- Every natural in the view of `nt` is `≤ M` once `3 ≤ M` (constructor tags) and every mentioned vertex is. -/
theorem mx_nt_le {M : ℕ} (h3 : 3 ≤ M) (nt : NT) (h : ∀ v ∈ nt.mentioned, v ≤ M) : mx nt ≤ M := by
  induction nt with
  | leaf => simp [mx, Val.maxNat]
  | intro v c ih =>
    have hc := ih (fun u hu => h u (by simp [NT.mentioned, hu]))
    have hv := h v (by simp [NT.mentioned])
    simp only [mx, toVal_nt_intro, Val.maxNat] at hc ⊢
    omega
  | forget v c ih =>
    have hc := ih (fun u hu => h u (by simp [NT.mentioned, hu]))
    have hv := h v (by simp [NT.mentioned])
    simp only [mx, toVal_nt_forget, Val.maxNat] at hc ⊢
    omega
  | join a b iha ihb =>
    have ha := iha (fun u hu => h u (by simp [NT.mentioned, hu]))
    have hb := ihb (fun u hu => h u (by simp [NT.mentioned, hu]))
    simp only [mx, toVal_nt_join, Val.maxNat] at ha hb ⊢
    omega

theorem le_mx_nt : ∀ (nt : NT) {v : ℕ}, v ∈ nt.mentioned → v ≤ mx nt
  | .leaf, v, h => by simp [NT.mentioned] at h
  | .intro w c, v, h => by
    simp only [NT.mentioned, Finset.mem_insert] at h
    simp only [mx, toVal_nt_intro, Val.maxNat]
    rcases h with rfl | h
    · omega
    · have := le_mx_nt c h; simp only [mx] at this; omega
  | .forget w c, v, h => by
    simp only [NT.mentioned, Finset.mem_insert] at h
    simp only [mx, toVal_nt_forget, Val.maxNat]
    rcases h with rfl | h
    · omega
    · have := le_mx_nt c h; simp only [mx] at this; omega
  | .join a b, v, h => by
    simp only [NT.mentioned, Finset.mem_union] at h
    simp only [mx, toVal_nt_join, Val.maxNat]
    rcases h with h | h
    · have := le_mx_nt a h; simp only [mx] at this; omega
    · have := le_mx_nt b h; simp only [mx] at this; omega

theorem mentioned_subset_under_of_wf : ∀ nt : NT, nt.Wf → nt.mentioned ⊆ nt.under
  | .leaf, _ => by simp [NT.mentioned]
  | .intro v c, h => by
    intro x hx
    simp only [NT.mentioned, Finset.mem_insert] at hx
    simp only [NT.under, Finset.mem_insert]
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (mentioned_subset_under_of_wf c h.2 hx)
  | .forget v c, h => by
    intro x hx
    simp only [NT.mentioned, Finset.mem_insert] at hx
    simp only [NT.under]
    rcases hx with rfl | hx
    · exact NT.bag_subset_under c h.1
    · exact mentioned_subset_under_of_wf c h.2 hx
  | .join a b, h => by
    intro x hx
    simp only [NT.mentioned, Finset.mem_union] at hx
    simp only [NT.under, Finset.mem_union]
    rcases hx with hx | hx
    · exact Or.inl (mentioned_subset_under_of_wf a h.2.1 hx)
    · exact Or.inr (mentioned_subset_under_of_wf b h.2.2 hx)

theorem under_subset_mentioned : ∀ nt : NT, nt.under ⊆ nt.mentioned
  | .leaf => by simp [NT.under]
  | .intro v c => by
    intro x hx
    simp only [NT.under, Finset.mem_insert] at hx
    simp only [NT.mentioned, Finset.mem_insert]
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (under_subset_mentioned c hx)
  | .forget v c => by
    intro x hx
    simp only [NT.under] at hx
    simp only [NT.mentioned, Finset.mem_insert]
    exact Or.inr (under_subset_mentioned c hx)
  | .join a b => by
    intro x hx
    simp only [NT.under, Finset.mem_union] at hx
    simp only [NT.mentioned, Finset.mem_union]
    rcases hx with hx | hx
    · exact Or.inl (under_subset_mentioned a hx)
    · exact Or.inr (under_subset_mentioned b hx)

/-- For a shape-correct nice tree: every natural in its view is `≤ M` once `3 ≤ M` and the vertices are. -/
theorem mx_nt_le_of_wf {nt : NT} (h : nt.Wf) {M : ℕ} (h3 : 3 ≤ M) (hv : ∀ v ∈ nt.under, v ≤ M) : mx nt ≤ M :=
  mx_nt_le h3 nt fun v hx => hv v (mentioned_subset_under_of_wf nt h hx)

theorem under_le_mx_nt (nt : NT) {v : ℕ} (hv : v ∈ nt.under) : v ≤ mx nt :=
  le_mx_nt nt (under_subset_mentioned nt hv)

end Lax117284Proofs.Treewidth.Fun
