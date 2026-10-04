import Lax117284Proofs.Treewidth.Seq.RingTyp
import Lax117284Proofs.Treewidth.Chars.AnalyzeRT

/-! ### `Lax117284Proofs.Treewidth.Seq.RingRealise` -/

section
/-!
# Realising a typical ring sum on exact sequences (S1)

`ringTyp (τ a) (τ b)` is computed from the *typical* forms; every element `d` of it is realised, up to
`≺`, by a genuine element `c ∈ a ⊕ b` of the exact sequences: `τ c ≺ d`.  This is
Lemma 3.13 applied to `a ≡ τ a`, `b ≡ τ b` (compare `ringTyp_cover_right`).
-/

namespace Lax117284Proofs.Treewidth.Seq

/-- **Ring-sum realisation.**  If `d ∈ ringTyp (τ a) (τ b)` then some `c ∈ a ⊕ b` has `τ c ≺ d`.
(For `a = []` the hypothesis is void, since `ringTyp [] _ = ∅`.) -/
theorem ringSum_realise {a b d : List ℕ} (h : d ∈ ringTyp (typical a) (typical b)) :
    ∃ c, RingSum a b c ∧ Dom (typical c) d := by
  by_cases ha : a = []
  · subst ha
    simp [ringTyp, typical] at h
  · obtain ⟨c, hc, hd⟩ := ringTyp_cover_right ha h
    obtain ⟨c₀, hc₀, rfl⟩ := (mem_ringTyp ha).mp hc
    exact ⟨c₀, hc₀, hd⟩

end Lax117284Proofs.Treewidth.Seq

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeAR` -/

section
/-!
# `mergeAR`: existence and unfolding (C3, realisation of the join)

* `F3`, `F4` — aligned lists;
* `joinC_inv`, `joinKids_F3` — inversion of `joinC`;
* `mergeKids_F4`, `mergeAR_inv` — unfolding of `mergeAR = some`;
* `mergeAR_exists` — the merge succeeds for every option `c ∈ joinC …` of two analyses with non-empty chains.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## aligned lists -/

/-- `P` holds of aligned triples. -/
def F3 {α β γ : Type} (P : α → β → γ → Prop) : List α → List β → List γ → Prop
  | [], [], [] => True
  | a :: as, b :: bs, c :: cs => P a b c ∧ F3 P as bs cs
  | _, _, _ => False

/-- `P` holds of aligned quadruples. -/
def F4 {α β γ δ : Type} (P : α → β → γ → δ → Prop) : List α → List β → List γ → List δ → Prop
  | [], [], [], [] => True
  | a :: as, b :: bs, c :: cs, d :: ds => P a b c d ∧ F4 P as bs cs ds
  | _, _, _, _ => False

theorem F4.length_eq {α β γ δ : Type} {P : α → β → γ → δ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds →
      as.length = bs.length ∧ as.length = cs.length ∧ as.length = ds.length
  | [], [], [], [], _ => ⟨rfl, rfl, rfl⟩
  | a :: as, b :: bs, c :: cs, d :: ds, h => by
    have := F4.length_eq h.2
    simp only [List.length_cons]
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## inversion of `joinC` -/

theorem joinC_inv {kmax : ℕ} {S S' : Finset ℕ} {y y' : List ℕ} {ks ks' : List CT} {c : CT}
    (h : c ∈ joinC kmax (node S y ks) (node S' y' ks')) :
    S = S' ∧ ks.length = ks'.length ∧ ∃ d kk, c = node S d kk ∧ kk ∈ joinKids kmax ks ks' ∧
      d ∈ (((ringTypList y y').map (fun d => d.map (· - S.card))).dedup.filter (fun d => d.all (· ≤ kmax))) := by
  unfold joinC at h
  by_cases hc : S = S' ∧ ks.length = ks'.length
  · rw [if_pos hc] at h
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨kk, hkk, d, hd, rfl⟩ := h
    exact ⟨hc.1, hc.2, d, kk, rfl, hkk, hd⟩
  · rw [if_neg hc] at h
    simp at h

theorem joinKids_F3 (kmax : ℕ) {f g : AR → CT} : ∀ (ka kb : List AR) (kk : List CT),
    kk ∈ joinKids kmax (ka.map f) (kb.map g) → F3 (fun a b c => c ∈ joinC kmax (f a) (g b)) ka kb kk := by
  intro ka
  induction ka with
  | nil =>
    intro kb kk h
    cases kb with
    | nil => simp only [List.map_nil, joinKids, List.mem_singleton] at h; subst h; trivial
    | cons b kb => simp [joinKids] at h
  | cons a ka ih =>
    intro kb kk h
    cases kb with
    | nil => simp [joinKids] at h
    | cons b kb =>
      simp only [List.map_cons, joinKids, List.mem_flatMap, List.mem_map] at h
      obtain ⟨c, hc, kk', hkk', rfl⟩ := h
      exact ⟨hc, ih kb kk' hkk'⟩

/-! ## unfolding `mergeAR` -/

theorem mergeKids_F4 : ∀ (ka kb : List AR) (tk : List CT) (ks : List AR), mergeKids ka kb tk = some ks →
    F4 (fun a b t m => mergeAR a b t = some m) ka kb tk ks := by
  intro ka
  induction ka with
  | nil =>
    intro kb tk ks h
    cases kb <;> cases tk <;> simp [mergeKids] at h
    subst h; trivial
  | cons a ka ih =>
    intro kb tk ks h
    cases kb with
    | nil => cases tk <;> simp [mergeKids] at h
    | cons b kb =>
      cases tk with
      | nil => simp [mergeKids] at h
      | cons t tk =>
        simp only [mergeKids] at h
        obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 h2
        exact ⟨hr, ih kb tk rest hrest⟩

theorem mergeAR_inv {S S' : Finset ℕ} {na nb : List CNode} {ka kb : List AR} {T : Finset ℕ} {ty : List ℕ}
    {tk : List CT} {M : AR}
    (h : mergeAR (.run S na ka) (.run S' nb kb) (.node T ty tk) = some M) :
    ∃ Q kM, findPath (na.map (fun n => n.bag.card)) (nb.map (fun n => n.bag.card)) S.card ty = some Q ∧
      mergeKids ka kb tk = some kM ∧ M = .run S (mergeChain na nb none Q) kM := by
  unfold mergeAR at h
  split at h
  · simp at h
  · rename_i Q hQ
    obtain ⟨kM, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨Q, kM, hQ, hk, rfl⟩

/-! ## existence of the merge -/

/-- The path on the exact sequences behind a join option. -/
theorem exists_findPath {sa sb : List ℕ} {s kmax : ℕ} {d : List ℕ} (ha : sa ≠ []) (hb : sb ≠ [])
    (hd : d ∈ (((ringTypList (typical sa) (typical sb)).map (fun d => d.map (· - s))).dedup.filter
      (fun d => d.all (· ≤ kmax)))) : ∃ Q, findPath sa sb s d = some Q := by
  rw [List.mem_filter, List.mem_dedup, List.mem_map] at hd
  obtain ⟨⟨e, he, rfl⟩, -⟩ := hd
  have he' := mem_ringTypList.1 he
  obtain ⟨c0, hc0, hdom⟩ := ringSum_realise he'
  obtain ⟨c', hc', -, hty, -⟩ := RingSum.short hc0 ha
  obtain ⟨Q, hQ, rfl⟩ := (mem_pathSums_iff ha hb).1 hc'
  have hdom' : Dom ((typical (pathSum sa sb Q)).map (· - s)) (e.map (· - s)) := by
    rw [hty]
    exact hdom.map_mono (fun x y h => Nat.sub_le_sub_right h s)
  exact findPath_complete hQ hdom' ha hb

theorem mergeKids_exists (kmax : ℕ) : ∀ (ka kb : List AR) (kk : List CT),
    (∀ k ∈ ka, ∀ (A' : AR) (c : CT), AR.All (fun _ c => c ≠ []) k → AR.All (fun _ c => c ≠ []) A' →
      c ∈ joinC kmax (AR.charF Finset.card k) (AR.charF Finset.card A') → ∃ M, mergeAR k A' c = some M) →
    (∀ k ∈ ka, AR.All (fun _ c => c ≠ []) k) → (∀ k ∈ kb, AR.All (fun _ c => c ≠ []) k) →
    kk ∈ joinKids kmax (ka.map (AR.charF Finset.card)) (kb.map (AR.charF Finset.card)) →
    ∃ ks, mergeKids ka kb kk = some ks := by
  intro ka
  induction ka with
  | nil =>
    intro kb kk _ _ _ h
    cases kb with
    | nil => simp only [List.map_nil, joinKids, List.mem_singleton] at h; subst h; exact ⟨[], rfl⟩
    | cons b kb => simp [joinKids] at h
  | cons a ka ih =>
    intro kb kk hex hna hnb h
    cases kb with
    | nil => simp [joinKids] at h
    | cons b kb =>
      simp only [List.map_cons, joinKids, List.mem_flatMap, List.mem_map] at h
      obtain ⟨c, hc, kk', hkk', rfl⟩ := h
      obtain ⟨M, hM⟩ := hex a (by simp) b c (hna a (by simp)) (hnb b (by simp)) hc
      obtain ⟨ks, hks⟩ := ih kb kk' (fun k hk => hex k (List.mem_cons_of_mem _ hk))
        (fun k hk => hna k (List.mem_cons_of_mem _ hk)) (fun k hk => hnb k (List.mem_cons_of_mem _ hk)) hkk'
      exact ⟨M :: ks, by simp only [mergeKids, hM, hks, Option.bind_some, Option.map_some]⟩

/-- Every option of the join of two analyses (with non-empty chains everywhere) is realised by `mergeAR`. -/
theorem mergeAR_exists (kmax : ℕ) : ∀ (A : AR) (A' : AR) (c : CT),
    AR.All (fun _ c => c ≠ []) A → AR.All (fun _ c => c ≠ []) A' →
    c ∈ joinC kmax (AR.charF Finset.card A) (AR.charF Finset.card A') → ∃ M, mergeAR A A' c = some M := by
  intro A
  induction A using AR.ind with
  | _ S na ka ih =>
    intro A' c hA hA' hc
    obtain ⟨S', nb, kb⟩ := A'
    rw [AR.charF_run, AR.charF_run] at hc
    obtain ⟨hSS, hlen, d, kk, rfl, hkk, hd⟩ := joinC_inv hc
    have hna : na ≠ [] := hA.here
    have hnb : nb ≠ [] := hA'.here
    obtain ⟨Q, hQ⟩ := exists_findPath (s := S.card) (kmax := kmax) (sa := na.map (fun n => n.bag.card))
      (sb := nb.map (fun n => n.bag.card)) (by simpa using hna) (by simpa using hnb) (by
        simpa [List.map_map, Function.comp_def] using hd)
    obtain ⟨ks, hks⟩ := mergeKids_exists kmax ka kb kk
      (fun k hk A'' c' hk' hA'' hc' => ih k hk A'' c' hk' hA'' hc')
      (fun k hk => hA.kid hk) (fun k hk => hA'.kid hk) (by simpa [AR.charFL_eq] using hkk)
    refine ⟨.run S (mergeChain na nb none Q) ks, ?_⟩
    unfold mergeAR
    rw [hQ]
    simp only [hks, Option.map_some]

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeBasic` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeSide` -/

section
/-!
# One side of a merged chain (C3)

`PA n K i b` is the set of vertices below and at the `i`-th node of the chain `n` with tail `K` (the junk of the
node itself only if `b`).  The *side lemmas* describe how it changes when the merged path moves from the `i`-th to
the `i'`-th node of this side (`i' = i` or `i' = i + 1`); they are used for both sides of the merge.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The vertices at and below the `i`-th node (the junk of the node itself only if `b`). -/
def PA (n : List CNode) (K : List RT) (i : ℕ) (b : Bool) : Finset ℕ :=
  cbag n i ∪ (if b then RT.vertsL (cjunk n i) else ∅) ∪ RT.vertsL (succL n K i)

theorem mem_PA {n : List CNode} {K : List RT} {i : ℕ} {b : Bool} {x : ℕ} :
    x ∈ PA n K i b ↔ x ∈ cbag n i ∨ (b = true ∧ x ∈ RT.vertsL (cjunk n i)) ∨ x ∈ RT.vertsL (succL n K i) := by
  unfold PA
  cases b <;> simp [or_assoc]

/-- Moving to the same or the next node. -/
theorem PA_same {n : List CNode} {K : List RT} {i : ℕ} :
    PA n K i false = cbag n i ∪ RT.vertsL (succL n K i) := by
  unfold PA; simp

theorem PA_next {n : List CNode} {K : List RT} {i : ℕ} (hi : i + 1 < n.length) :
    PA n K (i + 1) true = RT.vertsL (succL n K i) := by
  ext x
  rw [mem_PA, vertsL_succL_lt hi]
  simp [or_assoc]

/-- The relation between the sets at `i` and at `i'` ∈ {i, i+1}. -/
theorem PA_step {n : List CNode} {K : List RT} {i i' : ℕ} (hi' : i' < n.length) (h : i' = i ∨ i' = i + 1) (b : Bool) :
    PA n K i b = cbag n i ∪ (if b then RT.vertsL (cjunk n i) else ∅) ∪ PA n K i' (decide (i ≠ i')) := by
  rcases h with rfl | rfl
  · simp only [ne_eq, not_true_eq_false, decide_false]
    rw [PA_same]
    unfold PA
    ext x; simp only [Finset.mem_union]; try tauto
  · have : decide (i ≠ i + 1) = true := by simp
    rw [this, PA_next hi']
    unfold PA
    ext x; simp only [Finset.mem_union]; try tauto

theorem PA_sub_step {n : List CNode} {K : List RT} {i i' : ℕ} (hi' : i' < n.length) (h : i' = i ∨ i' = i + 1) :
    ∀ x ∈ PA n K i' (decide (i ≠ i')), x ∈ cbag n i ∨ x ∈ RT.vertsL (succL n K i) := by
  intro x hx
  rcases h with rfl | rfl
  · simp only [ne_eq, not_true_eq_false, decide_false] at hx
    rw [PA_same] at hx
    exact Finset.mem_union.1 hx
  · have : decide (i ≠ i + 1) = true := by simp
    rw [this, PA_next hi'] at hx
    exact Or.inr hx

/-- Facts of one side used at a merged node. -/
theorem side_conn {n : List CNode} {K : List RT} {i i' : ℕ} (hi : i < n.length) (hi' : i' < n.length)
    (h : i' = i ∨ i' = i + 1)
    (hAr : ∀ K' ∈ cjunk n i ++ succL n K i, ∀ v ∈ cbag n i, v ∈ K'.verts → v ∈ K'.rootBag)
    (hAp : (cjunk n i ++ succL n K i).Pairwise
      (fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag n i)) :
    (∀ v ∈ cbag n i, v ∈ PA n K i' (decide (i ≠ i')) → v ∈ cbag n i') ∧
    (∀ J ∈ cjunk n i, ∀ v ∈ J.verts, v ∈ PA n K i' (decide (i ≠ i')) → v ∈ cbag n i) := by
  constructor
  · intro v hv hvP
    rcases h with rfl | rfl
    · exact hv
    · have : decide (i ≠ i + 1) = true := by simp
      rw [this, PA_next hi', mem_vertsL] at hvP
      obtain ⟨K', hK', hvK⟩ := hvP
      have := hAr K' (List.mem_append_right _ hK') v hv hvK
      rw [succL_of_lt hi', List.mem_singleton] at hK'
      subst hK'
      rw [rootBag_chainToRT_drop n K hi'] at this
      exact this
  · intro J hJ v hvJ hvP
    rcases PA_sub_step hi' h v hvP with h1 | h1
    · exact h1
    · rw [mem_vertsL] at h1
      obtain ⟨K', hK', hvK⟩ := h1
      rw [List.pairwise_append] at hAp
      exact hAp.2.2 J hJ K' hK' v hvJ hvK

/-- Coverage: what is below the `i`-th node is covered by what is at the `i'`-th. -/
theorem side_bags {n : List CNode} {K : List RT} {i i' : ℕ} (hi : i < n.length) (hi' : i' < n.length)
    (h : i' = i ∨ i' = i + 1) :
    ∀ K' ∈ succL n K i, ∀ X ∈ K'.bags,
      X = cbag n i' ∨ ((decide (i ≠ i') = true) ∧ ∃ J ∈ cjunk n i', X ∈ J.bags) ∨ ∃ K'' ∈ succL n K i', X ∈ K''.bags := by
  intro K' hK' X hX
  rcases h with rfl | rfl
  · right; right; exact ⟨K', hK', hX⟩
  · rw [succL_of_lt hi', List.mem_singleton] at hK'
    subst hK'
    rw [chainToRT_drop n K hi', RT.bags_node] at hX
    rcases hX with hX | ⟨J, hJ, hX⟩
    · left; exact hX
    · rcases List.mem_append.1 hJ with hJ | hJ
      · right; left; exact ⟨by simp, J, hJ, hX⟩
      · right; right; exact ⟨J, hJ, hX⟩

/-! ## the `B`-vertices of a side -/

theorem PA_inter_B {n : List CNode} {K : List RT} {B S : Finset ℕ}
    (hbag : ∀ x ∈ n, x.bag ∩ B = S) (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ∩ B ⊆ S)
    {i : ℕ} (hi : i < n.length) (b : Bool) :
    ∀ x ∈ PA n K i b, x ∈ B → x ∈ S ∨ x ∈ RT.vertsL K := by
  intro x hx hxB
  rw [mem_PA] at hx
  have hmem : n[i] ∈ n := List.getElem_mem hi
  rcases hx with hx | ⟨-, hx⟩ | hx
  · left
    have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
    rw [hb] at hx
    rw [← hbag _ hmem]; exact Finset.mem_inter.2 ⟨hx, hxB⟩
  · left
    have hj' : cjunk n i = n[i].junk := by unfold cjunk; rw [getD_chain hi]
    rw [hj', mem_vertsL] at hx
    obtain ⟨J, hJ, hxJ⟩ := hx
    exact hjunk _ hmem J hJ (Finset.mem_inter.2 ⟨hxJ, hxB⟩)
  · exact reg_verts hbag hjunk hi x hx hxB

theorem S_sub_PA {n : List CNode} {K : List RT} {B S : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ∩ B = S)
    {i : ℕ} (hi : i < n.length) (b : Bool) : S ⊆ PA n K i b := by
  intro x hx
  rw [mem_PA]
  left
  have hmem : n[i] ∈ n := List.getElem_mem hi
  have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
  rw [hb]
  have := hbag _ hmem
  rw [← this] at hx
  exact (Finset.mem_inter.1 hx).1

theorem vertsL_sub_PA {n : List CNode} {K : List RT} {i : ℕ} (hi : i < n.length) (b : Bool) :
    ∀ x ∈ RT.vertsL K, x ∈ PA n K i b := by
  intro x hx
  rw [mem_PA]
  exact Or.inr (Or.inr (vertsL_sub_succL hi x hx))

theorem succL_verts_sub {n : List CNode} {K : List RT} {U : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ⊆ U)
    (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ⊆ U) (hK : ∀ K' ∈ K, K'.verts ⊆ U) :
    ∀ d i, n.length = i + 1 + d → ∀ x ∈ RT.vertsL (succL n K i), x ∈ U := by
  intro d
  induction d with
  | zero =>
    intro i hi x hx
    rw [succL_of_last (by omega), mem_vertsL] at hx
    obtain ⟨K', hK', hxK⟩ := hx
    exact hK K' hK' hxK
  | succ d ih =>
    intro i hi x hx
    have hlt : i + 1 < n.length := by omega
    rw [vertsL_succL_lt hlt] at hx
    have hmem : n[i + 1] ∈ n := List.getElem_mem hlt
    rcases hx with hx | hx | hx
    · have hb : cbag n (i + 1) = n[i + 1].bag := by unfold cbag; rw [getD_chain hlt]
      rw [hb] at hx
      exact hbag _ hmem hx
    · have hj' : cjunk n (i + 1) = n[i + 1].junk := by unfold cjunk; rw [getD_chain hlt]
      rw [hj', mem_vertsL] at hx
      obtain ⟨J, hJ, hxJ⟩ := hx
      exact hjunk _ hmem J hJ hxJ
    · exact ih (i + 1) (by omega) x hx

theorem PA_sub_U {n : List CNode} {K : List RT} {U : Finset ℕ} (hbag : ∀ x ∈ n, x.bag ⊆ U)
    (hjunk : ∀ x ∈ n, ∀ J ∈ x.junk, J.verts ⊆ U) (hK : ∀ K' ∈ K, K'.verts ⊆ U) {i : ℕ} (hi : i < n.length)
    (b : Bool) : PA n K i b ⊆ U := by
  intro x hx
  have hmem : n[i] ∈ n := List.getElem_mem hi
  rw [mem_PA] at hx
  rcases hx with hx | ⟨-, hx⟩ | hx
  · have hb : cbag n i = n[i].bag := by unfold cbag; rw [getD_chain hi]
    rw [hb] at hx; exact hbag _ hmem hx
  · have hj' : cjunk n i = n[i].junk := by unfold cjunk; rw [getD_chain hi]
    rw [hj', mem_vertsL] at hx
    obtain ⟨J, hJ, hxJ⟩ := hx
    exact hjunk _ hmem J hJ hxJ
  · exact succL_verts_sub hbag hjunk hK (n.length - (i + 1)) i (by omega) x hx

theorem cbag_mem {n : List CNode} {i : ℕ} (hi : i < n.length) : cbag n i = n[i].bag := by
  unfold cbag; rw [getD_chain hi]

theorem cjunk_mem {n : List CNode} {i : ℕ} (hi : i < n.length) : cjunk n i = n[i].junk := by
  unfold cjunk; rw [getD_chain hi]

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeConn` -/

section
/-!
# `Conn` of a merged chain (C3)

The interface `MergeI KM KA KB` says that the tree `KM` is a merge of `KA` and `KB`: it is connected, its vertices and
root bag are the unions, and every bag of `KA`, `KB` is contained in a bag of `KM`.  `MergeCtx` collects the
hypotheses on the two chains and the merged kid trees; `chain_claim` proves the interface for the merged chain by
induction along the lattice path.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

structure MergeI (KM KA KB : RT) : Prop where
  conn : KM.Conn
  verts : KM.verts = KA.verts ∪ KB.verts
  root : KM.rootBag = KA.rootBag ∪ KB.rootBag
  bagsA : ∀ X ∈ KA.bags, ∃ Y ∈ KM.bags, X ⊆ Y
  bagsB : ∀ X ∈ KB.bags, ∃ Y ∈ KM.bags, X ⊆ Y

structure MergeCtx (B Ua Ub S : Finset ℕ) (nA nB : List CNode) (kAT kBT kMT : List RT) : Prop where
  hU : Ua ∩ Ub = B
  Abag : ∀ x ∈ nA, x.bag ⊆ Ua ∧ x.bag ∩ B = S
  Bbag : ∀ x ∈ nB, x.bag ⊆ Ub ∧ x.bag ∩ B = S
  Ajunk : ∀ x ∈ nA, ∀ J ∈ x.junk, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S
  Bjunk : ∀ x ∈ nB, ∀ J ∈ x.junk, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S
  Akid : ∀ K ∈ kAT, K.verts ⊆ Ua
  Bkid : ∀ K ∈ kBT, K.verts ⊆ Ub
  Aconn : (AR.chainToRT nA kAT).Conn
  Bconn : (AR.chainToRT nB kBT).Conn
  kids : F3 (fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B) kMT kAT kBT

/-! ## small helpers -/

theorem sub_ite {α : Type} (b : Bool) (l : List α) : (if b = true then l else []).Sublist l := by
  cases b <;> simp

theorem mem_vertsL_ite (b : Bool) (l : List RT) (x : ℕ) :
    x ∈ RT.vertsL (if b = true then l else []) ↔ b = true ∧ x ∈ RT.vertsL l := by
  cases b <;> simp [RT.mem_vertsL_iff]

theorem vertsL_kids {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) (x : ℕ) :
    x ∈ RT.vertsL kMT ↔ x ∈ RT.vertsL kAT ∨ x ∈ RT.vertsL kBT := by
  rw [mem_vertsL, mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨K, hK, hx⟩
    obtain ⟨a, ha, b, hb, hI, _⟩ := F3.mem_mid ctx.kids K hK
    rw [hI.verts] at hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl ⟨a, ha, hx⟩
    · exact Or.inr ⟨b, hb, hx⟩
  · rintro (⟨a, ha, hx⟩ | ⟨b, hb, hx⟩)
    · obtain ⟨m, hm, b, hb, hI, _⟩ := F3.mem_left ctx.kids a ha
      exact ⟨m, hm, by rw [hI.verts]; exact Finset.mem_union_left _ hx⟩
    · obtain ⟨m, hm, a, ha, hI, _⟩ := F3.mem_right ctx.kids b hb
      exact ⟨m, hm, by rw [hI.verts]; exact Finset.mem_union_right _ hx⟩

theorem kids_agree {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) (x : ℕ) (hx : x ∈ B) :
    x ∈ RT.vertsL kAT ↔ x ∈ RT.vertsL kBT := by
  rw [mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨a, ha, hxa⟩
    obtain ⟨m, hm, b, hb, hI, hag⟩ := F3.mem_left ctx.kids a ha
    have : x ∈ a.verts ∩ B := Finset.mem_inter.2 ⟨hxa, hx⟩
    rw [hag] at this
    exact ⟨b, hb, (Finset.mem_inter.1 this).1⟩
  · rintro ⟨b, hb, hxb⟩
    obtain ⟨m, hm, a, ha, hI, hag⟩ := F3.mem_right ctx.kids b hb
    have : x ∈ b.verts ∩ B := Finset.mem_inter.2 ⟨hxb, hx⟩
    rw [← hag] at this
    exact ⟨a, ha, (Finset.mem_inter.1 this).1⟩

/-- A `B`-vertex below a node on one side is below (the same-indexed node of) the other. -/
theorem PA_cross {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ} (hi : i < nA.length) (hj : j < nB.length)
    (b1 b2 : Bool) : ∀ x ∈ B, x ∈ PA nB kBT j b2 → x ∈ PA nA kAT i b1 := by
  intro x hxB hx
  rcases PA_inter_B (fun x hx => (ctx.Bbag x hx).2) (fun x hx J hJ => (ctx.Bjunk x hx J hJ).2) hj b2 x hx hxB with h | h
  · exact S_sub_PA (fun x hx => (ctx.Abag x hx).2) hi b1 h
  · exact vertsL_sub_PA hi b1 x ((kids_agree ctx x hxB).2 h)

theorem PB_cross {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ} (hi : i < nA.length) (hj : j < nB.length)
    (b1 b2 : Bool) : ∀ x ∈ B, x ∈ PA nA kAT i b1 → x ∈ PA nB kBT j b2 := by
  intro x hxB hx
  rcases PA_inter_B (fun x hx => (ctx.Abag x hx).2) (fun x hx J hJ => (ctx.Ajunk x hx J hJ).2) hi b1 x hx hxB with h | h
  · exact S_sub_PA (fun x hx => (ctx.Bbag x hx).2) hj b2 h
  · exact vertsL_sub_PA hj b2 x ((kids_agree ctx x hxB).1 h)

theorem mem_vertsL_append {l1 l2 : List RT} {x : ℕ} :
    x ∈ RT.vertsL (l1 ++ l2) ↔ x ∈ RT.vertsL l1 ∨ x ∈ RT.vertsL l2 := by
  rw [mem_vertsL, mem_vertsL, mem_vertsL]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact Or.inl ⟨k, hk, hx⟩
    · exact Or.inr ⟨k, hk, hx⟩
  · rintro (⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
    · exact ⟨k, List.mem_append_left _ hk, hx⟩
    · exact ⟨k, List.mem_append_right _ hk, hx⟩

theorem kid_verts_A {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) {m a b : RT} (hI : MergeI m a b)
    (hag : a.verts ∩ B = b.verts ∩ B) (hbU : b.verts ⊆ Ub) {v : ℕ} (hv : v ∈ Ua) (hvm : v ∈ m.verts) :
    v ∈ a.verts := by
  rw [hI.verts] at hvm
  rcases Finset.mem_union.1 hvm with h | h
  · exact h
  · have hvB : v ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨hv, hbU h⟩
    have : v ∈ b.verts ∩ B := Finset.mem_inter.2 ⟨h, hvB⟩
    rw [← hag] at this
    exact (Finset.mem_inter.1 this).1

theorem kid_verts_B {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) {m a b : RT} (hI : MergeI m a b)
    (hag : a.verts ∩ B = b.verts ∩ B) (haU : a.verts ⊆ Ua) {v : ℕ} (hv : v ∈ Ub) (hvm : v ∈ m.verts) :
    v ∈ b.verts := by
  rw [hI.verts] at hvm
  rcases Finset.mem_union.1 hvm with h | h
  · have hvB : v ∈ B := by rw [← hU]; exact Finset.mem_inter.2 ⟨haU h, hv⟩
    have : v ∈ a.verts ∩ B := Finset.mem_inter.2 ⟨h, hvB⟩
    rw [hag] at this
    exact (Finset.mem_inter.1 this).1
  · exact h

/-- The last node of a merged chain. -/
theorem claim_last {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j : ℕ}
    (hi : i < nA.length) (hj : j < nB.length) (hil : ¬ (i + 1 < nA.length)) (hjl : ¬ (j + 1 < nB.length))
    (b1 b2 : Bool) {T : RT}
    (hT : T = RT.node (cbag nA i ∪ cbag nB j)
        ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ kMT)) :
    T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
    (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i b1 ∨ x ∈ PA nB kBT j b2) ∧
    (∀ X, (X = cbag nA i ∨ (b1 = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨ ∃ K ∈ succL nA kAT i, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) ∧
    (∀ X, (X = cbag nB j ∨ (b2 = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨ ∃ K ∈ succL nB kBT j, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) := by
  subst hT
  obtain ⟨hAc, hAk, hAr, hAp⟩ := local_facts hi (conn_drop ctx.Aconn i hi)
  obtain ⟨hBc, hBk, hBr, hBp⟩ := local_facts hj (conn_drop ctx.Bconn j hj)
  have hsA : succL nA kAT i = kAT := succL_of_last hil
  have hsB : succL nB kBT j = kBT := succL_of_last hjl
  rw [hsA] at hAk hAr hAp
  rw [hsB] at hBk hBr hBp
  have hmA : nA[i] ∈ nA := List.getElem_mem hi
  have hmB : nB[j] ∈ nB := List.getElem_mem hj
  have hXA : cbag nA i ⊆ Ua := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).1
  have hAB : cbag nA i ∩ B = S := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).2
  have hXB : cbag nB j ⊆ Ub := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).1
  have hBB : cbag nB j ∩ B = S := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).2
  have hjA : ∀ J ∈ cjunk nA i, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hi]; exact fun J hJ => ctx.Ajunk _ hmA J hJ
  have hjB : ∀ J ∈ cjunk nB j, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hj]; exact fun J hJ => ctx.Bjunk _ hmB J hJ
  have hcisub : (if b1 = true then cjunk nA i else []).Sublist (cjunk nA i) := sub_ite b1 _
  have hcjsub : (if b2 = true then cjunk nB j else []).Sublist (cjunk nB j) := sub_ite b2 _
  have hSA : S ⊆ cbag nA i := by rw [← hAB]; exact Finset.inter_subset_left
  have hSB : S ⊆ cbag nB j := by rw [← hBB]; exact Finset.inter_subset_left
  have hconn : (RT.node (cbag nA i ∪ cbag nB j)
      ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ kMT)).Conn := by
    apply conn_merged_node (B := B) (Ua := Ua) (Ub := Ub) (S := S) ctx.hU hXA hXB hAB hBB
    · exact fun J hJ => hAc J (hcisub.subset hJ)
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).1
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).2
    · exact fun J hJ => hAr J (List.mem_append_left _ (hcisub.subset hJ))
    · exact List.Pairwise.sublist hcisub (List.pairwise_append.1 hAp).1
    · exact fun J hJ => hBc J (hcjsub.subset hJ)
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).1
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).2
    · exact fun J hJ => hBr J (List.mem_append_left _ (hcjsub.subset hJ))
    · exact List.Pairwise.sublist hcjsub (List.pairwise_append.1 hBp).1
    · -- successors are connected
      intro K hK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      exact hP.1.conn
    · intro K hK v hv hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hva := kid_verts_A ctx.hU hP.1 hP.2 (ctx.Bkid b hb) (hXA hv) hvK
      have := hAr a (List.mem_append_right _ ha) v hv hva
      rw [hP.1.root]; exact Finset.mem_union_left _ this
    · intro K hK v hv hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hvb := kid_verts_B ctx.hU hP.1 hP.2 (ctx.Akid a ha) (hXB hv) hvK
      have := hBr b (List.mem_append_right _ hb) v hv hvb
      rw [hP.1.root]; exact Finset.mem_union_right _ this
    · intro J hJ K hK v hvJ hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hJ' := hcisub.subset hJ
      by_cases hvUa : v ∈ Ua
      · have hva := kid_verts_A ctx.hU hP.1 hP.2 (ctx.Bkid b hb) hvUa hvK
        exact (List.pairwise_append.1 hAp).2.2 J hJ' a ha v hvJ hva
      · exact absurd ((hjA J hJ').1 hvJ) hvUa
    · intro J hJ K hK v hvJ hvK
      obtain ⟨a, ha, b, hb, hP⟩ := F3.mem_mid ctx.kids K hK
      have hJ' := hcjsub.subset hJ
      have hvUb := (hjB J hJ').1 hvJ
      have hvb := kid_verts_B ctx.hU hP.1 hP.2 (ctx.Akid a ha) hvUb hvK
      exact (List.pairwise_append.1 hBp).2.2 J hJ' b hb v hvJ hvb
    · -- pairwise successors
      apply F3.pairwise (P := fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B)
        (RA := fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag nA i)
        (RB := fun k1 k2 => ∀ v, v ∈ k1.verts → v ∈ k2.verts → v ∈ cbag nB j) ctx.kids _
        (List.pairwise_append.1 hAp).2.1 (List.pairwise_append.1 hBp).2.1
      intro m1 hm1 a1 ha1 b1 hb1 m2 hm2 a2 ha2 b2 hb2 P1 P2 R1 R2 v hv1 hv2
      have hs1 : v ∈ Ua ∨ v ∈ Ub := by
        rw [P1.1.verts] at hv1
        rcases Finset.mem_union.1 hv1 with h | h
        · exact Or.inl (ctx.Akid a1 ha1 h)
        · exact Or.inr (ctx.Bkid b1 hb1 h)
      rcases hs1 with hUa | hUb
      · have h1 := kid_verts_A ctx.hU P1.1 P1.2 (ctx.Bkid b1 hb1) hUa hv1
        have h2 := kid_verts_A ctx.hU P2.1 P2.2 (ctx.Bkid b2 hb2) hUa hv2
        exact Finset.mem_union_left _ (R1 v h1 h2)
      · have h1 := kid_verts_B ctx.hU P1.1 P1.2 (ctx.Akid a1 ha1) hUb hv1
        have h2 := kid_verts_B ctx.hU P2.1 P2.2 (ctx.Akid a2 ha2) hUb hv2
        exact Finset.mem_union_right _ (R2 v h1 h2)
  refine ⟨hconn, rfl, ?_, ?_, ?_⟩
  · intro x
    rw [RT.verts_node, ← mem_vertsL, mem_vertsL_append, mem_vertsL_append, mem_vertsL_ite, mem_vertsL_ite,
      vertsL_kids ctx, mem_PA, mem_PA, hsA, hsB]
    simp only [Finset.mem_union]
    tauto
  · intro X hX
    rcases hX with hX | ⟨hb1, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_left
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb1, if_true, List.mem_append]
      exact Or.inl (Or.inl hJ)
    · rw [hsA] at hK
      obtain ⟨m, hm, b, hb, hP⟩ := F3.mem_left ctx.kids K hK
      obtain ⟨Y, hY, hXY⟩ := hP.1.bagsA X hX
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨m, List.mem_append_right _ hm, hY⟩), hXY⟩
  · intro X hX
    rcases hX with hX | ⟨hb2, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_right
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb2, if_true, List.mem_append]
      exact Or.inl (Or.inr hJ)
    · rw [hsB] at hK
      obtain ⟨m, hm, a, ha, hP⟩ := F3.mem_right ctx.kids K hK
      obtain ⟨Y, hY, hXY⟩ := hP.1.bagsB X hX
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨m, List.mem_append_right _ hm, hY⟩), hXY⟩

theorem mem_ite_empty (b : Bool) (s : Finset ℕ) (x : ℕ) : x ∈ (if b = true then s else ∅) ↔ b = true ∧ x ∈ s := by
  cases b <;> simp

theorem logic_step (p1 p2 q1 q2 a b : Prop) :
    ((p1 ∨ p2) ∨ (q1 ∨ q2) ∨ a ∨ b) ↔ (((p1 ∨ q1) ∨ a) ∨ ((p2 ∨ q2) ∨ b)) := by tauto

/-- An inner node of a merged chain. -/
theorem claim_step {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) {i j i' j' : ℕ}
    (hi : i < nA.length) (hj : j < nB.length) (hi' : i' < nA.length) (hj' : j' < nB.length)
    (hst : LStep (i, j) (i', j')) (b1 b2 : Bool) {T T' : RT}
    (hC' : T'.Conn) (hR' : T'.rootBag = cbag nA i' ∪ cbag nB j')
    (hV' : ∀ x, x ∈ T'.verts ↔ x ∈ PA nA kAT i' (decide (i ≠ i')) ∨ x ∈ PA nB kBT j' (decide (j ≠ j')))
    (hCA' : ∀ X, (X = cbag nA i' ∨ (decide (i ≠ i') = true ∧ ∃ J ∈ cjunk nA i', X ∈ J.bags) ∨
      ∃ K ∈ succL nA kAT i', X ∈ K.bags) → ∃ Y ∈ T'.bags, X ⊆ Y)
    (hCB' : ∀ X, (X = cbag nB j' ∨ (decide (j ≠ j') = true ∧ ∃ J ∈ cjunk nB j', X ∈ J.bags) ∨
      ∃ K ∈ succL nB kBT j', X ∈ K.bags) → ∃ Y ∈ T'.bags, X ⊆ Y)
    (hT : T = RT.node (cbag nA i ∪ cbag nB j)
        ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ [T'])) :
    T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
    (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i b1 ∨ x ∈ PA nB kBT j b2) ∧
    (∀ X, (X = cbag nA i ∨ (b1 = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨ ∃ K ∈ succL nA kAT i, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) ∧
    (∀ X, (X = cbag nB j ∨ (b2 = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨ ∃ K ∈ succL nB kBT j, X ∈ K.bags) →
      ∃ Y ∈ T.bags, X ⊆ Y) := by
  subst hT
  have hAi : i' = i ∨ i' = i + 1 := by
    rcases hst with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp only at h1 <;> omega
  have hBj : j' = j ∨ j' = j + 1 := by
    rcases hst with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp only at h2 <;> omega
  obtain ⟨hAc, hAk, hAr, hAp⟩ := local_facts hi (conn_drop ctx.Aconn i hi)
  obtain ⟨hBc, hBk, hBr, hBp⟩ := local_facts hj (conn_drop ctx.Bconn j hj)
  obtain ⟨hSA1, hSA2⟩ := side_conn hi hi' hAi hAr hAp
  obtain ⟨hSB1, hSB2⟩ := side_conn hj hj' hBj hBr hBp
  have hmA : nA[i] ∈ nA := List.getElem_mem hi
  have hmB : nB[j] ∈ nB := List.getElem_mem hj
  have hXA : cbag nA i ⊆ Ua := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).1
  have hAB : cbag nA i ∩ B = S := by rw [cbag_mem hi]; exact (ctx.Abag _ hmA).2
  have hXB : cbag nB j ⊆ Ub := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).1
  have hBB : cbag nB j ∩ B = S := by rw [cbag_mem hj]; exact (ctx.Bbag _ hmB).2
  have hjA : ∀ J ∈ cjunk nA i, J.verts ⊆ Ua ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hi]; exact fun J hJ => ctx.Ajunk _ hmA J hJ
  have hjB : ∀ J ∈ cjunk nB j, J.verts ⊆ Ub ∧ J.verts ∩ B ⊆ S := by
    rw [cjunk_mem hj]; exact fun J hJ => ctx.Bjunk _ hmB J hJ
  have hcisub : (if b1 = true then cjunk nA i else []).Sublist (cjunk nA i) := sub_ite b1 _
  have hcjsub : (if b2 = true then cjunk nB j else []).Sublist (cjunk nB j) := sub_ite b2 _
  have hPAsub : PA nA kAT i' (decide (i ≠ i')) ⊆ Ua :=
    PA_sub_U (fun x hx => (ctx.Abag x hx).1) (fun x hx J hJ => (ctx.Ajunk x hx J hJ).1) ctx.Akid hi' _
  have hPBsub : PA nB kBT j' (decide (j ≠ j')) ⊆ Ub :=
    PA_sub_U (fun x hx => (ctx.Bbag x hx).1) (fun x hx J hJ => (ctx.Bjunk x hx J hJ).1) ctx.Bkid hj' _
  -- a vertex of `T'` in `Ua` lies in the `A`-part, one in `Ub` lies in the `B`-part
  have hToA : ∀ v ∈ Ua, v ∈ T'.verts → v ∈ PA nA kAT i' (decide (i ≠ i')) := by
    intro v hv hvT
    rcases (hV' v).1 hvT with h | h
    · exact h
    · have hvB : v ∈ B := by rw [← ctx.hU]; exact Finset.mem_inter.2 ⟨hv, hPBsub h⟩
      exact PA_cross ctx hi' hj' _ _ v hvB h
  have hToB : ∀ v ∈ Ub, v ∈ T'.verts → v ∈ PA nB kBT j' (decide (j ≠ j')) := by
    intro v hv hvT
    rcases (hV' v).1 hvT with h | h
    · have hvB : v ∈ B := by rw [← ctx.hU]; exact Finset.mem_inter.2 ⟨hPAsub h, hv⟩
      exact PB_cross ctx hi' hj' _ _ v hvB h
    · exact h
  have hconn : (RT.node (cbag nA i ∪ cbag nB j)
      ((if b1 = true then cjunk nA i else []) ++ (if b2 = true then cjunk nB j else []) ++ [T'])).Conn := by
    apply conn_merged_node (B := B) (Ua := Ua) (Ub := Ub) (S := S) ctx.hU hXA hXB hAB hBB
    · exact fun J hJ => hAc J (hcisub.subset hJ)
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).1
    · exact fun J hJ => (hjA J (hcisub.subset hJ)).2
    · exact fun J hJ => hAr J (List.mem_append_left _ (hcisub.subset hJ))
    · exact List.Pairwise.sublist hcisub (List.pairwise_append.1 hAp).1
    · exact fun J hJ => hBc J (hcjsub.subset hJ)
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).1
    · exact fun J hJ => (hjB J (hcjsub.subset hJ)).2
    · exact fun J hJ => hBr J (List.mem_append_left _ (hcjsub.subset hJ))
    · exact List.Pairwise.sublist hcjsub (List.pairwise_append.1 hBp).1
    · intro K hK; rw [List.mem_singleton] at hK; subst hK; exact hC'
    · intro K hK v hv hvK
      rw [List.mem_singleton] at hK; subst hK
      have := hSA1 v hv (hToA v (hXA hv) hvK)
      rw [hR']; exact Finset.mem_union_left _ this
    · intro K hK v hv hvK
      rw [List.mem_singleton] at hK; subst hK
      have := hSB1 v hv (hToB v (hXB hv) hvK)
      rw [hR']; exact Finset.mem_union_right _ this
    · intro J hJ K hK v hvJ hvK
      rw [List.mem_singleton] at hK; subst hK
      have hJ' := hcisub.subset hJ
      exact hSA2 J hJ' v hvJ (hToA v ((hjA J hJ').1 hvJ) hvK)
    · intro J hJ K hK v hvJ hvK
      rw [List.mem_singleton] at hK; subst hK
      have hJ' := hcjsub.subset hJ
      exact hSB2 J hJ' v hvJ (hToB v ((hjB J hJ').1 hvJ) hvK)
    · exact List.pairwise_singleton _ _
  refine ⟨hconn, rfl, ?_, ?_, ?_⟩
  · intro x
    rw [RT.verts_node, ← mem_vertsL, mem_vertsL_append, mem_vertsL_append, mem_vertsL_ite, mem_vertsL_ite,
      PA_step hi' hAi b1, PA_step hj' hBj b2]
    simp only [mem_vertsL, List.mem_singleton, exists_eq_left, Finset.mem_union, mem_ite_empty]
    rw [hV' x]
    exact logic_step _ _ _ _ _ _
  · intro X hX
    rcases hX with hX | ⟨hb1, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_left
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb1, if_true, List.mem_append]
      exact Or.inl (Or.inl hJ)
    · obtain ⟨Y, hY, hXY⟩ := hCA' X (side_bags hi hi' hAi K hK X hX)
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨T', by simp, hY⟩), hXY⟩
  · intro X hX
    rcases hX with hX | ⟨hb2, J, hJ, hX⟩ | ⟨K, hK, hX⟩
    · refine ⟨cbag nA i ∪ cbag nB j, (RT.bags_node _ _).2 (Or.inl rfl), ?_⟩
      rw [hX]; exact Finset.subset_union_right
    · refine ⟨X, (RT.bags_node _ _).2 (Or.inr ⟨J, ?_, hX⟩), Finset.Subset.refl _⟩
      simp only [hb2, if_true, List.mem_append]
      exact Or.inl (Or.inr hJ)
    · obtain ⟨Y, hY, hXY⟩ := hCB' X (side_bags hj hj' hBj K hK X hX)
      exact ⟨Y, (RT.bags_node _ _).2 (Or.inr ⟨T', by simp, hY⟩), hXY⟩

/-! ## the induction along the path -/

def nw1 (prev : Option (ℕ × ℕ)) (i : ℕ) : Bool := prev.elim true (fun p => decide (p.1 ≠ i))
def nw2 (prev : Option (ℕ × ℕ)) (j : ℕ) : Bool := prev.elim true (fun p => decide (p.2 ≠ j))

theorem mergeChain_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (rest : List (ℕ × ℕ)) :
    mergeChain na nb prev ((i, j) :: rest) =
      ⟨cbag na i ∪ cbag nb j, (if nw1 prev i = true then cjunk na i else []) ++
        (if nw2 prev j = true then cjunk nb j else [])⟩ :: mergeChain na nb (some (i, j)) rest := rfl

theorem chainToRT_merge_last (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (K : List RT) :
    AR.chainToRT (mergeChain na nb prev [(i, j)]) K =
      RT.node (cbag na i ∪ cbag nb j)
        ((if nw1 prev i = true then cjunk na i else []) ++ (if nw2 prev j = true then cjunk nb j else []) ++ K) := by
  rw [mergeChain_cons]
  rfl

theorem chainToRT_merge_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j i' j' : ℕ)
    (rest : List (ℕ × ℕ)) (K : List RT) :
    AR.chainToRT (mergeChain na nb prev ((i, j) :: (i', j') :: rest)) K =
      RT.node (cbag na i ∪ cbag nb j)
        ((if nw1 prev i = true then cjunk na i else []) ++ (if nw2 prev j = true then cjunk nb j else []) ++
          [AR.chainToRT (mergeChain na nb (some (i, j)) ((i', j') :: rest)) K]) := by
  rw [mergeChain_cons na nb prev i j ((i', j') :: rest), mergeChain_cons na nb (some (i, j)) i' j' rest]
  rfl

theorem chain_claim {B Ua Ub S : Finset ℕ} {nA nB : List CNode} {kAT kBT kMT : List RT}
    (ctx : MergeCtx B Ua Ub S nA nB kAT kBT kMT) :
    ∀ (Q : List (ℕ × ℕ)) (i j : ℕ) (prev : Option (ℕ × ℕ)),
      Q.head? = some (i, j) → Q.getLast? = some (nA.length - 1, nB.length - 1) → Q.IsChain LStep →
      (∀ p, prev = some p → LStep p (i, j)) → i < nA.length → j < nB.length →
      ∀ T, T = AR.chainToRT (mergeChain nA nB prev Q) kMT →
        T.Conn ∧ T.rootBag = cbag nA i ∪ cbag nB j ∧
        (∀ x, x ∈ T.verts ↔ x ∈ PA nA kAT i (nw1 prev i) ∨ x ∈ PA nB kBT j (nw2 prev j)) ∧
        (∀ X, (X = cbag nA i ∨ (nw1 prev i = true ∧ ∃ J ∈ cjunk nA i, X ∈ J.bags) ∨
          ∃ K ∈ succL nA kAT i, X ∈ K.bags) → ∃ Y ∈ T.bags, X ⊆ Y) ∧
        (∀ X, (X = cbag nB j ∨ (nw2 prev j = true ∧ ∃ J ∈ cjunk nB j, X ∈ J.bags) ∨
          ∃ K ∈ succL nB kBT j, X ∈ K.bags) → ∃ Y ∈ T.bags, X ⊆ Y) := by
  intro Q
  induction Q with
  | nil => intro i j prev h; simp at h
  | cons q rest ih =>
    intro i j prev hh hl hc hp hi hj T hT
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq, Prod.mk.injEq] at hl
      rw [chainToRT_merge_last] at hT
      exact claim_last ctx hi hj (by omega) (by omega) _ _ hT
    | cons q' rest' =>
      obtain ⟨i', j'⟩ := q'
      rw [List.isChain_cons_cons] at hc
      rw [List.getLast?_cons_cons] at hl
      have hlast := chain_le_last rest' (i', j') hc.2 _ (by rw [hl]; rfl)
      simp only at hlast
      have hi' : i' < nA.length := by omega
      have hj' : j' < nB.length := by omega
      rw [chainToRT_merge_cons] at hT
      have IH := ih i' j' (some (i, j)) rfl hl hc.2 (by intro p hp; simp only [Option.some.injEq] at hp; subst hp; exact hc.1)
        hi' hj' _ rfl
      obtain ⟨hC', hR', hV', hCA', hCB'⟩ := IH
      have e1 : nw1 (some (i, j)) i' = decide (i ≠ i') := rfl
      have e2 : nw2 (some (i, j)) j' = decide (j ≠ j') := rfl
      rw [e1, e2] at hV'
      rw [e1] at hCA'
      rw [e2] at hCB'
      exact claim_step ctx hi hj hi' hj' hc.1 _ _ hC' hR' hV' hCA' hCB' hT

end Lax117284Proofs.Treewidth.Chars

end

/-! ### `Lax117284Proofs.Treewidth.Chars.MergeIface` -/

section
/-!
# The interface of a merged run (C3)

`merge_interface`: if `mergeAR A A' c = some M` for two canonical analyses `A`, `A'` of tree decompositions of graphs on
`Ua`, `Ub` with `Ua ∩ Ub = B` and `c` a join option of their characteristics, then `M.toRT` is connected, has the
union of the vertex sets and root bags, and contains (a superset of) every bag of `A.toRT` and `A'.toRT`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## vertices and bags of a chain -/

theorem verts_chainToRT_cons (a : CNode) (r : List CNode) (K : List RT) (x : ℕ) :
    x ∈ (AR.chainToRT (a :: r) K).verts ↔
      x ∈ a.bag ∨ (∃ J ∈ a.junk, x ∈ J.verts) ∨ x ∈ (AR.chainToRT r K).verts := by
  cases r with
  | nil =>
    rw [AR.chainToRT, RT.verts_node, AR.chainToRT, RT.verts_node]
    simp only [List.mem_append, Finset.notMem_empty, false_or]
    constructor
    · rintro (h | ⟨k, hk | hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, hk, hx⟩)
      · exact Or.inr (Or.inr ⟨k, hk, hx⟩)
    · rintro (h | ⟨k, hk, hx⟩ | ⟨k, hk, hx⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl hk, hx⟩
      · exact Or.inr ⟨k, Or.inr hk, hx⟩
  | cons b r =>
    rw [AR.chainToRT, RT.verts_node]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨k, hk | rfl, hx⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨k, hk, hx⟩)
      · exact Or.inr (Or.inr hx)
    · rintro (h | ⟨k, hk, hx⟩ | hx)
      · exact Or.inl h
      · exact Or.inr ⟨k, Or.inl hk, hx⟩
      · exact Or.inr ⟨_, Or.inr rfl, hx⟩

theorem mem_verts_chainToRT (K : List RT) : ∀ (n : List CNode) (x : ℕ),
    x ∈ (AR.chainToRT n K).verts ↔ (∃ y ∈ n, x ∈ y.bag) ∨ (∃ y ∈ n, ∃ J ∈ y.junk, x ∈ J.verts) ∨
      ∃ K' ∈ K, x ∈ K'.verts := by
  intro n
  induction n with
  | nil => intro x; simp [AR.chainToRT, RT.verts_node]
  | cons a r ih =>
    intro x
    rw [verts_chainToRT_cons, ih x]
    constructor
    · rintro (h | ⟨J, hJ, hx⟩ | ⟨y, hy, hxy⟩ | ⟨y, hy, hx⟩ | h)
      · exact Or.inl ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, J, hJ, hx⟩)
      · exact Or.inl ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
      · obtain ⟨J, hJ, hxJ⟩ := hx
        exact Or.inr (Or.inl ⟨y, List.mem_cons_of_mem _ hy, J, hJ, hxJ⟩)
      · exact Or.inr (Or.inr h)
    · rintro (⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | h)
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inl hxy
        · exact Or.inr (Or.inr (Or.inl ⟨y, hy, hxy⟩))
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact Or.inr (Or.inl ⟨J, hJ, hxJ⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨y, hy, J, hJ, hxJ⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-! ## `B`-vertices of the profile and the analysis -/

theorem verts_prof (B : Finset ℕ) : ∀ t : RT, CT.verts (RT.prof B t) = t.verts ∩ B := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [RT.prof_node]
    ext x
    simp only [CT.mem_verts, Finset.mem_inter, RT.verts_node, List.mem_map]
    constructor
    · rintro (h | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · exact ⟨Or.inl h.1, h.2⟩
      · rw [ih k hk, Finset.mem_inter] at hx
        exact ⟨Or.inr ⟨k, hk, hx.1⟩, hx.2⟩
    · rintro ⟨h | ⟨k, hk, hx⟩, hxB⟩
      · exact Or.inl ⟨h, hxB⟩
      · exact Or.inr ⟨_, ⟨k, hk, rfl⟩, by rw [ih k hk]; exact Finset.mem_inter.2 ⟨hx, hxB⟩⟩

theorem verts_char (B : Finset ℕ) (t : RT) : CT.verts (t.char B) = t.verts ∩ B := by
  unfold RT.char; rw [verts_norm, verts_prof]

/-- Junk contains no `B`-vertex outside the label. -/
theorem verts_inter_B_of_Jk {B S : Finset ℕ} {J : RT} (h : Jk B S J) : J.verts ∩ B ⊆ S := by
  intro v hv
  have h1 : v ∈ CT.verts (J.char B) := by rw [verts_char]; exact hv
  rw [char_eq_charF] at h1
  obtain ⟨hleaf, hsub⟩ := h
  cases hA : analyze B J with
  | run S' c ks =>
    rw [hA] at hleaf hsub h1
    simp only [AR.isLeaf, AR.kids, List.isEmpty_iff] at hleaf
    subst hleaf
    simp only [AR.charF_run, List.map_nil, CT.mem_verts] at h1
    simp only [AR.S] at hsub
    rcases h1 with h1 | ⟨k, hk, _⟩
    · exact hsub h1
    · simp at hk

/-- `B`-vertices of a canonical analysis are those of its labels. -/
theorem toRT_verts_inter_B (B : Finset ℕ) (f : Finset ℕ → ℕ) : ∀ r : AR, Canon B r →
    ∀ x, (x ∈ (AR.toRT r).verts ∧ x ∈ B) ↔ x ∈ CT.verts (AR.charF f r) := by
  intro r
  induction r using AR.ind with
  | _ S c ks ih =>
    intro h x
    rw [canon_run] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [AR.toRT_run, mem_verts_chainToRT, AR.charF_run, CT.mem_verts]
    simp only [List.mem_map]
    have hS : ∀ y ∈ c, y.bag ∩ B = S := fun y hy => (h2 y hy).1
    constructor
    · rintro ⟨(⟨y, hy, hxy⟩ | ⟨y, hy, J, hJ, hxJ⟩ | ⟨K', ⟨k, hk, rfl⟩, hxk⟩), hxB⟩
      · left; rw [← hS y hy]; exact Finset.mem_inter.2 ⟨hxy, hxB⟩
      · left
        exact verts_inter_B_of_Jk ((h2 y hy).2 J hJ) (Finset.mem_inter.2 ⟨hxJ, hxB⟩)
      · right
        exact ⟨_, ⟨k, hk, rfl⟩, (ih k hk (h7 k hk) x).1 ⟨hxk, hxB⟩⟩
    · rintro (hx | ⟨_, ⟨k, hk, rfl⟩, hx⟩)
      · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil c h1
        have : x ∈ y.bag ∩ B := by rw [hS y hy]; exact hx
        exact ⟨Or.inl ⟨y, hy, (Finset.mem_inter.1 this).1⟩, (Finset.mem_inter.1 this).2⟩
      · obtain ⟨hv, hB⟩ := (ih k hk (h7 k hk) x).2 hx
        exact ⟨Or.inr (Or.inr ⟨_, ⟨k, hk, rfl⟩, hv⟩), hB⟩

/-! ## the joined runs have the same labels -/

mutual
theorem joinC_verts_aux_rec (kmax : ℕ) : ∀ (a b c : CT), c ∈ joinC kmax a b → CT.verts a = CT.verts b
  | node S y ks, node S' y' ks', c, h => by
    obtain ⟨rfl, hl, d, kk, rfl, hkk, hd⟩ := joinC_inv h
    have := joinKids_verts_aux_rec kmax ks ks' kk hkk
    simp only [CT.verts, this]
theorem joinKids_verts_aux_rec (kmax : ℕ) : ∀ (ks ks' : List CT) (kk : List CT),
    kk ∈ joinKids kmax ks ks' → CT.vertsL ks = CT.vertsL ks'
  | [], [], _, _ => rfl
  | k :: ks, k' :: ks', kk, h => by
    simp only [joinKids, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, kk', hkk', rfl⟩ := h
    have h1 := joinC_verts_aux_rec kmax k k' c hc
    have h2 := joinKids_verts_aux_rec kmax ks ks' kk' hkk'
    simp only [CT.vertsL, h1, h2]
  | [], _ :: _, _, h => by simp [joinKids] at h
  | _ :: _, [], _, h => by simp [joinKids] at h
end

theorem joinC_verts_aux_pair : (type_of% @joinC_verts_aux_rec) ∧ (type_of% @joinKids_verts_aux_rec) :=
  ⟨@joinC_verts_aux_rec, @joinKids_verts_aux_rec⟩

theorem joinC_verts_aux : type_of% @joinC_verts_aux_rec := joinC_verts_aux_pair.1

/-! ## the package of an analysis of a tree decomposition -/

mutual
/-- `r` is connected, lives on `U`, and so do its kids. -/
def Pkg (U : Finset ℕ) : AR → Prop
  | .run S c ks => (AR.toRT (.run S c ks)).Conn ∧ (AR.toRT (.run S c ks)).verts ⊆ U ∧ PkgL U ks
def PkgL (U : Finset ℕ) : List AR → Prop
  | [] => True
  | k :: ks => Pkg U k ∧ PkgL U ks
end

theorem pkgL_iff (U : Finset ℕ) : ∀ ks : List AR, PkgL U ks ↔ ∀ k ∈ ks, Pkg U k
  | [] => by simp [PkgL]
  | k :: ks => by simp [PkgL, pkgL_iff U ks]

theorem pkg_run (U : Finset ℕ) (S : Finset ℕ) (c : List CNode) (ks : List AR) :
    Pkg U (.run S c ks) ↔ (AR.toRT (.run S c ks)).Conn ∧ (AR.toRT (.run S c ks)).verts ⊆ U ∧ ∀ k ∈ ks, Pkg U k := by
  simp only [Pkg, pkgL_iff]

theorem pkg_kids {U : Finset ℕ} {r : AR} (h : Pkg U r) : ∀ k ∈ r.kids, Pkg U k := by
  cases r with
  | run S c ks => exact ((pkg_run U S c ks).1 h).2.2

theorem pkg_intro {U : Finset ℕ} {r : AR} (h1 : (AR.toRT r).Conn) (h2 : (AR.toRT r).verts ⊆ U)
    (h3 : ∀ k ∈ r.kids, Pkg U k) : Pkg U r := by
  cases r with
  | run S c ks => exact (pkg_run U S c ks).2 ⟨h1, h2, h3⟩

theorem mkNode_kids_pkg {U : Finset ℕ} (S X : Finset ℕ) (junk : List RT) (core : List AR)
    (hcore : ∀ r ∈ core, Pkg U r) : ∀ k ∈ (mkNode S X junk core).kids, Pkg U k := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp [mkNode, AR.kids]
  · simp only [mkNode]
    have hk := hcore k (by simp)
    obtain ⟨S', c, ks⟩ := k
    by_cases h : S' = S
    · subst h
      simp only [AR.S, if_true, AR.kids]
      exact fun k' hk' => pkg_kids hk k' hk'
    · have : (AR.run S' c ks).S ≠ S := h
      simp only [this, if_false, AR.kids]
      intro k' hk'
      simp only [List.mem_singleton] at hk'
      subst hk'; exact hk
  · simp only [mkNode, AR.kids]
    intro k' hk'
    exact hcore k' (mem_sortAR.1 hk')

theorem pkg_analyze (B U : Finset ℕ) : ∀ t : RT, t.Conn → t.verts ⊆ U → Pkg U (analyze B t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc hv
    rw [analyze_node_shape]
    have hcore : ∀ r ∈ ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)), Pkg U r := by
      intro r hr
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
      have hk1 := (List.mem_filter.1 hk).1
      obtain ⟨h1, -, -⟩ := (RT.conn_node_iff X ks).1 hc
      refine ih k hk1 (h1 k hk1) (fun x hx => hv ?_)
      rw [RT.verts_node]; exact Or.inr ⟨k, hk1, hx⟩
    have hkids := mkNode_kids_pkg (U := U) (X ∩ B) X (ks.filter (fun k => prunedB (X ∩ B) (analyze B k))) _ hcore
    refine pkg_intro ?_ ?_ hkids
    · have := conn_toRT_analyze B (.node X ks) hc
      rwa [analyze_node_shape] at this
    · have := verts_toRT_analyze B (.node X ks)
      rw [analyze_node_shape] at this
      rw [this]; exact hv

/-! ## the merged run -/

theorem chainToRT_facts (K : List RT) : ∀ n : List CNode, (∀ y ∈ n, y.bag ⊆ (AR.chainToRT n K).verts) ∧
    (∀ y ∈ n, ∀ J ∈ y.junk, J.verts ⊆ (AR.chainToRT n K).verts) ∧ (∀ K' ∈ K, K'.verts ⊆ (AR.chainToRT n K).verts) := by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro y hy x hx
    rw [mem_verts_chainToRT]; exact Or.inl ⟨y, hy, hx⟩
  · intro y hy J hJ x hx
    rw [mem_verts_chainToRT]; exact Or.inr (Or.inl ⟨y, hy, J, hJ, hx⟩)
  · intro K' hK' x hx
    rw [mem_verts_chainToRT]; exact Or.inr (Or.inr ⟨K', hK', hx⟩)

theorem kids_iface {B Ua Ub : Finset ℕ} (kmax : ℕ) :
    ∀ (kA kB : List AR) (kk : List CT) (kM : List AR),
    (∀ a ∈ kA, ∀ (b : AR) (t : CT) (m : AR), Canon B a → Canon B b → Pkg Ua a → Pkg Ub b →
      t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b) → mergeAR a b t = some m →
      MergeI (AR.toRT m) (AR.toRT a) (AR.toRT b)) →
    (∀ a ∈ kA, Canon B a ∧ Pkg Ua a) → (∀ b ∈ kB, Canon B b ∧ Pkg Ub b) →
    F4 (fun a b t m => mergeAR a b t = some m) kA kB kk kM →
    F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB kk →
    F3 (fun KM KA KB => MergeI KM KA KB ∧ KA.verts ∩ B = KB.verts ∩ B)
      (kM.map AR.toRT) (kA.map AR.toRT) (kB.map AR.toRT) := by
  intro kA
  induction kA with
  | nil =>
    intro kB kk kM _ _ _ h4 h3
    cases kB <;> cases kk <;> cases kM <;> simp_all [F4, F3]
  | cons a kA ih =>
    intro kB kk kM hih hca hcb h4 h3
    cases kB with
    | nil => cases kk <;> cases kM <;> simp [F4] at h4
    | cons b kB =>
      cases kk with
      | nil => simp [F4] at h4
      | cons t kk =>
        cases kM with
        | nil => simp [F4] at h4
        | cons m kM =>
          refine ⟨⟨?_, ?_⟩, ih kB kk kM (fun a' ha' => hih a' (List.mem_cons_of_mem _ ha'))
            (fun a' ha' => hca a' (List.mem_cons_of_mem _ ha'))
            (fun b' hb' => hcb b' (List.mem_cons_of_mem _ hb')) h4.2 h3.2⟩
          · exact hih a (by simp) b t m (hca a (by simp)).1 (hcb b (by simp)).1 (hca a (by simp)).2
              (hcb b (by simp)).2 h3.1 h4.1
          · have e1 := toRT_verts_inter_B B Finset.card a (hca a (by simp)).1
            have e2 := toRT_verts_inter_B B Finset.card b (hcb b (by simp)).1
            have e3 := joinC_verts_aux kmax _ _ t h3.1
            ext x
            simp only [Finset.mem_inter]
            rw [e1 x, e2 x, e3]

theorem bags_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) (X : Finset ℕ)
    (hX : X ∈ (AR.chainToRT n K).bags) :
    X = cbag n 0 ∨ (∃ J ∈ cjunk n 0, X ∈ J.bags) ∨ ∃ K' ∈ succL n K 0, X ∈ K'.bags := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := chainToRT_drop n K hlen
  rw [List.drop_zero] at this
  rw [this, RT.bags_node] at hX
  rcases hX with hX | ⟨J, hJ, hX⟩
  · exact Or.inl hX
  · rcases List.mem_append.1 hJ with hJ | hJ
    · exact Or.inr (Or.inl ⟨J, hJ, hX⟩)
    · exact Or.inr (Or.inr ⟨J, hJ, hX⟩)

theorem verts_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) (x : ℕ) :
    x ∈ (AR.chainToRT n K).verts ↔ x ∈ PA n K 0 true := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := verts_drop n K hlen x
  rw [List.drop_zero] at this
  rw [this, mem_PA, mem_vertsL, mem_vertsL]
  simp

theorem rootBag_chain_zero {n : List CNode} {K : List RT} (hn : n ≠ []) :
    (AR.chainToRT n K).rootBag = cbag n 0 := by
  have hlen : 0 < n.length := List.length_pos_iff.2 hn
  have := rootBag_chainToRT_drop n K hlen
  rwa [List.drop_zero] at this

/-- **The interface of a merged run.** -/
theorem merge_interface {B Ua Ub : Finset ℕ} (hU : Ua ∩ Ub = B) (kmax : ℕ) :
    ∀ (A A' : AR) (c : CT) (M : AR), Canon B A → Canon B A' → Pkg Ua A → Pkg Ub A' →
      c ∈ joinC kmax (AR.charF Finset.card A) (AR.charF Finset.card A') →
      mergeAR A A' c = some M → MergeI (AR.toRT M) (AR.toRT A) (AR.toRT A') := by
  intro A
  induction A using AR.ind with
  | _ S nA kA ih =>
    intro A' c M hcA hcA' hpA hpA' hc hM
    obtain ⟨S', nB, kB⟩ := A'
    obtain ⟨T, ty, tk⟩ := c
    rw [AR.charF_run, AR.charF_run] at hc
    obtain ⟨hSS, hlen, d, kk, hcd, hkk, hd⟩ := joinC_inv hc
    obtain ⟨rfl, rfl, rfl⟩ : T = S ∧ ty = d ∧ tk = kk := by
      simp only [node.injEq] at hcd; exact hcd
    subst hSS
    obtain ⟨Q, kM, hQ, hK, rfl⟩ := mergeAR_inv hM
    have hF4 := mergeKids_F4 kA kB tk kM hK
    have hF3 : F3 (fun a b t => t ∈ joinC kmax (AR.charF Finset.card a) (AR.charF Finset.card b)) kA kB tk :=
      joinKids_F3 kmax (f := AR.charF Finset.card) (g := AR.charF Finset.card) kA kB tk
        (by simpa [AR.charFL_eq] using hkk)
    rw [canon_run] at hcA hcA'
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hcA
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ := hcA'
    have hpA1 := (pkg_run Ua _ _ _).1 hpA
    have hpB1 := (pkg_run Ub _ _ _).1 hpA'
    have hkids := kids_iface (B := B) (Ua := Ua) (Ub := Ub) kmax kA kB tk kM
      (fun a ha b t m hca hcb hpa hpb ht hm => ih a ha b t m hca hcb hpa hpb ht hm)
      (fun a ha => ⟨hA7 a ha, hpA1.2.2 a ha⟩) (fun b hb => ⟨hB7 b hb, hpB1.2.2 b hb⟩) hF4 hF3
    rw [AR.toRT_run] at hpA1 hpB1
    have hfA := chainToRT_facts (kA.map AR.toRT) nA
    have hfB := chainToRT_facts (kB.map AR.toRT) nB
    have ctx : MergeCtx B Ua Ub T nA nB (kA.map AR.toRT) (kB.map AR.toRT) (kM.map AR.toRT) :=
      { hU := hU
        Abag := fun x hx => ⟨fun v hv => hpA1.2.1 (hfA.1 x hx hv), (hA2 x hx).1⟩
        Bbag := fun x hx => ⟨fun v hv => hpB1.2.1 (hfB.1 x hx hv), (hB2 x hx).1⟩
        Ajunk := fun x hx J hJ => ⟨fun v hv => hpA1.2.1 (hfA.2.1 x hx J hJ hv),
          verts_inter_B_of_Jk ((hA2 x hx).2 J hJ)⟩
        Bjunk := fun x hx J hJ => ⟨fun v hv => hpB1.2.1 (hfB.2.1 x hx J hJ hv),
          verts_inter_B_of_Jk ((hB2 x hx).2 J hJ)⟩
        Akid := fun K hK => fun v hv => hpA1.2.1 (hfA.2.2 K hK hv)
        Bkid := fun K hK => fun v hv => hpB1.2.1 (hfB.2.2 K hK hv)
        Aconn := hpA1.1
        Bconn := hpB1.1
        kids := hkids }
    obtain ⟨hpath1, hpath2, hpath3⟩ := (findPath_spec hQ).1
    have hnA : 0 < nA.length := List.length_pos_iff.2 hA1
    have hnB : 0 < nB.length := List.length_pos_iff.2 hB1
    have hclaim := chain_claim ctx Q 0 0 none (by simpa using hpath1)
      (by simpa using hpath2) hpath3 (by intro p hp; simp at hp) hnA hnB (AR.chainToRT (mergeChain nA nB none Q) (kM.map AR.toRT)) rfl
    obtain ⟨hC, hR, hV, hCA, hCB⟩ := hclaim
    have hrA : (AR.toRT (.run T nA kA)).rootBag = cbag nA 0 := by
      rw [AR.toRT_run]; exact rootBag_chain_zero hA1
    have hrB : (AR.toRT (.run T nB kB)).rootBag = cbag nB 0 := by
      rw [AR.toRT_run]; exact rootBag_chain_zero hB1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [AR.toRT_run]; exact hC
    · rw [AR.toRT_run] at *
      ext x
      rw [Finset.mem_union, hV x]
      rw [AR.toRT_run, verts_chain_zero hA1, AR.toRT_run, verts_chain_zero hB1]
      rfl
    · rw [hrA, hrB, AR.toRT_run]; exact hR
    · intro X hX
      rw [AR.toRT_run] at hX
      have hX' := bags_chain_zero hA1 X hX
      rw [AR.toRT_run]
      exact hCA X (by
        rcases hX' with h | ⟨J, hJ, h⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨rfl, J, hJ, h⟩)
        · exact Or.inr (Or.inr h))
    · intro X hX
      rw [AR.toRT_run] at hX
      have hX' := bags_chain_zero hB1 X hX
      rw [AR.toRT_run]
      exact hCB X (by
        rcases hX' with h | ⟨J, hJ, h⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨rfl, J, hJ, h⟩)
        · exact Or.inr (Or.inr h))

end Lax117284Proofs.Treewidth.Chars

end
