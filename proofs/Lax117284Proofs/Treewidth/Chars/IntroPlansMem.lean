import Lax117284Proofs.Treewidth.Chars.Alg
import Lax117284Proofs.Treewidth.Chars.IntroChains
import Lax117284Proofs.Treewidth.Seq.Concat
import Lax117284Proofs.Treewidth.Seq.Transport

/-!
# The options of `introPlans`, as inductively described result sets (work package C4, part 3)

`introPlans v N t` enumerates triples `(path, plan, result)`; only the *results* matter for the exact and typical
layers.  Here the set of results is described by recursive propositions in terms of `Seq.splits` (the enumeration by
`Cut`s and `List.range`s is turned into membership in `splits`):

* `WinR v t r c` — `(r, c)` is the replacement subtree and covered vertex set of a region `W` containing the first
  tree node of the run `t` (`winPlans v 0 t`);
* `KidR v ks kids c` — per kid: leave it, or continue into it;
* `WtopR v t r c` — `W` has its topmost node inside the run (`wtopPlans v t`);
* `AttR v N t r` — a new branch hangs at a node of the run (`attachPlans v N t`);
* `IR v N t r` — the results of `introPlans v N t` (inductive family: at the run, or inside a kid).

`mem_introPlans : (∃ path plan, (path, plan, r) ∈ introPlans v N t) ↔ IR v N t r`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## splits, with indices -/

theorem mem_splits_iff {y d1 d2 : List ℕ} : (d1, d2) ∈ splits y ↔
    (∃ f, f < y.length ∧ d1 = y.take (f + 1) ∧ d2 = y.drop f) ∨
    (∃ f, f + 1 < y.length ∧ d1 = y.take (f + 1) ∧ d2 = y.drop (f + 1)) := by
  rw [mem_splits]
  constructor
  · rintro (⟨f, h1, h2, rfl, rfl⟩ | ⟨f, h1, h2, rfl, rfl⟩)
    · left; exact ⟨f - 1, by omega, by congr 1; omega, by congr 1⟩
    · right; exact ⟨f - 1, by omega, by congr 1; omega, by congr 1; omega⟩
  · rintro (⟨f, h1, rfl, rfl⟩ | ⟨f, h1, rfl, rfl⟩)
    · left; exact ⟨f + 1, by omega, by omega, rfl, by congr 1⟩
    · right; exact ⟨f + 1, by omega, by omega, rfl, rfl⟩

/-- Splits of a dropped sequence, in terms of the indices of the whole sequence. -/
theorem mem_splits_drop {y d1 d2 : List ℕ} {lo : ℕ} : (d1, d2) ∈ splits (y.drop lo) ↔
    (∃ f, lo ≤ f ∧ f < y.length ∧ d1 = (y.take (f + 1)).drop lo ∧ d2 = y.drop f) ∨
    (∃ f, lo ≤ f ∧ f + 1 < y.length ∧ d1 = (y.take (f + 1)).drop lo ∧ d2 = y.drop (f + 1)) := by
  rw [mem_splits_iff]
  simp only [List.length_drop]
  constructor
  · rintro (⟨f, h1, rfl, rfl⟩ | ⟨f, h1, rfl, rfl⟩)
    · left
      have e : lo + f + 1 - lo = f + 1 := by omega
      refine ⟨lo + f, by omega, by omega, ?_, ?_⟩
      · rw [List.drop_take, e]
      · rw [List.drop_drop]
    · right
      have e : lo + f + 1 + 1 - lo = f + 1 + 1 := by omega
      have e' : lo + f + 1 - lo = f + 1 := by omega
      refine ⟨lo + f, by omega, by omega, ?_, ?_⟩
      · rw [List.drop_take, e']
      · rw [List.drop_drop]; congr 1
  · rintro (⟨f, hlo, h1, rfl, rfl⟩ | ⟨f, hlo, h1, rfl, rfl⟩)
    · left
      have e : f + 1 - lo = f - lo + 1 := by omega
      refine ⟨f - lo, by omega, ?_, ?_⟩
      · rw [List.drop_take, e]
      · rw [List.drop_drop]; congr 1; omega
    · right
      have e : f + 1 - lo = f - lo + 1 := by omega
      refine ⟨f - lo, by omega, ?_, ?_⟩
      · rw [List.drop_take, e]
      · rw [List.drop_drop]; congr 1; omega

/-! ## the descriptions -/

mutual
/-- `W` contains the first tree node of the run `t`: the results `(r, c)` of `winPlans v 0 t`. -/
def WinR (v : ℕ) : CT → CT → Finset ℕ → Prop
  | node S y ks, r, c =>
    (∃ d1 d2, (d1, d2) ∈ splits y ∧ r = node (insert v S) (plus1 d1) [node S d2 ks] ∧ c = S) ∨
    (∃ kids cv, KidR v ks kids cv ∧ r = node (insert v S) (plus1 y) kids ∧ c = S ∪ cv)
/-- Per kid: leave it (covering nothing) or let `W` continue into it. -/
def KidR (v : ℕ) : List CT → List CT → Finset ℕ → Prop
  | [], kids, c => kids = [] ∧ c = ∅
  | k :: ks, kids, c => ∃ k' kids' c1 c2, kids = k' :: kids' ∧ c = c1 ∪ c2 ∧
      ((k' = k ∧ c1 = ∅) ∨ WinR v k k' c1) ∧ KidR v ks kids' c2
end

/-- `W`'s topmost node lies inside the run (`wtopPlans`). -/
def WtopR (v : ℕ) : CT → CT → Finset ℕ → Prop
  | node S y ks, r, c => WinR v (node S y ks) r c ∨
      ∃ d1 d2 X, (d1, d2) ∈ splits y ∧ WinR v (node S d2 ks) X c ∧ r = node S d1 [X]

/-- A new branch hangs at a node of the run (`attachPlans`). -/
def AttR (v : ℕ) (N : Finset ℕ) : CT → CT → Prop
  | node S y ks, r => ∃ chain M, (chain, M) ∈ allChains S N ∧
      (r = node S y (ks ++ [pathSubtree v chain M]) ∨
       ∃ d1 d2, (d1, d2) ∈ splits y ∧ r = node S d1 [pathSubtree v chain M, node S d2 ks])

/-- The results of `introPlans v N t`. -/
inductive IR (v : ℕ) (N : Finset ℕ) : CT → CT → Prop
  | top {S : Finset ℕ} {y : List ℕ} {ks : List CT} {r : CT} {c : Finset ℕ} :
      WtopR v (node S y ks) r c → N ⊆ c → IR v N (node S y ks) r
  | att {S : Finset ℕ} {y : List ℕ} {ks : List CT} {r : CT} :
      N ⊆ S → AttR v N (node S y ks) r → IR v N (node S y ks) r
  | kid {S : Finset ℕ} {y : List ℕ} {pre : List CT} {k : CT} {post : List CT} {r' : CT} :
      IR v N k r' → IR v N (node S y (pre ++ k :: post)) (node S y (pre ++ r' :: post))

/-! ## `winPlans` and `kidChoices` -/

theorem foldl_union_cov (S : Finset ℕ) (l : List (Option WPlan × CT × Finset ℕ)) :
    l.foldl (fun a c => a ∪ c.2.2) S = S ∪ l.foldl (fun a c => a ∪ c.2.2) ∅ := by
  induction l generalizing S with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons]
    rw [ih (S ∪ c.2.2), ih (∅ ∪ c.2.2)]
    simp [Finset.union_assoc]

mutual
theorem winPlans_mem (v : ℕ) (lo : ℕ) : ∀ (t : CT) (r : CT) (c : Finset ℕ),
    (∃ w, (w, r, c) ∈ winPlans v lo t) ↔ WinR v (node t.S (t.y.drop lo) t.kids) r c
  | node S y ks, r, c => by
    simp only [CT.S, CT.y, CT.kids, winPlans, List.mem_append, List.mem_map, WinR]
    constructor
    · rintro ⟨w, ((⟨f, hf, h⟩ | ⟨f, hf, h⟩) | ⟨combo, hcombo, h⟩)⟩
      · left
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        rw [List.mem_range'_1] at hf
        refine ⟨_, _, ?_, rfl, rfl⟩
        rw [mem_splits_drop]; left; exact ⟨f, hf.1, by omega, rfl, rfl⟩
      · left
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        rw [List.mem_range'_1] at hf
        refine ⟨_, _, ?_, rfl, rfl⟩
        rw [mem_splits_drop]; right; exact ⟨f, hf.1, by omega, rfl, rfl⟩
      · right
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨combo.map (·.2.1), combo.foldl (fun a c => a ∪ c.2.2) ∅,
          (kidChoices_mem v ks _ _).1 ⟨combo, hcombo, rfl, rfl⟩, rfl, foldl_union_cov _ _⟩
    · rintro (⟨d1, d2, hd, rfl, rfl⟩ | ⟨kids, cv, hk, rfl, rfl⟩)
      · rw [mem_splits_drop] at hd
        rcases hd with ⟨f, hlo, hf, rfl, rfl⟩ | ⟨f, hlo, hf, rfl, rfl⟩
        · exact ⟨_, Or.inl (Or.inl ⟨f, List.mem_range'_1.2 ⟨hlo, by omega⟩, rfl⟩)⟩
        · exact ⟨_, Or.inl (Or.inr ⟨f, List.mem_range'_1.2 ⟨hlo, by omega⟩, rfl⟩)⟩
      · obtain ⟨combo, hcombo, rfl, rfl⟩ := (kidChoices_mem v ks kids cv).2 hk
        exact ⟨_, Or.inr ⟨combo, hcombo, by rw [foldl_union_cov]⟩⟩
theorem kidChoices_mem (v : ℕ) : ∀ (ks : List CT) (kids : List CT) (cv : Finset ℕ),
    (∃ combo ∈ kidChoices v ks, combo.map (·.2.1) = kids ∧ combo.foldl (fun a c => a ∪ c.2.2) ∅ = cv) ↔
      KidR v ks kids cv
  | [], kids, cv => by
    simp only [kidChoices, List.mem_singleton, KidR]
    constructor
    · rintro ⟨combo, rfl, rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; exact ⟨[], rfl, rfl, rfl⟩
  | k :: ks, kids, cv => by
    simp only [kidChoices, List.mem_flatMap, List.mem_map, KidR]
    constructor
    · rintro ⟨combo, ⟨o, ho, combo', hcombo', rfl⟩, rfl, rfl⟩
      have hrec := (kidChoices_mem v ks (combo'.map (·.2.1)) (combo'.foldl (fun a c => a ∪ c.2.2) ∅)).1
        ⟨combo', hcombo', rfl, rfl⟩
      refine ⟨o.2.1, combo'.map (·.2.1), o.2.2, combo'.foldl (fun a c => a ∪ c.2.2) ∅, rfl, ?_, ?_, hrec⟩
      · simp only [List.foldl_cons]
        rw [foldl_union_cov]; simp
      · rcases List.mem_cons.1 ho with rfl | ho2
        · left; exact ⟨rfl, rfl⟩
        · right
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho2
          have := (winPlans_mem v 0 k p.2.1 p.2.2).1 ⟨p.1, hp⟩
          cases k with
          | node Sk yk kk => exact this
    · rintro ⟨k', kids', c1, c2, rfl, rfl, hk, hrec⟩
      obtain ⟨combo', hcombo', rfl, rfl⟩ := (kidChoices_mem v ks kids' c2).2 hrec
      rcases hk with ⟨hk1, rfl⟩ | hw
      · subst hk1
        refine ⟨(none, k', ∅) :: combo', ⟨(none, k', ∅), by simp, combo', hcombo', rfl⟩, rfl, ?_⟩
        simp only [List.foldl_cons]
        rw [foldl_union_cov]; simp
      · obtain ⟨w, hw'⟩ := (winPlans_mem v 0 k k' c1).2 (by cases k with | node Sk yk kk => exact hw)
        refine ⟨(some w, k', c1) :: combo', ⟨(some w, k', c1), ?_, combo', hcombo', rfl⟩, rfl, ?_⟩
        · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨(w, k', c1), hw', rfl⟩)
        · simp only [List.foldl_cons]
          rw [foldl_union_cov]; simp
end

/-! ## `wtopPlans` and `attachPlans` -/

theorem winPlans_mem0 (v : ℕ) (k : CT) (r : CT) (c : Finset ℕ) :
    (∃ w, (w, r, c) ∈ winPlans v 0 k) ↔ WinR v k r c := by
  rw [winPlans_mem]
  cases k with
  | node Sk yk kk => exact Iff.rfl

theorem wtopPlans_mem (v : ℕ) (t : CT) (r : CT) (c : Finset ℕ) :
    (∃ p, (p, r, c) ∈ wtopPlans v t) ↔ WtopR v t r c := by
  cases t with
  | node S y ks =>
    simp only [wtopPlans, WtopR, List.mem_append, List.mem_map, List.mem_flatMap]
    constructor
    · rintro ⟨pl, ((⟨⟨w, r0, c0⟩, hp, h⟩ | ⟨f, hf, ⟨w, r0, c0⟩, hp, h⟩) | ⟨f, hf, ⟨w, r0, c0⟩, hp, h⟩)⟩
      · left
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact (winPlans_mem0 v (node S y ks) r0 c0).1 ⟨w, hp⟩
      · right
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        refine ⟨_, _, r0, ?_, (winPlans_mem v f (node S y ks) r0 c0).1 ⟨w, hp⟩, rfl⟩
        rw [mem_splits_iff]; left; exact ⟨f, List.mem_range.1 hf, rfl, rfl⟩
      · right
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        refine ⟨_, _, r0, ?_, (winPlans_mem v (f + 1) (node S y ks) r0 c0).1 ⟨w, hp⟩, rfl⟩
        have := List.mem_range.1 hf
        rw [mem_splits_iff]; right; exact ⟨f, by omega, rfl, rfl⟩
    · rintro (hw | ⟨d1, d2, X, hd, hw, rfl⟩)
      · obtain ⟨w, hp⟩ := (winPlans_mem0 v (node S y ks) r c).2 hw
        exact ⟨_, Or.inl (Or.inl ⟨(w, r, c), hp, rfl⟩)⟩
      · rw [mem_splits_iff] at hd
        rcases hd with ⟨f, hf, rfl, rfl⟩ | ⟨f, hf, rfl, rfl⟩
        · obtain ⟨w, hp⟩ := (winPlans_mem v f (node S y ks) X c).2 hw
          exact ⟨_, Or.inl (Or.inr ⟨f, List.mem_range.2 hf, (w, X, c), hp, rfl⟩)⟩
        · obtain ⟨w, hp⟩ := (winPlans_mem v (f + 1) (node S y ks) X c).2 hw
          exact ⟨_, Or.inr ⟨f, List.mem_range.2 (by omega), (w, X, c), hp, rfl⟩⟩

theorem attachPlans_mem (v : ℕ) (N : Finset ℕ) (t : CT) (r : CT) :
    (∃ p, (p, r) ∈ attachPlans v N t) ↔ AttR v N t r := by
  cases t with
  | node S y ks =>
    simp only [attachPlans, AttR, List.mem_flatMap, List.mem_cons, List.mem_append, List.mem_map]
    constructor
    · rintro ⟨pl, ⟨chain, M⟩, hcm, ((h | ⟨f, hf, h⟩) | ⟨f, hf, h⟩)⟩
      · refine ⟨chain, M, hcm, Or.inl ?_⟩
        simp only [Prod.mk.injEq] at h
        exact h.2
      · refine ⟨chain, M, hcm, Or.inr ⟨y.take (f + 1), y.drop f, ?_, ?_⟩⟩
        · rw [mem_splits_iff]; left; exact ⟨f, List.mem_range.1 hf, rfl, rfl⟩
        · simp only [Prod.mk.injEq] at h
          exact h.2.symm
      · refine ⟨chain, M, hcm, Or.inr ⟨y.take (f + 1), y.drop (f + 1), ?_, ?_⟩⟩
        · have := List.mem_range.1 hf
          rw [mem_splits_iff]; right; exact ⟨f, by omega, rfl, rfl⟩
        · simp only [Prod.mk.injEq] at h
          exact h.2.symm
    · rintro ⟨chain, M, hcm, (rfl | ⟨d1, d2, hd, rfl⟩)⟩
      · exact ⟨_, (chain, M), hcm, Or.inl (Or.inl rfl)⟩
      · rw [mem_splits_iff] at hd
        rcases hd with ⟨f, hf, rfl, rfl⟩ | ⟨f, hf, rfl, rfl⟩
        · exact ⟨_, (chain, M), hcm, Or.inl (Or.inr ⟨f, List.mem_range.2 hf, rfl⟩)⟩
        · exact ⟨_, (chain, M), hcm, Or.inr ⟨f, List.mem_range.2 (by omega), rfl⟩⟩

/-! ## `introPlans` -/

theorem IR_to_introKids (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) (y : List ℕ) (k : CT) (r' : CT)
    (hk : ∃ path plan, (path, plan, r') ∈ introPlans v N k) :
    ∀ (pre0 pre post : List CT),
      ∃ path plan, (path, plan, node S y (pre0 ++ pre ++ r' :: post)) ∈ introKids v N S y pre0 (pre ++ k :: post) := by
  intro pre0 pre
  induction pre generalizing pre0 with
  | nil =>
    intro post
    obtain ⟨path, plan, hp⟩ := hk
    refine ⟨pre0.length :: path, plan, ?_⟩
    simp only [introKids, List.mem_append, List.mem_map, List.nil_append, List.append_nil]
    left
    exact ⟨(path, plan, r'), hp, rfl⟩
  | cons k0 pre ih =>
    intro post
    obtain ⟨path, plan, hp⟩ := ih (pre0 ++ [k0]) post
    refine ⟨path, plan, ?_⟩
    simp only [introKids, List.cons_append, List.mem_append]
    right
    simpa [List.append_assoc] using hp

mutual
theorem introPlans_toIR (v : ℕ) (N : Finset ℕ) : ∀ (t : CT) (r : CT),
    (∃ path plan, (path, plan, r) ∈ introPlans v N t) → IR v N t r
  | node S y ks, r, h => by
    obtain ⟨pa, pl, h⟩ := h
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    rcases h with (⟨⟨p, r0, c0⟩, ⟨hp, hN⟩, h⟩ | h) | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact IR.top ((wtopPlans_mem v (node S y ks) r0 c0).1 ⟨p, hp⟩) hN
    · split_ifs at h with hNS
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨p, r0⟩, hp, -, -, rfl⟩ := h
        exact IR.att hNS ((attachPlans_mem v N (node S y ks) r0).1 ⟨p, hp⟩)
      · simp at h
    · obtain ⟨pre2, k, post, r', rfl, hk, rfl⟩ := introKids_toIR v N S y ks [] r ⟨pa, pl, h⟩
      simpa using IR.kid (pre := pre2) (post := post) hk
theorem introKids_toIR (v : ℕ) (N : Finset ℕ) (S : Finset ℕ) (y : List ℕ) :
    ∀ (ks pre : List CT) (r : CT), (∃ path plan, (path, plan, r) ∈ introKids v N S y pre ks) →
      ∃ pre2 k post r', ks = pre2 ++ k :: post ∧ IR v N k r' ∧ r = node S y (pre ++ pre2 ++ r' :: post)
  | [], pre, r, h => by obtain ⟨pa, pl, h⟩ := h; simp [introKids] at h
  | k :: post, pre, r, h => by
    obtain ⟨pa, pl, h⟩ := h
    simp only [introKids, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨path, plan, r'⟩, hp, h⟩ | h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact ⟨[], k, post, r', rfl, introPlans_toIR v N k r' ⟨path, plan, hp⟩, by simp⟩
    · obtain ⟨pre2, k2, post2, r2, rfl, hk, rfl⟩ := introKids_toIR v N S y post (pre ++ [k]) r ⟨pa, pl, h⟩
      exact ⟨k :: pre2, k2, post2, r2, by simp, hk, by simp⟩
end

theorem IR_toPlans (v : ℕ) (N : Finset ℕ) {t r : CT} (h : IR v N t r) :
    ∃ path plan, (path, plan, r) ∈ introPlans v N t := by
  induction h with
  | @top S y ks r c hw hN =>
    obtain ⟨p, hp⟩ := (wtopPlans_mem v (node S y ks) r c).2 hw
    refine ⟨[], p, ?_⟩
    simp only [introPlans, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact Or.inl (Or.inl ⟨(p, r, c), ⟨hp, hN⟩, rfl⟩)
  | @att S y ks r hNS ha =>
    obtain ⟨p, hp⟩ := (attachPlans_mem v N (node S y ks) r).2 ha
    refine ⟨[], p, ?_⟩
    simp only [introPlans, List.mem_append, if_pos hNS]
    exact Or.inl (Or.inr (List.mem_map.2 ⟨(p, r), hp, rfl⟩))
  | @kid S y pre k post r' hk ih =>
    obtain ⟨path, plan, hp⟩ := IR_to_introKids v N S y k r' ih [] pre post
    refine ⟨path, plan, ?_⟩
    simp only [introPlans, List.mem_append]
    right
    simpa using hp

end Lax117284Proofs.Treewidth.Chars
