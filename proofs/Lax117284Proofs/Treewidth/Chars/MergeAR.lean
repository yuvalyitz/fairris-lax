import Lax117284Proofs.Treewidth.Chars.AnalyzeRT
import Lax117284Proofs.Treewidth.Seq.RingRealise

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

theorem F3.length_eq {α β γ : Type} {P : α → β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ}, F3 P as bs cs → as.length = bs.length ∧ as.length = cs.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | a :: as, b :: bs, c :: cs, h => by
    have := F3.length_eq h.2
    simp only [List.length_cons]
    constructor <;> omega

theorem F4.length_eq {α β γ δ : Type} {P : α → β → γ → δ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds →
      as.length = bs.length ∧ as.length = cs.length ∧ as.length = ds.length
  | [], [], [], [], _ => ⟨rfl, rfl, rfl⟩
  | a :: as, b :: bs, c :: cs, d :: ds, h => by
    have := F4.length_eq h.2
    simp only [List.length_cons]
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem F3.mono {α β γ : Type} {P Q : α → β → γ → Prop} (as : List α) :
    ∀ {bs : List β} {cs : List γ}, (∀ a ∈ as, ∀ b c, P a b c → Q a b c) → F3 P as bs cs → F3 Q as bs cs := by
  induction as with
  | nil => intro bs cs _ h; cases bs <;> cases cs <;> simpa [F3] using h
  | cons a as ih =>
    intro bs cs hPQ h
    cases bs with
    | nil => exact absurd h (by simp [F3])
    | cons b bs =>
      cases cs with
      | nil => exact absurd h (by simp [F3])
      | cons c cs =>
        exact ⟨hPQ a (by simp) b c h.1, ih (fun a' ha' => hPQ a' (List.mem_cons_of_mem _ ha')) h.2⟩

theorem F4.mono {α β γ δ : Type} {P Q : α → β → γ → δ → Prop} (as : List α) :
    ∀ {bs : List β} {cs : List γ} {ds : List δ}, (∀ a ∈ as, ∀ b c d, P a b c d → Q a b c d) →
      F4 P as bs cs ds → F4 Q as bs cs ds := by
  induction as with
  | nil => intro bs cs ds _ h; cases bs <;> cases cs <;> cases ds <;> simpa [F4] using h
  | cons a as ih =>
    intro bs cs ds hPQ h
    cases bs with
    | nil => exact absurd h (by simp [F4])
    | cons b bs =>
      cases cs with
      | nil => exact absurd h (by simp [F4])
      | cons c cs =>
        cases ds with
        | nil => exact absurd h (by simp [F4])
        | cons d ds =>
          exact ⟨hPQ a (by simp) b c d h.1, ih (fun a' ha' => hPQ a' (List.mem_cons_of_mem _ ha')) h.2⟩

/-- Combine a `F3` and a `F4` relation over the same three lists. -/
theorem F4.and_F3 {α β γ δ : Type} {P : α → β → γ → δ → Prop} {Q : α → β → γ → Prop} :
    ∀ {as : List α} {bs : List β} {cs : List γ} {ds : List δ}, F4 P as bs cs ds → F3 Q as bs cs →
      F4 (fun a b c d => P a b c d ∧ Q a b c) as bs cs ds
  | [], [], [], [], _, _ => trivial
  | a :: as, b :: bs, c :: cs, d :: ds, h, h' => ⟨⟨h.1, h'.1⟩, F4.and_F3 h.2 h'.2⟩
  | [], [], [], _ :: _, h, _ => absurd h (by simp [F4])
  | [], [], _ :: _, _, h, _ => absurd h (by simp [F4])
  | [], _ :: _, _, _, h, _ => absurd h (by simp [F4])
  | _ :: _, [], _, _, h, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, [], _, h, _ => absurd h (by simp [F4])
  | _ :: _, _ :: _, _ :: _, [], h, _ => absurd h (by simp [F4])

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
