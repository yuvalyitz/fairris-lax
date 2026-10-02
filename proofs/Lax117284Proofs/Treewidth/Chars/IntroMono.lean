import Lax117284Proofs.Treewidth.Chars.IntroPlansMem
import Lax117284Proofs.Treewidth.Chars.NormMono
import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.JoinSeq

/-!
# `introC_mono` (work package C4, part 4)

The options of the introduction are monotone for `DomC`: `IR_mono` says that for `DomC t t'` every option `r'` of
`t'` is `DomC`-dominated by an option `r` of `t` (raw results, before `norm`); `introC_mono` follows by `norm_mono`.

The engine is the split transport of `Seq/Transport.lean`: a cut of the (longer, larger) sequence `y'` is an `IsSplit`
of it, `split_up_of_dom` produces a split of `y` whose parts dominate the two parts.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem dom_plus1 {a b : List ℕ} (h : Dom a b) : Dom (plus1 a) (plus1 b) :=
  Dom.map_mono (fun x y h => Nat.add_le_add_right h 1) h

theorem domCL_append : ∀ {a b c d : List CT}, DomCL a b → DomCL c d → DomCL (a ++ c) (b ++ d)
  | [], [], c, d, _, h2 => h2
  | [], _ :: _, _, _, h1, _ => h1.elim
  | _ :: _, [], _, _, h1, _ => h1.elim
  | a :: as, b :: bs, c, d, h1, h2 => ⟨h1.1, domCL_append h1.2 h2⟩

theorem domCL_split {ks : List CT} : ∀ {pre : List CT} {k : CT} {post : List CT},
    DomCL ks (pre ++ k :: post) →
    ∃ pre0 k0 post0, ks = pre0 ++ k0 :: post0 ∧ DomCL pre0 pre ∧ DomC k0 k ∧ DomCL post0 post := by
  intro pre
  induction pre generalizing ks with
  | nil =>
    intro k post h
    cases ks with
    | nil => exact h.elim
    | cons k0 ks0 => exact ⟨[], k0, ks0, rfl, trivial, h.1, h.2⟩
  | cons p pre ih =>
    intro k post h
    cases ks with
    | nil => exact h.elim
    | cons k1 ks1 =>
      obtain ⟨pre0, k0, post0, rfl, h1, h2, h3⟩ := ih (ks := ks1) h.2
      exact ⟨k1 :: pre0, k0, post0, rfl, ⟨h.1, h1⟩, h2, h3⟩

mutual
theorem winR_mono_rec (v : ℕ) : ∀ (t t' : CT), DomC t t' → ∀ (r' : CT) (c : Finset ℕ), WinR v t' r' c →
    ∃ r, WinR v t r c ∧ DomC r r'
  | node S y ks, node S' y' ks', h, r', c, hw => by
    obtain ⟨rfl, hy, hk⟩ := h
    rcases hw with ⟨d1', d2', hd', rfl, rfl⟩ | ⟨kids', cv, hkid, rfl, rfl⟩
    · obtain ⟨d1, d2, hd, h1, h2⟩ := split_up_of_dom hy (isSplit_of_mem_splits hd')
      exact ⟨_, Or.inl ⟨d1, d2, hd, rfl, rfl⟩, rfl, dom_plus1 h1, ⟨⟨rfl, h2, hk⟩, trivial⟩⟩
    · obtain ⟨kids, hkid2, hk2⟩ := kidR_mono_rec v ks ks' hk kids' cv hkid
      exact ⟨_, Or.inr ⟨kids, cv, hkid2, rfl, rfl⟩, rfl, dom_plus1 hy, hk2⟩
theorem kidR_mono_rec (v : ℕ) : ∀ (ks ks' : List CT), DomCL ks ks' → ∀ (kids' : List CT) (c : Finset ℕ),
    KidR v ks' kids' c → ∃ kids, KidR v ks kids c ∧ DomCL kids kids'
  | [], [], _, kids', c, hk => by obtain ⟨rfl, rfl⟩ := hk; exact ⟨[], ⟨rfl, rfl⟩, trivial⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | k :: ks, k' :: ks', h, kids', c, hk => by
    obtain ⟨k'', kids'', c1, c2, rfl, rfl, hkk, hrec⟩ := hk
    obtain ⟨kidsR, hrec2, hd2⟩ := kidR_mono_rec v ks ks' h.2 kids'' c2 hrec
    rcases hkk with ⟨rfl, rfl⟩ | hw
    · exact ⟨k :: kidsR, ⟨k, kidsR, ∅, c2, rfl, rfl, Or.inl ⟨rfl, rfl⟩, hrec2⟩, h.1, hd2⟩
    · obtain ⟨r, hr, hd⟩ := winR_mono_rec v k k' h.1 k'' c1 hw
      exact ⟨r :: kidsR, ⟨r, kidsR, c1, c2, rfl, rfl, Or.inr hr, hrec2⟩, hd, hd2⟩
end

theorem winR_mono_pair : (type_of% @winR_mono_rec) ∧ (type_of% @kidR_mono_rec) :=
  ⟨@winR_mono_rec, @kidR_mono_rec⟩

theorem winR_mono : type_of% @winR_mono_rec := winR_mono_pair.1

theorem wtopR_mono (v : ℕ) {t t' : CT} (h : DomC t t') {r' : CT} {c : Finset ℕ} (hw : WtopR v t' r' c) :
    ∃ r, WtopR v t r c ∧ DomC r r' := by
  cases t with
  | node S y ks =>
    cases t' with
    | node S' y' ks' =>
      obtain ⟨rfl, hy, hk⟩ := h
      rcases hw with hw | ⟨d1', d2', X', hd', hX', rfl⟩
      · obtain ⟨r, hr, hd⟩ := winR_mono v (node S y ks) (node S y' ks') ⟨rfl, hy, hk⟩ r' c hw
        exact ⟨r, Or.inl hr, hd⟩
      · obtain ⟨d1, d2, hd, h1, h2⟩ := split_up_of_dom hy (isSplit_of_mem_splits hd')
        obtain ⟨X, hX, hXd⟩ := winR_mono v (node S d2 ks) (node S d2' ks') ⟨rfl, h2, hk⟩ X' c hX'
        exact ⟨node S d1 [X], Or.inr ⟨d1, d2, X, hd, hX, rfl⟩, ⟨rfl, h1, ⟨hXd, trivial⟩⟩⟩

theorem attR_mono (v : ℕ) (N : Finset ℕ) {t t' : CT} (h : DomC t t') {r' : CT} (ha : AttR v N t' r') :
    ∃ r, AttR v N t r ∧ DomC r r' := by
  cases t with
  | node S y ks =>
    cases t' with
    | node S' y' ks' =>
      obtain ⟨rfl, hy, hk⟩ := h
      obtain ⟨chain, M, hcm, hr⟩ := ha
      rcases hr with rfl | ⟨d1', d2', hd', rfl⟩
      · refine ⟨node S y (ks ++ [pathSubtree v chain M]), ⟨chain, M, hcm, Or.inl rfl⟩, rfl, hy, ?_⟩
        exact domCL_append hk ⟨DomC.refl _, trivial⟩
      · obtain ⟨d1, d2, hd, h1, h2⟩ := split_up_of_dom hy (isSplit_of_mem_splits hd')
        exact ⟨node S d1 [pathSubtree v chain M, node S d2 ks], ⟨chain, M, hcm, Or.inr ⟨d1, d2, hd, rfl⟩⟩,
          rfl, h1, ⟨DomC.refl _, ⟨rfl, h2, hk⟩, trivial⟩⟩

/-- **Monotonicity of the options** (raw results). -/
theorem IR_mono (v : ℕ) (N : Finset ℕ) {t' r' : CT} (h : IR v N t' r') :
    ∀ t : CT, DomC t t' → ∃ r, IR v N t r ∧ DomC r r' := by
  induction h with
  | @top S y ks r c hw hN =>
    intro t ht
    cases t with
    | node S0 y0 ks0 =>
      obtain ⟨rfl, -, -⟩ := id ht
      obtain ⟨r0, hr0, hd⟩ := wtopR_mono v ht hw
      exact ⟨r0, IR.top hr0 hN, hd⟩
  | @att S y ks r hNS ha =>
    intro t ht
    cases t with
    | node S0 y0 ks0 =>
      obtain ⟨rfl, -, -⟩ := id ht
      obtain ⟨r0, hr0, hd⟩ := attR_mono v N ht ha
      exact ⟨r0, IR.att hNS hr0, hd⟩
  | @kid S y pre k post r' hk ih =>
    intro t ht
    cases t with
    | node S0 y0 ks0 =>
      obtain ⟨rfl, hy, hks⟩ := ht
      obtain ⟨pre0, k0, post0, rfl, h1, h2, h3⟩ := domCL_split hks
      obtain ⟨r0, hr0, hd⟩ := ih k0 h2
      exact ⟨node S0 y0 (pre0 ++ r0 :: post0), IR.kid hr0, rfl, hy,
        domCL_append h1 ⟨hd, h3⟩⟩

/-- `Dom` is monotone for the maximal entry. -/
theorem foldr_max_dom_le {a b : List ℕ} (h : Dom a b) : a.foldr max 0 ≤ b.foldr max 0 := by
  rw [foldr_max_le_iff]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h.exists_le hx
  have : y ≤ b.foldr max 0 := (foldr_max_le_iff.1 le_rfl) y hy
  omega

mutual
theorem maxEntry_dom_le_rec : ∀ {a b : CT}, DomC a b → maxEntry a ≤ maxEntry b
  | node S y ks, node S' y' ks', h => by
    obtain ⟨rfl, hy, hk⟩ := h
    simp only [maxEntry]
    exact max_le_max (foldr_max_dom_le hy) (maxEntryL_domL_le_rec hk)
theorem maxEntryL_domL_le_rec : ∀ {a b : List CT}, DomCL a b → maxEntryL a ≤ maxEntryL b
  | [], [], _ => le_rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | k :: ks, k' :: ks', h => by
    simp only [maxEntryL]
    exact max_le_max (maxEntry_dom_le_rec h.1) (maxEntryL_domL_le_rec h.2)
end

theorem maxEntry_dom_le_pair : (type_of% @maxEntry_dom_le_rec) ∧ (type_of% @maxEntryL_domL_le_rec) :=
  ⟨@maxEntry_dom_le_rec, @maxEntryL_domL_le_rec⟩

theorem maxEntry_dom_le : type_of% @maxEntry_dom_le_rec := maxEntry_dom_le_pair.1

/-- Membership in `introC` in terms of the described results. -/
theorem mem_introC {kmax v : ℕ} {N : Finset ℕ} {t c : CT} :
    c ∈ introC kmax v N t ↔ ∃ r, IR v N t r ∧ norm r = c ∧ c.maxEntry ≤ kmax := by
  unfold introC
  rw [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨⟨path, plan, r⟩, hp, rfl⟩, hk⟩
    exact ⟨r, introPlans_toIR v N t r ⟨path, plan, hp⟩, rfl, by simpa using hk⟩
  · rintro ⟨r, hr, rfl, hk⟩
    obtain ⟨path, plan, hp⟩ := IR_toPlans v N hr
    exact ⟨⟨⟨path, plan, r⟩, hp, rfl⟩, by simpa using hk⟩

/-- **`introC` is monotone** (Split transport lifted along the plans of the introduction). -/
theorem introC_mono (kmax v : ℕ) (N : Finset ℕ) {a a' : CT} (h : DomC a a') :
    ∀ c' ∈ introC kmax v N a', ∃ c ∈ introC kmax v N a, DomC c c' := by
  intro c' hc'
  obtain ⟨r', hr', rfl, hk⟩ := mem_introC.1 hc'
  obtain ⟨r, hr, hd⟩ := IR_mono v N hr' a h
  have hd' := norm_mono hd
  exact ⟨norm r, mem_introC.2 ⟨r, hr, rfl, (maxEntry_dom_le hd').trans hk⟩, hd'⟩

end Lax117284Proofs.Treewidth.Chars
