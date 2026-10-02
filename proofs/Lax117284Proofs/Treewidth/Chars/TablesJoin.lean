import Lax117284Proofs.Treewidth.Chars.NormGood
import Lax117284Proofs.Treewidth.Chars.NormMono
import Lax117284Proofs.Treewidth.Seq.RingTyp
import Lax117284Proofs.Treewidth.Seq.Symmetry
import Lax117284Proofs.Treewidth.Chars.Lattice

/-!
# `joinC` preserves well-formedness (work package C6a, part 1)

`joinC_wf : Wf B kmax a → Wf B kmax b → c ∈ joinC kmax a b → Wf B kmax c`.

The shape of a join option is the shape of `a` (labels, vertex sets, leaf-ness are unchanged; only the run sequences
change), so `Good`/`Conn` transport along the relation `JR`; the run sequences are `τ` of ring sums minus `|S|`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

/-! ## ring sums -/

theorem pathSums_prop : ∀ (n : ℕ) (a b c : List ℕ), a.length + b.length = n → c ∈ pathSums a b →
    c ≠ [] ∧ ∀ e ∈ c, ∃ x ∈ a, ∃ y ∈ b, e = x + y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn hc
    cases a with
    | nil => simp at hc
    | cons x a =>
      cases b with
      | nil => simp at hc
      | cons y b =>
        simp only [List.length_cons] at hn
        rcases mem_pathSums_cons_cons.mp hc with ⟨rfl, rfl, rfl⟩ | ⟨p, hp, rfl⟩
        · refine ⟨by simp, ?_⟩
          intro e he
          simp at he; subst he
          exact ⟨x, by simp, y, by simp, rfl⟩
        · refine ⟨by simp, ?_⟩
          intro e he
          rw [List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨x, by simp, y, by simp, rfl⟩
          · rcases hp with hp | hp | hp
            · obtain ⟨-, h⟩ := ih (a.length + (y :: b).length) (by simp only [List.length_cons]; omega) a (y :: b) p rfl hp
              obtain ⟨x', hx', y', hy', rfl⟩ := h e he
              exact ⟨x', by simp [hx'], y', hy', rfl⟩
            · obtain ⟨-, h⟩ := ih ((x :: a).length + b.length) (by simp only [List.length_cons]; omega) (x :: a) b p rfl hp
              obtain ⟨x', hx', y', hy', rfl⟩ := h e he
              exact ⟨x', hx', y', by simp [hy'], rfl⟩
            · obtain ⟨-, h⟩ := ih (a.length + b.length) (by omega) a b p rfl hp
              obtain ⟨x', hx', y', hy', rfl⟩ := h e he
              exact ⟨x', by simp [hx'], y', by simp [hy'], rfl⟩

theorem pathSums_single {x y : ℕ} {c : List ℕ} (h : c ∈ pathSums [x] [y]) : c = [x + y] := by
  rcases mem_pathSums_cons_cons.mp h with ⟨-, -, rfl⟩ | ⟨p, hp, rfl⟩
  · rfl
  · simp at hp

/-- The typical ring sums: non-empty, typical, entries are sums; singletons give a singleton. -/
theorem ringTyp_prop {a b d : List ℕ} (hd : d ∈ ringTyp a b) :
    d ≠ [] ∧ typical d = d ∧ (∀ e ∈ d, ∃ x ∈ a, ∃ y ∈ b, e = x + y) ∧
      (∀ x y, a = [x] → b = [y] → d = [x + y]) := by
  unfold ringTyp at hd
  rw [Finset.mem_image] at hd
  obtain ⟨p, hp, rfl⟩ := hd
  obtain ⟨hne, hsum⟩ := pathSums_prop _ a b p rfl hp
  refine ⟨typical_ne_nil hne, typical_typical p, ?_, ?_⟩
  · intro e he; exact hsum e (mem_of_mem_typical he)
  · rintro x y rfl rfl
    rw [pathSums_single hp, typical_singleton]

/-! ## the shape relation -/

/-- `c` has the shape of `k`: same label, same vertices, leaf iff leaf. -/
def JR (k c : CT) : Prop := c.S = k.S ∧ verts c = verts k ∧ (c.kids = [] ↔ k.kids = [])

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, by simp, h⟩
    · obtain ⟨a, ha, hr⟩ := forall₂_mem_right t b hb
      exact ⟨a, by simp [ha], hr⟩

theorem forall₂_pairwise {α β : Type} {R : α → β → Prop} {P : α → α → Prop} {P' : β → β → Prop}
    (hR : ∀ a b a' b', R a a' → R b b' → P a b → P' a' b') :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.Pairwise P → l'.Pairwise P'
  | _, _, .nil, _ => List.Pairwise.nil
  | _, _, .cons (a := a) (b := a') h t, hp => by
    rw [List.pairwise_cons] at hp ⊢
    refine ⟨fun y' hy' => ?_, forall₂_pairwise hR t hp.2⟩
    obtain ⟨y, hy, hry⟩ := forall₂_mem_right t y' hy'
    exact hR _ _ _ _ h hry (hp.1 y hy)

theorem key_of_JR (S : Finset ℕ) {k c : CT} (h : JR k c) : key S c = key S k := by
  unfold key; rw [h.2.1]

theorem kidsConn_transport {S : Finset ℕ} {ks kk : List CT} (hF : List.Forall₂ JR ks kk) (hc : ConnL kk)
    (h : KidsConn S ks) : KidsConn S kk := by
  refine ⟨hc, ?_, ?_⟩
  · intro c hcm u hu huc
    obtain ⟨k, hk, hr⟩ := forall₂_mem_right hF c hcm
    rw [hr.2.1] at huc
    rw [hr.1]
    exact h.2.1 k hk u hu huc
  · refine forall₂_pairwise ?_ hF h.2.2
    intro a b a' b' ha hb hab u hu1 hu2
    rw [ha.2.1] at hu1; rw [hb.2.1] at hu2
    exact hab u hu1 hu2

theorem vertsL_of_forall₂ {ks kk : List CT} (hF : List.Forall₂ JR ks kk) : vertsL kk = vertsL ks := by
  induction hF with
  | nil => rfl
  | cons h _ ih => rw [vertsL, vertsL, h.2.1, ih]

/-! ## the main induction -/

mutual
theorem joinC_aux (B : Finset ℕ) (kmax : ℕ) : ∀ (a b c : CT), Good B a → Good B b → c ∈ joinC kmax a b →
    Good B c ∧ JR a c ∧ maxEntry c ≤ kmax ∧ (Conn a → Conn c)
  | node S y ks, node S' y' ks', c, ha, hb, hc => by
    rw [joinC] at hc
    split_ifs at hc with hcond
    · obtain ⟨rfl, hlen⟩ := hcond
      rw [List.mem_flatMap] at hc
      obtain ⟨kk, hkk, hc⟩ := hc
      rw [List.mem_map] at hc
      obtain ⟨d, hd, rfl⟩ := hc
      rw [List.mem_filter, List.mem_dedup, List.mem_map] at hd
      obtain ⟨⟨d0, hd0, rfl⟩, hdk⟩ := hd
      rw [mem_ringTypList] at hd0
      obtain ⟨hGa1, hGa2, hGa3, hGa4, hGa5, hGa6, hGa7, hGa8, hGa9⟩ := ha
      obtain ⟨hGb1, hGb2, hGb3, hGb4, hGb5, hGb6, hGb7, hGb8, hGb9⟩ := hb
      obtain ⟨hne0, hty0, hsum0, hsing⟩ := ringTyp_prop hd0
      obtain ⟨hGK, hF, hbK, hCK⟩ := joinKids_aux B kmax ks ks' kk hGa9 hGb9 hkk
      have hge : ∀ e ∈ d0, 2 * S.card ≤ e := by
        intro e he
        obtain ⟨x, hx, z, hz, rfl⟩ := hsum0 e he
        have := hGa4 x hx; have := hGb4 z hz; omega
      have hlenkk : kk.length = ks.length := (hF.length_eq).symm
      refine ⟨⟨hGa1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hGK⟩, ⟨rfl, ?_, ?_⟩, ?_, ?_⟩
      · rw [typical_map_sub d0 S.card (fun e he => by have := hge e he; omega), hty0]
      · simpa using hne0
      · intro e he
        rw [List.mem_map] at he
        obtain ⟨z, hz, rfl⟩ := he
        have := hge z hz; omega
      · intro hkk0
        have hks0 : ks = [] := List.length_eq_zero_iff.1 (by rw [← hlenkk, hkk0]; rfl)
        have hks0' : ks' = [] := List.length_eq_zero_iff.1 (by rw [← hlen, hks0]; rfl)
        have h1 := hGa5 hks0
        have h2 := hGb5 hks0'
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 h1
        obtain ⟨z, rfl⟩ := List.length_eq_one_iff.1 h2
        rw [hsing x z rfl rfl]
        simp
      · intro k hk hkl
        obtain ⟨k0, hk0, hr⟩ := forall₂_mem_right hF k hk
        rw [hr.1]
        exact hGa6 k0 hk0 (hr.2.2.1 hkl)
      · intro k hkk
        obtain ⟨k0, l, hr, hl, rfl⟩ := List.forall₂_cons_right_iff.1 (hkk ▸ hF)
        rw [hr.1]
        exact hGa7 k0 (by rw [List.forall₂_nil_right_iff.1 hl])
      · exact forall₂_pairwise (P := fun a b => key S a < key S b) (fun a b a' b' ha hb h => by
          rw [key_of_JR S ha, key_of_JR S hb]; exact h) hF hGa8
      · rw [verts, verts, vertsL_of_forall₂ hF]
      · show kk = [] ↔ ks = []
        rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlenkk]
      · rw [maxEntry_le_iff]
        refine ⟨?_, hbK⟩
        intro e he
        rw [List.mem_map] at he
        obtain ⟨z, hz, rfl⟩ := he
        have := List.all_eq_true.1 hdk (z - S.card) (List.mem_map.2 ⟨z, hz, rfl⟩)
        simpa using this
      · intro hcn
        exact kidsConn_transport hF (hCK hcn.1) hcn
    · simp at hc
theorem joinKids_aux (B : Finset ℕ) (kmax : ℕ) : ∀ (ks ks' kk : List CT), GoodL B ks → GoodL B ks' →
    kk ∈ joinKids kmax ks ks' →
    GoodL B kk ∧ List.Forall₂ JR ks kk ∧ (∀ k ∈ kk, maxEntry k ≤ kmax) ∧ (ConnL ks → ConnL kk)
  | [], [], kk, _, _, h => by
    simp only [joinKids, List.mem_singleton] at h
    subst h
    exact ⟨trivial, List.Forall₂.nil, by simp, fun _ => trivial⟩
  | [], _ :: _, kk, _, _, h => by simp [joinKids] at h
  | _ :: _, [], kk, _, _, h => by simp [joinKids] at h
  | k :: ks, k' :: ks', kk, ha, hb, h => by
    simp only [joinKids, List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, l, hl, rfl⟩ := h
    obtain ⟨hg1, hj1, hm1, hcn1⟩ := joinC_aux B kmax k k' c ha.1 hb.1 hc
    obtain ⟨hg2, hj2, hm2, hcn2⟩ := joinKids_aux B kmax ks ks' l ha.2 hb.2 hl
    refine ⟨⟨hg1, hg2⟩, List.Forall₂.cons hj1 hj2, ?_, fun hcn => ⟨hcn1 hcn.1, hcn2 hcn.2⟩⟩
    intro k'' hk''
    rcases List.mem_cons.1 hk'' with rfl | hk''
    · exact hm1
    · exact hm2 _ hk''
end

/-- **`joinC` preserves well-formedness.** -/
theorem joinC_wf {B : Finset ℕ} {kmax : ℕ} {a b c : CT} (ha : Wf B kmax a) (hb : Wf B kmax b)
    (hc : c ∈ joinC kmax a b) : Wf B kmax c := by
  obtain ⟨g, j, m, cn⟩ := joinC_aux B kmax a b c ha.good hb.good hc
  exact ⟨j.2.1.trans ha.verts_eq, g, cn ha.conn, m⟩

end CT

end Lax117284Proofs.Treewidth.Chars
