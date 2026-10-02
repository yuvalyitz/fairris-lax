import Lax117284Proofs.Treewidth.Chars.RealizeChain
import Lax117284Proofs.Treewidth.Chars.IntroSetup

/-!
# Normal-form algebra for the realisation of the introduce step (work package C5, part 3)

* `prof_insert_of_free` — a `v`-free tree has the same profile with respect to `B` and `insert v B`;
* `chainToRT_append` — a chain is the nesting of its two halves;
* `chain_norm` — the normal form of the profile of a chain of nodes with a common label is `normF` of that label, the
  typical sequence of the bag sizes and the normalised profiles of the kids (the junk is pruned);
* `keep_of_mem_verts`, `le_maxEntry_normF_*` — survival of a subtree containing a new vertex, and of its entries.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-! ## profiles of `v`-free trees -/

theorem prof_insert_of_free (v : ℕ) (B : Finset ℕ) : ∀ t : RT, (∀ X ∈ t.bags, v ∉ X) →
    RT.prof (insert v B) t = RT.prof B t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro h
    rw [RT.prof_node, RT.prof_node]
    have hX : v ∉ X := h X ((RT.bags_node X ks).2 (Or.inl rfl))
    have e : X ∩ insert v B = X ∩ B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, rfl | h2⟩
        · exact absurd h1 hX
        · exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
    rw [e]
    congr 1
    apply List.map_congr_left
    intro k hk
    exact ih k hk (fun Y hY => h Y ((RT.bags_node X ks).2 (Or.inr ⟨k, hk, hY⟩)))

/-! ## nesting of chains -/

theorem chainToRT_append (c1 c2 : List CNode) (K : List RT) (h1 : c1 ≠ []) (h2 : c2 ≠ []) :
    AR.chainToRT (c1 ++ c2) K = AR.chainToRT c1 [AR.chainToRT c2 K] := by
  induction c1 with
  | nil => exact absurd rfl h1
  | cons n r ih =>
    cases r with
    | nil =>
      obtain ⟨m, r2, rfl⟩ := List.exists_cons_of_ne_nil h2
      simp [AR.chainToRT]
    | cons m r' =>
      have := ih (by simp)
      simp only [List.cons_append] at this ⊢
      simp only [AR.chainToRT] at this ⊢
      rw [this]

/-! ## the profile of a chain -/

theorem chain_norm (B'' ℓ : Finset ℕ) : ∀ (c : List CNode) (K : List RT), c ≠ [] →
    (∀ n ∈ c, n.bag ∩ B'' = ℓ ∧ ∀ J ∈ n.junk, keep ℓ (norm (RT.prof B'' J)) = false) →
    norm (RT.prof B'' (AR.chainToRT c K)) =
      normF ℓ (typical (csz c)) (((K.map (RT.prof B'')).map norm).filter (keep ℓ)) := by
  intro c
  induction c with
  | nil => intro K h; exact absurd rfl h
  | cons n r ih =>
    intro K _ hc
    obtain ⟨hn1, hn2⟩ := hc n (by simp)
    have hjunk : (((n.junk.map (RT.prof B'')).map norm)).filter (keep ℓ) = [] := by
      rw [List.filter_eq_nil_iff]
      intro k hk
      obtain ⟨k1, hk1, rfl⟩ := List.mem_map.1 hk
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hk1
      simp [hn2 J hJ]
    cases r with
    | nil =>
      simp only [AR.chainToRT]
      rw [RT.prof_node, norm_node', hn1]
      simp only [List.map_append, List.filter_append, hjunk, List.nil_append]
      simp [csz, typical_singleton]
    | cons m r' =>
      simp only [AR.chainToRT]
      rw [RT.prof_node, norm_node', hn1]
      have hrest := ih K (by simp) (fun n' hn' => hc n' (List.mem_cons_of_mem _ hn'))
      simp only [List.map_append, List.filter_append, hjunk, List.nil_append, List.map_cons, List.map_nil]
      rw [hrest]
      have hF : ∀ k ∈ ((K.map (RT.prof B'')).map norm).filter (keep ℓ), keep ℓ k = true :=
        fun k hk => (List.mem_filter.1 hk).2
      have := normF_merge ℓ (s := [n.bag.card]) (y := typical (csz (m :: r')))
        (by simp) hF
      have e : typical ([n.bag.card] ++ typical (csz (m :: r'))) = typical (csz (n :: m :: r')) := by
        rw [← typical_append_typical_right]; simp [csz]
      rw [this, e]

/-! ## survival -/

theorem keep_of_mem_verts {σ : Finset ℕ} {p : CT} {v : ℕ} (hv : v ∈ verts p) (hσ : v ∉ σ) :
    keep σ (norm p) = true := by
  by_contra hcon
  have hf : keep σ (norm p) = false := by simpa using hcon
  have hn := (keep_norm_false_iff σ p).1 hf
  exact hσ (nested_root_sub hn (verts_nested σ p hn hv))

theorem le_maxEntry_y {q : CT} {e : ℕ} (h : e ∈ q.y) : e ≤ maxEntry q := by
  cases q with
  | node S y ks =>
    have := (maxEntry_le_iff (S := S) (y := y) (ks := ks) (n := maxEntry (node S y ks))).1 le_rfl
    exact this.1 e h

theorem maxOf_typical_le_maxEntry {q : CT} {z : List ℕ} (hz : q.y = typical z) : maxOf z ≤ maxEntry q := by
  rw [← maxOf_typical, ← hz]
  exact maxOf_le fun e he => le_maxEntry_y he

theorem le_maxEntry_normF_kid {S : Finset ℕ} {y : List ℕ} {F : List CT} {k : CT} (hk : k ∈ F) :
    maxEntry k ≤ maxEntry (normF S y F) := by
  match F, hk with
  | [], hk => simp at hk
  | [k0], hk =>
    have : k = k0 := by simpa using hk
    subst this
    rw [normF_single]
    split_ifs with hS
    · obtain ⟨Sk, yk, kk⟩ := k
      rw [maxEntry_le_iff]
      refine ⟨fun e he => ?_, fun k' hk' => ?_⟩
      · have h1 := maxOf_typical_le_maxEntry (q := node S (typical (y ++ yk)) kk) (z := y ++ yk) rfl
        exact (le_maxOf (List.mem_append_right _ he)).trans h1
      · exact maxEntry_kid_le (q := node S (typical (y ++ yk)) kk) hk'
    · exact maxEntry_kid_le (q := node S y [k]) (by simp [CT.kids])
  | a :: b :: t, hk =>
    rw [normF_ge2]
    exact maxEntry_kid_le (q := node S y (sortKids S (a :: b :: t))) (mem_sortKids.2 hk)

theorem le_maxEntry_normF_y {S : Finset ℕ} {y : List ℕ} {F : List CT} (hF : F ≠ [] ∨ y.length ≤ 1) {e : ℕ}
    (he : e ∈ y) : e ≤ maxEntry (normF S y F) := by
  match F, hF with
  | [], hF =>
    have hy : y.length ≤ 1 := by
      rcases hF with h | h
      · exact absurd rfl h
      · exact h
    rw [normF_nil]
    apply le_maxEntry_y
    simp only [CT.y]
    rw [List.take_of_length_le hy]; exact he
  | [k0], hF =>
    rw [normF_single]
    split_ifs with hS
    · have h1 := maxOf_typical_le_maxEntry (q := node S (typical (y ++ k0.y)) k0.kids) (z := y ++ k0.y) rfl
      exact (le_maxOf (List.mem_append_left _ he)).trans h1
    · exact le_maxEntry_y (q := node S y [k0]) he
  | a :: b :: t, hF =>
    rw [normF_ge2]
    exact le_maxEntry_y (q := node S y (sortKids S (a :: b :: t))) he

theorem norm_kid_le {σ : Finset ℕ} {y : List ℕ} {K : List CT} {k : CT} (hk : k ∈ K)
    (hkeep : keep σ (norm k) = true) : maxEntry (norm k) ≤ maxEntry (norm (node σ y K)) := by
  rw [norm_node']
  apply le_maxEntry_normF_kid
  exact List.mem_filter.2 ⟨List.mem_map.2 ⟨k, hk, rfl⟩, hkeep⟩

theorem norm_y_le {σ : Finset ℕ} {y : List ℕ} {K : List CT} (hF : (∃ k ∈ K, keep σ (norm k) = true) ∨ y.length ≤ 1)
    {e : ℕ} (he : e ∈ y) : e ≤ maxEntry (norm (node σ y K)) := by
  rw [norm_node']
  apply le_maxEntry_normF_y _ he
  rcases hF with ⟨k, hk, hkeep⟩ | h
  · left
    intro hnil
    have : norm k ∈ (K.map norm).filter (keep σ) := List.mem_filter.2 ⟨List.mem_map.2 ⟨k, hk, rfl⟩, hkeep⟩
    rw [hnil] at this; simp at this
  · right; exact h


/-! ## adding one to sequences -/

theorem ext_map_inj (f : ℕ → ℕ) (hf : Function.Injective f) : ∀ {a w : List ℕ}, Ext a w → Ext (a.map f) (w.map f) := by
  intro a w
  induction w generalizing a with
  | nil => intro h; rw [ext_nil_right] at h; subst h; simp
  | cons y w ih =>
    intro h
    cases a with
    | nil => exact absurd h (ext_nil_cons _ _)
    | cons x a =>
      obtain ⟨rfl, h | h⟩ := ext_cons_cons.mp h
      · simp only [List.map_cons]
        exact ext_cons_cons.mpr ⟨rfl, Or.inl (by simpa using ih h)⟩
      · simp only [List.map_cons]
        exact ext_cons_cons.mpr ⟨rfl, Or.inr (ih h)⟩

theorem leSeq_map_succ {a b : List ℕ} (h : LeSeq a b) : LeSeq (a.map (· + 1)) (b.map (· + 1)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons (by simp only []; omega) ih

theorem dom_map_succ {a b : List ℕ} (h : Dom a b) : Dom (a.map (· + 1)) (b.map (· + 1)) := by
  obtain ⟨a', b', ha, hb, hle⟩ := h
  exact ⟨a'.map (· + 1), b'.map (· + 1), ext_map_inj _ (fun x y h => by simpa using h) ha,
    ext_map_inj _ (fun x y h => by simpa using h) hb, leSeq_map_succ hle⟩

theorem typical_plus1 (a : List ℕ) : typical (a.map (· + 1)) = plus1 (typical a) := by
  unfold plus1; exact typical_map_add a 1

end Lax117284Proofs.Treewidth.Chars
