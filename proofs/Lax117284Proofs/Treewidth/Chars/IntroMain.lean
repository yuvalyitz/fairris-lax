import Lax117284Proofs.Treewidth.Chars.IntroMainI
import Lax117284Proofs.Treewidth.Chars.Forget
import Lax117284Proofs.Treewidth.Chars.JoinShape
import Lax117284Proofs.Treewidth.Chars.Join
import Lax117284Proofs.Treewidth.Trees.Bridge1Restrict

/-!
# `char_intro_dom` (work package C4, part 12)

`main_intro` — the FT-level statement (one induction on the flagged profile tree); `mkFT` — the flagged profile tree of
a real decomposition; `char_intro_dom` — the assembly.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT FT

/-- **The introduction on flagged profile trees.** -/
theorem main_intro (v : ℕ) : ∀ P : FT, FOk v P → Conn (fT v P) →
    (P.w = true → ∃ r c, WinR v (gA P) r c ∧ cov P ⊆ c ∧ DomC (norm r) (fN v P)) ∧
    (P.w = false → occ P = true → ∀ N : Finset ℕ, N ⊆ cov P →
      ∃ r, IR v N (gA P) r ∧ DomC (norm r) (fN v P)) := by
  intro P
  induction P using FT.ind with
  | _ S e w ks ih =>
    intro hok hc
    have hkOk : ∀ K ∈ ks, FOk v K := FOkL_iff.1 hok.2.2.2.2
    have hkConn : ∀ K ∈ ks, Conn (fT v K) := by
      have hc' : Conn (CT.node (if w then insert v S else S) [if w then e + 1 else e] (ks.map (fT v))) := by
        rw [fT_node] at hc; exact hc
      have := ((conn_node).1 hc').1
      intro K hK
      exact (ConnL_iff.1 this) (fT v K) (List.mem_map.2 ⟨K, hK, rfl⟩)
    have hIH := fun K hK => ih K hK (hkOk K hK) (hkConn K hK)
    refine ⟨?_, ?_⟩
    · intro hw
      have hw' : w = true := hw
      subst hw'
      exact step_R v S e ks hok hc (fun K hK hwK => (hIH K hK).1 hwK)
    · intro hw hocc N hN
      have hw' : w = false := hw
      subst hw'
      rcases hok.2.2.2.1 rfl with hno | ⟨pre, K0, post, hks, hK0, hpre, hpost⟩
      · simp only [occ, Bool.false_or] at hocc
        rw [hno] at hocc; exact absurd hocc (by simp)
      · subst hks
        exact step_I v N S e pre K0 post hok hK0 hpre hpost hc hN
          (fun hwK => (hIH K0 (by simp)).1 hwK)
          (fun hwK hN0 => (hIH K0 (by simp)).2 hwK hK0 N hN0)

/-! ## the flagged profile tree of a real decomposition -/

mutual
/-- Label `X ∩ B`, size `|X ∩ U|`, flag `v ∈ X`. -/
def mkFT (B U : Finset ℕ) (v : ℕ) : RT → FT
  | .node X ks => FT.node (X ∩ B) (X ∩ U).card (decide (v ∈ X)) (mkFTL B U v ks)
def mkFTL (B U : Finset ℕ) (v : ℕ) : List RT → List FT
  | [] => []
  | k :: ks => mkFT B U v k :: mkFTL B U v ks
end

theorem mkFTL_eq (B U : Finset ℕ) (v : ℕ) (ks : List RT) : mkFTL B U v ks = ks.map (mkFT B U v) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [mkFTL, ih]

theorem mkFT_node (B U : Finset ℕ) (v : ℕ) (X : Finset ℕ) (ks : List RT) :
    mkFT B U v (.node X ks) = FT.node (X ∩ B) (X ∩ U).card (decide (v ∈ X)) (ks.map (mkFT B U v)) := by
  simp [mkFT, mkFTL_eq]

theorem uT_mkFT (B U : Finset ℕ) (v : ℕ) : ∀ t : RT,
    uT (mkFT B U v t) = RT.profF (fun X => (X ∩ U).card) B t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node, uT_node, RT.profF_node]
    congr 1
    rw [List.map_map]
    exact List.map_congr_left (fun k hk => ih k hk)

theorem fT_mkFT (B U : Finset ℕ) (v : ℕ) (hvU : v ∉ U) (hvB : v ∉ B) : ∀ t : RT,
    (∀ X ∈ t.bags, X ⊆ insert v U) → fT v (mkFT B U v t) = RT.prof (insert v B) t := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hX
    have hXX : X ⊆ insert v U := hX X ((RT.bags_node X ks).2 (Or.inl rfl))
    rw [mkFT_node, fT_node, RT.prof_node]
    have hlab : (if decide (v ∈ X) = true then insert v (X ∩ B) else X ∩ B) = X ∩ insert v B := by
      by_cases hv : v ∈ X
      · rw [decide_eq_true hv]
        simp only [if_true]
        ext x
        simp only [Finset.mem_insert, Finset.mem_inter]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨hv, Or.inl rfl⟩
          · exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h2⟩
      · rw [decide_eq_false hv]
        simp only [Bool.false_eq_true, if_false]
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, Or.inr h2⟩
        · rintro ⟨h1, h2 | h2⟩
          · exact absurd (h2 ▸ h1) hv
          · exact ⟨h1, h2⟩
    have hsize : (if decide (v ∈ X) = true then (X ∩ U).card + 1 else (X ∩ U).card) = X.card := by
      by_cases hv : v ∈ X
      · rw [decide_eq_true hv]
        simp only [if_true]
        have : X = insert v (X ∩ U) := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_inter]
          constructor
          · intro hx
            by_cases hxv : x = v
            · exact Or.inl hxv
            · rcases Finset.mem_insert.1 (hXX hx) with h | h
              · exact absurd h hxv
              · exact Or.inr ⟨hx, h⟩
          · rintro (rfl | ⟨h1, h2⟩)
            · exact hv
            · exact h1
        conv_rhs => rw [this]
        rw [Finset.card_insert_of_notMem (by simp [hvU])]
      · rw [decide_eq_false hv]
        simp only [Bool.false_eq_true, if_false]
        congr 1
        ext x
        simp only [Finset.mem_inter]
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rcases Finset.mem_insert.1 (hXX hx) with h | h
          · exact absurd (h ▸ hx) hv
          · exact h
    have hkids : (ks.map (mkFT B U v)).map (fT v) = ks.map (RT.prof (insert v B)) := by
      rw [List.map_map]
      exact List.map_congr_left (fun k hk => ih k hk
        (fun Y hY => hX Y ((RT.bags_node X ks).2 (Or.inr ⟨k, hk, hY⟩))))
    rw [hlab, hsize, hkids]

theorem w_mkFT (B U : Finset ℕ) (v : ℕ) (k : RT) : (mkFT B U v k).w = decide (v ∈ k.rootBag) := by
  cases k; rfl

theorem occ_mkFT (B U : Finset ℕ) (v : ℕ) : ∀ t : RT, occ (mkFT B U v t) = true ↔ v ∈ t.verts := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node, occ_node, RT.verts_node]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_map, List.any_eq_true, Function.comp]
    constructor
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, (ih k hk).1 h⟩
    · rintro (h | ⟨k, hk, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, hk, (ih k hk).2 h⟩

theorem mem_cov_mkFT (B U : Finset ℕ) (v : ℕ) (x : ℕ) : ∀ t : RT,
    x ∈ cov (mkFT B U v t) ↔ ∃ X ∈ t.bags, v ∈ X ∧ x ∈ X ∧ x ∈ B := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    rw [mkFT_node]
    simp only [cov, Finset.mem_union, mem_covL, List.mem_map, RT.bags_node]
    constructor
    · rintro (h | ⟨k', ⟨k, hk, rfl⟩, h⟩)
      · split_ifs at h with hw
        · have hv : v ∈ X := by simpa using hw
          rw [Finset.mem_inter] at h
          exact ⟨X, Or.inl rfl, hv, h⟩
        · simp at h
      · obtain ⟨Y, hY, h'⟩ := (ih k hk).1 h
        exact ⟨Y, Or.inr ⟨k, hk, hY⟩, h'⟩
    · rintro ⟨Y, hY | ⟨k, hk, hY⟩, hvY, hxY, hxB⟩
      · subst hY
        left
        rw [if_pos (by simpa using hvY)]
        exact Finset.mem_inter.2 ⟨hxY, hxB⟩
      · right
        exact ⟨mkFT B U v k, ⟨k, hk, rfl⟩, (ih k hk).2 ⟨Y, hY, hvY, hxY, hxB⟩⟩

theorem decomp_occ {v : ℕ} : ∀ ks : List RT, ks.Pairwise (fun k1 k2 => v ∈ k1.verts → v ∈ k2.verts → False) →
    (∀ k ∈ ks, v ∉ k.verts) ∨ ∃ pre k post, ks = pre ++ k :: post ∧ v ∈ k.verts ∧
      (∀ k' ∈ pre, v ∉ k'.verts) ∧ (∀ k' ∈ post, v ∉ k'.verts) := by
  intro ks
  induction ks with
  | nil => intro _; left; simp
  | cons k ks ih =>
    intro h
    rw [List.pairwise_cons] at h
    by_cases hk : v ∈ k.verts
    · right
      exact ⟨[], k, ks, rfl, hk, by simp, fun k' hk' hv => h.1 k' hk' hk hv⟩
    · rcases ih h.2 with h1 | ⟨pre, k0, post, rfl, h2, h3, h4⟩
      · left
        intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · exact hk
        · exact h1 k' hk'
      · right
        refine ⟨k :: pre, k0, post, rfl, h2, ?_, h4⟩
        intro k' hk'
        rcases List.mem_cons.1 hk' with rfl | hk'
        · exact hk
        · exact h3 k' hk'

theorem FOk_mkFT (B U : Finset ℕ) (v : ℕ) (hB : B ⊆ U) (hvB : v ∉ B) : ∀ t : RT, t.Conn →
    FOk v (mkFT B U v t) := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hc
    obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff X ks).1 hc
    rw [mkFT_node]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact hvB (Finset.mem_inter.1 h).2
    · exact Finset.card_le_card (Finset.inter_subset_inter_left hB)
    · intro hw k' hk' hocc
      have hvX : v ∈ X := by simpa using hw
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      have hv := (occ_mkFT B U v k).1 hocc
      have := h2 k hk v hvX hv
      rw [w_mkFT]
      simpa using this
    · intro hw
      have hvX : v ∉ X := by simpa using hw
      have hpw : ks.Pairwise (fun k1 k2 => v ∈ k1.verts → v ∈ k2.verts → False) :=
        h3.imp (fun {a b} h hva hvb => hvX (h v hva hvb))
      rcases decomp_occ ks hpw with hno | ⟨pre, k0, post, rfl, hk0, hpre, hpost⟩
      · left
        rw [occL_eq_any, List.any_eq_false]
        intro k' hk'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
        have := hno k hk
        simpa [occ_mkFT B U v k] using this
      · right
        refine ⟨pre.map (mkFT B U v), mkFT B U v k0, post.map (mkFT B U v), by simp, (occ_mkFT B U v k0).2 hk0, ?_, ?_⟩
        · rw [occL_eq_any, List.any_eq_false]
          intro k' hk'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
          simpa [occ_mkFT B U v k] using hpre k hk
        · rw [occL_eq_any, List.any_eq_false]
          intro k' hk'
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
          simpa [occ_mkFT B U v k] using hpost k hk
    · rw [FOkL_iff]
      intro k' hk'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
      exact ih k hk (h1 k hk)

theorem maxEntry_prof_le (B : Finset ℕ) {k : ℕ} : ∀ t : RT, t.Width k → maxEntry (RT.prof B t) ≤ k + 1 := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro hw
    rw [RT.prof_node, maxEntry_le_iff]
    refine ⟨?_, ?_⟩
    · intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact hw X ((RT.bags_node X ks).2 (Or.inl rfl))
    · intro k' hk'
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hk'
      exact ih k0 hk0 (fun Y hY => hw Y ((RT.bags_node X ks).2 (Or.inr ⟨k0, hk0, hY⟩)))

/-- **Introduce** (exact layer + split transport). -/
theorem char_intro_dom {adj : Adj} {v : ℕ} {c : NT} {k : ℕ} {t : RT} (hg : (NT.intro v c).Good adj)
    (h : PTD adj (.intro v c) k t) :
    ∃ c' ∈ CT.introC (k + 1) v (nbrs adj v c.bag) ((t.restrict c.under).char c.bag),
      DomC c' (t.char (insert v c.bag)) := by
  obtain ⟨hvB, -, hvU, -⟩ := hg
  have hBU : c.bag ⊆ c.under := NT.bag_subset_under c
  have hverts : t.verts = insert v c.under := h.1.verts_eq
  have hbags : ∀ X ∈ t.bags, X ⊆ insert v c.under := by
    intro X hX x hx
    rw [← hverts]
    exact (RT.mem_verts_iff t x).2 ⟨X, hX, hx⟩
  have hconn := h.1.conn
  have hok := FOk_mkFT c.bag c.under v hBU hvB t hconn
  have huT := uT_mkFT c.bag c.under v t
  have hfT := fT_mkFT c.bag c.under v hvU hvB t hbags
  have hcf : Conn (fT v (mkFT c.bag c.under v t)) := by rw [hfT]; exact RT.conn_prof _ t hconn
  have hocc : occ (mkFT c.bag c.under v t) = true := (occ_mkFT c.bag c.under v t).2 (by rw [hverts]; simp)
  have hN : nbrs adj v c.bag ⊆ cov (mkFT c.bag c.under v t) := by
    intro w hw
    obtain ⟨hwB, hadj⟩ := Finset.mem_filter.1 hw
    have hwU := hBU hwB
    have hne : v ≠ w := fun e => hvB (e ▸ hwB)
    have hadjG : adj.graph.Adj v w := by
      simp only [Adj.graph, SimpleGraph.fromRel_adj]; exact ⟨hne, Or.inl hadj⟩
    obtain ⟨X, hX, hvX, hwX⟩ := h.1.edges v w hadjG (by simp [NT.under]) (by simp [NT.under, hwU])
    exact (mem_cov_mkFT c.bag c.under v w t).2 ⟨X, hX, hvX, hwX, hwB⟩
  have key : ∃ r, IR v (nbrs adj v c.bag) (norm (uT (mkFT c.bag c.under v t))) r ∧
      DomC (norm r) (norm (fT v (mkFT c.bag c.under v t))) := by
    by_cases hw : (mkFT c.bag c.under v t).w = true
    · obtain ⟨r, c0, h1, h2, h3⟩ := (main_intro v _ hok hcf).1 hw
      exact ⟨r, IR_of_winR v _ h1 (hN.trans h2), h3⟩
    · exact (main_intro v _ hok hcf).2 (by simpa using hw) hocc _ hN
  obtain ⟨r, hr, hd⟩ := key
  have hchar1 : (t.restrict c.under).char c.bag = norm (uT (mkFT c.bag c.under v t)) := by
    unfold RT.char; rw [RT.prof_restrict hBU, huT]
  have hchar2 : t.char (insert v c.bag) = norm (fT v (mkFT c.bag c.under v t)) := by
    unfold RT.char; rw [hfT]
  refine ⟨norm r, ?_, ?_⟩
  · rw [hchar1]
    refine mem_introC.2 ⟨r, hr, rfl, ?_⟩
    refine (maxEntry_dom_le hd).trans ?_
    rw [hfT]
    exact (maxEntry_norm_le _).trans (maxEntry_prof_le _ _ h.2)
  · rw [hchar2]; exact hd

end Lax117284Proofs.Treewidth.Chars
