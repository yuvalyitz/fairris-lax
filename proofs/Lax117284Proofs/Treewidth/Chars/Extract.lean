import Lax117284Proofs.Treewidth.Chars.TablesSound

/-!
# `extract_spec` (work package C6b): correctness of the extraction

For every table entry `c` of a good nice tree, `extract adj k nt c` returns a real decomposition which is a partial
decomposition of width `≤ k` whose characteristic is dominated by `c`.  Proved by induction on the nice tree,
together with *definedness* (`extract … ≠ none`) and *soundness of every returned value* (the `findSome?` may pick
a different table entry than the one used to prove definedness, so both facts are carried).

**Repair** (relative to `proofs-todo/Statements.lean`): as for `tables_sound`, the extra hypotheses
`hs : adj.SymmOn W` and `nt.under ⊆ W` (needed by `realIntro_spec`).
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

theorem findSome_exists {α β : Type} {l : List α} {f : α → Option β} {x : α} (hx : x ∈ l) {t : β}
    (hf : f x = some t) : ∃ t', l.findSome? f = some t' := by
  have : (l.findSome? f).isSome = true := List.findSome?_isSome_iff.2 ⟨x, hx, by simp [hf]⟩
  exact Option.isSome_iff_exists.1 this

theorem findSome_sound {α β : Type} {l : List α} {f : α → Option β} {t : β} (h : l.findSome? f = some t) :
    ∃ x ∈ l, f x = some t := by
  obtain ⟨l₁, a, l₂, rfl, ha, -⟩ := List.findSome?_eq_some_iff.1 h
  exact ⟨a, by simp, ha⟩

theorem extract_all {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) :
    ∀ {nt : NT}, nt.Good adj → nt.under ⊆ W → ∀ c ∈ tables adj k nt,
    (∃ t, extract adj k nt c = some t) ∧
      ∀ t, extract adj k nt c = some t → PTD adj nt k t ∧ DomC (t.char nt.bag) c
  | .leaf, _, _, c, hc => by
    simp only [tables, List.mem_singleton] at hc
    subst hc
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro t ht
    simp only [extract, Option.some.injEq] at ht
    subst ht
    refine ⟨ptd_leaf adj k, ?_⟩
    have := char_leaf (adj := adj) (k := k) (.node ∅ []) (ptd_leaf adj k)
    simp only [NT.bag]
    rw [this]
    exact CT.DomC.refl _
  | .forget x c, hg, hW, q, hq => by
    have hmem := hq
    simp only [tables, forgetTable, List.mem_dedup, List.mem_map] at hmem
    obtain ⟨q0, hq0, hq0e⟩ := hmem
    have key : ∀ q1 t0, PTD adj c k t0 → DomC (t0.char c.bag) q1 → CT.forgetC x q1 = q →
        PTD adj (.forget x c) k t0 ∧ DomC (t0.char (NT.forget x c).bag) q := by
      intro q1 t0 ht0 hd he
      refine ⟨ht0, ?_⟩
      simp only [NT.bag]
      rw [char_forget c.bag x t0 ht0.1.conn, ← he]
      exact forgetC_mono x hd
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨t0, ht0⟩, -⟩ := extract_all hs hg.2 hW q0 hq0
      refine findSome_exists (x := q0) hq0 (t := t0) ?_
      simp [hq0e, ht0]
    · intro t ht
      simp only [extract] at ht
      obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
      by_cases he : CT.forgetC x q1 = q
      · simp only [he, if_true] at hf
        obtain ⟨-, hsp⟩ := extract_all hs hg.2 hW q1 hq1
        obtain ⟨h1, h2⟩ := hsp t hf
        exact key q1 t h1 h2 he
      · simp [he] at hf
  | .join a b, hg, hW, q, hq => by
    have hg' : a.bag = b.bag ∧ a.under ∩ b.under ⊆ a.bag ∧ NT.Good adj a ∧ NT.Good adj b ∧
      (∀ u ∈ a.under, ∀ v ∈ b.under, (adj u v = true ∨ adj v u = true) → u ∈ a.bag ∨ v ∈ a.bag) := hg
    obtain ⟨hab, -, hga, hgb, -⟩ := hg'
    have hWa : a.under ⊆ W := fun x hx => hW (Finset.mem_union_left _ hx)
    have hWb : b.under ⊆ W := fun x hx => hW (Finset.mem_union_right _ hx)
    have hmem := hq
    simp only [tables, joinTable, List.mem_dedup, List.mem_flatMap] at hmem
    obtain ⟨ca, hca, cb, hcb, hq'⟩ := hmem
    -- the step, for any pair of entries
    have step : ∀ ca cb ta tb, ca ∈ tables adj k a → cb ∈ tables adj k b → PTD adj a k ta →
        DomC (ta.char a.bag) ca → PTD adj b k tb → DomC (tb.char b.bag) cb → q ∈ CT.joinC (k + 1) ca cb →
        ∃ t, realJoin (k + 1) a.bag ta tb q = some t ∧ PTD adj (.join a b) k t ∧
          DomC (t.char (NT.join a b).bag) q := by
      intro ca cb ta tb _ _ hta hda htb hdb hqq
      rw [← hab] at hdb
      exact realJoin_spec hg hta htb hda hdb hqq
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨ta, hta⟩, -⟩ := extract_all hs hga hWa ca hca
      obtain ⟨⟨tb, htb⟩, -⟩ := extract_all hs hgb hWb cb hcb
      obtain ⟨-, hspa⟩ := extract_all hs hga hWa ca hca
      obtain ⟨-, hspb⟩ := extract_all hs hgb hWb cb hcb
      obtain ⟨pa, da⟩ := hspa ta hta
      obtain ⟨pb, db⟩ := hspb tb htb
      obtain ⟨t, ht, -⟩ := step ca cb ta tb hca hcb pa da pb db hq'
      have inner : ∃ t', (tables adj k b).findSome? (fun cb => if q ∈ CT.joinC (k + 1) ca cb then
          (extract adj k a ca).bind (fun ta => (extract adj k b cb).bind (fun tb =>
            realJoin (k + 1) a.bag ta tb q)) else none) = some t' := by
        refine findSome_exists (x := cb) hcb (t := t) ?_
        simp [hq', hta, htb, ht]
      obtain ⟨t', ht'⟩ := inner
      refine findSome_exists (x := ca) hca (t := t') ?_
      simpa [extract] using ht'
    · intro t ht
      simp only [extract] at ht
      obtain ⟨ca1, hca1, hf⟩ := findSome_sound ht
      obtain ⟨cb1, hcb1, hf'⟩ := findSome_sound hf
      by_cases he : q ∈ CT.joinC (k + 1) ca1 cb1
      · simp only [he, if_true] at hf'
        obtain ⟨-, hspa⟩ := extract_all hs hga hWa ca1 hca1
        obtain ⟨-, hspb⟩ := extract_all hs hgb hWb cb1 hcb1
        rcases hea : extract adj k a ca1 with _ | ta
        · simp [hea] at hf'
        rcases heb : extract adj k b cb1 with _ | tb
        · simp [hea, heb] at hf'
        simp only [hea, heb, Option.bind_some] at hf'
        obtain ⟨pa, da⟩ := hspa ta hea
        obtain ⟨pb, db⟩ := hspb tb heb
        obtain ⟨t2, ht2, h1, h2⟩ := step ca1 cb1 ta tb hca1 hcb1 pa da pb db he
        rw [ht2] at hf'
        cases hf'
        exact ⟨h1, h2⟩
      · simp [he] at hf'
  | .intro v c, hg, hW, q, hq => by
    have hgc := hg.2.2.2
    have hWc : c.under ⊆ W := fun x hx => hW (Finset.mem_insert_of_mem hx)
    have hvW : v ∈ W := hW (Finset.mem_insert_self _ _)
    have hsym : ∀ u ∈ c.under, adj u v = true → adj v u = true := by
      intro u hu h
      rw [← hs u (hWc hu) v hvW]; exact h
    have hmem := hq
    simp only [tables, introTable, List.mem_dedup, List.mem_flatMap] at hmem
    obtain ⟨q0, hq0, hq'⟩ := hmem
    have step : ∀ q0 t0, q0 ∈ tables adj k c → PTD adj c k t0 → DomC (t0.char c.bag) q0 →
        q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q0 →
        ∃ t, realIntro (k + 1) v (nbrs adj v c.bag) c.bag t0 q = some t ∧ PTD adj (.intro v c) k t ∧
          DomC (t.char (NT.intro v c).bag) q := by
      intro q0 t0 _ ht0 hd hqq
      exact realIntro_spec hg hsym ht0 hd hqq
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨t0, ht0⟩, hsp⟩ := extract_all hs hgc hWc q0 hq0
      obtain ⟨p0, d0⟩ := hsp t0 ht0
      obtain ⟨t, ht, -⟩ := step q0 t0 hq0 p0 d0 hq'
      refine findSome_exists (x := q0) hq0 (t := t) ?_
      simp [hq', ht0, ht]
    · intro t ht
      simp only [extract] at ht
      obtain ⟨q1, hq1, hf⟩ := findSome_sound ht
      by_cases he : q ∈ CT.introC (k + 1) v (nbrs adj v c.bag) q1
      · simp only [he, if_true] at hf
        obtain ⟨-, hsp⟩ := extract_all hs hgc hWc q1 hq1
        rcases hea : extract adj k c q1 with _ | t0
        · simp [hea] at hf
        simp only [hea, Option.bind_some] at hf
        obtain ⟨p0, d0⟩ := hsp t0 hea
        obtain ⟨t2, ht2, h1, h2⟩ := step q1 t0 hq1 p0 d0 he
        rw [ht2] at hf
        cases hf
        exact ⟨h1, h2⟩
      · simp [he] at hf

/-- **Soundness = correctness of extraction.** -/
theorem extract_spec {adj : Adj} {k : ℕ} {W : Finset ℕ} (hs : adj.SymmOn W) {nt : NT} (hg : nt.Good adj)
    (hW : nt.under ⊆ W) : ∀ c ∈ tables adj k nt,
    ∃ t, extract adj k nt c = some t ∧ PTD adj nt k t ∧ DomC (t.char nt.bag) c := by
  intro c hc
  obtain ⟨⟨t, ht⟩, hsp⟩ := extract_all hs hg hW c hc
  exact ⟨t, ht, hsp t ht⟩

end Lax117284Proofs.Treewidth.Chars
