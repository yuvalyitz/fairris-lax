import Lax117284Proofs.Treewidth.Chars.AnalyzeRT

/-!
# The remaining `analyze` lemmas (C8a)

* `analyze_char` : the characteristic read off the analysis is `RT.char`;
* `conn_of_conn_toRT_analyze`, `analyze_toRT_isTD`, `analyze_toRT_width` : the two directions of validity / width of
  the reassembled analysis (C3 proved the forward directions);
* `analyze_toRT_char` : true for `B' = B` (this is `char_toRT_analyze`); for `B' ≠ B` it is FALSE as typed in
  `proofs-todo/Statements.lean` (reassembling the analysis sorts the kids by `key` relative to `B`; the normal form
  relative to `B'` sorts stably, so ties in `B'`-keys expose the reordering).  See `Wrap/NOTES.md`.
-/

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- **NEW** the analysis computes the characteristic. -/
theorem analyze_char (B : Finset ℕ) (t : RT) : (analyze B t).char = t.char B := by
  rw [char_eq_charF, AR.char_eq_charF]

/-- The reverse of `conn_node_rearr`. -/
theorem conn_node_rearr_rev {X : Finset ℕ} {ks L : List RT} (ψ : RT → RT)
    (hv : ∀ k ∈ ks, (ψ k).verts = k.verts) (hr : ∀ k ∈ ks, (ψ k).rootBag = k.rootBag)
    (hc : ∀ k ∈ ks, (ψ k).Conn → k.Conn) (hperm : L.Perm (ks.map ψ)) (h : (RT.node X L).Conn) :
    (RT.node X ks).Conn := by
  obtain ⟨h1, h2, h3⟩ := (RT.conn_node_iff X L).1 h
  rw [RT.conn_node_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact hc k hk (h1 _ ((hperm.mem_iff).2 (List.mem_map.2 ⟨k, hk, rfl⟩)))
  · intro k hk v hvX hvK
    have hmem : ψ k ∈ L := (hperm.mem_iff).2 (List.mem_map.2 ⟨k, hk, rfl⟩)
    rw [← hv k hk] at hvK
    have := h2 _ hmem v hvX hvK
    rwa [hr k hk] at this
  · have hsymm : ∀ {x y : RT}, (∀ v ∈ x.verts, v ∈ y.verts → v ∈ X) → (∀ v ∈ y.verts, v ∈ x.verts → v ∈ X) :=
      fun hxy v hy hx => hxy v hx hy
    rw [List.Perm.pairwise_iff hsymm hperm] at h3
    rw [List.pairwise_map] at h3
    refine (List.Pairwise.and_mem.1 h3).imp ?_
    rintro a b ⟨ha, hb, hab⟩ v hva hvb
    rw [← hv a ha] at hva
    rw [← hv b hb] at hvb
    exact hab v hva hvb

theorem conn_of_conn_toRT_analyze (B : Finset ℕ) : ∀ t : RT, (AR.toRT (analyze B t)).Conn → t.Conn := by
  intro t
  induction t using RT.ind with
  | _ X ks ih =>
    intro h
    obtain ⟨core', hp, e⟩ := toRT_analyze_shape B X ks
    rw [e] at h
    let ψ : RT → RT := fun k => if prunedB (X ∩ B) (analyze B k) = true then k else AR.toRT (analyze B k)
    apply conn_node_rearr_rev (ks := ks) (ψ := ψ) ?_ ?_ ?_ ?_ h
    · intro k hk
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simp [ψ, hh]
      · simp [ψ, hh, verts_toRT_analyze]
    · intro k hk
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simp [ψ, hh]
      · simp [ψ, hh, rootBag_toRT_analyze]
    · intro k hk hck
      by_cases hh : prunedB (X ∩ B) (analyze B k) = true
      · simpa [ψ, hh] using hck
      · simp only [ψ, hh] at hck
        exact ih k hk hck
    · have h1 : (ks.map ψ).Perm ((ks.filter (fun k => prunedB (X ∩ B) (analyze B k))).map ψ ++
          (ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map ψ) :=
        (((List.filter_append_perm (fun k => prunedB (X ∩ B) (analyze B k)) ks).map ψ).symm).trans
          (by rw [List.map_append])
      refine List.Perm.trans ?_ h1.symm
      have e1 : (ks.filter (fun k => prunedB (X ∩ B) (analyze B k))).map ψ =
          ks.filter (fun k => prunedB (X ∩ B) (analyze B k)) := by
        conv_rhs => rw [← List.map_id (ks.filter _)]
        apply List.map_congr_left
        intro k hk
        simp [ψ, (List.mem_filter.1 hk).2]
      have e2 : (ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map ψ =
          ((ks.filter (fun k => !prunedB (X ∩ B) (analyze B k))).map (analyze B)).map AR.toRT := by
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have : prunedB (X ∩ B) (analyze B k) = false := prunedB_false_of_not (List.mem_filter.1 hk).2
        simp [ψ, this]
      rw [e1, e2]
      exact List.Perm.append_left _ (hp.map AR.toRT)

/-- **NEW** reassembling the analysis gives an equivalent tree: same validity. -/
theorem analyze_toRT_isTD (B : Finset ℕ) (t : RT) (G : SimpleGraph ℕ) (U : Finset ℕ) :
    (AR.toRT (analyze B t)).IsTD G U ↔ t.IsTD G U := by
  refine ⟨fun h => ⟨by rw [← verts_toRT_analyze B t]; exact h.verts_eq, ?_,
      conn_of_conn_toRT_analyze B t h.conn⟩, fun h => isTD_toRT_analyze B h⟩
  intro u v huv hu hv
  obtain ⟨X, hX, hxu, hxv⟩ := h.edges u v huv hu hv
  exact ⟨X, (mem_bags_toRT_analyze B t X).1 hX, hxu, hxv⟩

/-- **NEW** reassembling the analysis preserves the width. -/
theorem analyze_toRT_width (B : Finset ℕ) (t : RT) (w : ℕ) : (AR.toRT (analyze B t)).Width w ↔ t.Width w :=
  ⟨fun h X hX => h X ((mem_bags_toRT_analyze B t X).2 hX), fun h => width_toRT_analyze B h⟩

/-- **NEW** reassembling the analysis preserves the characteristic (relative to the boundary of the analysis; for
another boundary the statement of `Statements.lean` is false, see the module docstring). -/
theorem analyze_toRT_char (B : Finset ℕ) (t : RT) : (AR.toRT (analyze B t)).char B = t.char B :=
  char_toRT_analyze B t

end Lax117284Proofs.Treewidth.Chars
