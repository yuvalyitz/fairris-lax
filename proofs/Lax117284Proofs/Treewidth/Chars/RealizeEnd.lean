import Lax117284Proofs.Treewidth.Chars.RealizeWin

/-!
# The end-case of the region step (work package C5, part 8)

`pr_end`: `processRun v pre (endAt c₂)` realises the plan `top pre (endAt c₂)`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The replacement subtree of a plan with an optional pre-cut. -/
def topRep (S : Finset ℕ) (y : List ℕ) : Option Cut → CT → CT
  | none, X => X
  | some c, X => CT.node S (y.take (cHi c + 1)) [X]

def preLo : Option Cut → ℕ
  | none => 0
  | some c => cLo c

theorem kid_keep {v : ℕ} {B S : Finset ℕ} {k : AR} (hk : RunOk v B k) (hp : prunedB S k = false) :
    keep S (norm (AR.charF Finset.card k)) = true := by
  have hn := norm_prof_kid hk.canon hk.free
  have : norm (AR.charF Finset.card k) = AR.charF Finset.card k := by rw [← hn, norm_idem]
  rw [this, AR.keep_charF]
  have : (k.isLeaf && decide (k.S ⊆ S)) = false := hp
  simp [this]

theorem processRun_endAt_eq (v : ℕ) (pre : Option Cut) (c : Cut) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    processRun v pre (.endAt c) (.run S ns ks) =
      .run S (processRun v pre (.endAt c) (.run S ns ks)).chain ks := by
  rw [processRun_chain_eq, processRun_eq]

theorem toRT_processRun_endAt (v : ℕ) (pre : Option Cut) (c : Cut) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    AR.toRT (processRun v pre (.endAt c) (.run S ns ks)) =
      AR.chainToRT (processRun v pre (.endAt c) (.run S ns ks)).chain (ks.map AR.toRT) := by
  conv_lhs => rw [processRun_endAt_eq]
  rw [AR.toRT_run]


theorem kids_norm_prof {v : ℕ} {B : Finset ℕ} {ks : List AR} (hk : ∀ k ∈ ks, RunOk v B k) :
    (ks.map (AR.charF Finset.card)).map norm = ((ks.map AR.toRT).map (RT.prof (insert v B))).map norm := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro k hkk
  have hn := norm_prof_kid (hk k hkk).canon (hk k hkk).free
  simp only [Function.comp]
  rw [← hn, norm_idem]

theorem pr_end (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) (pre : Option Cut) (c2 : Cut)
    (hpre : PreOk (typical (csz ns)).length pre) (hc2 : c2.Valid (typical (csz ns)).length)
    (hlh : LoHi pre (.endAt c2)) :
    PRC v B (.run S ns ks) (processRun v pre (.endAt c2) (.run S ns ks))
      (topRep S (typical (csz ns)) pre
        (CT.node (insert v S) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
          [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))]))
      S pre.isSome := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hs : csz ns ≠ [] := by
    intro h; apply hns; unfold csz at h; exact List.map_eq_nil_iff.1 h
  have hlenw : (witnesses (csz ns)).length = (typical (csz ns)).length := (witnesses_cover (csz ns)).len
  have hp' : PreOk (witnesses (csz ns)).length pre := by rw [hlenw]; exact hpre
  have hw' : WOk (witnesses (csz ns)).length (.endAt c2) := by
    show c2.Valid _; rw [hlenw]; exact hc2
  obtain ⟨L, M, R, ns2, st, re, hdup, hns2, hchainA, hchain, hcL, hcM, hcR, hMne, hL0, hL1, hRw, hRe⟩ :=
    processRun_chain v pre (.endAt c2) S ns ks hns hp' hw' hlh
  have hRne : R ≠ [] := hRe c2 rfl
  have hinfo := hdup.info
  have hMsub : ∀ m ∈ M, m ∈ (L ++ M ++ R) := fun n hn => by simp [hn]
  -- kids
  have hK : List.Forall₂ (TI v) (ks.map AR.toRT) (ks.map AR.toRT) := List.forall₂_same.2 (fun k _ => TI.refl v k)
  have hKQ := kids_norm_prof (v := v) (B := B) hkids
  have hK1 : R = [] → tcL v (ks.map AR.toRT) true = 0 := fun h => absurd h hRne
  have hK2 : R ≠ [] → tcL v (ks.map AR.toRT) false = 0 := by
    intro _
    rw [tcL_eq_sum, List.sum_eq_zero]
    intro x hx'
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hx'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
    exact tc_zero_of_notin v _ false (hkfree k hk)
  obtain ⟨hTI, htc, hnorm, hvb, hmb⟩ := region_PRC v B S hvB (ns := ns) (L := L) (M := M) (R := R) (ks := ks)
    (K' := ks.map AR.toRT) (ks.map (AR.charF Finset.card)) (chain'' := (processRun v pre (.endAt c2) (.run S ns ks)).chain)
    hns hMne hbase (by rw [← hns2]; exact hdup) hchain (by
      obtain ⟨g, hg, he⟩ := addV_map v st re ns2
      exact ⟨g, hg, by rw [hchainA, he, hns2]⟩) hK hK1 hK2 hKQ
  rw [hchain] at hTI htc hnorm hvb hmb
  have hxt : AR.toRT (processRun v pre (.endAt c2) (.run S ns ks)) =
      AR.chainToRT (L ++ M.map (av v) ++ R) (ks.map AR.toRT) := by
    rw [toRT_processRun_endAt, hchain]
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hMfree : ∀ m ∈ M, v ∉ m.bag := by
    intro m hm
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    rw [hb]; exact (hbase n0 hn0).2.1
  have hc2' : c2.Valid (witnesses (csz ns)).length := by rw [hlenw]; exact hc2
  -- dominance of the three pieces
  have hM : Dom (typical (csz M)) (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)) := by
    rw [hcM]
    cases pre with
    | none =>
      have := dom_left hs hc2'
      simpa [preAB, endAB, preLo] using this
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have := (dom_mid hs hc1' hc2' hlh).2
      simpa [preAB, endAB, preLo] using this
  have hR : Dom (typical (csz R)) ((typical (csz ns)).drop (cLo c2)) := by
    rw [hcR]; exact dom_right hs hc2'
  have hMq : Dom (typical (csz (M.map (av v)))) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre))) := by
    rw [csz_map_av hMfree, typical_plus1]
    unfold plus1
    exact dom_map_succ hM
  -- the region
  have hwin : DomC (CT.node (insert v S) (typical (csz (M.map (av v)))) [CT.node S (typical (csz R)) (ks.map (AR.charF Finset.card))])
      (CT.node (insert v S) (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
          [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))]) :=
    ⟨rfl, hMq, ⟨⟨rfl, hR, DomCL.refl _⟩, trivial⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; exact hTI
  · intro p
    rw [hxt, htc p]
    cases pre with
    | none => simp [hL0 rfl]
    | some c1 => simp [hL1 (by simp)]
  · rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    exact (RT.mem_verts_iff _ v).2 ⟨insert v m.bag, hmb m hm, Finset.mem_insert_self _ _⟩
  · intro u hu
    rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    refine ⟨insert v m.bag, hmb m hm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
    have : u ∈ n0.bag ∩ B := by rw [(hbase n0 hn0).1]; exact hu
    rw [hb]; exact (Finset.mem_inter.1 this).1
  · -- chr
    refine ⟨regionQ v S L M R (ks.map (AR.charF Finset.card)), by rw [hxt]; exact hnorm, ?_⟩
    cases pre with
    | none =>
      simp only [regionQ, if_neg hRne, hL0 rfl, if_true, topRep]
      exact hwin
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have hL : Dom (typical (csz L)) ((typical (csz ns)).take (cHi c1 + 1)) := by
        rw [hcL]; simpa [preAB] using dom_left hs hc1'
      have hLne : L ≠ [] := hL1 (by simp)
      simp only [regionQ, if_neg hRne, if_neg hLne, topRep]
      exact ⟨rfl, hL, ⟨hwin, trivial⟩⟩
  · -- wid
    intro Y hY hvY
    rw [hxt] at hY
    have hkeep : (∃ k ∈ [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))],
        keep (insert v S) (norm k) = true) ∨
        (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre))).length ≤ 1 := by
      by_cases hka : ks = []
      · right
        have h1 : ns.length = 1 := hleaf hka
        have hy1 : (typical (csz ns)).length ≤ 1 := by
          obtain ⟨x0, hx0⟩ : ∃ x0, csz ns = [x0] := by
            have : (csz ns).length = 1 := by rw [csz_length]; exact h1
            exact List.length_eq_one_iff.1 this
          rw [hx0, typical_singleton]; simp
        simp only [plus1, List.length_map, List.length_drop, List.length_take]
        omega
      · left
        obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil ks hka
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        by_contra hcon
        have hf : keep (insert v S) (norm (CT.node S ((typical (csz ns)).drop (cLo c2))
            (ks.map (AR.charF Finset.card)))) = false := by simpa using hcon
        have hnest := (keep_norm_false_iff _ _).1 hf
        obtain ⟨-, hL⟩ := hnest
        have h1 := (nestedL_iff_keep S _).2 hL (AR.charF Finset.card k0) (List.mem_map.2 ⟨k0, hk0, rfl⟩)
        have h2 := kid_keep (hkids k0 hk0) (hkp k0 hk0)
        rw [h1] at h2
        exact absurd h2 (by simp)
    have hwidwin : Y.card ≤ maxEntry (norm (CT.node (insert v S)
        (plus1 (((typical (csz ns)).take (cHi c2 + 1)).drop (preLo pre)))
        [CT.node S ((typical (csz ns)).drop (cLo c2)) (ks.map (AR.charF Finset.card))])) := by
      rcases hvb Y hY hvY with ⟨m, hm, rfl⟩ | ⟨k', hk', hYk⟩
      · have h1 : (insert v m.bag).card ∈ csz (M.map (av v)) := mem_csz (List.mem_map_of_mem hm)
        have h2 := le_maxOf h1
        rw [← maxOf_typical] at h2
        refine h2.trans ((dom_maxOf_le hMq).trans (maxOf_le fun e he => norm_y_le hkeep he))
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hk'
        exact absurd ((RT.mem_verts_iff _ v).2 ⟨Y, hYk, hvY⟩) (hkfree k hk)
    cases pre with
    | none => exact hwidwin
    | some c1 =>
      refine hwidwin.trans (norm_kid_le (K := [_]) (List.mem_singleton_self _) ?_)
      exact keep_of_mem_verts (by simp [CT.verts_node]) (fun h => hvB (hSB h))
  · -- vrep
    cases pre with
    | none => simp [topRep, CT.verts_node]
    | some c1 =>
      simp only [topRep]
      exact CT.mem_verts.2 (Or.inr ⟨_, List.mem_singleton_self _,
        CT.mem_verts.2 (Or.inl (Finset.mem_insert_self _ _))⟩)
  · -- nest
    intro hpre σ hσ hN
    have hpre' : pre = none := by cases pre <;> simp_all
    subst hpre'
    simp only [topRep] at hN
    obtain ⟨h1, h2, -⟩ := hN
    apply hσ
    rw [AR.charF_run]
    refine ⟨?_, h2.2⟩
    intro z hz
    have := h1 (Finset.mem_insert_of_mem hz)
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hSB hz) hvB
    · exact h3

end Lax117284Proofs.Treewidth.Chars
