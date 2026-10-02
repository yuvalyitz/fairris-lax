import Lax117284Proofs.Treewidth.Chars.RealizeEnd

/-!
# The whole-case of the region step (work package C5, part 9)

`kc_agg`: the aggregated invariants of a list of kids, processed or not; `pr_whole`: `processRun v pre (whole ps)`
realises the plan `top pre (whole ps)`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

section Agg

variable {v : ℕ} {B : Finset ℕ}

theorem kc_agg {ks : List AR} {combo : List (Option WPlan × CT × Finset ℕ)}
    (hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo) :
    List.Forall₂ (TI v) (ks.map AR.toRT) ((applyKids v (combo.map (·.1)) ks).map AR.toRT) ∧
    tcL v ((applyKids v (combo.map (·.1)) ks).map AR.toRT) true = 0 ∧
    (∃ Qs : List CT, Qs.map norm = (((applyKids v (combo.map (·.1)) ks).map AR.toRT).map (RT.prof (insert v B))).map norm ∧
      DomCL Qs (combo.map (·.2.1))) ∧
    (∀ Y (k' : AR), k' ∈ applyKids v (combo.map (·.1)) ks → Y ∈ (AR.toRT k').bags → v ∈ Y →
      ∃ r ∈ combo.map (·.2.1), Y.card ≤ maxEntry (norm r)) ∧
    (∀ u ∈ combo.foldl (fun a c => a ∪ c.2.2) ∅,
      ∃ k' ∈ applyKids v (combo.map (·.1)) ks, ∃ Y ∈ (AR.toRT k').bags, v ∈ Y ∧ u ∈ Y) ∧
    List.Forall₂ (fun k r => ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) r) ks (combo.map (·.2.1)) := by
  induction hkc with
  | nil =>
    simp only [List.map_nil, applyKids]
    refine ⟨List.Forall₂.nil, rfl, ⟨[], rfl, trivial⟩, ?_, ?_, List.Forall₂.nil⟩
    · intro Y k' hk'; simp at hk'
    · intro u hu; simp at hu
  | @cons k o ks combo hk hrest ih =>
    obtain ⟨ih1, ih2, ⟨Qs, ih3, ih3'⟩, ih4, ih5, ih6⟩ := ih
    simp only [List.map_cons, applyKids]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.Forall₂.cons hk.ti ih1
    · rw [tcL, hk.tcv, ih2]
    · obtain ⟨Q, hQ1, hQ2⟩ := hk.chr
      refine ⟨Q :: Qs, ?_, ⟨hQ2, ih3'⟩⟩
      simp only [List.map_cons]
      rw [hQ1, ih3]
    · intro Y k' hk' hY hvY
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨o.2.1, List.mem_cons_self, hk.wid Y hY hvY⟩
      · obtain ⟨r, hr, h⟩ := ih4 Y k' hk' hY hvY
        exact ⟨r, List.mem_cons_of_mem _ hr, h⟩
    · intro u hu
      rw [List.foldl_cons] at hu
      have hfold : ∀ (S0 : Finset ℕ) (l : List (Option WPlan × CT × Finset ℕ)),
          l.foldl (fun a c => a ∪ c.2.2) S0 = S0 ∪ l.foldl (fun a c => a ∪ c.2.2) ∅ := by
        intro S0 l
        induction l generalizing S0 with
        | nil => simp
        | cons c l ih' =>
          simp only [List.foldl_cons]
          rw [ih' (S0 ∪ c.2.2), ih' (∅ ∪ c.2.2)]
          simp [Finset.union_assoc]
      rw [hfold] at hu
      simp only [Finset.empty_union, Finset.mem_union] at hu
      rcases hu with hu | hu
      · obtain ⟨Y, hY, hvY, huY⟩ := hk.cov u hu
        exact ⟨applyOpt v o.1 k, List.mem_cons_self, Y, hY, hvY, huY⟩
      · obtain ⟨k', hk', h⟩ := ih5 u (by simpa using hu)
        exact ⟨k', List.mem_cons_of_mem _ hk', h⟩
    · exact List.Forall₂.cons hk.nest ih6

theorem nestedL_of_forall2 {S : Finset ℕ} {ks : List AR} {rs : List CT}
    (h : List.Forall₂ (fun k r => ∀ σ, ¬ Nested σ (AR.charF Finset.card k) → ¬ Nested (insert v σ) r) ks rs)
    (hN : NestedL (insert v S) rs) : NestedL S (ks.map (AR.charF Finset.card)) := by
  induction h with
  | nil => trivial
  | @cons k r ks rs hkr _ ih =>
    obtain ⟨h1, h2⟩ := hN
    refine ⟨?_, ih h2⟩
    by_contra hcon
    exact hkr S hcon h1

end Agg


theorem toRT_processRun_whole (v : ℕ) (pre : Option Cut) (ps : List (Option WPlan)) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) :
    AR.toRT (processRun v pre (.whole ps) (.run S ns ks)) =
      AR.chainToRT (processRun v pre (.whole ps) (.run S ns ks)).chain ((applyKids v ps ks).map AR.toRT) := by
  have h : processRun v pre (.whole ps) (.run S ns ks) =
      .run S (processRun v pre (.whole ps) (.run S ns ks)).chain (applyKids v ps ks) := by
    rw [processRun_chain_eq, processRun_eq]
  conv_lhs => rw [h]
  rw [AR.toRT_run]

theorem pr_whole (v : ℕ) (B S : Finset ℕ) (ns : List CNode) (ks : List AR) (hvB : v ∉ B)
    (hx : RunOk v B (.run S ns ks)) (pre : Option Cut) (combo : List (Option WPlan × CT × Finset ℕ))
    (hpre : PreOk (typical (csz ns)).length pre)
    (hkc : List.Forall₂ (fun k o => KC v B k (applyOpt v o.1 k) o.2.1 o.2.2) ks combo) :
    PRC v B (.run S ns ks) (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks))
      (topRep S (typical (csz ns)) pre
        (CT.node (insert v S) (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1))))
      (combo.foldl (fun a c => a ∪ c.2.2) S) pre.isSome := by
  obtain ⟨hns, hbase, hkids, hleaf, hkp, hSB, hkfree⟩ := runOk_run hx
  have hs : csz ns ≠ [] := by
    intro h; apply hns; unfold csz at h; exact List.map_eq_nil_iff.1 h
  have hlenw : (witnesses (csz ns)).length = (typical (csz ns)).length := (witnesses_cover (csz ns)).len
  have hp' : PreOk (witnesses (csz ns)).length pre := by rw [hlenw]; exact hpre
  have hw' : WOk (witnesses (csz ns)).length (.whole (combo.map (·.1))) := trivial
  have hlh : LoHi pre (.whole (combo.map (·.1))) := by cases pre <;> exact trivial
  obtain ⟨L, M, R, ns2, st, re, hdup, hns2, hchainA, hchain, hcL, hcM, hcR, hMne, hL0, hL1, hRw, hRe⟩ :=
    processRun_chain v pre (.whole (combo.map (·.1))) S ns ks hns hp' hw' hlh
  have hR0 : R = [] := hRw _ rfl
  subst hR0
  have hinfo := hdup.info
  have hMsub : ∀ m ∈ M, m ∈ (L ++ M ++ []) := fun n hn => by simp [hn]
  obtain ⟨hA1, hA2, ⟨Qs, hA3, hA3'⟩, hA4, hA5, hA6⟩ := kc_agg hkc
  obtain ⟨hTI, htc, hnorm, hvb, hmb⟩ := region_PRC v B S hvB (ns := ns) (L := L) (M := M) (R := []) (ks := ks)
    (K' := (applyKids v (combo.map (·.1)) ks).map AR.toRT) Qs
    (chain'' := (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks)).chain)
    hns hMne hbase (by rw [← hns2]; exact hdup) hchain (by
      obtain ⟨g, hg, he⟩ := addV_map v st re ns2
      exact ⟨g, hg, by rw [hchainA, he, hns2]⟩) hA1 (fun _ => hA2) (fun h => absurd rfl h) hA3
  rw [hchain] at hTI htc hnorm hvb hmb
  have hxt : AR.toRT (processRun v pre (.whole (combo.map (·.1))) (.run S ns ks)) =
      AR.chainToRT (L ++ M.map (av v) ++ []) ((applyKids v (combo.map (·.1)) ks).map AR.toRT) := by
    rw [toRT_processRun_whole, hchain]
  have hxo : AR.toRT (.run S ns ks) = AR.chainToRT ns (ks.map AR.toRT) := AR.toRT_run S ns ks
  have hMfree : ∀ m ∈ M, v ∉ m.bag := by
    intro m hm
    obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
    rw [hb]; exact (hbase n0 hn0).2.1
  -- dominance of the pieces
  have hM : Dom (typical (csz M)) ((typical (csz ns)).drop (preLo pre)) := by
    rw [hcM]
    cases pre with
    | none =>
      simp only [preAB, endAB, preLo, List.drop_zero, Nat.sub_zero, List.take_length]
      exact Dom.refl _
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have := dom_right hs hc1'
      have e : (csz ns).length - cB (csz ns) c1 = ((csz ns).drop (cB (csz ns) c1)).length := by simp
      simp only [preAB, endAB, preLo]
      rw [e, List.take_length]
      exact this
  have hMq : Dom (typical (csz (M.map (av v)))) (plus1 ((typical (csz ns)).drop (preLo pre))) := by
    rw [csz_map_av hMfree, typical_plus1]
    unfold plus1
    exact dom_map_succ hM
  have hwin : DomC (CT.node (insert v S) (typical (csz (M.map (av v)))) Qs)
      (CT.node (insert v S) (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1))) :=
    ⟨rfl, hMq, hA3'⟩
  -- kept kids
  have hkeepr : ∀ r ∈ combo.map (·.2.1), keep (insert v S) (norm r) = true := by
    intro r hr
    obtain ⟨k, hk, hkr⟩ := forall2_exists_right hA6 r hr
    have hkk := kid_keep (hkids k hk) (hkp k hk)
    have hnn : ¬ Nested S (AR.charF Finset.card k) := by
      intro hN
      have := (keep_norm_false_iff S _).2 hN
      rw [this] at hkk; exact absurd hkk (by simp)
    by_contra hcon
    have hf : keep (insert v S) (norm r) = false := by simpa using hcon
    exact hkr S hnn ((keep_norm_false_iff _ _).1 hf)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxt, hxo]; simpa using hTI
  · intro p
    rw [hxt, htc p]
    cases pre with
    | none => simp [hL0 rfl]
    | some c1 => simp [hL1 (by simp)]
  · rw [hxt]
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    exact (RT.mem_verts_iff _ v).2 ⟨insert v m.bag, by simpa using hmb m hm, Finset.mem_insert_self _ _⟩
  · intro u hu
    rw [hxt]
    have hfold : ∀ (S0 : Finset ℕ) (l : List (Option WPlan × CT × Finset ℕ)),
        l.foldl (fun a c => a ∪ c.2.2) S0 = S0 ∪ l.foldl (fun a c => a ∪ c.2.2) ∅ := by
      intro S0 l
      induction l generalizing S0 with
      | nil => simp
      | cons c l ih' =>
        simp only [List.foldl_cons]
        rw [ih' (S0 ∪ c.2.2), ih' (∅ ∪ c.2.2)]
        simp [Finset.union_assoc]
    rw [hfold, Finset.mem_union] at hu
    rcases hu with hu | hu
    · obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
      obtain ⟨n0, hn0, hb, -⟩ := hinfo m (by rw [hns2]; exact hMsub m hm)
      refine ⟨insert v m.bag, by simpa using hmb m hm, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
      have : u ∈ n0.bag ∩ B := by rw [(hbase n0 hn0).1]; exact hu
      rw [hb]; exact (Finset.mem_inter.1 this).1
    · obtain ⟨k', hk', Y, hY, hvY, huY⟩ := hA5 u hu
      refine ⟨Y, ?_, hvY, huY⟩
      have hne'' : (L ++ M.map (av v) ++ []) ≠ [] := by
        obtain ⟨m0, M', rfl⟩ := List.exists_cons_of_ne_nil hMne
        simp
      rw [mem_bags_chainToRT _ _ hne'']
      exact Or.inr (Or.inr ⟨AR.toRT k', List.mem_map.2 ⟨k', hk', rfl⟩, hY⟩)
  · -- chr
    refine ⟨regionQ v S L M [] Qs, by rw [hxt]; exact hnorm, ?_⟩
    cases pre with
    | none =>
      simp only [regionQ, hL0 rfl, topRep]
      simpa using hwin
    | some c1 =>
      have hc1' : c1.Valid (witnesses (csz ns)).length := hp'
      have hL : Dom (typical (csz L)) ((typical (csz ns)).take (cHi c1 + 1)) := by
        rw [hcL]; simpa [preAB] using dom_left hs hc1'
      have hLne : L ≠ [] := hL1 (by simp)
      simp only [regionQ, if_neg hLne, topRep]
      simp only [if_true]
      exact ⟨rfl, hL, ⟨hwin, trivial⟩⟩
  · -- wid
    intro Y hY hvY
    rw [hxt] at hY
    have hkeep : (∃ k ∈ combo.map (·.2.1), keep (insert v S) (norm k) = true) ∨
        (plus1 ((typical (csz ns)).drop (preLo pre))).length ≤ 1 := by
      by_cases hka : ks = []
      · right
        have h1 : ns.length = 1 := hleaf hka
        have hy1 : (typical (csz ns)).length ≤ 1 := by
          obtain ⟨x0, hx0⟩ : ∃ x0, csz ns = [x0] := by
            have : (csz ns).length = 1 := by rw [csz_length]; exact h1
            exact List.length_eq_one_iff.1 this
          rw [hx0, typical_singleton]; simp
        simp only [plus1, List.length_map, List.length_drop]
        omega
      · left
        have hlen := hkc.length_eq
        have hne : combo.map (·.2.1) ≠ [] := by
          intro h
          have : combo = [] := by simpa using h
          rw [this] at hlen
          exact hka (List.length_eq_zero_iff.1 hlen)
        obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
        exact ⟨r, hr, hkeepr r hr⟩
    have hwidwin : Y.card ≤ maxEntry (norm (CT.node (insert v S)
        (plus1 ((typical (csz ns)).drop (preLo pre))) (combo.map (·.2.1)))) := by
      rcases hvb Y hY hvY with ⟨m, hm, rfl⟩ | ⟨k', hk', hYk⟩
      · have h1 : (insert v m.bag).card ∈ csz (M.map (av v)) := mem_csz (List.mem_map_of_mem hm)
        have h2 := le_maxOf h1
        rw [← maxOf_typical] at h2
        refine h2.trans ((dom_maxOf_le hMq).trans (maxOf_le fun e he => norm_y_le hkeep he))
      · obtain ⟨k'', hk'', rfl⟩ := List.mem_map.1 hk'
        obtain ⟨r, hr, hle⟩ := hA4 Y k'' hk'' hYk hvY
        exact hle.trans (norm_kid_le hr (hkeepr r hr))
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
    obtain ⟨h1, h2⟩ := hN
    apply hσ
    rw [AR.charF_run]
    refine ⟨?_, nestedL_of_forall2 hA6 h2⟩
    intro z hz
    have := h1 (Finset.mem_insert_of_mem hz)
    rcases Finset.mem_insert.1 this with rfl | h3
    · exact absurd (hSB hz) hvB
    · exact h3

end Lax117284Proofs.Treewidth.Chars
