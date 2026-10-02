import Lax117284Proofs.Treewidth.Chars.RealizeSeq
import Lax117284Proofs.Treewidth.Chars.AnalyzeRT

/-!
# The chain surgery of `applyPlan`, in coordinates (work package C5, part 2)

`processRun` cuts the chain of a run (at most twice: an optional *pre-cut* and an *end-cut*), then adds `v` to the nodes
between the two cuts.  Here we compute the resulting chain in the coordinates of `RealizeSeq`:

* `DupOf ns ns'` — `ns'` arises from `ns` by inserting copies (same bag, no junk) after some nodes (`dupAfter`);
* `processRun_chain` — the new chain is `L ++ M.map av ++ R` where `L ++ M ++ R` is a `DupOf` of the old chain and the
  bag sizes of `L`, `M`, `R` are `s.take a₁`, `(s.drop b₁).take (a₂ - b₁)`, `s.drop b₂` for the coordinates of the cuts.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees CT

/-- The bag sizes of a chain. -/
def csz (ns : List CNode) : List ℕ := ns.map (fun n => n.bag.card)

/-- Add the vertex `v` to the bag of a node. -/
def av (v : ℕ) (n : CNode) : CNode := ⟨insert v n.bag, n.junk⟩

/-! ## `dupAfter` -/

theorem dupAfter_of_lt {i : ℕ} {ns : List CNode} (hi : i < ns.length) :
    dupAfter i ns = ns.take (i + 1) ++ [⟨ns[i].bag, []⟩] ++ ns.drop (i + 1) := by
  unfold dupAfter
  rw [List.getElem?_eq_getElem hi]

theorem length_dupAfter (i : ℕ) (ns : List CNode) (hi : i < ns.length) :
    (dupAfter i ns).length = ns.length + 1 := by
  rw [dupAfter_of_lt hi]; simp; omega

theorem dupAfter_of_ge {i : ℕ} {ns : List CNode} (hi : ns.length ≤ i) : dupAfter i ns = ns := by
  unfold dupAfter
  rw [List.getElem?_eq_none hi]

theorem csz_dupAfter {i : ℕ} {ns : List CNode} (hi : i < ns.length) :
    csz (dupAfter i ns) = (csz ns).take (i + 1) ++ (csz ns).drop i := by
  unfold csz
  rw [dupAfter_of_lt hi]
  simp only [List.map_append, List.map_cons, List.map_nil, ← List.map_take, ← List.map_drop]
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.map_cons, List.singleton_append, List.append_assoc]

/-- `ns'` arises from `ns` by inserting copies. -/
inductive DupOf (ns : List CNode) : List CNode → Prop
  | refl : DupOf ns ns
  | dup {ns' : List CNode} (i : ℕ) : DupOf ns ns' → DupOf ns (dupAfter i ns')

theorem DupOf.length_ge {ns ns' : List CNode} (h : DupOf ns ns') : ns.length ≤ ns'.length := by
  induction h with
  | refl => exact le_rfl
  | @dup ns' i _ ih =>
    by_cases hi : i < ns'.length
    · rw [length_dupAfter i ns' hi]; omega
    · rw [dupAfter_of_ge (by omega)]; exact ih

/-- Every node of a duplicated chain is an old node or a junk-free copy of one. -/
theorem DupOf.mem {ns ns' : List CNode} (h : DupOf ns ns') :
    ∀ n ∈ ns', n ∈ ns ∨ ∃ n0 ∈ ns, n = ⟨n0.bag, []⟩ := by
  induction h with
  | refl => intro n hn; exact Or.inl hn
  | @dup ns' i _ ih =>
    intro n hn
    unfold dupAfter at hn
    cases hh : ns'[i]? with
    | none => rw [hh] at hn; exact ih n hn
    | some m =>
      rw [hh] at hn
      simp only [List.mem_append, List.mem_singleton] at hn
      rcases hn with (hn | rfl) | hn
      · exact ih n (List.mem_of_mem_take hn)
      · rcases ih m (List.mem_of_getElem? hh) with h1 | ⟨n0, hn0, rfl⟩
        · exact Or.inr ⟨m, h1, rfl⟩
        · exact Or.inr ⟨n0, hn0, rfl⟩
      · exact ih n (List.mem_of_mem_drop hn)

/-! ## `cutAt` -/

theorem csz_cutAt_t1 (y w : List ℕ) (f : ℕ) {ns : List CNode} (hi : w.getD f 0 < ns.length) :
    csz (cutAt y w (Cut.t1 f) ns).1 = (csz ns).take (w.getD f 0 + 1) ++ (csz ns).drop (w.getD f 0) := by
  simp only [cutAt]
  exact csz_dupAfter hi

theorem cutAt_t2_fst (y w : List ℕ) (f : ℕ) (ns : List CNode) : (cutAt y w (Cut.t2 f) ns).1 = ns := rfl

theorem DupOf_cutAt {ns ns' : List CNode} (h : DupOf ns ns') (y w : List ℕ) (c : Cut) :
    DupOf ns (cutAt y w c ns').1 := by
  cases c with
  | t1 f => exact DupOf.dup _ h
  | t2 f => exact h

/-- Coordinates: the size list of the cut chain. -/
theorem csz_cutAt {s : List ℕ} (hs : s ≠ []) {c : Cut} (hc : c.Valid (witnesses s).length) {ns : List CNode}
    (hns : s.length ≤ ns.length) :
    csz (cutAt (typical s) (witnesses s) c ns).1 = (csz ns).take (cA s c) ++ (csz ns).drop (cB s c) := by
  cases c with
  | t1 f =>
    have := Wf_lt hs (f := f) hc
    exact csz_cutAt_t1 (typical s) (witnesses s) f (by
      show Wf s f < ns.length
      omega)
  | t2 f =>
    simp only [cutAt, cA, cB]
    rw [List.take_append_drop]

/-- The index returned by a cut. -/
theorem cutAt_snd {s : List ℕ} (c : Cut) (ns : List CNode) :
    (cutAt (typical s) (witnesses s) c ns).2 + 1 = cA s c := by
  cases c with
  | t1 f => simp [cutAt, cA, Wf]
  | t2 f => simp [cutAt, cA, leftEnd2, Wf, Yf]

/-! ## `addV` -/

theorem addV_some (v : ℕ) {st e : ℕ} (ns : List CNode) (h1 : st ≤ e + 1) (h2 : e + 1 ≤ ns.length) :
    addV v st (some e) ns = ns.take st ++ ((ns.drop st).take (e + 1 - st)).map (av v) ++ ns.drop (e + 1) := by
  apply List.ext_getElem?
  intro k
  unfold addV
  rw [List.getElem?_mapIdx]
  have hlA : (ns.take st).length = st := by simp; omega
  have hlM : (((ns.drop st).take (e + 1 - st)).map (av v)).length = e + 1 - st := by simp; omega
  have hlAM : (ns.take st ++ ((ns.drop st).take (e + 1 - st)).map (av v)).length = e + 1 := by
    rw [List.length_append, hlA, hlM]; omega
  by_cases hk1 : k < st
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega),
      List.getElem?_take_of_lt hk1]
    cases hh : ns[k]? with
    | none => simp
    | some n =>
      simp only [Option.map_some]
      rw [if_neg (by simp; omega)]
  · by_cases hk2 : k < e + 1
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
      rw [hlA, List.getElem?_map, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
      have : st + (k - st) = k := by omega
      rw [this]
      cases hh : ns[k]? with
      | none => simp
      | some n =>
        simp only [Option.map_some, Option.map]
        rw [if_pos (by simp; omega)]
        rfl
    · rw [List.getElem?_append_right (by omega)]
      rw [hlAM]
      rw [List.getElem?_drop]
      have : e + 1 + (k - (e + 1)) = k := by omega
      rw [this]
      cases hh : ns[k]? with
      | none => simp
      | some n =>
        simp only [Option.map_some]
        rw [if_neg (by simp; omega)]

theorem addV_none (v : ℕ) {st : ℕ} (ns : List CNode) :
    addV v st none ns = ns.take st ++ (ns.drop st).map (av v) := by
  apply List.ext_getElem?
  intro k
  unfold addV
  rw [List.getElem?_mapIdx]
  by_cases hkl : k < ns.length
  · by_cases hk1 : k < st
    · have hlA : (ns.take st).length = min st ns.length := by simp
      rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hk1,
        List.getElem?_eq_getElem hkl]
      simp only [Option.map_some]
      rw [if_neg (by simp; omega)]
    · have hlA : (ns.take st).length = min st ns.length := by simp
      have hlA' : (ns.take st).length = st := by omega
      rw [List.getElem?_append_right (by omega), hlA', List.getElem?_map, List.getElem?_drop]
      have : st + (k - st) = k := by omega
      rw [this, List.getElem?_eq_getElem hkl]
      simp only [Option.map_some, Option.map]
      rw [if_pos (by simp; omega)]
      rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp only [Option.map_none]
    symm
    rw [List.getElem?_eq_none]
    simp; omega


/-! ## `processRun`: the chain in coordinates -/

/-- Coordinates `(a₁, b₁)` of the pre-cut. -/
def preAB (s : List ℕ) : Option Cut → ℕ × ℕ
  | none => (0, 0)
  | some c => (cA s c, cB s c)

/-- Coordinates `(a₂, b₂)` of the end of the region. -/
def endAB (s : List ℕ) : WPlan → ℕ × ℕ
  | .endAt c => (cA s c, cB s c)
  | .whole _ => (s.length, s.length)

def PreOk (m : ℕ) : Option Cut → Prop
  | none => True
  | some c => c.Valid m

def WOk (m : ℕ) : WPlan → Prop
  | .endAt c => c.Valid m
  | .whole _ => True

/-- The region starts (in `y`) no later than it ends. -/
def LoHi : Option Cut → WPlan → Prop
  | some c1, .endAt c2 => cLo c1 ≤ cHi c2
  | _, _ => True

theorem comp_cuts (s : List ℕ) {a1 b1 a2 b2 : ℕ} (h1 : b1 ≤ a1) (h2 : a1 ≤ a2) (h3 : a2 ≤ s.length) :
    (s.take a2 ++ s.drop b2).take a1 ++ (s.take a2 ++ s.drop b2).drop b1 =
      s.take a1 ++ (s.drop b1).take (a2 - b1) ++ s.drop b2 := by
  have hl : (s.take a2).length = a2 := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
    List.take_take, List.drop_take, Nat.min_eq_left h2]
  simp [List.append_assoc]

theorem coords_ok {s : List ℕ} (hs : s ≠ []) {pre : Option Cut} {w : WPlan}
    (hp : PreOk (witnesses s).length pre) (hw : WOk (witnesses s).length w) (hlh : LoHi pre w) :
    (preAB s pre).2 ≤ (preAB s pre).1 ∧ (preAB s pre).1 ≤ (preAB s pre).2 + 1 ∧
    (preAB s pre).2 + 1 ≤ (endAB s w).1 ∧ (preAB s pre).1 ≤ (endAB s w).1 ∧
    (endAB s w).1 ≤ s.length ∧ (endAB s w).2 ≤ s.length ∧ (endAB s w).2 ≤ (endAB s w).1 := by
  have hn : 0 < s.length := List.length_pos_of_ne_nil hs
  cases pre with
  | none =>
    cases w with
    | endAt c2 =>
      have := cA_pos (s := s) c2
      have := cA_le hs hw
      have := cB_le_cA (s := s) c2
      simp only [preAB, endAB]; omega
    | whole ps => simp only [preAB, endAB]; omega
  | some c1 =>
    have hc1 : c1.Valid (witnesses s).length := hp
    have := cB_le_cA (s := s) c1
    cases w with
    | endAt c2 =>
      have hm := dom_mid hs hc1 hw hlh
      have := cA_le hs hw
      have := cB_le_cA (s := s) c2
      simp only [preAB, endAB]; omega
    | whole ps =>
      have := cB_lt hs hc1
      have := cA_le hs hc1
      simp only [preAB, endAB]; omega

theorem csz_exists_pieces {ns : List CNode} {A M R : List ℕ} (h : csz ns = A ++ M ++ R) :
    ∃ L M' R', ns = L ++ M' ++ R' ∧ csz L = A ∧ csz M' = M ∧ csz R' = R := by
  unfold csz at h
  obtain ⟨l12, R', rfl, h12, hR⟩ := List.map_eq_append_iff.1 h
  obtain ⟨L, M', rfl, hL, hM⟩ := List.map_eq_append_iff.1 h12
  exact ⟨L, M', R', rfl, hL, hM, hR⟩


/-- The end index of the region (in the chain after both cuts), if it does not extend to the end. -/
def regionEnd (s : List ℕ) (pre : Option Cut) : WPlan → Option ℕ
  | .endAt c => some ((cA s c) + ((preAB s pre).1 - (preAB s pre).2) - 1)
  | .whole _ => none

/-- The chain computation of `processRun`, factored out. -/
def prStep (pre : Option Cut) (w : WPlan) (ns : List CNode) : List CNode × ℕ × Option ℕ :=
  let y := typical (csz ns)
  let wp := witnesses (csz ns)
  let endStep : List CNode × Option ℕ := match w with
    | .endAt c => ((cutAt y wp c ns).1, some (cutAt y wp c ns).2)
    | .whole _ => (ns, none)
  match pre with
  | none => (endStep.1, 0, endStep.2)
  | some c => ((cutAt y wp c endStep.1).1, (cutAt y wp c endStep.1).2 + 1,
      if c.isT1 then endStep.2.map (· + 1) else endStep.2)

theorem processRun_eq (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    processRun v pre w (.run S ns ks) = .run S
      (addV v (prStep pre w ns).2.1 (prStep pre w ns).2.2 (prStep pre w ns).1)
      (match w with
        | .endAt _ => ks
        | .whole ps => applyKids v ps ks) := by
  cases w <;> cases pre <;> (simp only [processRun, prStep]; try rfl)

theorem processRun_chain_eq (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    (processRun v pre w (.run S ns ks)).chain =
      addV v (prStep pre w ns).2.1 (prStep pre w ns).2.2 (prStep pre w ns).1 := by
  rw [processRun_eq]; rfl

theorem processRun_S (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode) (ks : List AR) :
    (processRun v pre w (.run S ns ks)).S = S := by
  rw [processRun_eq]; rfl

theorem cA_sub_cB_t1 (s : List ℕ) (f : ℕ) : cA s (Cut.t1 f) - cB s (Cut.t1 f) = 1 := by simp [cA, cB]
theorem cA_sub_cB_t2 (s : List ℕ) (f : ℕ) : cA s (Cut.t2 f) - cB s (Cut.t2 f) = 0 := by simp [cA, cB]

theorem prStep_spec (pre : Option Cut) (w : WPlan) (ns : List CNode) (hne : ns ≠ [])
    (hp : PreOk (witnesses (csz ns)).length pre) (hw : WOk (witnesses (csz ns)).length w) (hlh : LoHi pre w) :
    ∃ ns2, (prStep pre w ns).1 = ns2 ∧ (prStep pre w ns).2.1 = (preAB (csz ns) pre).1 ∧
      (prStep pre w ns).2.2 = regionEnd (csz ns) pre w ∧ DupOf ns ns2 ∧
      csz ns2 = (csz ns).take (preAB (csz ns) pre).1 ++
        ((csz ns).drop (preAB (csz ns) pre).2).take ((endAB (csz ns) w).1 - (preAB (csz ns) pre).2) ++
        (csz ns).drop (endAB (csz ns) w).2 := by
  have hs : csz ns ≠ [] := by
    intro h; apply hne; unfold csz at h
    exact List.map_eq_nil_iff.1 h
  have hco := coords_ok hs hp hw hlh
  have hlen : (csz ns).length = ns.length := by simp [csz]
  cases pre with
  | none =>
    cases w with
    | endAt c2 =>
      have hc2 : c2.Valid (witnesses (csz ns)).length := hw
      have e2 := cutAt_snd (s := csz ns) c2 ns
      have h1 := cA_pos (s := csz ns) c2
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1, rfl, rfl, ?_,
        DupOf_cutAt DupOf.refl _ _ c2, ?_⟩
      · simp only [prStep, regionEnd, preAB]
        congr 1
        omega
      · rw [csz_cutAt hs hc2 (by omega)]
        simp only [preAB, endAB, List.take_zero, List.drop_zero, List.nil_append, Nat.sub_zero]
    | whole ps =>
      refine ⟨ns, rfl, rfl, rfl, DupOf.refl, ?_⟩
      simp only [preAB, endAB, List.take_zero, List.drop_zero, List.nil_append, Nat.sub_zero,
        List.take_length, List.drop_length, List.append_nil]
  | some c1 =>
    have hc1 : c1.Valid (witnesses (csz ns)).length := hp
    obtain ⟨hb1, hab1, hba, ha12, ha2, hb2, hb2a⟩ := hco
    simp only [preAB] at hb1 hab1 hba ha12
    cases w with
    | endAt c2 =>
      have hc2 : c2.Valid (witnesses (csz ns)).length := hw
      have hs1 : csz (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1 =
          (csz ns).take (cA (csz ns) c2) ++ (csz ns).drop (cB (csz ns) c2) :=
        csz_cutAt hs hc2 (by omega)
      have hlen1 : (csz ns).length ≤ (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1.length :=
        (hlen.le.trans (DupOf_cutAt DupOf.refl (typical (csz ns)) (witnesses (csz ns)) c2).length_ge)
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c1
          (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1).1, rfl, ?_, ?_,
        DupOf_cutAt (DupOf_cutAt DupOf.refl _ _ c2) _ _ c1, ?_⟩
      · have e1 := cutAt_snd (s := csz ns) c1 (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1
        simp only [prStep, preAB]
        omega
      · have e2 := cutAt_snd (s := csz ns) c2 ns
        have e1 := cutAt_snd (s := csz ns) c1 (cutAt (typical (csz ns)) (witnesses (csz ns)) c2 ns).1
        have h1 := cA_pos (s := csz ns) c2
        have hc := cB_le_cA (s := csz ns) c1
        simp only [prStep, regionEnd, preAB]
        cases c1 with
        | t1 f =>
          simp only [Cut.isT1, if_true, Option.map_some]
          rw [cA_sub_cB_t1]
          congr 1 <;> omega
        | t2 f =>
          simp only [Cut.isT1, Bool.false_eq_true, if_false]
          rw [cA_sub_cB_t2]
          congr 1 <;> omega
      · rw [csz_cutAt hs hc1 hlen1, hs1]
        simp only [preAB, endAB]
        exact comp_cuts (csz ns) hb1 ha12 ha2
    | whole ps =>
      refine ⟨(cutAt (typical (csz ns)) (witnesses (csz ns)) c1 ns).1, rfl, ?_, ?_,
        DupOf_cutAt DupOf.refl _ _ c1, ?_⟩
      · have e1 := cutAt_snd (s := csz ns) c1 ns
        simp only [prStep, preAB]
        omega
      · simp only [prStep, regionEnd, preAB]
        cases c1 <;> simp [Cut.isT1]
      · rw [csz_cutAt hs hc1 hlen.le]
        have := comp_cuts (csz ns) (a1 := cA (csz ns) c1) (b1 := cB (csz ns) c1) (a2 := (csz ns).length)
          (b2 := (csz ns).length) hb1 ha12 (le_refl _)
        simp only [preAB, endAB, List.take_length, List.drop_length, List.append_nil] at this ⊢
        simpa using this


theorem addV_pieces_some (v : ℕ) (L M R : List CNode) {e : ℕ} (h : L.length + M.length = e + 1) :
    addV v L.length (some e) (L ++ M ++ R) = L ++ M.map (av v) ++ R := by
  rw [addV_some v _ (by omega) (by simp; omega)]
  have e1 : (L ++ M ++ R).take L.length = L := by
    rw [List.append_assoc, List.take_left']; rfl
  have e2 : (L ++ M ++ R).drop L.length = M ++ R := by
    rw [List.append_assoc, List.drop_left']; rfl
  have e3 : (M ++ R).take (e + 1 - L.length) = M := by
    rw [show e + 1 - L.length = M.length by omega, List.take_left']; rfl
  have e4 : (L ++ M ++ R).drop (e + 1) = R := by
    rw [← h, ← List.length_append, List.drop_left']; rfl
  rw [e1, e2, e3, e4]

theorem addV_pieces_none (v : ℕ) (L M : List CNode) :
    addV v L.length none (L ++ M) = L ++ M.map (av v) := by
  rw [addV_none, List.take_left' rfl, List.drop_left' rfl]

theorem csz_length (ns : List CNode) : (csz ns).length = ns.length := by simp [csz]

theorem processRun_chain (v : ℕ) (pre : Option Cut) (w : WPlan) (S : Finset ℕ) (ns : List CNode)
    (ks : List AR) (hne : ns ≠ []) (hp : PreOk (witnesses (csz ns)).length pre)
    (hw : WOk (witnesses (csz ns)).length w) (hlh : LoHi pre w) :
    ∃ L M R ns2 st re, DupOf ns ns2 ∧ ns2 = L ++ M ++ R ∧
      (processRun v pre w (.run S ns ks)).chain = addV v st re ns2 ∧
      (processRun v pre w (.run S ns ks)).chain = L ++ M.map (av v) ++ R ∧
      csz L = (csz ns).take (preAB (csz ns) pre).1 ∧
      csz M = ((csz ns).drop (preAB (csz ns) pre).2).take ((endAB (csz ns) w).1 - (preAB (csz ns) pre).2) ∧
      csz R = (csz ns).drop (endAB (csz ns) w).2 ∧
      M ≠ [] ∧ (pre = none → L = []) ∧ (pre ≠ none → L ≠ []) ∧
      (∀ ps, w = .whole ps → R = []) ∧ (∀ c, w = .endAt c → R ≠ []) := by
  have hs : csz ns ≠ [] := by
    intro h; apply hne; unfold csz at h
    exact List.map_eq_nil_iff.1 h
  have hco := coords_ok hs hp hw hlh
  obtain ⟨b1a1, a1b1, hba, ha12, ha2, hb2, hb2a⟩ := hco
  obtain ⟨ns2, h1, h2, h3, hdup, hcsz⟩ := prStep_spec pre w ns hne hp hw hlh
  obtain ⟨L, M, R, rfl, hL, hM, hR⟩ := csz_exists_pieces hcsz
  have hlenL : L.length = (preAB (csz ns) pre).1 := by
    rw [← csz_length L, hL]; simp; omega
  have hlenM : M.length = (endAB (csz ns) w).1 - (preAB (csz ns) pre).2 := by
    rw [← csz_length M, hM]; simp; omega
  have hlenR : R.length = (csz ns).length - (endAB (csz ns) w).2 := by
    rw [← csz_length R, hR]; simp
  refine ⟨L, M, R, L ++ M ++ R, (preAB (csz ns) pre).1, regionEnd (csz ns) pre w, hdup, rfl, ?_, ?_, hL, hM, hR,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [processRun_chain_eq, h1, h2, h3]
  · rw [processRun_chain_eq, h1, h2, h3, ← hlenL]
    cases w with
    | endAt c2 =>
      simp only [regionEnd]
      apply addV_pieces_some
      simp only [endAB] at hlenM b1a1 a1b1 hba ha12 ha2 hb2 hb2a ⊢
      omega
    | whole ps =>
      simp only [regionEnd]
      have hR0 : R = [] := by
        rw [← List.length_eq_zero_iff, hlenR]; simp [endAB]
      subst hR0
      simpa using addV_pieces_none v L M
  · rw [← List.length_pos_iff, hlenM]; omega
  · intro h; subst h
    rw [← List.length_eq_zero_iff, hlenL]; rfl
  · intro h
    rw [← List.length_pos_iff, hlenL]
    cases pre with
    | none => exact absurd rfl h
    | some c => simp only [preAB]; exact cA_pos c
  · intro ps hps; subst hps
    rw [← List.length_eq_zero_iff, hlenR]; simp [endAB]
  · intro c hc; subst hc
    rw [← List.length_pos_iff, hlenR]
    have := cB_lt hs (c := c) hw
    simp only [endAB]; omega

end Lax117284Proofs.Treewidth.Chars
