import Lax117284Proofs.Treewidth.Fun.E5R

/-!
# WP E5 (layer D): `mergeChain`, `mergeAR`, `mergeKids`, `mergeReal`, `realJoin`

Ids `520 …`:

| id | function | arguments |
|---|---|---|
| 520 `fMergeChain` | `mergeChain` | `[na, nb, prev, path]` |
| 521 `fMergeAR` | `mergeAR` | `[a, b, target]` |
| 522 `fMergeKids` | `mergeKids` | `[ka, kb, tk]` |
| 523 `fMergeReal` | `mergeReal` | `[Bd, ta, tb, target]` |
| 524 `fPredJoin` | the predicate `fun d => domCB d target` of `realJoin` (context `target`) | `[target, d]` |
| 525 `fRealJoin` | `realJoin` | `[kmax, Bd, ta, tb, target]` |
| 526 `fFlagI` / 527 `fFlagJ` | the "first visit" flags of `mergeChain` | `[prev, i]` / `[prev, j]` |

The lattice path search is E1's `findPath` (id `E1D.fFindPath = 156`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Lax117284Proofs.Treewidth.Fun
namespace E5D

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

abbrev fMergeChain : ℕ := 520
abbrev fMergeAR : ℕ := 521
abbrev fMergeKids : ℕ := 522
abbrev fMergeReal : ℕ := 523
abbrev fPredJoin : ℕ := 524
abbrev fRealJoin : ℕ := 525
abbrev fFlagI : ℕ := 526
abbrev fFlagJ : ℕ := 527

/-! ## the Lean side -/

/-- first visit of the `a`-side node -/
abbrev flagI (prev : Option (ℕ × ℕ)) (i : ℕ) : Bool := prev.elim true (fun p => decide (p.1 ≠ i))
/-- first visit of the `b`-side node -/
abbrev flagJ (prev : Option (ℕ × ℕ)) (j : ℕ) : Bool := prev.elim true (fun p => decide (p.2 ≠ j))

/-- the default chain node of `mergeChain` -/
abbrev dflt : CNode := ⟨∅, []⟩

theorem mergeChain_cons (na nb : List CNode) (prev : Option (ℕ × ℕ)) (i j : ℕ) (rest : List (ℕ × ℕ)) :
    mergeChain na nb prev ((i, j) :: rest) =
      ⟨(na.getD i dflt).bag ∪ (nb.getD j dflt).bag,
        (if flagI prev i then (na.getD i dflt).junk else []) ++
          (if flagJ prev j then (nb.getD j dflt).junk else [])⟩ :: mergeChain na nb (some (i, j)) rest := rfl

/-- `path` has at most `|sa| + |sb|` steps -/
theorem findPath_len {sa sb : List ℕ} {c : ℕ} {want : List ℕ} {P : List (ℕ × ℕ)}
    (h : findPath sa sb c want = some P) : P.length ≤ sa.length + sb.length := by
  unfold findPath at h
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some hst
  have := E1D.latticeStates_path_length hm
  simpa using this

/-! ## the terms -/

/-- `[prev, i]` -/
def flagITm : Tm := .ite (.isNat (V 0)) (.lit 1) (.sub (.lit 1) (.eq (.fst (.snd (V 0))) (V 1)))
/-- `[prev, j]` -/
def flagJTm : Tm := .ite (.isNat (V 0)) (.lit 1) (.sub (.lit 1) (.eq (.snd (.snd (V 0))) (V 1)))

/-- `[na, nb, prev, path]` -/
def mergeChainTm : Tm :=
  .ite (.isNat (V 3)) (V 3)
    (.letE (.call fNthD [V 0, .fst (.fst (V 3)), .cons (.lit 0) (.lit 0)])
      (.letE (.call fNthD [V 2, .snd (.fst (V 4)), .cons (.lit 0) (.lit 0)])
        (.cons
          (.cons (.call Lib3.fUnionS [.fst (V 1), .fst (V 0)])
            (.call fAppend
              [.ite (.call fFlagI [V 4, .fst (.fst (V 5))]) (.snd (V 1)) (.lit 0),
               .ite (.call fFlagJ [V 4, .snd (.fst (V 5))]) (.snd (V 0)) (.lit 0)]))
          (.call fMergeChain [V 2, V 3, .cons (.lit 1) (.fst (V 5)), .snd (V 5)]))))

/-- `[a, b, target]` -/
def mergeARTm : Tm :=
  .letE (.call fCards [.fst (.snd (V 0))])
    (.letE (.call fCards [.fst (.snd (V 2))])
      (.letE (.call E1D.fFindPath [V 1, V 0, .call fLength [.fst (V 2)], .fst (.snd (V 4))])
        (.ite (.isNat (V 0)) (.lit 0)
          (.letE (.call fMergeKids [.snd (.snd (V 3)), .snd (.snd (V 4)), .snd (.snd (V 5))])
            (.ite (.isNat (V 0)) (.lit 0)
              (.cons (.lit 1)
                (.cons (.fst (V 4))
                  (.cons (.call fMergeChain [.fst (.snd (V 4)), .fst (.snd (V 5)), .lit 0, .snd (V 1)])
                    (.snd (V 0))))))))))

/-- `[ka, kb, tk]` -/
def mergeKidsTm : Tm :=
  .ite (.isNat (V 0))
    (.ite (.isNat (V 1)) (.ite (.isNat (V 2)) (.cons (.lit 1) (.lit 0)) (.lit 0)) (.lit 0))
    (.ite (.isNat (V 1)) (.lit 0)
      (.ite (.isNat (V 2)) (.lit 0)
        (.letE (.call fMergeAR [.fst (V 0), .fst (V 1), .fst (V 2)])
          (.ite (.isNat (V 0)) (.lit 0)
            (.letE (.call fMergeKids [.snd (V 1), .snd (V 2), .snd (V 3)])
              (.ite (.isNat (V 0)) (.lit 0)
                (.cons (.lit 1) (.cons (.snd (V 1)) (.snd (V 0))))))))))

/-- `[Bd, ta, tb, target]` -/
def mergeRealTm : Tm :=
  .letE (.call fMergeAR [.call E5B.fAnalyze [V 0, V 1], .call E5B.fAnalyze [V 0, V 2], V 3])
    (.ite (.isNat (V 0)) (.lit 0) (.cons (.lit 1) (.call E5A.fToRT [.snd (V 0)])))

/-- `[target, d]` -/
def predJoinTm : Tm := .call idDomC [V 1, V 0]

/-- `[kmax, Bd, ta, tb, target]` -/
def realJoinTm : Tm :=
  .letE (.call idJoinC [V 0, .call fChar [V 1, V 2], .call fChar [V 1, V 3]])
    (.letE (.call Lib4.fFind [.lit fPredJoin, V 5, V 0])
      (.ite (.isNat (V 0)) (.lit 0) (.call fMergeReal [V 3, V 4, V 5, .snd (V 0)])))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 520 => some mergeChainTm | 521 => some mergeARTm | 522 => some mergeKidsTm | 523 => some mergeRealTm
  | 524 => some predJoinTm | 525 => some realJoinTm | 526 => some flagITm | 527 => some flagJTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5R.Δ 520 tbl

abbrev size : ℕ := 528

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 528 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h520 : 520 ≤ f := by omega
    simp only [h520, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extR : E5R.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5R.Δ_lt h; simp [E5R.size] at this; omega)
theorem ext3 : E5C3.Δ ⊑ Δ := Ext.trans E5R.ext3 extR
theorem ext2 : E5C2.Δ ⊑ Δ := Ext.trans E5R.ext2 extR
theorem ext1 : E5C1.Δ ⊑ Δ := Ext.trans E5R.ext1 extR
theorem extB : E5B.Δ ⊑ Δ := Ext.trans E5R.extB extR
theorem extA : E5A.Δ ⊑ Δ := Ext.trans E5R.extA extR
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5R.extE1 extR

theorem Δ_mergeChain : Δ fMergeChain = some mergeChainTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeChain by decide)]; rfl
theorem Δ_mergeAR : Δ fMergeAR = some mergeARTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeAR by decide)]; rfl
theorem Δ_mergeKids : Δ fMergeKids = some mergeKidsTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeKids by decide)]; rfl
theorem Δ_mergeReal : Δ fMergeReal = some mergeRealTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fMergeReal by decide)]; rfl
theorem Δ_predJoin : Δ fPredJoin = some predJoinTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fPredJoin by decide)]; rfl
theorem Δ_realJoin : Δ fRealJoin = some realJoinTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fRealJoin by decide)]; rfl
theorem Δ_flagI : Δ fFlagI = some flagITm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fFlagI by decide)]; rfl
theorem Δ_flagJ : Δ fFlagJ = some flagJTm := by
  simp [Δ, layerΔ_ge tbl (show 520 ≤ fFlagJ by decide)]; rfl

/-! ## sizes -/

theorem sz_dflt : sz dflt = 3 := by
  simp only [dflt, sz_cnode, sz_finset]; simp [sz_nil]

theorem sz_mergeChain_le (na nb : List CNode) : ∀ (P : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    sz (mergeChain na nb prev P) ≤ P.length * (sz na + sz nb + 8) + 1
  | [], _ => by simp [mergeChain]
  | (i, j) :: rest, prev => by
    have ih := sz_mergeChain_le na nb rest (some (i, j))
    rw [mergeChain_cons]
    have h1 := sz_getD_le na i dflt
    have h2 := sz_getD_le nb j dflt
    have h3 := sz_dflt
    have hA : sz (na.getD i dflt) = sz (na.getD i dflt).bag + sz (na.getD i dflt).junk + 1 :=
      sz_cnode _ _
    have hB : sz (nb.getD j dflt) = sz (nb.getD j dflt).bag + sz (nb.getD j dflt).junk + 1 :=
      sz_cnode _ _
    have h4 := sz_union_le (na.getD i dflt).bag (nb.getD j dflt).bag
    have h5 := sz_append_le (if flagI prev i then (na.getD i dflt).junk else [])
      (if flagJ prev j then (nb.getD j dflt).junk else [])
    have h6 : sz (if flagI prev i then (na.getD i dflt).junk else []) ≤ sz (na.getD i dflt).junk := by
      split_ifs
      · exact le_refl _
      · have : sz ([] : List RT) = 1 := rfl; have := sz_pos (na.getD i dflt).junk; omega
    have h7 : sz (if flagJ prev j then (nb.getD j dflt).junk else []) ≤ sz (nb.getD j dflt).junk := by
      split_ifs
      · exact le_refl _
      · have : sz ([] : List RT) = 1 := rfl; have := sz_pos (nb.getD j dflt).junk; omega
    simp only [sz_cons, sz_cnode, List.length_cons]
    have := sz_pos (na.getD i dflt).junk
    have := sz_pos (nb.getD j dflt).junk
    nlinarith


/-! ## size of the merged analysis -/

theorem arith_merge (Yc Wl sS Y : ℕ) (hY : Yc + Wl + sS + 4 ≤ Y) :
    sS + Yc * (Yc + 8) + 3 + 9 * Wl ^ 2 ≤ 9 * Y ^ 2 := by
  nlinarith [Nat.zero_le (Yc * Wl), Nat.zero_le (Wl * sS), Nat.zero_le (Yc * sS), Nat.zero_le Yc, Nat.zero_le Wl,
    Nat.mul_le_mul hY hY, Nat.zero_le sS]

mutual
theorem sz_mergeAR_le : ∀ (a b : AR) (c : CT) (r : AR), mergeAR a b c = some r →
    sz r ≤ 9 * (sz a + sz b) ^ 2
  | .run S na ka, .run S' nb kb, .node S'' ty tk, r, h => by
    simp only [mergeAR] at h
    split at h
    · simp at h
    · rename_i path hp
      obtain ⟨ks, hks, rfl⟩ := Option.map_eq_some_iff.1 h
      have h1 := sz_mergeKids_le ka kb tk ks hks
      have hpl := findPath_len hp
      simp only [List.length_map] at hpl
      have h2 := sz_mergeChain_le na nb path none
      have h3 := sz_chain_ge na
      have h4 := sz_chain_ge nb
      have hpc : path.length * (sz na + sz nb + 8) ≤ (sz na + sz nb) * (sz na + sz nb + 8) :=
        Nat.mul_le_mul_right _ (by omega)
      have h5 := arith_merge (sz na + sz nb) (sz ka + sz kb) (sz S) (sz (AR.run S na ka) + sz (AR.run S' nb kb))
        (by rw [sz_ar, sz_ar]; have := sz_pos S'; omega)
      rw [sz_ar]
      simp only [sz_ar] at h5 ⊢
      omega
theorem sz_mergeKids_le : ∀ (ka kb : List AR) (tk : List CT) (ks : List AR), mergeKids ka kb tk = some ks →
    sz ks ≤ 9 * (sz ka + sz kb) ^ 2
  | [], [], [], ks, h => by
    simp only [mergeKids, Option.some.injEq] at h; subst h
    simp only [sz_nil]; norm_num
  | a :: as, b :: bs, t :: ts, ks, h => by
    simp only [mergeKids] at h
    obtain ⟨r, hr, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h2
    have h1 := sz_mergeAR_le a b t r hr
    have h3 := sz_mergeKids_le as bs ts l hl
    simp only [sz_cons]
    nlinarith [Nat.zero_le ((sz a + sz b) * (sz as + sz bs)), sz_pos a, sz_pos b, sz_pos as, sz_pos bs]
  | [], [], _ :: _, _, h => by simp [mergeKids] at h
  | [], _ :: _, _, _, h => by simp [mergeKids] at h
  | _ :: _, [], _, _, h => by simp [mergeKids] at h
  | _ :: _, _ :: _, [], _, h => by simp [mergeKids] at h
end

/-! ## chain cardinalities and the cost constants -/

mutual
/-- every chain node of the analysis has a bag of at most `L` vertices -/
def ARcard (L : ℕ) : AR → Prop
  | .run _ c ks => (∀ n ∈ c, n.bag.card ≤ L) ∧ ARcardL L ks
def ARcardL (L : ℕ) : List AR → Prop
  | [] => True
  | k :: ks => ARcard L k ∧ ARcardL L ks
end

/-- the cost of one `findPath` call (chains of at most `s` nodes, entries `≤ L`, target sequence of length `≤ s`) -/
def fpBound (s L : ℕ) : ℕ :=
  6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
    4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + s) + 100 * (2 * (L + L) + 1) + 100) + 12 * (s + s) + 200

theorem findPathCost_le (la lb lw s L : ℕ) (ha : la ≤ s) (hb : lb ≤ s) (hw : lw ≤ s) :
    6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) +
      12 * (la + lb) + 200 ≤ fpBound s L := by
  unfold fpBound
  have h1 : 3 ^ (2 * (L + L) + 1 + lw) ≤ 3 ^ (2 * (L + L) + 1 + s) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 6000 * (la + 1) * (lb + 1) ≤ 6000 * (s + 1) * (s + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 6000 (by omega)) (by omega)
  have h3 : 6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 ≤
      6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  have h4 : 4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) ≤
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + s) + 100 * (2 * (L + L) + 1) + 100) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- local cost of `mergeAR` -/
def cMA (s L : ℕ) : ℕ := fpBound s L + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300

theorem ARcardL_iff {L : ℕ} : ∀ ks : List AR, ARcardL L ks ↔ ∀ k ∈ ks, ARcard L k
  | [] => by simp [ARcardL]
  | k :: ks => by simp [ARcardL, ARcardL_iff ks]

theorem ARcard_mkNode (L : ℕ) (S X : Finset ℕ) (junk : List RT) (core : List AR) (hX : X.card ≤ L)
    (hc : ∀ k ∈ core, ARcard L k) : ARcard L (mkNode S X junk core) := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, ARcard, ARcardL]
    exact ⟨by simpa using hX, trivial⟩
  · obtain ⟨Sk, ck, kk⟩ := k
    have hk := hc _ (List.mem_singleton_self _)
    simp only [mkNode, AR.S, AR.chain, AR.kids]
    by_cases h : Sk = S
    · simp only [h, if_true, ARcard]
      simp only [ARcard] at hk
      refine ⟨?_, hk.2⟩
      intro n hn
      rcases List.mem_cons.1 hn with rfl | hn
      · exact hX
      · exact hk.1 n hn
    · simp only [h, if_false, ARcard, ARcardL]
      exact ⟨by simpa using hX, hk, trivial⟩
  · simp only [mkNode, ARcard]
    refine ⟨by simpa using hX, ?_⟩
    rw [ARcardL_iff]
    intro x hx
    unfold sortAR at hx
    have hx' : x ∈ (k :: k2 :: t) :=
      (List.mergeSort_perm (k :: k2 :: t) (fun a b => decide (CT.key S a.char ≤ CT.key S b.char))).mem_iff.1 hx
    exact hc x hx'

theorem ARcard_analyze (L : ℕ) (Bd : Finset ℕ) (t : RT) :
    (∀ X ∈ t.bags, X.card ≤ L) → ARcard L (analyze Bd t) := by
  induction t using RT.ind with
  | h X ks ih =>
    intro hb
    rw [analyze_node, analyzeNode_eq]
    apply ARcard_mkNode
    · exact hb X (by simp [RT.bags])
    · intro k hk
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
      obtain ⟨hp1, _⟩ := List.mem_filter.1 hp
      obtain ⟨k0, hk0, rfl⟩ := List.mem_map.1 hp1
      exact ih k0 hk0 (fun Y hY => hb Y (by
        simp only [RT.bags, List.mem_cons]
        exact Or.inr ((RT.mem_bagsL_iff ks Y).2 ⟨k0, hk0, hY⟩)))

/-! ## the lemmas -/

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem flagI_runs (prev : Option (ℕ × ℕ)) (i : ℕ) (hB : 1 < B) :
    Runs Δ' B fFlagI [toVal prev, toVal i] (toVal (flagI prev i)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_flagI) ?_
  rcases prev with _ | ⟨pi, pj⟩
  · simp only [Option.elim]
    ev_start
    · ev_run
    · omega
  · by_cases h : pi = i
    · subst h
      simp only [Option.elim, ne_eq, not_true_eq_false, decide_false, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [Option.elim, ne_eq, h, not_false_eq_true, decide_true, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h]; done) | (simp [h]; omega))
      · omega

theorem flagJ_runs (prev : Option (ℕ × ℕ)) (j : ℕ) (hB : 1 < B) :
    Runs Δ' B fFlagJ [toVal prev, toVal j] (toVal (flagJ prev j)) 20 := by
  refine Runs.mk (hΔ _ _ Δ_flagJ) ?_
  rcases prev with _ | ⟨pi, pj⟩
  · simp only [Option.elim]
    ev_start
    · ev_run
    · omega
  · by_cases h : pj = j
    · subst h
      simp only [Option.elim, ne_eq, not_true_eq_false, decide_false, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · simp only [Option.elim, ne_eq, h, not_false_eq_true, decide_true, toVal_some, toVal_pair]
      ev_start
      · ev_run
        all_goals (first | omega | (simp [h]; done) | (simp [h]; omega))
      · omega

theorem mergeChain_runs (s : ℕ) (hB : 1000 + 100 * (s + 1) < B) (na nb : List CNode) (hna : sz na ≤ s)
    (hnb : sz nb ≤ s) : ∀ (path : List (ℕ × ℕ)) (prev : Option (ℕ × ℕ)),
    Runs Δ' B fMergeChain [toVal na, toVal nb, toVal prev, toVal path] (toVal (mergeChain na nb prev path))
      (250 * (s + 3) * path.length + 8)
  | [], prev => by
    refine Runs.mk (hΔ _ _ Δ_mergeChain) ?_
    simp only [mergeChain, List.length_nil]
    ev_start
    · ev_run
    · omega
  | (i, j) :: rest, prev => by
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hB1 : 1 < B := by omega
    have ih := mergeChain_runs s hB na nb hna hnb rest (some (i, j))
    have hn1 := E5A.nthD_runs hΔA B hB1 na i dflt
    have hn2 := E5A.nthD_runs hΔA B hB1 nb j dflt
    simp only [dflt, toVal_cnode, toVal_empty_finset, toVal_nil] at hn1 hn2
    have hfi := flagI_runs hΔ B prev i hB1
    have hfj := flagJ_runs hΔ B prev j hB1
    have hu := Lib3.union_runs (l3 hE1) B (na.getD i dflt).bag (nb.getD j dflt).bag
    have hla := length_le_sz na
    have hlb := length_le_sz nb
    have hga := sz_getD_le na i dflt
    have hgb := sz_getD_le nb j dflt
    have hd := sz_dflt
    have hA : sz (na.getD i dflt) = sz (na.getD i dflt).bag + sz (na.getD i dflt).junk + 1 := sz_cnode _ _
    have hBg : sz (nb.getD j dflt) = sz (nb.getD j dflt).bag + sz (nb.getD j dflt).junk + 1 := sz_cnode _ _
    have hc1 := card_le_sz (na.getD i dflt).bag
    have hc2 := card_le_sz (nb.getD j dflt).bag
    have hj1 := length_le_sz (na.getD i dflt).junk
    have hj2 := length_le_sz (nb.getD j dflt).junk
    have hk : fFlagI < B := by have : fFlagI < 1000 := by decide
                               omega
    have hk2 : fFlagJ < B := by have : fFlagJ < 1000 := by decide
                                omega
    have hk3 : fMergeChain < B := by have : fMergeChain < 1000 := by decide
                                     omega
    have hap := Lib1.append_runs (l1 hE1) B (if flagI prev i then (na.getD i dflt).junk else [])
      (if flagJ prev j then (nb.getD j dflt).junk else [])
    have hjl1 : (if flagI prev i then (na.getD i dflt).junk else []).length ≤ (na.getD i dflt).junk.length := by
      split_ifs <;> simp
    have hjl2 : (if flagJ prev j then (nb.getD j dflt).junk else []).length ≤ (nb.getD j dflt).junk.length := by
      split_ifs <;> simp
    have e : 250 * (s + 3) * (rest.length + 1) = 250 * (s + 3) * rest.length + 250 * (s + 3) := by ring
    refine Runs.mk (hΔ _ _ Δ_mergeChain) ?_
    rw [mergeChain_cons]
    simp only [toVal_cons, toVal_pair, toVal_cnode, List.length_cons]
    by_cases hI : flagI prev i = true <;> by_cases hJ : flagJ prev j = true
    · simp only [hI, hJ, if_true] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hJ
      simp only [hI, hJ, if_true, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hI
      simp only [hI, hJ, if_true, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega
    · simp only [Bool.not_eq_true] at hI hJ
      simp only [hI, hJ, Bool.false_eq_true, if_false] at hfi hfj hap ⊢
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · rw [e]; try simp only [List.length_nil]
        omega

mutual
theorem mergeAR_runs (s L : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (a b : AR) (c : CT), sz a ≤ s → sz b ≤ s → sz c ≤ s → ARcard L a → ARcard L b →
    Runs Δ' B fMergeAR [toVal a, toVal b, toVal c] (toVal (mergeAR a b c)) (cMA s L * cnt a)
  | .run S na ka, .run S' nb kb, .node S'' ty tk, ha, hb, hc, hca, hcb => by
    have hE1 := Ext.trans extE1 hΔ
    have hΔA : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
    have hB1 : 1 < B := by omega
    have hna : sz na ≤ s := by have := sz_c_lt S na ka; omega
    have hnb : sz nb ≤ s := by have := sz_c_lt S' nb kb; omega
    have hka : sz ka ≤ s := by have := sz_ks_lt S na ka; omega
    have hkb : sz kb ≤ s := by have := sz_ks_lt S' nb kb; omega
    have hSs : sz S ≤ s := by have := sz_S_lt S na ka; omega
    have hty : sz ty ≤ s := by have := E5R.sz_ct_y_lt S'' ty tk; omega
    have htk : sz tk ≤ s := by have := E5R.sz_ct_ks_lt S'' ty tk; omega
    have hlna := length_le_sz na
    have hlnb := length_le_sz nb
    have hlty := length_le_sz ty
    have hlka := length_le_sz ka
    have hcS := card_le_sz S
    have hcards1 := cards_runs hΔA B na (by omega)
    have hcards2 := cards_runs hΔA B nb (by omega)
    have hlen := Lib4.card_runs (l4 hE1) B S (by omega)
    have hcna : ∀ x ∈ na.map (fun n => n.bag.card), x ≤ L := by
      intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx; exact hca.1 n hn
    have hcnb : ∀ x ∈ nb.map (fun n => n.bag.card), x ≤ L := by
      intro x hx; obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx; exact hcb.1 n hn
    have hfp := E1D.findPath_runs (eD hE1) B (by omega) (na.map (fun n => n.bag.card))
      (nb.map (fun n => n.bag.card)) S.card ty L L hcna hcnb (by simp; omega)
    have hfpc := findPathCost_le (na.map (fun n => n.bag.card)).length (nb.map (fun n => n.bag.card)).length
      ty.length s L (by simp; omega) (by simp; omega) (by omega)
    have hkids := mergeKids_runs s L hL hB ka kb tk hka hkb htk hca.2 hcb.2
    have hk1 : fMergeKids < B := by have : fMergeKids < 1000 := by decide
                                    omega
    have hk2 : fMergeChain < B := by have : fMergeChain < 1000 := by decide
                                     omega
    have hk3 : fCards < B := by have : fCards < 1000 := by decide
                                omega
    have hk4 : fLength < B := by have : fLength < 1000 := by decide
                                 omega
    have hk5 : E1D.fFindPath < B := by have : E1D.fFindPath < 1000 := by decide
                                       omega
    have hcnt := length_le_cntL ka
    have hcntp := cnt_pos (AR.run S na ka)
    have hcm : cMA s L = fpBound s L + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA s L * (1 + cntL ka) = cMA s L + cMA s L * cntL ka := by ring
    have hs3 : (s + 3) ≤ (s + 3) ^ 2 := le_pw (by omega) (by omega)
    have hlen' : ka.length ≤ s := by omega
    simp only [cnt]
    rcases hfp' : findPath (na.map (fun n => n.bag.card)) (nb.map (fun n => n.bag.card)) S.card ty with _ | path
    · rw [hfp'] at hfp
      refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
      simp only [mergeAR, hfp', toVal_ar, toVal_ct, toVal_none]
      ev_start
      · ev_run
      · rw [e]
        simp only [List.length_map] at *
        omega
    · rw [hfp'] at hfp
      have hpl := findPath_len hfp'
      simp only [List.length_map] at hpl
      have hmc0 := mergeChain_runs hΔ B s hB na nb hna hnb path none
      have hmc : 250 * (s + 3) * path.length ≤ 500 * (s + 3) ^ 2 := by
        calc 250 * (s + 3) * path.length ≤ 250 * (s + 3) * (2 * (s + 3)) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 500 * (s + 3) ^ 2 := by ring
      rcases hks : mergeKids ka kb tk with _ | ks
      · rw [hks] at hkids
        refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
        simp only [mergeAR, hfp', hks, toVal_ar, toVal_ct, Option.map_none, toVal_none]
        ev_start
        · ev_run
        · rw [e]
          simp only [List.length_map] at *
          omega
      · rw [hks] at hkids
        refine Runs.mk (hΔ _ _ Δ_mergeAR) ?_
        simp only [mergeAR, hfp', hks, toVal_ar, toVal_ct, Option.map_some, toVal_some, toVal_none]
        ev_start
        · ev_run
        · rw [e]
          simp only [List.length_map] at *
          omega
theorem mergeKids_runs (s L : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (ka kb : List AR) (tk : List CT), sz ka ≤ s → sz kb ≤ s → sz tk ≤ s → ARcardL L ka → ARcardL L kb →
    Runs Δ' B fMergeKids [toVal ka, toVal kb, toVal tk] (toVal (mergeKids ka kb tk))
      (cMA s L * cntL ka + 40 * ka.length + 20)
  | [], [], [], _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_some, toVal_nil]
    ev_start
    · ev_run
    · omega
  | [], [], _ :: _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega
  | [], _ :: _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega
  | _ :: _, [], _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega
  | _ :: _, _ :: _, [], _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega
  | a :: as, b :: bs, t :: ts, hka, hkb, htk, hca, hcb => by
    have ha : sz a ≤ s := by have := sz_head_lt a as; omega
    have has : sz as ≤ s := by have := sz_tail_lt a as; omega
    have hb : sz b ≤ s := by have := sz_head_lt b bs; omega
    have hbs : sz bs ≤ s := by have := sz_tail_lt b bs; omega
    have ht : sz t ≤ s := by have := sz_head_lt t ts; omega
    have hts : sz ts ≤ s := by have := sz_tail_lt t ts; omega
    have h1 := mergeAR_runs s L hL hB a b t ha hb ht hca.1 hcb.1
    have h2 := mergeKids_runs s L hL hB as bs ts has hbs hts hca.2 hcb.2
    have hk1 : fMergeAR < B := by have : fMergeAR < 1000 := by decide
                                  omega
    have hk2 : fMergeKids < B := by have : fMergeKids < 1000 := by decide
                                    omega
    have hcm : cMA s L = fpBound s L + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA s L * (cnt a + cntL as) = cMA s L * cnt a + cMA s L * cntL as := by ring
    have hcp := cnt_pos a
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    rcases hr : mergeAR a b t with _ | r
    · rw [hr] at h1
      simp only [mergeKids, hr, toVal_cons, toVal_none, cntL, List.length_cons]
      ev_start
      · ev_run
      · rw [e]; omega
    · rw [hr] at h1
      rcases hrs : mergeKids as bs ts with _ | rs
      · rw [hrs] at h2
        simp only [mergeKids, hr, hrs, Option.map_none, toVal_cons, toVal_none, cntL,
          List.length_cons]
        ev_start
        · ev_run
        · rw [e]; omega
      · rw [hrs] at h2
        simp only [mergeKids, hr, hrs, Option.map_some, toVal_cons, toVal_some, toVal_none, cntL,
          List.length_cons]
        ev_start
        · ev_run
        · rw [e]; omega
end

/-- cost of `mergeReal` -/
def cMergeReal (s L ck6 : ℕ) : ℕ :=
  2 * (E5B.cA s ck6 * s) + cMA (5 * s) L * (5 * s) + 100 * (900 * (s * s) + 1) * (900 * (s * s)) + 100

theorem mergeReal_runs (E : Ext5 Δ') (Bd : Finset ℕ) (ta tb : RT) (target : CT) (s L : ℕ)
    (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) < B) :
    Runs Δ' B fMergeReal [toVal Bd, toVal ta, toVal tb, toVal target] (toVal (mergeReal Bd ta tb target))
      (cMergeReal s L (E.cKey (6 * s))) := by
  have hq : (s + 1) ^ 2 = s * s + 2 * s + 1 := by ring
  have hq2 : 0 ≤ (s + 1) ^ 2 := Nat.zero_le _
  have hB1 : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B := by nlinarith
  have hB2 : 1000 + 100 * (5 * s + 1) < B := by nlinarith
  have hΔB : E5B.Δ ⊑ Δ' := Ext.trans extB hΔ
  have h1 := E5B.analyze_runs hΔB B E Bd s hBd hB1 ta hta
  have h2 := E5B.analyze_runs hΔB B E Bd s hBd hB1 tb htb
  have sa := le_trans (E5B.sz_analyze_le Bd ta) (by omega : 5 * sz ta ≤ 5 * s)
  have sb := le_trans (E5B.sz_analyze_le Bd tb) (by omega : 5 * sz tb ≤ 5 * s)
  have hm := mergeAR_runs hΔ B (5 * s) L hL hB2 (analyze Bd ta) (analyze Bd tb) target sa sb (by omega)
    (ARcard_analyze L Bd ta hca) (ARcard_analyze L Bd tb hcb)
  have ca := le_trans (cnt_le_sz (analyze Bd ta)) sa
  have t1 : E5B.cA s (E.cKey (6 * s)) * ta.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz ta) hta)
  have t2 : E5B.cA s (E.cKey (6 * s)) * tb.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz tb) htb)
  have t3 : cMA (5 * s) L * cnt (analyze Bd ta) ≤ cMA (5 * s) L * (5 * s) := Nat.mul_le_mul_left _ ca
  have hk1 : fMergeAR < B := by have : fMergeAR < 1000 := by decide
                                omega
  have hk2 : E5B.fAnalyze < B := by have : E5B.fAnalyze < 1000 := by decide
                                    omega
  have hk3 : E5A.fToRT < B := by have : E5A.fToRT < 1000 := by decide
                                 omega
  have hgoal : mergeReal Bd ta tb target = (mergeAR (analyze Bd ta) (analyze Bd tb) target).map AR.toRT := rfl
  rw [hgoal]
  rcases hr : mergeAR (analyze Bd ta) (analyze Bd tb) target with _ | r
  · rw [hr] at hm
    refine Runs.mk (hΔ _ _ Δ_mergeReal) ?_
    simp only [Option.map_none]
    ev_start
    · ev_run
    · unfold cMergeReal; omega
  · rw [hr] at hm
    have hsr := sz_mergeAR_le _ _ target r hr
    have hsr' : sz r ≤ 900 * (s * s) := by
      have : (sz (analyze Bd ta) + sz (analyze Bd tb)) ^ 2 ≤ (10 * s) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (10 * s) ^ 2 = 100 * (s * s) := by ring
      omega
    have hcr := le_trans (cnt_le_sz r) hsr'
    have hrt := E5A.toRT_runs (Ext.trans extA hΔ) B (900 * (s * s)) (by nlinarith) r hsr'
    have t4 : 100 * (900 * (s * s) + 1) * cnt r ≤ 100 * (900 * (s * s) + 1) * (900 * (s * s)) :=
      Nat.mul_le_mul_left _ hcr
    refine Runs.mk (hΔ _ _ Δ_mergeReal) ?_
    simp only [Option.map_some, toVal_some]
    ev_start
    · ev_run
    · unfold cMergeReal; omega

theorem predJoin_runs (E : Ext5 Δ') (target d : CT) (s : ℕ) (hd : sz d ≤ s) (htg : sz target ≤ s)
    (hPD : E.PD s d target)
    (hB : 1000 + E.cDom s < B) :
    Runs Δ' B fPredJoin [toVal target, toVal d] (toVal (CT.domCB d target)) (E.cDom s + 10) := by
  have h1 := E.domC B s d target hPD hd htg (by omega)
  refine Runs.mk (hΔ _ _ Δ_predJoin) ?_
  ev_start
  · ev_run
  · omega

/-- cost of `realJoin` -/
def cRealJoin (s L Lj cnorm5 cdom ck6 cj : ℕ) : ℕ :=
  2 * (200 * (s + 1) * s + cnorm5 + 8) + cj + (24 * Lj + 6 + Lj * (cdom + 10)) + cMergeReal s L ck6 + 100

theorem realJoin_runs (E : Ext5 Δ') (X : ExtJ Δ') (kmax : ℕ) (Bd : Finset ℕ) (ta tb : RT) (target : CT)
    (s L Lj : ℕ) (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L)
    (hPJ : X.PJ kmax (ta.char Bd) (tb.char Bd)) (hLen : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).length ≤ Lj)
    (hjs : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), sz d ≤ s)
    (hPD : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), E.PD s d target)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) + E.cNorm (5 * s) + E.cDom s +
      X.cJ kmax (ta.char Bd) (tb.char Bd) < B) :
    Runs Δ' B fRealJoin [toVal kmax, toVal Bd, toVal ta, toVal tb, toVal target]
      (toVal (realJoin kmax Bd ta tb target))
      (cRealJoin s L Lj (E.cNorm (5 * s)) (E.cDom s) (E.cKey (6 * s)) (X.cJ kmax (ta.char Bd) (tb.char Bd))) := by
  have hE1 := Ext.trans extE1 hΔ
  have hq2 : s + 1 ≤ (s + 1) ^ 2 := le_pw (by omega) (by omega)
  have hch1 := E5A.char_runs (Ext.trans extA hΔ) B E Bd ta s hta hBd (by nlinarith)
  have hch2 := E5A.char_runs (Ext.trans extA hΔ) B E Bd tb s htb hBd (by nlinarith)
  have hjc := X.joinC B kmax (ta.char Bd) (tb.char Bd) hPJ (by omega)
  have hfind := Lib4.find_runs (l4 hE1) B fPredJoin (toVal target) (fun d => CT.domCB d target)
    (fun _ => E.cDom s + 10) (CT.joinC kmax (ta.char Bd) (tb.char Bd))
    (fun d hd => predJoin_runs hΔ B E target d s (hjs d hd) htg (hPD d hd) (by nlinarith)) (by omega)
  simp only [E5.sum_map_const] at hfind
  have hmul : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).length * (E.cDom s + 10) ≤ Lj * (E.cDom s + 10) :=
    Nat.mul_le_mul_right _ hLen
  have hts1 : 200 * (s + 1) * ta.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz ta) hta)
  have hts2 : 200 * (s + 1) * tb.size ≤ 200 * (s + 1) * s := Nat.mul_le_mul_left _ (le_trans (size_le_sz tb) htb)
  have hk1 : fChar < B := by have : fChar < 1000 := by decide
                             nlinarith
  have hk2 : fPredJoin < B := by have : fPredJoin < 1000 := by decide
                                 nlinarith
  have hk3 : fMergeReal < B := by have : fMergeReal < 1000 := by decide
                                  nlinarith
  have hk4 : Lib4.fFind < B := by have : Lib4.fFind < 1000 := by decide
                                  nlinarith
  have hgoal : realJoin kmax Bd ta tb target =
      ((CT.joinC kmax (ta.char Bd) (tb.char Bd)).find? (fun d => CT.domCB d target)).bind
        (mergeReal Bd ta tb) := rfl
  rw [hgoal]
  rcases hf : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).find? (fun d => CT.domCB d target) with _ | d
  · rw [hf] at hfind
    refine Runs.mk (hΔ _ _ Δ_realJoin) ?_
    simp only [Option.bind_none]
    ev_start
    · ev_run
    · unfold cRealJoin; omega
  · rw [hf] at hfind
    have hdm : d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd) := List.mem_of_find?_eq_some hf
    have hmr := mergeReal_runs hΔ B E Bd ta tb d s L hBd hta htb (hjs d hdm) hL hca hcb (by nlinarith)
    refine Runs.mk (hΔ _ _ Δ_realJoin) ?_
    simp only [Option.bind_some, toVal_some]
    ev_start
    · ev_run
    · unfold cRealJoin; omega

end proofs
end E5D
end Lax117284Proofs.Treewidth.Fun
