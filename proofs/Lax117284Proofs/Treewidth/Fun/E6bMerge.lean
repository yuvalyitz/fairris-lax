import Lax117284Proofs.Treewidth.Fun.E6bDefs
import Lax117284Proofs.Treewidth.Size.Cells

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (5): `realJoin` with the target-sequence length as a separate parameter

**Why this file exists.**  the original (unprimed, now removed) `mergeAR_runs` of `E5D` bounded the cost of one `findPath` call by `fpBound s L`, which contains
`3^(2(L+L)+1+s)`: the length `lw` of the *target run sequence* is bounded by the global size bound `s` (`findPathCost_le`,
hypothesis `lw ≤ s`).  For `realJoin` on the trees built by `extract`, `s` must dominate the size of the *real trees*, which
grows with `|nt|`, so that bound is exponential in `|nt|`.  The run sequences of a characteristic of a boundary of `b` vertices
have length `≤ 2 kmax + 1` (`RB`), a bound independent of the tree.  Here: `fpBound'` with `3^(2(L+L)+1+Ly)`, and the
three statements `mergeAR_runs'`, `mergeKids_runs'`, `mergeReal_runs'`, `realJoin_runs'` re-proved with the extra
hypothesis `RB · Ly` on the target (proofs identical to `E5D`'s; only the `findPath` cost lemma differs).
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5D

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A E5C1

/-- the cost of one `findPath` call: chains of at most `s` nodes, entries `≤ L`, target sequence of length `≤ Ly` -/
def fpBound' (s L Ly : ℕ) : ℕ :=
  6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
    4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + Ly) + 100 * (2 * (L + L) + 1) + 100) + 12 * (s + s) + 200

theorem findPathCost_le' (la lb lw s L Ly : ℕ) (ha : la ≤ s) (hb : lb ≤ s) (hw : lw ≤ Ly) :
    6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 +
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) +
      12 * (la + lb) + 200 ≤ fpBound' s L Ly := by
  unfold fpBound'
  have h1 : 3 ^ (2 * (L + L) + 1 + lw) ≤ 3 ^ (2 * (L + L) + 1 + Ly) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 6000 * (la + 1) * (lb + 1) ≤ 6000 * (s + 1) * (s + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 6000 (by omega)) (by omega)
  have h3 : 6000 * (la + 1) * (lb + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 ≤
      6000 * (s + 1) * (s + 1) * (4 ^ (L + L + 1) + 1) ^ 2 * (2 * (L + L) + 1 + 2) ^ 2 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
  have h4 : 4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + lw) + 100 * (2 * (L + L) + 1) + 100) ≤
      4 ^ (L + L + 1) * (100 * 3 ^ (2 * (L + L) + 1 + Ly) + 100 * (2 * (L + L) + 1) + 100) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- local cost of `mergeAR` -/
def cMA' (s L Ly : ℕ) : ℕ := fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

mutual
theorem mergeAR_runs'_rec (s L Ly : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (a b : AR) (c : CT), sz a ≤ s → sz b ≤ s → sz c ≤ s → ARcard L a → ARcard L b → CT.RB s Ly c →
    Runs Δ' B fMergeAR [toVal a, toVal b, toVal c] (toVal (mergeAR a b c)) (cMA' s L Ly * cnt a)
  | .run S na ka, .run S' nb kb, .node S'' ty tk, ha, hb, hc, hca, hcb, hrb => by
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
    have hfpc := findPathCost_le' (na.map (fun n => n.bag.card)).length (nb.map (fun n => n.bag.card)).length
      ty.length s L Ly (by simp; omega) (by simp; omega) hrb.2.1
    have hkids := mergeKids_runs'_rec s L Ly hL hB ka kb tk hka hkb htk hca.2 hcb.2 hrb.2.2
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
    have hcm : cMA' s L Ly = fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA' s L Ly * (1 + cntL ka) = cMA' s L Ly + cMA' s L Ly * cntL ka := by ring
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
theorem mergeKids_runs'_rec (s L Ly : ℕ) (hL : L ≤ s) (hB : 1000 + 100 * (s + 1) < B) :
    ∀ (ka kb : List AR) (tk : List CT), sz ka ≤ s → sz kb ≤ s → sz tk ≤ s → ARcardL L ka → ARcardL L kb → CT.RBL s Ly tk →
    Runs Δ' B fMergeKids [toVal ka, toVal kb, toVal tk] (toVal (mergeKids ka kb tk))
      (cMA' s L Ly * cntL ka + 40 * ka.length + 20)
  | [], [], [], _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_some, toVal_nil]
    ev_start
    · ev_run
    · omega
  | [], [], _ :: _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega
  | [], _ :: _, _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, cntL, toVal_none]
    ev_start
    · ev_run
    · omega
  | _ :: _, [], _, _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega
  | _ :: _, _ :: _, [], _, _, _, _, _, _ => by
    refine Runs.mk (hΔ _ _ Δ_mergeKids) ?_
    simp only [mergeKids, toVal_none]
    ev_start
    · ev_run
    · omega
  | a :: as, b :: bs, t :: ts, hka, hkb, htk, hca, hcb, hrb => by
    have ha : sz a ≤ s := by have := sz_head_lt a as; omega
    have has : sz as ≤ s := by have := sz_tail_lt a as; omega
    have hb : sz b ≤ s := by have := sz_head_lt b bs; omega
    have hbs : sz bs ≤ s := by have := sz_tail_lt b bs; omega
    have ht : sz t ≤ s := by have := sz_head_lt t ts; omega
    have hts : sz ts ≤ s := by have := sz_tail_lt t ts; omega
    have h1 := mergeAR_runs'_rec s L Ly hL hB a b t ha hb ht hca.1 hcb.1 hrb.1
    have h2 := mergeKids_runs'_rec s L Ly hL hB as bs ts has hbs hts hca.2 hcb.2 hrb.2
    have hk1 : fMergeAR < B := by have : fMergeAR < 1000 := by decide
                                  omega
    have hk2 : fMergeKids < B := by have : fMergeKids < 1000 := by decide
                                    omega
    have hcm : cMA' s L Ly = fpBound' s L Ly + 600 * (s + 3) ^ 2 + 200 * (s + 1) + 300 := rfl
    have e : cMA' s L Ly * (cnt a + cntL as) = cMA' s L Ly * cnt a + cMA' s L Ly * cntL as := by ring
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

end proofs

theorem mergeAR_runs'_pair : (type_of% @mergeAR_runs'_rec) ∧ (type_of% @mergeKids_runs'_rec) :=
  ⟨@mergeAR_runs'_rec, @mergeKids_runs'_rec⟩

theorem mergeAR_runs' : type_of% @mergeAR_runs'_rec := mergeAR_runs'_pair.1

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ


/-- cost of `mergeReal` -/
def cMergeReal' (s L Ly ck6 : ℕ) : ℕ :=
  2 * (E5B.cA s ck6 * s) + cMA' (5 * s) L Ly * (5 * s) + 100 * (900 * (s * s) + 1) * (900 * (s * s)) + 100

theorem mergeReal_runs' (E : Ext5 Δ') (Bd : Finset ℕ) (ta tb : RT) (target : CT) (s L Ly : ℕ)
    (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L) (hRB : CT.RB (5 * s) Ly target)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) < B) :
    Runs Δ' B fMergeReal [toVal Bd, toVal ta, toVal tb, toVal target] (toVal (mergeReal Bd ta tb target))
      (cMergeReal' s L Ly (E.cKey (6 * s))) := by
  have hq : (s + 1) ^ 2 = s * s + 2 * s + 1 := by ring
  have hq2 : 0 ≤ (s + 1) ^ 2 := Nat.zero_le _
  have hB1 : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B := by nlinarith
  have hB2 : 1000 + 100 * (5 * s + 1) < B := by nlinarith
  have hΔB : E5B.Δ ⊑ Δ' := Ext.trans extB hΔ
  have h1 := E5B.analyze_runs hΔB B E Bd s hBd hB1 ta hta
  have h2 := E5B.analyze_runs hΔB B E Bd s hBd hB1 tb htb
  have sa := le_trans (E5B.sz_analyze_le Bd ta) (by omega : 5 * sz ta ≤ 5 * s)
  have sb := le_trans (E5B.sz_analyze_le Bd tb) (by omega : 5 * sz tb ≤ 5 * s)
  have hm := mergeAR_runs' hΔ B (5 * s) L Ly hL hB2 (analyze Bd ta) (analyze Bd tb) target sa sb (by omega)
    (ARcard_analyze L Bd ta hca) (ARcard_analyze L Bd tb hcb) hRB
  have ca := le_trans (cnt_le_sz (analyze Bd ta)) sa
  have t1 : E5B.cA s (E.cKey (6 * s)) * ta.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz ta) hta)
  have t2 : E5B.cA s (E.cKey (6 * s)) * tb.size ≤ E5B.cA s (E.cKey (6 * s)) * s :=
    Nat.mul_le_mul_left _ (le_trans (size_le_sz tb) htb)
  have t3 : cMA' (5 * s) L Ly * cnt (analyze Bd ta) ≤ cMA' (5 * s) L Ly * (5 * s) := Nat.mul_le_mul_left _ ca
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
    · unfold cMergeReal'; omega
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
    · unfold cMergeReal'; omega

/-- cost of `realJoin` -/
def cRealJoin' (s L Ly Lj cnorm5 cdom ck6 cj : ℕ) : ℕ :=
  2 * (200 * (s + 1) * s + cnorm5 + 8) + cj + (24 * Lj + 6 + Lj * (cdom + 10)) + cMergeReal' s L Ly ck6 + 100

theorem realJoin_runs' (E : Ext5 Δ') (X : ExtJ Δ') (kmax : ℕ) (Bd : Finset ℕ) (ta tb : RT) (target : CT)
    (s L Ly Lj : ℕ) (hBd : sz Bd ≤ s) (hta : sz ta ≤ s) (htb : sz tb ≤ s) (htg : sz target ≤ s) (hL : L ≤ 5 * s)
    (hca : ∀ X ∈ ta.bags, X.card ≤ L) (hcb : ∀ X ∈ tb.bags, X.card ≤ L)
    (hPJ : X.PJ kmax (ta.char Bd) (tb.char Bd)) (hLen : (CT.joinC kmax (ta.char Bd) (tb.char Bd)).length ≤ Lj)
    (hjs : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), sz d ≤ s)
    (hPD : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), E.PD s d target)
    (hRB : ∀ d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd), CT.RB (5 * s) Ly d)
    (hB : 200000 + 100000 * (s + 1) ^ 2 + E.cKey (6 * s) + E.cNorm (5 * s) + E.cDom s +
      X.cJ kmax (ta.char Bd) (tb.char Bd) < B) :
    Runs Δ' B fRealJoin [toVal kmax, toVal Bd, toVal ta, toVal tb, toVal target]
      (toVal (realJoin kmax Bd ta tb target))
      (cRealJoin' s L Ly Lj (E.cNorm (5 * s)) (E.cDom s) (E.cKey (6 * s)) (X.cJ kmax (ta.char Bd) (tb.char Bd))) := by
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
    · unfold cRealJoin'; omega
  · rw [hf] at hfind
    have hdm : d ∈ CT.joinC kmax (ta.char Bd) (tb.char Bd) := List.mem_of_find?_eq_some hf
    have hmr := mergeReal_runs' hΔ B E Bd ta tb d s L Ly hBd hta htb (hjs d hdm) hL hca hcb (hRB d hdm) (by nlinarith)
    refine Runs.mk (hΔ _ _ Δ_realJoin) ?_
    simp only [Option.bind_some, toVal_some]
    ev_start
    · ev_run
    · unfold cRealJoin'; omega


end proofs
end E5D
end Lax117284Proofs.Treewidth.Fun
