import Lax117284Proofs.Treewidth.Fun.E5A
import Lax117284Proofs.Treewidth.Chars.JoinShape

/-!
# WP E5 (layer B): `sortAR`, `analyzeNode`, `analyze`

Ids `460 …`:

| id | function | arguments |
|---|---|---|
| 460 `fKeyLeAR` | `decide (key S a.char ≤ key S b.char)` (comparison of `sortAR`) | `[S, a, b]` |
| 461 `fSortAR` | `sortAR` | `[S, ks]` |
| 462 `fPruned` | the predicate `p.2.isLeaf && decide (p.2.S ⊆ S)` | `[S, p]` |
| 463 `fNotPruned` | its negation | `[S, p]` |
| 464 `fFstP` / 465 `fSndP` | `p.1` / `p.2` (`map` callees) | `[_, p]` |
| 466 `fAnalyzeNode` | `analyzeNode` | `[Bd, X, kids]` |
| 467 `fAnalyze` | `analyze` | `[Bd, t]` |
| 468 `fAnalyzeL` | `analyzeL` | `[Bd, ks]` |

The recursion of `analyze` is charged per node: `Runs … fAnalyze … (cA E s · t.size)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E5B

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees E5 E5A

abbrev fKeyLeAR : ℕ := 460
abbrev fSortAR : ℕ := 461
abbrev fPruned : ℕ := 462
abbrev fNotPruned : ℕ := 463
abbrev fFstP : ℕ := 464
abbrev fSndP : ℕ := 465
abbrev fAnalyzeNode : ℕ := 466
abbrev fAnalyze : ℕ := 467
abbrev fAnalyzeL : ℕ := 468

/-- the pruning predicate of `analyzeNode` -/
abbrev prunedP (S : Finset ℕ) : RT × AR → Bool := fun p => p.2.isLeaf && decide (p.2.S ⊆ S)

def keyLeARTm : Tm := .call idKeyLe [V 0, .call fCharAR [V 1], .call fCharAR [V 2]]

def sortARTm : Tm := .call Lib2.fISort [.lit fKeyLeAR, V 0, V 1]

def prunedTm : Tm :=
  .mul (.isNat (.snd (.snd (.snd (V 1))))) (.call Lib3.fSubsetS [.fst (.snd (V 1)), V 0])

def notPrunedTm : Tm := .sub (.lit 1) (.call fPruned [V 0, V 1])

def fstPTm : Tm := .fst (V 1)
def sndPTm : Tm := .snd (V 1)

/-- environment after the three `let`s: `[core, junk, S, Bd, X, kids]` -/
def analyzeNodeTm : Tm :=
  .letE (.call Lib3.fInterS [V 1, V 0])
    (.letE (.call fMap [.lit fFstP, .lit 0, .call fFilter [.lit fPruned, V 0, V 3]])
      (.letE (.call fMap [.lit fSndP, .lit 0, .call fFilter [.lit fNotPruned, V 1, V 4]])
        (.ite (.isNat (V 0))
          (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.lit 0)))
          (.ite (.isNat (.snd (V 0)))
            (.ite (.call fEqV [.fst (.fst (V 0)), V 2])
              (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.fst (.snd (.fst (V 0)))))
                (.snd (.snd (.fst (V 0))))))
              (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.cons (.fst (V 0)) (.lit 0)))))
            (.cons (V 2) (.cons (.cons (.cons (V 4) (V 1)) (.lit 0)) (.call fSortAR [V 2, V 0])))))))

def analyzeTm : Tm :=
  .call fAnalyzeNode [V 0, .fst (V 1), .call fAnalyzeL [V 0, .snd (V 1)]]

def analyzeLTm : Tm :=
  .ite (.isNat (V 1)) (V 1)
    (.cons (.cons (.fst (V 1)) (.call fAnalyze [V 0, .fst (V 1)])) (.call fAnalyzeL [V 0, .snd (V 1)]))

def tbl : ℕ → Option Tm := fun f =>
  match f with
  | 460 => some keyLeARTm | 461 => some sortARTm | 462 => some prunedTm | 463 => some notPrunedTm
  | 464 => some fstPTm | 465 => some sndPTm | 466 => some analyzeNodeTm | 467 => some analyzeTm
  | 468 => some analyzeLTm | _ => none

def Δ : ℕ → Option Tm := layerΔ E5A.Δ 460 tbl

abbrev size : ℕ := 469

theorem Δ_lt {f : ℕ} {b : Tm} (h : Δ f = some b) : f < size := by
  by_contra hf
  have hf : 469 ≤ f := by simpa [size] using hf
  have : Δ f = none := by
    unfold Δ layerΔ
    have h460 : 460 ≤ f := by omega
    simp only [h460, if_true]; unfold tbl; split <;> first | rfl | omega
  rw [this] at h; cases h

theorem extA : E5A.Δ ⊑ Δ := Ext.layer tbl (fun f b h => by have := E5A.Δ_lt h; simp [E5A.size] at this; omega)
theorem extE1 : E1.e1Δ ⊑ Δ := Ext.trans E5A.extE1 extA

theorem Δ_keyLeAR : Δ fKeyLeAR = some keyLeARTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fKeyLeAR by decide)]; rfl
theorem Δ_sortAR : Δ fSortAR = some sortARTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fSortAR by decide)]; rfl
theorem Δ_pruned : Δ fPruned = some prunedTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fPruned by decide)]; rfl
theorem Δ_notPruned : Δ fNotPruned = some notPrunedTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fNotPruned by decide)]; rfl
theorem Δ_fstP : Δ fFstP = some fstPTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fFstP by decide)]; rfl
theorem Δ_sndP : Δ fSndP = some sndPTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fSndP by decide)]; rfl
theorem Δ_analyzeNode : Δ fAnalyzeNode = some analyzeNodeTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyzeNode by decide)]; rfl
theorem Δ_analyze : Δ fAnalyze = some analyzeTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyze by decide)]; rfl
theorem Δ_analyzeL : Δ fAnalyzeL = some analyzeLTm := by
  simp [Δ, layerΔ_ge tbl (show 460 ≤ fAnalyzeL by decide)]; rfl

/-! ## sizes -/

theorem sz_mkNode_le (S X : Finset ℕ) (junk : List RT) (core : List AR) :
    sz (mkNode S X junk core) ≤ sz S + sz X + sz junk + sz core + 7 := by
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, sz_ar, sz_cons, sz_cnode]
    have : sz ([] : List CNode) = 1 := rfl
    have : sz ([] : List AR) = 1 := rfl
    omega
  · obtain ⟨Sk, ck, kk⟩ := k
    simp only [mkNode, AR.S, AR.chain, AR.kids]
    by_cases h : Sk = S
    · subst h
      simp only [if_true, sz_ar, sz_cons, sz_cnode]
      have : sz ([] : List AR) = 1 := rfl
      omega
    · simp only [h, if_false, sz_ar, sz_cons, sz_cnode]
      have : sz ([] : List AR) = 1 := rfl
      have : sz ([] : List CNode) = 1 := rfl
      omega
  · have hp := sz_perm' (List.mergeSort_perm (k :: k2 :: t) (fun a b => decide (CT.key S a.char ≤ CT.key S b.char)))
    simp only [mkNode, sortAR, sz_ar, sz_cons, sz_cnode] at hp ⊢
    have : sz ([] : List CNode) = 1 := rfl
    omega

theorem sz_junk_core (l : List (RT × AR)) (pr : RT × AR → Bool) (h : ∀ p ∈ l, sz p.2 ≤ 5 * sz p.1) :
    sz ((l.filter pr).map Prod.fst) + sz ((l.filter (fun p => !pr p)).map Prod.snd) ≤
      2 + 5 * (l.map (fun p => sz p.1 + 1)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have ih' := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (List.mem_cons_self ..)
    by_cases hpr : pr p = true
    · simp only [List.filter_cons, hpr, Bool.not_true, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, sz_cons]
      omega
    · simp only [Bool.not_eq_true] at hpr
      simp only [List.filter_cons, hpr, Bool.not_false, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, sz_cons]
      omega

theorem sz_analyze_le (Bd : Finset ℕ) (t : RT) : sz (analyze Bd t) ≤ 5 * sz t := by
  induction t using RT.ind with
  | h X ks ih =>
    rw [analyze_node, analyzeNode_eq]
    have hk : ∀ p ∈ ks.map (fun k => (k, analyze Bd k)), sz p.2 ≤ 5 * sz p.1 := by
      intro p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hp
      exact ih k hk
    have h1 := sz_junk_core _ (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd)) hk
    have h2 := sz_mkNode_le (X ∩ Bd) X (((ks.map (fun k => (k, analyze Bd k))).filter
        (fun p => p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd))).map Prod.fst)
      (((ks.map (fun k => (k, analyze Bd k))).filter
        (fun p => !(p.2.isLeaf && decide (p.2.S ⊆ X ∩ Bd)))).map Prod.snd)
    have h3 := sz_inter_le X Bd
    have h4 : (ks.map (fun k => (k, analyze Bd k))).map (fun p => sz p.1 + 1) = ks.map (fun k => sz k + 1) := by
      rw [List.map_map]; rfl
    have h5 : sz ks = 1 + (ks.map (fun k => sz k + 1)).sum := by
      rw [sz_list]
      have : ∀ l : List RT, (l.map sz).sum + l.length = (l.map (fun k => sz k + 1)).sum := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
      have := this ks
      omega
    rw [h4] at h1
    rw [sz_rt_node]
    omega

theorem sz_analyzeL_le (Bd : Finset ℕ) (ks : List RT) : sz (analyzeL Bd ks) ≤ 6 * sz ks := by
  rw [analyzeL_eq]
  have key : ∀ l : List RT, sz (l.map (fun k => (k, analyze Bd k))) ≤ 6 * sz l := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      have := sz_analyze_le Bd a
      simp only [List.map_cons, sz_cons, sz_pair]
      omega
  exact key ks

/-! ## the comparison and the sort -/

/-- cost of `sortAR` on inputs of size `≤ s`, `ck` the cost of one `keyLe`. -/
def cSort (s ck : ℕ) : ℕ := (800 * (s + 1) ^ 4 + ck + 80) * (s + 1) ^ 2 + 8

section proofs
variable {Δ' : ℕ → Option Tm} (hΔ : Δ ⊑ Δ') (B : ℕ)
include hΔ

theorem keyLeAR_runs (E : Ext5 Δ') (S : Finset ℕ) (a b : AR) (s : ℕ) (hS : sz S ≤ s) (ha : sz a ≤ s)
    (hb : sz b ≤ s) (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fKeyLeAR [toVal S, toVal a, toVal b] (toVal (decide (CT.key S a.char ≤ CT.key S b.char)))
      (800 * (s + 1) ^ 4 + E.cKey s + 10) := by
  have hΔ' : E5A.Δ ⊑ Δ' := Ext.trans extA hΔ
  have h1 := charAR_runs hΔ' B s (by omega) a ha
  have h2 := charAR_runs hΔ' B s (by omega) b hb
  have h3 := E.keyLe B s S a.char b.char hS (le_trans (sz_charAR_le a) ha) (le_trans (sz_charAR_le b) hb) (by omega)
  have ca := le_trans (cnt_le_sz a) ha
  have cb := le_trans (cnt_le_sz b) hb
  have e1 : 400 * (s + 1) ^ 3 * cnt a ≤ 400 * (s + 1) ^ 4 := by
    calc 400 * (s + 1) ^ 3 * cnt a ≤ 400 * (s + 1) ^ 3 * (s + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (s + 1) ^ 4 := by ring
  have e2 : 400 * (s + 1) ^ 3 * cnt b ≤ 400 * (s + 1) ^ 4 := by
    calc 400 * (s + 1) ^ 3 * cnt b ≤ 400 * (s + 1) ^ 3 * (s + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = 400 * (s + 1) ^ 4 := by ring
  refine Runs.mk (hΔ _ _ Δ_keyLeAR) ?_
  ev_start
  · ev_run
  · omega

theorem sortAR_runs (E : Ext5 Δ') (S : Finset ℕ) (ks : List AR) (s : ℕ) (hS : sz S ≤ s) (hks : sz ks ≤ s)
    (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fSortAR [toVal S, toVal ks] (toVal (sortAR S ks)) (cSort s (E.cKey s)) := by
  have hΔ2 : Lib2.Δ ⊑ Δ' := l2 (Ext.trans extE1 hΔ)
  have h1 := Lib2.mergeSort_runs hΔ2 B fKeyLeAR (toVal S) (fun a b : AR => decide (CT.key S a.char ≤ CT.key S b.char))
    (800 * (s + 1) ^ 4 + E.cKey s + 10)
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) ks
    (fun x hx y hy => keyLeAR_runs hΔ B E S x y s hS (le_trans (sz_le_of_mem hx) hks)
      (le_trans (sz_le_of_mem hy) hks) hB)
  have hlen : ks.length ≤ s := le_trans (length_le_sz ks) hks
  have h2 : (ks.length + 1) ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h3 : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hk : fKeyLeAR < B := by show 460 < B; omega
  refine Runs.mk (hΔ _ _ Δ_sortAR) ?_
  unfold sortAR
  ev_start
  · ev_run
  · unfold cSort
    have h4 : (800 * (s + 1) ^ 4 + E.cKey s + 10 + 60) * (ks.length + 1) ^ 2 ≤
        (800 * (s + 1) ^ 4 + E.cKey s + 10 + 60) * (s + 1) ^ 2 := Nat.mul_le_mul_left _ h2
    nlinarith

theorem pruned_runs (S : Finset ℕ) (p : RT × AR) (s : ℕ) (hS : sz S ≤ s) (hp : sz p ≤ s)
    (hB : 1000 + 100 * (s + 1) < B) :
    Runs Δ' B fPruned [toVal S, toVal p] (toVal (prunedP S p)) (130 * (s + 1)) := by
  obtain ⟨r, ⟨Sa, c, ka⟩⟩ := p
  have hSa : sz Sa ≤ s := by
    have := sz_S_lt Sa c ka; have := sz_pair_le (a := r) (b := AR.run Sa c ka); omega
  have h1 := card_le_sz S
  have h2 := card_le_sz Sa
  have hsub := Lib3.subset_runs (l3 (Ext.trans extE1 hΔ)) B (by omega) Sa S (decide (Sa ⊆ S)) (by simp)
  have hsub' : Runs Δ' B Lib3.fSubsetS [toVal Sa, toVal S] (toVal (decide (Sa ⊆ S))) (120 * s + 20) :=
    hsub.mono (by omega)
  clear hsub
  refine Runs.mk (hΔ _ _ Δ_pruned) ?_
  simp only [toVal_pair, toVal_ar]
  cases ka with
  | nil =>
    by_cases hs : Sa ⊆ S
    · have : prunedP S (r, AR.run Sa c []) = true := by simp [AR.isLeaf, AR.kids, AR.S, hs]
      rw [this]
      simp only [hs, decide_true] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
    · have : prunedP S (r, AR.run Sa c []) = false := by simp [AR.isLeaf, AR.kids, AR.S, hs]
      rw [this]
      simp only [hs, decide_false] at hsub'
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done) | (simp; omega))
      · omega
  | cons k ks =>
    have : prunedP S (r, AR.run Sa c (k :: ks)) = false := by simp [AR.isLeaf, AR.kids]
    rw [this]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega

theorem notPruned_runs (S : Finset ℕ) (p : RT × AR) (s : ℕ) (hS : sz S ≤ s) (hp : sz p ≤ s)
    (hB : 1000 + 100 * (s + 1) < B) :
    Runs Δ' B fNotPruned [toVal S, toVal p] (toVal (!prunedP S p)) (130 * (s + 1) + 6) := by
  have h1 := pruned_runs hΔ B S p s hS hp hB
  have hk : fPruned < B := by show 462 < B; omega
  refine Runs.mk (hΔ _ _ Δ_notPruned) ?_
  cases hq : prunedP S p
  · simp only [hq] at h1
    simp only [Bool.not_false]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega
  · simp only [hq] at h1
    simp only [Bool.not_true]
    ev_start
    · ev_run
      all_goals (first | omega | (simp; done) | (simp; omega))
    · omega

theorem fstP_runs (ctx : Val) (p : RT × AR) : Runs Δ' B fFstP [ctx, toVal p] (toVal p.1) 3 := by
  obtain ⟨r, a⟩ := p
  refine Runs.mk (hΔ _ _ Δ_fstP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

theorem sndP_runs (ctx : Val) (p : RT × AR) : Runs Δ' B fSndP [ctx, toVal p] (toVal p.2) 3 := by
  obtain ⟨r, a⟩ := p
  refine Runs.mk (hΔ _ _ Δ_sndP) ?_
  simp only [toVal_pair]
  ev_start
  · ev_run
  · omega

/-- local cost of `analyzeNode` -/
def cAN (s ck : ℕ) : ℕ := 1000 * (s + 1) ^ 2 + cSort s ck

theorem analyzeNode_runs (E : Ext5 Δ') (Bd X : Finset ℕ) (kids : List (RT × AR)) (s : ℕ)
    (hBd : sz Bd ≤ s) (hX : sz X ≤ s) (hk : sz kids ≤ s) (hB : 1000 + 100 * (s + 1) + E.cKey s < B) :
    Runs Δ' B fAnalyzeNode [toVal Bd, toVal X, toVal kids] (toVal (analyzeNode Bd X kids)) (cAN s (E.cKey s)) := by
  have hE1 := Ext.trans extE1 hΔ
  have hS := Lib3.inter_runs (l3 hE1) B X Bd
  have hSsz : sz (X ∩ Bd) ≤ s := le_trans (sz_inter_le X Bd) hX
  have hlen : kids.length ≤ s := le_trans (length_le_sz kids) hk
  have hc1 := card_le_sz X
  have hc2 := card_le_sz Bd
  rw [sz_finset] at hX hBd
  have hkp : fPruned < B := by show 462 < B; omega
  have hkn : fNotPruned < B := by show 463 < B; omega
  have hkf : fFstP < B := by show 464 < B; omega
  have hks : fSndP < B := by show 465 < B; omega
  have hf1 := Lib1.filter_runs (l1 hE1) B fPruned (toVal (X ∩ Bd)) (prunedP (X ∩ Bd)) (fun _ => 130 * (s + 1)) kids
    (fun p hp => pruned_runs hΔ B _ p s hSsz (le_trans (sz_le_of_mem hp) hk) (by omega))
  have hf2 := Lib1.filter_runs (l1 hE1) B fNotPruned (toVal (X ∩ Bd)) (fun p => !prunedP (X ∩ Bd) p)
    (fun _ => 130 * (s + 1) + 6) kids
    (fun p hp => notPruned_runs hΔ B _ p s hSsz (le_trans (sz_le_of_mem hp) hk) (by omega))
  simp only [E5.sum_map_const] at hf1 hf2
  have hl1 : (kids.filter (prunedP (X ∩ Bd))).length ≤ kids.length := List.length_filter_le _ _
  have hl2 : (kids.filter (fun p => !prunedP (X ∩ Bd) p)).length ≤ kids.length := List.length_filter_le _ _
  have hm1 := Lib1.map_runs (l1 hE1) B fFstP (Val.nat 0) Prod.fst (fun _ => 3) (kids.filter (prunedP (X ∩ Bd)))
    (fun p _ => fstP_runs hΔ B _ p)
  have hm2 := Lib1.map_runs (l1 hE1) B fSndP (Val.nat 0) Prod.snd (fun _ => 3)
    (kids.filter (fun p => !prunedP (X ∩ Bd) p)) (fun p _ => sndP_runs hΔ B _ p)
  simp only [E5.sum_map_const] at hm1 hm2
  have hjsz : sz ((kids.filter (prunedP (X ∩ Bd))).map Prod.fst) ≤ s :=
    le_trans (sz_map_le' _ _ (fun p _ => (sz_pair_le (a := p.1) (b := p.2)).1))
      (le_trans (sz_filter_le' _ _) hk) |>.trans (le_refl _)
  have hcsz : sz ((kids.filter (fun p => !prunedP (X ∩ Bd) p)).map Prod.snd) ≤ s :=
    le_trans (sz_map_le' _ _ (fun p _ => (sz_pair_le (a := p.1) (b := p.2)).2))
      (le_trans (sz_filter_le' _ _) hk) |>.trans (le_refl _)
  rw [analyzeNode_eq]
  generalize (kids.filter (prunedP (X ∩ Bd))).map Prod.fst = junk at hm1 hjsz ⊢
  generalize (kids.filter (fun p => !prunedP (X ∩ Bd) p)).map Prod.snd = core at hm2 hcsz ⊢
  have hP1 : kids.length * (130 * (s + 1)) ≤ 130 * (s + 1) ^ 2 := by
    calc kids.length * (130 * (s + 1)) ≤ s * (130 * (s + 1)) := Nat.mul_le_mul_right _ hlen
      _ ≤ 130 * (s + 1) ^ 2 := by nlinarith
  have hP2 : kids.length * (130 * (s + 1) + 6) ≤ 136 * (s + 1) ^ 2 := by
    calc kids.length * (130 * (s + 1) + 6) ≤ s * (130 * (s + 1) + 6) := Nat.mul_le_mul_right _ hlen
      _ ≤ 136 * (s + 1) ^ 2 := by nlinarith
  have hs1 : s + 1 ≤ (s + 1) ^ 2 := le_pw (by omega) (by omega)
  have hs2 : 1 ≤ (s + 1) ^ 2 := one_le_pw (by omega) 2
  have hkc : 0 ≤ cSort s (E.cKey s) := Nat.zero_le _
  refine Runs.mk (hΔ _ _ Δ_analyzeNode) ?_
  rcases core with _ | ⟨k, _ | ⟨k2, t⟩⟩
  · simp only [mkNode, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
    simp only [toVal_nil] at hm2
    ev_start
    · ev_run
    · unfold cAN
      omega
  · obtain ⟨Sk, ck, kk⟩ := k
    simp only [toVal_cons, toVal_nil, toVal_ar] at hm2
    have hSk : sz Sk ≤ s := by
      have := sz_S_lt Sk ck kk
      have : sz (AR.run Sk ck kk) < sz [AR.run Sk ck kk] := by rw [sz_cons]; have := sz_pos ([] : List AR); omega
      omega
    by_cases hSkeq : Sk = X ∩ Bd
    · have heq := Lib1.eqV_runs_typed (l1 hE1) B (by omega) Sk (X ∩ Bd) true (by simp [hSkeq])
      simp only [mkNode, AR.S, AR.chain, AR.kids, hSkeq, if_true, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
      have hmin : min (sz (X ∩ Bd)) (sz (X ∩ Bd)) ≤ s := le_trans (min_le_left _ _) hSsz
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done))
      · unfold cAN
        have : 30 * min (sz (X ∩ Bd)) (sz (X ∩ Bd)) ≤ 30 * s := by omega
        omega
    · have heq := Lib1.eqV_runs_typed (l1 hE1) B (by omega) Sk (X ∩ Bd) false (by simp [hSkeq])
      simp only [mkNode, AR.S, AR.chain, AR.kids, hSkeq, if_false, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
      have hmin : min (sz Sk) (sz (X ∩ Bd)) ≤ s := le_trans (min_le_left _ _) hSk
      ev_start
      · ev_run
        all_goals (first | omega | (simp; done))
      · unfold cAN
        have : 30 * min (sz Sk) (sz (X ∩ Bd)) ≤ 30 * s := by omega
        omega
  · have hsort := sortAR_runs hΔ B E (X ∩ Bd) (k :: k2 :: t) s hSsz hcsz hB
    have hksort : fSortAR < B := by show 461 < B; omega
    simp only [toVal_cons, toVal_nil] at hm2
    simp only [mkNode, toVal_ar, toVal_cons, toVal_nil, toVal_cnode]
    simp only [toVal_cons] at hsort
    ev_start
    · ev_run
    · unfold cAN
      omega

/-- constant of the per-node cost of `analyze` (`ck6 = E.cKey (6 s)`) -/
def cA (s ck6 : ℕ) : ℕ := cAN (6 * s) ck6 + 20 * s + 100

mutual
theorem analyze_runs_rec (E : Ext5 Δ') (Bd : Finset ℕ) (s : ℕ) (hBd : sz Bd ≤ s)
    (hB : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B) : ∀ t : RT, sz t ≤ s →
    Runs Δ' B fAnalyze [toVal Bd, toVal t] (toVal (analyze Bd t)) (cA s (E.cKey (6 * s)) * t.size)
  | .node X ks, hs => by
    have hX : sz X ≤ s := by have := sz_rt_X_lt X ks; omega
    have hks : sz ks ≤ s := by have := sz_rt_ks_lt X ks; omega
    have hlen : ks.length ≤ s := le_trans (length_le_sz ks) hks
    have h1 := analyzeNode_runs hΔ B E Bd X (analyzeL Bd ks) (6 * s) (by omega) (by omega)
      (le_trans (sz_analyzeL_le Bd ks) (by omega)) (by omega)
    have h2 := analyzeL_runs_rec E Bd s hBd hB ks hks
    have hka : fAnalyzeL < B := by show 468 < B; omega
    have hkb : fAnalyzeNode < B := by show 466 < B; omega
    refine Runs.mk (hΔ _ _ Δ_analyze) ?_
    simp only [analyze, toVal_rt, RT.size]
    ev_start
    · ev_run
    · have e : cA s (E.cKey (6 * s)) * (1 + RT.sizeL ks) =
          cA s (E.cKey (6 * s)) + cA s (E.cKey (6 * s)) * RT.sizeL ks := by ring
      rw [e]
      unfold cA
      omega
theorem analyzeL_runs_rec (E : Ext5 Δ') (Bd : Finset ℕ) (s : ℕ) (hBd : sz Bd ≤ s)
    (hB : 1000 + 100 * (6 * s + 1) + E.cKey (6 * s) < B) : ∀ ks : List RT, sz ks ≤ s →
    Runs Δ' B fAnalyzeL [toVal Bd, toVal ks] (toVal (analyzeL Bd ks))
      (cA s (E.cKey (6 * s)) * RT.sizeL ks + 20 * ks.length + 8)
  | [], hs => by
    refine Runs.mk (hΔ _ _ Δ_analyzeL) ?_
    simp only [analyzeL, RT.sizeL]
    ev_start
    · ev_run
    · simp
  | k :: ks, hs => by
    have hk : sz k ≤ s := by have := sz_head_lt k ks; omega
    have hks : sz ks ≤ s := by have := sz_tail_lt k ks; omega
    have h1 := analyze_runs_rec E Bd s hBd hB k hk
    have h2 := analyzeL_runs_rec E Bd s hBd hB ks hks
    have hka : fAnalyze < B := by show 467 < B; omega
    have hkb : fAnalyzeL < B := by show 468 < B; omega
    refine Runs.mk (hΔ _ _ Δ_analyzeL) ?_
    simp only [analyzeL, RT.sizeL, toVal_cons, toVal_pair, List.length_cons]
    ev_start
    · ev_run
    · have e : cA s (E.cKey (6 * s)) * (k.size + RT.sizeL ks) =
          cA s (E.cKey (6 * s)) * k.size + cA s (E.cKey (6 * s)) * RT.sizeL ks := by ring
      rw [e]
      omega
end

end proofs

theorem analyze_runs_pair : (type_of% @analyze_runs_rec) ∧ (type_of% @analyzeL_runs_rec) :=
  ⟨@analyze_runs_rec, @analyzeL_runs_rec⟩

theorem analyze_runs : type_of% @analyze_runs_rec := analyze_runs_pair.1

end E5B
end Lax117284Proofs.Treewidth.Fun
