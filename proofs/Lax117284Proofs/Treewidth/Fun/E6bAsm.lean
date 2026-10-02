import Lax117284Proofs.Treewidth.Fun.E6bCand

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# WP E6b (10): the assembly lemmas of `fExtract` (callee facts as hypotheses, small contexts)
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E6b

open ToVal Lib1 Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT
open E4 (adjOfWord nOfWord)

section asm
variable {Δ' : ℕ → Option Tm} (hΔ : Ext6 Δ') (B : ℕ)
include hΔ

theorem leaf_asm (x : List ℕ) (k : ℕ) (target : CT) (hB : 500 < B) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal NT.leaf, toVal target]
      (toVal (some (RT.node ∅ []) : Option RT)) 10 := by
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_leaf]
  ev_start
  · ev_run
  · omega

theorem forget_ext_asm (x : List ℕ) (k y : ℕ) (c : NT) (target : CT) (T : List CT) (r : Option RT) (Ct Cs C : ℕ)
    (hB : 1000 < B) (hk : k + 1 < B)
    (hT : Runs Δ' B E4.fTables [toVal x, toVal k, toVal c] (toVal T) Ct)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fFgCand, toVal (x, k, y, c, target), toVal T] (toVal r) Cs)
    (hC : 60 + Ct + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.forget y c), toVal target] (toVal r) C := by
  have h1 : fFgCand < B := by show 705 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_forget, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem intro_ext_asm (x : List ℕ) (k v : ℕ) (c : NT) (target : CT) (T : List CT) (N : Finset ℕ) (r : Option RT)
    (Ct Cbag Cnb Cs C : ℕ) (hB : 1000 < B) (hk : k + 1 < B)
    (hT : Runs Δ' B E4.fTables [toVal x, toVal k, toVal c] (toVal T) Ct)
    (hbag : Runs Δ' B E4.fNtBag [toVal c] (toVal c.bag) Cbag)
    (hnb : Runs Δ' B E4.fNbrs [toVal x, toVal v, toVal c.bag] (toVal N) Cnb)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fInCand, toVal ((k + 1, v, N), x, k, c, c.bag, target), toVal T]
      (toVal r) Cs)
    (hC : 100 + Ct + Cbag + Cnb + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.intro v c), toVal target] (toVal r) C := by
  have h1 : fInCand < B := by show 706 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_intro, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem join_ext_asm (x : List ℕ) (k : ℕ) (a b : NT) (target : CT) (Ta Tb : List CT) (r : Option RT)
    (Cta Ctb Cbag Cs C : ℕ) (hB : 1000 < B)
    (hTa : Runs Δ' B E4.fTables [toVal x, toVal k, toVal a] (toVal Ta) Cta)
    (hTb : Runs Δ' B E4.fTables [toVal x, toVal k, toVal b] (toVal Tb) Ctb)
    (hbag : Runs Δ' B E4.fNtBag [toVal a] (toVal a.bag) Cbag)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fJnOuter, toVal ((x, k, a, b, a.bag, target), Tb), toVal Ta]
      (toVal r) Cs)
    (hC : 100 + Cta + Ctb + Cbag + Cs ≤ C) :
    Runs Δ' B fExtract [toVal x, toVal k, toVal (NT.join a b), toVal target] (toVal r) C := by
  have h1 : fJnOuter < B := by show 707 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_extract) ?_
  simp only [toVal_nt_join, toVal_pair] at *
  ev_start
  · ev_run
  · omega

theorem jnOuter_asm (x : List ℕ) (k : ℕ) (a b : NT) (target ca : CT) (Tb : List CT) (r : Option RT) (Cs C : ℕ)
    (hB : 1000 < B)
    (hS : Runs Δ' B Lib4.fFindSome [Val.nat fJnInner, toVal (ca, x, k, a, b, a.bag, target), toVal Tb]
      (toVal r) Cs) (hC : 20 + Cs ≤ C) :
    Runs Δ' B fJnOuter [toVal ((x, k, a, b, a.bag, target), Tb), toVal ca] (toVal r) C := by
  have h1 : fJnInner < B := by show 708 < B; omega
  refine Runs.mk (hΔ.e6 _ _ Δ_jnOuter) ?_
  simp only [toVal_pair] at *
  ev_start
  · ev_run
  · omega

end asm

end E6b
end Lax117284Proofs.Treewidth.Fun
