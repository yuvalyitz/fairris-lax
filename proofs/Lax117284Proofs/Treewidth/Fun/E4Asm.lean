import Lax117284Proofs.Treewidth.Fun.E4Base

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-!
# WP E4 (3b): the three recursion steps of `fTables`, with the callee facts as hypotheses

Small contexts (no numerics), so that `ev_run` and its `simp` side goals are fast.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E4

open ToVal Lib1 Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT

section asm
variable {Δ' : ℕ → Option Tm} (hΔ : Ext4 Δ') (B : ℕ)
include hΔ

theorem forget_assemble (x : List ℕ) (k y : ℕ) (c : NT) (T R : List CT) (Cc CF C : ℕ) (hB : 500 < B)
    (IH : Runs Δ' B fTables [toVal x, toVal k, toVal c] (toVal T) Cc)
    (hF : Runs Δ' B fForgetTable [toVal y, toVal T] (toVal R) CF) (hC : 60 + Cc + CF ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.forget y c)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_forget]
  ev_start
  · ev_run
  · omega

theorem intro_assemble (x : List ℕ) (k v : ℕ) (c : NT) (T R : List CT) (N : Finset ℕ) (Cc Cbag Cnb CI C : ℕ)
    (hB : 500 < B) (hk : k + 1 < B)
    (IH : Runs Δ' B fTables [toVal x, toVal k, toVal c] (toVal T) Cc)
    (hbag : Runs Δ' B fNtBag [toVal c] (toVal c.bag) Cbag)
    (hnb : Runs Δ' B fNbrs [toVal x, toVal v, toVal c.bag] (toVal N) Cnb)
    (hI : Runs Δ' B fIntroTable [toVal (k + 1), toVal v, toVal N, toVal T] (toVal R) CI)
    (hC : 100 + Cc + Cbag + Cnb + CI ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.intro v c)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_intro]
  ev_start
  · ev_run
  · omega

theorem join_assemble (x : List ℕ) (k : ℕ) (a b : NT) (Ta Tb : List CT) (R : List CT) (Ca Cb CJ C : ℕ)
    (hB : 500 < B) (hk : k + 1 < B)
    (IHa : Runs Δ' B fTables [toVal x, toVal k, toVal a] (toVal Ta) Ca)
    (IHb : Runs Δ' B fTables [toVal x, toVal k, toVal b] (toVal Tb) Cb)
    (hJ : Runs Δ' B fJoinTable [toVal (k + 1), toVal Ta, toVal Tb] (toVal R) CJ)
    (hC : 100 + Ca + Cb + CJ ≤ C) :
    Runs Δ' B fTables [toVal x, toVal k, toVal (NT.join a b)] (toVal R) C := by
  refine Runs.mk (hΔ.e4 _ _ Δ_tables) ?_
  simp only [toVal_nt_join]
  ev_start
  · ev_run
  · omega

end asm

end E4
end Lax117284Proofs.Treewidth.Fun
