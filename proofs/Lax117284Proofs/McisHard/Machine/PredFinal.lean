import Lax117284Proofs.McisHard.Machine.PredMain

/-!
# The Adjacency Bit of `H` on the Machine: the Final Theorem (WP6)

`bitCom_run`: given the state `SatAccept.prepSat` leaves (the stream `ns` in `TK`, `N`, `A2`), the command `bitCom`
writes `adjF ns w w2` to `bt`; `bitCom_run_M` is the same about `adjM`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Bit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem

/-- The cost of one bit, on `N` positions. -/
def Kbit (N : ℕ) : ℕ := 128 * N + 1500

/-- The scratch scalars of `bitCom`: `bt`, the scalars of `SatRank.rankCom` (`o vo so j vj sj cnt`) and names
starting with `b`. -/
@[simp] def AB : List String := ["bTi", "bTj", "bTu", "bTv", "bTn"] ++ ATree

set_option maxRecDepth 100000 in
theorem bitCom_fspec {B : ℕ} (ns : List ℕ) (hP : Pars B ns) :
    Spec B (fun σ => Ctx[ns, σ] ∧ σ.vars "w" < B ∧ σ.vars "w2" < B) bitCom
      (fun σ σ' => (σ'.vars "bt" = ind (adjM ns (σ.vars "w") (σ.vars "w2")) ∧ σ'.vars "bt" ≤ 1) ∧
        Fr AB σ σ' ∧ Ctx[ns, σ']) (Kbit (SlotsN ns)) :=
  (frSpecC (bitCom_spec ns hP) AB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).post fun _ σ' _ ⟨hq, hf⟩ => ⟨⟨hq, hq ▸ ind_le _⟩, hf⟩

/-- The standing assumptions of the commands, from the hypotheses of the reduction. -/
theorem pars_of (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) : Pars B ns :=
  ⟨hs.2.1, fun k => by
    by_cases hk : k < 3 + 2 * SlotsN ns
    · exact hE k hk
    · rw [List.getD_eq_default _ _ (by have := hs.2.1; omega)]; omega,
    hB, fun o ho => hs.2.2 o ho⟩

/-- **The adjacency bit, in the shape the machine computes it.** -/
theorem bitCom_run_M (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (σ : Env) (hA : σ.arrs "TK" = ns) (hN : σ.vars "N" = SlotsN ns)
    (hA2 : σ.vars "A2" = 2 * ns.getD 1 0) (w w2 : ℕ) (hw : σ.vars "w" = w) (hw2 : σ.vars "w2" = w2)
    (hwB : w < B) (hw2B : w2 < B) :
    ∃ σ', Run B bitCom σ σ' (Kbit (SlotsN ns)) ∧ σ'.vars "bt" = ind (adjM ns w w2) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ∉ AB → σ'.vars y = σ.vars y := by
  obtain ⟨σ', hr, ⟨hq, -⟩, ⟨harr, hout, hinp, hfr⟩, -⟩ :=
    bitCom_fspec ns (pars_of B ns hs hB hE) σ ⟨⟨hA, hN, hA2⟩, hw ▸ hwB, hw2 ▸ hw2B⟩
  refine ⟨σ', hr, ?_, harr, hout, hinp, hfr⟩
  rw [hq, hw, hw2]

open Classical in
/-- **The adjacency bit.**  Started with the stream `ns` in `TK`, `N`, `A2` as `prepSat` leaves them, and
two vertex numbers `w`, `w2` (below the word bound) in the scalars `w`, `w2`, the command leaves the bit
`adjF ns w w2` in `bt`. -/
theorem bitCom_run (B : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns)
    (hB : 60 * (SlotsN ns + 4) < B) (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (σ : Env) (hA : σ.arrs "TK" = ns) (hN : σ.vars "N" = SlotsN ns)
    (hA2 : σ.vars "A2" = 2 * ns.getD 1 0) (w w2 : ℕ) (hw : σ.vars "w" = w) (hw2 : σ.vars "w2" = w2)
    (hwB : w < B) (hw2B : w2 < B) :
    ∃ σ', Run B bitCom σ σ' (Kbit (SlotsN ns)) ∧
      σ'.vars "bt" = (if decide (adjF ns w w2) then 1 else 0) ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      ∀ y, y ∉ AB → σ'.vars y = σ.vars y := by
  obtain ⟨σ', hr, hbt, h1, h2, h3, h4⟩ := bitCom_run_M B ns hs hB hE σ hA hN hA2 w w2 hw hw2 hwB hw2B
  refine ⟨σ', hr, ?_, h1, h2, h3, h4⟩
  rw [hbt, ind_congr (adjM_iff_adjF ns hs hc w w2)]
  unfold ind
  simp

end Lax117284Proofs.McisHard.Bit
