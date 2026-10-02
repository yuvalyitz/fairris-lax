import Lax117284Proofs.Treewidth.Fun.E5Util
import Lax117284Proofs.Treewidth.Fun.ToValAlg

/-!
# WP E5 (1): the external functions E5 calls, as hypotheses

`E5` embeds `analyze … realJoin`; these call functions owned by other work packages:

| function | owner | id | shape of the hypothesis |
|---|---|---|---|
| `CT.norm` | E2 | `166` (`E5.idNorm`) | `Ext5.norm` : `Runs` for `sz c ≤ s`, cost `cNorm s`, plus `sz (norm c) ≤ sz c` |
| `decide (CT.key S a ≤ CT.key S b)` | E2 | `162` (`E5.idKeyLe`) | `Ext5.keyLe` |
| `CT.domCB` | E2 | `181` (`E5.idDomC`) | `Ext5.domC` (precondition `Ext5.PD`) |
| `CT.joinC` | E2 | `177` (`E5.idJoinC`) | `ExtJ` (precondition `PJ`, cost `cJ`) |
| `CT.introPlans` | E3 | passed at run time (first argument of `realIntro`) | `ExtIP` (precondition `PIP`, cost `cIP`) |

The E2 ids are those of the docstring table of `Fun/E2Defs.lean` (contract: the assembler must use them, or re-point
`E5.idNorm …`).  Every hypothesis has the same shape as the corresponding `E2`/`E3` theorem
(`E2.norm_runs`, `E2.keyLe_runs`, …): *for every `B` above the cost, the function runs within the cost*.  The cost functions
are abstract (`ℕ → ℕ` in the size bound `s`), so nothing here depends on the constants of E2/E3.
-/

namespace Lax117284Proofs.Treewidth.Fun
namespace E5

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees

abbrev idKeyLe : ℕ := 162
abbrev idNorm : ℕ := 166
abbrev idJoinC : ℕ := 177
abbrev idDomC : ℕ := 181

/-- The E2 functions used by `sortAR`, `RT.char`, `realIntro`, `realJoin`. -/
structure Ext5 (Δ' : ℕ → Option Tm) where
  cKey : ℕ → ℕ
  keyLe : ∀ (B s : ℕ) (S : Finset ℕ) (a b : CT), sz S ≤ s → sz a ≤ s → sz b ≤ s → cKey s < B →
    Runs Δ' B idKeyLe [toVal S, toVal a, toVal b] (toVal (decide (CT.key S a ≤ CT.key S b))) (cKey s)
  cNorm : ℕ → ℕ
  norm : ∀ (B s : ℕ) (c : CT), sz c ≤ s → cNorm s < B →
    Runs Δ' B idNorm [toVal c] (toVal (CT.norm c)) (cNorm s)
  norm_sz : ∀ c : CT, sz (CT.norm c) ≤ sz c
  /-- precondition of `domCB` (E2: run sequences of both arguments have length `≤ L`, `CT.RB`) -/
  PD : ℕ → CT → CT → Prop
  cDom : ℕ → ℕ
  domC : ∀ (B s : ℕ) (a b : CT), PD s a b → sz a ≤ s → sz b ≤ s → cDom s < B →
    Runs Δ' B idDomC [toVal a, toVal b] (toVal (CT.domCB a b)) (cDom s)

/-- `CT.joinC` (E2). -/
structure ExtJ (Δ' : ℕ → Option Tm) where
  PJ : ℕ → CT → CT → Prop
  cJ : ℕ → CT → CT → ℕ
  joinC : ∀ (B kmax : ℕ) (a b : CT), PJ kmax a b → cJ kmax a b < B →
    Runs Δ' B idJoinC [toVal kmax, toVal a, toVal b] (toVal (CT.joinC kmax a b)) (cJ kmax a b)

/-- `CT.introPlans` (E3), called through the id `ip`. -/
structure ExtIP (Δ' : ℕ → Option Tm) where
  ip : ℕ
  PIP : ℕ → Finset ℕ → CT → Prop
  cIP : ℕ → Finset ℕ → CT → ℕ
  introPlans : ∀ (B v : ℕ) (N : Finset ℕ) (t : CT), PIP v N t → cIP v N t < B →
    Runs Δ' B ip [toVal v, toVal N, toVal t] (toVal (CT.introPlans v N t)) (cIP v N t)

end E5
end Lax117284Proofs.Treewidth.Fun
