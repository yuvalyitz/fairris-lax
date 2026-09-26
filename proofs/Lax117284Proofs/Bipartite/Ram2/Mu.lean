import Lax808846Proofs.Reasoning
import Lax808846Proofs.Tactic

/-!
The matching array: the machine-level version of `Matching.μ : R → Option L`.

Right vertex `j`'s cell holds `0` if `j` is unmatched, or `l + 1` if `j` is matched to left
vertex `l` — shifting by one so `0` is free to mean "nothing here", the usual encoding for an
optional value in a word.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile

variable {B : ℕ}

/-- The `"mu"` array agrees with `μ`, encoding `none` as `0` and `some l` as `l + 1`, for every
right vertex below `m`. -/
def MuOK (μ : ℕ → Option ℕ) (m : ℕ) (σ : Env) : Prop :=
  (σ.arrs "mu").length = m ∧
    ∀ j < m, (σ.arrs "mu").getD j 0 = match μ j with | none => 0 | some l => l + 1

/-- Read `mu[j]` into `occ`, as the shifted encoding: `0` for unmatched, `l + 1` for `some l`. -/
def readMu (j occ : String) : Com := .assign occ (.get "mu" (.var j))

/-- Write `mu[j] := l + 1`, recording that right vertex `j` is now matched to left vertex `l`. -/
def writeMu (j l : String) : Com := .store "mu" (.var j) (.add (.var l) (.lit 1))

@[simp] theorem warrs_writeMu (j l : String) : (writeMu j l).warrs = ["mu"] := by
  simp [writeMu, Com.warrs]

/-- **Recording that `j` is now matched to `l`.** -/
theorem writeMu_spec {μ : ℕ → Option ℕ} {m j lv nB : ℕ} (h1B : 1 < B) (hmB : m < B)
    (hlB : lv + 1 < nB) (hnB : nB ≤ B) (hjm : j < m) (jn ln : String) :
    Spec B (fun σ => MuOK μ m σ ∧ σ.vars jn = j ∧ σ.vars ln = lv) (writeMu jn ln)
      (fun _ σ' => MuOK (Function.update μ j (some lv)) m σ') 5 := by
  intro σ ⟨⟨hlen, hval⟩, hjv, hlv⟩
  have hidxlt : j < (σ.arrs "mu").length := by omega
  have hjB : σ.vars jn < B := by omega
  have hlnB : σ.vars ln < B := by omega
  have hi : (Expr.var jn).evalB B σ = some j := by rw [evalB_var hjB, hjv]
  have hbop : Bop.add.apply (σ.vars ln) 1 = σ.vars ln + 1 := rfl
  have hget : (Expr.add (.var ln) (.lit 1)).evalB B σ = some (lv + 1) := by
    rw [show Expr.add (.var ln) (Expr.lit 1) = Expr.bin Bop.add (.var ln) (.lit 1) from rfl]
    rw [evalB_bin (evalB_var hlnB) (evalB_lit (n := 1) (by omega)) (by rw [hbop]; omega), hbop, hlv]
  have hst : Run B (writeMu jn ln) σ (σ.setArr "mu" j (lv + 1)) 5 :=
    Run.store hi hget hidxlt
  refine ⟨σ.setArr "mu" j (lv + 1), hst, ?_⟩
  constructor
  · simpa using hlen
  · intro k hk
    by_cases hkj : k = j
    · subst hkj
      simp [Function.update_self, List.getD_eq_getElem?_getD, hidxlt]
    · have := hval k hk
      simp [Function.update_of_ne hkj, List.getD_eq_getElem?_getD, Ne.symm hkj]
      rwa [← List.getD_eq_getElem?_getD]

end Lax117284Proofs.Bipartite.Ram2
