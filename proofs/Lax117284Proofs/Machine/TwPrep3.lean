import Lax117284Proofs.Machine.TwPrep2

/-!
The preparation of the main program: the constants of the word, the logarithm of its length, the
number of admitted widths, and the word length and memory size of the simulated machine.
-/

namespace Lax117284Proofs.Machine.TwPrep

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {B : ℕ}

theorem wcLoop_run (cc : ℕ) (σ0 : Env) (m ℓ : ℕ) (hcc : 1 ≤ cc) (hccB : cc < B)
    (hm : σ0.vars "m" = m) (hlg1 : σ0.vars "lg1" = ℓ + 1) (hwc0 : σ0.vars "wc" = 0)
    (hgB : geE cc m ℓ + 3 < B) (hℓ : ℓ + 3 < B) :
    ∃ σ', Run B (wcLoop cc) σ0 σ' ((40 + 10 + 4) * (ℓ + 1) + 6) ∧ σ'.vars "wc" = wcnt cc m ℓ ∧
      Agr ["j", "wc"] σ0 σ' ∧ σ'.out = σ0.out := by
  have hf := fLoop_spec (B := B) "j" "lg1" "wc" (wcBody cc) ["j", "wc"]
    (fun j a => a + (if geE cc m j < ℓ + 1 then 1 else 0)) (fun j a => a ≤ j) 40 (ℓ + 1) σ0
    (by simp) (by simp) (by decide) hlg1 (by omega) (by omega)
    (fun j a h => by split_ifs <;> omega)
    (by
      intro σ hA hlt hQ
      have hfr : ∀ y, y ∉ ["j", "wc"] → σ.vars y = σ0.vars y := hA.2
      have e1 : σ.vars "m" = m := by rw [hfr "m" (by simp)]; exact hm
      have e2 : σ.vars "lg1" = ℓ + 1 := by rw [hfr "lg1" (by simp)]; exact hlg1
      have hjl : σ.vars "j" < ℓ + 1 := hlt
      have hge : geE cc m (σ.vars "j") ≤ geE cc m ℓ := geE_mono cc m (by omega)
      obtain ⟨σ', r, hv, hA', hj, ho⟩ := wcBody_run (B := B) cc σ hcc hccB
        (by rw [e1]; omega) (by rw [e2]; omega) (by have := hQ; omega)
      refine ⟨σ', r, ?_, agr_comp (S := ["j", "wc"]) hA hA' (by intro x hx; exact hx)
        (by intro x hx; simp at hx; simp [hx]), hj, ho⟩
      rw [hv, e1, e2])
  obtain ⟨σ', r, hv, hA, ho⟩ := hf
  refine ⟨σ', r, ?_, hA, ho⟩
  rw [hv, hwc0, Lax117284Proofs.TwViol.foldl_add_range]
  simp only [wcnt, Nat.zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : geE cc m j ≤ ℓ
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- The constants of the word. -/
def prepPre : Com := seqs
  [ .assign "mn" (mul (V "m") (V "n")),
    .assign "lg" (Expr.lit 0) ]

/-- The digit that holds every day, and the base of the digits: only when the guard holds, since
`2 ^ m` may otherwise be far more than the word can hold. -/
def maskCom : Com := seqs
  [ .assign "mask" (sub (.bin .shiftl (Expr.lit 1) (V "m")) (Expr.lit 1)),
    .assign "bb" (.bin .shiftl (Expr.lit 1) (V "m")) ]

/-- The bound of the loop over the widths. -/
def prepMid : Com := seqs
  [ .assign "lg1" (add (V "lg") (Expr.lit 1)), .assign "wc" (Expr.lit 0) ]

/-- The guard flag. -/
def okCom : Com := seqs
  [ .assign "ok" (Expr.lit 0),
    .ite (.lt (Expr.lit 0) (V "wc"))
      (.ite (.lt (Expr.lit 0) (V "m")) (.assign "ok" (Expr.lit 1)) .skip) .skip ]

/-- The width, the word length and the memory of the simulated machine. -/
def prepTail (cc plit : ℕ) : Com := seqs
  [ .assign "w" (sub (V "wc") (Expr.lit 1)),
    .assign "wp" (add (add (mul (Expr.lit (2 * cc + 1)) (V "lg")) (Expr.lit (4 * cc)))
      (Expr.lit plit)),
    .assign "P" (.bin .shiftl (Expr.lit 1) (V "wp")) ]

/-- The guard, the width, the word length and the memory of the simulated machine. -/
def prepPost (cc plit : ℕ) : Com := .seq okCom (prepTail cc plit)

/-- The preparation. -/
def prepCom (cc plit : ℕ) : Com :=
  .seq prepPre (.seq lgLoop (.seq prepMid (.seq (wcLoop cc) (prepPost cc plit))))

/-- The scalars the preparation writes. -/
def SPrep : List String :=
  ["mn", "lg", "j", "lg1", "wc", "ok", "w", "wp", "P"]

theorem prepPre_run (σ : Env) (n m : ℕ) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hmn : m * n + 3 < B) (hnB : n + 3 < B) (hmB : m + 3 < B) :
    ∃ σ1, Run B prepPre σ σ1 40 ∧ σ1 = (σ.setVar "mn" (m * n)).setVar "lg" 0 := by
  unfold prepPre seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hn, hm]; omega))
  all_goals (try simp only [hn, hm, one_mul])

theorem maskCom_run (σ : Env) (m : ℕ) (hm : σ.vars "m" = m) (h2m : 2 ^ m + 3 < B) :
    ∃ σ1, Run B maskCom σ σ1 30 ∧ σ1 = (σ.setVar "mask" (2 ^ m - 1)).setVar "bb" (2 ^ m) := by
  have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
  have h12 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  unfold maskCom seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hm]; omega))
  all_goals (try simp only [hm, one_mul])

theorem prepMid_run (σ : Env) (lg : ℕ) (hlg : σ.vars "lg" = lg) (hB : lg + 3 < B) :
    ∃ σ1, Run B prepMid σ σ1 20 ∧ σ1 = (σ.setVar "lg1" (lg + 1)).setVar "wc" 0 := by
  unfold prepMid seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hlg]; omega))
  all_goals (try simp only [hlg])

theorem okCom_run (σ : Env) (hB : 3 < B) (hwc : σ.vars "wc" < B) (hm : σ.vars "m" < B) :
    ∃ σ1, Run B okCom σ σ1 30 ∧
      σ1.vars "ok" = (if 0 < σ.vars "wc" ∧ 0 < σ.vars "m" then 1 else 0) ∧ σ1.arrs = σ.arrs ∧
      (∀ y, y ≠ "ok" → σ1.vars y = σ.vars y) ∧ σ1.out = σ.out := by
  unfold okCom seqs
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrm
       simp only [vars_setVar, ↓reduceIte, String.reduceEq] at *
       first
         | rw [if_pos ⟨by omega, by omega⟩]
         | rw [if_neg (by omega)])
    | omega

theorem prepTail_run (cc plit : ℕ) (σ : Env) (wc lg : ℕ) (hwc : σ.vars "wc" = wc)
    (hlg : σ.vars "lg" = lg) (hwcB : wc + 3 < B)
    (hwp : (2 * cc + 1) * lg + 4 * cc + plit + 3 < B)
    (hP : 2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) + 3 < B)
    (hccB : 2 * cc + 1 + 3 < B) (h4 : 4 * cc + 3 < B) (hpl : plit + 3 < B) (hlgB : lg + 3 < B) :
    ∃ σ1, Run B (prepTail cc plit) σ σ1 60 ∧ σ1 = ((σ.setVar "w" (wc - 1)).setVar "wp"
      ((2 * cc + 1) * lg + 4 * cc + plit)).setVar "P"
      (2 ^ ((2 * cc + 1) * lg + 4 * cc + plit)) := by
  have hpp : (2 * cc + 1) * lg ≤ (2 * cc + 1) * lg + 4 * cc + plit := by omega
  unfold prepTail seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hwc, hlg]; omega))
  all_goals (try simp only [hwc, hlg, one_mul])

theorem prepPost_run (cc plit : ℕ) (σ : Env) (wc m lg : ℕ) (hwc : σ.vars "wc" = wc)
    (hm : σ.vars "m" = m) (hlg : σ.vars "lg" = lg) (hwcB : wc + 3 < B) (hmB : m + 3 < B)
    (hwp : (2 * cc + 1) * lg + 4 * cc + plit + 3 < B)
    (hP : 2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) + 3 < B)
    (hccB : 2 * cc + 1 + 3 < B) (h4 : 4 * cc + 3 < B) (hpl : plit + 3 < B) (hlgB : lg + 3 < B) :
    ∃ σ1, Run B (prepPost cc plit) σ σ1 100 ∧
      σ1.vars "ok" = (if 0 < wc ∧ 0 < m then 1 else 0) ∧ σ1.vars "w" = wc - 1 ∧
      σ1.vars "wp" = (2 * cc + 1) * lg + 4 * cc + plit ∧
      σ1.vars "P" = 2 ^ ((2 * cc + 1) * lg + 4 * cc + plit) ∧
      Agr ["ok", "w", "wp", "P"] σ σ1 ∧ σ1.out = σ.out := by
  obtain ⟨σ2, r2, ho2, ha2, hf2, hu2⟩ := okCom_run (B := B) σ (by omega) (by omega) (by omega)
  have hwc2 : σ2.vars "wc" = wc := by rw [hf2 "wc" (by decide), hwc]
  have hlg2 : σ2.vars "lg" = lg := by rw [hf2 "lg" (by decide), hlg]
  obtain ⟨σ3, r3, e3⟩ := prepTail_run (B := B) cc plit σ2 wc lg hwc2 hlg2 hwcB hwp hP hccB h4 hpl
    hlgB
  refine ⟨σ3, (r2.seq r3).mono (by omega), ?_, ?_, ?_, ?_, ⟨?_, fun y hy => ?_⟩, ?_⟩
  · rw [e3]; simp [Env.setVar, ho2, hwc, hm]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar, ha2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, hf2 y hy.1]
  · rw [e3]; simp [Env.setVar, hu2]

end Lax117284Proofs.Machine.TwPrep
