import Lax117284Proofs.Machine.TwIntro2

/-!
The cell of the table of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- The cost of the count of the violations, for a bag of `l` clients and `m` days. -/
def vcost (m l : ℕ) : ℕ :=
  (30 + ((30 + (200 + 10 + 4) * m + 6 + 10 + 4) * l + 6) + ((10 + 10 + 4) * m + 6 + 2) + 20 + 10 +
    4) * l + 6 + 2

lemma vcost_mono (m : ℕ) {l l' : ℕ} (h : l ≤ l') : vcost m l ≤ vcost m l' := by
  unfold vcost; gcongr

lemma violN_le (X : List ℕ) (n m kk : ℕ) (bl : List ℕ) (e : ℕ) :
    violN X n m kk bl e ≤ bl.length * (bl.length * m + 1) := by
  unfold violN
  refine le_trans (Finset.sum_le_sum (g := fun _ => 1 + bl.length * m) fun t ht => ?_) ?_
  · have ht' := Finset.mem_range.1 ht
    have h1 : ∑ t2 ∈ Finset.range t, cfDayN X n m bl[t]! bl[t2]! (dg (2 ^ m) e t)
        (dg (2 ^ m) e t2) ≤ t * m := by
      calc _ ≤ ∑ t2 ∈ Finset.range t, m :=
            Finset.sum_le_sum fun t2 _ => cfDayN_le _ _ _ _ _ _ _
        _ = t * m := by simp
    have h2 : t * m ≤ bl.length * m := Nat.mul_le_mul_right m ht'.le
    split_ifs <;> omega
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [add_comm 1]

/-- The lookup in the table of the child, when there is no violation. -/
def introTail : Com :=
  .ite (.lt (L 0) (V "vi")) (.assign "val" (L 0))
    (seqs [ .assign "lo" (.bin .and (V "e") (sub (V "Pp") (L 1))),
            .assign "hi" (.bin .shiftr (V "e") (V "shp1")),
            .assign "rm" (add (V "lo") (mul (V "hi") (V "Pp"))),
            .assign "val" (G "TB" (add (V "cbase") (V "rm"))) ])

theorem introTail_run (σ : Env) (m p e cb : ℕ) (hPp : σ.vars "Pp" = 2 ^ (m * p))
    (hsh : σ.vars "shp1" = m * (p + 1)) (he : σ.vars "e" = e) (hcb : σ.vars "cbase" = cb)
    (hidx : cb + rmN (2 ^ m) p e < (σ.arrs "TB").length)
    (hTB : (σ.arrs "TB").getD (cb + rmN (2 ^ m) p e) 0 < B)
    (hrm : rmN (2 ^ m) p e < B) (hcbB : cb + rmN (2 ^ m) p e < B)
    (hpp : 2 ^ (m * p) < B) (hsB : m * (p + 1) < B) (heB : e < B) (hB : 2 < B)
    (hvi : σ.vars "vi" < B) :
    ∃ σ', Run B introTail σ σ' 40 ∧
      σ'.vars "val" = (if σ.vars "vi" = 0 then (σ.arrs "TB").getD (cb + rmN (2 ^ m) p e) 0
        else 0) ∧
      σ'.arrs = σ.arrs ∧ (∀ y, y ∉ ["lo", "hi", "rm", "val"] → σ'.vars y = σ.vars y) ∧
      σ'.out = σ.out := by
  have hrs := rmN_shift m p e
  have hlo : Nat.land e (2 ^ (m * p) - 1) < B := by omega
  have hhp : e / 2 ^ (m * (p + 1)) * 2 ^ (m * p) < B := by omega
  have hhi : e / 2 ^ (m * (p + 1)) < B := lt_of_le_of_lt (Nat.div_le_self _ _) heB
  unfold introTail seqs
  run_vcg
  all_goals (try nrmA)
  all_goals try (first | omega | exact hTB | (simp only [hPp, hsh, he, hcb, ← hrs]; first | omega | exact hTB | exact hidx))
  · refine ⟨?_, trivial, ?_, trivial⟩
    · rw [if_neg (by omega)]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hy.2.2.2]
  · refine ⟨?_, trivial, ?_, trivial⟩
    · simp only [hPp, hsh, he, hcb, ← hrs]
      rw [if_pos (by omega)]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]

end Lax117284Proofs.Machine.TwNode
