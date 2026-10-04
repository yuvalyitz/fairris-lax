import Lax117284Proofs.Machine.ClMainRead
import Lax117284Proofs.IlpClientsBridge
import Lax117284Proofs.Machine.ClBruteFinal
import Lax117284Proofs.ExtremeFairness

/-! ### `Lax117284Proofs.Machine.ClMainCrit` -/

section
/-!
The test of the main program: whether the word is long enough for the integer program's word
to be built, `Q n + 2 ≤ |x|`. It is decided by doubling a counter that is held at the length, so
that no value exceeds twice the length, and only when `n * (n + 1) ≤ |x|`, so that the number of
doublings, `2 n² + n + 3`, is itself bounded by a multiple of the length.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One doubling, the counter held at the length. -/
def critStep : Com := seqs [asg "cp" (cap (mul (lit 2) (V "cp")) (V "L")),
  asg "ci" (add (V "ci") (lit 1))]

def critLoop : Com := .seq (asg "ci" (lit 0)) (.while (.lt (V "ci") (V "E")) critStep)

/-- The doubling part: `cp` becomes `min (2 ^ E) L`. -/
def critFit : Com := seqs [
  asg "E" (add (add (mul (lit 2) (mul (V "n") (V "n"))) (V "n")) (lit 3)),
  asg "cp" (lit 1), critLoop,
  .ite (.lt (add (V "cp") (lit 2)) (add (V "L") (lit 1))) (asg "fit" (lit 1)) .skip]

/-- The test: `fit` is `1` when `Q n + 2 ≤ L`. -/
def critCom : Com := seqs [asg "fit" (lit 0),
  .ite (.lt (V "n") (add (dv (V "L") (add (V "n") (lit 1))) (lit 1))) critFit .skip]

variable {B n L : ℕ}

/-- The invariant of the doubling loop. -/
def CI (n L : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "L" = L ∧ σ.vars "E" = 2 * (n * n) + n + 3 ∧
    σ.vars "ci" ≤ 2 * (n * n) + n + 3 ∧ σ.vars "cp" = min (2 ^ σ.vars "ci") L ∧
      σ.vars "fit" = 0

theorem critStep_spec (hL : 1 ≤ L) (hB : 2 * L < B) (hEB : 2 * (n * n) + n + 4 < B) :
    Spec B (fun σ => CI n L σ ∧ σ.vars "ci" < 2 * (n * n) + n + 3) critStep
      (fun σ σ' => CI n L σ' ∧ σ'.vars "ci" = σ.vars "ci" + 1) 40 := by
  run_vcg
  all_goals rename_i hσ hlt
  all_goals obtain ⟨hn, hLv, hE, hci, hcp, hf⟩ := hσ
  have hp : 2 ^ (σ.vars "ci" + 1) = 2 * 2 ^ σ.vars "ci" := by ring
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Env.setVar, hn, hLv, hE, hf]
    · omega
    · rw [hp]; omega
  all_goals omega

theorem critLoop_spec (hL : 1 ≤ L) (hB : 2 * L < B) (hEB : 2 * (n * n) + n + 4 < B) :
    Spec B (fun σ => CI n L (σ.setVar "ci" 0)) critLoop
      (fun _ σ' => CI n L σ' ∧ σ'.vars "ci" = 2 * (n * n) + n + 3) ((40 + 4) * (2 * (n * n) + n + 3) + 6) :=
  Spec.forRangeZero "ci" "E" (CI n L) (2 * (n * n) + n + 3) 40 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (critStep_spec hL hB hEB)

theorem Q_eq (n : ℕ) : Q n = 2 ^ (2 * (n * n) + n + 3) := rfl

/-- What the doubling part starts from. -/
def CP (n L : ℕ) (σ : Env) : Prop := σ.vars "n" = n ∧ σ.vars "L" = L ∧ σ.vars "fit" = 0

theorem critFit_spec (hL : 1 ≤ L) (hnL : n * n + n ≤ L) (hB : 3 * L + 8 < B) :
    Spec B (CP n L) critFit
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (44 * (2 * (n * n) + n + 3) + 100) := by
  have hEB : 2 * (n * n) + n + 4 < B := by omega
  run_vcg [critLoop_spec (n := n) (L := L) hL (by omega) hEB]
  all_goals try obtain ⟨hn, hLv, hf⟩ := ‹CP n L σ›
  all_goals try (simp only [hn]; omega)
  · rename_i w hCI hc
    obtain ⟨⟨-, hLw, -, -, hcp, -⟩, hci⟩ := hCI
    rw [hci, ← Q_eq] at hcp
    simp only [Env.setVar, if_true]
    rw [if_pos]; omega
  · rename_i w hCI hc
    obtain ⟨⟨-, hLw, -, -, hcp, hfw⟩, hci⟩ := hCI
    rw [hci, ← Q_eq] at hcp
    rw [hfw, if_neg]; omega
  · simp [CI, Env.setVar, hn, hLv, hf]; omega
  all_goals (rename_i w hCI; obtain ⟨⟨-, hLw, -, -, hcp, -⟩, -⟩ := hCI; omega)

theorem Q_gt (hn : L < n * n + n) : L < Q n := by
  have := @Nat.lt_two_pow_self (2 * (n * n) + n + 3)
  rw [Q_eq]; omega

theorem critCom_spec (hL : 1 ≤ L) (hnB : n + 1 < B) (hB : 3 * L + 8 < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "L" = L) critCom
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (90 * L + 300) := by
  have hcs : Spec B (fun σ => CP n L σ ∧ n * n + n ≤ L) critFit
      (fun _ σ' => σ'.vars "fit" = if Q n + 2 ≤ L then 1 else 0) (88 * L + 240) :=
    fun σ ⟨h1, h2⟩ => Spec.mono (critFit_spec hL h2 hB) (by omega) σ h1
  run_vcg [hcs]
  · assumption
  · rename_i hn hL' hc
    simp [Env.setVar, hn, hL'] at hc ⊢
    have h1 : L / (n + 1) < n := by omega
    have h2 : L < n * (n + 1) := (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mp h1
    have := Q_gt (n := n) (L := L) (by nlinarith)
    omega
  · rename_i hn hL'
    have := Nat.div_le_self L (n + 1)
    simp [Env.setVar, hn, hL']
    omega
  · rename_i hn hL'
    have := Nat.div_le_self L (n + 1)
    simp [Env.setVar, hn, hL']
    omega
  · rename_i hn hL' hc
    simp [Env.setVar, hn, hL'] at hc
    have h1 : n ≤ L / (n + 1) := by omega
    have h2 : n * (n + 1) ≤ L := (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mp h1
    exact ⟨⟨by simp [CP, Env.setVar, hn, hL'], by simp [CP, Env.setVar, hn, hL'], by simp [CP, Env.setVar]⟩,
      by nlinarith⟩

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainWp` -/

section
/-!
The word length of the oracle: the least power of two that is at least `c1 * (2 * zl + m + 1) ^ E`,
found by doubling; `wpv` is its exponent and `Mp` the power itself.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The doubling of the power, one step. -/
def wpStep : Com := seqs [asg "Mp" (mul (lit 2) (V "Mp")), asg "wpv" (add (V "wpv") (lit 1))]

def wpLoop : Com := .while (.lt (V "Mp") (V "tg")) wpStep

/-- `E` multiplications of `tg` by `bs`. -/
def mulSteps : ℕ → Com
  | 0 => .skip
  | n + 1 => .seq (asg "tg" (mul (V "tg") (V "bs"))) (mulSteps n)

/-- The exponent `wpv` and the power `Mp` for the target `tg = c1 * (2 * zl + m + 1) ^ E`. -/
def wpCom (c1 E : ℕ) : Com := seqs [
  asg "bs" (add (add (mul (lit 2) (V "zl")) (V "m")) (lit 1)),
  asg "tg" (lit c1), mulSteps E, asg "wpv" (lit 0), asg "Mp" (lit 1), wpLoop]

variable {B tg zl m : ℕ} {σ : Env}

/-- The invariant of the doubling. -/
def WI (tg : ℕ) (σ : Env) : Prop :=
  σ.vars "tg" = tg ∧ σ.vars "Mp" = 2 ^ σ.vars "wpv" ∧ (σ.vars "wpv" = 0 → σ.vars "Mp" = 1) ∧
    (0 < σ.vars "wpv" → σ.vars "Mp" < 2 * tg)

theorem WI.mp_lt (h : WI tg σ) (h1 : 1 ≤ tg) (hB : 2 * tg < B) : σ.vars "Mp" < B := by
  by_cases hw : σ.vars "wpv" = 0
  · rw [h.2.2.1 hw]; omega
  · have := h.2.2.2 (Nat.pos_of_ne_zero hw); omega

theorem wpStep_spec (h1 : 1 ≤ tg) (hB : 2 * tg < B) :
    Spec B (fun σ => WI tg σ ∧ (Cond.lt (V "Mp") (V "tg")).evalB B σ = some true) wpStep
      (fun σ σ' => WI tg σ' ∧ tg - σ'.vars "Mp" < tg - σ.vars "Mp") 40 := by
  have key : ∀ σ : Env, WI tg σ ∧ (Cond.lt (V "Mp") (V "tg")).evalB B σ = some true →
      WI tg σ ∧ σ.vars "Mp" < tg := fun σ ⟨h, hv⟩ =>
    ⟨h, by have := lt_of_condLt_true hv; rw [h.1] at this; exact this⟩
  refine Spec.pre (P := fun σ => WI tg σ ∧ σ.vars "Mp" < tg) ?_ key
  run_vcg
  all_goals obtain ⟨ht, hM, h0, hp⟩ := ‹WI tg σ›
  all_goals have hw : σ.vars "wpv" < 2 ^ σ.vars "wpv" := Nat.lt_two_pow_self
  all_goals have hpos : 1 ≤ 2 ^ σ.vars "wpv" := Nat.one_le_two_pow
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Env.setVar, ht, hM, pow_succ]
    all_goals omega
  all_goals simp [Env.setVar]
  all_goals omega

theorem wpLoop_spec (h1 : 1 ≤ tg) (hB : 2 * tg < B) :
    Spec B (WI tg) wpLoop
      (fun _ σ' => σ'.vars "Mp" = 2 ^ σ'.vars "wpv" ∧ tg ≤ σ'.vars "Mp" ∧ σ'.vars "Mp" ≤ 2 * tg ∧
        σ'.vars "wpv" = Nat.clog 2 tg)
      ((1 + 3 + 40) * tg + 1 + 3) := by
  have hs : (Cond.lt (V "Mp") (V "tg")).size = 3 := by simp
  refine (Spec.while_count (B := B) (b := Cond.lt (V "Mp") (V "tg")) (c := wpStep) (WI tg)
    (fun σ => tg - σ.vars "Mp") 40 ?_ (wpStep_spec h1 hB) (fun σ h => h) ?_).post ?_
  · intro σ h
    exact evalB_condLt_vars (h.mp_lt h1 hB) (by rw [h.1]; omega)
  · intro σ h
    have : tg - σ.vars "Mp" ≤ tg := Nat.sub_le _ _
    show (1 + 3 + 40) * (tg - σ.vars "Mp") + 1 + 3 ≤ (1 + 3 + 40) * tg + 1 + 3
    have := Nat.mul_le_mul_left (1 + 3 + 40) this
    omega
  · intro σ σ' h ⟨hI, hf⟩
    have hle := le_of_condLt_false hf
    obtain ⟨ht, hM, h0, hp⟩ := hI
    rw [ht] at hle
    refine ⟨hM, hle, ?_, ?_⟩
    · by_cases hw : σ'.vars "wpv" = 0
      · rw [h0 hw]; omega
      · have := hp (Nat.pos_of_ne_zero hw); omega
    · apply le_antisymm
      · by_cases hw : σ'.vars "wpv" = 0
        · omega
        · have hp' := hp (Nat.pos_of_ne_zero hw)
          have h2 : 2 ^ σ'.vars "wpv" = 2 * 2 ^ (σ'.vars "wpv" - 1) := by
            rw [← pow_succ']; congr 1; omega
          have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := tg) (y := σ'.vars "wpv" - 1)).mpr
            (by omega)
          omega
      · exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by rw [← hM]; exact hle)

/-- The scalars the exponent is computed from. -/
def WP (zl m : ℕ) (σ : Env) : Prop := σ.vars "zl" = zl ∧ σ.vars "m" = m

theorem mulSteps_spec (b : ℕ) (hb : 1 ≤ b) (hbB : b < B) : ∀ (n t : ℕ), t * b ^ n < B →
    Spec B (fun σ => σ.vars "bs" = b ∧ σ.vars "tg" = t) (mulSteps n)
      (fun _ σ' => σ'.vars "bs" = b ∧ σ'.vars "tg" = t * b ^ n) (10 * n + 1)
  | 0, t, _ => by
    refine Spec.mono (Spec.post Spec.skip ?_) (by omega)
    rintro σ σ' ⟨h1, h2⟩ rfl
    exact ⟨h1, by simpa using h2⟩
  | n + 1, t, h => by
    have hbn : b ≤ b ^ (n + 1) := Nat.le_self_pow (by omega) b
    have htb : t * b ≤ t * b ^ (n + 1) := Nat.mul_le_mul_left _ hbn
    have hp1 : 1 ≤ b ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
    have ht : t ≤ t * b ^ (n + 1) := Nat.le_mul_of_pos_right _ hp1
    have h' : t * b * b ^ n < B := by rw [mul_assoc, ← pow_succ']; exact h
    have ih := mulSteps_spec b hb hbB n (t * b) h'
    have e : t * b ^ (n + 1) = t * b * b ^ n := by ring
    have hs : Spec B (fun σ => σ.vars "bs" = b ∧ σ.vars "tg" = t) (asg "tg" (mul (V "tg") (V "bs")))
        (fun _ σ' => σ'.vars "bs" = b ∧ σ'.vars "tg" = t * b) 4 := by
      run_vcg
      all_goals (rename_i h1 h2)
      all_goals first | (simp [Env.setVar, h1, h2]; done) | (simp only [h1, h2]; omega) | omega
    unfold mulSteps
    refine Spec.mono (Spec.post (Spec.seq hs ih (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) ?_) (by omega)
    rintro σ σ' - h
    rw [e]; exact h

theorem wpCom_spec (c1 E : ℕ) (hc : 1 ≤ c1) (hbB : 2 * zl + m + 1 < B)
    (hB : 2 * (c1 * (2 * zl + m + 1) ^ E) < B) :
    Spec B (WP zl m) (wpCom c1 E)
      (fun _ σ' => σ'.vars "Mp" = 2 ^ σ'.vars "wpv" ∧ c1 * (2 * zl + m + 1) ^ E ≤ σ'.vars "Mp" ∧
        σ'.vars "Mp" ≤ 2 * (c1 * (2 * zl + m + 1) ^ E) ∧
        σ'.vars "wpv" = Nat.clog 2 (c1 * (2 * zl + m + 1) ^ E))
      (44 * (c1 * (2 * zl + m + 1) ^ E) + 10 * E + 80) := by
  have hb1 : 1 ≤ 2 * zl + m + 1 := by omega
  have hp1 : 1 ≤ (2 * zl + m + 1) ^ E := Nat.one_le_pow _ _ hb1
  have h1 : 1 ≤ c1 * (2 * zl + m + 1) ^ E := Nat.mul_pos hc hp1
  have hl := wpLoop_spec (B := B) h1 hB
  have hc1B : c1 < B := by
    have := Nat.le_mul_of_pos_right c1 hp1
    omega
  have hm := mulSteps_spec (B := B) (2 * zl + m + 1) hb1 hbB E c1 (by omega)
  run_vcg [hm, hl]
  all_goals try assumption
  all_goals try obtain ⟨hz, hm'⟩ := ‹WP zl m σ›
  all_goals try (rw [hz]; omega)
  all_goals try (rw [hm']; omega)
  all_goals try omega
  all_goals try (simp [Env.setVar, hz, hm']; done)
  simp [WI, Env.setVar]
  simp_all

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainDefs` -/

section
/-!
The main program's definitions: the largest entry, the largest literal of the oracle's program,
the array lengths the machine is started with, and the bounds of the entries of the integer
program's word.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The largest entry. -/
def Mx (y : List ℕ) : ℕ := y.foldr max 0

lemma le_Mx {y : List ℕ} {v : ℕ} (hv : v ∈ y) : v ≤ Mx y := by
  induction y with
  | nil => cases hv
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · omega
    · have := ih h; omega

lemma Mx_mem_or_zero (y : List ℕ) : Mx y ∈ y ∨ Mx y = 0 := by
  induction y with
  | nil => right; rfl
  | cons a t ih =>
    simp only [Mx, List.foldr_cons] at ih ⊢
    rcases le_total a (t.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih with h1 | h1
      · left; exact List.mem_cons_of_mem _ h1
      · right; exact h1
    · rw [max_eq_left h]; left; exact List.mem_cons_self

/-- The largest literal of a program. -/
def PB (P : Program) : ℕ :=
  P.foldr (fun i acc => max acc (max (code i).2.1 (max (code i).2.2.1 (code i).2.2.2))) 0

lemma le_PB {P : Program} {i : Lax808846.Ram.Instr} (hi : i ∈ P) :
    (code i).2.1 ≤ PB P ∧ (code i).2.2.1 ≤ PB P ∧ (code i).2.2.2 ≤ PB P := by
  induction P with
  | nil => cases hi
  | cons a t ih =>
    simp only [PB, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hi with rfl | h
    · refine ⟨?_, ?_, ?_⟩ <;> omega
    · have := ih h; omega

/-- The lengths the machine's arrays are started with. -/
def extF (P : Program) (c1 : ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "X" then x.length
  else if a = "cnt" then nT (x.getD 0 0)
  else if a = "okt" then nV (x.getD 0 0)
  else if a = "z" then zLen (x.getD 0 0)
  else if a = "bfsc" then x.getD 1 0 * x.getD 0 0
  else if a = "om" then 2 ^ Nat.clog 2 (c1 * (2 * zLen (x.getD 0 0) + x.getD 1 0 + 1) ^ (c1 - 1))
  else if a = "ip0" ∨ a = "ip1" ∨ a = "ip2" ∨ a = "ip3" then P.length
  else 0

section entries
variable (n m k : ℕ)

theorem coefRaw_le (r c : ℕ) : coefRaw n r c ≤ 1 := by
  unfold coefRaw
  split_ifs <;> omega

theorem zFunRaw_le (cnt : ℕ → ℕ) (M : ℕ) (hcnt : ∀ r, cnt r ≤ M) (idx : ℕ) :
    zFunRaw n m k cnt idx ≤ max (zLen n) (max m M) := by
  have h1 := (sizes_le_zLen n).2.2.2.1
  have h2 := (sizes_le_zLen n).2.2.2.2.1
  have h3 := (sizes_le_zLen n).2.2.2.2.2.2.2
  unfold zFunRaw
  split_ifs
  · omega
  · omega
  · have := coefRaw_le n ((idx - 2) / nN n) ((idx - 2) % nN n); omega
  · unfold rhsRaw
    split_ifs
    · have := hcnt (idx - 2 - nM n * nN n); omega
    · omega

theorem cntN_le (I : Instance) (r : ℕ) : cntN I r ≤ I.days := by
  unfold cntN
  calc _ ≤ (range I.days).card := Finset.card_filter_le _ _
    _ = I.days := Finset.card_range _

/-- Every entry of the word of the program is at most the larger of its length and `m`. -/
theorem mem_zList_le (I : Instance) (k : ℕ) {v : ℕ} (hv : v ∈ zList I.clients I.days k (cntN I)) :
    v ≤ max (zLen I.clients) I.days := by
  unfold zList at hv
  obtain ⟨idx, -, rfl⟩ := List.mem_map.mp hv
  have := zFunRaw_le I.clients I.days k (cntN I) I.days (cntN_le I) idx
  simpa using this

end entries

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainFit` -/

section
/-!
The branch of the main program that hands the integer program to the oracle: build the word,
choose the oracle's word length, run the interpreter, print the answer.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The branch: build, choose, interpret, print. -/
def fitRun (P : Program) (c1 : ℕ) : Com :=
  seqs [buildCom, wpCom c1 (c1 - 1), simCom P, .write (V "outv")]

theorem write_spec {B v : ℕ} (hv : v < B) :
    Spec B (fun σ => σ.out = [] ∧ σ.vars "outv" = v) (.write (V "outv"))
      (fun _ σ' => σ'.out = [v]) 3 := by
  run_vcg
  all_goals (rename_i h1 h2; simp [h1, h2])

theorem pow_clog_le {t : ℕ} (h : 1 ≤ t) : 2 ^ Nat.clog 2 t ≤ 2 * t := by
  by_cases h1 : t = 1
  · subst h1; simp
  · have hc : 0 < Nat.clog 2 t := Nat.clog_pos (by norm_num) (by omega)
    have := Nat.pow_lt_of_lt_clog (b := 2) (x := t) (y := Nat.clog 2 t - 1) (by omega)
    have e : 2 ^ Nat.clog 2 t = 2 * 2 ^ (Nat.clog 2 t - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- After the builder. -/
def G1 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ Sizes I σ ∧ σ.arrs "z" = zList I.clients I.days k (cntN I) ∧
    (∀ a, a ∉ ["X", "cnt", "okt", "z"] → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
    σ.inp = [] ∧ σ.out = []

/-- After the choice of the word length. -/
def G2 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  G1 P c1 I x k σ ∧ σ.vars "Mp" = 2 ^ Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) ∧
    σ.vars "wpv" = Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1))

theorem mulSteps_frame (n : ℕ) : (∀ y ∈ (mulSteps n).wvars, y = "tg") ∧ (mulSteps n).warrs = [] ∧
    ¬ (mulSteps n).reads ∧ (mulSteps n).NoWrite := by
  induction n with
  | zero => simp [mulSteps, Com.wvars, Com.warrs, Com.reads, Com.NoWrite]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨fun y hy => ?_, ?_, ?_, ?_⟩
    · simp only [mulSteps, Com.wvars, asg, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy
      · exact hy
      · exact h1 y hy
    · simp [mulSteps, Com.warrs, asg, h2]
    · simp [mulSteps, Com.reads, asg, h3]
    · simp [mulSteps, Com.NoWrite, asg, h4]

theorem wpCom_frame (c1 E : ℕ) : (∀ y, y ∉ ["bs", "tg", "wpv", "Mp"] → y ∉ (wpCom c1 E).wvars) ∧
    (∀ a, a ∉ (wpCom c1 E).warrs) ∧ ¬ (wpCom c1 E).reads ∧ (wpCom c1 E).NoWrite := by
  obtain ⟨h1, h2, h3, h4⟩ := mulSteps_frame E
  refine ⟨fun y hy h => ?_, fun a h => ?_, ?_, ?_⟩
  · simp only [wpCom, wpLoop, wpStep, Com.wvars, seqs, asg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at h hy
    have := h1 y
    tauto
  · simp [wpCom, wpLoop, wpStep, Com.warrs, seqs, asg, h2] at h
  · simp [wpCom, wpLoop, wpStep, Com.reads, seqs, asg, h3]
  · simp [wpCom, wpLoop, wpStep, Com.NoWrite, seqs, asg, h4]

/-- The word of the program, its length, its entries. -/
theorem zList_length (I : Instance) (k : ℕ) : (zList I.clients I.days k (cntN I)).length = zLen I.clients := by
  simp [zList]

open Classical Lax117284.ParameterizedComplexity in
open Lax117284.IlpClients (decodeILP ilpClients) in
theorem fitRun_spec (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1)
    (hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t)
    (h : Bh I x k B) (hcrit : Q I.clients + 2 ≤ x.length) (hkm : k ≤ I.days ∨ I.clients = 0)
    (hbB : 2 * x.length + I.days + 1 < B)
    (hw : 16 * (c1 * (2 * x.length + I.days + 1) ^ (c1 - 1)) + 32 < B) (hP : P.length < B)
    (hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (fun σ => Ctx0 I x k σ ∧ (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
        σ.inp = [] ∧ σ.out = [])
      (fitRun P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (buildCost I + (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) +
        (20 * P.length + 101 + ((c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 + 4)) + 3) := by
  have hc1' : 1 ≤ c1 := by omega
  have hE : c1 - 1 = c' := by omega
  have hn : x.getD 0 0 = I.clients := ClientsWord.x0 h.enc
  have hm : x.getD 1 0 = I.days := ClientsWord.x1 h.enc
  have hn' : x[0]?.getD 0 = I.clients := by simpa [List.getD_eq_getElem?_getD] using hn
  have hm' : x[1]?.getD 0 = I.days := by simpa [List.getD_eq_getElem?_getD] using hm
  have hzl : zLen I.clients ≤ x.length := by have := zLen_le I.clients; omega
  have hLB : x.length < B := h.hL
  set Z := zList I.clients I.days k (cntN I) with hZ
  have hZl : Z.length = zLen I.clients := zList_length I k
  set tgt := c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1) with htgt
  have hb1 : 1 ≤ 2 * zLen I.clients + I.days + 1 := by omega
  have htgt1 : 1 ≤ tgt := Nat.mul_pos hc1' (Nat.one_le_pow _ _ hb1)
  set wp := Nat.clog 2 tgt with hwp
  have hpw : 2 ^ wp ≤ 2 * tgt := pow_clog_le htgt1
  have hpw2 : tgt ≤ 2 ^ wp := Nat.le_pow_clog (by norm_num) tgt
  have htgtB : tgt ≤ c1 * (2 * x.length + I.days + 1) ^ (c1 - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hBnd : Bnd B wp := by unfold Bnd; omega
  have hmB : I.days < B := h.m_lt
  have hzE : ∀ v ∈ Z, v < B := by
    intro v hv
    have := mem_zList_le I k hv
    have := h.hL
    omega
  have hFits : Fits c' wp Z := by
    intro v hv
    have := mem_zList_le I k hv
    have h1 : c' * (Z.length + v + 1) ^ c' ≤ c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1) := by
      rw [hE]
      exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by rw [hZl]; omega) _)
    omega
  have hZD : Z ∈ ilpClients.Domain := Lax117284Proofs.IlpClientsBridge.zList_mem_domain _ _ _ _
  obtain ⟨t, ht, hrun⟩ := hOr wp Z hZD hFits
  have hHS : HypS B wp P Z := by
    refine ⟨hBnd, by rw [hZl]; omega, ?_, ?_, hP, hLits⟩
    · intro i
      by_cases hi : i < Z.length
      · rw [List.getD_eq_getElem _ _ hi]; exact hzE _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]; omega
    · intro i hi; exact hzE _ (List.getElem_mem hi)
  have hb' : Spec B (fun σ => Ctx0 I x k σ ∧
      (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧ σ.inp = [] ∧ σ.out = [])
      buildCom (fun _ σ' => G1 P c1 I x k σ') (buildCost I) := by
    refine Spec.post (Spec.pre (buildCom_spec h) ?_) ?_
    · rintro σ ⟨hC, hZ0, hi, ho⟩
      refine ⟨hC, ?_, ?_, ?_⟩
      · rw [hZ0 "cnt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "okt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "z" (by decide)]; simp [extF, hn', hm']
    · rintro σ σ' ⟨hC, hZ0, hi, ho⟩ ⟨hC1, hS1, hz1, hA1, hA2, hA3, hA4⟩
      refine ⟨hC1, hS1, hz1, fun a ha => ?_, by rw [hA2, hi], by rw [hA3, ho]⟩
      rw [hA1 a (by simp [BA, CA, OA, FA]; simp at ha; tauto)]
      exact hZ0 a (by simp at ha; tauto)
  have hwpB : 2 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) < B := by omega
  have hbB' : 2 * zLen I.clients + I.days + 1 < B := by omega
  have hwp' : Spec B (G1 P c1 I x k) (wpCom c1 (c1 - 1)) (fun _ σ' => G2 P c1 I x k σ')
      (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) := by
    have hs := (wpCom_spec (B := B) (zl := zLen I.clients) (m := I.days) c1 (c1 - 1) hc1' hbB' hwpB).frame
    refine Spec.post (Spec.pre hs (fun σ hσ => ⟨hσ.2.1.zl, hσ.1.m⟩)) ?_
    rintro σ σ' ⟨hC, hS, hz, hA, hi, ho⟩ ⟨⟨hMp, -, -, hwpv⟩, hv, ha, hr, hwr⟩
    obtain ⟨fv, fa, fr, fw⟩ := wpCom_frame c1 (c1 - 1)
    have hv' : ∀ y, y ∉ ["bs", "tg", "wpv", "Mp"] → σ'.vars y = σ.vars y := fun y hy => hv y (fv y hy)
    have hA' : σ'.arrs = σ.arrs := funext fun a => ha a (fa a)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, (by rw [hMp, hwpv]), hwpv⟩
    · rw [hA']; exact hC.X
    · rw [hv' _ (by decide)]; exact hC.n
    · rw [hv' _ (by decide)]; exact hC.m
    · rw [hv' _ (by decide)]; exact hC.k
    · rw [hv' _ (by decide)]; exact hS.nn
    · rw [hv' _ (by decide)]; exact hS.T
    · rw [hv' _ (by decide)]; exact hS.Z
    · rw [hv' _ (by decide)]; exact hS.Vv
    · rw [hv' _ (by decide)]; exact hS.N
    · rw [hv' _ (by decide)]; exact hS.M
    · rw [hv' _ (by decide)]; exact hS.zl
    · rw [hA']; exact hz
    · intro a' ha'; rw [hA']; exact hA a' ha'
    · rw [hr fr, hi]
    · rw [hwr fw, ho]
  have hsim' : Spec B (G2 P c1 I x k) (simCom P)
      (fun _ σ' => σ'.out = [] ∧ σ'.vars "outv" = if (decodeILP Z).Feasible then 1 else 0)
      (20 * P.length + 101 + ((t + 1) * 604 + 4)) := by
    have hs := simCom_spec hHS t hrun
    refine Spec.post (Spec.pre hs ?_) ?_
    · rintro σ ⟨⟨hC, hS, hz, hA, hi, ho⟩, hMp, hwpv⟩
      have hrep : ∀ a, a ∉ ["X", "cnt", "okt", "z"] → σ.arrs a = List.replicate (extF P c1 x a) 0 := hA
      refine ⟨?_, ?_, ?_, ?_, ?_, hz, hwpv, ?_, ?_⟩
      · rw [hrep "ip0" (by decide)]; simp [extF]
      · rw [hrep "ip1" (by decide)]; simp [extF]
      · rw [hrep "ip2" (by decide)]; simp [extF]
      · rw [hrep "ip3" (by decide)]; simp [extF]
      · rw [hrep "om" (by decide)]; simp [extF, hn', hm', hwp, htgt]
      · exact hMp
      · rw [hS.zl, hZl]
    · rintro σ σ' ⟨⟨hC, hS, hz, hA, hi, ho⟩, hMp, hwpv⟩ ⟨-, hov, -, -, hi', ho'⟩
      exact ⟨by rw [ho', ho], hov⟩
  have hwr' : Spec B (fun σ => σ.out = [] ∧ σ.vars "outv" = if (decodeILP Z).Feasible then 1 else 0)
      (.write (V "outv")) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    have hfe : (decodeILP Z).Feasible ↔ I.HasKFairSchedule k := zList_feasible_iff I k hkm
    have hv1 : (if (decodeILP Z).Feasible then 1 else 0) < B := by
      split_ifs <;> omega
    refine Spec.post (write_spec hv1) ?_
    rintro σ σ' - hσ'
    rw [hσ']
    by_cases hK : I.HasKFairSchedule k
    · rw [if_pos hK, if_pos (hfe.mpr hK)]
    · rw [if_neg hK, if_neg (fun hh => hK (hfe.mp hh))]
  have s3 := Spec.seq hsim' hwr' (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)
  have s2 := Spec.seq hwp' s3 (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  have s1 := Spec.seq hb' s2 (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  unfold fitRun
  refine Spec.mono s1 ?_
  have : (t + 1) * 604 ≤ (c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 := by
    have h1 : t ≤ c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' := by
      have := ht
      rw [hZl] at this
      have e : Z.getD 0 0 = nN I.clients := decode_N I.clients I.days k (cntN I)
      rw [e] at this
      exact this
    omega
  first | omega | linarith | (simp only [hwp, htgt] at *; omega)

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainBr` -/

section
/-!
The two branches of the main program: the one that builds the integer program (after handling
the case `k > m` directly) and the brute force.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- `1` when `m < k` and `0 < n`. -/
def scE : Expr := mul (ltFl (V "m") (V "k")) (ltFl (lit 0) (V "n"))

/-- The branch for a long word: answer `0` when `k > m`, else build. -/
def fitBranch (P : Program) (c1 : ℕ) : Com := seqs [asg "sc" scE,
  .ite (.lt (lit 0) (V "sc")) (.write (lit 0)) (fitRun P c1)]

variable {B k c1 : ℕ} {I : Instance} {x : List ℕ} {P : Program}

/-- What the branches start from. -/
def F0 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  Ctx0 I x k σ ∧ (∀ a, a ≠ "X" → σ.arrs a = List.replicate (extF P c1 x a) 0) ∧
    σ.inp = [] ∧ σ.out = []

theorem scCom_spec (hn : I.clients < B) (hm : I.days < B) (hk : k < B) (h1 : 1 < B) :
    Spec B (F0 P c1 I x k) (asg "sc" scE)
      (fun _ σ' => F0 P c1 I x k σ' ∧ σ'.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0)
      20 := by
  have e1 : k - I.days - (k - I.days - 1) = if I.days < k then 1 else 0 := by
    split_ifs <;> omega
  have e2 : I.clients - 0 - (I.clients - 0 - 1) = if 0 < I.clients then 1 else 0 := by
    split_ifs <;> omega
  unfold scE
  run_vcg
  all_goals obtain ⟨⟨hX, hn', hm', hk'⟩, hZ, hi, ho⟩ := ‹F0 P c1 I x k σ›
  · refine ⟨⟨⟨by simpa [Env.setVar] using hX, by simp [Env.setVar, hn'], by simp [Env.setVar, hm'],
      by simp [Env.setVar, hk']⟩, hZ, by simp [Env.setVar, hi], by simp [Env.setVar, ho]⟩, ?_⟩
    simp only [Env.setVar, hn', hm', hk', ite_true]
    rw [e1, e2]
    split_ifs <;> simp_all
  all_goals (simp only [hn', hm', hk']; try (rw [e1, e2]; split_ifs <;> simp <;> omega))
  all_goals omega

theorem cond0_true {B : ℕ} {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some true) : 0 < σ.vars y := by
  simp only [evalB_condLt_iff, ClSim.lit, ClSim.V, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem cond0_false {B : ℕ} {σ : Env} {y : String}
    (h : (Cond.lt (lit 0) (V y)).evalB B σ = some false) : σ.vars y = 0 := by
  simp only [evalB_condLt_iff, ClSim.lit, ClSim.V, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem cond0_def {B : ℕ} {σ : Env} {y : String} (h1 : 0 < B) (h : σ.vars y < B) :
    ∃ v, (Cond.lt (lit 0) (V y)).evalB B σ = some v :=
  ⟨_, evalB_condLt (evalB_lit h1) (evalB_var h)⟩

/-- The cost of the branch that builds. -/
def Kfit (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (I : Instance) : ℕ :=
  buildCost I + (44 * (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 10 * (c1 - 1) + 80) +
    (20 * P.length + 101 + ((c' * g' (nN I.clients) * (zLen I.clients + 1) ^ c' * (Nat.clog 2 (c1 * (2 * zLen I.clients + I.days + 1) ^ (c1 - 1)) + 1) ^ c' + 1) * 604 + 4)) + 3

open Classical Lax117284.ParameterizedComplexity in
open Lax117284.IlpClients (decodeILP ilpClients) in
theorem fitBranch_spec (P : Program) (c' : ℕ) (g' : ℕ → ℕ) (c1 : ℕ) (hc1 : c1 = c' + 1)
    (hOr : ∀ w z, z ∈ ilpClients.Domain → Fits c' w z → ∃ t ≤ c' * g' (z.getD 0 0) * (z.length + 1) ^ c' * (w + 1) ^ c',
      RunsTo w P z [if (decodeILP z).Feasible then 1 else 0] t)
    (h : Bh I x k B) (hcrit : Q I.clients + 2 ≤ x.length)
    (hbB : 2 * x.length + I.days + 1 < B)
    (hw : 16 * (c1 * (2 * x.length + I.days + 1) ^ (c1 - 1)) + 32 < B) (hP : P.length < B)
    (hLits : ∀ i ∈ P, (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (F0 P c1 I x k) (fitBranch P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) (Kfit P c' g' c1 I + 30) := by
  have hn := h.n_lt
  have hm := h.m_lt
  have hk := h.k_lt
  have hB1 : 1 < B := by have := h.hL; have := h.hzB; have := (sizes_le_zLen I.clients).2.2.2.2.2.2.2; omega
  have hsc := scCom_spec (P := P) (c1 := c1) (x := x) hn hm hk hB1
  have hT : Spec B (fun σ => (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
      (Cond.lt (lit 0) (V "sc")).evalB B σ = some true)
      (.write (lit 0)) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    have hw0 : Spec B (fun σ => σ.out = []) (.write (lit 0)) (fun _ σ' => σ'.out = [0]) 3 := by
      run_vcg
      all_goals (rename_i h1; simp [h1])
    refine Spec.post (Spec.pre hw0 (fun σ hσ => hσ.1.1.2.2.2)) ?_
    rintro σ σ' ⟨⟨hF0, hsc⟩, hc⟩ hσ'
    have hpos := cond0_true hc
    rw [hsc] at hpos
    have hcond : I.days < k ∧ 0 < I.clients := by
      by_contra hn
      rw [if_neg hn] at hpos; omega
    rw [hσ', if_neg (ExtremeFairness.not_hasKFairSchedule_of_days_lt hcond.1 hcond.2)]
  have hF : Spec B (fun σ => (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
      (Cond.lt (lit 0) (V "sc")).evalB B σ = some false)
      (fitRun P c1) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) (Kfit P c' g' c1 I) := by
    have hkm : ∀ σ, (F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0) ∧
        (Cond.lt (lit 0) (V "sc")).evalB B σ = some false → k ≤ I.days ∨ I.clients = 0 := by
      rintro σ ⟨⟨hF0, hsc⟩, hc⟩
      have h0 := cond0_false hc
      rw [hsc] at h0
      by_contra hn
      rw [if_pos (by omega)] at h0; omega
    intro σ hσ
    exact fitRun_spec P c' g' c1 hc1 hOr h hcrit (hkm σ hσ) hbB hw hP hLits σ hσ.1.1
  have hite := Spec.ite (P := fun σ => F0 P c1 I x k σ ∧ σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0)
    (b := Cond.lt (lit 0) (V "sc")) (c := .write (lit 0)) (d := fitRun P c1)
    (fun σ hσ => cond0_def (by omega) (by rw [hσ.2]; split_ifs <;> omega))
    (Spec.mono hT (by omega : 3 ≤ Kfit P c' g' c1 I + 3))
    (Spec.mono hF (by omega : Kfit P c' g' c1 I ≤ Kfit P c' g' c1 I + 3))
  have hsz : (Cond.lt (lit 0) (V "sc")).size = 3 := by simp [lit, V]
  unfold fitBranch
  refine Spec.mono (Spec.seq hsc hite (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)) ?_
  rw [hsz]; omega

/-- The brute force, then its answer. -/
def bruteBranch : Com := .seq ClBrute.bruteCom (.write (V "bfans"))

open Classical in
theorem bruteBranch_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hB : 4 * x.length + 64 < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (F0 P c1 I x k) bruteBranch
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (ClBrute.bruteCost I.days I.clients + 3) := by
  have hbr := ClBrute.brute_spec I x k B hdec hB hX
  have hn' : x.getD 0 0 = I.clients := ClientsWord.x0 hdec
  have hm' : x.getD 1 0 = I.days := ClientsWord.x1 hdec
  have hn'' : x[0]?.getD 0 = I.clients := by simpa [List.getD_eq_getElem?_getD] using hn'
  have hm'' : x[1]?.getD 0 = I.days := by simpa [List.getD_eq_getElem?_getD] using hm'
  have hv1 : (if I.HasKFairSchedule k then 1 else 0) < B := by split_ifs <;> omega
  have hw : Spec B (fun σ => σ.out = [] ∧ σ.vars "bfans" = if I.HasKFairSchedule k then 1 else 0)
      (.write (V "bfans")) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) 3 := by
    run_vcg
    all_goals (rename_i h1 h2; simp [h1, h2])
  have hb' : Spec B (F0 P c1 I x k) ClBrute.bruteCom
      (fun _ σ' => σ'.out = [] ∧ σ'.vars "bfans" = if I.HasKFairSchedule k then 1 else 0)
      (ClBrute.bruteCost I.days I.clients) := by
    refine Spec.post (Spec.pre hbr ?_) ?_
    · rintro σ ⟨⟨hX', hn, hm, hk⟩, hZ, hi, ho⟩
      refine ⟨hX', hn, hm, hk, ?_⟩
      rw [hZ "bfsc" (by decide)]; simp [extF, hn'', hm'']
    · rintro σ σ' ⟨⟨hX', hn, hm, hk⟩, hZ, hi, ho⟩ ⟨hans, -, -, -, -, hi', ho'⟩
      exact ⟨by rw [ho', ho], hans⟩
  unfold bruteBranch
  exact Spec.seq hb' hw (fun σ σ' _ h => h) (fun _ _ _ _ _ h => h)

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainAll` -/

section
/-!
The main program, whole: read the word, test its length, then either build the integer program and
run the oracle on it, or brute-force.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff code simCom SV SA Pre0 HypS simCom_spec Bnd)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The main program. -/
def mainCom (P : Program) (c1 : ℕ) : Com :=
  .seq readCom (.seq critCom (.ite (.lt (lit 0) (V "fit")) (fitBranch P c1) bruteBranch))

variable {B k c1 : ℕ} {I : Instance} {x : List ℕ} {P : Program}

/-- The machine's start: the input, an empty output, the arrays of the declared lengths. -/
def M0 (P : Program) (c1 : ℕ) (x : List ℕ) (σ : Env) : Prop :=
  σ.inp = x ∧ σ.out = [] ∧ ∀ a, σ.arrs a = List.replicate (extF P c1 x a) 0

/-- After the reading and the test. -/
def R2 (P : Program) (c1 : ℕ) (I : Instance) (x : List ℕ) (k : ℕ) (σ : Env) : Prop :=
  F0 P c1 I x k σ ∧ σ.vars "L" = x.length ∧
    σ.vars "fit" = if Q I.clients + 2 ≤ x.length then 1 else 0

theorem critCom_frame : (∀ y, y ∉ ["fit", "E", "cp", "ci"] → y ∉ critCom.wvars) ∧
    (∀ a, a ∉ critCom.warrs) ∧ ¬ critCom.reads ∧ critCom.NoWrite := by
  refine ⟨fun y hy h => ?_, fun a h => ?_, ?_, ?_⟩
  · simp [critCom, critFit, critLoop, critStep, Com.wvars, seqs, asg] at h hy
    tauto
  · simp [critCom, critFit, critLoop, critStep, Com.warrs, seqs, asg] at h
  · simp [critCom, critFit, critLoop, critStep, Com.reads, seqs, asg]
  · simp [critCom, critFit, critLoop, critStep, Com.NoWrite, seqs, asg]

theorem read_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (M0 P c1 x) readCom (fun _ σ' => F0 P c1 I x k σ' ∧ σ'.vars "L" = x.length)
      (24 * x.length + 60) := by
  refine Spec.post (Spec.pre (readCom_spec hdec hL hX) ?_) ?_
  · rintro σ ⟨hi, ho, hZ⟩
    refine ⟨hi, ho, ?_⟩
    rw [hZ "X"]; simp [extF]
  · rintro σ σ' ⟨hi, ho, hZ⟩ ⟨hC, hLv, hi', ho', hA, hV⟩
    exact ⟨⟨hC, fun a ha => by rw [hA a ha, hZ a], hi', ho'⟩, hLv⟩

theorem test_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hnB : I.clients + 1 < B) (h3 : 3 * x.length + 8 < B) :
    Spec B (fun σ => F0 P c1 I x k σ ∧ σ.vars "L" = x.length) critCom (fun _ σ' => R2 P c1 I x k σ')
      (90 * x.length + 300) := by
  have hl := ClientsWord.len_eq hdec
  have hs := (critCom_spec (n := I.clients) (L := x.length) (B := B) (by omega) hnB h3).frame
  refine Spec.post (Spec.pre hs ?_) ?_
  · rintro σ ⟨⟨hC, -, -, -⟩, hLv⟩
    exact ⟨hC.n, hLv⟩
  · rintro σ σ' ⟨⟨hC, hZ, hi, ho⟩, hLv⟩ ⟨hfit, hv, ha, hr, hw⟩
    obtain ⟨fv, fa, fr, fw⟩ := critCom_frame
    have hv' : ∀ y, y ∉ ["fit", "E", "cp", "ci"] → σ'.vars y = σ.vars y := fun y hy => hv y (fv y hy)
    have hA' : σ'.arrs = σ.arrs := funext fun a => ha a (fa a)
    refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, hfit⟩
    · rw [hA']; exact hC.X
    · rw [hv' _ (by decide)]; exact hC.n
    · rw [hv' _ (by decide)]; exact hC.m
    · rw [hv' _ (by decide)]; exact hC.k
    · intro a' ha'; rw [hA']; exact hZ a' ha'
    · rw [hr fr, hi]
    · rw [hw fw, ho]
    · rw [hv' _ (by decide)]; exact hLv

open Classical in
theorem main_core (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) (hnB : I.clients + 1 < B) (h3 : 3 * x.length + 8 < B)
    (K1 K2 : ℕ)
    (hT : Q I.clients + 2 ≤ x.length → Spec B (F0 P c1 I x k) (fitBranch P c1)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) K1)
    (hF : ¬ Q I.clients + 2 ≤ x.length → Spec B (F0 P c1 I x k) bruteBranch
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0]) K2) :
    Spec B (M0 P c1 x) (mainCom P c1) (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      ((24 * x.length + 60) + ((90 * x.length + 300) +
        (4 + (if Q I.clients + 2 ≤ x.length then K1 else K2)))) := by
  have hl := ClientsWord.len_eq hdec
  have hsz : (Cond.lt (lit 0) (V "fit")).size = 3 := by simp [lit, V]
  have hite : Spec B (R2 P c1 I x k) (.ite (.lt (lit 0) (V "fit")) (fitBranch P c1) bruteBranch)
      (fun _ σ' => σ'.out = [if I.HasKFairSchedule k then 1 else 0])
      (4 + (if Q I.clients + 2 ≤ x.length then K1 else K2)) := by
    have hdef : ∀ σ, R2 P c1 I x k σ → ∃ v, (Cond.lt (lit 0) (V "fit")).evalB B σ = some v := by
      intro σ hσ
      refine cond0_def (by omega) ?_
      rw [hσ.2.2]; split_ifs <;> omega
    by_cases hc : Q I.clients + 2 ≤ x.length
    · have := Spec.ite (P := R2 P c1 I x k) (b := Cond.lt (lit 0) (V "fit")) (c := fitBranch P c1) (d := bruteBranch) hdef
        (Spec.pre (hT hc) (fun σ hσ => hσ.1.1))
        (fun σ ⟨hR, hev⟩ => by
          have := cond0_false hev
          rw [hR.2.2, if_pos hc] at this
          omega)
      rw [hsz] at this
      rw [if_pos hc]
      exact Spec.mono this (by omega)
    · have := Spec.ite (P := R2 P c1 I x k) (b := Cond.lt (lit 0) (V "fit")) (c := fitBranch P c1) (d := bruteBranch) hdef
        (fun σ ⟨hR, hev⟩ => by
          have := cond0_true hev
          rw [hR.2.2, if_neg hc] at this
          omega)
        (Spec.pre (hF hc) (fun σ hσ => hσ.1.1))
      rw [hsz] at this
      rw [if_neg hc]
      exact Spec.mono this (by omega)
  unfold mainCom
  exact Spec.seq (read_spec hdec hL hX) (Spec.seq (test_spec hdec hnB h3) hite (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

end Lax117284Proofs.Machine.ClMain

end

/-! ### `Lax117284Proofs.Machine.ClMainOk` -/

section
/-!
The layout of the main program: the scalars and arrays it mentions and the depth of its
expressions, computed from the syntax, and the proof that a layout that has them compiles it.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg seqs code simCom)
open Lax117284Proofs.Machine.ClBuild

/-- The scalars an expression mentions. -/
def eS : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .get _ i => eS i
  | .bin _ e f => eS e ++ eS f

/-- The arrays an expression mentions. -/
def eA : Expr → List String
  | .lit _ => []
  | .var _ => []
  | .get a i => a :: eA i
  | .bin _ e f => eA e ++ eA f

/-- The number of temporaries an expression needs. -/
def eD : Expr → ℕ
  | .lit _ => 0
  | .var _ => 0
  | .get _ i => max (eD i) 1
  | .bin _ e f => max (eD f) (eD e + 1)

/-- The scalars a command mentions. -/
def cS : Com → List String
  | .skip => []
  | .assign x e => x :: eS e
  | .store _ i e => eS i ++ eS e
  | .seq c d => cS c ++ cS d
  | .ite b c d => eS (condExpr b) ++ (cS c ++ cS d)
  | .while b c => eS (condExpr b) ++ cS c
  | .read x => [x]
  | .write e => eS e

/-- The arrays a command mentions. -/
def cA : Com → List String
  | .skip => []
  | .assign _ e => eA e
  | .store a i e => a :: (eA i ++ eA e)
  | .seq c d => cA c ++ cA d
  | .ite b c d => eA (condExpr b) ++ (cA c ++ cA d)
  | .while b c => eA (condExpr b) ++ cA c
  | .read _ => []
  | .write e => eA e

/-- The number of temporaries a command needs. -/
def cD : Com → ℕ
  | .skip => 0
  | .assign _ e => eD e
  | .store _ i e => max (max (eD i) (eD e + 1)) 1
  | .seq c d => max (cD c) (cD d)
  | .ite b c d => max (eD (condExpr b)) (max (cD c) (cD d))
  | .while b c => max (eD (condExpr b)) (cD c)
  | .read _ => 0
  | .write e => max (eD e) 1

theorem expr_ok (L : Layout) : ∀ (e : Expr) (d : ℕ), (∀ y ∈ eS e, y ∈ L.scalars) →
    (∀ a ∈ eA e, a ∈ L.arrays) → d + eD e ≤ L.temps → Expr.Ok L e d
  | .lit _, d, _, _, _ => by simp [Expr.Ok]
  | .var x, d, hs, _, _ => by simpa [Expr.Ok, eS] using hs x (by simp [eS])
  | .get a i, d, hs, ha, hd => by
    simp only [Expr.Ok]
    refine ⟨ha a (by simp [eA]), expr_ok L i d hs (fun a' h => ha a' (by simp [eA, h]))
      (by simp only [eD] at hd; omega), by simp only [eD] at hd; omega⟩
  | .bin _ e f, d, hs, ha, hd => by
    simp only [Expr.Ok]
    simp only [eD] at hd
    refine ⟨expr_ok L f d (fun y h => hs y (by simp [eS, h])) (fun a h => ha a (by simp [eA, h]))
      (by omega),
      expr_ok L e (d + 1) (fun y h => hs y (by simp [eS, h])) (fun a h => ha a (by simp [eA, h]))
      (by omega), by omega⟩

theorem com_ok (L : Layout) : ∀ (c : Com), (∀ y ∈ cS c, y ∈ L.scalars) →
    (∀ a ∈ cA c, a ∈ L.arrays) → cD c ≤ L.temps → Com.Ok L c
  | .skip, _, _, _ => by simp [Com.Ok]
  | .assign x e, hs, ha, hd => by
    simp only [Com.Ok]
    exact ⟨hs x (by simp [cS]), expr_ok L e 0 (fun y h => hs y (by simp [cS, h]))
      (fun a h => ha a (by simpa [cA] using h)) (by simpa [cD] using hd)⟩
  | .store a i e, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    refine ⟨ha a (by simp [cA]), expr_ok L i 0 (fun y h => hs y (by simp [cS, h]))
      (fun a' h => ha a' (by simp [cA, h])) (by omega),
      expr_ok L e 1 (fun y h => hs y (by simp [cS, h])) (fun a' h => ha a' (by simp [cA, h]))
      (by omega), by omega⟩
  | .seq c d, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    exact ⟨com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L d (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .ite b c d, hs, ha, hd => by
    simp only [Com.Ok, Cond.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L _ 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L d (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .while b c, hs, ha, hd => by
    simp only [Com.Ok, Cond.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L _ 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), com_ok L c (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega)⟩
  | .read x, hs, _, _ => by simpa [Com.Ok, cS] using hs x (by simp [cS])
  | .write e, hs, ha, hd => by
    simp only [Com.Ok]
    simp only [cD] at hd
    exact ⟨expr_ok L e 0 (fun y h => hs y (by simp [cS, h])) (fun a h => ha a (by simp [cA, h]))
      (by omega), by omega⟩

/-- The arrays of the machine. -/
def arrs10 : List String := ["X", "cnt", "okt", "z", "ip0", "ip1", "ip2", "ip3", "om", "bfsc"]

theorem loadFrom_names (P : List Instr) (j : ℕ) : cS (ClSim.loadFrom j P) = [] ∧
    (∀ a ∈ cA (ClSim.loadFrom j P), a ∈ arrs10) ∧ cD (ClSim.loadFrom j P) ≤ 1 := by
  induction P generalizing j with
  | nil => simp [ClSim.loadFrom, cS, cA, cD]
  | cons i rest ih =>
    obtain ⟨h1, h2, h3⟩ := ih (j + 1)
    simp only [ClSim.loadFrom, ClSim.storeInstr, cS, cA, cD, eS, eA, eD, List.nil_append, h1,
      List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ClSim.lit]
    refine ⟨trivial, ?_, ?_⟩
    · intro a ha
      rcases ha with (h | h | h | h) | h
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · rw [h]; simp [arrs10]
      · exact h2 a h
    · omega

/-- A command fits: its arrays are the machine's and it needs at most twelve temporaries. -/
def Fine (c : Com) : Prop := (∀ a ∈ cA c, a ∈ arrs10) ∧ cD c ≤ 12

theorem fine_read : Fine readCom := by unfold Fine; decide +kernel
theorem fine_crit : Fine critCom := by unfold Fine; decide +kernel
theorem fine_build : Fine buildCom := by unfold Fine; decide +kernel
theorem fine_brute : Fine ClBrute.bruteCom := by unfold Fine; decide +kernel
theorem Fine.seq' {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_mulSteps (n : ℕ) : Fine (mulSteps n) := by
  induction n with
  | zero => unfold Fine; simp [mulSteps, cA, cD]
  | succ n ih =>
    have h0 : Fine (asg "tg" (mul (V "tg") (V "bs"))) := by unfold Fine; decide +kernel
    exact Fine.seq' h0 ih

theorem fine_wp (c1 E : ℕ) : Fine (wpCom c1 E) := by
  have h1 : Fine (asg "bs" (add (add (mul (lit 2) (V "zl")) (V "m")) (lit 1))) := by
    unfold Fine; decide +kernel
  have h2 : Fine (asg "tg" (lit c1)) := by
    unfold Fine; simp [asg, ClSim.lit, cA, cD, eA, eD]
  have h3 : Fine (asg "wpv" (lit 0)) := by unfold Fine; decide +kernel
  have h4 : Fine (asg "Mp" (lit 1)) := by unfold Fine; decide +kernel
  have h5 : Fine wpLoop := by unfold Fine; decide +kernel
  exact h1.seq' (h2.seq' ((fine_mulSteps E).seq' (h3.seq' (h4.seq' h5))))
theorem fine_simInit (P : Program) : Fine (ClSim.simInit P) := by
  have : Fine (ClSim.simInit []) := by unfold Fine; decide +kernel
  exact this
theorem fine_interp : Fine ClSim.interpLoop := by unfold Fine; decide +kernel
theorem fine_sc : Fine (asg "sc" scE) := by unfold Fine; decide +kernel
theorem fine_write_outv : Fine (Com.write (V "outv")) := by unfold Fine; decide +kernel
theorem fine_write_bfans : Fine (Com.write (V "bfans")) := by unfold Fine; decide +kernel
theorem fine_write_zero : Fine (Com.write (lit 0)) := by unfold Fine; decide +kernel
theorem eD_fit : eD (condExpr (.lt (lit 0) (V "fit"))) ≤ 12 := by decide +kernel
theorem eD_sc : eD (condExpr (.lt (lit 0) (V "sc"))) ≤ 12 := by decide +kernel

theorem Fine.seq {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem Fine.ite {b : Cond} {c d : Com} (hb : eD (condExpr b) ≤ 12) (hbA : ∀ a ∈ eA (condExpr b), a ∈ arrs10)
    (h1 : Fine c) (h2 : Fine d) : Fine (.ite b c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha | ha
    · exact hbA a ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_loadFrom (P : List Instr) (j : ℕ) : Fine (ClSim.loadFrom j P) := by
  obtain ⟨-, h2, h3⟩ := loadFrom_names P j
  exact ⟨h2, by omega⟩

theorem fine_sim (P : Program) : Fine (simCom P) :=
  ((fine_loadFrom P 0).seq (fine_simInit P)).seq fine_interp

theorem fine_fitRun (P : Program) (c1 : ℕ) : Fine (fitRun P c1) :=
  fine_build.seq ((fine_wp c1 (c1 - 1)).seq ((fine_sim P).seq fine_write_outv))

theorem fine_fitBranch (P : Program) (c1 : ℕ) : Fine (fitBranch P c1) :=
  fine_sc.seq (Fine.ite eD_sc (by decide +kernel) fine_write_zero (fine_fitRun P c1))

theorem fine_main (P : Program) (c1 : ℕ) : Fine (mainCom P c1) :=
  fine_read.seq (fine_crit.seq (Fine.ite eD_fit (by decide +kernel) (fine_fitBranch P c1)
    (fine_brute.seq fine_write_bfans)))

end Lax117284Proofs.Machine.ClMain

end
