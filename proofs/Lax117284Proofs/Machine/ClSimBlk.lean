import Lax117284Proofs.Machine.ClSimCom

/-!
The blocks of the interpreter, one specification per opcode.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- What the fetch has computed, for the instruction of operands `a b c` in the state `s`. -/
structure Fetched (wp : ℕ) (s : State) (o a b c : ℕ) (σ : Env) : Prop where
  op : σ.vars "op" = o
  fa : σ.vars "fa" = a
  fb : σ.vars "fb" = b
  fc : σ.vars "fc" = c
  ra : σ.vars "ra" = a % 2 ^ wp
  rb : σ.vars "rb" = b % 2 ^ wp
  rc : σ.vars "rc" = c % 2 ^ wp
  xa : σ.vars "xa" = s.mem (a % 2 ^ wp)
  xv : σ.vars "xv" = s.mem (b % 2 ^ wp)
  yv : σ.vars "yv" = s.mem (c % 2 ^ wp)
  xx : σ.vars "xx" = s.mem (s.mem (b % 2 ^ wp) % 2 ^ wp)
  xa_lt : σ.vars "xa" < 2 ^ wp
  xv_lt : σ.vars "xv" < 2 ^ wp
  yv_lt : σ.vars "yv" < 2 ^ wp
  xx_lt : σ.vars "xx" < 2 ^ wp
  wf : σ.vars "wf" = 0
  wa : σ.vars "wa" = 0
  wv : σ.vars "wv" = 0
  npc : σ.vars "npc" = s.pc + 1
  rdi : σ.vars "rdi" = 0
  wo : σ.vars "wo" = 0
  wov : σ.vars "wov" = 0

/-- What the block has computed: the effect of the instruction, or a stop at the end of the
program. -/
def Res (B wp pl : ℕ) (s : State) (o : Option State) (σ : Env) : Prop :=
  match o with
  | some s' => s' = EffData wp (σ.vars "wf") (σ.vars "wa") (σ.vars "wv") (σ.vars "npc")
      (σ.vars "rdi") (σ.vars "wo") (σ.vars "wov") s ∧
      (σ.vars "wf" = 1 → σ.vars "wa" < 2 ^ wp ∧ σ.vars "wv" < 2 ^ wp) ∧
      σ.vars "rd" + σ.vars "rdi" ≤ σ.vars "zl" ∧ σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
      (σ.vars "wo" = 1 → σ.vars "wov" < 2 ^ wp) ∧ σ.vars "npc" < B
  | none => σ.vars "npc" = pl ∧ σ.vars "wf" = 0 ∧ σ.vars "wo" = 0 ∧ σ.vars "rdi" = 0

/-- The bound the blocks need. -/
def Bnd (B wp : ℕ) : Prop := 8 * 2 ^ wp + 32 < B

variable {B wp pl v : ℕ} {s : State} {P : Program} {z : List ℕ}

theorem mod_pow_lt (x wp : ℕ) : x % 2 ^ wp < 2 ^ wp := Nat.mod_lt _ (Nat.two_pow_pos wp)

set_option linter.unusedVariables false
set_option hygiene false in
/-- Unpack the context of a block, everywhere. -/
macro "blk_prep" : tactic => `(tactic| (
  all_goals have hFe := ‹Fetched _ _ _ _ _ _ _›
  all_goals have hop := hFe.op
  all_goals have hfa := hFe.fa
  all_goals have hfb := hFe.fb
  all_goals have hfc := hFe.fc
  all_goals have hra := hFe.ra
  all_goals have hrb := hFe.rb
  all_goals have hrc := hFe.rc
  all_goals have hxa := hFe.xa
  all_goals have hxv := hFe.xv
  all_goals have hyv := hFe.yv
  all_goals have hxx := hFe.xx
  all_goals have hxalt := hFe.xa_lt
  all_goals have hxvlt := hFe.xv_lt
  all_goals have hyvlt := hFe.yv_lt
  all_goals have hxxlt := hFe.xx_lt
  all_goals have hwf := hFe.wf
  all_goals have hwa := hFe.wa
  all_goals have hwv := hFe.wv
  all_goals have hnpc := hFe.npc
  all_goals have hrdi := hFe.rdi
  all_goals have hwo := hFe.wo
  all_goals have hwov := hFe.wov
  all_goals clear hFe
  all_goals obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := ‹KRel _ _ _ _›
  all_goals obtain ⟨hspc, hrd, hinp, hinput, homlen, hmem, hword, hout⟩ := ‹DRel _ _ _ _ _›
  all_goals simp only [Bnd] at hB))

set_option hygiene false in
/-- Simplify the goals of a block with the facts of the fetch. -/
macro "blk_simp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  all_goals try simp [Res, EffData, Env.setVar, hfa, hfb, hfc, hra, hrb, hrc, hxa, hxv, hyv, hxx, hmask, hnpc,
    hrdi, hwo, hwov, hwf, hwa, hwv, hplen, hzl, hwpv, hMp, hhh, hhm, hhm2, mod_pow_lt, $ts,*])

set_option hygiene false in
/-- Close what is left: an arithmetic bound. -/
macro "blk_bnd" : tactic => `(tactic| all_goals first
    | omega
    | (refine lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wp)) ?_; omega)
    | (refine lt_of_lt_of_le (hw _) ?_; omega)
    | (refine lt_of_le_of_lt (Nat.div_le_self _ _) ?_; refine lt_of_lt_of_le (hw _) ?_; omega)
    | (refine lt_of_le_of_lt Nat.and_le_left ?_; refine lt_of_lt_of_le (hw _) ?_; omega)
    | exact ⟨hw _, by omega⟩
    | exact ⟨lt_of_le_of_lt (Nat.div_le_self _ _) (hw _), by omega⟩
    | exact ⟨lt_of_le_of_lt Nat.and_le_left (hw _), by omega⟩)

/-- The precondition of every block. -/
abbrev Pre (P : Program) (z : List ℕ) (wp v : ℕ) (s : State) (o a b c : ℕ) (σ : Env) : Prop :=
  Fetched wp s o a b c σ ∧ KRel P z wp σ ∧ DRel z wp v σ s

macro "blk_open" : tactic => `(tactic| (run_vcg; blk_prep))

theorem blk0_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hlb : b < B) :
    Spec B (Pre P z wp v s 0 a b c) (blk 0)
      (fun σ σ' => Res B wp P.length s ((Instr.set a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_set]
  blk_bnd

theorem blk1_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 1 a b c) (blk 1)
      (fun σ σ' => Res B wp P.length s ((Instr.load a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  blk_simp [eff_load, hmw]
  blk_bnd

theorem blk2_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 2 a b c) (blk 2)
      (fun σ σ' => Res B wp P.length s ((Instr.store a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_store]
  blk_bnd

theorem blk3_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 3 a b c) (blk 3)
      (fun σ σ' => Res B wp P.length s ((Instr.add a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_add]
  blk_bnd

theorem blk4_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 4 a b c) (blk 4)
      (fun σ σ' => Res B wp P.length s ((Instr.sub a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hsub : ∀ x y, (s.mem x - s.mem y) % 2 ^ wp = s.mem x - s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_sub, hsub]
  blk_bnd

theorem blk6_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 6 a b c) (blk 6)
      (fun σ σ' => Res B wp P.length s ((Instr.div a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hdiv : ∀ x y, (s.mem x / s.mem y) % 2 ^ wp = s.mem x / s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_div, hdiv]
  blk_bnd

theorem blk7_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 7 a b c) (blk 7)
      (fun σ σ' => Res B wp P.length s ((Instr.and a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hand : ∀ x y, (s.mem x &&& s.mem y) % 2 ^ wp = s.mem x &&& s.mem y :=
    fun x y => Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left (hw x))
  run_vcg
  blk_prep
  blk_simp [eff_and, hand]
  blk_bnd

theorem blk9_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 9 a b c) (blk 9)
      (fun σ σ' => Res B wp P.length s ((Instr.not a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hnot : ∀ x, (2 ^ wp - 1 - s.mem x) % 2 ^ wp = 2 ^ wp - 1 - s.mem x :=
    fun x => Nat.mod_eq_of_lt (by have := hw x; omega)
  run_vcg
  blk_prep
  blk_simp [eff_not, hnot]
  blk_bnd

theorem blk10_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hla : a < B) :
    Spec B (Pre P z wp v s 10 a b c) (blk 10)
      (fun σ σ' => Res B wp P.length s ((Instr.jump a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_jump]
  blk_bnd

theorem blk13_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzl' : z.length < B) :
    Spec B (Pre P z wp v s 13 a b c) (blk 13)
      (fun σ σ' => Res B wp P.length s ((Instr.inputLength a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [eff_inputLength, hinput]
  blk_bnd

theorem blk15_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)  :
    Spec B (Pre P z wp v s 15 a b c) (blk 15)
      (fun σ σ' => Res B wp P.length s (Instr.halt.effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  run_vcg
  blk_prep
  blk_simp [Lax808846Proofs.Machine.effect_halt]
  blk_bnd

theorem blk17_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 17 a b c) (blk 17)
      (fun σ σ' => Res B wp P.length s ((Instr.write a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  blk_simp [eff_write, hmw]
  blk_bnd

/-! ### The bounds inside a multiplication -/

section MulBounds

variable (wp X Y : ℕ)

theorem mb_pow_h : 2 ^ ((wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem mb_mask_h : 2 ^ ((wp + 1) / 2) - 1 < 2 ^ wp := by
  have := mb_pow_h wp; have := Nat.two_pow_pos ((wp + 1) / 2); omega

theorem mb_mask_k : 2 ^ (wp - (wp + 1) / 2) - 1 < 2 ^ wp := by
  have : 2 ^ (wp - (wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.two_pow_pos (wp - (wp + 1) / 2); omega

theorem mb_mod_h : X % 2 ^ ((wp + 1) / 2) < 2 ^ wp :=
  lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (mb_pow_h wp)

theorem mb_prod_low : X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) < 2 * 2 ^ wp := by
  have h1 : X % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : Y % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) ≤ 2 * 2 ^ wp := by
    calc 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) = 2 ^ ((wp + 1) / 2 + (wp + 1) / 2) := by
          rw [pow_add]
      _ ≤ 2 ^ (wp + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ wp := by rw [pow_succ]; ring
  calc X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2))
      < 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := Nat.mul_lt_mul'' h1 h2
    _ ≤ 2 * 2 ^ wp := h3

theorem mb_cross1 (hX : X < 2 ^ wp) :
    X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) < 2 ^ wp := by
  have h2 : Y % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2))
      ≤ X / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := Nat.mul_le_mul_left _ h2.le
    _ ≤ X := Nat.div_mul_le_self _ _
    _ < 2 ^ wp := hX

theorem mb_cross2 (hY : Y < 2 ^ wp) :
    X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) < 2 ^ wp := by
  have h1 : X % 2 ^ ((wp + 1) / 2) < 2 ^ ((wp + 1) / 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
  calc X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2))
      ≤ 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) := Nat.mul_le_mul_right _ h1.le
    _ = Y / 2 ^ ((wp + 1) / 2) * 2 ^ ((wp + 1) / 2) := mul_comm _ _
    _ ≤ Y := Nat.div_mul_le_self _ _
    _ < 2 ^ wp := hY

theorem mb_cross_sum (hX : X < 2 ^ wp) (hY : Y < 2 ^ wp) :
    X / 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) +
      X % 2 ^ ((wp + 1) / 2) * (Y / 2 ^ ((wp + 1) / 2)) < 2 * 2 ^ wp := by
  have := mb_cross1 wp X Y hX
  have := mb_cross2 wp X Y hY
  omega

theorem mb_mod_k (S : ℕ) : S % 2 ^ (wp - (wp + 1) / 2) < 2 ^ wp :=
  lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem mb_high (S : ℕ) : S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) < 2 ^ wp := by
  have h1 : S % 2 ^ (wp - (wp + 1) / 2) < 2 ^ (wp - (wp + 1) / 2) :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) = 2 ^ wp := by
    rw [← pow_add]; congr 1; omega
  calc S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2)
      < 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    _ = 2 ^ wp := h3

theorem mb_total (S : ℕ) :
    X % 2 ^ ((wp + 1) / 2) * (Y % 2 ^ ((wp + 1) / 2)) +
      S % 2 ^ (wp - (wp + 1) / 2) * 2 ^ ((wp + 1) / 2) < 3 * 2 ^ wp := by
  have := mb_prod_low wp X Y
  have := mb_high wp S
  omega

end MulBounds

set_option hygiene false in
macro "blk_mulbnd" : tactic => `(tactic| first
    | (refine lt_of_lt_of_le (mb_mod_h _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mask_h _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mask_k _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_prod_low _ _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross1 _ _ _ (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross2 _ _ _ (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_cross_sum _ _ _ (hw _) (hw _)) ?_; omega)
    | (refine lt_of_lt_of_le (mb_mod_k _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_high _ _) ?_; omega)
    | (refine lt_of_lt_of_le (mb_total _ _ _ _) ?_; omega))

theorem blk5_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 5 a b c) (blk 5)
      (fun σ σ' => Res B wp P.length s ((Instr.mul a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  run_vcg
  blk_prep
  blk_simp [eff_mul, ← mulmod_eq, mulmod]
  all_goals first | blk_bnd | blk_mulbnd

set_option hygiene false in
/-- Close what is left in a block with a case split. -/
macro "blk_fin" : tactic => `(tactic| all_goals first
    | omega
    | (intro _; omega)
    | (refine lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos wp)) ?_; omega)
    | (exfalso; omega))

theorem blk11_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hlb : b < B) :
    Spec B (Pre P z wp v s 11 a b c) (blk 11)
      (fun σ σ' => Res B wp P.length s ((Instr.jzero a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  run_vcg
  blk_prep
  all_goals try simp_all [Res, eff_jzero, EffData, Env.setVar]
  blk_fin

theorem blk12_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) (hla : a < B)
    (hzB : z.length < B) :
    Spec B (Pre P z wp v s 12 a b c) (blk 12)
      (fun σ σ' => Res B wp P.length s ((Instr.jeof a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  run_vcg
  blk_prep
  all_goals try simp_all [Res, eff_jeof, EffData, Env.setVar]
  blk_fin

theorem shl_lt (wp X Y : ℕ) (hy : Y < wp) : X % 2 ^ (wp - Y) * 2 ^ Y < 2 ^ wp := by
  have h1 : X % 2 ^ (wp - Y) < 2 ^ (wp - Y) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h3 : 2 ^ (wp - Y) * 2 ^ Y = 2 ^ wp := by rw [← pow_add]; congr 1; omega
  calc X % 2 ^ (wp - Y) * 2 ^ Y < 2 ^ (wp - Y) * 2 ^ Y :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    _ = 2 ^ wp := h3

theorem blk8_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B) :
    Spec B (Pre P z wp v s 8 a b c) (blk 8)
      (fun σ σ' => Res B wp P.length s ((Instr.shiftl a b c).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  have hpw : 2 ^ (wp - s.mem (c % 2 ^ wp)) ≤ 2 ^ wp :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e : (s.mem (b % 2 ^ wp) * 2 ^ s.mem (c % 2 ^ wp)) % 2 ^ wp =
      if s.mem (c % 2 ^ wp) < wp then s.mem (b % 2 ^ wp) % 2 ^ (wp - s.mem (c % 2 ^ wp)) *
        2 ^ s.mem (c % 2 ^ wp) else 0 := by
    rw [← shlmod_eq]; rfl
  by_cases hy : s.mem (c % 2 ^ wp) < wp
  · have hsl := shl_lt wp (s.mem (b % 2 ^ wp)) (s.mem (c % 2 ^ wp)) hy
    rw [if_pos hy] at e
    run_vcg
    blk_prep
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    blk_simp [eff_shiftl, e]
    blk_fin
  · rw [if_neg hy] at e
    run_vcg
    blk_prep
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    blk_simp [eff_shiftl, e]
    blk_fin

theorem blk14_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzB : z.length < B) (hzE : ∀ i, z.getD i 0 < B) (hzE' : ∀ i (h : i < z.length), z[i] < B) :
    Spec B (Pre P z wp v s 14 a b c) (blk 14)
      (fun σ σ' => Res B wp P.length s ((Instr.inputLoad a b).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  have hmw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  run_vcg
  blk_prep
  all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try simp_all [Res, eff_inputLoad, EffData, Env.setVar, hmw, List.getD_eq_getElem?_getD]
  blk_fin

theorem drop_cons_facts {z : List ℕ} {r u : ℕ} {rest : List ℕ} (h : u :: rest = z.drop r) :
    ∃ hr : r < z.length, u = z[r] := by
  have hr : r < z.length := by
    by_contra hcon
    rw [List.drop_eq_nil_of_le (by omega)] at h
    cases h
  refine ⟨hr, ?_⟩
  rw [List.drop_eq_getElem_cons hr] at h
  exact (List.cons.inj h).1

theorem blk16_spec (a b c : ℕ) (hB : Bnd B wp) (hw : ∀ x, s.mem x < 2 ^ wp) (hpc : s.pc < P.length) (hpl : P.length < B)
    (hzB : z.length < B) (hzE : ∀ i, z.getD i 0 < B) (hzE' : ∀ i (h : i < z.length), z[i] < B)  :
    Spec B (Pre P z wp v s 16 a b c) (blk 16)
      (fun σ σ' => Res B wp P.length s ((Instr.read a).effect wp s) σ') 150 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by have : 8 * 2 ^ wp + 32 < B := hB; omega)
  rcases hcs : s.inp with _ | ⟨u, rest⟩
  · have hn := eff_read_none wp a s hcs
    run_vcg
    blk_prep
    all_goals
      have hk : z.length ≤ σ.vars "rd" := by
        have h2 : [] = z.drop (σ.vars "rd") := hcs ▸ hinp
        exact List.drop_eq_nil_iff.mp h2.symm
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp_all [Res, hn, EffData, Env.setVar]
    blk_fin
  · have hn := eff_read_some wp a u rest s hcs
    run_vcg
    blk_prep
    all_goals
      obtain ⟨hk, hku⟩ : ∃ hr : σ.vars "rd" < z.length, u = z[σ.vars "rd"] :=
        drop_cons_facts (hcs ▸ hinp)
    all_goals try simp only [Env.setVar, String.reduceEq, ↓reduceIte] at *
    all_goals try simp_all [Res, hn, EffData, Env.setVar]
    blk_fin

end Lax117284Proofs.Machine.ClSim
