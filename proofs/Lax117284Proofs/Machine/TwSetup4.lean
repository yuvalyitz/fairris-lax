import Lax117284Proofs.Machine.TwSetup1
import Lax117284Proofs.Machine.TwViol

/-! ### `Lax117284Proofs.Machine.TwSetup2` -/

section
/-!
Loading the code of the cited program into the arrays the interpreter reads.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

variable {B : ℕ}

/-- The four numbers of an instruction, stored at position `i`. -/
def storeIns (i : ℕ) (ins : Instr) : Com := seqs
  [ .store "OP" (Expr.lit i) (Expr.lit (opcode ins)),
    .store "XA" (Expr.lit i) (Expr.lit (fa ins)),
    .store "XB" (Expr.lit i) (Expr.lit (fb ins)),
    .store "XC" (Expr.lit i) (Expr.lit (fc ins)) ]

/-- The code of a list of instructions, from position `i` on. -/
def loadFrom : ℕ → List Instr → Com
  | _, [] => .skip
  | i, ins :: rest => .seq (storeIns i ins) (loadFrom (i + 1) rest)

/-- The list `l` with the entries from position `i` on replaced by `vs`. -/
def setFrom : List ℕ → ℕ → List ℕ → List ℕ
  | l, _, [] => l
  | l, i, v :: vs => setFrom (l.set i v) (i + 1) vs

lemma setFrom_length (vs : List ℕ) : ∀ (l : List ℕ) (i : ℕ), (setFrom l i vs).length = l.length := by
  induction vs with
  | nil => intro l i; rfl
  | cons v vs ih => intro l i; simp [setFrom, ih]

lemma getD_set'' (l : List ℕ) (i j v : ℕ) :
    (l.set i v).getD j 0 = if j = i ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

lemma setFrom_getD (vs : List ℕ) : ∀ (l : List ℕ) (i : ℕ), i + vs.length ≤ l.length → ∀ k,
    (setFrom l i vs).getD k 0 = if i ≤ k ∧ k < i + vs.length then vs.getD (k - i) 0 else l.getD k 0 := by
  induction vs with
  | nil => intro l i h k; simp [setFrom]
  | cons v vs ih =>
    intro l i h k
    have hlen : (v :: vs).length = vs.length + 1 := rfl
    have h' : i + 1 + vs.length ≤ l.length := by omega
    simp only [setFrom]
    rw [ih (l.set i v) (i + 1) (by rw [List.length_set]; omega) k, getD_set'', hlen]
    by_cases hk : k = i
    · subst hk
      rw [if_neg (by omega), if_pos ⟨rfl, by omega⟩, if_pos (by omega)]
      simp
    · by_cases hk2 : i + 1 ≤ k ∧ k < i + 1 + vs.length
      · rw [if_pos hk2, if_pos (by omega)]
        have : k - i = (k - (i + 1)) + 1 := by omega
        rw [this]; simp
      · rw [if_neg hk2, if_neg (by omega), if_neg (by omega)]

/-- **Replacing all of a list of zeros.** -/
lemma setFrom_replicate (vs : List ℕ) : setFrom (List.replicate vs.length 0) 0 vs = vs := by
  apply List.ext_getElem
  · rw [setFrom_length]; simp
  · intro k h1 h2
    have := setFrom_getD vs (List.replicate vs.length 0) 0 (by simp) k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1] at this
    simp only [Option.getD_some] at this
    rw [this, if_pos ⟨by omega, by omega⟩, Nat.sub_zero, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2]
    simp

theorem storeIns_run (i : ℕ) (ins : Instr) (σ : Env)
    (hOP : i < (σ.arrs "OP").length) (hXA : i < (σ.arrs "XA").length)
    (hXB : i < (σ.arrs "XB").length) (hXC : i < (σ.arrs "XC").length)
    (hi : i + 3 < B) (h1 : opcode ins + 3 < B) (h2 : fa ins + 3 < B) (h3 : fb ins + 3 < B)
    (h4 : fc ins + 3 < B) :
    ∃ σ1, Run B (storeIns i ins) σ σ1 12 ∧ σ1 = (((σ.setArr "OP" i (opcode ins)).setArr "XA" i
      (fa ins)).setArr "XB" i (fb ins)).setArr "XC" i (fc ins) := by
  unfold storeIns seqs
  run_vcg
  all_goals first | omega | rfl

end Lax117284Proofs.Machine.TwSetup

end

/-! ### `Lax117284Proofs.Machine.TwSetup3` -/

section
/-!
Loading the code, and the frame of the interpreter's loop.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

variable {B : ℕ}

theorem loopCom_frame_vars : Lax117284Proofs.Machine.TwRam.loopCom.wvars ⊆
    ["pc", "cur", "ol", "run", "op", "ia", "ib", "ic", "t1", "t2", "ta"] := by
  decide +kernel

theorem loopCom_frame_arrs : Lax117284Proofs.Machine.TwRam.loopCom.warrs ⊆ ["M", "O"] := by
  decide +kernel

theorem loopCom_frame_write : Lax117284Proofs.Machine.TwRam.loopCom.NoWrite := by
  decide +kernel

theorem loadFrom_run : ∀ (rest : List Instr) (i : ℕ) (σ : Env),
    (∀ a ∈ ["OP", "XA", "XB", "XC"], i + rest.length ≤ (σ.arrs a).length) →
    i + rest.length + 3 < B →
    (∀ ins ∈ rest, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B) →
    ∃ σ', Run B (loadFrom i rest) σ σ' (13 * rest.length + 1) ∧
      σ'.arrs "OP" = setFrom (σ.arrs "OP") i (rest.map opcode) ∧
      σ'.arrs "XA" = setFrom (σ.arrs "XA") i (rest.map fa) ∧
      σ'.arrs "XB" = setFrom (σ.arrs "XB") i (rest.map fb) ∧
      σ'.arrs "XC" = setFrom (σ.arrs "XC") i (rest.map fc) ∧
      (∀ a, a ∉ ["OP", "XA", "XB", "XC"] → σ'.arrs a = σ.arrs a) ∧ σ'.vars = σ.vars ∧
      σ'.out = σ.out
  | [], i, σ, _, _, _ => by
    refine ⟨σ, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩
    exact Run.skip.mono (by simp)
  | ins :: rest, i, σ, hlen, hB, hv => by
    have hl1 : ∀ a ∈ ["OP", "XA", "XB", "XC"], i + 1 + rest.length ≤ (σ.arrs a).length := by
      intro a ha; have := hlen a ha; simp only [List.length_cons] at this; omega
    have h0 := hv ins List.mem_cons_self
    obtain ⟨σ1, r1, e1⟩ := storeIns_run (B := B) i ins σ
      (by have := hlen "OP" (by simp); simp at this; omega)
      (by have := hlen "XA" (by simp); simp at this; omega)
      (by have := hlen "XB" (by simp); simp at this; omega)
      (by have := hlen "XC" (by simp); simp at this; omega)
      (by simp at hB; omega) h0.1 h0.2.1 h0.2.2.1 h0.2.2.2
    obtain ⟨σ2, r2, hOP, hXA, hXB, hXC, hoth, hvar, hout⟩ := loadFrom_run rest (i + 1) σ1
      (by
        intro a ha
        have := hl1 a ha
        rw [e1]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simpa using this)
      (by simp at hB; omega) (fun ins' h' => hv ins' (List.mem_cons_of_mem _ h'))
    refine ⟨σ2, (r1.seq r2).mono (by simp only [List.length_cons]; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hOP, e1]; simp [setFrom]
    · rw [hXA, e1]; simp [setFrom]
    · rw [hXB, e1]; simp [setFrom]
    · rw [hXC, e1]; simp [setFrom]
    · intro a ha
      rw [hoth a ha, e1]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2]
    · rw [hvar, e1]; simp
    · rw [hout, e1]; simp

end Lax117284Proofs.Machine.TwSetup

end

/-! ### `Lax117284Proofs.Machine.TwSetup4` -/

section
/-!
The interpreter phase: load the code, set the constants, run the loop.
-/

namespace Lax117284Proofs.Machine.TwSetup

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TwViol
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Cst InitEnv loopCom interp_run Small)

variable {B : ℕ}

/-- The constants the interpreter reads and the run flag. -/
def initCom (plen : ℕ) : Com := seqs
  [ .assign "run" (Expr.lit 1),
    .assign "ylen" (add (mul (V "n") (V "n")) (Expr.lit 2)),
    .assign "plen" (Expr.lit plen) ]

/-- **The interpreter phase.** -/
def interpCom (prog : Program) : Com :=
  .seq (loadFrom 0 prog) (.seq (initCom prog.length) loopCom)

/-- The scalars the interpreter writes. -/
def SI : List String :=
  ["pc", "cur", "ol", "run", "op", "ia", "ib", "ic", "t1", "t2", "ta", "ylen", "plen"]

theorem initCom_run (plen : ℕ) (σ : Env) (n : ℕ) (hn : σ.vars "n" = n) (hnB : n < B) (hnn : n * n + 3 < B)
    (hpl : plen + 3 < B) :
    ∃ σ1, Run B (initCom plen) σ σ1 30 ∧ σ1 = ((σ.setVar "run" 1).setVar "ylen"
      (n * n + 2)).setVar "plen" plen := by
  unfold initCom seqs
  run_vcg
  all_goals (try nrm)
  all_goals try (first | omega | (simp only [hn]; omega))
  all_goals (try simp only [hn])

theorem interpCom_run (prog : Program) (y z : List ℕ) (n Pn Wp OL t : ℕ) (σ : Env)
    (hY : σ.arrs "Y" = y) (hn : σ.vars "n" = n) (hyl : y.length = n * n + 2)
    (hOP : σ.arrs "OP" = List.replicate prog.length 0)
    (hXA : σ.arrs "XA" = List.replicate prog.length 0)
    (hXB : σ.arrs "XB" = List.replicate prog.length 0)
    (hXC : σ.arrs "XC" = List.replicate prog.length 0)
    (hM : σ.arrs "M" = List.replicate Pn 0) (hO : σ.arrs "O" = List.replicate OL 0)
    (hpc : σ.vars "pc" = 0) (hcur : σ.vars "cur" = 0) (hol : σ.vars "ol" = 0)
    (hP : σ.vars "P" = Pn) (hwp : σ.vars "wp" = Wp) (hPn : Pn = 2 ^ Wp)
    (hsm : Small Wp prog) (hyP : ∀ v ∈ y, v < Pn) (hyPn : y.length < Pn)
    (bPP : Pn * Pn < B) (b2 : Pn + Pn < B) (bnd : prog.length + OL + y.length + Pn + 24 < B)
    (hOL : 0 < OL) (hOLt : t < OL)
    (hlit : ∀ ins ∈ prog, opcode ins + 3 < B ∧ fa ins + 3 < B ∧ fb ins + 3 < B ∧ fc ins + 3 < B)
    (hRuns : RunsTo Wp prog y z t) :
    ∃ σ', Run B (interpCom prog) σ σ' (13 * prog.length + 1 + 30 + 250 * (t + 1)) ∧
      z = (σ'.arrs "O").take (σ'.vars "ol") ∧ (σ'.arrs "O").length = OL ∧
      (∀ v, v ∉ SI → σ'.vars v = σ.vars v) ∧
      (∀ a, a ∉ ["OP", "XA", "XB", "XC", "M", "O"] → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out := by
  have hcnt : ∀ (f : Instr → ℕ) (l : List ℕ), l = List.replicate prog.length 0 →
      setFrom l 0 (prog.map f) = prog.map f := by
    intro f l hl
    have hl' : (prog.map f).length = prog.length := List.length_map _
    rw [hl, ← hl']
    exact setFrom_replicate (prog.map f)
  obtain ⟨σ1, r1, hOP1, hXA1, hXB1, hXC1, hoth1, hvar1, hout1⟩ := loadFrom_run (B := B) prog 0 σ
    (by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp [hOP, hXA, hXB, hXC])
    (by omega) hlit
  obtain ⟨σ2, r2, e2⟩ := initCom_run (B := B) prog.length σ1 n (by rw [hvar1]; exact hn)
    (by nlinarith) (by omega) (by omega)
  have hInit : InitEnv Wp Pn prog y OL σ2 := by
    have hs : ∀ v, v ∉ ["run", "ylen", "plen"] → σ2.vars v = σ.vars v := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      rw [e2]; simp [Env.setVar, hvar1, hv.1, hv.2.1, hv.2.2]
    have ha : σ2.arrs = σ1.arrs := by rw [e2]; simp [Env.setVar]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs "P" (by simp), hP]
    · rw [hs "wp" (by simp), hwp]
    · rw [e2]; simp [Env.setVar, hyl]
    · rw [e2]; simp [Env.setVar]
    · rw [ha, hoth1 "Y" (by simp), hY]
    · rw [ha, hOP1, hcnt opcode _ hOP]
    · rw [ha, hXA1, hcnt fa _ hXA]
    · rw [ha, hXB1, hcnt fb _ hXB]
    · rw [ha, hXC1, hcnt fc _ hXC]
    · rw [ha, hoth1 "M" (by simp), hM]; simp
    · rw [ha, hoth1 "O" (by simp), hO]; simp
    · rw [hs "pc" (by simp), hpc]
    · rw [hs "cur" (by simp), hcur]
    · rw [hs "ol" (by simp), hol]
    · rw [e2]; simp [Env.setVar]
    · rw [ha, hoth1 "M" (by simp), hM]
  have hS := hInit.sctx (B := B) hPn bPP b2 bnd hyP hyPn hsm hOL
  obtain ⟨σ3, r3, hC3, -, hz⟩ := interp_run hS hRuns hOLt
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), hz, hC3.Olen, ?_, ?_, ?_⟩
  · intro v hv
    have h3 : σ3.vars v = σ2.vars v := r3.frame_var v (fun h => hv (by
      have := loopCom_frame_vars h
      simp only [SI, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      tauto))
    rw [h3, e2]
    have hv' : v ≠ "run" ∧ v ≠ "ylen" ∧ v ≠ "plen" := ⟨fun h => hv (by simp [SI, h]), fun h => hv (by simp [SI, h]), fun h => hv (by simp [SI, h])⟩
    simp [Env.setVar, hvar1, hv'.1, hv'.2.1, hv'.2.2]
  · intro a ha
    have h3 : σ3.arrs a = σ2.arrs a := r3.frame_arr a (fun h => ha (by
      have := loopCom_frame_arrs h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      tauto))
    rw [h3, show σ2.arrs = σ1.arrs by rw [e2]; simp [Env.setVar], hoth1 a (fun h => ha (by simp at h ⊢; tauto))]
  · rw [r3.out_eq loopCom_frame_write, e2]; simp [Env.setVar, hout1]

end Lax117284Proofs.Machine.TwSetup

end
