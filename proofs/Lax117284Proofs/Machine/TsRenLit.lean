import Lax117284Proofs.Machine.TsRenFo
import Lax117284Proofs.Machine.UEmit

/-!
Writing the image: a literal is a one, the first occurrence of its variable in unary, a zero
and its sign; a clause is a one, its two literals and a zero; the formula is its clauses and
a final zero.
-/

namespace Lax117284Proofs.Machine.TsRenLit

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.T9Ops
open Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.UEmit
open Lax117284Proofs.TwoSatRename Lax117284Proofs.Machine.TsRenSem Lax117284Proofs.Machine.TsRenFo

variable {B : ℕ}

/-- The literal of the position held by `p`. -/
def litCom : Com :=
  .seq (.write (.lit 1))
  (.seq (.assign "vp" (.get "TK" (add (.lit 2) (mul (.lit 2) (V "p")))))
  (.seq (.assign "r" (V "p"))
  (.seq foLoop
  (.seq (emitRep 1 (V "r"))
  (.seq (.write (.lit 0))
  (.seq (.assign "sg" (.get "TK" (add (.lit 3) (mul (.lit 2) (V "p")))))
    (.write (V "sg"))))))))

/-- The scalars a literal assigns. -/
def AL : List String := ["vp", "r", "j", "vj", "cn", "cc", "sg"]

/-- The cost of a literal at a position below `S`. -/
def Klit (S : ℕ) : ℕ := 2 + 12 + 2 + ((40 + 4) * S + 6) + (2 + ((6 + 4) * S + 6)) + 2 + 12 + 2

/-- The bounds the positions below `S` of the array satisfy. -/
structure Bnd (B : ℕ) (arr : List ℕ) (S : ℕ) : Prop where
  hEv : ∀ k < S, arr.getD (2 + 2 * k) 0 + 8 < B
  hEs : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B
  hlen : 2 + 2 * S ≤ arr.length
  hSB : 2 * S + 16 < B

/-- **One literal.** -/
theorem litCom_run (arr : List ℕ) (S p : ℕ) (σ : Env) (hb : Bnd B arr S) (hp : p < S)
    (hA : σ.arrs "TK" = arr) (hpv : σ.vars "p" = p) :
    ∃ σ', Run B litCom σ σ' (Klit S) ∧
      σ'.out = σ.out ++ litBits (fo (idxA arr) p) (sgA arr p) ∧ σ'.arrs = σ.arrs ∧
      ∀ y, y ∉ AL → σ'.vars y = σ.vars y := by
  obtain ⟨hEv, hEs, hlen, hSB⟩ := hb
  have e1 := hEv p hp
  have e2 := hEs p hp
  have hfle := fo_le (idxA arr) p
  -- write 1
  have w1 := write_bit (B := B) 1 (by omega) σ
  set σ1 : Env := { σ with out := σ.out ++ [1] } with hσ1
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, hA]
  have hp1 : σ1.vars "p" = p := by simp [hσ1, hpv]
  -- vp := TK[2 + 2 p]
  have s2 := asg_idx (B := B) "vp" 2 2 "p" σ1 arr p hA1 hp1 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ2 := σ1.setVar "vp" (arr.getD (2 + 2 * p) 0) with hσ2
  have hp2 : σ2.vars "p" = p := by simp [hσ2, hp1]
  -- r := p
  have s3 : Run B (.assign "r" (V "p")) σ2 (σ2.setVar "r" p) 2 := by
    have := Run.assign (B := B) (σ := σ2) (x := "r") (e := V "p") (v := p)
      (by have := evalB_var (B := B) (x := "p") (σ := σ2) (by omega); rwa [hp2] at this)
    exact this.mono (by simp [Expr.size])
  set σ3 := σ2.setVar "r" p with hσ3
  -- the first occurrence
  obtain ⟨σ4, r4, hr4, ha4, ho4, hf4⟩ := foLoop_spec (B := B) arr p σ3
    (fun k hk => hEv k (by omega)) (by omega) (by omega)
    (by simp [hσ3, hσ2, Env.setVar, hA1]) (by simp [hσ3, hσ2, Env.setVar, hp1])
    (by simp [hσ3, hσ2, Env.setVar]) (by simp [hσ3, Env.setVar])
  -- the unary run
  obtain ⟨σ5, r5, ho5, ha5, -, hf5⟩ := emitRep_run (B := B) 1 (V "r") (fo (idxA arr) p) σ4
    (by omega) (by omega)
    (by have := evalB_var (B := B) (x := "r") (σ := σ4) (by rw [hr4]; omega); rwa [hr4] at this)
  -- write 0
  have w6 := write_bit (B := B) 0 (by omega) σ5
  set σ6 : Env := { σ5 with out := σ5.out ++ [0] } with hσ6
  have hA6 : σ6.arrs "TK" = arr := by
    simp only [hσ6]
    rw [ha5, ha4]; simp [hσ3, hσ2, Env.setVar, hA1]
  have hp6 : σ6.vars "p" = p := by
    simp only [hσ6]
    rw [hf5 "p" (by decide) (by decide), hf4 "p" (by simp [AF])]
    simp [hσ3, hσ2, Env.setVar, hp1]
  -- sg := TK[3 + 2 p]
  have s7 := asg_idx (B := B) "sg" 3 2 "p" σ6 arr p hA6 hp6 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  set σ7 := σ6.setVar "sg" (arr.getD (3 + 2 * p) 0) with hσ7
  have hsg7 : σ7.vars "sg" = arr.getD (3 + 2 * p) 0 := by simp [hσ7, Env.setVar]
  -- write sg
  have w8 : Run B (.write (V "sg")) σ7 { σ7 with out := σ7.out ++ [arr.getD (3 + 2 * p) 0] } 2 := by
    have := Run.write (B := B) (σ := σ7) (e := V "sg")
      (evalB_var (B := B) (x := "sg") (σ := σ7) (by rw [hsg7]; omega))
    rw [hsg7] at this
    exact this.mono (by simp [Expr.size])
  refine ⟨_, (w1.seq (s2.seq (s3.seq (r4.seq (r5.seq (w6.seq (s7.seq w8))))))).mono ?_, ?_, ?_,
    fun y hy => ?_⟩
  · unfold Klit
    have h1 : (40 + 4) * p + 6 ≤ (40 + 4) * S + 6 := by omega
    have h2 : (6 + 4) * fo (idxA arr) p + 6 ≤ (6 + 4) * S + 6 := by omega
    simp only [Expr.size]
    omega
  · simp only [hσ7, Env.setVar, hσ6]
    rw [ho5, ho4]
    simp only [hσ3, hσ2, Env.setVar, hσ1]
    simp [litBits, sgA, List.append_assoc]
  · simp only [hσ7, Env.setVar, hσ6]
    rw [ha5, ha4]
    simp [hσ3, hσ2, hσ1, Env.setVar]
  · have g1 : y ≠ "sg" := fun h => hy (by simp [AL, h])
    have g2 : y ≠ "cc" := fun h => hy (by simp [AL, h])
    have g3 : y ≠ "cn" := fun h => hy (by simp [AL, h])
    have g4 : y ∉ AF := fun h => hy (by
      simp only [AF, AL, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
    have g5 : y ≠ "r" := fun h => hy (by simp [AL, h])
    have g6 : y ≠ "vp" := fun h => hy (by simp [AL, h])
    simp only [hσ7, Env.setVar, if_neg g1, hσ6]
    rw [hf5 y g2 g3, hf4 y g4]
    simp [hσ3, hσ2, hσ1, Env.setVar, g5, g6]

/-- The clause `i`: a one, its two literals, a zero. -/
def clauseBody : Com :=
  .seq (.write (.lit 1))
  (.seq (.assign "p" (.bin .mul (V "i") (.lit 2)))
  (.seq litCom
  (.seq (.assign "p" (add (.lit 1) (mul (.lit 2) (V "i"))))
  (.seq litCom (.write (.lit 0))))))

/-- The scalars a clause assigns. -/
def SC : List String := "i" :: "p" :: AL

/-- The cost of a clause. -/
def Kcl (S : ℕ) : ℕ := 2 + 4 + Klit S + 12 + Klit S + 2

/-- The bits of the clause `c`. -/
noncomputable def clauseOut (arr : List ℕ) (c : ℕ) : List ℕ :=
  clauseBits (fo (idxA arr) (2 * c)) (sgA arr (2 * c)) (fo (idxA arr) (2 * c + 1))
    (sgA arr (2 * c + 1))

/-- **One clause.** -/
theorem clauseBody_run (arr : List ℕ) (S : ℕ) (σ0 σ : Env) (hb : Bnd B arr S)
    (hAg : Agr SC σ0 σ) (hA : σ0.arrs "TK" = arr) (hlt : 2 * σ.vars "i" + 1 < S) :
    ∃ σ', Run B clauseBody σ σ' (Kcl S) ∧ σ'.out = σ.out ++ clauseOut arr (σ.vars "i") ∧
      Agr SC σ0 σ' ∧ σ'.vars "i" = σ.vars "i" := by
  have hSB := hb.hSB
  obtain ⟨i, hi⟩ : ∃ i, σ.vars "i" = i := ⟨_, rfl⟩
  rw [hi] at hlt
  rw [hi]
  have hAσ : σ.arrs "TK" = arr := by rw [hAg.1, hA]
  -- write 1
  have w1 := write_bit (B := B) 1 (by omega) σ
  set σ1 : Env := { σ with out := σ.out ++ [1] } with hσ1
  have hi1 : σ1.vars "i" = i := by simp [hσ1, hi]
  -- p := 2 i
  have s2 := asg_binr (B := B) .mul "i" 2 "p" σ1 i hi1 (by simp; omega) (by omega) (by omega)
  simp only [Bop.apply_mul] at s2
  set σ2 := σ1.setVar "p" (i * 2) with hσ2
  obtain ⟨σ3, r3, ho3, ha3, hf3⟩ := litCom_run (B := B) arr S (i * 2) σ2 hb (by omega)
    (by simp [hσ2, hσ1, Env.setVar, hAσ]) (by simp [hσ2, Env.setVar])
  have hi3 : σ3.vars "i" = i := by
    rw [hf3 "i" (by decide)]; simp [hσ2, hσ1, Env.setVar, hi]
  -- p := 1 + 2 i
  have s4 := asg_linl (B := B) "p" 1 2 "i" σ3 i hi3 (by omega) (by omega) (by omega) (by omega)
    (by omega)
  set σ4 := σ3.setVar "p" (1 + 2 * i) with hσ4
  have hA4 : σ4.arrs "TK" = arr := by
    simp only [hσ4, Env.setVar]; rw [ha3]; simp [hσ2, hσ1, Env.setVar, hAσ]
  obtain ⟨σ5, r5, ho5, ha5, hf5⟩ := litCom_run (B := B) arr S (1 + 2 * i) σ4 hb (by omega) hA4
    (by simp [hσ4, Env.setVar])
  -- write 0
  have w6 := write_bit (B := B) 0 (by omega) σ5
  have hout : σ5.out ++ [0] = σ.out ++ clauseOut arr i := by
    rw [ho5]
    simp only [hσ4, Env.setVar]
    rw [ho3]
    simp only [hσ2, Env.setVar, hσ1, clauseOut, clauseBits]
    rw [show 1 + 2 * i = 2 * i + 1 by omega, show i * 2 = 2 * i by omega]
    simp [List.append_assoc]
  have harr : σ5.arrs = σ0.arrs := by
    rw [ha5]; simp only [hσ4, Env.setVar]; rw [ha3]; simp only [hσ2, Env.setVar, hσ1]
    exact hAg.1
  have hfr : ∀ y, y ∉ SC → σ5.vars y = σ0.vars y := by
    intro y hy
    have g1 : y ∉ AL := fun h => hy (by simp [SC, h])
    have g2 : y ≠ "p" := fun h => hy (by simp [SC, h])
    rw [hf5 y g1]
    simp only [hσ4, Env.setVar, if_neg g2]
    rw [hf3 y g1]
    simp only [hσ2, Env.setVar, if_neg g2, hσ1]
    exact hAg.2 y hy
  have hi5 : σ5.vars "i" = i := by
    rw [hf5 "i" (by decide)]
    simp only [hσ4, Env.setVar, if_neg (by decide : "i" ≠ "p")]
    exact hi3
  refine ⟨_, (w1.seq (s2.seq (r3.seq (s4.seq (r5.seq w6))))).mono ?_, hout, ⟨harr, hfr⟩, hi5⟩
  unfold Kcl; omega

/-- Write the whole image: the clauses, then a zero. -/
def printR : Com := .seq (outLoop "C" clauseBody) (.write (.lit 0))

/-- The cost of writing the image of `C` clauses. -/
def Kprint (S C : ℕ) : ℕ := (Kcl S + 10 + 4) * C + 6 + 2

/-- **Writing the image.** -/
theorem printR_run (arr : List ℕ) (C : ℕ) (σ : Env) (hb : Bnd B arr (2 * C))
    (hA : σ.arrs "TK" = arr) (hC : σ.vars "C" = C) (hCB : C + 1 < B) :
    ∃ σ', Run B printR σ σ' (Kprint (2 * C) C) ∧ σ'.out = σ.out ++ outBits arr C := by
  obtain ⟨σ1, r1, o1, -⟩ := eLoop (B := B) "C" clauseBody SC (clauseOut arr) (Kcl (2 * C)) C σ
    (by simp [SC]) (by decide) hC hCB (by
      intro τ hAg hlt
      exact clauseBody_run (B := B) arr (2 * C) σ τ hb hAg hA (by omega))
  have w2 := write_bit (B := B) 0 (by omega) σ1
  refine ⟨_, (r1.seq w2).mono (by unfold Kprint; omega), ?_⟩
  simp only
  rw [o1]
  unfold outBits clauseOut
  simp [List.append_assoc]

end Lax117284Proofs.Machine.TsRenLit
