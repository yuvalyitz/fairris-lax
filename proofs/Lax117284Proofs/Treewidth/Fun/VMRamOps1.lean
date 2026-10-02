import Lax117284Proofs.Treewidth.Fun.VMRamDefs

/-!
# WP V2 (2): one-step lemmas, part 1 — inversion of `Prog.step` and the stack instructions

`lit`, `var`, `add`, `sub`, `mul`, `lt`, `eq`, `slide`.  Every lemma has the shape `Core blk 40 i`
(`Run` at cost `≤ 40`, `Abs` of the successor); the frame conclusions of `Refines` come from `Frames`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## Inversion of `Prog.step` -/

theorem inv_lit {P : Prog} {s s' : St} {n : ℕ} (hc : P.code s.pc = .lit n) (h : P.step s = some s') :
    s' = { s with pc := s.pc + 1, stk := n :: s.stk } := by
  simp only [Prog.step, hc] at h
  exact (Option.some.inj h).symm

theorem inv_var {P : Prog} {s s' : St} {i : ℕ} (hc : P.code s.pc = .var i) (h : P.step s = some s') :
    ∃ w, s.stk[i]? = some w ∧ s' = { s with pc := s.pc + 1, stk := w :: s.stk } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w hw; exact ⟨w, hw, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_add {P : Prog} {s s' : St} (hc : P.code s.pc = .add) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a + b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_sub {P : Prog} {s s' : St} (hc : P.code s.pc = .sub) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a - b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_mul {P : Prog} {s s' : St} (hc : P.code s.pc = .mul) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧ s' = { s with pc := s.pc + 1, stk := (a * b) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_lt {P : Prog} {s s' : St} (hc : P.code s.pc = .lt) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if a < b then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_eq {P : Prog} {s s' : St} (hc : P.code s.pc = .eq) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if a = b then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_slide {P : Prog} {s s' : St} (hc : P.code s.pc = .slide) (h : P.step s = some s') :
    ∃ v u r, s.stk = v :: u :: r ∧ s' = { s with pc := s.pc + 1, stk := v :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i v u r hst; exact ⟨v, u, r, hst, (Option.some.inj h).symm⟩
  · simp at h

/-! ## Reading the stack -/

theorem stk_get {s : St} {σ : Env} (hA : Abs s σ) {i x : ℕ} (hi : s.stk[i]? = some x) :
    (σ.arrs "STK").getD (σ.vars "sp" - 1 - i) 0 = x := by
  rw [hA.sp, List.getD_eq_getElem?_getD, hA.stk.getTop hi]; rfl

theorem stk_top {s : St} {σ : Env} (hA : Abs s σ) {b : ℕ} {r : List ℕ} (hst : s.stk = b :: r) :
    (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = b := by
  have := stk_get hA (i := 0) (x := b) (by simp [hst])
  simpa using this

theorem stk_nx {s : St} {σ : Env} (hA : Abs s σ) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) :
    (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 = a := by
  have := stk_get hA (i := 1) (x := a) (by simp [hst])
  simpa [Nat.sub_sub] using this

/-- The tower produced by the `add`/`sub`/`mul`/`lt`/`eq`/`slide` blocks (value `v` written at `sp - 2`). -/
def twBin (σ : Env) (v : ℕ) : Env :=
  ((σ.setArr "STK" (σ.vars "sp" - 2) v).setVar "sp" ((σ.setArr "STK" (σ.vars "sp" - 2) v).vars "sp" - 1)).setVar
    "pc" (((σ.setArr "STK" (σ.vars "sp" - 2) v).setVar "sp" ((σ.setArr "STK" (σ.vars "sp" - 2) v).vars "sp" - 1)).vars
      "pc" + 1)

theorem abs_bin {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hlen : s.stk.length ≤ W) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) (v : ℕ) :
    Abs ⟨s.pc + 1, v :: r, s.ret, s.heap⟩ (twBin σ v) := by
  have hsp : σ.vars "sp" = r.length + 2 := by rw [hA.sp, hst]; simp
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [a, b]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hlen' : r.length + 2 ≤ W := by rw [hst] at hlen; simp at hlen; omega
  unfold twBin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hA.pc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 2) (by rw [hsp]; simp) (by omega) v
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## The instructions -/

theorem core_lit (n : ℕ) : Core bLit 40 (.lit n) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  have hs' := inv_lit hc hs
  subst hs'
  have hn : n ≤ W := hB'.stk n (by simp)
  have hspW : s.stk.length + 1 ≤ W := by have := hB'.stkLen; simpa using this
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hoa : σ.vars "oa" = n := hf.oa
  have hsp := hA.sp
  have hpc := hA.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  unfold bLit
  run_vcg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hA.stk.push (k := σ.vars "sp") (by rw [hsp]; simp) (by omega) n
    rw [hoa]; simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem core_var (i : ℕ) : Core bVar 40 (.var i) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, hw, rfl⟩ := inv_var hc hs
  have hwW : w ≤ W := hB.stk w (List.mem_of_getElem? hw)
  have hspW : s.stk.length + 1 ≤ W := by have := hB'.stkLen; simpa using this
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hoa : σ.vars "oa" = i := hf.oa
  have hsp := hA.sp
  have hpc := hA.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hilt : i < s.stk.length := (List.getElem?_eq_some_iff.mp hw).1
  have g := stk_get hA hw
  rw [← hoa] at g
  unfold bVar
  run_vcg
  rw [g]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hA.stk.push (k := σ.vars "sp") (by rw [hsp]; simp) (by omega) w
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-- Facts shared by the binary instructions. -/
theorem bin_facts {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) {b a : ℕ} {r : List ℕ} (hst : s.stk = b :: a :: r) :
    b ≤ W ∧ a ≤ W ∧ σ.vars "sp" = r.length + 2 ∧ r.length + 2 ≤ W ∧
    (σ.arrs "STK").length = W + 1 ∧
    (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = b ∧ (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 = a := by
  refine ⟨hB.stk b (by simp [hst]), hB.stk a (by simp [hst]), by rw [hA.sp, hst]; simp, ?_,
    hC.len "STK" (by simp [arrNames]), stk_top hA hst, stk_nx hA hst⟩
  have := hB.stkLen; rw [hst] at this; simp at this; omega

theorem core_add : Core (bBin .add) 40 .add := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_add hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a + b ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_sub : Core (bBin .sub) 40 .sub := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_sub hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a - b ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_mul : Core (bBin .mul) 40 .mul := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_mul hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : a * b ≤ W := hB'.stk _ (by simp)
  have hprod : (σ.arrs "STK").getD (σ.vars "sp" - 2) 0 * (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 ≤ W := by
    rw [g1, g2]; exact hvW
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bBin
  run_vcg
  rw [g1, g2]
  exact abs_bin hA hC hB.stkLen hst _

theorem core_lt : Core bLt 40 .lt := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_lt hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bLt
  run_vcg
  · have h : a < b := by omega
    rw [if_pos h]; exact abs_bin hA hC hB.stkLen hst 1
  · have h : ¬ a < b := by omega
    rw [if_neg h]; exact abs_bin hA hC hB.stkLen hst 0

theorem core_eq : Core bEq 40 .eq := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_eq hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bEq
  run_vcg
  · have h : a = b := by omega
    rw [if_pos h]; exact abs_bin hA hC hB.stkLen hst 1
  · have h : ¬ a = b := by omega
    rw [if_neg h]; exact abs_bin hA hC hB.stkLen hst 0

theorem core_slide : Core bSlide 40 .slide := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨v, u, r, hst, rfl⟩ := inv_slide hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  unfold bSlide
  run_vcg
  rw [g1]
  exact abs_bin hA hC hB.stkLen hst _

end Lax117284Proofs.Treewidth.Fun.VM.Ram
