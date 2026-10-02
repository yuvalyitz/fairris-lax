import Lax117284Proofs.Treewidth.Fun.VMRamOps1

/-!
# WP V2 (3): one-step lemmas, part 2 — heap, tests, jumps, calls, `halt`

`cons`, `fst`, `snd`, `isNat`, `jz`, `jmp`, `call`, `ret`, `halt`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## Inversion of `Prog.step` -/

theorem inv_cons {P : Prog} {s s' : St} (hc : P.code s.pc = .cons) (h : P.step s = some s') :
    ∃ b a r, s.stk = b :: a :: r ∧
      s' = { s with pc := s.pc + 1, stk := (P.B + s.heap.length) :: r, heap := s.heap ++ [(a, b)] } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i b a r hst; exact ⟨b, a, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_fst {P : Prog} {s s' : St} (hc : P.code s.pc = .fst) (h : P.step s = some s') :
    ∃ w r c, s.stk = w :: r ∧ P.B ≤ w ∧ s.heap[w - P.B]? = some c ∧
      s' = { s with pc := s.pc + 1, stk := c.1 :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst
    split at h
    · rename_i hle
      split at h
      · rename_i c hc'; exact ⟨w, r, c, hst, hle, hc', (Option.some.inj h).symm⟩
      · simp at h
    · simp at h
  · simp at h

theorem inv_snd {P : Prog} {s s' : St} (hc : P.code s.pc = .snd) (h : P.step s = some s') :
    ∃ w r c, s.stk = w :: r ∧ P.B ≤ w ∧ s.heap[w - P.B]? = some c ∧
      s' = { s with pc := s.pc + 1, stk := c.2 :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst
    split at h
    · rename_i hle
      split at h
      · rename_i c hc'; exact ⟨w, r, c, hst, hle, hc', (Option.some.inj h).symm⟩
      · simp at h
    · simp at h
  · simp at h

theorem inv_isNat {P : Prog} {s s' : St} (hc : P.code s.pc = .isNat) (h : P.step s = some s') :
    ∃ w r, s.stk = w :: r ∧
      s' = { s with pc := s.pc + 1, stk := (if w < P.B then 1 else 0) :: r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst; exact ⟨w, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_jz {P : Prog} {s s' : St} {k : ℕ} (hc : P.code s.pc = .jz k) (h : P.step s = some s') :
    ∃ w r, s.stk = w :: r ∧
      s' = { s with pc := if w = 0 then s.pc + 1 + k else s.pc + 1, stk := r } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r hst; exact ⟨w, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_jmp {P : Prog} {s s' : St} {k : ℕ} (hc : P.code s.pc = .jmp k) (h : P.step s = some s') :
    s' = { s with pc := s.pc + 1 + k } := by
  simp only [Prog.step, hc] at h
  exact (Option.some.inj h).symm

theorem inv_call {P : Prog} {s s' : St} {n : ℕ} (hc : P.code s.pc = .call n) (h : P.step s = some s') :
    ∃ f r, s.stk = f :: r ∧
      s' = { s with pc := P.ft f, stk := r, ret := (s.pc + 1, r.length - n) :: s.ret } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i f r hst; exact ⟨f, r, hst, (Option.some.inj h).symm⟩
  · simp at h

theorem inv_ret {P : Prog} {s s' : St} (hc : P.code s.pc = .ret) (h : P.step s = some s') :
    ∃ w r pc' h' rs, s.stk = w :: r ∧ s.ret = (pc', h') :: rs ∧
      s' = { s with pc := pc', stk := w :: r.drop (r.length - h'), ret := rs } := by
  simp only [Prog.step, hc] at h
  split at h
  · rename_i w r pc' h' rs hst hret; exact ⟨w, r, pc', h', rs, hst, hret, (Option.some.inj h).symm⟩
  · simp at h

/-! ## `cons` -/

theorem core_cons : Core bCons 40 .cons := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨b, a, r, hst, rfl⟩ := inv_cons hc hs
  obtain ⟨hbW, haW, hsp, hspW, hl, g1, g2⟩ := bin_facts hA hC hB hst
  have hvW : P.B + s.heap.length ≤ W := hB'.stk _ (by simp)
  have hhW : s.heap.length + 1 ≤ W := by have := hB'.heapLen; simpa using this
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hhp := hA.hp
  have htb := hC.tb
  have hlA : (σ.arrs "HA").length = W + 1 := hC.len "HA" (by simp [arrNames])
  have hlB : (σ.arrs "HB").length = W + 1 := hC.len "HB" (by simp [arrNames])
  have hsum : σ.vars "B" + σ.vars "hp" ≤ W := by rw [htb, hhp]; exact hvW
  unfold bCons
  run_vcg
  all_goals try (nrm; omega)
  nrm
  rw [g1, g2]
  have hstk : Pfx (r.reverse ++ [a, b]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; rw [hhp]; simp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 2) (by rw [hsp]; simp) (by omega) (σ.vars "B" + σ.vars "hp")
    rw [htb, hhp] at this ⊢
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm
    have := hA.ha.push (k := σ.vars "hp") (by rw [hhp]; simp) (by omega) a
    rw [hhp] at this ⊢
    simpa using this
  · nrm
    have := hA.hb.push (k := σ.vars "hp") (by rw [hhp]; simp) (by omega) b
    rw [hhp] at this ⊢
    simpa using this

/-! ## `fst`, `snd`, `isNat` -/

/-- The tower of the blocks that overwrite the top of the stack and advance `pc`. -/
def twTop (σ : Env) (v : ℕ) : Env :=
  (σ.setArr "STK" (σ.vars "sp" - 1) v).setVar "pc" ((σ.setArr "STK" (σ.vars "sp" - 1) v).vars "pc" + 1)

theorem abs_top {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hlen : s.stk.length ≤ W) {w : ℕ} {r : List ℕ} (hst : s.stk = w :: r) (v : ℕ) :
    Abs ⟨s.pc + 1, v :: r, s.ret, s.heap⟩ (twTop σ v) := by
  have hsp : σ.vars "sp" = r.length + 1 := by rw [hA.sp, hst]; simp
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hlen' : r.length + 1 ≤ W := by rw [hst] at hlen; simpa using hlen
  unfold twTop
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hA.pc]
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm
    have := hstk.write (k := σ.vars "sp" - 1) (by rw [hsp]; simp) (by omega) v
    simpa using this
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem top_facts {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    (hB : s.Bd W) {w : ℕ} {r : List ℕ} (hst : s.stk = w :: r) :
    w ≤ W ∧ σ.vars "sp" = r.length + 1 ∧ r.length + 1 ≤ W ∧
    (σ.arrs "STK").length = W + 1 ∧ (σ.arrs "STK").getD (σ.vars "sp" - 1) 0 = w := by
  refine ⟨hB.stk w (by simp [hst]), by rw [hA.sp, hst]; simp, ?_, hC.len "STK" (by simp [arrNames]),
    stk_top hA hst⟩
  have := hB.stkLen; rw [hst] at this; simp at this; omega

theorem core_fst : Core bFst 40 .fst := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, c, hst, hle, hheap, rfl⟩ := inv_fst hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hvW : c.1 ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hlA : (σ.arrs "HA").length = W + 1 := hC.len "HA" (by simp [arrNames])
  have hidx : w - P.B < s.heap.length := (List.getElem?_eq_some_iff.mp hheap).1
  have hhW : s.heap.length ≤ W := hB.heapLen
  have hHA : (σ.arrs "HA").getD ((σ.arrs "STK").getD (σ.vars "sp" - 1) 0 - σ.vars "B") 0 = c.1 := by
    rw [g1, htb, List.getD_eq_getElem?_getD]
    have : (σ.arrs "HA")[w - P.B]? = some c.1 := by
      apply hA.ha.get; simp [hheap]
    rw [this]; rfl
  unfold bFst
  run_vcg
  rw [hHA]
  exact abs_top hA hC hB.stkLen hst _

theorem core_snd : Core bSnd 40 .snd := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, c, hst, hle, hheap, rfl⟩ := inv_snd hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hvW : c.2 ≤ W := hB'.stk _ (by simp)
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hlA : (σ.arrs "HB").length = W + 1 := hC.len "HB" (by simp [arrNames])
  have hidx : w - P.B < s.heap.length := (List.getElem?_eq_some_iff.mp hheap).1
  have hhW : s.heap.length ≤ W := hB.heapLen
  have hHB : (σ.arrs "HB").getD ((σ.arrs "STK").getD (σ.vars "sp" - 1) 0 - σ.vars "B") 0 = c.2 := by
    rw [g1, htb, List.getD_eq_getElem?_getD]
    have : (σ.arrs "HB")[w - P.B]? = some c.2 := by
      apply hA.hb.get; simp [hheap]
    rw [this]; rfl
  unfold bSnd
  run_vcg
  rw [hHB]
  exact abs_top hA hC hB.stkLen hst _

theorem core_isNat : Core bIsNat 40 .isNat := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, hst, rfl⟩ := inv_isNat hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpcW : s.pc + 1 ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have htb := hC.tb
  have hPB := hC.bW
  unfold bIsNat
  run_vcg
  · have h : w < P.B := by omega
    rw [if_pos h]; exact abs_top hA hC hB.stkLen hst 1
  · have h : ¬ w < P.B := by omega
    rw [if_neg h]; exact abs_top hA hC hB.stkLen hst 0

/-! ## `jz`, `jmp` -/

/-- The tower of the blocks that only change `pc` (to the value `v`). -/
def twPc (σ : Env) (v : ℕ) : Env := σ.setVar "pc" v

/-- The tower of `jz`: `pc := v`, `sp := sp - 1`. -/
def twJz (σ : Env) (v : ℕ) : Env :=
  (σ.setVar "pc" v).setVar "sp" ((σ.setVar "pc" v).vars "sp" - 1)

theorem abs_jz {s : St} {σ : Env} (hA : Abs s σ) {w : ℕ} {r : List ℕ}
    (hst : s.stk = w :: r) (v : ℕ) :
    Abs ⟨v, r, s.ret, s.heap⟩ (twJz σ v) := by
  have hsp : σ.vars "sp" = r.length + 1 := by rw [hA.sp, hst]; simp
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  unfold twJz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm
  · nrm; rw [hsp]; simp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hstk.left
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

theorem core_jz (k : ℕ) : Core bJz 40 (.jz k) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, hst, rfl⟩ := inv_jz hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpcW : (if w = 0 then s.pc + 1 + k else s.pc + 1) ≤ W := hB'.pc
  have hpcW1 : s.pc + 1 ≤ W := by split_ifs at hpcW <;> omega
  have hpcW2 : w = 0 → s.pc + 1 + k ≤ W := fun h => by simpa [h] using hpcW
  have hB18 := hC.bi
  have hpc := hA.pc
  have hoa : σ.vars "oa" = k := hf.oa
  unfold bJz
  run_vcg
  · have h : w = 0 := by omega
    rw [if_pos h]
    rw [hpc, hoa]
    exact abs_jz hA hst _
  · have h : ¬ w = 0 := by omega
    rw [if_neg h]
    rw [hpc]
    exact abs_jz hA hst _

theorem core_jmp (k : ℕ) : Core bJmp 40 (.jmp k) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  have hs' := inv_jmp hc hs
  subst hs'
  have hpcW : s.pc + 1 + k ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hoa : σ.vars "oa" = k := hf.oa
  unfold bJmp
  run_vcg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hpc, hoa]
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## `halt` -/

theorem halt_run {P : Prog} {W Bi : ℕ} {s : St} {σ : Env} (hA : Abs s σ) (hC : Cst P W Bi σ) :
    ∃ σ', Run Bi bHalt σ σ' 4 ∧ Abs s σ' ∧ Cst P W Bi σ' ∧ σ'.vars "run" = 0 := by
  have hB18 := hC.bi
  obtain ⟨σ', hr, rfl⟩ : ∃ σ', Run Bi bHalt σ σ' 4 ∧ σ' = σ.setVar "run" 0 := by
    unfold bHalt
    run_vcg
    rfl
  refine ⟨_, hr, ?_, hC.of_run hr (by decide) (by decide) (by decide) (by decide), by simp⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; exact hA.pc
  · nrm; exact hA.sp
  · nrm; exact hA.rp
  · nrm; exact hA.hp
  · nrm; exact hA.stk
  · nrm; exact hA.rpc
  · nrm; exact hA.rh
  · nrm; exact hA.ha
  · nrm; exact hA.hb

end Lax117284Proofs.Treewidth.Fun.VM.Ram
