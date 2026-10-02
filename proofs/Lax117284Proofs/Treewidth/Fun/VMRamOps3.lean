import Lax117284Proofs.Treewidth.Fun.VMRamOps2

/-!
# WP V2 (4): one-step lemmas, part 3 — `call` and `ret`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## `call` -/

theorem core_call (n : ℕ) : Core bCall 40 (.call n) := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨f, r, hst, rfl⟩ := inv_call hc hs
  obtain ⟨hfW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hp1 : s.pc + 1 ≤ W := (hB'.ret (s.pc + 1, r.length - n) (by simp)).1
  have hp2 : r.length - n ≤ W := (hB'.ret (s.pc + 1, r.length - n) (by simp)).2
  have hrpW : s.ret.length + 1 ≤ W := by have := hB'.retLen; simpa using this
  have hftW : P.ft f ≤ W := hB'.pc
  have hB18 := hC.bi
  have hpc := hA.pc
  have hrp := hA.rp
  have hoa : σ.vars "oa" = n := hf.oa
  have hnB : n < Bi := by
    have := hC.opa_lt s.pc hB.pc
    rwa [hc] at this
  have hlP : (σ.arrs "RETPC").length = W + 1 := hC.len "RETPC" (by simp [arrNames])
  have hlH : (σ.arrs "RETH").length = W + 1 := hC.len "RETH" (by simp [arrNames])
  have hlF : (σ.arrs "FT").length = W + 1 := hC.len "FT" (by simp [arrNames])
  have hFT : (σ.arrs "FT").getD f 0 = P.ft f := by
    rw [List.getD_eq_getElem?_getD, hC.ft f hfW]; rfl
  have hstk : Pfx (r.reverse ++ [f]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  unfold bCall
  run_vcg
  all_goals try (first | (nrm; omega) | (nrm; rw [g1]; omega))
  nrm
  rw [g1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nrm; rw [hFT]
  · nrm; rw [hsp]; simp
  · nrm; rw [hrp]; simp
  · nrm; exact hA.hp
  · nrm; exact hstk.left
  · nrm
    have := hA.rpc.push (k := σ.vars "rp") (by rw [hrp]; simp) (by omega) (σ.vars "pc" + 1)
    rw [hpc] at this ⊢
    simpa using this
  · nrm
    have := hA.rh.push (k := σ.vars "rp") (by rw [hrp]; simp) (by omega) (r.length - n)
    have e : σ.vars "sp" - 1 - σ.vars "oa" = r.length - n := by omega
    rw [e]
    simpa using this
  · nrm; exact hA.ha
  · nrm; exact hA.hb

/-! ## `ret` -/

theorem pfx_ret {r arr : List ℕ} {w h k : ℕ} (hs : Pfx (r.reverse ++ [w]) arr) (hk : k = min h r.length)
    (hlt : k < arr.length) : Pfx (w :: r.drop (r.length - h)).reverse (arr.set k w) := by
  have e1 : (w :: r.drop (r.length - h)).reverse = r.reverse.take h ++ [w] := by
    rw [List.reverse_cons, ← List.take_reverse]
  rw [e1]
  have hs' : Pfx (r.reverse.take h ++ (r.reverse.drop h ++ [w])) arr := by
    rw [← List.append_assoc, List.take_append_drop]; exact hs
  exact hs'.write (by simp [hk]) hlt w

theorem abs_ret {P : Prog} {W Bi : ℕ} {s : St} {σ σ' : Env} (hA : Abs s σ) (hC : Cst P W Bi σ)
    {w : ℕ} {r : List ℕ} {pc' h : ℕ} {rs : List (ℕ × ℕ)} (hst : s.stk = w :: r)
    (hret : s.ret = (pc', h) :: rs) (hlt : min h r.length < W + 1)
    (e1 : σ'.vars "pc" = pc') (e2 : σ'.vars "sp" = min h r.length + 1) (e3 : σ'.vars "rp" = rs.length)
    (e4 : σ'.vars "hp" = s.heap.length)
    (e5 : σ'.arrs "STK" = (σ.arrs "STK").set (min h r.length) w)
    (e6 : σ'.arrs "RETPC" = σ.arrs "RETPC") (e7 : σ'.arrs "RETH" = σ.arrs "RETH")
    (e8 : σ'.arrs "HA" = σ.arrs "HA") (e9 : σ'.arrs "HB" = σ.arrs "HB") :
    Abs ⟨pc', w :: r.drop (r.length - h), rs, s.heap⟩ σ' := by
  have hl : (σ.arrs "STK").length = W + 1 := hC.len "STK" (by simp [arrNames])
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hrpc : Pfx ((s.ret.reverse.map Prod.fst)) (σ.arrs "RETPC") := hA.rpc
  have hrh : Pfx ((s.ret.reverse.map Prod.snd)) (σ.arrs "RETH") := hA.rh
  rw [hret] at hrpc hrh
  simp only [List.reverse_cons, List.map_append] at hrpc hrh
  refine ⟨e1, ?_, e3, e4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2]; simp; omega
  · rw [e5]; exact pfx_ret hstk rfl (by omega)
  · rw [e6]; have := hrpc.left; simpa using this
  · rw [e7]; have := hrh.left; simpa using this
  · rw [e8]; exact hA.ha
  · rw [e9]; exact hA.hb

theorem core_ret : Core bRet 40 .ret := by
  intro P W Bi s s' σ hA hC hB hB' hc hs hf
  obtain ⟨w, r, pc', h, rs, hst, hret, rfl⟩ := inv_ret hc hs
  obtain ⟨hwW, hsp, hspW, hl, g1⟩ := top_facts hA hC hB hst
  have hpW : pc' ≤ W := (hB.ret (pc', h) (by simp [hret])).1
  have hhW : h ≤ W := (hB.ret (pc', h) (by simp [hret])).2
  have hrpW : rs.length + 1 ≤ W := by have := hB.retLen; rw [hret] at this; simpa using this
  have hrp : σ.vars "rp" = rs.length + 1 := by rw [hA.rp, hret]; simp
  have hB18 := hC.bi
  have hpc := hA.pc
  have hlP : (σ.arrs "RETPC").length = W + 1 := hC.len "RETPC" (by simp [arrNames])
  have hlH : (σ.arrs "RETH").length = W + 1 := hC.len "RETH" (by simp [arrNames])
  have hRH : (σ.arrs "RETH").getD (σ.vars "rp" - 1) 0 = h := by
    rw [List.getD_eq_getElem?_getD]
    have : (σ.arrs "RETH")[σ.vars "rp" - 1]? = some h := by
      apply hA.rh.get
      rw [hret, show σ.vars "rp" - 1 = rs.length by omega]; simp
    rw [this]; rfl
  have hRPC : (σ.arrs "RETPC").getD (σ.vars "rp" - 1) 0 = pc' := by
    rw [List.getD_eq_getElem?_getD]
    have : (σ.arrs "RETPC")[σ.vars "rp" - 1]? = some pc' := by
      apply hA.rpc.get
      rw [hret, show σ.vars "rp" - 1 = rs.length by omega]; simp
    rw [this]; rfl
  have hstk : Pfx (r.reverse ++ [w]) (σ.arrs "STK") := by
    have := hA.stk; rw [hst] at this; simpa using this
  have hdrop : (r.drop (r.length - h)).length ≤ r.length := by simp
  have hNL : (w :: r.drop (r.length - h)).length ≤ W := by simpa using hB'.stkLen
  unfold bRet
  run_vcg
  all_goals try (first | (nrm; omega) | (nrm; rw [g1]; omega))
  all_goals refine abs_ret hA hC hst hret (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals nrm
  all_goals (try simp only [vars_setVar, arrs_setVar, ↓reduceIte, String.reduceEq, eq_self] at *)
  all_goals first
    | exact hRPC
    | exact hA.hp
    | omega
    | (rw [g1, hRH]; congr 1; omega)
    | (rw [g1]; congr 1; omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram
