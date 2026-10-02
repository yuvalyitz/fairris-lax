import Lax117284Proofs.Treewidth.Fun.VMLoadSetup

/-!
# WP V3 (6): the loaded environment represents the initial VM configuration

`Loaded` collects the facts the loader leaves in the environment (scalars, and each array as a named function `arrOf`);
`abs_of_loaded` and `cst_of_loaded` turn them into the two hypotheses of `vm_ram_correctF`:
`Abs ⟨0, [Bv], [], heapOf x Bv⟩ σ` (via `Abs.init`) and `Cst (mkProgF …) W Bi σ` (via `Cst.of_arrays`).
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning ToVal

/-! ## The code lists -/

/-- The code of the machine program of `Δ` (functions `< N`, entry `main` of arity 1). -/
def codeL (Δ : ℕ → Option Tm) (N main : ℕ) : List Instr := progCode Δ N main 1

def opsL (Δ : ℕ → Option Tm) (N main : ℕ) : List ℕ := (codeL Δ N main).map opc
def opasL (Δ : ℕ → Option Tm) (N main : ℕ) : List ℕ := (codeL Δ N main).map opa
def ftL (Δ : ℕ → Option Tm) (N : ℕ) : List ℕ := (List.range N).map (offset Δ)

theorem opsL_getD (Δ : ℕ → Option Tm) (N main Bv k : ℕ) :
    (opsL Δ N main).getD k 0 = opc ((mkProgF Δ N main 1 Bv).code k) := by
  show ((codeL Δ N main).map opc).getD k 0 = opc ((codeL Δ N main).getD k .halt)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (codeL Δ N main)[k]? <;> simp [opc]

theorem opasL_getD (Δ : ℕ → Option Tm) (N main Bv k : ℕ) :
    (opasL Δ N main).getD k 0 = opa ((mkProgF Δ N main 1 Bv).code k) := by
  show ((codeL Δ N main).map opa).getD k 0 = opa ((codeL Δ N main).getD k .halt)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (codeL Δ N main)[k]? <;> simp [opa]

theorem ftL_getD (Δ : ℕ → Option Tm) (N main Bv k : ℕ) :
    (ftL Δ N).getD k 0 = (mkProgF Δ N main 1 Bv).ft k := by
  rw [mkProgF_ft, ftL, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : k < N
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

theorem opasL_le (Δ : ℕ → Option Tm) (N main Bv k : ℕ) :
    opa ((mkProgF Δ N main 1 Bv).code k) ≤ wordMax (opasL Δ N main) := by
  rw [← opasL_getD Δ N main Bv k]; exact wordMax_getD_le _ _

theorem opsL_length (Δ : ℕ → Option Tm) (N main : ℕ) : (opsL Δ N main).length = (codeL Δ N main).length := by
  simp [opsL]
theorem opasL_length (Δ : ℕ → Option Tm) (N main : ℕ) : (opasL Δ N main).length = (codeL Δ N main).length := by
  simp [opasL]
theorem ftL_length (Δ : ℕ → Option Tm) (N : ℕ) : (ftL Δ N).length = N := by simp [ftL]

theorem opsL_lt (Δ : ℕ → Option Tm) (N main : ℕ) : ∀ v ∈ opsL Δ N main, v ≤ 16 := by
  intro v hv
  simp only [opsL, List.mem_map] at hv
  obtain ⟨i, _, rfl⟩ := hv
  exact opc_le i

theorem mkProgF_len' (Δ : ℕ → Option Tm) (N main Bv : ℕ) :
    (mkProgF Δ N main 1 Bv).len = (codeL Δ N main).length := rfl

/-! ## The loaded environment -/

/-- What the loader leaves. `A = W + 1` is the length of every array. -/
structure Loaded (Δ : ℕ → Option Tm) (N main : ℕ) (x : List ℕ) (Bv A : ℕ) (σ : IEnv) : Prop where
  pc : σ.vars "pc" = 0
  sp : σ.vars "sp" = 1
  rp : σ.vars "rp" = 0
  hp : σ.vars "hp" = x.length
  tb : σ.vars "B" = Bv
  run : σ.vars "run" = 1
  ha : σ.arrs "HA" = arrOf A (fun j => x.getD j 0)
  hb : σ.arrs "HB" = arrOf A (hbF Bv x.length)
  stk : σ.arrs "STK" = arrOf A (fun j => if j = 0 then Bv else 0)
  rpc : (σ.arrs "RETPC").length = A
  rh : (σ.arrs "RETH").length = A
  op : σ.arrs "OP" = arrOf A (fun k => (opsL Δ N main).getD k 0)
  oa : σ.arrs "OA" = arrOf A (fun k => (opasL Δ N main).getD k 0)
  ft : σ.arrs "FT" = arrOf A (fun k => (ftL Δ N).getD k 0)

theorem pfx_arrOf {l : List ℕ} {A : ℕ} {f : ℕ → ℕ} (h : ∀ j (hj : j < l.length), f j = l[j]) (hA : l.length ≤ A) :
    Pfx l (arrOf A f) := by
  intro j hj
  rw [getElem?_arrOf f (by omega), h j hj, List.getElem?_eq_getElem hj]

theorem abs_of_loaded {Δ : ℕ → Option Tm} {N main : ℕ} {x : List ℕ} {Bv A : ℕ} {σ : IEnv}
    (h : Loaded Δ N main x Bv A σ) (hA : x.length ≤ A) (hA1 : 1 ≤ A) (hx : x ≠ []) :
    Abs ⟨0, [Bv], [], heapOf x Bv⟩ σ := by
  refine Abs.init h.pc (by simpa using h.sp) h.rp (by rw [h.hp, heapOf_length]) ?_ ?_ ?_
  · rw [h.stk]
    refine pfx_arrOf ?_ hA1
    intro j hj
    simp at hj
    subst hj; simp
  · rw [h.ha]
    refine pfx_arrOf ?_ (by simpa [heapOf] using hA)
    intro j hj
    simp [heapOf] at hj ⊢
  · rw [h.hb]
    refine pfx_arrOf ?_ (by simpa [heapOf] using hA)
    intro j hj
    simp [heapOf] at hj ⊢

theorem cst_of_loaded {Δ : ℕ → Option Tm} {N main : ℕ} {x : List ℕ} {Bv A Bi : ℕ} {σ : IEnv}
    (h : Loaded Δ N main x Bv A σ) {W : ℕ} (hAW : A = W + 1) (hBW : Bv ≤ W) (hBi : W + 18 ≤ Bi)
    (hmo : wordMax (opasL Δ N main) < Bi) :
    Cst (mkProgF Δ N main 1 Bv) W Bi σ := by
  subst hAW
  refine Cst.of_arrays h.tb ?_ ?_ ?_ ?_ ?_ hBW hBi
  · rw [h.op]; exact arrOf_congr (fun k _ => opsL_getD Δ N main Bv k)
  · rw [h.oa]; exact arrOf_congr (fun k _ => opasL_getD Δ N main Bv k)
  · rw [h.ft]; exact arrOf_congr (fun k _ => ftL_getD Δ N main Bv k)
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · rw [h.stk]; simp
    · exact h.rpc
    · exact h.rh
    · rw [h.ha]; simp
    · rw [h.hb]; simp
  · intro i _
    exact lt_of_le_of_lt (opasL_le Δ N main Bv i) hmo

end Lax117284Proofs.Treewidth.Fun.VM.Ram
