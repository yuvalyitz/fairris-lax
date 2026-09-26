import Lax117284Proofs.Machine.TwNum5

/-!
The facts the correctness theorem of the main program asks of the bound `Bx`, and the lengths of
the arrays.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc Small)
open Lax117284Proofs.Machine.TwMain (GB DPB)

/-- **The declared lengths of the arrays.** -/
def extx (prog : Program) (ca cc plit : ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "X" then x.length
  else if a = "Y" then nx x * nx x + 2
  else if a = "OP" ∨ a = "XA" ∨ a = "XB" ∨ a = "XC" then prog.length
  else if a = "M" then 2 ^ Wpx cc plit x
  else if a = "O" then Tbx ca cc x + 4
  else if a = "SZ" then Tbx ca cc x
  else if a = "BG" then Tbx ca cc x * (wx cc x + 1)
  else if a = "TB" then Tbx ca cc x * tabsx cc x
  else if a = "bfsc" then mx x * nx x
  else 0

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

section unconditional

variable (hx : Dm x)
include hx

theorem B_unc :
    x.length + 8 < Bx prog ca cc plit x ∧ 4 * x.length + 64 < Bx prog ca cc plit x ∧
    (∀ v ∈ x, v < Bx prog ca cc plit x) ∧ nx x + 8 < Bx prog ca cc plit x ∧
    mx x + 8 < Bx prog ca cc plit x ∧ mx x * nx x + 8 < Bx prog ca cc plit x ∧
    TwPrep.geE cc (mx x) (lgx x) + 8 < Bx prog ca cc plit x ∧ 2 * cc + 8 < Bx prog ca cc plit x ∧
    plit + 8 < Bx prog ca cc plit x ∧ Wpx cc plit x + 8 < Bx prog ca cc plit x ∧
    2 ^ Wpx cc plit x + 8 < Bx prog ca cc plit x := by
  obtain ⟨I, k, hdec, hl, hn, hm⟩ := hx.len
  have hnM := hx.nMx
  have hmn : mx x * nx x = I.days * I.clients := by rw [hn, hm]
  have hpw := Nat.two_pow_pos (Wpx cc plit x)
  have hB : Bx prog ca cc plit x ≥ bU prog cc plit x + 1 := by unfold Bx; omega
  unfold bU at hB
  refine ⟨by omega, by omega, fun v hv => ?_, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩
  have := le_Mx hv
  omega

end unconditional

theorem mem_gwList {X : List ℕ} {n m v : ℕ} (h : v ∈ TwGraph.gwList X n m) : v = n ∨ v ≤ 1 := by
  unfold TwGraph.gwList at h
  rcases List.mem_cons.mp h with h | h
  · exact Or.inl h
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
    right
    unfold TwGraph.adjBit
    split_ifs <;> omega

theorem Wp_ge (hcc : 1 ≤ cc) : lgx x + 4 ≤ Wpx cc plit x := by
  unfold Wpx
  have : lgx x ≤ (2 * cc + 1) * lgx x := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **The bound serves the guarded branch.** -/
theorem gb_of (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hx : Dm x) (hg : gdx cc x)
    (hpl1 : PLit prog ≤ plit) :
    GB (Bx prog ca cc plit x) prog x (nx x) (mx x) (Tbx ca cc x + 4) (Wpx cc plit x)
      (2 ^ Wpx cc plit x) (wx cc x) := by
  have gd := hx.gd hca hcc hg
  have hnL := hx.nL hg.2
  have hpw := Nat.two_pow_pos (Wpx cc plit x)
  have hpm := Nat.two_pow_pos (mx x)
  have hB : Bx prog ca cc plit x = bU prog cc plit x + bG ca cc plit x + 1 := by
    unfold Bx; rw [if_pos hg]
  have hU : prog.length + PLit prog + 2 ^ Wpx cc plit x + 64 ≤ bU prog cc plit x := by
    unfold bU; omega
  have hG : 2 ^ mx x + nx x * nx x + wx cc x + 2 ^ Wpx cc plit x * 2 ^ Wpx cc plit x +
      2 ^ Wpx cc plit x + Tbx ca cc x + 64 ≤ bG ca cc plit x := by
    unfold bG; omega
  generalize bU prog cc plit x = u at *
  generalize bG ca cc plit x = g at *
  have hWp := Wp_ge (cc := cc) (plit := plit) (x := x) (by omega)
  have hL2 : x.length < 2 ^ Wpx cc plit x :=
    lt_of_lt_of_le gd.hlg2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hwL : wx cc x ≤ x.length := by have := gd.wlg; have := gd.lgL; omega
  have h3L := gd.hL
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, by omega, by omega, by omega, by omega, ?_, rfl⟩
  · intro i hi
    have h := le_PLit hi
    have : plit ≤ Wpx cc plit x := by unfold Wpx; omega
    have h2 : PLit prog < 2 ^ Wpx cc plit x :=
      lt_of_lt_of_le (lt_of_le_of_lt hpl1 Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) this)
    exact ⟨by omega, by omega, by omega⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases mem_gwList hv with rfl | h1 <;> omega
    · have : v = wx cc x := by simpa using hv
      omega
  · have h1 : x.length + 1 ≤ 2 ^ (lgx x + 1) := gd.hlg2
    have h2 : 2 ^ (lgx x + 1) * 2 ^ (lgx x + 1) ≤ 2 ^ Wpx cc plit x := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by unfold Wpx; nlinarith)
    have h3 : nx x * nx x ≤ x.length * x.length := Nat.mul_le_mul hnL hnL
    have h4 : (x.length + 1) * (x.length + 1) ≤ 2 ^ (lgx x + 1) * 2 ^ (lgx x + 1) :=
      Nat.mul_le_mul h1 h1
    have := gd.hL
    nlinarith
  · intro i hi
    have h := le_PLit hi
    refine ⟨by omega, by omega, by omega, by omega⟩

open Lax117284Proofs.Machine.TwNode (Params)
open Lax117284.Bodlaender (NiceDecomposition nodeCount)

/-- **The bound serves the dynamic program.** -/
theorem dpb_of (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hx : Dm x) (hg : gdx cc x)
    {I : Instance} {y0 : List ℕ} {k : ℕ} {D : List ℕ} {w : ℕ} (hwe : w = wx cc x)
    (hy : EncodesInstance y0 I)
    (hD : NiceDecomposition I w D) (hn : nx x = I.clients) (hm : mx x = I.days)
    (hk : k ≤ Mx x) (hN : 3 * nodeCount D + 2 ≤ Tbx ca cc x) {Kdp : ℕ}
    (hcost : 60 + TwNode.dpCost ⟨I, y0, k, D, w, hy, hD⟩ ≤ Kdp) :
    DPB (Bx prog ca cc plit x) x.length (Tbx ca cc x + 4) Kdp (extx prog ca cc plit x)
      ⟨I, y0, k, D, w, hy, hD⟩ := by
  subst hwe
  have hnM := hx.nMx
  have hpm := Nat.two_pow_pos (mx x)
  have hB : Bx prog ca cc plit x = bU prog cc plit x + bG ca cc plit x + 1 := by
    unfold Bx; rw [if_pos hg]
  have hU : 3 * Mx x + 4 * x.length + 64 ≤ bU prog cc plit x := by
    unfold bU; have := Nat.two_pow_pos (Wpx cc plit x); omega
  have hG : Tbx ca cc x * tabsx cc x + tabsx cc x + Tbx ca cc x * (wx cc x + 1) + (wx cc x + 1) +
      3 * Tbx ca cc x + tabsx cc x * 2 ^ mx x + (wx cc x + 1) * ((wx cc x + 1) * mx x + 1) +
      (wx cc x + 1) * mx x + mx x + mx x * (wx cc x + 1 + 1) + 2 ^ mx x + 64 ≤
      bG ca cc plit x := by
    unfold bG; have := Nat.two_pow_pos (Wpx cc plit x); omega
  generalize bU prog cc plit x = u at *
  generalize bG ca cc plit x = g at *
  have eN : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).N = nodeCount D := rfl
  have eW : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).wid = wx cc x + 1 := rfl
  have eT : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).tabs = tabsx cc x := by
    simp [Params.tabs, Params.bs, Params.wid, Params.m, tabsx, hm]
  have eM : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).m = mx x := hm.symm
  have eBS : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).bs = 2 ^ mx x := by
    simp [Params.bs, Params.m, hm]
  have eNn : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).n = nx x := hn.symm
  have eK : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).kk = k := rfl
  have hNT : nodeCount D * tabsx cc x ≤ Tbx ca cc x * tabsx cc x :=
    Nat.mul_le_mul_right _ (by omega)
  have hNW : nodeCount D * (wx cc x + 1) ≤ Tbx ca cc x * (wx cc x + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcost⟩
  · rw [eN]; simp [extx]; omega
  · rw [eN, eW]; simp [extx]; first | exact hNW | omega
  · rw [eN, eT]; simp [extx]; first | exact hNT | omega
  · rw [eN]; omega
  · rw [eN, eT]; omega
  · rw [eN, eW]; omega
  · rw [eN]; omega
  · rw [eT, eBS]; omega
  · rw [eW, eM]; omega
  · omega
  · omega
  · rw [eNn, eM, eK]; omega
  · rw [eM, eW]; omega
  · rw [eM]; omega

end Lax117284Proofs.Machine.TwNum
