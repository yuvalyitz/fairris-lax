import Lax117284Proofs.ComputableBounds
import Lax117284Proofs.Machine.TwNum4
import Mathlib.Tactic
import Lax228581.Treewidth
import Lax117284Proofs.Injectivity
import Lax117284Proofs.Machine.ClBruteFinal
import Lax117284.Bodlaender
import Lax117284Proofs.Machine.ClMainOk
import Lax117284.Theorem4

/-! ### `Lax117284Proofs.Machine.TwNum5` -/

section
/-!
The bound on the values of the main program, and the facts about it that the correctness theorem
asks of it.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero mem_x)
open Lax117284Proofs.Machine.TwRam (opcode fa fb fc)

/-- The largest number in the code of a program, in sum. -/
def PLit (prog : Program) : ℕ := (prog.map fun i => opcode i + fa i + fb i + fc i).sum

theorem le_PLit {prog : Program} {i : Instr} (h : i ∈ prog) :
    opcode i ≤ PLit prog ∧ fa i ≤ PLit prog ∧ fb i ≤ PLit prog ∧ fc i ≤ PLit prog := by
  unfold PLit
  induction prog with
  | nil => cases h
  | cons j rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

/-- The part of the bound that is present whether or not the guard holds. -/
def bU (prog : Program) (cc plit : ℕ) (x : List ℕ) : ℕ :=
  4 * x.length + 64 + 3 * Mx x + TwPrep.geE cc (mx x) (lgx x) + 2 * cc + plit + Wpx cc plit x +
    2 ^ Wpx cc plit x + PLit prog + prog.length + 64

/-- The part of the bound that the guarded branch needs. -/
def bG (ca cc plit : ℕ) (x : List ℕ) : ℕ :=
  2 ^ mx x + nx x * nx x + wx cc x + 2 ^ Wpx cc plit x * 2 ^ Wpx cc plit x + 2 ^ Wpx cc plit x +
    Tbx ca cc x + Tbx ca cc x * tabsx cc x + tabsx cc x + Tbx ca cc x * (wx cc x + 1) +
    (wx cc x + 1) + 3 * Tbx ca cc x + tabsx cc x * 2 ^ mx x +
    (wx cc x + 1) * ((wx cc x + 1) * mx x + 1) + (wx cc x + 1) * mx x + mx x +
    mx x * (wx cc x + 1 + 1) + 64

open Classical in
/-- **The bound on the values of the main program.** -/
noncomputable def Bx (prog : Program) (ca cc plit : ℕ) (x : List ℕ) : ℕ :=
  bU prog cc plit x + (if gdx cc x then bG ca cc plit x else 0) + 1

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ} {P : List ℕ → Prop}

theorem Bx_pos (x : List ℕ) : 1 < Bx prog ca cc plit x := by
  unfold Bx bU; have := Nat.two_pow_pos (Wpx cc plit x); omega

/-! ### The bound is polynomial -/

theorem atom_Mx : PlOn Aw P Mx :=
  PlOn.base.mono (fun x _ => by unfold Aw; omega)

theorem atom_lenA : PlOn Aw P (fun x => x.length) :=
  PlOn.base.mono (fun x _ => by unfold Aw; omega)

theorem PlOn.toA {f : List ℕ → ℕ} (h : PlOn Lp P f) : PlOn Aw P f :=
  h.base_mono (fun x _ => Lp_le_Aw x)

theorem plon_bU (hP : ∀ x, P x → Dm x) : PlOn Aw P (bU prog cc plit) := by
  have hm : PlOn Aw P mx := atom_Mx.mono (fun x hx => (hP x hx).nMx.2)
  have hlg : PlOn Aw P lgx := atom_lg.toA
  have hge : PlOn Aw P (fun x => TwPrep.geE cc (mx x) (lgx x)) := by
    have : PlOn Aw P (fun x => cc * ((lgx x + 1) * (lgx x + 1) * (lgx x + 1)) +
        mx x * (lgx x + 1) + 2) := by
      repeat' first | exact hm | exact hlg | exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul
    exact this
  have hWp : PlOn Aw P (Wpx cc plit) := atom_Wp.toA
  have hPn : PlOn Aw P (fun x => 2 ^ Wpx cc plit x) := (atom_Pn hP).toA
  show PlOn Aw P (fun x => bU prog cc plit x)
  unfold bU
  repeat' first | exact hge | exact hWp | exact hPn | exact atom_Mx | exact atom_lenA |
    exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul

theorem plon_bG (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Aw (fun x => Dm x ∧ gdx cc x) (bG ca cc plit) := by
  have hm : PlOn Aw (fun x => Dm x ∧ gdx cc x) mx := (atom_m hca hcc).toA
  have hn : PlOn Aw (fun x => Dm x ∧ gdx cc x) nx := (atom_n hca hcc).toA
  have hw : PlOn Aw (fun x => Dm x ∧ gdx cc x) (wx cc) := (atom_w hca hcc).toA
  have hpm : PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ mx x) := (atom_pm hca hcc).toA
  have htb : PlOn Aw (fun x => Dm x ∧ gdx cc x) (Tbx ca cc) := (atom_Tb hca hcc).toA
  have hta : PlOn Aw (fun x => Dm x ∧ gdx cc x) (tabsx cc) := (atom_tabs hca hcc).toA
  have hPn : PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => 2 ^ Wpx cc plit x) :=
    (atom_Pn (fun x hx => hx.1)).toA
  show PlOn Aw (fun x => Dm x ∧ gdx cc x) (fun x => bG ca cc plit x)
  unfold bG
  repeat' first | exact hm | exact hn | exact hw | exact hpm | exact htb | exact hta | exact hPn |
    exact PlOn.const _ | apply PlOn.addA | apply PlOn.mul

open Classical in
theorem plon_Bx (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) : PlOn Aw Dm (Bx prog ca cc plit) := by
  have h1 : PlOn Aw Dm (bU prog cc plit) := plon_bU (fun x hx => hx)
  have h2 : PlOn Aw Dm (fun x => if gdx cc x then bG ca cc plit x else 0) :=
    PlOn.guard (plon_bG hca hcc)
  show PlOn Aw Dm (fun x => bU prog cc plit x + (if gdx cc x then bG ca cc plit x else 0) + 1)
  exact (h1.addA h2).addA (PlOn.const 1)

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum6` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.TwNum7` -/

section
/-!
The cost of the dynamic program as a function of the sizes of its tables, and its polynomial
bound.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax117284Proofs.Machine.TwNode (Params vcost dpCost)

/-- **The cost of the dynamic program** for `N` nodes, `m` days, bags of `wid` clients and `tabs`
restrictions. -/
def dpCostN (N m wid tabs : ℕ) : ℕ :=
  (((60 + ((34 * wid + 130) + ((20 + 20 + 4) * wid + 6) + 100 +
        ((vcost m wid + 60 + 20 + 4) * tabs + 6)) +
      ((34 * wid + 130) + ((20 + 20 + 4) * wid + 6) + 100 +
        ((44 * 2 ^ m + 130 + 20 + 4) * tabs + 6)) +
      (100 + ((10 + 20 + 4) * wid + 6) + 100 + ((30 + 20 + 4) * tabs + 6))) + 10 + 4) * N + 6) +
    (60 + ((20 + 10 + 4) * tabs + 6) + 10)

theorem dpCost_eq (P : Params) : dpCost P = dpCostN P.N P.m P.wid P.tabs := rfl

theorem dpCostN_mono {N N' : ℕ} (h : N ≤ N') (m wid tabs : ℕ) :
    dpCostN N m wid tabs ≤ dpCostN N' m wid tabs := by
  unfold dpCostN; gcongr

variable {P : List ℕ → Prop} {ca cc plit : ℕ}

theorem plon_dpCostN (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x)) := by
  have hm := atom_m (ca := ca) (cc := cc) hca hcc
  have hw := atom_w (ca := ca) (cc := cc) hca hcc
  have hpm := atom_pm (ca := ca) (cc := cc) hca hcc
  have htb := atom_Tb (ca := ca) (cc := cc) hca hcc
  have hta := atom_tabs (ca := ca) (cc := cc) hca hcc
  show PlOn Lp (fun x => Dm x ∧ gdx cc x)
    (fun x => dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x))
  unfold dpCostN vcost
  repeat' first | exact hm | exact hw | exact hpm | exact htb | exact hta |
    exact PlOn.const _ | apply PlOn.addL | apply PlOn.mul

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwTW` -/

section
/-!
Two facts about the archive's treewidth: a graph on at most `w + 1` vertices has treewidth at most
`w` (a single bag), and a width at which there is no decomposition lies below the treewidth.
-/

namespace Lax117284Proofs.Machine.TwTW

open Lax228581.Treewidth

/-- The decomposition with one node and one bag holding every vertex. -/
def oneBag {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : TreeDecomposition G where
  Node := Unit
  tree := ⊥
  isTree := ⟨⟨fun u v => by cases u; cases v; exact SimpleGraph.Reachable.refl _⟩,
    SimpleGraph.isAcyclic_bot⟩
  bag _ := Finset.univ
  vertex_mem_bag v := ⟨(), Finset.mem_univ v⟩
  edge_mem_bag u v _ := ⟨(), Finset.mem_univ u, Finset.mem_univ v⟩
  bag_indices_connected v := by
    have : Nonempty {i : Unit | v ∈ (Finset.univ : Finset V)} := ⟨⟨(), Finset.mem_univ v⟩⟩
    refine ⟨fun a b => ?_⟩
    have : a = b := Subsingleton.elim _ _
    rw [this]

theorem hasTW_of_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {w : ℕ}
    (h : Fintype.card V ≤ w + 1) : HasTreewidthAtMost G w :=
  ⟨oneBag G, fun _ => by simpa [oneBag] using h⟩

theorem hasTW_mono {V : Type} {G : SimpleGraph V} {w w' : ℕ} (h : HasTreewidthAtMost G w)
    (hw : w ≤ w') : HasTreewidthAtMost G w' := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun i => (hD i).trans (by omega)⟩

/-- **A width without a decomposition lies below the treewidth.** -/
theorem lt_treewidth_of_not {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {w : ℕ}
    (h : ¬ HasTreewidthAtMost G w) : w < treewidth G := by
  have hne : {w | HasTreewidthAtMost G w}.Nonempty := ⟨Fintype.card V, hasTW_of_card G (by omega)⟩
  have hmem : treewidth G ∈ {w | HasTreewidthAtMost G w} := Nat.sInf_mem hne
  by_contra hc
  exact h (hasTW_mono hmem (by omega))

end Lax117284Proofs.Machine.TwTW

end

/-! ### `Lax117284Proofs.Machine.TwNum8` -/

section
/-!
The cost of the main program on a word, and its bound: a polynomial in the length, plus the cost of
the enumeration, which is only paid on a word whose length is bounded by a function of the days and
the treewidth.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284Proofs.Machine.TwMain (Kprep Kgi)

/-- The instance a word declares. -/
noncomputable def Ix (x : List ℕ) : Instance := decode x.dropLast

theorem Ix_eq {x : List ℕ} {I : Instance} {k : ℕ} (h : EncodesUniform x I k) : Ix x = I := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  unfold Ix
  rw [h1]
  exact Lax117284Proofs.Injectivity.decode_eq hy

/-- The bound on the number of instructions the program takes on a word. -/
noncomputable def Kdp (ca cc : ℕ) (x : List ℕ) : ℕ :=
  60 + dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x)

open Classical in
/-- **The cost of the main program on a word.** -/
noncomputable def Kx (prog : Program) (ca cc : ℕ) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    (if gdx cc x then
      Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + (Kdp ca cc x +
        (if Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x) then 0
          else Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3)))
    else 4 + (if 0 < mx x then Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3 else 12))))

open Classical in
/-- The polynomial part of the cost. -/
noncomputable def KP (prog : Program) (ca cc : ℕ) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    ((if gdx cc x then Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) +
      16)))

open Classical in
/-- The part of the cost that is the enumeration. -/
noncomputable def KB (cc : ℕ) (x : List ℕ) : ℕ :=
  if gdx cc x then
    (if Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x) then 0
      else Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3)
  else (if 0 < mx x then Lax117284Proofs.Machine.ClBrute.bruteCost (mx x) (nx x) + 3 else 0)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem Kx_le : Kx prog ca cc x ≤ KP prog ca cc x + KB cc x := by
  classical
  unfold Kx KP KB
  by_cases hg : gdx cc x
  · simp only [if_pos hg]
    by_cases ht : Lax228581.Treewidth.HasTreewidthAtMost (overallGraph (Ix x)) (wx cc x)
    · simp only [if_pos ht]; omega
    · simp only [if_neg ht]; omega
  · simp only [if_neg hg]
    by_cases hm : 0 < mx x
    · simp only [if_pos hm]; omega
    · simp only [if_neg hm]; omega

theorem plon_KP (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) : PlOn Lp Dm (KP prog ca cc) := by
  classical
  have hlen : PlOn Lp Dm (fun x => x.length) := atom_len
  have hlg : PlOn Lp Dm lgx := atom_lg
  have hK : PlOn Lp Dm (fun x => Kprep x.length (lgx x)) := by
    show PlOn Lp Dm (fun x => 40 + ((20 + 10 + 4) * x.length + 6) + 20 +
      ((40 + 10 + 4) * (lgx x + 1) + 6) + 100)
    repeat' first | exact hlen | exact hlg | exact PlOn.const _ | apply PlOn.addL | apply PlOn.mul
  have hm := atom_m (ca := ca) (cc := cc) hca hcc
  have hn := atom_n (ca := ca) (cc := cc) hca hcc
  have htb := atom_Tb (ca := ca) (cc := cc) hca hcc
  have hg : PlOn Lp (fun x => Dm x ∧ gdx cc x)
      (fun x => Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x)) := by
    have hgi : PlOn Lp (fun x => Dm x ∧ gdx cc x)
        (fun x => Kgi (mx x) (nx x) (Tbx ca cc x) prog.length) := by
      show PlOn Lp (fun x => Dm x ∧ gdx cc x) (fun x => 30 + ((214 * mx x + 90 + 20 + 4) *
        (nx x * nx x) + 6 + 60) + (13 * prog.length + 1 + 30 + 250 * (Tbx ca cc x + 1)))
      repeat' first | exact hm | exact hn | exact htb | exact PlOn.const _ | apply PlOn.addL |
        apply PlOn.mul
    have hdp : PlOn Lp (fun x => Dm x ∧ gdx cc x) (Kdp ca cc) := by
      show PlOn Lp (fun x => Dm x ∧ gdx cc x)
        (fun x => 60 + dpCostN (Tbx ca cc x) (mx x) (wx cc x + 1) (tabsx cc x))
      exact (PlOn.const 60).addL (plon_dpCostN hca hcc)
    exact hgi.addL ((PlOn.const 10).addL hdp)
  have hg' : PlOn Lp Dm (fun x => if gdx cc x then
      Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) :=
    PlOn.guard hg
  show PlOn Lp Dm (fun x => (24 * x.length + 60) + (Kprep x.length (lgx x) + (10 +
    ((if gdx cc x then Kgi (mx x) (nx x) (Tbx ca cc x) prog.length + (10 + Kdp ca cc x) else 0) +
      16))))
  exact (((PlOn.const 24).mul hlen).addL (PlOn.const 60)).addL
    (hK.addL ((PlOn.const 10).addL (hg'.addL (PlOn.const 16))))

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum9` -/

section
/-!
The enumeration is only paid for on a word whose length is bounded by a function of the number of
days and the treewidth.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph

/-- The largest length of a word on which the enumeration is run, for the parameter `p`. -/
def Fm (cc p : ℕ) : ℕ := 2 ^ TwPrep.geE cc p p

/-- The function of the parameter that bounds the cost of the enumeration. -/
def HB (cc p : ℕ) : ℕ := 5000 * 2 ^ Fm cc p * (2 * Fm cc p + 2) ^ 2 + 3

theorem geE_mono2 (cc : ℕ) {m m' w w' : ℕ} (hm : m ≤ m') (hw : w ≤ w') :
    TwPrep.geE cc m w ≤ TwPrep.geE cc m' w' := by
  unfold TwPrep.geE; gcongr

theorem brute_le_HB {cc p L m n : ℕ} (hL : L < Fm cc p) (hl : L = 3 + 2 * (m * n)) (hm : 0 < m) :
    Lax117284Proofs.Machine.ClBrute.bruteCost m n + 3 ≤ HB cc p := by
  have h1 := Lax117284Proofs.Machine.ClBrute.bruteCost_le m n
  have hn : n ≤ m * n := Nat.le_mul_of_pos_left _ hm
  have h2 : m * n + n + 2 ≤ 2 * Fm cc p + 2 := by omega
  have h3 : 2 ^ (m * n) ≤ 2 ^ Fm cc p := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 5000 * 2 ^ (m * n) * (m * n + n + 2) ^ 2 ≤ 5000 * 2 ^ Fm cc p * (2 * Fm cc p + 2) ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) (Nat.pow_le_pow_left h2 _)
  unfold HB
  omega

variable {cc : ℕ} {x : List ℕ}

/-- **The length of a word is below `Fm`** when the guard admits no width beyond `w'`. -/
theorem len_lt_Fm (hcc : 1 ≤ cc) (hx : Dm x) {p w' : ℕ} (hm : mx x ≤ p) (hw' : wcx cc x ≤ w')
    (hwp : w' ≤ p) : x.length < Fm cc p := by
  have hL0 := hx.three
  have h1 := (TwPrep.wcnt_spec hcc (mx x) (lgx x)).2.2
  have h2 : lgx x + 1 ≤ TwPrep.geE cc p p :=
    le_trans h1 (geE_mono2 cc hm (le_trans hw' hwp))
  have h3 : x.length < 2 ^ (lgx x + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  exact lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by norm_num) h2)

/-- **The enumeration costs at most a function of the parameter.** -/
theorem KB_le (hcc : 1 ≤ cc) (hx : Dm x) :
    KB cc x ≤ HB cc ((Ix x).days + treewidth (Ix x)) := by
  classical
  obtain ⟨I, k, hdec, hl, hn, hm⟩ := hx.len
  have hI : Ix x = I := Ix_eq hdec
  have hl' : x.length = 3 + 2 * (mx x * nx x) := by rw [hl, hm, hn]
  rw [hI]
  unfold KB
  rw [hI]
  by_cases hg : gdx cc x
  · simp only [if_pos hg]
    by_cases ht : Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)
    · simp only [if_pos ht]; exact Nat.zero_le _
    · simp only [if_neg ht]
      have hlt : wx cc x < treewidth I := Lax117284Proofs.Machine.TwTW.lt_treewidth_of_not ht
      have hwc : wcx cc x ≤ treewidth I := by have := hg.1; unfold wx at hlt; omega
      exact brute_le_HB (len_lt_Fm hcc hx (p := I.days + treewidth I) (w' := treewidth I)
        (by omega) hwc (by omega)) hl' hg.2
  · simp only [if_neg hg]
    by_cases hm0 : 0 < mx x
    · simp only [if_pos hm0]
      have hwc : wcx cc x = 0 := by
        by_contra h; exact hg ⟨by omega, hm0⟩
      exact brute_le_HB (len_lt_Fm hcc hx (p := I.days + treewidth I) (w' := 0) (by omega)
        (by omega) (by omega)) hl' hm0
    · simp only [if_neg hm0]; exact Nat.zero_le _

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum10` -/

section
/-!
The time bound: `10 * Kx + 1` is at most a function of the parameter times a power of the length.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph

/-- The function of the parameter in the time bound. -/
def Gp (cc Cp : ℕ) (p : ℕ) : ℕ := 10 * Cp + 10 * HB cc p + 1

theorem time_le {prog : Program} {ca cc : ℕ} (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) :
    ∃ Cp Ep : ℕ, ∀ x, Dm x →
      10 * Kx prog ca cc x + 1 ≤
        Gp cc Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ Ep := by
  obtain ⟨Cp, Ep, h⟩ := plon_KP (prog := prog) hca hcc
  refine ⟨Cp, Ep, fun x hx => ?_⟩
  have h1 := h x hx
  have h2 := KB_le (cc := cc) (by omega) hx
  have h3 := Kx_le (prog := prog) (ca := ca) (cc := cc) (x := x)
  have h4 : 1 ≤ (x.length + 1) ^ Ep := Nat.one_le_pow _ _ (by omega)
  unfold Lp at h1
  unfold Gp
  generalize (x.length + 1) ^ Ep = a at *
  generalize HB cc ((Ix x).days + treewidth (Ix x)) = hb at *
  nlinarith

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum11` -/

section
/-!
The decomposition step run on the graph of a word: what the cited theorem gives, in the numbers of
the main program.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)

/-- **The cited theorem**, for the program `prog` and the constant `ca`. -/
def AxStmt (prog : Program) (ca : ℕ) : Prop :=
  ∀ (W w : ℕ) (g : List ℕ) (I : Instance), EncodesGraph g I →
    (∀ v ∈ g ++ [w], ca * 2 ^ (ca * w ^ 3) * ((g ++ [w]).length + v + 1) ^ ca ≤ 2 ^ W) →
    ∃ (out : List ℕ) (t : ℕ), t ≤ ca * 2 ^ (ca * w ^ 3) * (g.length + 2) ^ ca ∧
      RunsTo W prog (g ++ [w]) out t ∧
      (out = [0] ∧ ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) w ∨
        ∃ D, out = 1 :: D ∧ NiceDecomposition I w D)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem core_key (hax : AxStmt prog ca) (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hpl : ca ≤ plit)
    (hx : Dm x) {I : Instance} {y0 : List ℕ} {k : ℕ} (hxe : x = y0 ++ [k])
    (hy : EncodesInstance y0 I) (hn : nx x = I.clients) (hm : mx x = I.days) :
    ∃ (z : List ℕ) (t : ℕ), t ≤ Tbx ca cc x ∧
      (gdx cc x → RunsTo (Wpx cc plit x) prog (TwGraph.gwList x (nx x) (mx x) ++ [wx cc x]) z t ∧
        (z = [0] ∨ ∃ D, z = 1 :: D)) ∧
      (gdx cc x → ∀ D, z = 1 :: D → NiceDecomposition I (wx cc x) D ∧ D.length + 1 ≤ t) ∧
      (gdx cc x → z = [0] → ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)) ∧
      (¬ gdx cc x → z = [0]) := by
  by_cases hg : gdx cc x
  · have gd := hx.gd hca hcc hg
    have hnL := hx.nL hg.2
    have hXy : ∀ j < y0.length, x.getD j 0 = y0.getD j 0 := by
      intro j hj
      rw [hxe, List.getD_append _ _ _ _ hj]
    have hEG : EncodesGraph (TwGraph.gwList x (nx x) (mx x)) I := by
      rw [hn, hm]; exact TwGraph.encodesGraph_gwList hy hXy
    have hlen : (TwGraph.gwList x (nx x) (mx x) ++ [wx cc x]).length = nx x * nx x + 2 := by
      simp [TwGraph.gwList_length]; omega
    have hwL : wx cc x ≤ x.length := by have := gd.wlg; have := gd.lgL; omega
    obtain ⟨out, t, ht, hrun, hcase⟩ := hax (Wpx cc plit x) (wx cc x)
      (TwGraph.gwList x (nx x) (mx x)) I hEG (by
        intro v hv
        rw [hlen]
        have hvL : v ≤ x.length := by
          rcases List.mem_append.mp hv with hv | hv
          · rcases Machine.TwNum.mem_gwList hv with rfl | h1
            · exact hnL
            · have := gd.hL; omega
          · have : v = wx cc x := by simpa using hv
            omega
        exact gd.ax hnL hvL hpl)
    have ht' : t ≤ Tbx ca cc x := by
      refine le_trans ht (le_of_eq ?_)
      unfold Tbx
      rw [TwGraph.gwList_length]
      congr 2; ring
    refine ⟨out, t, ht', fun _ => ⟨hrun, ?_⟩, fun _ D hD => ?_, fun _ h0 => ?_, fun h => absurd hg h⟩
    · rcases hcase with ⟨h, -⟩ | ⟨D, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨D, h⟩
    · rcases hcase with ⟨h, -⟩ | ⟨D', h, hN⟩
      · rw [h] at hD; simp at hD
      · rw [h] at hD
        have hDD : D' = D := by simpa using hD
        subst hDD
        refine ⟨hN, ?_⟩
        have := TwSetup.RunsTo.out_length_le hrun
        rw [h] at this; simpa using this
    · rcases hcase with ⟨-, h⟩ | ⟨D, h, -⟩
      · exact h
      · rw [h] at h0; simp at h0
  · exact ⟨[0], 0, Nat.zero_le _, fun h => absurd h hg, fun h => absurd h hg,
      fun h => absurd h hg, fun _ => rfl⟩

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum12` -/

section
/-!
The main program solves the problem: on every word of the domain it runs, within the bound `Bx` on
its values and the cost `Kx`, to an output that is the answer.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)
open Lax117284Proofs.Machine.TwMain (W)
open Lax117284Proofs.Machine.TwNode (Params)

/-- What the program answers: `1` for a word whose instance block has a `k`-fair schedule. -/
noncomputable def fAnsT (x : List ℕ) : List ℕ :=
  open Classical in if (decode x.dropLast).HasKFairSchedule (parameter x) then [1] else [0]

theorem fAnsT_eq {x : List ℕ} {I : Instance} {k : ℕ} (h : EncodesUniform x I k) :
    fAnsT x = open Classical in if I.HasKFairSchedule k then [1] else [0] := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  have h2 : parameter (y ++ [k]) = k := by simp [parameter]
  unfold fAnsT
  rw [h1, h2, Lax117284Proofs.Injectivity.decode_eq hy]

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

theorem dpCost_le {I : Instance} {y0 : List ℕ} {k : ℕ} {D : List ℕ} {w : ℕ} (hwe : w = wx cc x)
    (hy : EncodesInstance y0 I) (hD : NiceDecomposition I w D) (hm : mx x = I.days)
    (hN : nodeCount D ≤ Tbx ca cc x) :
    60 + TwNode.dpCost ⟨I, y0, k, D, w, hy, hD⟩ ≤ Kdp ca cc x := by
  subst hwe
  have e1 : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).tabs = tabsx cc x := by
    simp [Params.tabs, Params.bs, Params.wid, Params.m, tabsx, hm]
  have e2 : (⟨I, y0, k, D, wx cc x, hy, hD⟩ : Params).m = mx x := hm.symm
  rw [dpCost_eq, e1, e2]
  unfold Kdp
  exact Nat.add_le_add_left (dpCostN_mono hN _ _ _) 60

open Classical in
theorem Kmain_le {I : Instance} {z : List ℕ} {t : ℕ} (hI : Ix x = I) (hn : nx x = I.clients)
    (hm : mx x = I.days)
    (hgiff : (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) ↔ gdx cc x)
    (ht : t ≤ Tbx ca cc x)
    (hz : gdx cc x → z = [0] →
      ¬ Lax228581.Treewidth.HasTreewidthAtMost (overallGraph I) (wx cc x)) :
    TwMain.Kmain x.length (Nat.log 2 x.length) I.days I.clients t prog.length (Kdp ca cc x)
      (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) (z = [0]) ≤
      Kx prog ca cc x := by
  have hK : TwMain.Kgi I.days I.clients t prog.length ≤ TwMain.Kgi I.days I.clients (Tbx ca cc x)
      prog.length := by unfold TwMain.Kgi; omega
  unfold TwMain.Kmain Kx
  rw [hI]
  simp only [hn, hm, lgx]
  by_cases hg : gdx cc x
  · simp only [if_pos (hgiff.2 hg), if_pos hg]
    by_cases hz0 : z = [0]
    · have := hz hg hz0
      simp only [if_pos hz0, if_neg this]
      omega
    · simp only [if_neg hz0]
      split_ifs <;> omega
  · simp only [if_neg (fun h => hg (hgiff.1 h)), if_neg hg]
    omega

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwNum13` -/

section
/-!
The correctness of the main program on a word of the domain, with the bound and the cost of this
development.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)
open Lax117284Proofs.Machine.ClMain (Mx le_Mx)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

open Classical in
/-- **The main program solves the problem on a word of the domain.** -/
theorem core (hax : AxStmt prog ca) (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hpl1 : PLit prog ≤ plit)
    (hpl2 : ca ≤ plit) (hx : Dm x) :
    ∃ σ', Run (Bx prog ca cc plit x) (TwMain.mainCom prog cc plit)
        (initEnv (extx prog ca cc plit x) x) σ' (Kx prog ca cc x) ∧ σ'.out = fAnsT x := by
  have hx' : x ∈ UniformInstances := hx
  obtain ⟨I, k, hdec⟩ := hx'
  obtain ⟨y0, hxe, hy⟩ := id hdec
  have hn : nx x = I.clients := ClientsWord.x0 hdec
  have hm : mx x = I.days := ClientsWord.x1 hdec
  have hI : Ix x = I := Ix_eq hdec
  obtain ⟨z, t, ht, hcit0, hnice0, hnoTW, hnogd⟩ := core_key hax hca hcc hpl2 hx hxe hy hn hm
  obtain ⟨hL, hbr, hXB, hnB, hmB, hmnB, hgeB, hccB, hplB, hwpB, hPB⟩ :=
    B_unc (prog := prog) (ca := ca) (cc := cc) (plit := plit) hx
  have hw : wx cc x = TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1 := by
    unfold wx wcx lgx; rw [hm]
  have hgiff : (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) ↔ gdx cc x := by
    unfold gdx wcx lgx; rw [hm]
  have hk : k ≤ Mx x := le_Mx (by rw [hxe]; simp)
  rw [hn] at hnB hmnB
  rw [hm] at hmB hmnB hgeB
  have hmain := TwMain.main_run (B := Bx prog ca cc plit x) hxe hy prog cc plit (by omega)
    (extx prog ca cc plit x) (Tbx ca cc x + 4) (Kdp ca cc x) z t
    (initEnv (extx prog ca cc plit x) x) rfl rfl ⟨fun a _ => rfl, fun v _ => rfl⟩
    (by simp [extx]) (by simp [extx, hn]) (by simp [extx]) (by simp [extx]) (by simp [extx])
    (by simp [extx]) (by simp [extx, Wpx, lgx]) (by simp [extx]) (by simp [extx, hm, hn])
    hL hbr hXB hnB hmB hmnB hgeB hccB hplB hwpB hPB
    (fun h => by
      have := gb_of hca hcc hx (hgiff.1 h) hpl1
      rw [hn, hm, hw] at this
      exact this)
    (fun h => by
      have hg := hgiff.1 h
      obtain ⟨hr, hzc⟩ := hcit0 hg
      rw [hn, hm, hw] at hr
      exact ⟨hr, by omega, hzc⟩)
    (fun D hD hz => by
      have hg : gdx cc x := by
        by_contra h
        have := hnogd h
        rw [this] at hz; simp at hz
      obtain ⟨-, hlen⟩ := hnice0 hg D hz
      have hDl := hD.length_eq
      have hN : nodeCount D ≤ Tbx ca cc x := by omega
      have hN3 : 3 * nodeCount D + 2 ≤ Tbx ca cc x := by omega
      exact dpb_of hca hcc hx hg hw.symm hy hD hn hm hk hN3 (dpCost_le hw.symm hy hD hm hN))
    (fun D h hz => by
      have := (hnice0 (hgiff.1 h) D hz).1
      rw [hw] at this; exact this)
  obtain ⟨σ', hrun, hout⟩ := hmain
  refine ⟨σ', hrun.mono (Kmain_le hI hn hm hgiff ht hnoTW), ?_⟩
  rw [hout, fAnsT_eq hdec]
  by_cases hK : I.HasKFairSchedule k <;> simp [hK]

end Lax117284Proofs.Machine.TwNum

end

/-! ### `Lax117284Proofs.Machine.TwLay` -/

section
/-!
The layout of the main program: the scalars and arrays it mentions and the depth of its
expressions, and the proof that a layout that has them compiles it.
-/

namespace Lax117284Proofs.Machine.TwLay

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846.Ram
open Lax117284Proofs.Machine.ClMain (cS cA cD eS eA eD com_ok)
open Lax117284Proofs.Machine.TwMain

/-- The arrays of the machine. -/
def arrsT : List String :=
  ["OP", "XA", "XB", "XC", "Y", "M", "O", "BG", "SZ", "TB", "X", "bfsc"]

/-- A command fits: its arrays are the machine's and it needs at most five temporaries. -/
def Fine (c : Com) : Prop := (∀ a ∈ cA c, a ∈ arrsT) ∧ cD c ≤ 5

theorem Fine.seq {c d : Com} (h1 : Fine c) (h2 : Fine d) : Fine (.seq c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem Fine.ite {b : Cond} {c d : Com} (hb : eD (condExpr b) ≤ 5)
    (hbA : ∀ a ∈ eA (condExpr b), a ∈ arrsT) (h1 : Fine c) (h2 : Fine d) :
    Fine (.ite b c d) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [cA, List.mem_append] at ha
    rcases ha with ha | ha | ha
    · exact hbA a ha
    · exact h1.1 a ha
    · exact h2.1 a ha
  · simp only [cD]; have := h1.2; have := h2.2; omega

theorem fine_read : Fine ClMain.readCom := by unfold Fine; decide +kernel
theorem fine_prep (cc plit : ℕ) : Fine (TwPrep.prepCom cc plit) := by
  have : Fine (TwPrep.prepCom 0 0) := by unfold Fine; decide +kernel
  exact this
theorem fine_mask : Fine TwPrep.maskCom := by unfold Fine; decide +kernel
theorem fine_gw : Fine TwGraph.gwCom := by unfold Fine; decide +kernel
theorem fine_loop : Fine TwRam.loopCom := by unfold Fine; decide +kernel
theorem fine_init (plen : ℕ) : Fine (TwSetup.initCom plen) := by
  have : Fine (TwSetup.initCom 0) := by unfold Fine; decide +kernel
  exact this
theorem fine_dpSetup : Fine TwNode.dpSetup := by unfold Fine; decide +kernel
theorem fine_dpCom : Fine TwNode.dpCom := by unfold Fine; decide +kernel
theorem fine_brute0 : Fine brute0 := by unfold Fine brute0 brute zeroCom; decide +kernel

theorem fine_loadFrom (P : List Instr) (j : ℕ) : Fine (TwSetup.loadFrom j P) := by
  induction P generalizing j with
  | nil => refine ⟨fun a ha => ?_, ?_⟩ <;> simp [TwSetup.loadFrom, cA, cD] at *
  | cons i rest ih =>
    have hs : Fine (TwSetup.storeIns j i) := by
      have : Fine (TwSetup.storeIns 0 (.halt)) := by unfold Fine; decide +kernel
      exact this
    exact hs.seq (ih (j + 1))

theorem fine_brute : Fine brute := by unfold Fine brute; decide +kernel

theorem fine_interp (prog : Program) : Fine (TwSetup.interpCom prog) :=
  (fine_loadFrom prog 0).seq ((fine_init prog.length).seq fine_loop)

theorem eD_ok : eD (condExpr (.eq (Expr.get "O" (Expr.lit 0)) (Expr.lit 1))) ≤ 5 := by
  decide +kernel
theorem eA_ok : ∀ a ∈ eA (condExpr (.eq (Expr.get "O" (Expr.lit 0)) (Expr.lit 1))), a ∈ arrsT := by
  decide +kernel
theorem eD_ok' : eD (condExpr (.lt (Expr.lit 0) (Expr.var "ok"))) ≤ 5 := by decide +kernel
theorem eA_ok' : ∀ a ∈ eA (condExpr (.lt (Expr.lit 0) (Expr.var "ok"))), a ∈ arrsT := by decide +kernel

theorem fine_guarded (prog : Program) : Fine (guarded prog) :=
  (fine_mask.seq (fine_gw.seq (fine_interp prog))).seq
    (Fine.ite eD_ok eA_ok (fine_dpSetup.seq fine_dpCom) fine_brute)

theorem fine_main (prog : Program) (cc plit : ℕ) : Fine (mainCom prog cc plit) :=
  fine_read.seq ((fine_prep cc plit).seq (Fine.ite eD_ok' eA_ok' (fine_guarded prog) fine_brute0))

/-- **The layout of the main program.** -/
def layoutT (prog : Program) (cc plit : ℕ) : Layout := ⟨cS (mainCom prog cc plit), arrsT, 5⟩

theorem layout_ok (prog : Program) (cc plit : ℕ) : Com.Ok (layoutT prog cc plit) (mainCom prog cc plit) :=
  com_ok (layoutT prog cc plit) (mainCom prog cc plit) (fun y h => h) (fine_main prog cc plit).1
    (fine_main prog cc plit).2

end Lax117284Proofs.Machine.TwLay

end

/-! ### `Lax117284Proofs.Machine.TwFinal` -/

section
/-!
The second bullet of Theorem 4, from the cited theorem on nice tree decompositions: the main
program decides the problem within `c * g (parameter) * (|x| + 1) ^ c` instructions.
-/

namespace Lax117284Proofs.Machine.TwFinal

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Transfer Lax808846Proofs.Compile
open Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax117284.ParameterizedComplexity
open Lax117284Proofs.Machine.TwNum
open Lax117284Proofs.Machine.ClMain (Mx le_Mx Mx_mem_or_zero)

theorem mono_ineq {c c' : ℕ} (hc : c ≤ c') (b w : ℕ) (hb : 1 ≤ b) :
    c * 2 ^ (c * w ^ 3) * b ^ c ≤ c' * 2 ^ (c' * w ^ 3) * b ^ c' :=
  Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num)
    (Nat.mul_le_mul_right _ hc))) (Nat.pow_le_pow_right hb hc)

/-- The cited theorem holds at every larger constant. -/
theorem AxStmt.mono {prog : Program} {c c' : ℕ} (h : AxStmt prog c) (hc : c ≤ c') :
    AxStmt prog c' := by
  intro W w g I hg hyp
  obtain ⟨out, t, ht, hr, hcase⟩ := h W w g I hg (fun v hv =>
    le_trans (mono_ineq hc _ w (by omega)) (hyp v hv))
  exact ⟨out, t, ht.trans (mono_ineq hc _ w (by omega)), hr, hcase⟩

theorem fits_Mx {c w : ℕ} {x : List ℕ} (hx : Dm x) (hf : Fits c w x) :
    c * (x.length + Mx x + 1) ^ c ≤ 2 ^ w := by
  have hl := hx.three
  rcases Mx_mem_or_zero x with hm | hm
  · exact hf _ hm
  · have h0 := hf (x.getD 0 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    rw [hm]
    have : c * (x.length + 0 + 1) ^ c ≤ c * (x.length + x.getD 0 0 + 1) ^ c :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega

theorem fits_num {a b CB EB S c w : ℕ} (ha : 1 ≤ a) (hb : b ≤ CB * a ^ EB) (hEB : EB ≤ c)
    (hc : 7 + S + 12 * CB ≤ c) (h2 : c * a ^ c ≤ 2 ^ w) :
    b ≤ 2 ^ w ∧ 5 + 2 + S + 12 * b ≤ 2 ^ w := by
  have h1 : a ^ EB ≤ a ^ c := Nat.pow_le_pow_right ha hEB
  have h3 : b ≤ CB * a ^ c := hb.trans (Nat.mul_le_mul_left _ h1)
  have h4 : 1 ≤ a ^ c := Nat.one_le_pow _ _ ha
  refine ⟨?_, ?_⟩
  · have : CB * a ^ c ≤ c * a ^ c := Nat.mul_le_mul_right _ (by omega)
    omega
  · have h5 : (7 + S + 12 * CB) * a ^ c ≤ c * a ^ c := Nat.mul_le_mul_right _ hc
    have h6 : 7 + S ≤ (7 + S) * a ^ c := Nat.le_mul_of_pos_right _ h4
    nlinarith

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The problem is fixed-parameter tractable in the number of days plus the treewidth**, given
the cited theorem. -/
theorem fpt_real (hex : ∃ (prog : Program) (c : ℕ), AxStmt prog c) :
    FptDecision Lax117284.Theorem4.byDaysAndTreewidth := by
  obtain ⟨prog, c0, hax0⟩ := hex
  have hca : 1 ≤ c0 + 1 := by omega
  have hcc : c0 + 1 + 1 ≤ c0 + 1 + 1 := le_rfl
  have hax : AxStmt prog (c0 + 1) := AxStmt.mono hax0 (by omega)
  obtain ⟨Cp, Ep, hT⟩ := time_le (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1) hca hcc
  obtain ⟨CB, EB, hB⟩ := plon_Bx (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1)
    (plit := PLit prog + (c0 + 1) + 1) hca hcc
  set lay := TwLay.layoutT prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) with hlay
  set S := lay.scalars.length with hS
  set c := Ep + EB + (7 + S + 12 * CB) + 1 with hcdef
  have hg : Computable (Gp (c0 + 1 + 1) Cp) := by
    unfold Gp HB Fm TwPrep.geE
    bound_computable
  apply Lax117284Proofs.FptBridge.decision (prog := compileProgram lay
    (TwMain.mainCom prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1))) (c := c) hg
  intro w
  have hs : Solves lay (TwMain.mainCom prog (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1))
      {x | x ∈ Lax117284.Theorem4.byDaysAndTreewidth.Domain ∧ Fits c w x} fAnsT
      (Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1))
      (Kx prog (c0 + 1) (c0 + 1 + 1)) := by
    refine ⟨TwLay.layout_ok _ _ _, fun x hx v hv => ?_, fun x hx => ?_⟩
    · exact (B_unc (prog := prog) (ca := c0 + 1) (cc := c0 + 1 + 1)
        (plit := PLit prog + (c0 + 1) + 1) hx.1).2.2.1 v hv
    · exact ⟨extx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x,
        core hax hca hcc (by omega) (by omega) hx.1⟩
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hx, hf⟩
    have hfM := fits_Mx hx hf
    have hb := hB x hx
    have ha : 1 ≤ Aw x := Aw_pos x
    have := fits_num (S := S) (w := w) ha hb (by omega) (by omega) hfM
    refine fitsWords_of_max_le (Bx_pos x) (max_le this.1 ?_)
    have e : lay.span (Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x) =
        5 + 2 + S + 12 * Bx prog (c0 + 1) (c0 + 1 + 1) (PLit prog + (c0 + 1) + 1) x := rfl
    rw [e]; exact this.2
  · rintro x ⟨hx, hf⟩
    have h1 := hT x hx
    have h2 : (x.length + 1) ^ Ep ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1 ≤
        Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c :=
      h1.trans (Nat.mul_le_mul_left _ h2)
    show 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1 ≤ c * Gp (c0 + 1 + 1) Cp
      ((decode x.dropLast).days + treewidth (decode x.dropLast)) * (x.length + 1) ^ c
    have : Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) ≤
        c * Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    calc 10 * Kx prog (c0 + 1) (c0 + 1 + 1) x + 1
        ≤ Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c := h3
      _ ≤ c * Gp (c0 + 1 + 1) Cp ((Ix x).days + treewidth (Ix x)) * (x.length + 1) ^ c :=
          Nat.mul_le_mul_right _ this

end Lax117284Proofs.Machine.TwFinal

end
