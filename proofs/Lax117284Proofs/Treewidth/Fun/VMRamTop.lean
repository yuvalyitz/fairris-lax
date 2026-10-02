import Lax117284Proofs.Treewidth.Fun.VMRamLoop
import Lax117284Proofs.Treewidth.Fun.VMTop

/-!
# WP V2 (6): compilability, initial states, and `vm_ram_correct`
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-! ## `Com.Ok` for the layout, block by block -/

macro "okSimp" : tactic => `(tactic| simp [Com.Ok, Cond.Ok, Expr.Ok, condExpr, Lvm, arrNames, tp, nx, incPc, incSp, decSp])

theorem ok_bHalt : Com.Ok Lvm bHalt := by unfold bHalt; okSimp
theorem ok_bLit : Com.Ok Lvm bLit := by unfold bLit; okSimp
theorem ok_bVar : Com.Ok Lvm bVar := by unfold bVar; okSimp
theorem ok_bBin (o : Bop) : Com.Ok Lvm (bBin o) := by unfold bBin; okSimp
theorem ok_bLt : Com.Ok Lvm bLt := by unfold bLt; okSimp
theorem ok_bEq : Com.Ok Lvm bEq := by unfold bEq; okSimp
theorem ok_bCons : Com.Ok Lvm bCons := by unfold bCons; okSimp
theorem ok_bFst : Com.Ok Lvm bFst := by unfold bFst; okSimp
theorem ok_bSnd : Com.Ok Lvm bSnd := by unfold bSnd; okSimp
theorem ok_bIsNat : Com.Ok Lvm bIsNat := by unfold bIsNat; okSimp
theorem ok_bJz : Com.Ok Lvm bJz := by unfold bJz; okSimp
theorem ok_bJmp : Com.Ok Lvm bJmp := by unfold bJmp; okSimp
theorem ok_bSlide : Com.Ok Lvm bSlide := by unfold bSlide; okSimp
theorem ok_bCall : Com.Ok Lvm bCall := by unfold bCall; okSimp
theorem ok_bRet : Com.Ok Lvm bRet := by unfold bRet; okSimp
theorem ok_bFetch : Com.Ok Lvm bFetch := by unfold bFetch; okSimp

theorem ok_blkOp (j : ℕ) : Com.Ok Lvm (blkOp j) := by
  unfold blkOp
  split
  all_goals first
    | exact ok_bHalt
    | exact ok_bLit
    | exact ok_bVar
    | exact ok_bBin _
    | exact ok_bLt
    | exact ok_bEq
    | exact ok_bCons
    | exact ok_bFst
    | exact ok_bSnd
    | exact ok_bIsNat
    | exact ok_bJz
    | exact ok_bJmp
    | exact ok_bSlide
    | exact ok_bCall
    | exact ok_bRet

theorem ok_dispatchFrom : ∀ (f k : ℕ), Com.Ok Lvm (dispatchFrom k f) := by
  intro f
  induction f with
  | zero => intro k; simpa [dispatchFrom] using ok_blkOp k
  | succ f ih =>
    intro k
    simp only [dispatchFrom, Com.Ok]
    refine ⟨?_, ok_blkOp k, ih (k + 1)⟩
    simp [Cond.Ok, Expr.Ok, condExpr, Lvm]

/-- **The interpreter compiles under the layout `Lvm`.** -/
theorem ok_vmLoop : Com.Ok Lvm vmLoop := by
  unfold vmLoop
  simp only [Com.Ok]
  refine ⟨by simp [Cond.Ok, Expr.Ok, condExpr, Lvm], ?_⟩
  unfold bBody
  exact ⟨ok_bFetch, ok_dispatchFrom 16 0⟩

/-! ## Compilability is monotone in the layout (V3 extends `Lvm` by its reader/writer names) -/

theorem expr_ok_mono {L L' : Layout} (hs : ∀ x ∈ L.scalars, x ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e d := by
  intro e
  induction e with
  | lit n => intro d _; exact Expr.ok_lit _ _ _
  | var x => intro d h; exact hs x h
  | get a i ih => intro d h; exact ⟨ha a h.1, ih d h.2.1, by have := h.2.2; omega⟩
  | bin o e f ihe ihf => intro d h; exact ⟨ihf d h.1, ihe (d + 1) h.2.1, by have := h.2.2; omega⟩

theorem com_ok_mono {L L' : Layout} (hs : ∀ x ∈ L.scalars, x ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ c : Com, Com.Ok L c → Com.Ok L' c := by
  have hE := expr_ok_mono hs ha ht
  have hC : ∀ (b : Cond) (d : ℕ), Cond.Ok L b d → Cond.Ok L' b d := by
    intro b d h; exact hE _ _ h
  intro c
  induction c with
  | skip => intro _; exact Com.ok_skip _
  | assign x e => intro h; exact ⟨hs x h.1, hE _ _ h.2⟩
  | store a i e => intro h; exact ⟨ha a h.1, hE _ _ h.2.1, hE _ _ h.2.2.1, by have := h.2.2.2; omega⟩
  | seq c d ihc ihd => intro h; exact ⟨ihc h.1, ihd h.2⟩
  | ite b c d ihc ihd => intro h; exact ⟨hC b 0 h.1, ihc h.2.1, ihd h.2.2⟩
  | «while» b c ih => intro h; exact ⟨hC b 0 h.1, ih h.2⟩
  | read x => intro h; exact hs x h
  | write e => intro h; exact ⟨hE _ _ h.1, by have := h.2; omega⟩

/-! ## Initial and final states -/

/-- **What the loader (V3) must establish, part 1.**  An initial configuration `⟨0, stk, [], H⟩` is represented as
soon as the scalars are right and the stack and the heap sit in their arrays. -/
theorem Abs.init {σ : Lax808846Proofs.Imp.Env} {stk : List ℕ} {H : List (ℕ × ℕ)} (hpc : σ.vars "pc" = 0)
    (hsp : σ.vars "sp" = stk.length) (hrp : σ.vars "rp" = 0) (hhp : σ.vars "hp" = H.length)
    (hstk : Pfx stk.reverse (σ.arrs "STK")) (hha : Pfx (H.map Prod.fst) (σ.arrs "HA"))
    (hhb : Pfx (H.map Prod.snd) (σ.arrs "HB")) : Abs ⟨0, stk, [], H⟩ σ :=
  ⟨hpc, hsp, by simpa using hrp, hhp, hstk, Pfx.nil _, Pfx.nil _, hha, hhb⟩

/-- **What the loader (V3) must establish, part 2.**  The constants: the code, operand and function-table
arrays are the `W + 1` first cells of the program; the other five arrays have length `W + 1`; `B` holds `P.B`;
every operand of the program is `< Bi`. -/
theorem Cst.of_arrays {P : Prog} {W Bi : ℕ} {σ : Lax808846Proofs.Imp.Env} (htb : σ.vars "B" = P.B)
    (hOP : σ.arrs "OP" = arrOf (W + 1) (fun i => opc (P.code i)))
    (hOA : σ.arrs "OA" = arrOf (W + 1) (fun i => opa (P.code i)))
    (hFT : σ.arrs "FT" = arrOf (W + 1) P.ft)
    (hlen : ∀ a ∈ ["STK", "RETPC", "RETH", "HA", "HB"], (σ.arrs a).length = W + 1)
    (hopa : ∀ i, i ≤ W → opa (P.code i) < Bi) (hbW : P.B ≤ W) (hbi : W + 18 ≤ Bi) : Cst P W Bi σ where
  tb := htb
  op := fun i hi => by rw [hOP, getElem?_arrOf _ (by omega)]
  oa := fun i hi => by rw [hOA, getElem?_arrOf _ (by omega)]
  ft := fun i hi => by rw [hFT, getElem?_arrOf _ (by omega)]
  opa_lt := hopa
  len := fun a ha => by
    simp only [arrNames, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hOP]; simp
    · rw [hOA]; simp
    · rw [hFT]; simp
    all_goals exact hlen _ (by simp)
  bW := hbW
  bi := hbi

/-- The result of a finished run: the stack has the result on top, above the untouched `stk₀`. -/
theorem Abs.result {σ : Lax808846Proofs.Imp.Env} {w : ℕ} {stk₀ : List ℕ} {H' : List (ℕ × ℕ)}
    (hA : Abs ⟨2, w :: stk₀, [], H'⟩ σ) :
    σ.vars "sp" = stk₀.length + 1 ∧ (σ.arrs "STK")[stk₀.length]? = some w := by
  refine ⟨by simpa using hA.sp, ?_⟩
  have := hA.stk (stk₀.length) (by simp)
  simpa using this

/-! ## The combined theorem -/

end Lax117284Proofs.Treewidth.Fun.VM.Ram
