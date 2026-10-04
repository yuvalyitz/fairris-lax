import Lax117284Proofs.Treewidth.Fun.VMRamTop
import Lax117284Proofs.Treewidth.Fun.ToVal

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadCode` -/

section
/-!
# WP V3 (1): the loaded program — a function-entry table cut off at `N`, and `vm_ram_correct` for it

`vm_ram_correct` (V2) is stated for `mkProg Δ N main k B`, whose entry table `ft f = offset Δ f` is defined for *all*
`f`.  Its `Cst` therefore asks the array `FT` to be correct on the whole range `0 … W`, and `W` is (a multiple of) the
run-time word bound, which is *not* affordable to fill.  The function ids that a run ever calls are all `< N`
(`Δ f = some _`), so nothing is lost by cutting the table: `mkProgF` is `mkProg` with `ft f = 0` for `f ≥ N`, and the
V1/V2 proofs go through verbatim (they only use `Prog.Real` and the stub).  Here the two theorems are re-stated for it.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- The IMP+ environment (`Env` alone means the VM's `Env`, in this namespace). -/
abbrev IEnv : Type := Lax808846Proofs.Imp.Env

/-- `mkProg` with the entry table cut off at `N` (`ft f = 0` for `f ≥ N`, where `Δ f = none`). -/
def mkProgF (Δ : ℕ → Option Tm) (N main k B : ℕ) : Prog :=
  { mkProg Δ N main k B with ft := fun f => if f < N then offset Δ f else 0 }

theorem mkProgF_ft (Δ : ℕ → Option Tm) (N main k B f : ℕ) :
    (mkProgF Δ N main k B).ft f = if f < N then offset Δ f else 0 := rfl

theorem mkProgF_real (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main k B : ℕ) :
    (mkProgF Δ N main k B).Real Δ := by
  intro f body hf
  have hfN : f < N := by
    by_contra h
    have := hN f (by omega); rw [this] at hf; simp at hf
  have hfit := mkProg_fits Δ hfN main k B
  have hcode : funCode Δ f = compile id body ++ [.ret] := by simp [funCode, hf]
  rw [hcode] at hfit
  have hft : (mkProgF Δ N main k B).ft f = offset Δ f := by rw [mkProgF_ft, if_pos hfN]
  have h1 := hfit.1
  have h2 := le_offset Δ f
  have hft' : (mkProg Δ N main k B).ft f = offset Δ f := rfl
  refine ⟨?_, ?_⟩
  · show f ≤ (mkProg Δ N main k B).len
    omega
  · rw [hft]
    rw [hft'] at hfit
    exact hfit

theorem mkProgF_stub (Δ : ℕ → Option Tm) (N main k B : ℕ) :
    FitsAt (mkProgF Δ N main k B) 0 (stub main k) := mkProg_stub Δ N main k B

/-- V1 (`vm_runs`) for any program that realizes the table and starts with the stub. -/
theorem vm_runs_gen {P : Prog} (Δ : ℕ → Option Tm) (hreal : P.Real Δ) {main : ℕ} {xs : List Val}
    (hstub : FitsAt P 0 (stub main xs.length)) (hB : 2 ≤ P.B) {y : Val} {c : ℕ}
    (h : Runs Δ P.B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL P.B H ws xs) {W : ℕ}
    (hbd : St.Bd W ⟨0, ws ++ stk₀, [], H⟩) (hL : P.len ≤ W)
    (hheap : P.B + H.length + c ≤ W) (hstk : (ws ++ stk₀).length + 3 * c ≤ W) (hret : 3 * c + 1 ≤ W) :
    ∃ n ≤ 3 * c + 3, ∃ (w : ℕ) (H' : List (ℕ × ℕ)),
      StepsB P W n ⟨0, ws ++ stk₀, [], H⟩ ⟨2, w :: stk₀, [], H'⟩ ∧
        HExt H H' ∧ Rep P.B H' w y ∧ H'.length ≤ H.length + c := by
  obtain ⟨body, hΔ, c', hc', hev⟩ := h
  have hsim := ev_sim hB hreal hev
  have hpos := hev.pos
  have hlen3 : 3 ≤ P.len := by simpa [stub] using hstub.1
  have hcode0 : P.code 0 = .lit main := by simpa [stub] using hstub.head
  have hcode1 : P.code 1 = .call ws.length := by
    have := (hstub.tail).head
    simpa [stub, hrep.length_eq] using this
  have hmain : main ≤ W := Nat.le_trans (hreal main body hΔ).1 hL
  have hstep := step_lit (P := P) (s := ⟨0, ws ++ stk₀, [], H⟩) hcode0
  have hbd₁ : St.Bd W ⟨0 + 1, main :: (ws ++ stk₀), [], H⟩ :=
    hbd.setStk (by omega) (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hmain
      · exact hbd.stk x hx) (by simp only [List.length_cons]; omega)
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := callee_run hreal hΔ hsim (ws := ws) (stk₀ := stk₀) (ret₀ := [])
    (H := H) (pcc := 1) hcode1 hrep hbd₁ hL (by omega) (by omega) (by omega) (by show 0 + 1 + 3 * c' ≤ W; omega)
  exact ⟨n + 1, by omega, w, H', StepsB.step hbd hstep hs, hx, hr, by omega⟩

/-- **`vm_ram_correct` for the cut table** (statement of V2 with `mkProgF`). -/
theorem vm_ram_correctF (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) {B : ℕ} (hB : 2 ≤ B)
    {main : ℕ} {xs : List Val} {y : Val} {c : ℕ} (h : Runs Δ B main xs y c) {ws stk₀ : List ℕ}
    {H : List (ℕ × ℕ)} (hrep : RepL B H ws xs) {W₀ : ℕ} (hbd : St.Bd W₀ ⟨0, ws ++ stk₀, [], H⟩)
    {Bi : ℕ} {σ : Lax808846Proofs.Imp.Env}
    (hA : Abs ⟨0, ws ++ stk₀, [], H⟩ σ)
    (hC : Cst (mkProgF Δ N main xs.length B)
      (W₀ + (mkProgF Δ N main xs.length B).len + B + 3 * c + 3) Bi σ)
    (hrun : σ.vars "run" = 1) :
    ∃ (w : ℕ) (H' : List (ℕ × ℕ)) (σ' : Lax808846Proofs.Imp.Env),
      Run Bi vmLoop σ σ' (124 * (3 * c + 4)) ∧ Abs ⟨2, w :: stk₀, [], H'⟩ σ' ∧
      Cst (mkProgF Δ N main xs.length B) (W₀ + (mkProgF Δ N main xs.length B).len + B + 3 * c + 3) Bi σ' ∧
      σ'.vars "run" = 0 ∧ HExt H H' ∧ Rep B H' w y ∧ H'.length ≤ H.length + c := by
  have hreal := mkProgF_real Δ hN main xs.length B
  have hstub := mkProgF_stub Δ N main xs.length B
  have hPB : (mkProgF Δ N main xs.length B).B = B := rfl
  generalize mkProgF Δ N main xs.length B = P at hreal hstub hPB hC ⊢
  subst hPB
  have h1 : H.length ≤ W₀ := hbd.heapLen
  have h2 : (ws ++ stk₀).length ≤ W₀ := hbd.stkLen
  obtain ⟨n, hn, w, H', hs, hx, hr, hh⟩ := vm_runs_gen Δ hreal hstub hB h hrep
    (W := W₀ + P.len + P.B + 3 * c + 3) (hbd.mono (by omega)) (by omega)
    (by omega) (by omega) (by omega)
  have hhalt : P.code 2 = .halt := by
    have := hstub.2 2 (by simp [stub])
    simpa [stub] using this
  obtain ⟨σ', hrunσ, hA', hC', hrun'⟩ := loop_run hs (by simpa using hhalt) σ hA hC hrun
  exact ⟨w, H', σ', hrunσ.mono (by omega), hA', hC', hrun', hx, hr, hh⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadStore` -/

section
/-!
# WP V3 (2): straight-line stores — the loader of a *fixed* list of constants

`storeSeq a i l` is the command `a[i] := l₀; a[i+1] := l₁; …` (one `store` of two literals per element, a
right-nested `seq`; **never** simplified as a whole: every statement below is proved by induction on the list).
It loads the code arrays `OP`, `OA` and the function table `FT`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- `a[i] := l₀; a[i+1] := l₁; …`. -/
def storeSeq (a : String) : ℕ → List ℕ → Com
  | _, [] => .skip
  | i, v :: vs => .seq (.store a (.lit i) (.lit v)) (storeSeq a (i + 1) vs)

theorem storeSeq_ok {L : Layout} {a : String} (ha : a ∈ L.arrays) (h0 : 0 < L.temps) :
    ∀ (l : List ℕ) (i : ℕ), Com.Ok L (storeSeq a i l) := by
  intro l
  induction l with
  | nil => intro i; exact Com.ok_skip _
  | cons v vs ih =>
    intro i
    exact ⟨⟨ha, trivial, trivial, h0⟩, ih (i + 1)⟩

/-- The function an array becomes after `storeSeq`. -/
def stored (i : ℕ) (l : List ℕ) (f : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if i ≤ k ∧ k < i + l.length then l.getD (k - i) 0 else f k

theorem stored_cons (i v : ℕ) (vs : List ℕ) (f : ℕ → ℕ) :
    stored (i + 1) vs (fun k => if k = i then v else f k) = stored i (v :: vs) f := by
  funext k
  unfold stored
  beta_reduce
  by_cases hk : k = i
  · subst hk
    rw [if_neg (by omega), if_pos rfl, if_pos (by simp)]
    simp
  · by_cases h1 : i + 1 ≤ k
    · by_cases h2 : k < i + 1 + vs.length
      · rw [if_pos ⟨h1, h2⟩, if_pos ⟨by omega, by simp; omega⟩]
        have e : k - i = (k - (i + 1)) + 1 := by omega
        rw [e, List.getD_cons_succ]
      · rw [if_neg (by omega), if_neg hk, if_neg (by simp; omega)]
    · have : k < i := by omega
      rw [if_neg (by omega), if_neg hk, if_neg (by omega)]

/-- **Running `storeSeq`.**  From an array `arrOf n f`, `l.length` cells (from `i`) are overwritten. -/
theorem storeSeq_run {Bi : ℕ} (a : String) :
    ∀ (l : List ℕ) (i : ℕ) (σ : IEnv) (n : ℕ) (f : ℕ → ℕ), σ.arrs a = arrOf n f → i + l.length ≤ n →
      (∀ v ∈ l, v < Bi) → i + l.length < Bi →
      ∃ σ', Run Bi (storeSeq a i l) σ σ' (3 * l.length + 1) ∧ σ'.arrs a = arrOf n (stored i l f) ∧
        σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ b, b ≠ a → σ'.arrs b = σ.arrs b := by
  intro l
  induction l with
  | nil =>
    intro i σ n f h _ _ _
    refine ⟨σ, Run.skip.mono (by simp), ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
    rw [h]; congr 1
    funext k; simp [stored]
  | cons v vs ih =>
    intro i σ n f h hn hv hb
    have hvB : v < Bi := hv v (by simp)
    have hlen : i < (σ.arrs a).length := by rw [h]; simp; simp at hn; omega
    have hr1 : Run Bi (.store a (.lit i) (.lit v)) σ (σ.setArr a i v) 3 :=
      (Run.store (i := .lit i) (e := .lit v) (idx := i) (v := v) (evalB_lit (by simp at hb; omega))
        (evalB_lit hvB) hlen).mono (by simp)
    have h1 : (σ.setArr a i v).arrs a = arrOf n (fun k => if k = i then v else f k) := by
      simp only [arrs_setArr, if_true]; rw [h, set_arrOf]
    obtain ⟨σ', hr, ha', hv', hi', ho', hb'⟩ := ih (i + 1) (σ.setArr a i v) n _ h1
      (by simp at hn; omega) (fun w hw => hv w (List.mem_cons_of_mem _ hw)) (by simp at hb; omega)
    refine ⟨σ', (hr1.seq hr).mono (by simp; omega), ?_, hv', hi', ho', ?_⟩
    · rw [ha', stored_cons]
    · intro b hb2
      rw [hb' b hb2]; simp [arrs_setArr, hb2]

/-- The cells of the array that are loaded read back: if the array was zero, `stored` is the list. -/
theorem storeSeq_run0 {Bi : ℕ} (a : String) (l : List ℕ) (σ : IEnv) (n : ℕ)
    (h : σ.arrs a = List.replicate n 0) (hn : l.length ≤ n) (hv : ∀ v ∈ l, v < Bi) (hb : l.length < Bi) :
    ∃ σ', Run Bi (storeSeq a 0 l) σ σ' (3 * l.length + 1) ∧ σ'.arrs a = arrOf n (fun k => l.getD k 0) ∧
        σ'.vars = σ.vars ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ b, b ≠ a → σ'.arrs b = σ.arrs b := by
  obtain ⟨σ', hr, ha, h1, h2, h3, h4⟩ := storeSeq_run (Bi := Bi) a l 0 σ n (fun _ => 0)
    (by rw [h, replicate_eq_arrOf]) (by omega) hv (by omega)
  refine ⟨σ', hr, ?_, h1, h2, h3, h4⟩
  rw [ha]
  congr 1
  funext k
  unfold stored
  by_cases hk : k < l.length
  · simp [hk]
  · have : l.getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp [hk, this]

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadRead` -/

section
/-!
# WP V3 (3): reading the input word into the heap array `HA`

The tape is the raw word `x` (no length prefix; IMP+ has no end-of-input test).  `rdOne` reads one entry `v`, stores it
at `HA[i]`, keeps the running maximum `M`, and bumps `i`; `rdLoop` repeats it while `i < tot`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- The largest entry of a word (`0` for the empty word). -/
def wordMax (l : List ℕ) : ℕ := l.foldr max 0

theorem wordMax_append_single (l : List ℕ) (a : ℕ) : wordMax (l ++ [a]) = max (wordMax l) a := by
  induction l with
  | nil => simp [wordMax]
  | cons b l ih => simp only [List.cons_append, wordMax, List.foldr_cons] at ih ⊢; rw [ih]; omega

theorem wordMax_take_succ (x : List ℕ) (i : ℕ) (h : i < x.length) :
    wordMax (x.take (i + 1)) = max (wordMax (x.take i)) (x.getD i 0) := by
  have : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  rw [this, wordMax_append_single]
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem wordMax_lt {l : List ℕ} {B : ℕ} (hB : 0 < B) (h : ∀ v ∈ l, v < B) : wordMax l < B := by
  induction l with
  | nil => simpa [wordMax] using hB
  | cons a l ih =>
    have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have := h a (by simp)
    simp only [wordMax, List.foldr_cons] at *
    omega

theorem wordMax_getD_le (x : List ℕ) (j : ℕ) : x.getD j 0 ≤ wordMax x := by
  induction x generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero => simp [wordMax]
    | succ j =>
      have := ih j
      simp only [wordMax, List.foldr_cons, List.getD_cons_succ] at *
      omega

/-- `nrm` at all hypotheses and the goal. -/
macro "nrmAt" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, inp_setVar, out_setVar, vars_setArr,
  arrs_setArr, inp_setArr, out_setArr, ↓reduceIte, String.reduceEq, eq_self, if_true, if_false] at *)

theorem getD_lt {x : List ℕ} {B : ℕ} (hB : 0 < B) (hxB : ∀ v ∈ x, v < B) (j : ℕ) : x.getD j 0 < B :=
  lt_of_le_of_lt (wordMax_getD_le x j) (wordMax_lt hB hxB)

abbrev bump (s : String) : Com := .assign s (pl (V s) (L 1))

/-- read one entry, store it at `HA[i]`, update the maximum, bump `i` -/
def rdOne : Com :=
  .seq (.read "v") (.seq (.store "HA" (V "i") (V "v"))
    (.seq (.ite (.lt (V "M") (V "v")) (.assign "M" (V "v")) .skip) (bump "i")))

def rdLoop : Com := .while (.lt (V "i") (V "tot")) rdOne

/-- The reader's invariant: the first `i` entries of the word have been read into `HA`. -/
structure RCore (x : List ℕ) (A : ℕ) (σ : IEnv) : Prop where
  hi : σ.vars "i" ≤ x.length
  inp : σ.inp = x.drop (σ.vars "i")
  ha : σ.arrs "HA" = arrOf A (fun j => if j < σ.vars "i" then x.getD j 0 else 0)
  hM : σ.vars "M" = wordMax (x.take (σ.vars "i"))

theorem headD_drop_eq (x : List ℕ) (i : ℕ) : (x.drop i).headD 0 = x.getD i 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x.length
  · rw [List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h]; rfl
  · rw [List.drop_of_length_le (by omega), List.getElem?_eq_none (by omega)]; rfl

theorem rdOne_spec {x : List ℕ} {A Bi : ℕ} (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) :
    Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" < x.length) rdOne
      (fun σ σ' => RCore x A σ' ∧ σ'.vars "i" = σ.vars "i" + 1 ∧ σ'.vars "tot" = σ.vars "tot" ∧
        σ'.vars "v" = x.getD (σ.vars "i") 0) 22 := by
  refine Spec.pre (P := fun σ => RCore x A σ ∧ σ.vars "i" < x.length ∧ σ.inp ≠ [] ∧ σ.inp.headD 0 < Bi ∧
    σ.vars "i" < (σ.arrs "HA").length ∧ σ.vars "M" < Bi ∧ σ.vars "i" + 1 < Bi) ?_ ?_
  · unfold rdOne bump
    run_vcg
    all_goals dsimp only at *
    all_goals nrmAt
    all_goals try assumption
    all_goals have hI : RCore x A σ := ‹_›
    all_goals have hlt : σ.vars "i" < x.length := ‹_›
    all_goals have hhd : σ.inp.headD 0 = x.getD (σ.vars "i") 0 := by rw [hI.inp, headD_drop_eq]
    all_goals have hMt := wordMax_take_succ x (σ.vars "i") hlt
    all_goals refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals try nrmAt
    all_goals first
      | omega
      | exact hhd
      | trivial
      | rfl
      | (rw [hI.inp, List.tail_drop]; done)
      | (rw [hI.ha, set_arrOf]; congr 1; funext k; simp only [hhd]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = σ.vars "i" := by omega
                                             subst this; rfl))
      | (rw [hMt, ← hI.hM]; omega)
  · intro σ ⟨hI, hlt⟩
    have hMB : σ.vars "M" < Bi := by
      rw [hI.hM]; exact wordMax_lt (by omega) (fun v hv => hxB v (List.mem_of_mem_take hv))
    have hxi : x.getD (σ.vars "i") 0 < Bi := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact hxB _ (List.getElem_mem _)
    have hhd : σ.inp.headD 0 = x.getD (σ.vars "i") 0 := by rw [hI.inp, headD_drop_eq]
    have hne : σ.inp ≠ [] := by
      rw [hI.inp]; intro h
      have := congrArg List.length h
      simp at this; omega
    have hHA : (σ.arrs "HA").length = A := by rw [hI.ha]; simp
    exact ⟨hI, hlt, hne, by rw [hhd]; exact hxi, by omega, hMB, by omega⟩

/-- The counted reading loop's invariant. -/
def RInv (x : List ℕ) (A N : ℕ) (σ : IEnv) : Prop :=
  RCore x A σ ∧ σ.vars "tot" = N ∧ N ≤ x.length ∧ σ.vars "i" ≤ N

theorem rdLoop_spec {x : List ℕ} {A Bi : ℕ} (N : ℕ) (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi)
    (hL : x.length + 1 < Bi) :
    Spec Bi (fun σ => RInv x A N σ) rdLoop (fun _ σ' => RInv x A N σ' ∧ σ'.vars "i" = N) (26 * N + 4) := by
  refine Spec.forRange "i" "tot" (RInv x A N) N 22 (26 * N + 4) ?_ ?_ ?_ ?_ ?_ (fun _ h => h) ?_
  · intro σ h; have := h.2.2.1; have := h.2.2.2; omega
  · intro σ h; have := h.2.2.1; have := h.2.1; omega
  · intro σ h; exact h.2.1
  · intro σ h; exact h.2.2.2
  · intro σ ⟨h, hlt⟩
    obtain ⟨hc, ht, hN, hi⟩ := h
    obtain ⟨σ', hr, hq⟩ := (rdOne_spec (A := A) hA hxB hL).run (σ := σ) ⟨hc, by omega⟩
    refine ⟨σ', hr, ⟨hq.1, by rw [hq.2.2.1]; exact ht, hN, by rw [hq.2.1]; omega⟩, hq.2.1⟩
  · intro σ h
    have : (22 + 4) * (N - σ.vars "i") ≤ 26 * N := by
      have := Nat.mul_le_mul_left 26 (Nat.sub_le N (σ.vars "i")); omega
    omega

/-! ## The header: `n` is the first entry; the reader then knows how many entries the graph part has -/

/-- Read `n` (entry 0), store it, start the maximum, `i := 1`, `tot := n * n + t0`. -/
def hdrCom (t0 : ℕ) : Com :=
  .seq (.read "v") (.seq (.store "HA" (L 0) (V "v")) (.seq (.assign "M" (V "v"))
    (.seq (.assign "i" (L 1)) (.assign "tot" (pl (ml (V "v") (V "v")) (L t0))))))

theorem hdrCom_spec {x : List ℕ} {A Bi t0 : ℕ} (ht : 1 ≤ t0) (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hN : x.getD 0 0 * x.getD 0 0 + t0 ≤ x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) (hdrCom t0)
      (fun _ σ' => RInv x A (x.getD 0 0 * x.getD 0 0 + t0) σ' ∧ σ'.vars "i" = 1) 20 := by
  have hpos : 0 < x.length := List.length_pos_iff.mpr hx
  have h0B : x.getD 0 0 < Bi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]; exact hxB _ (List.getElem_mem _)
  have hM1 : wordMax (x.take 1) = x.getD 0 0 := by
    have := wordMax_take_succ x 0 hpos
    simp only [Nat.zero_add, List.take_zero] at this
    rw [this]; simp [wordMax]
  refine Spec.pre (P := fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0) ∧ σ.inp ≠ [] ∧
    σ.inp.headD 0 < Bi ∧ σ.inp.headD 0 * σ.inp.headD 0 + t0 < Bi ∧ 0 < (σ.arrs "HA").length) ?_ ?_
  · unfold hdrCom
    run_vcg
    all_goals dsimp only at *
    all_goals nrmAt
    all_goals try (first | assumption | omega)
    all_goals have hinp : σ.inp = x := ‹_›
    all_goals have hha : σ.arrs "HA" = arrOf A (fun _ => 0) := ‹_›
    all_goals have hhd : σ.inp.headD 0 = x.getD 0 0 := by rw [hinp]; cases x <;> simp_all
    all_goals refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
    all_goals try nrmAt
    all_goals first
      | omega
      | trivial
      | rfl
      | (rw [hinp]; cases x <;> simp_all; done)
      | (rw [hha, set_arrOf]; congr 1; funext k; simp only [hhd]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = 0 := by omega
                                             subst this; rfl))
      | (rw [hM1, hhd])
      | (rw [hhd])
  · intro σ ⟨hinp, hha⟩
    have hhd : σ.inp.headD 0 = x.getD 0 0 := by rw [hinp]; cases x <;> simp_all
    refine ⟨hinp, hha, by rw [hinp]; exact hx, by rw [hhd]; exact h0B, by rw [hhd]; omega, by rw [hha]; simp; omega⟩

/-! ## The two input formats -/

/-- `Fmt.graphK`: `n :: n² entries ++ [k]`, of length `n² + 2`. -/
def loadK : Com := .seq (hdrCom 2) rdLoop

/-- `Fmt.graphKLD`: `n :: n² entries ++ [k, l] ++ D`, `D = d :: 3d entries`, of length `n² + 4 + 3d`. -/
def loadKLD : Com :=
  .seq (hdrCom 3) (.seq rdLoop (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)))

/-- The whole word has been read. -/
def Read (x : List ℕ) (A : ℕ) (σ : IEnv) : Prop :=
  RInv x A x.length σ ∧ σ.vars "i" = x.length

theorem loadK_spec {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hlen : x.getD 0 0 * x.getD 0 0 + 2 = x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) loadK
      (fun _ σ' => Read x A σ') (26 * x.length + 24) := by
  have h1 := hdrCom_spec (t0 := 2) (by omega) hx hA hxB hL (by omega)
  rw [hlen] at h1
  have h2 := rdLoop_spec (A := A) (Bi := Bi) x.length hA hxB hL
  refine Spec.mono (Spec.seq h1 h2 ?_ ?_) (by omega)
  · intro σ σ' _ hq; exact hq.1
  · intro σ σ' σ'' _ _ hq; exact hq

theorem loadKLD_spec {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi)
    (hlen : x.getD 0 0 * x.getD 0 0 + 4 + 3 * x.getD (x.getD 0 0 * x.getD 0 0 + 3) 0 = x.length) :
    Spec Bi (fun σ => σ.inp = x ∧ σ.arrs "HA" = arrOf A (fun _ => 0)) loadKLD
      (fun _ σ' => Read x A σ') (52 * x.length + 60) := by
  set n2 := x.getD 0 0 * x.getD 0 0 with hn2
  set d := x.getD (n2 + 3) 0 with hd
  have hlt3 : n2 + 3 < x.length := by omega
  have hdB : d < Bi := getD_lt (by omega) hxB _
  have h1 := hdrCom_spec (t0 := 3) (by omega) hx hA hxB hL (by omega)
  have h2 := rdLoop_spec (A := A) (Bi := Bi) (n2 + 3) hA hxB hL
  have h3 := rdOne_spec (A := A) (Bi := Bi) hA hxB hL
  have h5 := rdLoop_spec (A := A) (Bi := Bi) x.length hA hxB hL
  have h4 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (.assign "tot" (pl (V "i") (ml (L 3) (V "v"))))
      (fun σ σ' => σ' = σ.setVar "tot" (σ.vars "i" + 3 * σ.vars "v")) 6 := by
    have := Spec.assign (B := Bi) (P := fun σ : IEnv => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (x := "tot") (e := pl (V "i") (ml (L 3) (V "v"))) (f := fun σ => σ.vars "i" + 3 * σ.vars "v") (by
        intro σ ⟨_, hi, hv⟩
        have e1 : σ.vars "i" + 3 * σ.vars "v" = x.length := by rw [hi, hv]; omega
        exact RunStep.eval_add Bi σ _ _ _ _ (RunStep.eval_var Bi σ "i" (by omega))
          (RunStep.eval_mul Bi σ _ _ 3 (σ.vars "v") (RunStep.eval_lit Bi 3 σ (by omega))
            (RunStep.eval_var Bi σ "v" (by rw [hv]; exact hdB)) (by omega)) (by omega))
    simpa using this
  have h3' : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 3) rdOne
      (fun σ σ' => RCore x A σ' ∧ σ'.vars "i" = n2 + 4 ∧ σ'.vars "v" = d) 22 :=
    (h3.pre (fun σ h => ⟨h.1, by rw [h.2]; exact hlt3⟩)).post (fun σ σ' h hq => ⟨hq.1, by rw [hq.2.1, h.2], by
      rw [hq.2.2.2, h.2]⟩)
  have h45 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 4 ∧ σ.vars "v" = d)
      (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop) (fun _ σ' => Read x A σ')
      (6 + (26 * x.length + 4)) := by
    refine Spec.seq h4 h5 ?_ (fun _ _ _ _ _ hq => hq)
    intro σ σ' ⟨hc, hi, hv⟩ hq
    subst hq
    have e1 : σ.vars "i" + 3 * σ.vars "v" = x.length := by rw [hi, hv]; omega
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, le_rfl, ?_⟩
    · simpa using hc.hi
    · simpa using hc.inp
    · simpa using hc.ha
    · simpa using hc.hM
    · simpa using e1
    · simpa using hc.hi
  have h345 : Spec Bi (fun σ => RCore x A σ ∧ σ.vars "i" = n2 + 3)
      (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)) (fun _ σ' => Read x A σ')
      (22 + (6 + (26 * x.length + 4))) :=
    Spec.seq h3' h45 (fun σ σ' _ hq => hq) (fun _ _ _ _ _ hq => hq)
  have h2345 : Spec Bi (fun σ => RInv x A (n2 + 3) σ)
      (.seq rdLoop (.seq rdOne (.seq (.assign "tot" (pl (V "i") (ml (L 3) (V "v")))) rdLoop)))
      (fun _ σ' => Read x A σ') ((26 * (n2 + 3) + 4) + (22 + (6 + (26 * x.length + 4)))) :=
    Spec.seq h2 h345 (fun σ σ' _ hq => ⟨hq.1.1, hq.2⟩) (fun _ _ _ _ _ hq => hq)
  refine Spec.mono (Spec.seq h1 h2345 (fun σ σ' _ hq => hq.1) (fun _ _ _ _ _ hq => hq)) (by omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadK` -/

section
/-!
# WP V3 (4): the cost bound `K` and the tag bound `B` as IMP+ expressions

The loader cannot receive `Bv` or `K` from outside: the program is fixed before them.  What it *can* do is compute them
from the input, when they are given by a closed formula.  The interface of `compile_solves` therefore fixes

    `K x = c₀ · 2^(c₁ · kw³) · (|x| + c₂)^c₃`     (`KP.k`),     `B x = (maxEntry x + K x + 2)² + 1`     (`bexp`)

with `kw` the parameter entry of the word (`k` or `l`), and the loader evaluates both by a straight-line command:
`kw³` and the exponent by multiplications, `2^e` by one `shiftl`, the power `(|x|+c₂)^c₃` by `c₃` multiplications.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The four constants of the cost formula. -/
structure KP where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ

/-- The cost bound `c₀ · 2^(c₁ kw³) · (len + c₂)^c₃`. -/
def KP.k (p : KP) (len kw : ℕ) : ℕ := p.c0 * 2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3

/-- The tag bound: strictly above `(M + K + 2)²`, where `M` bounds the input entries. -/
def bexp (M K : ℕ) : ℕ := (M + K + 2) ^ 2 + 1

/-- `e^n` by `n` multiplications. -/
def pwE (e : Expr) : ℕ → Expr
  | 0 => L 1
  | n + 1 => ml e (pwE e n)

/-- The expression of `KP.k`, over the scalars `len` and `kw`. -/
def kE (p : KP) : Expr :=
  ml (ml (L p.c0) (.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw"))))))
    (pwE (pl (V "len") (L p.c2)) p.c3)

/-- The expression of `bexp`, over the scalars `M` and `K`. -/
def bE : Expr :=
  pl (ml (pl (pl (V "M") (V "K")) (L 2)) (pl (pl (V "M") (V "K")) (L 2))) (L 1)

theorem pwE_eval {Bi : ℕ} {σ : IEnv} {e : Expr} {v : ℕ} (he : e.evalB Bi σ = some v) (hv : 1 ≤ v) (h1 : 1 < Bi) :
    ∀ n : ℕ, v ^ n < Bi → (pwE e n).evalB Bi σ = some (v ^ n) := by
  intro n
  induction n with
  | zero => intro _; simpa [pwE] using RunStep.eval_lit Bi 1 σ h1
  | succ n ih =>
    intro h
    have hle : v ^ n ≤ v ^ (n + 1) := Nat.pow_le_pow_right hv (by omega)
    have := RunStep.eval_mul Bi σ e (pwE e n) v (v ^ n) he (ih (by omega)) (by rw [← pow_succ']; exact h)
    rw [← pow_succ'] at this
    exact this

/-- The evaluation of `kE`: every subterm value stays below `K`. -/
theorem kE_eval {Bi : ℕ} {σ : IEnv} (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2)
    {len kw : ℕ} (hlen : σ.vars "len" = len) (hkw : σ.vars "kw" = kw)
    (hc1 : p.c1 < Bi) (hlB : len + p.c2 < Bi) (hkwB : kw < Bi) (hK : p.k len kw < Bi) :
    (kE p).evalB Bi σ = some (p.k len kw) := by
  have hBi : 1 < Bi := by
    unfold KP.k at hK
    have a1 : 1 ≤ 2 ^ (p.c1 * kw ^ 3) := Nat.one_le_two_pow
    have a2 : 1 ≤ (len + p.c2) ^ p.c3 := Nat.one_le_pow p.c3 (len + p.c2) (by omega)
    have a3 := Nat.mul_le_mul h0 (Nat.mul_le_mul a1 a2)
    have a4 : p.c0 * (2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3) = p.c0 * 2 ^ (p.c1 * kw ^ 3) * (len + p.c2) ^ p.c3 := by ring
    omega
  -- the quantities
  set s2 := kw * kw with hs2
  set s3 := kw * s2 with hs3
  set e := p.c1 * s3 with he
  have hs3e : s3 = kw ^ 3 := by rw [hs3, hs2]; ring
  have he' : e = p.c1 * kw ^ 3 := by rw [he, hs3e]
  have hP1 : 1 ≤ (len + p.c2) ^ p.c3 := Nat.one_le_pow _ _ (by omega)
  have h2e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hU : 2 ^ e ≤ p.c0 * 2 ^ e := Nat.le_mul_of_pos_left _ (by omega)
  have hK' : p.k len kw = p.c0 * 2 ^ e * (len + p.c2) ^ p.c3 := by rw [KP.k, he']
  have hKU : p.c0 * 2 ^ e ≤ p.k len kw := by rw [hK']; exact Nat.le_mul_of_pos_right _ (by omega)
  have h1U : 1 ≤ p.c0 * 2 ^ e := by omega
  have hKP : (len + p.c2) ^ p.c3 ≤ p.k len kw := by
    rw [hK']; exact Nat.le_mul_of_pos_left _ (by omega)
  have hes : e < 2 ^ e := Nat.lt_two_pow_self
  have hs3e' : s3 ≤ e := by rw [he]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hs2s3 : s2 ≤ s3 := by
    rcases Nat.eq_zero_or_pos kw with h | h
    · rw [hs2, h]; simp
    · rw [hs3]; exact Nat.le_mul_of_pos_left _ h
  have hbig : e < Bi := by omega
  have hsh : 1 * 2 ^ e < Bi := by rw [one_mul]; omega
  have hmid : p.c0 * (1 * 2 ^ e) < Bi := by rw [one_mul]; omega
  have hfin : p.c0 * (1 * 2 ^ e) * (len + p.c2) ^ p.c3 < Bi := by rw [one_mul, ← hK']; exact hK
  have hc0le : p.c0 ≤ p.c0 * 2 ^ e := Nat.le_mul_of_pos_right _ (by omega)
  have hc0B : p.c0 < Bi := by omega
  have hvkw : (Expr.var "kw").evalB Bi σ = some kw := by rw [← hkw]; exact RunStep.eval_var Bi σ "kw" (by omega)
  have hvlen : (Expr.var "len").evalB Bi σ = some len := by
    rw [← hlen]; exact RunStep.eval_var Bi σ "len" (by omega)
  have e2 : (ml (V "kw") (V "kw")).evalB Bi σ = some s2 :=
    RunStep.eval_mul Bi σ _ _ kw kw hvkw hvkw (by omega)
  have e3 : (ml (V "kw") (ml (V "kw") (V "kw"))).evalB Bi σ = some s3 :=
    RunStep.eval_mul Bi σ _ _ kw s2 hvkw e2 (by omega)
  have ee : (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw")))).evalB Bi σ = some e :=
    RunStep.eval_mul Bi σ _ _ p.c1 s3 (RunStep.eval_lit Bi _ σ hc1) e3 (by omega)
  have esh : (Expr.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw"))))).evalB Bi σ
      = some (1 * 2 ^ e) :=
    RunStep.eval_shiftl Bi σ _ _ 1 e (RunStep.eval_lit Bi 1 σ hBi) ee hsh
  have eu : (ml (L p.c0) (.bin .shiftl (L 1) (ml (L p.c1) (ml (V "kw") (ml (V "kw") (V "kw")))))).evalB Bi σ
      = some (p.c0 * (1 * 2 ^ e)) :=
    RunStep.eval_mul Bi σ _ _ p.c0 (1 * 2 ^ e) (RunStep.eval_lit Bi _ σ hc0B) esh hmid
  have ebase : (pl (V "len") (L p.c2)).evalB Bi σ = some (len + p.c2) :=
    RunStep.eval_add Bi σ _ _ len p.c2 hvlen (RunStep.eval_lit Bi _ σ (by omega)) hlB
  have ep := pwE_eval ebase (by omega) hBi p.c3 (by omega)
  have := RunStep.eval_mul Bi σ _ _ _ _ eu ep hfin
  have h' : p.k len kw = p.c0 * (1 * 2 ^ e) * (len + p.c2) ^ p.c3 := by rw [one_mul]; exact hK'
  unfold kE
  rw [h']
  exact this

end Lax117284Proofs.Treewidth.Fun.VM.Ram

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

/-- `len := i`; `kw := HA[HA[0]² + off]`; `K := kE`; `B := bE`. -/
def setKB (off : ℕ) (p : KP) : Com :=
  .seq (.assign "len" (V "i"))
    (.seq (.assign "kw" (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off))))
      (.seq (.assign "K" (kE p)) (.assign "B" bE)))

/-- The scalars set by `setKB`, as one environment. -/
def afterKB (x : List ℕ) (off : ℕ) (p : KP) (σ : IEnv) : IEnv :=
  (((σ.setVar "len" x.length).setVar "kw" (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)).setVar "K"
    (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0))).setVar "B"
    (bexp (wordMax x) (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)))

theorem bE_size : bE.size = 13 := by simp [bE]

theorem setKB_run {x : List ℕ} {A Bi off : ℕ} (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2)
    (hA : x.length ≤ A) (hxB : ∀ v ∈ x, v < Bi) (hidx : x.getD 0 0 * x.getD 0 0 + off < x.length)
    (hc1 : p.c1 < Bi) (hlB : x.length + p.c2 < Bi)
    (hK : p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0) < Bi)
    (hB : bexp (wordMax x) (p.k x.length (x.getD (x.getD 0 0 * x.getD 0 0 + off) 0)) < Bi)
    {σ : IEnv} (hi : σ.vars "i" = x.length) (hha : σ.arrs "HA" = arrOf A (fun j => x.getD j 0))
    (hM : σ.vars "M" = wordMax x) :
    Run Bi (setKB off p) σ (afterKB x off p σ) ((kE p).size + 40) := by
  set n := x.getD 0 0 with hn
  set kwv := x.getD (n * n + off) 0 with hkwv
  set Kv := p.k x.length kwv with hKv
  have hBi : 0 < Bi := by omega
  have hlenA : (σ.arrs "HA").length = A := by rw [hha]; simp
  have hnB : n < Bi := getD_lt hBi hxB 0
  have hkwB : kwv < Bi := getD_lt hBi hxB _
  -- step 1
  have r1 : Run Bi (.assign "len" (V "i")) σ (σ.setVar "len" x.length) 2 := by
    have := Run.assign (B := Bi) (x := "len") (e := V "i") (v := x.length)
      (by rw [← hi]; exact RunStep.eval_var Bi σ "i" (by omega))
    simpa using this.mono (by simp)
  set σ1 := σ.setVar "len" x.length with hσ1
  -- step 2
  have hσ1i : σ1.vars "i" = x.length := by simp [hσ1, hi]
  have hσ1a : σ1.arrs "HA" = arrOf A (fun j => x.getD j 0) := by simp [hσ1, hha]
  have hg0 : (G "HA" (L 0)).evalB Bi σ1 = some n := by
    have := RunStep.eval_get Bi σ1 "HA" (L 0) 0 (RunStep.eval_lit Bi 0 σ1 (by omega))
      (by rw [hσ1a]; simp; omega) (by rw [hσ1a, getD_arrOf _ (by omega)]; exact hnB)
    rw [hσ1a, getD_arrOf _ (by omega)] at this
    exact this
  have hsq : (ml (G "HA" (L 0)) (G "HA" (L 0))).evalB Bi σ1 = some (n * n) :=
    RunStep.eval_mul Bi σ1 _ _ n n hg0 hg0 (by omega)
  have hpl : (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off)).evalB Bi σ1 = some (n * n + off) :=
    RunStep.eval_add Bi σ1 _ _ (n * n) off hsq (RunStep.eval_lit Bi off σ1 (by omega)) (by omega)
  have hgk : (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off))).evalB Bi σ1 = some kwv := by
    have := RunStep.eval_get Bi σ1 "HA" _ (n * n + off) hpl
      (by rw [hσ1a]; simp; omega) (by rw [hσ1a, getD_arrOf _ (by omega)]; exact hkwB)
    rw [hσ1a, getD_arrOf _ (by omega)] at this
    exact this
  have r2 : Run Bi (.assign "kw" (G "HA" (pl (ml (G "HA" (L 0)) (G "HA" (L 0))) (L off)))) σ1
      (σ1.setVar "kw" kwv) 9 := by
    have := Run.assign (B := Bi) (x := "kw") hgk
    exact this.mono (by simp)
  set σ2 := σ1.setVar "kw" kwv with hσ2
  -- step 3
  have hσ2l : σ2.vars "len" = x.length := by simp [hσ2, hσ1]
  have hσ2k : σ2.vars "kw" = kwv := by simp [hσ2]
  have r3 : Run Bi (.assign "K" (kE p)) σ2 (σ2.setVar "K" Kv) ((kE p).size + 1) := by
    have := Run.assign (B := Bi) (x := "K") (kE_eval (σ := σ2) p h0 h1 h2 hσ2l hσ2k hc1 hlB hkwB hK)
    exact this.mono (by omega)
  set σ3 := σ2.setVar "K" Kv with hσ3
  -- step 4
  have hσ3M : σ3.vars "M" = wordMax x := by simp [hσ3, hσ2, hσ1, hM]
  have hσ3K : σ3.vars "K" = Kv := by simp [hσ3]
  have hMB : wordMax x < Bi := wordMax_lt hBi hxB
  have hKb : Kv < bexp (wordMax x) Kv := by
    unfold bexp; nlinarith [Nat.zero_le (wordMax x)]
  have hMK : wordMax x + Kv + 2 ≤ (wordMax x + Kv + 2) ^ 2 := by nlinarith [Nat.zero_le (wordMax x + Kv)]
  have hb1 : (pl (V "M") (V "K")).evalB Bi σ3 = some (wordMax x + Kv) :=
    RunStep.eval_add Bi σ3 _ _ _ _ (by rw [← hσ3M]; exact RunStep.eval_var Bi σ3 "M" (by omega))
      (by rw [← hσ3K]; exact RunStep.eval_var Bi σ3 "K" (by omega)) (by unfold bexp at hB; omega)
  have hb2 : (pl (pl (V "M") (V "K")) (L 2)).evalB Bi σ3 = some (wordMax x + Kv + 2) :=
    RunStep.eval_add Bi σ3 _ _ _ 2 hb1 (RunStep.eval_lit Bi 2 σ3 (by unfold bexp at hB; omega))
      (by unfold bexp at hB; omega)
  have hb3 : (ml (pl (pl (V "M") (V "K")) (L 2)) (pl (pl (V "M") (V "K")) (L 2))).evalB Bi σ3
      = some ((wordMax x + Kv + 2) * (wordMax x + Kv + 2)) :=
    RunStep.eval_mul Bi σ3 _ _ _ _ hb2 hb2 (by unfold bexp at hB; rw [← pow_two]; omega)
  have hb4 : bE.evalB Bi σ3 = some (bexp (wordMax x) Kv) := by
    have := RunStep.eval_add Bi σ3 _ _ _ 1 hb3 (RunStep.eval_lit Bi 1 σ3 (by unfold bexp at hB; omega)) (by
      unfold bexp at hB; rw [← pow_two]; omega)
    unfold bE bexp
    rw [← pow_two] at this
    exact this
  have r4 : Run Bi (.assign "B" bE) σ3 (σ3.setVar "B" (bexp (wordMax x) Kv)) 14 := by
    have := Run.assign (B := Bi) (x := "B") hb4
    exact this.mono (by rw [bE_size])
  unfold setKB afterKB
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by omega)

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadSetup` -/

section
/-!
# WP V3 (5): the second heap array `HB` and the initial scalars

After reading, `HA[j] = x_j`.  The heap of the input list `x₀ :: x₁ :: … :: xₙ₋₁ :: nil` is laid out *forwards*: cell `j` is
`(x_j, B + j + 1)` for `j + 1 < n` and `(x_{n-1}, 0)` for the last one, root `B` (cell `0`).  `hbLoop` fills `HB[j] := B + j + 1`
for `j < n - 1` (the last cell keeps `HB = 0`, the empty list), and `setupCom` sets `sp hp run` and `STK[0] := B`.
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning ToVal

def hbBody : Com := .seq (.store "HB" (V "i") (pl (pl (V "B") (V "i")) (L 1))) (bump "i")

/-- `i := 0; while i < tot do HB[i] := B + i + 1; i++`. -/
def hbLoop : Com := .seq (.assign "i" (L 0)) (.while (.lt (V "i") (V "tot")) hbBody)

def hbCom : Com := .seq (.assign "tot" (mi (V "len") (L 1))) hbLoop

/-- The invariant of the `HB` fill. -/
def HbInv (A Bv N : ℕ) (σ : IEnv) : Prop :=
  σ.vars "tot" = N ∧ σ.vars "i" ≤ N ∧ σ.vars "B" = Bv ∧
    σ.arrs "HB" = arrOf A (fun j => if j < σ.vars "i" then Bv + j + 1 else 0)

theorem hbBody_spec {A Bv N Bi : ℕ} (hNA : N ≤ A) (hb : Bv + N + 1 < Bi) :
    Spec Bi (fun σ => HbInv A Bv N σ ∧ σ.vars "i" < N) hbBody
      (fun σ σ' => HbInv A Bv N σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 12 := by
  refine Spec.pre (P := fun σ => HbInv A Bv N σ ∧ σ.vars "i" < N ∧ σ.vars "i" < (σ.arrs "HB").length ∧
    Bv + σ.vars "i" + 1 < Bi ∧ σ.vars "i" + 1 < Bi) ?_ ?_
  · unfold hbBody bump
    run_vcg
    all_goals try dsimp only at *
    all_goals try nrmAt
    all_goals have hI : HbInv A Bv N σ := ‹_›
    all_goals have hBv : σ.vars "B" = Bv := hI.2.2.1
    all_goals have hlt : σ.vars "i" < N := ‹_›
    all_goals try (first | assumption | omega)
    all_goals refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try nrmAt
    all_goals first
      | exact hI.1
      | omega
      | trivial
      | (rw [hI.2.2.2, set_arrOf]; congr 1; funext k
         rw [hBv]
         split_ifs with h1 h2 <;>
           first | rfl | (exfalso; omega) | (have : k = σ.vars "i" := by omega
                                             subst this; rfl))
  · intro σ ⟨hI, hlt⟩
    obtain ⟨_, _, hBv, hHB⟩ := hI
    have hl : (σ.arrs "HB").length = A := by rw [hHB]; simp
    exact ⟨⟨‹_›, ‹_›, hBv, hHB⟩, hlt, by omega, by omega, by omega⟩

theorem hbLoop_spec {A Bv N Bi : ℕ} (hNA : N ≤ A) (hb : Bv + N + 1 < Bi) (hNB : N < Bi) :
    Spec Bi (fun σ => HbInv A Bv N (σ.setVar "i" 0)) hbLoop
      (fun _ σ' => HbInv A Bv N σ' ∧ σ'.vars "i" = N) ((12 + 4) * N + 6) :=
  Spec.forRangeZero "i" "tot" (HbInv A Bv N) N 12 hNB (fun _ h => h.2.1) (fun _ h => h.1)
    (hbBody_spec hNA hb)

/-- The whole `HB` phase: from `len = |x|`, `B = Bv` and `HB` all zero. -/
theorem hbCom_spec {A Bv n Bi : ℕ} (hnA : n ≤ A) (hn : 1 ≤ n) (hb : Bv + n + 1 < Bi) (hnB : n < Bi) :
    Spec Bi (fun σ => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧ σ.arrs "HB" = arrOf A (fun _ => 0)) hbCom
      (fun _ σ' => HbInv A Bv (n - 1) σ' ∧ σ'.vars "i" = n - 1 ∧ σ'.vars "len" = n) (12 + (16 * n + 6)) := by
  have h1 : Spec Bi (fun σ : IEnv => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧ σ.arrs "HB" = arrOf A (fun _ => 0))
      (.assign "tot" (mi (V "len") (L 1))) (fun σ σ' => σ' = σ.setVar "tot" (σ.vars "len" - 1)) 4 := by
    have := Spec.assign (B := Bi) (P := fun σ : IEnv => σ.vars "len" = n ∧ σ.vars "B" = Bv ∧
        σ.arrs "HB" = arrOf A (fun _ => 0)) (x := "tot") (e := mi (V "len") (L 1))
      (f := fun σ => σ.vars "len" - 1) (by
        intro σ ⟨hl, _, _⟩
        exact RunStep.eval_sub Bi σ _ _ _ 1 (RunStep.eval_var Bi σ "len" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
    exact this.mono (by simp)
  have h2 := (hbLoop_spec (A := A) (Bv := Bv) (N := n - 1) (Bi := Bi) (by omega) (by omega) (by omega)).frame
  refine Spec.mono (Spec.seq h1 h2 ?_ ?_) (by omega)
  · intro σ σ' ⟨hl, hB, hHB⟩ hq
    subst hq
    refine ⟨by simp; omega, by simp, by simpa using hB, ?_⟩
    simpa using hHB
  · intro σ σ' σ'' ⟨hl, _, _⟩ hq hq'
    subst hq
    refine ⟨hq'.1.1, hq'.1.2, ?_⟩
    rw [hq'.2.1 "len" (by decide)]
    simpa using hl

/-! ## The initial scalars -/

/-- `sp := 1; hp := len; run := 1; STK[0] := B`. -/
def setupCom : Com :=
  .seq (.assign "sp" (L 1)) (.seq (.assign "hp" (V "len"))
    (.seq (.assign "run" (L 1)) (.store "STK" (L 0) (V "B"))))

def afterSetup (n Bv : ℕ) (σ : IEnv) : IEnv :=
  (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1).setArr "STK" 0 Bv

theorem setup_run {Bi n Bv : ℕ} (h1 : 1 < Bi) {σ : IEnv} (hlen : σ.vars "len" = n) (hB : σ.vars "B" = Bv) (hn : n < Bi)
    (hBv : Bv < Bi) (hSTK : 0 < (σ.arrs "STK").length) :
    Run Bi setupCom σ (afterSetup n Bv σ) 12 := by
  have r1 : Run Bi (.assign "sp" (L 1)) σ (σ.setVar "sp" 1) 2 :=
    (Run.assign (B := Bi) (x := "sp") (RunStep.eval_lit Bi 1 σ h1)).mono (by simp)
  have r2 : Run Bi (.assign "hp" (V "len")) (σ.setVar "sp" 1) ((σ.setVar "sp" 1).setVar "hp" n) 2 := by
    have := Run.assign (B := Bi) (x := "hp") (e := V "len") (σ := σ.setVar "sp" 1) (v := n)
      (by have := RunStep.eval_var Bi (σ.setVar "sp" 1) "len" (by simp; omega); simpa [hlen] using this)
    exact this.mono (by simp)
  have r3 : Run Bi (.assign "run" (L 1)) ((σ.setVar "sp" 1).setVar "hp" n)
      (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) 2 :=
    (Run.assign (B := Bi) (x := "run") (RunStep.eval_lit Bi 1 _ h1)).mono (by simp)
  have r4 : Run Bi (.store "STK" (L 0) (V "B")) (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1)
      ((((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1).setArr "STK" 0 Bv) 3 := by
    have := Run.store (B := Bi) (a := "STK") (i := L 0) (e := V "B") (idx := 0) (v := Bv)
      (σ := ((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) (RunStep.eval_lit Bi 0 _ (by omega))
      (by have := RunStep.eval_var Bi (((σ.setVar "sp" 1).setVar "hp" n).setVar "run" 1) "B" (by simp; omega)
          simpa [hB] using this) (by simpa using hSTK)
    exact this.mono (by simp)
  unfold setupCom afterSetup
  exact (r1.seq (r2.seq (r3.seq r4))).mono (by omega)

/-! ## The heap of the input list -/

/-- The tail pointer of cell `j` of the forward layout of a list of length `n`. -/
def hbF (Bv n j : ℕ) : ℕ := if j + 1 < n then Bv + j + 1 else 0

/-- The heap of the input word: cell `j = (x_j, hbF)`. -/
def heapOf (x : List ℕ) (Bv : ℕ) : List (ℕ × ℕ) :=
  (List.range x.length).map (fun j => (x.getD j 0, hbF Bv x.length j))

theorem heapOf_length (x : List ℕ) (Bv : ℕ) : (heapOf x Bv).length = x.length := by simp [heapOf]

theorem heapOf_get {x : List ℕ} {Bv j : ℕ} (hj : j < x.length) :
    (heapOf x Bv)[j]? = some (x.getD j 0, hbF Bv x.length j) := by
  simp [heapOf, hj]

/-- Every suffix of the input list is represented in the forward layout. -/
theorem rep_suffix {x : List ℕ} {Bv : ℕ} (hB : 0 < Bv) (hxB : ∀ v ∈ x, v < Bv) :
    ∀ m j, x.length - j = m → j ≤ x.length →
      Rep Bv (heapOf x Bv) (if j < x.length then Bv + j else 0) (listVal (x.drop j)) := by
  intro m
  induction m with
  | zero =>
    intro j hm hj
    have : x.length ≤ j := by omega
    rw [if_neg (by omega), List.drop_of_length_le this]
    exact Rep.nat hB
  | succ m ih =>
    intro j hm hj
    have hlt : j < x.length := by omega
    rw [if_pos hlt, List.drop_eq_getElem_cons hlt]
    have hxj : x[j] = x.getD j 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
    have hxjB : x[j] < Bv := hxB _ (List.getElem_mem _)
    have := ih (j + 1) (by omega) (by omega)
    have hcell := heapOf_get (x := x) (Bv := Bv) hlt
    show Rep Bv (heapOf x Bv) (Bv + j) (Val.cons (Val.nat x[j]) (listVal (x.drop (j + 1))))
    refine Rep.cons hcell (a := x.getD j 0) (b := hbF Bv x.length j) ?_ ?_
    · rw [← hxj]; exact Rep.nat hxjB
    · unfold hbF
      by_cases h : j + 1 < x.length
      · rw [if_pos h]
        have e : Bv + j + 1 = Bv + (j + 1) := by ring
        rw [e]
        simpa [if_pos h] using this
      · rw [if_neg h]
        simpa [if_neg h] using this

theorem rep_input {x : List ℕ} {Bv : ℕ} (hB : 0 < Bv) (hxB : ∀ v ∈ x, v < Bv) (hx : x ≠ []) :
    Rep Bv (heapOf x Bv) Bv (toVal x) := by
  have hpos : 0 < x.length := List.length_pos_iff.mpr hx
  have := rep_suffix (x := x) hB hxB x.length 0 (by omega) (by omega)
  rw [if_pos hpos, List.drop_zero, Nat.add_zero] at this
  rw [toVal_list]
  exact this

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMLoadInit` -/

section
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

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolveWrite` -/

section
/-!
# WP V3 (7): the writer — emit the output list from the final heap

After the VM has halted, `STK[0]` holds a word `w` with `Rep B H' w (listVal out)`.  The writer walks the list:
`while B - 1 < w do write HA[w - B]; w := HB[w - B]` (`B - 1 < w` is `w ≥ B`, i.e. `w` is a pointer, since `1 ≤ B`).
Its cost is linear in `|out|`; the caller must charge `|out|` (a value's tree size is not bounded by the derivation cost).
-/

namespace Lax117284Proofs.Treewidth.Fun.VM.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning ToVal

def wrBody : Com :=
  .seq (.write (G "HA" (mi (V "w") (V "B")))) (.assign "w" (G "HB" (mi (V "w") (V "B"))))

def wrLoop : Com := .while (.lt (mi (V "B") (L 1)) (V "w")) wrBody

/-- `w := STK[0]` then the loop. -/
def wrCom : Com := .seq (.assign "w" (G "STK" (L 0))) wrLoop

theorem wrLoop_run {Bi B : ℕ} {H : List (ℕ × ℕ)} (hB : 1 ≤ B) (hBi : B + H.length + 1 < Bi) :
    ∀ (l : List ℕ) (w : ℕ) (σ : IEnv), Rep B H w (listVal l) → σ.vars "w" = w → σ.vars "B" = B →
      Pfx (H.map Prod.fst) (σ.arrs "HA") → Pfx (H.map Prod.snd) (σ.arrs "HB") →
      ∃ σ', Run Bi wrLoop σ σ' (16 * l.length + 6) ∧ σ'.out = σ.out ++ l := by
  intro l
  induction l with
  | nil =>
    intro w σ hr hw hb _ _
    have hw0 : w = 0 := (Rep.nat_inv (by simpa [listVal] using hr)).1
    have hcond : (Cond.lt (mi (V "B") (L 1)) (V "w")).evalB Bi σ = some false := by
      have := RunStep.cond_lt_false Bi σ (mi (V "B") (L 1)) (V "w") (B - 1) w
        (RunStep.eval_sub Bi σ _ _ B 1 (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega)) (by omega)
      exact this
    exact ⟨σ, (Run.while_false hcond).mono (by simp), by simp⟩
  | cons a l ih =>
    intro w σ hr hw hb hHA hHB
    have hr' : Rep B H w (Val.cons (Val.nat a) (listVal l)) := by simpa [listVal] using hr
    obtain ⟨p, a', b, hwp, hp, hra, hrb⟩ := hr'.cons_inv
    have ha' : a' = a := (Rep.nat_inv hra).1
    have hpl : p < H.length := (List.getElem?_eq_some_iff.mp hp).1
    have haB : a < B := (Rep.nat_inv hra).2
    rw [ha'] at hp hra
    have hcond : (Cond.lt (mi (V "B") (L 1)) (V "w")).evalB Bi σ = some true := by
      have := RunStep.cond_lt_true Bi σ (mi (V "B") (L 1)) (V "w") (B - 1) w
        (RunStep.eval_sub Bi σ _ _ B 1 (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega))
          (RunStep.eval_lit Bi 1 σ (by omega)) (by omega))
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega)) (by omega)
      exact this
    have hidx : (mi (V "w") (V "B")).evalB Bi σ = some p := by
      have := RunStep.eval_sub Bi σ (V "w") (V "B") w B
        (by rw [← hw]; exact RunStep.eval_var Bi σ "w" (by omega))
        (by rw [← hb]; exact RunStep.eval_var Bi σ "B" (by omega)) (by omega)
      rw [show w - B = p by omega] at this
      exact this
    have hHAp : (σ.arrs "HA")[p]? = some a := hHA.get (j := p) (x := a) (by simp [hp])
    have hHBp : (σ.arrs "HB")[p]? = some b := hHB.get (j := p) (x := b) (by simp [hp])
    have hpA : p < (σ.arrs "HA").length := (List.getElem?_eq_some_iff.mp hHAp).1
    have hpB : p < (σ.arrs "HB").length := (List.getElem?_eq_some_iff.mp hHBp).1
    have hgA : (σ.arrs "HA").getD p 0 = a := by
      rw [List.getD_eq_getElem?_getD, hHAp]; rfl
    have hgB : (σ.arrs "HB").getD p 0 = b := by
      rw [List.getD_eq_getElem?_getD, hHBp]; rfl
    have hbl : b < B + H.length := Rep.lt hrb
    -- the body
    have r1 : Run Bi (.write (G "HA" (mi (V "w") (V "B")))) σ { σ with out := σ.out ++ [a] } 5 := by
      have := Run.write (B := Bi) (σ := σ) (e := G "HA" (mi (V "w") (V "B"))) (v := a)
        (by have := RunStep.eval_get Bi σ "HA" (mi (V "w") (V "B")) p hidx hpA (by rw [hgA]; omega)
            rwa [hgA] at this)
      exact this.mono (by simp)
    set σ1 : IEnv := { σ with out := σ.out ++ [a] } with hσ1
    have hidx1 : (mi (V "w") (V "B")).evalB Bi σ1 = some p := hidx
    have r2 : Run Bi (.assign "w" (G "HB" (mi (V "w") (V "B")))) σ1 (σ1.setVar "w" b) 5 := by
      have := Run.assign (B := Bi) (σ := σ1) (x := "w") (e := G "HB" (mi (V "w") (V "B"))) (v := b)
        (by have := RunStep.eval_get Bi σ1 "HB" (mi (V "w") (V "B")) p hidx1 hpB (by rw [hgB]; omega)
            rwa [hgB] at this)
      exact this.mono (by simp)
    obtain ⟨σ', hr', hout'⟩ := ih b (σ1.setVar "w" b) hrb (by simp) (by simpa [hσ1] using hb)
      (by simpa [hσ1] using hHA) (by simpa [hσ1] using hHB)
    refine ⟨σ', ?_, ?_⟩
    · have := run_while_step hcond (r1.seq r2) hr'
      exact this.mono (by simp; omega)
    · simp [hσ1] at hout'
      simp [hout']

theorem wrCom_run {Bi B w : ℕ} {H : List (ℕ × ℕ)} {l : List ℕ} {σ : IEnv} (hB : 1 ≤ B)
    (hBi : B + H.length + 1 < Bi) (hr : Rep B H w (listVal l)) (hstk : (σ.arrs "STK")[0]? = some w)
    (hb : σ.vars "B" = B) (hHA : Pfx (H.map Prod.fst) (σ.arrs "HA"))
    (hHB : Pfx (H.map Prod.snd) (σ.arrs "HB")) :
    ∃ σ', Run Bi wrCom σ σ' (16 * l.length + 12) ∧ σ'.out = σ.out ++ l := by
  have hwl : w < B + H.length := Rep.lt hr
  have hlen : 0 < (σ.arrs "STK").length := (List.getElem?_eq_some_iff.mp hstk).1
  have hg : (σ.arrs "STK").getD 0 0 = w := by rw [List.getD_eq_getElem?_getD, hstk]; rfl
  have r1 : Run Bi (.assign "w" (G "STK" (L 0))) σ (σ.setVar "w" w) 3 := by
    have := Run.assign (B := Bi) (σ := σ) (x := "w") (e := G "STK" (L 0)) (v := w)
      (by have := RunStep.eval_get Bi σ "STK" (L 0) 0 (RunStep.eval_lit Bi 0 σ (by omega)) hlen
            (by rw [hg]; omega)
          rwa [hg] at this)
    exact this.mono (by simp)
  obtain ⟨σ', hr', ho⟩ := wrLoop_run hB hBi l w (σ.setVar "w" w) hr (by simp) (by simpa using hb)
    (by simpa using hHA) (by simpa using hHB)
  exact ⟨σ', (r1.seq hr').mono (by omega), by simpa using ho⟩

end Lax117284Proofs.Treewidth.Fun.VM.Ram

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolveDefs` -/

section
/-!
# WP V3 (8): the whole program `solveCom`, its layout, and the numeric quantities

`solveCom Δ N main fmt p` is the single IMP+ command of `compile_solves`:

    read the word into the heap array · compute `K`, `B` · fill `HB` · initial scalars · load `OP`, `OA`, `FT`
    · `vmLoop` · write the output list.

Numeric quantities (all functions of the input `x` and of the fixed data `Δ N main fmt p`):

* `Kx p fmt x = c₀ · 2^(c₁ kw³) · (|x| + c₂)^c₃` — the cost bound of the functional run (`kw = fmt.kw x`, the entry `k`/`l`);
* `Bx p fmt x = (maxEntry x + Kx + 2)² + 1` — the tag bound of the VM;
* `kappa Δ N main p` — the constant, `1000 ·` (program length + table size + largest operand + largest table entry
  + `c₀ + c₁ + c₂` + size of `kE` + 1);
* the IMP+ value bound `Bimp = 2 Bx + 4 (Kx + |x| + 8) + kappa`, the word bound `Wx`, the array length `Wx + 1`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram

set_option genSizeOfSpec false in
/-- The input formats: `g ++ [k]` and `g ++ [k, l] ++ D` (`g = n :: n²` adjacency entries, `D = d :: 3d` entries). -/
inductive Fmt where
  | graphK
  | graphKLD
  deriving DecidableEq

def nOfWord (x : List ℕ) : ℕ := x.getD 0 0

/-- The length of the word in the format, read off the header. -/
def fmtLen : Fmt → List ℕ → ℕ
  | .graphK, x => nOfWord x * nOfWord x + 2
  | .graphKLD, x => 1 + nOfWord x * nOfWord x + 2 + 1 + 3 * x.getD (1 + nOfWord x * nOfWord x + 2) 0

/-- Position of the parameter entry: `k` (last entry) for `graphK`, `l` for `graphKLD`, relative to `n²`. -/
def Fmt.off : Fmt → ℕ
  | .graphK => 1
  | .graphKLD => 2

/-- The parameter entry of the word (`k`, resp. `l`). -/
def Fmt.kw (fmt : Fmt) (x : List ℕ) : ℕ := x.getD (x.getD 0 0 * x.getD 0 0 + fmt.off) 0

def Fmt.loadCom : Fmt → Com
  | .graphK => loadK
  | .graphKLD => loadKLD

/-- The largest entry of a word. -/
def maxEntry (x : List ℕ) : ℕ := x.foldr max 0

/-- The cost bound. -/
def Kx (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ := p.k x.length (fmt.kw x)

/-- The tag bound of the VM. -/
def Bx (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ := bexp (maxEntry x) (Kx p fmt x)

/-! ## The constants of the program -/

def progLen (Δ : ℕ → Option Tm) (N main : ℕ) : ℕ := (codeL Δ N main).length

def kS (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ :=
  progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 + (kE p).size + 1

def kappa (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ := 1000 * kS Δ N main p

/-- The IMP+ value bound. -/
def Bimp (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  2 * Bx p fmt x + 4 * (Kx p fmt x + x.length + 8) + kappa Δ N main p

/-- The IMP+ cost bound. -/
def Cimp (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  kappa Δ N main p * (Kx p fmt x + x.length + 1)

/-- The word bound of the VM run: `W₀ + len + B + 3K + 3` with `W₀ = B + |x| + 1`. -/
def Wx (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) : ℕ :=
  (Bx p fmt x + x.length + 1) + progLen Δ N main + Bx p fmt x + 3 * Kx p fmt x + 3

/-! ## The program -/

def solveCom (Δ : ℕ → Option Tm) (N main : ℕ) (fmt : Fmt) (p : KP) : Com :=
  .seq fmt.loadCom (.seq (setKB fmt.off p) (.seq hbCom (.seq setupCom
    (.seq (storeSeq "OP" 0 (opsL Δ N main)) (.seq (storeSeq "OA" 0 (opasL Δ N main))
      (.seq (storeSeq "FT" 0 (ftL Δ N)) (.seq vmLoop wrCom)))))))

/-- The layout: the interpreter's plus the loader's scalars. -/
def solveLayout : Layout where
  scalars := ["pc", "sp", "rp", "hp", "B", "run", "op", "oa", "t1", "t2", "i", "tot", "v", "M", "len", "kw", "K", "w"]
  arrays := arrNames
  temps := 8

/-! ## Compilability -/

macro "okS" : tactic => `(tactic| simp [Com.Ok, Cond.Ok, Expr.Ok, condExpr, solveLayout, arrNames, V, L, G, pl, ml, mi,
  bump])

theorem ok_hdrCom (t0 : ℕ) : Com.Ok solveLayout (hdrCom t0) := by unfold hdrCom; okS
theorem ok_rdOne : Com.Ok solveLayout rdOne := by unfold rdOne; okS
theorem ok_rdLoop : Com.Ok solveLayout rdLoop := by unfold rdLoop; simp only [Com.Ok]; refine ⟨?_, ok_rdOne⟩; okS
theorem ok_loadK : Com.Ok solveLayout loadK := ⟨ok_hdrCom 2, ok_rdLoop⟩
theorem ok_loadKLD : Com.Ok solveLayout loadKLD := by
  unfold loadKLD
  refine ⟨ok_hdrCom 3, ok_rdLoop, ok_rdOne, ?_, ok_rdLoop⟩
  okS

theorem ok_loadCom (fmt : Fmt) : Com.Ok solveLayout fmt.loadCom := by
  cases fmt
  · exact ok_loadK
  · exact ok_loadKLD

theorem pwE_ok {Ly : Layout} {e : Expr} {d : ℕ} (h1 : Expr.Ok Ly e (d + 1))
    (hd : d < Ly.temps) : ∀ n, Expr.Ok Ly (pwE e n) d := by
  intro n
  induction n with
  | zero => exact Expr.ok_lit _ _ _
  | succ n ih => exact ⟨ih, h1, hd⟩

theorem ok_kE (p : KP) : Expr.Ok solveLayout (kE p) 0 := by
  unfold kE
  refine ⟨?_, ?_, by simp [solveLayout]⟩
  · refine pwE_ok ?_ (by simp [solveLayout]) _
    simp [Expr.Ok, solveLayout, pl, V, L]
  · simp [Expr.Ok, solveLayout, ml, V, L]

theorem ok_setKB (off : ℕ) (p : KP) : Com.Ok solveLayout (setKB off p) := by
  unfold setKB
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Com.Ok, Expr.Ok, solveLayout, V]
  · simp [Com.Ok, Expr.Ok, solveLayout, V, L, G, pl, ml, arrNames]
  · exact ⟨by simp [solveLayout], ok_kE p⟩
  · refine ⟨by simp [solveLayout], ?_⟩
    simp [bE, Expr.Ok, solveLayout, V, L, pl, ml]

theorem ok_hbCom : Com.Ok solveLayout hbCom := by
  unfold hbCom hbLoop hbBody; okS

theorem ok_setupCom : Com.Ok solveLayout setupCom := by unfold setupCom; okS

theorem ok_wrCom : Com.Ok solveLayout wrCom := by unfold wrCom wrLoop wrBody; okS

theorem ok_vmLoop' : Com.Ok solveLayout vmLoop :=
  com_ok_mono (L := Lvm) (L' := solveLayout) (by intro x hx; simp [Lvm] at hx; simp [solveLayout]; tauto)
    (by intro a ha; exact ha) (by simp [Lvm, solveLayout]) _ ok_vmLoop

theorem ok_solveCom (Δ : ℕ → Option Tm) (N main : ℕ) (fmt : Fmt) (p : KP) :
    Com.Ok solveLayout (solveCom Δ N main fmt p) := by
  have h0 : 0 < solveLayout.temps := by simp [solveLayout]
  unfold solveCom
  refine ⟨ok_loadCom fmt, ok_setKB _ p, ok_hbCom, ok_setupCom, ?_, ?_, ?_, ok_vmLoop', ok_wrCom⟩
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _
  · exact storeSeq_ok (by simp [solveLayout, arrNames]) h0 _ _

end Lax117284Proofs.Treewidth.Fun.Load

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolvePhases` -/

section
/-!
# WP V3 (9): the phases of `solveCom` on the input `x`, with frames

`read_phase`, and the numeric facts about `Bimp` that all phases share.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal

/-! ## Numeric facts -/

theorem N_le_progLen (Δ : ℕ → Option Tm) (N main : ℕ) : N ≤ progLen Δ N main := by
  have h : progLen Δ N main = offset Δ N := by
    simp [progLen, codeL, progCode, stub, offset_eq]; ring
  rw [h]; exact le_offset Δ N

theorem le_wordMax_of_mem {l : List ℕ} {v : ℕ} (hv : v ∈ l) : v ≤ wordMax l := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  have : l.getD j 0 = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  rw [← this]; exact wordMax_getD_le l j

theorem bexp_gt_M (M K : ℕ) : M < bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]
theorem bexp_gt_K (M K : ℕ) : K < bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]
theorem bexp_ge_two (M K : ℕ) : 2 ≤ bexp M K := by unfold bexp; nlinarith [Nat.zero_le (M + K + 2)]

theorem entry_lt_Bx (p : KP) (fmt : Fmt) (x : List ℕ) : ∀ v ∈ x, v < Bx p fmt x := by
  intro v hv
  have h1 : v ≤ wordMax x := by
    have : ∃ j, x.getD j 0 = v ∨ v = 0 := by
      obtain ⟨j, hj⟩ := List.getElem_of_mem hv
      exact ⟨j, Or.inl (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj.1]; simp [hj.2])⟩
    obtain ⟨j, hj | hj⟩ := this
    · rw [← hj]; exact wordMax_getD_le x j
    · omega
  exact lt_of_le_of_lt h1 (bexp_gt_M _ _)

theorem Bx_gt_K (p : KP) (fmt : Fmt) (x : List ℕ) : Kx p fmt x < Bx p fmt x := bexp_gt_K _ _

/-! ## The read phase -/

theorem read_phase (fmt : Fmt) {x : List ℕ} {A Bi : ℕ} (hx : x ≠ []) (hA : x.length ≤ A)
    (hxB : ∀ v ∈ x, v < Bi) (hL : x.length + 1 < Bi) (hfmt : fmtLen fmt x = x.length) {σ : IEnv}
    (hinp : σ.inp = x) (hha : σ.arrs "HA" = arrOf A (fun _ => 0)) :
    ∃ σ', Run Bi fmt.loadCom σ σ' (52 * x.length + 60) ∧ Read x A σ' ∧
      (∀ y, y ∉ ["v", "M", "i", "tot"] → σ'.vars y = σ.vars y) ∧
      (∀ a, a ≠ "HA" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out := by
  cases fmt with
  | graphK =>
    have hlen : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    obtain ⟨σ', hr, hq⟩ := (loadK_spec hx hA hxB hL hlen).run (σ := σ) ⟨hinp, hha⟩
    refine ⟨σ', hr.mono (by omega), hq, ?_, ?_, ?_⟩
    · intro y hy; exact hr.frame_var y (by simp [loadK, hdrCom, rdLoop, rdOne, Com.wvars] at hy ⊢; tauto)
    · intro a ha; exact hr.frame_arr a (by simp [loadK, hdrCom, rdLoop, rdOne, Com.warrs]; exact ha)
    · exact hr.out_eq (by simp [loadK, hdrCom, rdLoop, rdOne, Com.NoWrite])
  | graphKLD =>
    have hlen : x.getD 0 0 * x.getD 0 0 + 4 + 3 * x.getD (x.getD 0 0 * x.getD 0 0 + 3) 0 = x.length := by
      have e : 1 + x.getD 0 0 * x.getD 0 0 + 2 = x.getD 0 0 * x.getD 0 0 + 3 := by omega
      have hfmt' : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0
          = x.length := hfmt
      rw [e] at hfmt'
      omega
    obtain ⟨σ', hr, hq⟩ := (loadKLD_spec hx hA hxB hL hlen).run (σ := σ) ⟨hinp, hha⟩
    refine ⟨σ', hr.mono (by omega), hq, ?_, ?_, ?_⟩
    · intro y hy; exact hr.frame_var y (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.wvars] at hy ⊢; tauto)
    · intro a ha; exact hr.frame_arr a (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.warrs]; exact ha)
    · exact hr.out_eq (by simp [loadKLD, hdrCom, rdLoop, rdOne, bump, Com.NoWrite])

theorem idx_lt (fmt : Fmt) (x : List ℕ) (hfmt : fmtLen fmt x = x.length) :
    x.getD 0 0 * x.getD 0 0 + fmt.off < x.length := by
  cases fmt with
  | graphK =>
    have : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    show x.getD 0 0 * x.getD 0 0 + 1 < x.length
    omega
  | graphKLD =>
    have hh : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0 = x.length :=
      hfmt
    show x.getD 0 0 * x.getD 0 0 + 2 < x.length
    omega

theorem two_le_len (fmt : Fmt) (x : List ℕ) (hfmt : fmtLen fmt x = x.length) : 2 ≤ x.length := by
  cases fmt with
  | graphK =>
    have : x.getD 0 0 * x.getD 0 0 + 2 = x.length := hfmt
    omega
  | graphKLD =>
    have hh : 1 + x.getD 0 0 * x.getD 0 0 + 2 + 1 + 3 * x.getD (1 + x.getD 0 0 * x.getD 0 0 + 2) 0 = x.length :=
      hfmt
    omega

/-! ## Cost and word arithmetic (isolated) -/

theorem cost_total_le (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x y : List ℕ)
    (hy : y.length ≤ Kx p fmt x) :
    (52 * x.length + 60) + ((kE p).size + 40) + (12 + (16 * x.length + 6)) + 12 +
      (3 * progLen Δ N main + 1) + (3 * progLen Δ N main + 1) + (3 * N + 1) +
      124 * (3 * Kx p fmt x + 4) + (16 * y.length + 12) ≤ Cimp Δ N main p fmt x := by
  unfold Cimp kappa kS
  set kk := progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 +
    (kE p).size + 1 with hkk
  set K := Kx p fmt x with hK
  set n := x.length with hn
  have h1 : 1000 * K ≤ 1000 * kk * K := Nat.mul_le_mul_right _ (by omega)
  have h2 : 1000 * n ≤ 1000 * kk * n := Nat.mul_le_mul_right _ (by omega)
  have e : 1000 * kk * (K + n + 1) = 1000 * kk * K + 1000 * kk * n + 1000 * kk := by ring
  rw [e]
  omega

end Lax117284Proofs.Treewidth.Fun.Load

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolveRun` -/

section
/-!
# WP V3 (10): `solve_run` — the whole program on one input

From the initial environment `initEnv (fun _ => Wx + 1) x` the command `solveCom` runs, within `Cimp`, with every value
below `Bimp`, to an environment whose output tape is `y`, provided the functional run `Runs Δ (Bx x) main [toVal x] (toVal y) (Kx x)`
exists and `|y| ≤ Kx x`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal

theorem getD_of_ge (x : List ℕ) {j : ℕ} (h : x.length ≤ j) : x.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem noWrite_dispatchFrom : ∀ (f k : ℕ), (dispatchFrom k f).NoWrite := by
  intro f
  induction f with
  | zero =>
    intro k
    simp only [dispatchFrom]
    unfold blkOp
    split <;> simp [bHalt, bLit, bVar, bBin, bLt, bEq, bCons, bFst, bSnd, bIsNat, bJz, bJmp, bSlide, bCall, bRet,
      incPc, incSp, decSp, Com.NoWrite]
  | succ f ih =>
    intro k
    simp only [dispatchFrom, Com.NoWrite]
    refine ⟨?_, ih (k + 1)⟩
    unfold blkOp
    split <;> simp [bHalt, bLit, bVar, bBin, bLt, bEq, bCons, bFst, bSnd, bIsNat, bJz, bJmp, bSlide, bCall, bRet,
      incPc, incSp, decSp, Com.NoWrite]

theorem noWrite_vmLoop : vmLoop.NoWrite := by
  unfold vmLoop bBody bFetch bDispatch
  simp only [Com.NoWrite]
  exact ⟨⟨trivial, trivial⟩, noWrite_dispatchFrom 16 0⟩

theorem solve_run (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt) (p : KP)
    (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) {x y : List ℕ} (hfmt : fmtLen fmt x = x.length)
    (hruns : Runs Δ (Bx p fmt x) main [toVal x] (toVal y) (Kx p fmt x)) (hy : y.length ≤ Kx p fmt x) :
    ∃ σ', Run (Bimp Δ N main p fmt x) (solveCom Δ N main fmt p)
      (initEnv (fun _ => Wx Δ N main p fmt x + 1) x) σ' (Cimp Δ N main p fmt x) ∧ σ'.out = y := by
  -- numeric facts, front-loaded
  have hn2 : 2 ≤ x.length := two_le_len fmt x hfmt
  have hx : x ≠ [] := by intro h; rw [h] at hn2; simp at hn2
  have hBv2 : 2 ≤ Bx p fmt x := bexp_ge_two _ _
  have hKB : Kx p fmt x < Bx p fmt x := Bx_gt_K p fmt x
  have hxBv : ∀ v ∈ x, v < Bx p fmt x := entry_lt_Bx p fmt x
  have hBiEq : Bimp Δ N main p fmt x = 2 * Bx p fmt x + 4 * (Kx p fmt x + x.length + 8) + kappa Δ N main p := rfl
  have hWEq : Wx Δ N main p fmt x = (Bx p fmt x + x.length + 1) + progLen Δ N main + Bx p fmt x + 3 * Kx p fmt x + 3 := rfl
  have hkS : progLen Δ N main + N + wordMax (opasL Δ N main) + wordMax (ftL Δ N) + p.c0 + p.c1 + p.c2 + (kE p).size + 1
      = kS Δ N main p := rfl
  have hκ : kappa Δ N main p = 1000 * kS Δ N main p := rfl
  have hκpl : progLen Δ N main < kappa Δ N main p := by omega
  have hκN : N < kappa Δ N main p := by omega
  have hκo : wordMax (opasL Δ N main) < kappa Δ N main p := by omega
  have hκf : wordMax (ftL Δ N) < kappa Δ N main p := by omega
  have hκc1 : p.c1 < kappa Δ N main p := by omega
  have hκc2 : p.c2 < kappa Δ N main p := by omega
  have hκ16 : 16 < kappa Δ N main p := by omega
  have hNp := N_le_progLen Δ N main
  have hCost := cost_total_le Δ N main p fmt x y hy
  set n := x.length with hn
  set Bv := Bx p fmt x with hBv
  set Kv := Kx p fmt x with hKv
  set κ := kappa Δ N main p with hκdef
  set Bi := Bimp Δ N main p fmt x with hBidef
  set W := Wx Δ N main p fmt x with hWdef
  set A := W + 1 with hAdef
  set σ0 : IEnv := initEnv (fun _ => A) x with hσ0
  have hAn : n ≤ A := by omega
  have hxB : ∀ v ∈ x, v < Bi := fun v hv => by have := hxBv v hv; omega
  have hL : n + 1 < Bi := by omega
  have hσ0inp : σ0.inp = x := rfl
  have hσ0arr : ∀ a, σ0.arrs a = List.replicate A 0 := fun a => rfl
  have hσ0out : σ0.out = [] := rfl
  -- phase 1: read
  obtain ⟨σ1, hr1, hread, hv1, ha1, ho1⟩ := read_phase fmt (Bi := Bi) hx hAn hxB hL hfmt (σ := σ0) hσ0inp
    (by rw [hσ0arr]; exact replicate_eq_arrOf _ _)
  have hi1 : σ1.vars "i" = n := hread.2
  have hha1 : σ1.arrs "HA" = arrOf A (fun j => x.getD j 0) := by
    rw [hread.1.1.ha, hi1]
    exact arrOf_congr (fun j _ => by
      by_cases hj : j < n
      · simp [hj]
      · rw [if_neg hj, getD_of_ge x (show x.length ≤ j by omega)])
  have hM1 : σ1.vars "M" = wordMax x := by
    have := hread.1.1.hM
    rw [hi1, hn, List.take_length] at this
    exact this
  -- phase 2: K, B
  have hidx : x.getD 0 0 * x.getD 0 0 + fmt.off < n := idx_lt fmt x hfmt
  have r2 := setKB_run (x := x) (A := A) (Bi := Bi) (off := fmt.off) p h0 h1 h2 hAn hxB hidx
    (by omega) (by omega) (show Kx p fmt x < Bi by omega) (show Bx p fmt x < Bi by omega) hi1 hha1 hM1
  set σ2 := afterKB x fmt.off p σ1 with hσ2
  have hσ2len : σ2.vars "len" = n := by simp [hσ2, afterKB]; rfl
  have hσ2B : σ2.vars "B" = Bv := by simp [hσ2, afterKB]; rfl
  have hσ2a : ∀ a, σ2.arrs a = σ1.arrs a := fun a => rfl
  have hσ2o : σ2.out = σ1.out := rfl
  have hσ2v : ∀ y, y ≠ "len" → y ≠ "kw" → y ≠ "K" → y ≠ "B" → σ2.vars y = σ1.vars y := by
    intro y a b c d; simp [hσ2, afterKB, a, b, c, d]
  -- phase 3: HB
  obtain ⟨σ3, hr3, hq3⟩ := (hbCom_spec (A := A) (Bv := Bv) (n := n) (Bi := Bi) hAn (by omega) (by omega)
    (by omega)).run (σ := σ2) ⟨hσ2len, hσ2B, by rw [hσ2a, ha1 "HB" (by decide), hσ0arr "HB"]; exact replicate_eq_arrOf _ _⟩
  have hv3 : ∀ y, y ≠ "tot" → y ≠ "i" → σ3.vars y = σ2.vars y := fun y a b =>
    hr3.frame_var y (by simp [hbCom, hbLoop, hbBody, bump, Com.wvars, a, b])
  have ha3 : ∀ a, a ≠ "HB" → σ3.arrs a = σ2.arrs a := fun a ha =>
    hr3.frame_arr a (by simp [hbCom, hbLoop, hbBody, Com.warrs, ha])
  have ho3 : σ3.out = σ2.out := hr3.out_eq (by simp [hbCom, hbLoop, hbBody, bump, Com.NoWrite])
  have hB3 : σ3.vars "B" = Bv := hq3.1.2.2.1
  have hlen3 : σ3.vars "len" = n := hq3.2.2
  have hi3 : σ3.vars "i" = n - 1 := hq3.2.1
  have hHB3 : σ3.arrs "HB" = arrOf A (fun j => if j < n - 1 then Bv + j + 1 else 0) := by
    have := hq3.1.2.2.2; rw [hi3] at this; exact this
  -- phase 4: scalars
  have hSTK3 : σ3.arrs "STK" = List.replicate A 0 := by
    rw [ha3 _ (by decide), hσ2a, ha1 _ (by decide), hσ0arr]
  have hr4 := setup_run (Bi := Bi) (n := n) (Bv := Bv) (by omega) (σ := σ3) hlen3 hB3 (by omega) (by omega)
    (by rw [hSTK3]; simp; omega)
  set σ4 := afterSetup n Bv σ3 with hσ4
  have hz : ∀ a, a ≠ "HA" → a ≠ "HB" → a ≠ "STK" → σ4.arrs a = List.replicate A 0 := by
    intro a a1 a2 a3'
    simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar, a3', if_false]
    rw [ha3 a a2, hσ2a, ha1 a a1, hσ0arr]
  have hv4 : ∀ y, y ≠ "sp" → y ≠ "hp" → y ≠ "run" → σ4.vars y = σ3.vars y := by
    intro y a b c; simp [hσ4, afterSetup, a, b, c]
  -- phases 5-7: the code arrays
  have hopsB : ∀ v ∈ opsL Δ N main, v < Bi := fun v hv => by have := opsL_lt Δ N main v hv; omega
  have hopasB : ∀ v ∈ opasL Δ N main, v < Bi := fun v hv => by have := le_wordMax_of_mem hv; omega
  have hftB : ∀ v ∈ ftL Δ N, v < Bi := fun v hv => by have := le_wordMax_of_mem hv; omega
  have hlo : (opsL Δ N main).length = progLen Δ N main := opsL_length Δ N main
  have hla : (opasL Δ N main).length = progLen Δ N main := opasL_length Δ N main
  have hlf : (ftL Δ N).length = N := ftL_length Δ N
  obtain ⟨σ5, hr5, ha5, hv5, hi5, ho5, hb5⟩ := storeSeq_run0 (Bi := Bi) "OP" (opsL Δ N main) σ4 A
    (hz "OP" (by decide) (by decide) (by decide)) (by omega) hopsB (by omega)
  obtain ⟨σ6, hr6, ha6, hv6, hi6, ho6, hb6⟩ := storeSeq_run0 (Bi := Bi) "OA" (opasL Δ N main) σ5 A
    (by rw [hb5 _ (by decide)]; exact hz "OA" (by decide) (by decide) (by decide)) (by omega) hopasB (by omega)
  obtain ⟨σ7, hr7, ha7, hv7, hi7, ho7, hb7⟩ := storeSeq_run0 (Bi := Bi) "FT" (ftL Δ N) σ6 A
    (by rw [hb6 _ (by decide), hb5 _ (by decide)]; exact hz "FT" (by decide) (by decide) (by decide)) (by omega) hftB
    (by omega)
  have hv47 : σ7.vars = σ4.vars := by rw [hv7, hv6, hv5]
  have hLoaded : Loaded Δ N main x Bv A σ7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hv3 _ (by decide) (by decide),
        hσ2v _ (by decide) (by decide) (by decide) (by decide), hv1 _ (by decide)]; rfl
    · rw [hv47]; simp [hσ4, afterSetup]
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hv3 _ (by decide) (by decide),
        hσ2v _ (by decide) (by decide) (by decide) (by decide), hv1 _ (by decide)]; rfl
    · rw [hv47]; simp [hσ4, afterSetup]; rfl
    · rw [hv47, hv4 _ (by decide) (by decide) (by decide), hB3]
    · rw [hv47]; simp [hσ4, afterSetup]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_neg (by decide), ha3 _ (by decide), hσ2a, hha1]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_neg (by decide), hHB3]
      exact arrOf_congr (fun j _ => by unfold hbF; split_ifs <;> first | rfl | (exfalso; omega))
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide)]
      simp only [hσ4, afterSetup, arrs_setArr, arrs_setVar]
      rw [if_true, hSTK3, replicate_eq_arrOf, set_arrOf]
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide), hz "RETPC" (by decide) (by decide) (by decide)]
      simp
    · rw [hb7 _ (by decide), hb6 _ (by decide), hb5 _ (by decide), hz "RETH" (by decide) (by decide) (by decide)]
      simp
    · rw [hb7 _ (by decide), hb6 _ (by decide)]; exact ha5
    · rw [hb7 _ (by decide)]; exact ha6
    · exact ha7
  -- the VM run
  have hWeq' : W = (Bv + n + 1) + (mkProgF Δ N main 1 Bv).len + Bv + 3 * Kv + 3 := hWEq
  have hAbs7 : Abs ⟨0, [Bv] ++ [], [], heapOf x Bv⟩ σ7 := abs_of_loaded hLoaded hAn (by omega) hx
  have hCst7 : Cst (mkProgF Δ N main 1 Bv) ((Bv + n + 1) + (mkProgF Δ N main 1 Bv).len + Bv + 3 * Kv + 3) Bi σ7 := by
    rw [← hWeq']
    exact cst_of_loaded hLoaded (W := W) rfl (by omega) (by omega) (by omega)
  have hrep : RepL Bv (heapOf x Bv) [Bv] [toVal x] := RepL.cons (rep_input (by omega) hxBv hx) RepL.nil
  have hbd : St.Bd (Bv + n + 1) ⟨0, [Bv] ++ [], [], heapOf x Bv⟩ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 ≤ _; omega
    · simp
    · intro w hw; simp at hw; omega
    · simp
    · intro q hq; simp at hq
    · show (heapOf x Bv).length ≤ Bv + n + 1
      rw [heapOf_length]; omega
    · intro q hq
      simp only [heapOf, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      have := getD_lt (B := Bv) (x := x) (by omega) hxBv j
      unfold hbF
      constructor
      · omega
      · split_ifs <;> omega
  obtain ⟨w, H', σ8, hr8, hA8, hC8, hrun8, hext, hrep8, hlen8⟩ := vm_ram_correctF Δ hN hBv2 (main := main)
    (xs := [toVal x]) (y := toVal y) (c := Kv) hruns hrep hbd hAbs7 hCst7 hLoaded.run
  rw [heapOf_length] at hlen8
  have hrep8' : Rep Bv H' w (listVal y) := by rw [← toVal_list]; exact hrep8
  have hstk8 : (σ8.arrs "STK")[0]? = some w := by
    have := hA8.result.2
    simpa using this
  obtain ⟨σ9, hr9, ho9⟩ := wrCom_run (Bi := Bi) (B := Bv) (w := w) (H := H') (l := y) (σ := σ8) (by omega)
    (by omega) hrep8' hstk8 hC8.tb hA8.ha hA8.hb
  refine ⟨σ9, ?_, ?_⟩
  · exact ((hr1.seq (r2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq hr9)))))))).mono
      (by have := hCost; omega))
  · rw [ho9]
    have e8 : σ8.out = σ7.out := hr8.out_eq noWrite_vmLoop
    have e4 : σ4.out = σ3.out := rfl
    rw [e8, ho7, ho6, ho5, e4, ho3, hσ2o, ho1]
    simp [σ0, initEnv]

end Lax117284Proofs.Treewidth.Fun.Load

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolve` -/

section
/-!
# WP V3 (11): `compile_solves` — the compiler theorem

`solve_solves` : the single IMP+ program `solveCom Δ N main fmt p` under the layout `solveLayout` **solves** the function `f`
(`Transfer.Solves`) on every set `D` of words of the format `fmt` on which the table `Δ` computes `f` functionally:

    `Runs Δ (Bx x) main [toVal x] (toVal (f x)) (Kx x)`  and  `|f x| ≤ Kx x`

with the explicit bounds `Bimp = 2 Bx + 4 (Kx + |x| + 8) + κ` (IMP+ values) and `Cimp = κ (Kx + |x| + 1)` (IMP+ cost), where
`Kx = c₀ · 2^(c₁ kw³) · (|x| + c₂)^c₃`, `Bx = (maxEntry x + Kx + 2)² + 1`, `kw` = the parameter entry (`k`, resp. `l`).

`compile_solves` is the `∃ layout, program, κ, ∀ D f, …` form asked for by `proofs-todo/Machine.lean`, modified in two ways that
the mathematics forces: (i) the tag bound `Bv` and the cost bound `K` are the closed formulas above rather than arbitrary
functions (the program is fixed before them, so it must be able to *compute* them); (ii) the output length is charged
(`|f x| ≤ Kx x`): a value's tree size is not bounded by the derivation cost (`cons (var 0) (var 0)` doubles the size).
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram ToVal
open Lax808846Proofs.Transfer

theorem solve_solves (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt) (p : KP)
    (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) {D : Set (List ℕ)} {f : List ℕ → List ℕ}
    (hfmt : ∀ x ∈ D, fmtLen fmt x = x.length)
    (hruns : ∀ x ∈ D, Runs Δ (Bx p fmt x) main [toVal x] (toVal (f x)) (Kx p fmt x))
    (hlen : ∀ x ∈ D, (f x).length ≤ Kx p fmt x) :
    Solves solveLayout (solveCom Δ N main fmt p) D f (Bimp Δ N main p fmt) (Cimp Δ N main p fmt) where
  ok := ok_solveCom Δ N main fmt p
  inp := by
    intro x hx v hv
    have := entry_lt_Bx p fmt x v hv
    unfold Bimp; omega
  run := by
    intro x hx
    obtain ⟨σ', hr, ho⟩ := solve_run Δ hN main fmt p h0 h1 h2 (hfmt x hx) (hruns x hx) (hlen x hx)
    exact ⟨_, σ', hr, ho⟩

end Lax117284Proofs.Treewidth.Fun.Load

end

/-! ### `Lax117284Proofs.Treewidth.Fun.VMSolveGuard` -/

section
/-!
# WP V3 (12): `fits_of_guard` — the word-length guard of the concept implies `Layout.FitsWords`

The concept's guard is `∀ v ∈ x, c · 2^(c e³) · (|x| + v + 1)^c ≤ 2^W`.  For the layout `Ly` (its span is
`temps + 2 + #scalars + #arrays · B`) and `Bfun c' e x = c' · 2^(c' e³) · (|x| + maxEntry x + 1)^c'` the fitting condition
`1 < B`, `B ≤ 2^W`, `span B ≤ 2^W` follows once `c ≥ (temps + 2 + #scalars + #arrays) · c'`.
-/

namespace Lax117284Proofs.Treewidth.Fun.Load

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax117284Proofs.Treewidth.Fun.VM Lax117284Proofs.Treewidth.Fun.VM.Ram

/-- The IMP+ value bound of the concept-level statements (`c'`, exponent parameter `e`). -/
def Bfun (c' e : ℕ) (x : List ℕ) : ℕ := c' * 2 ^ (c' * e ^ 3) * (x.length + maxEntry x + 1) ^ c'

theorem maxEntry_mem : ∀ {x : List ℕ}, x ≠ [] → maxEntry x ∈ x := by
  intro x
  induction x with
  | nil => intro h; exact absurd rfl h
  | cons a l ih =>
    intro _
    by_cases hl : l = []
    · subst hl; simp [maxEntry]
    · have := ih hl
      simp only [maxEntry, List.foldr_cons] at this ⊢
      rcases max_choice a (l.foldr max 0) with h | h
      · rw [h]; simp
      · rw [h]; exact List.mem_cons_of_mem _ this

theorem fits_of_guard {Ly : Layout} {c' c W e : ℕ} {x : List ℕ} (hx : x ≠ []) (hc' : 1 ≤ c')
    (hc : (Ly.temps + 2 + Ly.scalars.length + Ly.arrays.length) * c' ≤ c)
    (hg : ∀ v ∈ x, c * 2 ^ (c * e ^ 3) * (x.length + v + 1) ^ c ≤ 2 ^ W) :
    Ly.FitsWords (Bfun c' e x) W := by
  have hg' := hg _ (maxEntry_mem hx)
  set m := Ly.temps + 2 + Ly.scalars.length + Ly.arrays.length with hm
  set X := x.length + maxEntry x + 1 with hX
  have hxl : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hX2 : 2 ≤ X := by omega
  have hm1 : 1 ≤ m := by omega
  have hc'c : c' ≤ c := by nlinarith
  have hp1 : 2 ^ (c' * e ^ 3) ≤ 2 ^ (c * e ^ 3) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hc'c)
  have hp2 : X ^ c' ≤ X ^ c := Nat.pow_le_pow_right (by omega) hc'c
  have hB1 : 1 ≤ 2 ^ (c' * e ^ 3) := Nat.one_le_two_pow
  have hXB : X ≤ X ^ c' := Nat.le_self_pow (by omega) X
  set B := Bfun c' e x with hB
  have hBdef : B = c' * 2 ^ (c' * e ^ 3) * X ^ c' := rfl
  have hB2 : 2 ≤ B := by
    rw [hBdef]
    have : 1 * 1 * 2 ≤ c' * 2 ^ (c' * e ^ 3) * X ^ c' :=
      Nat.mul_le_mul (Nat.mul_le_mul hc' hB1) (le_trans hX2 hXB)
    omega
  have hmB : m * B ≤ 2 ^ W := by
    calc m * B = (m * c') * 2 ^ (c' * e ^ 3) * X ^ c' := by rw [hBdef]; ring
      _ ≤ c * 2 ^ (c * e ^ 3) * X ^ c :=
          Nat.mul_le_mul (Nat.mul_le_mul hc hp1) hp2
      _ ≤ 2 ^ W := hg'
  refine ⟨by omega, ?_, ?_⟩
  · calc B ≤ 1 * B := by omega
      _ ≤ m * B := Nat.mul_le_mul_right _ hm1
      _ ≤ 2 ^ W := hmB
  · have : Ly.span B ≤ m * B := by
      unfold Layout.span
      have : Ly.temps + 2 + Ly.scalars.length ≤ (Ly.temps + 2 + Ly.scalars.length) * B := by
        nlinarith
      have e : m * B = (Ly.temps + 2 + Ly.scalars.length) * B + Ly.arrays.length * B := by rw [hm]; ring
      omega
    omega

theorem fitsWords_mono {Ly : Layout} {B B' W : ℕ} (h : Ly.FitsWords B W) (hle : B' ≤ B) (h1 : 1 < B') :
    Ly.FitsWords B' W := by
  refine ⟨h1, le_trans hle h.bound, le_trans ?_ h.span⟩
  unfold Layout.span
  have := Nat.mul_le_mul_left Ly.arrays.length hle
  omega

theorem bimp_arith (S A1 A2 Z2 K n κ κZ : ℕ) (hS : S ≤ A1) (hK : K ≤ A2) (hn : n ≤ Z2) (h1 : 1 ≤ Z2)
    (hκ : κ ≤ κZ) : 2 * (S + 1) + 4 * (K + n + 8) + κ ≤ 2 * A1 + 4 * A2 + 38 * Z2 + κZ := by omega

/-- The constant `c'` for which the IMP+ value bound of `compile_solves` is below `Bfun c'`. -/
def cB (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : ℕ :=
  2 * (1 + p.c0 * p.c2 ^ p.c3) ^ 2 + 4 * (p.c0 * p.c2 ^ p.c3) + 38 + kappa Δ N main p + 2 * p.c1 + 2 * p.c3 + 2

theorem cB_pos (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) : 1 ≤ cB Δ N main p := by unfold cB; omega

/-- **The IMP+ value bound of `compile_solves` is dominated by the concept's `Bfun`** (with `e = kw`). -/
theorem Bimp_le_Bfun (Δ : ℕ → Option Tm) (N main : ℕ) (p : KP) (fmt : Fmt) (x : List ℕ) (h0 : 1 ≤ p.c0)
    (h2 : 1 ≤ p.c2) (hn : 1 ≤ x.length) :
    Bimp Δ N main p fmt x ≤ Bfun (cB Δ N main p) (fmt.kw x) x := by
  set n := x.length with hn'
  set M := maxEntry x with hM
  set X := n + M + 1 with hX
  set e := fmt.kw x with he
  set u := p.c0 * p.c2 ^ p.c3 with hu
  set Q := 2 ^ (p.c1 * e ^ 3) with hQ
  set Z := Q * X ^ (p.c3 + 1) with hZ
  set κ := kappa Δ N main p with hκ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hX1 : 1 ≤ X := by omega
  have hXM : M + 2 ≤ X := by omega
  have hZX : X ≤ Z := by
    calc X ≤ X ^ (p.c3 + 1) := Nat.le_self_pow (by omega) X
      _ = 1 * X ^ (p.c3 + 1) := by ring
      _ ≤ Q * X ^ (p.c3 + 1) := Nat.mul_le_mul_right _ hQ1
  have hR : (n + p.c2) ^ p.c3 ≤ p.c2 ^ p.c3 * X ^ p.c3 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le M]) _
  have hK : Kx p fmt x = p.c0 * Q * (n + p.c2) ^ p.c3 := rfl
  have hKu : Kx p fmt x ≤ u * Z := by
    rw [hK]
    calc p.c0 * Q * (n + p.c2) ^ p.c3 ≤ p.c0 * Q * (p.c2 ^ p.c3 * X ^ p.c3) := Nat.mul_le_mul_left _ hR
      _ = u * (Q * X ^ p.c3) := by rw [hu]; ring
      _ ≤ u * (Q * X ^ (p.c3 + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have hMK : M + Kx p fmt x + 2 ≤ (1 + u) * Z := by
    have : (1 + u) * Z = Z + u * Z := by ring
    omega
  have hsq : (M + Kx p fmt x + 2) ^ 2 ≤ (1 + u) ^ 2 * Z ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hMK 2
  have hZ1 : 1 ≤ Z := le_trans hX1 hZX
  have hZ2 : Z ≤ Z ^ 2 := by
    calc Z = Z * 1 := by ring
      _ ≤ Z * Z := Nat.mul_le_mul_left _ hZ1
      _ = Z ^ 2 := by ring
  have h3 : n ≤ Z ^ 2 := by omega
  have h4 : 1 ≤ Z ^ 2 := le_trans hZ1 hZ2
  have h5 : Kx p fmt x ≤ u * Z ^ 2 := le_trans hKu (Nat.mul_le_mul_left _ hZ2)
  have h6 : κ ≤ κ * Z ^ 2 := by
    calc κ = κ * 1 := by ring
      _ ≤ κ * Z ^ 2 := Nat.mul_le_mul_left _ h4
  have h7 : Bimp Δ N main p fmt x ≤ (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 := by
    unfold Bimp Bx bexp
    rw [← hM]
    have e : (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 =
        2 * ((1 + u) ^ 2 * Z ^ 2) + 4 * (u * Z ^ 2) + 38 * Z ^ 2 + κ * Z ^ 2 := by ring
    rw [e]
    exact bimp_arith _ _ _ _ _ _ _ _ hsq h5 h3 h4 h6
  have h8 : (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * Z ^ 2 ≤ Bfun (cB Δ N main p) e x := by
    unfold Bfun
    have hcBe : cB Δ N main p = 2 * (1 + u) ^ 2 + 4 * u + 38 + κ + 2 * p.c1 + 2 * p.c3 + 2 := rfl
    have hcB : 2 * (1 + u) ^ 2 + 4 * u + 38 + κ ≤ cB Δ N main p := by omega
    have hZe : Z ^ 2 = 2 ^ (2 * p.c1 * e ^ 3) * X ^ (2 * p.c3 + 2) := by
      rw [hZ, hQ, mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    have hp1 : 2 ^ (2 * p.c1 * e ^ 3) ≤ 2 ^ (cB Δ N main p * e ^ 3) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
    have hp2 : X ^ (2 * p.c3 + 2) ≤ X ^ (cB Δ N main p) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hZe]
    calc (2 * (1 + u) ^ 2 + 4 * u + 38 + κ) * (2 ^ (2 * p.c1 * e ^ 3) * X ^ (2 * p.c3 + 2))
        ≤ cB Δ N main p * (2 ^ (cB Δ N main p * e ^ 3) * X ^ (cB Δ N main p)) :=
          Nat.mul_le_mul hcB (Nat.mul_le_mul hp1 hp2)
      _ = cB Δ N main p * 2 ^ (cB Δ N main p * e ^ 3) * X ^ (cB Δ N main p) := by ring
  exact le_trans h7 h8

open Lax808846.Ram Lax808846.RamComputes Lax117284Proofs.Treewidth.Fun.ToVal in
/-- **End-to-end (WP V3 + the guard).**  One machine program `prog` (chosen before `D`, `f`, `w`) computes `f` on `D` in time
`10 κ (Kx + |x| + 1) + 1`, at every word length `w` satisfying the guard
`∀ x ∈ D, ∀ v ∈ x, c · 2^(c · kw³) · (|x| + v + 1)^c ≤ 2^w`, provided the table computes `f` functionally
(`Runs Δ (Bx x) main [toVal x] (toVal (f x)) (Kx x)`, `|f x| ≤ Kx x`). -/
theorem compile_computes (Δ : ℕ → Option Tm) {N : ℕ} (hN : ∀ f, N ≤ f → Δ f = none) (main : ℕ) (fmt : Fmt)
    (p : KP) (h0 : 1 ≤ p.c0) (h1 : 1 ≤ p.c1) (h2 : 1 ≤ p.c2) :
    ∃ (prog : Program) (c : ℕ), ∀ (D : Set (List ℕ)) (f : List ℕ → List ℕ),
      (∀ x ∈ D, fmtLen fmt x = x.length) →
      (∀ x ∈ D, Runs Δ (Bx p fmt x) main [Lax117284Proofs.Treewidth.Fun.ToVal.toVal x] (Lax117284Proofs.Treewidth.Fun.ToVal.toVal (f x)) (Kx p fmt x)) →
      (∀ x ∈ D, (f x).length ≤ Kx p fmt x) →
      ∀ w, (∀ x ∈ D, ∀ v ∈ x, c * 2 ^ (c * (fmt.kw x) ^ 3) * (x.length + v + 1) ^ c ≤ 2 ^ w) →
        ComputesInTime w prog D f (fun x => 10 * kappa Δ N main p * (Kx p fmt x + x.length + 1) + 1) := by
  refine ⟨compileProgram solveLayout (solveCom Δ N main fmt p),
    (solveLayout.temps + 2 + solveLayout.scalars.length + solveLayout.arrays.length) * cB Δ N main p,
    fun D f hfmt hruns hlen w hg => ?_⟩
  have hS := solve_solves Δ hN main fmt p h0 h1 h2 hfmt hruns hlen
  refine Lax808846Proofs.Transfer.computesInTime_of_solves hS (fun x hx => ?_) (fun x hx => ?_)
  · have hx0 : x ≠ [] := by
      intro h; have := two_le_len fmt x (hfmt x hx); rw [h] at this; simp at this
    have hfit := fits_of_guard (Ly := solveLayout) (c' := cB Δ N main p) (e := fmt.kw x) (W := w) hx0
      (cB_pos Δ N main p) le_rfl (hg x hx)
    refine fitsWords_mono hfit (Bimp_le_Bfun Δ N main p fmt x h0 h2 (List.length_pos_iff.mpr hx0)) ?_
    have : 2 ≤ Bx p fmt x := bexp_ge_two _ _
    unfold Bimp; omega
  · have : solveLayout.const = 10 := rfl
    rw [this]; unfold Cimp; rw [Nat.mul_assoc]

end Lax117284Proofs.Treewidth.Fun.Load

end
