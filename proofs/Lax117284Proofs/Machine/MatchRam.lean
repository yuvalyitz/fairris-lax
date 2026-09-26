import Lax117284Proofs.Machine.MatchGuard
import Lax117284Proofs.Machine.RamBridge2
import Lax808846Proofs.Transfer

/-!
The guarded conversion as a polynomial-time word RAM computation on the length-prefixed input:
the second stage of the proof of Theorem 2's tractability, between the reduction of `UFinal`
and the cited decider of `lax-817977`.

The program reads the length prefix into `len`, the word into `t`, and the header `R = t[0]`,
`C = t[1]`; it prints the fixed word `W1` when `R = 0` (the empty left side is saturated) and the
fixed word `W0` when `C = 0`, when the table does not reach its last row, or when `C` exceeds the
word (`Heavy` fails); otherwise it converts the table into the CSR word
(`MatchGuard.convCom`) and prints it. Every value it handles is below
`Bof x = 8 (|x| + max x + 1) + 40`, and it runs within a polynomial of the bit size of the word.
-/

namespace Lax117284Proofs.Machine.MatchRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944Proofs.Encoding
open Lax117284Proofs.Machine.MatchGuard
open scoped Classical

variable {B : ℕ}

/-! ### Printing the array -/

/-- One entry of `a` to the output, and the step. -/
def outBody : Com :=
  .seq (.write (.get "a" (.var "wr"))) (.assign "wr" (.add (.var "wr") (.lit 1)))

/-- The printing loop: the entries of `a` below `lc`. -/
def outLoop : Com :=
  .seq (.assign "wr" (.lit 0)) (.while (.lt (.var "wr") (.var "lc")) outBody)

/-- The CSR word, held in `a`, to the output: its length is `4 + V + p`. -/
def outCom : Com :=
  .seq (.assign "lc" (.add (.add (.lit 4) (.var "V")) (.var "p"))) outLoop

/-- The invariant of the printing loop: the entries before `wr` are out. -/
def OInv (Z : List ℕ) (σ : Env) : Prop :=
  σ.vars "lc" = Z.length ∧ σ.arrs "a" = Z ∧ σ.vars "wr" ≤ Z.length ∧
    σ.out = Z.take (σ.vars "wr")

theorem outBody_spec {Z : List ℕ} (hZ : Z.length < B) (hE : ∀ v ∈ Z, v < B) :
    Spec B (fun σ => OInv Z σ ∧ σ.vars "wr" < Z.length) outBody
      (fun σ σ' => OInv Z σ' ∧ σ'.vars "wr" = σ.vars "wr" + 1) 7 := by
  have hw : Spec B (fun σ => OInv Z σ ∧ σ.vars "wr" < Z.length) (.write (.get "a" (.var "wr")))
      (fun σ σ' => σ' = { σ with out := σ.out ++ [Z.getD (σ.vars "wr") 0] }) 3 := by
    refine Spec.write (f := fun σ => Z.getD (σ.vars "wr") 0) ?_
    rintro σ ⟨⟨hzl, hz, hle, hout⟩, hlt⟩
    have hmem : Z.getD (σ.vars "wr") 0 ∈ Z := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
    refine evalB_get (k := σ.vars "wr") (evalB_var (by omega)) ?_ (hE _ hmem)
    rw [hz, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  have ha : Spec B (fun σ => σ.vars "wr" < Z.length) (.assign "wr" (.add (.var "wr") (.lit 1)))
      (fun σ σ' => σ' = σ.setVar "wr" (σ.vars "wr" + 1)) 4 := by
    refine Spec.assign (f := fun σ => σ.vars "wr" + 1) ?_
    intro σ hlt
    exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by show _ + _ < B; omega)
  unfold outBody
  refine Spec.seq hw ha ?_ ?_
  · rintro σ σ' ⟨⟨hzl, hz, hle, hout⟩, hlt⟩ rfl
    exact hlt
  · rintro σ σ' σ'' ⟨⟨hzl, hz, hle, hout⟩, hlt⟩ rfl rfl
    refine ⟨⟨by simp [Env.setVar, hzl], by simp [Env.setVar, hz], by simp [Env.setVar]; omega, ?_⟩,
      by simp [Env.setVar]⟩
    simp only [Env.setVar, if_true, hout]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.take_succ_eq_append_getElem hlt]

/-- **The loop prints `a`.** -/
theorem outLoop_spec {Z : List ℕ} (hZ : Z.length < B) (hE : ∀ v ∈ Z, v < B) :
    Spec B (fun σ => σ.vars "lc" = Z.length ∧ σ.arrs "a" = Z ∧ σ.out = []) outLoop
      (fun _ σ' => σ'.out = Z) (11 * Z.length + 6) := by
  have h := Spec.forRangeZero (B := B) (c := outBody) "wr" "lc" (OInv Z) Z.length 7 hZ
    (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1) (outBody_spec hZ hE)
  refine Spec.conseq h ?_ ?_ le_rfl
  · rintro σ ⟨h1, h2, h3⟩
    exact ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2, by simp [Env.setVar],
      by simp [Env.setVar, h3]⟩
  · rintro σ σ' _ ⟨⟨-, -, -, hout⟩, hi⟩
    rw [hout, hi, List.take_length]

/-! ### The heavy path -/

/-- **The heavy path**: convert, then print. -/
def heavyCom : Com := .seq convCom outCom

/-- The cost of the heavy path. -/
def heavyCost (x : List ℕ) : ℕ := 300 * x.length + 300

theorem arrOf_eq_of_getD {n : ℕ} {f : ℕ → ℕ} {l : List ℕ} (hl : l.length = n)
    (h : ∀ i < n, f i = l.getD i 0) : arrOf n f = l := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < n := by simpa using h1
  have e1 : (arrOf n f)[i] = f i := by simp [arrOf]
  have e2 : l[i] = l.getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  rw [e1, e2]
  exact h i hi

/-- **The heavy path, run**: the CSR word is printed. -/
theorem heavy_run {x : List ℕ} {R C Lt : ℕ} (hc : HC x R C) (hB : 8 * x.length + 40 ≤ B)
    (hx : ∀ v ∈ x, v < B) (hLt : 2 + R * C ≤ Lt) {σ : Env}
    (hR : σ.vars "R" = R) (hC : σ.vars "C" = C) (htab : TabOK x Lt σ)
    (ha : σ.arrs "a" = List.replicate (Lc x R C) 0) (hout : σ.out = []) :
    ∃ σ' K, Run B heavyCom σ σ' K ∧ K ≤ heavyCost x ∧ σ'.out = csrP x R C := by
  have hRle := hc.Rle
  have hCle := hc.Cle
  have hRC := hc.RC
  have hLc := hc.hLc
  have hE := hc.hE
  have hlen' : (csrP x R C).length = Lc x R C := Lc_eq x R C
  -- the conversion
  obtain ⟨σ₁, r1, hR₁, hC₁, hV₁, hp₁, -, ha₁⟩ := (conv_spec hc hB hx hLt).run ⟨hR, hC, htab, ha⟩
  have hout₁ : σ₁.out = [] := by rw [r1.out_eq (by decide)]; exact hout
  have ha₁' : σ₁.arrs "a" = csrP x R C := by
    rw [ha₁]
    exact arrOf_eq_of_getD hlen' (fun i hi => AFin_eq x R C hi)
  -- lc := 4 + V + p
  have hVe : (Expr.var "V").evalB B σ₁ = some (R + C) := by
    rw [← hV₁]; exact RunStep.eval_var B σ₁ "V" (by rw [hV₁]; omega)
  have hpe : (Expr.var "p").evalB B σ₁ = some (E x R C) := by
    rw [← hp₁]; exact RunStep.eval_var B σ₁ "p" (by rw [hp₁]; omega)
  have h4 := RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 4 σ₁ (by omega)) hVe (by omega)
  have hlc := RunStep.eval_add B σ₁ _ _ _ _ h4 hpe (by unfold Lc at hLc; omega)
  have r2 := RunStep.assign B σ₁ "lc" _ _ hlc
  set σ₂ := σ₁.setVar "lc" (4 + (R + C) + E x R C) with hσ₂
  -- the loop
  have hZ : (csrP x R C).length < B := by rw [hlen']; omega
  have hEz : ∀ v ∈ csrP x R C, v < B := fun v hv => by
    have := mem_csrP_le x R C hv; omega
  obtain ⟨σ₃, r3, hout₃⟩ := (outLoop_spec hZ hEz).run (σ := σ₂)
    ⟨by rw [hlen']; simp [hσ₂, Lc], by simp [hσ₂, ha₁'], by simp [hσ₂, hout₁]⟩
  refine ⟨σ₃, _, r1.seq (r2.seq r3), ?_, hout₃⟩
  simp only [size_lit, size_var, size_add, size_bin, Expr.add_def]
  unfold heavyCost convCost
  rw [hlen']
  unfold Lc
  omega

/-! ### The guards -/

/-- The header: `R := t[0]; C := t[1]; tl := len - 2`. -/
def hdrT : Com :=
  .seq (.assign "R" (.get "t" (.lit 0)))
    (.seq (.assign "C" (.get "t" (.lit 1))) (.assign "tl" (.sub (.var "len") (.lit 2))))

/-- `(R - 1) * C < tl`, in a form the machine evaluates without a product. -/
def coverC : Cond :=
  .lt (.sub (.var "R") (.lit 1))
    (.div (.sub (.add (.var "tl") (.var "C")) (.lit 1)) (.var "C"))

/-- The word `W1`, printed. -/
def w1Com : Com :=
  .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 0))))

/-- The word `W0`, printed. -/
def w0Com : Com :=
  .seq (.write (.lit 1))
    (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.write (.lit 1)))))

/-- **The guarded program**, after the length has been read. -/
def gmainCom : Com :=
  .seq readT
    (.seq hdrT
      (.ite (.eq (.var "R") (.lit 0)) w1Com
        (.ite (.eq (.var "C") (.lit 0)) w0Com
          (.ite coverC
            (.ite (.lt (.var "len") (.var "C")) w0Com heavyCom)
            w0Com))))

/-- The cost of the guarded program. -/
noncomputable def gCost (x : List ℕ) : ℕ :=
  40 * x.length + 100 + (if Heavy x then heavyCost x else 0)

theorem hdrT_spec {x : List ℕ} {Lt : ℕ} (hLt : 2 ≤ Lt) (h0 : x.getD 0 0 < B)
    (h1 : x.getD 1 0 < B) (hlB : x.length < B) (h2B : 2 < B) :
    Spec B (fun σ => TabOK x Lt σ ∧ σ.vars "len" = x.length) hdrT
      (fun σ σ' => σ' = ((σ.setVar "R" (x.getD 0 0)).setVar "C" (x.getD 1 0)).setVar "tl"
        (x.length - 2)) 12 := by
  rintro σ ⟨htab, hl⟩
  have hlen := htab.length
  have hg0 : (σ.arrs "t").getD 0 0 = x.getD 0 0 := htab.getD (by omega)
  have hg1 : (σ.arrs "t").getD 1 0 = x.getD 1 0 := htab.getD (by omega)
  rw [List.getD_eq_getElem?_getD] at hg0 hg1
  unfold hdrT
  run_vcg
  all_goals (try simp [hl, hg0, hg1])
  all_goals (try omega)

/-- `(n-1) * m < tl` in a form the machine can evaluate without a product. -/
theorem cover_iff (n m tl : ℕ) (hm : 1 ≤ m) :
    (n - 1 < (tl + m - 1) / m) ↔ (n - 1) * m < tl := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hm]
  have : (n - 1 + 1) * m = (n - 1) * m + m := by ring
  rw [this]
  omega

/-- `coverC` evaluates to the comparison it spells. -/
theorem coverC_eval {σ : Env} (hB : 1 < B) (hn : σ.vars "R" < B) (htl : σ.vars "tl" < B)
    (hm : σ.vars "C" < B) (hsum : σ.vars "tl" + σ.vars "C" < B) :
    coverC.evalB B σ = some (decide (σ.vars "R" - 1 <
      (σ.vars "tl" + σ.vars "C" - 1) / σ.vars "C")) := by
  unfold coverC
  have h1 : (Expr.sub (.var "R") (.lit 1)).evalB B σ = some (σ.vars "R" - 1) :=
    RunStep.eval_sub B σ (.var "R") (.lit 1) (σ.vars "R") 1 (evalB_var hn)
      (evalB_lit (by omega)) (by omega)
  have h2 : (Expr.sub (.add (.var "tl") (.var "C")) (.lit 1)).evalB B σ =
      some (σ.vars "tl" + σ.vars "C" - 1) := by
    have hadd := RunStep.eval_add B σ (.var "tl") (.var "C") (σ.vars "tl") (σ.vars "C")
      (evalB_var htl) (evalB_var hm) hsum
    exact RunStep.eval_sub B σ _ (.lit 1) _ 1 hadd (evalB_lit (by omega)) (by omega)
  have h3 : (Expr.div (.sub (.add (.var "tl") (.var "C")) (.lit 1)) (.var "C")).evalB B σ =
      some ((σ.vars "tl" + σ.vars "C" - 1) / σ.vars "C") :=
    RunStep.eval_div B σ _ _ _ _ h2 (evalB_var hm)
      (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))
  exact evalB_condLt h1 h3

theorem eqLit_true {σ : Env} {y : String} {n : ℕ} (hy : σ.vars y < B) (hn : n < B)
    (h : σ.vars y = n) : (Cond.eq (.var y) (.lit n)).evalB B σ = some true := by
  rw [evalB_condEq (evalB_var hy) (evalB_lit hn), h]; simp

theorem eqLit_false {σ : Env} {y : String} {n : ℕ} (hy : σ.vars y < B) (hn : n < B)
    (h : σ.vars y ≠ n) : (Cond.eq (.var y) (.lit n)).evalB B σ = some false := by
  rw [evalB_condEq (evalB_var hy) (evalB_lit hn)]; simp [h]

theorem write_run {σ : Env} (v : ℕ) (hv : v < B) :
    Run B (.write (.lit v)) σ { σ with out := σ.out ++ [v] } 2 :=
  (Run.write (evalB_lit hv)).mono (by simp)

theorem ltVars_eval {σ : Env} {a b : String} (ha : σ.vars a < B) (hb : σ.vars b < B) :
    (Cond.lt (.var a) (.var b)).evalB B σ = some (decide (σ.vars a < σ.vars b)) :=
  evalB_condLt (evalB_var ha) (evalB_var hb)

theorem w1_run {σ : Env} (hB : 1 < B) : ∃ σ', Run B w1Com σ σ' 8 ∧ σ'.out = σ.out ++ W1 := by
  have h0 : 0 < B := by omega
  refine ⟨_, (write_run 0 h0).seq ((write_run 0 h0).seq ((write_run 0 h0).seq (write_run 0 h0))),
    ?_⟩
  simp [W1]

theorem w0_run {σ : Env} (hB : 1 < B) : ∃ σ', Run B w0Com σ σ' 10 ∧ σ'.out = σ.out ++ W0 := by
  have h0 : 0 < B := by omega
  refine ⟨_, (write_run 1 hB).seq ((write_run 0 h0).seq ((write_run 0 h0).seq
    ((write_run 0 h0).seq (write_run 1 hB)))), ?_⟩
  simp [W0]

/-! ### The value bound -/

/-- The largest entry of the word. -/
def mxE (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mxE {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mxE x := by
  induction x with
  | nil => simp at h
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem mxE_cases (x : List ℕ) : mxE x = 0 ∨ mxE x ∈ x := by
  induction x with
  | nil => left; simp [mxE]
  | cons a t ih =>
      rw [mxE, List.foldr_cons]
      change max a (mxE t) = 0 ∨ max a (mxE t) ∈ a :: t
      rcases max_choice a (mxE t) with h | h
      · rw [h]; right; exact List.mem_cons_self
      · rw [h]
        rcases ih with h0 | h0
        · left; exact h0
        · right; exact List.mem_cons_of_mem _ h0

theorem getD_le_mxE (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ mxE x := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · exact Nat.zero_le _
  · exact le_mxE (List.mem_of_getElem? h)

/-- The value bound the program runs under. -/
def Bof (x : List ℕ) : ℕ := 8 * (x.length + mxE x + 1) + 40

theorem Bof_hx (x : List ℕ) : ∀ v ∈ x, v < Bof x := fun v hv => by
  have := le_mxE hv
  unfold Bof; omega

/-- The array lengths declared to the run. -/
def extM (x : List ℕ) : String → ℕ := fun a =>
  if a = "t" then x.length + 2 + x.getD 0 0 * x.getD 1 0
  else if a = "a" then Lc x (x.getD 0 0) (x.getD 1 0)
  else 0

/-- The environment after the length prefix is read: all zero, arrays as declared, and `len`
holding the length of the word. -/
def lenEnv (ext : String → ℕ) (x : List ℕ) : Env := (initEnv ext x).setVar "len" x.length

/-! ### The run -/

theorem gmain_run (x : List ℕ) :
    ∃ σ' K, Run (Bof x) gmainCom (lenEnv (extM x) x) σ' K ∧ K ≤ gCost x ∧ σ'.out = conv x := by
  set B := Bof x with hBdef
  have hxB : ∀ v ∈ x, v < B := Bof_hx x
  have hB : 8 * x.length + 40 ≤ B := by unfold Bof at hBdef; omega
  have h0m := getD_le_mxE x 0
  have h1m := getD_le_mxE x 1
  have h0 : x.getD 0 0 < B := by unfold Bof at hBdef; omega
  have h1 : x.getD 1 0 < B := by unfold Bof at hBdef; omega
  have hlB : x.length < B := by omega
  set σ₀ := lenEnv (extM x) x with hσ₀
  set Lt := x.length + 2 + x.getD 0 0 * x.getD 1 0 with hLtdef
  have h0len : σ₀.vars "len" = x.length := by simp [hσ₀, lenEnv]
  have h0inp : σ₀.inp = x := rfl
  have h0out : σ₀.out = [] := rfl
  have h0arr : ∀ a, σ₀.arrs a = List.replicate (extM x a) 0 := fun a => rfl
  -- the read
  obtain ⟨σ₁, r1, ⟨-, htab₁, hlen₁⟩, hfv₁, hfa₁, -, hfo₁⟩ :=
    (readT_spec (B := B) (Lt := Lt) hxB hlB (by omega)).frame.run
      ⟨h0len, h0inp, by
        rw [h0arr, replicate_eq_arrOf]
        simp only [extM, ↓reduceIte]
        rw [← hLtdef]⟩
  have harr₁ : ∀ a, a ≠ "t" → σ₁.arrs a = σ₀.arrs a := fun a h =>
    hfa₁ a (by simp [readT, readTBody, Com.warrs, h])
  have hout₁ : σ₁.out = [] := by rw [hfo₁ (by simp [readT, readTBody, Com.NoWrite])]; exact h0out
  -- the header
  obtain ⟨σ₂, r2, hq₂⟩ := (hdrT_spec (B := B) (x := x) (Lt := Lt) (by omega) h0 h1 hlB
    (by omega)).run
    (σ := σ₁) ⟨htab₁, hlen₁⟩
  have hR₂ : σ₂.vars "R" = x.getD 0 0 := by rw [hq₂]; simp
  have hC₂ : σ₂.vars "C" = x.getD 1 0 := by rw [hq₂]; simp
  have htl₂ : σ₂.vars "tl" = x.length - 2 := by rw [hq₂]; simp
  have hlen₂ : σ₂.vars "len" = x.length := by rw [hq₂]; simpa using hlen₁
  have hout₂ : σ₂.out = [] := by rw [hq₂]; simpa using hout₁
  have hRB : σ₂.vars "R" < B := by rw [hR₂]; exact h0
  have hCB : σ₂.vars "C" < B := by rw [hC₂]; exact h1
  have htlB : σ₂.vars "tl" < B := by rw [htl₂]; omega
  have hB1 : 1 < B := by omega
  -- the guards
  by_cases hn0 : x.getD 0 0 = 0
  · have hc := eqLit_true (B := B) (σ := σ₂) (y := "R") (n := 0) hRB (by omega) (by rw [hR₂, hn0])
    have hH : ¬ Heavy x := fun h => by have := h.1; omega
    obtain ⟨σ₃, r3, hout₃⟩ := w1_run (B := B) (σ := σ₂) hB1
    refine ⟨_, _, r1.seq (r2.seq (Run.ite_true hc r3)), ?_, ?_⟩
    · simp only [Cond.size, Expr.size, gCost, if_neg hH]; omega
    · rw [hout₃, hout₂, conv, if_neg hH, if_pos hn0]; rfl
  have hc₁ := eqLit_false (B := B) (σ := σ₂) (y := "R") (n := 0) hRB (by omega)
    (by rw [hR₂]; exact hn0)
  by_cases hm0 : x.getD 1 0 = 0
  · have hc := eqLit_true (B := B) (σ := σ₂) (y := "C") (n := 0) hCB (by omega) (by rw [hC₂, hm0])
    have hH : ¬ Heavy x := fun h => by have := h.2.1; omega
    obtain ⟨σ₃, r3, hout₃⟩ := w0_run (B := B) (σ := σ₂) hB1
    refine ⟨_, _, r1.seq (r2.seq (Run.ite_false hc₁ (Run.ite_true hc r3))), ?_, ?_⟩
    · simp only [Cond.size, Expr.size, gCost, if_neg hH]; omega
    · rw [hout₃, hout₂, conv, if_neg hH, if_neg hn0]; rfl
  have hc₂ := eqLit_false (B := B) (σ := σ₂) (y := "C") (n := 0) hCB (by omega)
    (by rw [hC₂]; exact hm0)
  have hev := coverC_eval (σ := σ₂) hB1 hRB htlB hCB (by rw [htl₂, hC₂]; unfold Bof at hBdef; omega)
  by_cases hcov : (x.getD 0 0 - 1) * x.getD 1 0 < x.length - 2
  · have hc : coverC.evalB B σ₂ = some true := by
      rw [hev, hR₂, hC₂, htl₂]
      simp only [Option.some.injEq, decide_eq_true_eq]
      exact (cover_iff _ _ _ (by omega)).2 hcov
    have hlen : (Cond.lt (.var "len") (.var "C")).evalB B σ₂ =
        some (decide (x.length < x.getD 1 0)) := by
      rw [ltVars_eval (by rw [hlen₂]; omega) hCB, hlen₂, hC₂]
    by_cases hml : x.getD 1 0 ≤ x.length
    · -- the heavy path
      have hH : Heavy x := ⟨by omega, by omega, hcov, hml⟩
      have hf : (Cond.lt (.var "len") (.var "C")).evalB B σ₂ = some false := by
        rw [hlen, decide_eq_false (by omega)]
      have hHC := HC.of_heavy hH
      have htab₂ : TabOK x Lt σ₂ := htab₁.congr (by simp only [hq₂, arrs_setVar])
      have harr₂ : ∀ a, a ≠ "t" → σ₂.arrs a = List.replicate (extM x a) 0 := fun a h => by
        rw [hq₂]; simp only [arrs_setVar]; rw [harr₁ a h, h0arr]
      obtain ⟨σ₃, K₃, r3, hK₃, hout₃⟩ := heavy_run (B := B) hHC hB hxB (Lt := Lt) (by omega)
        hR₂ hC₂ htab₂ (by rw [harr₂ _ (by decide)]; simp [extM]) hout₂
      refine ⟨σ₃, _, r1.seq (r2.seq (Run.ite_false hc₁ (Run.ite_false hc₂ (Run.ite_true hc
        (Run.ite_false hf r3))))), ?_, ?_⟩
      · simp only [Cond.size, Expr.size, gCost, coverC, if_pos hH]
        omega
      · rw [hout₃, conv, if_pos hH]; rfl
    · have hH : ¬ Heavy x := fun h => hml h.2.2.2
      have ht : (Cond.lt (.var "len") (.var "C")).evalB B σ₂ = some true := by
        rw [hlen, decide_eq_true (by omega)]
      obtain ⟨σ₃, r3, hout₃⟩ := w0_run (B := B) (σ := σ₂) hB1
      refine ⟨_, _, r1.seq (r2.seq (Run.ite_false hc₁ (Run.ite_false hc₂ (Run.ite_true hc
        (Run.ite_true ht r3))))), ?_, ?_⟩
      · simp only [Cond.size, Expr.size, gCost, coverC, if_neg hH]; omega
      · rw [hout₃, hout₂, conv, if_neg hH, if_neg hn0]; rfl
  · have hH : ¬ Heavy x := fun h => hcov h.2.2.1
    have hc : coverC.evalB B σ₂ = some false := by
      rw [hev, hR₂, hC₂, htl₂]
      simp only [Option.some.injEq, decide_eq_false_iff_not]
      rw [cover_iff _ _ _ (by omega)]
      exact hcov
    obtain ⟨σ₃, r3, hout₃⟩ := w0_run (B := B) (σ := σ₂) hB1
    refine ⟨_, _, r1.seq (r2.seq (Run.ite_false hc₁ (Run.ite_false hc₂ (Run.ite_false hc r3)))),
      ?_, ?_⟩
    · simp only [Cond.size, Expr.size, gCost, coverC, if_neg hH]; omega
    · rw [hout₃, hout₂, conv, if_neg hH, if_neg hn0]; rfl

/-! ### The layout and the transfer -/

/-- The whole program: read the length prefix, then run the guarded conversion. -/
def pcom : Com := .seq (.read "len") gmainCom

/-- The layout: every scalar and array of the program. -/
def layout : Layout :=
  ⟨["len", "rt", "v", "R", "C", "tl", "V", "p", "q", "r", "c", "i2", "lc", "wr"], ["t", "a"], 8⟩

theorem pcom_ok : Com.Ok layout pcom := by
  simp [pcom, gmainCom, readT, readTBody, hdrT, coverC, heavyCom, convCom, rowLoop, rowBody,
    colBody, colThen, tailLoop, tailBody, outCom, outLoop, outBody, w1Com, w0Com, layout,
    Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem const_eq : layout.const = 10 := by simp [Layout.const]

/-- **The program on the length-prefixed input.** -/
theorem pcom_run (x : List ℕ) :
    ∃ σ', Run (Bof x) pcom (initEnv (extM x) (x.length :: x)) σ' (1 + gCost x) ∧
      σ'.out = conv x := by
  obtain ⟨σ', K, hr, hK, hout⟩ := gmain_run x
  have h1 : Run (Bof x) (.read "len") (initEnv (extM x) (x.length :: x))
      (lenEnv (extM x) x) 1 := Run.read (by rfl)
  exact ⟨σ', (h1.seq hr).mono (by omega), hout⟩

theorem solves (x : List ℕ) :
    Solves layout pcom {z | z = x.length :: x} (fun _ => conv x) (fun _ => Bof x)
      (fun _ => 1 + gCost x) where
  ok := pcom_ok
  inp := by
    intro z hz v hv
    rw [hz] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bof; omega
    · exact Bof_hx x v hv'
  run := by
    intro z hz
    rw [hz]
    obtain ⟨σ', hr, ho⟩ := pcom_run x
    exact ⟨extM x, σ', hr, ho⟩

lemma bof_fit (x : List ℕ) : max (Bof x) (layout.span (Bof x)) ≤ 2 ^ (bitSize x + 10) := by
  have hlen := length_le_bitSize x
  have hmx : mxE x < 2 ^ (bitSize x + 1) := by
    rcases mxE_cases x with h | h
    · rw [h]; exact Nat.pos_of_ne_zero (by positivity)
    · exact mem_lt_two_pow_bitSize_add_one h
  have hs : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have e1 : (2 : ℕ) ^ (bitSize x + 1) = 2 * 2 ^ bitSize x := by ring
  have e2 : (2 : ℕ) ^ (bitSize x + 10) = 1024 * 2 ^ bitSize x := by ring
  simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff, Bof]
  constructor <;> omega

lemma time_bound (x : List ℕ) :
    10 * (1 + gCost x) + 1 ≤ 30000 * (bitSize x + 1) ^ 3 := by
  have hlen := length_le_bitSize x
  have hu3 : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hcube : x.length + 1 ≤ (x.length + 1) ^ 3 := by
    have : (x.length + 1) ^ 3 = (x.length + 1) * (x.length + 1) * (x.length + 1) := by ring
    rw [this]
    nlinarith [Nat.zero_le x.length]
  have hH : (if Heavy x then heavyCost x else 0) ≤ heavyCost x := by
    split_ifs <;> omega
  unfold gCost
  unfold heavyCost at hH ⊢
  generalize (if Heavy x then 300 * x.length + 300 else 0) = H at hH ⊢
  generalize (x.length + 1) ^ 3 = Q at hu3 hcube ⊢
  generalize (bitSize x + 1) ^ 3 = Q' at hu3 ⊢
  omega

theorem prog_runs (w : ℕ) (x : List ℕ) (hw : bitSize x + 11 ≤ w) :
    ∃ t ≤ 30000 * (bitSize x + 1) ^ 3, RunsTo w (compileProgram layout pcom) (x.length :: x)
      (conv x) t := by
  have hfit : layout.FitsWords (Bof x) w := by
    refine fitsWords_of_max_le (by unfold Bof; omega) ?_
    exact (bof_fit x).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h := computesInTime_of_solves (w := w) (T := fun _ => 10 * (1 + gCost x) + 1)
    (solves x) (fun z hz => hfit) (fun z hz => by rw [const_eq])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, ht.trans (time_bound x), hrun⟩

/-- **The guarded conversion is a polynomial-time word RAM computation.** -/
theorem conv_ramPolytime : RamPolytime conv := by
  refine Lax117284Proofs.Machine.RamBridge2.ramPolytime_of_wordlen (d := 1) (K := 10)
    (prog := compileProgram layout pcom)
    (Polynomial.C 30000 * (Polynomial.X + Polynomial.C 1) ^ 3) le_rfl ?_ ?_
  · intro x v hv
    have hlen := length_le_bitSize x
    have hs : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
    have e2 : (2 : ℕ) ^ (1 * bitSize x + 10) = 1024 * 2 ^ bitSize x := by ring
    rw [e2]
    unfold conv at hv
    split_ifs at hv with hH h0
    · have hHC := HC.of_heavy hH
      have h1 := mem_csrP_le x _ _ hv
      have h2 := hHC.hE
      have := hHC.Rle
      have := hHC.Cle
      omega
    · simp [W1] at hv; omega
    · simp [W0] at hv; omega
  · intro w x hw
    obtain ⟨t, ht, hr⟩ := prog_runs w x (by omega)
    refine ⟨t, ?_, hr⟩
    simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add] using ht

end Lax117284Proofs.Machine.MatchRam
