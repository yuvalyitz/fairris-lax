import Lax117284Proofs.Machine.ClMainOk
import Lax117284Proofs.Injectivity

/-!
The program of the reduction of Theorem 4's third bullet, and its pieces: read the word; when the
parameter exceeds the number of days and there is a client, print a fixed infeasible program; when
there is no client, print the (feasible) program of the instance directly; otherwise build the
word of the integer program in the array `z` and print it.
-/

namespace Lax117284Proofs.Machine.ClRed

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg)
open Lax117284Proofs.Machine.ClBuild Lax117284Proofs.Machine.ClMain
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Lax117284.InstanceEncoding

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The fixed infeasible program `0 · x = 1`: one variable, one constraint. -/
def rejCom : Com :=
  .seq (.write (lit 1)) (.seq (.write (lit 1)) (.seq (.write (lit 0)) (.write (lit 1))))

/-- The program of an instance without clients, `1 · x = m`. -/
def zeroCom : Com :=
  .seq (.write (lit 1)) (.seq (.write (lit 1)) (.seq (.write (lit 1)) (.write (V "m"))))

/-- One entry of `z` to the output, and the step. -/
def outBody : Com := .seq (.write (.get "z" (V "i"))) (asg "i" (add (V "i") (lit 1)))

/-- The word held in `z` to the output. -/
def outCom : Com := .seq (asg "i" (lit 0)) (.while (.lt (V "i") (V "zl")) outBody)

/-- The reduction. -/
def redCom : Com := .seq readCom (.seq (asg "sc" scE)
  (.ite (.lt (lit 0) (V "sc")) rejCom
    (.ite (.lt (lit 0) (V "n")) (.seq buildCom outCom) zeroCom)))

/-- The word the reduction produces on the instance `I` with the parameter `k`. -/
def fI (I : Instance) (k : ℕ) : List ℕ :=
  if I.days < k ∧ 0 < I.clients then [1, 1, 0, 1] else zList I.clients I.days k (cntN I)

/-- The reduction, as a map on words. -/
noncomputable def fRed (x : List ℕ) : List ℕ :=
  if x.getD 1 0 < parameter x ∧ 0 < x.getD 0 0 then [1, 1, 0, 1]
  else zList (x.getD 0 0) (x.getD 1 0) (parameter x) (cntN (decode x.dropLast))

variable {B k : ℕ} {I : Instance} {x : List ℕ}

theorem decode_dropLast (h : EncodesUniform x I k) : decode x.dropLast = I := by
  obtain ⟨y, rfl, hy⟩ := h
  have h1 : (y ++ [k]).dropLast = y := by simp
  rw [h1, Lax117284Proofs.Injectivity.decode_eq hy]

theorem parameter_eq (h : EncodesUniform x I k) : parameter x = k := by
  obtain ⟨y, rfl, hy⟩ := h
  simp [parameter]

theorem fRed_eq (h : EncodesUniform x I k) : fRed x = fI I k := by
  have h0 := ClientsWord.x0 h
  have h1 := ClientsWord.x1 h
  have hd := decode_dropLast h
  have hp := parameter_eq h
  unfold fRed fI
  rw [h0, h1, hd, hp]

/-- The word of an instance without clients: one variable, one constraint `1 · x = m`. -/
theorem zList_zero (hn : I.clients = 0) :
    zList I.clients I.days k (cntN I) = [1, 1, 1, I.days] := by
  have hc : cntN I 0 = I.days := by
    have := sum_cntN I
    rw [hn] at this
    simpa [nT] using this
  rw [hn]
  have hz : zLen 0 = 4 := by decide
  simp only [zList, hz]
  simp [List.range_succ, zFunRaw, coefRaw, rhsRaw, indepB, nT, nZ, nV, nN, nM, hc]

theorem fI_length (I : Instance) (k : ℕ) : 2 ≤ (fI I k).length := by
  unfold fI
  split_ifs
  · simp
  · rw [zList_length]; exact (sizes_le_zLen _).2.2.2.2.2.2.2

/-! ### The pieces that print -/

theorem write_lit0 (o : List ℕ) {v : ℕ} (hv : v < B) :
    Spec B (fun σ => σ.out = o) (.write (lit v)) (fun _ σ' => σ'.out = o ++ [v]) 2 :=
  (Spec.write (P := fun σ => σ.out = o) (f := fun _ => v) (fun σ _ => evalB_lit hv)).post
    (fun σ σ' hσ h => by subst h; simp [hσ])

theorem write_lit (o : List ℕ) (y : String) (u : ℕ) {v : ℕ} (hv : v < B) :
    Spec B (fun σ => σ.out = o ∧ σ.vars y = u) (.write (lit v))
      (fun _ σ' => σ'.out = o ++ [v] ∧ σ'.vars y = u) 2 :=
  (Spec.write (P := fun σ => σ.out = o ∧ σ.vars y = u) (f := fun _ => v)
    (fun σ _ => evalB_lit hv)).post
    (fun σ σ' hσ h => by subst h; exact ⟨by simp [hσ.1], hσ.2⟩)

theorem write_var (o : List ℕ) (y : String) {u : ℕ} (hu : u < B) :
    Spec B (fun σ => σ.out = o ∧ σ.vars y = u) (.write (V y))
      (fun _ σ' => σ'.out = o ++ [u]) 2 :=
  (Spec.write (P := fun σ => σ.out = o ∧ σ.vars y = u) (f := fun _ => u)
    (fun σ hσ => by
      have := evalB_var (B := B) (x := y) (σ := σ) (by rw [hσ.2]; exact hu)
      rwa [hσ.2] at this)).post
    (fun σ σ' hσ h => by subst h; simp [hσ.1])

theorem rejCom_spec (o : List ℕ) (h1 : 1 < B) :
    Spec B (fun σ => σ.out = o) rejCom (fun _ σ' => σ'.out = o ++ [1, 1, 0, 1]) 8 := by
  have h0 : 0 < B := by omega
  have s := Spec.seq (write_lit0 o h1) (Spec.seq (write_lit0 (o ++ [1]) h1)
    (Spec.seq (write_lit0 (o ++ [1] ++ [1]) h0) (write_lit0 (o ++ [1] ++ [1] ++ [0]) h1)
      (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  refine Spec.post s ?_
  intro σ σ' _ h; rw [h]; simp

theorem zeroCom_spec (o : List ℕ) {m : ℕ} (h1 : 1 < B) (hm : m < B) :
    Spec B (fun σ => σ.out = o ∧ σ.vars "m" = m) zeroCom
      (fun _ σ' => σ'.out = o ++ [1, 1, 1, m]) 8 := by
  have s := Spec.seq (write_lit o "m" m h1) (Spec.seq (write_lit (o ++ [1]) "m" m h1)
    (Spec.seq (write_lit (o ++ [1] ++ [1]) "m" m h1) (write_var (o ++ [1] ++ [1] ++ [1]) "m" hm)
      (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)) (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
  refine Spec.post s ?_
  intro σ σ' _ h; rw [h]; simp

/-- The invariant of the printing loop: the entries before `i` are out. -/
def OInv (Z : List ℕ) (σ : Env) : Prop :=
  σ.vars "zl" = Z.length ∧ σ.arrs "z" = Z ∧ σ.vars "i" ≤ Z.length ∧ σ.out = Z.take (σ.vars "i")

theorem outBody_spec {Z : List ℕ} (hZ : Z.length < B) (hE : ∀ v ∈ Z, v < B) :
    Spec B (fun σ => OInv Z σ ∧ σ.vars "i" < Z.length) outBody
      (fun σ σ' => OInv Z σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 7 := by
  have hw : Spec B (fun σ => OInv Z σ ∧ σ.vars "i" < Z.length) (.write (.get "z" (V "i")))
      (fun σ σ' => σ' = { σ with out := σ.out ++ [Z.getD (σ.vars "i") 0] }) 3 := by
    refine Spec.write (f := fun σ => Z.getD (σ.vars "i") 0) ?_
    rintro σ ⟨⟨hzl, hz, hle, hout⟩, hlt⟩
    have hmem : Z.getD (σ.vars "i") 0 ∈ Z := by
      rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
    refine evalB_get (k := σ.vars "i") (evalB_var (by omega)) ?_ (hE _ hmem)
    rw [hz, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  have ha : Spec B (fun σ => σ.vars "i" < Z.length) (asg "i" (add (V "i") (lit 1)))
      (fun σ σ' => σ' = σ.setVar "i" (σ.vars "i" + 1)) 4 := by
    refine Spec.assign (f := fun σ => σ.vars "i" + 1) ?_
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
    rw [List.getD_eq_getElem _ _ hlt, List.take_succ_eq_append_getElem hlt]

theorem outCom_spec {Z : List ℕ} (hZ : Z.length < B) (hE : ∀ v ∈ Z, v < B) :
    Spec B (fun σ => σ.vars "zl" = Z.length ∧ σ.arrs "z" = Z ∧ σ.out = []) outCom
      (fun _ σ' => σ'.out = Z) (11 * Z.length + 6) := by
  have h := Spec.forRangeZero (B := B) (c := outBody) "i" "zl" (OInv Z) Z.length 7 hZ
    (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.1) (outBody_spec hZ hE)
  refine Spec.conseq h ?_ ?_ le_rfl
  · rintro σ ⟨h1, h2, h3⟩
    exact ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2, by simp [Env.setVar],
      by simp [Env.setVar, h3]⟩
  · rintro σ σ' _ ⟨⟨-, -, -, hout⟩, hi⟩
    rw [hout, hi, List.take_length]

/-! ### The layout -/

theorem fine_rej : Fine rejCom := by unfold Fine; decide +kernel
theorem fine_zero : Fine zeroCom := by unfold Fine; decide +kernel
theorem fine_out : Fine outCom := by unfold Fine; decide +kernel
theorem eD_n : eD (condExpr (.lt (lit 0) (V "n"))) ≤ 12 := by decide +kernel

theorem fine_red : Fine redCom :=
  fine_read.seq (fine_sc.seq (Fine.ite eD_sc (by decide +kernel) fine_rej
    (Fine.ite eD_n (by decide +kernel) (fine_build.seq fine_out) fine_zero)))

/-- The layout of the reduction: the scalars it mentions, the ten arrays of the main program (of
which it uses `X`, `cnt`, `okt` and `z`), twelve temporaries. -/
def layoutR : Layout := ⟨cS redCom, arrs10, 12⟩

theorem layoutR_ok : Com.Ok layoutR redCom :=
  com_ok layoutR redCom (fun y h => h) fine_red.1 fine_red.2

end Lax117284Proofs.Machine.ClRed
