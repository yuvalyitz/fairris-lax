import Lax117284Proofs.Machine.ClMainOk
import Lax117284Proofs.Injectivity

/-! ### `Lax117284Proofs.Machine.ClRedProg` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.ClRedSpec` -/

section
/-!
The reduction's program, whole: on the word of a uniform instance it prints the word of the
reduction, within the bound `BR` on its values and the cost `KR`.
-/

namespace Lax117284Proofs.Machine.ClRed

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax808846Proofs.Transfer
open Lax808846.Ram
open Lax117284Proofs.Machine.ClSim (V lit asg)
open Lax117284Proofs.Machine.ClBuild Lax117284Proofs.Machine.ClMain
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Lax117284.InstanceEncoding

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The cost of the inner branch: eight writes without a client, else the builder and the
printing loop. -/
def bK (I : Instance) : ℕ :=
  if I.clients = 0 then 8 else buildCost I + (11 * zLen I.clients + 6)

/-- The cost of the reduction on the word of `I`. -/
def redK (I : Instance) (x : List ℕ) : ℕ :=
  (24 * x.length + 60) + (20 + (4 + (8 + (4 + bK I))))

/-- The builder and the printing loop: the word of the integer program is out. -/
theorem buildOut_spec (h : Bh I x k B) :
    Spec B (F0 [] 1 I x k) (.seq buildCom outCom)
      (fun _ σ' => σ'.out = zList I.clients I.days k (cntN I))
      (buildCost I + (11 * zLen I.clients + 6)) := by
  set Z := zList I.clients I.days k (cntN I) with hZdef
  have hZl : Z.length = zLen I.clients := zList_length I k
  have hn' : x[0]?.getD 0 = I.clients := by
    simpa [List.getD_eq_getElem?_getD] using ClientsWord.x0 h.enc
  have hm' : x[1]?.getD 0 = I.days := by
    simpa [List.getD_eq_getElem?_getD] using ClientsWord.x1 h.enc
  have hmB := h.m_lt
  have hzB := h.hzB
  have hE : ∀ v ∈ Z, v < B := fun v hv => by
    have := mem_zList_le I k hv; omega
  have hb : Spec B (F0 [] 1 I x k) buildCom
      (fun _ σ' => σ'.vars "zl" = zLen I.clients ∧ σ'.arrs "z" = Z ∧ σ'.out = []) (buildCost I) := by
    refine Spec.post (Spec.pre (buildCom_spec h) ?_) ?_
    · rintro σ ⟨hC, hZ0, hi, ho⟩
      refine ⟨hC, ?_, ?_, ?_⟩
      · rw [hZ0 "cnt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "okt" (by decide)]; simp [extF, hn', hm']
      · rw [hZ0 "z" (by decide)]; simp [extF, hn', hm']
    · rintro σ σ' ⟨hC, hZ0, hi, ho⟩ ⟨hC1, hS1, hz1, hA⟩
      exact ⟨hS1.zl, hz1, by rw [hA.2.2.1, ho]⟩
  have ho := outCom_spec (B := B) (Z := Z) (by rw [hZl]; exact hzB) hE
  refine Spec.mono (Spec.seq hb ho (fun _ _ _ h => ⟨by rw [h.1, hZl], h.2.1, h.2.2⟩)
    (fun _ _ _ _ _ h => h)) ?_
  rw [hZl]

/-- **The reduction's program prints the word of the reduction.** The bound `B` must admit the
word, and the word of the integer program when it is built. -/
theorem redCom_spec (hdec : EncodesUniform x I k) (hL : x.length < B) (hX : ∀ v ∈ x, v < B)
    (hzB : ¬ (I.days < k ∧ 0 < I.clients) → 0 < I.clients → zLen I.clients < B) :
    Spec B (M0 [] 1 x) redCom (fun _ σ' => σ'.out = fI I k) (redK I x) := by
  have hl := ClientsWord.len_eq hdec
  have hg : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  have hnB : I.clients < B := by rw [← ClientsWord.x0 hdec]; exact hg 0
  have hmB : I.days < B := by rw [← ClientsWord.x1 hdec]; exact hg 1
  have hkB : k < B := by rw [← ClientsWord.xk hdec]; exact hg _
  have hB1 : 1 < B := by omega
  have hr := read_spec (P := []) (c1 := 1) hdec hL hX
  have hsc := scCom_spec (P := []) (c1 := 1) (x := x) hnB hmB hkB hB1
  -- the precondition of the outer conditional
  set P1 : Env → Prop := fun σ => F0 [] 1 I x k σ ∧
    σ.vars "sc" = if I.days < k ∧ 0 < I.clients then 1 else 0 with hP1
  have hdef1 : ∀ σ, P1 σ → ∃ v, (Cond.lt (lit 0) (V "sc")).evalB B σ = some v :=
    fun σ hσ => cond0_def (by omega) (by rw [hσ.2]; split_ifs <;> omega)
  have hdef2 : ∀ σ, F0 [] 1 I x k σ → ∃ v, (Cond.lt (lit 0) (V "n")).evalB B σ = some v :=
    fun σ hσ => cond0_def (by omega) (by rw [hσ.1.n]; exact hnB)
  have hsz1 : (Cond.lt (lit 0) (V "sc")).size = 3 := by simp [lit, V]
  have hsz2 : (Cond.lt (lit 0) (V "n")).size = 3 := by simp [lit, V]
  -- the rejecting branch
  have hT : Spec B (fun σ => P1 σ ∧ (Cond.lt (lit 0) (V "sc")).evalB B σ = some true) rejCom
      (fun _ σ' => σ'.out = fI I k) (8 + (4 + bK I)) := by
    by_cases hc : I.days < k ∧ 0 < I.clients
    · refine Spec.mono (Spec.conseq (rejCom_spec [] hB1) (fun σ hσ => hσ.1.1.2.2.2) ?_ le_rfl)
        (by omega)
      intro σ σ' _ h; rw [h]; simp [fI, hc]
    · rintro σ ⟨⟨hF, hsc'⟩, hev⟩
      have := cond0_true hev
      rw [hsc', if_neg hc] at this
      exact absurd this (lt_irrefl 0)
  -- the building branch, with its own conditional on the number of clients
  have hF : Spec B (fun σ => P1 σ ∧ (Cond.lt (lit 0) (V "sc")).evalB B σ = some false)
      (.ite (.lt (lit 0) (V "n")) (.seq buildCom outCom) zeroCom)
      (fun _ σ' => σ'.out = fI I k) (4 + bK I) := by
    by_cases hc : I.days < k ∧ 0 < I.clients
    · rintro σ ⟨⟨hF, hsc'⟩, hev⟩
      have := cond0_false hev
      rw [hsc', if_pos hc] at this
      exact absurd this one_ne_zero
    · have hfI : fI I k = zList I.clients I.days k (cntN I) := by simp [fI, hc]
      refine Spec.pre ?_ (fun σ hσ => hσ.1.1)
      by_cases hn0 : I.clients = 0
      · have hbK : bK I = 8 := by simp [bK, hn0]
        rw [hbK]
        have hz : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some false) zeroCom
            (fun _ σ' => σ'.out = fI I k) 8 := by
          refine Spec.conseq (zeroCom_spec [] hB1 hmB) (fun σ hσ => ⟨hσ.1.2.2.2, hσ.1.1.m⟩) ?_ le_rfl
          intro σ σ' _ h
          rw [h, hfI, zList_zero hn0]; simp
        have hb : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some true) (.seq buildCom outCom)
            (fun _ σ' => σ'.out = fI I k) 8 := by
          rintro σ ⟨hF0, hev⟩
          have := cond0_true hev
          rw [hF0.1.n, hn0] at this
          exact absurd this (lt_irrefl 0)
        have hite := Spec.ite hdef2 hb hz
        rw [hsz2] at hite
        exact hite
      · have hbK : bK I = buildCost I + (11 * zLen I.clients + 6) := by simp [bK, hn0]
        rw [hbK]
        have hb : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some true) (.seq buildCom outCom)
            (fun _ σ' => σ'.out = fI I k) (buildCost I + (11 * zLen I.clients + 6)) := by
          refine Spec.conseq (buildOut_spec ⟨hdec, hL, hX, hzB hc (by omega)⟩)
            (fun σ hσ => hσ.1) ?_ le_rfl
          intro σ σ' _ h; rw [h, hfI]
        have hz : Spec B (fun σ => F0 [] 1 I x k σ ∧
            (Cond.lt (lit 0) (V "n")).evalB B σ = some false) zeroCom
            (fun _ σ' => σ'.out = fI I k) (buildCost I + (11 * zLen I.clients + 6)) := by
          rintro σ ⟨hF0, hev⟩
          have := cond0_false hev
          rw [hF0.1.n] at this
          exact absurd this hn0
        have hite := Spec.ite hdef2 hb hz
        rw [hsz2] at hite
        exact hite
  have hite := Spec.ite (P := P1) hdef1 hT (Spec.mono hF (by omega))
  rw [hsz1] at hite
  unfold redCom
  refine Spec.mono (Spec.seq hr (Spec.seq hsc hite (fun _ _ _ h => h) (fun _ _ _ _ _ h => h))
    (fun _ _ _ h => h.1) (fun _ _ _ _ _ h => h)) ?_
  unfold redK; omega

/-! ### The value bound and the cost, as functions of the word -/

/-- The bound on the values of the reduction's program: the word and its image, each with its
length and its largest entry. -/
noncomputable def BR (x : List ℕ) : ℕ :=
  (x.length + Mx x + 1) + ((fRed x).length + Mx (fRed x) + 1)

/-- The cost of the reduction's program on the word `x`. -/
noncomputable def KR (x : List ℕ) : ℕ := redK (decode x.dropLast) x

/-- **The reduction's program solves the reduction** on every word of a uniform instance. -/
theorem solves : Solves layoutR redCom UniformInstances fRed BR KR where
  ok := layoutR_ok
  inp := by
    rintro x ⟨I, k, hdec⟩ v hv
    have := le_Mx hv
    unfold BR; omega
  run := by
    rintro x ⟨I, k, hdec⟩
    have hL : x.length < BR x := by unfold BR; omega
    have hX : ∀ v ∈ x, v < BR x := fun v hv => by
      have := le_Mx hv; unfold BR; omega
    have hzB : ¬ (I.days < k ∧ 0 < I.clients) → 0 < I.clients → zLen I.clients < BR x := by
      intro hc _
      unfold BR
      rw [fRed_eq hdec]
      simp only [fI, if_neg hc, zList_length]
      omega
    refine ⟨extF [] 1 x, ?_⟩
    obtain ⟨σ', hrun, hout⟩ :=
      redCom_spec hdec hL hX hzB (initEnv (extF [] 1 x) x) ⟨rfl, rfl, fun a => rfl⟩
    refine ⟨σ', ?_, ?_⟩
    · unfold KR; rw [decode_dropLast hdec]; exact hrun
    · rw [hout, fRed_eq hdec]

end Lax117284Proofs.Machine.ClRed

end
