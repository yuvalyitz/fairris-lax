import Lax117284Proofs.Bipartite.Ram2.SymmDeg

/-!
The symmetrized word built in `a`, first half: the header, the offsets `offS` by prefix sums of
the degrees, the last entry, and the cursors `pos` at the offsets (`FixedA`, `PosOK`).
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

theorem offS_le_n (x : List ℕ) (i : ℕ) : offS x i ≤ offS x (nw x) := by
  rcases Nat.lt_or_ge i (nw x) with h | h
  · exact offS_mono x (le_of_lt h)
  · rw [offS_of_ge x h]

theorem deg_le_n (x : List ℕ) {l : ℕ} (hl : l < nw x) : deg x l ≤ offS x (nw x) := by
  have h1 := offS_succ_of_lt x hl
  have h2 := offS_le_n x (l + 1)
  omega

/-- The owner of a slot of the target array. -/
theorem exists_owner (x : List ℕ) {s : ℕ} (hs : s < offS x (nw x)) :
    ∃ l < nw x, offS x l ≤ s ∧ s < offS x (l + 1) := by
  have key : ∀ i ≤ nw x, s < offS x i → ∃ l < i, offS x l ≤ s ∧ s < offS x (l + 1) := by
    intro i
    induction i with
    | zero => intro _ h; rw [offS_zero] at h; omega
    | succ i ih =>
      intro hi h
      rcases Nat.lt_or_ge s (offS x i) with h' | h'
      · obtain ⟨l, hl, h1, h2⟩ := ih (by omega) h'
        exact ⟨l, by omega, h1, h2⟩
      · exact ⟨i, by omega, h', h⟩
  exact key _ le_rfl hs

/-! ### The fixed cells of `a` -/

/-- The header, the offsets and the last entry of the symmetrized word, in `a`. -/
structure FixedA (x : List ℕ) (σ : Env) : Prop where
  len : (σ.arrs "a").length = x.length
  h0 : (σ.arrs "a").getD 0 0 = Vw x
  h1 : (σ.arrs "a").getD 1 0 = x.getD 1 0
  off : ∀ i ≤ Vw x, (σ.arrs "a").getD (2 + i) 0 = offS x i
  last : (σ.arrs "a").getD (3 + Vw x + 2 * x.getD 1 0) 0 = nw x

theorem FixedA.congr {x : List ℕ} {σ σ' : Env} (h : FixedA x σ) (ha : σ'.arrs "a" = σ.arrs "a") :
    FixedA x σ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [ha]
  exacts [h.len, h.h0, h.h1, h.off, h.last]

/-- A store into the target area keeps the fixed cells. -/
theorem FixedA.setTgt {x : List ℕ} {σ : Env} (hw : WellFormed x) (h : FixedA x σ) {s v : ℕ}
    (hs : s < 2 * x.getD 1 0) : FixedA x (σ.setArr "a" (3 + Vw x + s) v) := by
  have hlen := wf_len hw
  refine ⟨by simp [h.len], ?_, ?_, fun i hi => ?_, ?_⟩
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.h0
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.h1
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.off i hi
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h.last

/-! ### The prefix sums -/

/-- `if i < n then a[3 + i] := a[2 + i] + deg[i] else a[3 + i] := a[2 + i]; i := i + 1`. -/
def prefixThen : Com :=
  .store "a" (.add (.lit 3) (.var "i"))
    (.add (.get "a" (.add (.lit 2) (.var "i"))) (.get "deg" (.var "i")))

def prefixElse : Com := .store "a" (.add (.lit 3) (.var "i")) (.get "a" (.add (.lit 2) (.var "i")))

def prefixBody : Com :=
  .seq (.ite (.lt (.var "i") (.var "n")) prefixThen prefixElse)
    (.assign "i" (.add (.var "i") (.lit 1)))

/-- The header, the offsets by prefix sums, the last entry. -/
def prefixCom : Com :=
  .seq (.store "a" (.lit 0) (.var "V"))
    (.seq (.store "a" (.lit 1) (.var "E"))
      (.seq (.store "a" (.lit 2) (.lit 0))
        (.seq (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "V")) prefixBody))
          (.store "a" (.add (.add (.lit 3) (.var "V")) (.mul (.lit 2) (.var "E"))) (.var "n")))))

/-- The degrees in `deg`. -/
def DegOK (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "deg").length = nw x ∧ ∀ l < nw x, (σ.arrs "deg").getD l 0 = deg x l

/-- The invariant of the prefix loop. -/
structure PreInv (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  deg : DegOK x σ
  len : (σ.arrs "a").length = x.length
  h0 : (σ.arrs "a").getD 0 0 = Vw x
  h1 : (σ.arrs "a").getD 1 0 = x.getD 1 0
  i_le : σ.vars "i" ≤ Vw x
  off : ∀ i ≤ σ.vars "i", (σ.arrs "a").getD (2 + i) 0 = offS x i

theorem prefixBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => PreInv x σ ∧ σ.vars "i" < Vw x) prefixBody
      (fun σ σ' => PreInv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 24 := by
  rintro σ ⟨hPre, hlt⟩
  have hb := hPre.base
  obtain ⟨hlenD, hdeg⟩ := hPre.deg
  have hlen := hPre.len
  have h0 := hPre.h0
  have h1 := hPre.h1
  have hi := hPre.i_le
  have hoff := hPre.off
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hn := hb.n
  set i := σ.vars "i" with hidef
  have hie : (Expr.var "i").evalB B σ = some i := RunStep.eval_var B σ "i" (by omega)
  have hne : (Expr.var "n").evalB B σ = some (nw x) := by
    rw [← hn]; exact RunStep.eval_var B σ "n" (by rw [hn]; have := wf_nV hw; omega)
  have hidx : (Expr.add (.lit 3) (.var "i")).evalB B σ = some (3 + i) :=
    RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hie (by omega)
  have hoffi : (σ.arrs "a").getD (2 + i) 0 = offS x i := hoff i le_rfl
  have hoffB : offS x i < B := by have := offS_le_n x i; omega
  have hread : (Expr.get "a" (.add (.lit 2) (.var "i"))).evalB B σ = some (offS x i) := by
    rw [← hoffi]
    exact RunStep.eval_get B σ "a" _ _
      (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega)) hie (by omega))
      (by omega) (by rw [hoffi]; exact hoffB)
  have hinc : ∀ (τ : Env) (v : ℕ), Run B (.assign "i" (.add (.var "i") (.lit 1)))
      (σ.setArr "a" (3 + i) v) ((σ.setArr "a" (3 + i) v).setVar "i" (i + 1)) 4 := fun τ v =>
    RunStep.assign B _ "i" _ _ (RunStep.eval_add B _ (.var "i") (.lit 1) _ _
      (RunStep.eval_var B _ "i" (by simp; omega)) (RunStep.eval_lit B 1 _ (by omega)) (by omega))
  have hpost : ∀ v, v = offS x (i + 1) →
      PreInv x ((σ.setArr "a" (3 + i) v).setVar "i" (i + 1)) := by
    intro v hv
    refine ⟨(hb.setArr (by decide) _ _).setVar "i" (by simp) _, ⟨by simpa using hlenD,
      by simpa using hdeg⟩, by simp [hlen], ?_, ?_, by simp; omega, fun i' hi' => ?_⟩
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (by omega)]; exact h0
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (by omega)]; exact h1
    · simp only [arrs_setVar, arrs_setArr, String.reduceEq, ↓reduceIte, vars_setVar] at hi' ⊢
      by_cases hii : i' = i + 1
      · subst hii
        rw [show 2 + (i + 1) = 3 + i by omega, getD_set_self (by omega), hv]
      · rw [getD_set_ne (by omega)]; exact hoff i' (by omega)
  by_cases hin : i < nw x
  · have hc := RunStep.cond_lt_true B σ _ _ _ _ hie hne hin
    have hdegi : (σ.arrs "deg").getD i 0 = deg x i := hdeg i hin
    have hdegB : deg x i < B := by have := deg_le_n x hin; omega
    have hgd : (Expr.get "deg" (.var "i")).evalB B σ = some (deg x i) := by
      rw [← hdegi]
      exact RunStep.eval_get B σ "deg" _ _ hie (by omega) (by rw [hdegi]; exact hdegB)
    have hsum := RunStep.eval_add B σ _ _ _ _ hread hgd (by
      have := offS_succ_of_lt x hin; have := offS_le_n x (i + 1); omega)
    have rs := RunStep.store B σ "a" _ _ _ _ hidx hsum (by omega)
    have rite := RunStep.ite_true B _ prefixThen prefixElse σ _ _ hc rs
    refine ⟨_, (rite.seq (hinc σ _)).mono (by simp), hpost _ (offS_succ_of_lt x hin).symm,
      by simp only [vars_setVar, ↓reduceIte]; omega⟩
  · have hc := RunStep.cond_lt_false B σ _ _ _ _ hie hne hin
    have rs := RunStep.store B σ "a" _ _ _ _ hidx hread (by omega)
    have rite := RunStep.ite_false B _ prefixThen prefixElse σ _ _ hc rs
    refine ⟨_, (rite.seq (hinc σ _)).mono (by simp), hpost _ ?_,
      by simp only [vars_setVar, ↓reduceIte]; omega⟩
    rw [offS_of_ge x (by omega), offS_of_ge x (i := i + 1) (by omega)]

/-- **The prefix sums**: from a zero `a`, the fixed cells of the symmetrized word. -/
theorem prefix_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ DegOK x σ ∧ σ.arrs "a" = List.replicate x.length 0) prefixCom
      (fun _ σ' => Base x σ' ∧ DegOK x σ' ∧ FixedA x σ')
      (3 + 3 + 3 + ((24 + 4) * Vw x + 6) + 10) := by
  rintro σ ⟨hb, hdeg, ha⟩
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlen : (σ.arrs "a").length = x.length := by rw [ha]; simp
  have hV := hb.V
  have hE := hb.E
  have hn := hb.n
  have hVB : Vw x < B := by omega
  have hEB : 2 * x.getD 1 0 < B := by omega
  -- the three header stores
  have r1 := RunStep.store B σ "a" (.lit 0) (.var "V") 0 (Vw x) (RunStep.eval_lit B 0 σ (by omega))
    (by rw [← hV]; exact RunStep.eval_var B σ "V" (by rw [hV]; omega)) (by omega)
  set σ₁ := σ.setArr "a" 0 (Vw x) with hσ₁
  have hE₁ : σ₁.vars "E" = x.getD 1 0 := by simp [hσ₁, hE]
  have r2 := RunStep.store B σ₁ "a" (.lit 1) (.var "E") 1 (x.getD 1 0)
    (RunStep.eval_lit B 1 σ₁ (by omega))
    (by rw [← hE₁]; exact RunStep.eval_var B σ₁ "E" (by rw [hE₁]; omega)) (by simp [hσ₁]; omega)
  set σ₂ := σ₁.setArr "a" 1 (x.getD 1 0) with hσ₂
  have r3 := RunStep.store B σ₂ "a" (.lit 2) (.lit 0) 2 0 (RunStep.eval_lit B 2 σ₂ (by omega))
    (RunStep.eval_lit B 0 σ₂ (by omega)) (by simp [hσ₂, hσ₁]; omega)
  set σ₃ := σ₂.setArr "a" 2 0 with hσ₃
  -- the loop
  have hloop := Spec.forRangeZero (B := B) (c := prefixBody) "i" "V" (PreInv x) (Vw x) 24 hVB
    (fun σ hσ => hσ.i_le) (fun σ hσ => hσ.base.V) (prefixBody_spec hw hB)
  have hb₃ : Base x σ₃ := ((hb.setArr (by decide) _ _).setArr (by decide) _ _).setArr (by decide) _ _
  have hdeg₃ : DegOK x σ₃ := by simpa [DegOK, hσ₃, hσ₂, hσ₁] using hdeg
  obtain ⟨σ₄, r4, hPost₄, hi₄⟩ := hloop.run (σ := σ₃) (by
    refine ⟨hb₃.setVar "i" (by simp) 0, by simpa [DegOK] using hdeg₃, by simp [hσ₃, hσ₂, hσ₁, hlen],
      ?_, ?_, by simp, fun i hi => ?_⟩
    · simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (i := 2) (j := 0) (by decide), getD_set_ne (i := 1) (j := 0) (by decide),
        getD_set_self (by omega)]
    · simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_ne (i := 2) (j := 1) (by decide), getD_set_self (by simp only [List.length_set]; omega)]
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte] at hi
      have : i = 0 := by omega
      subst this
      simp only [arrs_setVar, hσ₃, hσ₂, hσ₁, arrs_setArr, String.reduceEq, ↓reduceIte]
      rw [getD_set_self (by simp only [List.length_set]; omega), offS_zero])
  have hb₄ := hPost₄.base
  have hdeg₄ := hPost₄.deg
  have hlen₄ := hPost₄.len
  have h0₄ := hPost₄.h0
  have h1₄ := hPost₄.h1
  have hoff₄ := hPost₄.off
  rw [hi₄] at hoff₄
  -- the last entry
  have hV₄ := hb₄.V
  have hE₄ := hb₄.E
  have hn₄ := hb₄.n
  have hidx : (Expr.add (.add (.lit 3) (.var "V")) (.mul (.lit 2) (.var "E"))).evalB B σ₄ =
      some (3 + Vw x + 2 * x.getD 1 0) := by
    have hVe : (Expr.var "V").evalB B σ₄ = some (Vw x) := by
      rw [← hV₄]; exact RunStep.eval_var B σ₄ "V" (by rw [hV₄]; omega)
    have hEe : (Expr.var "E").evalB B σ₄ = some (x.getD 1 0) := by
      rw [← hE₄]; exact RunStep.eval_var B σ₄ "E" (by rw [hE₄]; omega)
    exact RunStep.eval_add B σ₄ _ _ _ _
      (RunStep.eval_add B σ₄ _ _ _ _ (RunStep.eval_lit B 3 σ₄ (by omega)) hVe (by omega))
      (RunStep.eval_mul B σ₄ _ _ _ _ (RunStep.eval_lit B 2 σ₄ (by omega)) hEe hEB) (by omega)
  have r5 := RunStep.store B σ₄ "a" _ (.var "n") _ (nw x) hidx
    (by rw [← hn₄]; exact RunStep.eval_var B σ₄ "n" (by rw [hn₄]; omega)) (by omega)
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by
    simp only [size_lit, size_var, size_add, size_mul, size_bin, Expr.add_def, Expr.mul_def]
    omega), hb₄.setArr (by decide) _ _,
    by simpa [DegOK] using hdeg₄, ⟨by simp [hlen₄], ?_, ?_, fun i hi => ?_, ?_⟩⟩
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h0₄
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact h1₄
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_ne (by omega)]; exact hoff₄ i hi
  · simp only [arrs_setArr, String.reduceEq, ↓reduceIte]
    rw [getD_set_self (by omega)]

/-! ### The cursors -/

/-- `l := 0; while l < n do pos[l] := a[2 + l]; l := l + 1`. -/
def posBody : Com :=
  .seq (.store "pos" (.var "l") (.get "a" (.add (.lit 2) (.var "l"))))
    (.assign "l" (.add (.var "l") (.lit 1)))

def posCom : Com := .seq (.assign "l" (.lit 0)) (.while (.lt (.var "l") (.var "n")) posBody)

/-- The cursors at the offsets. -/
def PosOK (x : List ℕ) (σ : Env) : Prop :=
  (σ.arrs "pos").length = nw x ∧ ∀ l < nw x, (σ.arrs "pos").getD l 0 = offS x l

structure PosInv (x : List ℕ) (σ : Env) : Prop where
  base : Base x σ
  fixed : FixedA x σ
  lenP : (σ.arrs "pos").length = nw x
  l_le : σ.vars "l" ≤ nw x
  pos : ∀ l < σ.vars "l", (σ.arrs "pos").getD l 0 = offS x l

theorem posBody_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => PosInv x σ ∧ σ.vars "l" < nw x) posBody
      (fun σ σ' => PosInv x σ' ∧ σ'.vars "l" = σ.vars "l" + 1) 12 := by
  rintro σ ⟨hPos, hlt⟩
  have hb := hPos.base
  have hf := hPos.fixed
  have hlenP := hPos.lenP
  have hl := hPos.l_le
  have hpos := hPos.pos
  have hxlen := wf_len hw
  have hoffn := wf_offS_n hw
  have hnV := wf_nV hw
  have hlenA := hf.len
  set l := σ.vars "l" with hldef
  have hle : (Expr.var "l").evalB B σ = some l := RunStep.eval_var B σ "l" (by omega)
  have hoffl : (σ.arrs "a").getD (2 + l) 0 = offS x l := hf.off l (by omega)
  have hoffB : offS x l < B := by have := offS_le_n x l; omega
  have hread : (Expr.get "a" (.add (.lit 2) (.var "l"))).evalB B σ = some (offS x l) := by
    rw [← hoffl]
    exact RunStep.eval_get B σ "a" _ _
      (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega)) hle (by omega))
      (by omega) (by rw [hoffl]; exact hoffB)
  have rs := RunStep.store B σ "pos" _ _ _ _ hle hread (by omega)
  set σ₁ := σ.setArr "pos" l (offS x l) with hσ₁
  have ri := RunStep.assign B σ₁ "l" (.add (.var "l") (.lit 1)) (l + 1)
    (RunStep.eval_add B σ₁ (.var "l") (.lit 1) _ _ (RunStep.eval_var B σ₁ "l" (by simp [hσ₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) (by omega))
  refine ⟨_, (rs.seq ri).mono (by simp), ⟨(hb.setArr (by decide) _ _).setVar "l" (by simp) _,
    hf.congr (by simp [hσ₁]), by simp [hσ₁, hlenP], by simp; omega, fun l' hl' => ?_⟩,
    by simp only [vars_setVar, ↓reduceIte]; omega⟩
  simp only [vars_setVar, String.reduceEq, ↓reduceIte, hσ₁, arrs_setVar, arrs_setArr] at hl' ⊢
  by_cases hll : l' = l
  · subst hll; rw [getD_set_self (by omega)]
  · rw [getD_set_ne (Ne.symm hll)]; exact hpos l' (by omega)

theorem pos_spec {x : List ℕ} (hw : WellFormed x) (hB : 8 * x.length + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ FixedA x σ ∧ (σ.arrs "pos").length = nw x) posCom
      (fun _ σ' => Base x σ' ∧ FixedA x σ' ∧ PosOK x σ') ((12 + 4) * nw x + 6) := by
  have hnB : nw x < B := by have := wf_nV hw; have := wf_len hw; omega
  have hloop := Spec.forRangeZero (B := B) (c := posBody) "l" "n" (PosInv x) (nw x) 12 hnB
    (fun σ hσ => hσ.l_le) (fun σ hσ => hσ.base.n) (posBody_spec hw hB)
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hb, hf, hlenP⟩
    exact ⟨hb.setVar "l" (by simp) 0, hf.congr rfl, by simpa using hlenP, by simp,
      fun l hl => by simp at hl⟩
  · rintro σ σ' - ⟨hPos, hl⟩
    have hb := hPos.base
    have hf := hPos.fixed
    have hlenP := hPos.lenP
    have hpos := hPos.pos
    rw [hl] at hpos
    exact ⟨hb, hf, hlenP, hpos⟩

end Lax117284Proofs.Bipartite.Ram2
