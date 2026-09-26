import Lax117284Proofs.Bipartite.Ram2.Validate

/-!
The three syntactic checks of the validator, each a `Spec` on the flag `ok`: `n ≤ V` and the
length (`chk1`), the offsets (`chk2`), the targets (`chk3`). Every array read of a later check is
in range once the earlier ones passed; a failed check clears the flag.
-/

namespace Lax117284Proofs.Bipartite.Ram2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax117284.BipartiteDecision
open scoped Classical

variable {B : ℕ}

/-! ### The checks -/

/-- A guard clearing the flag: `if b then ok := 0 else skip`. -/
theorem okGuard_run {σ : Env} {b : Cond} {v : Bool} (hb : b.evalB B σ = some v) (h0 : 0 < B) :
    Run B (.ite b (.assign "ok" (.lit 0)) .skip) σ (if v then σ.setVar "ok" 0 else σ)
      (1 + b.size + 2) := by
  cases v
  · exact RunStep.ite_false B b _ .skip σ σ 2 hb ((RunStep.skip B σ).mono (by omega))
  · exact RunStep.ite_true B b _ .skip σ _ 2 hb
      (RunStep.assign B σ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ h0))

/-- A guard keeping the flag: `if b then skip else ok := 0`. -/
theorem okGuard_run' {σ : Env} {b : Cond} {v : Bool} (hb : b.evalB B σ = some v) (h0 : 0 < B) :
    Run B (.ite b .skip (.assign "ok" (.lit 0))) σ (if v then σ else σ.setVar "ok" 0)
      (1 + b.size + 2) := by
  cases v
  · exact RunStep.ite_false B b .skip _ σ _ 2 hb
      (RunStep.assign B σ "ok" (.lit 0) 0 (RunStep.eval_lit B 0 σ h0))
  · exact RunStep.ite_true B b .skip _ σ σ 2 hb ((RunStep.skip B σ).mono (by omega))

/-- The flag after a guard: `1` exactly when it was `1` and the guard did not fire. -/
theorem ok_ite {σ : Env} (v : Bool) :
    (if v then σ.setVar "ok" 0 else σ).vars "ok" = if v then 0 else σ.vars "ok" := by
  cases v <;> simp

theorem ok_ite' {σ : Env} (v : Bool) :
    (if v then σ else σ.setVar "ok" 0).vars "ok" = if v then σ.vars "ok" else 0 := by
  cases v <;> simp

theorem base_ite {x : List ℕ} {σ : Env} (hb : Base x σ) (v : Bool) :
    Base x (if v then σ.setVar "ok" 0 else σ) := by
  cases v
  · exact hb
  · exact hb.setVar "ok" (by simp) 0

theorem base_ite' {x : List ℕ} {σ : Env} (hb : Base x σ) (v : Bool) :
    Base x (if v then σ else σ.setVar "ok" 0) := by
  cases v
  · exact hb.setVar "ok" (by simp) 0
  · exact hb

theorem vars_ite {σ : Env} (v : Bool) (y : String) (hy : y ≠ "ok") :
    (if v then σ.setVar "ok" 0 else σ).vars y = σ.vars y := by
  cases v <;> simp [hy]

theorem vars_ite' {σ : Env} (v : Bool) (y : String) (hy : y ≠ "ok") :
    (if v then σ else σ.setVar "ok" 0).vars y = σ.vars y := by
  cases v <;> simp [hy]

theorem arrs_ite' {σ : Env} (v : Bool) : (if v then σ else σ.setVar "ok" 0).arrs = σ.arrs := by
  cases v <;> rfl

/-- `if V < n then ok := 0; if len = 4 + V + 2E then skip else ok := 0`. -/
def chk1 : Com :=
  .seq (.ite (.lt (.var "V") (.var "n")) (.assign "ok" (.lit 0)) .skip)
    (.ite (.eq (.var "len") (.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E"))))
      .skip (.assign "ok" (.lit 0)))

theorem chk1_spec {x : List ℕ}
    (hB : 8 * (x.length + Vw x + x.getD 1 0 + nw x) + 40 ≤ B) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk1
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ nw x ≤ Vw x ∧ x.length = 4 + Vw x + 2 * x.getD 1 0)) 24 := by
  rintro σ ⟨hb, hok⟩
  have hl := hb.len
  have hV := hb.V
  have hE := hb.E
  have hn := hb.n
  have hc1 : (Cond.lt (.var "V") (.var "n")).evalB B σ = some (decide (Vw x < nw x)) := by
    have := evalB_condLt (B := B) (σ := σ) (evalB_var (x := "V") (by omega))
      (evalB_var (x := "n") (by omega))
    rwa [hV, hn] at this
  have r1 := okGuard_run hc1 (by omega)
  set σ₁ := (if decide (Vw x < nw x) then σ.setVar "ok" 0 else σ) with hσ₁
  have hb₁ : Base x σ₁ := base_ite hb _
  have hsum : (Expr.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E"))).evalB B σ₁ =
      some (4 + Vw x + 2 * x.getD 1 0) := by
    have hVe : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
      rw [← hb₁.V]; exact RunStep.eval_var B σ₁ "V" (by rw [hb₁.V]; omega)
    have hEe : (Expr.var "E").evalB B σ₁ = some (x.getD 1 0) := by
      rw [← hb₁.E]; exact RunStep.eval_var B σ₁ "E" (by rw [hb₁.E]; omega)
    have h4 := RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 4 σ₁ (by omega)) hVe (by omega)
    have h2 := RunStep.eval_mul B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hEe (by omega)
    exact RunStep.eval_add B σ₁ _ _ _ _ h4 h2 (by omega)
  have hc2 : Cond.evalB B (Cond.eq (.var "len")
      (.add (.add (.lit 4) (.var "V")) (.mul (.lit 2) (.var "E")))) σ₁ =
      some (decide (x.length = 4 + Vw x + 2 * x.getD 1 0)) := by
    have hle : (Expr.var "len").evalB B σ₁ = some x.length := by
      rw [← hb₁.len]; exact RunStep.eval_var B σ₁ "len" (by rw [hb₁.len]; omega)
    rw [evalB_condEq hle hsum]
    congr 1
    try (by_cases h : x.length = 4 + Vw x + 2 * x.getD 1 0 <;> simp [h])
  have r2 := okGuard_run' hc2 (by omega)
  refine ⟨_, (r1.seq r2).mono (by simp), base_ite' hb₁ _, ?_, ?_⟩
  · rw [ok_ite']; split_ifs
    · rw [hσ₁, ok_ite]; split_ifs <;> omega
    · exact Nat.zero_le _
  · rw [ok_ite', hσ₁, ok_ite, hok]
    by_cases h1 : Vw x < nw x <;> by_cases h2 : x.length = 4 + Vw x + 2 * x.getD 1 0 <;>
      simp [h1, h2] <;> omega

/-- The offsets: `t[2] = 0`, `t[2 + V] = 2E`, and `t[2 + i] ≤ t[3 + i]` for `i < V`. -/
def chk2Body : Com :=
  .seq (.ite (.lt (.get "t" (.add (.lit 3) (.var "i"))) (.get "t" (.add (.lit 2) (.var "i"))))
      (.assign "ok" (.lit 0)) .skip)
    (.assign "i" (.add (.var "i") (.lit 1)))

def chk2 : Com :=
  .seq (.ite (.eq (.get "t" (.lit 2)) (.lit 0)) .skip (.assign "ok" (.lit 0)))
    (.seq (.ite (.eq (.get "t" (.add (.lit 2) (.var "V"))) (.mul (.lit 2) (.var "E"))) .skip
        (.assign "ok" (.lit 0)))
      (.seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "V")) chk2Body)))

/-- The invariant of the offsets loop. -/
def Chk2Inv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.vars "i" ≤ Vw x ∧ σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ (offw x 0 = 0 ∧ offw x (Vw x) = 2 * x.getD 1 0 ∧
      ∀ i < σ.vars "i", offw x i ≤ offw x (i + 1)))

theorem chk2Body_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Chk2Inv x σ ∧ σ.vars "i" < Vw x) chk2Body
      (fun σ σ' => Chk2Inv x σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 20 := by
  rintro σ ⟨⟨hb, hi, hok, hiff⟩, hlt⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  set i := σ.vars "i" with hidef
  have hg2 : (σ.arrs "t").getD (2 + i) 0 = offw x i := hb.tab.getD (by omega)
  have hg3 : (σ.arrs "t").getD (3 + i) 0 = offw x (i + 1) := by
    rw [hb.tab.getD (by omega)]; unfold offw; congr 1; omega
  have h2B : offw x i < B := getD_lt_of_mem hx (by omega) _
  have h3B : offw x (i + 1) < B := getD_lt_of_mem hx (by omega) _
  have hiB : i + 1 < B := by omega
  have e2 : (Expr.get "t" (.add (.lit 2) (.var "i"))).evalB B σ = some (offw x i) := by
    rw [← hg2]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 2 σ (by omega))
      (RunStep.eval_var B σ "i" (by omega)) (by omega)) (by omega) (by rw [hg2]; exact h2B)
  have e3 : (Expr.get "t" (.add (.lit 3) (.var "i"))).evalB B σ = some (offw x (i + 1)) := by
    rw [← hg3]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega))
      (RunStep.eval_var B σ "i" (by omega)) (by omega)) (by omega) (by rw [hg3]; exact h3B)
  have hc := evalB_condLt e3 e2
  have r1 := okGuard_run hc (by omega)
  set σ₁ := (if decide (offw x (i + 1) < offw x i) then σ.setVar "ok" 0 else σ) with hσ₁
  have hi₁ : σ₁.vars "i" = i := vars_ite _ "i" (by decide)
  have r2 := RunStep.assign B σ₁ "i" (.add (.var "i") (.lit 1)) (i + 1)
    (RunStep.eval_add B σ₁ (.var "i") (.lit 1) _ _
      (by rw [← hi₁]; exact RunStep.eval_var B σ₁ "i" (by rw [hi₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) hiB)
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨(base_ite hb _).setVar "i" (by simp) _,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega, ?_, ?_⟩,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite]; split_ifs <;> omega
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite]
    by_cases h : offw x (i + 1) < offw x i
    · rw [if_pos (by simpa using h)]
      constructor
      · intro h0; omega
      · rintro ⟨-, -, hall⟩
        exfalso
        have := hall i (by omega)
        omega
    · rw [if_neg (by simpa using h), hiff]
      constructor
      · rintro ⟨h0, hV', hall⟩
        refine ⟨h0, hV', fun i' hi' => ?_⟩
        rcases Nat.lt_or_ge i' i with h' | h'
        · exact hall i' h'
        · have : i' = i := by omega
          subst this; omega
      · rintro ⟨h0, hV', hall⟩
        exact ⟨h0, hV', fun i' hi' => hall i' (by omega)⟩

theorem chk2_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk2
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ (offw x 0 = 0 ∧ offw x (Vw x) = 2 * x.getD 1 0 ∧
          ∀ i < Vw x, offw x i ≤ offw x (i + 1))))
      (16 + 16 + ((20 + 4) * Vw x + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := chk2Body) "i" "V" (Chk2Inv x) (Vw x) 20
    (by omega) (fun σ hσ => hσ.2.1) (fun σ hσ => hσ.1.V) (chk2Body_spec hx hB hlen)
  rintro σ ⟨hb, hok⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  have hE := hb.E
  have hg2 : (σ.arrs "t").getD 2 0 = offw x 0 := hb.tab.getD (by omega)
  have hgV : (σ.arrs "t").getD (2 + Vw x) 0 = offw x (Vw x) := hb.tab.getD (by omega)
  have h2B : offw x 0 < B := getD_lt_of_mem hx (by omega) _
  have hVB : offw x (Vw x) < B := getD_lt_of_mem hx (by omega) _
  have hEB : 2 * x.getD 1 0 < B := by omega
  -- `t[2] = 0`
  have e2 : (Expr.get "t" (.lit 2)).evalB B σ = some (offw x 0) := by
    rw [← hg2]
    exact RunStep.eval_get B σ "t" _ _ (RunStep.eval_lit B 2 σ (by omega)) (by omega)
      (by rw [hg2]; exact h2B)
  have hc1 := evalB_condEq e2 (RunStep.eval_lit B 0 σ (by omega))
  have r1 := okGuard_run' hc1 (by omega)
  set σ₁ := (if (offw x 0 == 0) then σ else σ.setVar "ok" 0) with hσ₁
  have hb₁ : Base x σ₁ := base_ite' hb _
  have ha₁ : σ₁.arrs = σ.arrs := arrs_ite' _
  -- `t[2 + V] = 2E`
  have eV : (Expr.get "t" (.add (.lit 2) (.var "V"))).evalB B σ₁ = some (offw x (Vw x)) := by
    have hVe : (Expr.var "V").evalB B σ₁ = some (Vw x) := by
      rw [← hb₁.V]; exact RunStep.eval_var B σ₁ "V" (by rw [hb₁.V]; omega)
    rw [← hgV, ← ha₁]
    exact RunStep.eval_get B σ₁ "t" _ _
      (RunStep.eval_add B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hVe (by omega))
      (by rw [ha₁]; omega) (by rw [ha₁, hgV]; exact hVB)
  have eE : (Expr.mul (.lit 2) (.var "E")).evalB B σ₁ = some (2 * x.getD 1 0) := by
    have hEe : (Expr.var "E").evalB B σ₁ = some (x.getD 1 0) := by
      rw [← hb₁.E]; exact RunStep.eval_var B σ₁ "E" (by rw [hb₁.E]; omega)
    exact RunStep.eval_mul B σ₁ _ _ _ _ (RunStep.eval_lit B 2 σ₁ (by omega)) hEe hEB
  have hc2 := evalB_condEq eV eE
  have r2 := okGuard_run' hc2 (by omega)
  set σ₂ := (if (offw x (Vw x) == 2 * x.getD 1 0) then σ₁ else σ₁.setVar "ok" 0) with hσ₂
  have hb₂ : Base x σ₂ := base_ite' hb₁ _
  -- the loop
  obtain ⟨σ₃, r3, ⟨hb₃, -, hok₃, hiff₃⟩, hi₃⟩ := hloop.run (σ := σ₂) (by
    refine ⟨hb₂.setVar "i" (by simp) 0, by simp, ?_, ?_⟩
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      rw [hσ₂, ok_ite']; split_ifs
      · rw [hσ₁, ok_ite']; split_ifs <;> omega
      · exact Nat.zero_le _
    · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
      rw [hσ₂, ok_ite', hσ₁, ok_ite', hok]
      by_cases h1 : offw x 0 = 0 <;> by_cases h2 : offw x (Vw x) = 2 * x.getD 1 0 <;>
        simp [h1, h2])
  rw [hi₃] at hiff₃
  exact ⟨σ₃, (r1.seq (r2.seq r3)).mono (by simp only [size_condEq, size_get, size_lit, size_var,
    size_add, size_mul, size_bin, Expr.add_def, Expr.mul_def]; omega), hb₃, hok₃, hiff₃⟩

/-- The targets: `t[3 + V + j] < V` for `j < 2E`. -/
def chk3Body : Com :=
  .seq (.ite (.lt (.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))) (.var "V")) .skip
      (.assign "ok" (.lit 0)))
    (.assign "j" (.add (.var "j") (.lit 1)))

def chk3 : Com :=
  .seq (.assign "e2" (.mul (.lit 2) (.var "E")))
    (.seq (.assign "j" (.lit 0)) (.while (.lt (.var "j") (.var "e2")) chk3Body))

/-- The invariant of the targets loop. -/
def Chk3Inv (x : List ℕ) (σ : Env) : Prop :=
  Base x σ ∧ σ.vars "e2" = 2 * x.getD 1 0 ∧ σ.vars "j" ≤ 2 * x.getD 1 0 ∧ σ.vars "ok" ≤ 1 ∧
    (σ.vars "ok" = 1 ↔ ∀ j < σ.vars "j", tgtw x j < Vw x)

theorem chk3Body_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Chk3Inv x σ ∧ σ.vars "j" < 2 * x.getD 1 0) chk3Body
      (fun σ σ' => Chk3Inv x σ' ∧ σ'.vars "j" = σ.vars "j" + 1) 20 := by
  rintro σ ⟨⟨hb, he2, hj, hok, hiff⟩, hlt⟩
  have hlenT := hb.tab.length
  have hV := hb.V
  set j := σ.vars "j" with hjdef
  have hg : (σ.arrs "t").getD (3 + Vw x + j) 0 = tgtw x j := hb.tab.getD (by omega)
  have hgB : tgtw x j < B := getD_lt_of_mem hx (by omega) _
  have hVB : Vw x < B := by omega
  have hjB : j + 1 < B := by omega
  have eg : (Expr.get "t" (.add (.add (.lit 3) (.var "V")) (.var "j"))).evalB B σ =
      some (tgtw x j) := by
    have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
      rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
    have h3 := RunStep.eval_add B σ _ _ _ _ (RunStep.eval_lit B 3 σ (by omega)) hVe (by omega)
    have h4 := RunStep.eval_add B σ _ _ _ _ h3 (RunStep.eval_var B σ "j" (by omega)) (by omega)
    rw [← hg]
    exact RunStep.eval_get B σ "t" _ _ h4 (by omega) (by rw [hg]; exact hgB)
  have hVe : (Expr.var "V").evalB B σ = some (Vw x) := by
    rw [← hV]; exact RunStep.eval_var B σ "V" (by omega)
  have hc := evalB_condLt eg hVe
  have r1 := okGuard_run' hc (by omega)
  set σ₁ := (if decide (tgtw x j < Vw x) then σ else σ.setVar "ok" 0) with hσ₁
  have hj₁ : σ₁.vars "j" = j := vars_ite' _ "j" (by decide)
  have r2 := RunStep.assign B σ₁ "j" (.add (.var "j") (.lit 1)) (j + 1)
    (RunStep.eval_add B σ₁ (.var "j") (.lit 1) _ _
      (by rw [← hj₁]; exact RunStep.eval_var B σ₁ "j" (by rw [hj₁]; omega))
      (RunStep.eval_lit B 1 σ₁ (by omega)) hjB)
  have he2₁ : σ₁.vars "e2" = 2 * x.getD 1 0 := by
    rw [hσ₁, vars_ite' _ "e2" (by decide)]; exact he2
  refine ⟨_, (r1.seq r2).mono (by simp), ⟨(base_ite' hb _).setVar "j" (by simp) _,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; exact he2₁,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega, ?_, ?_⟩,
    by simp only [vars_setVar, String.reduceEq, ↓reduceIte]; omega⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite']; split_ifs <;> omega
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hσ₁, ok_ite']
    by_cases h : tgtw x j < Vw x
    · rw [if_pos (by simpa using h), hiff]
      constructor
      · intro hall j' hj'
        rcases Nat.lt_or_ge j' j with h' | h'
        · exact hall j' h'
        · have : j' = j := by omega
          subst this; exact h
      · intro hall j' hj'; exact hall j' (by omega)
    · rw [if_neg (by simpa using h)]
      constructor
      · intro h0; omega
      · intro hall
        exfalso
        exact h (hall j (by omega))

theorem chk3_spec {x : List ℕ} (hx : ∀ v ∈ x, v < B) (hB : 8 * x.length + 40 ≤ B)
    (hlen : x.length = 4 + Vw x + 2 * x.getD 1 0) :
    Spec B (fun σ => Base x σ ∧ σ.vars "ok" = 1) chk3
      (fun _ σ' => Base x σ' ∧ σ'.vars "ok" ≤ 1 ∧
        (σ'.vars "ok" = 1 ↔ ∀ s < 2 * x.getD 1 0, tgtw x s < Vw x))
      (4 + ((20 + 4) * (2 * x.getD 1 0) + 6)) := by
  have hloop := Spec.forRangeZero (B := B) (c := chk3Body) "j" "e2" (Chk3Inv x)
    (2 * x.getD 1 0) 20 (by omega) (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1)
    (chk3Body_spec hx hB hlen)
  rintro σ ⟨hb, hok⟩
  have hE := hb.E
  have hEB : 2 * x.getD 1 0 < B := by omega
  have r1 := RunStep.assign B σ "e2" (.mul (.lit 2) (.var "E")) (2 * x.getD 1 0)
    (RunStep.eval_mul B σ (.lit 2) (.var "E") 2 (x.getD 1 0) (RunStep.eval_lit B 2 σ (by omega))
      (by rw [← hE]; exact RunStep.eval_var B σ "E" (by omega)) hEB)
  set σ₁ := σ.setVar "e2" (2 * x.getD 1 0) with hσ₁
  obtain ⟨σ₂, r2, ⟨hb₂, -, -, hok₂, hiff₂⟩, hj₂⟩ := hloop.run (σ := σ₁) (by
    refine ⟨(hb.setVar "e2" (by simp) _).setVar "j" (by simp) _, by simp [hσ₁], by simp,
      by simp [hσ₁, hok], ?_⟩
    simp [hσ₁, hok])
  rw [hj₂] at hiff₂
  exact ⟨σ₂, (r1.seq r2).mono (by simp), hb₂, hok₂, hiff₂⟩

end Lax117284Proofs.Bipartite.Ram2
