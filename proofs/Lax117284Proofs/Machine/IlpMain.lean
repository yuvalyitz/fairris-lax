import Lax117284Proofs.Machine.IlpHdr

/-!
The whole solver: read the word, then either solve the program `a x = b` or search.
-/

namespace Lax117284Proofs.Machine.Ilp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax117284Proofs.IlpClients Classical Finset

noncomputable section

/-- The cost of the big branch. -/
def Kbig (n : ℕ) : ℕ :=
  ((2 + (14 * n + 10)) + (60 + (((20 + 4) * (n + 1) + 6) + 80))) + Ksearch n + 3

theorem writeFound_vals {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => σ.out = [] ∧ σ.vars "found" ≤ 1) (.write (V "found"))
      (fun σ σ' => σ'.out = [σ.vars "found"]) 3 := by
  run_vcg
  all_goals
    have hB5 := hb.five_lt_B
    have hf : σ.vars "found" ≤ 1 := ‹σ.vars "found" ≤ 1›
    have ho : σ.out = [] := ‹σ.out = []›
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (first | omega | (rw [ho]; rfl))

/-- **The big branch.** -/
theorem bigCom_spec {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B) :
    Spec B (fun σ => Read0 n cnt bb σ ∧ σ.out = [] ∧ σ.arrs "dg" = arrOf (Dn n) (fun _ => 0))
      bigCom
      (fun _ σ' => σ'.out = [if (decodeILP (ilpWord n cnt bb)).Feasible then 1 else 0])
      (Kbig n) := by
  intro σ0 ⟨h0, hout0, hdg0⟩
  obtain ⟨σ1, r1, hC1, hv1, ha1, -, hout1⟩ := (hdrCom_spec hb).frame σ0 h0
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0) := by rw [ha1 "dg" (by decide)]; exact hdg0
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; exact hout0
  obtain ⟨σ2, r2, ⟨hC2, hfound2⟩, hv2, ha2, -, hout2⟩ := (searchCom_spec hb).frame σ1 ⟨hC1, hdg1⟩
  have hout2' : σ2.out = [] := by rw [hout2 (by decide)]; exact hout1'
  have hf2 : σ2.vars "found" ≤ 1 := by rw [hfound2]; split_ifs <;> omega
  obtain ⟨σ3, r3, hout3⟩ := writeFound_vals hb σ2 ⟨hout2', hf2⟩
  refine ⟨σ3, Run.mono (r1.seq (r2.seq r3)) ?_, ?_⟩
  · unfold Kbig; omega
  · show σ3.out = _
    rw [hout3, hfound2]
    have hiff := feasible_iff_accT n cnt bb
    congr 1
    by_cases hF : (decodeILP (ilpWord n cnt bb)).Feasible
    · rw [if_pos (hiff.mp hF), if_pos hF]
    · rw [if_neg (fun h => hF (hiff.mpr h)), if_neg hF]

theorem dvd_iff_sub' (a b : ℕ) : b - b / a * a = 0 ↔ (0 < a → a ∣ b) ∧ (a = 0 → b = 0) := by
  by_cases ha : a = 0
  · subst ha; simp
  · have h1 := Nat.div_add_mod' b a
    have h2 : a ∣ b ↔ b % a = 0 := Nat.dvd_iff_mod_eq_zero
    constructor
    · intro h
      refine ⟨fun _ => h2.mpr (by omega), fun h0 => absurd h0 ha⟩
    · rintro ⟨h, -⟩
      have := h2.mp (h (Nat.pos_of_ne_zero ha))
      omega

theorem smallP_iff (a b : ℕ) :
    ((a = 0 → b = 0) ∧ (0 < a → a ∣ b)) ↔ (if a = 0 then b = 0 else b - b / a * a = 0) := by
  by_cases ha : a = 0
  · subst ha; simp
  · rw [if_neg ha]
    have := dvd_iff_sub' a b
    constructor
    · intro h; exact this.mpr ⟨h.2, h.1⟩
    · intro h; exact ⟨(this.mp h).2, (this.mp h).1⟩

/-- **The small branch**: the program `a x = b`. -/
theorem smallCom_spec {B : ℕ} (a0 b0 : ℕ) (ha : a0 < B) (hb : b0 < B) (hB : 5 < B) :
    Spec B (fun σ => σ.arrs "z" = [1, 1, a0, b0] ∧ σ.out = []) smallCom
      (fun _ σ' => σ'.out = [if (a0 = 0 → b0 = 0) ∧ (0 < a0 → a0 ∣ b0) then 1 else 0]) 30 := by
  unfold smallCom
  run_vcg
  all_goals
    have hz : σ.arrs "z" = [1, 1, a0, b0] := ‹σ.arrs "z" = [1, 1, a0, b0]›
    have ho : σ.out = [] := ‹σ.out = []›
    have g2 : [1, 1, a0, b0].getD 2 0 = a0 := rfl
    have g3 : [1, 1, a0, b0].getD 3 0 = b0 := rfl
    have hl : [1, 1, a0, b0].length = 4 := rfl
    have hdiv : b0 / a0 * a0 ≤ b0 := Nat.div_mul_le_self _ _
    have hdiv2 : b0 / a0 ≤ b0 := Nat.div_le_self _ _
    clear_runs
  all_goals (try simp only [Env.setVar, Env.setArr, ↓reduceIte, String.reduceEq] at *)
  all_goals (try simp only [hz, ho] at *)
  all_goals (try simp only [g2, g3, hl] at *)
  all_goals (try simp only [List.nil_append])
  all_goals (first | omega | (refine congrArg (fun x => [x]) ?_; split_ifs with hP <;>
    first | rfl | (exfalso; have := (smallP_iff a0 b0).mp hP; simp_all) |
      (exfalso; apply hP; rw [smallP_iff]; simp_all)))

/-- The lengths of the arrays. -/
def extI (n len : ℕ) (a : String) : ℕ :=
  if a = "z" then len else if a = "dg" then Dn n else if a = "S" then n else
  if a = "hl" ∨ a = "sg" ∨ a = "es" then nT n else
  if a = "kd" ∨ a = "rkA" ∨ a = "wv" ∨ a = "xv" then nN n else 0

theorem ilpWord_zero (cnt : ℕ → ℕ) (bb : ℕ) : ilpWord 0 cnt bb = [1, 1, 1, cnt 0] := by
  rfl


theorem two_le_nN {n : ℕ} (hn : 1 ≤ n) : 2 ≤ nN n := by
  have h1 := nT_le_nN n
  have h2 : 2 ≤ nT n := by
    unfold nT
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  omega

/-- The cost of the whole solver on a word of the family with `n ≥ 1` clients. -/
def Kfam (n : ℕ) : ℕ := (30 + ((10 + 4) * (zLen n - 2) + 6)) + (4 + Kbig n)

theorem readInit {x : List ℕ} {ext : String → ℕ} (hz : ext "z" = x.length) :
    (initEnv ext x).inp = x ∧ ((initEnv ext x).arrs "z").length = x.length := by
  refine ⟨rfl, ?_⟩
  simp [initEnv, hz]

/-- **The solver on a word of the family with `n ≥ 1` clients.** -/
theorem ilpFamily_run {n : ℕ} {cnt : ℕ → ℕ} {bb vb B : ℕ} (hb : Hyp n cnt bb vb B)
    (hxle : ∀ v ∈ ilpWord n cnt bb, v ≤ vb) :
    ∃ σ', Run B ilpCom (initEnv (extI n (zLen n)) (ilpWord n cnt bb)) σ' (Kfam n) ∧
      σ'.out = [if (decodeILP (ilpWord n cnt bb)).Feasible then 1 else 0] := by
  set x := ilpWord n cnt bb with hxdef
  have hlen : x.length = zLen n := ilpWord_length n cnt bb
  have h0 : x.getD 0 0 = nN n := by
    rw [hxdef, ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
  have h1 : x.getD 1 0 = nM n := by
    rw [hxdef, ilpWord_getD, if_pos (by have := zLen_ge n; omega)]; simp [wordFun]
  have hx : x.length = 2 + x.getD 1 0 * x.getD 0 0 + x.getD 1 0 := by
    rw [h0, h1, hlen]; unfold zLen; ring
  have hxB : ∀ v ∈ x, v < B := fun v hv => hb.lt_U (by
    have := hxle v hv; unfold Ub; omega)
  have hlB : x.length + 1 < B := hb.lt_U (by rw [hlen]; unfold Ub; omega)
  have h2 : 2 ≤ x.length := by rw [hlen]; have := zLen_ge n; omega
  obtain ⟨σ1, r1, ⟨hN1, hM1, hz1, hin1⟩, hv1, ha1, -, hout1⟩ :=
    (readCom_spec x hx hxB hlB h2).frame (initEnv (extI n (zLen n)) x)
      (readInit (by simp [extI, hlen]))
  have hN1' : σ1.vars "N" = nN n := by rw [hN1, h0]
  have hM1' : σ1.vars "M" = nM n := by rw [hM1, h1]
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; rfl
  have hlens : ∀ a, (σ1.arrs a).length = ((initEnv (extI n (zLen n)) x).arrs a).length := by
    intro a; exact run_len_arrs r1 a
  have hread : Read0 n cnt bb σ1 :=
    { hN := hN1', hM := hM1', hz := by rw [hz1],
      ldg := by rw [hlens]; simp [initEnv, extI],
      lhl := by rw [hlens]; simp [initEnv, extI],
      lkd := by rw [hlens]; simp [initEnv, extI],
      lrk := by rw [hlens]; simp [initEnv, extI],
      lsg := by rw [hlens]; simp [initEnv, extI],
      lS := by rw [hlens]; simp [initEnv, extI],
      lwv := by rw [hlens]; simp [initEnv, extI],
      les := by rw [hlens]; simp [initEnv, extI],
      lxv := by rw [hlens]; simp [initEnv, extI] }
  have hdg1 : σ1.arrs "dg" = arrOf (Dn n) (fun _ => 0) := by
    rw [ha1 "dg" (by decide)]
    simp only [initEnv, extI]
    simpa using replicate_eq_arrOf (Dn n) 0
  obtain ⟨σ2, r2, hout2⟩ := bigCom_spec hb σ1 ⟨hread, hout1', hdg1⟩
  have hn2 : 2 ≤ nN n := two_le_nN hb.n1
  have hBN := hb.nN_lt
  have hB1 := hb.one_lt_B
  have hcond : (Cond.eq (V "N") (lit 1)).evalB B σ1 = some false := by
    have := evalB_condEq (evalB_var (B := B) (σ := σ1) (x := "N") (by rw [hN1']; exact hBN))
      (evalB_lit (B := B) (n := 1) (σ := σ1) hB1)
    rw [this, hN1']
    simp
    omega
  refine ⟨σ2, ?_, hout2⟩
  refine Run.mono (show Run B (.seq readCom (.ite (Cond.eq (V "N") (lit 1)) smallCom bigCom)) _ σ2 _ from
    r1.seq (Run.ite_false hcond r2)) ?_
  unfold Kfam
  simp
  omega

/-- **The solver on a word `[1, 1, a, b]`.** -/
theorem ilpSmall_run {B : ℕ} (a0 b0 : ℕ) (ha : a0 < B) (hb : b0 < B) (hB : 5 < B) :
    ∃ σ', Run B ilpCom (initEnv (extI 0 4) [1, 1, a0, b0]) σ' 100 ∧
      σ'.out = [if (a0 = 0 → b0 = 0) ∧ (0 < a0 → a0 ∣ b0) then 1 else 0] := by
  have hx : ([1, 1, a0, b0] : List ℕ).length = 2 +
      ([1, 1, a0, b0] : List ℕ).getD 1 0 * ([1, 1, a0, b0] : List ℕ).getD 0 0 +
      ([1, 1, a0, b0] : List ℕ).getD 1 0 := rfl
  have hxB : ∀ v ∈ ([1, 1, a0, b0] : List ℕ), v < B := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> first | omega | assumption
  have hlB : ([1, 1, a0, b0] : List ℕ).length + 1 < B := by
    simp; omega
  obtain ⟨σ1, r1, ⟨hN1, hM1, hz1, hin1⟩, hv1, ha1, -, hout1⟩ :=
    (readCom_spec [1, 1, a0, b0] hx hxB hlB (by simp)).frame (initEnv (extI 0 4) [1, 1, a0, b0])
      (readInit (by simp [extI]))
  have hout1' : σ1.out = [] := by rw [hout1 (by decide)]; rfl
  obtain ⟨σ2, r2, hout2⟩ := smallCom_spec (B := B) a0 b0 ha hb hB σ1 ⟨hz1, hout1'⟩
  have hcond : (Cond.eq (V "N") (lit 1)).evalB B σ1 = some true := by
    have := evalB_condEq (evalB_var (B := B) (σ := σ1) (x := "N") (by rw [hN1]; simp; omega))
      (evalB_lit (B := B) (n := 1) (σ := σ1) (by omega))
    rw [this, hN1]
    simp
  refine ⟨σ2, ?_, hout2⟩
  refine Run.mono (show Run B (.seq readCom (.ite (Cond.eq (V "N") (lit 1)) smallCom bigCom)) _ σ2 _ from
    r1.seq (Run.ite_true hcond r2)) ?_
  simp

end

end Lax117284Proofs.Machine.Ilp
