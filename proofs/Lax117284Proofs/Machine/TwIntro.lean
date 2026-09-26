import Lax117284Proofs.Machine.TwKeep
import Lax117284Proofs.Machine.TwCf

/-!
The program of an introduce node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- Every sorted bag has at most `wid` entries. -/
lemma bagL_len_le (P : Params) {j : ℕ} (hj : j < P.N) : (bagL P.D j).length ≤ P.wid :=
  bagL_length_le P.hD hj

/-- The entries of a sorted bag are clients (or the default zero). -/
lemma bagL_get_le (P : Params) {j : ℕ} (hj : j < P.N) (t : ℕ) : (bagL P.D j)[t]! ≤ P.n := by
  by_cases ht : t < (bagL P.D j).length
  · obtain ⟨-, hm⟩ := bagL_spec P.hD j hj
    have := ((hm _).1 (List.getElem_mem ht)).1
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]
    exact this.le
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp

lemma bagL_get_lt (P : Params) {j t : ℕ} (hj : j < P.N) (ht : t < (bagL P.D j).length) :
    (bagL P.D j)[t]! < P.n := by
  obtain ⟨-, hm⟩ := bagL_spec P.hD j hj
  have := ((hm _).1 (List.getElem_mem ht)).1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  exact this

lemma vertex_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (3 + 3 * i) 0 = vertex P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (2 + 3 * i) (by omega)
  rw [show 2 + 3 * i + 1 = 3 + 3 * i by omega] at this
  rw [this]; rfl

lemma other_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (4 + 3 * i) 0 = other P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (3 + 3 * i) (by omega)
  rw [show 3 + 3 * i + 1 = 4 + 3 * i by omega] at this
  rw [this]; rfl

lemma kind_eq (P : Params) (hC : NC P B σ) {i : ℕ} (hi : i < P.N) :
    (σ.arrs "O").getD (2 + 3 * i) 0 = kind P.D i := by
  have hl : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have := hC.O_ (1 + 3 * i) (by omega)
  rw [show 1 + 3 * i + 1 = 2 + 3 * i by omega] at this
  rw [this]; rfl

/-! ### The head: the record, the position, the sizes -/

/-- The sizes an introduce node needs. -/
def introTail1 : Com := seqs
  [ .assign "s1" (add (V "s") (L 1)),
    .assign "iw" (mul (V "i") (V "w1")),
    .assign "bs" (V "iw"),
    .assign "fn" (V "s1") ]

/-- The head of the program of an introduce node. -/
def introHead : Com := .seq recCom (.seq posLoop introTail1)

lemma SR_sub : ∀ y ∈ SR, y ∈ SN := by intro y hy; simp only [SR, List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [SN]

theorem introHead_run {i0 : ℕ} (hC : NC P B σ)
    (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ) (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) :
    ∃ σ1, Run B introHead σ σ1 (34 * P.wid + 130) ∧ Keep σ σ1 ∧ σ1.arrs = σ.arrs ∧
      σ1.vars "c" = i0 ∧ σ1.vars "s" = (bagL P.D i0).length ∧
      σ1.vars "vx" = vertex P.D (i0 + 1) ∧ σ1.vars "ot" = other P.D (i0 + 1) ∧
      σ1.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) ∧ σ1.vars "cw" = i0 * P.wid ∧
      σ1.vars "s1" = (bagL P.D i0).length + 1 ∧ σ1.vars "iw" = (i0 + 1) * P.wid ∧
      σ1.vars "bs" = (i0 + 1) * P.wid ∧ σ1.vars "fn" = (bagL P.D i0).length + 1 := by
  have hBpos : 0 < B := by have := hC.b3; omega
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hw1 := hC.w1_
  have hNw : ∀ j, j ≤ P.N → j * P.wid ≤ P.N * P.wid := fun j hj => Nat.mul_le_mul_right _ hj
  have hi2 : (i0 + 2) * P.wid ≤ P.N * P.wid := hNw _ (by omega)
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hSc : (σ.arrs "SZ").getD i0 0 < B := by
    rw [hN.sz i0 (by omega)]; omega
  obtain ⟨σ1, r1, hc1, hvx1, hot1, hs1, hcw1, hp1, A1, o1⟩ := recCom_run (B := B) (σ := σ)
    (i := i0 + 1) (N := P.N) hi hiN hC.lenSZ (by have := hC.lenO; omega)
    (hC.O_lt (by omega) (by omega)) (hC.O_lt (by omega) (by omega))
    (by simpa using hSc) (by have := hC.b3; omega)
    (by rw [hw1, Nat.add_sub_cancel]; have := hNw i0 (by omega); omega)
    (by rw [hw1]; have := hNw 1 (by omega); omega)
  have hvx' : σ1.vars "vx" = vertex P.D (i0 + 1) := by rw [hvx1, vertex_eq P hC hiN]
  have hot' : σ1.vars "ot" = other P.D (i0 + 1) := by rw [hot1, other_eq P hC hiN]
  have hs' : σ1.vars "s" = (bagL P.D i0).length := by
    rw [hs1, Nat.add_sub_cancel, hN.sz i0 (by omega)]
  have hcw' : σ1.vars "cw" = i0 * P.wid := by rw [hcw1, Nat.add_sub_cancel, hw1]
  have hvxB : σ1.vars "vx" < B := by rw [hvx1]; exact hC.O_lt (by omega) (by omega)
  obtain ⟨σ2, r2, hp2, A2, o2⟩ := posLoop_run (B := B) (σ0 := σ1) (f := fun t => (bagL P.D i0)[t]!)
    (s0 := (bagL P.D i0).length) (cw0 := i0 * P.wid) hs' hcw' hp1
    (fun t ht => by rw [A1.1]; exact hN.bg i0 (by omega) t ht)
    (by rw [A1.1]; have := hC.lenBG; omega)
    (fun t => by have := bagL_get_le P (j := i0) (by omega) t; have := hC.b8; omega) hvxB
    (by have := bagL_len_le P (j := i0) (by omega); omega)
  have hs2 : σ2.vars "s" = (bagL P.D i0).length := by rw [A2.2 "s" (by simp), hs']
  have hi2v : σ2.vars "i" = i0 + 1 := by rw [A2.2 "i" (by simp), A1.2 "i" (by simp [SR]), hi]
  have hw2 : σ2.vars "w1" = P.wid := by rw [A2.2 "w1" (by simp), A1.2 "w1" (by simp [SR]), hw1]
  have hp' : σ2.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1)) := by
    rw [hp2, pos_eq_sum, hvx']
  obtain ⟨σ3, r3, e3⟩ : ∃ σ3, Run B introTail1 σ2 σ3 40 ∧ σ3 =
      (((σ2.setVar "s1" ((bagL P.D i0).length + 1)).setVar "iw" ((i0 + 1) * P.wid)).setVar "bs"
        ((i0 + 1) * P.wid)).setVar "fn" ((bagL P.D i0).length + 1) := by
    unfold introTail1 seqs
    run_vcg
    all_goals try (nrmA; simp only [hs2, hi2v, hw2]; omega)
    all_goals try (nrmA; omega)
    all_goals (try nrmA)
    all_goals (try simp only [hs2, hi2v, hw2])
  have hv3 : ∀ y, y ∉ ["s1", "iw", "bs", "fn"] → σ3.vars y = σ2.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have k1 := Keep.of_agr A1 SR_sub o1
  have k2 := Keep.of_agr A2 (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [SN]) o2
  have k3 : Keep σ2 σ3 := by
    rw [e3]
    exact ((((Keep.refl σ2).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _
  have har : σ3.arrs = σ.arrs := by rw [e3]; simp [A2.1, A1.1]
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), k1.trans (k2.trans k3), har, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv3 "c" (by simp), A2.2 "c" (by simp), hc1]; simp
  · rw [hv3 "s" (by simp), hs2]
  · rw [hv3 "vx" (by simp), A2.2 "vx" (by simp), hvx']
  · rw [hv3 "ot" (by simp), A2.2 "ot" (by simp), hot']
  · rw [hv3 "p" (by simp), hp']
  · rw [hv3 "cw" (by simp), A2.2 "cw" (by simp), hcw']
  · rw [e3]; simp [Env.setVar, hs2]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar, hs2]

/-! ### The row of the bag -/

/-- The value of the cell of the new bag: the child's entry before the position, the vertex at it,
the child's entry one earlier after it. -/
def bgPreIntro : Com :=
  .ite (.lt (V "fc") (V "p")) (.assign "val" (G "BG" (add (V "cw") (V "fc"))))
    (.ite (.eq (V "fc") (V "p")) (.assign "val" (V "vx"))
      (.assign "val" (G "BG" (sub (add (V "cw") (V "fc")) (L 1)))))

theorem bgPreIntro_run (σ : Env) (l : List ℕ) (p vx cw : ℕ) (hp : σ.vars "p" = p)
    (hvx : σ.vars "vx" = vx) (hcw : σ.vars "cw" = cw)
    (hrd : ∀ t < l.length, (σ.arrs "BG").getD (cw + t) 0 = l[t]!) (hpl : p ≤ l.length)
    (hf : σ.vars "fc" ≤ l.length) (hlen : cw + l.length + 1 ≤ (σ.arrs "BG").length)
    (hbd : ∀ t : ℕ, l[t]! < B) (hvxB : vx < B) (hb : cw + l.length + 8 < B) :
    ∃ σ', Run B bgPreIntro σ σ' 20 ∧
      σ'.vars "val" = (l.insertIdx p vx)[σ.vars "fc"]! ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hrd' : ∀ t < l.length, (σ.arrs "BG").getD (σ.vars "cw" + t) 0 = l[t]! := by
    rw [hcw]; exact hrd
  have hins := getElem!_insertIdx l p vx hpl (σ.vars "fc")
  unfold bgPreIntro
  run_vcg
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_pos (by omega), hrd' _ (by omega)]
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_neg (by omega), if_pos (by omega), hvx]
  · refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
    nrmA
    rw [hins, if_neg (by omega), if_neg (by omega),
      show σ.vars "cw" + σ.vars "fc" - 1 = σ.vars "cw" + (σ.vars "fc" - 1) by omega,
      hrd' _ (by omega)]
  · rw [hrd' _ (by omega)]; exact hbd _
  · rw [show σ.vars "cw" + σ.vars "fc" - 1 = σ.vars "cw" + (σ.vars "fc" - 1) by omega,
      hrd' _ (by omega)]
    exact hbd _

/-- The length of the bag of an introduce node. -/
lemma bagL_intro_len (P : Params) {i : ℕ} (hk : kind P.D (i + 1) = 1) :
    (bagL P.D (i + 1)).length = (bagL P.D i).length + 1 := by
  rw [bagL_intro hk, List.length_insertIdx_of_le_length pos_le_length]

/-- **The state after the head of an introduce node**, without the description of the arrays. -/
structure HQ (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  i_ : σ.vars "i" = i0 + 1
  c_ : σ.vars "c" = i0
  s_ : σ.vars "s" = (bagL P.D i0).length
  vx_ : σ.vars "vx" = vertex P.D (i0 + 1)
  p_ : σ.vars "p" = pos (bagL P.D i0) (vertex P.D (i0 + 1))
  cw_ : σ.vars "cw" = i0 * P.wid
  s1_ : σ.vars "s1" = (bagL P.D i0).length + 1
  iw_ : σ.vars "iw" = (i0 + 1) * P.wid
  bs_ : σ.vars "bs" = (i0 + 1) * P.wid
  fn_ : σ.vars "fn" = (bagL P.D i0).length + 1
  k_ : kind P.D (i0 + 1) = 1

/-- The state after the head of an introduce node. -/
structure HP (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop extends HQ P B i0 σ where
  N : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ

lemma HQ.transfer {i0 : ℕ} {σ σ' : Env} (h : HQ P B i0 σ) (k : Keep σ σ')
    (hv : ∀ y ∈ ["i", "c", "s", "vx", "p", "cw", "s1", "iw", "bs", "fn"],
      σ'.vars y = σ.vars y) : HQ P B i0 σ' :=
  ⟨k.nc h.C, h.iN, by rw [hv "i" (by simp)]; exact h.i_, by rw [hv "c" (by simp)]; exact h.c_,
    by rw [hv "s" (by simp)]; exact h.s_, by rw [hv "vx" (by simp)]; exact h.vx_,
    by rw [hv "p" (by simp)]; exact h.p_, by rw [hv "cw" (by simp)]; exact h.cw_,
    by rw [hv "s1" (by simp)]; exact h.s1_, by rw [hv "iw" (by simp)]; exact h.iw_,
    by rw [hv "bs" (by simp)]; exact h.bs_, by rw [hv "fn" (by simp)]; exact h.fn_, h.k_⟩

lemma NI.of_arrs {I kk D w1 Tm i} {σ σ' : Env} (h : NI I kk D w1 Tm i σ)
    (he : σ'.arrs = σ.arrs) : NI I kk D w1 Tm i σ' :=
  ⟨fun j hj => by rw [he]; exact h.sz j hj, fun j hj t ht => by rw [he]; exact h.bg j hj t ht,
    fun j hj e he' => by rw [he]; exact h.tb j hj e he'⟩

theorem introBG_run {i0 : ℕ} (h : HP P B i0 σ) :
    ∃ σ4, Run B (fillLoop "BG" bgPreIntro) σ σ4 ((20 + 20 + 4) * ((bagL P.D i0).length + 1) + 6) ∧
      AgrA ["fc", "val"] "BG" σ σ4 ∧ σ4.out = σ.out ∧
      (σ4.arrs "BG").length = (σ.arrs "BG").length ∧
      RowDesc "BG" ((i0 + 1) * P.wid) (bagL P.D (i0 + 1)).length
        (fun t => (bagL P.D (i0 + 1))[t]!) σ σ4 := by
  have hC := h.C
  have hiN := h.iN
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
  have hl1 := bagL_intro_len P h.k_
  have hle1 := bagL_len_le P (j := i0 + 1) h.iN
  have hle0 := bagL_len_le P (j := i0) (by have := h.iN; omega)
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hb8 := hC.b8
  have hBpos : 0 < B := by omega
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ h.iN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlenBG := hC.lenBG
  have hvxB : σ.vars "vx" < B := by
    rw [h.vx_, ← vertex_eq P hC h.iN]; exact hC.O_lt (by omega) (by omega)
  have hpl : pos (bagL P.D i0) (vertex P.D (i0 + 1)) ≤ (bagL P.D i0).length := pos_le_length
  have hres := fillLoop_run (B := B) "BG" bgPreIntro (fun t => (bagL P.D (i0 + 1))[t]!)
    ["fc", "val"] 20 ((bagL P.D i0).length + 1) σ h.fn_ (by omega)
    (by rw [h.bs_]; omega) (fun t => by
      have := bagL_get_le P (j := i0 + 1) h.iN t; omega) (by simp) (by rw [h.bs_]; omega) (by
    intro σ' hF hA hlt
    have e1 : σ'.vars "p" = σ.vars "p" := hA.1 "p" (by simp)
    have e2 : σ'.vars "vx" = σ.vars "vx" := hA.1 "vx" (by simp)
    have e3 : σ'.vars "cw" = σ.vars "cw" := hA.1 "cw" (by simp)
    have hbsl : σ.vars "bs" = (i0 + 1) * P.wid := h.bs_
    obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := bgPreIntro_run (B := B) σ' (bagL P.D i0)
      (pos (bagL P.D i0) (vertex P.D (i0 + 1))) (vertex P.D (i0 + 1)) (i0 * P.wid)
      (by rw [e1, h.p_]) (by rw [e2, h.vx_]) (by rw [e3, h.cw_])
      (fun t ht => by
        rw [hF.2, if_neg (by rw [hbsl]; omega)]
        exact h.N.bg i0 (by omega) t ht) hpl (by omega)
      (by rw [hF.1]; omega)
      (fun t => by have := bagL_get_le P (j := i0) (by omega) t; omega)
      (by rw [← h.vx_]; exact hvxB) (by omega)
    refine ⟨σ'', r, ?_, by rw [ha], fun y hy => hfr y (by intro e; exact hy (by simp [e])),
      hfr "fc" (by decide), ho⟩
    rw [hv, ← bagL_intro h.k_])
  obtain ⟨σ4, r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ4, r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, h.bs_, hl1]

end Lax117284Proofs.Machine.TwNode
