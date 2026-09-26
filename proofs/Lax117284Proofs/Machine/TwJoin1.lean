import Lax117284Proofs.Machine.TwForget5

/-!
The program of a join node: the head and the row of the bag.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

/-- **The second child of a join node is earlier and has the same bag.** -/
lemma join_facts (P : Params) {i : ℕ} (hi : i + 1 < P.N) (hk : kind P.D (i + 1) = 3) :
    other P.D (i + 1) < i ∧ bagL P.D (other P.D (i + 1)) = bagL P.D i := by
  have hN : P.N = nodeCount P.D := rfl
  have hshape := P.hD.shape (i + 1) hi
  rcases hshape with h0 | ⟨_, h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, ho, hb⟩
  · omega
  · omega
  · omega
  · have hb' : bagAt P.I.clients P.D (other P.D (i + 1)) = bagAt P.I.clients P.D i := by
      simpa using hb
    obtain ⟨hp0, hm0⟩ := bagL_spec P.hD i (by omega)
    obtain ⟨hpo, hmo⟩ := bagL_spec P.hD (other P.D (i + 1)) (by omega)
    refine ⟨by omega, eq_of_mem_iff hpo hp0 fun x => ?_⟩
    rw [hmo, hm0, hb']

/-- **The table entry of a join node**, as a number. -/
lemma tbv_join {I : Lax117284.Scheduling.Instance} {kk : ℕ} {D : List ℕ} {i e : ℕ}
    (hk : kind D (i + 1) = 3) (ho : other D (i + 1) < i + 1) :
    tbv I kk D (i + 1) e = tbv I kk D i e * tbv I kk D (other D (i + 1)) e := by
  by_cases h1 : TB I kk D i e <;> by_cases h2 : TB I kk D (other D (i + 1)) e
  · rw [tbv_one ((TB_join hk ho).2 ⟨h1, h2⟩), tbv_one h1, tbv_one h2]
  · rw [tbv_zero (fun h => h2 ((TB_join hk ho).1 h).2), tbv_zero h2]; simp
  · rw [tbv_zero (fun h => h1 ((TB_join hk ho).1 h).1), tbv_zero h1]; simp
  · rw [tbv_zero (fun h => h1 ((TB_join hk ho).1 h).1), tbv_zero h1]; simp

/-- The sizes a join node needs. -/
def joinTail1 : Com := seqs
  [ .assign "s1" (V "s"),
    .assign "iw" (mul (V "i") (V "w1")),
    .assign "bs" (V "iw"),
    .assign "fn" (V "s") ]

/-- The head of the program of a join node. -/
def joinHead : Com := .seq recCom joinTail1

theorem joinHead_run {i0 : ℕ} (hC : NC P B σ)
    (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ) (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) :
    ∃ σ1, Run B joinHead σ σ1 100 ∧ Keep σ σ1 ∧ σ1.arrs = σ.arrs ∧
      σ1.vars "c" = i0 ∧ σ1.vars "s" = (bagL P.D i0).length ∧
      σ1.vars "ot" = other P.D (i0 + 1) ∧ σ1.vars "cw" = i0 * P.wid ∧
      σ1.vars "s1" = (bagL P.D i0).length ∧ σ1.vars "iw" = (i0 + 1) * P.wid ∧
      σ1.vars "bs" = (i0 + 1) * P.wid ∧ σ1.vars "fn" = (bagL P.D i0).length := by
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hlD : P.D.length = 1 + 3 * P.N := P.hD.length_eq
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
  have hot' : σ1.vars "ot" = other P.D (i0 + 1) := by rw [hot1, other_eq P hC hiN]
  have hs' : σ1.vars "s" = (bagL P.D i0).length := by
    rw [hs1, Nat.add_sub_cancel, hN.sz i0 (by omega)]
  have hcw' : σ1.vars "cw" = i0 * P.wid := by rw [hcw1, Nat.add_sub_cancel, hw1]
  have hi1v : σ1.vars "i" = i0 + 1 := by rw [A1.2 "i" (by simp [SR]), hi]
  have hw1v : σ1.vars "w1" = P.wid := by rw [A1.2 "w1" (by simp [SR]), hw1]
  obtain ⟨σ3, r3, e3⟩ : ∃ σ3, Run B joinTail1 σ1 σ3 40 ∧ σ3 =
      (((σ1.setVar "s1" (bagL P.D i0).length).setVar "iw" ((i0 + 1) * P.wid)).setVar "bs"
        ((i0 + 1) * P.wid)).setVar "fn" (bagL P.D i0).length := by
    unfold joinTail1 seqs
    run_vcg
    all_goals (try nrmA)
    all_goals try (first | omega | (simp only [hs', hi1v, hw1v]; omega))
    all_goals (try simp only [hs', hi1v, hw1v])
  have hv3 : ∀ y, y ∉ ["s1", "iw", "bs", "fn"] → σ3.vars y = σ1.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [e3]; simp [Env.setVar, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  have k1 := Keep.of_agr A1 SR_sub o1
  have k3 : Keep σ1 σ3 := by
    rw [e3]
    exact ((((Keep.refl σ1).setVar (by simp [SN]) _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _
  have har : σ3.arrs = σ.arrs := by rw [e3]; simp [A1.1]
  refine ⟨σ3, (r1.seq r3).mono (by omega), k1.trans k3, har, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv3 "c" (by simp), hc1]; simp
  · rw [hv3 "s" (by simp), hs']
  · rw [hv3 "ot" (by simp), hot']
  · rw [hv3 "cw" (by simp), hcw']
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]
  · rw [e3]; simp [Env.setVar]

/-! ### The row of the bag -/

/-- The value of the cell of the new bag: the child's entry. -/
def bgPreJoin : Com := .assign "val" (G "BG" (add (V "cw") (V "fc")))

theorem bgPreJoin_run (σ : Env) (l : List ℕ) (cw : ℕ) (hcw : σ.vars "cw" = cw)
    (hrd : ∀ t < l.length, (σ.arrs "BG").getD (cw + t) 0 = l[t]!)
    (hf : σ.vars "fc" < l.length) (hlen : cw + l.length ≤ (σ.arrs "BG").length)
    (hbd : ∀ t : ℕ, l[t]! < B) (hb : cw + l.length + 8 < B) :
    ∃ σ', Run B bgPreJoin σ σ' 10 ∧ σ'.vars "val" = l[σ.vars "fc"]! ∧ σ'.arrs = σ.arrs ∧
      (∀ y, y ≠ "val" → σ'.vars y = σ.vars y) ∧ σ'.out = σ.out := by
  have hrd' : ∀ t < l.length, (σ.arrs "BG").getD (σ.vars "cw" + t) 0 = l[t]! := by
    rw [hcw]; exact hrd
  unfold bgPreJoin
  run_vcg
  all_goals first
    | (refine ⟨?_, rfl, fun y hy => by simp [Env.setVar, hy], rfl⟩
       nrmA
       rw [hrd' _ (by omega)])
    | omega
    | (rw [hrd' _ (by omega)]; exact hbd _)

/-- **The state after the head of a join node**, without the description of the arrays. -/
structure HQj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop where
  C : NC P B σ
  iN : i0 + 1 < P.N
  i_ : σ.vars "i" = i0 + 1
  c_ : σ.vars "c" = i0
  s_ : σ.vars "s" = (bagL P.D i0).length
  ot_ : σ.vars "ot" = other P.D (i0 + 1)
  cw_ : σ.vars "cw" = i0 * P.wid
  s1_ : σ.vars "s1" = (bagL P.D i0).length
  iw_ : σ.vars "iw" = (i0 + 1) * P.wid
  bs_ : σ.vars "bs" = (i0 + 1) * P.wid
  fn_ : σ.vars "fn" = (bagL P.D i0).length
  k_ : kind P.D (i0 + 1) = 3

/-- The state after the head of a join node. -/
structure HPj (P : Params) (B : ℕ) (i0 : ℕ) (σ : Env) : Prop extends HQj P B i0 σ where
  N : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ

lemma HQj.transfer {i0 : ℕ} {σ σ' : Env} (h : HQj P B i0 σ) (k : Keep σ σ')
    (hv : ∀ y ∈ ["i", "c", "s", "ot", "cw", "s1", "iw", "bs", "fn"],
      σ'.vars y = σ.vars y) : HQj P B i0 σ' :=
  ⟨k.nc h.C, h.iN, by rw [hv "i" (by simp)]; exact h.i_, by rw [hv "c" (by simp)]; exact h.c_,
    by rw [hv "s" (by simp)]; exact h.s_, by rw [hv "ot" (by simp)]; exact h.ot_,
    by rw [hv "cw" (by simp)]; exact h.cw_,
    by rw [hv "s1" (by simp)]; exact h.s1_, by rw [hv "iw" (by simp)]; exact h.iw_,
    by rw [hv "bs" (by simp)]; exact h.bs_, by rw [hv "fn" (by simp)]; exact h.fn_, h.k_⟩

theorem joinBG_run {i0 : ℕ} (h : HPj P B i0 σ) :
    ∃ σ4, Run B (fillLoop "BG" bgPreJoin) σ σ4 ((10 + 20 + 4) * (bagL P.D i0).length + 6) ∧
      AgrA ["fc", "val"] "BG" σ σ4 ∧ σ4.out = σ.out ∧
      (σ4.arrs "BG").length = (σ.arrs "BG").length ∧
      RowDesc "BG" ((i0 + 1) * P.wid) (bagL P.D (i0 + 1)).length
        (fun t => (bagL P.D (i0 + 1))[t]!) σ σ4 := by
  have hC := h.C
  have hiN := h.iN
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join h.k_
  have hle0 := bagL_len_le P (j := i0) (by omega)
  have hb2 := hC.b2
  have hb3 := hC.b3
  have hb8 := hC.b8
  have hBpos : 0 < B := by omega
  have hNw : (i0 + 2) * P.wid ≤ P.N * P.wid := Nat.mul_le_mul_right _ h.iN
  have hi2' : (i0 + 2) * P.wid = i0 * P.wid + P.wid + P.wid := by ring
  have hi1' : (i0 + 1) * P.wid = i0 * P.wid + P.wid := by ring
  have hlenBG := hC.lenBG
  have hres := fillLoop_run (B := B) "BG" bgPreJoin (fun t => (bagL P.D (i0 + 1))[t]!)
    ["fc", "val"] 10 (bagL P.D i0).length σ h.fn_ (by omega)
    (by rw [h.bs_]; omega) (fun t => by
      have := bagL_get_le P (j := i0 + 1) h.iN t; omega) (by simp) (by rw [h.bs_]; omega) (by
    intro σ' hF hA hlt
    have e3 : σ'.vars "cw" = σ.vars "cw" := hA.1 "cw" (by simp)
    have hbsl : σ.vars "bs" = (i0 + 1) * P.wid := h.bs_
    obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := bgPreJoin_run (B := B) σ' (bagL P.D i0) (i0 * P.wid)
      (by rw [e3, h.cw_])
      (fun t ht => by
        rw [hF.2, if_neg (by rw [hbsl]; omega)]
        exact h.N.bg i0 (by omega) t ht) (by omega)
      (by rw [hF.1]; omega)
      (fun t => by have := bagL_get_le P (j := i0) (by omega) t; omega) (by omega)
    refine ⟨σ'', r, ?_, by rw [ha], fun y hy => hfr y (by intro e; exact hy (by simp [e])),
      hfr "fc" (by decide), ho⟩
    rw [hv, hl1])
  obtain ⟨σ4, r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ4, r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, h.bs_, hl1]

end Lax117284Proofs.Machine.TwNode
