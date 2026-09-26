import Lax117284Proofs.Machine.TwJoin2

/-!
The fill of the table of a join node, and the whole program of a join node.
-/

namespace Lax117284Proofs.Machine.TwNode

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender Lax117284Proofs.TwDigits Lax117284Proofs.TwBags Lax117284Proofs.TwDP
open Lax117284Proofs.TwList Lax117284Proofs.TwViol
open Lax117284Proofs.Machine.TwViol Lax117284Proofs.Machine.TwFill Lax117284Proofs.Machine.TwCf
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.Emit

variable {P : Params} {B : ℕ} {σ : Env}

theorem joinTB_run {i0 : ℕ} (hT : TCj P B i0 σ) (hbs : σ.vars "bs" = (i0 + 1) * P.tabs)
    (hfn : σ.vars "fn" = 2 ^ (P.m * (bagL P.D i0).length)) :
    ∃ σ', Run B (fillLoop "TB" joinCell) σ σ'
        ((30 + 20 + 4) * 2 ^ (P.m * (bagL P.D i0).length) + 6) ∧
      AgrA ["fc", "val"] "TB" σ σ' ∧ σ'.out = σ.out ∧
      (σ'.arrs "TB").length = (σ.arrs "TB").length ∧
      RowDesc "TB" ((i0 + 1) * P.tabs) ((2 ^ P.I.days) ^ (bagL P.D (i0 + 1)).length)
        (fun e => tbv P.I P.kk P.D (i0 + 1) e) σ σ' := by
  have hC := hT.C
  have hiN := hT.iN
  have hjf := join_facts P hiN hT.k_
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join hT.k_
  have hlen0 := bagL_len_le P (j := i0) (by omega)
  have hb1 := hC.b1
  have hlenTB := hC.lenTB
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hlen0
  have hpt0 : (2 ^ P.m) ^ (bagL P.D i0).length ≤ P.tabs := by
    rw [bpow']; exact hpt
  have hNt : (i0 + 2) * P.tabs ≤ P.N * P.tabs := Nat.mul_le_mul_right _ hiN
  have hi2t : (i0 + 2) * P.tabs = (i0 + 1) * P.tabs + P.tabs := by ring
  have hi1t : (i0 + 1) * P.tabs = i0 * P.tabs + P.tabs := by ring
  have hoi : (other P.D (i0 + 1) + 1) * P.tabs ≤ i0 * P.tabs := Nat.mul_le_mul_right _ (by omega)
  have hoi1 : (other P.D (i0 + 1) + 1) * P.tabs = other P.D (i0 + 1) * P.tabs + P.tabs := by ring
  have hres := fillLoop_run (B := B) "TB" joinCell (fun e => tbv P.I P.kk P.D (i0 + 1) e)
    ["fc", "val"] 30 (2 ^ (P.m * (bagL P.D i0).length))
    σ hfn (by omega) (by rw [hbs]; omega)
    (fun k => lt_of_le_of_lt tbv_le_one (by omega)) (by simp)
    (by rw [hbs]; omega) (by
      intro σ' hF hA hlt
      have hC' : NC P B σ' := hC.of_agrA hA hF.1
        (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inr rfl))
      have hS : ∀ y, y ∈ ["cbase", "ob"] → σ'.vars y = σ.vars y :=
        fun y hy => hA.1 y (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl <;> simp)
      have hT' : TCj P B i0 σ' :=
        ⟨hC', hiN, hT.k_, fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tb e he,
          fun e he => by
            rw [hF.2, if_neg (by rw [hbs]; omega)]; exact hT.tbo e he,
          by rw [hS "cbase" (by simp)]; exact hT.cbase_,
          by rw [hS "ob" (by simp)]; exact hT.ob_⟩
      obtain ⟨σ'', r, hv, ha, hfr, ho⟩ := joinCell_run hT' hlt
      exact ⟨σ'', r.mono (by omega), hv, ha, fun y hy => hfr y (fun h => hy (by simp [h])),
        hfr "fc" (by decide), ho⟩)
  obtain ⟨σ', r, hl, hg, hA, ho⟩ := hres
  refine ⟨σ', r, hA, ho, hl, fun k => ?_⟩
  rw [hg k, hbs, hl1, bpow]

/-- **The program of a join node.** -/
def joinCom : Com :=
  .seq joinHead (.seq (fillLoop "BG" bgPreJoin) (.seq joinMid (fillLoop "TB" joinCell)))

/-- What a join node costs. -/
def joinCost (P : Params) : ℕ :=
  100 + ((10 + 20 + 4) * P.wid + 6) + 100 + ((30 + 20 + 4) * P.tabs + 6)

theorem joinCom_run {i0 : ℕ} (hC : NC P B σ) (hN : NI P.I P.kk P.D P.wid P.tabs (i0 + 1) σ)
    (hi : σ.vars "i" = i0 + 1) (hiN : i0 + 1 < P.N) (hk : kind P.D (i0 + 1) = 3) :
    ∃ σ', Run B joinCom σ σ' (joinCost P) ∧ Keep σ σ' ∧
      NI P.I P.kk P.D P.wid P.tabs (i0 + 1 + 1) σ' ∧ σ'.out = σ.out := by
  have hjf := join_facts P hiN hk
  have hl1 : bagL P.D (i0 + 1) = bagL P.D i0 := bagL_join hk
  have hle0 := bagL_len_le P (j := i0) (by omega)
  obtain ⟨σ3, r3, k3, har3, hc3, hs3, hot3, hcw3, hs13, hiw3, hbs3, hfn3⟩ :=
    joinHead_run hC hN hi hiN
  have hQ3 : HQj P B i0 σ3 :=
    ⟨k3.nc hC, hiN, (k3.vars "i" (by simp [SN, SV, Stt, St2, SD])).trans hi, hc3, hs3, hot3,
      hcw3, hs13, hiw3, hbs3, hfn3, hk⟩
  have hP3 : HPj P B i0 σ3 := ⟨hQ3, hN.of_arrs har3⟩
  obtain ⟨σ4, r4, hA4, o4, hl4, hrow4⟩ := joinBG_run hP3
  have k4 : Keep σ3 σ4 := Keep.of_agrA hA4 hl4
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inl rfl)) o4
  have hQ4 : HQj P B i0 σ4 := hQ3.transfer k4 (fun y hy => hA4.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
  obtain ⟨σ5, r5, e5⟩ := joinMid_run hQ4
  have k5 : Keep σ4 σ5 := by
    rw [e5]; unfold midStateJ
    exact (((((Keep.refl σ4).setArr (Or.inl rfl) _ _).setVar (by simp [SN]) _).setVar
      (by simp [SN]) _).setVar (by simp [SN]) _).setVar (by simp [SN]) _
  have hTB5 : σ5.arrs "TB" = σ.arrs "TB" := by
    rw [e5]; simp [midStateJ, hA4.2 "TB" (by decide), har3]
  have hSZ5 : σ5.arrs "SZ" = (σ.arrs "SZ").set (i0 + 1) (bagL P.D i0).length := by
    rw [e5]; simp [midStateJ, hA4.2 "SZ" (by decide), har3]
  have hBG5 : σ5.arrs "BG" = σ4.arrs "BG" := by
    rw [e5]; simp [midStateJ]
  have hT5 : TCj P B i0 σ5 := by
    refine ⟨k5.nc hQ4.C, hiN, hk, fun e he => ?_, fun e he => ?_, ?_, ?_⟩
    · rw [hTB5]; exact hN.tb i0 (by omega) e he
    · rw [hTB5]
      exact hN.tb (other P.D (i0 + 1)) (by omega) e (by rw [hjf.2]; exact he)
    · rw [e5]; simp [midStateJ]
    · rw [e5]; simp [midStateJ]
  have hbs5 : σ5.vars "bs" = (i0 + 1) * P.tabs := by rw [e5]; simp [midStateJ]
  have hfn5 : σ5.vars "fn" = 2 ^ (P.m * (bagL P.D i0).length) := by
    rw [e5]; simp [midStateJ]
  obtain ⟨σ6, r6, hA6, o6, hl6, hrow6⟩ := joinTB_run hT5 hbs5 hfn5
  have k6 : Keep σ5 σ6 := Keep.of_agrA hA6 hl6
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp [SN]) (Or.inr (Or.inr rfl)) o6
  have hpt : 2 ^ (P.m * (bagL P.D i0).length) ≤ P.tabs := pow_le_tabs P hle0
  have hK : (30 + 20 + 4) * 2 ^ (P.m * (bagL P.D i0).length) ≤ (30 + 20 + 4) * P.tabs :=
    Nat.mul_le_mul le_rfl hpt
  refine ⟨σ6, (r3.seq (r4.seq (r5.seq r6))).mono (by unfold joinCost; omega),
    k3.trans (k4.trans (k5.trans k6)), ?_, by rw [o6, e5]; simp [midStateJ, o4, k3.out]⟩
  refine NI_next (i := i0 + 1) (σ0 := σ) hN (fun j hj => bagL_len_le P (by omega))
    (fun s hs => by rw [bpow]; exact pow_le_tabs P hs) ?_ ?_ ?_
  · intro k
    rw [hA6.2 "SZ" (by decide), hSZ5, getD_set']
    by_cases hk1 : k = i0 + 1
    · subst hk1
      rw [if_pos ⟨rfl, by have := hC.lenSZ; omega⟩, if_pos (by omega), hl1]
    · rw [if_neg (by omega), if_neg (by omega)]
  · intro k
    rw [hA6.2 "BG" (by decide), hBG5, hrow4, har3]
  · intro k
    rw [hrow6, hTB5]

end Lax117284Proofs.Machine.TwNode
