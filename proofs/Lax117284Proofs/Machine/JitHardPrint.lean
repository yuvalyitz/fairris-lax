import Lax117284Proofs.Machine.JitHardSem

/-!
Writing the image of the reduction: the two counts, the due dates of the jobs, the due date of
each wall, and then, machine by machine, the processing time of every job and of every wall.
-/

namespace Lax117284Proofs.Machine.JitHardPrint

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.JitHardLoop
open Lax117284Proofs.Machine.JitHardFormat Lax117284Proofs.Machine.JitHardSem

variable {B : ℕ}

/-- The due date, plus one, of the job the counter names. -/
def dueBody : Com := emitVal (add (.get "TK" (add (V "o1") (V "i"))) (.lit 1))

/-- **A due date, on the number it reads.** -/
theorem dueCore (Sz dv : ℕ) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hp : dv + 1 + 4 < B) :
    Spec B (fun σ =>
        σ.vars "o1" + σ.vars "i" < (σ.arrs "TK").length ∧ σ.vars "o1" + σ.vars "i" < B ∧
        (σ.arrs "TK").getD (σ.vars "o1" + σ.vars "i") 0 = dv ∧
        σ.vars "o1" < B ∧ σ.vars "i" < B) dueBody
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (dv + 1) ∧
        σ'.arrs = σ.arrs ∧ ∀ y ∉ SCELL, σ'.vars y = σ.vars y) (48 * Sz + 100) := by
  unfold dueBody emitVal
  run_vcg [(EmitNat.emitNat_spec (B := B) Sz).frame]
  all_goals (
    have e1 := ‹(σ.arrs "TK").getD (σ.vars "o1" + σ.vars "i") 0 = dv›
    try simp at e1
    try simp [e1] at *
    first
    | omega
    | exact ⟨hp, hs _ hp⟩
    | (obtain ⟨hout, hfv, hfa, -, -⟩ := ‹_ ∧ (∀ y ∉ EmitNat.emitNat.wvars, _) ∧ _›
       refine ⟨by rw [hout], ?_, fun y hy => ?_⟩
       · funext b; exact hfa b (by simp [Out.warrs_emitNat])
       · simp only [SCELL, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
           not_or] at hy
         obtain ⟨h1, h2, h3, h4, hrest⟩ := hy
         have hy1 : y ∉ EmitNat.emitNat.wvars := by
           rw [Out.wvars_emitNat]; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
           tauto
         rw [hfv y hy1]
         simp [h2]))

theorem dueBody_spec (Sz : ℕ) (ns : List ℕ) (hsh : ShapeH ns)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B) (hL : 4 * ns.length + 16 < B) :
    Spec B (fun σ => CellPre ns σ ∧ σ.vars "i" < ns.getD 0 0) dueBody
      (fun σ σ' => σ'.out = σ.out ++ bitsNat (dueN ns (σ.vars "i")) ∧
        σ'.arrs = σ.arrs ∧ ∀ y ∉ SCELL, σ'.vars y = σ.vars y) (48 * Sz + 100) := by
  intro σ ⟨⟨hA, hlen, hn, hm, ho1, ho2⟩, hi⟩
  obtain ⟨hsh2, hshl, hshb⟩ := hsh
  have hE0 := hE 0 (by omega)
  have hE3 := hE (2 + ns.getD 0 0 + σ.vars "i") (by omega)
  obtain ⟨σ', r, hout, harr, hfv⟩ := dueCore (B := B) Sz (ns.getD (2 + ns.getD 0 0 + σ.vars "i") 0)
    hs (by omega) σ ⟨by rw [ho1]; omega, by rw [ho1]; omega,
      by rw [ho1]; exact hA _ (by omega), by rw [ho1]; omega, by omega⟩
  exact ⟨σ', r.mono (by omega), by rw [hout]; rfl, harr, hfv⟩

theorem oneBody_spec (Sz : ℕ) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 1 + 4 < B) :
    Spec B (fun _ => True) (emitLit 1)
      (fun σ σ' => σ'.out = σ.out ++ bitsNat 1 ∧ σ'.arrs = σ.arrs ∧
        ∀ y ∉ SCELL, σ'.vars y = σ.vars y) (48 * Sz + 50) := by
  intro σ _
  obtain ⟨σ', r, hout, hfv, harr⟩ := emitLit_spec (B := B) 1 Sz hB (hs 1 hB) σ trivial
  refine ⟨σ', r, hout, harr, fun y hy => hfv y ?_⟩
  simp only [SCELL, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    not_or] at hy ⊢
  tauto

/-- Everything a row reads. -/
def RowPre (ns : List ℕ) (σ : Env) : Prop :=
  CellPre ns σ ∧ σ.vars "Wl" = wallsN (ns.getD 0 0) (ns.getD 1 0)

/-- The scratch scalars of a row. -/
def SROW : List String := "jj" :: "kk" :: SCELL

/-- The row of machine `i`: the processing time of every job, and then of every wall. -/
def rowBody : Com := .seq (cLoop "jj" "n" cellBody) (cLoop "kk" "Wl" (emitLit 1))

/-- The cost of a row. -/
def Krow (Sz n W : ℕ) : ℕ := ((48 * Sz + 200) + 10 + 4) * n + 6 + ((48 * Sz + 50) + 10 + 4) * W + 6

theorem rowBody_spec (Sz : ℕ) (ns : List ℕ) (hsh : ShapeH ns)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B) (hL : 4 * ns.length + 16 < B) :
    Spec B (fun σ => RowPre ns σ ∧ σ.vars "i" < wallsN (ns.getD 0 0) (ns.getD 1 0)) rowBody
      (fun σ σ' => σ'.out = σ.out ++ ((List.range (ns.getD 0 0)).flatMap
          (fun j => bitsNat (cellN ns (σ.vars "i") j)) ++
          (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap (fun _ => bitsNat 1)) ∧
        σ'.arrs = σ.arrs ∧ ∀ y ∉ SROW, σ'.vars y = σ.vars y)
      (Krow Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0))) := by
  intro σ ⟨⟨hpre, hWl⟩, hi⟩
  obtain ⟨hA, hlen, hn, hm, ho1, ho2⟩ := hpre
  obtain ⟨hsh2, hshl, hshb⟩ := hsh
  have hn0 : 0 < ns.getD 0 0 := by
    rcases Nat.eq_zero_or_pos (ns.getD 0 0) with h | h
    · rw [h, wallsN_zero] at hi; omega
    · exact h
  have hW : wallsN (ns.getD 0 0) (ns.getD 1 0) = ns.getD 1 0 := wallsN_pos _ _ hn0
  have hE0 := hE 0 (by omega)
  have hE1 := hE 1 (by omega)
  -- the cells
  obtain ⟨σ1, r1, o1, hAg1⟩ := cLoop_spec (B := B) "jj" "n" cellBody ("jj" :: SCELL)
    (fun j => bitsNat (cellN ns (σ.vars "i") j)) (48 * Sz + 200) (ns.getD 0 0) σ (by simp)
    (by decide) hn (by omega) (by
      intro τ hAg hlt
      have hτi : τ.vars "i" = σ.vars "i" := hAg.2 "i" (by decide)
      obtain ⟨τ', r, hout, harr, hfv⟩ := cellBody_spec (B := B) Sz ns ⟨hsh2, hshl, hshb⟩ hs hE hL τ
        ⟨⟨fun k hk => by rw [hAg.1]; exact hA k hk, by rw [hAg.1]; exact hlen,
          by rw [hAg.2 "n" (by decide)]; exact hn, by rw [hAg.2 "m" (by decide)]; exact hm,
          by rw [hAg.2 "o1" (by decide)]; exact ho1,
          by rw [hAg.2 "o2" (by decide)]; exact ho2⟩, hlt, by rw [hτi]; exact hi⟩
      have hτ'j : τ'.vars "jj" = τ.vars "jj" := hfv "jj" (by decide)
      refine ⟨τ', r, by rw [hout, hτi], ⟨harr.trans hAg.1, fun y hy => ?_⟩, hτ'j⟩
      have hy' : y ∉ SCELL := fun h => hy (List.mem_cons_of_mem _ h)
      rw [hfv y hy', hAg.2 y hy])
  -- the walls
  have hWl1 : σ1.vars "Wl" = wallsN (ns.getD 0 0) (ns.getD 1 0) := by
    rw [hAg1.2 "Wl" (by decide), hWl]
  obtain ⟨σ2, r2, o2, hAg2⟩ := cLoop_spec (B := B) "kk" "Wl" (emitLit 1) ("kk" :: SCELL)
    (fun _ => bitsNat 1) (48 * Sz + 50) (wallsN (ns.getD 0 0) (ns.getD 1 0)) σ1 (by simp)
    (by decide) hWl1 (by rw [hW]; omega) (by
      intro τ hAg hlt
      obtain ⟨τ', r, hout, harr, hfv⟩ := oneBody_spec (B := B) Sz hs (by omega) τ trivial
      refine ⟨τ', r, hout, ⟨harr.trans hAg.1, fun y hy => ?_⟩, hfv "kk" (by decide)⟩
      have hy' : y ∉ SCELL := fun h => hy (List.mem_cons_of_mem _ h)
      rw [hfv y hy', hAg.2 y hy])
  refine ⟨σ2, (r1.seq r2).mono (by unfold Krow; omega), ?_, hAg2.1.trans hAg1.1, fun y hy => ?_⟩
  · rw [o2, o1, List.append_assoc]
  · have h1 : y ∉ "jj" :: SCELL := fun h => hy (by
      simp only [SROW, List.mem_cons] at h ⊢
      tauto)
    have h2 : y ∉ "kk" :: SCELL := fun h => hy (by
      simp only [SROW, List.mem_cons] at h ⊢
      tauto)
    rw [hAg2.2 y h2, hAg1.2 y h1]

end Lax117284Proofs.Machine.JitHardPrint
