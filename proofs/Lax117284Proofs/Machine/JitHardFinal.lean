import Lax117284Proofs.Machine.JitHardSem
import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.JitHardFormat
import Lax117284Proofs.Machine.MisNk
import Lax117284Proofs.Machine.WrapTFinal

/-! ### `Lax117284Proofs.Machine.JitHardPrint` -/

section
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

end

/-! ### `Lax117284Proofs.Machine.JitHardAccept` -/

section
/-!
The whole of the reduction after the tokenizer has accepted: read the counts off the array, and
write the image.
-/

namespace Lax117284Proofs.Machine.JitHardAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.JitHardLoop
open Lax117284Proofs.Machine.JitHardFormat Lax117284Proofs.Machine.JitHardSem
open Lax117284Proofs.Machine.JitHardPrint

variable {B : ℕ}

lemma numBits_replicate (k a : ℕ) :
    numBits (List.replicate k a) = (List.range k).flatMap (fun _ => bitsNat a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', List.range_succ, List.flatMap_append, ← ih, numBits_append]
    simp

lemma numBits_map (l : List ℕ) (f : ℕ → ℕ) :
    numBits (l.map f) = l.flatMap (fun x => bitsNat (f x)) := by
  simp [numBits, List.flatMap_map]

lemma numBits_flatMap (l : List ℕ) (g : ℕ → List ℕ) :
    numBits (l.flatMap g) = l.flatMap (fun x => numBits (g x)) := by
  simp [numBits, List.flatMap_assoc]

/-- The image, as the bits of its numbers. -/
lemma numBits_outH (ns : List ℕ) :
    numBits (outH ns) = bitsNat (ns.getD 0 0 + wallsN (ns.getD 0 0) (ns.getD 1 0)) ++
      bitsNat (ns.getD 1 0) ++
      (List.range (ns.getD 0 0)).flatMap (fun j => bitsNat (dueN ns j)) ++
      (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap (fun _ => bitsNat 1) ++
      (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap (fun i =>
        (List.range (ns.getD 0 0)).flatMap (fun j => bitsNat (cellN ns i j)) ++
          (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap (fun _ => bitsNat 1)) := by
  unfold outH
  simp only [numBits_append, numBits_flatMap, numBits_map, numBits_replicate, numBits_cons,
    numBits_nil, List.append_nil, List.append_assoc]

/-- Write the whole image. -/
def printH : Com :=
  .seq (emitVar "J") (.seq (emitVar "m")
    (.seq (cLoop "i" "n" dueBody) (.seq (cLoop "i" "Wl" (emitLit 1)) (cLoop "i" "Wl" rowBody))))

/-- The cost of writing the image. -/
def KprintH (Sz n W : ℕ) : ℕ :=
  2 * (48 * Sz + 50) + (((48 * Sz + 100) + 10 + 4) * n + 6) +
    (((48 * Sz + 50) + 10 + 4) * W + 6) + ((Krow Sz n W + 10 + 4) * W + 6)

lemma wallsN_le_len (ns : List ℕ) (hsh : ShapeH ns) : wallsN (ns.getD 0 0) (ns.getD 1 0) ≤ ns.length := by
  obtain ⟨h2, hl, hb⟩ := hsh
  rcases Nat.eq_zero_or_pos (ns.getD 0 0) with h | h
  · rw [h, wallsN_zero]; omega
  · rw [wallsN_pos _ _ h]
    have : ns.getD 1 0 ≤ ns.getD 0 0 * ns.getD 1 0 := Nat.le_mul_of_pos_left _ h
    omega

theorem printH_run (Sz : ℕ) (ns : List ℕ) (hsh : ShapeH ns)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B) (hL : 4 * ns.length + 16 < B)
    (σ : Env) (hpre : RowPre ns σ) (hJ : σ.vars "J" = ns.getD 0 0 + wallsN (ns.getD 0 0) (ns.getD 1 0)) :
    ∃ σ', Run B printH σ σ' (KprintH Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0))) ∧
      σ'.out = σ.out ++ numBits (outH ns) := by
  obtain ⟨hcell, hWl⟩ := hpre
  obtain ⟨hA, hlen, hn, hm, ho1, ho2⟩ := hcell
  have hWle := wallsN_le_len ns hsh
  obtain ⟨hsh2, hshl, hshb⟩ := hsh
  have hE0 := hE 0 (by omega)
  have hE1 := hE 1 (by omega)
  -- the two counts
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "J" Sz σ
    ⟨by rw [hJ]; omega, by rw [hJ]; exact hs _ (by omega)⟩
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m" Sz σ1
    ⟨by rw [v1 "m" (by decide), hm]; omega, by rw [v1 "m" (by decide), hm]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have hpre2 : CellPre ns σ2 := ⟨fun k hk => by rw [a2, a1]; exact hA k hk,
    by rw [a2, a1]; exact hlen, by rw [z2 "n" (by decide)]; exact hn,
    by rw [z2 "m" (by decide)]; exact hm, by rw [z2 "o1" (by decide)]; exact ho1,
    by rw [z2 "o2" (by decide)]; exact ho2⟩
  have hn2 : σ2.vars "n" = ns.getD 0 0 := hpre2.2.2.1
  have hW2 : σ2.vars "Wl" = wallsN (ns.getD 0 0) (ns.getD 1 0) := by
    rw [z2 "Wl" (by decide)]; exact hWl
  -- the due dates
  obtain ⟨σ3, r3, o3, hAg3⟩ := cLoop_spec (B := B) "i" "n" dueBody ("i" :: SCELL)
    (fun j => bitsNat (dueN ns j)) (48 * Sz + 100) (ns.getD 0 0) σ2 (by simp) (by decide) hn2
    (by omega) (by
      intro τ hAg hlt
      obtain ⟨τ', r, hout, harr, hfv⟩ := dueBody_spec (B := B) Sz ns ⟨hsh2, hshl, hshb⟩ hs hE hL τ
        ⟨⟨fun k hk => by rw [hAg.1]; exact hpre2.1 k hk, by rw [hAg.1]; exact hpre2.2.1,
          by rw [hAg.2 "n" (by decide)]; exact hpre2.2.2.1,
          by rw [hAg.2 "m" (by decide)]; exact hpre2.2.2.2.1,
          by rw [hAg.2 "o1" (by decide)]; exact hpre2.2.2.2.2.1,
          by rw [hAg.2 "o2" (by decide)]; exact hpre2.2.2.2.2.2⟩, hlt⟩
      refine ⟨τ', r, hout, ⟨harr.trans hAg.1, fun y hy => ?_⟩, hfv "i" (by decide)⟩
      have hy' : y ∉ SCELL := fun h => hy (List.mem_cons_of_mem _ h)
      rw [hfv y hy', hAg.2 y hy])
  have z3 : ∀ y, y ∉ "i" :: SCELL → σ3.vars y = σ2.vars y := hAg3.2
  have hW3 : σ3.vars "Wl" = wallsN (ns.getD 0 0) (ns.getD 1 0) := by
    rw [z3 "Wl" (by decide), hW2]
  -- the walls
  obtain ⟨σ4, r4, o4, hAg4⟩ := cLoop_spec (B := B) "i" "Wl" (emitLit 1) ("i" :: SCELL)
    (fun _ => bitsNat 1) (48 * Sz + 50) (wallsN (ns.getD 0 0) (ns.getD 1 0)) σ3 (by simp)
    (by decide) hW3 (by omega) (by
      intro τ hAg hlt
      obtain ⟨τ', r, hout, harr, hfv⟩ := oneBody_spec (B := B) Sz hs (by omega) τ trivial
      refine ⟨τ', r, hout, ⟨harr.trans hAg.1, fun y hy => ?_⟩, hfv "i" (by decide)⟩
      have hy' : y ∉ SCELL := fun h => hy (List.mem_cons_of_mem _ h)
      rw [hfv y hy', hAg.2 y hy])
  have z4 : ∀ y, y ∉ "i" :: SCELL → σ4.vars y = σ3.vars y := hAg4.2
  have hW4 : σ4.vars "Wl" = wallsN (ns.getD 0 0) (ns.getD 1 0) := by
    rw [z4 "Wl" (by decide), hW3]
  -- the rows
  obtain ⟨σ5, r5, o5, hAg5⟩ := cLoop_spec (B := B) "i" "Wl" rowBody ("i" :: SROW)
    (fun i => (List.range (ns.getD 0 0)).flatMap (fun j => bitsNat (cellN ns i j)) ++
      (List.range (wallsN (ns.getD 0 0) (ns.getD 1 0))).flatMap (fun _ => bitsNat 1))
    (Krow Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0)))
    (wallsN (ns.getD 0 0) (ns.getD 1 0)) σ4 (by simp) (by decide) hW4 (by omega) (by
      intro τ hAg hlt
      have hz : ∀ y, y ∉ "i" :: SROW → τ.vars y = σ4.vars y := hAg.2
      have hzz : ∀ y, y ∉ "i" :: SCELL → σ4.vars y = σ2.vars y := fun y hy =>
        (z4 y hy).trans (z3 y hy)
      have hzy : ∀ y, y ∉ "i" :: SROW → τ.vars y = σ2.vars y := fun y hy =>
        (hz y hy).trans (hzz y (fun h => hy (by
          simp only [SROW, List.mem_cons] at h ⊢
          tauto)))
      have hτA : τ.arrs = σ2.arrs := hAg.1.trans (hAg4.1.trans hAg3.1)
      obtain ⟨τ', r, hout, harr, hfv⟩ := rowBody_spec (B := B) Sz ns ⟨hsh2, hshl, hshb⟩ hs hE hL τ
        ⟨⟨⟨fun k hk => by rw [hτA]; exact hpre2.1 k hk, by rw [hτA]; exact hpre2.2.1,
          by rw [hzy "n" (by decide)]; exact hpre2.2.2.1,
          by rw [hzy "m" (by decide)]; exact hpre2.2.2.2.1,
          by rw [hzy "o1" (by decide)]; exact hpre2.2.2.2.2.1,
          by rw [hzy "o2" (by decide)]; exact hpre2.2.2.2.2.2⟩,
          by rw [hzy "Wl" (by decide)]; exact hW2⟩, hlt⟩
      refine ⟨τ', r, hout, ⟨harr.trans hAg.1, fun y hy => ?_⟩, hfv "i" (by simp [SROW, SCELL, SCR])⟩
      have hy' : y ∉ SROW := fun h => hy (List.mem_cons_of_mem _ h)
      rw [hfv y hy', hAg.2 y hy])
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by unfold KprintH; omega), ?_⟩
  rw [o5, o4, o3, o2, o1, numBits_outH, ← hJ, ← hm, v1 "m" (by decide), hm]
  simp only [List.append_assoc]

/-- Read the counts off the array. -/
def prepH : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "Wl" (mul (V "m") (sub (V "n") (sub (V "n") (.lit 1)))))
  (.seq (.assign "J" (add (V "n") (V "Wl")))
  (.seq (.assign "o1" (add (.lit 2) (V "n")))
    (.assign "o2" (add (.lit 2) (mul (.lit 3) (V "n"))))))))

theorem prepH_spec (a b : ℕ) (hB : 3 * a + b + 16 < B) :
    Spec B (fun σ => (σ.arrs "TK").getD 0 0 = a ∧ (σ.arrs "TK").getD 1 0 = b ∧
        2 ≤ (σ.arrs "TK").length) prepH
      (fun σ σ' => σ'.vars "n" = a ∧ σ'.vars "m" = b ∧ σ'.vars "Wl" = wallsN a b ∧
        σ'.vars "J" = a + wallsN a b ∧ σ'.vars "o1" = 2 + a ∧ σ'.vars "o2" = 2 + 3 * a ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ∉ ["n", "m", "Wl", "J", "o1", "o2"] → σ'.vars y = σ.vars y) 100 := by
  have hw : b * (a - (a - 1)) ≤ b := wallsN_le a b
  run_vcg
  all_goals (
    have e0 := ‹(σ.arrs "TK").getD 0 0 = a›
    have e1 := ‹(σ.arrs "TK").getD 1 0 = b›
    have hl := ‹2 ≤ (σ.arrs "TK").length›
    try simp at e0 e1
    try simp [Env.setVar, e0, e1] at *
    first
    | omega
    | (refine ⟨rfl, fun y y1 y2 y3 y4 y5 y6 => ?_⟩
       simp [y1, y2, y3, y4, y5, y6]))

/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptH : Com := .seq prepH printH

/-- The cost of the accepting phase. -/
def KaccH (Sz n W : ℕ) : ℕ := 100 + KprintH Sz n W

theorem acceptH_run (Sz : ℕ) (ns : List ℕ) (hsh : ShapeH ns)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B) (hL : 4 * ns.length + 16 < B)
    (σ : Env) (hA : ∀ k < ns.length, (σ.arrs "TK").getD k 0 = ns.getD k 0)
    (hlen : ns.length ≤ (σ.arrs "TK").length) :
    ∃ σ', Run B acceptH σ σ' (KaccH Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0))) ∧
      σ'.out = σ.out ++ numBits (outH ns) := by
  have hsh' := hsh
  obtain ⟨hsh2, hshl, hshb⟩ := hsh
  have hE0 := hE 0 (by omega)
  have hE1 := hE 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1W, e1J, e1o1, e1o2, e1a, e1o, e1f⟩ :=
    prepH_spec (B := B) (ns.getD 0 0) (ns.getD 1 0) (by omega) σ
      ⟨by rw [hA 0 (by omega)], by rw [hA 1 (by omega)], by omega⟩
  obtain ⟨σ2, r2, o2⟩ := printH_run (B := B) Sz ns hsh' hs hE hL σ1
    ⟨⟨fun k hk => by rw [e1a]; exact hA k hk, by rw [e1a]; exact hlen, e1n, e1m, e1o1, e1o2⟩,
      e1W⟩ e1J
  exact ⟨σ2, (r1.seq r2).mono (by unfold KaccH; omega), by rw [o2, e1o]⟩

lemma KaccH_le (Sz n W l : ℕ) (hn : n ≤ l) (hW : W ≤ l) :
    KaccH Sz n W ≤ 400 * (Sz + 1) * (l + 1) ^ 2 := by
  unfold KaccH KprintH Krow
  have h1 : n * W ≤ l * l := Nat.mul_le_mul hn hW
  have h2 : W * W ≤ l * l := Nat.mul_le_mul hW hW
  have h3 : Sz * (n * W) ≤ Sz * (l * l) := Nat.mul_le_mul_left _ h1
  have h4 : Sz * (W * W) ≤ Sz * (l * l) := Nat.mul_le_mul_left _ h2
  have h5 : Sz * n ≤ Sz * l := Nat.mul_le_mul_left _ hn
  have h6 : Sz * W ≤ Sz * l := Nat.mul_le_mul_left _ hW
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le n, Nat.zero_le W, Nat.zero_le (Sz * l),
    Nat.zero_le (l * l), Nat.zero_le (Sz * (l * l))]

end Lax117284Proofs.Machine.JitHardAccept

end

/-! ### `Lax117284Proofs.Machine.JitHardNk` -/

section
/-!
What the format of an instance of interval scheduling with eligible machine sets expects next, as
a command: a number for each of the two counts and each of the `3 n` entries of the three
tables, and then a bit for each entry of the matrix.
-/

namespace Lax117284Proofs.Machine.JitHardNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.JitHardFormat
open Lax117284Proofs.Machine.MisNk (sub mul)

/-- What the format expects, the counts being `TK[0]` and `TK[1]`. -/
def nkH : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (mul (.lit 3) (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n3")) (set "kind" 0)
          (.seq (.assign "nm" (mul (.get "TK" (.lit 0)) (.get "TK" (.lit 1))))
            (.ite (.lt (sub (V "j") (V "n3")) (V "nm")) (set "kind" 1) (set "kind" 2))))))

/-- The code of what is expected after `Tn` tokens, the counts being `a` and `b`. -/
def kindCodeH (Tn a b : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindH a b (Tn - 2))

variable {B : ℕ}

theorem nkH_flat (Tn a b : ℕ) (hB : 3 * a + a * b + Tn + a + b + 16 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = a ∧
        (σ.arrs "TK").getD 1 0 = b ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkH
      (fun σ σ' => σ'.vars "kind" = kindCodeH Tn a b ∧
        (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 100 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = a›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = b›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y y1 y2 y3 y4 => by simp [y1, y2, y3, y4]⟩
    unfold kindCodeH kindH
    split_ifs <;> first | rfl | omega)

theorem setKind_spec (v : ℕ) (hv : v < B) :
    Spec B (fun _ => True) (set "kind" v)
      (fun σ σ' => σ'.vars "kind" = v ∧ (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkH_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt EH cap nkH 100 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3", "nm"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · have hE : EH toks = .num := by unfold EH; rw [if_pos h2]
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind_spec (B := B) 0 (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have h3 : 2 ≤ toks.length := by omega
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have hg : ∀ k, k < 2 → (σ.arrs "TK").getD k 0 = Tok.val (toks.getD k (.num 0)) := fun k hk => by
      have h1 : (σ.arrs "TK").getD k 0 = ((σ.arrs "TK").take toks.length).getD k 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega)]
      rw [h1, hTK, Lax117284Proofs.Machine.MisFormat.getD_map_val]
    have hb : ∀ k, k < 2 → Tok.val (toks.getD k (.num 0)) < Bt := fun k hk => by
      have hk' : k < toks.length := by omega
      rw [List.getD_eq_getElem _ _ hk']
      exact hsm _ (List.getElem_mem hk')
    have ha := hb 0 (by omega)
    have hb1 := hb 1 (by omega)
    have hab : Tok.val (toks.getD 0 (.num 0)) * Tok.val (toks.getD 1 (.num 0)) ≤ Bt * Bt :=
      Nat.mul_le_mul ha.le hb1.le
    have hbig : 3 * Tok.val (toks.getD 0 (.num 0)) + Tok.val (toks.getD 0 (.num 0)) *
        Tok.val (toks.getD 1 (.num 0)) + toks.length + Tok.val (toks.getD 0 (.num 0)) +
        Tok.val (toks.getD 1 (.num 0)) + 16 < B := by nlinarith
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkH_flat (B := B) toks.length
      (Tok.val (toks.getD 0 (.num 0))) (Tok.val (toks.getD 1 (.num 0))) hbig σ
      ⟨hT, hg 0 (by omega), hg 1 (by omega), fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1]
    unfold kindCodeH EH
    rw [if_neg h2, if_neg h2]

end Lax117284Proofs.Machine.JitHardNk

end

/-! ### `Lax117284Proofs.Machine.JitHardFinal` -/

section
/-!
The reduction from interval scheduling with eligible machine sets to just-in-time scheduling, as
a word RAM program on the zeros and ones of its input.
-/

namespace Lax117284Proofs.Machine.JitHardFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.JitHardFormat Lax117284Proofs.Machine.JitHardSem
open Lax117284Proofs.Machine.JitHardAccept Lax117284Proofs.Machine.JitHardNk
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan
open Lax117284Proofs.Machine.TokProg (Tok.val)

open scoped Classical

/-- The word every word that is not the code of a stream of the format is sent to. -/
def rejH : Word := numCode [1, 0, 1]

/-- The reduction, as a map on words: the image of a stream of the format, and the rejected
word for every other word. -/
noncomputable def redH (w : Word) : Word :=
  if h : ∃ ts, w = code ts ∧ Conforms EH ts then numCode (outH (h.choose.map Tok.val))
  else rejH

theorem redH_code (ts : List Tok) (hc : Conforms EH ts) :
    redH (code ts) = numCode (outH (ts.map Tok.val)) := by
  have h : ∃ ts', code ts = code ts' ∧ Conforms EH ts' := ⟨ts, rfl, hc⟩
  unfold redH
  rw [dif_pos h]
  obtain ⟨hw', hs'⟩ := h.choose_spec
  have hnn : h.choose = ts := by
    rw [← (accept_complete EH h.choose hs').2, ← hw']; exact (accept_complete EH ts hc).2
  rw [hnn]

theorem redH_rej (w : Word) (h : ¬ ∃ ts, w = code ts ∧ Conforms EH ts) : redH w = rejH := by
  unfold redH
  rw [dif_neg h]

lemma getD_eq_of_take' {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

/-- The cost of the accepting phase. -/
def KaccW (Sz l : ℕ) : ℕ := 400 * (Sz + 1) * (l + 1) ^ 2

lemma KaccW_mono (Sz a b : ℕ) (h : a ≤ b) : KaccW Sz a ≤ KaccW Sz b := by
  unfold KaccW
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EH
  nk := nkH
  Knk := 100
  hnk := fun B Bt cap hB => nkH_spec (B := B) Bt cap hB
  red := redH
  cond := fun _ => True
  outW := fun ts => numCode (outH (ts.map Tok.val))
  sem_acc := fun ts hc _ => redH_code ts hc
  rejW := rejH
  sem_rej := fun w h => redH_rej w (fun ⟨ts, hw, hc⟩ => h ⟨ts, hw, hc, trivial⟩)
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o]; unfold rejH; rw [natBits_numCode]⟩
  acc := acceptH
  Kacc := KaccW
  Kmono := KaccW_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    obtain ⟨ns, hns⟩ : ∃ ns, ts.map Tok.val = ns := ⟨_, rfl⟩
    rw [hns] at hshape
    have hlenns : ns.length = ts.length := by rw [← hns]; simp
    have harr' : arr.take ns.length = ns := by rw [hlenns, ← hns]; exact harr
    have hg := getD_eq_of_take' harr'
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr'
      rw [List.length_take] at this
      omega
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      have hk' : k < (ts.map Tok.val).length := by rw [hns]; exact hk
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk')
      have : (ts.map Tok.val)[k] = ns[k] := by simp [hns]
      rw [← this, ← e]
      exact hvals t ht
    have hp1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hp2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hp3 : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hp4 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hlenL' : ns.length ≤ L := by omega
    have hE : ∀ k < ns.length, 4 * ns.getD k 0 + 16 < B := fun k hk => by
      have := hval k hk
      omega
    have hL : 4 * ns.length + 16 < B := by omega
    obtain ⟨σ', r, o⟩ := acceptH_run (B := B) Sz ns hshape hs hE hL σ
      (fun k hk => by rw [hA]; exact hg k hk) (by rw [hA]; exact hlenA)
    refine ⟨σ', r.mono ?_, ?_⟩
    · show KaccH Sz (ns.getD 0 0) (wallsN (ns.getD 0 0) (ns.getD 1 0)) ≤ KaccW Sz ts.length
      unfold KaccW
      rw [← hlenns]
      have hshl := hshape.2.1
      exact KaccH_le Sz _ _ _ (by omega) (wallsN_le_len ns hshape)
    · rw [o, hns]
      simp [natBits_numCode]

/-- The scalars of the program. -/
def layoutH : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "nm",
    "n", "m", "Wl", "J", "o1", "o2", "jj", "kk", "bt", "pp", "dd", "v", "s", "u", "i2", "ix",
    "aa", "M"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutH W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, nkH,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptH, prepH, printH, JitHardLoop.cLoop, JitHardPrint.dueBody, JitHardPrint.rowBody,
    JitHardSem.cellBody, FreeAccept.rejectPrint, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutH, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 400 * (Sz + 1) * (l + 1) ^ 2 := fun _ _ => le_rfl

/-- **The reduction is a polynomial-time word RAM computation on the zeros and ones of its
input.** -/
theorem ramPolytime : Lax759944.RamPolytime.RamPolytime W.redBits :=
  WrapTFinal.ramPolytimeE W layoutH com_ok rfl (by simp [layoutH]) 400 2 (by omega) Kpoly
    (fun Sz => by
      show 3 * (48 * Sz + 50) ≤ 400 * (Sz + 1)
      omega)

end Lax117284Proofs.Machine.JitHardFinal

end
