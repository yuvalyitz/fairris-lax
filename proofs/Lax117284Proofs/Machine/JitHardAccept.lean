import Lax117284Proofs.Machine.JitHardPrint

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
