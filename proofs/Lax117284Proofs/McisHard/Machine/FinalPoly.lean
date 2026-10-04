import Lax117284Proofs.McisHard.Machine.PredFinal
import Lax117284Proofs.Machine.ILoop
import Lax117284Proofs.McisHard.MathFinal
import Lax117284Proofs.Machine.SatAccept
import Lax117284Proofs.Machine.SatCong
import Lax117284Proofs.Machine.SatNk
import Lax117284Proofs.Machine.WrapTFinal

/-! ### `Lax117284Proofs.McisHard.Machine.PrintMat` -/

section
/-!
# Writing the Adjacency Matrix of `H` (WP7, Part 1)

Two nested counters `w`, `w2` below the scalar `pV` (`= kOf * nOf`); every iteration runs `bitCom`, which
reads `w`, `w2`, and writes the bit it leaves in `bt` to the output.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.ILoop
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit

open Classical in
/-- The bit of the matrix, as a number. -/
noncomputable def bitOf (ns : List ℕ) (w w2 : ℕ) : ℕ := if decide (adjF ns w w2) then 1 else 0

/-- One bit: compute it, write it. -/
def rowBody : Com := .seq bitCom (.write (.var "bt"))

/-- One row: the bits at `(w, w2)` for `w2 < pV`. -/
def rowCom : Com := fLoop "w2" "pV" rowBody

/-- The matrix: all the rows. -/
def matCom : Com := fLoop "w" "pV" rowCom

variable {B : ℕ}

theorem bitCom_warrs : bitCom.warrs = [] := by decide

theorem AB_w : "w" ∉ AB := by decide
theorem AB_w2 : "w2" ∉ AB := by decide
theorem AB_pV : "pV" ∉ AB := by decide
theorem AB_N : "N" ∉ AB := by decide
theorem AB_A2 : "A2" ∉ AB := by decide

theorem rowCom_run (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (Vv : ℕ) (hV : Vv + 8 < B) (σ : Env)
    (hctx : Ctx[ns, σ]) (hpv : σ.vars "pV" = Vv) (w0 : ℕ) (hw : σ.vars "w" = w0) (hw0 : w0 < B) :
    ∃ σ', Run B rowCom σ σ' ((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6) ∧
      σ'.out = σ.out ++ (List.range Vv).map (fun w2 => bitOf ns w0 w2) ∧ Ctx[ns, σ'] ∧
      σ'.vars "pV" = Vv ∧ σ'.vars "w" = w0 := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "w2" "pV" rowBody
    (fun j σ1 => Ctx[ns, σ1] ∧ σ1.vars "pV" = Vv ∧ σ1.vars "w" = w0 ∧
      σ1.out = σ.out ++ (List.range j).map (fun w2 => bitOf ns w0 w2))
    (Kbit (SlotsN ns) + 2) Vv σ hpv
    (fun j σ1 h => h.2.1) (by decide) (by omega)
    ⟨⟨by simpa [Env.setVar] using hctx.1, by simpa [Env.setVar] using hctx.2.1,
        by simpa [Env.setVar] using hctx.2.2⟩,
      by simp [Env.setVar, hpv], by simp [Env.setVar, hw], by simp [Env.setVar]⟩
    (fun j σ1 v h => ⟨⟨by simpa [Env.setVar] using h.1.1, by simpa [Env.setVar] using h.1.2.1,
        by simpa [Env.setVar] using h.1.2.2⟩, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2.1, by simpa [Env.setVar] using h.2.2.2⟩)
    (by
      intro j σ1 hq hj hjV
      obtain ⟨hc1, hp1, hw1, ho1⟩ := hq
      obtain ⟨σ2, r2, hbt, ha2, ho2, hi2, hf2⟩ := bitCom_run B ns hs hc hB hE σ1 hc1.1 hc1.2.1
        hc1.2.2 w0 j hw1 (by simpa using hj) (by omega) (by omega)
      have hbtB : σ2.vars "bt" < B := by rw [hbt]; split <;> omega
      have r3 : Run B (.write (.var "bt")) σ2 { σ2 with out := σ2.out ++ [σ2.vars "bt"] } 2 :=
        (Run.write (evalB_var hbtB)).mono (by simp [Expr.size])
      refine ⟨_, (r2.seq r3).mono (by omega), ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · simpa [ha2] using hc1.1
      · simpa [hf2 "N" AB_N] using hc1.2.1
      · simpa [hf2 "A2" AB_A2] using hc1.2.2
      · simpa [hf2 "pV" AB_pV] using hp1
      · simpa [hf2 "w" AB_w] using hw1
      · simp only [ho2, ho1, List.range_succ, List.map_append, List.append_assoc, hbt]
        simp [bitOf]
      · simpa [hf2 "w2" AB_w2] using hj)
  obtain ⟨hc2, hp2, hw2, ho2⟩ := hQ
  refine ⟨σ', r, ?_, hc2, hp2, hw2⟩
  simpa using ho2

theorem matCom_run (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) (hB : 60 * (SlotsN ns + 4) < B)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (Vv : ℕ) (hV : Vv + 8 < B) (σ : Env)
    (hctx : Ctx[ns, σ]) (hpv : σ.vars "pV" = Vv) :
    ∃ σ', Run B matCom σ σ' (((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6 + 10 + 4) * Vv + 6) ∧
      σ'.out = σ.out ++ (List.range Vv).flatMap (fun w => (List.range Vv).map
        (fun w2 => bitOf ns w w2)) ∧ Ctx[ns, σ'] ∧ σ'.vars "pV" = Vv := by
  obtain ⟨σ', r, hQ⟩ := iLoop_spec (B := B) "w" "pV" rowCom
    (fun j σ1 => Ctx[ns, σ1] ∧ σ1.vars "pV" = Vv ∧
      σ1.out = σ.out ++ (List.range j).flatMap (fun w => (List.range Vv).map
        (fun w2 => bitOf ns w w2)))
    ((Kbit (SlotsN ns) + 2 + 10 + 4) * Vv + 6) Vv σ hpv
    (fun j σ1 h => h.2.1) (by decide) (by omega)
    ⟨⟨by simpa [Env.setVar] using hctx.1, by simpa [Env.setVar] using hctx.2.1,
        by simpa [Env.setVar] using hctx.2.2⟩,
      by simp [Env.setVar, hpv], by simp [Env.setVar]⟩
    (fun j σ1 v h => ⟨⟨by simpa [Env.setVar] using h.1.1, by simpa [Env.setVar] using h.1.2.1,
        by simpa [Env.setVar] using h.1.2.2⟩, by simpa [Env.setVar] using h.2.1,
      by simpa [Env.setVar] using h.2.2⟩)
    (by
      intro j σ1 hq hj hjV
      obtain ⟨hc1, hp1, ho1⟩ := hq
      obtain ⟨σ2, r2, ho2, hc2, hp2, hw2⟩ := rowCom_run ns hs hc hB hE Vv hV σ1 hc1 hp1 j hj
        (by omega)
      refine ⟨σ2, r2, ⟨hc2, hp2, ?_⟩, hw2.trans hj.symm ▸ hj⟩
      rw [ho2, ho1, List.range_succ, List.flatMap_append]
      simp)
  obtain ⟨hc2, hp2, ho2⟩ := hQ
  exact ⟨σ', r, ho2, hc2, hp2⟩

end Lax117284Proofs.McisHard.Print

end

/-! ### `Lax117284Proofs.McisHard.Machine.PrintHdr` -/

section
/-!
# The Header of the Image of `H` (WP7, Part 2)

`hdrCom` computes `pK = kOf ns`, `pM = nOf ns`, `pV = pK * pM`; `preCom` writes the two numbers.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.FoldLoop Lax117284Proofs.Machine.ILoop
open Lax117284Proofs.Machine.Out (emitVar emitVar_spec)
open Lax117284Proofs.Machine.Bits (bitsNat)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit

variable {B : ℕ}

/-- `pK = kOf`, `pM = nOf`, `pV = pK * pM`. -/
def hdrCom : Com :=
  .seq (.ite (.eq (V "N") (.lit 0))
    (.seq (.assign "pK" (.lit 2)) (.assign "pM" (.lit 4)))
    (.seq (.assign "pM" (mul (V "N") (.lit 36)))
      (.assign "pK" (add (add (.get "TK" (.lit 1)) (.get "TK" (.lit 2))) (mul (V "N") (.lit 10))))))
    (.assign "pV" (mul (V "pK") (V "pM")))

theorem kOf_ge (ns : List ℕ) : 2 ≤ kOf ns := by
  unfold kOf; split_ifs with h <;> omega

theorem nOf_ge (ns : List ℕ) : 4 ≤ nOf ns := by
  unfold nOf; split_ifs with h
  · omega
  · unfold SlotsN at h ⊢; omega

theorem kOf_le_V (ns : List ℕ) : kOf ns ≤ kOf ns * nOf ns := by
  have := nOf_ge ns
  nlinarith

theorem nOf_le_V (ns : List ℕ) : nOf ns ≤ kOf ns * nOf ns := by
  have := kOf_ge ns
  nlinarith

set_option maxHeartbeats 1600000 in
theorem hdrCom_spec (ns : List ℕ) (hP : Pars B ns) (hV : kOf ns * nOf ns + 8 < B) :
    Spec B (fun σ => Ctx[ns, σ]) hdrCom
      (fun σ σ' => σ'.vars "pK" = kOf ns ∧ σ'.vars "pM" = nOf ns ∧
        σ'.vars "pV" = kOf ns * nOf ns ∧ Ctx[ns, σ'] ∧ σ'.out = σ.out) 40 := by
  have hk := kOf_le_V ns
  have hn := nOf_le_V ns
  have hE1 := hP.hE1
  have hlen := hP.hlen
  by_cases h0 : SlotsN ns = 0
  · have hkk : kOf ns = 2 := by unfold kOf; rw [if_pos h0]
    have hnn : nOf ns = 4 := by unfold nOf; rw [if_pos h0]
    run_vcg
    vcg_norm
    vcg_fin
  · have hkk : kOf ns = ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns := by
      unfold kOf; rw [if_neg h0]
    have hnn : nOf ns = SlotsN ns * 36 := by unfold nOf; rw [if_neg h0]
    run_vcg
    vcg_norm
    vcg_fin
    all_goals first | omega | (ring_nf at hV ⊢; omega)


/-- The whole image: the two numbers of the header, then the matrix. -/
def printCom : Com :=
  .seq hdrCom (.seq (emitVar "pK") (.seq (emitVar "pM") matCom))

/-- The cost of writing the image, with `V` the number of vertices of `H`. -/
def KprintM (Sz N V : ℕ) : ℕ :=
  40 + (48 * Sz + 50) + (48 * Sz + 50) + (((Kbit N + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6)

end Lax117284Proofs.McisHard.Print

end

/-! ### `Lax117284Proofs.McisHard.Machine.PrintMain` -/

section
/-!
# Writing the Image of `H` (WP7, Part 3): `printCom_run`
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Print

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.Out (emitVar emitVar_spec)
open Lax117284Proofs.Machine.Bits (bitsNat natBits natBits_encodeNat)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Bit
open Lax117284.Problems (encodeNat)

variable {B : ℕ}

open Classical in
/-- **The image on bits.** -/
theorem natBits_image (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns) :
    natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) =
      bitsNat (kOf ns) ++ bitsNat (nOf ns) ++ (List.range (kOf ns * nOf ns)).flatMap
        (fun w => (List.range (kOf ns * nOf ns)).map (fun w2 => bitOf ns w w2)) := by
  rw [Proved.encodeInstance_Hfin ns hs hc]
  simp only [natBits, List.map_append, List.map_flatMap, List.map_map]
  have h1 := natBits_encodeNat (kOf ns)
  have h2 := natBits_encodeNat (nOf ns)
  simp only [natBits] at h1 h2
  rw [h1, h2]
  rfl

theorem printCom_run (Sz : ℕ) (ns : List ℕ) (hs : ShapeF ns) (hc : CondN ns)
    (hB : 60 * (SlotsN ns + 4) < B) (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B)
    (hV : kOf ns * nOf ns + 8 < B) (hsz : ∀ v, v + 4 < B → v.size ≤ Sz) (σ : Env)
    (hctx : Ctx[ns, σ]) :
    ∃ σ', Run B printCom σ σ' (KprintM Sz (SlotsN ns) (kOf ns * nOf ns)) ∧
      σ'.out = σ.out ++ natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) := by
  have hP := pars_of B ns hs hB hE
  obtain ⟨σ1, r1, hK, hM, hVv, hc1, ho1⟩ := hdrCom_spec ns hP hV σ hctx
  have hkB := kOf_le_V ns
  have hnB := nOf_le_V ns
  obtain ⟨σ2, r2, o2, f2, a2⟩ := emitVar_spec (B := B) "pK" Sz σ1
    ⟨by rw [hK]; omega, by rw [hK]; exact hsz _ (by omega)⟩
  have c2 : Ctx[ns, σ2] := ⟨by rw [a2]; exact hc1.1, by rw [f2 "N" (by decide)]; exact hc1.2.1,
    by rw [f2 "A2" (by decide)]; exact hc1.2.2⟩
  have m2 : σ2.vars "pM" = nOf ns := by rw [f2 "pM" (by decide)]; exact hM
  have v2 : σ2.vars "pV" = kOf ns * nOf ns := by rw [f2 "pV" (by decide)]; exact hVv
  obtain ⟨σ3, r3, o3, f3, a3⟩ := emitVar_spec (B := B) "pM" Sz σ2
    ⟨by rw [m2]; omega, by rw [m2]; exact hsz _ (by omega)⟩
  have c3 : Ctx[ns, σ3] := ⟨by rw [a3]; exact c2.1, by rw [f3 "N" (by decide)]; exact c2.2.1,
    by rw [f3 "A2" (by decide)]; exact c2.2.2⟩
  have v3 : σ3.vars "pV" = kOf ns * nOf ns := by rw [f3 "pV" (by decide)]; exact v2
  obtain ⟨σ4, r4, o4, -, -⟩ := matCom_run ns hs hc hB hE (kOf ns * nOf ns) hV σ3 c3 v3
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintM; omega), ?_⟩
  rw [o4, o3, o2, m2, hK, ho1, natBits_image ns hs hc]
  simp

end Lax117284Proofs.McisHard.Print

end

/-! ### `Lax117284Proofs.McisHard.Machine.AcceptPrefix` -/

section
/-!
# Running a Store-Free Command on a Longer Array (WP8)

The token array `TK` the tokenizer leaves is as long as the input word, and the stream of the formula is
only a prefix of it.  A command that never stores into an array and never reads an entry past the end of
the arrays it is started on (a run on the shorter arrays exists) runs identically on longer arrays.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Prefix

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

theorem getElem?_of_prefix {l1 l2 : List ℕ} (h : l1 <+: l2) {k v : ℕ} (hu : l1[k]? = some v) :
    l2[k]? = some v := by
  obtain ⟨t, rfl⟩ := h
  have hk : k < l1.length := (List.getElem?_eq_some_iff.mp hu).1
  rw [List.getElem?_append_left hk]; exact hu

theorem evalB_prefix {B : ℕ} {σ1 σ : Env} (hv : σ.vars = σ1.vars)
    (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∀ (e : Expr) {v : ℕ}, e.evalB B σ1 = some v → e.evalB B σ = some v := by
  intro e
  induction e with
  | lit n => intro v h; simpa [Expr.evalB] using h
  | var x => intro v h; simpa [Expr.evalB, hv] using h
  | get a i ih =>
      intro v h
      simp only [Expr.evalB, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨k, hk, u, hu, hf⟩ := h
      exact ⟨k, ih hk, u, getElem?_of_prefix (ha a) hu, hf⟩
  | bin op e f ihe ihf =>
      intro v h
      simp only [Expr.evalB, Option.bind_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, ihe hm, n, ihf hn, hf⟩

theorem condB_prefix {B : ℕ} {σ1 σ : Env} (hv : σ.vars = σ1.vars)
    (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∀ (b : Cond) {r : Bool}, b.evalB B σ1 = some r → b.evalB B σ = some r := by
  intro b
  cases b with
  | eq e f =>
      intro r h
      simp only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, evalB_prefix hv ha e hm, n, evalB_prefix hv ha f hn, hf⟩
  | lt e f =>
      intro r h
      simp only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨m, hm, n, hn, hf⟩ := h
      exact ⟨m, evalB_prefix hv ha e hm, n, evalB_prefix hv ha f hn, hf⟩

/-- **A store-free run on shorter arrays is a run on longer arrays.** -/
theorem bigStepB_prefix {B : ℕ} {c : Com} (hw : c.warrs = []) {σ1 σ1' : Env} {k : ℕ}
    (h : BigStepB B c σ1 σ1' k) :
    ∀ σ : Env, σ.vars = σ1.vars → σ.out = σ1.out → σ.inp = σ1.inp →
      (∀ a, σ1.arrs a <+: σ.arrs a) →
      ∃ σ', BigStepB B c σ σ' k ∧ σ'.vars = σ1'.vars ∧ σ'.out = σ1'.out ∧ σ'.inp = σ1'.inp ∧
        σ'.arrs = σ.arrs ∧ σ1'.arrs = σ1.arrs := by
  induction h with
  | skip =>
      intro σ hv ho hi ha
      exact ⟨σ, .skip, hv, ho, hi, rfl, rfl⟩
  | assign he =>
      rename_i σ1 x e v
      intro σ hv ho hi ha
      refine ⟨σ.setVar x v, .assign (evalB_prefix hv ha e he), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Env.setVar, hv]
      · simp [Env.setVar, ho]
      · simp [Env.setVar, hi]
      · rfl
      · rfl
  | store hi he hk => simp [Com.warrs] at hw
  | seq h1 h2 ih1 ih2 =>
      rename_i c d σ1 σ2 σ3 k k'
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r1, v1, o1, i1, a1, e1⟩ := ih1 hw.1 σ hv ho hi ha
      obtain ⟨τ', r2, v2, o2, i2, a2, e2⟩ := ih2 hw.2 τ v1 o1 i1
        (fun a => by rw [e1, a1]; exact ha a)
      exact ⟨τ', r1.seq r2, v2, o2, i2, a2.trans a1, e2.trans e1⟩
  | ite_true hb hc ih =>
      rename_i b c d σ1 σ1' k
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r, v, o, i, a, e⟩ := ih hw.1 σ hv ho hi ha
      exact ⟨τ, .ite_true (condB_prefix hv ha b hb) r, v, o, i, a, e⟩
  | ite_false hb hd ih =>
      rename_i b c d σ1 σ1' k
      simp only [Com.warrs, List.append_eq_nil_iff] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r, v, o, i, a, e⟩ := ih hw.2 σ hv ho hi ha
      exact ⟨τ, .ite_false (condB_prefix hv ha b hb) r, v, o, i, a, e⟩
  | while_true hb hc hw' ih ih' =>
      rename_i b c σ1 σ2 σ3 k k'
      simp only [Com.warrs] at hw
      intro σ hv ho hi ha
      obtain ⟨τ, r1, v1, o1, i1, a1, e1⟩ := ih hw σ hv ho hi ha
      obtain ⟨τ', r2, v2, o2, i2, a2, e2⟩ := ih' (by simpa [Com.warrs] using hw) τ v1 o1 i1
        (fun a => by rw [e1, a1]; exact ha a)
      exact ⟨τ', .while_true (condB_prefix hv ha b hb) r1 r2, v2, o2, i2, a2.trans a1,
        e2.trans e1⟩
  | while_false hb =>
      rename_i b c σ1
      intro σ hv ho hi ha
      exact ⟨σ, .while_false (condB_prefix hv ha b hb), hv, ho, hi, rfl, rfl⟩
  | read h =>
      rename_i σ1 x v rest
      intro σ hv ho hi ha
      refine ⟨{ σ.setVar x v with inp := rest }, .read (by rw [hi]; exact h), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Env.setVar, hv]
      · simp [Env.setVar, ho]
      · rfl
      · rfl
      · rfl
  | write he =>
      rename_i σ1 e v
      intro σ hv ho hi ha
      refine ⟨{ σ with out := σ.out ++ [v] }, .write (evalB_prefix hv ha e he), hv, ?_, hi, rfl,
        rfl⟩
      simp [ho]

/-- The same for `Run`. -/
theorem run_prefix {B : ℕ} {c : Com} (hw : c.warrs = []) {σ1 σ1' : Env} {K : ℕ}
    (h : Run B c σ1 σ1' K) (σ : Env) (hv : σ.vars = σ1.vars) (ho : σ.out = σ1.out)
    (hi : σ.inp = σ1.inp) (ha : ∀ a, σ1.arrs a <+: σ.arrs a) :
    ∃ σ', Run B c σ σ' K ∧ σ'.vars = σ1'.vars ∧ σ'.out = σ1'.out ∧ σ'.inp = σ1'.inp ∧
      σ'.arrs = σ.arrs := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨σ', r, v, o, i, a, -⟩ := bigStepB_prefix hw hb σ hv ho hi ha
  exact ⟨σ', ⟨k, hk, r⟩, v, o, i, a⟩

end Lax117284Proofs.McisHard.Prefix

end

/-! ### `Lax117284Proofs.McisHard.Machine.AcceptRun` -/

section
/-!
# The Accepting Phase of the Reduction to `H` (WP8)

`accMcis`: read the counts, check the positions, and write the image `H` if the check passes (and nothing
otherwise).  The output is `natBits (encodeInstance (Hfin ns))` when `CondN ns` and empty otherwise.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Acc

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.SatOps Lax117284Proofs.Machine.SatSem
open Lax117284Proofs.Machine.SatRank Lax117284Proofs.Machine.SatCheck Lax117284Proofs.Machine.SatAccept
open Lax117284Proofs.Machine.SatCong Lax117284Proofs.Machine.Flag
open Lax117284Proofs.Machine.SatFormat (SlotsN ShapeF)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Print Lax117284Proofs.McisHard.Bit

variable {B : ℕ}

/-- The size of `H` is at most `400 (N + 1)²`. -/
theorem V_le (ns : List ℕ) : kOf ns * nOf ns ≤ 400 * (SlotsN ns + 1) ^ 2 := by
  unfold kOf nOf
  by_cases h : SlotsN ns = 0
  · rw [if_pos h, if_pos h, h]; norm_num
  · rw [if_neg h, if_neg h]
    have h1 : ns.getD 1 0 + ns.getD 2 0 ≤ SlotsN ns := by unfold SlotsN; omega
    have h2 : (ns.getD 1 0 + ns.getD 2 0 + 10 * SlotsN ns) * (SlotsN ns * 36) ≤
        (11 * SlotsN ns) * (SlotsN ns * 36) := Nat.mul_le_mul (by omega) le_rfl
    nlinarith [Nat.zero_le (SlotsN ns)]

/-- The phase after the tokenizer. -/
def accMcis : Com :=
  .seq prepSat (.seq chkLoop (.ite (.eq (V "ok") (.lit 1)) printCom .skip))

/-- The cost of the phase, on an input of `l` tokens. -/
def KaccM (Sz l : ℕ) : ℕ :=
  200 + ((120 + 64 * l + 4) * l + 6) + KprintM Sz l (400 * (l + 1) ^ 2)

lemma KprintM_mono (Sz N N' V V' : ℕ) (hN : N ≤ N') (hV : V ≤ V') :
    KprintM Sz N V ≤ KprintM Sz N' V' := by
  unfold KprintM Kbit
  have h1 : (128 * N + 1500 + 2 + 10 + 4) * V ≤ (128 * N' + 1500 + 2 + 10 + 4) * V' :=
    Nat.mul_le_mul (by omega) hV
  have h2 : ((128 * N + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V ≤
      ((128 * N' + 1500 + 2 + 10 + 4) * V' + 6 + 10 + 4) * V' :=
    Nat.mul_le_mul (by omega) hV
  omega

lemma KaccM_mono (Sz a b : ℕ) (h : a ≤ b) : KaccM Sz a ≤ KaccM Sz b := by
  unfold KaccM
  have h1 : (120 + 64 * a + 4) * a ≤ (120 + 64 * b + 4) * b := Nat.mul_le_mul (by omega) h
  have h2 := KprintM_mono Sz a b (400 * (a + 1) ^ 2) (400 * (b + 1) ^ 2) h
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  omega

theorem printCom_warrs : printCom.warrs = [] := by
  simp [printCom, hdrCom, matCom, rowCom, rowBody, Print.bitCom_warrs, Lax117284Proofs.Machine.Out.emitVar,
    Lax117284Proofs.Machine.FoldLoop.fLoop, Com.warrs, Lax117284Proofs.Machine.EmitNat.emitNat,
    Lax117284Proofs.Machine.EmitNat.sizeLoop, Lax117284Proofs.Machine.EmitNat.sizeBody,
    Lax117284Proofs.Machine.EmitNat.onesLoop, Lax117284Proofs.Machine.EmitNat.onesBody,
    Lax117284Proofs.Machine.EmitNat.digLoop, Lax117284Proofs.Machine.EmitNat.digBody]

lemma getD_of_take {arr ns : List ℕ} (h : arr.take ns.length = ns) :
    ∀ k < ns.length, arr.getD k 0 = ns.getD k 0 := fun k hk => by
  conv_rhs => rw [← h]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

open Classical in
set_option maxHeartbeats 3200000 in
/-- **The accepting phase.** `ns` is the stream of the formula, a prefix of the token array `arr`. -/
theorem accMcis_run (Sz l : ℕ) (arr ns : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hA : σ.arrs "TK" = arr) (hsh : ShapeF ns)
    (hpre : arr.take ns.length = ns)
    (hE : ∀ k < 3 + 2 * SlotsN ns, ns.getD k 0 + 8 < B) (hl : SlotsN ns ≤ l)
    (hB : 60 * (SlotsN ns + 4) < B)
    (hb : 4 * ns.getD 0 0 + 8 * (ns.getD 1 0 + ns.getD 2 0) + 64 < B)
    (hVl : 400 * (SlotsN ns + 1) ^ 2 + 8 < B) :
    ∃ σ', Run B accMcis σ σ' (KaccM Sz l) ∧
      σ'.out = σ.out ++ (if CondN ns then
        natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin ns)) else []) := by
  obtain ⟨S, hSdef⟩ : ∃ S, SlotsN ns = S := ⟨_, rfl⟩
  have hlenns : ns.length = 3 + 2 * S := by rw [hsh.2.1, hSdef]
  have hAg : Agree arr ns S := fun k hk => getD_of_take hpre k (by omega)
  have hSa : SlotsN arr = S := hAg.slots.trans hSdef
  have hlenA : 3 + 2 * S ≤ arr.length := by
    have := congrArg List.length hpre
    rw [List.length_take] at this
    omega
  rw [hSdef] at hE hl hB hVl
  have hB2 : 6 < B := by omega
  have hEa : ∀ k < 3 + 2 * S, arr.getD k 0 + 8 < B := fun k hk => by rw [hAg k hk]; exact hE k hk
  have hba : 4 * arr.getD 0 0 + 8 * (arr.getD 1 0 + arr.getD 2 0) + 64 < B := by
    rw [hAg.n, hAg.na, hAg.nb]; exact hb
  obtain ⟨σ1, r1, e1n, e1N, e1V3, e1A2, e1K7, e1K9, e1C, e1ok, e1a, e1o, e1f⟩ :=
    prepSat_run (B := B) arr σ hA (by omega) (fun k hk => hEa k (by omega)) hba
  rw [hSa] at e1N e1C e1ok
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  have hok0 : (if S < arr.getD 0 0 then 0 else 1) ≤ 1 := by split <;> omega
  have hEv : ∀ k < S, arr.getD (3 + 2 * k) 0 + 8 < B := fun k hk => hEa _ (by omega)
  have hEs : ∀ k < S, arr.getD (4 + 2 * k) 0 + 8 < B := fun k hk => hEa _ (by omega)
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := chkLoop_spec (B := B) arr S (arr.getD 0 0)
    (if S < arr.getD 0 0 then 0 else 1) σ1 rfl hEv hEs hlenA (by omega)
    (hEa 0 (by omega)) hok0 A1 e1N e1n e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have hcondA : σ2.vars "ok" = 1 ↔ CondN arr := by
    rw [e2ok, flagTo_eq_one]
    unfold CondN
    rw [hSa]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra h
      have : S < arr.getD 0 0 := by omega
      rw [if_pos this] at h1
      exact absurd h1 (by decide)
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [if_neg (by omega)], h2⟩
  have hcond : σ2.vars "ok" = 1 ↔ CondN ns := hcondA.trans (hAg.cond hSdef)
  have hokB : σ2.vars "ok" < B := by
    rw [e2ok]; have := flagTo_le (PassS arr) (if S < arr.getD 0 0 then 0 else 1) S; omega
  by_cases hok : σ2.vars "ok" = 1
  · have hc := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hcc : CondN ns := hc
    -- the state on which `printCom` runs: the token array is exactly the stream
    let σn : Env := { σ2 with arrs := fun a => if a = "TK" then ns else σ2.arrs a }
    have hctx : Ctx[ns, σn] := by
      refine ⟨by simp [σn], ?_, ?_⟩
      · show σ2.vars "N" = SlotsN ns
        rw [e2f "N" (by decide), e1N, hSdef]
      · show σ2.vars "A2" = 2 * ns.getD 1 0
        rw [e2f "A2" (by decide), e1A2, hAg.na]
    have hV : kOf ns * nOf ns + 8 < B := by
      have := V_le ns
      rw [hSdef] at this
      omega
    obtain ⟨σ3, r3, o3⟩ := printCom_run (B := B) Sz ns hsh hc (by rw [hSdef]; exact hB)
      (by rw [hSdef]; exact hE) hV hs σn hctx
    obtain ⟨σ4, r4, v4, o4, i4, a4⟩ := Prefix.run_prefix printCom_warrs r3 σ2 rfl rfl rfl (fun a => by
      by_cases h : a = "TK"
      · subst h; simp only [σn, if_true]; rw [A2]; exact hpre ▸ List.take_prefix _ _
      · simp [σn, h])
    have hK := KprintM_mono Sz (SlotsN ns) l (kOf ns * nOf ns) (400 * (l + 1) ^ 2)
      (by rw [hSdef]; exact hl) (le_trans (V_le ns) (by
        rw [hSdef]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)))
    refine ⟨σ4, (r1.seq (r2.seq (Run.ite_true hcondT r4))).mono ?_, ?_⟩
    · unfold KaccM
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [o4, o3, show σn.out = σ2.out from rfl, e2o, e1o, if_pos hcc]
  · have hno : ¬ CondN ns := fun h => hok (hcond.2 h)
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ2 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ2, (r1.seq (r2.seq (Run.ite_false hcondF Run.skip))).mono ?_, ?_⟩
    · unfold KaccM
      have h1 : (120 + 64 * S + 4) * S ≤ (120 + 64 * l + 4) * l := Nat.mul_le_mul (by omega) hl
      simp only [Cond.size, Expr.size]
      omega
    · rw [e2o, e1o, if_neg hno]; simp

end Lax117284Proofs.McisHard.Acc

end

/-! ### `Lax117284Proofs.McisHard.Machine.FinalStruct` -/

section
/-!
# The Reduction to `H` as a `WrapT` (WP9, Part 1)
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists
open Lax117284Proofs.Machine.SatFormat Lax117284Proofs.Machine.SatSem Lax117284Proofs.Machine.SatCong
open Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.TokModel
open Lax117284Proofs.Machine.TokProg (Tok.val)
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc

open scoped Classical

/-- The image is at most `2^(2L+4)`: `400 (S+1)² + 8 < 2^(2L+4) + 8L + 64` once `L ≥ 3 + 2S`. -/
theorem sq_le_pow (S : ℕ) : 400 * (S + 1) ^ 2 ≤ 1024 * 16 ^ S := by
  induction S with
  | zero => norm_num
  | succ n ih =>
    have e : 16 ^ (n + 1) = 16 * 16 ^ n := by ring
    rw [e]
    nlinarith [Nat.zero_le n]

theorem V_lt_B (S L B : ℕ) (hL : 3 + 2 * S ≤ L) (hB : 2 ^ (2 * L + 4) + 8 * L + 64 ≤ B) :
    400 * (S + 1) ^ 2 + 8 < B := by
  have h1 := sq_le_pow S
  have h2 : (1024 : ℕ) * 16 ^ S = 2 ^ (4 * S + 10) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    rw [show (1024 : ℕ) = 2 ^ 10 by norm_num, ← pow_add]; ring_nf
  have h3 : 2 ^ (4 * S + 10) ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **The reduction as a reduction on tokens.** -/
noncomputable def W : WrapT where
  E := EF
  nk := Lax117284Proofs.Machine.SatNk.nkF
  Knk := 80
  hnk := fun B Bt cap hB => Lax117284Proofs.Machine.SatNk.nkF_spec (B := B) Bt cap hB
  red := reduceMcis
  cond := fun ts => CondN (ts.map Tok.val)
  outW := fun ts => Lax117284.MulticolouredIndepSet.encodeInstance (Hfin (ts.map Tok.val))
  sem_acc := fun ts hc hcond => Proved.reduceMcis_code ts hc hcond
  rejW := []
  sem_rej := fun w h => Proved.reduceMcis_rej w h
  rej := Com.skip
  Krej := fun _ => 1
  rejRun := fun B Sz σ hs hB => ⟨σ, Run.skip, by simp [natBits]⟩
  acc := accMcis
  Kacc := KaccM
  Kmono := KaccM_mono
  accRun := fun B Sz L ts arr σ hconf harr hA hlenL hvals hB hs => by
    obtain ⟨hshape, hts⟩ := shape_of_conforms hconf
    have hsh := hshape
    obtain ⟨h3, hl, hsg⟩ := hshape
    have hlenns : (ts.map Tok.val).length = ts.length := by simp
    have harr' : arr.take (ts.map Tok.val).length = ts.map Tok.val := by rw [hlenns]; exact harr
    obtain ⟨S, hS⟩ : ∃ S, SlotsN (ts.map Tok.val) = S := ⟨_, rfl⟩
    have hl' := hl
    rw [hS] at hl' hsg
    have hval : ∀ k < (ts.map Tok.val).length, (ts.map Tok.val).getD k 0 < 2 ^ (L + 1) := by
      intro k hk
      rw [List.getD_eq_getElem _ _ hk]
      obtain ⟨t, ht, e⟩ := List.mem_map.mp (List.getElem_mem hk)
      rw [← e]
      exact hvals t ht
    have hL3 : 3 ≤ L := by omega
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hP8 : 8 ≤ 2 ^ L := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL3
    have hPL : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    have hPP : 8 * 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul_right _ hP8
    have hE : ∀ k < 3 + 2 * S, (ts.map Tok.val).getD k 0 + 8 < B := by
      intro k hk
      have := hval k (by omega)
      omega
    have hn0 := hval 0 (by omega)
    have hSN : 2 * (ts.map Tok.val).getD 1 0 + 3 * (ts.map Tok.val).getD 2 0 = S := hS
    have hVl : 400 * (S + 1) ^ 2 + 8 < B := V_lt_B S L B (by omega) hB
    obtain ⟨σ', r, o⟩ := accMcis_run (B := B) Sz ts.length arr (ts.map Tok.val) σ hs hA hsh harr'
      (by rw [hS]; exact hE) (by rw [hS]; omega) (by rw [hS]; omega) (by omega) (by rw [hS]; exact hVl)
    refine ⟨σ', r, ?_⟩
    rw [o]
    show _ = σ.out ++ (if CondN (ts.map Tok.val) then
      natBits (Lax117284.MulticolouredIndepSet.encodeInstance (Hfin (ts.map Tok.val))) else natBits [])
    simp [natBits]

end Lax117284Proofs.McisHard.Final

end

/-! ### `Lax117284Proofs.McisHard.Machine.FinalLayout` -/

section
/-!
# The Layout of the Reduction to `H` (WP9, Part 2)

The 90 scalars of the program and the two arrays; `Com.Ok`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine Lax117284Proofs.Machine.WrapT Lax117284Proofs.Machine.SatAccept
open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc Lax117284Proofs.McisHard.Print
open Lax117284Proofs.McisHard.Bit

/-- The scalars of the program and its arrays. -/
def layoutM : Layout :=
  ⟨["L", "rt", "rv", "Ln", "ph", "val", "pw", "i", "T", "kind", "j", "n3", "p", "c", "tv", "n", "na",
    "nb", "A2", "t3", "N", "V3", "C", "K7", "K9", "ok", "o", "vo", "so", "cnt", "vj", "sj", "pK", "pM",
    "pV", "v", "s", "u", "i2", "w", "w2", "bTi", "bTu", "bTj", "bTv", "bt", "bTn", "bTo", "bTr",
    "bTo2", "bTr2", "ba", "bb", "bpe", "bk1", "bk2", "bv1", "bs1", "bv2", "bs2", "bc", "bTx", "bTq",
    "bTt", "bj", "bu", "bs", "bq1", "bx", "by", "bz", "bm", "bd0", "bTqa", "bTta", "bg", "bg2", "bE1",
    "bE2", "bE", "bcd", "bd", "bTg", "bjp", "bF1", "bF2", "bF", "bl", "br1", "bTl"],
    ["a", "TK"], 12⟩

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 100000 in
theorem com_ok : Com.Ok layoutM W.mainW := by
  simp [WrapT.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, SatNk.nkF,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    accMcis, prepSat, SatCheck.chkLoop, SatCheck.chkBody, SatRank.rankCom, SatRank.rankLoop,
    SatRank.rankBody, SatRank.bumpS, printCom, hdrCom, matCom, rowCom, rowBody,
    FoldLoop.fLoop, bitCom, treeCom, compCom, cidCom, clauseCom, gadCom, peCom, linkCom, coCntCom,
    unmatchedCom, gadTest, gadChain, unmLeaf, slotDecode, posSlot, gadBlock, linkBlock, slotDec, slotSlot,
    Out.emitVar, EmitNat.emitNat, EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop,
    EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody, layoutM, Com.Ok, Cond.Ok, condExpr,
    Expr.Ok]

end Lax117284Proofs.McisHard.Final

end

/-! ### `Lax117284Proofs.McisHard.Machine.FinalPoly` -/

section
/-!
# The Cost of the Reduction to `H` Is Polynomial (WP9, Part 3)

`KaccM Sz l ≤ 4·10⁸ · (Sz + 1) · (l + 1)^5`.
-/

set_option autoImplicit false

namespace Lax117284Proofs.McisHard.Final

open Lax117284Proofs.McisHard Lax117284Proofs.McisHard.Acc Lax117284Proofs.McisHard.Print
open Lax117284Proofs.McisHard.Bit

theorem Kpoly (Sz l : ℕ) : KaccM Sz l ≤ 400000000 * (Sz + 1) * (l + 1) ^ 5 := by
  unfold KaccM KprintM Kbit
  obtain ⟨u, hu⟩ : ∃ u, u = l + 1 := ⟨_, rfl⟩
  rw [← hu]
  have hl : l ≤ u := by omega
  have hu1 : 1 ≤ u := by omega
  have p2 : u ≤ u ^ 2 := Nat.le_self_pow (by omega) u
  have p3 : u ^ 2 ≤ u ^ 3 := Nat.pow_le_pow_right hu1 (by omega)
  have p5 : u ^ 3 ≤ u ^ 5 := Nat.pow_le_pow_right hu1 (by omega)
  obtain ⟨V, hV⟩ : ∃ V, V = 400 * u ^ 2 := ⟨_, rfl⟩
  rw [← hV]
  have hX : 128 * l + 1500 + 2 + 10 + 4 ≤ 1644 * u := by omega
  have hA : (128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4 ≤ 657620 * u ^ 3 := by
    have h1 : (128 * l + 1500 + 2 + 10 + 4) * V ≤ (1644 * u) * (400 * u ^ 2) := by
      rw [hV]; exact Nat.mul_le_mul hX le_rfl
    nlinarith
  have hB : (((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6) ≤ 263048006 * u ^ 5 := by
    have h1 : ((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V ≤ (657620 * u ^ 3) * V :=
      Nat.mul_le_mul hA le_rfl
    have h2 : (657620 * u ^ 3) * V = 263048000 * u ^ 5 := by rw [hV]; ring
    nlinarith
  have hC : (120 + 64 * l + 4) * l + 6 ≤ 190 * u ^ 2 := by nlinarith
  have hs : 1 ≤ (Sz + 1) := by omega
  have hD : 200 + ((120 + 64 * l + 4) * l + 6) + (40 + (48 * Sz + 50) + (48 * Sz + 50) +
      (((128 * l + 1500 + 2 + 10 + 4) * V + 6 + 10 + 4) * V + 6)) ≤
      (263048006 + 190 + 400) * (Sz + 1) * u ^ 5 + 200 * (Sz + 1) := by nlinarith
  nlinarith

/-- **The reduction to normal-form Multicoloured Independent Set is polynomial-time computable**: a word RAM
program on the zeros and ones of its input (tokenizer, the check of the positions, and the matrix of `H`,
bit by bit, each bit from the ports of the two vertices), transferred to a Turing machine. -/
theorem reduceMcis_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id reduceMcis) :=
  Lax117284Proofs.Machine.WrapTFinal.polyTimeE W layoutM com_ok rfl (by simp [layoutM]) 400000000 5
    (by omega) (fun Sz l => Kpoly Sz l) (fun Sz => by
      show 1 ≤ 400000000 * (Sz + 1)
      omega)

end Lax117284Proofs.McisHard.Final

end
