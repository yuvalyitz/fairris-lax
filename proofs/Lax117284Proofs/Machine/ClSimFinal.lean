import Lax117284Proofs.Machine.ClSimLoad

/-!
The interpreter, whole: load the program, set the constants, run the loop.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {B wp v : ℕ} {P : Program} {z : List ℕ}

/-- Set the constants of the word length, from `wpv`, `Mp` and `zl`, and the state of the machine
at the start. -/
def simInit (P : Program) : Com := seqs [
  asg "plen" (lit P.length), asg "mk" (.sub (V "Mp") (lit 1)),
  asg "hh" (.shiftr (.add (V "wpv") (lit 1)) (lit 1)),
  asg "hm" (.sub (.shiftl (lit 1) (V "hh")) (lit 1)),
  asg "hm2" (.sub (.shiftl (lit 1) (.sub (V "wpv") (V "hh"))) (lit 1)),
  asg "spc" (lit 0), asg "rd" (lit 0), asg "nout" (lit 0), asg "outv" (lit 0)]

theorem simInit_spec (hB : Bnd B wp) (hpl : P.length < B) :
    Spec B (fun σ => σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp) (simInit P)
      (fun σ σ' => σ'.vars "plen" = P.length ∧ σ'.vars "mk" = 2 ^ wp - 1 ∧
        σ'.vars "hh" = (wp + 1) / 2 ∧ σ'.vars "hm" = 2 ^ ((wp + 1) / 2) - 1 ∧
        σ'.vars "hm2" = 2 ^ (wp - (wp + 1) / 2) - 1 ∧ σ'.vars "spc" = 0 ∧ σ'.vars "rd" = 0 ∧
        σ'.vars "nout" = 0 ∧ σ'.vars "outv" = 0 ∧
        (∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
          σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) 100 := by
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hwlt : wp < 2 ^ wp := Nat.lt_two_pow_self
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have h1 : 2 ^ ((wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (wp - (wp + 1) / 2) ≤ 2 ^ wp := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.two_pow_pos ((wp + 1) / 2)
  have h4 := Nat.two_pow_pos (wp - (wp + 1) / 2)
  run_vcg
  all_goals
    obtain ⟨hwp, hMp⟩ : σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp := ⟨‹_›, ‹_›⟩
  all_goals try simp [Env.setVar, hwp, hMp]
  all_goals try omega
  all_goals try
    (intro y h1 h2 h3 h4 h5 h6 h7 h8 h9
     simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9])

/-- The interpreter with its program. -/
def simCom (P : Program) : Com := .seq (.seq (loadFrom 0 P) (simInit P)) interpLoop

/-- What the interpreter needs at the start. -/
def Pre0 (P : Program) (z : List ℕ) (wp : ℕ) (σ : Env) : Prop :=
  (σ.arrs "ip0").length = P.length ∧ (σ.arrs "ip1").length = P.length ∧
  (σ.arrs "ip2").length = P.length ∧ (σ.arrs "ip3").length = P.length ∧
  σ.arrs "om" = List.replicate (2 ^ wp) 0 ∧ σ.arrs "z" = z ∧ σ.vars "wpv" = wp ∧
  σ.vars "Mp" = 2 ^ wp ∧ σ.vars "zl" = z.length

/-- The scalars the interpreter may change. -/
def SV : List String := FV ++ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"]

/-- The arrays the interpreter may change. -/
def SA : List String := ["ip0", "ip1", "ip2", "ip3", "om"]

theorem progEnc_of_loaded {σ σ' : Env} (h : Pre0 P z wp σ) (hL : Loaded 0 P σ σ') : ProgEnc P σ' := by
  obtain ⟨l0, l1, l2, l3, -, -, -, -, -⟩ := h
  obtain ⟨-, -, -, -, ⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := hL
  refine ⟨by rw [a0, l0], by rw [a1, l1], by rw [a2, l2], by rw [a3, l3], ?_⟩
  intro j i hj
  have hjl : j < P.length := (List.getElem?_eq_some_iff.mp hj).1
  have hmap : ∀ f : Instr → ℕ, (P.map f).getD j 0 = f i := by
    intro f
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hj]
  have hc : 0 ≤ j ∧ j - 0 < P.length := ⟨Nat.zero_le _, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [b0, if_pos (by simpa using hc)]; exact hmap _
  · rw [b1, if_pos (by simpa using hc)]; exact hmap _
  · rw [b2, if_pos (by simpa using hc)]; exact hmap _
  · rw [b3, if_pos (by simpa using hc)]; exact hmap _

theorem lits_lt (HS : HypS B wp P z) : ∀ i ∈ P, lits i < B := by
  intro i hi
  have h1 := HS.hLits i hi
  have h2 := code_fst_le i
  have h3 := HS.hB
  simp only [Bnd] at h3
  have h4 := Nat.two_pow_pos wp
  simp only [lits]
  omega

/-- The machine has not started: the relations at the beginning. -/
theorem init_rel {σ0 σ1 σ2 : Env} (h0 : Pre0 P z wp σ0) (hL : Loaded 0 P σ0 σ1)
    (hI : σ2.vars "plen" = P.length ∧ σ2.vars "mk" = 2 ^ wp - 1 ∧
        σ2.vars "hh" = (wp + 1) / 2 ∧ σ2.vars "hm" = 2 ^ ((wp + 1) / 2) - 1 ∧
        σ2.vars "hm2" = 2 ^ (wp - (wp + 1) / 2) - 1 ∧ σ2.vars "spc" = 0 ∧ σ2.vars "rd" = 0 ∧
        σ2.vars "nout" = 0 ∧ σ2.vars "outv" = 0 ∧
        (∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
          σ2.vars y = σ1.vars y) ∧ σ2.arrs = σ1.arrs ∧ σ2.inp = σ1.inp ∧ σ2.out = σ1.out) :
    KRel P z wp σ2 ∧ DRel z wp v σ2 (initState z) := by
  obtain ⟨hplen, hmk, hhh, hhm, hhm2, hspc, hrd, hnout, houtv, hfr, harr, hinp, hout⟩ := hI
  have hpe := progEnc_of_loaded h0 hL
  obtain ⟨hv1, hi1, ho1, ha1, -⟩ := hL
  obtain ⟨l0, l1, l2, l3, hom, hz, hwp, hMp, hzl⟩ := h0
  have hom1 : σ1.arrs "om" = σ0.arrs "om" := ha1 "om" (by decide) (by decide) (by decide) (by decide)
  have hz1 : σ1.arrs "z" = σ0.arrs "z" := ha1 "z" (by decide) (by decide) (by decide) (by decide)
  have hnm : ∀ y, y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] →
      σ2.vars y = σ0.vars y := fun y hy => by rw [hfr y hy, hv1]
  refine ⟨⟨hplen, by rw [hnm "zl" (by decide)]; exact hzl, by rw [hnm "wpv" (by decide)]; exact hwp,
    by rw [hnm "Mp" (by decide)]; exact hMp, hmk, hhh, hhm, hhm2, by rw [harr, hz1]; exact hz,
    by simpa [ProgEnc, harr] using hpe⟩, ?_⟩
  refine ⟨by simp [hspc, initState], by rw [hrd]; exact Nat.zero_le _, by simp [hrd, initState],
    rfl, ?_, ?_, ?_, ?_⟩
  · rw [harr, hom1, hom]; simp
  · intro a ha
    rw [harr, hom1, hom]; simp [initState, List.getD_eq_getElem?_getD, List.getElem?_replicate, ha]
  · intro a; simp [initState, Nat.two_pow_pos]
  · left; exact ⟨rfl, hnout⟩

theorem loop_frame_ok : (∀ y ∈ interpLoop.wvars, y ∈ SV) ∧ (∀ a ∈ interpLoop.warrs, a ∈ SA) ∧
    ¬ interpLoop.reads ∧ interpLoop.NoWrite := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem loadInit_spec (HS : HypS B wp P z) :
    Spec B (Pre0 P z wp) (.seq (loadFrom 0 P) (simInit P))
      (fun σ σ2 => KRel P z wp σ2 ∧ DRel z wp v σ2 (initState z) ∧ σ2.vars "spc" < B ∧
        (∀ y, y ∉ SV → σ2.vars y = σ.vars y) ∧ (∀ a, a ∉ SA → σ2.arrs a = σ.arrs a) ∧
        σ2.inp = σ.inp ∧ σ2.out = σ.out) (20 * P.length + 1 + 100) := by
  have hload := loadFrom_spec (B := B) P 0 (lits_lt HS) (by simpa using HS.hpl)
  have hinit := simInit_spec (B := B) (P := P) HS.hB HS.hpl
  refine Spec.seq (P' := fun σ => σ.vars "wpv" = wp ∧ σ.vars "Mp" = 2 ^ wp)
    (Spec.pre hload (fun σ h => by
      obtain ⟨l0, l1, l2, l3, -⟩ := h
      exact ⟨by omega, by omega, by omega, by omega⟩)) hinit ?_ ?_
  · intro σ σ1 h0 hL
    obtain ⟨-, -, -, -, -, -, hwp, hMp, -⟩ := h0
    obtain ⟨hv1, -⟩ := hL
    exact ⟨by rw [hv1]; exact hwp, by rw [hv1]; exact hMp⟩
  · intro σ σ1 σ2 h0 hL hI
    have hrel := init_rel (v := v) h0 hL hI
    obtain ⟨hplen, hmk, hhh, hhm, hhm2, hspc, hrd, hnout, houtv, hfr, harr, hinp, hout⟩ := hI
    obtain ⟨hv1, hi1, ho1, ha1, -⟩ := hL
    refine ⟨hrel.1, hrel.2, by rw [hspc]; have := HS.hpl; omega, ?_, ?_, ?_, ?_⟩
    · intro y hy
      have : y ∉ ["plen", "mk", "hh", "hm", "hm2", "spc", "rd", "nout", "outv"] := fun h =>
        hy (by simp only [SV, List.mem_append]; exact Or.inr h)
      rw [hfr y this, hv1]
    · intro a ha
      have h0 : a ≠ "ip0" := fun e => ha (by simp [SA, e])
      have h1 : a ≠ "ip1" := fun e => ha (by simp [SA, e])
      have h2 : a ≠ "ip2" := fun e => ha (by simp [SA, e])
      have h3 : a ≠ "ip3" := fun e => ha (by simp [SA, e])
      rw [harr, ha1 a h0 h1 h2 h3]
    · rw [hinp, hi1]
    · rw [hout, ho1]

/-- **The interpreter runs a machine program that halts with the output `[v]`.** From the state in
which the program is not yet loaded, the memory is zero, the input is in `z`, the counter is set
to the word length `wp` and its power, the command reaches a state with `nout = 1`, `outv = v`, and
changes nothing but the scalars `SV` and the arrays `SA`. -/
theorem simCom_spec (HS : HypS B wp P z) (t : ℕ) (hrun : RunsTo wp P z [v] t) :
    Spec B (Pre0 P z wp) (simCom P)
      (fun σ σ' => σ'.vars "nout" = 1 ∧ σ'.vars "outv" = v ∧
        (∀ y, y ∉ SV → σ'.vars y = σ.vars y) ∧ (∀ a, a ∉ SA → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) (20 * P.length + 101 + ((t + 1) * 604 + 4)) := by
  obtain ⟨k, sf, hk, hstep, hout, ht⟩ := hrun
  have hkt : k ≤ t := by rw [ht]; exact Nat.le_add_right _ _
  have hloop : Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ (initState z) ∧ σ.vars "spc" < B)
      interpLoop (fun σ σ' => KRel P z wp σ' ∧ Fin' P z wp v σ' sf) ((k + 1) * 604 + 4) := by
    intro σ ⟨hK, hD, hsB⟩
    obtain ⟨σ', hr, hK', hF⟩ := loop_run HS sf hout hstep k (initState z) σ hK hD hsB hk
    exact ⟨σ', hr, hK', hF⟩
  obtain ⟨hv, ha, hr, hw⟩ := loop_frame_ok
  refine Spec.mono (Spec.seq (loadInit_spec (v := v) HS) (Spec.frame hloop)
    (fun σ σ2 _ h => ⟨h.1, h.2.1, h.2.2.1⟩) ?_) (by nlinarith)
  intro σ σ2 σ' h0 hQ hQ'
  obtain ⟨hK, hD, hsB, hf1, hf2, hf3, hf4⟩ := hQ
  obtain ⟨⟨hK', ⟨hDf, -⟩⟩, hf1', hf2', hf3', hf4'⟩ := hQ'
  refine ⟨?_, ?_, fun y hy => ?_, fun a ha' => ?_, ?_, ?_⟩
  · have := hDf.out
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [hout] at h1; simp at h1
    · exact h2
  · have := hDf.out
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [hout] at h1; simp at h1
    · exact h3
  · rw [hf1' y (fun h => hy (hv y h |> fun h' => h')), hf1 y hy]
  · rw [hf2' a (fun h => ha' (ha a h)), hf2 a ha']
  · rw [hf3' hr, hf3]
  · rw [hf4' hw, hf4]

end Lax117284Proofs.Machine.ClSim
