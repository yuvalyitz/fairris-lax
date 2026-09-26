import Lax117284Proofs.Machine.ClSimDisp

/-!
One iteration of the interpreter: fetch, dispatch, commit.
-/

namespace Lax117284Proofs.Machine.ClSim

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

variable {B wp v : ℕ} {s : State} {P : Program} {z : List ℕ}

/-- The scalars a fetch assigns. -/
def FV : List String := ["op", "fa", "fb", "fc", "ra", "rb", "rc", "xa", "xv", "yv", "xx", "wf",
  "wa", "wv", "npc", "rdi", "wo", "wov"]

/-- `σ'` differs from `σ` only in the scalars of the list. -/
def AgreeOff (L : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ ∀ y, y ∉ L → σ'.vars y = σ.vars y

theorem KRel.agree {σ σ' : Env} (h : KRel P z wp σ) (hA : AgreeOff FV σ σ') : KRel P z wp σ' := by
  obtain ⟨ha, -, -, hv⟩ := hA
  have hp : ProgEnc P σ' := by simpa [ProgEnc, ha] using h.prog
  exact ⟨by rw [hv "plen" (by decide)]; exact h.plen, by rw [hv "zl" (by decide)]; exact h.zl,
    by rw [hv "wpv" (by decide)]; exact h.wpv, by rw [hv "Mp" (by decide)]; exact h.Mp,
    by rw [hv "mk" (by decide)]; exact h.mask, by rw [hv "hh" (by decide)]; exact h.hh,
    by rw [hv "hm" (by decide)]; exact h.hm, by rw [hv "hm2" (by decide)]; exact h.hm2,
    by rw [ha]; exact h.zarr, hp⟩

theorem DRel.agree {σ σ' : Env} (h : DRel z wp v σ s) (hA : AgreeOff FV σ σ') : DRel z wp v σ' s := by
  obtain ⟨ha, -, -, hv⟩ := hA
  refine ⟨by rw [hv "spc" (by decide)]; exact h.spc, by rw [hv "rd" (by decide)]; exact h.rd,
    by rw [hv "rd" (by decide)]; exact h.inp, h.input, by rw [ha]; exact h.omlen,
    fun a ha' => by rw [ha]; exact h.mem a ha', h.word, ?_⟩
  rw [hv "nout" (by decide), hv "outv" (by decide)]
  exact h.out

set_option maxHeartbeats 3200000 in
theorem code_fst_le (i : Instr) : (code i).1 ≤ 17 := by cases i <;> simp [code]

set_option maxHeartbeats 3200000 in
theorem fetch_spec (i : Instr) (H : Hyp B wp s P z)
    (hL : (code i).2.1 < B ∧ (code i).2.2.1 < B ∧ (code i).2.2.2 < B) :
    Spec B (fun σ => KRel P z wp σ ∧ DRel z wp v σ s ∧ P[s.pc]? = some i) fetchCom
      (fun σ σ' => Fetched wp s (code i).1 (code i).2.1 (code i).2.2.1 (code i).2.2.2 σ' ∧
        AgreeOff FV σ σ') 200 := by
  obtain ⟨hB, hw, hzB, hzE, hzE', hpl, hpc'⟩ := H
  have hpos : 0 < 2 ^ wp := Nat.two_pow_pos wp
  have hB' : 8 * 2 ^ wp + 32 < B := hB
  have hwlt : ∀ x, s.mem x < 2 ^ wp := hw
  run_vcg
  all_goals
    obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := ‹KRel P z wp _›
    obtain ⟨hspc, hrd, hinp, hinput, homlen, hmem, hword, hout⟩ := ‹DRel z wp v _ s›
    have hget := ‹P[s.pc]? = some i›
    obtain ⟨hl0, hl1, hl2, hl3, henc⟩ := hprog
    obtain ⟨he0, he1, he2, he3⟩ := henc s.pc i hget
    have hpc : s.pc < P.length := (List.getElem?_eq_some_iff.mp hget).1
    have hb0 : ∀ h : s.pc < (‹Env›.arrs "ip0").length, (‹Env›.arrs "ip0")[s.pc] = (code i).1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he0
    have hb1 : ∀ h : s.pc < (‹Env›.arrs "ip1").length, (‹Env›.arrs "ip1")[s.pc] = (code i).2.1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he1
    have hb2 : ∀ h : s.pc < (‹Env›.arrs "ip2").length, (‹Env›.arrs "ip2")[s.pc] = (code i).2.2.1 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he2
    have hb3 : ∀ h : s.pc < (‹Env›.arrs "ip3").length, (‹Env›.arrs "ip3")[s.pc] = (code i).2.2.2 := by
      intro h; simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using he3
    have hmem' : ∀ x, (‹Env›.arrs "om")[x % 2 ^ wp]?.getD 0 = s.mem (x % 2 ^ wp) :=
      fun x => by simpa [List.getD_eq_getElem?_getD] using hmem _ (Nat.mod_lt _ hpos)
    have hmemw : ∀ x, (‹Env›.arrs "om")[s.mem x]?.getD 0 = s.mem (s.mem x) :=
      fun x => by simpa [List.getD_eq_getElem?_getD] using hmem _ (hword x)
    have hmemI : ∀ (k : ℕ) (h : k < (‹Env›.arrs "om").length), (‹Env›.arrs "om")[k] = s.mem k :=
      fun k h => by
        have := hmem k (homlen ▸ h)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using this
    have hop17 := code_fst_le i
    have hwB : ∀ x, s.mem x < B := fun x => lt_of_lt_of_le (hw x) (by omega)
    have hwL : ∀ x, s.mem x < (‹Env›.arrs "om").length := fun x => homlen ▸ hword x
    have hmodw : ∀ x, s.mem x % 2 ^ wp = s.mem x := fun x => Nat.mod_eq_of_lt (hw x)
  all_goals try simp only [Env.setVar, arrs_setVar, String.reduceEq, ↓reduceIte] at *
  all_goals try omega
  all_goals try
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, rfl, rfl, ?_⟩
  all_goals try simp [Env.setVar, hspc, hl0, hl1, hl2, hl3, he0, he1, he2, he3, hb0, hb1, hb2, hb3,
    hmask, hmem', hmemw, hpc, hplen, hzl, hwpv, hMp, hhh, hhm, hhm2, hword,
    hL.1, hL.2.1, hL.2.2, hwB, hwL, hmodw, hmemI]
  all_goals try omega
  all_goals try
    (intro y hy
     simp only [FV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
     obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hy
     simp [Env.setVar, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18])

/-- The environment after the commit, as a function. -/
def commitEnv (σ : Env) : Env :=
  let σ1 := if σ.vars "wf" = 1 then σ.setArr "om" (σ.vars "wa") (σ.vars "wv") else σ
  let σ2 := if σ1.vars "wo" = 1 then (σ1.setVar "outv" (σ1.vars "wov")).setVar "nout" 1 else σ1
  let σ3 := σ2.setVar "spc" (σ2.vars "npc")
  σ3.setVar "rd" (σ3.vars "rd" + σ3.vars "rdi")

theorem commit_run (hK : True) :
    Spec B (fun σ => σ.vars "wf" ≤ 1 ∧ σ.vars "wo" ≤ 1 ∧
        (σ.vars "wf" = 1 → σ.vars "wa" < (σ.arrs "om").length ∧ σ.vars "wa" < B ∧ σ.vars "wv" < B) ∧
        (σ.vars "wo" = 1 → σ.vars "wov" < B) ∧ σ.vars "npc" < B ∧
        σ.vars "rd" + σ.vars "rdi" < B ∧ 1 < B) commitCom
      (fun σ σ' => σ' = commitEnv σ) 100 := by
  run_vcg
  all_goals try simp_all [commitEnv, Env.setVar, Env.setArr]
  all_goals try omega

theorem commitEnv_vars (σ : Env) (y : String) : (commitEnv σ).vars y =
    if y = "rd" then σ.vars "rd" + σ.vars "rdi"
    else if y = "spc" then σ.vars "npc"
    else if y = "nout" ∧ σ.vars "wo" = 1 then 1
    else if y = "outv" ∧ σ.vars "wo" = 1 then σ.vars "wov"
    else σ.vars y := by
  unfold commitEnv
  by_cases h1 : σ.vars "wf" = 1 <;> by_cases h2 : σ.vars "wo" = 1 <;>
    by_cases hy1 : y = "rd" <;> by_cases hy2 : y = "spc" <;> by_cases hy3 : y = "nout" <;>
    by_cases hy4 : y = "outv" <;> simp [Env.setVar, Env.setArr, h1, h2, hy1, hy2, hy3, hy4]

theorem commitEnv_arrs (σ : Env) (a : String) : (commitEnv σ).arrs a =
    if a = "om" ∧ σ.vars "wf" = 1 then (σ.arrs "om").set (σ.vars "wa") (σ.vars "wv")
    else σ.arrs a := by
  unfold commitEnv
  by_cases h1 : σ.vars "wf" = 1 <;> by_cases h2 : σ.vars "wo" = 1 <;>
    by_cases ha : a = "om" <;> simp [Env.setVar, Env.setArr, h1, h2, ha]

/-- The state after a halt or a stop at the end of the program: the counter at the end. -/
def halted (P : Program) (s : State) : State := { s with pc := P.length }

theorem List.prefix_single_iff {α : Type*} (l : List α) (a b : α) :
    (l ++ [a]) <+: [b] → l = [] ∧ a = b := by
  intro h
  obtain ⟨t, ht⟩ := h
  cases l with
  | nil => simp at ht; exact ⟨rfl, ht.1⟩
  | cons x l => simp at ht

theorem commit_krel {σ : Env} (hK : KRel P z wp σ) : KRel P z wp (commitEnv σ) := by
  obtain ⟨hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2, hzarr, hprog⟩ := hK
  obtain ⟨hl0, hl1, hl2, hl3, henc⟩ := hprog
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [commitEnv_vars]; simp [hplen, hzl, hwpv, hMp, hmask, hhh, hhm, hhm2]; done)
    | (rw [commitEnv_arrs]; simp [hzarr]; done)
    | skip
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [commitEnv_arrs]; simpa using hl0
  · rw [commitEnv_arrs]; simpa using hl1
  · rw [commitEnv_arrs]; simpa using hl2
  · rw [commitEnv_arrs]; simpa using hl3
  · intro j i hj
    have := henc j i hj
    rw [commitEnv_arrs, commitEnv_arrs, commitEnv_arrs, commitEnv_arrs]
    simpa using this

theorem commit_drel_some {σ : Env} {s s' : State} (hD : DRel z wp v σ s)
    (hzl : σ.vars "zl" = z.length)
    (hR : Res B wp P.length s (some s') σ) (hp : s'.out <+: [v]) :
    DRel z wp v (commitEnv σ) s' := by
  simp only [Res] at hR
  obtain ⟨hs', hwa, hrd, hwf1, hwo1, hwov, hnpc⟩ := hR
  obtain ⟨hspc, hrd', hinp, hinput, homlen, hmem, hword, hout⟩ := hD
  subst hs'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [commitEnv_vars]; simp [EffData]
  · rw [commitEnv_vars]; simp only [if_true]; omega
  · rw [commitEnv_vars]; simp [EffData, hinp, List.drop_drop]
  · simp [EffData, hinput]
  · rw [commitEnv_arrs]; split_ifs <;> simp [homlen]
  · intro a ha
    rw [commitEnv_arrs]
    by_cases h1 : σ.vars "wf" = 1
    · obtain ⟨hwa1, hwv1⟩ := hwa h1
      have hlen : σ.vars "wa" < (σ.arrs "om").length := by rw [homlen]; exact hwa1
      simp only [h1, and_self, if_true, EffData, setCell, Nat.mod_eq_of_lt hwa1,
        Nat.mod_eq_of_lt hwv1]
      by_cases hae : a = σ.vars "wa"
      · subst hae
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hae), hae]
        exact hmem a ha
    · simp only [h1, and_false, if_false, EffData]
      exact hmem a ha
  · intro a
    by_cases h1 : σ.vars "wf" = 1
    · obtain ⟨hwa1, hwv1⟩ := hwa h1
      simp only [h1, if_true, EffData, setCell]
      split_ifs
      · exact Nat.mod_lt _ (Nat.two_pow_pos wp)
      · exact hword a
    · simp only [h1, if_false, EffData]
      exact hword a
  · by_cases h2 : σ.vars "wo" = 1
    · simp only [h2, if_true, EffData] at hp ⊢
      obtain ⟨hs0, hv0⟩ := List.prefix_single_iff _ _ _ hp
      right
      refine ⟨by simp [hs0, hv0], ?_, ?_⟩
      · rw [commitEnv_vars]; simp [h2]
      · rw [commitEnv_vars]; simp [h2, hv0]
    · simp only [h2, if_false, EffData]
      rcases hout with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
      · left
        refine ⟨h3, ?_⟩
        rw [commitEnv_vars]; simpa [h2] using h4
      · right
        refine ⟨h3, ?_, ?_⟩
        · rw [commitEnv_vars]; simpa [h2] using h4
        · rw [commitEnv_vars]; simpa [h2] using h5

theorem commit_drel_none {σ : Env} {s : State} (hD : DRel z wp v σ s)
    (hzl : σ.vars "zl" = z.length)
    (hR : Res B wp P.length s none σ) : DRel z wp v (commitEnv σ) (halted P s) := by
  simp only [Res] at hR
  obtain ⟨hnpc, hwf, hwo, hrdi⟩ := hR
  obtain ⟨hspc, hrd', hinp, hinput, homlen, hmem, hword, hout⟩ := hD
  have hwf' : ¬ σ.vars "wf" = 1 := by omega
  have hwo' : ¬ σ.vars "wo" = 1 := by omega
  refine ⟨?_, ?_, ?_, hinput, ?_, ?_, hword, ?_⟩
  · rw [commitEnv_vars]; simp [halted, hnpc]
  · rw [commitEnv_vars]; simp [hrdi]; exact hrd'
  · rw [commitEnv_vars]; simp [halted, hrdi, hinp]
  · rw [commitEnv_arrs]; simp [hwf', homlen]
  · intro a ha
    rw [commitEnv_arrs]; simp [hwf', halted]
    exact hmem a ha
  · rcases hout with ⟨h3, h4⟩ | ⟨h3, h4, h5⟩
    · left
      refine ⟨h3, ?_⟩
      rw [commitEnv_vars]; simpa [hwo'] using h4
    · right
      refine ⟨h3, ?_, ?_⟩
      · rw [commitEnv_vars]; simpa [hwo'] using h4
      · rw [commitEnv_vars]; simpa [hwo'] using h5

end Lax117284Proofs.Machine.ClSim
