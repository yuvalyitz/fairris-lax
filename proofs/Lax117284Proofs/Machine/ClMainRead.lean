import Lax117284Proofs.Machine.ClBuildAll

/-!
Reading the word: the two counts into scalars, the whole word into the array `X`, the fairness
parameter from its last entry.
-/

namespace Lax117284Proofs.Machine.ClMain

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.ClSim (V lit asg seqs AgreeOff)
open Lax117284Proofs.Machine.ClBuild
open Lax117284Proofs.ClientsILP Lax117284.Scheduling Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- One further entry of the word into `X`. -/
def readStep : Com := seqs [.read "rv", .store "X" (V "rt") (V "rv"), asg "rt" (add (V "rt") (lit 1))]

/-- The header: the counts, the length, the first two cells, the counter. -/
def hdrCom : Com := seqs [
  .read "n", .read "m",
  asg "L" (add (mul (lit 2) (mul (V "m") (V "n"))) (lit 3)),
  .store "X" (lit 0) (V "n"), .store "X" (lit 1) (V "m"), asg "rt" (lit 2)]

/-- The word: the header, the rest, the parameter. -/
def readCom : Com := .seq hdrCom (.seq (.while (.lt (V "rt") (V "L")) readStep)
  (asg "k" (.get "X" (sub (V "L") (lit 1)))))

variable {B k : ℕ} {I : Instance} {x : List ℕ}

/-- The state before the reading. -/
def RIn (x : List ℕ) (σ : Env) : Prop :=
  σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "X").length = x.length

/-- The reading loop's invariant. -/
def RLoop (I : Instance) (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "n" = I.clients ∧ σ.vars "m" = I.days ∧ σ.vars "L" = x.length ∧
    (σ.arrs "X").length = x.length ∧ σ.vars "rt" ≤ x.length ∧
    (∀ i < σ.vars "rt", (σ.arrs "X").getD i 0 = x.getD i 0) ∧
    σ.inp = x.drop (σ.vars "rt") ∧ σ.out = []

theorem x_eq_cons (h : Lax117284.InstanceEncoding.EncodesUniform x I k) :
    x = I.clients :: I.days :: x.drop 2 := by
  have h0 := ClientsWord.x0 h
  have h1 := ClientsWord.x1 h
  have hl := ClientsWord.len_eq h
  obtain ⟨a, b, r, rfl⟩ : ∃ a b r, x = a :: b :: r := by
    rcases x with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp only [List.length_nil] at hl; omega
    · simp only [List.length_singleton] at hl; omega
    · exact ⟨a, b, r, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  simp [h0, h1]

theorem readStep_spec (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ ∧ σ.vars "rt" < x.length) readStep
      (fun σ σ' => RLoop I x σ' ∧ σ'.vars "rt" = σ.vars "rt" + 1) 20 := by
  refine Spec.pre (P := fun σ => RLoop I x σ ∧ σ.vars "rt" < x.length ∧ σ.inp ≠ [] ∧
      σ.inp.headD 0 < B ∧ σ.vars "rt" < (σ.arrs "X").length) ?_ ?_
  · run_vcg
    · obtain ⟨hn, hm, hLv, hlen, hle, hcell, hinp, hout⟩ := ‹RLoop I x σ›
      have htlt := ‹σ.vars "rt" < x.length›
      have hidx : σ.vars "rt" < (σ.arrs "X").length := by rw [hlen]; exact htlt
      simp only [RLoop]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp
      · exact hn
      · exact hm
      · exact hLv
      · exact hlen
      · exact htlt
      · intro i hi
        rcases Nat.lt_or_ge i (σ.vars "rt") with h | h
        · rw [List.getElem?_set_ne (by omega)]
          simpa [List.getD_eq_getElem?_getD] using hcell i h
        · have hie : i = σ.vars "rt" := by omega
          subst hie
          rw [hinp]
          simp [hidx, List.head?_drop]
      · rw [hinp, List.tail_drop]
      · exact hout
    · simp only [Env.setVar]
      exact ‹σ.inp.headD 0 < B›
  · rintro σ ⟨hI, ht⟩
    have hinp : σ.inp = x.drop (σ.vars "rt") := hI.2.2.2.2.2.2.1
    have hne : σ.inp ≠ [] := by
      rw [hinp]; intro hc
      have : (x.drop (σ.vars "rt")).length = 0 := by rw [hc]; rfl
      simp only [List.length_drop] at this; omega
    refine ⟨hI, ht, hne, ?_, by rw [hI.2.2.2.1]; exact ht⟩
    rcases hh : σ.inp with _ | ⟨u, rest⟩
    · exact absurd hh hne
    · have : u ∈ x.drop (σ.vars "rt") := by rw [← hinp, hh]; exact List.mem_cons_self
      exact hX u (List.mem_of_mem_drop this)

theorem readLoop_spec (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ) (.while (.lt (V "rt") (V "L")) readStep)
      (fun _ σ' => RLoop I x σ' ∧ σ'.vars "rt" = x.length) (24 * x.length + 4) :=
  Spec.forRange "rt" "L" (RLoop I x) x.length 20 (24 * x.length + 4)
    (fun _ h => lt_of_le_of_lt h.2.2.2.2.1 hL) (fun _ h => by rw [h.2.2.1]; exact hL)
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.2.1) (readStep_spec hL hX) (fun _ h => h)
    (fun σ _ => by
      have : (20 + 4) * (x.length - σ.vars "rt") ≤ (20 + 4) * x.length :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      omega)

theorem hdrCom_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) hdrCom
      (fun σ σ' => RLoop I x σ' ∧ σ'.vars "rt" = 2 ∧ (∀ a, a ≠ "X" → σ'.arrs a = σ.arrs a) ∧
        ∀ y, y ∉ ["n", "m", "L", "rt", "rv"] → σ'.vars y = σ.vars y) 40 := by
  have hl := ClientsWord.len_eq hdec
  have h0 := ClientsWord.x0 hdec
  have h1 := ClientsWord.x1 hdec
  have hcons := x_eq_cons hdec
  have hnhd : x.head?.getD 0 = I.clients := by rw [hcons]; simp
  have hm1 : x[1]?.getD 0 = I.days := by rw [hcons]; simp
  have hhd : x.headD 0 = I.clients := by rw [hcons]; simp
  have hhd2 : x.tail.headD 0 = I.days := by rw [hcons]; simp
  have htt : x.tail.tail = x.drop 2 := by rw [hcons]; simp
  have hnB : I.clients < B := hX I.clients (by rw [hcons]; simp)
  have hmB : I.days < B := hX I.days (by rw [hcons]; simp)
  have hxne : x ≠ [] := by intro h; rw [h] at hl; simp only [List.length_nil] at hl; omega
  have hxt : x.tail ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hx0' : x[0]?.getD 0 = I.clients := by rw [hcons]; simp
  clear hcons
  run_vcg
  all_goals obtain ⟨hin, hout, hXl⟩ := ‹RIn x σ›
  all_goals simp [Env.setVar, hin, hhd, hhd2, htt, hxne, hxt, hnB, hmB, hnhd, hm1, hXl]
  all_goals try omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals try simp [RLoop, Env.setArr, hin, hout, hXl, hl]
  · omega
  · omega
  · have hX2 : 1 < (σ.arrs "X").length := by omega
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · have hX0 : 0 < (σ.arrs "X").length := by omega
      simp [hX0, hx0', List.getElem?_set]
    · simp [hX2, hm1, List.getElem?_set]
  · intro a ha; simp [ha]
  · intro y h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]

/-- The last entry: the parameter. -/
theorem kCom_spec (hx : 0 < x.length) (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (fun σ => RLoop I x σ ∧ σ.vars "rt" = x.length) (asg "k" (.get "X" (sub (V "L") (lit 1))))
      (fun σ σ' => σ'.vars "k" = x.getD (x.length - 1) 0 ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
        σ'.out = σ.out ∧ ∀ y, y ≠ "k" → σ'.vars y = σ.vars y) 10 := by
  have hgB : ∀ j, x.getD j 0 < B := by
    intro j
    by_cases hj : j < x.length
    · rw [List.getD_eq_getElem _ _ hj]; exact hX _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; omega
  run_vcg
  all_goals rename_i hRL hrt
  all_goals obtain ⟨hn1, hm1, hL1, hlen1, -, hcell1, hinp1, hout1⟩ := hRL
  all_goals (have hcx : (σ.arrs "X").getD (σ.vars "L" - 1) 0 = x.getD (x.length - 1) 0 := by
               rw [hL1]; exact hcell1 _ (by omega))
  · have hcx' : (σ.arrs "X")[σ.vars "L" - 1]?.getD 0 = x[x.length - 1]?.getD 0 := by
      simpa [List.getD_eq_getElem?_getD] using hcx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hcx']
    intro y h1 h2; exact absurd h2 h1
  all_goals try omega
  simp only [hcx]; exact hgB _

theorem readCore_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) readCom
      (fun σ σ' => Ctx0 I x k σ' ∧ σ'.vars "L" = x.length ∧ σ'.inp = [] ∧ σ'.out = [])
      (24 * x.length + 60) := by
  have hl := ClientsWord.len_eq hdec
  have hk := ClientsWord.xk hdec
  unfold readCom
  refine Spec.mono (Spec.post (Spec.seq' (hdrCom_spec hdec hL hX)
    (Spec.seq' (readLoop_spec (I := I) hL hX) (kCom_spec (by omega) hL hX)
      (fun σ σ' _ h => h))
    (fun σ σ' _ h => h.1)) ?_) (by omega)
  rintro σ σ2 hin ⟨σ1, ⟨hA1, hA2, hA3, hA4⟩, σ3, ⟨⟨hn1, hm1, hL1, hlen1, -, hcell1, hinp1, hout1⟩, hrt1⟩,
    hC1, hC2, hC3, hC4, hC5⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hC2]
    refine List.ext_getElem hlen1 fun i h1 h2 => ?_
    have := hcell1 i (by rw [hrt1]; exact h2)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at this
  · rw [hC5 _ (by decide), hn1]
  · rw [hC5 _ (by decide), hm1]
  · rw [hC1, ← hk]; congr 1; omega
  · rw [hC5 _ (by decide), hL1]
  · rw [hC3, hinp1, hrt1]; simp
  · rw [hC4, hout1]

theorem readCom_spec (hdec : Lax117284.InstanceEncoding.EncodesUniform x I k)
    (hL : x.length < B) (hX : ∀ v ∈ x, v < B) :
    Spec B (RIn x) readCom
      (fun σ σ' => Ctx0 I x k σ' ∧ σ'.vars "L" = x.length ∧ σ'.inp = [] ∧ σ'.out = [] ∧
        (∀ a, a ≠ "X" → σ'.arrs a = σ.arrs a) ∧
        ∀ y, y ∉ ["n", "m", "L", "rt", "k", "rv"] → σ'.vars y = σ.vars y)
      (24 * x.length + 60) := by
  refine (readCore_spec hdec hL hX).frame.post ?_
  rintro σ σ' - ⟨⟨h1, h2, h3, h4⟩, hv, ha, -, -⟩
  refine ⟨h1, h2, h3, h4, fun a hn => ha a ?_, fun y hy => hv y ?_⟩
  · simp [readCom, hdrCom, readStep, Com.warrs, seqs, asg, hn]
  · simp only [readCom, hdrCom, readStep, Com.wvars, seqs, asg, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    tauto

end Lax117284Proofs.Machine.ClMain
