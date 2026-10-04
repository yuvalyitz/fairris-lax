import Lax117284Proofs.Machine.TokLoop
import Lax117284Proofs.Machine.InstSem
import Lax117284Proofs.Machine.BlockSem
import Lax117284.Lemma15
import Lax117284Proofs.Machine.FreeCheck
import Lax117284Proofs.Machine.Emit
import Lax117284Proofs.Machine.BlockProg
import Lax117284Proofs.Machine.FreeAccept
import Lax117284Proofs.Machine.BlockAccept
import Lax117284Proofs.Machine.BlockFinal

/-! ### `Lax117284Proofs.Machine.PNk` -/

section
/-!
What the format of an instance with a fairness parameter expects next, as a command.
-/

namespace Lax117284Proofs.Machine.PNk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.TokModel Lax117284Proofs.Machine.TokScan Lax117284Proofs.Machine.TokProg
open Lax117284Proofs.Machine.InstSem

/-- The per-client format: the counts, the table, and one parameter per client. -/
abbrev eP : ℕ → ℕ → ℕ := fun n _ => n

abbrev sub (e f : Expr) : Expr := .bin .sub e f
abbrev mul (e f : Expr) : Expr := .bin .mul e f
abbrev add (e f : Expr) : Expr := .bin .add e f

/-- What the format expects, the counts and the parameter being `n`, `m`: a number as long as the
table has not been read, and the end after it. -/
def nkP : Com :=
  .ite (.lt (V "T") (.lit 2)) (set "kind" 0)
    (.seq (.assign "j" (sub (V "T") (.lit 2)))
      (.seq (.assign "n3" (add (mul (.lit 2) (mul (.get "TK" (.lit 1)) (.get "TK" (.lit 0))))
          (.get "TK" (.lit 0))))
        (.ite (.lt (V "j") (V "n3")) (set "kind" 0) (set "kind" 2))))

/-- The code of what is expected after `Tn` tokens, the counts being `n` and `m`. -/
def kindCodeP (Tn n m : ℕ) : ℕ := if Tn < 2 then 0 else kcode (kindI eP n m (Tn - 2))

variable {B : ℕ}

theorem nkP_flat (Tn n m : ℕ) (hB : 2 * (m * n) + Tn + n + 8 < B) (hm : m + 8 < B) (hn : n + 8 < B) :
    Spec B (fun σ => σ.vars "T" = Tn ∧ (σ.arrs "TK").getD 0 0 = n ∧
        (σ.arrs "TK").getD 1 0 = m ∧ (2 ≤ Tn → 2 ≤ (σ.arrs "TK").length)) nkP
      (fun σ σ' => σ'.vars "kind" = kindCodeP Tn n m ∧
        (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.out = σ.out ∧ σ'.inp = σ.inp) 60 := by
  run_vcg
  all_goals have hT := ‹σ.vars "T" = Tn›
  all_goals have h0 := ‹(σ.arrs "TK").getD 0 0 = n›
  all_goals have h1 := ‹(σ.arrs "TK").getD 1 0 = m›
  all_goals have hl := ‹2 ≤ Tn → 2 ≤ (σ.arrs "TK").length›
  all_goals try simp [Env.setVar] at *
  all_goals try simp only [h0, h1, hT] at *
  all_goals try omega
  all_goals (
    refine ⟨?_, fun y a b c => by simp [a, b, c]⟩
    have k0 : kcode .num = 0 := rfl
    have k2 : kcode .done = 2 := rfl
    have hE1 : eP n m = n := rfl
    unfold kindCodeP kindI
    split_ifs <;> omega)

theorem setKind0_spec (hB : 2 < B) :
    Spec B (fun _ => True) (set "kind" 0)
      (fun σ σ' => σ'.vars "kind" = 0 ∧ (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp) 2 := by
  run_vcg
  · refine ⟨by simp [Env.setVar], fun y hy => ?_, by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]⟩
    have : y ≠ "kind" := fun h => hy (by simp [h])
    simp [Env.setVar, this]
  all_goals omega

/-- **The command meets the contract of the tokenizer.** -/
theorem nkP_spec (Bt cap : ℕ) (hB : 2 * (Bt * Bt) + 2 * Bt + cap + 16 < B) :
    NkSpec B Bt (EI eP) cap nkP 60 := by
  intro toks hfol hcap
  have frame : ∀ {σ σ' : Env}, (∀ y ∉ ["kind", "j", "n3"], σ'.vars y = σ.vars y) →
      ∀ y ∈ scanVars, σ'.vars y = σ.vars y := fun h y hy => h y (by
    simp only [scanVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  by_cases h2 : toks.length < 2
  · -- fewer than two tokens: a count is expected
    have hE : EI eP toks = .num := by
      rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · cases a <;> rfl
      · simp at h2
    rintro σ ⟨⟨hT, -⟩, -⟩
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ :=
      (ite_true_spec (B := B) (P := fun σ => σ.vars "T" = toks.length)
        (b := .lt (V "T") (.lit 2)) (d := _)
        (fun σ h => by
          rw [evalB_condLt (evalB_var (by rw [h]; omega)) (evalB_lit (by omega)), h]
          simp [h2])
        ((setKind0_spec (B := B) (by omega)).pre (fun _ _ => trivial))) σ hT
    exact ⟨σ', r.mono (by simp [Cond.size, Expr.size]), by rw [q1, hE]; rfl, frame q2, q3, q4, q5⟩
  · -- the counts are known
    rcases toks with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h2
    · simp at h2
    have ha : a.kind = .num := by simpa [EI] using hfol 0 (by simp)
    have hb : b.kind = .num := by
      have := hfol 1 (by simp)
      simpa [EI] using this
    obtain ⟨n, rfl⟩ : ∃ n, a = .num n := by cases a <;> simp_all [Tok.kind]
    obtain ⟨m, rfl⟩ : ∃ m, b = .num m := by cases b <;> simp_all [Tok.kind]
    intro σ ⟨⟨hT, hTK⟩, hsm⟩
    have hn : n < Bt := hsm (.num n) (by simp)
    have hm : m < Bt := hsm (.num m) (by simp)
    have hlen : 2 ≤ (σ.arrs "TK").length := by
      have := congrArg List.length hTK
      simp at this; omega
    have g0 : (σ.arrs "TK").getD 0 0 = n := by
      have := congrArg (fun l => l.getD 0 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    have g1 : (σ.arrs "TK").getD 1 0 = m := by
      have := congrArg (fun l => l.getD 1 0) hTK
      simpa [List.getD_eq_getElem?_getD, List.getElem?_take, Tok.val] using this
    simp only [List.length_cons] at hcap hT
    have hmn : m * n ≤ Bt * Bt := Nat.mul_le_mul hm.le hn.le
    obtain ⟨σ', r, q1, q2, q3, q4, q5⟩ := nkP_flat (B := B) (rest.length + 2) n m (by omega)
      (by omega) (by omega) σ ⟨by rw [hT], g0, g1, fun _ => hlen⟩
    refine ⟨σ', r, ?_, frame q2, q3, q4, q5⟩
    rw [q1, EI_cons]
    simp [kindCodeP]

end Lax117284Proofs.Machine.PNk

end

/-! ### `Lax117284Proofs.Machine.PerSem` -/

section
/-!
The reduction of Lemma 15 on the numbers of a stream: an instance with one parameter per client is
the counts, the table of jobs and the parameters; the image is the numbers of the constructed
instance with the parameter `m`, computed cell by cell from the closed form of the cell.
-/

namespace Lax117284Proofs.Machine.PerSem

open Lax117284.Scheduling Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.BlockSem Lax117284Proofs.Machine.PNk

/-- The numbers of an instance with one parameter per client. -/
def perToks (I : Instance) (k : Fin I.clients → ℕ) : List ℕ :=
  instToks I ++ (List.finRange I.clients).map fun j => k j

theorem encodePerClient_eq (I : Instance) (k : Fin I.clients → ℕ) :
    encodePerClient I k = numCode (perToks I k) := by
  unfold encodePerClient perToks
  rw [numCode_append, encodeInstance_eq]
  congr 1
  simp [numCode, List.flatMap_map]

/-- The parameter of client `j` in a stream. -/
def paramAt (ns : List ℕ) (j : ℕ) : ℕ := ns.getD (2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + j) 0

lemma instToks_take (ns : List ℕ) (hv : Valid ns) (h2 : 2 ≤ ns.length)
    (hl : 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) ≤ ns.length) :
    instToks (instOf ns hv) = ns.take (2 + 2 * (ns.getD 1 0 * ns.getD 0 0)) := by
  have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
  have hdy : (instOf ns hv).days = ns.getD 1 0 := rfl
  unfold instToks
  rw [hcl, hdy]
  have hmap : (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap (fun t =>
      [(instOf ns hv).pAt (t / ns.getD 0 0) (t % ns.getD 0 0),
       (instOf ns hv).dAt (t / ns.getD 0 0) (t % ns.getD 0 0)])
      = (List.range (ns.getD 1 0 * ns.getD 0 0)).flatMap (fun t =>
      [ns.getD (2 + 2 * t) 0, ns.getD (2 + 2 * t + 1) 0]) :=
    List.flatMap_congr fun t ht => by
      have := instOf_pAt ns hv (List.mem_range.mp ht)
      rw [this.1, this.2]
  rw [hmap, flatMap_pairs ns 2 _ hl]
  obtain ⟨n, m, rest, rfl⟩ : ∃ n m rest, ns = n :: m :: rest := by
    rcases ns with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp at h2
    exact ⟨a, b, rest, rfl⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
  rw [show 2 + 2 * (m * n) = (2 * (m * n)) + 1 + 1 by ring]
  simp

lemma param_toks (ns : List ℕ) (h2 : 2 ≤ ns.length)
    (hl : ns.length = 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + ns.getD 0 0) :
    ns.drop (2 + 2 * (ns.getD 1 0 * ns.getD 0 0)) = (List.range (ns.getD 0 0)).map (paramAt ns) := by
  apply List.ext_getElem
  · rw [List.length_drop, List.length_map, List.length_range]; omega
  · intro i h1 h2'
    simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
    simp only [List.length_drop] at h1
    unfold paramAt
    exact (List.getD_eq_getElem ns 0 (by omega)).symm

/-- **The streams of the per-client format that are instances with parameters not above the
number of days.** -/
theorem per_iff (w : Word) :
    (∃ (I : Instance) (k : Fin I.clients → ℕ), encodePerClient I k = w ∧ ∀ j, k j ≤ I.days) ↔
      ∃ ns : List ℕ, w = numCode ns ∧ Shape eP ns ∧ Valid ns ∧
        ∀ j < ns.getD 0 0, paramAt ns j ≤ ns.getD 1 0 := by
  constructor
  · rintro ⟨I, k, hw, hk⟩
    have hl := instToks_length I
    have h0 : (perToks I k).getD 0 0 = I.clients := by
      unfold perToks
      rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).1
    have h1 : (perToks I k).getD 1 0 = I.days := by
      unfold perToks
      rw [List.getD_append _ _ _ _ (by omega)]; exact (instToks_getD_head I).2
    have hlen : (perToks I k).length = 2 + 2 * (I.days * I.clients) + I.clients := by
      unfold perToks; simp [hl]
    refine ⟨perToks I k, by rw [← hw, encodePerClient_eq], ⟨by omega, ?_⟩, ?_, ?_⟩
    · rw [h0, h1, hlen]
    · intro t ht
      rw [h0, h1] at ht
      have ht' : t < I.days * I.clients := ht
      have hp := instToks_getD_cell I ht'
      unfold perToks
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hp.1, hp.2]
      exact ⟨I.pAt_pos _ _, I.pAt_le_dAt _ _⟩
    · intro j hj
      rw [h0] at hj
      unfold paramAt
      rw [h0, h1]
      unfold perToks
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have : 2 + 2 * (I.days * I.clients) + j - (instToks I).length = j := by omega
      rw [this, List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_finRange]
      exact hk ⟨j, hj⟩
  · rintro ⟨ns, hw, ⟨h2, hl⟩, hv, hk⟩
    simp only [eP] at hl
    refine ⟨instOf ns hv, fun j => paramAt ns j, ?_, fun j => hk j j.isLt⟩
    rw [hw, encodePerClient_eq]
    congr 1
    unfold perToks
    have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
    rw [instToks_take ns hv h2 (by omega), hcl]
    have : (List.finRange (ns.getD 0 0)).map (fun j : Fin (ns.getD 0 0) => paramAt ns j)
        = (List.range (ns.getD 0 0)).map (paramAt ns) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2'
        simp
    simp only [this]
    rw [← param_toks ns h2 hl, List.take_append_drop]


lemma perToks_instOf (ns : List ℕ) (hv : Valid ns) (h2 : 2 ≤ ns.length)
    (hl : ns.length = 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + ns.getD 0 0) :
    perToks (instOf ns hv) (fun j => paramAt ns j) = ns := by
  unfold perToks
  have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
  rw [instToks_take ns hv h2 (by omega), hcl]
  have : (List.finRange (ns.getD 0 0)).map (fun j : Fin (ns.getD 0 0) => paramAt ns j)
      = (List.range (ns.getD 0 0)).map (paramAt ns) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2'
      simp
  simp only [this]
  rw [← param_toks ns h2 hl, List.take_append_drop]

/-! ### The image -/

/-- The two numbers of cell `t` of the image, whose rows have `n + 2` cells, read off an array;
`dm` is the largest due date of the table. -/
def cellLG (arr : List ℕ) (n m dm t : ℕ) : List ℕ :=
  if t % (n + 2) < n then
    (if t / (n + 2) < m then
      [arr.getD (2 + 2 * (t / (n + 2) * n + t % (n + 2))) 0,
       arr.getD (2 + 2 * (t / (n + 2) * n + t % (n + 2)) + 1) 0]
    else [1, if t / (n + 2) - m < arr.getD (2 + 2 * (m * n) + t % (n + 2)) 0
        then dm + (t % (n + 2) + 1) else dm + (n + 1) + (t % (n + 2) + 1)])
  else [n + 1, dm + (n + 1)]

/-- The numbers of the image: the counts, the table, and the parameter `m`. -/
def outLG (arr : List ℕ) (n m dm : ℕ) : List ℕ :=
  [n + 2, 2 * m] ++ (List.range (2 * m * (n + 2))).flatMap (cellLG arr n m dm) ++ [m]

/-- The numbers of the image of a stream. -/
def outL (ns : List ℕ) : List ℕ := outLG ns (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns)

/-- The numbers of the image for every accepted stream: with no clients, a fixed instance. -/
def outLAll (ns : List ℕ) : List ℕ := if ns.getD 0 0 = 0 then [0, 0, 0] else outL ns

section Cells

variable (I : Instance) (k : Fin I.clients → ℕ)

lemma pAt_inst {a b : ℕ} (ha : a < 2 * I.days) (hb : b < I.clients + 2) :
    (Lax117284.Lemma15.inst I k).pAt a b =
      if b < I.clients then (if a < I.days then I.pAt a b else 1)
      else Lax117284.Lemma15.span I := by
  simp only [Instance.pAt, Lax117284.Lemma15.inst]
  rw [dif_pos ha, dif_pos hb]

lemma dAt_inst {a b : ℕ} (ha : a < 2 * I.days) (hb : b < I.clients + 2) :
    (Lax117284.Lemma15.inst I k).dAt a b =
      if hj : b < I.clients then
        (if a < I.days then I.dAt a b
          else if a - I.days < k ⟨b, hj⟩ then Lax117284.Lemma15.dmax I + (b + 1)
            else Lax117284.Lemma15.dmax I + Lax117284.Lemma15.span I + (b + 1))
      else Lax117284.Lemma15.dmax I + Lax117284.Lemma15.span I := by
  simp only [Instance.dAt, Lax117284.Lemma15.inst]
  rw [dif_pos ha, dif_pos hb]

end Cells

lemma dmax_instOf (ns : List ℕ) (hv : Valid ns) :
    Lax117284.Lemma15.dmax (instOf ns hv) = dmaxOf ns := by
  have := bound_instOf ns hv
  unfold Lax117284.Corollary8.bound bdOf at this
  unfold Lax117284.Lemma15.dmax
  omega

/-- **The numbers of the constructed instance.** -/
theorem instToks_inst (ns : List ℕ) (hv : Valid ns) :
    instToks (Lax117284.Lemma15.inst (instOf ns hv) (fun j => paramAt ns j)) =
      [ns.getD 0 0 + 2, 2 * ns.getD 1 0] ++
        (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap
          (cellLG ns (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns)) := by
  set I := instOf ns hv with hI
  have hn : ns.getD 0 0 = I.clients := rfl
  have hm : ns.getD 1 0 = I.days := rfl
  have hd := dmax_instOf ns hv
  unfold instToks
  show [ns.getD 0 0 + 2, 2 * ns.getD 1 0] ++
    (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap (fun t =>
      [(Lax117284.Lemma15.inst I (fun j => paramAt ns j)).pAt (t / (ns.getD 0 0 + 2))
        (t % (ns.getD 0 0 + 2)), (Lax117284.Lemma15.inst I (fun j => paramAt ns j)).dAt
        (t / (ns.getD 0 0 + 2)) (t % (ns.getD 0 0 + 2))]) = _
  congr 1
  refine List.flatMap_congr fun t ht => ?_
  have ht' : t < 2 * ns.getD 1 0 * (ns.getD 0 0 + 2) := List.mem_range.mp ht
  have hn1 : 0 < ns.getD 0 0 + 2 := by omega
  have h1 : t / (ns.getD 0 0 + 2) < 2 * ns.getD 1 0 := by
    rw [Nat.div_lt_iff_lt_mul hn1]; exact ht'
  have h2 : t % (ns.getD 0 0 + 2) < ns.getD 0 0 + 2 := Nat.mod_lt _ hn1
  rw [pAt_inst I _ (by rw [← hm]; exact h1) (by rw [← hn]; exact h2),
    dAt_inst I _ (by rw [← hm]; exact h1) (by rw [← hn]; exact h2), hd]
  unfold cellLG
  by_cases hbn : t % (ns.getD 0 0 + 2) < ns.getD 0 0
  · have hbn' : t % (ns.getD 0 0 + 2) < I.clients := by rw [← hn]; exact hbn
    by_cases han : t / (ns.getD 0 0 + 2) < ns.getD 1 0
    · have han' : t / (ns.getD 0 0 + 2) < I.days := by rw [← hm]; exact han
      rw [if_pos hbn, if_pos han, if_pos hbn', if_pos han', dif_pos hbn', if_pos han',
        inst_p ns hv _ _ han hbn, inst_d ns hv _ _ han hbn]
    · have han' : ¬ t / (ns.getD 0 0 + 2) < I.days := by rw [← hm]; exact han
      rw [if_pos hbn, if_neg han, if_pos hbn', if_neg han', dif_pos hbn', if_neg han']
      rfl
  · have hbn' : ¬ t % (ns.getD 0 0 + 2) < I.clients := by rw [← hn]; exact hbn
    rw [if_neg hbn, if_neg hbn', dif_neg hbn']
    rfl


/-- **The reduction writes the numbers of the constructed instance.** -/
theorem per_eq (ns : List ℕ) (hv : Valid ns) (hs : Shape eP ns)
    (hk : ∀ j < ns.getD 0 0, paramAt ns j ≤ ns.getD 1 0) :
    Lax117284.Lemma15.reduce (numCode ns) = numCode (outLAll ns) := by
  classical
  obtain ⟨h2, hl⟩ := hs
  simp only [eP] at hl
  have hI : encodePerClient (instOf ns hv) (fun j => paramAt ns j) = numCode ns := by
    rw [encodePerClient_eq, perToks_instOf ns hv h2 hl]
  have hg : ∃ (I : Instance) (k : Fin I.clients → ℕ),
      encodePerClient I k = numCode ns ∧ ∀ j, k j ≤ I.days :=
    ⟨instOf ns hv, fun j => paramAt ns j, hI, fun j => hk j j.isLt⟩
  unfold Lax117284.Lemma15.reduce
  rw [dif_pos hg]
  have key : ∀ (I' : Instance) (k' : Fin I'.clients → ℕ), encodePerClient I' k' = numCode ns →
      (if I'.clients = 0 then encodeUniform (Lax117284.Corollary8.noClients 0) 0
        else encodeUniform (Lax117284.Lemma15.inst I' k') I'.days) = numCode (outLAll ns) := by
    intro I' k' h'
    obtain ⟨rfl, hk'⟩ := Injectivity.encodePerClient_inj (h'.trans hI.symm)
    obtain rfl := eq_of_heq hk'
    have hcl : (instOf ns hv).clients = ns.getD 0 0 := rfl
    have hdy : (instOf ns hv).days = ns.getD 1 0 := rfl
    unfold outLAll
    by_cases hn0 : ns.getD 0 0 = 0
    · rw [if_pos (by rw [hcl]; exact hn0), if_pos hn0, encodeUniform, encodeInstance_eq]
      have : instToks (Lax117284.Corollary8.noClients 0) = [0, 0] := by
        simp [instToks, Lax117284.Corollary8.noClients]
      rw [this]
      simp [numCode]
    · rw [if_neg (by rw [hcl]; exact hn0), if_neg hn0, encodeUniform, encodeInstance_eq,
        instToks_inst ns hv, hdy]
      unfold outL outLG
      simp only [numCode_append, List.append_assoc, numCode_cons, numCode_nil, List.append_nil,
        List.cons_append, List.nil_append]
  exact key _ _ hg.choose_spec.choose_spec.1

/-- **A word that is not the code of an accepted stream is rejected.** -/
theorem per_rej (w : Word)
    (h : ¬ ∃ ns : List ℕ, w = numCode ns ∧ Shape eP ns ∧ Valid ns ∧
      ∀ j < ns.getD 0 0, paramAt ns j ≤ ns.getD 1 0) :
    Lax117284.Lemma15.reduce w = rejected := by
  classical
  unfold Lax117284.Lemma15.reduce
  rw [dif_neg (fun hg => h ((per_iff w).1 hg))]

end Lax117284Proofs.Machine.PerSem

end

/-! ### `Lax117284Proofs.Machine.PerCheck` -/

section
/-!
The pass over the parameters that checks that none of them exceeds the number of days.
-/

namespace Lax117284Proofs.Machine.PerCheck

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.PerSem

variable {B : ℕ}

/-- The test on parameter `i`. -/
def parChk : Com :=
  .seq (.assign "p" (.get "TK" (add (add (.lit 2) (V "N2")) (V "i"))))
    (.ite (.lt (V "m") (V "p")) (.assign "ok" (.lit 0)) .skip)

def parBody : Com := .seq parChk (.assign "i" (.bin .add (V "i") (.lit 1)))

def parLoop : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "n")) parBody)

/-- Parameter `j` does not exceed `m`. -/
def PassK (arr : List ℕ) (m N2 j : ℕ) : Prop := arr.getD (2 + N2 + j) 0 ≤ m

instance (arr : List ℕ) (m N2 : ℕ) : DecidablePred (PassK arr m N2) := fun j => by
  unfold PassK; infer_instance

lemma flagK_fail (arr : List ℕ) (m N2 ok0 i : ℕ) (h : ¬ PassK arr m N2 i) :
    flagTo (PassK arr m N2) ok0 (i + 1) = 0 := by
  rw [flagTo_succ]; simp [h]

lemma flagK_pass (arr : List ℕ) (m N2 ok0 i : ℕ) (h : PassK arr m N2 i) (hok : ok0 ≤ 1) :
    flagTo (PassK arr m N2) ok0 (i + 1) = flagTo (PassK arr m N2) ok0 i := by
  rw [flagTo_succ]
  have := flagTo_le (PassK arr m N2) ok0 i
  by_cases h1 : flagTo (PassK arr m N2) ok0 i = 1
  · simp [h1, h]
  · have : flagTo (PassK arr m N2) ok0 i = 0 := by omega
    simp [this]

structure ParInv (arr : List ℕ) (n m N2 ok0 : ℕ) (σ0 σ : Env) : Prop where
  arrs : σ.arrs = σ0.arrs
  out : σ.out = σ0.out
  hA : σ0.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vN2 : σ.vars "N2" = N2
  hi : σ.vars "i" ≤ n
  hok : σ.vars "ok" = flagTo (PassK arr m N2) ok0 (σ.vars "i")
  fr : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → σ.vars y = σ0.vars y

theorem parBody_spec (arr : List ℕ) (n m N2 ok0 : ℕ) (σ0 : Env)
    (hE : ∀ k < 2 + N2 + n, arr.getD k 0 + 8 < B) (hL : 2 + N2 + n + 8 < B)
    (hN : 2 + N2 + n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) (hok0 : ok0 ≤ 1) :
    Spec B (fun σ => ParInv arr n m N2 ok0 σ0 σ ∧ σ.vars "i" < n) parBody
      (fun σ σ' => ParInv arr n m N2 ok0 σ0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 40 := by
  run_vcg
  all_goals (
    have hI := ‹ParInv arr n m N2 ok0 σ0 σ›
    have hlt := ‹σ.vars "i" < n›
    have hsa := hI.arrs
    have hso := hI.out
    have hA0 := hI.hA
    have hnv := hI.vn
    have hmv := hI.vm
    have hN2 := hI.vN2
    have hi := hI.hi
    have hok := hI.hok
    have hfr := hI.fr
    clear hI
    have hA : σ.arrs "TK" = arr := by rw [hsa, hA0]
    have h1 := hE (2 + σ.vars "N2" + σ.vars "i") (by omega)
    have hN2r : N2 = σ.vars "N2" := hN2.symm
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y a b c => ?_⟩
    · exact hsa
    · exact hso
    · exact hA0
    · simp [hnv]
    · simp [hmv]
    · simp [hN2]
    · simp; omega
    · simp
      first
        | exact (flagK_fail (σ.arrs "TK") m N2 ok0 _ (by simp [PassK, hN2r]; omega)).symm
        | (rw [flagK_pass (σ.arrs "TK") m N2 ok0 _ (by simp [PassK, hN2r]; omega) hok0, hok])
    · simp [a, b, c]; exact hfr y a b c)

theorem parLoop_spec (arr : List ℕ) (n m N2 ok0 : ℕ) (σ : Env)
    (hE : ∀ k < 2 + N2 + n, arr.getD k 0 + 8 < B) (hL : 2 + N2 + n + 8 < B)
    (hN : 2 + N2 + n ≤ arr.length) (hnB : n + 8 < B) (hmB : m + 8 < B) (hok0 : ok0 ≤ 1)
    (hA : σ.arrs "TK" = arr) (hnv : σ.vars "n" = n) (hmv : σ.vars "m" = m)
    (hN2 : σ.vars "N2" = N2) (hok : σ.vars "ok" = ok0) :
    ∃ σ', Run B parLoop σ σ' ((40 + 4) * n + 6) ∧
      σ'.vars "ok" = flagTo (PassK arr m N2) ok0 n ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → σ'.vars y = σ.vars y := by
  obtain ⟨σ', r, hI, hi⟩ := (Spec.forRangeZero (B := B) (c := parBody) "i" "n"
    (ParInv arr n m N2 ok0 σ) n 40 (by omega) (fun _ h => h.hi) (fun _ h => h.vn)
    (parBody_spec arr n m N2 ok0 σ hE hL hN hnB hmB hok0)) σ
    ⟨by simp [Env.setVar], by simp [Env.setVar], hA, hnv, hmv, hN2, by simp [Env.setVar], by
      simp only [Env.setVar]
      simp [flagTo_zero (PassK arr m N2) ok0 hok0, hok], fun y a b c => by
      simp [Env.setVar, b]⟩
  refine ⟨σ', r, ?_, hI.arrs.trans (by simp [Env.setVar]), hI.out.trans (by simp [Env.setVar]), ?_⟩
  · rw [hI.hok, hi]
  · intro y a b c
    rw [hI.fr y a b c]

end Lax117284Proofs.Machine.PerCheck

end

/-! ### `Lax117284Proofs.Machine.PerProg` -/

section
/-!
The program that writes the image of Lemma 15 once the numbers of its input are in an array: the
counts with two more clients and twice the days, the table cell by cell from its closed form, and
the parameter `m`.
-/

namespace Lax117284Proofs.Machine.PerProg

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out
open Lax117284Proofs.Machine.Emit Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.BlockProg
open Lax117284Proofs.Machine.InstSem

variable {B : ℕ}

/-- Write a cell of the additional days that belongs to an original client. -/
def newCell : Com :=
  .seq (emitLit 1)
    (.seq (.assign "kj" (.get "TK" (add (add (.lit 2) (V "N2")) (V "cb"))))
      (.seq (.assign "cr" (sub (V "ca") (V "m")))
        (.ite (.lt (V "cr") (V "kj"))
          (emitVal (add (V "g") (add (V "cb") (.lit 1))))
          (emitVal (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1)))))))

/-- Scratch scalars of a cell. -/
def SCP : List String := SCB ++ ["kj", "cr"]

lemma scb_of_scp {y : String} (h : y ∉ SCP) : y ∉ SCB := fun h' =>
  h (List.mem_append_left _ h')

/-- **A cell of the additional days.** -/
theorem newCell_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env) (a b : ℕ)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hca : σ.vars "ca" = a) (hcb : σ.vars "cb" = b)
    (hm : σ.vars "m" = m) (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm)
    (hN2 : σ.vars "N2" = 2 * (m * n))
    (hbn : b < n) (ham : m ≤ a) (haB : a + 8 < B) (hmB : m + 8 < B)
    (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B newCell σ σ' (10 + (48 * Sz + 50) + (20 + 20 + (48 * Sz + 60))) ∧
      σ'.out = σ.out ++ (bitsNat 1 ++ bitsNat (if a - m < arr.getD (2 + 2 * (m * n) + b) 0
        then dm + (b + 1) else dm + (n + 1) + (b + 1))) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitLit_spec (B := B) 1 Sz (by omega) (hs _ (by omega)) σ trivial
  have s1 : Same σ σ1 := same_of_frame v1 a1
  have A1 : σ1.arrs "TK" = arr := by rw [a1]; exact hA
  have h1 : ∀ x : String, x ∉ SCR → σ1.vars x = σ.vars x := fun x hx => s1.1 x hx
  have hidx : 2 + 2 * (m * n) + b < 2 + 2 * (m * n) + n := by omega
  have hkjB := hE _ hidx
  -- the bound
  have hkv : σ1.vars "N2" = 2 * (m * n) := by rw [h1 "N2" (by decide)]; exact hN2
  have hcb1 : σ1.vars "cb" = b := by rw [h1 "cb" (by decide)]; exact hcb
  have ev1i : (add (add (.lit 2) (V "N2")) (V "cb")).evalB B σ1 = some (2 + 2 * (m * n) + b) := by
    have h := evalB_bin (B := B) (op := .add)
      (evalB_bin (B := B) (op := .add) (evalB_lit (B := B) (σ := σ1) (n := 2) (by omega))
        (evalB_var (B := B) (x := "N2") (σ := σ1) (by omega)) (by simp [hkv]; omega))
      (evalB_var (B := B) (x := "cb") (σ := σ1) (by omega)) (by simp [hkv, hcb1]; omega)
    simpa [hkv, hcb1] using h
  have ev1 : (Expr.get "TK" (add (add (.lit 2) (V "N2")) (V "cb"))).evalB B σ1
      = some (arr.getD (2 + 2 * (m * n) + b) 0) := by
    have := RunStep.eval_get B σ1 "TK" _ (2 + 2 * (m * n) + b) ev1i (by rw [A1]; omega)
      (by rw [A1]; omega)
    rwa [A1] at this
  have r2 := Run.assign (x := "kj") ev1
  set σ2 := σ1.setVar "kj" (arr.getD (2 + 2 * (m * n) + b) 0) with hσ2
  have hca2 : σ2.vars "ca" = a := by simp [hσ2, Env.setVar, h1 "ca" (by decide), hca]
  have hm2 : σ2.vars "m" = m := by simp [hσ2, Env.setVar, h1 "m" (by decide), hm]
  have ev3 : (sub (V "ca") (V "m")).evalB B σ2 = some (a - m) := by
    have h := evalB_bin (B := B) (op := .sub)
      (evalB_var (B := B) (x := "ca") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "m") (σ := σ2) (by omega)) (by simp [hca2, hm2]; omega)
    simpa [hca2, hm2] using h
  have r3 := Run.assign (x := "cr") ev3
  set σ3 := σ2.setVar "cr" (a - m) with hσ3
  have hcr3 : σ3.vars "cr" = a - m := by simp [hσ3, Env.setVar]
  have hkj3 : σ3.vars "kj" = arr.getD (2 + 2 * (m * n) + b) 0 := by simp [hσ3, hσ2, Env.setVar]
  have hc : (Cond.lt (V "cr") (V "kj")).evalB B σ3
      = some (decide (a - m < arr.getD (2 + 2 * (m * n) + b) 0)) := by
    have h := evalB_condLt (B := B) (σ := σ3)
      (evalB_var (B := B) (x := "cr") (σ := σ3) (by omega))
      (evalB_var (B := B) (x := "kj") (σ := σ3) (by omega))
    simpa [hcr3, hkj3] using h
  have hcb3 : σ3.vars "cb" = b := by simp [hσ3, hσ2, Env.setVar, hcb1]
  have hg3 : σ3.vars "g" = dm := by simp [hσ3, hσ2, Env.setVar, h1 "g" (by decide), hg]
  have hn13 : σ3.vars "n1" = n + 1 := by
    simp [hσ3, hσ2, Env.setVar, h1 "n1" (by decide), hn1]
  have hbase : ∀ σ' : Env, (∀ y ∉ ["v", "s", "u", "i2"], σ'.vars y = σ3.vars y) →
      σ'.arrs = σ3.arrs → (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
    intro σ' hv ha
    refine ⟨fun y hy => ?_, ?_⟩
    · have hy1 : y ∉ SCR := by
        intro h; exact hy (by simp only [SCP, SCB, List.mem_append]; tauto)
      have hyk : y ≠ "kj" := fun h => hy (by simp [SCP, h])
      have hyr : y ≠ "cr" := fun h => hy (by simp [SCP, h])
      have hy2 : y ∉ ["v", "s", "u", "i2"] := fun h => hy1 (by
        simp only [SCR, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)
      rw [hv y hy2]
      simp [hσ3, hσ2, Env.setVar, hyk, hyr, h1 y hy1]
    · rw [ha]; simp [hσ3, hσ2, Env.setVar, a1]
  by_cases hk : a - m < arr.getD (2 + 2 * (m * n) + b) 0
  · have hcT : (Cond.lt (V "cr") (V "kj")).evalB B σ3 = some true := by rw [hc]; exact congrArg some (decide_eq_true hk)
    have ev4 : (add (V "g") (add (V "cb") (.lit 1))).evalB B σ3 = some (dm + (b + 1)) := by
      have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ3) (by omega))
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "cb") (σ := σ3) (by omega))
          (evalB_lit (B := B) (σ := σ3) (n := 1) (by omega)) (by simp [hcb3]; omega))
        (by simp [hg3, hcb3]; omega)
      simpa [hg3, hcb3] using h
    obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVal_spec (B := B)
      (add (V "g") (add (V "cb") (.lit 1))) (fun _ => dm + (b + 1)) Sz σ3
      ⟨ev4, by omega, hs _ (by omega)⟩
    obtain ⟨hv4, ha4⟩ := hbase σ4 v4 a4
    refine ⟨σ4, ((r1.seq (r2.seq (r3.seq (Run.ite_true hcT r4))))).mono ?_, ?_, hv4, ha4⟩
    · simp [Expr.size, Cond.size]; omega
    · rw [o4, if_pos hk]
      simp [hσ3, hσ2, Env.setVar, o1]
  · have hcF : (Cond.lt (V "cr") (V "kj")).evalB B σ3 = some false := by rw [hc]; exact congrArg some (decide_eq_false hk)
    have ev4 : (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1))).evalB B σ3
        = some (dm + (n + 1) + (b + 1)) := by
      have h := evalB_bin (B := B) (op := .add)
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ3) (by omega))
          (evalB_var (B := B) (x := "n1") (σ := σ3) (by omega)) (by simp [hg3, hn13]; omega))
        (evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "cb") (σ := σ3) (by omega))
          (evalB_lit (B := B) (σ := σ3) (n := 1) (by omega)) (by simp [hcb3]; omega))
        (by simp [hg3, hn13, hcb3]; omega)
      simpa [hg3, hn13, hcb3] using h
    obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVal_spec (B := B)
      (add (add (V "g") (V "n1")) (add (V "cb") (.lit 1))) (fun _ => dm + (n + 1) + (b + 1)) Sz σ3
      ⟨ev4, by omega, hs _ (by omega)⟩
    obtain ⟨hv4, ha4⟩ := hbase σ4 v4 a4
    refine ⟨σ4, ((r1.seq (r2.seq (r3.seq (Run.ite_false hcF r4))))).mono ?_, ?_, hv4, ha4⟩
    · simp [Expr.size, Cond.size]; omega
    · rw [o4, if_neg hk]
      simp [hσ3, hσ2, Env.setVar, o1]


/-- **A cell of a new client.** -/
theorem clCell_run (Sz : ℕ) (n dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm) (hsum : dm + 2 * n + 16 < B) :
    ∃ σ', Run B (.seq (emitVar "n1") (emitVal (add (V "g") (V "n1")))) σ σ'
        ((48 * Sz + 50) + (1 + 3 + (48 * Sz + 40))) ∧
      σ'.out = σ.out ++ (bitsNat (n + 1) ++ bitsNat (dm + (n + 1))) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n1" Sz σ
    ⟨by rw [hn1]; omega, by rw [hn1]; exact hs _ (by omega)⟩
  have h1 : ∀ y ∉ ["v", "s", "u", "i2"], σ1.vars y = σ.vars y := v1
  have hn11 : σ1.vars "n1" = n + 1 := by rw [h1 "n1" (by decide)]; exact hn1
  have hg1 : σ1.vars "g" = dm := by rw [h1 "g" (by decide)]; exact hg
  have ev : (add (V "g") (V "n1")).evalB B σ1 = some (dm + (n + 1)) := by
    have h := evalB_bin (B := B) (op := .add) (evalB_var (B := B) (x := "g") (σ := σ1) (by omega))
      (evalB_var (B := B) (x := "n1") (σ := σ1) (by omega)) (by simp [hg1, hn11]; omega)
    simpa [hg1, hn11] using h
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVal_spec (B := B) (add (V "g") (V "n1"))
    (fun _ => dm + (n + 1)) Sz σ1 ⟨ev, by omega, hs _ (by omega)⟩
  refine ⟨σ2, (r1.seq r2).mono (by simp [Expr.size]), ?_, fun y hy => ?_, ?_⟩
  · rw [o2, o1, hn1]; simp
  · have hy' : y ∉ ["v", "s", "u", "i2"] := fun h => hy (by
      simp only [SCP, SCB, SCR, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      tauto)
    rw [v2 y hy', h1 y hy']
  · rw [a2, a1]

/-- Write a cell of the image. -/
def cellBodyL : Com :=
  .seq (.assign "ca" (.bin .div (V "i") (V "n2")))
  (.seq (.assign "cb" (sub (V "i") (mul (V "ca") (V "n2"))))
   (.ite (.lt (V "cb") (V "n"))
     (.ite (.lt (V "ca") (V "m"))
        (.seq (.assign "cs" (add (mul (V "ca") (V "n")) (V "cb")))
          (.seq (emitCell "cs" 0) (emitCell "cs" 1)))
        newCell)
     (.seq (emitVar "n1") (emitVal (add (V "g") (V "n1"))))))

/-- The cost of a cell. -/
def KcellP (Sz : ℕ) : ℕ := 300 + 4 * (48 * Sz + 60)

/-- **A cell of the image.** -/
theorem cellBodyL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn2 : σ.vars "n2" = n + 2) (hn1 : σ.vars "n1" = n + 1) (hg : σ.vars "g" = dm)
    (hN2 : σ.vars "N2" = 2 * (m * n))
    (ht : σ.vars "i" < 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B cellBodyL σ σ' (KcellP Sz) ∧
      σ'.out = σ.out ++ numBits (cellLG arr n m dm (σ.vars "i")) ∧
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨t, ht'⟩ : ∃ t, σ.vars "i" = t := ⟨_, rfl⟩
  rw [ht'] at ht ⊢
  have hn1p : 0 < n + 2 := by omega
  obtain ⟨a, ha⟩ : ∃ a, a = t / (n + 2) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = t % (n + 2) := ⟨_, rfl⟩
  have hdm : (n + 2) * a + b = t := by rw [ha, hb]; exact Nat.div_add_mod t (n + 2)
  have hale : a ≤ t := by rw [ha]; exact Nat.div_le_self _ _
  have hb_lt : b < n + 2 := by rw [hb]; exact Nat.mod_lt _ hn1p
  have ha_lt : a < 2 * m := by rw [ha, Nat.div_lt_iff_lt_mul hn1p]; exact ht
  have hmc : a * (n + 2) = (n + 2) * a := Nat.mul_comm _ _
  have hiB : t < B := by omega
  have ev1 : (Expr.bin .div (V "i") (V "n2")).evalB B σ = some a := by
    have h := evalB_bin (B := B) (op := .div) (evalB_var (B := B) (x := "i") (σ := σ) (by omega))
      (evalB_var (B := B) (x := "n2") (σ := σ) (by omega)) (by simp [hn2, ht']; omega)
    simpa [hn2, ht', ha] using h
  have r1 := Run.assign (x := "ca") ev1
  set σ1 := σ.setVar "ca" a with hσ1
  have h1i : σ1.vars "i" = t := by simp [hσ1, Env.setVar, ht']
  have h1n2 : σ1.vars "n2" = n + 2 := by simp [hσ1, Env.setVar, hn2]
  have h1ca : σ1.vars "ca" = a := by simp [hσ1, Env.setVar]
  have ev2a : (mul (V "ca") (V "n2")).evalB B σ1 = some (a * (n + 2)) := by
    have h := evalB_bin (B := B) (op := .mul) (evalB_var (B := B) (x := "ca") (σ := σ1) (by omega))
      (evalB_var (B := B) (x := "n2") (σ := σ1) (by omega)) (by simp [h1ca, h1n2]; omega)
    simpa [h1ca, h1n2] using h
  have ev2 : (sub (V "i") (mul (V "ca") (V "n2"))).evalB B σ1 = some b := by
    have h := evalB_bin (B := B) (op := .sub) (evalB_var (B := B) (x := "i") (σ := σ1) (by omega))
      ev2a (by simp [h1i]; omega)
    have e : t - a * (n + 2) = b := by omega
    simpa [h1i, e] using h
  have r2 := Run.assign (x := "cb") ev2
  set σ2 := σ1.setVar "cb" b with hσ2
  have h2ca : σ2.vars "ca" = a := by simp [hσ2, Env.setVar, h1ca]
  have h2cb : σ2.vars "cb" = b := by simp [hσ2, Env.setVar]
  have h2n : σ2.vars "n" = n := by simp [hσ2, hσ1, Env.setVar, hn]
  have h2m : σ2.vars "m" = m := by simp [hσ2, hσ1, Env.setVar, hm]
  have h2n1 : σ2.vars "n1" = n + 1 := by simp [hσ2, hσ1, Env.setVar, hn1]
  have h2g : σ2.vars "g" = dm := by simp [hσ2, hσ1, Env.setVar, hg]
  have h2N2 : σ2.vars "N2" = 2 * (m * n) := by simp [hσ2, hσ1, Env.setVar, hN2]
  have h2A : σ2.arrs "TK" = arr := by simp [hσ2, hσ1, Env.setVar, hA]
  have hc1 : (Cond.lt (V "cb") (V "n")).evalB B σ2 = some (decide (b < n)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "cb") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "n") (σ := σ2) (by omega))
    simpa [h2cb, h2n] using h
  have hc2 : (Cond.lt (V "ca") (V "m")).evalB B σ2 = some (decide (a < m)) := by
    have h := evalB_condLt (B := B) (σ := σ2) (evalB_var (B := B) (x := "ca") (σ := σ2) (by omega))
      (evalB_var (B := B) (x := "m") (σ := σ2) (by omega))
    simpa [h2ca, h2m] using h
  have hbase : ∀ σ' : Env, (∀ y ∉ SCP, σ'.vars y = σ2.vars y) → σ'.arrs = σ2.arrs →
      (∀ y ∉ SCP, σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs := by
    intro σ' hv ha'
    refine ⟨fun y hy => ?_, ?_⟩
    · have hyc : y ≠ "ca" := fun h => hy (by simp [SCP, SCB, h])
      have hyb : y ≠ "cb" := fun h => hy (by simp [SCP, SCB, h])
      rw [hv y hy]
      simp [hσ2, hσ1, Env.setVar, hyc, hyb]
    · rw [ha']; simp [hσ2, hσ1, Env.setVar]
  by_cases hbn : b < n
  · by_cases ham : a < m
    · have hab : a * n + b < m * n := cell_lt ham hbn
      have hnpos : 1 ≤ n := by omega
      obtain ⟨σ3, r3, o3, v3, a3⟩ := branchOld (B := B) Sz arr n m σ2 a b hs h2A h2ca h2cb h2n ham hbn
        hnB hab (by omega) (fun k hk => hE k (by omega)) (by omega) (by omega)
      have hcell : cellLG arr n m dm t = [arr.getD (2 + 2 * (a * n + b)) 0,
          arr.getD (2 + 2 * (a * n + b) + 1) 0] := by
        unfold cellLG; rw [← ha, ← hb, if_pos hbn, if_pos ham]
      have hv3 : ∀ y ∉ SCP, σ3.vars y = σ2.vars y := fun y hy => v3 y (scb_of_scp hy)
      obtain ⟨hv, ha3⟩ := hbase σ3 hv3 a3
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_true (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hv, ha3⟩
      · simp [Cond.size, Expr.size, KcellP]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
    · have ham' : m ≤ a := by omega
      obtain ⟨σ3, r3, o3, v3, a3⟩ := newCell_run (B := B) Sz arr n m dm σ2 a b hs h2A h2ca h2cb h2m
        h2n1 h2g h2N2 hbn ham' (by omega) hmB hsum hE hL hlen
      have hcell : cellLG arr n m dm t = [1, if a - m < arr.getD (2 + 2 * (m * n) + b) 0
          then dm + (b + 1) else dm + (n + 1) + (b + 1)] := by
        unfold cellLG; rw [← ha, ← hb, if_pos hbn, if_neg ham]
      obtain ⟨hv, ha3⟩ := hbase σ3 v3 a3
      refine ⟨σ3, (r1.seq (r2.seq (Run.ite_true (by simpa [hbn] using hc1)
        (Run.ite_false (by simpa [ham] using hc2) r3)))).mono ?_, ?_, hv, ha3⟩
      · simp [Cond.size, Expr.size, KcellP]; omega
      · rw [o3, hcell, numBits_pair]
        simp [hσ2, hσ1, Env.setVar]
  · obtain ⟨σ3, r3, o3, v3, a3⟩ := clCell_run (B := B) Sz n dm σ2 hs h2n1 h2g hsum
    have hcell : cellLG arr n m dm t = [n + 1, dm + (n + 1)] := by
      unfold cellLG; rw [← hb, if_neg hbn]
    obtain ⟨hv, ha3⟩ := hbase σ3 v3 a3
    refine ⟨σ3, (r1.seq (r2.seq (Run.ite_false (by simpa [hbn] using hc1) r3))).mono ?_, ?_, hv,
      ha3⟩
    · simp [Cond.size, Expr.size, KcellP]; omega
    · rw [o3, hcell, numBits_pair]
      simp [hσ2, hσ1, Env.setVar]


/-- **The loop over the cells.** -/
theorem cellLoopL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ0 : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ0.arrs "TK" = arr) (hn : σ0.vars "n" = n) (hm : σ0.vars "m" = m)
    (hn2 : σ0.vars "n2" = n + 2) (hn1 : σ0.vars "n1" = n + 1) (hg : σ0.vars "g" = dm)
    (hN2 : σ0.vars "N2" = 2 * (m * n))
    (hM : σ0.vars "M2" = 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B (outLoop "M2" cellBodyL) σ0 σ' ((KcellP Sz + 10 + 4) * (2 * m * (n + 2)) + 6) ∧
      σ'.out = σ0.out ++ numBits ((List.range (2 * m * (n + 2))).flatMap (cellLG arr n m dm)) ∧
      (∀ y ∉ "i" :: SCP, σ'.vars y = σ0.vars y) ∧ σ'.arrs = σ0.arrs := by
  obtain ⟨σ', r, o, hAg⟩ := eLoop (B := B) "M2" cellBodyL ("i" :: SCP)
    (fun t => numBits (cellLG arr n m dm t)) (KcellP Sz) (2 * m * (n + 2)) σ0
    (by simp) (by decide) hM (by omega) (by
      intro σ hAg hlt
      have hA' : σ.arrs "TK" = arr := by rw [hAg.1]; exact hA
      have hn' : σ.vars "n" = n := by rw [hAg.2 "n" (by decide)]; exact hn
      have hm' : σ.vars "m" = m := by rw [hAg.2 "m" (by decide)]; exact hm
      have hn2' : σ.vars "n2" = n + 2 := by rw [hAg.2 "n2" (by decide)]; exact hn2
      have hn1' : σ.vars "n1" = n + 1 := by rw [hAg.2 "n1" (by decide)]; exact hn1
      have hg' : σ.vars "g" = dm := by rw [hAg.2 "g" (by decide)]; exact hg
      have hN2' : σ.vars "N2" = 2 * (m * n) := by rw [hAg.2 "N2" (by decide)]; exact hN2
      obtain ⟨σ1, r1, o1, v1, a1⟩ := cellBodyL_run (B := B) Sz arr n m dm σ hs hA' hn' hm' hn2' hn1'
        hg' hN2' hlt hM2 hnB hmB hsum hE hL hlen
      refine ⟨σ1, r1, o1, ⟨a1.trans hAg.1, fun y hy => ?_⟩, ?_⟩
      · have hy' : y ∉ SCP := fun h => hy (List.mem_cons_of_mem _ h)
        rw [v1 y hy', hAg.2 y hy]
      · exact v1 "i" (by decide))
  refine ⟨σ', r, ?_, hAg.2, hAg.1⟩
  rw [o, numBits_flatMap]

/-- Write the whole image. -/
def printL : Com :=
  .seq (emitVar "n2") (.seq (emitVar "m2") (.seq (outLoop "M2" cellBodyL) (emitVar "m")))

/-- The cost of writing the image. -/
def KprintL (Sz M2 : ℕ) : ℕ := 3 * (48 * Sz + 50) + (KcellP Sz + 10 + 4) * M2 + 6

/-- **Writing the image.** -/
theorem printL_run (Sz : ℕ) (arr : List ℕ) (n m dm : ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hA : σ.arrs "TK" = arr) (hn : σ.vars "n" = n) (hm : σ.vars "m" = m)
    (hn2 : σ.vars "n2" = n + 2) (hm2 : σ.vars "m2" = 2 * m) (hn1 : σ.vars "n1" = n + 1)
    (hg : σ.vars "g" = dm) (hN2 : σ.vars "N2" = 2 * (m * n))
    (hM : σ.vars "M2" = 2 * m * (n + 2)) (hM2 : 2 * m * (n + 2) + 8 < B)
    (hnB : n + 8 < B) (hmB : m + 8 < B) (hsum : dm + 2 * n + 16 < B)
    (hE : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (m * n) + n + 8 < B) (hlen : 2 + 2 * (m * n) + n ≤ arr.length) :
    ∃ σ', Run B printL σ σ' (KprintL Sz (2 * m * (n + 2))) ∧
      σ'.out = σ.out ++ numBits (outLG arr n m dm) := by
  have h2m : 2 * m ≤ 2 * m * (n + 2) := Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨σ1, r1, o1, v1, a1⟩ := emitVar_spec (B := B) "n2" Sz σ
    ⟨by rw [hn2]; omega, by rw [hn2]; exact hs _ (by omega)⟩
  have z1 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ1.vars y = σ.vars y := v1
  obtain ⟨σ2, r2, o2, v2, a2⟩ := emitVar_spec (B := B) "m2" Sz σ1
    ⟨by rw [v1 "m2" (by decide), hm2]; omega,
      by rw [v1 "m2" (by decide), hm2]; exact hs _ (by omega)⟩
  have z2 : ∀ y, y ∉ ["v", "s", "u", "i2"] → σ2.vars y = σ.vars y := fun y hy => by
    rw [v2 y hy, v1 y hy]
  have A2 : σ2.arrs "TK" = arr := by rw [a2, a1]; exact hA
  obtain ⟨σ3, r3, o3, v3, a3⟩ := cellLoopL_run (B := B) Sz arr n m dm σ2 hs A2
    (by rw [z2 "n" (by decide)]; exact hn) (by rw [z2 "m" (by decide)]; exact hm)
    (by rw [z2 "n2" (by decide)]; exact hn2) (by rw [z2 "n1" (by decide)]; exact hn1)
    (by rw [z2 "g" (by decide)]; exact hg) (by rw [z2 "N2" (by decide)]; exact hN2)
    (by rw [z2 "M2" (by decide)]; exact hM) hM2 hnB hmB hsum hE hL hlen
  -- the parameter: `m` is not touched by the loop
  have hm3 : σ3.vars "m" = m := by
    rw [v3 "m" (by decide), z2 "m" (by decide)]; exact hm
  obtain ⟨σ4, r4, o4, v4, a4⟩ := emitVar_spec (B := B) "m" Sz σ3
    ⟨by rw [hm3]; omega, by rw [hm3]; exact hs _ (by omega)⟩
  refine ⟨σ4, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold KprintL; omega), ?_⟩
  rw [o4, o3, o2, o1, hm3, hn2, z1 "m2" (by decide), hm2]
  unfold outLG
  simp only [numBits_append, numBits_cons, numBits_nil, List.append_nil, List.append_assoc]

/-- Write the image of an instance without clients. -/
def print0L : Com := .seq (emitLit 0) (.seq (emitLit 0) (emitLit 0))

theorem print0L_run (Sz : ℕ) (σ : Env) (hs : ∀ v, v + 4 < B → v.size ≤ Sz) (hB : 6 < B) :
    ∃ σ', Run B print0L σ σ' (3 * (48 * Sz + 50)) ∧ σ'.out = σ.out ++ numBits [0, 0, 0] := by
  obtain ⟨σ1, r1, o1, v1, a1⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ trivial
  obtain ⟨σ2, r2, o2, v2, a2⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ1 trivial
  obtain ⟨σ3, r3, o3, v3, a3⟩ := (emitLit_spec (B := B) 0 Sz (by omega) (hs _ (by omega))) σ2 trivial
  refine ⟨σ3, (r1.seq (r2.seq r3)).mono (by omega), ?_⟩
  rw [o3, o2, o1]
  simp [numBits]

end Lax117284Proofs.Machine.PerProg

end

/-! ### `Lax117284Proofs.Machine.PerAccept` -/

section
/-!
The whole of the reduction of Lemma 15 after the tokenizer has accepted: read the counts off the
array, check the table and the parameters, find the largest due date, and write either the image or
the rejected word.
-/

namespace Lax117284Proofs.Machine.PerAccept

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Bits
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.InstSem Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.Flag Lax117284Proofs.Machine.BlockCheck
open Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.PerCheck Lax117284Proofs.Machine.PerProg
open Lax117284Proofs.Machine.FreeAccept

variable {B : ℕ}

/-- Read the counts off the array. -/
def prepP : Com :=
  .seq (.assign "n" (.get "TK" (.lit 0)))
  (.seq (.assign "m" (.get "TK" (.lit 1)))
  (.seq (.assign "N" (mul (V "m") (V "n")))
  (.seq (.assign "N2" (mul (.lit 2) (V "N")))
  (.seq (.assign "n1" (add (V "n") (.lit 1)))
  (.seq (.assign "n2" (add (V "n") (.lit 2)))
  (.seq (.assign "m2" (mul (.lit 2) (V "m")))
  (.seq (.assign "M2" (mul (V "m2") (V "n2")))
  (.seq (.assign "g" (.lit 0))
    (.assign "ok" (.lit 1))))))))))

set_option maxHeartbeats 1600000 in
theorem prepP_spec (arr : List ℕ)
    (hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0, arr.getD k 0 + 8 < B)
    (hL : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 + 8 < B)
    (hlen : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hm2 : 2 * arr.getD 1 0 + 8 < B)
    (hM2 : 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) + 8 < B) :
    Spec B (fun σ => σ.arrs "TK" = arr) prepP
      (fun σ σ' => σ'.vars "n" = arr.getD 0 0 ∧ σ'.vars "m" = arr.getD 1 0 ∧
        σ'.vars "N" = arr.getD 1 0 * arr.getD 0 0 ∧
        σ'.vars "N2" = 2 * (arr.getD 1 0 * arr.getD 0 0) ∧
        σ'.vars "n1" = arr.getD 0 0 + 1 ∧ σ'.vars "n2" = arr.getD 0 0 + 2 ∧
        σ'.vars "m2" = 2 * arr.getD 1 0 ∧
        σ'.vars "M2" = 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) ∧ σ'.vars "g" = 0 ∧
        σ'.vars "ok" = 1 ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
        ∀ y, y ≠ "n" → y ≠ "m" → y ≠ "N" → y ≠ "N2" → y ≠ "n1" → y ≠ "n2" → y ≠ "m2" →
          y ≠ "M2" → y ≠ "g" → y ≠ "ok" → σ'.vars y = σ.vars y) 100 := by
  run_vcg
  all_goals (
    have hA := ‹σ.arrs "TK" = arr›
    have e0 := hE 0 (by omega)
    have e1 := hE 1 (by omega)
    subst hA
    try simp only [Env.setVar] at *
    try simp at *)
  all_goals try omega
  all_goals (
    intro y a b c d e f g h i j
    simp [a, b, c, d, e, f, g, h, i, j])


/-- The whole of the reduction, after the tokenizer has accepted. -/
def acceptP : Com :=
  .seq prepP (.seq okLoop (.seq parLoop
    (.ite (.eq (V "ok") (.lit 1))
      (.ite (.eq (V "n") (.lit 0)) print0L (.seq dmaxLoop printL))
      rejectPrint)))

/-- The numbers of the image, read off the array. -/
def outPG (arr : List ℕ) : List ℕ :=
  if arr.getD 0 0 = 0 then [0, 0, 0]
  else outLG arr (arr.getD 0 0) (arr.getD 1 0) (runMaxD arr (arr.getD 1 0 * arr.getD 0 0))

/-- The cost of the accepting phase, on an input of `l` numbers. -/
def KaccP (Sz l : ℕ) : ℕ := 400 + 132 * l + 3 * (48 * Sz + 50) + KprintL Sz (6 * l)

lemma KprintL_mono (Sz a b : ℕ) (h : a ≤ b) : KprintL Sz a ≤ KprintL Sz b := by
  unfold KprintL
  have := Nat.mul_le_mul_left (KcellP Sz + 10 + 4) h
  omega

lemma KaccP_mono (Sz a b : ℕ) (h : a ≤ b) : KaccP Sz a ≤ KaccP Sz b := by
  unfold KaccP
  have := KprintL_mono Sz (6 * a) (6 * b) (by omega)
  omega

theorem acceptP_run (Sz l : ℕ) (arr : List ℕ) (σ : Env)
    (hs : ∀ v, v + 4 < B → v.size ≤ Sz)
    (hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0, arr.getD k 0 + 16 < B)
    (hL : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 + 8 < B)
    (hlen : 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 ≤ arr.length)
    (hNB : 2 * (arr.getD 1 0 * arr.getD 0 0) + 8 < B)
    (hm2 : 2 * arr.getD 1 0 + 8 < B)
    (hM2 : 2 * arr.getD 1 0 * (arr.getD 0 0 + 2) + 8 < B)
    (hsum : runMaxD arr (arr.getD 1 0 * arr.getD 0 0) + 2 * arr.getD 0 0 + 16 < B)
    (hl : arr.getD 1 0 * arr.getD 0 0 + arr.getD 0 0 ≤ l)
    (hA : σ.arrs "TK" = arr) :
    ∃ σ', Run B acceptP σ σ' (KaccP Sz l) ∧
      σ'.out = σ.out ++
        (if (∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
            (∀ j < arr.getD 0 0, PassK arr (arr.getD 1 0) (2 * (arr.getD 1 0 * arr.getD 0 0)) j)
          then numBits (outPG arr) else numBits [1, 0, 1]) := by
  set n := arr.getD 0 0 with hn'
  set m := arr.getD 1 0 with hm'
  set N := m * n with hN'
  have hB2 : 6 < B := by omega
  have hE8 : ∀ k < 2 + 2 * N + n, arr.getD k 0 + 8 < B := fun k hk => by
    have := hE k hk; omega
  have hn0 : n + 8 < B := hE8 0 (by omega)
  have hm0 : m + 8 < B := hE8 1 (by omega)
  obtain ⟨σ1, r1, e1n, e1m, e1N, e1N2, e1n1, e1n2, e1m2, e1M2, e1g, e1ok, e1a, e1o, e1f⟩ :=
    (prepP_spec (B := B) arr hE8 hL hlen hNB hm2 hM2) σ hA
  have A1 : σ1.arrs "TK" = arr := by rw [e1a]; exact hA
  -- the table
  obtain ⟨σ2, r2, e2ok, e2a, e2o, e2f⟩ := okLoop_spec (B := B) arr N 1 σ1
    (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) le_rfl A1 e1N e1ok
  have A2 : σ2.arrs "TK" = arr := by rw [e2a]; exact A1
  have z2 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ2.vars y = σ1.vars y := e2f
  -- the parameters
  obtain ⟨σ3, r3, e3ok, e3a, e3o, e3f⟩ := parLoop_spec (B := B) arr n m (2 * N)
    (flagTo (Pass arr) 1 N) σ2 hE8 hL hlen hn0 hm0 (flagTo_le _ _ _) A2
    (by rw [z2 "n" (by decide) (by decide) (by decide) (by decide), e1n])
    (by rw [z2 "m" (by decide) (by decide) (by decide) (by decide), e1m])
    (by rw [z2 "N2" (by decide) (by decide) (by decide) (by decide), e1N2]) e2ok
  have A3 : σ3.arrs "TK" = arr := by rw [e3a]; exact A2
  have z3 : ∀ y, y ≠ "ok" → y ≠ "i" → y ≠ "p" → y ≠ "d" → σ3.vars y = σ1.vars y :=
    fun y a b c d => by rw [e3f y a b c, z2 y a b c d]
  have hcond : (σ3.vars "ok" = 1) ↔
      ((∀ t < N, Pass arr t) ∧ (∀ j < n, PassK arr m (2 * N) j)) := by
    rw [e3ok, flagTo_eq_one, flagTo_eq_one]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨rfl, h1⟩, h2⟩
  have hokB : σ3.vars "ok" < B := by
    rw [e3ok]; have := flagTo_le (PassK arr m (2 * N)) (flagTo (Pass arr) 1 N) n; omega
  have hn3 : σ3.vars "n" = n := by
    rw [z3 "n" (by decide) (by decide) (by decide) (by decide), e1n]
  by_cases hok : σ3.vars "ok" = 1
  · obtain ⟨hpass, hparam⟩ := hcond.1 hok
    have hcondT : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some true := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    have hnB : σ3.vars "n" < B := by omega
    by_cases hn00 : n = 0
    · have hcondT2 : (Cond.eq (V "n") (.lit 0)).evalB B σ3 = some true := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn3, hn00]
      obtain ⟨σ4, r4, o4⟩ := print0L_run (B := B) Sz σ3 hs hB2
      refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_true hcondT2 r4))))).mono ?_, ?_⟩
      · unfold KaccP KprintL
        simp only [Cond.size, Expr.size]
        omega
      · rw [o4, e3o, e2o, e1o, if_pos ⟨hpass, hparam⟩]
        unfold outPG
        rw [if_pos hn00]
    · have hcondF2 : (Cond.eq (V "n") (.lit 0)).evalB B σ3 = some false := by
        rw [evalB_condEq (evalB_var hnB) (evalB_lit (by omega))]
        simp [hn3, hn00]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn00
      -- the largest due date
      obtain ⟨σ4, r4, e4g, e4a, e4o, e4f⟩ := dmaxLoop_spec (B := B) arr N σ3
        (fun k hk => hE8 k (by omega)) (by omega) (by omega) (by omega) A3
        (by rw [z3 "N" (by decide) (by decide) (by decide) (by decide), e1N])
        (by rw [z3 "g" (by decide) (by decide) (by decide) (by decide), e1g])
      have A4 : σ4.arrs "TK" = arr := by rw [e4a]; exact A3
      have z4 : ∀ y, y ≠ "g" → y ≠ "i" → y ≠ "p" → y ≠ "ok" → y ≠ "d" →
          σ4.vars y = σ1.vars y := fun y a b c d e => by
        rw [e4f y a b c, z3 y d b c e]
      have hg4 : σ4.vars "g" = runMaxD arr N := e4g
      have hM2' : 2 * m * (n + 2) ≤ 6 * l := by
        rcases Nat.eq_zero_or_pos m with hm00 | hm00
        · rw [hm00]; simp
        · have : n + 2 ≤ 3 * n := by omega
          have h2 := Nat.mul_le_mul_left (2 * m) this
          have h3 : 2 * m * (3 * n) = 6 * (m * n) := by ring
          omega
      obtain ⟨σ5, r5, o5⟩ := printL_run (B := B) Sz arr n m (runMaxD arr N) σ4 hs A4
        (by rw [z4 "n" (by decide) (by decide) (by decide) (by decide) (by decide), e1n])
        (by rw [z4 "m" (by decide) (by decide) (by decide) (by decide) (by decide), e1m])
        (by rw [z4 "n2" (by decide) (by decide) (by decide) (by decide) (by decide), e1n2])
        (by rw [z4 "m2" (by decide) (by decide) (by decide) (by decide) (by decide), e1m2])
        (by rw [z4 "n1" (by decide) (by decide) (by decide) (by decide) (by decide), e1n1])
        hg4
        (by rw [z4 "N2" (by decide) (by decide) (by decide) (by decide) (by decide), e1N2])
        (by rw [z4 "M2" (by decide) (by decide) (by decide) (by decide) (by decide), e1M2])
        hM2 hn0 hm0 hsum hE8 hL hlen
      refine ⟨σ5, (r1.seq (r2.seq (r3.seq (Run.ite_true hcondT (Run.ite_false hcondF2
        (r4.seq r5)))))).mono ?_, ?_⟩
      · unfold KaccP
        simp only [Cond.size, Expr.size]
        have := KprintL_mono Sz _ _ hM2'
        omega
      · rw [o5, e4o, e3o, e2o, e1o, if_pos ⟨hpass, hparam⟩]
        unfold outPG
        rw [if_neg hn00]
  · have hno : ¬ ((∀ t < N, Pass arr t) ∧ (∀ j < n, PassK arr m (2 * N) j)) :=
      fun h => hok (hcond.2 h)
    obtain ⟨σ4, r4, e4o, e4a, e4f⟩ := rejectPrint_run (B := B) Sz σ3 hs hB2
    have hcondF : (Cond.eq (V "ok") (.lit 1)).evalB B σ3 = some false := by
      rw [evalB_condEq (evalB_var hokB) (evalB_lit (by omega))]
      simp [hok]
    refine ⟨σ4, (r1.seq (r2.seq (r3.seq (Run.ite_false hcondF r4)))).mono ?_, ?_⟩
    · unfold KaccP
      simp only [Cond.size, Expr.size]
      omega
    · rw [e4o, e3o, e2o, e1o, if_neg hno]

end Lax117284Proofs.Machine.PerAccept

end

/-! ### `Lax117284Proofs.Machine.PerFinal` -/

section
/-!
The reduction of Lemma 15 from per-client parameters to a uniform one is polynomial-time
computable.
-/

namespace Lax117284Proofs.Machine.PerFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.BlockSem
open Lax117284Proofs.Machine.BlockCheck Lax117284Proofs.Machine.PerSem Lax117284Proofs.Machine.PerCheck
open Lax117284Proofs.Machine.PerProg Lax117284Proofs.Machine.PerAccept Lax117284Proofs.Machine.Wrap
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.PNk Lax117284Proofs.Machine.BlockFinal

open scoped Classical

/-- The streams that are mapped to an image. -/
def condP (ns : List ℕ) : Prop := Valid ns ∧ ∀ j < ns.getD 0 0, paramAt ns j ≤ ns.getD 1 0

lemma cellLG_congr (arr ns : List ℕ) (n m dm t : ℕ)
    (h : ∀ k < 2 + 2 * (m * n) + n, arr.getD k 0 = ns.getD k 0) :
    cellLG arr n m dm t = cellLG ns n m dm t := by
  unfold cellLG
  by_cases hb : t % (n + 2) < n
  · by_cases ha : t / (n + 2) < m
    · have hab := cell_lt ha hb
      rw [if_pos hb, if_pos ha, if_pos hb, if_pos ha, h _ (by omega), h _ (by omega)]
    · rw [if_pos hb, if_neg ha, if_pos hb, if_neg ha, h _ (by omega)]
  · rw [if_neg hb, if_neg hb]

theorem outPG_eq (arr ns : List ℕ) (hs : Shape eP ns) (h : arr.take ns.length = ns) :
    outPG arr = outLAll ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eP] at hl
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  unfold outPG outLAll
  rw [h0, h1]
  by_cases hn : ns.getD 0 0 = 0
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    unfold outL outLG
    have hk : ∀ k < 2 + 2 * (ns.getD 1 0 * ns.getD 0 0) + ns.getD 0 0, arr.getD k 0 = ns.getD k 0 :=
      fun k hk => hg k (by omega)
    have hmax : runMaxD arr (ns.getD 1 0 * ns.getD 0 0) = dmaxOf ns := by
      unfold dmaxOf
      exact runMaxD_congr arr ns _ (fun j hj => hg _ (by
        have : ns.getD 0 0 ≥ 1 := by omega
        have h3 : j < ns.getD 1 0 * ns.getD 0 0 := hj
        omega))
    rw [hmax]
    have hcells : (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap
        (cellLG arr (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns))
        = (List.range (2 * ns.getD 1 0 * (ns.getD 0 0 + 2))).flatMap
          (cellLG ns (ns.getD 0 0) (ns.getD 1 0) (dmaxOf ns)) :=
      List.flatMap_congr fun t _ => cellLG_congr arr ns _ _ _ t hk
    rw [hcells]

theorem cond_iffP (arr ns : List ℕ) (h : arr.take ns.length = ns) (hs : Shape eP ns) :
    ((∀ t < arr.getD 1 0 * arr.getD 0 0, Pass arr t) ∧
      (∀ j < arr.getD 0 0, PassK arr (arr.getD 1 0) (2 * (arr.getD 1 0 * arr.getD 0 0)) j)) ↔
      condP ns := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eP] at hl
  have h0 := hg 0 (by omega)
  have h1 := hg 1 (by omega)
  unfold condP
  rw [h0, h1]
  constructor
  · rintro ⟨hp, hq⟩
    refine ⟨fun t ht => ?_, fun j hj => ?_⟩
    · have := hp t ht
      unfold Pass at this
      rw [hg _ (by omega), hg _ (by omega)] at this
      exact this
    · have := hq j hj
      unfold PassK at this
      rw [hg _ (by omega)] at this
      exact this
  · rintro ⟨hv, hq⟩
    refine ⟨fun t ht => ?_, fun j hj => ?_⟩
    · have := hv t ht
      unfold Pass
      rw [hg _ (by omega), hg _ (by omega)]
      exact this
    · have := hq j hj
      unfold PassK
      rw [hg _ (by omega)]
      exact this

lemma KmonoP (Sz a b : ℕ) (h : a ≤ b) : KaccP Sz a ≤ KaccP Sz b := KaccP_mono Sz a b h

/-- **The reduction as a reduction on numbers.** -/
noncomputable def W : Wrap where
  E := EI eP
  Sh := Shape eP
  nk := PNk.nkP
  Knk := 60
  hnk := fun B Bt cap hB => PNk.nkP_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eP hs
  hshape := fun ts h => shape_of_conforms eP h
  red := Lax117284.Lemma15.reduce
  cond := condP
  outW := fun ns => numCode (outLAll ns)
  sem_acc := fun ns hs hc => per_eq ns hc.1 hs hc.2
  sem_rej := fun w h => per_rej w (by
    rintro ⟨ns, hw, hs, hv, hp⟩
    exact h ⟨ns, hw, hs, hv, hp⟩)
  rejW := rejected
  rej := FreeAccept.rejectPrint
  Krej := fun Sz => 3 * (48 * Sz + 50)
  rejRun := fun B Sz σ hs hB => by
    obtain ⟨σ', r, o, -, -⟩ := FreeAccept.rejectPrint_run (B := B) Sz σ hs hB
    exact ⟨σ', r, by rw [o, FreeMain.natBits_rejected]⟩
  acc := acceptP
  Kacc := KaccP
  Kmono := KmonoP
  accRun := fun B Sz L ns arr σ hsh harr hA hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    simp only [eP] at hl
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0,
        arr.getD k 0 + 16 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hmn : arr.getD 0 0 < 2 ^ (L + 1) := by rw [h0]; exact hval 0 (by omega)
    have hmm : arr.getD 1 0 < 2 ^ (L + 1) := by rw [h1]; exact hval 1 (by omega)
    have hl' : ns.length = 2 + 2 * (arr.getD 1 0 * arr.getD 0 0) + arr.getD 0 0 := by
      rw [h0, h1]; exact hl
    have hprod : (2 * arr.getD 1 0) * (arr.getD 0 0 + 2) ≤ (2 * 2 ^ (L + 1)) * (2 ^ (L + 1) + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hpp2 : (2 * 2 ^ (L + 1)) * (2 ^ (L + 1) + 2) = 8 * (2 ^ L * 2 ^ L) + 8 * 2 ^ L := by
      rw [hpow1]; ring
    have hrm : runMaxD arr (arr.getD 1 0 * arr.getD 0 0) ≤ 2 ^ (L + 1) := by
      refine foldl_max_le (fun j => arr.getD (2 + 2 * j + 1) 0) (2 ^ (L + 1)) _ 0 (Nat.zero_le _)
        (fun j hj => ?_)
      have hj' : j < arr.getD 1 0 * arr.getD 0 0 := hj
      have := hval (2 + 2 * j + 1) (by omega)
      rw [hg _ (by omega)]
      omega
    obtain ⟨σ', r, o⟩ := acceptP_run (B := B) Sz ns.length arr σ hs hE
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hA
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : condP ns
    · rw [if_pos hc, if_pos ((cond_iffP arr ns harr ⟨h2, hl⟩).2 hc), outPG_eq arr ns ⟨h2, hl⟩ harr,
        natBits_numCode]
    · rw [if_neg hc, if_neg (fun h => hc ((cond_iffP arr ns harr ⟨h2, hl⟩).1 h)),
        FreeMain.natBits_rejected]


def layoutP : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "n1", "n2", "m2", "M2", "ca", "cb", "cs", "kj", "cr"], ["a", "TK"], 12⟩

theorem com_ok : Com.Ok layoutP W.mainW := by
  simp [Wrap.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, PNk.nkP,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptP, prepP, print0L, printL, cellBodyL, newCell, Emit.emitCell,
    FreeAccept.rejectPrint, FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    parLoop, parBody, parChk, dmaxLoop, dmaxBody, dmaxChk,
    Out.outLoop, Out.emitTK,
    Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    layoutP, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

theorem Kpoly : ∀ Sz l, W.Kacc Sz l ≤ 5000 * (Sz + 1) * (l + 1) := by
  intro Sz l
  show KaccP Sz l ≤ _
  unfold KaccP KprintL KcellP
  nlinarith [Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le (Sz * l)]

/--
---
conclusion: Lax117284.Lemma15.reduce_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a one-pass tokenizer reads
the numbers of the instance and its parameters, a first pass over the table checks that every job
takes some time and is not due before it starts, a second pass checks that no parameter exceeds
the number of days, a third finds the largest due date, and the numbers of the image are written
cell by cell, the closed form of every cell being computed from its row and column: the original
jobs on the original days, the private unit job of each client on each additional day, placed in
the stretch of the two new clients or after it according to its parameter, and the common job of
the two new clients. An instance without clients is answered with a fixed yes-instance, and a
word that is not the code of an admissible instance with the rejected word. The numbers may be
exponential in the length of the input, which the word length of a polynomial-time word RAM
accommodates, and polynomial time on the word RAM transfers to a Turing machine.
-/
theorem reduce_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax117284.Lemma15.reduce) :=
  WrapFinal.polyTime W layoutP com_ok rfl (by simp [layoutP]) 5000 Kpoly (fun Sz => by
    show 3 * (48 * Sz + 50) ≤ 5000 * (Sz + 1)
    omega)

end Lax117284Proofs.Machine.PerFinal

end
