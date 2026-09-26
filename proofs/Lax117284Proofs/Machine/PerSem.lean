import Lax117284Proofs.Machine.BlockSem
import Lax117284Proofs.Machine.PNk
import Lax117284.Lemma15

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
