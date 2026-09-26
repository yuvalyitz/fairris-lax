import Lax117284Proofs.Lemma14Build
import Lax117284Proofs.Lemma14Layout

/-!
The two descriptions of Lemma 14's instance are the same instance: the day the development
calls a vertex day, a validation day or an edge day is the numbered day of that kind, and
the clients that take part in a day's gadget are the same on both sides.
-/

namespace Lax117284Proofs.Lemma14Match

open Lax117284.MulticolouredIndepSet Lax117284.Lemma14
open Lax117284Proofs.Lemma14Graph Lax117284Proofs.Lemma14Build
open Lax117284Proofs.Lemma14Layout

variable (G : Instance)

/-! ### Reading a number as a block and a place inside it -/

theorem block_div {s i a : ℕ} (ha : a < s) : (i * s + a) / s = i := by
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) ha
  rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt ha, Nat.add_zero]

theorem block_mod {s i a : ℕ} (ha : a < s) : (i * s + a) % s = a := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

/-! ### The kind of each day -/

theorem isVertexDay_dV (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    IsVertexDay G (dayNum G hreg (Sum.inl v)) := by
  have h2 := vtx_snd_lt G hreg v
  refine ⟨dV_lt G hreg v, ?_⟩
  show (dayNum G hreg (Sum.inl v)) % (G.size + 1) < G.size
  simp only [dayNum]
  rw [block_mod (by omega)]
  exact h2

theorem dayVertex_dV (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx) :
    dayVertex G (dayNum G hreg (Sum.inl v)) = num G v := by
  have h2 := vtx_snd_lt G hreg v
  show (dayNum G hreg (Sum.inl v)) / (G.size + 1) * G.size
    + (dayNum G hreg (Sum.inl v)) % (G.size + 1) = num G v
  simp only [dayNum]
  rw [block_div (by omega), block_mod (by omega)]
  rfl

theorem isValidationDay_dW (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ) :
    IsValidationDay G (dayNum G hreg (Sum.inr (Sum.inl i))) := by
  refine ⟨dW_lt G hreg i, ?_⟩
  show ¬ (dayNum G hreg (Sum.inr (Sum.inl i))) % (G.size + 1) < G.size
  simp only [dayNum]
  rw [block_mod (by omega)]
  omega

theorem dayColour_dW (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ) :
    dayColour G (dayNum G hreg (Sum.inr (Sum.inl i))) = (i : ℕ) := by
  show (dayNum G hreg (Sum.inr (Sum.inl i))) / (G.size + 1) = (i : ℕ)
  simp only [dayNum]
  exact block_div (by omega)

theorem isEdgeDay_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    IsEdgeDay G (dayNum G hreg (Sum.inr (Sum.inr e))) := by
  show ¬ (dayNum G hreg (Sum.inr (Sum.inr e))) < G.colours * (G.size + 1)
  simp only [dayNum]
  omega

theorem dayEdge_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    dayEdge G (dayNum G hreg (Sum.inr (Sum.inr e))) = incPair G e.1.1 e.1.2 := by
  show G.edgeList.getD ((dayNum G hreg (Sum.inr (Sum.inr e)))
    - G.colours * (G.size + 1)) (0, 0) = _
  simp only [dayNum]
  rw [show G.colours * (G.size + 1) + eIdx G hreg e - G.colours * (G.size + 1)
    = eIdx G hreg e by omega]
  exact edgeAt_eIdx G hreg e

/-! ### The two edge clients of an edge day -/

theorem edgeTail_eq (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size) (q : Fin (deg G)) :
    incId G (incPair G v q).1 ((G.nbrs (incPair G v q).1).idxOf (incPair G v q).2)
      = incId G (num G v) (q : ℕ) := by
  have hlen : (q : ℕ) < (G.nbrs (num G v)).length := by
    rw [hreg _ (num_lt G v)]; exact q.isLt
  show incId G (num G v) ((G.nbrs (num G v)).idxOf (num G (nbr G v q))) = _
  rw [num_nbr G hreg]
  show incId G (num G v)
    ((G.nbrs (num G v)).idxOf ((G.nbrs (num G v)).getD (q : ℕ) 0)) = _
  rw [idxOf_getD (nbrs_nodup G (num G v)) hlen]

theorem edgeHead_eq (hreg : G.Regular (deg G)) (v : Fin G.colours × Fin G.size) (q : Fin (deg G)) :
    incId G (incPair G v q).2 ((G.nbrs (incPair G v q).2).idxOf (incPair G v q).1)
      = incId G (num G (nbr G v q)) (revNum G (num G v) (q : ℕ)) := by
  show incId G (num G (nbr G v q))
    ((G.nbrs (num G (nbr G v q))).idxOf (num G v)) = _
  rw [num_nbr G hreg]
  rfl

theorem edgeTail_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    edgeTail G (dayNum G hreg (Sum.inr (Sum.inr e)))
      = clientNum G hreg (Sum.inr (Sum.inr (Sum.inl e.1))) := by
  simp only [edgeTail]
  rw [dayEdge_dE G hreg e]
  exact edgeTail_eq G hreg e.1.1 e.1.2

theorem edgeHead_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    edgeHead G (dayNum G hreg (Sum.inr (Sum.inr e)))
      = clientNum G hreg (Sum.inr (Sum.inr (Sum.inl ((mis G hreg).rev e.1)))) := by
  simp only [edgeHead]
  rw [dayEdge_dE G hreg e]
  exact edgeHead_eq G hreg e.1.1 e.1.2

/-! ### Who takes part in a day's gadget, on both sides

The clients the development calls *big* on a day are exactly the clients the numbered
construction names in that day's gadget. -/

theorem named_iff_big_dV (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx)
    (c : (mis G hreg).Client) :
    Named G (dayNum G hreg (Sum.inl v)) (clientNum G hreg c)
      ↔ (mis G hreg).Big (Sum.inl v) c := by
  rw [named_vertexDay G (isVertexDay_dV G hreg v), dayVertex_dV G hreg v,
    Model.Lemma14.MIS.big_dV]
  have h1 : vtxId G (num G v) = clientNum G hreg (Sum.inl v) := rfl
  have h2 : selId (G.classOf (num G v)) = clientNum G hreg (Sum.inr (Sum.inl v.1)) :=
    congrArg selId (classOf_num G v)
  rw [h1, h2]
  constructor
  · rintro (h | h)
    · exact Or.inl (clientNum_injective G hreg h)
    · exact Or.inr (clientNum_injective G hreg h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem named_iff_big_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge)
    (c : (mis G hreg).Client) :
    Named G (dayNum G hreg (Sum.inr (Sum.inr e))) (clientNum G hreg c)
      ↔ (mis G hreg).Big (Sum.inr (Sum.inr e)) c := by
  rw [named_edgeDay G (isEdgeDay_dE G hreg e), edgeTail_dE G hreg e, edgeHead_dE G hreg e,
    Model.Lemma14.MIS.big_dE]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl (clientNum_injective G hreg h)))
    · exact Or.inr (Or.inr (Or.inr (clientNum_injective G hreg h)))
    · exact Or.inl (clientNum_injective G hreg h)
    · exact Or.inr (Or.inl (clientNum_injective G hreg h))
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

theorem named_iff_big_dW (hreg : G.Regular (deg G)) (i : Fin (mis G hreg).ℓ)
    (c : (mis G hreg).Client) :
    Named G (dayNum G hreg (Sum.inr (Sum.inl i))) (clientNum G hreg c)
      ↔ (mis G hreg).Big (Sum.inr (Sum.inl i)) c := by
  rw [named_validationDay G (isValidationDay_dW G hreg i), dayColour_dW G hreg i,
    Model.Lemma14.MIS.big_dW]
  rcases c with w | j | x | b | u
  · have hnum := num_lt G w
    have hc : clientNum G hreg (Sum.inl w) = 3 + G.colours + num G w := rfl
    have hsub : 3 + G.colours + num G w - (3 + G.colours) = num G w := by omega
    have hcl : G.classOf (num G w) = ((w.1 : Fin G.colours) : ℕ) := classOf_num G w
    rw [hc, hsub, hcl]
    constructor
    · rintro (⟨-, -, h3⟩ | ⟨h1, -⟩)
      · exact Or.inl ⟨w, Fin.ext h3, rfl⟩
      · exact absurd h1 (by omega)
    · rintro (⟨w', hw', hcw⟩ | ⟨x, -, hcx⟩)
      · refine Or.inl ⟨by omega, by omega, ?_⟩
        rw [Sum.inl_injective hcw]
        exact congrArg Fin.val hw'
      · exact absurd hcx (by simp)
  · have hj := col_lt G hreg j
    have hc : clientNum G hreg (Sum.inr (Sum.inl j)) = 3 + (j : ℕ) := rfl
    rw [hc]
    constructor
    · rintro (⟨h1, -, -⟩ | ⟨h1, -⟩)
      · exact absurd h1 (by omega)
      · exact absurd h1 (by omega)
    · rintro (⟨w', -, hcw⟩ | ⟨x, -, hcx⟩)
      · exact absurd hcw (by simp)
      · exact absurd hcx (by intro hh; rw [Model.Lemma14.MIS.ce] at hh; simp only [Sum.inr.injEq] at hh; cases hh)
  · have hq := inc_snd_lt G hreg x
    have hv := inc_fst_lt G hreg x
    have hc : clientNum G hreg (Sum.inr (Sum.inr (Sum.inl x)))
        = 3 + G.colours + G.vertices + (num G x.1 * deg G + (x.2 : ℕ)) := by
      show incId G (num G x.1) ((x.2 : ℕ)) = _
      simp only [incId]
      omega
    have hsub : 3 + G.colours + G.vertices + (num G x.1 * deg G + (x.2 : ℕ))
        - (3 + G.colours + G.vertices) = num G x.1 * deg G + (x.2 : ℕ) := by omega
    have hdiv : (num G x.1 * deg G + (x.2 : ℕ)) / deg G = num G x.1 := block_div hq
    have hcl : G.classOf (num G x.1) = ((x.1.1 : Fin G.colours) : ℕ) := classOf_num G x.1
    rw [hc, hsub, hdiv, hcl]
    constructor
    · rintro (⟨-, h2, -⟩ | ⟨-, h3⟩)
      · exact absurd h2 (by omega)
      · exact Or.inr ⟨x, Fin.ext h3, rfl⟩
    · rintro (⟨w', -, hcw⟩ | ⟨x', hx', hcx⟩)
      · exact absurd hcw (by simp)
      · refine Or.inr ⟨by omega, ?_⟩
        have : x = x' := by
          have := Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hcx))
          exact this
        rw [this]
        exact congrArg Fin.val hx'
  · have hc : clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inl b))))
        = (if b then 1 else 2) := rfl
    rw [hc]
    constructor
    · rintro (⟨h1, -, -⟩ | ⟨h1, -⟩)
      · exfalso; revert h1; split <;> omega
      · exfalso; revert h1; split <;> omega
    · rintro (⟨w', -, hcw⟩ | ⟨x, -, hcx⟩)
      · exact absurd hcw (by simp)
      · exact absurd hcx (by intro hh; rw [Model.Lemma14.MIS.ce] at hh; simp only [Sum.inr.injEq] at hh; cases hh)
  · have hc : clientNum G hreg (Sum.inr (Sum.inr (Sum.inr (Sum.inr u)))) = 0 := rfl
    rw [hc]
    constructor
    · rintro (⟨h1, -, -⟩ | ⟨h1, -⟩)
      · exact absurd h1 (by omega)
      · exact absurd h1 (by omega)
    · rintro (⟨w', -, hcw⟩ | ⟨x, -, hcx⟩)
      · exact absurd hcw (by simp)
      · exact absurd hcx (by intro hh; rw [Model.Lemma14.MIS.ce] at hh; simp only [Sum.inr.injEq] at hh; cases hh)

/-! ### The two layouts differ by a shift on each day

On every day the development's gadget jobs are the numbered construction's moved along by a
constant — one time unit on a vertex day and on an edge day, `r` of them on a validation
day — with the same processing times. Since a conflict is the same arithmetic condition on
both sides, a shift leaves it alone. -/

/-- How far past the numbered gadget the development's sits, on each kind of day. -/
noncomputable def shift (hreg : G.Regular (deg G)) : (mis G hreg).Day → ℕ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => deg G
  | Sum.inr (Sum.inr _) => 1

/-! #### The numbered jobs of the clients that take part -/

theorem job_dV (hreg : G.Regular (deg G)) (v : (mis G hreg).Vtx)
    {c : (mis G hreg).Client} (h : (mis G hreg).Big (Sum.inl v) c) :
    job G (dayNum G hreg (Sum.inl v)) (clientNum G hreg c) = (deg G, deg G) := by
  rw [Model.Lemma14.MIS.big_dV] at h
  have hd : dayVertex G (dayNum G hreg (Sum.inl v)) = num G v := dayVertex_dV G hreg v
  have hcl : selId (G.classOf (num G v)) = clientNum G hreg (Sum.inr (Sum.inl v.1)) :=
    congrArg selId (classOf_num G v)
  rcases h with rfl | rfl
  · have hj := job_vertexDay_vtx G (isVertexDay_dV G hreg v)
    rw [hd] at hj
    exact hj
  · have hj := job_vertexDay_sel G (isVertexDay_dV G hreg v)
    rw [hd, hcl] at hj
    exact hj

theorem job_dW_cv (hreg : G.Regular (deg G)) (j : Fin (mis G hreg).ℓ)
    (w : (mis G hreg).Vtx) (hw : w.1 = j) :
    job G (dayNum G hreg (Sum.inr (Sum.inl j))) (clientNum G hreg (Sum.inl w))
      = (deg G, deg G * ((w.2 : ℕ) + 1)) := by
  have hc : G.classOf (num G w) = dayColour G (dayNum G hreg (Sum.inr (Sum.inl j))) := by
    rw [dayColour_dW G hreg j]
    exact (classOf_num G w).trans (congrArg Fin.val hw)
  have hj := job_validationDay_vtx G (isValidationDay_dW G hreg j) (num_lt G w) hc
  rw [indexOf_num G w] at hj
  exact hj

theorem job_dW_ce (hreg : G.Regular (deg G)) (j : Fin (mis G hreg).ℓ)
    (x : (mis G hreg).Inc) (hx : x.1.1 = j) :
    job G (dayNum G hreg (Sum.inr (Sum.inl j)))
        (clientNum G hreg (Sum.inr (Sum.inr (Sum.inl x))))
      = (1, deg G * ((x.1.2 : ℕ)) + (x.2 : ℕ) + 1) := by
  have hc : G.classOf (num G x.1) = dayColour G (dayNum G hreg (Sum.inr (Sum.inl j))) := by
    rw [dayColour_dW G hreg j]
    exact (classOf_num G x.1).trans (congrArg Fin.val hx)
  have hj := job_validationDay_inc G (isValidationDay_dW G hreg j) (num_lt G x.1)
    (inc_snd_lt G hreg x) hc
  rw [indexOf_num G x.1] at hj
  exact hj

theorem head_ne_tail (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge) :
    edgeHead G (dayNum G hreg (Sum.inr (Sum.inr e)))
      ≠ edgeTail G (dayNum G hreg (Sum.inr (Sum.inr e))) := by
  rw [edgeTail_dE G hreg e, edgeHead_dE G hreg e]
  intro hh
  exact (mis G hreg).rev_ne e.1
    (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (clientNum_injective G hreg hh))))

theorem job_dE (hreg : G.Regular (deg G)) (e : (mis G hreg).Edge)
    {c : (mis G hreg).Client} (h : (mis G hreg).Big (Sum.inr (Sum.inr e)) c) :
    job G (dayNum G hreg (Sum.inr (Sum.inr e))) (clientNum G hreg c)
      = (if c = Sum.inr (Sum.inr (Sum.inl e.1)) then (1, 3)
        else if c = Sum.inr (Sum.inr (Sum.inl ((mis G hreg).rev e.1))) then (1, 1)
        else if c = Sum.inr (Sum.inr (Sum.inr (Sum.inl true))) then (2, 3) else (2, 2)) := by
  have hrev : (Sum.inr (Sum.inr (Sum.inl ((mis G hreg).rev e.1))) : (mis G hreg).Client)
      ≠ Sum.inr (Sum.inr (Sum.inl e.1)) := by
    intro hh
    exact (mis G hreg).rev_ne e.1
      (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hh)))
  rw [Model.Lemma14.MIS.big_dE] at h
  rcases h with rfl | rfl | rfl | rfl
  · rw [if_pos rfl, ← edgeTail_dE G hreg e]
    exact job_edgeDay_tail G (isEdgeDay_dE G hreg e)
  · rw [if_neg hrev, if_pos rfl, ← edgeHead_dE G hreg e]
    exact job_edgeDay_head G (isEdgeDay_dE G hreg e) (head_ne_tail G hreg e)
  · rw [if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_pos rfl]
    exact job_edgeDay_plus G (isEdgeDay_dE G hreg e)
  · rw [if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh)]
    exact job_edgeDay_minus G (isEdgeDay_dE G hreg e)

/-! #### The shift itself -/

theorem job_shift (hreg : G.Regular (deg G)) {i : (mis G hreg).Day}
    {c : (mis G hreg).Client} (h : (mis G hreg).Big i c) :
    (mis G hreg).dd i c
        = (inst G).dAt (dayNum G hreg i) (clientNum G hreg c) + shift G hreg i
      ∧ (mis G hreg).pp i c
        = (inst G).pAt (dayNum G hreg i) (clientNum G hreg c) := by
  have hi := dayNum_lt G hreg i
  have hc := clientNum_lt G hreg c
  have hd := dAt_eq G hi hc
  have hp := pAt_eq G hi hc
  rcases i with v | j | e
  · rw [hd, hp, job_dV G hreg v h]
    rw [Model.Lemma14.MIS.big_dV] at h
    rcases h with rfl | rfl
    · refine ⟨?_, ?_⟩ <;> simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift]
    · refine ⟨?_, ?_⟩ <;> simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift]
  · rw [Model.Lemma14.MIS.big_dW] at h
    rcases h with ⟨w, hw, rfl⟩ | ⟨x, hx, rfl⟩
    · rw [hd, hp, job_dW_cv G hreg j w hw]
      have hring : deg G * ((w.2 : ℕ) + 2) = deg G * ((w.2 : ℕ) + 1) + deg G := by ring
      refine ⟨?_, ?_⟩
      · show (if w.1 = j then (mis G hreg).r * ((w.2 : ℕ) + 2) else _) = _
        rw [if_pos hw]
        show (mis G hreg).r * ((w.2 : ℕ) + 2) = _
        show deg G * ((w.2 : ℕ) + 2) = deg G * ((w.2 : ℕ) + 1) + shift G hreg _
        simp only [shift]
        omega
      · show (if w.1 = j then (mis G hreg).r else 1) = _
        rw [if_pos hw]
        rfl
    · rw [hd, hp, job_dW_ce G hreg j x hx]
      have hring : deg G * ((x.1.2 : ℕ) + 1) = deg G * ((x.1.2 : ℕ)) + deg G := by ring
      refine ⟨?_, ?_⟩
      · show (if x.1.1 = j then (mis G hreg).r * ((x.1.2 : ℕ) + 1) + (x.2 : ℕ) + 1 else _) = _
        rw [if_pos hx]
        show deg G * ((x.1.2 : ℕ) + 1) + (x.2 : ℕ) + 1
          = deg G * ((x.1.2 : ℕ)) + (x.2 : ℕ) + 1 + shift G hreg _
        simp only [shift]
        omega
      · rfl
  · rw [hd, hp, job_dE G hreg e h]
    have hrev : (Sum.inr (Sum.inr (Sum.inl ((mis G hreg).rev e.1))) : (mis G hreg).Client)
        ≠ Sum.inr (Sum.inr (Sum.inl e.1)) := by
      intro hh
      exact (mis G hreg).rev_ne e.1
        (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective hh)))
    rw [Model.Lemma14.MIS.big_dE] at h
    rcases h with rfl | rfl | rfl | rfl
    · rw [if_pos rfl]
      refine ⟨?_, ?_⟩ <;> simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift]
    · rw [if_neg hrev, if_pos rfl]
      have hne := (mis G hreg).rev_ne e.1
      refine ⟨?_, ?_⟩ <;>
        simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift, hne]
    · rw [if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_pos rfl]
      refine ⟨?_, ?_⟩ <;> simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift]
    · rw [if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh), if_neg (by intro hh; simp only [Sum.inr.injEq, Sum.inl.injEq] at hh; cases hh)]
      refine ⟨?_, ?_⟩ <;> simp [Model.Lemma14.MIS.dd, Model.Lemma14.MIS.pp, shift]

/-! ### The two instances have the same conflicts

Nine cases, from the two trichotomies: the dummy client, a client taking part in the day's
gadget, and a parked one. Only the gadget-against-gadget case sees the construction at all,
and there the shift settles it; the rest are the parking facts, proved once on each side. -/

theorem named_iff_big (hreg : G.Regular (deg G)) (i : (mis G hreg).Day)
    (c : (mis G hreg).Client) :
    Named G (dayNum G hreg i) (clientNum G hreg c) ↔ (mis G hreg).Big i c := by
  rcases i with v | j | e
  · exact named_iff_big_dV G hreg v c
  · exact named_iff_big_dW G hreg j c
  · exact named_iff_big_dE G hreg e c

theorem clientNum_eq_zero_iff (hreg : G.Regular (deg G)) (c : (mis G hreg).Client) :
    clientNum G hreg c = 0 ↔ c = (mis G hreg).c0 := by
  refine ⟨fun h => clientNum_injective G hreg h, ?_⟩
  rintro rfl
  rfl

theorem conflict_iff (hreg : G.Regular (deg G)) (i : (mis G hreg).Day)
    (c c' : (mis G hreg).Client) :
    (mis G hreg).inst.Conflict i c c'
      ↔ (inst G).ConflictAt (dayNum G hreg i) (clientNum G hreg c)
          (clientNum G hreg c') := by
  have hi := dayNum_lt G hreg i
  have hcc := clientNum_lt G hreg c
  have hcc' := clientNum_lt G hreg c'
  have hz : clientNum G hreg (mis G hreg).c0 = 0 := rfl
  rcases eq_or_ne c (mis G hreg).c0 with rfl | hc0
  · rcases eq_or_ne c' (mis G hreg).c0 with rfl | hc0'
    · exact iff_of_true (Model.Instance.conflict_self _ _)
        (conflictAt_self _ _ _)
    · have hn0' : clientNum G hreg c' ≠ 0 :=
        fun hh => hc0' ((clientNum_eq_zero_iff G hreg c').1 hh)
      by_cases hb' : (mis G hreg).Big i c'
      · refine iff_of_false ((mis G hreg).not_conflict_c0_big hb') ?_
        rw [hz]
        exact not_conflict_zero_named G hi hcc' ((named_iff_big G hreg i c').2 hb')
      · refine iff_of_true ((mis G hreg).conflict_c0_small ⟨hc0', hb'⟩) ?_
        rw [hz]
        exact conflict_zero_parked G hi hcc' hn0'
          (fun hh => hb' ((named_iff_big G hreg i c').1 hh))
  · have hn0 : clientNum G hreg c ≠ 0 :=
      fun hh => hc0 ((clientNum_eq_zero_iff G hreg c).1 hh)
    by_cases hb : (mis G hreg).Big i c
    · have hnc : Named G (dayNum G hreg i) (clientNum G hreg c) :=
        (named_iff_big G hreg i c).2 hb
      rcases eq_or_ne c' (mis G hreg).c0 with rfl | hc0'
      · refine iff_of_false (fun h => (mis G hreg).not_conflict_c0_big hb
          (Model.Instance.conflict_symm h)) ?_
        rw [hz]
        exact fun h => not_conflict_zero_named G hi hcc hnc (conflictAt_symm h)
      · have hn0' : clientNum G hreg c' ≠ 0 :=
          fun hh => hc0' ((clientNum_eq_zero_iff G hreg c').1 hh)
        by_cases hb' : (mis G hreg).Big i c'
        · obtain ⟨hd, hp⟩ := job_shift G hreg hb
          obtain ⟨hd', hp'⟩ := job_shift G hreg hb'
          have hle := (inst G).pAt_le_dAt (dayNum G hreg i) (clientNum G hreg c)
          have hle' := (inst G).pAt_le_dAt (dayNum G hreg i) (clientNum G hreg c')
          have e1 : (mis G hreg).inst.d i c = (mis G hreg).dd i c := rfl
          have e2 : (mis G hreg).inst.p i c = (mis G hreg).pp i c := rfl
          have e3 : (mis G hreg).inst.d i c' = (mis G hreg).dd i c' := rfl
          have e4 : (mis G hreg).inst.p i c' = (mis G hreg).pp i c' := rfl
          simp only [Model.Instance.Conflict, Model.Instance.start,
            Lax117284.Scheduling.Instance.ConflictAt]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨by omega, by omega⟩
          · rintro ⟨h1, h2⟩
            exact ⟨by omega, by omega⟩
        · have hnc' : ¬ Named G (dayNum G hreg i) (clientNum G hreg c') :=
            fun hh => hb' ((named_iff_big G hreg i c').1 hh)
          refine iff_of_false (fun h => (mis G hreg).not_conflict_small_big ⟨hc0', hb'⟩ hb
            (Model.Instance.conflict_symm h)) ?_
          exact fun h => not_conflict_parked_named G hi hcc' hcc hn0' hnc' hnc
            (conflictAt_symm h)
    · have hnc : ¬ Named G (dayNum G hreg i) (clientNum G hreg c) :=
        fun hh => hb ((named_iff_big G hreg i c).1 hh)
      rcases eq_or_ne c' (mis G hreg).c0 with rfl | hc0'
      · refine iff_of_true (Model.Instance.conflict_symm
          ((mis G hreg).conflict_c0_small ⟨hc0, hb⟩)) ?_
        rw [hz]
        exact conflictAt_symm (conflict_zero_parked G hi hcc hn0 hnc)
      · have hn0' : clientNum G hreg c' ≠ 0 :=
          fun hh => hc0' ((clientNum_eq_zero_iff G hreg c').1 hh)
        by_cases hb' : (mis G hreg).Big i c'
        · have hnc' : Named G (dayNum G hreg i) (clientNum G hreg c') :=
            (named_iff_big G hreg i c').2 hb'
          exact iff_of_false ((mis G hreg).not_conflict_small_big ⟨hc0, hb⟩ hb')
            (not_conflict_parked_named G hi hcc hcc' hn0 hnc hnc')
        · have hnc' : ¬ Named G (dayNum G hreg i) (clientNum G hreg c') :=
            fun hh => hb' ((named_iff_big G hreg i c').1 hh)
          rcases eq_or_ne c c' with rfl | hne
          · exact iff_of_true (Model.Instance.conflict_self _ _)
              (conflictAt_self _ _ _)
          · have hnn : clientNum G hreg c ≠ clientNum G hreg c' :=
              fun hh => hne (clientNum_injective G hreg hh)
            exact iff_of_false
              ((mis G hreg).not_conflict_small_small ⟨hc0, hb⟩ ⟨hc0', hb'⟩ hne)
              (not_conflict_parked_parked G hi hcc hcc' hn0 hn0' hnn hnc hnc')

end Lax117284Proofs.Lemma14Match
