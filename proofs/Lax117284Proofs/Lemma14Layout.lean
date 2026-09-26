import Lax117284.Lemma14

/-!
The layout of Lemma 14's construction: which of the three kinds a day is, which clients take
part in its gadget, and where the dummy client's job begins. Everything the correctness
argument uses about the jobs of the clients that do *not* take part is collected here: the
dummy client covers a stretch beginning at the end of the day's gadget, and every other such
client occupies one unit of that stretch, its own.
-/

namespace Lax117284Proofs.Lemma14Layout

open Lax117284.MulticolouredIndepSet Lax117284.Lemma14

variable (G : Instance)

/-! ### The three kinds of day -/

/-- The colour whose block day `i` belongs to. -/
def dayColour (i : ℕ) : ℕ := i / (G.size + 1)

/-- The vertex whose vertex day `i` is. -/
def dayVertex (i : ℕ) : ℕ := (i / (G.size + 1)) * G.size + i % (G.size + 1)

/-- The edge whose edge day `i` is. -/
noncomputable def dayEdge (i : ℕ) : ℕ × ℕ :=
  G.edgeList.getD (i - G.colours * (G.size + 1)) (0, 0)

/-- Day `i` is the vertex day of a vertex. -/
def IsVertexDay (i : ℕ) : Prop :=
  i < G.colours * (G.size + 1) ∧ i % (G.size + 1) < G.size

/-- Day `i` is the validation day of a colour. -/
def IsValidationDay (i : ℕ) : Prop :=
  i < G.colours * (G.size + 1) ∧ ¬ i % (G.size + 1) < G.size

/-- Day `i` is the edge day of an edge. -/
def IsEdgeDay (i : ℕ) : Prop := ¬ i < G.colours * (G.size + 1)

instance (i : ℕ) : Decidable (IsVertexDay G i) := by unfold IsVertexDay; infer_instance

instance (i : ℕ) : Decidable (IsValidationDay G i) := by
  unfold IsValidationDay; infer_instance

instance (i : ℕ) : Decidable (IsEdgeDay G i) := by unfold IsEdgeDay; infer_instance

theorem day_trichotomy (i : ℕ) :
    IsVertexDay G i ∨ IsValidationDay G i ∨ IsEdgeDay G i := by
  unfold IsVertexDay IsValidationDay IsEdgeDay
  by_cases h : i < G.colours * (G.size + 1)
  · by_cases h' : i % (G.size + 1) < G.size
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr (Or.inl ⟨h, h'⟩)
  · exact Or.inr (Or.inr h)

theorem job_of_vertexDay {i : ℕ} (h : IsVertexDay G i) (c : ℕ) :
    job G i c = vertexDay G (dayVertex G i) c := by
  simp [job, dayVertex, IsVertexDay] at h ⊢
  simp [h.1, h.2]

theorem job_of_validationDay {i : ℕ} (h : IsValidationDay G i) (c : ℕ) :
    job G i c = validationDay G (dayColour G i) c := by
  simp only [IsValidationDay] at h
  simp [job, dayColour, h.1, h.2]

theorem job_of_edgeDay {i : ℕ} (h : IsEdgeDay G i) (c : ℕ) :
    job G i c = edgeDay G (dayEdge G i).1 (dayEdge G i).2 c := by
  simp only [IsEdgeDay] at h
  simp [job, dayEdge, h]

/-! ### The clients taking part in a day's gadget -/

/-- Client `c` takes part in day `i`'s gadget. -/
noncomputable def Named (i c : ℕ) : Prop :=
  if IsVertexDay G i then
    c = vtxId G (dayVertex G i) ∨ c = selId (G.classOf (dayVertex G i))
  else if IsValidationDay G i then
    (3 + G.colours ≤ c ∧ c < 3 + G.colours + G.vertices ∧
        G.classOf (c - (3 + G.colours)) = dayColour G i) ∨
      (3 + G.colours + G.vertices ≤ c ∧
        G.classOf ((c - (3 + G.colours + G.vertices)) / deg G) = dayColour G i)
  else
    c = 1 ∨ c = 2 ∨
      c = incId G (dayEdge G i).1 ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2) ∨
      c = incId G (dayEdge G i).2 ((G.nbrs (dayEdge G i).2).idxOf (dayEdge G i).1)

/-- The time at which day `i`'s gadget ends and the dummy client's job begins. -/
noncomputable def base (i : ℕ) : ℕ :=
  if IsVertexDay G i then deg G
  else if IsValidationDay G i then deg G * G.size
  else 3

/-! ### The dummy client, and the clients its job blocks -/

theorem job_zero (i : ℕ) : job G i 0 = (span G, base G i + span G) := by
  rcases day_trichotomy G i with h | h | h
  · rw [job_of_vertexDay G h]
    simp only [base, if_pos h]
    simp [vertexDay]
  · have hv : ¬ IsVertexDay G i := fun hc => h.2 hc.2
    rw [job_of_validationDay G h]
    simp only [base, if_neg hv, if_pos h]
    simp [validationDay]
  · have hv : ¬ IsVertexDay G i := fun hc => h hc.1
    have hw : ¬ IsValidationDay G i := fun hc => h hc.1
    rw [job_of_edgeDay G h]
    simp only [base, if_neg hv, if_neg hw]
    simp [edgeDay]

theorem job_parked {i c : ℕ} (hc : c ≠ 0) (h : ¬ Named G i c) :
    job G i c = (1, base G i + c) := by
  rcases day_trichotomy G i with hd | hd | hd
  · rw [job_of_vertexDay G hd]
    simp only [Named, if_pos hd] at h
    simp only [base, if_pos hd]
    simp [vertexDay, hc, h]
  · have hv : ¬ IsVertexDay G i := fun hcc => hd.2 hcc.2
    rw [job_of_validationDay G hd]
    simp only [Named, if_neg hv, if_pos hd] at h
    push_neg at h
    simp only [base, if_neg hv, if_pos hd]
    simp only [validationDay]
    rw [if_neg hc, if_neg (by tauto), if_neg (by tauto)]
  · have hv : ¬ IsVertexDay G i := fun hcc => hd hcc.1
    have hw : ¬ IsValidationDay G i := fun hcc => hd hcc.1
    rw [job_of_edgeDay G hd]
    simp only [Named, if_neg hv, if_neg hw] at h
    push_neg at h
    simp only [base, if_neg hv, if_neg hw]
    simp only [edgeDay]
    rw [if_neg hc, if_neg (by tauto), if_neg (by tauto), if_neg (by tauto),
      if_neg (by tauto)]


/-! ### The jobs of an instance, read off the layout -/

theorem pAt_eq {i c : ℕ} (hi : i < dayCount G) (hc : c < clientCount G) :
    (inst G).pAt i c = (job G i c).1 := by
  simp [Lax117284.Scheduling.Instance.pAt, inst, hi, hc]

theorem dAt_eq {i c : ℕ} (hi : i < dayCount G) (hc : c < clientCount G) :
    (inst G).dAt i c = (job G i c).2 := by
  simp [Lax117284.Scheduling.Instance.dAt, inst, hi, hc]

theorem le_span {c : ℕ} (hc : c < clientCount G) : c ≤ span G := by
  have h : clientCount G = span G + 1 := by
    simp only [clientCount, span]
    omega
  omega

/-- A client taking part in a day's gadget is not the dummy client. -/
theorem named_ne_zero {i c : ℕ} (h : Named G i c) : c ≠ 0 := by
  rcases day_trichotomy G i with hd | hd | hd
  · simp only [Named, if_pos hd] at h
    rcases h with h | h <;> simp only [vtxId, selId] at h <;> omega
  · have hv : ¬ IsVertexDay G i := fun hcc => hd.2 hcc.2
    simp only [Named, if_neg hv, if_pos hd] at h
    rcases h with ⟨h, -, -⟩ | ⟨h, -⟩ <;> omega
  · have hv : ¬ IsVertexDay G i := fun hcc => hd hcc.1
    have hw : ¬ IsValidationDay G i := fun hcc => hd hcc.1
    simp only [Named, if_neg hv, if_neg hw] at h
    rcases h with h | h | h | h <;> first
      | omega
      | (simp only [incId] at h; omega)

/-- The job of a client taking part in a day's gadget ends by the end of the gadget. -/
theorem due_le_base {i c : ℕ} (hc : c < clientCount G) (h : Named G i c) :
    (job G i c).2 ≤ base G i := by
  have hdeg : 1 ≤ deg G := le_max_left 1 _
  have hne := named_ne_zero G h
  rcases day_trichotomy G i with hd | hd | hd
  · rw [job_of_vertexDay G hd]
    simp only [Named, if_pos hd] at h
    simp only [base, if_pos hd, vertexDay]
    rw [if_neg hne, if_pos h]
  · have hv : ¬ IsVertexDay G i := fun hcc => hd.2 hcc.2
    have hsize : 0 < G.size := by
      rcases Nat.eq_zero_or_pos G.size with h0 | h0
      · exfalso
        have hv0 : G.vertices = G.colours * G.size := rfl
        have hcc : clientCount G
            = 3 + G.colours + G.vertices + G.vertices * deg G := rfl
        rw [h0, Nat.mul_zero] at hv0
        rw [hv0, Nat.zero_mul] at hcc
        simp only [Named, if_neg hv, if_pos hd] at h
        rcases h with ⟨h1, h2, -⟩ | ⟨h1, -⟩ <;> omega
      · exact h0
    rw [job_of_validationDay G hd]
    simp only [Named, if_neg hv, if_pos hd] at h
    simp only [base, if_neg hv, if_pos hd, validationDay]
    rw [if_neg hne]
    rcases h with h | h
    · rw [if_pos h]
      have hmod : G.indexOf (c - (3 + G.colours)) < G.size := Nat.mod_lt _ hsize
      have := Nat.mul_le_mul_left (deg G)
        (show G.indexOf (c - (3 + G.colours)) + 1 ≤ G.size by omega)
      have hexp : deg G * (G.indexOf (c - (3 + G.colours)) + 1)
          = deg G * G.indexOf (c - (3 + G.colours)) + deg G := by ring
      omega
    · rw [if_neg (by rintro ⟨-, h2, -⟩; omega), if_pos h]
      have hmod : G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G) < G.size :=
        Nat.mod_lt _ hsize
      have hq : (c - (3 + G.colours + G.vertices)) % deg G < deg G := Nat.mod_lt _ hdeg
      have := Nat.mul_le_mul_left (deg G)
        (show G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G) + 1 ≤ G.size by omega)
      have hexp : deg G * (G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G) + 1)
          = deg G * G.indexOf ((c - (3 + G.colours + G.vertices)) / deg G) + deg G := by
        ring
      omega
  · have hv : ¬ IsVertexDay G i := fun hcc => hd hcc.1
    have hw : ¬ IsValidationDay G i := fun hcc => hd hcc.1
    rw [job_of_edgeDay G hd]
    simp only [Named, if_neg hv, if_neg hw] at h
    simp only [base, if_neg hv, if_neg hw, edgeDay]
    rw [if_neg hne]
    rcases h with h | h | h | h
    · rw [if_neg (by omega), if_pos h]
    · rw [if_pos h]
      omega
    · have h3 : 3 ≤ c := by simp only [incId] at h; omega
      rw [if_neg (by omega), if_neg (by omega), if_pos h]
    · have h3 : 3 ≤ c := by simp only [incId] at h; omega
      rw [if_neg (by omega), if_neg (by omega)]
      by_cases he : c = incId G (dayEdge G i).1
          ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2)
      · rw [if_pos he]
      · rw [if_neg he, if_pos h]
        omega

/-! ### What the dummy client blocks, and what it does not

These four facts are everything the correctness argument uses about the clients that do not
take part in a day's gadget, and they are what the repair of the source's construction
buys: the dummy client blocks each of them, and they block neither each other nor the
gadget. -/

/-- **The dummy client blocks every client not taking part in the gadget.** -/
theorem conflict_zero_parked {i c : ℕ} (hi : i < dayCount G) (hc : c < clientCount G)
    (hne : c ≠ 0) (h : ¬ Named G i c) : (inst G).ConflictAt i 0 c := by
  have h0 : (0 : ℕ) < clientCount G := by simp only [clientCount]; omega
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi h0, dAt_eq G hi h0,
    pAt_eq G hi hc, dAt_eq G hi hc, job_zero G i, job_parked G hne h]
  have := le_span G hc
  omega

/-- **The dummy client does not block a client taking part in the gadget.** -/
theorem not_conflict_zero_named {i c : ℕ} (hi : i < dayCount G) (hc : c < clientCount G)
    (h : Named G i c) : ¬ (inst G).ConflictAt i 0 c := by
  have h0 : (0 : ℕ) < clientCount G := by simp only [clientCount]; omega
  have hdue := due_le_base G hc h
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi h0, dAt_eq G hi h0,
    pAt_eq G hi hc, dAt_eq G hi hc, job_zero G i]
  omega

/-- **Two clients not taking part in the gadget do not block each other.** -/
theorem not_conflict_parked_parked {i c c' : ℕ} (hi : i < dayCount G)
    (hc : c < clientCount G) (hc' : c' < clientCount G) (hne : c ≠ 0) (hne' : c' ≠ 0)
    (hcc : c ≠ c') (h : ¬ Named G i c) (h' : ¬ Named G i c') :
    ¬ (inst G).ConflictAt i c c' := by
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi hc, dAt_eq G hi hc,
    pAt_eq G hi hc', dAt_eq G hi hc', job_parked G hne h, job_parked G hne' h']
  omega

/-- **A client not taking part in the gadget does not block one that does.** -/
theorem not_conflict_parked_named {i c c' : ℕ} (hi : i < dayCount G)
    (hc : c < clientCount G) (hc' : c' < clientCount G) (hne : c ≠ 0)
    (h : ¬ Named G i c) (h' : Named G i c') : ¬ (inst G).ConflictAt i c c' := by
  have hdue := due_le_base G hc' h'
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi hc, dAt_eq G hi hc,
    pAt_eq G hi hc', dAt_eq G hi hc', job_parked G hne h]
  omega

/-! ### Where the numbers of the clients and of the vertices lie -/

theorem one_le_deg' : 1 ≤ deg G := le_max_left 1 _

theorem vtxId_lt {w : ℕ} (hw : w < G.vertices) : vtxId G w < clientCount G := by
  simp only [vtxId, clientCount]; omega

theorem incId_lt {w q : ℕ} (hw : w < G.vertices) (hq : q < deg G) :
    incId G w q < clientCount G := by
  have h : w * deg G + deg G ≤ G.vertices * deg G :=
    le_trans (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hw) (le_refl _)
  simp only [incId, clientCount]
  omega

/-- Two vertex numbers with the same class and the same index inside it are the same. -/
theorem vertex_ext {w w' : ℕ} (hc : G.classOf w = G.classOf w')
    (hi : G.indexOf w = G.indexOf w') : w = w' := by
  have h1 := Nat.div_add_mod w G.size
  have h2 := Nat.div_add_mod w' G.size
  simp only [Instance.classOf, Instance.indexOf] at hc hi
  rw [← hc, ← hi] at h2
  exact h1.symm.trans h2

/-- Blocks of `r` consecutive units indexed by the vertices of a class do not overlap. -/
theorem block_le {a b : ℕ} (h : a < b) : deg G * a + deg G ≤ deg G * b := by
  have h1 := Nat.mul_le_mul_left (deg G) (show a + 1 ≤ b from h)
  have h2 : deg G * (a + 1) = deg G * a + deg G := by ring
  omega

theorem dayColour_lt {i : ℕ} (h : i < G.colours * (G.size + 1)) :
    dayColour G i < G.colours :=
  (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).2 h

theorem dayVertex_lt {i : ℕ} (h : IsVertexDay G i) : dayVertex G i < G.vertices := by
  have hc := dayColour_lt G h.1
  have h1 : (dayColour G i + 1) * G.size ≤ G.colours * G.size :=
    Nat.mul_le_mul_right _ hc
  have h2 : (dayColour G i + 1) * G.size = dayColour G i * G.size + G.size := by ring
  have h3 : dayVertex G i = dayColour G i * G.size + i % (G.size + 1) := rfl
  have h4 : G.vertices = G.colours * G.size := rfl
  have h5 := h.2
  omega

/-! ### The gadget of a vertex day

The vertex client of the day's vertex and the selection client of its colour have the same
job, so they conflict; they are the only clients taking part. -/

theorem job_vertexDay_vtx {i : ℕ} (h : IsVertexDay G i) :
    job G i (vtxId G (dayVertex G i)) = (deg G, deg G) := by
  rw [job_of_vertexDay G h]
  unfold vertexDay
  rw [if_neg (show vtxId G (dayVertex G i) ≠ 0 by simp only [vtxId]; omega),
    if_pos (Or.inl rfl)]

theorem job_vertexDay_sel {i : ℕ} (h : IsVertexDay G i) :
    job G i (selId (G.classOf (dayVertex G i))) = (deg G, deg G) := by
  rw [job_of_vertexDay G h]
  unfold vertexDay
  rw [if_neg (show selId (G.classOf (dayVertex G i)) ≠ 0 by simp only [selId]; omega),
    if_pos (Or.inr rfl)]

/-! ### The gadget of a validation day

The vertex clients of the day's colour occupy consecutive blocks of `r` units, one per
index inside the class, and the incidence clients of a vertex occupy the units of its own
block. So a vertex client conflicts with exactly its own incidence clients. -/

theorem job_validationDay_vtx {i : ℕ} (h : IsValidationDay G i) {w : ℕ}
    (hw : w < G.vertices) (hc : G.classOf w = dayColour G i) :
    job G i (vtxId G w) = (deg G, deg G * (G.indexOf w + 1)) := by
  have hsub : vtxId G w - (3 + G.colours) = w := by simp only [vtxId]; omega
  rw [job_of_validationDay G h]
  unfold validationDay
  rw [if_neg (show vtxId G w ≠ 0 by simp only [vtxId]; omega),
    if_pos (⟨by simp only [vtxId]; omega, by simp only [vtxId]; omega, by rw [hsub]; exact hc⟩ :
      3 + G.colours ≤ vtxId G w ∧ vtxId G w < 3 + G.colours + G.vertices ∧
        G.classOf (vtxId G w - (3 + G.colours)) = dayColour G i),
    hsub]

theorem job_validationDay_inc {i : ℕ} (h : IsValidationDay G i) {w q : ℕ}
    (hw : w < G.vertices) (hq : q < deg G) (hc : G.classOf w = dayColour G i) :
    job G i (incId G w q) = (1, deg G * G.indexOf w + q + 1) := by
  have hdeg := one_le_deg' G
  have hsub : incId G w q - (3 + G.colours + G.vertices) = w * deg G + q := by
    simp only [incId]; omega
  have hdiv : (w * deg G + q) / deg G = w := by
    rw [Nat.mul_comm, Nat.mul_add_div hdeg, Nat.div_eq_of_lt hq, Nat.add_zero]
  have hmod : (w * deg G + q) % deg G = q := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hq]
  rw [job_of_validationDay G h]
  unfold validationDay
  rw [if_neg (show incId G w q ≠ 0 by simp only [incId]; omega),
    if_neg (by rintro ⟨-, h2, -⟩; simp only [incId] at h2; omega),
    if_pos (⟨by simp only [incId]; omega, by rw [hsub, hdiv]; exact hc⟩ :
      3 + G.colours + G.vertices ≤ incId G w q ∧
        G.classOf ((incId G w q - (3 + G.colours + G.vertices)) / deg G) = dayColour G i),
    hsub, hdiv, hmod]

section Validation

variable {G}
variable {i w w' q q' : ℕ}

/-- …and nothing else on that day. -/
theorem not_conflict_validationDay_vtx_inc (hi : i < dayCount G) (h : IsValidationDay G i)
    (hw : w < G.vertices) (hw' : w' < G.vertices) (hq : q < deg G)
    (hc : G.classOf w = dayColour G i) (hc' : G.classOf w' = dayColour G i)
    (hne : w ≠ w') : ¬ (inst G).ConflictAt i (vtxId G w) (incId G w' q) := by
  have hdeg := one_le_deg' G
  have hv := vtxId_lt G hw
  have hx := incId_lt G hw' hq
  have hidx : G.indexOf w ≠ G.indexOf w' := fun hh => hne (vertex_ext G (hc.trans hc'.symm) hh)
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi hv, dAt_eq G hi hv,
    pAt_eq G hi hx, dAt_eq G hi hx, job_validationDay_vtx G h hw hc,
    job_validationDay_inc G h hw' hq hc']
  have he : deg G * (G.indexOf w + 1) = deg G * G.indexOf w + deg G := by ring
  rcases Nat.lt_or_ge (G.indexOf w) (G.indexOf w') with hlt | hge
  · have := block_le G hlt
    omega
  · have hlt' : G.indexOf w' < G.indexOf w := by omega
    have := block_le G hlt'
    omega

/-- Two vertex clients of the day's colour occupy disjoint blocks. -/
theorem not_conflict_validationDay_vtx_vtx (hi : i < dayCount G) (h : IsValidationDay G i)
    (hw : w < G.vertices) (hw' : w' < G.vertices)
    (hc : G.classOf w = dayColour G i) (hc' : G.classOf w' = dayColour G i)
    (hne : w ≠ w') : ¬ (inst G).ConflictAt i (vtxId G w) (vtxId G w') := by
  have hdeg := one_le_deg' G
  have hv := vtxId_lt G hw
  have hv' := vtxId_lt G hw'
  have hidx : G.indexOf w ≠ G.indexOf w' := fun hh => hne (vertex_ext G (hc.trans hc'.symm) hh)
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi hv, dAt_eq G hi hv,
    pAt_eq G hi hv', dAt_eq G hi hv', job_validationDay_vtx G h hw hc,
    job_validationDay_vtx G h hw' hc']
  have he : deg G * (G.indexOf w + 1) = deg G * G.indexOf w + deg G := by ring
  have he' : deg G * (G.indexOf w' + 1) = deg G * G.indexOf w' + deg G := by ring
  rcases Nat.lt_or_ge (G.indexOf w) (G.indexOf w') with hlt | hge
  · have := block_le G hlt
    omega
  · have hlt' : G.indexOf w' < G.indexOf w := by omega
    have := block_le G hlt'
    omega

/-- Two incidence clients of the day's colour occupy different unit slots. -/
theorem not_conflict_validationDay_inc_inc (hi : i < dayCount G) (h : IsValidationDay G i)
    (hw : w < G.vertices) (hw' : w' < G.vertices) (hq : q < deg G) (hq' : q' < deg G)
    (hc : G.classOf w = dayColour G i) (hc' : G.classOf w' = dayColour G i)
    (hne : incId G w q ≠ incId G w' q') :
    ¬ (inst G).ConflictAt i (incId G w q) (incId G w' q') := by
  have hdeg := one_le_deg' G
  have hx := incId_lt G hw hq
  have hx' := incId_lt G hw' hq'
  have hslot : deg G * G.indexOf w + q ≠ deg G * G.indexOf w' + q' := by
    intro hh
    refine hne ?_
    rcases Nat.lt_trichotomy (G.indexOf w) (G.indexOf w') with hlt | heq | hgt
    · have := block_le G hlt; omega
    · have hww : w = w' := vertex_ext G (hc.trans hc'.symm) heq
      have : q = q' := by rw [heq] at hh; omega
      rw [hww, this]
    · have := block_le G hgt; omega
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi hx, dAt_eq G hi hx,
    pAt_eq G hi hx', dAt_eq G hi hx', job_validationDay_inc G h hw hq hc,
    job_validationDay_inc G h hw' hq' hc']
  omega

end Validation

/-! ### The gadget of an edge day

The two interaction clients and the edge's two incidence clients occupy the intervals
`(0,2]`, `(1,3]`, `(2,3]` and `(0,1]`: the conflict graph of the day is the path
`c_{u,v} — c⁻ — c⁺ — c_{v,u}`. -/

/-- The tail client of the day's edge. -/
noncomputable def edgeTail (i : ℕ) : ℕ :=
  incId G (dayEdge G i).1 ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2)

/-- The head client of the day's edge. -/
noncomputable def edgeHead (i : ℕ) : ℕ :=
  incId G (dayEdge G i).2 ((G.nbrs (dayEdge G i).2).idxOf (dayEdge G i).1)

theorem job_edgeDay_plus {i : ℕ} (h : IsEdgeDay G i) : job G i 1 = (2, 3) := by
  rw [job_of_edgeDay G h]
  unfold edgeDay
  rw [if_neg (by omega : (1 : ℕ) ≠ 0), if_neg (by omega : (1 : ℕ) ≠ 2), if_pos rfl]

theorem job_edgeDay_minus {i : ℕ} (h : IsEdgeDay G i) : job G i 2 = (2, 2) := by
  rw [job_of_edgeDay G h]
  unfold edgeDay
  rw [if_neg (by omega : (2 : ℕ) ≠ 0), if_pos rfl]

theorem job_edgeDay_tail {i : ℕ} (h : IsEdgeDay G i) : job G i (edgeTail G i) = (1, 3) := by
  rw [job_of_edgeDay G h]
  show edgeDay G _ _ (incId G _ _) = _
  unfold edgeDay
  rw [if_neg (show incId G (dayEdge G i).1 ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2)
        ≠ 0 by simp only [incId]; omega),
    if_neg (show incId G (dayEdge G i).1 ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2)
        ≠ 2 by simp only [incId]; omega),
    if_neg (show incId G (dayEdge G i).1 ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2)
        ≠ 1 by simp only [incId]; omega),
    if_pos rfl]

theorem job_edgeDay_head {i : ℕ} (h : IsEdgeDay G i) (hne : edgeHead G i ≠ edgeTail G i) :
    job G i (edgeHead G i) = (1, 1) := by
  rw [job_of_edgeDay G h]
  show edgeDay G _ _ (edgeHead G i) = _
  unfold edgeDay
  rw [if_neg (show edgeHead G i ≠ 0 by simp only [edgeHead, incId]; omega),
    if_neg (show edgeHead G i ≠ 2 by simp only [edgeHead, incId]; omega),
    if_neg (show edgeHead G i ≠ 1 by simp only [edgeHead, incId]; omega),
    if_neg (show edgeHead G i ≠ incId G (dayEdge G i).1
        ((G.nbrs (dayEdge G i).1).idxOf (dayEdge G i).2) from hne),
    if_pos (show edgeHead G i = incId G (dayEdge G i).2
        ((G.nbrs (dayEdge G i).2).idxOf (dayEdge G i).1) from rfl)]

section Edge

variable {G}
variable {i : ℕ}

/-- The edge's two incidence clients do not conflict. -/
theorem not_conflict_edgeDay_tail_head (hi : i < dayCount G) (h : IsEdgeDay G i)
    (ht : edgeTail G i < clientCount G) (hh : edgeHead G i < clientCount G)
    (hne : edgeHead G i ≠ edgeTail G i) :
    ¬ (inst G).ConflictAt i (edgeTail G i) (edgeHead G i) := by
  simp only [Lax117284.Scheduling.Instance.ConflictAt, pAt_eq G hi ht, dAt_eq G hi ht,
    pAt_eq G hi hh, dAt_eq G hi hh, job_edgeDay_tail G h, job_edgeDay_head G h hne]
  omega

end Edge

/-! ### Who takes part, read off the day's kind -/

theorem named_vertexDay {i : ℕ} (h : IsVertexDay G i) (c : ℕ) :
    Named G i c ↔ (c = vtxId G (dayVertex G i) ∨ c = selId (G.classOf (dayVertex G i))) := by
  simp only [Named, if_pos h]

theorem named_validationDay {i : ℕ} (h : IsValidationDay G i) (c : ℕ) :
    Named G i c ↔
      ((3 + G.colours ≤ c ∧ c < 3 + G.colours + G.vertices ∧
          G.classOf (c - (3 + G.colours)) = dayColour G i) ∨
        (3 + G.colours + G.vertices ≤ c ∧
          G.classOf ((c - (3 + G.colours + G.vertices)) / deg G) = dayColour G i)) := by
  have hv : ¬ IsVertexDay G i := fun hc => h.2 hc.2
  simp only [Named, if_neg hv, if_pos h]

theorem named_edgeDay {i : ℕ} (h : IsEdgeDay G i) (c : ℕ) :
    Named G i c ↔
      (c = 1 ∨ c = 2 ∨ c = edgeTail G i ∨ c = edgeHead G i) := by
  have hv : ¬ IsVertexDay G i := fun hc => h hc.1
  have hw : ¬ IsValidationDay G i := fun hc => h hc.1
  simp only [Named, if_neg hv, if_neg hw, edgeTail, edgeHead]

/-! ### Conflict, on the numbered side -/

theorem conflictAt_symm {I : Lax117284.Scheduling.Instance} {i j j' : ℕ}
    (h : I.ConflictAt i j j') : I.ConflictAt i j' j := ⟨h.2, h.1⟩

theorem conflictAt_self (I : Lax117284.Scheduling.Instance) (i j : ℕ) :
    I.ConflictAt i j j := by
  have hp := I.pAt_pos i j
  have hd := I.pAt_le_dAt i j
  exact ⟨by omega, by omega⟩

end Lax117284Proofs.Lemma14Layout
