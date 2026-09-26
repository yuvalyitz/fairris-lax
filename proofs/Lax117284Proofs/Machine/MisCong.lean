import Lax117284Proofs.Machine.MisSem

/-!
Everything the reduction of Lemma 14 reads of its array is in the first `2 + V²` entries, and so an
array that agrees with the token values there has the same image.
-/

namespace Lax117284Proofs.Machine.MisCong

open Lax117284Proofs.Machine.MisSem
open Lax117284Proofs.Machine.MisFormat (VM)

/-- The arrays agree on the entries the reduction reads. -/
def AgrM (arr ns : List ℕ) : Prop := ∀ k < 2 + VM ns * VM ns, arr.getD k 0 = ns.getD k 0

variable {arr ns : List ℕ}

lemma lN_cong (h : AgrM arr ns) : lN arr = lN ns := h 0 (by omega)

lemma nN_cong (h : AgrM arr ns) : nN arr = nN ns := h 1 (by omega)

lemma VM_cong (h : AgrM arr ns) : VM arr = VM ns := by
  have h0 := lN_cong h
  have h1 := nN_cong h
  unfold lN at h0
  unfold nN at h1
  unfold VM
  rw [h0, h1]

lemma qualE_cong (h : AgrM arr ns) {t : ℕ} (ht : t < VM ns * VM ns) :
    qualE arr t = qualE ns t := by
  unfold qualE
  rw [VM_cong h, h (2 + t) (by omega)]

lemma edgeN_cong (h : AgrM arr ns) : edgeN arr = edgeN ns := by
  unfold edgeN
  rw [VM_cong h]
  exact List.countP_congr (fun t ht => by
    rw [qualE_cong h (List.mem_range.mp ht)])

lemma edgeCells_cong (h : AgrM arr ns) : edgeCellsN arr = edgeCellsN ns := by
  unfold edgeCellsN
  rw [VM_cong h]
  congr 1
  exact List.filter_congr (fun t ht => qualE_cong h (List.mem_range.mp ht))

lemma mat_cong (h : AgrM arr ns) {w w' : ℕ} (hw : w < VM ns) (hw' : w' < VM ns) :
    mat arr w w' = mat ns w w' := by
  unfold mat
  rw [VM_cong h]
  exact h _ (by have := cell_lt ns hw hw'; omega)

lemma rowSum_cong (h : AgrM arr ns) {w : ℕ} (hw : w < VM ns) : rowSum arr w = rowSum ns w := by
  unfold rowSum
  rw [VM_cong h]
  exact List.countP_congr (fun w' hw' => by
    rw [mat_cong h hw (List.mem_range.mp hw')])

lemma rowSum_zero_cong (h : AgrM arr ns) : rowSum arr 0 = rowSum ns 0 := by
  by_cases hv : 0 < VM ns
  · exact rowSum_cong h hv
  · have : VM ns = 0 := by omega
    unfold rowSum
    rw [VM_cong h, this]
    rfl

lemma degN_cong (h : AgrM arr ns) : degN arr = degN ns := by
  unfold degN; rw [rowSum_zero_cong h]

lemma spanN_cong (h : AgrM arr ns) : spanN arr = spanN ns := by
  unfold spanN; rw [lN_cong h, VM_cong h, degN_cong h]

lemma clN_cong (h : AgrM arr ns) : clN arr = clN ns := by
  unfold clN; rw [lN_cong h, VM_cong h, degN_cong h]

lemma daysN_cong (h : AgrM arr ns) : daysN arr = daysN ns := by
  unfold daysN; rw [lN_cong h, nN_cong h, edgeN_cong h]

lemma idxN_cong (h : AgrM arr ns) {w w' : ℕ} (hw : w' = 0 ∨ (w < VM ns ∧ w' ≤ VM ns)) :
    idxN arr w w' = idxN ns w w' := by
  unfold idxN
  rcases hw with hw | ⟨hw, hw'⟩
  · subst hw; rfl
  · exact List.countP_congr (fun x hx => by
      have hx' := List.mem_range.mp hx
      rw [mat_cong h hw (by omega)])

lemma PassM_cong (h : AgrM arr ns) {t : ℕ} (ht : t < VM ns * VM ns) :
    PassM arr t ↔ PassM ns t := by
  have hV : 0 < VM ns := by
    rcases Nat.eq_zero_or_pos (VM ns) with h0 | h0
    · rw [h0] at ht; omega
    · exact h0
  have hq : t / VM ns < VM ns := (Nat.div_lt_iff_lt_mul hV).2 ht
  have hr : t % VM ns < VM ns := Nat.mod_lt _ hV
  have hc := cell_lt ns hr hq
  unfold PassM
  rw [VM_cong h, nN_cong h, h (2 + t) (by omega), h (2 + (t % VM ns * VM ns + t / VM ns)) (by omega)]

lemma RegM_cong (h : AgrM arr ns) : RegM arr ↔ RegM ns := by
  unfold RegM
  rw [VM_cong h, rowSum_zero_cong h]
  constructor
  · rintro (h0 | ⟨h1, h2⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨h1, fun w hw => by rw [← rowSum_cong h hw, h2 w hw]⟩
  · rintro (h0 | ⟨h1, h2⟩)
    · exact Or.inl h0
    · exact Or.inr ⟨h1, fun w hw => by rw [rowSum_cong h hw, h2 w hw]⟩

/-- **The check reads only the entries it should.** -/
lemma CondM_cong (h : AgrM arr ns) : CondM arr ↔ CondM ns := by
  unfold CondM
  rw [nN_cong h, VM_cong h, edgeN_cong h, RegM_cong h]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun t ht => (PassM_cong h ht).1 (h2 t ht), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun t ht => (PassM_cong h ht).2 (h2 t ht), h3, h4⟩

lemma edgeCells_getD_lt (ns : List ℕ) (j : ℕ) :
    ((edgeCellsN ns).getD j (0, 0)).1 = 0 ∧ ((edgeCellsN ns).getD j (0, 0)).2 = 0 ∨
    ((edgeCellsN ns).getD j (0, 0)).1 < VM ns ∧ ((edgeCellsN ns).getD j (0, 0)).2 < VM ns := by
  by_cases hj : j < (edgeCellsN ns).length
  · right
    have hm := List.getElem_mem hj
    rw [← List.getD_eq_getElem _ (0, 0) hj] at hm
    generalize (edgeCellsN ns).getD j (0, 0) = q at hm ⊢
    unfold edgeCellsN at hm
    obtain ⟨t, ht, e⟩ := List.mem_map.mp hm
    have ht' := List.mem_range.mp (List.mem_filter.mp ht).1
    have hV : 0 < VM ns := by
      rcases Nat.eq_zero_or_pos (VM ns) with h0 | h0
      · rw [h0] at ht'; omega
      · exact h0
    rw [← e]
    exact ⟨(Nat.div_lt_iff_lt_mul hV).2 ht', Nat.mod_lt _ hV⟩
  · left
    rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨rfl, rfl⟩

lemma edgeDayN_cong (h : AgrM arr ns) {w w' : ℕ}
    (hw : (w = 0 ∧ w' = 0) ∨ (w < VM ns ∧ w' < VM ns)) (c : ℕ) :
    edgeDayN arr w w' c = edgeDayN ns w w' c := by
  have e1 : idxN arr w w' = idxN ns w w' := idxN_cong h (by omega)
  have e2 : idxN arr w' w = idxN ns w' w := idxN_cong h (by omega)
  unfold edgeDayN incIdN
  rw [e1, e2, lN_cong h, VM_cong h, degN_cong h, spanN_cong h]

lemma jobN_cong (h : AgrM arr ns) (i c : ℕ) : jobN arr i c = jobN ns i c := by
  unfold jobN
  simp only [lN_cong h, nN_cong h, edgeCells_cong h]
  split_ifs with h1 h2
  · unfold vertexDayN
    simp only [lN_cong h, nN_cong h, degN_cong h, spanN_cong h]
  · unfold validationDayN
    simp only [lN_cong h, nN_cong h, degN_cong h, spanN_cong h, VM_cong h]
  · exact edgeDayN_cong h (by
      rcases edgeCells_getD_lt ns (i - lN ns * (nN ns + 1)) with ⟨a, b⟩ | ⟨a, b⟩
      · exact Or.inl ⟨a, b⟩
      · exact Or.inr ⟨a, b⟩) c

lemma kvN_cong (h : AgrM arr ns) (c : ℕ) : kvN arr c = kvN ns c := by
  unfold kvN; rw [daysN_cong h, edgeN_cong h]

/-- **The image only depends on the entries the reduction reads.** -/
lemma outM_cong (h : AgrM arr ns) : outM arr = outM ns := by
  have hk : kvN arr = kvN ns := funext (kvN_cong h)
  unfold outM
  rw [clN_cong h, daysN_cong h, hk]
  simp only [jobN_cong h]

end Lax117284Proofs.Machine.MisCong
