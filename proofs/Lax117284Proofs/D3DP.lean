import Lax117284Proofs.MathlibLite

/-!
The dynamic program for day-independent due dates, on numbers: the state is, for every day, the
position in the order of the last client served on it, or zero; a client is served on `k` days, one
day at a time.
-/

namespace Lax117284Proofs.D3DP

variable (m k : ℕ) (q : ℕ → ℕ → ℕ) (e : ℕ → ℕ)

/-- The time a day is free from, given the position of the last client served on it. -/
def fv (δ : ℕ) : ℕ := if δ = 0 then 0 else e (δ - 1)

/-- A state: for every day, the position of the last client served on it, or zero. -/
abbrev Vec := Fin m → ℕ

/-- The client at position `c` can be served on day `i` from the state `v`. -/
def feas (c : ℕ) (v : Vec m) (i : Fin m) : Prop := q i c + fv e (v i) ≤ e c

/-- The state after the client at position `c` is served on the days of `S`. -/
def stepV (c : ℕ) (S : Finset (Fin m)) (v : Vec m) : Vec m := fun i => if i ∈ S then c + 1 else v i

/-- The states reachable after the first `c` clients. -/
def Reach : ℕ → Set (Vec m)
  | 0 => {fun _ => 0}
  | c + 1 => {v' | ∃ v ∈ Reach c, ∃ S : Finset (Fin m), S.card = k ∧
      (∀ i ∈ S, feas m q e c v i) ∧ v' = stepV m c S v}

/-- The states, with the number of days served so far, after the days below `i` of the client at
position `c` have been decided. -/
def Lay (c : ℕ) : ℕ → Set (Vec m × ℕ)
  | 0 => {p | p.1 ∈ Reach m k q e c ∧ p.2 = 0}
  | i + 1 => {p | ∃ p0 ∈ Lay c i, p = p0 ∨ ∃ h : i < m, p0.2 < k ∧ feas m q e c p0.1 ⟨i, h⟩ ∧
      p = (Function.update p0.1 ⟨i, h⟩ (c + 1), p0.2 + 1)}

/-- **The layers are the choices of the days.** -/
theorem lay_iff (c : ℕ) : ∀ i, i ≤ m → ∀ (v' : Vec m) (t : ℕ),
    (v', t) ∈ Lay m k q e c i ↔ ∃ v ∈ Reach m k q e c, ∃ S : Finset (Fin m),
      (∀ x ∈ S, x.val < i) ∧ S.card = t ∧ t ≤ k ∧ (∀ x ∈ S, feas m q e c v x) ∧
        v' = stepV m c S v
  | 0, _, v', t => by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨v', h1, ∅, by simp, by simpa using h2.symm, by omega, by simp, ?_⟩
      funext x; simp [stepV]
    · rintro ⟨v, hv, S, hS, hc, -, -, rfl⟩
      have : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx; exact absurd (hS x hx) (by omega)
      subst this
      refine ⟨?_, by simpa using hc.symm⟩
      have : stepV m c ∅ v = v := by funext x; simp [stepV]
      rw [this]; exact hv
  | i + 1, hi, v', t => by
    have ih := lay_iff c i (by omega)
    constructor
    · rintro ⟨⟨v0, t0⟩, h0, h⟩
      rcases h with h | ⟨hh, hlt, hf, h⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨v, hv, S, hS, hc, hk, hfs, rfl⟩ := (ih _ _).1 h0
        exact ⟨v, hv, S, fun x hx => by have := hS x hx; omega, hc, hk, hfs, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨v, hv, S, hS, hc, hk, hfs, rfl⟩ := (ih _ _).1 h0
        have hnot : (⟨i, hh⟩ : Fin m) ∉ S := fun hx => by have := hS _ hx; simp at this
        refine ⟨v, hv, insert ⟨i, hh⟩ S, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · simp
          · have := hS x hx; omega
        · rw [Finset.card_insert_of_notMem hnot, hc]
        · simp at hlt; omega
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · have : stepV m c S v ⟨i, hh⟩ = v ⟨i, hh⟩ := by simp [stepV, hnot]
            simpa [feas, this] using hf
          · exact hfs x hx
        · funext x
          by_cases hx : x = ⟨i, hh⟩
          · subst hx; simp [stepV]
          · simp [stepV, Function.update, hx]
    · rintro ⟨v, hv, S, hS, hc, hk, hfs, rfl⟩
      by_cases hmem : ∃ hh : i < m, (⟨i, hh⟩ : Fin m) ∈ S
      · obtain ⟨hh, hx⟩ := hmem
        have hS0 : ∀ x ∈ S.erase ⟨i, hh⟩, x.val < i := by
          intro x hx'
          have hne : x ≠ ⟨i, hh⟩ := Finset.ne_of_mem_erase hx'
          have := hS x (Finset.mem_of_mem_erase hx')
          have : x.val ≠ i := fun h => hne (Fin.ext h)
          omega
        have hcard : (S.erase ⟨i, hh⟩).card + 1 = S.card := Finset.card_erase_add_one hx
        refine ⟨(stepV m c (S.erase ⟨i, hh⟩) v, S.card - 1), ?_, Or.inr ⟨hh, ?_, ?_, ?_⟩⟩
        · exact (ih _ _).2 ⟨v, hv, S.erase ⟨i, hh⟩, hS0, by omega, by omega,
            fun x hx' => hfs x (Finset.mem_of_mem_erase hx'), rfl⟩
        · have : 0 < S.card := Finset.card_pos.2 ⟨_, hx⟩
          show S.card - 1 < k
          omega
        · have hnot : (⟨i, hh⟩ : Fin m) ∉ S.erase ⟨i, hh⟩ := by simp
          have : stepV m c (S.erase ⟨i, hh⟩) v ⟨i, hh⟩ = v ⟨i, hh⟩ := by simp [stepV]
          simpa [feas, this] using hfs _ hx
        · refine Prod.ext ?_ ?_
          · funext x
            by_cases hx' : x = ⟨i, hh⟩
            · subst hx'; simp [stepV, hx]
            · simp [stepV, Function.update, hx']
          · show t = S.card - 1 + 1
            have : 0 < S.card := Finset.card_pos.2 ⟨_, hx⟩
            omega
      · have hS' : ∀ x ∈ S, x.val < i := by
          intro x hx'
          have := hS x hx'
          by_contra hge
          have : x.val = i := by omega
          have hxe : x = ⟨i, by omega⟩ := Fin.ext this
          exact hmem ⟨by omega, hxe ▸ hx'⟩
        exact ⟨(stepV m c S v, t), (ih _ _).2 ⟨v, hv, S, hS', hc, hk, hfs, rfl⟩, Or.inl rfl⟩

end Lax117284Proofs.D3DP
