import Lax117284Proofs.IlpClients.Final

/-!
# Numeric bounds: Alg F runs with word-sized numbers

Let `Bd n cnt B = (n+1) · n! · (N K + ∑_{t<T} cnt t + B + 1)` (`N = nN n`, `K = Kn n`).  For a
certificate in the box every intermediate number of `decode` is at most `Bd` (the digits, `sigma`,
`cp`, `Sj`, `P_i`, `Q_i`, the values of the extras and, once the guards hold, of the bases; a
running sum of at most `n` extras is at most `n · Bd`), and `Bd n cnt B ≤ (zLen n + v + 1)^4` when
`B` and all `cnt t` (`t < T`) are at most `v`.
-/

namespace Lax117284Proofs.IlpClients

open Finset
open Classical

noncomputable section

/-- The bound on every intermediate number. -/
def Bd (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) : ℕ :=
  (n + 1) * n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1)

section Numbers

variable {n : ℕ} {cnt : ℕ → ℕ} {B : ℕ} {ω : Cert}

theorem coef_le_one' (r c : ℕ) : coef n r c ≤ 1 := coef_le_one n r c

theorem sigma_le (d : ℕ → ℕ) (t : ℕ) : sigma n d t ≤ nN n * Kn n := by
  unfold sigma
  calc ∑ c ∈ range (nN n), (if tyOf n c = some t ∧ d c < Kn n then d c else 0)
      ≤ ∑ _c ∈ range (nN n), Kn n := by
        refine Finset.sum_le_sum fun c _ => ?_
        split_ifs with h
        · exact h.2.le
        · exact Nat.zero_le _
    _ = nN n * Kn n := by simp

theorem cnt_le_sum {t : ℕ} (ht : t < nT n) : cnt t ≤ ∑ t' ∈ range (nT n), cnt t' :=
  Finset.single_le_sum (f := cnt) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)

/-- Two bases of the same type coincide. -/
theorem isBase_inj (d : ℕ → ℕ) {c c' : ℕ} (hc : isBase n d c) (hc' : isBase n d c')
    (h : tyIdx n c = tyIdx n c') : c = c' := by
  obtain ⟨hcL, hτ, hbs⟩ := hc
  obtain ⟨hcL', hτ', hbs'⟩ := hc'
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hτ
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hτ'
  have h1 : tyIdx n c = t := by simp [tyIdx, ht]
  have h2 : tyIdx n c' = t' := by simp [tyIdx, ht']
  have h3 : tyOf n c = tyOf n c' := by rw [ht, ht', ← h1, ← h2, h]
  rw [← hbs, ← hbs']
  exact bs_congr (tyOf n) _ hcL h3

theorem bases_le (d : ℕ → ℕ) :
    ∑ c ∈ range (nN n), (if isBase n d c then cnt (tyIdx n c) else 0) ≤
      ∑ t ∈ range (nT n), cnt t := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (f := cnt) (s := (range (nN n)).filter (isBase n d)) (g := tyIdx n)
    (fun c hc c' hc' h => isBase_inj d (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hc').2 h)]
  refine Finset.sum_le_sum_of_subset ?_
  intro t ht
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
  have hτ := (Finset.mem_filter.mp hc).2.2.1
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hτ
  have : tyIdx n c = t' := by simp [tyIdx, ht']
  rw [this]
  exact Finset.mem_range.mpr (tyOf_some ht').2.2

/-- `Sj` is at most `N K + ∑ cnt`. -/
theorem Sj_le (d : ℕ → ℕ) (j : ℕ) :
    Sj n cnt d j ≤ nN n * Kn n + ∑ t ∈ range (nT n), cnt t := by
  unfold Sj
  refine Nat.add_le_add ?_ ?_
  · calc ∑ c ∈ range (nN n), (if d c < Kn n then d c * coef n (nT n + j) c else 0)
        ≤ ∑ _c ∈ range (nN n), Kn n := by
          refine Finset.sum_le_sum fun c _ => ?_
          split_ifs with h
          · have := coef_le_one n (nT n + j) c
            calc d c * coef n (nT n + j) c ≤ d c * 1 := Nat.mul_le_mul_left _ this
              _ ≤ Kn n := by omega
          · exact Nat.zero_le _
      _ = nN n * Kn n := by simp
  · refine le_trans (Finset.sum_le_sum fun c _ => ?_) (bases_le (cnt := cnt) d)
    split_ifs with h
    · have := coef_le_one n (nT n + j) c
      calc cp n cnt d (tyIdx n c) * coef n (nT n + j) c ≤ cp n cnt d (tyIdx n c) * 1 :=
            Nat.mul_le_mul_left _ this
        _ ≤ cnt (tyIdx n c) := by
          rw [mul_one]; exact Nat.sub_le _ _
    · exact Nat.zero_le _

/-- `P_i` and `Q_i` (`i < n`) are at most `n · n! · (B + N K + ∑ cnt)`. -/
theorem Pi_le (hω : InBox n ω) {i : ℕ} (hi : i < n) :
    Pi n cnt B ω i ≤ n * (n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t))) := by
  unfold Pi
  calc ∑ j ∈ range n, (ω.Hp i j * B + ω.Hn i j * Sj n cnt ω.d j)
      ≤ ∑ _j ∈ range n, n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have h1 := (hω.2.1 i hi j hj').1
        have h2 := (hω.2.1 i hi j hj').2
        have h3 := Sj_le (n := n) (cnt := cnt) ω.d j
        calc ω.Hp i j * B + ω.Hn i j * Sj n cnt ω.d j
            ≤ n.factorial * B + n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t) :=
              Nat.add_le_add (Nat.mul_le_mul h1 le_rfl) (Nat.mul_le_mul h2 h3)
          _ = _ := by ring
    _ = _ := by simp

theorem Qi_le (hω : InBox n ω) {i : ℕ} (hi : i < n) :
    Qi n cnt B ω i ≤ n * (n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t))) := by
  unfold Qi
  calc ∑ j ∈ range n, (ω.Hp i j * Sj n cnt ω.d j + ω.Hn i j * B)
      ≤ ∑ _j ∈ range n, n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' := Finset.mem_range.mp hj
        have h1 := (hω.2.1 i hi j hj').1
        have h2 := (hω.2.1 i hi j hj').2
        have h3 := Sj_le (n := n) (cnt := cnt) ω.d j
        calc ω.Hp i j * Sj n cnt ω.d j + ω.Hn i j * B
            ≤ n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t) + n.factorial * B :=
              Nat.add_le_add (Nat.mul_le_mul h1 h3) (Nat.mul_le_mul h2 le_rfl)
          _ = _ := by ring
    _ = _ := by simp

theorem PQ_le_Bd (n : ℕ) (cnt : ℕ → ℕ) (B : ℕ) :
    n * (n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t))) ≤ Bd n cnt B := by
  unfold Bd
  have : (n : ℕ) * n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t)) ≤
      (n + 1) * n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ n) le_rfl)
    omega
  calc n * (n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t)))
      = n * n.factorial * (B + (nN n * Kn n + ∑ t ∈ range (nT n), cnt t)) := by ring
    _ ≤ _ := this

theorem Pi_le_Bd (hω : InBox n ω) {i : ℕ} (hi : i < n) : Pi n cnt B ω i ≤ Bd n cnt B :=
  (Pi_le hω hi).trans (PQ_le_Bd n cnt B)

theorem Qi_le_Bd (hω : InBox n ω) {i : ℕ} (hi : i < n) : Qi n cnt B ω i ≤ Bd n cnt B :=
  (Qi_le hω hi).trans (PQ_le_Bd n cnt B)

theorem sigma_le_Bd (d : ℕ → ℕ) (t : ℕ) : sigma n d t ≤ Bd n cnt B := by
  refine (sigma_le d t).trans ?_
  unfold Bd
  have h1 : 1 ≤ (n + 1) * n.factorial := Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)
  calc nN n * Kn n ≤ nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1 := by omega
    _ ≤ (n + 1) * n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1) :=
        Nat.le_mul_of_pos_left _ h1

theorem Sj_le_Bd (d : ℕ → ℕ) (j : ℕ) : Sj n cnt d j ≤ Bd n cnt B := by
  refine (Sj_le d j).trans ?_
  unfold Bd
  have h1 : 1 ≤ (n + 1) * n.factorial := Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)
  calc nN n * Kn n + ∑ t ∈ range (nT n), cnt t
      ≤ nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1 := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left _ h1

theorem cnt_le_Bd {t : ℕ} (ht : t < nT n) : cnt t ≤ Bd n cnt B := by
  refine (cnt_le_sum ht).trans ?_
  unfold Bd
  have h1 : 1 ≤ (n + 1) * n.factorial := Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)
  calc ∑ t ∈ range (nT n), cnt t ≤ nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1 := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left _ h1

theorem Kn_le_Bd : Kn n ≤ Bd n cnt B := by
  unfold Bd
  have h1 : 1 ≤ (n + 1) * n.factorial := Nat.mul_pos (Nat.succ_pos _) (Nat.factorial_pos _)
  have h2 : 1 ≤ nN n := nN_pos n
  calc Kn n ≤ nN n * Kn n := Nat.le_mul_of_pos_left _ h2
    _ ≤ nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1 := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left _ h1

/-- The value of an extra is at most `Bd` (when its rank is `< n`). -/
theorem wcol_le_Bd (hω : InBox n ω) {c : ℕ} (hc : rk n ω.d c < n) :
    wcol n cnt B ω c ≤ Bd n cnt B := by
  unfold wcol
  exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans (Pi_le_Bd hω hc))

/-- The rank of an extra is below the number of extras. -/
theorem rk_lt_card {d : ℕ → ℕ} {c : ℕ} (hc : c ∈ Ext n d) : rk n d c < (Ext n d).card := by
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨c, hc, ?_⟩
    simp
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hxN : x < nN n := hx.1.trans (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxN, hx.2⟩

/-- A running sum of at most `n` extras of a type is at most `n · Bd`. -/
theorem extraSum_le (hω : InBox n ω) (hE : (Ext n ω.d).card ≤ n) (t : ℕ) :
    extraSum n cnt B ω t ≤ n * Bd n cnt B := by
  unfold extraSum
  rw [← Finset.sum_filter]
  have hsub : (range (nN n)).filter (fun c => isExtra n ω.d c ∧ tyOf n c = some t) ⊆
      Ext n ω.d := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2.1⟩
  calc ∑ c ∈ (range (nN n)).filter (fun c => isExtra n ω.d c ∧ tyOf n c = some t),
        wcol n cnt B ω c
      ≤ ∑ _c ∈ (range (nN n)).filter (fun c => isExtra n ω.d c ∧ tyOf n c = some t),
          Bd n cnt B := by
        refine Finset.sum_le_sum fun c hc => wcol_le_Bd hω ?_
        exact (rk_lt_card (hsub hc)).trans_le hE
    _ ≤ ∑ _c ∈ Ext n ω.d, Bd n cnt B := Finset.sum_le_sum_of_subset hsub
    _ ≤ n * Bd n cnt B := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hE

/-- Once the guards hold, every value of the candidate is at most `Bd`. -/
theorem xval_le_Bd (hω : InBox n ω) (hG : Guards n cnt B ω) (c : ℕ) :
    xval n cnt B ω c ≤ Bd n cnt B := by
  unfold xval
  by_cases h1 : isLive n c ∧ ω.d c < Kn n
  · rw [if_pos h1]
    exact h1.2.le.trans Kn_le_Bd
  · rw [if_neg h1]
    by_cases h2 : isExtra n ω.d c
    · rw [if_pos h2]
      have hcE : c ∈ Ext n ω.d :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have := h2.1
          unfold Lset at this
          exact Finset.mem_range.mp (Finset.mem_filter.mp this).1), h2⟩
      exact wcol_le_Bd hω ((rk_lt_card hcE).trans_le hG.2.1)
    · rw [if_neg h2]
      by_cases h3 : isBase n ω.d c
      · rw [if_pos h3]
        obtain ⟨-, hτ, -⟩ := h3
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hτ
        have hti : tyIdx n c = t := by simp [tyIdx, ht]
        rw [hti]
        refine (Nat.sub_le _ _).trans ?_
        exact (Nat.sub_le _ _).trans (cnt_le_Bd (tyOf_some ht).2.2)
      · rw [if_neg h3]; exact Nat.zero_le _

end Numbers

section Sizes

/-- `n + 1 ≤ 2 ^ n`. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

theorem factorial_le_nT (n : ℕ) : n.factorial ≤ nT n := by
  calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le n
    _ = nT n := by unfold nT; rw [← pow_mul]

theorem nT_le_nN (n : ℕ) : nT n ≤ nN n := by
  unfold nN nV
  have := Nat.mul_le_mul_left (nT n) (Nat.one_le_two_pow (n := n))
  simp only [nZ]; nlinarith [Nat.one_le_two_pow (n := n)]

theorem nN_le_zLen (n : ℕ) : nN n + 1 ≤ zLen n := by
  unfold zLen nM
  have h1 : 1 ≤ nT n + n := by have := nT_pos n; omega
  have : nN n * 1 ≤ (nT n + n) * nN n := by nlinarith
  omega

theorem n_succ_le_zLen (n : ℕ) : n + 1 ≤ zLen n := by
  have h1 := nN_le_zLen n
  unfold nN at h1
  omega

theorem Kn_le_zLen (n : ℕ) : Kn n ≤ zLen n := by
  have h1 : (n + 1) ^ (n + 1) ≤ nV n := by
    calc (n + 1) ^ (n + 1) ≤ (2 ^ n) ^ (n + 1) := Nat.pow_le_pow_left (succ_le_two_pow n) _
      _ = nV n := by unfold nV nT nZ; rw [← pow_mul, ← pow_add]; congr 1
  have h2 := nN_le_zLen n
  unfold Kn nN at *
  omega

/-- `Bd n cnt B ≤ (zLen n + v + 1)^4` whenever `B` and the `cnt t` (`t < T`) are at most `v`. -/
theorem Bd_le_pow4 (n : ℕ) (cnt : ℕ → ℕ) (B v : ℕ) (hB : B ≤ v)
    (hcnt : ∀ t < nT n, cnt t ≤ v) : Bd n cnt B ≤ (zLen n + v + 1) ^ 4 := by
  set a := zLen n with ha
  have h1 : n + 1 ≤ a := n_succ_le_zLen n
  have h2 : n.factorial ≤ a := (factorial_le_nT n).trans
    ((nT_le_nN n).trans (by have := nN_le_zLen n; omega))
  have h3 : nN n ≤ a := by have := nN_le_zLen n; omega
  have h4 : Kn n ≤ a := Kn_le_zLen n
  have h5 : nT n ≤ a := (nT_le_nN n).trans h3
  have h6 : ∑ t ∈ range (nT n), cnt t ≤ a * v := by
    calc ∑ t ∈ range (nT n), cnt t ≤ ∑ _t ∈ range (nT n), v :=
          Finset.sum_le_sum fun t ht => hcnt t (Finset.mem_range.mp ht)
      _ = nT n * v := by simp
      _ ≤ a * v := Nat.mul_le_mul_right _ h5
  unfold Bd
  have h7 : nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1 ≤ (a + v + 1) * (a + v + 1) := by
    have : nN n * Kn n ≤ a * a := Nat.mul_le_mul h3 h4
    nlinarith
  have h8 : (n + 1) * n.factorial ≤ (a + v + 1) * (a + v + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc (n + 1) * n.factorial * (nN n * Kn n + ∑ t ∈ range (nT n), cnt t + B + 1)
      ≤ ((a + v + 1) * (a + v + 1)) * ((a + v + 1) * (a + v + 1)) := Nat.mul_le_mul h8 h7
    _ = (a + v + 1) ^ 4 := by ring

end Sizes

end

end Lax117284Proofs.IlpClients
