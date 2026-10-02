import Lax117284Proofs.Treewidth.Fun.E2Join1

/-!
# WP E2 (6): `joinC` and `joinKids` as F-functions

Cost of `joinC kmax a b` for `Good B0 a`, `Good B0 b`, entries `≤ kmax`, `sz ≤ s`:

    Hb X R0 s a = 8000 (s+1) (X^3)^(count a) + count a · R0,     X = cbound |B0| kmax 1 = 2^(4(|B0|+kmax+2)),

where `R0` bounds the cost of one call of `ringTypList` on entries `≤ kmax` and length `≤ 2 kmax + 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax117284Proofs.Treewidth.Fun
namespace E2

open ToVal Lax117284Proofs.Treewidth.Chars Lax117284Proofs.Treewidth.Trees CT Lib1 Lax117284Proofs.Treewidth.Seq

/-- the cost bound of `joinC` -/
def Hb (X R0 s : ℕ) (c : CT) : ℕ := 8000 * (s + 1) * (X ^ 3) ^ count c + count c * R0

/-- `R0` bounds the cost of `ringTypList` on the run sequences of characteristics with entries `≤ kmax`. -/
def RingOK (Δ' : ℕ → Option Tm) (B rid R0 kmax : ℕ) : Prop :=
  ∀ y y' : List ℕ, (∀ x ∈ y, x ≤ kmax) → (∀ x ∈ y', x ≤ kmax) → y.length ≤ 2 * kmax + 1 → y'.length ≤ 2 * kmax + 1 →
    Runs Δ' B rid [toVal y, toVal y'] (toVal (ringTypList y y')) R0

theorem Hb_mono {X R0 s : ℕ} (hX : 1 ≤ X) {c c' : CT} (h : count c ≤ count c') : Hb X R0 s c ≤ Hb X R0 s c' := by
  unfold Hb
  have h1 : (X ^ 3) ^ count c ≤ (X ^ 3) ^ count c' := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) h
  have := Nat.mul_le_mul_left (8000 * (s + 1)) h1
  have := Nat.mul_le_mul_right R0 h
  nlinarith

theorem jk_step_arith (Jl r j ρ Q Hk Sr m : ℕ) (hJ : Jl ≤ j) (hr : r ≤ ρ) (hQ : Q = j * ρ) (hj : j ≤ Q)
    (hρQ : ρ ≤ Q) (hQ256 : 256 ≤ Q) :
    1 + 1 + (1 + 1 + (1 + (1 + 1 + (1 + 1 + 0)) + (Sr + m * (100 * ρ + 40) + 10) + 1 +
      (1 + (1 + (1 + (1 + 1 + (1 + 1 + 0)) + Hk + 1 + 0)) + (Jl * (30 * r + 30 + 10 * r + 20) + 8) + 1) + 1) + 1) + 1 ≤
    Hk + Sr + (m + 1) * (100 * Q + 40) + 10 := by
  have h1 : Jl * (30 * r + 30 + 10 * r + 20) ≤ j * (40 * ρ + 50) := Nat.mul_le_mul hJ (by omega)
  have h2 : j * (40 * ρ + 50) ≤ 90 * Q := by nlinarith
  have h3 : m * (100 * ρ + 40) ≤ m * (100 * Q + 40) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

theorem jc_arith (t Z X W A cL R0 Sc m1 m2 Yl J Sg mn : ℕ) (hXZ : X ≤ Z) (hZ8 : 8 ≤ Z) (hWA : W ≤ A)
    (hA1 : 1 ≤ A) (ht : 1 ≤ t) (hm1 : m1 ≤ t) (hm2 : m2 ≤ t) (hSc : Sc ≤ t) (hmn : mn ≤ t) (hYl : Yl ≤ X)
    (hJ : J ≤ W) (hSg : Sg ≤ 8000 * t * A + cL * R0) :
    1 + 1 + (1 + 1 + 0) + 30 * mn + 1 +
      (1 + 1 + 1 + 0 + (8 * m1 + 5) + 1 + (1 + 1 + 1 + 0 + (8 * m2 + 5) + 1) + 1 +
        (1 + 1 + (1 + (1 + 1 + 1 + (1 + 1 + 1 + 0))) + (R0 + 8 * Sc + 4000 * Z) + 1 +
          (1 + (1 + 1 + 1 + (1 + 1 + 1 + 0)) + (Sg + m1 * (100 * W + 40) + 10) + 1 +
            (1 + (1 + 1 + 1 + 1 + (1 + 0)) + (J * (30 * Yl + 30 + 10 * Yl + 20) + 8) + 1) + 1) + 1) + 1) + 1 ≤
    8000 * t * (A * Z) + (1 + cL) * R0 := by
  have h1 : m1 * (100 * W + 40) ≤ t * (100 * A + 40) := Nat.mul_le_mul hm1 (by omega)
  have h2 : J * (30 * Yl + 30 + 10 * Yl + 20) ≤ A * (40 * Z + 50) :=
    Nat.mul_le_mul (le_trans hJ hWA) (by omega)
  have hP1 : 8 * (t * A) ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP2 : A * Z ≤ t * A * Z := by
    have : A * Z * 1 ≤ A * Z * t := Nat.mul_le_mul_left _ ht
    nlinarith
  have hP3 : t ≤ t * A * Z := by nlinarith [Nat.zero_le t]
  have hP4 : A ≤ t * A * Z := by nlinarith [Nat.zero_le A]
  have hP5 : Z ≤ t * A * Z := by nlinarith [Nat.zero_le Z]
  have hP6 : t * A ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP7 : 1 ≤ t * A * Z := by nlinarith
  nlinarith

theorem sum_Hb_le {X R0 s : ℕ} (hX : 2 ≤ X ^ 3) (ks : List CT) :
    (ks.map (Hb X R0 s)).sum ≤ 8000 * (s + 1) * (X ^ 3) ^ countL ks + countL ks * R0 := by
  have e : (ks.map (Hb X R0 s)).sum =
      8000 * (s + 1) * (ks.map (fun k => (X ^ 3) ^ count k)).sum + (ks.map (fun k => count k * R0)).sum := by
    induction ks with
    | nil => simp
    | cons k ks ih => simp only [List.map_cons, List.sum_cons, Hb] at ih ⊢; rw [ih]; ring
  have h1 := sum_count_pow_le hX ks
  have h2 := sum_count_mul ks R0
  rw [e, h2]
  nlinarith

theorem hb_ge {X R0 s : ℕ} (c : CT) (hX : 1 ≤ X) : R0 + 8 * s + 4000 * X ^ 3 ≤ Hb X R0 s c := by
  unfold Hb
  have hc := count_ge_one c
  have h3 : X ^ 3 ≤ (X ^ 3) ^ count c := by
    calc X ^ 3 = (X ^ 3) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by omega)) hc
  have h4 := Nat.mul_le_mul_left (8000 * (s + 1)) h3
  have h5 : R0 ≤ count c * R0 := Nat.le_mul_of_pos_left _ (by omega)
  have h6 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h7 := Nat.mul_le_mul_left s h6
  nlinarith

theorem jkb_arith (t Z W A cL R0 m Sg : ℕ) (hZ8 : 8 ≤ Z) (hWA : W ≤ A) (hA1 : 1 ≤ A) (ht : 1 ≤ t) (hm : m ≤ t)
    (hSg : Sg ≤ 8000 * t * A + cL * R0) : Sg + m * (100 * W + 40) + 10 ≤ 8000 * t * (A * Z) + (1 + cL) * R0 := by
  have h1 : m * (100 * W + 40) ≤ t * (100 * A + 40) := Nat.mul_le_mul hm (by omega)
  have hP1 : 8 * (t * A) ≤ t * A * Z := by nlinarith [Nat.zero_le (t * A)]
  have hP3 : t ≤ t * A * Z := by nlinarith [Nat.zero_le t]
  have hP7 : 1 ≤ t * A * Z := by nlinarith
  nlinarith

section joinC
variable {rid : ℕ} {Δ' : ℕ → Option Tm} (hΔ : e2Δ rid ⊑ Δ') (B : ℕ)
include hΔ

theorem mapKK_runs (S : Finset ℕ) (ys : List (List ℕ)) (kk : List CT) (hB : 1000 + 30 * ys.length < B) :
    Runs Δ' B fMapKK [Val.cons (toVal S) (toVal ys), toVal kk] (toVal (ys.map (fun d => node S d kk)))
      (30 * ys.length + 30) := by
  have h := Lib1.map_runs (ext1 hΔ) B fMkNode (Val.cons (toVal S) (toVal kk)) (fun d => node S d kk)
    (fun _ => 8) ys (fun d _ => by
      refine Runs.mk (hΔ _ _ (Δ_mkNode rid)) ?_
      simp only [toVal_ct]
      ev_start
      · ev_run
      · omega)
  rw [sum_map_const_mul] at h
  have hl : fMkNode < B := by show 175 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_mapKK rid)) ?_
  ev_start
  · ev_run
  · omega

theorem consAll_runs (rest : List (List CT)) (c : CT) (hB : 1000 + 30 * rest.length < B) :
    Runs Δ' B fConsAll [toVal rest, toVal c] (toVal (rest.map (c :: ·))) (30 * rest.length + 30) := by
  have h := Lib1.map_runs (ext1 hΔ) B fConsTo (toVal c) (fun l => c :: l) (fun _ => 6) rest (fun l _ => by
      refine Runs.mk (hΔ _ _ (Δ_consTo rid)) ?_
      ev_start
      · ev_run
      · omega)
  rw [sum_map_const_mul] at h
  have hl : fConsTo < B := by show 179 < B; omega
  refine Runs.mk (hΔ _ _ (Δ_consAll rid)) ?_
  ev_start
  · ev_run
  · omega

set_option maxHeartbeats 1000000 in
theorem joinKids_runs_aux (B0 : Finset ℕ) (kmax R0 s X : ℕ) (hXdef : X = xb B0.card kmax) (ks : List CT) :
    ∀ ks' : List CT, (∀ k ∈ ks, Good B0 k) → (∀ k' ∈ ks', Good B0 k') →
    (∀ k ∈ ks, ∀ k' ∈ ks', Runs Δ' B fJoinC [toVal kmax, toVal k, toVal k'] (toVal (joinC kmax k k'))
      (Hb X R0 s k)) →
    (ks.map (Hb X R0 s)).sum + ks.length * (100 * X ^ countL ks + 40) + 10 + 1000 < B →
    Runs Δ' B fJoinKids [toVal kmax, toVal ks, toVal ks'] (toVal (joinKids kmax ks ks'))
      ((ks.map (Hb X R0 s)).sum + ks.length * (100 * X ^ countL ks + 40) + 10) := by
  have hX256 : 256 ≤ X := hXdef ▸ xb_ge _ _
  induction ks with
  | nil =>
    intro ks' _ _ _ hB
    refine Runs.mk (hΔ _ _ (Δ_joinKids rid)) ?_
    cases ks' with
    | nil =>
      have : joinKids kmax [] [] = [[]] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil, List.map_nil, List.sum_nil, List.length_nil, countL]
      ev_start
      · ev_run
      · omega
    | cons k' ks' =>
      have : joinKids kmax [] (k' :: ks') = [] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil, List.map_nil, List.sum_nil, List.length_nil, countL]
      ev_start
      · ev_run
      · omega
  | cons k ks ih =>
    intro ks' hgk hgk' hf hB
    refine Runs.mk (hΔ _ _ (Δ_joinKids rid)) ?_
    cases ks' with
    | nil =>
      have : joinKids kmax (k :: ks) [] = [] := rfl
      rw [this]
      simp only [toVal_cons, toVal_nil]
      ev_start
      · ev_run
      · omega
    | cons k' ks' =>
      have hgk1 : Good B0 k := hgk k (by simp)
      have hgk1' : Good B0 k' := hgk' k' (by simp)
      have hgL : GoodL B0 ks := GoodL_iff.2 (fun x hx => hgk x (List.mem_cons_of_mem _ hx))
      have hgL' : GoodL B0 ks' := GoodL_iff.2 (fun x hx => hgk' x (List.mem_cons_of_mem _ hx))
      have hlj : (joinC kmax k k').length ≤ X ^ count k := by
        have := joinC_length_le_good (kmax := kmax) hgk1 hgk1'
        rw [hXdef, ← cbound_eq_pow]; exact this
      have hlr : (joinKids kmax ks ks').length ≤ X ^ countL ks := by
        have := joinKids_length_le_good (kmax := kmax) ks ks' hgL hgL'
        rw [hXdef, ← cbound_eq_pow]; exact this
      have hcL : countL (k :: ks) = count k + countL ks := rfl
      have hQ : X ^ countL (k :: ks) = X ^ count k * X ^ countL ks := by rw [hcL, pow_add]
      have hr1 : 1 ≤ X ^ countL ks := Nat.one_le_pow _ _ (by omega)
      have hcnt := count_ge_one k
      have hj1 : X ≤ X ^ count k := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ count k := Nat.pow_le_pow_right (by omega) hcnt
      have hrQ : X ^ countL ks ≤ X ^ countL (k :: ks) := by
        rw [hQ]; exact Nat.le_mul_of_pos_left _ (by omega)
      have hjQ : X ^ count k ≤ X ^ countL (k :: ks) := by
        rw [hQ]; exact Nat.le_mul_of_pos_right _ (by omega)
      have hQ256 : 256 ≤ X ^ countL (k :: ks) := le_trans hX256 (le_trans hj1 hjQ)
      simp only [List.map_cons, List.sum_cons, List.length_cons] at hB
      have hBm : 100 * X ^ countL (k :: ks) + 40 ≤ (ks.length + 1) * (100 * X ^ countL (k :: ks) + 40) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have hrest := ih ks' (fun x hx => hgk x (List.mem_cons_of_mem _ hx))
        (fun x hx => hgk' x (List.mem_cons_of_mem _ hx))
        (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        (by nlinarith [Nat.zero_le (ks.length * (100 * X ^ countL ks + 40)), Nat.zero_le (ks.length * X ^ countL ks)])
      have hJ := hf k (by simp) k' (by simp)
      have hcons : ∀ c ∈ joinC kmax k k', Runs Δ' B fConsAll [toVal (joinKids kmax ks ks'), toVal c]
          (toVal ((joinKids kmax ks ks').map (c :: ·))) (30 * (joinKids kmax ks ks').length + 30) := by
        intro c _
        exact consAll_runs hΔ B _ c (by omega)
      have hfm := flatMap_runs_le hΔ B fConsAll (toVal (joinKids kmax ks ks'))
        (fun c => (joinKids kmax ks ks').map (c :: ·)) (fun _ => 30 * (joinKids kmax ks ks').length + 30)
        (joinC kmax k k') (joinKids kmax ks ks').length (30 * (joinKids kmax ks ks').length + 30)
        (fun c _ => by simp) (fun _ _ => le_refl _) hcons
      have hlit : fConsAll < B := by show 180 < B; omega
      have hJK : joinKids kmax (k :: ks) (k' :: ks') =
          (joinC kmax k k').flatMap (fun c => (joinKids kmax ks ks').map (c :: ·)) := rfl
      rw [hJK]
      simp only [toVal_cons]
      ev_start
      · ev_run
      · simp only [List.map_cons, List.sum_cons, List.length_cons]
        exact jk_step_arith (Jl := (joinC kmax k k').length) (r := (joinKids kmax ks ks').length)
          (j := X ^ count k) (ρ := X ^ countL ks) (Q := X ^ countL (k :: ks)) (Hk := Hb X R0 s k)
          (Sr := (ks.map (Hb X R0 s)).sum) (m := ks.length) hlj hlr hQ hjQ hrQ hQ256

set_option maxHeartbeats 2000000 in
theorem joinC_runs_aux (B0 : Finset ℕ) (kmax R0 s X : ℕ) (hXdef : X = xb B0.card kmax)
    (hring : RingOK Δ' B rid R0 kmax) (a : CT) :
    ∀ b : CT, Good B0 a → Good B0 b → maxEntry a ≤ kmax → maxEntry b ≤ kmax → sz a ≤ s → sz b ≤ s →
    Hb X R0 s a + 1000 * (s + 1) + 1000 < B →
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b)) (Hb X R0 s a) := by
  have hX256 : 256 ≤ X := hXdef ▸ xb_ge _ _
  induction a using CT.ind with
  | h S y ks ih =>
    intro b hga hgb hma hmb hsa hsb hB
    obtain ⟨S', y', ks'⟩ := b
    have hcnode : count (node S y ks) = 1 + countL ks := rfl
    have hZ : 1 ≤ (X ^ 3) ^ count (node S y ks) := Nat.one_le_pow _ _ (by positivity)
    have hHb1 : 8000 * (s + 1) ≤ Hb X R0 s (node S y ks) := by
      unfold Hb; nlinarith [Nat.zero_le (count (node S y ks) * R0)]
    have hB1 : 1 < B := by omega
    have hsS := sz_S_le S y ks
    have hsks := sz_ks_le S y ks
    have hcardS := sz_finset_card S
    have hm : ks.length ≤ s := by
      have := length_le_sz ks; omega
    have hjc : joinC kmax (node S y ks) (node S' y' ks') =
        if S = S' ∧ ks.length = ks'.length then
          (joinKids kmax ks ks').flatMap (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk))
        else [] := rfl
    by_cases hS : S = S'
    · by_cases hlen : ks.length = ks'.length
      · subst hS
        have hs' : sz ks' < sz (node S y' ks') := sz_ks_le S y' ks'
        have hm' : ks'.length ≤ s := by have := length_le_sz ks'; omega
        obtain ⟨hgk, hmk⟩ := kids_good hga hma
        obtain ⟨hgk', hmk'⟩ := kids_good hgb hmb
        have hy : ∀ x ∈ y, x ≤ kmax := ((maxEntry_le_iff).1 hma).1
        have hy' : ∀ x ∈ y', x ≤ kmax := ((maxEntry_le_iff).1 hmb).1
        have hly := y_length_le hga hma
        have hly' := y_length_le hgb hmb
        have hgL : GoodL B0 ks := GoodL_iff.2 hgk
        have hgL' : GoodL B0 ks' := GoodL_iff.2 hgk'
        have hv : joinC kmax (node S y ks) (node S y' ks') =
            (joinKids kmax ks ks').flatMap (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk)) := by
          rw [hjc, if_pos ⟨rfl, hlen⟩]
        have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S true (by simp)
        have hl1 := Lib1.length_runs (ext1 hΔ) B ks (by omega)
        have hl2 := Lib1.length_runs (ext1 hΔ) B ks' (by omega)
        have hXk : 4 ^ (2 * kmax + 1) ≤ X := hXdef ▸ xb_ring _ _
        have hXk' : kmax + 1 ≤ X := hXdef ▸ xb_k _ _
        have hX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
        have hX38 : 8 ≤ X ^ 3 := by omega
        have hHb2 := hb_ge (X := X) (R0 := R0) (s := s) (node S y ks) (by omega)
        have hys := joinYs_runs hΔ B S kmax y y' R0 X hy hy' hXk hXk' (by omega) (hring y y' hy hy' hly hly')
          (by omega)
        have hysl : (joinYsL S.card kmax y y').length ≤ X := by
          have := joinYs_length_le (a := y) (b := y') (c := S.card) (kmax := kmax) (L₁ := kmax) (L₂ := kmax) hy hy'
          have h2 : 4 ^ (kmax + kmax + 1) = 4 ^ (2 * kmax + 1) := by congr 1; omega
          unfold joinYsL; omega
        have hjkl : (joinKids kmax ks ks').length ≤ X ^ countL ks := by
          have := joinKids_length_le_good (kmax := kmax) ks ks' hgL hgL'
          rw [hXdef, ← cbound_eq_pow]; exact this
        have hjk := joinKids_runs_aux hΔ B B0 kmax R0 s X hXdef ks ks' hgk hgk'
          (fun k hk k' hk' => ih k hk k' (hgk k hk) (hgk' k' hk') (hmk k hk) (hmk' k' hk')
            (by have := sz_le_of_mem_kids (S := S) (y := y) hk; omega)
            (by have := sz_le_of_mem_kids (S := S) (y := y') hk'; omega)
            (by
              have h6 : count k ≤ count (node S y ks) := by
                have := count_le_countL_of_mem hk; rw [hcnode]; omega
              have := Hb_mono (X := X) (R0 := R0) (s := s) (by omega) h6
              exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_right this _) _) hB))
          (by
            have hsum := sum_Hb_le (X := X) (R0 := R0) (s := s) (by omega) ks
            have hkb := jkb_arith (s + 1) (X ^ 3) (X ^ countL ks) ((X ^ 3) ^ countL ks) (countL ks) R0 ks.length
              ((ks.map (Hb X R0 s)).sum) hX38 (Nat.pow_le_pow_left hX3 _)
              (Nat.one_le_pow _ _ (by omega)) (by omega) (by omega) hsum
            have hHbeq : Hb X R0 s (node S y ks) =
                8000 * (s + 1) * ((X ^ 3) ^ countL ks * X ^ 3) + (1 + countL ks) * R0 := by
              unfold Hb; rw [hcnode, pow_add]; ring
            rw [hHbeq] at hB
            linarith)
        have hmk1 := fun kk (_ : kk ∈ joinKids kmax ks ks') =>
          mapKK_runs hΔ B S (joinYsL S.card kmax y y') kk (by linarith)
        have hfm := flatMap_runs_le hΔ B fMapKK (Val.cons (toVal S) (toVal (joinYsL S.card kmax y y')))
          (fun kk => (joinYsL S.card kmax y y').map (fun d => node S d kk))
          (fun _ => 30 * (joinYsL S.card kmax y y').length + 30) (joinKids kmax ks ks')
          (joinYsL S.card kmax y y').length (30 * (joinYsL S.card kmax y y').length + 30)
          (fun kk _ => by simp) (fun _ _ => le_refl _) hmk1
        have hlit : fMapKK < B := by show 176 < B; omega
        refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
        rw [hv]
        simp only [toVal_ct]
        ev_start
        · ev_run
        · have hHbeq : Hb X R0 s (node S y ks) =
              8000 * (s + 1) * ((X ^ 3) ^ countL ks * X ^ 3) + (1 + countL ks) * R0 := by
            unfold Hb; rw [hcnode, pow_add]; ring
          rw [hHbeq]
          exact jc_arith (s + 1) (X ^ 3) X (X ^ countL ks) ((X ^ 3) ^ countL ks) (countL ks) R0 S.card ks.length
            ks'.length (joinYsL S.card kmax y y').length (joinKids kmax ks ks').length
            ((ks.map (Hb X R0 s)).sum) (min (sz S) (sz S)) hX3 hX38 (Nat.pow_le_pow_left hX3 _)
            (Nat.one_le_pow _ _ (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) hysl hjkl
            (sum_Hb_le (X := X) (R0 := R0) (s := s) (by omega) ks)
      · have hv : joinC kmax (node S y ks) (node S' y' ks') = [] := by
          rw [hjc, if_neg (by simp [hlen])]
        have hm' : ks'.length ≤ s := by
          have := sz_ks_le S' y' ks'; have := length_le_sz ks'; omega
        have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S' true (by simp [hS])
        have hl1 := Lib1.length_runs (ext1 hΔ) B ks (by omega)
        have hl2 := Lib1.length_runs (ext1 hΔ) B ks' (by omega)
        refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
        rw [hv]
        simp only [toVal_ct, toVal_nil]
        ev_start
        · ev_run
        · have := min_le_left (sz S) (sz S')
          omega
    · have hv : joinC kmax (node S y ks) (node S' y' ks') = [] := by
        rw [hjc, if_neg (by simp [hS])]
      have heq := Lib1.eqV_runs_typed (ext1 hΔ) B hB1 S S' false (by simp [hS])
      refine Runs.mk (hΔ _ _ (Δ_joinC rid)) ?_
      rw [hv]
      simp only [toVal_ct, toVal_nil]
      ev_start
      · ev_run
      · have := min_le_left (sz S) (sz S')
        omega

omit hΔ in
theorem Hb_le_wf {B0 : Finset ℕ} {kmax : ℕ} {a : CT} (ha : a.Wf B0 kmax) (R0 s : ℕ) :
    Hb (xb B0.card kmax) R0 s a ≤ 8000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0 := by
  have hc : count a ≤ (2 * B0.card + 2) ^ 2 := by
    have := ha.count_le; unfold runBound at this; nlinarith
  have hX : xb B0.card kmax = 2 ^ (4 * (B0.card + kmax + 2)) := by
    unfold xb cbound; congr 1; ring
  have hN : B0.card + 1 ≤ B0.card + kmax + 2 := by omega
  have h2 : (2 * B0.card + 2) ^ 2 ≤ 4 * (B0.card + kmax + 2) ^ 2 := by
    have := Nat.pow_le_pow_left hN 2
    calc (2 * B0.card + 2) ^ 2 = 4 * (B0.card + 1) ^ 2 := by ring
      _ ≤ 4 * (B0.card + kmax + 2) ^ 2 := Nat.mul_le_mul_left _ this
  have h1 : ((xb B0.card kmax) ^ 3) ^ count a ≤ 2 ^ (48 * (B0.card + kmax + 2) ^ 3) := by
    rw [hX, ← pow_mul, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    calc 4 * (B0.card + kmax + 2) * (3 * count a) = (12 * (B0.card + kmax + 2)) * count a := by ring
      _ ≤ (12 * (B0.card + kmax + 2)) * (4 * (B0.card + kmax + 2) ^ 2) :=
          Nat.mul_le_mul_left _ (le_trans hc h2)
      _ = 48 * (B0.card + kmax + 2) ^ 3 := by ring
  unfold Hb
  have h3 := Nat.mul_le_mul_left (8000 * (s + 1)) h1
  have h4 := Nat.mul_le_mul_right R0 hc
  omega

/-- **`joinC` as an F-function**, for well-formed characteristics on the boundary `B0` (entries `≤ kmax`).
`R0` bounds one call of `ringTypList`; `s` bounds the sizes of the inputs.  The cost is
`8000 (s+1) 2^(48 (|B0|+kmax+2)^3) + (2|B0|+2)^2 · R0`. -/
theorem joinC_runs {B0 : Finset ℕ} {kmax : ℕ} {a b : CT} (ha : a.Wf B0 kmax) (hb : b.Wf B0 kmax) (R0 s : ℕ)
    (hring : RingOK Δ' B rid R0 kmax) (hsa : sz a ≤ s) (hsb : sz b ≤ s)
    (hB : 16000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0 + 2000 * (s + 1) + 2000 < B) :
    Runs Δ' B fJoinC [toVal kmax, toVal a, toVal b] (toVal (joinC kmax a b))
      (8000 * (s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3) + (2 * B0.card + 2) ^ 2 * R0) := by
  have hle := Hb_le_wf ha R0 s
  have h := joinC_runs_aux hΔ B B0 kmax R0 s (xb B0.card kmax) rfl hring a b ha.good hb.good ha.bounded hb.bounded
    hsa hsb (by
      have hpos := Nat.zero_le ((s + 1) * 2 ^ (48 * (B0.card + kmax + 2) ^ 3))
      nlinarith)
  exact h.mono hle

end joinC

end E2
end Lax117284Proofs.Treewidth.Fun
