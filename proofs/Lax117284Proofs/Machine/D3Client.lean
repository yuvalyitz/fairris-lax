import Lax117284Proofs.Machine.D3Day

/-!
One client of the dynamic program: the days are swept in turn, each on the table the day before
left, and the table is collapsed to the states that served the client on `k` days.
-/

namespace Lax117284Proofs.Machine.D3Client

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.Out Lax117284Proofs.Machine.Emit
open Lax117284Proofs.Machine.T9Ops Lax117284Proofs.Machine.FoldLoop
open Lax117284Proofs.Machine.MisBlk (asgE condLt_true condLt_false)
open Lax117284Proofs.Machine.X3Loop (rd)
open Lax117284Proofs.Machine.D3Ops Lax117284Proofs.Machine.D3Sweep Lax117284Proofs.Machine.D3Day
open Lax117284Proofs.Machine.D3Coll Lax117284Proofs.Machine.D3Cell
open Lax117284Proofs.D3DP Lax117284Proofs.D3Code Lax117284Proofs.D3Tab

variable {B : ℕ}

/-- The processing time, on a day, of the client at a position, through the order `R0`. -/
def qF (arr R0 : List ℕ) (PK n : ℕ) (i c : ℕ) : ℕ := arr.getD (2 + 2 * (i * n + R0.getD (PK + c) 0)) 0

/-- What the loops over clients and days read and never change: the scalars, the token array and
the numbers they satisfy. -/
structure CEnv (B : ℕ) (arr : List ℕ) (n m P k PK : ℕ) (σ : Env) : Prop where
  hA : σ.arrs "TK" = arr
  vn : σ.vars "n" = n
  vm : σ.vars "m" = m
  vPK : σ.vars "PK" = PK
  vPP : σ.vars "PP" = P
  vkp : σ.vars "kp" = k
  vb1 : σ.vars "b1" = n + 1
  vpk : σ.vars "pk" = P * k
  hP : P = (n + 1) ^ m
  hPK : PK = P * (k + 1)
  hn0 : 0 < n
  hm0 : 0 < m
  hlen : 3 + 2 * (m * n) ≤ arr.length
  hV : ∀ j < 3 + 2 * (m * n), 2 * arr.getD j 0 + 16 < B
  hmnB : 2 * (m * n) + 8 < B
  hPKB : PK + n + 8 < B

/-- The scalars the environment reads. -/
def CVars : List String := ["n", "m", "PK", "PP", "kp", "b1", "pk"]

lemma CEnv.congr {arr : List ℕ} {n m P k PK : ℕ} {σ σ' : Env} (h : CEnv B arr n m P k PK σ)
    (hv : ∀ y ∈ CVars, σ'.vars y = σ.vars y) (ha : σ'.arrs "TK" = σ.arrs "TK") :
    CEnv B arr n m P k PK σ' :=
  { h with
    hA := by rw [ha]; exact h.hA
    vn := by rw [hv "n" (by simp [CVars])]; exact h.vn
    vm := by rw [hv "m" (by simp [CVars])]; exact h.vm
    vPK := by rw [hv "PK" (by simp [CVars])]; exact h.vPK
    vPP := by rw [hv "PP" (by simp [CVars])]; exact h.vPP
    vkp := by rw [hv "kp" (by simp [CVars])]; exact h.vkp
    vb1 := by rw [hv "b1" (by simp [CVars])]; exact h.vb1
    vpk := by rw [hv "pk" (by simp [CVars])]; exact h.vpk }

lemma CEnv.P_le {arr : List ℕ} {n m P k PK : ℕ} {σ : Env} (h : CEnv B arr n m P k PK σ) :
    n + 1 ≤ P ∧ P ≤ PK ∧ k + 1 ≤ PK ∧ P * k ≤ PK ∧ 0 < P := by
  have hP := h.hP
  have h1 : n + 1 ≤ P := by
    rw [hP]
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ m := Nat.pow_le_pow_right (by omega) h.hm0
  have hP0 : 0 < P := by omega
  have hk : P * (k + 1) = P * k + P := by ring
  have h2 : P ≤ PK := by rw [h.hPK, hk]; omega
  have h3 : k + 1 ≤ PK := by
    rw [h.hPK]; calc k + 1 = 1 * (k + 1) := (one_mul _).symm
      _ ≤ P * (k + 1) := Nat.mul_le_mul_right _ hP0
  have h4 : P * k ≤ PK := by rw [h.hPK, hk]; omega
  exact ⟨h1, h2, h3, h4, hP0⟩

/-- The order in `R` and its values. -/
structure RInv (B n PK : ℕ) (R0 R : List ℕ) : Prop where
  len : PK + n ≤ R.length
  ord : ∀ y, PK ≤ y → R.getD y 0 = R0.getD y 0
  small : ∀ j, R.getD j 0 < B

/-- The environment of the sweep, from the environment of the loops. -/
lemma CEnv.sw {arr : List ℕ} {n m P k PK : ℕ} {σ : Env} (h : CEnv B arr n m P k PK σ)
    {R0 : List ℕ} (hR : RInv B n PK R0 (σ.arrs "R")) (hRv : ∀ c' < n, R0.getD (PK + c') 0 < n)
    {pw c qic ec : ℕ} (hcl : σ.vars "cl" = c) (hc : c < n) (hpw : σ.vars "pw" = pw)
    (hpwB : pw + 8 < B) (hq : σ.vars "qic" = qic) (hqB : qic + 8 < B) (hec : σ.vars "ec" = ec)
    (heB : ec + 8 < B) : SwEnv B arr n P k (n + 1) pw c qic ec PK σ := by
  obtain ⟨h1, h2, h3, h4, hP0⟩ := h.P_le
  have hmn : n ≤ m * n := Nat.le_mul_of_pos_left _ h.hm0
  have hPKB := h.hPKB
  have hlen := h.hlen
  have hmnB := h.hmnB
  have hRl := hR.len
  exact ⟨h.hA, h.vPK, h.vPP, h.vkp, h.vb1, hpw, hcl, hq, hec, by omega,
    fun j hj => by have := h.hV j (by omega); omega, by omega, hR.len, by omega,
    fun c' hc' => by rw [hR.ord _ (by omega)]; exact hRv c' hc', hR.small, hPKB, by omega, by omega,
    by omega, hpwB, by omega, hqB, heB⟩


/-- The value of an entry of the table of the stream is small. -/
lemma CEnv.arr_lt {arr : List ℕ} {n m P k PK : ℕ} {σ : Env} (h : CEnv B arr n m P k PK σ) {j : ℕ}
    (hj : j < 3 + 2 * (m * n)) : arr.getD j 0 + 8 < B := by
  have := h.hV j hj; omega

/-- **The times add up to a word.** -/
lemma CEnv.sum_lt {arr : List ℕ} {n m P k PK : ℕ} {σ : Env} (h : CEnv B arr n m P k PK σ)
    {R0 : List ℕ} (hRv : ∀ c' < n, R0.getD (PK + c') 0 < n) {i c : ℕ} (hi : i < m) (hc : c < n) :
    ∀ δ, δ ≤ n → qF arr R0 PK n i c + fv (eOrd arr R0 PK) δ + 8 < B := by
  intro δ hδ
  have hmn : n ≤ m * n := Nat.le_mul_of_pos_left _ h.hm0
  have hidx : i * n + R0.getD (PK + c) 0 < m * n := by
    have h1 := hRv c hc
    have h2 : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right _ hi
    have h3 : (i + 1) * n = i * n + n := by ring
    omega
  have h1 := h.hV (2 + 2 * (i * n + R0.getD (PK + c) 0)) (by omega)
  unfold qF
  unfold fv
  split
  · omega
  · rename_i hδ0
    have hr := hRv (δ - 1) (by omega)
    have h2 := h.hV (3 + 2 * R0.getD (PK + (δ - 1)) 0) (by omega)
    unfold eOrd
    omega

/-- The target function of the machine is the one of the table. -/
lemma tgtM_eq {n m k c i : ℕ} {q : ℕ → ℕ → ℕ} {e : ℕ → ℕ} {qic ec : ℕ} (hq : qic = q i c)
    (he : ec = e c) :
    tgtM ((n + 1) ^ m) k (n + 1) ((n + 1) ^ i) c qic ec e = tgt m k n q e c i := by
  subst hq he
  funext x
  unfold tgtM tgt dig
  rfl

/-- The days of a client. -/
def dayLoop : Com := fLoop "dy" "m" dayBody

/-- The scalars the days assign. -/
def SDL : List String := "dy" :: (SDAY ++ ("jj" :: SSW))

lemma cvars_frame {y : String} (hy : y ∈ CVars) : y ∉ SDL := by
  simp only [CVars, SDL, SDAY, SSW, S1, S2, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 12800000 in
/-- **The days of a client.** -/
theorem dayLoop_run {arr : List ℕ} {n m P k PK c : ℕ} (R0 : List ℕ) (σ : Env)
    (h : CEnv B arr n m P k PK σ) (hR : RInv B n PK R0 (σ.arrs "R"))
    (hRv : ∀ c' < n, R0.getD (PK + c') 0 < n) (hc : c < n) (hcl : σ.vars "cl" = c)
    (hjc : σ.vars "jc" = R0.getD (PK + c) 0)
    (hec : σ.vars "ec" = arr.getD (3 + 2 * R0.getD (PK + c) 0) 0)
    (hpw : σ.vars "pw" = 1) (hqB : σ.vars "qic" + 8 < B)
    (hRT : RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) c 0 (σ.arrs "R")) :
    ∃ σ', Run B dayLoop σ σ' ((((400 + 10 + 4) * PK + 6 + 60) + 10 + 4) * m + 6) ∧
      CEnv B arr n m P k PK σ' ∧ RInv B n PK R0 (σ'.arrs "R") ∧
      σ'.vars "cl" = c ∧ σ'.vars "jc" = R0.getD (PK + c) 0 ∧
      σ'.vars "ec" = arr.getD (3 + 2 * R0.getD (PK + c) 0) 0 ∧ σ'.vars "qic" + 8 < B ∧
      RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) c m (σ'.arrs "R") ∧
      σ'.out = σ.out ∧ σ'.arrs "TK" = σ.arrs "TK" ∧ ∀ y, y ∉ SDL → σ'.vars y = σ.vars y := by
  obtain ⟨hPle1, hPle2, -, -, hP0⟩ := h.P_le
  have hPK : PK = (n + 1) ^ m * (k + 1) := by rw [h.hPK, h.hP]
  have hmn : n ≤ m * n := Nat.le_mul_of_pos_left _ h.hm0
  have hPKB := h.hPKB
  have hmB : m + 8 < B := by
    have := h.hmnB
    have : m ≤ m * n := Nat.le_mul_of_pos_right _ h.hn0
    omega
  have hjcn : R0.getD (PK + c) 0 < n := hRv c hc
  have hpowle : ∀ i, i ≤ m → (n + 1) ^ i ≤ P := fun i hi => by
    rw [h.hP]; exact Nat.pow_le_pow_right (by omega) hi
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "dy" "m" dayBody
    (fun i σ' => CEnv B arr n m P k PK σ' ∧ RInv B n PK R0 (σ'.arrs "R") ∧
      σ'.vars "cl" = c ∧ σ'.vars "jc" = R0.getD (PK + c) 0 ∧
      σ'.vars "ec" = arr.getD (3 + 2 * R0.getD (PK + c) 0) 0 ∧ σ'.vars "pw" = (n + 1) ^ i ∧
      σ'.vars "qic" + 8 < B ∧ RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) c i (σ'.arrs "R") ∧
      σ'.out = σ.out ∧ σ'.arrs "TK" = σ.arrs "TK" ∧ ∀ y, y ∉ SDL → σ'.vars y = σ.vars y)
    ((400 + 10 + 4) * PK + 6 + 60) m σ h.vm
    (fun j σ' hq => hq.1.vm) (by decide) (by omega)
    ⟨h.congr (fun y hy => by
        have : y ≠ "dy" := fun e => cvars_frame hy (by simp [SDL, e])
        simp [Env.setVar, this]) (by simp [Env.setVar]),
      by simpa [Env.setVar] using hR, by simpa [Env.setVar] using hcl,
      by simpa [Env.setVar] using hjc, by simpa [Env.setVar] using hec,
      by simpa [Env.setVar] using hpw, by simpa [Env.setVar] using hqB,
      by simpa [Env.setVar] using hRT, by simp [Env.setVar], by simp [Env.setVar],
      fun y hy => by
        have : y ≠ "dy" := fun e => hy (by simp [SDL, e])
        simp [Env.setVar, this]⟩
    (fun j σ' v hq => ⟨hq.1.congr (fun y hy => by
        have : y ≠ "dy" := fun e => cvars_frame hy (by simp [SDL, e])
        simp [Env.setVar, this]) (by simp [Env.setVar]),
      by simpa [Env.setVar] using hq.2.1, by simpa [Env.setVar] using hq.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.1, by simpa [Env.setVar] using hq.2.2.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.2.2.1, by simpa [Env.setVar] using hq.2.2.2.2.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.2.2.2.2.1, by simpa [Env.setVar] using hq.2.2.2.2.2.2.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.2.2.2.2.2.2.1, fun y hy => by
        have : y ≠ "dy" := fun e => hy (by simp [SDL, e])
        simp only [Env.setVar, if_neg this]; exact hq.2.2.2.2.2.2.2.2.2.2 y hy⟩)
    (by
      intro i σ1 hq hdy hi
      obtain ⟨hC1, hR1, hcl1, hjc1, hec1, hpw1, hqB1, hRT1, hO1, hA1, hF1⟩ := hq
      have hpwle := hpowle i hi.le
      have hpwle2 := hpowle (i + 1) hi
      have hsw : SwEnv B arr n P k (n + 1) ((n + 1) ^ i) c (σ1.vars "qic") (σ1.vars "ec") PK σ1 :=
        hC1.sw hR1 hRv hcl1 hc hpw1 (by omega) rfl hqB1 rfl (by
          rw [hec1]; exact h.arr_lt (by
            have : R0.getD (PK + c) 0 < n := hjcn
            omega))
      have hidx : i * n + R0.getD (PK + c) 0 < m * n := by
        have h2 : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right _ hi
        have h3 : (i + 1) * n = i * n + n := by ring
        omega
      have hcells : ∀ x < PK, (σ1.arrs "R").getD x 0 = 1 → CellOk arr (σ1.arrs "R") n P k (n + 1)
          ((n + 1) ^ i) c (arr.getD (2 + 2 * (i * n + R0.getD (PK + c) 0)) 0) (σ1.vars "ec") PK B x := by
        intro x hx h1
        have hts : TS m k n (qF arr R0 PK n) (eOrd arr R0 PK) c i x := by
          have := hRT1 x (by rw [← hPK]; exact hx)
          rw [h1] at this
          by_contra hn'
          rw [if_neg hn'] at this
          omega
        have hRe : eOrd arr (σ1.arrs "R") PK = eOrd arr R0 PK := eOrd_congr _ _ _ _ hR1.ord
        have := cellOk_of_TS (arr := arr) (Rl := σ1.arrs "R") (B := B) (PK := PK) hc hi hts hPK hRe
          (h.sum_lt hRv hi hc)
        rw [← h.hP] at this
        rw [hec1]
        exact this
      have h01 : ∀ x < PK, (σ1.arrs "R").getD x 0 ≤ 1 := by
        intro x hx
        rw [hRT1 x (by rw [← hPK]; exact hx)]; split <;> omega
      have hpw2 : (n + 1) ^ i * (n + 1) + 8 < B := by
        rw [← pow_succ]; omega
      obtain ⟨σ2, r2, hsw2, hR2, hA2, hO2, hF2⟩ := dayBody_run (B := B) (m := m) σ1 hsw hP0 i
        (R0.getD (PK + c) 0) hdy (by rw [hC1.vn]) hjc1 hi hjcn h.hlen
        (fun j hj => h.arr_lt hj) h.hmnB hpw2 hcells h01
      obtain ⟨hRT2, hl2, hout2⟩ := RT_sweep (m := m) (k := k) (n := n) (q := qF arr R0 PK n)
        (e := eOrd arr R0 PK) (c := c) hc hi (σ1.arrs "R") (by rw [← hPK]; have := hR1.len; omega)
        hRT1
      have hRe : eOrd arr (σ1.arrs "R") PK = eOrd arr R0 PK := eOrd_congr _ _ _ _ hR1.ord
      have htgt : tgtM P k (n + 1) ((n + 1) ^ i) c
          (arr.getD (2 + 2 * (i * n + R0.getD (PK + c) 0)) 0) (σ1.vars "ec")
          (eOrd arr (σ1.arrs "R") PK) = tgt m k n (qF arr R0 PK n) (eOrd arr R0 PK) c i := by
        rw [hRe, h.hP]
        exact tgtM_eq rfl (by rw [hec1]; rfl)
      have hswe : σ2.arrs "R" = D3List.swRun ((n + 1) ^ m * (k + 1))
          (tgt m k n (qF arr R0 PK n) (eOrd arr R0 PK) c i) (σ1.arrs "R") := by
        rw [hR2, htgt, ← hPK]
      have hfr : ∀ y, y ∉ SDAY ++ ("jj" :: SSW) → σ2.vars y = σ1.vars y := hF2
      have hnot : ∀ {y : String}, y ∈ ["cl", "jc", "ec", "dy"] → y ∉ SDAY ++ ("jj" :: SSW) := by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        simp only [SDAY, SSW, S1, S2, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
        rcases hy with rfl | rfl | rfl | rfl <;> decide
      refine ⟨σ2, r2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩, ?_⟩
      · exact hC1.congr (fun y hy => hfr y (fun e => cvars_frame hy (List.mem_cons_of_mem _ e)))
          hA2
      · refine ⟨hsw2.hRlen, fun y hy => ?_, hsw2.hRB⟩
        rw [hswe, hout2 y (by rw [← hPK]; exact hy)]
        exact hR1.ord y hy
      · rw [hfr "cl" (hnot (by simp))]; exact hcl1
      · rw [hfr "jc" (hnot (by simp))]; exact hjc1
      · rw [hfr "ec" (hnot (by simp))]; exact hec1
      · rw [hsw2.vpw, pow_succ]
      · rw [hsw2.vqic]; exact h.arr_lt (by omega)
      · rw [hswe]; exact hRT2
      · rw [hO2]; exact hO1
      · rw [hA2]; exact hA1
      · have hy1 : y ∉ SDAY ++ ("jj" :: SSW) := fun e => hy (List.mem_cons_of_mem _ e)
        rw [hfr y hy1]; exact hF1 y hy
      · rw [hfr "dy" (hnot (by simp))]; exact hdy)
  obtain ⟨a1, a2, a3, a4, a5, -, a7, a8, a9, a10, a11⟩ := hQ
  exact ⟨σ', r, a1, a2, a3, a4, a5, a7, a8, a9, a10, a11⟩

/-- The body of the client loop: the day loop, then the collapse. -/
def clientBody : Com :=
  .seq (.assign "jc" (.get "R" (add (V "PK") (V "cl"))))
  (.seq (.assign "ec" (rd "jc" 1))
  (.seq (.assign "qic" (.lit 0))
  (.seq (.assign "pw" (.lit 1))
  (.seq dayLoop collLoop))))

/-- The scalars the client body assigns, besides its loop counter. -/
def SCL : List String := ["jc", "ec", "qic", "pw"] ++ SDL ++ ("cx" :: SCO)

lemma cvars_frame2 {y : String} (hy : y ∈ CVars) : y ∉ "cx" :: SCO := by
  simp only [CVars, SCO, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

set_option maxHeartbeats 12800000 in
/-- **One client of the dynamic program.** -/
theorem clientBody_run {arr : List ℕ} {n m P k PK c : ℕ} (R0 : List ℕ) (σ : Env)
    (h : CEnv B arr n m P k PK σ) (hR : RInv B n PK R0 (σ.arrs "R"))
    (hRv : ∀ c' < n, R0.getD (PK + c') 0 < n) (hc : c < n) (hcl : σ.vars "cl" = c)
    (hRT : RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) c 0 (σ.arrs "R")) :
    ∃ σ', Run B clientBody σ σ'
        ((((400 + 10 + 4) * PK + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * PK + 6)) ∧
      CEnv B arr n m P k PK σ' ∧ RInv B n PK R0 (σ'.arrs "R") ∧ σ'.vars "cl" = c ∧
      RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) (c + 1) 0 (σ'.arrs "R") ∧
      σ'.out = σ.out ∧ σ'.arrs "TK" = σ.arrs "TK" ∧ ∀ y, y ∉ "cl" :: SCL → σ'.vars y = σ.vars y := by
  obtain ⟨hPle1, hPle2, -, -, hP0⟩ := h.P_le
  have hPK : PK = (n + 1) ^ m * (k + 1) := by rw [h.hPK, h.hP]
  have hRl := hR.len
  have hPKB := h.hPKB
  have hmn : n ≤ m * n := Nat.le_mul_of_pos_left _ h.hm0
  have hlen := h.hlen
  have s1 := asg_R2 (B := B) "jc" "PK" "cl" σ PK c h.vPK hcl (by omega) (hR.small _) (by omega)
    (by omega) (by omega)
  set σ1 := σ.setVar "jc" ((σ.arrs "R").getD (PK + c) 0) with hσ1
  have hjc1 : σ1.vars "jc" = R0.getD (PK + c) 0 := by
    rw [show (σ.arrs "R").getD (PK + c) 0 = R0.getD (PK + c) 0 from hR.ord _ (by omega)] at hσ1
    simp [hσ1, Env.setVar]
  have hjcn : R0.getD (PK + c) 0 < n := hRv c hc
  have hA1 : σ1.arrs "TK" = arr := by simp [hσ1, Env.setVar, h.hA]
  have e1 := h.arr_lt (m := m) (arr := arr) (j := 2 + 2 * R0.getD (PK + c) 0 + 1) (by omega)
  have s2 := asg_tk (B := B) "jc" "ec" 1 σ1 arr (R0.getD (PK + c) 0) hA1 hjc1 (by omega) (by omega)
    (by omega)
  set σ2 := σ1.setVar "ec" (arr.getD (2 + 2 * R0.getD (PK + c) 0 + 1) 0) with hσ2
  have hec2 : σ2.vars "ec" = arr.getD (3 + 2 * R0.getD (PK + c) 0) 0 := by
    have e : 2 + 2 * R0.getD (PK + c) 0 + 1 = 3 + 2 * R0.getD (PK + c) 0 := by omega
    rw [e] at hσ2; simp [hσ2, Env.setVar]
  have hA2 : σ2.arrs "TK" = arr := by simp [hσ2, Env.setVar, hA1]
  have s3 := asgE (B := B) "qic" (.lit 0) σ2 (by simp [MisBlk.small]; omega)
  set σ3 := σ2.setVar "qic" (MisBlk.den σ2 (.lit 0)) with hσ3
  have hqic3 : σ3.vars "qic" = 0 := by simp [hσ3, MisBlk.den, Env.setVar]
  have s4 := asgE (B := B) "pw" (.lit 1) σ3 (by simp [MisBlk.small]; omega)
  set σ4 := σ3.setVar "pw" (MisBlk.den σ3 (.lit 1)) with hσ4
  have hpw4 : σ4.vars "pw" = 1 := by simp [hσ4, MisBlk.den, Env.setVar]
  have hcl4 : σ4.vars "cl" = c := by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hcl]
  have hjc4 : σ4.vars "jc" = R0.getD (PK + c) 0 := by
    simp [hσ4, hσ3, hσ2, Env.setVar, hjc1]
  have hec4 : σ4.vars "ec" = arr.getD (3 + 2 * R0.getD (PK + c) 0) 0 := by
    simp [hσ4, hσ3, Env.setVar, hec2]
  have hqB4 : σ4.vars "qic" + 8 < B := by
    have e : σ4.vars "qic" = σ3.vars "qic" := by simp [hσ4, Env.setVar]
    rw [e, hqic3]; omega
  have h4 : CEnv B arr n m P k PK σ4 := h.congr (fun y hy => by
    have hy' : y = "n" ∨ y = "m" ∨ y = "PK" ∨ y = "PP" ∨ y = "kp" ∨ y = "b1" ∨ y = "pk" := by
      simpa [CVars] using hy
    rcases hy' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [hσ4, hσ3, hσ2, hσ1, Env.setVar]) (by simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, h.hA])
  have hR4 : RInv B n PK R0 (σ4.arrs "R") := by
    simpa [hσ4, hσ3, hσ2, hσ1, Env.setVar] using hR
  have hRT4 : RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) c 0 (σ4.arrs "R") := by
    simpa [hσ4, hσ3, hσ2, hσ1, Env.setVar] using hRT
  obtain ⟨σ5, r5, hC5, hR5, hcl5, hjc5, hec5, hqB5, hRT5, hO5, hA5, hF5⟩ :=
    dayLoop_run (arr := arr) (R0 := R0) σ4 h4 hR4 hRv hc hcl4 hjc4 hec4 hpw4 hqB4 hRT4
  have hRK5 : PK ≤ (σ5.arrs "R").length := by have := hR5.len; omega
  have hRB5 : ∀ j, (σ5.arrs "R").getD j 0 < B := hR5.small
  have hcln : ClEnv B P k PK σ5 := ⟨hC5.vPP, hC5.vpk, hC5.hPK, hRK5, hRB5, by omega⟩
  obtain ⟨σ6, r6, hR6, hA6, hO6, hF6⟩ := collLoop_run (B := B) σ5 hcln hC5.vPK
  have hRK5' : (n + 1) ^ m * (k + 1) ≤ (σ5.arrs "R").length := by
    have := hRK5; rw [hC5.hPK, hC5.hP] at this; exact this
  obtain ⟨hRT6, hlen6, hout6⟩ := RT_collapse (m := m) (k := k) (n := n)
    (q := qF arr R0 PK n) (e := eOrd arr R0 PK) (c := c) hc (σ5.arrs "R") hRK5' hRT5
  have hPeq : P = (n + 1) ^ m := hC5.hP
  have hPKeq : PK = (n + 1) ^ m * (k + 1) := by rw [hC5.hPK, hPeq]
  have hReq : (List.foldl (fun A x => D3List.clStep P k x A) (σ5.arrs "R") (List.range PK)) =
      (List.foldl (fun A x => D3List.clStep ((n + 1) ^ m) k x A) (σ5.arrs "R")
        (List.range ((n + 1) ^ m * (k + 1)))) := by rw [hPeq, hPKeq]
  refine ⟨σ6, (s1.seq (s2.seq (s3.seq (s4.seq (r5.seq r6))))).mono (by simp [Expr.size]; omega), ?_,
    ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
  · exact hC5.congr (fun y hy => by rw [hF6 y (cvars_frame2 hy)]) hA6
  · refine ⟨by rw [hR6, hReq, hlen6]; exact hR5.len, fun y hy => ?_, fun j => ?_⟩
    · rw [hR6, hReq, hout6 y (by rw [← hPKeq]; exact hy)]
      exact hR5.ord y hy
    · by_cases hj : j < (n + 1) ^ m * (k + 1)
      · rw [hR6, hReq, hRT6 j hj]; split <;> omega
      · rw [hR6, hReq, hout6 j (by omega)]; exact hRB5 j
  · rw [hF6 "cl" (by simp [SCO])]
    rw [hF5 "cl" (by simp [SDL, SDAY, SSW, S1, S2])]
    exact hcl4
  · rw [hR6, hReq]; exact hRT6
  · rw [hO6]; exact hO5
  · rw [hA6]; exact hA5
  · have hy1 : y ≠ "cl" := fun e => hy (by simp [e])
    have hy2 : y ∉ "cx" :: SCO := fun e => hy (by
      simp only [SCL, List.mem_append, List.mem_cons] at e ⊢; tauto)
    rw [hF6 y hy2]
    have hy3 : y ∉ SDL := fun e => hy (by
      simp only [SCL, List.mem_append, List.mem_cons] at e ⊢; tauto)
    rw [hF5 y hy3]
    have hy4 : y ≠ "jc" := fun e => hy (by simp [SCL, e])
    have hy5 : y ≠ "ec" := fun e => hy (by simp [SCL, e])
    have hy6 : y ≠ "qic" := fun e => hy (by simp [SCL, e])
    have hy7 : y ≠ "pw" := fun e => hy (by simp [SCL, e])
    simp [hσ4, hσ3, hσ2, hσ1, Env.setVar, hy4, hy5, hy6, hy7]

/-- The client loop. -/
def clientLoop : Com := fLoop "cl" "n" clientBody

set_option maxHeartbeats 12800000 in
/-- **The whole of the dynamic program.** -/
theorem clientLoop_run {arr : List ℕ} {n m P k PK : ℕ} (R0 : List ℕ) (σ : Env)
    (h : CEnv B arr n m P k PK σ) (hR : RInv B n PK R0 (σ.arrs "R"))
    (hRv : ∀ c' < n, R0.getD (PK + c') 0 < n)
    (hRT : RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) 0 0 (σ.arrs "R")) :
    ∃ σ', Run B clientLoop σ σ'
        (((((((400 + 10 + 4) * PK + 6 + 60) + 10 + 4) * m + 6 + 60 +
          ((60 + 10 + 4) * PK + 6)) + 10 + 4) * n + 6)) ∧
      CEnv B arr n m P k PK σ' ∧ RInv B n PK R0 (σ'.arrs "R") ∧
      RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) n 0 (σ'.arrs "R") ∧
      σ'.out = σ.out ∧ σ'.arrs "TK" = σ.arrs "TK" ∧
      ∀ y, y ∉ "cl" :: SCL → σ'.vars y = σ.vars y := by
  have hnB : n + 1 < B := by have := h.hmnB; have : n ≤ m * n := Nat.le_mul_of_pos_left _ h.hm0; omega
  obtain ⟨σ', r, hQ⟩ := ILoop.iLoop_spec (B := B) "cl" "n" clientBody
    (fun j σ' => CEnv B arr n m P k PK σ' ∧ RInv B n PK R0 (σ'.arrs "R") ∧
      RT m k n (qF arr R0 PK n) (eOrd arr R0 PK) j 0 (σ'.arrs "R") ∧
      σ'.out = σ.out ∧ σ'.arrs "TK" = σ.arrs "TK" ∧ ∀ y, y ∉ "cl" :: SCL → σ'.vars y = σ.vars y)
    ((((400 + 10 + 4) * PK + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * PK + 6)) n σ h.vn
    (fun j σ' hq => hq.1.vn) (by decide) hnB
    ⟨h.congr (fun y hy => by
        have : y ≠ "cl" := fun e => by simp [CVars] at hy; rw [e] at hy; simp at hy
        simp [Env.setVar, this]) (by simp [Env.setVar]),
      by simpa [Env.setVar] using hR, by simpa [Env.setVar] using hRT,
      by simp [Env.setVar], by simp [Env.setVar], fun y hy => by
        have : y ≠ "cl" := fun e => hy (by simp [e])
        simp [Env.setVar, this]⟩
    (fun j σ' v hq => ⟨hq.1.congr (fun y hy => by
        have : y ≠ "cl" := fun e => by simp [CVars] at hy; rw [e] at hy; simp at hy
        simp [Env.setVar, this]) (by simp [Env.setVar]),
      by simpa [Env.setVar] using hq.2.1, by simpa [Env.setVar] using hq.2.2.1,
      by simpa [Env.setVar] using hq.2.2.2.1, by simpa [Env.setVar] using hq.2.2.2.2.1,
      fun y hy => by
        have : y ≠ "cl" := fun e => hy (by simp [e])
        simp only [Env.setVar, if_neg this]; exact hq.2.2.2.2.2 y hy⟩)
    (by
      intro j σ1 hq hjv hjn
      obtain ⟨hC1, hR1, hRT1, hO1, hA1, hF1⟩ := hq
      obtain ⟨σ2, r2, hC2, hR2, hcl2, hRT2, hO2, hA2, hF2⟩ :=
        clientBody_run (arr := arr) (R0 := R0) σ1 hC1 hR1 hRv hjn hjv hRT1
      refine ⟨σ2, r2, ⟨hC2, hR2, hRT2, hO2.trans hO1, hA2.trans hA1, fun y hy => ?_⟩, hcl2⟩
      have hy1 : y ∉ "cl" :: SCL := fun e => hy e
      rw [hF2 y hy1]; exact hF1 y hy1)
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hQ
  exact ⟨σ', r, a1, a2, a3, a4, a5, a6⟩

end Lax117284Proofs.Machine.D3Client
