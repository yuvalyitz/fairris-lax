import Lax117284Proofs.Machine.D3Accept
import Lax117284Proofs.Machine.X1Final
import Lax117284Proofs.Machine.WrapR
import Lax117284Proofs.Machine.WrapRFinal
import Lax117284Proofs.Machine.BlockFinal

/-!
The reduction that decides day-independent due dates with a fixed number of days is
polynomial-time computable.
-/

namespace Lax117284Proofs.Machine.D3Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Problems Lax434930.PolynomialTime
open Lax117284Proofs.Codes Lax117284Proofs.Machine.Lists Lax117284Proofs.Machine.InstSem
open Lax117284Proofs.Machine.FreeSem Lax117284Proofs.Machine.FreeCheck Lax117284Proofs.Machine.T9Sem
open Lax117284Proofs.Machine.T9Comp1 Lax117284Proofs.Machine.T9Prog Lax117284Proofs.Machine.T9Accept
open Lax117284Proofs.Machine.T9Final Lax117284Proofs.Machine.X1Accept
open Lax117284Proofs.Machine.D3Sem (DID did_iff goodM reduceM reduceM_correct uniform_iff_good
  divmod_row)
open Lax117284Proofs.Machine.D3Accept
open Lax117284Proofs.Machine.D3Pow (checkM checkMLoop powCom KcheckM KpowCom)
open Lax117284Proofs.Machine.D3Did (didCom SDID)
open Lax117284Proofs.Machine.D3Rk (rkLoop rkOuter rkInner rkCntCom ddA SRKO SRKC)
open Lax117284Proofs.Machine.D3Day (dayBody SDAY)
open Lax117284Proofs.Machine.D3Client (dayLoop clientBody clientLoop SDL SCL CVars)
open Lax117284Proofs.Machine.D3Coll (collLoop collBody)
open Lax117284Proofs.Machine.D3Setup (scanLoop scanBody initR_run SSC)
open Lax117284Proofs.Machine.WrapR Lax117284Proofs.Machine.Bits Lax117284Proofs.Machine.BlockFinal
open Lax117284Proofs.D3DP Lax117284Proofs.D3Rank Lax117284Proofs.D3Prog Lax117284Proofs.D3Link
open Lax117284Proofs.X1Word (satF)

open scoped Classical

/-! ### The output of the reduction, as numbers -/

lemma encode_sat : Lax117284.TwoSatisfiability.encodeFormula satF = encodeNat 1 ++ encodeNat 0 := by
  simp [Lax117284.TwoSatisfiability.encodeFormula, satF]

/-! ### The condition read off the array agrees with the condition on the stream -/

section Congr

variable {arr ns : List ℕ} (hv : Valid arr) (hv2 : Valid ns)

/-- **A due date below `n`, on the array's stream, agrees with the one on `ns`'s.** -/
theorem ddI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {j : ℕ} (hj : j < ns.getD 0 0) :
    D3Prog.ddI (instOf arr hv) j = D3Prog.ddI (instOf ns hv2) j := by
  have ht2 : j < ns.getD 1 0 * ns.getD 0 0 := lt_of_lt_of_le hj (Nat.le_mul_of_pos_left _ hm1)
  have ht : j < arr.getD 1 0 * arr.getD 0 0 := by rw [h0, h1]; exact ht2
  have e1 := (instOf_pAt arr hv ht).2
  have e2 := (instOf_pAt ns hv2 ht2).2
  have hdiv1 : j / arr.getD 0 0 = 0 := by rw [h0]; exact Nat.div_eq_of_lt hj
  have hmod1 : j % arr.getD 0 0 = j := by rw [h0]; exact Nat.mod_eq_of_lt hj
  have hdiv2 : j / ns.getD 0 0 = 0 := Nat.div_eq_of_lt hj
  have hmod2 : j % ns.getD 0 0 = j := Nat.mod_eq_of_lt hj
  rw [hdiv1, hmod1] at e1
  rw [hdiv2, hmod2] at e2
  unfold D3Prog.ddI
  rw [e1, e2, hag (2 + 2 * j + 1) (by omega)]

/-- **The client at a position below `n`, on the array's stream, agrees with the one on `ns`'s.** -/
theorem ordI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {c : ℕ} (hc : c < ns.getD 0 0) :
    D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c := by
  have hcl : (instOf arr hv).clients = ns.getD 0 0 := h0
  unfold D3Prog.ordI
  rw [hcl]
  refine ordOf_congr hc (fun j hj => ?_)
  exact ddI_congr hv hv2 h0 h1 hag hm1 hj

/-- **The processing time of the client at a position, on the array's stream, agrees with the
one on `ns`'s.** -/
theorem qI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {i c : ℕ} (hi : i < ns.getD 1 0) (hc : c < ns.getD 0 0) :
    D3Prog.qI (instOf arr hv) i c = D3Prog.qI (instOf ns hv2) i c := by
  have hordlt : D3Prog.ordI (instOf ns hv2) c < ns.getD 0 0 := by
    have h := D3Prog.ordI_lt (I := instOf ns hv2) (c := c) hc
    have h' : D3Prog.ordI (instOf ns hv2) c < (instOf ns hv2).clients := h
    have hcl : (instOf ns hv2).clients = ns.getD 0 0 := rfl
    rwa [hcl] at h'
  have hordeq : D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c :=
    ordI_congr hv hv2 h0 h1 hag hm1 hc
  have ht2 : i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c < ns.getD 1 0 * ns.getD 0 0 :=
    cell_lt hi hordlt
  have ht : i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c < arr.getD 1 0 * arr.getD 0 0 := by
    rw [h0, h1, hordeq]; exact ht2
  have hidxeq : i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c =
      i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c := by rw [h0, hordeq]
  have e1 := (instOf_pAt arr hv ht).1
  have e2 := (instOf_pAt ns hv2 ht2).1
  have hdiv1 : (i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c) / arr.getD 0 0 = i := by
    rw [hidxeq, h0]; exact (divmod_row (by omega) hordlt).1
  have hmod1 : (i * arr.getD 0 0 + D3Prog.ordI (instOf arr hv) c) % arr.getD 0 0 =
      D3Prog.ordI (instOf arr hv) c := by
    rw [hidxeq, h0, hordeq]; exact (divmod_row (by omega) hordlt).2
  have hdiv2 : (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c) / ns.getD 0 0 = i :=
    (divmod_row (by omega) hordlt).1
  have hmod2 : (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c) % ns.getD 0 0 =
      D3Prog.ordI (instOf ns hv2) c := (divmod_row (by omega) hordlt).2
  rw [hdiv1, hmod1] at e1
  rw [hdiv2, hmod2] at e2
  unfold D3Prog.qI
  rw [e1, e2, hidxeq, hag (2 + 2 * (i * ns.getD 0 0 + D3Prog.ordI (instOf ns hv2) c)) (by omega)]

/-- **The due date of the client at a position, on the array's stream, agrees with the one on
`ns`'s.** -/
theorem eI_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hm1 : 0 < ns.getD 1 0) {c : ℕ} (hc : c < ns.getD 0 0) :
    D3Prog.eI (instOf arr hv) c = D3Prog.eI (instOf ns hv2) c := by
  have hordlt : D3Prog.ordI (instOf ns hv2) c < ns.getD 0 0 := by
    have h := D3Prog.ordI_lt (I := instOf ns hv2) (c := c) hc
    have h' : D3Prog.ordI (instOf ns hv2) c < (instOf ns hv2).clients := h
    have hcl : (instOf ns hv2).clients = ns.getD 0 0 := rfl
    rwa [hcl] at h'
  have hordeq : D3Prog.ordI (instOf arr hv) c = D3Prog.ordI (instOf ns hv2) c :=
    ordI_congr hv hv2 h0 h1 hag hm1 hc
  unfold D3Prog.eI
  rw [hordeq]
  exact ddI_congr hv hv2 h0 h1 hag hm1 hordlt

/-- **A fair schedule on the array's stream exists exactly when one exists on `ns`'s.** -/
theorem hasKFair_congr (h0 : arr.getD 0 0 = ns.getD 0 0) (h1 : arr.getD 1 0 = ns.getD 1 0)
    (hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0)
    (hda : (instOf arr hv).DayIndepD) (hdn : (instOf ns hv2).DayIndepD) (hm1 : 0 < ns.getD 1 0)
    (k : ℕ) : (instOf arr hv).HasKFairSchedule k ↔ (instOf ns hv2).HasKFairSchedule k := by
  have hclA : (instOf arr hv).clients = arr.getD 0 0 := rfl
  have hdayA : (instOf arr hv).days = arr.getD 1 0 := rfl
  have hclN : (instOf ns hv2).clients = ns.getD 0 0 := rfl
  have hdayN : (instOf ns hv2).days = ns.getD 1 0 := rfl
  have hmA : 0 < (instOf arr hv).days := by rw [hdayA, h1]; exact hm1
  have hmN : 0 < (instOf ns hv2).days := by rw [hdayN]; exact hm1
  have hA := D3Prog.hasKFair_iff_reach hda hmA k
  have hN := D3Prog.hasKFair_iff_reach hdn hmN k
  rw [hdayA, hclA] at hA
  rw [hdayN, hclN] at hN
  rw [hA, hN, h1, h0,
    D3Link.reach_eq (fun i hi c hc => qI_congr hv hv2 h0 h1 hag hm1 hi hc)
      (fun c hc => eI_congr hv hv2 h0 h1 hag hm1 hc)]

end Congr

/-- **The array's own instance is fair exactly when the stream's is, once the counts and the
values below the table's length agree.** -/
theorem decideOk_congr (m : ℕ) (hm0 : 0 < m) (arr ns : List ℕ) (h : arr.take ns.length = ns)
    (hs : Shape eU ns) : decideOk arr m ↔ decideOk ns m := by
  have hg := getD_eq_of_take h
  obtain ⟨h2, hl⟩ := hs
  simp only [eU] at hl
  have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
  have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
  have hag : ∀ k < 3 + 2 * (ns.getD 1 0 * ns.getD 0 0), arr.getD k 0 = ns.getD k 0 :=
    fun k hk => hg k (by omega)
  have hpar : paramOf arr = paramOf ns := by unfold paramOf; rw [h0, h1]; exact hg _ (by omega)
  have hValidIff : Valid arr ↔ Valid ns := by
    unfold Valid; rw [h0, h1]
    constructor
    · intro hVa t ht
      have e1 := hag (2 + 2 * t) (by omega)
      have e2 := hag (2 + 2 * t + 1) (by omega)
      have := hVa t ht
      rwa [e1, e2] at this
    · intro hVn t ht
      have e1 := hag (2 + 2 * t) (by omega)
      have e2 := hag (2 + 2 * t + 1) (by omega)
      rw [e1, e2]; exact hVn t ht
  have hDIDIff : DID arr ↔ DID ns := by
    unfold DID; rw [h0, h1]
    constructor
    · intro hDa t ht
      have hmle : t % ns.getD 0 0 ≤ t := Nat.mod_le _ _
      have e1 := hag (2 + 2 * t + 1) (by omega)
      have e2 := hag (2 + 2 * (t % ns.getD 0 0) + 1) (by omega)
      have := hDa t ht
      rwa [e1, e2] at this
    · intro hDn t ht
      have hmle : t % ns.getD 0 0 ≤ t := Nat.mod_le _ _
      have e1 := hag (2 + 2 * t + 1) (by omega)
      have e2 := hag (2 + 2 * (t % ns.getD 0 0) + 1) (by omega)
      rw [e1, e2]; exact hDn t ht
  unfold decideOk
  constructor
  · rintro ⟨hv, hdid, hm', hk⟩
    have hv2 : Valid ns := hValidIff.mp hv
    have hdid2 : DID ns := hDIDIff.mp hdid
    have hm'2 : ns.getD 1 0 = m := by rw [← h1]; exact hm'
    have hm1 : 0 < ns.getD 1 0 := by rw [hm'2]; exact hm0
    have hda : (instOf arr hv).DayIndepD := (did_iff arr hv).2 hdid
    have hdn : (instOf ns hv2).DayIndepD := (did_iff ns hv2).2 hdid2
    refine ⟨hv2, hdid2, hm'2, ?_⟩
    rw [← hpar]
    exact (hasKFair_congr hv hv2 h0 h1 hag hda hdn hm1 _).1 hk
  · rintro ⟨hv2, hdid2, hm', hk⟩
    have hv : Valid arr := hValidIff.mpr hv2
    have hdid : DID arr := hDIDIff.mpr hdid2
    have hm1 : 0 < ns.getD 1 0 := by rw [hm']; exact hm0
    have hda : (instOf arr hv).DayIndepD := (did_iff arr hv).2 hdid
    have hdn : (instOf ns hv2).DayIndepD := (did_iff ns hv2).2 hdid2
    refine ⟨hv, hdid, by rw [h1]; exact hm', ?_⟩
    rw [hpar]
    exact (hasKFair_congr hv hv2 h0 h1 hag hda hdn hm1 _).2 hk

/-! ### The cost of the accepting phase is monotone -/

lemma KaccDPos_mono (m Sz : ℕ) {a b : ℕ} (h : a ≤ b) : KaccDPos m Sz a ≤ KaccDPos m Sz b := by
  unfold KaccDPos
  gcongr

/-! ### The reduction, as a `WrapR` -/

lemma nk_warrs' : "R" ∉ (UNk.nkU).warrs := by simp [UNk.nkU, Com.warrs]

open Classical in
/-- **The reduction to the numbers with day-independent due dates and `m` days.** -/
noncomputable def W (m : ℕ) (hm0 : 0 < m) : WrapR where
  Rext := fun L => 2 ^ (2 * L + 4)
  E := EI eU
  Sh := Shape eU
  nk := UNk.nkU
  Knk := 60
  nk_warrs := nk_warrs'
  hnk := fun B Bt cap hB => UNk.nkU_spec (B := B) Bt cap hB
  hconf := fun ns hs => conforms_of_shape eU hs
  hshape := fun ts h => shape_of_conforms eU h
  red := reduceM m
  cond := fun ns => decideOk ns m
  outW := fun _ => Lax117284.TwoSatisfiability.encodeFormula satF
  sem_acc := fun ns hshS hc => by
    have hmem : numCode ns ∈ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) := by
      obtain ⟨hv, hdid, hgetm, hk⟩ := hc
      exact (uniform_iff_good m (numCode ns)).2 ⟨ns, rfl, hshS, hv, ⟨hdid, hgetm⟩, hk⟩
    unfold reduceM
    rw [if_pos hmem]
  rejW := Lax117284.TwoSatisfiability.encodeFormula Lax117284.TwoSatisfiability.unsatisfiable
  sem_rej := fun w hnex => by
    have hnot : w ∉ Uniform (fun I _ => I.DayIndepD ∧ I.days = m) := fun hmem => by
      obtain ⟨ns, hw, hshS, hv, ⟨hdid, hgetm⟩, hk⟩ := (uniform_iff_good m w).1 hmem
      exact hnex ⟨ns, hw, hshS, hv, hdid, hgetm, hk⟩
    unfold reduceM
    rw [if_neg hnot]
  rej := rejT9
  Krej := Krej9
  rejRun := fun B Sz σ hs hB => rejT9_run (B := B) Sz σ hs hB
  acc := acceptDPos m
  Kacc := KaccDPos m
  Kmono := fun Sz a b h => KaccDPos_mono m Sz h
  accRun := fun B Sz L ns arr σ hsh harr hA hR hlenL hvals hB hs => by
    have hg := getD_eq_of_take harr
    have hlenA : ns.length ≤ arr.length := by
      have := congrArg List.length harr
      rw [List.length_take] at this; omega
    obtain ⟨h2, hl⟩ := hsh
    simp only [eU] at hl
    have h0 : arr.getD 0 0 = ns.getD 0 0 := hg 0 (by omega)
    have h1 : arr.getD 1 0 = ns.getD 1 0 := hg 1 (by omega)
    have hpow1 : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by ring
    have hpow2 : (2 : ℕ) ^ (2 * L + 4) = 16 * (2 ^ L * 2 ^ L) := by ring
    have hPP : 2 ^ L ≤ 2 ^ L * 2 ^ L := Nat.le_mul_of_pos_right _ (by positivity)
    have hLt : L < 2 ^ L := Nat.lt_two_pow_self
    have hval : ∀ k < ns.length, ns.getD k 0 < 2 ^ (L + 1) := fun k hk => by
      rw [List.getD_eq_getElem _ _ hk]; exact hvals _ (List.getElem_mem hk)
    have hE : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), arr.getD k 0 + 8 < B := fun k hk => by
      rw [h0, h1] at hk
      rw [hg k (by omega)]
      have := hval k (by omega)
      omega
    have hn : arr.getD 0 0 < 2 ^ (L + 1) := by rw [h0]; exact hval 0 (by omega)
    have hm : arr.getD 1 0 < 2 ^ (L + 1) := by rw [h1]; exact hval 1 (by omega)
    have hl' : ns.length = 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) := by rw [h0, h1]; omega
    have hmnL : arr.getD 1 0 * arr.getD 0 0 < 2 ^ L := by omega
    have hnn : arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hn.le hn.le
    have hmm : arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hm.le hm.le
    have hpp2 : (2 : ℕ) ^ (L + 1) * 2 ^ (L + 1) = 4 * (2 ^ L * 2 ^ L) := by ring
    have hC1 : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 ≤ 2 ^ L * 2 ^ (L + 1) :=
      Nat.mul_le_mul hmnL.le hn.le
    have hC2 : arr.getD 0 0 * arr.getD 1 0 * arr.getD 1 0 ≤ 2 ^ L * 2 ^ (L + 1) := by
      rw [Nat.mul_comm (arr.getD 0 0) (arr.getD 1 0)]
      exact Nat.mul_le_mul hmnL.le hm.le
    have hpp3 : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
    have htq : arr.getD 0 0 * arr.getD 1 0 ≤ 2 ^ L := by rw [Nat.mul_comm]; omega
    have hkp : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 < 2 ^ (L + 1) := by
      rw [hg _ (by omega)]; exact hval _ (by omega)
    have hkn : arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 * arr.getD 0 0 ≤
        2 ^ (L + 1) * 2 ^ (L + 1) := Nat.mul_le_mul hkp.le hn.le
    have hlm : arr.getD 1 0 * arr.getD 0 0 ≤ ns.length := by omega
    -- the day-count-cubed and doubled-coefficient bounds
    have hCU : arr.getD 1 0 * arr.getD 0 0 * arr.getD 0 0 +
        arr.getD 1 0 * arr.getD 0 0 + 8 < B := by omega
    have hE2 : ∀ k < 3 + 2 * (arr.getD 1 0 * arr.getD 0 0), 2 * arr.getD k 0 + 16 < B :=
      fun k hk => by
        rw [h0, h1] at hk
        rw [hg k (by omega)]
        have := hval k (by omega)
        omega
    -- the polynomial fit of the power of a fixed number of days, once the day count matches
    have hPPle : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m ≤ 2 ^ L := fun hgm => by
      rcases Nat.eq_zero_or_pos (arr.getD 0 0) with hn0 | hn0
      · rw [hn0]
        have : (0:ℕ) < 2 ^ L := by positivity
        simp only [Nat.zero_add, one_pow]
        omega
      · have hshape : 3 + 2 * (arr.getD 1 0 * arr.getD 0 0) ≤ L := by rw [← hl']; exact hlenL
        have hshape2 : 3 + 2 * (m * arr.getD 0 0) ≤ L := by rw [← hgm]; exact hshape
        have hle : m ≤ m * arr.getD 0 0 := Nat.le_mul_of_pos_right _ hn0
        have hbase : arr.getD 0 0 + 1 ≤ 2 ^ (arr.getD 0 0 + 1) := (Nat.lt_two_pow_self).le
        have hppbound : (arr.getD 0 0 + 1) ^ m ≤ (2 ^ (arr.getD 0 0 + 1) : ℕ) ^ m :=
          Nat.pow_le_pow_left hbase m
        have hexp : (2 ^ (arr.getD 0 0 + 1) : ℕ) ^ m = 2 ^ (m * arr.getD 0 0 + m) := by
          rw [← pow_mul]; congr 1; ring
        have hfinal : (2 : ℕ) ^ (m * arr.getD 0 0 + m) ≤ 2 ^ L :=
          Nat.pow_le_pow_right (by omega) (by omega)
        rw [hexp] at hppbound
        omega
    have hPPB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m + 8 < B := fun hgm => by
      have h1' := hPPle hgm
      have h2' : (2 : ℕ) ^ L ≤ 2 ^ (2 * L + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hPKB : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 + 8 < B :=
      fun hgm => by
        have h1' := hPPle hgm
        have h3' : (arr.getD 0 0 + 1) ^ m *
            (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) ≤ 2 ^ L * 2 ^ (L + 1) :=
          Nat.mul_le_mul h1' (by omega)
        have h4' : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
        omega
    have hRlen : arr.getD 1 0 = m → (arr.getD 0 0 + 1) ^ m *
        (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) + arr.getD 0 0 ≤
        (σ.arrs "R").length := fun hgm => by
      have hlen' : (σ.arrs "R").length = 2 ^ (2 * L + 4) := by
        rw [hR]; simp
      have h1' := hPPle hgm
      have h3' : (arr.getD 0 0 + 1) ^ m *
          (arr.getD (2 + 2 * (arr.getD 1 0 * arr.getD 0 0)) 0 + 1) ≤ 2 ^ L * 2 ^ (L + 1) :=
        Nat.mul_le_mul h1' (by omega)
      have h4' : (2 : ℕ) ^ L * 2 ^ (L + 1) = 2 * (2 ^ L * 2 ^ L) := by ring
      rw [hlen']
      omega
    have hR0zero : ∀ j, (σ.arrs "R").getD j 0 = 0 := fun j => by rw [hR]; simp
    have hRB : ∀ j, (σ.arrs "R").getD j 0 < B := fun j => by
      rw [hR0zero j]; omega
    have houtEq : natBits (Lax117284.TwoSatisfiability.encodeFormula satF) =
        bitsNat 1 ++ bitsNat 0 := by
      rw [encode_sat]
      simp only [T9Comp1.natBits_app, natBits_encodeNat]
    obtain ⟨σ', r, o⟩ := acceptDPos_run m hm0 Sz ns.length arr σ hs hE (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hCU hE2 hlm hA
      hPPB hPKB hRlen hR0zero hRB
    refine ⟨σ', r, ?_⟩
    rw [o]
    congr 1
    by_cases hc : decideOk ns m
    · have hca : decideOk arr m := (decideOk_congr m hm0 arr ns harr ⟨h2, hl⟩).2 hc
      rw [if_pos hca, if_pos hc, houtEq]
    · have hca : ¬ decideOk arr m := fun h => hc ((decideOk_congr m hm0 arr ns harr ⟨h2, hl⟩).1 h)
      rw [if_neg hca, if_neg hc]

/-! ### The layout and the polynomial bound -/

/-- The layout the machine of the reduction runs in. -/
abbrev layoutD3 : Layout :=
  ⟨["L", "rt", "rv", "Ln", "pw", "ph", "val", "i", "T", "p", "c", "kind", "j", "n3", "tv", "n",
    "m", "N", "N2", "m1", "g", "kp", "ok", "d", "b3", "v", "s", "u", "i2", "ix", "aa", "M",
    "k1", "nn", "mm", "V1", "C1", "C2", "CC", "tq", "ci", "cr", "j1", "j2", "tt", "x1", "x2", "pa",
    "da", "pb", "db", "cj", "r2", "i1", "CU",
    "PK", "PP", "b1", "cl", "cx", "dj", "dq", "dy", "ec", "fnd", "ix2", "jc", "jj", "mc", "pk",
    "qic", "sc", "dg", "dm", "dp", "dq2", "dr", "dw", "fvv", "sm", "ss", "tp", "tt2", "xx", "yy",
    "jd"], ["a", "TK", "R"], 12⟩

lemma powCom_ok (hPP : "PP" ∈ layoutD3.scalars) (hb1 : "b1" ∈ layoutD3.scalars)
    (hT : 0 < layoutD3.temps) : ∀ k, Com.Ok layoutD3 (powCom k) := by
  intro k
  induction k with
  | zero => simp [powCom, Com.Ok, Expr.Ok, hPP]
  | succ k ih => simp [powCom, Com.Ok, Expr.Ok, ih, hPP, hb1, hT]

lemma checkMLoop_ok (hmc : "mc" ∈ layoutD3.scalars) (hok : "ok" ∈ layoutD3.scalars)
    (hT : 1 < layoutD3.temps) : ∀ d, Com.Ok layoutD3 (checkMLoop d) := by
  have hT0 : 0 < layoutD3.temps := by omega
  intro d
  induction d with
  | zero => simp [checkMLoop, Com.Ok, Cond.Ok, condExpr, Expr.Ok, hmc, hok, hT, hT0]
  | succ d ih => simp [checkMLoop, Com.Ok, Cond.Ok, condExpr, Expr.Ok, hmc, hok, hT, hT0, ih]

theorem com_ok (m : ℕ) (hm0 : 0 < m) : Com.Ok layoutD3 (W m hm0).mainW := by
  have hPow := powCom_ok (by simp [layoutD3]) (by simp [layoutD3]) (by simp [layoutD3]) m
  have hChk := checkMLoop_ok (by simp [layoutD3]) (by simp [layoutD3]) (by simp [layoutD3]) m
  simp [WrapR.mainW, W, ReadAll.readAll, ReadAll.readLoop, ReadAll.readBody, UNk.nkU,
    TokRun.tokRun, TokRun.reset, TokLoop.scanLoop, TokLoop.scanBody, TokLoop.readBit,
    TokProg.dispatch, TokProg.put, TokProg.reset, TokProg.startDigits, TokProg.digit,
    acceptDPos, gateK, dpBody, fixOk, printZ, prepT, rejT9, checkM, hChk, hPow,
    didCom, D3Did.didBody, D3Did.SDID, rkLoop, D3Rk.rkOuter, D3Rk.rkInner, D3Rk.rkCntCom,
    clientLoop, D3Client.clientBody, D3Client.dayLoop, D3Day.dayBody, D3Coll.collLoop,
    D3Coll.collBody, D3Setup.scanLoop, D3Setup.scanBody, FoldLoop.fLoop,
    D3Sweep.sweepLoop, D3Sweep.sweepBody, D3Sweep.sweepServe, D3Sweep.sweepTry,
    D3Sweep.sweepSet, D3Sweep.seg1, D3Sweep.seg2,
    FreeCheck.okLoop, FreeCheck.okBody, FreeCheck.okChk,
    Out.outLoop, Out.emitTK, Out.emitAt, Out.emitVal, Out.emitVar, Out.emitLit, EmitNat.emitNat,
    EmitNat.sizeLoop, EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop,
    EmitNat.digBody, layoutD3, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

lemma KcheckMLoop_le (d : ℕ) :
    Lax117284Proofs.Machine.D3Pow.KcheckMLoop d ≤ 24 * d + 20 := by
  induction d with
  | zero => simp [Lax117284Proofs.Machine.D3Pow.KcheckMLoop]
  | succ d ih =>
    show Lax117284Proofs.Machine.D3Pow.KcheckMLoop (d + 1) ≤ 24 * (d + 1) + 20
    unfold Lax117284Proofs.Machine.D3Pow.KcheckMLoop
    simp only [Expr.size]
    omega

lemma KcheckM_le (m : ℕ) : KcheckM m ≤ 24 * m + 22 := by
  unfold KcheckM
  have := KcheckMLoop_le m
  simp only [Expr.size]
  omega

lemma KpowCom_le (k : ℕ) : KpowCom k ≤ 4 * k + 2 := by
  induction k with
  | zero => simp [KpowCom]
  | succ k ih =>
    show KpowCom (k + 1) ≤ 4 * (k + 1) + 2
    unfold KpowCom
    simp only [Expr.size]
    omega

theorem Kpoly (m : ℕ) (hm0 : 0 < m) :
    ∀ Sz l, (W m hm0).Kacc Sz l ≤ (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by
  intro Sz l
  show KaccDPos m Sz l ≤ _
  unfold KaccDPos Krej9
  have hck := KcheckM_le m
  have hpc := KpowCom_le m
  have h2 : (l + 1) ^ m * (l + 1) ≤ (l + 1) ^ (m + 3) := by
    calc (l + 1) ^ m * (l + 1) = (l + 1) ^ (m + 1) := (pow_succ _ _).symm
      _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (l + 1) ^ m ≤ (l + 1) ^ (m + 3) := by
    have : (l + 1) ^ m ≤ (l + 1) ^ m * (l + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hPl : (l + 1) ^ m * l ≤ (l + 1) ^ (m + 3) :=
    le_trans (Nat.mul_le_mul_left _ (by omega)) h2
  have hl1 : l ≤ (l + 1) ^ (m + 3) := by
    have : l + 1 ≤ (l + 1) ^ (m + 3) := by
      calc l + 1 = (l + 1) ^ 1 := (pow_one _).symm
        _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hl2 : l * l ≤ (l + 1) ^ (m + 3) := by
    calc l * l ≤ (l + 1) * (l + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (l + 1) ^ 2 := (sq (l + 1)).symm
      _ ≤ (l + 1) ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX3pos : 1 ≤ (l + 1) ^ (m + 3) := Nat.one_le_pow _ _ (by omega)
  have hAm : m ≤ (m + 1) * (m + 1) := by nlinarith
  have hA1 : 1 ≤ (m + 1) * (m + 1) := by nlinarith
  have hAm1 : m + 1 ≤ (m + 1) * (m + 1) := by nlinarith
  have hTeq : ((((((400 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6 + 60) + 10 + 4) * m + 6 + 60 + ((60 + 10 + 4) * ((l + 1) ^ m * (m + 1)) + 6)) + 10 + 4) * l + 6) =
      ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l) + (80 * m + 86) * l + 6 := by ring
  have hc : (414 * m + 74) * (m + 1) ≤ 500 * ((m + 1) * (m + 1)) := by nlinarith
  have hTb : ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l) ≤
      500 * ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    calc ((414 * m + 74) * (m + 1)) * ((l + 1) ^ m * l)
        ≤ (500 * ((m + 1) * (m + 1))) * ((l + 1) ^ m * l) := Nat.mul_le_mul_right _ hc
      _ ≤ (500 * ((m + 1) * (m + 1))) * (l + 1) ^ (m + 3) := Nat.mul_le_mul_left _ hPl
  have hml : m * l ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) := Nat.mul_le_mul (by omega) hl1
  have hAX : (l + 1) ^ (m + 3) ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmA : (m + 1) * (l + 1) ^ (m + 3) ≤ ((m + 1) * (m + 1)) * (l + 1) ^ (m + 3) :=
    Nat.mul_le_mul_right _ hAm1
  have hmA0 : m ≤ (m + 1) * (l + 1) ^ (m + 3) := by nlinarith
  have hsum : ((l + 1) ^ (m + 3) + Sz) ≤ (Sz + 1) * (l + 1) ^ (m + 3) := by nlinarith [hX3pos]
  have hbig : (100000 * ((m + 1) * (m + 1))) * ((l + 1) ^ (m + 3) + Sz) ≤
      (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by
    calc (100000 * ((m + 1) * (m + 1))) * ((l + 1) ^ (m + 3) + Sz) ≤
        (100000 * ((m + 1) * (m + 1))) * ((Sz + 1) * (l + 1) ^ (m + 3)) :=
          Nat.mul_le_mul_left _ hsum
      _ = (100000 * ((m + 1) * (m + 1))) * (Sz + 1) * (l + 1) ^ (m + 3) := by ring
  have hSzA : Sz ≤ ((m + 1) * (m + 1)) * Sz := Nat.le_mul_of_pos_left _ (by omega)
  rw [hTeq]
  nlinarith [hck, hpc, h1, hPl, hl1, hl2, hX3pos, hTb, hml, hAX, hmA, hmA0, hbig, hSzA,
    Nat.zero_le Sz, Nat.zero_le l, Nat.zero_le m, Nat.zero_le ((l + 1) ^ (m + 3))]

/-- **The reduction that decides day-independent due dates with a fixed positive number of days
is polynomial-time computable.** -/
theorem reduceM_polyTime (m : ℕ) (hm0 : 0 < m) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (reduceM m)) :=
  WrapRFinal.polyTimeE (W m hm0) layoutD3 (com_ok m hm0) (by simp [layoutD3]) (by simp [layoutD3])
    (100000 * ((m + 1) * (m + 1))) (m + 3) (by omega) (Kpoly m hm0) (fun Sz => by
      show 6 * (48 * Sz + 50) + 20 ≤ (100000 * ((m + 1) * (m + 1))) * (Sz + 1)
      have hA1 : 1 ≤ (m + 1) * (m + 1) := by nlinarith
      nlinarith [Nat.zero_le Sz, Nat.zero_le m, Nat.mul_le_mul_left (100000 * (Sz + 1)) hA1])

end Lax117284Proofs.Machine.D3Final
