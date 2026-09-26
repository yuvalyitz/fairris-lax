import Lax117284Proofs.Machine.TwNum12

/-!
The correctness of the main program on a word of the domain, with the bound and the cost of this
development.
-/

namespace Lax117284Proofs.Machine.TwNum

open Lax808846.Ram Lax117284.Scheduling Lax117284.InstanceEncoding Lax117284.ConflictGraph
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax117284.Bodlaender (EncodesGraph NiceDecomposition nodeCount)
open Lax117284Proofs.Machine.ClMain (Mx le_Mx)

variable {prog : Program} {ca cc plit : ℕ} {x : List ℕ}

open Classical in
/-- **The main program solves the problem on a word of the domain.** -/
theorem core (hax : AxStmt prog ca) (hca : 1 ≤ ca) (hcc : ca + 1 ≤ cc) (hpl1 : PLit prog ≤ plit)
    (hpl2 : ca ≤ plit) (hx : Dm x) :
    ∃ σ', Run (Bx prog ca cc plit x) (TwMain.mainCom prog cc plit)
        (initEnv (extx prog ca cc plit x) x) σ' (Kx prog ca cc x) ∧ σ'.out = fAnsT x := by
  have hx' : x ∈ UniformInstances := hx
  obtain ⟨I, k, hdec⟩ := hx'
  obtain ⟨y0, hxe, hy⟩ := id hdec
  have hn : nx x = I.clients := ClientsWord.x0 hdec
  have hm : mx x = I.days := ClientsWord.x1 hdec
  have hI : Ix x = I := Ix_eq hdec
  obtain ⟨z, t, ht, hcit0, hnice0, hnoTW, hnogd⟩ := core_key hax hca hcc hpl2 hx hxe hy hn hm
  obtain ⟨hL, hbr, hXB, hnB, hmB, hmnB, hgeB, hccB, hplB, hwpB, hPB⟩ :=
    B_unc (prog := prog) (ca := ca) (cc := cc) (plit := plit) hx
  have hw : wx cc x = TwPrep.wcnt cc I.days (Nat.log 2 x.length) - 1 := by
    unfold wx wcx lgx; rw [hm]
  have hgiff : (0 < TwPrep.wcnt cc I.days (Nat.log 2 x.length) ∧ 0 < I.days) ↔ gdx cc x := by
    unfold gdx wcx lgx; rw [hm]
  have hk : k ≤ Mx x := le_Mx (by rw [hxe]; simp)
  rw [hn] at hnB hmnB
  rw [hm] at hmB hmnB hgeB
  have hmain := TwMain.main_run (B := Bx prog ca cc plit x) hxe hy prog cc plit (by omega)
    (extx prog ca cc plit x) (Tbx ca cc x + 4) (Kdp ca cc x) z t
    (initEnv (extx prog ca cc plit x) x) rfl rfl ⟨fun a _ => rfl, fun v _ => rfl⟩
    (by simp [extx]) (by simp [extx, hn]) (by simp [extx]) (by simp [extx]) (by simp [extx])
    (by simp [extx]) (by simp [extx, Wpx, lgx]) (by simp [extx]) (by simp [extx, hm, hn])
    hL hbr hXB hnB hmB hmnB hgeB hccB hplB hwpB hPB
    (fun h => by
      have := gb_of hca hcc hx (hgiff.1 h) hpl1
      rw [hn, hm, hw] at this
      exact this)
    (fun h => by
      have hg := hgiff.1 h
      obtain ⟨hr, hzc⟩ := hcit0 hg
      rw [hn, hm, hw] at hr
      exact ⟨hr, by omega, hzc⟩)
    (fun D hD hz => by
      have hg : gdx cc x := by
        by_contra h
        have := hnogd h
        rw [this] at hz; simp at hz
      obtain ⟨-, hlen⟩ := hnice0 hg D hz
      have hDl := hD.length_eq
      have hN : nodeCount D ≤ Tbx ca cc x := by omega
      have hN3 : 3 * nodeCount D + 2 ≤ Tbx ca cc x := by omega
      exact dpb_of hca hcc hx hg hw.symm hy hD hn hm hk hN3 (dpCost_le hw.symm hy hD hm hN))
    (fun D h hz => by
      have := (hnice0 (hgiff.1 h) D hz).1
      rw [hw] at this; exact this)
  obtain ⟨σ', hrun, hout⟩ := hmain
  refine ⟨σ', hrun.mono (Kmain_le hI hn hm hgiff ht hnoTW), ?_⟩
  rw [hout, fAnsT_eq hdec]
  by_cases hK : I.HasKFairSchedule k <;> simp [hK]

end Lax117284Proofs.Machine.TwNum

