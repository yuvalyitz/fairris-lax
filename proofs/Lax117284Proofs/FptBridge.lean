import Lax117284.ParameterizedComplexity
import Lax496464Proofs.WHierarchy.Machine.Compose.Strict

/-! Transfer the scheduling programs' unprefixed tape and polynomial fitting condition
into the archive's shared fixed-parameter time definition. -/

namespace Lax117284Proofs.FptBridge
open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax117284.ParameterizedComplexity
open Lax496464.WH_A1_FptTime
open Lax496464Proofs.WHierarchy.Machine.Compose.Programs
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate
open Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.ComputableBounds

theorem computable_pow₂ {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable fun x => f x ^ g x := by
  have h := Computable.nat_rec (f := g) (g := fun _ => 1)
    (h := fun a (p : ℕ × ℕ) => p.2 * f a) hg (Computable.const 1)
    (Primrec.nat_mul.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst)).to₂
  exact h.of_eq fun a => by
    induction g a with
    | zero => rfl
    | succ n ih => simpa [pow_succ] using congrArg (fun z => z * f a) ih

theorem computable_sum {f : ℕ → ℕ} (hf : Computable f) :
    Computable fun n => ∑ i ∈ Finset.range n, f i := by
  have h := Computable.nat_rec (f := id) (g := fun _ => 0)
    (h := fun _ (p : ℕ × ℕ) => p.2 + f p.1) Computable.id (Computable.const 0)
    (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.snd))).to₂
  exact h.of_eq fun n => by
    induction n with
    | zero => simp
    | succ n ih => simpa [Finset.sum_range_succ] using congrArg (fun z => z + f n) ih

theorem fits_of_bits {c w a : ℕ} {x : List ℕ}
    (hl : x.length < 2 ^ a) (he : ∀ v ∈ x, v < 2 ^ a)
    (hw : c * (a + 2) ≤ w) : Fits c w x := by
  intro v hv
  have hbase : x.length + v + 1 ≤ 2 ^ (a + 1) := by
    have := he v hv
    rw [pow_succ]; omega
  calc c * (x.length + v + 1) ^ c ≤ 2 ^ c * (2 ^ (a + 1)) ^ c :=
        Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ (c * (a + 2)) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw

theorem of_machine {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ}
    {prog : Program} {c : ℕ} {g : ℕ → ℕ} (hg : Computable g)
    (htime : ∀ w, ComputesInTime w prog {x | x ∈ D ∧ Fits c w x ∧ Fits c w (F x)} F
      (fun x => c * g (κ x) * (x.length + 1) ^ c))
    (hout : ∃ (e : ℕ → ℕ) (d : ℕ), Computable e ∧
      ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (e (κ x) * (bitSize x + 1) ^ d)) :
    FptTimeOn D κ F := by
  obtain ⟨e, d, he, hbd⟩ := hout
  let L := lits prog
  let f := fun k => (c + 10) * c * g k + (c + 1) * e k + 4 * c + L + 11
  have hf : Computable f := by
    dsimp [f]
    exact computable_add (computable_add (computable_add
      (computable_add (computable_mul (Computable.const _) hg)
        (computable_mul (Computable.const _) he)) (Computable.const _))
      (Computable.const _)) (Computable.const _)
  apply Lax496464Proofs.WHierarchy.Machine.RunsTo.fptTimeOn_of_runsTo
    (p := strip prog) (f := f) (d := c + d + 1) hf
  all_goals
    intro x hx
    let n := bitSize x
    let T := c * g (κ x) * (x.length + 1) ^ c
    let E := e (κ x) * (n + 1) ^ d
    let B := fptBound f (c + d + 1) (κ x) n
    have hn : x.length ≤ n := length_le_bitSize x
    have heX : ∀ v ∈ x, v < 2 ^ n := fun v hv => lt_two_pow_bitSize hv
    have heF : ∀ v ∈ F x, v < 2 ^ E := hbd x hx
    have hN : n + 1 ≤ (n + 1) ^ (c + d + 1) :=
      Nat.le_self_pow (by omega) _
    have hT : T ≤ c * g (κ x) * (n + 1) ^ (c + d + 1) :=
      Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) c).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
    have hE : E ≤ e (κ x) * (n + 1) ^ (c + d + 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have hOne : 1 ≤ (n + 1) ^ (c + d + 1) := Nat.one_le_pow _ _ (by omega)
    have key : (c + 10) * T + (c + 1) * E + c * (n + 2) + 2 * c + L + n + 10 ≤ B := by
      dsimp [B, fptBound, f]
      nlinarith
  · intro w hw
    change B ≤ w at hw
    have hlenF : (F x).length ≤ T := by
      let a := bitSize x + bitSize (F x)
      let W := c * (a + 2)
      have hfit (z : List ℕ) (hz : bitSize z ≤ a) : Fits c W z :=
        fits_of_bits
          ((length_le_bitSize z).trans_lt (Nat.lt_two_pow_self.trans_le
            (Nat.pow_le_pow_right (by omega) hz)))
          (fun v hv => (lt_two_pow_bitSize hv).trans_le (Nat.pow_le_pow_right (by omega) hz)) le_rfl
      obtain ⟨t, ht, hr⟩ := htime W x ⟨hx, hfit x (by dsimp [a]; omega), hfit (F x) (by dsimp [a]; omega)⟩
      exact (runsTo_length_le hr).trans ht
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 2 := ⟨w - 2, by omega⟩
    have hfx : Fits c v x := fits_of_bits (hn.trans_lt Nat.lt_two_pow_self) heX (by nlinarith)
    have hfF : Fits c v (F x) := fits_of_bits
      (hlenF.trans_lt (Nat.lt_two_pow_self.trans_le
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right T E))))
      (fun u hu => (heF u hu).trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_add_left E T)))
      (by nlinarith)
    obtain ⟨t, ht, hr⟩ := htime v x ⟨hx, hfx, hfF⟩
    have hl : lits prog < 2 ^ v := Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by omega) (by dsimp [L] at key; omega))
    have hxw : x.length + 1 < 2 ^ (v + 2) := (Nat.lt_two_pow_self (n := x.length + 1)).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega))
    obtain ⟨t', ht', hr'⟩ := strip_runsTo (by omega) hl hxw hr
    exact ⟨t', by dsimp [T] at key; nlinarith, hr'⟩
  · intro v hv
    exact (heF v hv).trans_le (Nat.pow_le_pow_right (by omega) (by nlinarith))

open Classical in
theorem decision {P : Problem} {prog : Program} {c : ℕ} {g : ℕ → ℕ}
    (hg : Computable g) (hd : Decides P prog c g) : FptDecision P := by
  apply of_machine hg (fun w x hx => hd w x ⟨hx.1, hx.2.1⟩)
  refine ⟨fun _ => 1, 0, Computable.const 1, ?_⟩
  intro x hx v hv
  split_ifs at hv <;> simp_all
end Lax117284Proofs.FptBridge
