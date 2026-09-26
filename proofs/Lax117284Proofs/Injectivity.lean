import Lax117284Proofs.Codes
import Lax117284.InstanceEncoding
import Lax117284.TwoSatisfiability

/-!
A word determines the instance it encodes, together with the fairness parameters after it.
-/

namespace Lax117284Proofs.Injectivity

open Lax117284.Scheduling Lax117284.Problems Lax117284Proofs.Codes Lax434930.PolynomialTime

/-- **The code of an instance is prefix-free.** -/
theorem encodeInstance_prefixFree {I I' : Instance} {x y : Word}
    (h : encodeInstance I ++ x = encodeInstance I' ++ y) : I = I' ∧ x = y := by
  obtain ⟨n, m, p, d, hp, hd⟩ := I
  obtain ⟨n', m', p', d', hp', hd'⟩ := I'
  simp only [encodeInstance, List.append_assoc] at h
  obtain ⟨hn, h⟩ := encodeNat_prefixFree _ _ _ _ h
  obtain ⟨hm, h⟩ := encodeNat_prefixFree _ _ _ _ h
  subst hn; subst hm
  have hc := (natPair_prefixFree.fin n).fin m
  obtain ⟨hf, hxy⟩ := flatMap_inj (natPair_prefixFree.fin n) m
    (fun i j => (p i j, d i j)) (fun i j => (p' i j, d' i j)) x y (by simpa using h)
  have hpp : p = p' := funext fun i => funext fun j => by
    have := congrFun (congrFun hf i) j; simp only [Prod.mk.injEq] at this; exact this.1
  have hdd : d = d' := funext fun i => funext fun j => by
    have := congrFun (congrFun hf i) j; simp only [Prod.mk.injEq] at this; exact this.2
  subst hpp; subst hdd
  exact ⟨rfl, hxy⟩

/--
---
conclusion: Lax117284.Problems.encodeUniform_inj
---
The code of an instance is prefix-free, and the number after it is the code of a number.
-/
theorem encodeUniform_inj {I I' : Instance} {k k' : ℕ}
    (h : encodeUniform I k = encodeUniform I' k') : I = I' ∧ k = k' := by
  obtain ⟨hI, hk⟩ := encodeInstance_prefixFree h
  exact ⟨hI, encodeNat_injective hk⟩

/--
---
conclusion: Lax117284.Problems.encodePerClient_inj
---
The code of an instance is prefix-free, and the parameters after it are as many codes of
numbers as it has clients.
-/
theorem encodePerClient_inj {I I' : Instance} {k : Fin I.clients → ℕ}
    {k' : Fin I'.clients → ℕ} (h : encodePerClient I k = encodePerClient I' k') :
    I = I' ∧ HEq k k' := by
  obtain ⟨hI, hk⟩ := encodeInstance_prefixFree h
  subst hI
  obtain ⟨hkk, -⟩ := flatMap_inj encodeNat_prefixFree I.clients k k' [] [] (by simpa using hk)
  exact ⟨rfl, heq_of_eq hkk⟩

/-! ### The rejected words -/

theorem blocked_not_fair (k : Fin blocked.clients → ℕ) (hk : ∀ j, k j = 1) :
    ¬ blocked.HasFairSchedule k := by
  rintro ⟨σ, -, hfair⟩
  have h := hfair ⟨0, by decide⟩
  have hz : Instance.served σ ⟨0, by decide⟩ = 0 := by
    simp only [Instance.served]
    exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i _ => i.elim0)
  rw [hk, hz] at h
  omega

/--
---
conclusion: Lax117284.Problems.rejected_notMem
---
An instance with no day serves nobody, and the word is the code of one such instance with
the fairness parameter `1`, whichever instance and parameter a word of the language is the
code of.
-/
theorem rejected_notMem (C : Instance → ℕ → Prop) : rejected ∉ Uniform C := by
  rintro ⟨I, k, h, -, hfair⟩
  obtain ⟨rfl, rfl⟩ := encodeUniform_inj h
  exact blocked_not_fair (fun _ => 1) (fun _ => rfl) hfair

/--
---
conclusion: Lax117284.Problems.rejectedPerClient_notMem
---
The same, with the fairness parameter of the only client.
-/
theorem rejectedPerClient_notMem (C : (I : Instance) → (Fin I.clients → ℕ) → Prop) :
    rejectedPerClient ∉ PerClient C := by
  rintro ⟨I, k, h, -, hfair⟩
  obtain ⟨rfl, hk⟩ := encodePerClient_inj h
  have := eq_of_heq hk
  subst this
  exact blocked_not_fair _ (fun _ => rfl) hfair

/-! ### The decoding of a word of naturals -/

open Lax117284.InstanceEncoding in
/--
---
conclusion: Lax117284.InstanceEncoding.encodesInstance_unique
---
The two header entries are the numbers of clients and days, and the entries after them are
the processing times and due dates.
-/
theorem encodesInstance_unique {x : List ℕ} {I J : Instance} (hI : EncodesInstance x I)
    (hJ : EncodesInstance x J) : I = J := by
  obtain ⟨n, m, p, d, hp, hd⟩ := I
  obtain ⟨n', m', p', d', hp', hd'⟩ := J
  have hn : n = n' := hI.clientCount_eq.symm.trans hJ.clientCount_eq
  have hm : m = m' := hI.dayCount_eq.symm.trans hJ.dayCount_eq
  subst hn; subst hm
  have hpp : p = p' := funext fun i => funext fun j =>
    (hI.proc_eq i j).symm.trans (hJ.proc_eq i j)
  have hdd : d = d' := funext fun i => funext fun j =>
    (hI.due_eq i j).symm.trans (hJ.due_eq i j)
  subst hpp; subst hdd
  rfl

open Lax117284.InstanceEncoding in
/--
---
conclusion: Lax117284.InstanceEncoding.decode_eq
---
The decoding is a choice among the instances the word encodes, and there is only one.
-/
theorem decode_eq {x : List ℕ} {I : Instance} (h : EncodesInstance x I) : decode x = I := by
  classical
  have hex : ∃ J, EncodesInstance x J := ⟨I, h⟩
  unfold decode
  rw [dif_pos hex]
  exact encodesInstance_unique hex.choose_spec h

/--
---
conclusion: Lax117284.TwoSatisfiability.not_satisfiable_unsatisfiable
---
The formula has two clauses on its one variable, one demanding it true and one false.
-/
theorem not_satisfiable_unsatisfiable :
    ¬ Lax117284.TwoSatisfiability.unsatisfiable.Satisfiable := by
  rintro ⟨a, h⟩
  obtain ⟨α, hα⟩ := h (⟨0, by decide⟩ : Fin 2)
  obtain ⟨β, hβ⟩ := h (⟨1, by decide⟩ : Fin 2)
  simp [Lax117284.TwoSatisfiability.unsatisfiable] at hα hβ
  rw [hα] at hβ
  exact absurd hβ (by simp)

end Lax117284Proofs.Injectivity
