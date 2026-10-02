import Lax117284Proofs.Treewidth.Chars.Defs

/-!
# `DomC` is a preorder, and `domCB` decides it (work package C1)

`DomC a b` ("`a` is at least as good as `b`") = same shape, same labels, run-wise `Seq.Dom`.
-/

set_option linter.unusedVariables false

namespace Lax117284Proofs.Treewidth.Chars

open Lax117284Proofs.Treewidth.Seq Lax117284Proofs.Treewidth.Trees

namespace CT

mutual
theorem DomC.refl : ∀ c : CT, DomC c c
  | node S y ks => ⟨rfl, Dom.refl y, DomCL.refl ks⟩
theorem DomCL.refl : ∀ l : List CT, DomCL l l
  | [] => trivial
  | k :: ks => ⟨DomC.refl k, DomCL.refl ks⟩
end

mutual
theorem DomC.trans : ∀ {a b c : CT}, DomC a b → DomC b c → DomC a c
  | node S y ks, node S' y' ks', node S'' y'' ks'', h1, h2 =>
    ⟨h1.1.trans h2.1, Dom.trans h1.2.1 h2.2.1, DomCL.trans h1.2.2 h2.2.2⟩
theorem DomCL.trans : ∀ {a b c : List CT}, DomCL a b → DomCL b c → DomCL a c
  | [], [], [], _, _ => trivial
  | k :: ks, k' :: ks', k'' :: ks'', h1, h2 => ⟨DomC.trans h1.1 h2.1, DomCL.trans h1.2 h2.2⟩
end

mutual
theorem domCB_iff_aux : ∀ (a b : CT), domCB a b = true ↔ DomC a b
  | node S y ks, node S' y' ks' => by
    simp only [domCB, DomC, Bool.and_eq_true, decide_eq_true_eq, ← dom_iff_domB, and_assoc]
    rw [domCBL_iff_aux ks ks']
theorem domCBL_iff_aux : ∀ (a b : List CT), domCBL a b = true ↔ DomCL a b
  | [], [] => by simp [domCBL, DomCL]
  | [], _ :: _ => by simp [domCBL, DomCL]
  | _ :: _, [] => by simp [domCBL, DomCL]
  | k :: ks, k' :: ks' => by
    simp only [domCBL, DomCL, Bool.and_eq_true]
    rw [domCB_iff_aux k k', domCBL_iff_aux ks ks']
end

theorem domCB_iff {a b : CT} : domCB a b = true ↔ DomC a b := domCB_iff_aux a b

end CT

end Lax117284Proofs.Treewidth.Chars
