# Normal-form Multicoloured Independent Set is NP-hard — reduction from [2,3]-bounded 3-SAT (route B)

Goal: prove `Lax117284.MulticolouredIndepSet.normalMulticolouredIndepSet_npHard : Problems.NPHard NormalMulticolouredIndepSet`
(fairris-lax/concepts/Lax117284/MulticolouredIndepSet.lean; currently a cited axiom) from
`Lax117284.BoundedSat.boundedSat_npHard` (proved in tovey-lax, being wired separately; until then it is the cited axiom of fairris).

Verified by brute force: `check_pipeline.py` (gadget, regularisation, copy reduction, normal form).

## The reduction  φ ↦ H(φ)   (r = 5)

Input: a [2,3]-bounded 3-SAT formula φ (`BoundedSat.Formula`: p = twoClauses + threeClauses clauses of 2 or 3 literals, every literal
occupies at most 2 positions). S = 2·twoClauses + 3·threeClauses slots (positions).

1. **Occurrence graph G.**  Vertices = the S positions o.  o ~ o' (o ≠ o') iff same clause, or litAt o = (x, b) and litAt o' = (x, !b).
   Degree d(o) ≤ (clause size − 1) + (≤ 2 complementary positions) ≤ 4  ≤ r.   (Any repetition / tautology inside a clause only lowers d.)
   φ satisfiable  ⇔  α(G) ≥ p   (and α(G) ≤ p always: one vertex per clause clique).

2. **Regularise to r = 5.**  Gadget X = K₇ minus {path b–a–c, matching d–e, f–g} (vertices a,b,c,d,e,f,g): degrees 5,…,5 and deg(a) = 4;
   α(X) = 2 = α(X − a).  For every position o attach 5 − d(o) fresh copies of X, joining `a` of the copy to o.
   G' is 5-regular; α(G') = α(G) + 2g with g = Σ_o (5 − d(o)) (number of gadgets).  |V(G')| = S + 7g.
   General form: any odd r ≥ max degree, K_{r+2} minus (path + perfect matching of the other r−1 vertices).

3. **Copy reduction to MCIS.**  k' = p + 2g classes, each a copy of V(G'); (i,u) ~ (j,v) iff i ≠ j and (u = v or uv ∈ E(G')).
   H has an independent transversal  ⇔  α(G') ≥ k'  ⇔  α(G) ≥ p  ⇔  φ satisfiable.
   Normal form: Regular of degree (k'−1)(5+1) = 6(k'−1) > 0 when k' ≥ 2;  size = |V(G')| ≥ 4 (5-regular graph);
   edge count = k'·n'·6(k'−1)/2 = 3 n' k'(k'−1), even because k'(k'−1) is even.
   k' ≥ 2 whenever S ≥ 1 because g ≥ S ≥ 2 (each position has deficiency ≥ 1).

4. **Trivial cases.**  S = 0 (no clause): φ satisfiable; map to a fixed normal yes-instance.  Words that are not encodings of a
   formula (or with vars > slots): map to a fixed non-member (e.g. []).

Facts checked by `check_pipeline.py`: gadget degrees/α for r = 3,5,7; α(G') = α(G)+2g and r-regularity on random graphs;
regular degree (k−1)(r+1), even edge count, size ≥ 4 for the copy reduction; MCIS yes ⇔ α(G) ≥ k on random small graphs.

## Formalisation plan (in fairris-lax itself: proofs/Lax117284Proofs/McisHard/…, conclusion-tagged; the concept axiom stays)

Math layer (SimpleGraph level):  M1 copy reduction ⇔ and normal-form lemmas;  M2 gadget + α-shift + regularisation;
M3 [2,3]-SAT ⇒ occurrence graph;  M4 assemble an explicit `Instance` H(φ) with numbered vertices (the concept reads instances through
`adjAt`, `nbrs`, `edgeList`, `edgeCount`).
Machine layer:  M5 poly-time word function `encodeFormula φ ↦ encodeInstance H(φ)` (adjacency matrix bits) by an IMP+ program,
then `npHard_of_manyOne`.
