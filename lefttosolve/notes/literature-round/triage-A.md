# Agent A triage (2026-11-27)

No declaration on this list is closable in a few hours. Three groups.

## Already solved on lefttosolve.com (api `solution` non-null) - dropped
- Erdos96.erdos_96            site: disproof accepted
- Erdos97.erdos_97            site: disproof accepted
- Erdos14.erdos_14.parts.i    site: proof accepted
- Erdos14.erdos_14.parts.ii   site: disproof accepted

## Impossible under the checker: statement contains a `def ... answer := sorry`
The target type depends on sorryAx (verified: a theorem that only mentions
type_of% @Erdos732.erdos_732.parts.i prints sorryAx in its axioms), so neither OMA.solution nor
OMA.disproof can pass the axiom check, and nothing can be proved about an opaque sorry value anyway.
- Erdos692.erdos_692.parts.ii   (answer : N -> N)
- Erdos321.erdos_321            (answer : N -> N)
- Erdos732.erdos_732.parts.i    (answer : N -> List N -> Prop)
- Erdos857.erdos_857            (answer : N -> N -> R)

## Unsolved on site, genuine research statements, no shortcut found
- Erdos108.erdos_108   r is N and SimpleGraph.girth is N-valued (0 for acyclic), so no top/acyclic
                       trick; k = 2 is true; the statement is the real Erdos-Hajnal question.
                       Status changed to disproved 2026-10-16; construction not known to me, not on GitHub.
- Erdos910.parts.i     ZFC counterexample needed (Rudin needs CH; docstring says so). n = 0, 1 give no
                       cheap counterexample (intervals always have a non-homeomorphic subinterval).
- Erdos910.parts.ii    needs ind X > 1; no degenerate case; open-looking as stated.
- Erdos81.erdos_81     chordal n^2/6 + O(n); proved 2026-10-15, proof not available here; definitions faithful.
- Erdos143.parts.ii    convergence of sum 1/(x log x) for well-separated sets; faithful; research-level.

Upstream main versions of 96, 97, 108, 910, 14, 81, 143 are identical to the pinned commit
(no formal_proof links added).
