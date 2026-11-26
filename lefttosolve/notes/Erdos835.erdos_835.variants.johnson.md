# Erdos835.erdos_835.variants.johnson — NOTES (26 Nov 2026, ~22:50 UTC)

Status: NOT solved; no search run (see why). Proof file left as the original sorry stub.

## Key reduction (elementary)
A proper (k+1)-colouring of J(2k,k): every (k-1)-set T has k+1 k-supersets, pairwise adjacent,
so they get all k+1 colours. Hence each colour class is a Steiner system S(k-1,k,2k) and the
colouring is a partition of all k-subsets into k+1 disjoint S(k-1,k,2k) (a "large set").
Divisibility (checked by script) holds iff k+1 is prime (= Ma–Tang [MT25] condition).

## Ruled-out k
- k not of form p-1: Ma–Tang (divisibility). Includes all odd k.
- k=4: S(3,4,8) unique, chi(J(8,4))=6 (Brouwer table). k=6: S(5,6,12), chi(J(12,6))=8 (Brouwer).
- k=10: S(9,10,20) would derive (5 times) to S(4,5,15), which does not exist (Mendelsohn–Hung 1972).
- k=12: S(11,12,24) derives to S(4,5,17), nonexistent (Ostergard–Pottonen 2008).
  (These two are from my memory of the design-theory literature; not re-verified here, no network.)
- Smallest surviving candidate: k=16 -> needs 17 disjoint S(15,16,32); derived S(4,5,21) is itself
  an open existence question. No Steiner system with t>=6 is explicitly known at all.

## Consequence
A SOLUTION needs k>=16: C(32,16)=601,080,390 vertices and an explicit S(15,16,32) — far beyond
SAT/ILP/local search and beyond kernel `decide`. A DISPROOF needs all k (incl. k+1 prime, k>=16),
contradicting nothing known (Keevash-type existence suggests large k might even be true). Out of reach.
No CPU spent on searches: k in {4,6,10,12} are dead ranges, k>=16 infeasible.

## Possibly tractable neighbours
- johnsonGraph_2k_k_chromaticNumber_known_cases (3<=k<=8): odd k via Johnson bound; k=4,6 need
  nonexistence of two disjoint.. actually of 5 (resp 7) disjoint S(3,4,8)/S(5,6,12): S(3,4,8) has
  14 blocks, 30 copies, any two share blocks or are disjoint — max 2 disjoint; finite but needs clever Lean.
