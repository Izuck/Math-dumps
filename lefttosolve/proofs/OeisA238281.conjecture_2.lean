import FormalConjectures.OEIS.«238281»

-- Problem: Equal prime counts in adjacent intervals (kn, (k+1)n) and ((k+1)n, (k+2)n), conjecture 2
-- Upstream: formal-conjectures FormalConjectures/OEIS/238281.lean:75 (declaration OeisA238281.conjecture_2)
-- Disproof of the Lean statement as written: it fails at n = 14 (and n = 286).
-- For n = 14 the k < 14 with 2k+1 prime are 1,2,3,5,6,8,9,11, and the two half-open
-- intervals ((k-1)n, kn] and (kn, (k+1)n] never hold equally many primes.
-- This is an off-by-one in the formalization: with the intervals (kn, (k+1)n] and
-- ((k+1)n, (k+2)n] the statement holds for every 1 < n < 300 (checked by sieve).

set_option maxRecDepth 100000 in
theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro h
  obtain ⟨k, hk0, hk, hp, he⟩ := h 14 (by norm_num) (by norm_num)
  interval_cases k <;> revert he hp <;> decide +kernel
