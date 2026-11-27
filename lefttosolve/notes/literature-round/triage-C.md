# Triage, list C (agent C). Verdict: no declaration on this list is closable; all 17 variants are genuinely open (or unprovable as stated).

Best remaining leads first.

- Erdos49 primes_maximal (f(N)=pi(N) for all N>=2): OPEN. Stronger than Tao's (1+o(1))pi(N). Computed: longest strictly-phi-increasing subsequence of 1..N equals pi(N) for every N <= 3*10^6 (f49.py), so no small counterexample; a proof would need new maths.
- Erdos13 general (all r, |A| <= N/(r+1)+O(1)): OPEN for r>=3 (Bedert settles r=2 only; r=0,1 trivial). Brute force (e13.py, r=3,4,5, N<=65) finds max = ceil-ish N/(r+1), extremal set the top interval; no counterexample.
- Erdos308 all_N (representable set is an initial segment for EVERY N): OPEN. Equivalent to N_k <= N_{k+1}; needs: k+1 representable without 1 => k representable, i.e. an effective Croot theorem for all N. Not elementary, not a small finite computation.
- Erdos387 schinzel (all large non-prime-power k have n with no n-i | C(n,k)): OPEN (Schinzel's conjecture; BNPZ26 settles only the main question).
- Erdos126 isLittleO (f(n)=o(n/log n)): OPEN (Erdos: never proved; the Lean proof is of f/log n -> infinity). Every construction tried rescales to the {1..n} bound.
- Erdos321 isBigO / isLittleO / isTheta: UNPROVABLE AS STATED. Target mentions `answer`, a def whose body is `sorry` (sorryAx); nothing can be proved about it without the sorryAx axiom.
- Erdos418 odd_noncototient: OPEN (needs Goldbach-type input). Erdos418 density: OPEN (positive density of noncototients unknown).
- Erdos358 prime_set (limsup = infinity) and prime_set_density_representation: OPEN; Tao's construction is for a different sequence. Density variant would need a sieve second-moment bound, far from a few-hour formalization.
- Erdos344 sqrt_two: OPEN (sharp constant; Szemeredi-Vu gives only some large C). Definitions checked, no loophole.
- Erdos211 one_sixth: OPEN (sharp Beck constant, uniform in k).
- Erdos123 powers_2_3_5_snug: OPEN/hard (snug representations for every eps).
- Erdos94 regular_ngon: OPEN (Erdos-Fishburn extremal conjecture).
- Erdos21 three_n: OPEN (f(n)=3n+O(1); only 8n/3-3 <= f(n) << n known).
