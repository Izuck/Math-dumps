# Agent D triage (17 variants). Verdict: none closable; every one is a genuinely open variant.
All 16 files are byte-identical to upstream main (checked), none depends on an `answer := sorry` def.
Site `solution` field null for 741.lower, 542.only_two, 457.one_sub, 473.finite (only ones queried).

741.lower            OPEN, best lead. Lower-density split. Probably TRUE (random 2-colouring gives each colour >= c/4 in expectation at each scale; dense scales are fine for any balanced colouring since A_i+A_i contains e+A_i), but infinitely many scales with non-summable Chebyshev failure prob => needs a real idea. The DeepMind counterexample for exact density (B1 u B2 u S_C) does NOT refute it (split by residue works). Not a 2-hour job.
542.only_two         OPEN. Exhaustive search n<=70: only {2,3,5} (n=5) and {3,4,5,7,11} (n=11) have sum>1, so no cheap disproof; proof needs Chen-type argument for all n (Chen only gives <1.0179 for n>172509).
542.one_add_little_o OPEN (Erdos speculation; Chen's bound is a constant > 1).
457.one_sub          OPEN. Trivial bound is (1+o(1))log^2 n via theta; gaining 1-eps needs ruling out log n consecutive integers that are almost entirely products of distinct primes < log^2 n. No elementary route.
473.finite           OPEN conjecture (prime-sum Hamiltonian path on [n]); Bertrand gives only matchings, twin primes give infinitely many n.
477.X_pow_three      OPEN. The d=6 proof (plby/Price) is a greedy construction needing few k with k^d - c in B-B (determinant method, d>=6); for cubes that is the sum-of-three-cubes counting problem, unknown. Sekanina argument needs B-B huge. Statement may well be FALSE but neither direction is provable now.
490.limit            OPEN (existence of limit).
694.carmichael       OPEN: statement asserts a counterexample to Carmichael's conjecture.
733.limit_exists     OPEN (existence of lim log f(n)/sqrt n).
785.chen_conjecture  OPEN (3/2 threshold; proved only up to 3-sqrt 3).
865.sos              OPEN for k>=4 (k=2 folklore, k=3 is the 5/8 theorem); statement is for all k.
895.hindman          OPEN for k>=3 (k<=2 known); stated for all k.
977.factorial        OPEN (P(n!+1)/n -> oo).
1042.universal       OPEN, and needs capacity theory absent from Mathlib.
1044.fixed_degree    OPEN for n>=3; Hausdorff length of lemniscates, infeasible.
1050.transcendental  OPEN (includes transcendence of Erdos-Borwein constant, t=-1).
1180.optimal         OPEN (eps^{-1-o(1)}; best known eps^{-2}).
