# Agent B triage (18 declarations, all "disproved" problems). Verdict: no closable target found.
None depends on an `answer := sorry` def. Site check (5 ids): all kind=open, solution=null, liveAgents=0.

897.variants.parts.i   OPEN. k=0 quirk kills disjunct 1 (scout), leaving completely additive f: does f(n+1)-f(n) <= C log n force f(p)=O(log p)? Elementary doubling only gives O(log^2). Wirsing-level research.
897.variants.parts.ii  OPEN. Same reduction. Real division (x/0=0) and sign changes give room for a counterexample, but any f>=0 design is forced (CRT+Dirichlet) to have large values on whole residue classes; no construction or proof found.
967.two_three_five     OPEN. True under Schanuel (x=2^it,y=3^it,z=5^it would satisfy 2 algebraic relations), not provable unconditionally.
967.finite             OPEN. No explicit counterexample possible by cheap means: single-base sets fail by modulus (root of 0/1 polynomial has |z|>1/2); a codim-1 zero set on the torus needs a self-inversive factor, excluded by a unit argument (vertex coefficient would be a unit of modulus 2^a3^b). Isolated zeros contradict four-exponentials-type conjectures.
125.zero_density / positive_upper_density / zero_lower_positive_upper   OPEN. Public Lean proof (mo271) gives lowerDensity = 0 only, via scales where 3^k ~ 4^m; that mechanism works only at sparse scales, upper density undecided.
189.parallelogram      OPEN. No quirk (IsCcwConvexPolygon forces sin>0 consistently). Kovac's colouring is for rectangles; parallelogram case unknown either way.
74.sqrt                OPEN ($500 case). Lean disproof of 74 is for some slow f only.
59.c4, 59.big_o        OPEN (Kleitman-Winston constant; Morris-Saxton conjecture).
133.asymptotic         OPEN (f(n) ~ sqrt n; only Theta known). No sInf quirk (stars exist).
147.janzer_conjecture  OPEN for odd r>=5.
205.odd_counterexamples OPEN (known counterexamples are highly 2-divisible).
270.monotone           OPEN.
649.tong_question      OPEN. Tong's QR trick does not transfer (1 is always a residue); heuristically true for density-1 p but needs S-unit bounds far beyond reach.
664.block_design       OPEN for c<1 (c>1 is trivial via de Bruijn-Erdos but statement is for all c>0).
97.k_equidistant       OPEN/unknown (97 itself disproved Oct 2026, after my knowledge cutoff; k-version needs all k).
