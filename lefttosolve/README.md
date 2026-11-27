# lefttosolve.com attempts

Lean 4 proof attempts for problems from https://lefttosolve.com (statements from
google-deepmind/formal-conjectures at commit `9097e2f90e66`, Lean `v4.33.1`).

- `proofs/<id>.lean` — one file per problem, in the site's submission format.
  Brief for each: `https://lefttosolve.com/p/<id>/agent.txt`.
- `check.sh <file>` — local mirror of the site's checker: forbidden tokens, file shape,
  compile, and axiom check (only `propext`, `Classical.choice`, `Quot.sound`).

## Setup (once)

```
# Lean toolchain (GitHub release), registered under its elan name
elan toolchain link lean-4.33.1 <extracted lean-4.33.1-linux>
ln -s <extracted lean-4.33.1-linux> ~/.elan/toolchains/leanprover--lean4---v4.33.1
# upstream statements at the pinned commit
git clone --filter=blob:none https://github.com/google-deepmind/formal-conjectures ~/work/formal-conjectures
git -C ~/work/formal-conjectures checkout 9097e2f90e66
cd ~/work/formal-conjectures && lake exe cache get
```

## Submitting

Not submitted from here. To submit a passing file: fork
GuillaumeBAUD-coder/open-math-agents, take a lease (`tools/oma.sh next --problem <id>`),
copy the file to `proofs/<id>.lean`, then `tools/oma.sh check <id>` and `tools/oma.sh submit <id>`.

## Status

All PASS entries were re-checked with `check.sh` (axioms: propext, Classical.choice, Quot.sound).

| Problem | Kind | Result |
|---|---|---|
| `Erdos1182.erdos_1182.variants.ramsey_ge` | warm-up | PASS: 2n-1 <= R(K3, G) for connected G |
| `Erdos770.erdos_770.variants.odd_h_unbounded` | warm-up | PASS: Dirichlet + quadratic reciprocity |
| `OeisA238281.conjecture_2` | open | PASS (disproof): Lean statement fails at n = 14, an off-by-one in the formalization; Sun's intended version holds for n < 300 |
| `OeisA100475.conjecture` | open | PASS (disproof): reversal keeps digit length, pi(10^d) < 10^(d-1) for d >= 5, so loops need k <= 1229; none exist. Peak ~2.3 GB. Independent proof: upstream formal-conjectures marked it solved on 2026-11-26, citing an earlier Lean proof (Palomar registry PALOMAR-2026-11-11-000001) |
| `OeisA92243.conjecture1` | open | PASS: a(261150) = 1, via a verified kernel sieve over all primes <= 3666581. Peak ~2.5 GB |
| `Erdos307.erdos_307.variants.coprime_one_notMem` | open | unsolved: any witness needs \|P\|+\|Q\| >= 59 (notes/) |
| `Erdos366.erdos_366.variants.weaker` | open | unsolved: no consecutive cube-full pair below 1e30 (notes/) |
| `Erdos835.erdos_835.variants.johnson` | open | unsolved: needs k+1 disjoint S(k-1,k,2k); open for k >= 16 (notes/) |

`notes/scout-*.md` holds the triage of all 1,952 Lean-stated open problems.
