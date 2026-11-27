# SieveB: bitset sieve evaluated by the kernel's GMP arithmetic

File: `SieveB.lean` (namespace `OMA.SieveB`, first line `import FormalConjectures.OEIS.«92243»`).
Status: compiles in about 7 s, no sorry, every theorem below has axioms
`[propext, Classical.choice, Quot.sound]`, passes the token rules of `lefttosolve/check.sh`.

## Idea
- `primeBits N`: one Nat whose bit `i` is set iff `i ≤ N` and `i` is prime. The multiples of
  `p` are one GMP division of a shared numerator: `((2^L - 1) / (2^p - 1)) >>> (L % p)`
  (`mask`, proved through the geometric series `geo`). The composite mask is the `lor` of one
  such mask per prime `p ≤ R` (`comp`), with `R = 2^(log2 N / 2 + 1)` and the primes `≤ R`
  taken from a recursive call (`pb`, `sieveStep`).
- `segBits lo len R S`: the same for a window `[lo, lo+len)` only (`winMask`), so the cost
  does not depend on `lo`.
- Extraction: `bitsB`/`blk` = halving down to 256-bit blocks, then ONE kernel step per set
  bit (lowest set bit from `Nat.gcd x 2^256` and a lookup table; the result is checked at
  run time, fallback `bitsA`, so the table needs no proof). Count: `cntT` = halving down to
  bytes plus a popcount table (`popTab_spec` by `decide +kernel` over 256 cases).
- All hot loops are raw `Nat.rec`/`Bool.rec` terms (3-6x faster in the kernel than compiled
  structural recursion).

## API (all proved)
    primeBits N : ℕ
    testBit_primeBits N i : (primeBits N).testBit i = true ↔ i ≤ N ∧ i.Prime
    primeList N : List ℕ
    primeList_eq N : primeList N = (List.range (N + 1)).filter (fun m => decide m.Prime)     -- contract
    primeCount N : ℕ
    primeCount_eq_spec N : primeCount N = ((List.range (N + 1)).filter (fun m => decide m.Prime)).length
    primeCount_eq_length N : primeCount N = (primeList N).length
    primeCount_eq N : primeCount N = Nat.count Nat.Prime (N + 1)
    primeSeg N lo len : List ℕ                      -- slice of the full sieve up to N
    primeSeg_eq N lo len (h : lo + len ≤ N + 1) :
        primeSeg N lo len = (List.range' lo len).filter (fun m => decide m.Prime)
    spec_append_primeSeg N lo len h :
        (List.range (lo + len)).filter P = (List.range lo).filter P ++ primeSeg N lo len
    segBits lo len R S, testBit_segBits            -- window bitset: bit i ↔ (lo + i).Prime
    primeSegW R lo len : List ℕ                     -- windowed sieve, preferred for big N
    primeSegW_eq R lo len (hR2 : 2 ≤ R) (hRlo : R < lo) (hsq : lo + len ≤ R * R) :
        primeSegW R lo len = (List.range' lo len).filter (fun m => decide m.Prime)
    spec_append_primeSegW, filter_range_add
    primeCountW R lo len : ℕ
    primeCountW_eq R lo len hR2 hRlo hsq :
        primeCountW R lo len = ((List.range' lo len).filter (fun m => decide m.Prime)).length
    count_step                                     -- chains window counts (see Pi10M.lean)

Worked examples (complete, proved, std axioms):
- `Pi3666581.lean`: `OMA.Pi3666581.pi_3666581 :
  ((List.range (3666581 + 1)).filter (fun m => decide m.Prime)).length = 261151`
- `Pi10M.lean`: `OMA.Pi10M.pi_1e7 : ((List.range (10000000 + 1)).filter ..).length = 664579`
  and `count_1e7 : Nat.count Nat.Prime 10000001 = 664579`

## Measured (decide +kernel; kernel time from the profiler; peak RssAnon of the lean process,
## of which about 0.55 GB is the Mathlib baseline; machine shared with 4 other agents)
| what | kernel time | peak RssAnon |
|---|---|---|
| sieve only, `primeBits` 10^6 / 4*10^6 | 0.85 s / 1.23 s | 0.6 GB at 10^6; 1.7 GB for one file running 1M, 2M, 3M, 4M in turn |
| sieve only, `primeBits 10^7` | not profiled separately; whole file 17 s wall incl. 5 s import | 5.4 GB |
| `primeCount 10^6 = 78498` | 4.9 s | 1.07 GB |
| `primeCount 2*10^6 = 148933` | 11.1 s | 1.9 GB |
| `(primeList 10^6).length = 78498` | 6.5 s | 1.76 GB |
| `primeList 10^6` walked by a raw `List.rec` | 5.2 s | 1.25 GB (55 us, 8 KB per prime) |
| `(primeList 3666581).length = 261151` in ONE declaration | not completed: OOM-killed at 4.2 GB in the shared cgroup | |
| pi(3666581) as 14 slices `(primeSegW 2048 lo 2^18).length = c` | 28 s total (1.8 s per slice), file 35 s wall | 0.96 GB |
| `Pi3666581.lean` (4 windows of 2^20, `primeCountW`) | whole file 17 s wall | 1.3 GB |
| `Pi10M.lean` (10 windows of 2^20, `primeCountW 3163`) | 37 s kernel, whole file 39 s wall | 1.5 GB |

## Things a consumer must know
1. Kernel memory grows with every reduction step (about 8 KB per extracted prime here) and is
   only freed at the end of a declaration. Split long runs into several declarations
   (`primeSegW`, `primeCountW`); do not evaluate `primeList`/`primeCount` above about 2*10^6
   in one declaration.
2. Put each heavy slice in a Prop-valued `def`, NOT a `theorem`: ten heavy theorems in one
   file peaked at 6.1 GB, the same ten as `def` at 1.5 GB (theorem bodies are checked on
   worker threads and their memory piles up). `def` only gives a linter warning.
3. Wrap the computation in a named def before `decide +kernel` (as `primeCount N = c`); with
   a bare expression such as `primeBits N % 16 = 12` the elaborator spent 30 s before the
   kernel started.
4. `Nat.log2` is NOT GMP-accelerated in this kernel (it unfolds; 53 s on a 10^5-bit number).
   `Nat.pow` refuses exponents ≥ 2^24, so one bitset is limited to about 1.6*10^7 bits.
5. List elements are unevaluated `Nat.add off t` terms that reduce in O(1).

## Not done
- No vectorised (pure GMP) popcount here; `a100475/Pop.body` has one on top of `primeBits`.
- The full (non-windowed) sieve keeps 3 big numbers per sieving prime in the kernel cache
  (5.4 GB at 10^7); use the windowed sieve there.
