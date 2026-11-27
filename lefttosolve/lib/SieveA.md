# SieveA (namespace OMA.SieveA) -- status: DONE, all proved, no sorry

Files
- `SieveA.lean`      the deliverable (first line `import FormalConjectures.OEIS.«92243»`), self-contained,
                     no forbidden tokens, no double quotes; axioms: propext, Classical.choice, Quot.sound.
- `Full92243.lean`   complete candidate submission for OeisA92243.conjecture1 (SieveA + chunk theorems +
                     a92243/Reduction.lean + bridge + OMA.solution). `lefttosolve/check.sh` prints PASS, 46 s wall.
- `chunk.lean`, `chunk7.lean`  chunked kernel computations (tug fold at 3666581; pi(10^7)), appended to SieveA.lean
                     to benchmark. `run.py <file>` prints kernel time and peak RssAnon.

API (all theorems proved)
    def primeList (N : ℕ) : List ℕ                 -- list version (per-bit extraction); small N only
    theorem primeList_eq (N) : primeList N = (List.range (N + 1)).filter (fun m => decide m.Prime)
    def foldPrimes (N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : ℕ    -- fast path
    theorem foldPrimes_eq (N f s) :
        foldPrimes N f s = List.foldl f s ((List.range (N + 1)).filter (fun m => decide m.Prime))
    def primeCount (N) := foldPrimes N (fun s _ => Nat.succ s) 0
    theorem primeCount_eq (N) : primeCount N = ((List.range (N + 1)).filter (fun m => decide m.Prime)).length
    theorem primeCount_eq_length (N) : primeCount N = (primeList N).length
  chunking (kernel memory is released between declarations):
    def sieveOK N : Bool, numBlocks N, foldInit N f s, foldBlocks N f k j s
    theorem foldPrimes_eq_blocks (h : sieveOK N = true) :
        foldPrimes N f s = foldBlocks N f (numBlocks N) 0 (foldInit N f s)
    theorem foldBlocks_add : foldBlocks N f (k1 + k2) j s = foldBlocks N f k2 (j + k1) (foldBlocks N f k1 j s)
  tug of war (A92243):
    def tugZ, def tugStep (packed Nat state), theorem tug_fold, theorem tug_primes, theorem tugZ_zero_zero

Design
- base primes p <= R = 2^(log2 N / 2 + 1) from the list version (recursive, fuel 64, fallback = spec);
- odd-only segmented bitmask sieve, blocks of 2048 bits (4096 integers): for each odd base prime one
  GMP shift+or of the periodic pattern (2^(pK)-1)/(2^p-1); raw List.rec loop;
- extraction: raw Nat.rec loop over the 256 bytes of a block, 256-entry table (one Nat literal `tab`,
  checked by decide +kernel) giving the set-bit positions as hex digits, state forced after each prime;
- the fold function f must be made of kernel-accelerated Nat ops (no match / if / Prod).
- per-step kernel cost is the whole story: compiled structural recursion ~25-100 us and 3-14 KB retained
  per step; raw recursors ~4 us; Nat.log2 is not GMP-accelerated.

Measured (decide +kernel, kernel time / peak RssAnon of the whole lean process; baseline ~0.5 GB)
- primeCount 1000000 = 78498            5.2 s / 1.35 GB
- primeCount 2000000 = 148933           13.4 s / 2.5 GB
- primeCount 3666581 = 261151           23 s / 4.06 GB                     (single declaration)
- foldPrimes 3666581 tugStep 0 = 20690513873580050135229173390111381     34.6 s / 4.99 GB (single declaration)
- same in 4 chunk theorems (chunk.lean)  ~45 s wall whole file / 2.46 GB
- primeCount 10000000 = 664579 in 6 chunk theorems (chunk7.lean)   ~67 s kernel, 75 s wall / 4.3 GB
- (primeList 100000).length = 9592      4.7 s / 1.0 GB  (list version: ~3-5 KB per integer, do not use
  above ~10^6; (primeList 3666581).length as a single decide would need > 15 GB -> use primeCount and
  primeCount_eq_length instead)

Remaining gap: none for the two target problems. The literal contract benchmark
`(primeList 3666581).length = 261151 := by decide +kernel` is NOT feasible in list form (memory);
the equivalent proved route is `rw [← primeCount_eq_length]` then `decide +kernel` (23 s).
