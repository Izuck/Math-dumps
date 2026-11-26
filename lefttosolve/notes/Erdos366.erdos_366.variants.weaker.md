# Erdos366.erdos_366.variants.weaker — notes

Target: ∃ n > 0, (3).Full n ∧ (3).Full (n+1).

## Definition check (no quirk)
`Nat.Full k n := ∀ p ∈ n.primeFactors, p^k ∣ n` (FormalConjecturesForMathlib/Data/Nat/Full.lean).
Full 3 0 and Full 3 1 are true, but n > 0 is required and n = 1 gives n+1 = 2 (not 3-full).
So the Lean statement = the informal open question (consecutive cube-full n, n+1 with n >= 1). No shortcut.

## Search (s.cpp in this dir)
Every cube-full n is uniquely a^3 * b^4 * c^5 with b, c squarefree coprime. Enumerate all (b,c) with
b^4c^5 <= N, walk a upward in segments [((k-1)t)^3, (kt)^3), store n mod (2^64-59), radix sort, look
for adjacent residues differing by <= 1. (Do NOT use low 64 bits: multiples of 2^64 collide.)
Checks: count of cube-full <= 10^6 is 307, <= 10^9 is 3721 (matches OEIS A036966 counts);
positive control with diff <= 3 finds (125,128) at 10^12.
- N = 10^24: 460,160,083 cube-full numbers, NO consecutive pair. 23 s CPU.
- N = 10^30: see run30.out / run30.err (started 22:50 UTC 26 Nov; ~40-50 min, ~5 GB RAM).
Cost scales as N^(1/3): 10^33 would need ~8 h single-thread and ~16 GB for the (b,c) table as written
(would need to regenerate (b,c) pairs per segment instead of storing them).

## Heuristic
#cube-full <= x ~ 4.66 x^(1/3), so expected #pairs beyond X is ~ X^(-1/3) * const: essentially zero beyond
10^30. A witness search is not a realistic route; disproof = open conjecture (Erdos), needs abc-type input.

## RESULT (23:35 UTC): N = 10^30 complete, NO consecutive cube-full pair.
run30 (segments 1..480, died/killed before printing DONE, stdout flushed empty at seg 480 = 8.85e29)
+ run30b (s2.cpp, restart from segment 480 to 10^30; 1.95e9 numbers, cand 0). ~4.66e10 cube-full numbers
checked in total, ~45 min single-thread CPU, ~4 GB RAM.
Caveat handled: a pair straddling a segment boundary H=(k t)^3 (n = H-1, n+1 = H) is not seen by the
sort; checked separately in Python that (kt)^3 - 1 is never cube-full for the boundaries used
(needs kt-1 cube-full away from 3; none).
Usage: ./s E t   or   ./s2 E t kstart  (N = 10^E, segment k = [((k-1)t)^3, (kt)^3)).
