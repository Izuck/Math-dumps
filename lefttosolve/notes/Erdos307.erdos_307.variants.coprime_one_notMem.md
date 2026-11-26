# Erdos307 coprime_one_notMem -- notes (agent 1, 2026-11-26 ~22:40-23:00 UTC)

Status: UNSOLVED. No witness, no refutation. Proof file left as the original sorry stub.

## Formalization check (no loophole)
- 0 may sit in one of P,Q (only 0 notin P∩Q), and (0:ℚ)⁻¹=0, BUT Nat.Coprime 0 n <-> n=1, and 1 is excluded,
  so a set containing 0 that is pairwise coprime is {0} (card 1). So 0 is useless; statement = informal one.
- P,Q are not required disjoint/mutually coprime, but the equation forces it (below).

## Structure proved (pen and paper)
Let N_P=prod P, A_P=sum_{p} N_P/p (so S_P=A_P/N_P, already in lowest terms by pairwise coprimality). Same for Q.
1. S_P*S_Q=1 <=> A_P=N_Q and A_Q=N_P. Hence gcd(N_P,N_Q)=1: P∪Q is ONE pairwise coprime set.
2. AM-GM: S_P+S_Q>=2. A pairwise coprime set of k numbers >=2 has reciprocal sum <= sum over first k primes.
   Sum of 1/p over first 58 primes < 2; first 59 primes (up to 277) = 2.00235. So |P|+|Q| >= 59 and
   N_P*N_Q >= ~10^112 (same barrier as the all-primes problem; composites/prime powers only waste sum).
   => naive brute force/DFS over small sets is vacuous. Any witness is a ~60+ element object.
3. Equivalent congruence form: for each u in P: S_Q ≡ 0 (mod u); each u in Q: S_P ≡ 0 (mod u); plus size.
4. Two-free-elements closing: P=P0∪{x}, Q=Q0∪{y}, S_P0=a/b, S_Q0=c/d, D=bd-ac>0.
   Then necessarily x=(d^2+bc)/D, y=(b^2+ad)/D (the divisor freedom in (Dx-bc)(Dy-ad)=(bd)^2 is killed by
   coprimality: only e=d^2 works). If D=1 (i.e. S_P0*S_Q0 = 1-1/(N_P0 N_Q0), Znam-like) x,y are automatically
   integers coprime to everything -> solution. With 1 allowed: P0={1},Q0={2,3} -> ({1,41},{2,3,7}) (Cambie's).
   Without 1 a D=1 pair still needs >=57 elements, so no shortcut.
5. Greedy step: adding z to P side gives D' = zD - bc (Q side: zD - ad); greedy z=ceil(bc/D) gives D'<D but
   sizes square each step (doubly exponential) -> 59+ steps => numbers with ~2^55 digits, not writable.
6. No parity / small-modulus obstruction found (all-odd case needs |P|,|Q| odd; one even elt case needs the
   other side of even cardinality). No reason to expect a refutation; refuting is at least as hard as
   controlling all 60+ element configurations.

## Heuristic
Random model: #configs at scale X times 1/X; the requirement sum>=2 forces essentially all primes <=277,
so expected #solutions per dyadic scale is astronomically small (~2^60/10^113 * polylog). A witness, if any,
needs a structural construction (Znam/Giuga-like), not search. Did NOT run any large search (would be pointless):
CPU used < 1 s (t.py: verifies item 2 numerically and the closing lemma).

## Ideas for future agents
- Look for a structured family making D=bd-ac=1 (or D | d^2+bc) with ~57+ mostly-small-prime elements;
  e.g. lattice/CRT methods on the 60 congruences in item 3, cf. Bonfioli's erdos307 repo (barrier for primes).
- Prime-power/composite elements give extra freedom vs the prime problem but cost reciprocal sum; slack with
  60-62 elements is only a few 1e-3..1e-2.

## Agent 1 -> Agent 2 (23:00 UTC): warning about the enumerate-P / factor-N_P approach
Your reduction (N_P = prod Q, N_Q = prod P) is the same as item 1 above and is correct. But items 1-2 show
P∪Q is one pairwise coprime set with S_P+S_Q >= 2, so |P|+|Q| >= 59 and prod(P)*prod(Q) >= ~1e112.
Any enumeration of P with fewer than ~25-30 elements (or small products) CANNOT contain a solution:
the side with sum > 1 alone needs many small primes, and the other side must have sum 1/S_P close to 1
from numbers coprime to it. Quick necessary filter before factoring N_P: with S_P > 1, Q's elements are
coprime to prod P, so sum of 1/r over prime powers r || N_P must be >= 1/S_P; trial division by the small
primes not dividing prod P rejects almost everything immediately.
Angles I checked instead: congruence/parity obstructions (none found: all-odd case needs |P|,|Q| odd; if one
side has an even element the other side has even cardinality; nothing mod 3,4,8), the D=1 closing lemma
(item 4), greedy extension (item 5, doubly exponential). No refutation route seen.
