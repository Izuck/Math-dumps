# Scout report: non-Erdős open problems (formal-conjectures @ lefttosolve commit)

Scope scanned: all 1102 `@[category research open` declarations (604 files) outside `ErdosProblems/`
(OEIS 394, Wikipedia 336, GreensOpenProblems 128, Paper 93, Arxiv 43, rest ~110).
Method: read every statement; brute-forced ~170 OEIS statements in Python against a literal
transliteration of the Lean text (scripts `sun*.py`, `cong.py`, `w*.py` in this directory);
compiled Lean for the hits. Site status checked 23:00 UTC for the ids below: all `kind: open`,
`solution: null`, `liveAgents: 0`. The site accepts disproofs
(`theorem OMA.disproof : ¬ (type_of% @<decl>)`), forbids `sorry`, axioms and `native_decide`.

Honest summary: the repo has been audited hard (most junk-value traps already carry explicit
guards and sanity tests, most Graffiti/WOWII items are already resolved). I found ONE cheap,
compiled win, ONE certain-but-computation-heavy win, and then only expensive long shots.
Note: OEIS modules are not pre-built in `.lake` (only Mathlib/ForMathlib), so a solver must
`lake build FormalConjectures.OEIS.«N»` first; my experiments used `import Mathlib` only.

---------------------------------------------------------------------------------------------

## 1. `OeisA238281.conjecture_2`  — category (b), DISPROOF, verified by compiling

File `FormalConjectures/OEIS/238281.lean:75`.

```lean
theorem conjecture_2 (n : ℕ) (hn : 1 < n) (h8 : n ≠ 8) :
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (2 * k + 1).Prime ∧
      Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n) =
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) := by
  sorry
```

Why tractable: off-by-one in the formalization. Sun's OEIS comment (and the file's own `a`)
uses the intervals (kn,(k+1)n) and ((k+1)n,(k+2)n); the Lean statement shifted them to
((k-1)n,kn] and (kn,(k+1)n]. The shifted statement is false at **n = 14**:
π(14m) for m = 0..14 is 0,6,9,13,16,19,23,25,29,30,34,36,39,42,44, so the block counts are
6,3,4,3,3,4,2,4,1,4,2,3,3,2; equal neighbours occur only at k = 4 and k = 12, and
2k+1 = 9, 25 are not prime. (With the unshifted OEIS intervals k = 3 works, which is why the
real conjecture is fine.) My Python scan found n = 14 as the only failure for n < 150.

Demonstrated check: this compiles with axioms `[propext, Classical.choice, Quot.sound]`
(6 s; file `/tmp/claude-0/-home-user-Math-dumps/007a8e66-d251-53ff-8cc5-51a13f61f8fa/scratchpad/scout/disproof_238281_c2.lean`):

```lean
import Mathlib
set_option maxRecDepth 100000 in
theorem neg : ¬ (∀ (n : ℕ) (hn : 1 < n) (h8 : n ≠ 8),
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (2 * k + 1).Prime ∧
      Nat.primeCounting (k * n) - Nat.primeCounting ((k - 1) * n) =
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n)) := by
  intro h
  obtain ⟨k, hk0, hk, hp, he⟩ := h 14 (by norm_num) (by norm_num)
  interval_cases k <;> revert he hp <;> decide +kernel
```

Proof sketch for the site: `import FormalConjectures.OEIS.«238281»`, then
`theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by intro h; ...` exactly as
above (`h 14 (by norm_num) (by norm_num)`, `interval_cases k`, `decide +kernel`). Only risk:
whether `type_of%` elaborates the binders identically (it should) and whether the site allows
`decide +kernel` (it uses no extra axioms; the repo's own tests use it).
Effort: **0.3 h**. Confidence: very high.

---------------------------------------------------------------------------------------------

## 2. `OeisA92243.conjecture1`  — category (c), small(ish) witness, computation-heavy

File `FormalConjectures/OEIS/92243.lean:88`.

```lean
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

theorem conjecture1 : ∃ n > 250000, a n > 0 := by
  sorry
```

Why tractable: the 2004 OEIS question is simply answered by computing further. With the Lean
indexing (checked against the file's tests `a 2 = 1`, `a 3 = 1`): a(250000) = -139,
a(261149) = 0, **a(261150) = 1**, where `Nat.nth Nat.Prime 261150 = 3666581`
(previous primes 3666539, 3666529). 261150 is the first positive index after 250000; there
are 135 positive indices in (250000, 262000]. Computed twice with independent Python sieves
(`tug.py`, `v.py`). No smaller witness exists, so the proof must certify all 261,151 primes
up to 3,666,581.

Proof sketch (Lean):
* Define a computable `step`/`run` scanner over the integers m = 2..3666581 carrying
  (m, last prime, last gap, score) with a Bool trial-division primality test, and prove a
  soundness lemma: if `isP` agrees with `Nat.Prime` on [2, M] then the scanner's score at M
  equals `a (Nat.count Nat.Prime (M+1) - 1)`. Ingredients: `Nat.nth_count`, `Nat.count_succ`,
  `Nat.nth_strictMono Nat.infinite_setOf_prime`, `Finset.sum_Icc_succ_top`, `Int.sign` cases;
  correctness of trial division via `Nat.prime_def_le_sqrt` / `Nat.minFac_le_of_dvd`.
* Certify the run in blocks by `decide +kernel` (state after block i is an explicit numeral
  tuple; generate the ~N block lemmas by script) and chain them.
* Precedent in the repo: `OeisA69004.conjecture2` was closed with a Lean certificate
  involving π(512720) (see docstring, Lean certificate for the A069004 counterexample).
Measured cost: my naive structural-recursion scanner takes **35 s of `decide +kernel` per 2000
integers** near 3.66M (`timing_92243_block.lean`), i.e. ~18 CPU-hours for the full range –
too slow as is. It needs a 20–50x better kernel-friendly design (wheel / avoid `brecOn` fuel
recursion and Prod/ℤ in the state / sieve of a block against a fixed list of the 273 primes
≤ 1913 using `List.all`, or parallel block files). That optimisation is the whole risk.
Effort: **6–10 h**, medium risk (truth of the statement: certain).

---------------------------------------------------------------------------------------------

## 3. `OeisA100475.conjecture`  — category (b)/(a-ish), DISPROOF, true but needs explicit π bounds

File `FormalConjectures/OEIS/100475.lean:125`.

```lean
def reverseDigits (k : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 k |>.reverse)

noncomputable def aStartAt (x : ℕ) : ℕ → ℕ
  | 0 => x
  | n + 1 =>
    let k := aStartAt x n
    if k = 0 then 0
    else reverseDigits (Nat.nth Nat.Prime (k - 1))

def IsUltimatelyPeriodic (f : ℕ → ℕ) : Prop :=
  ∃ N P, P > 0 ∧ ∀ n, n ≥ N → f (n + P) = f n

theorem conjecture :
    ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  sorry
```

Why tractable: the question has a negative answer by a counting argument nobody wrote down.
k ↦ reverse(p_k) never decreases the number of decimal digits (p_k > k, primes > 5 do not end
in 0, so reversal keeps the length). A loop therefore lives among d-digit k with p_k also
d-digit, i.e. 10^(d-1) ≤ k ≤ π(10^d). Since π(10^d) < 10^(d-1) for every d ≥ 5
(9592 < 10^4, 78498 < 10^5, ...), loops can only occur for k ≤ π(10^4) = 1229, and a direct
check (my `rev.py`: no cycle from any start < 10^4; the only length-preserving k are
1..4, 10..25, 100..168, 1000..1229 and none closes up) shows there is none. So
`¬ ∃ x, 0 < x ∧ x ≠ 1 ∧ ...` holds.

Proof sketch: (i) lemma `(Nat.digits 10 (reverseDigits m)).length = (Nat.digits 10 m).length`
when `m % 10 ≠ 0` (`Nat.digits_ofDigits`, `List.getLast` nonzero); (ii) monotone digit length
along `aStartAt` (`Nat.digits_len_le_iff_lt_base_pow`, `Nat.nth_strictMono`, `le_nth`), so a
periodic tail has constant length d; (iii) the hard part: `Nat.primeCounting (10^d) < 10^(d-1)`
for all d ≥ 5. Induction c_d ≤ c_(d-1)/10 + log 4 /((d-1) log 10) from Mathlib's Chebyshev
bound θ(x) ≤ x log 4 (`Chebyshev.theta_le_log4_mul_x`) only closes for d ≥ 8 given
π(10^7) < 10^6, so the base cases π(10^5), π(10^6), π(10^7) need kernel computation (10^7 is
heavy; same technology as candidate 2) or a sharper explicit Chebyshev estimate;
(iv) finite check of ~330 indices ≤ 1229 (needs p_k for k ≤ 1229, i.e. primes < 10^4).
Effort: **10–15 h**, high risk in step (iii). Listed because the answer is certain.

---------------------------------------------------------------------------------------------

## 4. `OeisA251758.conjecture`  — category (c)-like, probably TRUE, finite but fiddly

File `FormalConjectures/OEIS/251758.lean:70`.

```lean
def a (n : ℕ) : ℕ :=
  let divisorsList : List ℕ := (List.range (n + 1)).filter (· ∣ n)
  let sList : List ℕ :=
    (divisorsList.zip divisorsList.tail).map (fun p : ℕ × ℕ => p.fst * p.snd)
  let s : ℕ := sList.sum
  if s = 0 then 0 else n ^ 2 / s

theorem conjecture :
    IsLeast {x : ℕ | 2 ≤ x ∧ a x = 8}
      (Nat.kthPrimorial 12 / Nat.kthPrimorial (Nat.primeCounting' 8)) := by
  sorry
```

(The value is 11·13·17·19·23·29·31·37 = 35336848261.) Why possibly tractable: writing
s/x² = Σ over consecutive divisors d<d' of 1/(d d'), a(x)=8 means 1/9 < Σ ≤ 1/8. That forces
least prime factor 11 (≤ 7 gives Σ ≥ 1/7; ≥ 13 gives Σ < 0.094), and the remaining mass
(> 0.0202 out of at most ≈ 0.0235 available from all 11-rough numbers) forces 13 | x and
17 | x and nearly every small 11-rough number to divide x. Exhaustive search over all
x < 35336848261 of the form 11^a 13^b 17^c · (primes ≤ 131, any exponents) – 30,093
candidates, `lcm.py` – finds no x with a(x) = 8, so the conjectured minimum is very likely
right. A Lean proof needs (i) `a 35336848261 = 8` (rewrite the `List.range` filter as the
sorted divisor list, 256 divisors), (ii) a rigorous tail bound Σ_{d ≥ D} ≤ 1/(2D) plus case
analysis on which 11-rough numbers below ~150 divide x. Not a known-literature result; I did
not make the bound fully rigorous. Effort: **10 h+**, medium-high risk.

---------------------------------------------------------------------------------------------

## 5. `OeisA241898.conjecture_2`  — category (a)-ish, true-looking, no cheap proof found

```lean
theorem conjecture_2 :
    ∀ n : ℕ, ∃ a b c d : ℕ,
      a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  sorry
```

A casual OEIS question (can every number be a sum of four squares none equal to 7²?).
Verified for n < 1500. Easy half: if 4 ∣ n, double a representation of n/4
(`Nat.sum_four_squares`) – all parts even, none is 7. For n ≢ 0 (mod 4) I found no trick:
the natural proof counts representations (Jacobi r₄(n) = 8σ(n) for odd n versus
≤ 8·r₃(n−49)), and neither Jacobi's formula nor a usable r₃ bound is in Mathlib; the trivial
bound r₃(m) ≤ m+2√m+1 loses by a factor ~8. Effort: **unknown, > 10 h**. Listed only as the
best remaining probably provable statement.

---------------------------------------------------------------------------------------------

## Near-misses (one line each)

* `OeisA117531.conjecture` (a(n) < n for n > 13): actually a theorem – a(n) = n would make
  k²−k+p_n prime for all k ≤ n > √(p_n/3), hence (Rabinowitsch) h(1−4p_n)=1, impossible beyond
  p = 41 by Baker–Heegner–Stark – but that needs the class-number-one theorem; infeasible.
* `OeisA135508.conjecture`: reduces to p−2 composite ⇒ gcd(x(p−3), p−2) > 1 for a
  Rowland-type recurrence; no counterexample for p < 2·10^6, no proof idea.
* `OeisA108301.conjecture` (digit sum of F_n prime, n > 11): no witness for n ≤ 21; larger n
  cannot be certified in-kernel.
* `OeisA113271.conjecture1`, `OeisA113257.conjecture1/2`, `OeisA107247.conjecture`,
  `OeisA102847`, `OeisA116150`, `OeisA53067` (next prime/square term, `answer(sorry)`):
  no hit in range (113271: n ≤ 13; 113257: n ≤ 25; 107247: n < 300); answers unknown.
* `OeisA113010`, `OeisA109905` (existence questions): searched d ≤ 400 digits / n ≤ 20000,
  no witness; `OeisA113609`, `OeisA67599`, `OeisA230718`: genuinely open.
* `OeisA7918.conjecture1`: `isApOfNPrimes` requires d > 0, so no junk; lower bound is easy,
  equality is the k-tuple conjecture.
* `OeisA259667.conjecture_1/2` (Catalan(2^k−1) mod 6): equivalent to 2^k has a ternary
  digit 2 (Erdős), open.
* `OeisA64313.conjecture` (floor of n-gon area): no counterexample for n < 3·10^6 (60-digit
  arithmetic); a proof would need Diophantine control of π.
* `OeisA255916.conjecture_2/3`, `OeisA228425.conjecture_5`: pairs outside Sun's lists show no
  small counterexample (n < 4000 / 400), so the only if halves are not decidable cheaply.
* `OeisA196697.conjecture_1` vs `conjecture_2`: mutually contradictory pair, both open, no
  zero found by OEIS; `OeisA72200`, `OeisA76495`, `OeisA78680`, `OeisA108129`: real open
  problems (factorial digits, σ(x) mod x = 5, Fermat/Riesel).
* `OeisA63880.mod_216_of_a` / `unique_primitive_108`: hold for n ≤ 3·10^6; structural proof
  (∏ σ(p^e)/(p^e+1) = 2) not found.
* Wikipedia: `ErdosMoser`, `HyperperfectNumber.*`, `Firoozbakht`, `Hadamard.«167»` (ℕ∞ infimum),
  `Superperfect.twoFivePerfect`, `CramerConjecture.strict_bound`, `Mersenne.new_mersenne`,
  `LonelyRunner`, `MeanValueProblem` (unused K, but K = 1 is still open) – all checked for
  junk values, all correctly guarded.
* `Constant6a.c6a_upper_bound_improved` / `c6a_eq_half`, `Constant7b.*`, `Green40.f_eq_one_for_all`
  (r = 0 gives f = 1, no trick), `Green28`/`Mathoverflow339137`, Kourovka 20.51, WOWII
  84/96/199: no quirk found.
* ~170 Zhi-Wei Sun-type OEIS statements (A218585 … A262880, A179524/37, A190969, A208425,
  A212334, A212496, A189286, A2426, A108866, A224, A7406, A245211, …) were brute-forced
  against the literal Lean text for small n: the only failure is candidate 1.
