# Scout report: Erdős problems (formal-conjectures @ lefttosolve commit)

Scope scanned: all 850 `@[category research open …]` declarations in
`FormalConjectures/ErdosProblems/*.lean` (544 files). Every statement was read once; about 150
definitions were opened; 10 computational searches and 2 Lean compile checks were run.

## Bottom line (read this first)

**I found no candidate that I believe can be closed in a few hours.** No junk-value quirk
survived checking, no small witness turned up, and no open here but solved in the literature
with a short proof case was confirmed. The corpus at this commit is heavily audited: docstrings
explicitly discuss `sInf ∅`, `ncard` of infinite sets, real `limsup` junk, `n = 0` cases, etc.,
and the definitions carry the guards (`Summable`, `2 ≤ s.card`, `0 < n`, …).

The ranked list below is therefore least hopeless, not promising. Probabilities are my honest
guesses for a few-hours Lean attempt.

Useful facts learned about the site/repo:
- The site accepts **disproofs**: the API record has a `disproofSkeleton` next to `skeleton`, and a
  `reductionSkeleton`. So refutable statements count as closable.
- The API record has an `erdosState` field (erdosproblems.com status: `open`, `falsifiable`,
  `disproved (Lean)`, …). I only queried 9 ids (rate-limited as instructed). Sweeping that field
  over all Erdős ids would be the cheapest remaining literature (a) signal; I did not do it because
  the brief limited site calls to the top candidates.
- Only 5 Erdős modules have `.olean`s (`307 366 770 835 1182`). For any other problem
  `import FormalConjectures.ErdosProblems.«N»` fails; scratch files must
  `import FormalConjecturesUtil` and copy the definitions (that is what I did), or the module must
  be built first.

---

## Ranked candidates

### 1. `Erdos897.erdos_897.variants.parts.i`  — category (b), partial quirk, verified by compiling

```lean
theorem erdos_897.variants.parts.i : ∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
    (∀ k p, p.Prime → f (p^k) = f p) ∨ (∀ (k p : ℕ), p.Prime → f (p^k) = k*f p) →
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n+1) - f n) / (n : ℝ).log : EReal)) = ⊤ := by
  sorry
```

Site: `erdosState` of the parent problem is `disproved (Lean)`, this variant `kind: open`,
`liveAgents 0`, no solution, difficulty 52.

Quirk (verified): the first disjunct quantifies over `k = 0`, so it gives
`f p = f (p^0) = f 1 = 0` for every prime (additivity gives `f 1 = 0`), hence `f (p^k) = 0`
everywhere and the `limsup = ⊤` hypothesis is contradicted. Compiled check
(`scout/t897.lean`, `import FormalConjecturesUtil`, no errors):

```lean
example (f : ℕ → ℝ) (hadd : ∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b)
    (h : ∀ k p, p.Prime → f (p^k) = f p) : ∀ k p, p.Prime → f (p^k) = 0 := by
  have h1 : f 1 = 0 := by
    have := hadd 1 Nat.one_pos 1 Nat.one_pos (Nat.coprime_one_left 1); simpa using this
  intro k p hp; have h0 := h 0 p hp; rw [pow_zero, h1] at h0; rw [h k p hp, ← h0]
```

So half of the statement is vacuous and the theorem is exactly the **completely additive** case
(`f (p^k) = k f p`, where `f(p^k)/log p^k = f(p)/log p`). That case is, as far as I can tell,
genuinely open mathematics. My attempt: assuming `f(n+1) − f(n) ≤ C log n` eventually, the binary
expansion trick only gives `f(n) = O(log² n)`, not `O(log n)`, so no contradiction with
`limsup f(p)/log p = ∞`; the increment cost `C log n` is on the same scale as `f`. Neither a proof
nor a counterexample fell out.

Sketch if someone finds the maths: `rcases` the disjunction; kill case 1 with the lemma above plus
`Filter.limsup_const`/`EReal.coe_zero` (needs `NeBot` of `atTop ⊓ 𝓟 {(p,k) | p.Prime}`, from
`Nat.exists_infinite_primes`); case 2 is the real work.
Effort: 1 h for the vacuous half; the other half is research. P(close) ≈ 2 %.

### 2. `Erdos897.erdos_897.variants.parts.ii`  — category (b), same partial quirk

```lean
theorem erdos_897.variants.parts.ii : ∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {(p, k) : ℕ × ℕ | p.Prime}).limsup
      (fun (p, k) => (f (p^k) / (p^k : ℝ).log : EReal)) = ⊤) →
    (∀ k p, p.Prime → f (p^k) = f p) ∨ (∀ (k p : ℕ), p.Prime → f (p^k) = k*f p) →
    Filter.atTop.limsup (fun (n : ℕ) => (f (n+1) / f n : EReal)) = ⊤ := by
  sorry
```

Site: `kind: open`, `liveAgents 0`, no solution. Same reduction to completely additive `f`. Extra
looseness: the ratio is a real division (`x/0 = 0`) and `f` may be negative, which might make a
*counterexample* easier to build than for part i (e.g. arrange `f n = 0` or sign patterns), but I
did not find one. Effort: research. P(close) ≈ 2 %.

### 3. `Erdos488.erdos_488`  — category (c), refutation by small witness (none found)

```lean
theorem erdos_488 : ∀ (A : Finset ℕ), A.Nonempty →
    -- These are needed for the reasons outlined here: https://github.com/google-deepmind/formal-conjectures/pull/256
    0 ∉ A → 1 ∉ A →
    letI B := {n ≥ 1 | ∃ a ∈ A, a ∣ n}
    ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
      ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
        2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n := by
  sorry
```

Site: `erdosState: falsifiable`, `liveAgents 0`, no solution, difficulty 54. A counterexample
would be a `decide`/`norm_num` disproof. Searches run (all negative):
exhaustive `A ⊆ [2,25]`, `|A| ≤ 4`, `m ≤ 6·max A + 20` (`scout/c488.py`); a 2-minute random search over sets with
`max A ≤ 60`, `|A| ≤ 12`, `m ≤ 4·max A` (`scout/c488b.py`). Best ratio seen is 1.983 from
singletons `A = {a}`, `n = 2a−1`, `m = 2a`, which tends to 2 but never reaches it. Easy partial
result: if `A ⊆ (n/2, n]` the claim holds, since the count at `m` is `≤ Σ ⌊m/a⌋ < 2m|A|/n` and the
count at `n` is `≥ |A|`. Any counterexample needs elements `≤ n/2` and a cleverer structure.
Effort: unknown; a bigger structured search is cheap, a proof is research. P(close) ≈ 2 %.

### 4. `Erdos883.erdos_883.parts.i`  — category (c), all-`n` statement, small cases verified true

```lean
theorem erdos_883.parts.i :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  sorry
```

Site: `kind: open`, `liveAgents 0`. The statement is for **all** `n` with floor arithmetic, so a
small counterexample would refute it. Exhaustive check (`scout/c883.c`, every `A` of size
threshold+1, every odd `l ≤ n/3+1`) for `3 ≤ n ≤ 31`: no counterexample. So it is not refutable by
a small witness, and a proof for all `n` is research (Sárközy has it only for large `n`).
P(close) ≈ 1 %.

### 5. `Erdos647.erdos_647`  — category (c), existential witness (none found)

```lean
theorem erdos_647 : ∃ n > 24, ⨆ m : Fin n, m + σ 0 m ≤ n + 2 := by
  sorry
```

Not queried on the site. I suspected the `⨆` binder would swallow the `≤` (making it a `Prop`
supremum, i.e. `∃ m`, trivially true with `n = 25, m = 0`). **Compiled check says no**: it
elaborates as `(⨆ m : Fin n, ↑m + σ 0 ↑m) ≤ n + 2`, the intended statement. Witness search
(`scout/c647.c`): the only `n ≤ 2·10⁸` with `max_{m<n}(m+τ(m)) ≤ n+2` are
`1,2,3,4,5,6,8,10,12,24`. No witness. P(close) < 1 %.

---

## Near-misses (one line each)

Quirk suspected, checked, not a quirk:
- `Erdos422.erdos_422.variants.well_defined`: ℕ+ truncated subtraction would make Hofstadter Q trivially total, but `IsHofstadterQ` demands `f (n-1) < n ∧ f (n-2) < n`.
- `Erdos509.erdos_509`: uncountable disc cover with junk `∑' = 0` is blocked by the `h_summable` field.
- `Erdos189.erdos_189.variants.parallelogram`: sign of `(∡ a b c).sin` is consistent with `IsCcwConvexPolygon` (defined by `(∡ pᵢ pⱼ pₖ).sign = 1`), so the area is positive.
- `Erdos197.erdos_197`: `HasMonotoneAP` on ℕ looked increasing-only (which a block construction beats), but `List.IsAPOfLengthWith` includes the reversed list.
- `Erdos151.erdos_151`: isolated vertices are excluded (`IsBigMaximalClique`); brute force over all graphs on ≤ 7 vertices gives no counterexample.
- `Erdos19.erdos_19`: `n = 0` is safe because `cover` forces `V` empty.
- `Erdos1101.erdos_1101.parts.i/ii`: `u 0 ∈ {0,1}` is excluded by coprimality / the product becoming 0.
- `Erdos312.erdos_312`: zero denominators let you pad the multiset, so sufficiently large is vacuous, but the remaining statement is still the real problem.
- `Erdos288.erdos_288`: overlapping intervals are allowed, but they give only finitely many extra solutions; finiteness still needs primes in short intervals.
- `Erdos274.erdos_274`: compares subgroup cardinalities, not indices; infinite groups give nothing (Neumann), finite case is Herzog–Schönheim.
- `Erdos647.erdos_647.variants.infinite`: `k = 0,1,2` are trivial, `k = 3` already needs Sophie-Germain-type primes.
- `Erdos1203.erdos_1203`, `Erdos495.erdos_495`, `Erdos329…converse_implication`: real `⨆`/`liminf`/`sSup` are bounded, no junk value.

Small-witness / counterexample searches, all negative:
- `Erdos49.erdos_49.variants.primes_maximal`: longest strictly-increasing-φ subset equals π(N) for all `2 ≤ N ≤ 3·10⁶`.
- `Erdos686.erdos_686.variants.four` and `.twenty_five`: no representation with `k ≤ 40`, `n ≤ 3000`.
- `Erdos699.erdos_699`: no counterexample for `n ≤ 260`.
- `Erdos677.erdos_677`: no collision for `k ≤ 40`, `n, m ≤ 4000`.
- `Erdos458.erdos_458`: a counterexample needs two prime powers in one prime gap with base product ≥ p (e.g. two prime squares); none small, unprovable in general.

Literature leads that died:
- `Erdos1154.erdos_1154.parts.i/ii`: Mauldin's subfields of every Hausdorff dimension need CH (the file already has that as a solved variant); ZFC version open.
- `Erdos672.erdos_672`: stated as the *existence* of a perfect-power AP product; Euler/Obláth/Győry et al. only give non-existence for particular `(k,l)`, so neither direction is closed.
- `Erdos501.erdos_501`, `Erdos910.erdos_910.parts.i`: CH counterexamples exist (Hechler, Rudin), so unprovable in ZFC and not refutable either.
- `Erdos143.erdos_143.parts.ii`: Koukoulopoulos–Lamzouri–Lichtman settled the other parts; the `1/(x log x)` sum remains open.
- `Erdos124.erdos124.ne_zero`: only `k = 0` was solved; `k ≥ 1` with the gcd condition is open.
- `Erdos835.erdos_835`, `Erdos835.johnson_chromaticNumber`: same open problem as the already-ruled-out `johnson` variant.

Not usable regardless: every declaration of the form `… = erdos_N.answer` (152 of the 850 mention an `answer`);
the `answer` is `sorry`, so I did not consider them.

## Files in the scout directory

`all.txt` (all 850 open statements, one per line, prefixed by file number), `t897.lean`,
`t647.lean` (compile checks), `c49.py c488.py c488b.py c686.py c699.py c677.py c883.c c151.c
c647.c` (searches).
