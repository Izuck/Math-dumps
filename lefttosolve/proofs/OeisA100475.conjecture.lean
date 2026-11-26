import FormalConjectures.OEIS.«100475»

-- Problem: Prime-th recurrence with reversal at each step (OEIS A100475), DISPROOF.
-- Upstream: formal-conjectures FormalConjectures/OEIS/100475.lean (declaration OeisA100475.conjecture)
-- Idea: k -> reverse(p_k) never shortens the decimal length, so a periodic tail has constant
-- length d and lives among k with 10^(d-1) <= k <= pi(10^d). Since pi(10^d) < 10^(d-1) for
-- d >= 5 (kernel-sieved counts at 10^5, 10^6, 2*10^6 plus the Chebyshev bound theta(x) <= x log 4),
-- every tail entry is <= pi(10^4) = 1229, and a kernel check shows each such orbit leaves [1,1229].

namespace OMA.SieveB

/- ## Geometric-series bit masks -/

/-- `geo d m` has exactly the bits `d * j`, `j < m`. -/
def geo (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 ^ (d * m) + geo d m

theorem geo_mul (d m : ℕ) : geo d m * (2 ^ d - 1) + 1 = 2 ^ (d * m) := by
  induction m with
  | zero => simp [geo]
  | succ m ih =>
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h2 : 2 ^ (d * (m + 1)) = 2 ^ (d * m) * 2 ^ d := by rw [Nat.mul_succ, pow_add]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ d = k + 1 := ⟨2 ^ d - 1, by omega⟩
    rw [h2, geo, add_mul, add_assoc, ih, hk, Nat.add_sub_cancel]
    ring

theorem geo_lt {d : ℕ} (hd : 0 < d) (m : ℕ) : geo d m < 2 ^ (d * m) := by
  have h := geo_mul d m
  have h1 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : geo d m ≤ geo d m * (2 ^ d - 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem testBit_geo {d : ℕ} (hd : 0 < d) (m i : ℕ) :
    (geo d m).testBit i = true ↔ d ∣ i ∧ i < d * m := by
  induction m with
  | zero => simp [geo]
  | succ m ih =>
    have h : geo d (m + 1) = 2 ^ (d * m) * 1 ||| geo d m := by
      rw [← Nat.two_pow_add_eq_or_of_lt (geo_lt hd m) 1, mul_one, geo]
    rw [h, Nat.testBit_lor, mul_one, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨dvd_mul_right _ _, by rw [Nat.mul_succ]; omega⟩
      · exact ⟨h1, by rw [Nat.mul_succ]; omega⟩
    · rintro ⟨⟨q, rfl⟩, h2⟩
      have hq : q < m + 1 := Nat.lt_of_mul_lt_mul_left h2
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | rfl
      · exact Or.inr ⟨dvd_mul_right _ _, Nat.mul_lt_mul_of_pos_left hq hd⟩
      · exact Or.inl rfl

theorem div_eq_geo {d : ℕ} (hd : 0 < d) (L : ℕ) :
    (2 ^ L - 1) / (2 ^ d - 1) = 2 ^ (L % d) * geo d (L / d) := by
  have hg := geo_mul d (L / d)
  have hL : 2 ^ L = 2 ^ (L % d) * 2 ^ (d * (L / d)) := by
    rw [← pow_add, Nat.mod_add_div]
  have hr : 2 ^ (L % d) < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt _ hd)
  have hr1 : 1 ≤ 2 ^ (L % d) := Nat.one_le_two_pow
  have key : 2 ^ L = 2 ^ (L % d) * geo d (L / d) * (2 ^ d - 1) + 2 ^ (L % d) := by
    rw [hL, ← hg]; ring
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [add_mul, one_mul]; omega

/-- The bits `d * j`, `j < L / d`, computed with one big division and one shift
from the shared numerator `M = 2 ^ L - 1`. -/
def mask (M L d : ℕ) : ℕ := Nat.shiftRight (M / (2 ^ d - 1)) (L % d)

theorem testBit_mask {d : ℕ} (hd : 0 < d) (L i : ℕ) :
    (mask (2 ^ L - 1) L d).testBit i = true ↔ d ∣ i ∧ i < d * (L / d) := by
  have h : mask (2 ^ L - 1) L d = geo d (L / d) := by
    unfold mask
    rw [div_eq_geo hd]
    show (2 ^ (L % d) * geo d (L / d)) >>> (L % d) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  rw [h, testBit_geo hd]

/- ## The sieve -/

/-- Or together the masks of all `p < d` whose bit is set in `S`. The outer `cond`
only forces evaluation of the accumulator. -/
def comp (M L S : ℕ) : ℕ → ℕ → ℕ
  | 0, C => C
  | d + 1, C =>
    cond (Nat.beq C 0)
      (comp M L S d (cond (S.testBit d) (Nat.lor C (mask M L d)) C))
      (comp M L S d (cond (S.testBit d) (Nat.lor C (mask M L d)) C))

theorem testBit_comp (M L S : ℕ) : ∀ (d C i : ℕ),
    (comp M L S d C).testBit i = true ↔
      C.testBit i = true ∨ ∃ p, p < d ∧ S.testBit p = true ∧ (mask M L p).testBit i = true := by
  intro d
  induction d with
  | zero => intro C i; simp [comp]
  | succ d ih =>
    intro C i
    rw [comp, Bool.cond_self, ih]
    cases hS : S.testBit d
    · simp only [cond_false]
      constructor
      · rintro (h | ⟨p, hp, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p, Nat.lt_succ_of_lt hp, h1, h2⟩
      · rintro (h | ⟨p, hp, h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
          · exact Or.inr ⟨p, hp, h1, h2⟩
          · rw [hS] at h1; cases h1
    · simp only [cond_true]
      have hl : (Nat.lor C (mask M L d)).testBit i =
          (C.testBit i || (mask M L d).testBit i) := Nat.testBit_lor _ _ _
      rw [hl, Bool.or_eq_true]
      constructor
      · rintro ((h | h) | ⟨p, hp, h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨d, Nat.lt_succ_self d, hS, h⟩
        · exact Or.inr ⟨p, Nat.lt_succ_of_lt hp, h1, h2⟩
      · rintro (h | ⟨p, hp, h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
          · exact Or.inr ⟨p, hp, h1, h2⟩
          · exact Or.inl (Or.inr h2)

/-- One sieve level: `S` is the bitset of primes `≤ R`, where `N < R * R` and `R ≤ N`. -/
def sieveStep (N R S : ℕ) : ℕ :=
  Nat.lor
    (Nat.xor (2 ^ (N + 1) - 1)
      (Nat.lor (comp (2 ^ (N + R) - 1) (N + R) S (R + 1) 0) 2 % 2 ^ (N + 1)))
    S

theorem testBit_two (i : ℕ) : Nat.testBit 2 i = decide (i = 1) := by
  have h := @Nat.testBit_two_pow 1 i
  rw [pow_one] at h
  rw [h]
  simp [eq_comm]

theorem testBit_sieveStep {N R S : ℕ} (hR2 : 2 ≤ R) (hRN : R ≤ N) (hN : N < R * R)
    (hS : ∀ i, S.testBit i = true ↔ i ≤ R ∧ i.Prime) (i : ℕ) :
    (sieveStep N R S).testBit i = true ↔ i ≤ N ∧ i.Prime := by
  have hC : ∀ j, (comp (2 ^ (N + R) - 1) (N + R) S (R + 1) 0).testBit j = true ↔
      ∃ p, p ≤ R ∧ p.Prime ∧ p ∣ j ∧ j < p * ((N + R) / p) := by
    intro j
    rw [testBit_comp]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨p, _, h1, h2⟩
      have hp := (hS p).mp h1
      have := (testBit_mask hp.2.pos (N + R) j).mp h2
      exact ⟨p, hp.1, hp.2, this.1, this.2⟩
    · rintro ⟨p, h1, h2, h3, h4⟩
      exact ⟨p, Nat.lt_succ_of_le h1, (hS p).mpr ⟨h1, h2⟩,
        (testBit_mask h2.pos (N + R) j).mpr ⟨h3, h4⟩⟩
  have hl : (sieveStep N R S).testBit i =
      (((2 ^ (N + 1) - 1) ^^^
        ((comp (2 ^ (N + R) - 1) (N + R) S (R + 1) 0 ||| 2) % 2 ^ (N + 1))).testBit i
        || S.testBit i) := Nat.testBit_lor _ _ _
  rw [hl, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
    Nat.testBit_lor, testBit_two]
  have hmark : ∀ p, p.Prime → p ≤ R → ∀ j, j ≤ N → p ∣ j → j < p * ((N + R) / p) := by
    intro p hp hpR j hj _
    have h1 := Nat.mod_add_div (N + R) p
    have h2 := Nat.mod_lt (N + R) hp.pos
    omega
  constructor
  · intro h
    rcases Bool.or_eq_true _ _ |>.mp h with h | h
    · by_cases hi : i < N + 1
      · have hiN : i ≤ N := Nat.lt_succ_iff.mp hi
        simp only [hi, decide_true, Bool.true_and, Bool.true_xor, Bool.not_eq_true',
          Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
        obtain ⟨h1, h2⟩ := h
        have h1' : ¬ ∃ p, p ≤ R ∧ p.Prime ∧ p ∣ i ∧ i < p * ((N + R) / p) := by
          rw [← hC]; simp [h1]
        refine ⟨hiN, ?_⟩
        by_contra hnp
        apply h1'
        have hi0 : i ≠ 0 := by
          rintro rfl
          exact h1' ⟨2, hR2, Nat.prime_two, dvd_zero _,
            hmark 2 Nat.prime_two hR2 0 (Nat.zero_le _) (dvd_zero _)⟩
        have hi2 : 2 ≤ i := by omega
        have hp := Nat.minFac_prime h2
        have hsq : i.minFac * i.minFac ≤ i := by
          have := Nat.minFac_sq_le_self (by omega) hnp
          rwa [sq] at this
        have hpR : i.minFac ≤ R := by
          by_contra hlt
          have hlt' : R < i.minFac := Nat.lt_of_not_le hlt
          have : R * R < i.minFac * i.minFac := Nat.mul_lt_mul'' hlt' hlt'
          omega
        exact ⟨i.minFac, hpR, hp, Nat.minFac_dvd i,
          hmark _ hp hpR i hiN (Nat.minFac_dvd i)⟩
      · simp [hi] at h
    · have := (hS i).mp h
      exact ⟨le_trans this.1 hRN, this.2⟩
  · rintro ⟨hiN, hip⟩
    by_cases hiR : i ≤ R
    · rw [(hS i).mpr ⟨hiR, hip⟩]; simp
    · have hi : i < N + 1 := Nat.lt_succ_of_le hiN
      have h1 : (comp (2 ^ (N + R) - 1) (N + R) S (R + 1) 0).testBit i = false := by
        rw [← Bool.not_eq_true, hC]
        rintro ⟨p, hpR, hp, hpi, _⟩
        have := (Nat.prime_dvd_prime_iff_eq hp hip).mp hpi
        omega
      have h2 : i ≠ 1 := hip.ne_one
      simp [hi, h1, h2]

/-- Primes below 16 as a bitset. -/
theorem testBit_base (N i : ℕ) (hN : N < 16) :
    (10412 % 2 ^ (N + 1)).testBit i = true ↔ i ≤ N ∧ i.Prime := by
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq, Nat.lt_succ_iff]
  by_cases hi : i < 16
  · interval_cases i <;> simp (decide := true)
  · have : Nat.testBit 10412 i = false := by
      apply Nat.testBit_lt_two_pow
      calc 10412 < 2 ^ 16 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [this]
    constructor
    · rintro ⟨_, h⟩; cases h
    · rintro ⟨h, _⟩; omega

/-- Recursive sieve: the primes `≤ N` as a bitset. First argument is fuel. -/
def pb : ℕ → ℕ → ℕ
  | 0, N => 10412 % 2 ^ (N + 1)
  | f + 1, N =>
    cond (Nat.ble 16 N)
      (sieveStep N (2 ^ (Nat.log2 N / 2 + 1)) (pb f (2 ^ (Nat.log2 N / 2 + 1))))
      (10412 % 2 ^ (N + 1))

theorem testBit_pb : ∀ (f N : ℕ), N ≤ f → ∀ i,
    (pb f N).testBit i = true ↔ i ≤ N ∧ i.Prime := by
  intro f
  induction f with
  | zero =>
    intro N hN i
    rw [pb]
    exact testBit_base N i (by omega)
  | succ f ih =>
    intro N hN i
    rw [pb]
    by_cases h16 : 16 ≤ N
    · have hb : Nat.ble 16 N = true := Nat.ble_eq_true_of_le h16
      rw [hb, cond_true]
      have hN0 : N ≠ 0 := by omega
      have hl4 : 4 ≤ Nat.log2 N := by
        by_contra hlt
        have h1 : Nat.log2 N < 4 := Nat.lt_of_not_le hlt
        have := (Nat.log2_lt hN0).mp h1
        omega
      have hlo : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le hN0
      have hhi : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
      have hR2 : 2 ≤ 2 ^ (Nat.log2 N / 2 + 1) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (Nat.log2 N / 2 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hRlt : 2 ^ (Nat.log2 N / 2 + 1) < N := by
        calc 2 ^ (Nat.log2 N / 2 + 1) < 2 ^ Nat.log2 N :=
              Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ ≤ N := hlo
      have hsq : N < 2 ^ (Nat.log2 N / 2 + 1) * 2 ^ (Nat.log2 N / 2 + 1) := by
        rw [← pow_add]
        calc N < 2 ^ (Nat.log2 N + 1) := hhi
          _ ≤ 2 ^ (Nat.log2 N / 2 + 1 + (Nat.log2 N / 2 + 1)) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
      exact testBit_sieveStep hR2 (le_of_lt hRlt) hsq (ih _ (by omega)) i
    · have hb : Nat.ble 16 N = false := by
        rw [← Bool.not_eq_true, Nat.ble_eq]; exact h16
      rw [hb, cond_false]
      exact testBit_base N i (by omega)

/-- Bitset of the primes `≤ N`. -/
def primeBits (N : ℕ) : ℕ := pb N N

theorem testBit_primeBits (N i : ℕ) : (primeBits N).testBit i = true ↔ i ≤ N ∧ i.Prime :=
  testBit_pb N N (le_refl N) i

theorem primeBits_lt (N : ℕ) : primeBits N < 2 ^ (N + 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [← Bool.not_eq_true, testBit_primeBits]
  rintro ⟨h, _⟩
  omega

/- ## Listing the set bits -/

/-- Specification: positions `< m` of the set bits of `x`, shifted by `off`, ascending. -/
def bl (x m off : ℕ) : List ℕ :=
  ((List.range m).filter (fun i => x.testBit i)).map (fun i => off + i)

theorem bl_zero (m off : ℕ) : bl 0 m off = [] := by
  simp [bl]

theorem bl_split (x a b off : ℕ) :
    bl x (a + b) off = bl (x % 2 ^ a) a off ++ bl (Nat.shiftRight x a) b (off + a) := by
  unfold bl
  rw [List.range_add, List.filter_append, List.map_append, List.filter_map, List.map_map]
  congr 1
  · congr 1
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  · have h1 : ((fun i => x.testBit i) ∘ fun x => a + x) =
        fun i => (Nat.shiftRight x a).testBit i := by
      funext i
      show x.testBit (a + i) = (x >>> a).testBit i
      rw [Nat.testBit_shiftRight]
    rw [h1]
    apply List.map_congr_left
    intro i _
    simp [add_assoc]

theorem bl_top {x m : ℕ} (hx : x ≠ 0) (hm : x < 2 ^ m) (off : ℕ) :
    bl x m off = bl (x - 2 ^ Nat.log2 x) (Nat.log2 x) off ++ [off + Nat.log2 x] := by
  have hlt : Nat.log2 x < m := (Nat.log2_lt hx).mpr hm
  have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le hx
  have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  obtain ⟨t, rfl⟩ : ∃ t, m = Nat.log2 x + 1 + t := ⟨m - (Nat.log2 x + 1), by omega⟩
  unfold bl
  rw [List.range_add, List.filter_append, List.range_succ, List.filter_append]
  have h1 : List.filter (fun i => x.testBit i)
      (List.map (fun i => Nat.log2 x + 1 + i) (List.range t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [Bool.not_eq_true]
    apply Nat.testBit_lt_two_pow
    calc x < 2 ^ (Nat.log2 x + 1) := hhi
      _ ≤ 2 ^ (Nat.log2 x + 1 + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : List.filter (fun i => x.testBit i) [Nat.log2 x] = [Nat.log2 x] := by
    simp [Nat.testBit_log2 hx]
  have h3 : List.filter (fun i => x.testBit i) (List.range (Nat.log2 x)) =
      List.filter (fun i => (x - 2 ^ Nat.log2 x).testBit i) (List.range (Nat.log2 x)) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    have hxe : x = 2 ^ Nat.log2 x + (x - 2 ^ Nat.log2 x) := by omega
    conv_lhs => rw [hxe]
    exact Nat.testBit_two_pow_add_gt hi _
  rw [h1, h2, h3]
  simp

/-- Extract the set bits of a small word, highest first, consing onto `acc`.
First argument is fuel (any bound on the bit length). -/
def bitsBlock : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, acc => acc
  | f + 1, x, off, acc =>
    cond (Nat.beq x 0) acc
      (bitsBlock f (x - 2 ^ Nat.log2 x) off ((off + Nat.log2 x) :: acc))

theorem beq_zero_of_ne {x : ℕ} (hx : x ≠ 0) : Nat.beq x 0 = false := by
  cases x with
  | zero => exact absurd rfl hx
  | succ n => rfl

theorem bitsBlock_eq : ∀ (f x m off : ℕ) (acc : List ℕ), x < 2 ^ m → m ≤ f →
    bitsBlock f x off acc = bl x m off ++ acc := by
  intro f
  induction f with
  | zero =>
    intro x m off acc hx hm
    obtain rfl : m = 0 := by omega
    simp [bitsBlock, bl]
  | succ f ih =>
    intro x m off acc hx hm
    rw [bitsBlock]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      have hlt : Nat.log2 x < m := (Nat.log2_lt h0).mpr hx
      have hlo : 2 ^ Nat.log2 x ≤ x := Nat.log2_self_le h0
      have hhi : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
      have hx' : x - 2 ^ Nat.log2 x < 2 ^ Nat.log2 x := by
        rw [pow_succ] at hhi; omega
      rw [ih _ (Nat.log2 x) off _ hx' (by omega), bl_top h0 hx off]
      simp

/-- Extract the set bits of `x < 2 ^ (B * 2 ^ k)` by recursive halving down to
blocks of `B` bits. -/
def bitsAux (B : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, x, off, acc => bitsBlock B x off acc
  | k + 1, x, off, acc =>
    cond (Nat.beq x 0) acc
      (bitsAux B k (x % 2 ^ (B * 2 ^ k)) off
        (bitsAux B k (Nat.shiftRight x (B * 2 ^ k)) (off + B * 2 ^ k) acc))

theorem bitsAux_eq (B : ℕ) : ∀ (k x off : ℕ) (acc : List ℕ), x < 2 ^ (B * 2 ^ k) →
    bitsAux B k x off acc = bl x (B * 2 ^ k) off ++ acc := by
  intro k
  induction k with
  | zero =>
    intro x off acc hx
    rw [bitsAux]
    exact bitsBlock_eq B x _ off acc hx (by simp)
  | succ k ih =>
    intro x off acc hx
    rw [bitsAux]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      have hW : B * 2 ^ (k + 1) = B * 2 ^ k + B * 2 ^ k := by rw [pow_succ]; ring
      have h1 : x % 2 ^ (B * 2 ^ k) < 2 ^ (B * 2 ^ k) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : Nat.shiftRight x (B * 2 ^ k) < 2 ^ (B * 2 ^ k) := by
        show x >>> (B * 2 ^ k) < _
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, ← hW]
        exact hx
      rw [ih _ _ _ h1, ih _ _ _ h2, hW, bl_split, List.append_assoc]

theorem primeList_width (N : ℕ) : N + 1 ≤ 1024 * 2 ^ (Nat.log2 N - 9) := by
  have hhi : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  by_cases h : 9 ≤ Nat.log2 N
  · have e : 2 ^ (Nat.log2 N + 1) = 1024 * 2 ^ (Nat.log2 N - 9) := by
      have : Nat.log2 N + 1 = 10 + (Nat.log2 N - 9) := by omega
      rw [this, pow_add]; norm_num
    omega
  · have h1 : 2 ^ (Nat.log2 N + 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (Nat.log2 N - 9) := Nat.one_le_two_pow
    omega

/-- The primes `≤ N`, ascending. -/
def primeList (N : ℕ) : List ℕ := bitsAux 1024 (Nat.log2 N - 9) (primeBits N) 0 []

theorem primeList_eq (N : ℕ) :
    primeList N = (List.range (N + 1)).filter (fun m => decide m.Prime) := by
  have hW : N + 1 ≤ 1024 * 2 ^ (Nat.log2 N - 9) := primeList_width N
  have hlt : primeBits N < 2 ^ (1024 * 2 ^ (Nat.log2 N - 9)) :=
    lt_of_lt_of_le (primeBits_lt N) (Nat.pow_le_pow_right (by norm_num) hW)
  unfold primeList
  rw [bitsAux_eq _ _ _ _ _ hlt, List.append_nil]
  obtain ⟨t, ht⟩ : ∃ t, 1024 * 2 ^ (Nat.log2 N - 9) = N + 1 + t := ⟨_, (Nat.add_sub_cancel' hW).symm⟩
  unfold bl
  rw [ht, List.range_add, List.filter_append]
  have h1 : List.filter (fun i => (primeBits N).testBit i)
      (List.map (fun i => N + 1 + i) (List.range t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [testBit_primeBits]
    rintro ⟨h, _⟩
    omega
  have h2 : List.filter (fun i => (primeBits N).testBit i) (List.range (N + 1)) =
      List.filter (fun m => decide m.Prime) (List.range (N + 1)) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [Bool.eq_iff_iff, testBit_primeBits, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  rw [h1, h2]
  simp

/- ## Counting the set bits -/

def cntBlock : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, x => cond (Nat.beq x 0) 0 (cntBlock f (x - 2 ^ Nat.log2 x) + 1)

theorem length_bitsBlock : ∀ (f x off : ℕ) (acc : List ℕ),
    (bitsBlock f x off acc).length = cntBlock f x + acc.length := by
  intro f
  induction f with
  | zero => intro x off acc; simp [bitsBlock, cntBlock]
  | succ f ih =>
    intro x off acc
    rw [bitsBlock, cntBlock]
    cases Nat.beq x 0
    · simp only [cond_false]
      rw [ih, List.length_cons]; omega
    · simp

def cntAux (B : ℕ) : ℕ → ℕ → ℕ
  | 0, x => cntBlock B x
  | k + 1, x =>
    cond (Nat.beq x 0) 0
      (cntAux B k (x % 2 ^ (B * 2 ^ k)) + cntAux B k (Nat.shiftRight x (B * 2 ^ k)))

theorem length_bitsAux (B : ℕ) : ∀ (k x off : ℕ) (acc : List ℕ),
    (bitsAux B k x off acc).length = cntAux B k x + acc.length := by
  intro k
  induction k with
  | zero => intro x off acc; rw [bitsAux, cntAux, length_bitsBlock]
  | succ k ih =>
    intro x off acc
    rw [bitsAux, cntAux]
    cases Nat.beq x 0
    · simp only [cond_false]
      rw [ih, ih]; omega
    · simp

/-- The number of primes `≤ N`. -/
def primeCount (N : ℕ) : ℕ := cntAux 1024 (Nat.log2 N - 9) (primeBits N)

theorem primeCount_eq_length (N : ℕ) : primeCount N = (primeList N).length := by
  unfold primeCount primeList
  rw [length_bitsAux]; rfl

theorem primeCount_eq (N : ℕ) : primeCount N = Nat.count Nat.Prime (N + 1) := by
  rw [primeCount_eq_length, primeList_eq, ← List.countP_eq_length_filter]
  rfl

end OMA.SieveB

namespace OMA.A100475
open OeisA100475

/-- decimal length -/
def len (k : ℕ) : ℕ := (Nat.digits 10 k).length

lemma len_eq_zero {k : ℕ} : len k = 0 ↔ k = 0 := by
  unfold len
  rw [List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]

lemma len_mono {a b : ℕ} (h : a ≤ b) : len a ≤ len b := Nat.le_length_digits_le 10 a b h

lemma len_reverse {m : ℕ} (h : m % 10 ≠ 0) : len (reverseDigits m) = len m := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at h
    · exact h0
  unfold len reverseDigits
  rw [Nat.digits_ofDigits 10 (by norm_num)]
  · simp
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
  · intro hne
    rw [List.getLast_reverse]
    simp only [Nat.digits_def' (by norm_num : 1 < 10) hm, List.head_cons]
    exact h

lemma prime_mod_ten {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ p := Nat.dvd_of_mod_eq_zero h
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (dvd_trans (by norm_num) h10)
  have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp (dvd_trans (by norm_num) h10)
  omega

/-- one step of the recurrence, for a positive index -/
noncomputable def step (k : ℕ) : ℕ := reverseDigits (Nat.nth Nat.Prime (k - 1))

lemma len_step (k : ℕ) : len (step k) = len (Nat.nth Nat.Prime (k - 1)) :=
  len_reverse (prime_mod_ten (Nat.prime_nth_prime _))

lemma le_nth_pred (k : ℕ) : k ≤ Nat.nth Nat.Prime (k - 1) := by
  have := Nat.add_two_le_nth_prime (k - 1)
  omega

lemma len_le_len_step (k : ℕ) : len k ≤ len (step k) := by
  rw [len_step]; exact len_mono (le_nth_pred k)

lemma step_pos (k : ℕ) : 0 < step k := by
  rcases Nat.eq_zero_or_pos (step k) with h | h
  · have h1 := len_step k
    rw [h] at h1
    have h2 : len (Nat.nth Nat.Prime (k - 1)) = 0 := by rw [← h1]; exact len_eq_zero.mpr rfl
    have h3 := len_eq_zero.mp h2
    have := (Nat.prime_nth_prime (k - 1)).pos
    omega
  · exact h

lemma aStartAt_succ (x n : ℕ) :
    aStartAt x (n + 1) = if aStartAt x n = 0 then 0 else step (aStartAt x n) := rfl

lemma aStartAt_pos {x : ℕ} (hx : 0 < x) (n : ℕ) : 0 < aStartAt x n := by
  induction n with
  | zero => exact hx
  | succ n ih => rw [aStartAt_succ, if_neg (by omega)]; exact step_pos _

lemma aStartAt_succ_pos {x : ℕ} (hx : 0 < x) (n : ℕ) :
    aStartAt x (n + 1) = step (aStartAt x n) := by
  rw [aStartAt_succ, if_neg (by have := aStartAt_pos hx n; omega)]

lemma len_aStartAt_mono {x : ℕ} (hx : 0 < x) {m n : ℕ} (h : m ≤ n) :
    len (aStartAt x m) ≤ len (aStartAt x n) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => rw [aStartAt_succ_pos hx]; exact ih.trans (len_le_len_step _)

/-- In a periodic tail, the length of an entry equals the length of the prime it indexes. -/
lemma tail_len {x : ℕ} (hx : 0 < x) {N P : ℕ} (hP : 0 < P)
    (hper : ∀ n, n ≥ N → aStartAt x (n + P) = aStartAt x n) {n : ℕ} (hn : n ≥ N) :
    len (Nat.nth Nat.Prime (aStartAt x n - 1)) = len (aStartAt x n) := by
  rw [← len_step, ← aStartAt_succ_pos hx]
  apply le_antisymm
  · have := len_aStartAt_mono hx (show n + 1 ≤ n + P by omega)
    rwa [hper n hn] at this
  · exact len_aStartAt_mono hx (Nat.le_succ n)

/-- Key counting step: if `k > 0` and `p_k` have the same decimal length `d`, then
`10 ^ d ≤ 10 * k` and `k ≤ π (10 ^ d)`. -/
lemma same_len_bounds {k : ℕ} (hk : 0 < k) (h : len (Nat.nth Nat.Prime (k - 1)) = len k) :
    10 ^ len k ≤ 10 * k ∧ k ≤ Nat.primeCounting (10 ^ len k) := by
  constructor
  · exact Nat.base_pow_length_digits_le 10 k (by norm_num) (by omega)
  · have h1 : Nat.nth Nat.Prime (k - 1) < 10 ^ len k := by
      rw [← h]; exact Nat.lt_base_pow_length_digits (by norm_num)
    have h2 := (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).mpr h1
    have h3 : Nat.count Nat.Prime (10 ^ len k) ≤ Nat.count Nat.Prime (10 ^ len k + 1) :=
      Nat.count_monotone _ (Nat.le_succ _)
    have h4 : k - 1 < Nat.count Nat.Prime (10 ^ len k + 1) := lt_of_lt_of_le h2 h3
    show k ≤ Nat.count Nat.Prime (10 ^ len k + 1)
    omega

/-- Every entry of a periodic tail is at most `π (10 ^ 4)`, given the `π` bounds. -/
lemma tail_le (HPi : ∀ d, 5 ≤ d → 10 * Nat.primeCounting (10 ^ d) < 10 ^ d)
    {x : ℕ} (hx : 0 < x) {N P : ℕ} (hP : 0 < P)
    (hper : ∀ n, n ≥ N → aStartAt x (n + P) = aStartAt x n) {n : ℕ} (hn : n ≥ N) :
    aStartAt x n ≤ Nat.primeCounting (10 ^ 4) := by
  have hk := aStartAt_pos hx n
  obtain ⟨h1, h2⟩ := same_len_bounds hk (tail_len hx hP hper hn)
  by_cases hd : 5 ≤ len (aStartAt x n)
  · have := HPi _ hd
    omega
  · refine h2.trans (Nat.monotone_primeCounting ?_)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)


/-- trial division, valid below `101 ^ 2` -/
def isP (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 101).all
    (fun m => !(decide (2 ≤ m) && decide (m * m ≤ n) && decide (n % m = 0)))

lemma isP_iff {n : ℕ} (hn : n < 10201) : isP n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [isP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun m hm hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    have hm101 : m < 101 := by nlinarith
    have := hall m hm101
    simp [hm, hmm, Nat.mod_eq_zero_of_dvd hdvd] at this
  · rintro ⟨h2, hall⟩
    refine ⟨h2, fun m _ => ?_⟩
    by_contra hc
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or,
      not_not] at hc
    obtain ⟨⟨hm, hmm⟩, hmod⟩ := hc
    exact hall m hm (Nat.le_sqrt.mpr hmm) (Nat.dvd_of_mod_eq_zero hmod)

/-- the primes below `10 ^ 4` -/
def primes4 : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
  179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
  283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
  547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
  661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
  811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
  1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
  1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
  1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
  1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657,
  1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
  1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987,
  1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
  2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287,
  2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423,
  2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617,
  2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
  2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903,
  2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079,
  3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257,
  3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
  3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571,
  3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727,
  3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907,
  3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
  4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231,
  4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409,
  4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583,
  4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751,
  4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937,
  4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087,
  5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279,
  5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443,
  5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639,
  5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791,
  5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939,
  5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133,
  6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301,
  6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473,
  6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673,
  6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833,
  6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997,
  7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207,
  7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411,
  7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561,
  7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723,
  7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919,
  7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111,
  8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291,
  8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501,
  8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677,
  8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831,
  8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011,
  9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199,
  9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377,
  9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533,
  9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733,
  9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887,
  9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

lemma primes4_eq_isP : (List.range 10001).filter isP = primes4 := by decide +kernel

lemma primes4_eq : (List.range 10001).filter (fun m => decide m.Prime) = primes4 := by
  rw [← primes4_eq_isP]
  apply List.filter_congr
  intro m hm
  rw [List.mem_range] at hm
  rw [Bool.eq_iff_iff, decide_eq_true_eq, isP_iff (by omega)]

lemma length_filter_eq_count (N : ℕ) :
    ((List.range N).filter (fun m => decide m.Prime)).length = Nat.count Nat.Prime N := by
  simp [Nat.count, List.countP_eq_length_filter]

lemma primeCounting_eq_length (n : ℕ) :
    Nat.primeCounting n = ((List.range (n + 1)).filter (fun m => decide m.Prime)).length :=
  (length_filter_eq_count (n + 1)).symm

lemma nth_eq_getD (N i : ℕ)
    (hi : i < ((List.range N).filter (fun m => decide m.Prime)).length) :
    Nat.nth Nat.Prime i = ((List.range N).filter (fun m => decide m.Prime)).getD i 0 := by
  induction N with
  | zero => simp at hi
  | succ N ih =>
    rw [List.range_succ, List.filter_append] at hi ⊢
    by_cases hN : N.Prime
    · have hs : List.filter (fun m => decide m.Prime) [N] = [N] := by simp [hN]
      rw [hs] at hi ⊢
      by_cases hlt : i < ((List.range N).filter (fun m => decide m.Prime)).length
      · rw [List.getD_append _ _ _ _ hlt]; exact ih hlt
      · have hieq : i = ((List.range N).filter (fun m => decide m.Prime)).length := by
          simp only [List.length_append, List.length_singleton] at hi; omega
        rw [List.getD_append_right _ _ _ _ (by omega), hieq, Nat.sub_self,
          length_filter_eq_count, Nat.nth_count hN]
        rfl
    · have hs : List.filter (fun m => decide m.Prime) [N] = [] := by simp [hN]
      rw [hs, List.append_nil] at hi ⊢
      exact ih hi

lemma primeCounting_four : Nat.primeCounting (10 ^ 4) = 1229 := by
  rw [primeCounting_eq_length]
  show ((List.range 10001).filter (fun m => decide m.Prime)).length = 1229
  rw [primes4_eq]; decide +kernel

/-- digit reversal with fuel -/
def revAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | f + 1, n, acc => if n = 0 then acc else revAux f (n / 10) (acc * 10 + n % 10)

lemma revAux_eq (f : ℕ) : ∀ n acc : ℕ, n ≤ f →
    revAux f n acc = Nat.ofDigits 10 (Nat.digits 10 n).reverse
      + acc * 10 ^ (Nat.digits 10 n).length := by
  induction f with
  | zero => intro n acc h; obtain rfl : n = 0 := by omega
            simp [revAux]
  | succ f ih =>
    intro n acc h
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [revAux]
    · rw [revAux, if_neg (by omega), ih _ _ (by omega),
        Nat.digits_def' (by norm_num : 1 < 10) h0 (n := n)]
      simp only [List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton,
        List.length_reverse, List.length_cons]
      ring

lemma reverseDigits_eq (n : ℕ) : reverseDigits n = revAux n n 0 := by
  rw [revAux_eq n n 0 le_rfl]; simp [reverseDigits]

/-- computable step -/
def stepC (k : ℕ) : ℕ := revAux (primes4.getD (k - 1) 0) (primes4.getD (k - 1) 0) 0

lemma nth_eq_primes4 {k : ℕ} (hk : k ≤ 1229) (hk0 : 0 < k) :
    Nat.nth Nat.Prime (k - 1) = primes4.getD (k - 1) 0 := by
  have h := nth_eq_getD 10001 (k - 1) (by
    rw [primes4_eq]
    have : primes4.length = 1229 := by decide +kernel
    omega)
  rw [h, primes4_eq]

/-- `esc f k`: the orbit of `k` leaves `[1, 1229]` within `f` steps -/
def esc : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, k => if k = 0 ∨ 1229 < k then true else esc f (stepC k)

lemma esc_all : (List.range 1230).all (esc 12) = true := by decide +kernel


lemma pi_sub_mul_log_le {a b : ℕ} (hab : a ≤ b) :
    ((Nat.primeCounting b : ℝ) - Nat.primeCounting a) * Real.log a
      ≤ Chebyshev.theta b - Chebyshev.theta a := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have hsub : Nat.primesLE a ⊆ Nat.primesLE b := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans hab, hp.2⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right,
    ← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    ← Finset.cast_card_sdiff hsub, ← nsmul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro p hp
  rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
  have hap : a < p := by
    by_contra h
    exact hp.2 ⟨by omega, hp.1.2⟩
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0
    simpa using Real.log_natCast_nonneg p
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hap.le)

lemma step_bound {a b : ℕ} (hab : a ≤ b) (T : ℝ) (hT : T ≤ Chebyshev.theta a) :
    ((Nat.primeCounting b : ℝ) - Nat.primeCounting a) * Real.log a
      ≤ 2 * Real.log 2 * b - T := by
  have h1 := pi_sub_mul_log_le hab
  have h2 := Chebyshev.theta_le_log4_mul_x (x := (b : ℝ)) (Nat.cast_nonneg b)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  rw [h4] at h2
  linarith

lemma log_ratio (m n : ℕ) (h : (2 : ℝ) ^ m < 10 ^ n) :
    m * Real.log 2 < n * Real.log 10 := by
  have := Real.log_lt_log (by positivity) h
  rwa [Real.log_pow, Real.log_pow] at this

lemma log10_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
lemma log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- induction step, valid from `d = 7` on -/
lemma pi_step {d : ℕ} (hd : 7 ≤ d) (h : 10 * Nat.primeCounting (10 ^ d) < 10 ^ d) :
    10 * Nat.primeCounting (10 ^ (d + 1)) < 10 ^ (d + 1) := by
  have hs := step_bound (a := 10 ^ d) (b := 10 ^ (d + 1))
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d)) 0 (Chebyshev.theta_nonneg _)
  push_cast at hs
  rw [Real.log_pow] at hs
  have hA : (10 : ℝ) * Nat.primeCounting (10 ^ d) < 10 ^ d := by exact_mod_cast h
  generalize (Nat.primeCounting (10 ^ d) : ℝ) = A at hs hA
  suffices hB : (Nat.primeCounting (10 ^ (d + 1)) : ℝ) < 10 ^ d by
    have : (10 : ℝ) * Nat.primeCounting (10 ^ (d + 1)) < 10 ^ (d + 1) := by
      have hp : (10 : ℝ) ^ (d + 1) = 10 ^ d * 10 := pow_succ _ _
      linarith
    exact_mod_cast this
  generalize (Nat.primeCounting (10 ^ (d + 1)) : ℝ) = B at hs ⊢
  have hX : (0 : ℝ) < 10 ^ d := by positivity
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (10 : ℝ) ^ (d + 1) = 10 ^ d * 10 := pow_succ _ _
  rw [hp] at hs
  generalize (10 : ℝ) ^ d = X at hs hA hX ⊢
  have hlog := log_ratio 13 4 (by norm_num)
  push_cast at hlog
  have hL := log10_pos
  by_cases hBA : B ≤ A
  · linarith
  · have hBA' : 0 < B - A := by linarith
    have e1 : (B - A) * 7 * Real.log 10 ≤ (B - A) * d * Real.log 10 := by
      have := mul_le_mul_of_nonneg_left hd' hBA'.le
      exact mul_le_mul_of_nonneg_right this hL.le
    have e2 : 20 * X * (13 * Real.log 2) < 20 * X * (4 * Real.log 10) :=
      mul_lt_mul_of_pos_left hlog (by linarith)
    have e3 : (B - A) * 91 * Real.log 10 < 80 * X * Real.log 10 := by nlinarith
    have e4 : (B - A) * 91 < 80 * X := lt_of_mul_lt_mul_right e3 hL.le
    linarith

lemma pi_all (h7 : 10 * Nat.primeCounting (10 ^ 7) < 10 ^ 7) :
    ∀ d, 7 ≤ d → 10 * Nat.primeCounting (10 ^ d) < 10 ^ d := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact h7
  | succ n hn ih => exact pi_step hn ih

/-- `π (10 ^ 7) < 10 ^ 6` from prime counts up to `2 * 10 ^ 6` only. -/
lemma pi_seven (K5 : Nat.primeCounting 100000 = 9592) (K6 : Nat.primeCounting 1000000 = 78498)
    (K2 : Nat.primeCounting 2000000 = 148933) :
    10 * Nat.primeCounting (10 ^ 7) < 10 ^ 7 := by
  have t1 := pi_sub_mul_log_le (a := 100000) (b := 1000000) (by norm_num)
  have t2 := pi_sub_mul_log_le (a := 1000000) (b := 2000000) (by norm_num)
  have t0 := Chebyshev.theta_nonneg ((100000 : ℕ) : ℝ)
  have l5 : Real.log ((100000 : ℕ) : ℝ) = 5 * Real.log 10 := by
    have : ((100000 : ℕ) : ℝ) = 10 ^ 5 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have l6 : Real.log ((1000000 : ℕ) : ℝ) = 6 * Real.log 10 := by
    have : ((1000000 : ℕ) : ℝ) = 10 ^ 6 := by norm_num
    rw [this, Real.log_pow]; push_cast; ring
  have l2 : Real.log ((2000000 : ℕ) : ℝ) = Real.log 2 + 6 * Real.log 10 := by
    have : ((2000000 : ℕ) : ℝ) = 2 * 10 ^ 6 := by norm_num
    rw [this, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  rw [K5, K6, l5] at t1
  rw [K6, K2, l6] at t2
  have hT : (767140 : ℝ) * Real.log 10 ≤ Chebyshev.theta ((2000000 : ℕ) : ℝ) := by
    push_cast at t1 t2 t0 ⊢
    linarith
  have hs := step_bound (a := 2000000) (b := 10 ^ 7) (by norm_num) _ hT
  rw [K2, l2] at hs
  have hlog := log_ratio 33 10 (by norm_num)
  have hL := log10_pos
  have h2 := log2_pos
  suffices hB : (Nat.primeCounting (10 ^ 7) : ℝ) < 10 ^ 6 by
    have : Nat.primeCounting (10 ^ 7) < 10 ^ 6 := by exact_mod_cast hB
    omega
  generalize (Nat.primeCounting (10 ^ 7) : ℝ) = B at hs ⊢
  push_cast at hs hlog
  by_contra hc
  have hc' : (851067 : ℝ) ≤ B - 148933 := by linarith
  have e1 := mul_le_mul_of_nonneg_right hc' (by linarith : (0 : ℝ) ≤ Real.log 2 + 6 * Real.log 10)
  linarith

lemma pi_bounds (K5 : Nat.primeCounting 100000 = 9592) (K6 : Nat.primeCounting 1000000 = 78498)
    (K2 : Nat.primeCounting 2000000 = 148933) :
    ∀ d, 5 ≤ d → 10 * Nat.primeCounting (10 ^ d) < 10 ^ d := by
  intro d hd
  by_cases h7 : 7 ≤ d
  · exact pi_all (pi_seven K5 K6 K2) d h7
  · have hd' : d = 5 ∨ d = 6 := by omega
    rcases hd' with rfl | rfl
    · rw [show (10 : ℕ) ^ 5 = 100000 by norm_num, K5]; norm_num
    · rw [show (10 : ℕ) ^ 6 = 1000000 by norm_num, K6]; norm_num


/-! ### Assembly -/

lemma esc_false (HPi : ∀ d, 5 ≤ d → 10 * Nat.primeCounting (10 ^ d) < 10 ^ d)
    {x : ℕ} (hx : 0 < x) {N P : ℕ} (hP : 0 < P)
    (hper : ∀ n, n ≥ N → aStartAt x (n + P) = aStartAt x n) :
    ∀ f n, n ≥ N → esc f (aStartAt x n) = false := by
  intro f
  induction f with
  | zero => intro n _; rfl
  | succ f ih =>
    intro n hn
    have hpos := aStartAt_pos hx n
    have hle := tail_le HPi hx hP hper hn
    rw [primeCounting_four] at hle
    have hstep : stepC (aStartAt x n) = aStartAt x (n + 1) := by
      rw [aStartAt_succ_pos hx, step, nth_eq_primes4 hle hpos, reverseDigits_eq]
      rfl
    rw [esc, if_neg (by omega), hstep]
    exact ih (n + 1) (by omega)

/-- The disproof, with the prime-counting bounds as a hypothesis. -/
theorem no_loop (HPi : ∀ d, 5 ≤ d → 10 * Nat.primeCounting (10 ^ d) < 10 ^ d) :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨x, hx, -, N, P, hP, hper⟩
  have hpos := aStartAt_pos hx N
  have hle := tail_le HPi hx hP hper (le_refl N)
  rw [primeCounting_four] at hle
  have h1 := esc_false HPi hx hP hper 12 N (le_refl N)
  have h2 := List.all_eq_true.mp esc_all (aStartAt x N) (List.mem_range.mpr (by omega))
  rw [h1] at h2
  exact Bool.false_ne_true h2

/-- The disproof from three prime counts, stated on the slow reference list. -/
theorem no_loop_of_counts
    (K5 : ((List.range (100000 + 1)).filter (fun m => decide m.Prime)).length = 9592)
    (K6 : ((List.range (1000000 + 1)).filter (fun m => decide m.Prime)).length = 78498)
    (K2 : ((List.range (2000000 + 1)).filter (fun m => decide m.Prime)).length = 148933) :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) :=
  no_loop (pi_bounds ((primeCounting_eq_length _).trans K5)
    ((primeCounting_eq_length _).trans K6) ((primeCounting_eq_length _).trans K2))

end OMA.A100475


namespace OMA.A100475

lemma pc_of_sieve {n c : ℕ} (h : OMA.SieveB.primeCount n = c) : Nat.primeCounting n = c := by
  rw [← h, OMA.SieveB.primeCount_eq]; rfl

theorem count5 : OMA.SieveB.primeCount 100000 = 9592 := by decide +kernel

theorem count6 : OMA.SieveB.primeCount 1000000 = 78498 := by decide +kernel

theorem count2 : OMA.SieveB.primeCount 2000000 = 148933 := by decide +kernel

end OMA.A100475

theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) :=
  OMA.A100475.no_loop (OMA.A100475.pi_bounds (OMA.A100475.pc_of_sieve OMA.A100475.count5)
    (OMA.A100475.pc_of_sieve OMA.A100475.count6) (OMA.A100475.pc_of_sieve OMA.A100475.count2))
