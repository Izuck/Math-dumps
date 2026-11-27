import FormalConjectures.OEIS.«92243»

-- Problem: Tug of war score between prime gap increases and decreases — conjecture1
-- Upstream: formal-conjectures FormalConjectures/OEIS/92243.lean:88 (declaration OeisA92243.conjecture1)
-- Witness: n = 261150 (the 0-indexed prime p_n = 3666581), where a n = 1.
-- Method: a verified bitset sieve (OMA.SieveB) evaluated by the kernel with decide +kernel.
-- The primes up to 3666581 are cut into windows of 262144 integers; each window is scored
-- by a one-pass checker in its own theorem, which keeps kernel memory per declaration small.

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
  · interval_cases i <;> simp +decide
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

theorem bl_one (x off : ℕ) (hx : x < 2) (h0 : x ≠ 0) : bl x 1 off = [off] := by
  obtain rfl : x = 1 := by omega
  simp [bl]

theorem beq_zero_of_ne {x : ℕ} (hx : x ≠ 0) : Nat.beq x 0 = false := by
  cases x with
  | zero => exact absurd rfl hx
  | succ n => rfl

/-- Extract the set bits of `x < 2 ^ 2 ^ k` by recursive halving, consing onto `acc`.
Written with raw recursors: this unfolds much faster in the kernel than
compiled structural recursion. -/
def bitsA (k : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ → List ℕ)
    (fun x off acc => Bool.rec (motive := fun _ => List ℕ) (off :: acc) acc (Nat.beq x 0))
    (fun k ih x off acc => Bool.rec (motive := fun _ => List ℕ)
      (ih (Nat.mod x (Nat.pow 2 (Nat.pow 2 k))) off
        (ih (Nat.shiftRight x (Nat.pow 2 k)) (Nat.add off (Nat.pow 2 k)) acc))
      acc (Nat.beq x 0)) k

theorem bitsA_zero (x off : ℕ) (acc : List ℕ) :
    bitsA 0 x off acc = cond (Nat.beq x 0) acc (off :: acc) := by
  cases h : Nat.beq x 0 <;> simp [bitsA, h]

theorem bitsA_succ (k x off : ℕ) (acc : List ℕ) :
    bitsA (k + 1) x off acc = cond (Nat.beq x 0) acc
      (bitsA k (x % 2 ^ 2 ^ k) off (bitsA k (Nat.shiftRight x (2 ^ k)) (off + 2 ^ k) acc)) := by
  cases h : Nat.beq x 0
  · show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl
  · show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl

theorem bitsA_eq : ∀ (k x off : ℕ) (acc : List ℕ), x < 2 ^ 2 ^ k →
    bitsA k x off acc = bl x (2 ^ k) off ++ acc := by
  intro k
  induction k with
  | zero =>
    intro x off acc hx
    rw [bitsA_zero]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false, pow_zero, bl_one x off (by simpa using hx) h0]
      rfl
  | succ k ih =>
    intro x off acc hx
    rw [bitsA_succ]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      have hW : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
      have h1 : x % 2 ^ 2 ^ k < 2 ^ 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : Nat.shiftRight x (2 ^ k) < 2 ^ 2 ^ k := by
        show x >>> (2 ^ k) < _
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, ← hW]
        exact hx
      rw [ih _ _ _ h1, ih _ _ _ h2, hW, bl_split, List.append_assoc]

theorem bl_primeBits (N W : ℕ) (hW : N + 1 ≤ W) :
    bl (primeBits N) W 0 = (List.range (N + 1)).filter (fun m => decide m.Prime) := by
  obtain ⟨t, ht⟩ : ∃ t, W = N + 1 + t := ⟨_, (Nat.add_sub_cancel' hW).symm⟩
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

/- ## Fast block extraction -/

/-- Lookup table: entry `2 ^ t % 269` holds `t`, 8 bits each. It is only a hint;
its output is checked at run time, so nothing needs to be proved about it. -/
def ctzTab : ℕ := 344455613645792824009884016410219778732632182012854712143509483596342490308005485563213424559790116626821646964098207758632324557041625634767761873660700798725050363608087935986789605340619771043795918541447810504023802993615139703147380057574925633553469149332228080126684297429042997713878859000834287993870215839652961918158764505424645017551771077353944857100337675990564876801623604351152573068923320297709419077304428150919004673947280528242183901261744620404681852451802341109378829705961953199030929553586850638014455084499624968671829527171451895342352061591847925441355712060917759692995825724540243017281334922984929744139115636356874240

/-- Candidate index of the lowest set bit of `x < 2 ^ 256`. -/
def ctz (x : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight ctzTab (Nat.mul 8 (Nat.mod (Nat.gcd x 115792089237316195423570985008687907853269984665640564039457584007913129639936) 269))) 255

theorem bl_of_lt {x m : ℕ} (hx : x < 2 ^ m) (t off : ℕ) : bl x (m + t) off = bl x m off := by
  unfold bl
  rw [List.range_add, List.filter_append]
  have h1 : List.filter (fun i => x.testBit i) (List.map (fun i => m + i) (List.range t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [Bool.not_eq_true]
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [h1, List.append_nil]

theorem bl_two_pow (t off : ℕ) : bl (2 ^ t) (t + 1) off = [off + t] := by
  unfold bl
  rw [List.range_succ, List.filter_append]
  have h1 : List.filter (fun i => (2 ^ t).testBit i) (List.range t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_range] at ha
    rw [Nat.testBit_two_pow]
    simp; omega
  have h2 : List.filter (fun i => (2 ^ t).testBit i) [t] = [t] := by
    simp [Nat.testBit_two_pow]
  rw [h1, h2]; rfl

/-- Extract the set bits of a block `x < 2 ^ 256`, lowest first, one step per set bit.
First argument is fuel. -/
def blk (f : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ → List ℕ)
    (fun _ _ tail => tail)
    (fun _ ih x off tail => Bool.rec (motive := fun _ => List ℕ)
      (Bool.rec (motive := fun _ => List ℕ)
        (bitsA 8 x off tail)
        (List.cons (Nat.add off (ctz x))
          (ih (Nat.shiftRight x (Nat.succ (ctz x))) (Nat.add off (Nat.succ (ctz x))) tail))
        (Nat.beq (Nat.mod x (Nat.pow 2 (Nat.succ (ctz x)))) (Nat.pow 2 (ctz x))))
      tail (Nat.beq x 0)) f

theorem blk_succ (f x off : ℕ) (tail : List ℕ) :
    blk (f + 1) x off tail = cond (Nat.beq x 0) tail
      (cond (Nat.beq (x % 2 ^ (ctz x + 1)) (2 ^ ctz x))
        ((off + ctz x) :: blk f (Nat.shiftRight x (ctz x + 1)) (off + (ctz x + 1)) tail)
        (bitsA 8 x off tail)) := by
  cases h : Nat.beq x 0
  · cases h2 : Nat.beq (x % 2 ^ (ctz x + 1)) (2 ^ ctz x)
    · show Bool.rec (motive := fun _ => List ℕ)
        (Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq (x % 2 ^ (ctz x + 1)) (2 ^ ctz x)))
        _ (Nat.beq x 0) = _
      rw [h, h2]; rfl
    · show Bool.rec (motive := fun _ => List ℕ)
        (Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq (x % 2 ^ (ctz x + 1)) (2 ^ ctz x)))
        _ (Nat.beq x 0) = _
      rw [h, h2]; rfl
  · show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl

theorem blk_eq : ∀ (f x m off : ℕ) (tail : List ℕ), x < 2 ^ m → m ≤ f → m ≤ 256 →
    blk f x off tail = bl x m off ++ tail := by
  intro f
  induction f with
  | zero =>
    intro x m off tail hx hm _
    obtain rfl : m = 0 := by omega
    obtain rfl : x = 0 := by simpa using hx
    rw [bl_zero]; rfl
  | succ f ih =>
    intro x m off tail hx hm hm2
    rw [blk_succ]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      cases hc : Nat.beq (x % 2 ^ (ctz x + 1)) (2 ^ ctz x)
      · rw [cond_false]
        obtain ⟨t, ht⟩ : ∃ t, 256 = m + t := ⟨_, (Nat.add_sub_cancel' hm2).symm⟩
        have hx8 : x < 2 ^ 2 ^ 8 :=
          lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [bitsA_eq _ _ _ _ hx8]
        have e : (2 : ℕ) ^ 8 = m + t := by rw [← ht]; norm_num
        rw [e, bl_of_lt hx]
      · rw [cond_true]
        have hc' : x % 2 ^ (ctz x + 1) = 2 ^ ctz x := Nat.eq_of_beq_eq_true hc
        have hle : 2 ^ ctz x ≤ x := by
          rw [← hc']; exact Nat.mod_le _ _
        have htm : ctz x < m := by
          by_contra hge
          have : 2 ^ m ≤ 2 ^ ctz x := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        obtain ⟨m', hm'⟩ : ∃ m', m = (ctz x + 1) + m' := ⟨_, (Nat.add_sub_cancel' htm).symm⟩
        have h2 : Nat.shiftRight x (ctz x + 1) < 2 ^ m' := by
          show x >>> (ctz x + 1) < _
          rw [Nat.shiftRight_eq_div_pow]
          apply Nat.div_lt_of_lt_mul
          rw [← pow_add, ← hm']
          exact hx
        rw [ih _ m' _ _ h2 (by omega) (by omega), hm', bl_split, hc', bl_two_pow]
        rfl

/-- Extract the set bits of `x < 2 ^ (256 * 2 ^ k)`: recursive halving down to
blocks of 256 bits, then `blk`. The list is produced front to back. -/
def bitsB (k : ℕ) : ℕ → ℕ → List ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → List ℕ → List ℕ)
    (fun x off acc => blk 256 x off acc)
    (fun k ih x off acc => Bool.rec (motive := fun _ => List ℕ)
      (ih (Nat.mod x (Nat.pow 2 (Nat.mul 256 (Nat.pow 2 k)))) off
        (ih (Nat.shiftRight x (Nat.mul 256 (Nat.pow 2 k)))
          (Nat.add off (Nat.mul 256 (Nat.pow 2 k))) acc))
      acc (Nat.beq x 0)) k

theorem bitsB_succ (k x off : ℕ) (acc : List ℕ) :
    bitsB (k + 1) x off acc = cond (Nat.beq x 0) acc
      (bitsB k (x % 2 ^ (256 * 2 ^ k)) off
        (bitsB k (Nat.shiftRight x (256 * 2 ^ k)) (off + 256 * 2 ^ k) acc)) := by
  cases h : Nat.beq x 0
  · show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl
  · show Bool.rec (motive := fun _ => List ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl

theorem bitsB_eq : ∀ (k x off : ℕ) (acc : List ℕ), x < 2 ^ (256 * 2 ^ k) →
    bitsB k x off acc = bl x (256 * 2 ^ k) off ++ acc := by
  intro k
  induction k with
  | zero =>
    intro x off acc hx
    show blk 256 x off acc = _
    exact blk_eq 256 x _ off acc hx (by simp) (by simp)
  | succ k ih =>
    intro x off acc hx
    rw [bitsB_succ]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      have hW : 256 * 2 ^ (k + 1) = 256 * 2 ^ k + 256 * 2 ^ k := by rw [pow_succ]; ring
      have h1 : x % 2 ^ (256 * 2 ^ k) < 2 ^ (256 * 2 ^ k) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : Nat.shiftRight x (256 * 2 ^ k) < 2 ^ (256 * 2 ^ k) := by
        show x >>> (256 * 2 ^ k) < _
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, ← hW]
        exact hx
      rw [ih _ _ _ h1, ih _ _ _ h2, hW, bl_split, List.append_assoc]

theorem width256 (N : ℕ) : N + 1 ≤ 256 * 2 ^ (Nat.log2 N - 7) := by
  have hhi : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  by_cases h : 7 ≤ Nat.log2 N
  · have e : 2 ^ (Nat.log2 N + 1) = 256 * 2 ^ (Nat.log2 N - 7) := by
      have : Nat.log2 N + 1 = 8 + (Nat.log2 N - 7) := by omega
      rw [this, pow_add]; norm_num
    omega
  · have h1 : 2 ^ (Nat.log2 N + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (Nat.log2 N - 7) := Nat.one_le_two_pow
    omega

/-- The primes `≤ N`, ascending. -/
def primeList (N : ℕ) : List ℕ := bitsB (Nat.log2 N - 7) (primeBits N) 0 []

theorem primeList_eq (N : ℕ) :
    primeList N = (List.range (N + 1)).filter (fun m => decide m.Prime) := by
  have hW := width256 N
  have hlt : primeBits N < 2 ^ (256 * 2 ^ (Nat.log2 N - 7)) :=
    lt_of_lt_of_le (primeBits_lt N) (Nat.pow_le_pow_right (by norm_num) hW)
  unfold primeList
  rw [bitsB_eq _ _ _ _ hlt, List.append_nil, bl_primeBits N _ hW]

/-- The primes in `[lo, lo + len)`, ascending, read off the sieve up to `N`
(intended use: `lo + len ≤ N + 1`). Lets a consumer split a long computation over
several declarations, since kernel memory is freed between declarations. -/
def primeSeg (N lo len : ℕ) : List ℕ :=
  bitsB (Nat.log2 len - 7) (Nat.shiftRight (primeBits N) lo % 2 ^ len) lo []

theorem primeSeg_eq (N lo len : ℕ) (h : lo + len ≤ N + 1) :
    primeSeg N lo len = (List.range' lo len).filter (fun m => decide m.Prime) := by
  have hW := width256 len
  have hy : Nat.shiftRight (primeBits N) lo % 2 ^ len < 2 ^ len :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hlt : Nat.shiftRight (primeBits N) lo % 2 ^ len < 2 ^ (256 * 2 ^ (Nat.log2 len - 7)) :=
    lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold primeSeg
  rw [bitsB_eq _ _ _ _ hlt, List.append_nil]
  obtain ⟨t, ht⟩ : ∃ t, 256 * 2 ^ (Nat.log2 len - 7) = len + t :=
    ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
  unfold bl
  rw [ht, List.range_add, List.filter_append]
  have h1 : List.filter (fun i => (Nat.shiftRight (primeBits N) lo % 2 ^ len).testBit i)
      (List.map (fun i => len + i) (List.range t)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    rw [Bool.not_eq_true]
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h2 : List.filter (fun i => (Nat.shiftRight (primeBits N) lo % 2 ^ len).testBit i)
        (List.range len) =
      List.filter ((fun m => decide m.Prime) ∘ fun i => lo + i) (List.range len) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.testBit_mod_two_pow]
    show (decide (i < len) && ((primeBits N) >>> lo).testBit i) = decide (lo + i).Prime
    rw [Nat.testBit_shiftRight, Bool.eq_iff_iff, Bool.and_eq_true, testBit_primeBits,
      decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · exact fun h => h.2.2
    · exact fun h => ⟨hi, by omega, h⟩
  rw [h1, h2, List.append_nil, ← List.filter_map, List.range'_eq_map_range]

/-- Glue lemma for splitting the specification list into slices. -/
theorem spec_append_primeSeg (N lo len : ℕ) (h : lo + len ≤ N + 1) :
    (List.range (lo + len)).filter (fun m => decide m.Prime) =
      (List.range lo).filter (fun m => decide m.Prime) ++ primeSeg N lo len := by
  rw [primeSeg_eq N lo len h, ← List.filter_append, List.range_eq_range', List.range_eq_range']
  congr 1
  have := @List.range'_append 0 lo len 1
  simp only [one_mul, zero_add] at this
  exact this.symm

/- ## Counting the set bits -/

/-- Popcounts of all bytes, 4 bits each. -/
def popTab : ℕ := 95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224

theorem popTab_spec : ∀ x, x < 256 →
    Nat.land (Nat.shiftRight popTab (Nat.mul 4 x)) 15 = (bl x 8 0).length := by
  decide +kernel

/-- Number of set bits of `x < 2 ^ (8 * 2 ^ k)`: recursive halving down to bytes,
then a table lookup. -/
def cntT (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ)
    (fun x => Bool.rec (motive := fun _ => ℕ)
      (Nat.land (Nat.shiftRight popTab (Nat.mul 4 x)) 15) 0 (Nat.beq x 0))
    (fun k ih x => Bool.rec (motive := fun _ => ℕ)
      (Nat.add (ih (Nat.mod x (Nat.pow 2 (Nat.mul 8 (Nat.pow 2 k)))))
        (ih (Nat.shiftRight x (Nat.mul 8 (Nat.pow 2 k)))))
      0 (Nat.beq x 0)) k

theorem cntT_zero (x : ℕ) :
    cntT 0 x = cond (Nat.beq x 0) 0 (Nat.land (Nat.shiftRight popTab (Nat.mul 4 x)) 15) := by
  cases h : Nat.beq x 0
  · show Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl
  · show Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl

theorem cntT_succ (k x : ℕ) :
    cntT (k + 1) x = cond (Nat.beq x 0) 0
      (cntT k (x % 2 ^ (8 * 2 ^ k)) + cntT k (Nat.shiftRight x (8 * 2 ^ k))) := by
  cases h : Nat.beq x 0
  · show Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl
  · show Bool.rec (motive := fun _ => ℕ) _ _ (Nat.beq x 0) = _
    rw [h]; rfl

theorem bl_length_off (x m off : ℕ) : (bl x m off).length = (bl x m 0).length := by
  simp [bl]

theorem cntT_eq : ∀ (k x : ℕ), x < 2 ^ (8 * 2 ^ k) →
    cntT k x = (bl x (8 * 2 ^ k) 0).length := by
  intro k
  induction k with
  | zero =>
    intro x hx
    rw [cntT_zero]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      exact popTab_spec x (by simpa using hx)
  | succ k ih =>
    intro x hx
    rw [cntT_succ]
    by_cases h0 : x = 0
    · subst h0
      rw [bl_zero]; rfl
    · rw [beq_zero_of_ne h0, cond_false]
      have hW : 8 * 2 ^ (k + 1) = 8 * 2 ^ k + 8 * 2 ^ k := by rw [pow_succ]; ring
      have h1 : x % 2 ^ (8 * 2 ^ k) < 2 ^ (8 * 2 ^ k) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have h2 : Nat.shiftRight x (8 * 2 ^ k) < 2 ^ (8 * 2 ^ k) := by
        show x >>> (8 * 2 ^ k) < _
        rw [Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, ← hW]
        exact hx
      rw [ih _ h1, ih _ h2, hW, bl_split, List.length_append,
        bl_length_off _ _ (0 + 8 * 2 ^ k)]

theorem count_width (N : ℕ) : N + 1 ≤ 8 * 2 ^ (Nat.log2 N - 2) := by
  have hhi : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  by_cases h : 2 ≤ Nat.log2 N
  · have e : 2 ^ (Nat.log2 N + 1) = 8 * 2 ^ (Nat.log2 N - 2) := by
      have : Nat.log2 N + 1 = 3 + (Nat.log2 N - 2) := by omega
      rw [this, pow_add]; norm_num
    omega
  · have h1 : 2 ^ (Nat.log2 N + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (Nat.log2 N - 2) := Nat.one_le_two_pow
    omega

/-- The number of primes `≤ N`. -/
def primeCount (N : ℕ) : ℕ := cntT (Nat.log2 N - 2) (primeBits N)

theorem primeCount_eq_spec (N : ℕ) :
    primeCount N = ((List.range (N + 1)).filter (fun m => decide m.Prime)).length := by
  have hW := count_width N
  have hlt : primeBits N < 2 ^ (8 * 2 ^ (Nat.log2 N - 2)) :=
    lt_of_lt_of_le (primeBits_lt N) (Nat.pow_le_pow_right (by norm_num) hW)
  unfold primeCount
  rw [cntT_eq _ _ hlt, bl_primeBits N _ hW]

theorem primeCount_eq_length (N : ℕ) : primeCount N = (primeList N).length := by
  rw [primeCount_eq_spec, primeList_eq]

theorem primeCount_eq (N : ℕ) : primeCount N = Nat.count Nat.Prime (N + 1) := by
  rw [primeCount_eq_spec, ← List.countP_eq_length_filter]
  rfl

end OMA.SieveB

namespace OMA.A92243

open OMA.SieveB

/-- Specification list of the primes up to N. -/
def primeListSpec (N : ℕ) : List ℕ := (List.range (N + 1)).filter (fun m => decide m.Prime)

theorem primeListSpec_eq_map (N : ℕ) :
    primeListSpec N = (List.range (Nat.count Nat.Prime (N + 1))).map (Nat.nth Nat.Prime) := by
  induction N with
  | zero =>
    have h : Nat.count Nat.Prime 1 = 0 := by
      rw [Nat.count_succ]; simp [Nat.not_prime_zero]
    rw [h]; simp [primeListSpec, List.range_succ, Nat.not_prime_zero]
  | succ N ih =>
    unfold primeListSpec at ih ⊢
    rw [List.range_succ, List.filter_append, ih, Nat.count_succ (p := Nat.Prime) (n := N + 1)]
    by_cases hp : (N + 1).Prime
    · simp [hp, List.range_succ, Nat.nth_count hp]
    · simp [hp]

theorem primeListSpec_length (N : ℕ) :
    (primeListSpec N).length = Nat.count Nat.Prime (N + 1) := by
  rw [primeListSpec_eq_map]; simp

/-- Item 1: the list is the initial segment of the prime enumeration. -/
theorem primeListSpec_getElem (N i : ℕ) (h : i < (primeListSpec N).length) :
    (primeListSpec N)[i] = Nat.nth Nat.Prime i := by
  simp [primeListSpec_eq_map]

/-- The tug-of-war score of a list of consecutive values. -/
def tugZ : List ℕ → ℤ
  | a :: b :: c :: l => (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign + tugZ (b :: c :: l)
  | _ => 0

theorem tugZ_map (f : ℕ → ℕ) (m : ℕ) :
    tugZ ((List.range (m + 2)).map f) =
      ∑ i ∈ Finset.range m, (((f (i + 2) - f (i + 1) : ℕ) : ℤ) - ((f (i + 1) - f i : ℕ) : ℤ)).sign := by
  induction m generalizing f with
  | zero => simp [List.range_succ, tugZ]
  | succ m ih =>
    have h3 : List.range (m + 1 + 2) = 0 :: 1 :: 2 :: (List.range m).map (· + 3) := by
      rw [List.range_eq_range', List.range_eq_range']
      simp [List.range'_succ, List.range'_eq_map_range, Nat.add_comm]
    have h2 : (List.range (m + 2)).map (fun i => f (i + 1)) =
        f 1 :: f 2 :: (List.range m).map (fun i => f (i + 3)) := by
      rw [List.range_eq_range', List.range_eq_range']
      simp [List.range'_succ, List.range'_eq_map_range, Nat.add_comm]
      intro a _; congr 1; omega
    have := ih (fun i => f (i + 1))
    rw [h2] at this
    rw [h3, Finset.sum_range_succ']
    simp only [List.map_cons, List.map_map, tugZ]
    rw [add_comm]
    congr 1

theorem a_eq_tugZ (n : ℕ) (hn : 2 ≤ n) :
    OeisA92243.a n = tugZ ((List.range (n + 1)).map (Nat.nth Nat.Prime)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e : m + 2 + 1 = (m + 1) + 2 := rfl
  rw [e, tugZ_map, OeisA92243.a, if_neg (by omega), Finset.sum_range_succ']
  have hI : Finset.Icc 2 (m + 2) = Finset.Ico 2 (m + 3) := by
    ext x; simp; omega
  rw [hI, Finset.sum_Ico_eq_sum_range, show m + 3 - 2 = m + 1 from rfl, Finset.sum_range_succ']
  simp only [OeisA92243.primeGap]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have e1 : 2 + (i + 1) = i + 3 := by omega
    have e2 : 2 + (i + 1) - 1 = i + 2 := by omega
    have e3 : i + 2 - 1 = i + 1 := by omega
    simp [e1, e3]

theorem tugZ_zero_zero (N n : ℕ) (hn : 1 ≤ n)
    (hlen : ((List.range (N + 1)).filter (fun m => decide m.Prime)).length = n + 1) :
    tugZ (0 :: 0 :: (List.range (N + 1)).filter (fun m => decide m.Prime)) =
      tugZ ((List.range (N + 1)).filter (fun m => decide m.Prime)) := by
  have hc : Nat.count Nat.Prime (N + 1) = n + 1 := by
    rw [← primeListSpec_length]; exact hlen
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (List.range (m + 2)).map (Nat.nth Nat.Prime) =
      2 :: 3 :: (List.range m).map (fun i => Nat.nth Nat.Prime (i + 2)) := by
    rw [List.range_eq_range', List.range_eq_range']
    simp [List.range'_succ, List.range'_eq_map_range, Nat.add_comm,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hL := primeListSpec_eq_map N
  rw [primeListSpec, hc, h2] at hL
  rw [hL]
  simp only [tugZ]
  have e1 : (((2 - 0 : ℕ) : ℤ) - ((0 - 0 : ℕ) : ℤ)).sign = 1 := by decide
  have e2 : (((3 - 2 : ℕ) : ℤ) - ((2 - 0 : ℕ) : ℤ)).sign = -1 := by decide
  rw [e1, e2]; omega

/-- Interface for a fold-style sieve: it suffices to know the number of primes `≤ N` and the
sign of the score of the prime list with two zeros prepended. -/
theorem a_pos_of_tugZ (n N : ℕ) (hn : 2 ≤ n)
    (hlen : ((List.range (N + 1)).filter (fun m => decide m.Prime)).length = n + 1)
    (hpos : 0 < tugZ (0 :: 0 :: (List.range (N + 1)).filter (fun m => decide m.Prime))) :
    0 < OeisA92243.a n := by
  have hc : Nat.count Nat.Prime (N + 1) = n + 1 := by
    rw [← primeListSpec_length]; exact hlen
  rw [tugZ_zero_zero N n (by omega) hlen] at hpos
  rw [a_eq_tugZ n hn, ← hc, ← primeListSpec_eq_map]
  exact hpos

/-- Kernel-friendly one-pass scorer. `a b` are the last two values seen, `cnt` counts the
remaining elements down, `bal` is the running score (offset); both counters are forced by
pattern matching at every step. At the end the state is compared with `a' b' cnt' bal'`. -/
def run (a' b' cnt' bal' : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], a, b, cnt, bal => Nat.beq a a' && Nat.beq b b' && Nat.beq cnt cnt' && Nat.beq bal bal'
  | _ :: _, _, _, 0, _ => false
  | _ :: _, _, _, _ + 1, 0 => false
  | c :: l, a, b, cnt + 1, bal + 1 =>
    bif Nat.blt (b - a) (c - b) then run a' b' cnt' bal' l b c cnt (bal + 2)
    else bif Nat.blt (c - b) (b - a) then run a' b' cnt' bal' l b c cnt bal
    else run a' b' cnt' bal' l b c cnt (bal + 1)

theorem run_sound (a' b' cnt' bal' : ℕ) (l : List ℕ) : ∀ (a b cnt bal : ℕ),
    run a' b' cnt' bal' l a b cnt bal = true →
    cnt = cnt' + l.length ∧
      ∀ l2, tugZ (a :: b :: (l ++ l2)) + bal = tugZ (a' :: b' :: l2) + bal' := by
  induction l with
  | nil =>
    intro a b cnt bal h
    simp only [run, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
      Nat.eq_of_beq_eq_true h4]
    simp
  | cons c l ih =>
    intro a b cnt bal h
    rcases cnt with _ | cnt
    · simp [run] at h
    rcases bal with _ | bal
    · simp [run] at h
    simp only [run] at h
    simp only [tugZ, List.length_cons, List.cons_append]
    by_cases h1 : b - a < c - b
    · rw [show Nat.blt (b - a) (c - b) = true by rw [Nat.blt_eq]; exact h1, cond_true] at h
      obtain ⟨hl, hb⟩ := ih b c cnt (bal + 2) h
      have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = 1 := Int.sign_eq_one_of_pos (by omega)
      refine ⟨by omega, fun l2 => ?_⟩
      have := hb l2
      rw [hs]; push_cast at this ⊢; omega
    · rw [show Nat.blt (b - a) (c - b) = false by
        rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h1, cond_false] at h
      by_cases h2 : c - b < b - a
      · rw [show Nat.blt (c - b) (b - a) = true by rw [Nat.blt_eq]; exact h2, cond_true] at h
        obtain ⟨hl, hb⟩ := ih b c cnt bal h
        have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = -1 :=
          Int.sign_eq_neg_one_of_neg (by omega)
        refine ⟨by omega, fun l2 => ?_⟩
        have := hb l2
        rw [hs]; push_cast at this ⊢; omega
      · rw [show Nat.blt (c - b) (b - a) = false by
          rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h2, cond_false] at h
        obtain ⟨hl, hb⟩ := ih b c cnt (bal + 1) h
        have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = 0 := by
          rw [show ((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ) = 0 by omega]; rfl
        refine ⟨by omega, fun l2 => ?_⟩
        have := hb l2
        rw [hs]; push_cast at this ⊢; omega

/-- `Reach c0 K lo a b c d`: scoring the primes below `lo`, starting from the virtual state
`0, 0` with `c0` primes still expected and score offset `K`, ends with last two values `a b`,
`c` primes still expected and offset score `d`. -/
def Reach (c0 K lo a b c d : ℕ) : Prop :=
  c0 = c + ((List.range lo).filter (fun m => decide m.Prime)).length ∧
    ∀ l2, tugZ (0 :: 0 :: ((List.range lo).filter (fun m => decide m.Prime) ++ l2)) + (K : ℤ) =
      tugZ (a :: b :: l2) + (d : ℤ)

theorem reach_zero (c0 K : ℕ) : Reach c0 K 0 0 0 c0 K := by
  simp [Reach]

theorem reach_step (N : ℕ) {c0 K lo len a b c d a' b' c' d' : ℕ} (r : Reach c0 K lo a b c d)
    (h : run a' b' c' d' (primeSeg N lo len) a b c d = true) (hN : lo + len ≤ N + 1)
    (lo' : ℕ) (hlo : lo + len = lo') : Reach c0 K lo' a' b' c' d' := by
  subst hlo
  obtain ⟨r1, r2⟩ := r
  obtain ⟨s1, s2⟩ := run_sound _ _ _ _ _ _ _ _ _ h
  unfold Reach
  rw [spec_append_primeSeg N lo len hN]
  refine ⟨by rw [List.length_append]; omega, fun l2 => ?_⟩
  rw [List.append_assoc, r2, s2]

/-- The reduction: a certified scoring run over all primes `≤ N` proves `a n > 0`. -/
theorem a_pos_of_reach (n N K a b d : ℕ) (hn : 2 ≤ n) (r : Reach (n + 1) K (N + 1) a b 0 d)
    (hK : K < d) : 0 < OeisA92243.a n := by
  obtain ⟨r1, r2⟩ := r
  have e := r2 []
  rw [List.append_nil] at e
  have e7 : tugZ [a, b] = 0 := rfl
  exact a_pos_of_tugZ n N hn (by omega) (by omega)

end OMA.A92243

namespace OMA.A92243

open OMA.SieveB

set_option maxHeartbeats 0 in
/-- All windows are checked inside ONE proof so that the kernel runs them one after another
(separate theorems would be checked in parallel and add up their memory). -/
theorem reach_all : Reach 261151 1000 3666582 3666539 3666581 0 1001 := by
  have r := reach_zero 261151 1000
  have w : run 262133 262139 238151 1053 (primeSeg 3666581 0 262144) 0 0 261151 1000 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (262144) (by norm_num)
  clear w
  have w : run 524269 524287 217761 1005 (primeSeg 3666581 262144 262144) 262133 262139 238151 1053 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (524288) (by norm_num)
  clear w
  have w : run 786419 786431 198205 1043 (primeSeg 3666581 524288 262144) 524269 524287 217761 1005 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (786432) (by norm_num)
  clear w
  have w : run 1048571 1048573 179126 1092 (primeSeg 3666581 786432 262144) 786419 786431 198205 1043 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (1048576) (by norm_num)
  clear w
  have w : run 1310693 1310719 160365 1135 (primeSeg 3666581 1048576 262144) 1048571 1048573 179126 1092 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (1310720) (by norm_num)
  clear w
  have w : run 1572841 1572853 141883 1057 (primeSeg 3666581 1310720 262144) 1310693 1310719 160365 1135 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (1572864) (by norm_num)
  clear w
  have w : run 1834999 1835003 123627 938 (primeSeg 3666581 1572864 262144) 1572841 1572853 141883 1057 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (1835008) (by norm_num)
  clear w
  have w : run 2097133 2097143 105540 879 (primeSeg 3666581 1835008 262144) 1834999 1835003 123627 938 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (2097152) (by norm_num)
  clear w
  have w : run 2359261 2359267 87637 857 (primeSeg 3666581 2097152 262144) 2097133 2097143 105540 879 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (2359296) (by norm_num)
  clear w
  have w : run 2621387 2621431 69843 723 (primeSeg 3666581 2359296 262144) 2359261 2359267 87637 857 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (2621440) (by norm_num)
  clear w
  have w : run 2883563 2883577 52137 750 (primeSeg 3666581 2621440 262144) 2621387 2621431 69843 723 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (2883584) (by norm_num)
  clear w
  have w : run 3145711 3145721 34602 806 (primeSeg 3666581 2883584 262144) 2883563 2883577 52137 750 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (3145728) (by norm_num)
  clear w
  have w : run 3407851 3407857 17082 814 (primeSeg 3666581 3145728 262144) 3145711 3145721 34602 806 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (3407872) (by norm_num)
  clear w
  have w : run 3666539 3666581 0 1001 (primeSeg 3666581 3407872 258710) 3407851 3407857 17082 814 = true := by
    decide +kernel
  have r := reach_step 3666581 r w (by norm_num) (3666582) (by norm_num)
  clear w
  exact r

end OMA.A92243

theorem OMA.solution : type_of% @OeisA92243.conjecture1 :=
  ⟨261150, by norm_num, OMA.A92243.a_pos_of_reach 261150 3666581 1000 3666539 3666581 1001 (by norm_num)
    OMA.A92243.reach_all (by norm_num)⟩
