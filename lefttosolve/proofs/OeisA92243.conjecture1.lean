import FormalConjectures.OEIS.«92243»

-- Problem: Tug of war score between prime gap increases and decreases — conjecture1
-- Upstream: formal-conjectures FormalConjectures/OEIS/92243.lean:88 (declaration OeisA92243.conjecture1)
-- Witness: n = 261150 (0-indexed prime 3666581), a n = 1.
-- STATUS: partial. Everything is proved except the final kernel computation, which needs a
-- verified fast sieve (primeList_eq) swapped in for the filter over List.range.

namespace OMA.A92243

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

/-- Kernel-friendly checker: `cnt` counts the remaining elements down, `bal` is the running score
offset by `K`; both are forced by pattern matching at every step. -/
def chk (K : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ → Bool
  | _, _, [], cnt, bal => Nat.beq cnt 0 && Nat.blt K bal
  | _, _, _ :: _, 0, _ => false
  | _, _, _ :: _, _ + 1, 0 => false
  | a, b, c :: l, cnt + 1, bal + 1 =>
    bif Nat.blt (b - a) (c - b) then chk K b c l cnt (bal + 2)
    else bif Nat.blt (c - b) (b - a) then chk K b c l cnt bal
    else chk K b c l cnt (bal + 1)

theorem chk_sound (K : ℕ) (l : List ℕ) : ∀ (a b cnt bal : ℕ), chk K a b l cnt bal = true →
    l.length = cnt ∧ (K : ℤ) < bal + tugZ (a :: b :: l) := by
  induction l with
  | nil =>
    intro a b cnt bal h
    simp only [chk, Bool.and_eq_true, Nat.blt_eq] at h
    simp [tugZ, h.2, (Nat.eq_of_beq_eq_true h.1)]
  | cons c l ih =>
    intro a b cnt bal h
    rcases cnt with _ | cnt
    · simp [chk] at h
    rcases bal with _ | bal
    · simp [chk] at h
    simp only [chk] at h
    simp only [tugZ, List.length_cons]
    by_cases h1 : b - a < c - b
    · rw [show Nat.blt (b - a) (c - b) = true by rw [Nat.blt_eq]; exact h1, cond_true] at h
      obtain ⟨hl, hb⟩ := ih b c cnt (bal + 2) h
      have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = 1 := Int.sign_eq_one_of_pos (by omega)
      rw [hs]; push_cast at hb ⊢; omega
    · rw [show Nat.blt (b - a) (c - b) = false by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h1, cond_false] at h
      by_cases h2 : c - b < b - a
      · rw [show Nat.blt (c - b) (b - a) = true by rw [Nat.blt_eq]; exact h2, cond_true] at h
        obtain ⟨hl, hb⟩ := ih b c cnt bal h
        have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = -1 :=
          Int.sign_eq_neg_one_of_neg (by omega)
        rw [hs]; push_cast at hb ⊢; omega
      · rw [show Nat.blt (c - b) (b - a) = false by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h2, cond_false] at h
        obtain ⟨hl, hb⟩ := ih b c cnt (bal + 1) h
        have hs : (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign = 0 := by
          rw [show ((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ) = 0 by omega]; rfl
        rw [hs]; push_cast at hb ⊢; omega

/-- `tugCheck K n L = true` certifies `L.length = n + 1` and `tugZ L > 0`. -/
def tugCheck (K n : ℕ) : List ℕ → Bool
  | a :: b :: l => chk K a b l (n - 1) K
  | _ => false

theorem tugCheck_sound (K n : ℕ) (hn : 1 ≤ n) (L : List ℕ) (h : tugCheck K n L = true) :
    L.length = n + 1 ∧ 0 < tugZ L := by
  match L, h with
  | a :: b :: l, h =>
    obtain ⟨hl, hb⟩ := chk_sound K l a b (n - 1) K h
    refine ⟨by simp [hl]; omega, by omega⟩

/-- The reduction: one kernel computation on the list of primes up to `N` proves `a n > 0`. -/
theorem a_pos_of_check (K n N : ℕ) (hn : 2 ≤ n)
    (h : tugCheck K n ((List.range (N + 1)).filter (fun m => decide m.Prime)) = true) :
    0 < OeisA92243.a n := by
  obtain ⟨hl, hpos⟩ := tugCheck_sound K n (by omega) _ h
  have hc : Nat.count Nat.Prime (N + 1) = n + 1 := by
    rw [← primeListSpec_length]; exact hl
  rw [a_eq_tugZ n hn, ← hc, ← primeListSpec_eq_map]
  exact hpos

end OMA.A92243

theorem OMA.solution : type_of% @OeisA92243.conjecture1 :=
  ⟨261150, by norm_num, OMA.A92243.a_pos_of_check 1000 261150 3666581 (by norm_num) (by
    -- to do: rw [← primeList_eq]; decide +kernel
    sorry)⟩
