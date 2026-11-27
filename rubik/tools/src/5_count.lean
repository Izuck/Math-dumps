/-! ## Stage 3b: counting canonical move sequences

A sequence is canonical if no two consecutive moves turn the same face and, for two
consecutive moves on opposite faces, the `U`/`R`/`F` one comes first.  `C k o` is the set of
states produced by canonical sequences of length `k` whose last face is `o`. -/

def axis : Face → Fin 3 | .U => 0 | .D => 0 | .R => 1 | .L => 1 | .F => 2 | .B => 2
def hi : Face → Bool | .U => false | .D => true | .R => false | .L => true | .F => false | .B => true

/-- May a move of face `f` follow a move of face `o` (or start the sequence, `o = none`)? -/
def allowed : Option Face → Face → Bool
  | none, _ => true
  | some g, f => decide (axis g ≠ axis f) || (!hi g && hi f)

def C : ℕ → Option Face → Finset Cube
  | 0, none => {1}
  | 0, some _ => ∅
  | _ + 1, none => ∅
  | k + 1, some f => (Finset.univ.filter (fun o => allowed o f = true)).biUnion fun o =>
      (C k o).biUnion fun s => Finset.univ.image fun j : Fin 3 => s * q f ^ (j.val + 1)

theorem mem_C_succ {k : ℕ} {f : Face} {s : Cube} : s ∈ C (k + 1) (some f) ↔
    ∃ o, allowed o f = true ∧ ∃ t ∈ C k o, ∃ j : Fin 3, t * q f ^ (j.val + 1) = s := by
  simp [C]

theorem mem_succ {k : ℕ} {o : Option Face} {f : Face} {t : Cube} (j : Fin 3)
    (ha : allowed o f = true) (ht : t ∈ C k o) : t * q f ^ (j.val + 1) ∈ C (k + 1) (some f) :=
  mem_C_succ.mpr ⟨o, ha, t, ht, j, rfl⟩

theorem pow_merge (f : Face) (i j : Fin 3) : q f ^ (i.val + 1) * q f ^ (j.val + 1) = 1 ∨
    ∃ j' : Fin 3, q f ^ (i.val + 1) * q f ^ (j.val + 1) = q f ^ (j'.val + 1) := by
  rw [← pow_add, pow_eq_pow_mod (i.val + 1 + (j.val + 1)) (q_pow_four f)]
  have : (i.val + 1 + (j.val + 1)) % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize (i.val + 1 + (j.val + 1)) % 4 = n at this
  interval_cases n
  · left; simp
  · right; exact ⟨0, rfl⟩
  · right; exact ⟨1, rfl⟩
  · right; exact ⟨2, rfl⟩

/-- Turns of opposite faces commute. -/
theorem bad_comm : ∀ g f, allowed (some g) f = false → g ≠ f → q g * q f = q f * q g := by
  decide +kernel
theorem bad_allowed : ∀ g f, allowed (some g) f = false → g ≠ f → allowed (some f) g = true := by
  decide
theorem bad_pred : ∀ o g f, allowed (some g) f = false → g ≠ f → allowed o g = true →
    o ≠ some f → allowed o f = true := by decide
theorem bad_pred' : ∀ o g f, allowed (some g) f = false → g ≠ f → allowed o f = true →
    allowed o g = true := by decide

/-- Appending a move to a canonical sequence gives a state that has a canonical sequence which
is not longer (merge equal faces, sort opposite faces). -/
theorem C_step {k : ℕ} {o : Option Face} {s : Cube} (hs : s ∈ C k o) (f : Face) (j : Fin 3) :
    ∃ k' ≤ k + 1, ∃ o', s * q f ^ (j.val + 1) ∈ C k' o' := by
  rcases o with _ | g
  · exact ⟨k + 1, le_rfl, some f, mem_succ j rfl hs⟩
  by_cases ha : allowed (some g) f = true
  · exact ⟨k + 1, le_rfl, some f, mem_succ j ha hs⟩
  rw [Bool.not_eq_true] at ha
  rcases k with _ | k0
  · simp [C] at hs
  obtain ⟨o0, ha0, t, ht, i, rfl⟩ := mem_C_succ.mp hs
  by_cases hgf : g = f
  · subst hgf
    rw [mul_assoc]
    rcases pow_merge g i j with h | ⟨j', h⟩
    · rw [h, mul_one]; exact ⟨k0, by omega, o0, ht⟩
    · rw [h]; exact ⟨k0 + 1, by omega, some g, mem_succ j' ha0 ht⟩
  have comm : q g ^ (i.val + 1) * q f ^ (j.val + 1) = q f ^ (j.val + 1) * q g ^ (i.val + 1) :=
    ((show Commute (q g) (q f) from bad_comm g f ha hgf).pow_pow _ _).eq
  rw [mul_assoc, comm, ← mul_assoc]
  by_cases h0 : o0 = some f
  · subst h0
    rcases k0 with _ | k1
    · simp [C] at ht
    obtain ⟨o1, ha1, u, hu, i2, rfl⟩ := mem_C_succ.mp ht
    rw [mul_assoc u]
    rcases pow_merge f i2 j with h | ⟨j', h⟩
    · rw [h, mul_one]
      exact ⟨k1 + 1, by omega, some g, mem_succ i (bad_pred' o1 g f ha hgf ha1) hu⟩
    · rw [h]
      exact ⟨k1 + 2, by omega, some g, mem_succ i (bad_allowed g f ha hgf) (mem_succ j' ha1 hu)⟩
  · have h1 : allowed o0 f = true := bad_pred o0 g f ha hgf ha0 h0
    exact ⟨k0 + 2, le_rfl, some g, mem_succ i (bad_allowed g f ha hgf) (mem_succ j h1 ht)⟩

/-- Every state produced by a sequence of length `n` lies in some `C k o` with `k ≤ n`. -/
theorem evalSeq_mem_C (l : List Move) : ∃ k ≤ l.length, ∃ o, evalSeq l ∈ C k o := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨0, le_rfl, none, by simp [C, evalSeq]⟩
  | append_singleton l m ih =>
    obtain ⟨k, hk, o, h⟩ := ih
    obtain ⟨k', hk', o', h'⟩ := C_step h m.face m.k
    refine ⟨k', ?_, o', ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [evalSeq_append, evalSeq_singleton]; exact h'

/-- `(bd k) = (n, a, b)`: bounds for `|C k none|`, `|C k (some f)|` for `f ∈ {U,R,F}`, resp.
`f ∈ {D,L,B}`. -/
def bd : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | k + 1 => (0, 3 * ((bd k).1 + 2 * (bd k).2.1 + 2 * (bd k).2.2),
      3 * ((bd k).1 + 3 * (bd k).2.1 + 2 * (bd k).2.2))

def N (k : ℕ) : Option Face → ℕ
  | none => (bd k).1
  | some f => if hi f then (bd k).2.2 else (bd k).2.1

theorem face_sum (g : Face → ℕ) : ∑ f, g f = g .U + g .D + g .R + g .L + g .F + g .B := by
  show Finset.sum {Face.U, .D, .R, .L, .F, .B} g = _
  simp [Finset.sum_insert, add_assoc]

theorem card_C_le : ∀ k o, (C k o).card ≤ N k o := by
  intro k
  induction k with
  | zero => intro o; cases o <;> simp [C, N, bd]
  | succ k ih =>
    intro o
    rcases o with _ | f
    · simp [C]
    calc (C (k + 1) (some f)).card
        ≤ ∑ o ∈ Finset.univ.filter (fun o => allowed o f = true), 3 * N k o := by
          unfold C
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun o _ => ?_)
          refine Finset.card_biUnion_le.trans ?_
          calc ∑ s ∈ C k o, (Finset.univ.image fun j : Fin 3 => s * q f ^ (j.val + 1)).card
              ≤ ∑ _s ∈ C k o, 3 := Finset.sum_le_sum fun s _ => by
                  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)))
                    (f := fun j : Fin 3 => s * q f ^ (j.val + 1))
            _ = (C k o).card * 3 := by simp
            _ ≤ 3 * N k o := by have := ih o; omega
      _ = N (k + 1) (some f) := by
          rw [Finset.sum_filter, Fintype.sum_option, face_sum]
          cases f <;> simp [allowed, axis, hi, N, bd] <;> ring

/-- All states at distance at most `n`. -/
def ball (n : ℕ) : Finset Cube :=
  (Finset.range (n + 1)).biUnion fun k => Finset.univ.biUnion fun o => C k o

/-- Number of canonical sequences of length at most `n`: `1, 19, 262, 3502, …`. -/
def tot : ℕ → ℕ
  | 0 => 1
  | k + 1 => tot k + ((bd (k + 1)).1 + 3 * (bd (k + 1)).2.1 + 3 * (bd (k + 1)).2.2)

theorem card_ball_le (n : ℕ) : (ball n).card ≤ tot n := by
  have h1 : ∀ k, (Finset.univ.biUnion fun o => C k o).card
      ≤ (bd k).1 + 3 * (bd k).2.1 + 3 * (bd k).2.2 := by
    intro k
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun o _ => card_C_le k o).trans ?_)
    rw [Fintype.sum_option, face_sum]
    simp [N, hi]; omega
  have h2 : ∀ n, ∑ k ∈ Finset.range (n + 1), ((bd k).1 + 3 * (bd k).2.1 + 3 * (bd k).2.2) = tot n := by
    intro n
    induction n with
    | zero => simp [bd, tot]
    | succ n ih => rw [Finset.sum_range_succ, ih]; rfl
  exact Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun k _ => h1 k).trans (h2 n).le)

theorem mem_ball_of_dist_le {s : Cube} {n : ℕ} (hs : Reachable s) (h : dist s ≤ n) : s ∈ ball n := by
  obtain ⟨l, hl, rfl⟩ := dist_spec hs
  obtain ⟨k, hk, o, hC⟩ := evalSeq_mem_C l
  simp only [ball, Finset.mem_biUnion, Finset.mem_range, Finset.mem_univ, true_and]
  exact ⟨k, by omega, o, hC⟩

theorem subset_ball (P : Finset Cube) (n : ℕ) (h : ∀ s ∈ P, Reachable s ∧ dist s ≤ n) :
    P ⊆ ball n := fun s hs => mem_ball_of_dist_le (h s hs).1 (h s hs).2

theorem tot_17 : tot 17 = 19973266111335481264 := by decide +kernel

/-- At most `19973266111335481264` states are within 17 moves of the solved cube. -/
theorem card_ball_17 : (ball 17).card ≤ 19973266111335481264 := tot_17 ▸ card_ball_le 17

/-! ## Main results -/

/-- **A state is reachable by face turns iff it satisfies the three invariants.** -/
theorem reachable_iff_valid (s : Cube) : Reachable s ↔ Valid s := by
  classical
  refine ⟨Reachable.valid, fun hs => ?_⟩
  obtain ⟨P, hP, hcard⟩ := exists_reachable_finset
  have hsub : P ⊆ Finset.univ.filter Valid := fun x hx => by
    simpa using (hP x hx).1.valid
  have hV : (Finset.univ.filter Valid).card = 43252003274489856000 := by
    rw [← card_valid, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have := Finset.eq_of_subset_of_card_le hsub (by rw [hV, hcard])
  exact (hP s (this ▸ by simpa using hs)).1

/-- **The cube group has `43252003274489856000 = 8! * 3^7 * 12! * 2^10` elements.** -/
theorem card_reachable : Nat.card {s // Reachable s} = 43252003274489856000 := by
  rw [← card_valid]
  exact Nat.card_congr (Equiv.subtypeEquivRight reachable_iff_valid)

/-- Every reachable state can be solved in at most `@UB@` moves (stabilizer-chain bound). -/
theorem dist_le_of_reachable {s : Cube} (hs : Reachable s) : dist s ≤ @UB@ := by
  classical
  obtain ⟨P, hP, hcard⟩ := exists_reachable_finset
  have hsub : P ⊆ Finset.univ.filter Valid := fun x hx => by
    simpa using (hP x hx).1.valid
  have hV : (Finset.univ.filter Valid).card = 43252003274489856000 := by
    rw [← card_valid, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have := Finset.eq_of_subset_of_card_le hsub (by rw [hV, hcard])
  exact (hP s (this ▸ by simpa using hs.valid)).2

/-- Some reachable state needs at least 18 moves. -/
theorem exists_dist_ge_18 : ∃ s, Reachable s ∧ 18 ≤ dist s := by
  obtain ⟨P, hP, hcard⟩ := exists_reachable_finset
  by_contra hcon
  have hsub : P ⊆ ball 17 := subset_ball P 17 fun s hs => by
    refine ⟨(hP s hs).1, ?_⟩
    by_contra h
    exact hcon ⟨s, (hP s hs).1, by omega⟩
  have := (Finset.card_le_card hsub).trans card_ball_17
  rw [hcard] at this
  omega

/-- **God's number of the 3x3x3 cube in the half-turn metric is at least 18.** -/
theorem eighteen_le_godsNumber : 18 ≤ godsNumber :=
  (le_godsNumber_iff 18).mpr exists_dist_ge_18

/-- God's number is at most `@UB@` (a weak, but fully kernel-checked, upper bound). -/
theorem godsNumber_le : godsNumber ≤ @UB@ :=
  (godsNumber_le_iff _).mpr fun _ hs => dist_le_of_reachable hs

/-- The half-turn-metric God's number lies in `[18, @UB@]`. -/
theorem godsNumber_bounds : 18 ≤ godsNumber ∧ godsNumber ≤ @UB@ :=
  ⟨eighteen_le_godsNumber, godsNumber_le⟩

end Rubik
