/-- The invariants as a group homomorphism. -/
def chi : Cube →* (Multiplicative (ZMod 3) × Multiplicative (ZMod 2)) × ℤˣ where
  toFun s := ((Multiplicative.ofAdd (∑ i, s.co i), Multiplicative.ofAdd (∑ i, s.eo i)),
    Equiv.Perm.sign s.cp * Equiv.Perm.sign s.ep)
  map_one' := by simp
  map_mul' a b := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp only [Cube.mul_co, Finset.sum_add_distrib, Prod.mk_mul_mk, ← ofAdd_add]
      rw [Equiv.sum_comp b.cp a.co]
    · simp only [Cube.mul_eo, Finset.sum_add_distrib, Prod.mk_mul_mk, ← ofAdd_add]
      rw [Equiv.sum_comp b.ep a.eo]
    · simp [mul_mul_mul_comm]

theorem chi_eq_one_iff (s : Cube) : chi s = 1 ↔ Valid s := by
  have h : ∀ u v : ℤˣ, u * v = 1 ↔ u = v := by decide
  simp only [chi, MonoidHom.coe_mk, OneHom.coe_mk, Prod.mk_eq_one, ofAdd_eq_one, h, Valid, and_assoc]

theorem chi_surjective : Function.Surjective chi := by
  rintro ⟨⟨a, b⟩, u⟩
  refine ⟨⟨if u = 1 then 1 else Equiv.swap 0 1, Pi.single 0 a.toAdd, 1, Pi.single 0 b.toAdd⟩, ?_⟩
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · show Multiplicative.ofAdd (∑ i, (Pi.single 0 a.toAdd : Fin 8 → ZMod 3) i) = a
    rw [Finset.sum_pi_single']; simp
  · show Multiplicative.ofAdd (∑ i, (Pi.single 0 b.toAdd : Fin 12 → ZMod 2) i) = b
    rw [Finset.sum_pi_single']; simp
  · show Equiv.Perm.sign (if u = 1 then 1 else Equiv.swap (0 : Fin 8) 1) * Equiv.Perm.sign (1 : Equiv.Perm (Fin 12)) = u
    rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem card_valid : Nat.card {s // Valid s} = 43252003274489856000 := by
  have h1 : Nat.card chi.ker * chi.ker.index = Nat.card Cube := Subgroup.card_mul_index _
  have h2 : chi.ker.index = 12 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr chi_surjective]
    simp [Nat.card_eq_fintype_card]
  have h3 : Nat.card chi.ker = Nat.card {s // Valid s} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by rw [MonoidHom.mem_ker, chi_eq_one_iff])
  rw [h2, h3, Nat.card_eq_fintype_card (α := Cube), Cube.card_cube] at h1
  have : Nat.factorial 8 * 3 ^ 8 * (Nat.factorial 12 * 2 ^ 12) = 43252003274489856000 * 12 := by
    norm_num [Nat.factorial]
  rw [this] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

