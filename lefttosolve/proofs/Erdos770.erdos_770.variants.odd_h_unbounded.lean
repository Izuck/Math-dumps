import FormalConjectures.ErdosProblems.«770»

-- Problem: Erdős Problem 770 — odd h unbounded
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/770.lean:51 (declaration Erdos770.erdos_770.variants.odd_h_unbounded)
-- Credit: @<your GitHub handle> (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMAProof

open Erdos770

lemma prime_sq (M p q : ℕ) (hp : p.Prime) (hpM : M < p) (hdvd : 8 * M.factorial ∣ p + 1)
    (hq : q.Prime) (hqM : q ≤ M) : IsSquare (q : ZMod p) := by
  have := Fact.mk hp
  have := Fact.mk hq
  have hqdvd : q ∣ p + 1 :=
    (dvd_mul_of_dvd_right (Nat.dvd_factorial hq.pos hqM) 8).trans hdvd
  have h8dvd : 8 ∣ p + 1 := (dvd_mul_right 8 _).trans hdvd
  have hp8 : p % 8 = 7 := by omega
  have hp4 : p % 4 = 3 := by omega
  have hp2 : p ≠ 2 := by omega
  have hpq : (p : ZMod q) = -1 := by
    have : ((p + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hqdvd
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  rcases hq.eq_two_or_odd' with rfl | hqodd
  · exact_mod_cast (ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inr hp8)
  · have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
      rcases hqodd with ⟨k, hk⟩
      omega
    rcases hq4 with h1 | h3
    · refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one h1 hp2).mp ?_
      rw [hpq]
      exact ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    · have hne : p ≠ q := by omega
      rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp4 h3 hne, hpq]
      intro h
      exact ZMod.exists_sq_eq_neg_one_iff.mp h h3

lemma all_sq (M p : ℕ) (H : ∀ q, q.Prime → q ≤ M → IsSquare (q : ZMod p)) :
    ∀ i, 0 < i → i ≤ M → IsSquare (i : ZMod p) := by
  intro i
  induction i using induction_on_primes with
  | zero => intro h; omega
  | one => intro _ _; exact ⟨1, by simp⟩
  | prime_mul q a hq ih =>
    intro hpos hle
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpos
    have hqa : q ≤ q * a := Nat.le_mul_of_pos_right q ha
    have haq : a ≤ q * a := Nat.le_mul_of_pos_left a hq.pos
    push_cast
    exact (H q hq (hqa.trans hle)).mul (ih ha (haq.trans hle))

lemma p_dvd (p i : ℕ) (hp : p.Prime) (hi0 : 0 < i) (hip : i < p) (hsq : IsSquare (i : ZMod p)) :
    p ∣ i ^ (p / 2) - 1 := by
  have := Fact.mk hp
  have hne : (i : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact absurd (Nat.le_of_dvd hi0 h) (by omega)
  have he := (ZMod.euler_criterion p hne).mp hsq
  have h1 : 1 ≤ i ^ (p / 2) := Nat.one_le_pow _ _ hi0
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1]
  push_cast
  rw [he]
  simp

lemma h_ge (n M p : ℕ) (hp : p.Prime) (hdiv : ∀ i, 2 ≤ i → i ≤ M → p ∣ i ^ n - 1) :
    ((M + 1 : ℕ) : ℕ∞) ≤ h n := by
  unfold h
  refine le_sInf ?_
  rintro m ⟨hm2, hgcd⟩
  by_contra hlt
  rw [not_le] at hlt
  have hmtop : m ≠ ⊤ := ne_top_of_lt hlt
  lift m to ℕ using hmtop
  have hmM : m ≤ M := by
    have : m < M + 1 := by exact_mod_cast hlt
    omega
  simp only [ENat.toNat_natCast] at hgcd
  have hpd : p ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id := by
    rw [Finset.dvd_gcd_iff]
    intro b hb
    simp only [Finset.mem_image, Finset.mem_Icc] at hb
    obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hb
    exact hdiv i h1 (h2.trans hmM)
  rw [hgcd] at hpd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)

lemma h_ne_top (n : ℕ) (hn : 2 ≤ n) : h n ≠ ⊤ := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmem : ((2 ^ n : ℕ) : ℕ∞) ∈ {m : ℕ∞ | 2 < m ∧
      ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1} := by
    refine ⟨?_, ?_⟩
    · have : 2 < 2 ^ n := by omega
      exact_mod_cast this
    · simp only [ENat.toNat_natCast]
      set g := ((Finset.Icc 2 (2 ^ n)).image fun i => (i ^ n - 1)).gcd id with hg
      have hg1 : g ∣ 2 ^ n - 1 := by
        have := Finset.gcd_dvd (f := id) (Finset.mem_image_of_mem (fun i => (i ^ n - 1))
          (show 2 ∈ Finset.Icc 2 (2 ^ n) by simp; omega))
        simpa using this
      have hg2 : g ∣ (2 ^ n - 1) ^ n - 1 := by
        have := Finset.gcd_dvd (f := id) (Finset.mem_image_of_mem (fun i => (i ^ n - 1))
          (show 2 ^ n - 1 ∈ Finset.Icc 2 (2 ^ n) by simp; omega))
        simpa using this
      have hg3 : g ∣ (2 ^ n - 1) ^ n := dvd_pow hg1 (by omega)
      have h1 : 1 ≤ (2 ^ n - 1) ^ n := Nat.one_le_pow _ _ (by omega)
      have := Nat.dvd_sub hg3 hg2
      rw [Nat.sub_sub_self h1] at this
      exact Nat.dvd_one.mp this
  intro htop
  have hle := sInf_le hmem
  unfold h at htop
  rw [htop] at hle
  exact absurd hle (by simp)

end OMAProof

theorem OMA.solution : type_of% @Erdos770.erdos_770.variants.odd_h_unbounded := by
  intro a
  have hNZ : 8 * (a + 2).factorial ≠ 0 := by positivity
  have : NeZero (8 * (a + 2).factorial) := ⟨hNZ⟩
  obtain ⟨p, hpgt, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    (q := 8 * (a + 2).factorial) (a := -1) isUnit_one.neg (a + 2)
  have hdvd : 8 * (a + 2).factorial ∣ p + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hpmod]
    ring
  have h8dvd : 8 ∣ p + 1 := (dvd_mul_right 8 _).trans hdvd
  have hp8 : p % 8 = 7 := by omega
  have hnodd : Odd (p / 2) := ⟨p / 4, by omega⟩
  have hn2 : 2 ≤ p / 2 := by omega
  have hge := OMAProof.h_ge (p / 2) (a + 2) p hp (fun i hi2 hiM =>
    OMAProof.p_dvd p i hp (by omega) (by omega)
      (OMAProof.all_sq (a + 2) p
        (fun q hq hqM => OMAProof.prime_sq (a + 2) p q hp hpgt hdvd hq hqM) i (by omega) hiM))
  have hne := OMAProof.h_ne_top (p / 2) hn2
  refine ⟨(Erdos770.h (p / 2)).toNat, ⟨Erdos770.h (p / 2), ⟨p / 2, hnodd, rfl⟩, rfl⟩, ?_⟩
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hk] at hge ⊢
  simp only [ENat.toNat_natCast]
  have : a + 2 + 1 ≤ k := by exact_mod_cast hge
  omega
