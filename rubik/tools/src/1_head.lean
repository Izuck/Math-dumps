import Mathlib

/-!
# The 3x3x3 Rubik's cube in the half-turn metric: model, invariants, and God's number ≥ 18

See `README.md`.  Conventions (Kociemba's cubie level):
corners `URF UFL ULB UBR DFR DLF DBL DRB` (0..7), edges `UR UF UL UB DR DF DL DB FR FL BL BR` (0..11).
A state is (corner permutation, corner twists, edge permutation, edge flips) with the
wreath-product group law.  A move sequence `[m₁, …, mₙ]` evaluates to `m₁ * ⋯ * mₙ`.
-/

namespace Rubik

/-! ## Stage 1: the model -/

/-- A cube state at the cubie level (all `8! * 3^8 * 12! * 2^12` assemblies of the cubies). -/
@[ext] structure Cube where
  cp : Equiv.Perm (Fin 8)
  co : Fin 8 → ZMod 3
  ep : Equiv.Perm (Fin 12)
  eo : Fin 12 → ZMod 2

instance : DecidableEq Cube := fun a b =>
  decidable_of_iff (a.cp = b.cp ∧ a.co = b.co ∧ a.ep = b.ep ∧ a.eo = b.eo) Cube.ext_iff.symm

namespace Cube

instance : Mul Cube :=
  ⟨fun a b => ⟨a.cp * b.cp, fun i => a.co (b.cp i) + b.co i, a.ep * b.ep, fun i => a.eo (b.ep i) + b.eo i⟩⟩
instance : One Cube := ⟨⟨1, 0, 1, 0⟩⟩
instance : Inv Cube :=
  ⟨fun a => ⟨a.cp⁻¹, fun i => -a.co (a.cp⁻¹ i), a.ep⁻¹, fun i => -a.eo (a.ep⁻¹ i)⟩⟩

@[simp] theorem mul_cp (a b : Cube) : (a * b).cp = a.cp * b.cp := rfl
@[simp] theorem mul_co (a b : Cube) (i) : (a * b).co i = a.co (b.cp i) + b.co i := rfl
@[simp] theorem mul_ep (a b : Cube) : (a * b).ep = a.ep * b.ep := rfl
@[simp] theorem mul_eo (a b : Cube) (i) : (a * b).eo i = a.eo (b.ep i) + b.eo i := rfl
@[simp] theorem one_cp : (1 : Cube).cp = 1 := rfl
@[simp] theorem one_co (i) : (1 : Cube).co i = 0 := rfl
@[simp] theorem one_ep : (1 : Cube).ep = 1 := rfl
@[simp] theorem one_eo (i) : (1 : Cube).eo i = 0 := rfl
@[simp] theorem inv_cp (a : Cube) : (a⁻¹).cp = a.cp⁻¹ := rfl
@[simp] theorem inv_co (a : Cube) (i) : (a⁻¹).co i = -a.co (a.cp⁻¹ i) := rfl
@[simp] theorem inv_ep (a : Cube) : (a⁻¹).ep = a.ep⁻¹ := rfl
@[simp] theorem inv_eo (a : Cube) (i) : (a⁻¹).eo i = -a.eo (a.ep⁻¹ i) := rfl

instance : Group Cube where
  mul_assoc a b c := by ext <;> simp [mul_assoc, add_assoc]
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by ext <;> simp [CharTwo.add_self_eq_zero]

/-- `Cube ≃ Perm (Fin 8) × (Fin 8 → ZMod 3) × Perm (Fin 12) × (Fin 12 → ZMod 2)`. -/
def equivProd : Cube ≃ Equiv.Perm (Fin 8) × (Fin 8 → ZMod 3) × Equiv.Perm (Fin 12) × (Fin 12 → ZMod 2) where
  toFun s := (s.cp, s.co, s.ep, s.eo)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Cube := Fintype.ofEquiv _ equivProd.symm

theorem card_cube : Fintype.card Cube = Nat.factorial 8 * 3 ^ 8 * (Nat.factorial 12 * 2 ^ 12) := by
  rw [Fintype.card_congr equivProd]
  simp [Fintype.card_perm, ZMod.card, mul_assoc]

end Cube

/-- A permutation of `Fin n` from explicit forward and backward tables. -/
def mkPerm {n : ℕ} (f g : Fin n → Fin n) (h : ∀ i, g (f i) = i) (h' : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin n) := ⟨f, g, h, h'⟩

def turnU : Cube := ⟨mkPerm ![3,0,1,2,4,5,6,7] ![1,2,3,0,4,5,6,7] (by decide) (by decide), ![0,0,0,0,0,0,0,0],
  mkPerm ![3,0,1,2,4,5,6,7,8,9,10,11] ![1,2,3,0,4,5,6,7,8,9,10,11] (by decide) (by decide), ![0,0,0,0,0,0,0,0,0,0,0,0]⟩
def turnD : Cube := ⟨mkPerm ![0,1,2,3,5,6,7,4] ![0,1,2,3,7,4,5,6] (by decide) (by decide), ![0,0,0,0,0,0,0,0],
  mkPerm ![0,1,2,3,5,6,7,4,8,9,10,11] ![0,1,2,3,7,4,5,6,8,9,10,11] (by decide) (by decide), ![0,0,0,0,0,0,0,0,0,0,0,0]⟩
def turnR : Cube := ⟨mkPerm ![4,1,2,0,7,5,6,3] ![3,1,2,7,0,5,6,4] (by decide) (by decide), ![2,0,0,1,1,0,0,2],
  mkPerm ![8,1,2,3,11,5,6,7,4,9,10,0] ![11,1,2,3,8,5,6,7,0,9,10,4] (by decide) (by decide), ![0,0,0,0,0,0,0,0,0,0,0,0]⟩
def turnL : Cube := ⟨mkPerm ![0,2,6,3,4,1,5,7] ![0,5,1,3,4,6,2,7] (by decide) (by decide), ![0,1,2,0,0,2,1,0],
  mkPerm ![0,1,10,3,4,5,9,7,8,2,6,11] ![0,1,9,3,4,5,10,7,8,6,2,11] (by decide) (by decide), ![0,0,0,0,0,0,0,0,0,0,0,0]⟩
def turnF : Cube := ⟨mkPerm ![1,5,2,3,0,4,6,7] ![4,0,2,3,5,1,6,7] (by decide) (by decide), ![1,2,0,0,2,1,0,0],
  mkPerm ![0,9,2,3,4,8,6,7,1,5,10,11] ![0,8,2,3,4,9,6,7,5,1,10,11] (by decide) (by decide), ![0,1,0,0,0,1,0,0,1,1,0,0]⟩
def turnB : Cube := ⟨mkPerm ![0,1,3,7,4,5,2,6] ![0,1,6,2,4,5,7,3] (by decide) (by decide), ![0,0,1,2,0,0,2,1],
  mkPerm ![0,1,2,11,4,5,6,10,8,9,3,7] ![0,1,2,10,4,5,6,11,8,9,7,3] (by decide) (by decide), ![0,0,0,1,0,0,0,1,0,0,1,1]⟩

/-- The six faces.  `U/D`, `R/L`, `F/B` are the three axes. -/
inductive Face | U | D | R | L | F | B
deriving DecidableEq, Repr

instance : Fintype Face := ⟨{.U, .D, .R, .L, .F, .B}, fun x => by cases x <;> decide⟩

/-- The clockwise quarter turn of a face. -/
def q : Face → Cube
  | .U => turnU | .D => turnD | .R => turnR | .L => turnL | .F => turnF | .B => turnB

/-- A move of the half-turn metric: a face and `k = 0, 1, 2` meaning a turn by `k + 1` quarters. -/
structure Move where
  face : Face
  k : Fin 3
deriving DecidableEq, Fintype, Repr

/-- The state produced by a single move. -/
def Move.toCube (m : Move) : Cube := q m.face ^ (m.k.val + 1)

/-- The state produced by a move sequence. -/
def evalSeq (l : List Move) : Cube := (l.map Move.toCube).prod

/-- States that can be produced from the solved cube by face turns. -/
def Reachable (s : Cube) : Prop := ∃ l : List Move, evalSeq l = s

/-- Half-turn-metric distance from the solved state (junk value `0` on unreachable states). -/
noncomputable def dist (s : Cube) : ℕ := sInf {n | ∃ l : List Move, l.length = n ∧ evalSeq l = s}

/-- God's number: the largest distance of a reachable state. -/
noncomputable def godsNumber : ℕ := sSup (dist '' {s | Reachable s})

/-- The superflip: all cubies in place, all twelve edges flipped. -/
def superflip : Cube := ⟨1, 0, 1, fun _ => 1⟩

/-! ### Sanity checks -/

theorem card_move : Fintype.card Move = 18 := by decide

theorem q_pow_four : ∀ f, q f ^ 4 = 1 := by decide +kernel
theorem q_pow_two_ne : ∀ f, q f ^ 2 ≠ 1 := by decide +kernel
theorem q_ne_one : ∀ f, q f ≠ 1 := by decide +kernel

/-- `(R U R' U')^6 = 1`. -/
theorem sexy_six : (q .R * q .U * (q .R)⁻¹ * (q .U)⁻¹) ^ 6 = 1 := by decide +kernel
theorem sexy_three_ne : (q .R * q .U * (q .R)⁻¹ * (q .U)⁻¹) ^ 3 ≠ 1 := by decide +kernel

abbrev mv (f : Face) (k : Fin 3) : Move := ⟨f, k⟩

/-- `U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2` produces the superflip. -/
theorem superflip_eq : evalSeq [mv .U 0, mv .R 1, mv .F 0, mv .B 0, mv .R 0, mv .B 1, mv .R 0, mv .U 1,
    mv .L 0, mv .B 1, mv .R 0, mv .U 2, mv .D 2, mv .R 1, mv .F 0, mv .R 2, mv .L 0, mv .B 1,
    mv .U 1, mv .F 1] = superflip := by decide +kernel

theorem superflip_reachable : Reachable superflip := ⟨_, superflip_eq⟩

theorem superflip_central : ∀ f, superflip * q f = q f * superflip := by decide +kernel

/-! ### Basic facts about sequences, reachability and distance -/

theorem evalSeq_nil : evalSeq [] = 1 := rfl
theorem evalSeq_append (l l' : List Move) : evalSeq (l ++ l') = evalSeq l * evalSeq l' := by
  simp [evalSeq]
theorem evalSeq_singleton (m : Move) : evalSeq [m] = q m.face ^ (m.k.val + 1) := by
  simp [evalSeq, Move.toCube]

theorem reachable_one : Reachable 1 := ⟨[], rfl⟩
theorem Reachable.mul {a b : Cube} (ha : Reachable a) (hb : Reachable b) : Reachable (a * b) := by
  obtain ⟨l, rfl⟩ := ha; obtain ⟨l', rfl⟩ := hb; exact ⟨l ++ l', evalSeq_append l l'⟩
theorem reachable_q (f : Face) : Reachable (q f) := ⟨[mv f 0], by simp [evalSeq_singleton]⟩

/-- The value of a word of quarter turns. -/
def evalQ (w : List Face) : Cube := (w.map q).prod

theorem reachable_evalQ (w : List Face) : Reachable (evalQ w) := by
  induction w with
  | nil => exact reachable_one
  | cons f w ih => simpa [evalQ] using (reachable_q f).mul ih

theorem dist_spec {s : Cube} (h : Reachable s) : ∃ l : List Move, l.length = dist s ∧ evalSeq l = s := by
  have hne : {n | ∃ l : List Move, l.length = n ∧ evalSeq l = s}.Nonempty := by
    obtain ⟨l, hl⟩ := h; exact ⟨l.length, l, rfl, hl⟩
  exact Nat.sInf_mem hne

theorem dist_le (l : List Move) : dist (evalSeq l) ≤ l.length := Nat.sInf_le ⟨l, rfl, rfl⟩

/-- `godsNumber` is attained and bounds every reachable distance, i.e. it really is the maximum. -/
theorem godsNumber_spec :
    (∀ s, Reachable s → dist s ≤ godsNumber) ∧ ∃ s, Reachable s ∧ dist s = godsNumber := by
  have hfin : (dist '' {s | Reachable s}).Finite := (Set.toFinite _).image _
  have hne : (dist '' {s | Reachable s}).Nonempty := ⟨dist 1, 1, reachable_one, rfl⟩
  refine ⟨fun s hs => le_csSup hfin.bddAbove ⟨s, hs, rfl⟩, ?_⟩
  obtain ⟨s, hs, h⟩ := Nat.sSup_mem hne hfin.bddAbove
  exact ⟨s, hs, h⟩

theorem le_godsNumber_iff (n : ℕ) : n ≤ godsNumber ↔ ∃ s, Reachable s ∧ n ≤ dist s := by
  constructor
  · intro h
    obtain ⟨s, hs, e⟩ := godsNumber_spec.2
    exact ⟨s, hs, e ▸ h⟩
  · rintro ⟨s, hs, h⟩
    exact h.trans (godsNumber_spec.1 s hs)

theorem godsNumber_le_iff (n : ℕ) : godsNumber ≤ n ↔ ∀ s, Reachable s → dist s ≤ n := by
  constructor
  · intro h s hs
    exact (godsNumber_spec.1 s hs).trans h
  · intro h
    obtain ⟨s, hs, e⟩ := godsNumber_spec.2
    exact e ▸ h s hs

theorem dist_superflip_le : dist superflip ≤ 20 := by
  have := dist_le [mv .U 0, mv .R 1, mv .F 0, mv .B 0, mv .R 0, mv .B 1, mv .R 0, mv .U 1,
    mv .L 0, mv .B 1, mv .R 0, mv .U 2, mv .D 2, mv .R 1, mv .F 0, mv .R 2, mv .L 0, mv .B 1,
    mv .U 1, mv .F 1]
  rwa [superflip_eq] at this

/-! ## Stage 2: the three classical invariants -/

/-- Total corner twist is `0 mod 3`, total edge flip is `0 mod 2`, and the corner and edge
permutations have the same sign. -/
def Valid (s : Cube) : Prop :=
  ∑ i, s.co i = 0 ∧ ∑ i, s.eo i = 0 ∧ Equiv.Perm.sign s.cp = Equiv.Perm.sign s.ep

theorem valid_one : Valid 1 := by simp [Valid]

theorem Valid.mul {a b : Cube} (ha : Valid a) (hb : Valid b) : Valid (a * b) := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cube.mul_co, Finset.sum_add_distrib]
    rw [Equiv.sum_comp b.cp a.co, a1, b1, add_zero]
  · simp only [Cube.mul_eo, Finset.sum_add_distrib]
    rw [Equiv.sum_comp b.ep a.eo, a2, b2, add_zero]
  · simp [a3, b3]

theorem valid_q : ∀ f, Valid (q f) := by
  intro f
  cases f <;> refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Every face turn (hence every move) preserves the invariants. -/
theorem Valid.mul_q {s : Cube} (h : Valid s) (f : Face) : Valid (s * q f) := h.mul (valid_q f)

theorem valid_pow {s : Cube} (h : Valid s) (n : ℕ) : Valid (s ^ n) := by
  induction n with
  | zero => simpa using valid_one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem valid_move (m : Move) : Valid m.toCube := valid_pow (valid_q _) _

/-- Every reachable state satisfies the three invariants. -/
theorem Reachable.valid {s : Cube} (h : Reachable s) : Valid s := by
  obtain ⟨l, rfl⟩ := h
  induction l with
  | nil => exact valid_one
  | cons m l ih => simpa [evalSeq] using (valid_move m).mul ih

/-- Examples of unreachable states: a single twisted corner, a single flipped edge, a single
swap of two edges. -/
theorem not_reachable_twist : ¬ Reachable ⟨1, ![1,0,0,0,0,0,0,0], 1, 0⟩ := fun h =>
  absurd h.valid.1 (by decide +kernel)
theorem not_reachable_flip : ¬ Reachable ⟨1, 0, 1, ![1,0,0,0,0,0,0,0,0,0,0,0]⟩ := fun h =>
  absurd h.valid.2.1 (by decide +kernel)
theorem not_reachable_swap : ¬ Reachable ⟨1, 0, Equiv.swap 0 1, 0⟩ := fun h =>
  absurd h.valid.2.2 (by simp)

