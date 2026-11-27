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

/-! ## Stage 3a: a stabilizer chain

A kernel-checked stabilizer chain (one cubie per level) exhibits `43252003274489856000`
distinct reachable states, each with an explicit bound on its distance. -/

theorem dist_mul_le {a b : Cube} (ha : Reachable a) (hb : Reachable b) :
    dist (a * b) ≤ dist a + dist b := by
  obtain ⟨l, hl, rfl⟩ := dist_spec ha
  obtain ⟨l', hl', rfl⟩ := dist_spec hb
  rw [← evalSeq_append, ← hl, ← hl', ← List.length_append]
  exact dist_le _

/-- Prepend a quarter turn to a move sequence, merging it with a leading move of the same face. -/
def pushQ (f : Face) : List Move → List Move
  | [] => [⟨f, 0⟩]
  | m :: l => if m.face = f then (if h : m.k.val < 2 then ⟨f, ⟨m.k.val + 1, by omega⟩⟩ :: l else l)
      else ⟨f, 0⟩ :: m :: l

/-- Turn a word of quarter turns into a sequence of half-turn-metric moves. -/
def compress (w : List Face) : List Move := w.foldr pushQ []

theorem pushQ_cons (f : Face) (m : Move) (l : List Move) : pushQ f (m :: l) =
    if m.face = f then (if h : m.k.val < 2 then ⟨f, ⟨m.k.val + 1, by omega⟩⟩ :: l else l)
      else ⟨f, 0⟩ :: m :: l := rfl

theorem evalSeq_cons (m : Move) (l : List Move) :
    evalSeq (m :: l) = q m.face ^ (m.k.val + 1) * evalSeq l := by
  simp [evalSeq, Move.toCube]

theorem evalSeq_pushQ (f : Face) (l : List Move) : evalSeq (pushQ f l) = q f * evalSeq l := by
  rcases l with _ | ⟨⟨g, k⟩, l⟩
  · simp [pushQ, evalSeq_cons]
  · rw [pushQ_cons]
    dsimp only
    by_cases hgf : g = f
    · subst hgf
      by_cases hk : k.val < 2
      · rw [if_pos rfl, dif_pos hk, evalSeq_cons, evalSeq_cons]
        show q g ^ (k.val + 1 + 1) * evalSeq l = q g * (q g ^ (k.val + 1) * evalSeq l)
        rw [← mul_assoc, ← pow_succ']
      · have hk2 : k.val = 2 := by omega
        rw [if_pos rfl, dif_neg hk, evalSeq_cons]
        show evalSeq l = q g * (q g ^ (k.val + 1) * evalSeq l)
        rw [← mul_assoc, ← pow_succ', hk2, q_pow_four, one_mul]
    · simp only [if_neg hgf, evalSeq_cons]
      simp

theorem evalSeq_compress (w : List Face) : evalSeq (compress w) = evalQ w := by
  induction w with
  | nil => rfl
  | cons f w ih =>
    have : evalQ (f :: w) = q f * evalQ w := by simp [evalQ]
    rw [this, ← ih]; exact evalSeq_pushQ f _

theorem dist_evalQ_le (w : List Face) : dist (evalQ w) ≤ (compress w).length := by
  rw [← evalSeq_compress]; exact dist_le _


/-- A cubie: one of the 8 corners or one of the 12 edges. -/
abbrev Pt := Fin 8 ⊕ Fin 12
/-- A cubie position together with an orientation. -/
abbrev PtImg := (Fin 8 × ZMod 3) ⊕ (Fin 12 × ZMod 2)

/-- The action of a state on oriented cubie positions. -/
def act (s : Cube) : PtImg → PtImg
  | .inl x => .inl (s.cp x.1, s.co x.1 + x.2)
  | .inr x => .inr (s.ep x.1, s.eo x.1 + x.2)

theorem act_mul (a b : Cube) (x : PtImg) : act (a * b) x = act a (act b x) := by
  rcases x with ⟨p, o⟩ | ⟨p, o⟩ <;> simp [act, add_assoc]

def base : Pt → PtImg
  | .inl i => .inl (i, 0)
  | .inr j => .inr (j, 0)

/-- Where (and in which orientation) the state `s` puts cubie `p`. -/
def img (s : Cube) (p : Pt) : PtImg := act s (base p)

/-- `s` leaves cubie `p` in place and untwisted. -/
def Fix (s : Cube) (p : Pt) : Prop := img s p = base p

theorem img_mul_of_fix {x y : Cube} {p : Pt} (h : Fix y p) : img (x * y) p = img x p := by
  unfold Fix img at *; rw [act_mul, h]

theorem Fix.mul {x y : Cube} {p : Pt} (hx : Fix x p) (hy : Fix y p) : Fix (x * y) p := by
  unfold Fix; rw [img_mul_of_fix hy]; exact hx

theorem fix_one (p : Pt) : Fix 1 p := by
  rcases p with i | j <;> simp [Fix, img, act, base]

/-- Track an oriented cubie position through a word of quarter turns (linear time). -/
def actW (w : List Face) (x : PtImg) : PtImg := w.foldr (fun f x => act (q f) x) x

theorem actW_eq (w : List Face) (x : PtImg) : actW w x = act (evalQ w) x := by
  induction w with
  | nil => rcases x with ⟨p, o⟩ | ⟨p, o⟩ <;> simp [actW, evalQ, act]
  | cons f w ih =>
    have : evalQ (f :: w) = q f * evalQ w := by simp [evalQ]
    rw [this, act_mul, ← ih]; rfl

/-- Kernel-checkable certificate for one level of the stabilizer chain: every word fixes the
cubies in `fixed`, uses at most `d` half-turn-metric moves, and the words send cubie `b` to
pairwise distinct oriented positions. -/
def checkLevel (fixed : List Pt) (b : Pt) (d : ℕ) (ws : List (List Face)) : Bool :=
  ws.all (fun w => fixed.all (fun p => decide (actW w (base p) = base p))) &&
    (ws.all (fun w => decide ((compress w).length ≤ d)) &&
    decide ((ws.map (fun w => actW w (base b))).Nodup))

theorem chain_step (fixed : List Pt) (b : Pt) (d : ℕ) (ws : List (List Face))
    (h : checkLevel fixed b d ws = true) (D : ℕ) (P : Finset Cube)
    (hP : ∀ s ∈ P, (Reachable s ∧ dist s ≤ D) ∧ ∀ p ∈ b :: fixed, Fix s p) :
    ∃ P' : Finset Cube, (∀ s ∈ P', (Reachable s ∧ dist s ≤ d + D) ∧ ∀ p ∈ fixed, Fix s p) ∧
      P'.card = ws.length * P.card := by
  classical
  simp only [checkLevel, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hfix, hlen, hnd⟩ := h
  set L : List Cube := ws.map evalQ with hL
  have hnd' : (L.map (fun x => img x b)).Nodup := by
    rw [hL, List.map_map]
    have : ((fun x => img x b) ∘ evalQ) = fun w => actW w (base b) := by
      funext w; simp [img, actW_eq]
    rw [this]; exact hnd
  have hLnd : L.Nodup := List.Nodup.of_map _ hnd'
  have hLfix : ∀ x ∈ L, ∀ p ∈ fixed, Fix x p := by
    intro x hx p hp
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have := hfix w hw p hp
    rwa [actW_eq] at this
  refine ⟨Finset.image₂ (· * ·) L.toFinset P, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hs
    rw [List.mem_toFinset] at hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have hd : dist (evalQ w * y) ≤ d + D :=
      (dist_mul_le (reachable_evalQ w) (hP y hy).1.1).trans
        (Nat.add_le_add ((dist_evalQ_le w).trans (hlen w hw)) (hP y hy).1.2)
    refine ⟨⟨(reachable_evalQ w).mul (hP y hy).1.1, hd⟩, fun p hp => ?_⟩
    exact (hLfix _ hx p hp).mul ((hP y hy).2 p (List.mem_cons_of_mem _ hp))
  · rw [← List.length_map (as := ws) evalQ, ← hL, ← List.toFinset_card_of_nodup hLnd]
    refine Finset.card_image₂_iff.mpr ?_
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' e
    change x * y = x' * y' at e
    simp only [Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hxy hxy'
    have hyb : Fix y b := (hP y hxy.2).2 b (List.mem_cons_self ..)
    have hyb' : Fix y' b := (hP y' hxy'.2).2 b (List.mem_cons_self ..)
    have e1 : img x b = img x' b := by
      rw [← img_mul_of_fix hyb, e, img_mul_of_fix hyb']
    have e2 : x = x' := List.inj_on_of_nodup_map hnd' hxy.1 hxy'.1 e1
    subst e2
    rw [mul_left_cancel e]

def fixedL (bs : List Pt) : ℕ → List Pt
  | 0 => []
  | n + 1 => bs.getD n (.inl 0) :: fixedL bs n

/-- Base of the stabilizer chain. -/
def basePts : List Pt := [.inr 0, .inr 1, .inr 2, .inr 3, .inr 4, .inr 5, .inr 6, .inr 7, .inr 8, .inr 9, .inr 10, .inr 11, .inl 0, .inl 1, .inl 2, .inl 3, .inl 4, .inl 5, .inl 6, .inl 7]

def T0 : List (List Face) := [[], [.U,.F,.R], [.U,.U,.U], [.F,.R], [.U,.U], [.U,.B,.B,.B,.R,.R,.R], [.U], [.B,.B,.B,.R,.R,.R], [.R,.R], [.D,.B,.R,.R,.R], [.D,.R,.R], [.F,.F,.F,.R], [.D,.D,.R,.R], [.D,.F,.F,.F,.R], [.D,.D,.D,.R,.R], [.B,.R,.R,.R], [.R], [.F,.F,.F,.U,.U,.U], [.L,.L,.L,.U,.U], [.F,.U,.U,.U], [.L,.U,.U], [.B,.B,.B,.U], [.R,.R,.R], [.B,.U]]
def T1 : List (List Face) := [[], [.R,.U,.U,.U,.R,.R,.R,.F,.F,.F], [.R,.R,.R,.U,.U,.U,.R], [.L,.F], [.R,.R,.R,.U,.U,.R], [.R,.U,.R,.R,.R,.F,.F,.F], [.D,.D,.D,.F,.F], [.R,.F,.F,.F,.R,.R,.R], [.F,.F], [.D,.D,.D,.L,.L,.L,.F], [.D,.F,.F], [.L,.L,.L,.F], [.D,.D,.F,.F], [.D,.L,.L,.L,.F], [.R,.U,.R,.R,.R], [.F,.F,.F], [.U,.L,.L,.L,.U,.U,.U], [.F], [.U,.L,.U,.U,.U], [.L,.L,.F], [.R,.R,.R,.U,.R], [.R,.R,.F,.F,.F,.R,.R]]
def T2 : List (List Face) := [[], [.U,.U,.U,.F,.F,.F,.U,.L,.L,.L], [.B,.B,.D,.L,.L], [.B,.L], [.D,.D,.L,.L], [.D,.B,.B,.B,.L], [.D,.D,.D,.L,.L], [.F,.L,.L,.L,.F,.F,.F], [.L,.L], [.D,.D,.D,.B,.B,.B,.L], [.D,.L,.L], [.B,.B,.B,.L], [.U,.U,.R,.U,.U], [.U,.U,.U,.F,.F,.F,.U], [.L,.L,.L], [.U,.U,.U,.F,.U], [.L], [.U,.B,.B,.B,.U,.U,.U], [.B,.B,.L], [.U,.B,.U,.U,.U]]
def T3 : List (List Face) := [[], [.U,.R,.U,.U,.U,.B], [.D,.B,.B], [.R,.R,.R,.B,.R], [.D,.D,.B,.B], [.R,.D,.R,.R,.R,.B], [.D,.D,.D,.B,.B], [.L,.B,.B,.B,.L,.L,.L], [.B,.B], [.L,.L,.L,.D,.L,.B,.B,.B], [.U,.R,.U,.U,.U], [.U,.U,.F,.F,.F,.U,.U], [.U,.U,.U,.L,.L,.L,.U], [.U,.U,.F,.U,.U], [.U,.U,.U,.L,.U], [.B,.B,.B], [.U,.R,.R,.R,.U,.U,.U], [.B]]
def T4 : List (List Face) := [[], [.F,.F,.F,.R,.F,.R,.R,.R,.D], [.D], [.R,.F,.F,.F,.R,.R,.R,.F], [.D,.D], [.L,.L,.L,.F,.F,.F,.D,.F,.L], [.D,.D,.D], [.R,.R,.R,.B,.R,.B,.B,.B], [.F,.F,.F,.R,.F,.R,.R,.R], [.F,.D,.F,.F,.F], [.L,.D,.D,.L,.L,.L], [.F,.F,.F,.D,.F], [.L,.L,.L,.D,.D,.L], [.B,.D,.D,.D,.B,.B,.B], [.B,.B,.R,.R,.R,.B,.B,.R], [.B,.B,.B,.D,.D,.D,.B]]
def T5 : List (List Face) := [[], [.F,.F,.F,.R,.R,.F,.R,.D,.D,.D,.R], [.R,.R,.R,.D,.R], [.F,.L,.L,.L,.F,.F,.F,.L], [.R,.R,.R,.D,.D,.R], [.F,.F,.F,.R,.R,.R,.D,.D,.D,.R,.F], [.R,.R,.R,.D,.D,.D,.R], [.F,.D,.F,.F,.F,.D,.D,.D], [.D,.D,.D,.L,.D,.L,.L,.L], [.L,.L,.L,.F,.L,.F,.F,.F], [.D,.D,.D,.L,.L,.L,.D,.L], [.D,.D,.B,.D,.D,.B,.B,.B], [.R,.D,.D,.D,.R,.R,.R], [.D,.D,.B,.B,.B,.D,.D,.B]]
def T6 : List (List Face) := [[], [.D,.D,.D,.B,.B,.B,.U,.U,.U,.D,.L,.L,.L,.U,.B], [.D,.L,.L,.L,.D,.D,.D,.L], [.L,.B,.B,.B,.L,.L,.L,.B], [.L,.L,.L,.F,.F,.L,.F,.F], [.D,.F,.D,.F,.F,.F,.D,.D], [.L,.D,.L,.L,.L,.D,.D,.D], [.D,.F,.F,.F,.D,.F,.D,.D], [.B,.B,.B,.L,.B,.L,.L,.L], [.D,.D,.D,.B,.D,.B,.B,.B], [.L,.B,.B,.L,.L,.L,.B,.B], [.D,.D,.D,.B,.B,.B,.D,.B]]
def T7 : List (List Face) := [[], [.L,.B,.B,.B,.L,.L,.L,.B,.L,.L,.L,.D,.L,.D,.D,.D], [.R,.D,.D,.D,.R,.R,.D,.R], [.B,.R,.R,.B,.B,.B,.R,.R], [.L,.L,.L,.D,.L,.L,.D,.D,.D,.L,.L,.L], [.B,.B,.B,.L,.L,.B,.L,.L], [.L,.D,.L,.L,.D,.D,.D,.L], [.L,.L,.B,.B,.B,.L,.L,.B], [.R,.R,.R,.D,.D,.D,.R,.R,.D,.R,.R,.R], [.R,.R,.B,.R,.R,.B,.B,.B]]
def T8 : List (List Face) := [[], [.B,.R,.R,.R,.U,.R,.R,.U,.U,.U,.R,.B,.B,.B,.R,.R], [.L,.L,.F,.F,.L,.L,.F,.F], [.F,.R,.U,.U,.U,.R,.R,.U,.R,.R,.R,.F,.F,.F,.R,.R], [.F,.F,.L,.L,.F,.F,.L,.L], [.L,.F,.F,.F,.L,.L,.U,.L,.L,.U,.U,.U,.F,.L,.L,.L], [.B,.B,.R,.R,.B,.B,.R,.R], [.B,.B,.R,.B,.U,.U,.U,.B,.B,.U,.B,.B,.B,.R,.R,.R]]
def T9 : List (List Face) := [[], [.L,.L,.B,.B,.B,.L,.U,.U,.U,.L,.L,.U,.L,.L,.L,.B], [.B,.B,.L,.L,.B,.B,.L,.L], [.B,.B,.B,.L,.L,.L,.B,.B,.U,.B,.B,.U,.U,.U,.L,.B], [.L,.L,.B,.B,.L,.L,.B,.B], [.L,.B,.L,.L,.U,.U,.U,.L,.L,.U,.B,.B,.B,.L,.L,.L]]
def T10 : List (List Face) := [[], [.B,.B,.L,.B,.B,.B,.U,.B,.B,.U,.U,.U,.B,.L,.L,.L], [.D,.L,.L,.L,.D,.D,.D,.B,.B,.U,.U,.U,.L,.L,.L,.U,.B,.B,.L], [.L,.L,.L,.B,.B,.B,.D,.D,.D,.B,.L,.D,.D,.D,.L,.L,.L,.D,.D,.D,.L,.D,.D]]
def T11 : List (List Face) := [[]]
def T12 : List (List Face) := [[], [.R,.R,.D,.D,.D,.B,.R,.R,.B,.B,.B,.R,.R,.B,.B,.B,.D,.D,.D,.B,.D,.D,.F,.F,.F,.R,.R,.F], [.R,.R,.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R,.F,.D,.D,.D], [.L,.D,.D,.D,.L,.L,.L,.U,.L,.D,.L,.L,.L,.U,.U,.U], [.U,.B,.B,.B,.U,.U,.U,.F,.F,.F,.U,.B,.U,.U,.U,.F], [.L,.L,.D,.D,.D,.L,.U,.U,.L,.L,.L,.D,.L,.U,.U,.L], [.L,.L,.L,.D,.D,.D,.L,.U,.U,.L,.L,.L,.D,.L,.U,.U], [.L,.L,.L,.B,.B,.B,.R,.B,.L,.B,.B,.B,.R,.R,.R,.B], [.B,.B,.B,.L,.F,.F,.F,.L,.L,.L,.B,.L,.F,.L,.L,.L], [.B,.B,.B,.D,.D,.D,.B,.U,.U,.U,.B,.B,.B,.D,.B,.U], [.B,.L,.L,.L,.D,.D,.D,.L,.U,.U,.L,.L,.L,.D,.L,.U,.U,.B,.B,.B], [.U,.U,.U,.L,.L,.L,.U,.R,.U,.U,.U,.L,.U,.R,.R,.R], [.D,.D,.L,.L,.D,.D,.D,.R,.R,.D,.L,.L,.D,.D,.D,.R,.R,.D,.D,.D], [.R,.R,.R,.D,.D,.D,.R,.U,.U,.R,.R,.R,.D,.R,.U,.U], [.F,.L,.L,.L,.F,.F,.F,.R,.R,.R,.F,.L,.F,.F,.F,.R], [.D,.D,.D,.B,.B,.D,.F,.F,.D,.D,.D,.B,.B,.D,.F,.F], [.U,.L,.L,.L,.U,.U,.U,.R,.R,.R,.U,.L,.U,.U,.U,.R], [.R,.R,.R,.D,.R,.U,.U,.R,.R,.R,.D,.D,.D,.R,.U,.U], [.L,.L,.L,.D,.D,.D,.R,.R,.D,.L,.D,.D,.D,.R,.R,.D], [.U,.U,.U,.R,.D,.D,.D,.R,.R,.R,.U,.R,.D,.R,.R,.R], [.R,.R,.R,.D,.D,.R,.U,.U,.R,.R,.R,.D,.D,.R,.U,.U], [.D,.L,.L,.L,.D,.D,.D,.R,.R,.D,.L,.D,.D,.D,.R,.R], [.F,.D,.D,.D,.F,.F,.F,.U,.U,.U,.F,.D,.F,.F,.F,.U], [.D,.D,.D,.B,.U,.U,.U,.B,.B,.B,.D,.B,.U,.B,.B,.B]]
def T13 : List (List Face) := [[], [.L,.L,.B,.B,.B,.L,.L,.B,.D,.D,.F,.D,.F,.F,.F,.L,.L,.F,.L,.L,.D,.D,.D,.F,.F,.F,.D,.D], [.F,.D,.D,.D,.R,.R,.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R], [.L,.L,.L,.D,.D,.D,.L,.U,.L,.L,.L,.D,.L,.U,.U,.U], [.U,.R,.R,.R,.U,.U,.U,.L,.L,.L,.U,.R,.U,.U,.U,.L], [.F,.F,.L,.D,.D,.D,.L,.L,.L,.U,.U,.U,.L,.D,.L,.L,.L,.U,.F,.F], [.R,.D,.D,.D,.R,.R,.R,.U,.U,.R,.D,.R,.R,.R,.U,.U], [.B,.B,.B,.L,.L,.B,.R,.B,.B,.B,.L,.L,.B,.R,.R,.R], [.D,.L,.L,.D,.D,.D,.R,.D,.L,.L,.D,.D,.D,.R,.R,.R], [.R,.R,.R,.B,.B,.B,.R,.F,.F,.R,.R,.R,.B,.R,.F,.F], [.L,.D,.D,.D,.L,.L,.L,.U,.U,.U,.L,.D,.L,.L,.L,.U], [.D,.D,.D,.R,.U,.U,.U,.R,.R,.R,.D,.R,.U,.R,.R,.R], [.D,.D,.B,.B,.D,.D,.D,.F,.F,.D,.B,.B,.D,.D,.D,.F,.F,.D,.D,.D], [.F,.F,.F,.D,.D,.D,.F,.U,.U,.U,.F,.F,.F,.D,.F,.U], [.L,.D,.L,.L,.L,.U,.U,.U,.L,.D,.D,.D,.L,.L,.L,.U], [.L,.L,.F,.R,.R,.R,.F,.F,.F,.L,.L,.F,.R,.F,.F,.F], [.U,.B,.B,.B,.U,.U,.U,.F,.F,.U,.B,.U,.U,.U,.F,.F], [.U,.B,.D,.B,.B,.B,.U,.U,.U,.B,.D,.D,.D,.B,.B,.B], [.B,.B,.B,.D,.D,.D,.F,.F,.D,.B,.D,.D,.D,.F,.F,.D], [.L,.D,.D,.L,.L,.L,.U,.U,.U,.L,.D,.D,.L,.L,.L,.U], [.U,.L,.L,.L,.D,.L,.U,.U,.U,.L,.L,.L,.D,.D,.D,.L]]
def T14 : List (List Face) := [[], [.B,.B,.B,.L,.L,.B,.L,.L,.D,.D,.D,.B,.B,.B,.U,.B,.B,.B,.U,.U,.U,.B,.B,.B,.D,.B,.B,.B,.L,.L], [.R,.R,.B,.B,.B,.R,.R,.B,.B,.B,.D,.D,.D,.B,.D,.D,.F,.F,.F,.R,.R,.F,.R,.R,.D,.D,.D,.B], [.R,.D,.D,.D,.R,.R,.R,.U,.R,.D,.R,.R,.R,.U,.U,.U], [.U,.R,.U,.U,.U,.L,.L,.U,.R,.R,.R,.U,.U,.U,.L,.L], [.R,.R,.D,.D,.R,.U,.U,.R,.R,.R,.D,.D,.R,.U,.U,.R], [.U,.R,.R,.U,.U,.U,.L,.L,.U,.R,.R,.U,.U,.U,.L,.L], [.B,.D,.D,.B,.B,.B,.U,.U,.U,.B,.D,.D,.B,.B,.B,.U], [.L,.L,.L,.D,.D,.L,.U,.U,.U,.L,.L,.L,.D,.D,.L,.U], [.L,.L,.U,.R,.R,.U,.U,.U,.L,.L,.U,.R,.R,.U,.U,.U], [.B,.D,.D,.D,.B,.B,.B,.U,.U,.U,.B,.D,.B,.B,.B,.U], [.D,.B,.B,.D,.D,.D,.F,.F,.F,.D,.B,.B,.D,.D,.D,.F], [.D,.D,.D,.B,.B,.U,.U,.U,.F,.U,.B,.B,.U,.U,.U,.F,.F,.F,.U,.D], [.L,.L,.L,.D,.D,.D,.L,.U,.U,.U,.L,.L,.L,.D,.L,.U], [.B,.D,.B,.B,.B,.U,.U,.U,.B,.D,.D,.D,.B,.B,.B,.U], [.B,.B,.U,.U,.U,.F,.U,.B,.B,.U,.U,.U,.F,.F,.F,.U], [.U,.R,.R,.R,.U,.U,.U,.L,.L,.U,.R,.U,.U,.U,.L,.L], [.L,.L,.L,.D,.L,.U,.U,.U,.L,.L,.L,.D,.D,.D,.L,.U]]
def T15 : List (List Face) := [[], [.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R,.F,.D,.D,.D,.R,.R], [.B,.R,.R,.B,.B,.B,.R,.R,.B,.B,.B,.D,.D,.D,.B,.D,.D,.F,.F,.F,.R,.R,.F,.R,.R,.D,.D,.D], [.D,.D,.D,.L,.L,.L,.D,.R,.R,.D,.D,.D,.L,.D,.R,.R], [.D,.D,.D,.F,.F,.F,.U,.F,.D,.F,.F,.F,.U,.U,.U,.F], [.B,.B,.B,.R,.F,.R,.R,.R,.B,.R,.F,.F,.F,.R,.R,.R], [.U,.U,.U,.L,.L,.U,.R,.R,.R,.U,.U,.U,.L,.L,.U,.R], [.D,.D,.D,.L,.L,.L,.U,.U,.L,.D,.L,.L,.L,.U,.U,.L], [.R,.R,.D,.D,.D,.L,.L,.L,.D,.R,.R,.D,.D,.D,.L,.D], [.L,.L,.L,.D,.D,.D,.L,.L,.L,.U,.U,.L,.D,.L,.L,.L,.U,.U,.L,.L], [.L,.L,.L,.U,.U,.L,.D,.L,.L,.L,.U,.U,.L,.D,.D,.D], [.U,.U,.U,.L,.U,.R,.R,.R,.U,.U,.U,.L,.L,.L,.U,.R], [.D,.D,.L,.L,.L,.D,.R,.R,.D,.D,.D,.L,.D,.R,.R,.D], [.B,.B,.B,.L,.L,.L,.B,.R,.B,.B,.B,.L,.B,.R,.R,.R], [.D,.D,.D,.R,.R,.R,.U,.U,.U,.R,.D,.R,.R,.R,.U,.R]]
def T16 : List (List Face) := [[], [.B,.B,.R,.R,.B,.B,.B,.R,.R,.B,.B,.B,.D,.D,.D,.B,.D,.D,.F,.F,.F,.R,.R,.F,.R,.R,.D,.D,.D,.B,.B,.B], [.R,.R,.R,.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R,.F,.D,.D,.D,.R,.R,.R], [.F,.L,.F,.F,.F,.R,.F,.L,.L,.L,.F,.F,.F,.R,.R,.R], [.R,.R,.R,.F,.B,.B,.B,.L,.L,.B,.R,.B,.B,.B,.L,.L,.B,.R,.R,.R,.F,.F,.F,.R], [.L,.B,.B,.B,.L,.L,.L,.F,.L,.B,.L,.L,.L,.F,.F,.F], [.F,.R,.F,.F,.F,.D,.D,.F,.R,.R,.R,.F,.F,.F,.R,.D,.D,.R,.R,.R], [.F,.L,.L,.L,.F,.F,.F,.R,.F,.L,.F,.F,.F,.R,.R,.R], [.F,.L,.B,.L,.L,.L,.F,.F,.F,.L,.B,.B,.B,.L,.L,.L], [.R,.R,.R,.B,.B,.B,.R,.F,.F,.F,.R,.R,.R,.B,.R,.F], [.D,.L,.D,.D,.D,.R,.R,.R,.D,.L,.L,.L,.D,.D,.D,.R], [.B,.R,.R,.D,.D,.D,.L,.L,.L,.D,.R,.R,.D,.D,.D,.L,.D,.B,.B,.B]]
def T17 : List (List Face) := [[], [.L,.B,.R,.B,.B,.B,.L,.L,.L,.B,.R,.R,.R,.B,.B,.L,.L,.L,.F,.F,.F,.L,.B,.L,.L,.L,.F,.L], [.F,.F,.D,.D,.D,.R,.R,.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R,.F,.F,.F], [.B,.B,.B,.L,.L,.L,.F,.F,.F,.L,.B,.L,.L,.L,.F,.L], [.R,.F,.F,.F,.D,.D,.F,.R,.R,.R,.F,.F,.F,.R,.D,.D,.R,.R,.R,.F], [.L,.L,.L,.F,.F,.F,.R,.F,.L,.F,.F,.F,.R,.R,.R,.F], [.B,.B,.U,.R,.U,.U,.U,.L,.L,.U,.R,.R,.R,.U,.U,.U,.L,.L,.B,.B], [.L,.D,.D,.D,.R,.R,.R,.D,.L,.L,.L,.D,.D,.D,.R,.D], [.L,.B,.R,.B,.B,.B,.L,.L,.L,.B,.R,.R,.R,.B,.B,.B]]
def T18 : List (List Face) := [[], [.B,.B,.B,.L,.L,.L,.F,.F,.F,.L,.B,.L,.L,.L,.F,.L,.L,.B,.R,.B,.B,.B,.L,.L,.L,.B,.R,.R,.R,.B,.B,.B], [.B,.B,.R,.R,.B,.B,.B,.D,.D,.F,.D,.D,.D,.F,.F,.F,.R,.R,.F,.F,.F,.R,.R,.F,.D,.D,.D,.R,.R,.B,.B,.B]]
def T19 : List (List Face) := [[]]

theorem T0_ok : checkLevel (fixedL basePts 0) (basePts.getD 0 (.inl 0)) 3 T0 = true := by decide +kernel
theorem T1_ok : checkLevel (fixedL basePts 1) (basePts.getD 1 (.inl 0)) 4 T1 = true := by decide +kernel
theorem T2_ok : checkLevel (fixedL basePts 2) (basePts.getD 2 (.inl 0)) 4 T2 = true := by decide +kernel
theorem T3_ok : checkLevel (fixedL basePts 3) (basePts.getD 3 (.inl 0)) 4 T3 = true := by decide +kernel
theorem T4_ok : checkLevel (fixedL basePts 4) (basePts.getD 4 (.inl 0)) 5 T4 = true := by decide +kernel
theorem T5_ok : checkLevel (fixedL basePts 5) (basePts.getD 5 (.inl 0)) 6 T5 = true := by decide +kernel
theorem T6_ok : checkLevel (fixedL basePts 6) (basePts.getD 6 (.inl 0)) 7 T6 = true := by decide +kernel
theorem T7_ok : checkLevel (fixedL basePts 7) (basePts.getD 7 (.inl 0)) 8 T7 = true := by decide +kernel
theorem T8_ok : checkLevel (fixedL basePts 8) (basePts.getD 8 (.inl 0)) 8 T8 = true := by decide +kernel
theorem T9_ok : checkLevel (fixedL basePts 9) (basePts.getD 9 (.inl 0)) 8 T9 = true := by decide +kernel
theorem T10_ok : checkLevel (fixedL basePts 10) (basePts.getD 10 (.inl 0)) 10 T10 = true := by decide +kernel
theorem T11_ok : checkLevel (fixedL basePts 11) (basePts.getD 11 (.inl 0)) 0 T11 = true := by decide +kernel
theorem T12_ok : checkLevel (fixedL basePts 12) (basePts.getD 12 (.inl 0)) 13 T12 = true := by decide +kernel
theorem T13_ok : checkLevel (fixedL basePts 13) (basePts.getD 13 (.inl 0)) 14 T13 = true := by decide +kernel
theorem T14_ok : checkLevel (fixedL basePts 14) (basePts.getD 14 (.inl 0)) 13 T14 = true := by decide +kernel
theorem T15_ok : checkLevel (fixedL basePts 15) (basePts.getD 15 (.inl 0)) 13 T15 = true := by decide +kernel
theorem T16_ok : checkLevel (fixedL basePts 16) (basePts.getD 16 (.inl 0)) 14 T16 = true := by decide +kernel
theorem T17_ok : checkLevel (fixedL basePts 17) (basePts.getD 17 (.inl 0)) 15 T17 = true := by decide +kernel
theorem T18_ok : checkLevel (fixedL basePts 18) (basePts.getD 18 (.inl 0)) 15 T18 = true := by decide +kernel
theorem T19_ok : checkLevel (fixedL basePts 19) (basePts.getD 19 (.inl 0)) 0 T19 = true := by decide +kernel
theorem T0_len : T0.length = 24 := by decide
theorem T1_len : T1.length = 22 := by decide
theorem T2_len : T2.length = 20 := by decide
theorem T3_len : T3.length = 18 := by decide
theorem T4_len : T4.length = 16 := by decide
theorem T5_len : T5.length = 14 := by decide
theorem T6_len : T6.length = 12 := by decide
theorem T7_len : T7.length = 10 := by decide
theorem T8_len : T8.length = 8 := by decide
theorem T9_len : T9.length = 6 := by decide
theorem T10_len : T10.length = 4 := by decide
theorem T11_len : T11.length = 1 := by decide
theorem T12_len : T12.length = 24 := by decide
theorem T13_len : T13.length = 21 := by decide
theorem T14_len : T14.length = 18 := by decide
theorem T15_len : T15.length = 15 := by decide
theorem T16_len : T16.length = 12 := by decide
theorem T17_len : T17.length = 9 := by decide
theorem T18_len : T18.length = 3 := by decide
theorem T19_len : T19.length = 1 := by decide

/-- The stabilizer chain `T0 … T19` exhibits `43252003274489856000` distinct reachable states,
each at distance at most `164`. -/
theorem exists_reachable_finset :
    ∃ P : Finset Cube, (∀ s ∈ P, Reachable s ∧ dist s ≤ 164) ∧ P.card = 43252003274489856000 := by
  have h20 : ∀ s ∈ ({1} : Finset Cube), (Reachable s ∧ dist s ≤ 0) ∧ ∀ p ∈ fixedL basePts 20, Fix s p := by
    intro s hs; rw [Finset.mem_singleton] at hs; subst hs
    exact ⟨⟨reachable_one, (dist_le []).trans (by simp)⟩, fun p _ => fix_one p⟩
  obtain ⟨P19, h19, c19⟩ := chain_step (fixedL basePts 19) (basePts.getD 19 (.inl 0)) 0 T19 T19_ok _ _ h20
  obtain ⟨P18, h18, c18⟩ := chain_step (fixedL basePts 18) (basePts.getD 18 (.inl 0)) 15 T18 T18_ok _ _ h19
  obtain ⟨P17, h17, c17⟩ := chain_step (fixedL basePts 17) (basePts.getD 17 (.inl 0)) 15 T17 T17_ok _ _ h18
  obtain ⟨P16, h16, c16⟩ := chain_step (fixedL basePts 16) (basePts.getD 16 (.inl 0)) 14 T16 T16_ok _ _ h17
  obtain ⟨P15, h15, c15⟩ := chain_step (fixedL basePts 15) (basePts.getD 15 (.inl 0)) 13 T15 T15_ok _ _ h16
  obtain ⟨P14, h14, c14⟩ := chain_step (fixedL basePts 14) (basePts.getD 14 (.inl 0)) 13 T14 T14_ok _ _ h15
  obtain ⟨P13, h13, c13⟩ := chain_step (fixedL basePts 13) (basePts.getD 13 (.inl 0)) 14 T13 T13_ok _ _ h14
  obtain ⟨P12, h12, c12⟩ := chain_step (fixedL basePts 12) (basePts.getD 12 (.inl 0)) 13 T12 T12_ok _ _ h13
  obtain ⟨P11, h11, c11⟩ := chain_step (fixedL basePts 11) (basePts.getD 11 (.inl 0)) 0 T11 T11_ok _ _ h12
  obtain ⟨P10, h10, c10⟩ := chain_step (fixedL basePts 10) (basePts.getD 10 (.inl 0)) 10 T10 T10_ok _ _ h11
  obtain ⟨P9, h9, c9⟩ := chain_step (fixedL basePts 9) (basePts.getD 9 (.inl 0)) 8 T9 T9_ok _ _ h10
  obtain ⟨P8, h8, c8⟩ := chain_step (fixedL basePts 8) (basePts.getD 8 (.inl 0)) 8 T8 T8_ok _ _ h9
  obtain ⟨P7, h7, c7⟩ := chain_step (fixedL basePts 7) (basePts.getD 7 (.inl 0)) 8 T7 T7_ok _ _ h8
  obtain ⟨P6, h6, c6⟩ := chain_step (fixedL basePts 6) (basePts.getD 6 (.inl 0)) 7 T6 T6_ok _ _ h7
  obtain ⟨P5, h5, c5⟩ := chain_step (fixedL basePts 5) (basePts.getD 5 (.inl 0)) 6 T5 T5_ok _ _ h6
  obtain ⟨P4, h4, c4⟩ := chain_step (fixedL basePts 4) (basePts.getD 4 (.inl 0)) 5 T4 T4_ok _ _ h5
  obtain ⟨P3, h3, c3⟩ := chain_step (fixedL basePts 3) (basePts.getD 3 (.inl 0)) 4 T3 T3_ok _ _ h4
  obtain ⟨P2, h2, c2⟩ := chain_step (fixedL basePts 2) (basePts.getD 2 (.inl 0)) 4 T2 T2_ok _ _ h3
  obtain ⟨P1, h1, c1⟩ := chain_step (fixedL basePts 1) (basePts.getD 1 (.inl 0)) 4 T1 T1_ok _ _ h2
  obtain ⟨P0, h0, c0⟩ := chain_step (fixedL basePts 0) (basePts.getD 0 (.inl 0)) 3 T0 T0_ok _ _ h1
  refine ⟨P0, fun s hs => (h0 s hs).1, ?_⟩
  rw [c0, T0_len, c1, T1_len, c2, T2_len, c3, T3_len, c4, T4_len, c5, T5_len, c6, T6_len, c7, T7_len, c8, T8_len, c9, T9_len, c10, T10_len, c11, T11_len, c12, T12_len, c13, T13_len, c14, T14_len, c15, T15_len, c16, T16_len, c17, T17_len, c18, T18_len, c19, T19_len, Finset.card_singleton]

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

/-- Every reachable state can be solved in at most `164` moves (stabilizer-chain bound). -/
theorem dist_le_of_reachable {s : Cube} (hs : Reachable s) : dist s ≤ 164 := by
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

/-- God's number is at most `164` (a weak, but fully kernel-checked, upper bound). -/
theorem godsNumber_le : godsNumber ≤ 164 :=
  (godsNumber_le_iff _).mpr fun _ hs => dist_le_of_reachable hs

/-- The half-turn-metric God's number lies in `[18, 164]`. -/
theorem godsNumber_bounds : 18 ≤ godsNumber ∧ godsNumber ≤ 164 :=
  ⟨eighteen_le_godsNumber, godsNumber_le⟩

end Rubik

#print axioms Rubik.godsNumber_spec
#print axioms Rubik.Reachable.valid
#print axioms Rubik.reachable_iff_valid
#print axioms Rubik.card_reachable
#print axioms Rubik.card_ball_17
#print axioms Rubik.eighteen_le_godsNumber
#print axioms Rubik.godsNumber_bounds
#print axioms Rubik.superflip_eq
