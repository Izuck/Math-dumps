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

