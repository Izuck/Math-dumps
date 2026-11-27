
namespace Rubik

/-! ## Stage 4: a Thistlethwaite-style subgroup chain and the upper bound

The chain is `G ⊃ {eo = 0} ⊃ {eo = 0, E slice preserved} ⊃ ⟨U,D,R2,L2,F2,B2⟩ ⊃ (a subgroup with the
corner and edge pattern of the squares group ⟨U2,D2,R2,L2,F2,B2⟩) ⊃ {corners solved} ⊃ 1`.  For each step a table of coset representatives (found by breadth-first
search outside Lean) is checked by the kernel: every word lies in the right subgroup, is short,
and the words have pairwise distinct values of a key that is constant on cosets.  The product of
the table sizes is the order of the cube group, so every reachable state is a product of one
representative per level. -/

/-- Code of an oriented cubie position: corners `3 * pos + ori`, edges `24 + 2 * pos + ori`. -/
def codeOf : PtImg → ℕ
  | .inl x => 3 * x.1.val + x.2.val
  | .inr x => 24 + 2 * x.1.val + x.2.val

def faceOfNat : ℕ → Face
  | 0 => .U | 1 => .D | 2 => .R | 3 => .L | 4 => .F | _ => .B

/-- Moves numbered `3 * face + k`. -/
def mvOfNat (n : ℕ) : Move := ⟨faceOfNat (n % 18 / 3), ⟨n % 3, Nat.mod_lt _ (by norm_num)⟩⟩

/-- The value of a word given by move numbers. -/
def evalW (w : List ℕ) : Cube := evalSeq (w.map mvOfNat)

theorem evalW_cons (m : ℕ) (w : List ℕ) : evalW (m :: w) = (mvOfNat m).toCube * evalW w := by
  simp [evalW, evalSeq]

theorem reachable_evalW (w : List ℕ) : Reachable (evalW w) := ⟨_, rfl⟩

theorem dist_evalW_le (w : List ℕ) : dist (evalW w) ≤ w.length := by
  simpa [evalW] using dist_le (w.map mvOfNat)

@ALLTAB@

/-- One move applied to a code: a table lookup made of kernel-accelerated `Nat` operations. -/
def stepN (m c : ℕ) : ℕ := (allTab >>> (6 * (48 * (m % 18) + c))) % 64

theorem stepN_spec : ∀ (k : Fin 18) (x : PtImg),
    codeOf (act (mvOfNat k.val).toCube x) = stepN k.val (codeOf x) := by decide +kernel

theorem stepN_spec' (n : ℕ) (x : PtImg) :
    codeOf (act (mvOfNat n).toCube x) = stepN n (codeOf x) := by
  have h := stepN_spec ⟨n % 18, Nat.mod_lt _ (by norm_num)⟩ x
  have h1 : mvOfNat (n % 18) = mvOfNat n := by
    simp [mvOfNat, Nat.mod_mod_of_dvd n (by norm_num : 3 ∣ 18)]
  have h2 : stepN (n % 18) = stepN n := by funext c; simp [stepN]
  simpa only [h1, h2] using h

/-- Track a code through a word (raw recursor: fast in the kernel). -/
noncomputable def trackN (w : List ℕ) (c : ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) c (fun m _ ih => stepN m ih) w

theorem act_one (x : PtImg) : act 1 x = x := by
  rcases x with ⟨p, o⟩ | ⟨p, o⟩ <;> simp [act]

theorem trackN_spec (w : List ℕ) (x : PtImg) : trackN w (codeOf x) = codeOf (act (evalW w) x) := by
  induction w with
  | nil => show codeOf x = _; rw [show evalW [] = 1 from rfl, act_one]
  | cons m w ih =>
    rw [evalW_cons, act_mul, stepN_spec', ← ih]; rfl

def cb (p : Pt) : ℕ := codeOf (base p)

def allPts : List Pt := [.inl 0, .inl 1, .inl 2, .inl 3, .inl 4, .inl 5, .inl 6, .inl 7,
  .inr 0, .inr 1, .inr 2, .inr 3, .inr 4, .inr 5, .inr 6, .inr 7, .inr 8, .inr 9, .inr 10, .inr 11]

def baseCodes : List ℕ := [0, 3, 6, 9, 12, 15, 18, 21, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46]

theorem baseCodes_eq : baseCodes = allPts.map cb := by decide
theorem univ_eq_allPts : (Finset.univ : Finset Pt) = allPts.toFinset := by decide
theorem mem_allPts (p : Pt) : p ∈ allPts := List.mem_toFinset.mp (univ_eq_allPts ▸ Finset.mem_univ p)

theorem sum_allPts (F : Pt → ℕ) : ∑ p, F p = (allPts.map F).sum := by
  rw [univ_eq_allPts, List.sum_toFinset _ (by decide : allPts.Nodup)]

/-- Subgroup membership test, stated on the abstract state. -/
def memG (cN : ℕ → ℕ → Bool) (s : Cube) : Prop := ∀ p : Pt, cN (cb p) (codeOf (img s p)) = true

/-- Coset key, stated on the abstract state. -/
def keyG (gN : ℕ → ℕ → ℕ) (s : Cube) : ℕ := ∑ p : Pt, gN (cb p) (codeOf (img s p))

/-- Membership test and key computed from a tracking function `tr` (code of a cubie ↦ code of its
image); raw recursors for kernel speed. -/
noncomputable def memT (cN : ℕ → ℕ → Bool) (tr : ℕ → ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun b _ ih => cN b (tr b) && ih) baseCodes

noncomputable def keyT (gN : ℕ → ℕ → ℕ) (tr : ℕ → ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0 (fun b _ ih => gN b (tr b) + ih) baseCodes

noncomputable def memW (cN : ℕ → ℕ → Bool) (w : List ℕ) : Bool := memT cN (trackN w)

noncomputable def keyW (gN : ℕ → ℕ → ℕ) (w : List ℕ) : ℕ := keyT gN (trackN w)

theorem rec_and (f : ℕ → Bool) (l : List ℕ) :
    @List.rec ℕ (fun _ => Bool) true (fun b _ ih => f b && ih) l = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.all_cons, ← ih]

theorem rec_sum (f : ℕ → ℕ) (l : List ℕ) :
    @List.rec ℕ (fun _ => ℕ) 0 (fun b _ ih => f b + ih) l = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, List.sum_cons, ← ih]

theorem trackN_cb (w : List ℕ) (p : Pt) : trackN w (cb p) = codeOf (img (evalW w) p) :=
  trackN_spec w (base p)

theorem memW_spec {cN : ℕ → ℕ → Bool} {w : List ℕ} (h : memW cN w = true) : memG cN (evalW w) := by
  intro p
  rw [memW, memT, rec_and, baseCodes_eq, List.all_eq_true] at h
  have := h (cb p) (List.mem_map_of_mem (mem_allPts p))
  rwa [trackN_cb] at this

theorem keyW_spec (gN : ℕ → ℕ → ℕ) (w : List ℕ) : keyW gN w = keyG gN (evalW w) := by
  rw [keyW, keyT, rec_sum, baseCodes_eq, List.map_map, keyG, sum_allPts]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp, trackN_cb]

/-- The key is invariant under right multiplication by `y` as soon as its weights are. -/
theorem keyG_mul (gN : ℕ → ℕ → ℕ) (x y : Cube)
    (hc : ∀ (i c : Fin 8) (o : ZMod 3), gN (cb (.inl i)) (codeOf (.inl (c, o + y.co i))) =
      gN (cb (.inl (y.cp i))) (codeOf (.inl (c, o))))
    (he : ∀ (j c : Fin 12) (o : ZMod 2), gN (cb (.inr j)) (codeOf (.inr (c, o + y.eo j))) =
      gN (cb (.inr (y.ep j))) (codeOf (.inr (c, o)))) :
    keyG gN (x * y) = keyG gN x := by
  unfold keyG
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · have : ∀ i, gN (cb (.inl i)) (codeOf (img (x * y) (.inl i))) =
        (fun k => gN (cb (.inl k)) (codeOf (img x (.inl k)))) (y.cp i) := by
      intro i
      simp only [img, act, base, Cube.mul_cp, Cube.mul_co, Equiv.Perm.mul_apply, add_zero]
      exact hc i _ _
    simp only [this]
    exact Equiv.sum_comp y.cp (fun k => gN (cb (.inl k)) (codeOf (img x (.inl k))))
  · have : ∀ j, gN (cb (.inr j)) (codeOf (img (x * y) (.inr j))) =
        (fun k => gN (cb (.inr k)) (codeOf (img x (.inr k)))) (y.ep j) := by
      intro j
      simp only [img, act, base, Cube.mul_ep, Cube.mul_eo, Equiv.Perm.mul_apply, add_zero]
      exact he j _ _
    simp only [this]
    exact Equiv.sum_comp y.ep (fun k => gN (cb (.inr k)) (codeOf (img x (.inr k))))

/-- One step of a general subgroup chain. -/
theorem chain_step2 (H H' : Cube → Prop) (K : Cube → ℕ) (d D : ℕ)
    (hclos : ∀ x y, H x → H' y → H (x * y)) (hinv : ∀ x y, H' y → K (x * y) = K x)
    (ws : List (List ℕ)) (hws : ∀ w ∈ ws, H (evalW w) ∧ w.length ≤ d)
    (hnd : (ws.map (fun w => K (evalW w))).Nodup)
    (P : Finset Cube) (hP : ∀ s ∈ P, (Reachable s ∧ dist s ≤ D) ∧ H' s) :
    ∃ P' : Finset Cube, (∀ s ∈ P', (Reachable s ∧ dist s ≤ d + D) ∧ H s) ∧
      P'.card = ws.length * P.card := by
  classical
  set L : List Cube := ws.map evalW with hL
  have hnd' : (L.map K).Nodup := by rw [hL, List.map_map]; exact hnd
  have hLnd : L.Nodup := List.Nodup.of_map _ hnd'
  refine ⟨Finset.image₂ (· * ·) L.toFinset P, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hs
    rw [List.mem_toFinset] at hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    have hd : dist (evalW w * y) ≤ d + D :=
      (dist_mul_le (reachable_evalW w) (hP y hy).1.1).trans
        (Nat.add_le_add ((dist_evalW_le w).trans (hws w hw).2) (hP y hy).1.2)
    exact ⟨⟨(reachable_evalW w).mul (hP y hy).1.1, hd⟩, hclos _ _ (hws w hw).1 (hP y hy).2⟩
  · rw [← List.length_map (as := ws) evalW, ← hL, ← List.toFinset_card_of_nodup hLnd]
    refine Finset.card_image₂_iff.mpr ?_
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' e
    change x * y = x' * y' at e
    simp only [Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hxy hxy'
    have e1 : K x = K x' := by
      rw [← hinv x y (hP y hxy.2).2, e, hinv x' y' (hP y' hxy'.2).2]
    have e2 : x = x' := List.inj_on_of_nodup_map hnd' hxy.1 hxy'.1 e1
    subst e2
    rw [mul_left_cancel e]

/-! ### Kernel-checkable chunks of a table -/

/-- The keys are strictly increasing and lie in `[lo, hi)`. -/
def sortedIn : ℕ → ℕ → List ℕ → Bool
  | lo, hi, [] => decide (lo ≤ hi)
  | lo, hi, k :: ks => decide (lo ≤ k) && sortedIn (k + 1) hi ks

theorem sortedIn_spec : ∀ (ks : List ℕ) (lo hi : ℕ), sortedIn lo hi ks = true →
    ks.Pairwise (· < ·) ∧ (∀ k ∈ ks, lo ≤ k ∧ k < hi) ∧ lo ≤ hi := by
  intro ks
  induction ks with
  | nil => intro lo hi h; simpa [sortedIn] using h
  | cons k ks ih =>
    intro lo hi h
    simp only [sortedIn, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h.2
    refine ⟨List.pairwise_cons.mpr ⟨fun k' hk' => (h2 k' hk').1, h1⟩, ?_, by omega⟩
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact ⟨h.1, by omega⟩
    · have := h2 k' hk'; exact ⟨by omega, this.2⟩

/-- A chunk of a table: all words are in the subgroup `memG cN`, have length at most `d`, and
their keys are strictly increasing inside `[lo, hi)`. -/
def ChunkP (cN : ℕ → ℕ → Bool) (K : Cube → ℕ) (d lo hi : ℕ) (ws : List (List ℕ)) : Prop :=
  (∀ w ∈ ws, memG cN (evalW w) ∧ w.length ≤ d) ∧
  (ws.map (fun w => K (evalW w))).Pairwise (· < ·) ∧
  (∀ w ∈ ws, lo ≤ K (evalW w) ∧ K (evalW w) < hi) ∧ lo ≤ hi

noncomputable def chunkCheck (cN : ℕ → ℕ → Bool) (KW : List ℕ → ℕ) (d lo hi : ℕ)
    (ws : List (List ℕ)) : Bool :=
  ws.all (fun w => memW cN w && decide (w.length ≤ d)) && sortedIn lo hi (ws.map KW)

theorem chunkCheck_spec {cN : ℕ → ℕ → Bool} {KW : List ℕ → ℕ} {K : Cube → ℕ} {d lo hi : ℕ}
    {ws : List (List ℕ)} (hK : ∀ w, KW w = K (evalW w))
    (h : chunkCheck cN KW d lo hi ws = true) : ChunkP cN K d lo hi ws := by
  simp only [chunkCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨s1, s2, s3⟩ := sortedIn_spec _ _ _ h2
  have e : ws.map KW = ws.map (fun w => K (evalW w)) := List.map_congr_left fun w _ => hK w
  rw [e] at s1 s2
  refine ⟨fun w hw => ⟨memW_spec (h1 w hw).1, (h1 w hw).2⟩, s1, fun w hw => ?_, s3⟩
  exact s2 _ (List.mem_map_of_mem (f := fun w => K (evalW w)) hw)

/-! Words packed into numerals (base 32, digit = move number + 1, first move least significant):
this keeps the source small.  `trackP` tracks a code through a packed word directly. -/

def wordAux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | f + 1, m + 1 => ((m + 1) % 32 - 1) :: wordAux f ((m + 1) / 32)

def wordOf (n : ℕ) : List ℕ := wordAux 40 n

noncomputable def trackP (fuel : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ => ℕ → ℕ → ℕ) (fun _ c => c)
    (fun _ ih n c => @Nat.rec (fun _ => ℕ) c
      (fun m _ => stepN ((m + 1) % 32 - 1) (ih ((m + 1) / 32) c)) n) fuel

theorem trackP_eq_aux : ∀ (fuel n c : ℕ), trackP fuel n c = trackN (wordAux fuel n) c := by
  intro fuel
  induction fuel with
  | zero => intro n c; rfl
  | succ f ih =>
    intro n c
    cases n with
    | zero => rfl
    | succ m =>
      show stepN ((m + 1) % 32 - 1) (trackP f ((m + 1) / 32) c) = _
      rw [ih]; rfl

theorem trackP_eq (n : ℕ) : trackP 40 n = trackN (wordOf n) := funext fun c => trackP_eq_aux 40 n c

noncomputable def chunkCheckP (cN : ℕ → ℕ → Bool) (KT : (ℕ → ℕ) → ℕ) (d lo hi : ℕ)
    (ns : List ℕ) : Bool :=
  ns.all (fun n => memT cN (trackP 40 n) && decide ((wordOf n).length ≤ d)) &&
    sortedIn lo hi (ns.map (fun n => KT (trackP 40 n)))

theorem chunkCheckP_spec {cN : ℕ → ℕ → Bool} {KT : (ℕ → ℕ) → ℕ} {K : Cube → ℕ} {d lo hi : ℕ}
    {ns : List ℕ} (hK : ∀ w, KT (trackN w) = K (evalW w))
    (h : chunkCheckP cN KT d lo hi ns = true) : ChunkP cN K d lo hi (ns.map wordOf) := by
  refine chunkCheck_spec (KW := fun w => KT (trackN w)) hK ?_
  simp only [chunkCheckP, trackP_eq] at h
  simpa only [chunkCheck, memW, List.all_map, List.map_map, Function.comp_def] using h

theorem ChunkP.append {cN : ℕ → ℕ → Bool} {K : Cube → ℕ} {d lo mid hi : ℕ} {a b : List (List ℕ)}
    (ha : ChunkP cN K d lo mid a) (hb : ChunkP cN K d mid hi b) : ChunkP cN K d lo hi (a ++ b) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  refine ⟨?_, ?_, ?_, a4.trans b4⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    exacts [a1 w h, b1 w h]
  · rw [List.map_append, List.pairwise_append]
    refine ⟨a2, b2, ?_⟩
    intro x hx y hy
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hy
    exact (a3 w hw).2.trans_le (b3 w' hw').1
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact ⟨(a3 w h).1, (a3 w h).2.trans_le b4⟩
    · exact ⟨a4.trans (b3 w h).1, (b3 w h).2⟩

/-- A fully checked table gives one step of the chain. -/
theorem level_step (cN : ℕ → ℕ → Bool) (K : Cube → ℕ) (d hi : ℕ) (H H' : Cube → Prop)
    (hclos : ∀ x y, H x → H' y → H (x * y)) (hinv : ∀ x y, H' y → K (x * y) = K x)
    (ws : List (List ℕ)) (hck : ChunkP cN K d 0 hi ws)
    (hH : ∀ w ∈ ws, memG cN (evalW w) → H (evalW w)) (D : ℕ)
    (P : Finset Cube) (hP : ∀ s ∈ P, (Reachable s ∧ dist s ≤ D) ∧ H' s) :
    ∃ P' : Finset Cube, (∀ s ∈ P', (Reachable s ∧ dist s ≤ d + D) ∧ H s) ∧
      P'.card = ws.length * P.card :=
  chain_step2 H H' K d D hclos hinv ws (fun w hw => ⟨hH w hw (hck.1 w hw).1, (hck.1 w hw).2⟩)
    (hck.2.1.imp (fun h => Nat.ne_of_lt h)) P hP

theorem dist_le_of_finset {B : ℕ} (hex : ∃ P : Finset Cube, (∀ s ∈ P, Reachable s ∧ dist s ≤ B) ∧
    P.card = 43252003274489856000) {s : Cube} (hs : Reachable s) : dist s ≤ B := by
  classical
  obtain ⟨P, hP, hcard⟩ := hex
  have hsub : P ⊆ Finset.univ.filter Valid := fun x hx => by
    simpa using (hP x hx).1.valid
  have hV : (Finset.univ.filter Valid).card = 43252003274489856000 := by
    rw [← card_valid, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have := Finset.eq_of_subset_of_card_le hsub (by rw [hV, hcard])
  exact (hP s (this ▸ by simpa using hs.valid)).2
