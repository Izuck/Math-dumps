
/-! ### The six levels: subgroups, membership tests and keys -/

def tetF (i : Fin 8) : Bool := (165 >>> i.val) % 2 == 1
def msF (j : Fin 12) : Bool := (170 >>> j.val) % 2 == 1
def tetN (y : ℕ) : Bool := (165 >>> (y / 3)) % 2 == 1
def msN (y : ℕ) : Bool := (170 >>> ((y - 24) / 2)) % 2 == 1

/-- All edges unflipped. -/
def HA (s : Cube) : Prop := ∀ j, s.eo j = 0
/-- ... and the four `E`-slice edges stay in the `E` slice. -/
def HS (s : Cube) : Prop := HA s ∧ ∀ j, (8 ≤ (s.ep j).val ↔ 8 ≤ j.val)
/-- ... and all corners untwisted: this is `⟨U, D, R2, L2, F2, B2⟩`. -/
def HC (s : Cube) : Prop := HS s ∧ ∀ i, s.co i = 0
/-- ... and the corner tetrads and the `M` slice are preserved. -/
def HD (s : Cube) : Prop := HC s ∧ (∀ i, tetF (s.cp i) = tetF i) ∧ ∀ j, msF (s.ep j) = msF j
/-- ... and all corners are solved. -/
def HE (s : Cube) : Prop := HD s ∧ ∀ i, s.cp i = i

theorem HA.mul {x y : Cube} (hx : HA x) (hy : HA y) : HA (x * y) := fun j => by
  simp [hx _, hy j]
theorem HS.mul {x y : Cube} (hx : HS x) (hy : HS y) : HS (x * y) :=
  ⟨hx.1.mul hy.1, fun j => by
    rw [Cube.mul_ep, Equiv.Perm.mul_apply]; exact (hx.2 _).trans (hy.2 j)⟩
theorem HC.mul {x y : Cube} (hx : HC x) (hy : HC y) : HC (x * y) :=
  ⟨hx.1.mul hy.1, fun i => by simp [hx.2 _, hy.2 i]⟩
theorem HD.mul {x y : Cube} (hx : HD x) (hy : HD y) : HD (x * y) :=
  ⟨hx.1.mul hy.1, fun i => by
    rw [Cube.mul_cp, Equiv.Perm.mul_apply]; exact (hx.2.1 _).trans (hy.2.1 i), fun j => by
    rw [Cube.mul_ep, Equiv.Perm.mul_apply]; exact (hx.2.2 _).trans (hy.2.2 j)⟩
theorem HE.mul {x y : Cube} (hx : HE x) (hy : HE y) : HE (x * y) :=
  ⟨hx.1.mul hy.1, fun i => by
    rw [Cube.mul_cp, Equiv.Perm.mul_apply, hy.2 i, hx.2 i]⟩

def cTrue (_ _ : ℕ) : Bool := true
def cNA (_ y : ℕ) : Bool := !(Nat.ble 24 y) || (y % 2 == 0)
def cNS (b y : ℕ) : Bool := cNA b y && (!(Nat.ble 24 y) || (Nat.ble 40 y == Nat.ble 40 b))
def cNC (b y : ℕ) : Bool := cNS b y && (Nat.ble 24 y || y % 3 == 0)
def cND (b y : ℕ) : Bool := cNC b y && (if 24 ≤ y then msN y == msN b else tetN y == tetN b)
def cNE (b y : ℕ) : Bool := cND b y && (Nat.ble 24 y || y == b)

def gN1 (_ y : ℕ) : ℕ := if 24 ≤ y then (y % 2) * 2 ^ ((y - 24) / 2) else 0
def gN2a (_ y : ℕ) : ℕ := if 24 ≤ y then 0 else (y % 3) * 4 ^ (y / 3)
def gN2b (b y : ℕ) : ℕ := if 40 ≤ b then 2 ^ ((y - 24) / 2) else 0
def gN3 (b y : ℕ) : ℕ :=
  if 24 ≤ b then (if msN b then 256 * 2 ^ ((y - 24) / 2) else 0) else (if tetN b then 2 ^ (y / 3) else 0)
def gN4 (b y : ℕ) : ℕ := if 24 ≤ b then 0 else (y / 3) * 8 ^ (b / 3)
def gN5 (b y : ℕ) : ℕ := if 24 ≤ b then ((y - 24) / 2) * 16 ^ ((b - 24) / 2) else 0

theorem fA : ∀ (j c : Fin 12) (o : ZMod 2), cNA (cb (.inr j)) (codeOf (.inr (c, o))) = true → o = 0 := by
  decide
theorem fS : ∀ (j c : Fin 12) (o : ZMod 2), cNS (cb (.inr j)) (codeOf (.inr (c, o))) = true →
    (8 ≤ c.val ↔ 8 ≤ j.val) := by decide
theorem fC : ∀ (i c : Fin 8) (o : ZMod 3), cNC (cb (.inl i)) (codeOf (.inl (c, o))) = true → o = 0 := by
  decide
theorem fD1 : ∀ (i c : Fin 8) (o : ZMod 3), cND (cb (.inl i)) (codeOf (.inl (c, o))) = true →
    tetF c = tetF i := by decide
theorem fD2 : ∀ (j c : Fin 12) (o : ZMod 2), cND (cb (.inr j)) (codeOf (.inr (c, o))) = true →
    msF c = msF j := by decide
theorem fE : ∀ (i c : Fin 8) (o : ZMod 3), cNE (cb (.inl i)) (codeOf (.inl (c, o))) = true →
    c = i := by decide

theorem memA {s : Cube} (h : memG cNA s) : HA s := fun j => by
  simpa [img, act, base] using fA j _ _ (h (.inr j))
theorem memS {s : Cube} (h : memG cNS s) : HS s :=
  ⟨memA fun p => (Bool.and_eq_true _ _ ▸ h p : _ ∧ _).1, fun j => by
    simpa [img, act, base] using fS j _ _ (h (.inr j))⟩
theorem memC {s : Cube} (h : memG cNC s) : HC s :=
  ⟨memS fun p => (Bool.and_eq_true _ _ ▸ h p : _ ∧ _).1, fun i => by
    simpa [img, act, base] using fC i _ _ (h (.inl i))⟩
theorem memD {s : Cube} (h : memG cND s) : HD s :=
  ⟨memC fun p => (Bool.and_eq_true _ _ ▸ h p : _ ∧ _).1, fun i => by
    simpa [img, act, base] using fD1 i _ _ (h (.inl i)), fun j => by
    simpa [img, act, base] using fD2 j _ _ (h (.inr j))⟩
theorem memE {s : Cube} (h : memG cNE s) : HE s :=
  ⟨memD fun p => (Bool.and_eq_true _ _ ▸ h p : _ ∧ _).1, fun i => by
    simpa [img, act, base] using fE i _ _ (h (.inl i))⟩

/-! Invariance of the keys under the next subgroup. -/

theorem g1c : ∀ (i i' c : Fin 8) (o o' : ZMod 3), gN1 (cb (.inl i)) (codeOf (.inl (c, o))) =
    gN1 (cb (.inl i')) (codeOf (.inl (c, o'))) := by decide
theorem g1e : ∀ (j j' c : Fin 12) (o : ZMod 2), gN1 (cb (.inr j)) (codeOf (.inr (c, o))) =
    gN1 (cb (.inr j')) (codeOf (.inr (c, o))) := by decide
theorem g2ac : ∀ (i i' c : Fin 8) (o : ZMod 3), gN2a (cb (.inl i)) (codeOf (.inl (c, o))) =
    gN2a (cb (.inl i')) (codeOf (.inl (c, o))) := by decide
theorem g2ae : ∀ (j j' c : Fin 12) (o : ZMod 2), gN2a (cb (.inr j)) (codeOf (.inr (c, o))) =
    gN2a (cb (.inr j')) (codeOf (.inr (c, o))) := by decide
theorem g2bc : ∀ (i i' c : Fin 8) (o o' : ZMod 3), gN2b (cb (.inl i)) (codeOf (.inl (c, o))) =
    gN2b (cb (.inl i')) (codeOf (.inl (c, o'))) := by decide
theorem g2be : ∀ (j j' c : Fin 12) (o : ZMod 2), (8 ≤ j'.val ↔ 8 ≤ j.val) →
    gN2b (cb (.inr j)) (codeOf (.inr (c, o))) = gN2b (cb (.inr j')) (codeOf (.inr (c, o))) := by decide
theorem g3c : ∀ (i i' c : Fin 8) (o : ZMod 3), tetF i' = tetF i →
    gN3 (cb (.inl i)) (codeOf (.inl (c, o))) = gN3 (cb (.inl i')) (codeOf (.inl (c, o))) := by decide
theorem g3e : ∀ (j j' c : Fin 12) (o : ZMod 2), msF j' = msF j →
    gN3 (cb (.inr j)) (codeOf (.inr (c, o))) = gN3 (cb (.inr j')) (codeOf (.inr (c, o))) := by decide
theorem g4e : ∀ (j j' c : Fin 12) (o : ZMod 2), gN4 (cb (.inr j)) (codeOf (.inr (c, o))) =
    gN4 (cb (.inr j')) (codeOf (.inr (c, o))) := by decide

theorem inv1 (x y : Cube) (hy : HA y) : keyG gN1 (x * y) = keyG gN1 x :=
  keyG_mul gN1 x y (fun i c o => g1c _ _ _ _ _) (fun j c o => by rw [hy j, add_zero]; exact g1e _ _ _ _)
theorem inv2s (x y : Cube) (hy : HS y) : keyG gN2b (x * y) = keyG gN2b x :=
  keyG_mul gN2b x y (fun i c o => g2bc _ _ _ _ _)
    (fun j c o => by rw [hy.1 j, add_zero]; exact g2be _ _ _ _ (hy.2 j))
theorem inv2c (x y : Cube) (hy : HC y) : keyG gN2a (x * y) = keyG gN2a x :=
  keyG_mul gN2a x y (fun i c o => by rw [hy.2 i, add_zero]; exact g2ac _ _ _ _)
    (fun j c o => by rw [hy.1.1 j, add_zero]; exact g2ae _ _ _ _)
theorem inv3 (x y : Cube) (hy : HD y) : keyG gN3 (x * y) = keyG gN3 x :=
  keyG_mul gN3 x y (fun i c o => by rw [hy.1.2 i, add_zero]; exact g3c _ _ _ _ (hy.2.1 i))
    (fun j c o => by rw [hy.1.1.1 j, add_zero]; exact g3e _ _ _ _ (hy.2.2 j))
theorem inv4 (x y : Cube) (hy : HE y) : keyG gN4 (x * y) = keyG gN4 x :=
  keyG_mul gN4 x y (fun i c o => by rw [hy.1.1.2 i, add_zero, hy.2 i])
    (fun j c o => by rw [hy.1.1.1.1 j, add_zero]; exact g4e _ _ _ _)
