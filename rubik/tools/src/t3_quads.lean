
/-! ### The squares-group level: a key built from 4-sets of corners

The twelve 4-sets in `quadL` (two corners of each tetrad, forming "matching" pairs) are permuted
among themselves by the corner permutations of the squares group. -/

def quadL : List (List (Fin 8)) := @QUADL@
def quadLN : List (List ℕ) := @QUADLN@

def quadF : Finset (Finset (Fin 8)) := (quadL.map List.toFinset).toFinset

/-- The corner permutation of `y` permutes the twelve 4-sets. -/
def PQ (y : Cube) : Prop := quadF.image (fun S => S.image y.cp) = quadF

instance (y : Cube) : Decidable (PQ y) :=
  inferInstanceAs (Decidable (quadF.image (fun S => S.image y.cp) = quadF))

def qkey (s : Cube) : ℕ := (quadL.map (fun S => 2 ^ ((S.map (fun i => 2 ^ (s.cp i).val)).sum))).sum

theorem qkey_eq (s : Cube) : qkey s = ∑ T ∈ quadF, 2 ^ (∑ i ∈ T, 2 ^ (s.cp i).val) := by
  unfold qkey quadF
  rw [List.sum_toFinset _ (by decide : (quadL.map List.toFinset).Nodup), List.map_map]
  congr 1

theorem qkey_mul (x y : Cube) (hy : PQ y) : qkey (x * y) = qkey x := by
  rw [qkey_eq, qkey_eq]
  have h1 : ∀ T : Finset (Fin 8), ∑ i ∈ T, 2 ^ ((x * y).cp i).val =
      ∑ j ∈ T.image y.cp, 2 ^ (x.cp j).val := by
    intro T
    rw [Finset.sum_image (fun a _ b _ h => y.cp.injective h)]
    rfl
  simp only [h1]
  conv_rhs => rw [← hy]
  rw [Finset.sum_image (fun a _ b _ h => Finset.image_injective y.cp.injective h)]

theorem PQ.mul {x y : Cube} (hx : PQ x) (hy : PQ y) : PQ (x * y) := by
  unfold PQ at *
  have : (fun S : Finset (Fin 8) => S.image (x * y).cp) =
      (fun S => S.image x.cp) ∘ (fun S => S.image y.cp) := by
    funext S
    simp only [Function.comp, Finset.image_image]
    rfl
  rw [this, ← Finset.image_image, hy, hx]

theorem PQ_of_cp {y : Cube} (h : ∀ i, y.cp i = i) : PQ y := by
  unfold PQ
  have : (fun S : Finset (Fin 8) => S.image y.cp) = id := by
    funext S; ext j; simp [h]
  rw [this, Finset.image_id]

/-- `HD` together with the 4-set condition: the corner positions are those of the squares group. -/
def HD3 (s : Cube) : Prop := HD s ∧ PQ s

theorem HD3.mul_HE {x y : Cube} (hx : HD3 x) (hy : HE y) : HD3 (x * y) :=
  ⟨hx.1.mul hy.1, hx.2.mul (PQ_of_cp hy.2)⟩

noncomputable def qkeyT (tr : ℕ → ℕ) : ℕ :=
  (quadLN.map (fun S => 2 ^ ((S.map (fun b => 2 ^ (tr b / 3))).sum))).sum

noncomputable def qkeyW (w : List ℕ) : ℕ := qkeyT (trackN w)

theorem quadLN_eq : quadLN = quadL.map (fun S => S.map (fun i => cb (.inl i))) := by decide

theorem track_div (w : List ℕ) (i : Fin 8) : trackN w (cb (.inl i)) / 3 = ((evalW w).cp i).val := by
  rw [trackN_cb]
  show (3 * ((evalW w).cp i).val + ((evalW w).co i + 0).val) / 3 = _
  have h := ZMod.val_lt ((evalW w).co i + 0)
  omega

theorem qkeyW_spec (w : List ℕ) : qkeyW w = qkey (evalW w) := by
  unfold qkeyW qkeyT qkey
  rw [quadLN_eq, List.map_map]
  congr 1
  refine List.map_congr_left fun S _ => ?_
  have : ((fun b => 2 ^ (trackN w b / 3)) ∘ fun i : Fin 8 => cb (Sum.inl i)) =
      fun i => 2 ^ ((evalW w).cp i).val := by
    funext i; simp only [Function.comp, track_div]
  simp only [Function.comp, List.map_map]
  rw [← this]

/-- Key for the cosets of the squares-group pattern inside `⟨U,D,R2,L2,F2,B2⟩`. -/
def K3 (s : Cube) : ℕ := keyG gN3 s + 65536 * qkey s
noncomputable def K3T (tr : ℕ → ℕ) : ℕ := keyT gN3 tr + 65536 * qkeyT tr

theorem K3T_spec (w : List ℕ) : K3T (trackN w) = K3 (evalW w) := by
  show keyW gN3 w + 65536 * qkeyW w = _
  rw [keyW_spec, qkeyW_spec]; rfl

theorem inv3' (x y : Cube) (hy : HD3 y) : K3 (x * y) = K3 x := by
  unfold K3; rw [inv3 x y hy.1, qkey_mul x y hy.2]
