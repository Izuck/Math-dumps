import FormalConjectures.OEIS.«92243»

namespace OMA.SieveA

def patt (p K : ℕ) : ℕ := (2 ^ (p * K) - 1) / (2 ^ p - 1)

def compMask (B a : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | p :: ps, acc => compMask B a ps (acc ||| (patt p (B / p + 2) >>> (a % p)))

def primeMask (B a len : ℕ) (base : List ℕ) : ℕ :=
  (2 ^ len - 1) ^^^ (compMask B a base 0 % 2 ^ len)

def bitc (a y i k : ℕ) (acc : List ℕ) : List ℕ :=
  match Nat.land (Nat.shiftRight y k) 1 with
  | 0 => acc
  | _ + 1 => (a + (i + k)) :: acc

def ext8 (a x : ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | j + 1, acc => ext8 a x j
      (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 0 (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 1
      (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 2 (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 3
      (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 4 (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 5
      (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 6 (bitc a (Nat.shiftRight x (8 * j)) (8 * j) 7 acc))))))))

def seg (B S T : ℕ) (base : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | j + 1, acc =>
    seg B S T base j
      (ext8 (S + j * (8 * B)) (primeMask (8 * B) (S + j * (8 * B)) (min (8 * B) (T - j * (8 * B))) base) B acc)

def primeListAux (B : ℕ) : ℕ → ℕ → List ℕ
  | 0, N => (List.range (N + 1)).filter (fun m => decide m.Prime)
  | f + 1, N =>
    match Nat.ble 5 N with
    | false => (match Nat.ble 2 N with
        | false => []
        | true => (match Nat.ble 3 N with
          | false => [2]
          | true => [2, 3]))
    | true =>
      match Nat.ble (2 ^ (N.log2 / 2 + 1)) N && Nat.blt N (2 ^ (N.log2 / 2 + 1) * 2 ^ (N.log2 / 2 + 1)) with
      | true => primeListAux B f (2 ^ (N.log2 / 2 + 1)) ++
          seg B (2 ^ (N.log2 / 2 + 1) + 1) (N - 2 ^ (N.log2 / 2 + 1)) (primeListAux B f (2 ^ (N.log2 / 2 + 1)))
            ((N - 2 ^ (N.log2 / 2 + 1)) / (8 * B) + 1) []
      | false => (List.range (N + 1)).filter (fun m => decide m.Prime)

def primeList (N : ℕ) : List ℕ := primeListAux 256 64 N

end OMA.SieveA

namespace OMA.SieveA

def geo (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => 2 ^ p * geo p K + 1

theorem two_le_two_pow {p : ℕ} (hp : 0 < p) : 2 ≤ 2 ^ p := by
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp

theorem geo_mul (p K : ℕ) : (2 ^ p - 1) * geo p K + 1 = 2 ^ (p * K) := by
  induction K with
  | zero => simp [geo]
  | succ K ih =>
    obtain ⟨v, hv⟩ : ∃ v, 2 ^ p = v + 1 := ⟨2 ^ p - 1, by have := Nat.one_le_two_pow (n := p); omega⟩
    rw [Nat.mul_succ, pow_add, ← ih]
    simp only [geo]
    rw [hv, Nat.add_sub_cancel]
    ring

theorem patt_eq {p : ℕ} (hp : 0 < p) (K : ℕ) : patt p K = geo p K := by
  unfold patt
  have h := geo_mul p K
  have h2 := two_le_two_pow hp
  have : 2 ^ (p * K) - 1 = (2 ^ p - 1) * geo p K := by omega
  rw [this]
  exact Nat.mul_div_cancel_left _ (by omega)

theorem geo_testBit {p : ℕ} (hp : 0 < p) (K j : ℕ) :
    (geo p K).testBit j = decide (p ∣ j ∧ j < p * K) := by
  induction K generalizing j with
  | zero => simp [geo]
  | succ K ih =>
    have h1 : 1 < 2 ^ p := two_le_two_pow hp
    simp only [geo]
    rw [Nat.testBit_two_pow_mul_add _ h1]
    split
    · rename_i hj
      cases j with
      | zero => simp [hp]
      | succ j =>
        have : ¬ p ∣ j + 1 := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
        simp [Nat.testBit_succ, this]
    · rename_i hj
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hj)
      rw [Nat.add_sub_cancel_left, ih, Nat.mul_succ]
      have : p ∣ p + i ↔ p ∣ i := Nat.dvd_add_self_left
      simp only [this]
      congr 1
      apply propext
      constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩

theorem compMask_testBit (B a : ℕ) (ps : List ℕ) (hps : ∀ p ∈ ps, 0 < p) (acc i : ℕ) (hi : i < B) :
    (compMask B a ps acc).testBit i = (acc.testBit i || ps.any (fun p => decide (p ∣ a + i))) := by
  induction ps generalizing acc with
  | nil => simp [compMask]
  | cons p ps ih =>
    have hp : 0 < p := hps p (by simp)
    simp only [compMask]
    rw [ih (fun q hq => hps q (by simp [hq])), Nat.testBit_lor, Nat.testBit_shiftRight, patt_eq hp,
      geo_testBit hp, List.any_cons, Bool.or_assoc]
    congr 2
    have h1 := Nat.div_add_mod B p
    have h2 := Nat.mod_lt B hp
    have h3 := Nat.mod_lt a hp
    have hb : a % p + i < p * (B / p + 2) := by rw [Nat.mul_add]; omega
    have hd : p ∣ a % p + i ↔ p ∣ a + i := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.mod_add_mod]
    simp [hb, hd]

theorem primeMask_testBit (B a len : ℕ) (base : List ℕ) (hps : ∀ p ∈ base, 0 < p) (hlen : len ≤ B)
    (H : ∀ i, i < len → ((a + i).Prime ↔ ∀ p ∈ base, ¬ p ∣ a + i)) (i : ℕ) :
    (primeMask B a len base).testBit i = (decide (i < len) && decide (a + i).Prime) := by
  unfold primeMask
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < len
  · rw [compMask_testBit B a base hps 0 i (by omega)]
    simp only [hi, H i hi]
    rw [Bool.eq_iff_iff]
    simp
  · simp [hi]

def sel (a x i : ℕ) : List ℕ := if x.testBit i then [a + i] else []

theorem bitc_eq (a x s k : ℕ) (acc : List ℕ) :
    bitc a (Nat.shiftRight x s) s k acc = sel a x (s + k) ++ acc := by
  have h : Nat.land (Nat.shiftRight (Nat.shiftRight x s) k) 1 = (x.testBit (s + k)).toNat := by
    show (x >>> s >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.toNat_testBit, ← Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
  unfold bitc sel
  rw [h]
  cases x.testBit (s + k) <;> rfl

theorem filter_range_succ_sel (a x n : ℕ) :
    ((List.range (n + 1)).filter (fun i => x.testBit i)).map (fun i => a + i) =
      ((List.range n).filter (fun i => x.testBit i)).map (fun i => a + i) ++ sel a x n := by
  simp only [List.range_succ, List.filter_append, List.map_append, sel]
  cases h : x.testBit n <;> simp [h]

theorem ext8_eq (a x : ℕ) (j : ℕ) (acc : List ℕ) :
    ext8 a x j acc =
      ((List.range (8 * j)).filter (fun i => x.testBit i)).map (fun i => a + i) ++ acc := by
  induction j generalizing acc with
  | zero => simp [ext8]
  | succ j ih =>
    simp only [ext8, bitc_eq]
    rw [ih]
    have : 8 * (j + 1) = 8 * j + 7 + 1 := by ring
    rw [this, filter_range_succ_sel, filter_range_succ_sel, filter_range_succ_sel,
      filter_range_succ_sel, filter_range_succ_sel, filter_range_succ_sel, filter_range_succ_sel,
      filter_range_succ_sel]
    simp only [List.append_assoc, Nat.add_zero]

theorem filter_lt_range (q : ℕ → Bool) (len n : ℕ) (h : len ≤ n) :
    (List.range n).filter (fun i => decide (i < len) && q i) = (List.range len).filter q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero =>
    apply List.filter_congr
    intro i hi
    have := List.mem_range.mp hi
    simp only [Nat.add_zero] at this
    simp [this]
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.filter_append, ih (by omega)]
    simp

theorem block_eq (B a len : ℕ) (base : List ℕ) (hps : ∀ p ∈ base, 0 < p) (hlen : len ≤ 8 * B)
    (H : ∀ i, i < len → ((a + i).Prime ↔ ∀ p ∈ base, ¬ p ∣ a + i)) (acc : List ℕ) :
    ext8 a (primeMask (8 * B) a len base) B acc =
      (List.range' a len).filter (fun m => decide m.Prime) ++ acc := by
  rw [ext8_eq]
  simp only [primeMask_testBit (8 * B) a len base hps hlen H]
  rw [filter_lt_range (fun i => decide (a + i).Prime) len (8 * B) hlen, List.range'_eq_map_range,
    List.filter_map]
  rfl

theorem min_step1 (j W T : ℕ) (hj : j * W ≤ T) :
    j * W + min W (T - j * W) = min ((j + 1) * W) T := by
  have : (j + 1) * W = j * W + W := Nat.succ_mul j W
  rw [this]
  generalize j * W = e at *
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem min_step2 (j W T : ℕ) (hj : ¬ j * W ≤ T) :
    min (j * W) T = min ((j + 1) * W) T := by
  have : (j + 1) * W = j * W + W := Nat.succ_mul j W
  rw [this]
  generalize j * W = e at *
  simp only [Nat.min_def]
  split_ifs <;> omega

theorem seg_eq (B S T : ℕ) (base : List ℕ) (hps : ∀ p ∈ base, 0 < p)
    (H : ∀ m, S ≤ m → m < S + T → (m.Prime ↔ ∀ p ∈ base, ¬ p ∣ m)) (j : ℕ) (acc : List ℕ) :
    seg B S T base j acc =
      (List.range' S (min (j * (8 * B)) T)).filter (fun m => decide m.Prime) ++ acc := by
  induction j generalizing acc with
  | zero => simp [seg]
  | succ j ih =>
    simp only [seg]
    rw [block_eq B _ _ base hps (Nat.min_le_left _ _)
      (fun i hi => H _ (by omega) (by have := Nat.min_le_right (8 * B) (T - j * (8 * B)); omega)),
      ih, ← List.append_assoc, ← List.filter_append]
    congr 2
    by_cases hj : j * (8 * B) ≤ T
    · rw [Nat.min_eq_left hj, List.range'_append_1]
      congr 1
      exact min_step1 _ _ _ hj
    · have h0 : T - j * (8 * B) = 0 := by omega
      rw [h0, Nat.min_zero, List.range'_zero, List.append_nil]
      congr 1
      exact min_step2 _ _ _ hj

theorem sieve_crit {R N m : ℕ} (hN : N < R * R) (h1 : R < m) (h2 : m ≤ N) :
    m.Prime ↔ ∀ p ∈ (List.range (R + 1)).filter (fun m => decide m.Prime), ¬ p ∣ m := by
  constructor
  · intro hm p hp hd
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
    have := (Nat.prime_dvd_prime_iff_eq hp.2 hm).1 hd
    omega
  · intro h
    by_contra hm
    have hR : 0 < R := by
      rcases Nat.eq_zero_or_pos R with h0 | h0
      · subst h0; omega
      · exact h0
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hm
    have hp := Nat.minFac_prime (by omega : m ≠ 1)
    refine h m.minFac ?_ (Nat.minFac_dvd m)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    refine ⟨?_, hp⟩
    by_contra hlt
    have : R + 1 ≤ m.minFac := by omega
    nlinarith

theorem primeListAux_eq (B : ℕ) (hB : 0 < B) (f N : ℕ) :
    primeListAux B f N = (List.range (N + 1)).filter (fun m => decide m.Prime) := by
  induction f generalizing N with
  | zero => rfl
  | succ f ih =>
    rw [primeListAux]
    split
    · rename_i h5
      have h5' : N < 5 := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h5
        exact absurd h5 (by simp)
      interval_cases N <;> simp [List.range_succ] <;> norm_num
    · split
      · rename_i hc
        rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
        obtain ⟨hRN, hNR⟩ := hc
        generalize 2 ^ (N.log2 / 2 + 1) = R at *
        rw [ih R]
        have hps : ∀ p ∈ (List.range (R + 1)).filter (fun m => decide m.Prime), 0 < p := by
          intro p hp
          simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
          exact hp.2.pos
        rw [seg_eq B (R + 1) (N - R) _ hps (fun m hm1 hm2 => sieve_crit hNR (by omega) (by omega)),
          List.append_nil]
        have hmin : min (((N - R) / (8 * B) + 1) * (8 * B)) (N - R) = N - R := by
          apply Nat.min_eq_right
          have h1 := Nat.div_add_mod' (N - R) (8 * B)
          have h2 := Nat.mod_lt (N - R) (by omega : 0 < 8 * B)
          rw [Nat.succ_mul]
          omega
        rw [hmin, ← List.filter_append, List.range_eq_range', List.range_eq_range']
        congr 1
        have : N + 1 = (R + 1) + (N - R) := by omega
        rw [this, ← List.range'_append_1 (s := 0) (m := R + 1) (n := N - R), Nat.zero_add]
      · rfl

theorem primeList_eq (N : ℕ) :
    primeList N = (List.range (N + 1)).filter (fun m => decide m.Prime) :=
  primeListAux_eq 256 (by norm_num) 64 N

end OMA.SieveA

namespace OMA.SieveA

def compMaskO (B a : ℕ) (ps : List ℕ) : ℕ → ℕ :=
  List.rec (fun acc => acc)
    (fun p _ ih acc => ih (Nat.lor acc
      (Nat.shiftRight (patt p (Nat.add (Nat.div B p) 2)) (Nat.mod (Nat.mul a (Nat.div (Nat.succ p) 2)) p)))) ps

def primeMaskO (B a len : ℕ) (base : List ℕ) : ℕ :=
  (2 ^ len - 1) ^^^ (compMaskO B a base 0 % 2 ^ len)

def tab : ℕ := 576884569514903465112829035301070915212904217550250840307890304938966762846968390645079406037421241394514718367336778540415953671424719498785423356702537831632048361433026949881132951321636979088994776949783222921551720844321132760178968102750447716929500522059593428560064490948761722368808686189937370651485783008477613548333955043466382860610978341327673386733800573639848370280513714790508630231181610708702188131825272624299913833064299060810112706002160486093080486882377551909888441690719607456641316183416781596493632739919349786555544173843631693541157733625792382215274764846963236230556052153568565119675946054256906966002916390913681104195778092186885057685211570984551085041398862001670820914889979282043044869930593067795202199696660417164254011048678460156991282168138432880292860541293096288482174781748966351002132666552047306959383480612739752644197348656662519780775532346014798461498570464509507007554926165734695588602533039604560052339060061515716009840025164725426774846282667526862575021858037850961486450675631083727483327490647953305310329554059222134872551941720742044333726182437012578177800169558121088220507429693041394418590863061386731715116821181271544491412783603705321757907964365772266542375898836414454847620241788480668307727313862253757027262288748412127395613024743053621626365394109499793228984249421290799549337851233466075123324131804532445439978471616846276011246298638237135972648599098743054517409430028416351468626591512828050762302979394315132813429432791860602530925820779265634493135552298935132713222034797478883818122578279656383316972577233530702070728447865201750931081038028079238918304703830170089564491931561960733179187520140599394625609380644383131842156106861668379947576529172264103782012709737803414760869738050972970899841470213524674391244394970523596571983120923543457945104276817673408975414001723913414397444052468416598985360252973009470858012634960494577229563255737692237428920496101718966066611031181999808114694428488045174506280128311395277009173588817873745677524233749396020838123508448248569091989938923322485214459893798321389982382561745492555112987215163539821722428958186394064698336106404078207185973314241081081694712418902243706751627808482137858497115408499418951072208693031145653690968525323458156288567258901702630846061222987500748499194546032919943824605714699776647352468207207519771338851584473822312779545116247581032644210590264730861212488436731043004197323286174947606528

def offs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, c => match Nat.land c 15 with
    | 0 => []
    | d + 1 => d :: offs fuel (Nat.shiftRight c 4)

def decF (fuel : ℕ) : (ℕ → ℕ → ℕ) → ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ :=
  Nat.rec (fun _ _ K _ s => K s)
    (fun _ ih f ai K c s => Nat.rec (K s)
      (fun d _ => Nat.rec (ih f ai K (Nat.shiftRight c 4) 0)
        (fun m _ => ih f ai K (Nat.shiftRight c 4) (Nat.succ m))
        (f s (Nat.add ai (Nat.mul 2 d))))
      (Nat.land c 15)) fuel

def extF (f : ℕ → ℕ → ℕ) (a x n : ℕ) : (ℕ → ℕ) → ℕ → ℕ :=
  Nat.rec (fun K s => K s)
    (fun j ih K s => ih (decF 8 f (Nat.add a (Nat.mul 16 j)) K
      (Nat.land (Nat.shiftRight tab (Nat.mul 32 (Nat.land (Nat.shiftRight x (Nat.mul 8 j)) 255)))
        4294967295)) s) n

def segF (B S T : ℕ) (base : List ℕ) (f : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, s => s
  | k + 1, j, s =>
    match extF f (S + 2 * (j * (8 * B)))
        (primeMaskO (8 * B) (S + 2 * (j * (8 * B))) (min (8 * B) (T - j * (8 * B))) base)
        B (fun r => r) s with
    | 0 => segF B S T base f k (j + 1) 0
    | m + 1 => segF B S T base f k (j + 1) (m + 1)

def foldPrimesAux (R N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : ℕ :=
  match Nat.ble 2 R && Nat.beq (R % 2) 0 && (Nat.ble R N && Nat.blt N (R * R)) with
  | true => segF 256 (R + 1) ((N - R + 1) / 2) (List.filter (fun p => !(Nat.beq p 2)) (primeList R)) f
      ((N - R + 1) / 2 / (8 * 256) + 1) 0 (List.foldl f s (primeList R))
  | false => List.foldl f s (primeList N)

def foldPrimes (N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : ℕ :=
  foldPrimesAux (2 ^ (N.log2 / 2 + 1)) N f s

def primeCount (N : ℕ) : ℕ := foldPrimes N (fun s _ => Nat.succ s) 0

theorem compMaskO_nil (B a acc : ℕ) : compMaskO B a [] acc = acc := rfl

theorem compMaskO_cons (B a p : ℕ) (ps : List ℕ) (acc : ℕ) :
    compMaskO B a (p :: ps) acc =
      compMaskO B a ps (acc ||| (patt p (B / p + 2) >>> ((a * ((p + 1) / 2)) % p))) := rfl

theorem odd_shift {p : ℕ} (hp : p % 2 = 1) (a i : ℕ) :
    p ∣ (a * ((p + 1) / 2)) % p + i ↔ p ∣ a + 2 * i := by
  have h2 : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hc : Nat.Coprime p 2 := by
    rw [Nat.coprime_comm]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have e1 : p ∣ (a * ((p + 1) / 2)) % p + i ↔ p ∣ a * ((p + 1) / 2) + i := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.mod_add_mod]
  have e2 : p ∣ a * ((p + 1) / 2) + i ↔ p ∣ (a * ((p + 1) / 2) + i) * 2 :=
    ⟨fun h => Dvd.dvd.mul_right h 2, fun h => hc.dvd_of_dvd_mul_right h⟩
  have e3 : (a * ((p + 1) / 2) + i) * 2 = p * a + (a + 2 * i) := by
    calc (a * ((p + 1) / 2) + i) * 2 = a * (2 * ((p + 1) / 2)) + 2 * i := by ring
      _ = p * a + (a + 2 * i) := by rw [h2]; ring
  rw [e1, e2, e3]
  exact (Nat.dvd_add_right (Dvd.intro a rfl))

theorem compMaskO_testBit (B a : ℕ) (ps : List ℕ) (hps : ∀ p ∈ ps, p % 2 = 1) (acc i : ℕ)
    (hi : i < B) :
    (compMaskO B a ps acc).testBit i =
      (acc.testBit i || ps.any (fun p => decide (p ∣ a + 2 * i))) := by
  induction ps generalizing acc with
  | nil => simp [compMaskO_nil]
  | cons p ps ih =>
    have hp2 : p % 2 = 1 := hps p (by simp)
    have hp : 0 < p := by omega
    rw [compMaskO_cons, ih (fun q hq => hps q (by simp [hq])), Nat.testBit_lor,
      Nat.testBit_shiftRight, patt_eq hp, geo_testBit hp, List.any_cons, Bool.or_assoc]
    congr 2
    have h1 := Nat.div_add_mod B p
    have h2 := Nat.mod_lt B hp
    have h3 := Nat.mod_lt (a * ((p + 1) / 2)) hp
    have hb : (a * ((p + 1) / 2)) % p + i < p * (B / p + 2) := by rw [Nat.mul_add]; omega
    simp [hb, odd_shift hp2]

theorem primeMaskO_testBit (B a len : ℕ) (base : List ℕ) (hps : ∀ p ∈ base, p % 2 = 1)
    (hlen : len ≤ B)
    (H : ∀ i, i < len → ((a + 2 * i).Prime ↔ ∀ p ∈ base, ¬ p ∣ a + 2 * i)) (i : ℕ) :
    (primeMaskO B a len base).testBit i = (decide (i < len) && decide (a + 2 * i).Prime) := by
  unfold primeMaskO
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < len
  · rw [compMaskO_testBit B a base hps 0 i (by omega)]
    simp only [hi, H i hi]
    rw [Bool.eq_iff_iff]
    simp
  · simp [hi]

theorem force_eq (k : ℕ → ℕ) (v : ℕ) :
    (Nat.rec (k 0) (fun m _ => k (Nat.succ m)) v : ℕ) = k v := by
  cases v <;> rfl

theorem decF_zero (f : ℕ → ℕ → ℕ) (ai : ℕ) (K : ℕ → ℕ) (c s : ℕ) : decF 0 f ai K c s = K s := rfl

theorem decF_succ (n : ℕ) (f : ℕ → ℕ → ℕ) (ai : ℕ) (K : ℕ → ℕ) (c s : ℕ) :
    decF (n + 1) f ai K c s =
      (Nat.rec (K s) (fun d _ => (Nat.rec (decF n f ai K (Nat.shiftRight c 4) 0)
        (fun m _ => decF n f ai K (Nat.shiftRight c 4) (Nat.succ m))
        (f s (ai + 2 * d)) : ℕ)) (Nat.land c 15) : ℕ) := rfl

theorem decF_eq (fuel : ℕ) (f : ℕ → ℕ → ℕ) (ai : ℕ) (K : ℕ → ℕ) (c s : ℕ) :
    decF fuel f ai K c s = K (((offs fuel c).map (fun d => ai + 2 * d)).foldl f s) := by
  induction fuel generalizing c s with
  | zero => simp [decF_zero, offs]
  | succ n ih =>
    rw [decF_succ, offs]
    cases hd : Nat.land c 15 with
    | zero => simp
    | succ d =>
      simp only []
      rw [force_eq (fun v => decF n f ai K (Nat.shiftRight c 4) v), ih]
      simp

theorem tab_ok : ∀ b < 256,
    offs 8 (Nat.land (Nat.shiftRight tab (Nat.mul 32 b)) 4294967295) =
      (List.range 8).filter (fun k => b.testBit k) := by
  decide +kernel

theorem extF_zero (f : ℕ → ℕ → ℕ) (a x : ℕ) (K : ℕ → ℕ) (s : ℕ) : extF f a x 0 K s = K s := rfl

theorem extF_succ (f : ℕ → ℕ → ℕ) (a x j : ℕ) (K : ℕ → ℕ) (s : ℕ) :
    extF f a x (j + 1) K s = extF f a x j (decF 8 f (a + 16 * j) K
      (Nat.land (Nat.shiftRight tab (Nat.mul 32 (Nat.land (Nat.shiftRight x (8 * j)) 255)))
        4294967295)) s := rfl

theorem byte_filter (x j : ℕ) :
    (List.range 8).filter (fun k => (Nat.land (Nat.shiftRight x (8 * j)) 255).testBit k) =
      (List.range 8).filter (fun k => x.testBit (8 * j + k)) := by
  apply List.filter_congr
  intro k hk
  have hk' := List.mem_range.mp hk
  have : Nat.land (Nat.shiftRight x (8 * j)) 255 = (x >>> (8 * j)) % 2 ^ 8 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  rw [this, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hk']

theorem extF_eq (f : ℕ → ℕ → ℕ) (a x n : ℕ) (K : ℕ → ℕ) (s : ℕ) :
    extF f a x n K s =
      K ((((List.range (8 * n)).filter (fun i => x.testBit i)).map (fun i => a + 2 * i)).foldl f s) := by
  induction n generalizing K s with
  | zero => simp [extF_zero]
  | succ j ih =>
    have hb : Nat.land (Nat.shiftRight x (8 * j)) 255 < 256 := by
      have : Nat.land (Nat.shiftRight x (8 * j)) 255 = (x >>> (8 * j)) % 2 ^ 8 :=
        Nat.and_two_pow_sub_one_eq_mod _ 8
      rw [this]; exact Nat.mod_lt _ (by norm_num)
    rw [extF_succ, ih, decF_eq, tab_ok _ hb, byte_filter, ← List.foldl_append]
    congr 2
    have : 8 * (j + 1) = 8 * j + 8 := by ring
    rw [this, List.range_add, List.filter_append, List.map_append, List.filter_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro d _
    simp only [Function.comp]
    ring

theorem blockF_eq (f : ℕ → ℕ → ℕ) (B a len : ℕ) (base : List ℕ) (hps : ∀ p ∈ base, p % 2 = 1)
    (hlen : len ≤ 8 * B)
    (H : ∀ i, i < len → ((a + 2 * i).Prime ↔ ∀ p ∈ base, ¬ p ∣ a + 2 * i)) (K : ℕ → ℕ) (s : ℕ) :
    extF f a (primeMaskO (8 * B) a len base) B K s =
      K ((((List.range len).filter (fun i => decide (a + 2 * i).Prime)).map
        (fun i => a + 2 * i)).foldl f s) := by
  rw [extF_eq]
  simp only [primeMaskO_testBit (8 * B) a len base hps hlen H]
  rw [filter_lt_range (fun i => decide (a + 2 * i).Prime) len (8 * B) hlen]

theorem reindex (S m len : ℕ) :
    ((List.range len).filter (fun i => decide (S + 2 * m + 2 * i).Prime)).map
        (fun i => S + 2 * m + 2 * i) =
      ((List.range' m len).filter (fun i => decide (S + 2 * i).Prime)).map (fun i => S + 2 * i) := by
  rw [List.range'_eq_map_range, List.filter_map, List.map_map]
  have h : ∀ i, S + 2 * (m + i) = S + 2 * m + 2 * i := fun i => by ring
  simp only [Function.comp_def, h]

theorem range'_step (j k W T : ℕ) :
    List.range' (j * W) (min W (T - j * W)) ++
        List.range' ((j + 1) * W) (min (k * W) (T - (j + 1) * W)) =
      List.range' (j * W) (min ((k + 1) * W) (T - j * W)) := by
  have h1 : (j + 1) * W = j * W + W := Nat.succ_mul j W
  have h2 : (k + 1) * W = k * W + W := Nat.succ_mul k W
  rw [h1, h2]
  generalize j * W = e
  generalize k * W = g
  by_cases h : W ≤ T - e
  · rw [Nat.min_eq_left h, List.range'_append_1]
    congr 1
    simp only [Nat.min_def]
    split_ifs <;> omega
  · have h0 : T - (e + W) = 0 := by omega
    rw [h0, Nat.min_zero, List.range'_zero, List.append_nil]
    congr 1
    simp only [Nat.min_def]
    split_ifs <;> omega

theorem segF_succ (B S T : ℕ) (base : List ℕ) (f : ℕ → ℕ → ℕ) (k j s : ℕ) :
    segF B S T base f (k + 1) j s = segF B S T base f k (j + 1)
      (extF f (S + 2 * (j * (8 * B)))
        (primeMaskO (8 * B) (S + 2 * (j * (8 * B))) (min (8 * B) (T - j * (8 * B))) base)
        B (fun r => r) s) := by
  rw [segF]
  split <;> rename_i h <;> rw [h]

theorem segF_add (B S T : ℕ) (base : List ℕ) (f : ℕ → ℕ → ℕ) (k1 k2 j s : ℕ) :
    segF B S T base f (k1 + k2) j s =
      segF B S T base f k2 (j + k1) (segF B S T base f k1 j s) := by
  induction k1 generalizing j s with
  | zero => simp [segF]
  | succ k1 ih =>
    rw [show k1 + 1 + k2 = (k1 + k2) + 1 by omega, segF_succ, ih, segF_succ,
      show j + 1 + k1 = j + (k1 + 1) by omega]

theorem segF_eq (B S T : ℕ) (base : List ℕ) (f : ℕ → ℕ → ℕ) (hps : ∀ p ∈ base, p % 2 = 1)
    (H : ∀ i, i < T → ((S + 2 * i).Prime ↔ ∀ p ∈ base, ¬ p ∣ S + 2 * i)) (k j s : ℕ) :
    segF B S T base f k j s =
      (((List.range' (j * (8 * B)) (min (k * (8 * B)) (T - j * (8 * B)))).filter
        (fun i => decide (S + 2 * i).Prime)).map (fun i => S + 2 * i)).foldl f s := by
  induction k generalizing j s with
  | zero => simp [segF]
  | succ k ih =>
    have hb := blockF_eq f B (S + 2 * (j * (8 * B))) (min (8 * B) (T - j * (8 * B))) base hps
      (Nat.min_le_left _ _)
      (fun i hi => by
        have h := H (j * (8 * B) + i)
          (by have := Nat.min_le_right (8 * B) (T - j * (8 * B)); omega)
        have e : S + 2 * (j * (8 * B) + i) = S + 2 * (j * (8 * B)) + 2 * i := by ring
        rw [e] at h; exact h) (fun r => r) s
    rw [reindex] at hb
    rw [segF_succ, hb, ih, ← List.foldl_append, ← List.map_append, ← List.filter_append, range'_step]

theorem odd_filter (n : ℕ) : ∀ S : ℕ, S % 2 = 1 → 3 ≤ S →
    (List.range' S n).filter (fun m => decide m.Prime) =
      ((List.range ((n + 1) / 2)).filter (fun i => decide (S + 2 * i).Prime)).map
        (fun i => S + 2 * i) := by
  induction n using Nat.twoStepInduction with
  | zero => intro S _ _; simp
  | one => intro S _ _; by_cases hS : S.Prime <;> simp [List.range_succ, hS]
  | more n ih _ =>
    intro S hS h3
    have hnp : ¬ (S + 1).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h <;> omega
    have e : (n + 2 + 1) / 2 = (n + 1) / 2 + 1 := by omega
    have ih' := ih (S + 1 + 1) (by omega) (by omega)
    have h : ∀ i, S + 1 + 1 + 2 * i = S + 2 * (i + 1) := fun i => by ring
    simp only [h] at ih'
    rw [e, List.range_succ_eq_map, List.range'_succ, List.range'_succ]
    by_cases hS : S.Prime <;>
      simp [List.filter_cons, hS, hnp, ih', List.filter_map, Function.comp_def]

theorem foldPrimesAux_eq (R N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) :
    foldPrimesAux R N f s =
      List.foldl f s ((List.range (N + 1)).filter (fun m => decide m.Prime)) := by
  unfold foldPrimesAux
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    obtain ⟨⟨hR2, hRe0⟩, hRN, hNR⟩ := hc
    have hRe : R % 2 = 0 := Nat.eq_of_beq_eq_true hRe0
    rw [primeList_eq]
    have hps : ∀ p ∈ List.filter (fun p => !(Nat.beq p 2))
        ((List.range (R + 1)).filter (fun m => decide m.Prime)), p % 2 = 1 := by
      intro p hp
      have hp' := List.mem_filter.mp hp
      have hpr : p.Prime := by simpa using (List.mem_filter.mp hp'.1).2
      rcases hpr.eq_two_or_odd with h | h
      · subst h; exact absurd hp'.2 (by decide)
      · exact h
    have H : ∀ i, i < (N - R + 1) / 2 → ((R + 1 + 2 * i).Prime ↔
        ∀ p ∈ List.filter (fun p => !(Nat.beq p 2))
          ((List.range (R + 1)).filter (fun m => decide m.Prime)), ¬ p ∣ R + 1 + 2 * i) := by
      intro i hi
      rw [sieve_crit hNR (by omega : R < R + 1 + 2 * i) (by omega)]
      constructor
      · intro h p hp
        exact h p (List.mem_of_mem_filter hp)
      · intro h p hp
        by_cases h2 : p = 2
        · subst h2; omega
        · refine h p (List.mem_filter.mpr ⟨hp, ?_⟩)
          rw [Bool.not_eq_true', ← Bool.not_eq_true]
          exact fun hb => h2 (Nat.eq_of_beq_eq_true hb)
    rw [segF_eq 256 (R + 1) ((N - R + 1) / 2) _ f hps H, ← List.foldl_append]
    congr 1
    simp only [Nat.zero_mul, Nat.sub_zero]
    have hmin : min (((N - R + 1) / 2 / (8 * 256) + 1) * (8 * 256)) ((N - R + 1) / 2)
        = (N - R + 1) / 2 := by
      omega
    rw [hmin, ← List.range_eq_range', ← odd_filter (N - R) (R + 1) (by omega) (by omega),
      ← List.filter_append, List.range_eq_range', List.range_eq_range']
    congr 1
    have : N + 1 = (R + 1) + (N - R) := by omega
    rw [this, ← List.range'_append_1 (s := 0) (m := R + 1) (n := N - R), Nat.zero_add]
  · rw [primeList_eq]

theorem foldPrimes_eq (N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) :
    foldPrimes N f s = List.foldl f s ((List.range (N + 1)).filter (fun m => decide m.Prime)) :=
  foldPrimesAux_eq _ N f s

theorem foldl_succ_eq (l : List ℕ) (s : ℕ) : List.foldl (fun s _ => Nat.succ s) s l = s + l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, List.length_cons]; omega

theorem primeCount_eq (N : ℕ) :
    primeCount N = ((List.range (N + 1)).filter (fun m => decide m.Prime)).length := by
  rw [primeCount, foldPrimes_eq, foldl_succ_eq, Nat.zero_add]

theorem primeCount_eq_length (N : ℕ) : primeCount N = (primeList N).length := by
  rw [primeCount_eq, primeList_eq]

/- ## Chunked API: check the range in several declarations -/

def sieveR (N : ℕ) : ℕ := 2 ^ (N.log2 / 2 + 1)

def sieveOK (N : ℕ) : Bool :=
  Nat.ble 2 (sieveR N) && Nat.beq (sieveR N % 2) 0 &&
    (Nat.ble (sieveR N) N && Nat.blt N (sieveR N * sieveR N))

def numBlocks (N : ℕ) : ℕ := (N - sieveR N + 1) / 2 / (8 * 256) + 1

def foldInit (N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : ℕ := List.foldl f s (primeList (sieveR N))

def foldBlocks (N : ℕ) (f : ℕ → ℕ → ℕ) (k j s : ℕ) : ℕ :=
  segF 256 (sieveR N + 1) ((N - sieveR N + 1) / 2)
    (List.filter (fun p => !(Nat.beq p 2)) (primeList (sieveR N))) f k j s

theorem foldPrimes_eq_blocks (N : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) (h : sieveOK N = true) :
    foldPrimes N f s = foldBlocks N f (numBlocks N) 0 (foldInit N f s) := by
  unfold sieveOK sieveR at h
  unfold foldPrimes foldPrimesAux
  rw [h]
  rfl

theorem foldBlocks_add (N : ℕ) (f : ℕ → ℕ → ℕ) (k1 k2 j s : ℕ) :
    foldBlocks N f (k1 + k2) j s = foldBlocks N f k2 (j + k1) (foldBlocks N f k1 j s) :=
  segF_add _ _ _ _ _ _ _ _ _

/- ## Packed tug-of-war step for OEIS A92243 -/

def tugZ : List ℕ → ℤ
  | a :: b :: c :: l => (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign + tugZ (b :: c :: l)
  | _ => 0

def tugAux (hi p g' g : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul (Nat.add (Nat.add hi 4294967296)
    (Nat.sub (Nat.add 1 (Nat.sub 1 (Nat.sub 1 (Nat.sub g' g)))) (Nat.sub 1 (Nat.sub 1 (Nat.sub g g')))))
    18446744073709551616) (Nat.mul g' 4294967296)) p

def tugStep (s p : ℕ) : ℕ :=
  tugAux (Nat.div s 18446744073709551616) p (Nat.sub p (Nat.mod s 4294967296))
    (Nat.mod (Nat.div s 4294967296) 4294967296)

def pack (b g bal cnt : ℕ) : ℕ :=
  b + 4294967296 * g + 18446744073709551616 * (bal + 4294967296 * cnt)

def tugInc (g g' : ℕ) : ℕ := 1 + (1 - (1 - (g' - g))) - (1 - (1 - (g - g')))

theorem tugStep_pack (b g bal cnt p : ℕ) (hb : b < 4294967296) (hg : g < 4294967296) :
    tugStep (pack b g bal cnt) p = pack p (p - b) (bal + tugInc g (p - b)) (cnt + 1) := by
  show ((pack b g bal cnt) / 18446744073709551616 + 4294967296 +
      (1 + (1 - (1 - (p - (pack b g bal cnt) % 4294967296 -
          (pack b g bal cnt) / 4294967296 % 4294967296))) -
        (1 - (1 - ((pack b g bal cnt) / 4294967296 % 4294967296 -
          (p - (pack b g bal cnt) % 4294967296)))))) * 18446744073709551616 +
      (p - (pack b g bal cnt) % 4294967296) * 4294967296 + p = _
  have h1 : (pack b g bal cnt) % 4294967296 = b := by unfold pack; omega
  have h2 : (pack b g bal cnt) / 4294967296 % 4294967296 = g := by unfold pack; omega
  have h3 : (pack b g bal cnt) / 18446744073709551616 = bal + 4294967296 * cnt := by
    unfold pack; omega
  rw [h1, h2, h3]
  unfold pack tugInc
  omega

theorem tugInc_cast (a b c : ℕ) :
    ((tugInc (b - a) (c - b) : ℕ) : ℤ) = 1 + (((c - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ)).sign := by
  rcases lt_trichotomy (b - a) (c - b) with h | h | h
  · rw [Int.sign_eq_one_of_pos (by omega)]; unfold tugInc; omega
  · rw [h, sub_self, Int.sign_zero]; unfold tugInc; omega
  · rw [Int.sign_eq_neg_one_of_neg (by omega)]; unfold tugInc; omega

theorem tugInc_le (g g' : ℕ) : tugInc g g' ≤ 2 := by unfold tugInc; omega

theorem tug_fold_aux (L : List ℕ) : ∀ (a b bal cnt : ℕ), b < 4294967296 → b - a < 4294967296 →
    (∀ p ∈ L, p < 4294967296) →
    ∃ b' g' bal', List.foldl tugStep (pack b (b - a) bal cnt) L = pack b' g' bal' (cnt + L.length) ∧
      b' < 4294967296 ∧ g' < 4294967296 ∧ bal' ≤ bal + 2 * L.length ∧
      (bal' : ℤ) = bal + L.length + tugZ (a :: b :: L) := by
  induction L with
  | nil =>
    intro a b bal cnt hb hg _
    exact ⟨b, b - a, bal, rfl, hb, hg, by simp, by simp [tugZ]⟩
  | cons c l ih =>
    intro a b bal cnt hb hg hL
    have hc : c < 4294967296 := hL c (by simp)
    rw [List.foldl_cons, tugStep_pack b (b - a) bal cnt c hb hg]
    obtain ⟨b', g', bal', h1, h2, h3, h4, h5⟩ := ih b c (bal + tugInc (b - a) (c - b)) (cnt + 1) hc
      (by omega) (fun p hp => hL p (by simp [hp]))
    refine ⟨b', g', bal', ?_, h2, h3, ?_, ?_⟩
    · rw [h1, List.length_cons]; congr 1; omega
    · have := tugInc_le (b - a) (c - b); rw [List.length_cons]; omega
    · have := tugInc_cast a b c
      rw [h5, tugZ, List.length_cons]
      push_cast
      omega

/-- Folding `tugStep` from `0` over a list of numbers below `2^32` yields a packed state whose
count field is the length and whose balance field is `length + tugZ (0 :: 0 :: L)`. -/
theorem tug_fold (L : List ℕ) (hL : ∀ p ∈ L, p < 4294967296) (hlen : 2 * L.length < 4294967296) :
    (L.foldl tugStep 0) / 79228162514264337593543950336 = L.length ∧
      (((L.foldl tugStep 0) / 18446744073709551616 % 4294967296 : ℕ) : ℤ) =
        L.length + tugZ (0 :: 0 :: L) := by
  obtain ⟨b', g', bal', h1, h2, h3, h4, h5⟩ := tug_fold_aux L 0 0 0 0 (by norm_num) (by norm_num) hL
  have h0 : pack 0 (0 - 0) 0 0 = 0 := rfl
  rw [h0] at h1
  rw [h1]
  have e1 : pack b' g' bal' (0 + L.length) / 79228162514264337593543950336 = L.length := by
    unfold pack; omega
  have e2 : pack b' g' bal' (0 + L.length) / 18446744073709551616 % 4294967296 = bal' := by
    unfold pack; omega
  rw [e1, e2, h5]
  simp

/-- Specialisation to the primes up to `N` (computed by `foldPrimes`). -/
theorem tug_primes (N : ℕ) (hN : N < 2147483647) :
    (foldPrimes N tugStep 0) / 79228162514264337593543950336 =
        ((List.range (N + 1)).filter (fun m => decide m.Prime)).length ∧
      (((foldPrimes N tugStep 0) / 18446744073709551616 % 4294967296 : ℕ) : ℤ) =
        ((List.range (N + 1)).filter (fun m => decide m.Prime)).length +
          tugZ (0 :: 0 :: (List.range (N + 1)).filter (fun m => decide m.Prime)) := by
  rw [foldPrimes_eq]
  apply tug_fold
  · intro p hp
    have := List.mem_range.mp (List.mem_of_mem_filter hp)
    omega
  · have := List.length_filter_le (fun m => decide m.Prime) (List.range (N + 1))
    rw [List.length_range] at this
    omega

theorem tugZ_zero_zero (l : List ℕ) : tugZ (0 :: 0 :: 2 :: 3 :: l) = tugZ (2 :: 3 :: l) := by
  have h : (2 : ℤ).sign = 1 := rfl
  simp [tugZ, h]

end OMA.SieveA

namespace OMA.SieveA
theorem c0 : foldInit 3666581 tugStep 0 = 24481502222810638420035086845943 := by decide +kernel
theorem c1 : foldBlocks 3666581 tugStep 300 0 24481502222810638420035086845943 = 7535073625838104615126303945967597 := by decide +kernel
theorem c2 : foldBlocks 3666581 tugStep 300 300 7535073625838104615126303945967597 = 14288165287471414878424783208679399 := by decide +kernel
theorem c3 : foldBlocks 3666581 tugStep 295 600 14288165287471414878424783208679399 = 20690513873580050135229173390111381 := by decide +kernel
theorem cOK : sieveOK 3666581 = true := by decide +kernel
theorem cNB : numBlocks 3666581 = 895 := by decide +kernel
theorem tugTotal : foldPrimes 3666581 tugStep 0 = 20690513873580050135229173390111381 := by
  rw [foldPrimes_eq_blocks _ _ _ cOK, cNB, c0, show 895 = 300 + (300 + 295) from rfl, foldBlocks_add,
    foldBlocks_add, c1, c2, c3]

end OMA.SieveA

namespace OMA.A92243

/-- Slow stand-in for a sieve. -/
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

theorem tugZ_zero_zero (N n : ℕ) (hn : 1 ≤ n)
    (hlen : ((List.range (N + 1)).filter (fun m => decide m.Prime)).length = n + 1) :
    tugZ (0 :: 0 :: (List.range (N + 1)).filter (fun m => decide m.Prime)) =
      tugZ ((List.range (N + 1)).filter (fun m => decide m.Prime)) := by
  have hc : Nat.count Nat.Prime (N + 1) = n + 1 := by
    rw [← primeListSpec_length]; exact hlen
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : (List.range (m + 2)).map (Nat.nth Nat.Prime) =
      2 :: 3 :: (List.range m).map (fun i => Nat.nth Nat.Prime (i + 2)) := by
    rw [List.range_eq_range', List.range_eq_range']
    simp [List.range'_succ, List.range'_eq_map_range, Nat.add_comm,
      Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  have hL := primeListSpec_eq_map N
  rw [primeListSpec, hc, h2] at hL
  rw [hL]
  simp only [tugZ]
  have e1 : (((2 - 0 : ℕ) : ℤ) - ((0 - 0 : ℕ) : ℤ)).sign = 1 := by decide
  have e2 : (((3 - 2 : ℕ) : ℤ) - ((2 - 0 : ℕ) : ℤ)).sign = -1 := by decide
  rw [e1, e2]; omega

/-- Interface for a fold-style sieve: it suffices to know the number of primes `≤ N` and the
sign of the score of the prime list with two zeros prepended. -/
theorem a_pos_of_tugZ (n N : ℕ) (hn : 2 ≤ n)
    (hlen : ((List.range (N + 1)).filter (fun m => decide m.Prime)).length = n + 1)
    (hpos : 0 < tugZ (0 :: 0 :: (List.range (N + 1)).filter (fun m => decide m.Prime))) :
    0 < OeisA92243.a n := by
  have hc : Nat.count Nat.Prime (N + 1) = n + 1 := by
    rw [← primeListSpec_length]; exact hlen
  rw [tugZ_zero_zero N n (by omega) hlen] at hpos
  rw [a_eq_tugZ n hn, ← hc, ← primeListSpec_eq_map]
  exact hpos

end OMA.A92243

namespace OMA.A92243

theorem tugZ_eq (L : List ℕ) : tugZ L = OMA.SieveA.tugZ L := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l2 =>
      cases l2 with
      | nil => rfl
      | cons c l3 => rw [tugZ, OMA.SieveA.tugZ, ih]

theorem range_two (m : ℕ) : List.range (m + 2) = 0 :: 1 :: (List.range m).map (· + 2) := by
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp

theorem a_261150 : OeisA92243.a 261150 = 1 := by
  have hT := OMA.SieveA.tug_primes 3666581 (by norm_num)
  rw [OMA.SieveA.tugTotal] at hT
  obtain ⟨h1, h2⟩ := hT
  have hlen : (primeListSpec 3666581).length = 261151 := by
    rw [primeListSpec, ← h1]
  have hc : Nat.count Nat.Prime (3666581 + 1) = 261151 := by
    rw [← primeListSpec_length]; exact hlen
  have hL : primeListSpec 3666581 = (List.range 261151).map (Nat.nth Nat.Prime) := by
    rw [primeListSpec_eq_map, hc]
  have hL' : (List.range (3666581 + 1)).filter (fun m => decide m.Prime) =
      (List.range 261151).map (Nat.nth Nat.Prime) := hL
  rw [hL'] at h2
  rw [a_eq_tugZ 261150 (by norm_num), tugZ_eq]
  have e : (261150 + 1 : ℕ) = 261149 + 2 := rfl
  have e2 : (261151 : ℕ) = 261149 + 2 := rfl
  rw [e]
  rw [e2, range_two, List.map_cons, List.map_cons, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three, OMA.SieveA.tugZ_zero_zero, List.length_cons, List.length_cons] at h2
  rw [range_two, List.map_cons, List.map_cons, Nat.nth_prime_zero_eq_two,
    Nat.nth_prime_one_eq_three]
  have h3 : ((20690513873580050135229173390111381 / 18446744073709551616 % 4294967296 : ℕ) : ℤ)
      = 261152 := by norm_num
  rw [h3] at h2
  simp only [List.length_map, List.length_range] at h2
  push_cast at h2
  linarith

end OMA.A92243

theorem OMA.solution : type_of% @OeisA92243.conjecture1 :=
  ⟨261150, by norm_num, by rw [OMA.A92243.a_261150]; norm_num⟩
