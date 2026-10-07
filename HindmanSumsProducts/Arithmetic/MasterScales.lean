import HindmanSumsProducts.Arithmetic.Outside

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- `V_l=2+M+∏_{j<l}X_j²` from §3. -/
def masterScaleV {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (l : Fin n) : ℕ :=
  2 + A.M N + ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < l)), (A.X N j) ^ 2

/-- `Q_l=W^{e₀}∏_{w<p≤V_l}p`, with the paper's `w=N+1`. The product runs over
`w<p≤V+1`, one more than the paper's `p≤V_l`; this only adds a prime below every pool
prime and matches `CRTPrimeRange` in `LinearForms.lean`. -/
def masterCRTModulus (w e V : ℕ) : ℕ :=
  (primorial w) ^ e *
    ∏ p ∈ (Finset.Ioc w (V + 1)).filter Nat.Prime, p

/-- Small-prime divisibility event for a finite polynomial template on uniform unit slots. -/
def uniformSmallPrimeException {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e : ℕ) (u : Fin m → Fin ((primorial w) ^ e)) : Prop :=
  ∃ p, p.Prime ∧ p ≤ w ∧ ∃ P ∈ D,
    ((p ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => ((u i).val : ℤ))

/-- The same small-prime event for actual prime slots in a pool. -/
def primeSmallDivisibilityEvent {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e : ℕ) (p : Fin m → ℕ) : Prop :=
  ∃ q, q.Prime ∧ q ≤ w ∧ ∃ P ∈ D,
    ((q ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ))

/-- A polynomial vanishes, or two prime slots repeat. -/
def polynomialZeroOrRepeated {m : ℕ} (D : Finset (IntegerPolynomial m))
    (p : Fin m → ℕ) : Prop :=
  (∃ P ∈ D, evalIntegerPolynomial P (fun i => (p i : ℤ)) = 0) ∨
    (∃ i j, i ≠ j ∧ p i = p j)

/-- The paper's smooth factor `h_j=W^{w2^{N-j}}` (§3 lines 205, 255), written 0-indexed:
`j : Fin n` gets the exponent `(N+1)·2^(n-1-j)`. It is the right side of
`MasterScaleCore.height_formula`. -/
def masterHeight (n N : ℕ) (j : Fin n) : ℤ :=
  (primorial (N + 1) : ℤ) ^ ((N + 1) * 2 ^ (n - j.val - 1))

/-- The modulus `M=W^{e₀+1+w2^n}` chosen after `e₀` (§3 lines 280–281). It is a power of `W`,
divisible by `W^w`, at least every `h_B`, and eventually divisible by `W^{e₀+1}c_d`. -/
def masterModulus (n N e0 : ℕ) : ℕ :=
  primorial (N + 1) ^ (e0 + 1 + (N + 1) * 2 ^ n)

/-- Algebraic and admissibility part of the master scales. It is one component of the result
`MasterScales`; it is not chosen before the prime pools, since `parameters.H` and
`parameters.X` are the gap lengths and cutoffs chosen after each pool (§3 lines 283–302).
The chain coefficients are integers only for all sufficiently large `w` (§3 lines 210–211,
262–266; §2 lines 80–88). -/
structure MasterScaleCore (n : ℕ) (Aset : Finset ℚ) where
  parameters : OAI.SourceAdmissible.Parameters n
  height_formula : ∀ N (j : Fin n),
    parameters.ht N j =
      (primorial (N + 1) : ℤ) ^ ((N + 1) * 2 ^ (n - j.val - 1))
  modulus_power : ∀ N, ∃ e : ℕ,
    parameters.M N = (primorial (N + 1)) ^ e
  adding_pair_ratio : ∀ N (B : OAI.SourceBlocks.Block n)
      (S : Finset (Fin n)),
    OAI.SourceBlocks.Added B.1 B.2.val S →
      ∃ d : ℤ,
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (parameters.ht N) S =
          OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (parameters.ht N) B.set *
              ((primorial (N + 1) : ℤ) ^ (N + 1) * d)
  chain_coefficients : ∀ᶠ N in atTop, ∀ r (C : MasterChain n r) (a : Fin r → ℚ),
    (∀ d, a d ∈ Aset) →
    ∃ c : Fin r → ℤ,
      (∀ d, (c d : ℚ) =
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (parameters.ht N) (C.block d).set : ℚ) * a d) ∧
      (∀ d, 0 < c d) ∧
      (∀ u d, u < d →
        ∃ k : ℕ, c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d)

/-- Prime-pool component of the master scales: `e₀`, the pools, their CRT accuracy and their
polynomial exceptional events (§3 lines 212–238, 247–251). -/
structure MasterScalePrimeStage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) (m : ℕ) (D : Finset (IntegerPolynomial m)) where
  e0 : ℕ → ℕ
  pool : ℕ → Fin n → PrimePool
  e0_pos : ∀ N, 1 ≤ e0 N
  uniform_small_prime_exception : Tendsto
    (fun N => uniformUnitTupleProbability
      ((primorial (N + 1)) ^ e0 N) m
      (uniformSmallPrimeException D (N + 1) (e0 N))) atTop (𝓝 0)
  pool_lower_dominates : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => ((pool N l).lower : ℝ))
      (fun N => (masterScaleV C.parameters N l : ℝ))
  pool_harmonic_mass_dominates : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => primePoolMass (pool N l).lower (pool N l).upper)
      (fun N => (masterScaleV C.parameters N l : ℝ))
  pool_residue_error : ∀ l,
    SuperPolynomialSmall
      (fun N => finiteL1
        (primePoolResidueLaw (pool N l).lower (pool N l).upper
          (masterCRTModulus (N + 1) (e0 N) (masterScaleV C.parameters N l)))
        (uniformUnitResidueLaw
          (masterCRTModulus (N + 1) (e0 N) (masterScaleV C.parameters N l))))
      (fun N => (masterScaleV C.parameters N l : ℝ))
  actual_small_prime_exception : ∀ l, Tendsto
    (fun N => independentPrimePoolProbability
      (fun _ : Fin m => (pool N l).lower)
      (fun _ : Fin m => (pool N l).upper)
      (primeSmallDivisibilityEvent D (N + 1) (e0 N))) atTop (𝓝 0)
  zero_and_repeat_probability : ∀ l,
    SuperPolynomialSmall
      (fun N => independentPrimePoolProbability
        (fun _ : Fin m => (pool N l).lower)
        (fun _ : Fin m => (pool N l).upper)
        (polynomialZeroOrRepeated D))
      (fun N => (masterScaleV C.parameters N l : ℝ))

/-- Gap-length and cutoff component of the master scales (§3 lines 219, 239–246, 296–302).
`W^{e₀+1}c_d ∣ M` holds only for all sufficiently large `w`: the fixed numerators of
`𝒜` must be `w`-smooth with bounded valuations (§3 lines 262–266, 280–281). -/
structure MasterScaleGapStage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) {m : ℕ} {D : Finset (IntegerPolynomial m)}
    (P : MasterScalePrimeStage C m D) : Prop where
  gap_dominates_pool_and_bound : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => (C.parameters.H N l : ℝ))
      (fun N => ((P.pool N l).upper + masterScaleV C.parameters N l : ℝ))
  gap_modulus_divides : ∀ N l, C.parameters.M N ∣ C.parameters.H N l
  earlier_gaps_divide : ∀ N (i j : Fin n), i < j →
    C.parameters.H N i ∣ C.parameters.H N j
  polynomial_values_divide_gap : ∀ N l (p : Fin m → ℕ) (Q : IntegerPolynomial m),
    Q ∈ D →
    (∀ i, (P.pool N l).lower ≤ p i ∧ p i < (P.pool N l).upper ∧ (p i).Prime) →
    evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0 →
    C.parameters.M N * (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∣
      C.parameters.H N l
  raw_cutoff_log_dominates_gap : ∀ l,
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (C.parameters.X N l : ℝ))
      (fun N => (C.parameters.H N l : ℝ))
  coefficient_divides_modulus : ∀ᶠ N in atTop, ∀ r (chain : MasterChain n r)
      (a : Fin r → ℚ), (∀ d, a d ∈ Aset) → ∀ c : Fin r → ℤ,
    (∀ d, (c d : ℚ) =
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (C.parameters.ht N) (chain.block d).set : ℚ) * a d) →
    ∀ d, ((primorial (N + 1) ^ (P.e0 N + 1) : ℕ) : ℤ) * c d ∣
      (C.parameters.M N : ℤ)
  valid_raw_cutoffs : ∀ N l,
    4 * primorial (N + 1) ≤ C.parameters.X N l

/-- Complete sequential master-scale data: an OAI admissible family plus the stronger
prime-pool and divisibility certificates required in §3. -/
structure MasterScales (n : ℕ) (Aset : Finset ℚ) (m : ℕ)
    (D : Finset (IntegerPolynomial m)) where
  core : MasterScaleCore n Aset
  primeStage : MasterScalePrimeStage core m D
  gapStage : MasterScaleGapStage core primeStage

/-- Binary subset separation used to make every earlier block-height ratio contain `W^w`
(§3 lines 254–266). -/
private lemma sum_pow_two_range (k : ℕ) :
    ∑ e ∈ Finset.range k, (2 : ℕ) ^ e = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      omega

theorem binary_subset_weight_separation (n : ℕ)
    (S T : Finset (Fin n)) (j : Fin n) (hjS : j ∈ S) (hjT : j ∉ T)
    (hfirst : ∀ i, i < j → (i ∈ S ↔ i ∈ T)) :
    ∑ i ∈ S, 2 ^ (n - i.val - 1) > ∑ i ∈ T, 2 ^ (n - i.val - 1) := by
  classical
  let f : Fin n → ℕ := fun i => 2 ^ (n - i.val - 1)
  let tail : Finset (Fin n) := Finset.univ.filter (fun i => j < i)
  let exponents : Finset ℕ := tail.image (fun i => (Fin.rev i).val)
  have hexp (i : Fin n) : f i = 2 ^ (Fin.rev i).val := by
    change 2 ^ (n - i.val - 1) = 2 ^ (Fin.rev i).val
    rw [Fin.val_rev, Nat.sub_sub]
  have hinj : Set.InjOn (fun i : Fin n => (Fin.rev i).val) (tail : Set (Fin n)) := by
    intro i hi i' hi' heq
    have hrev : Fin.rev i = Fin.rev i' := Fin.ext heq
    have heq' : i = i' := Fin.rev_injective hrev
    exact heq'
  have hexpsub : exponents ⊆ Finset.range (n - j.val - 1) := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
    have hij : j < i := (Finset.mem_filter.mp hi).2
    rw [Finset.mem_range, Fin.val_rev]
    omega
  have htail : (∑ i ∈ tail, f i) < f j := by
    have himage : (∑ i ∈ tail, f i) =
        ∑ e ∈ exponents, (2 : ℕ) ^ e := by
      calc
        (∑ i ∈ tail, f i) = ∑ i ∈ tail, (2 : ℕ) ^ (Fin.rev i).val := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hexp i
        _ = ∑ e ∈ exponents, (2 : ℕ) ^ e :=
          (Finset.sum_image hinj).symm
    have hgeom := sum_pow_two_range (n - j.val - 1)
    calc
      (∑ i ∈ tail, f i) = ∑ e ∈ exponents, (2 : ℕ) ^ e := himage
      _ ≤ ∑ e ∈ Finset.range (n - j.val - 1), (2 : ℕ) ^ e :=
        Finset.sum_le_sum_of_subset hexpsub
      _ = 2 ^ (n - j.val - 1) - 1 := hgeom
      _ < 2 ^ (n - j.val - 1) := by
        have hp : 0 < 2 ^ (n - j.val - 1) := by positivity
        omega
      _ = f j := rfl
  let common := S ∩ T
  let sdiff := S \ T
  let tdiff := T \ S
  have hSset : S = common ∪ sdiff := by
    ext i
    change i ∈ S ↔ i ∈ S ∩ T ∪ S \ T
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hTset : T = common ∪ tdiff := by
    ext i
    change i ∈ T ↔ i ∈ S ∩ T ∪ T \ S
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjS : Disjoint common sdiff := by
    apply Finset.disjoint_left.mpr
    intro i hi hs
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_inter.mp hi).2
  have hdisjT : Disjoint common tdiff := by
    apply Finset.disjoint_left.mpr
    intro i hi ht
    exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_inter.mp hi).1
  have hsumS : (∑ i ∈ S, f i) = (∑ i ∈ common, f i) + ∑ i ∈ sdiff, f i := by
    rw [hSset, Finset.sum_union hdisjS]
  have hsumT : (∑ i ∈ T, f i) = (∑ i ∈ common, f i) + ∑ i ∈ tdiff, f i := by
    rw [hTset, Finset.sum_union hdisjT]
  have hjSdiff : j ∈ sdiff := Finset.mem_sdiff.mpr ⟨hjS, hjT⟩
  have hsdiffLower : f j ≤ ∑ i ∈ sdiff, f i := by
    calc
      f j = ∑ i ∈ ({j} : Finset (Fin n)), f i := (Finset.sum_singleton f j).symm
      _ ≤ ∑ i ∈ sdiff, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr hjSdiff)
          (by intro i hi hni; exact Nat.zero_le _)
  have htdiffSubset : tdiff ⊆ tail := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hile : i.val ≤ j.val := Fin.not_lt.mp (by
      intro hij
      exact hnot (Fin.lt_iff_val_lt_val.mpr hij))
    by_cases heq : i.val = j.val
    · have hieq : i = j := Fin.ext heq
      subst i
      exact hjT (Finset.mem_sdiff.mp hi).1
    · have hijv : i.val < j.val := by omega
      have his : i ∈ S := (hfirst i (Fin.lt_iff_val_lt_val.mpr hijv)).2
        (Finset.mem_sdiff.mp hi).1
      exact (Finset.mem_sdiff.mp hi).2 his
  have htdiffUpper : (∑ i ∈ tdiff, f i) ≤ ∑ i ∈ tail, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg htdiffSubset
      (by intro i hi hni; exact Nat.zero_le _)
  have hdiff : (∑ i ∈ tdiff, f i) < ∑ i ∈ sdiff, f i :=
    lt_of_le_of_lt htdiffUpper (lt_of_lt_of_le htail hsdiffLower)
  rw [hsumS, hsumT]
  simpa [gt_iff_lt, add_comm] using
    (add_lt_add_left hdiff (∑ i ∈ common, f i))
/-! ### Item (1): heights, chain coefficients and the modulus (§3 lines 204–211, 255–266) -/

/-- For an adding pair `S ∈ 𝓔_B`, `h_S/h_B` is an integer multiple of `W^w`, for every `w`
(§3 lines 208, 255–262): the smallest index of the symmetric difference lies in `S`. This is
the form of `OAI.SourceAdmissible.Parameters.ratio`. -/
theorem master_height_adding_ratio (n N : ℕ) (B : OAI.SourceBlocks.Block n)
    (S : Finset (Fin n)) (hS : OAI.SourceBlocks.Added B.1 B.2.val S) :
    ∃ d : ℤ,
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) S =
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) B.set * ((primorial (N + 1) : ℤ) ^ (N + 1) * d) := by
  sorry

/-- For two blocks `u<d` of a master chain, `h_{B_u}/h_{B_d}` is a positive power of `W^w`,
for every `w` (§3 lines 259–262): the smallest index of the symmetric difference is
`min T_u`. -/
theorem master_chain_height_ratio (n N r : ℕ) (C : MasterChain n r) (u d : Fin r)
    (hud : u < d) :
    ∃ k : ℕ, 0 < k ∧
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) (C.block u).set =
        OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) (C.block d).set * ((primorial (N + 1) : ℤ) ^ (N + 1)) ^ k := by
  sorry

/-- Rational absorption for chains (§3 lines 209–211, 262–266; §2 lines 80–88): for all
sufficiently large `w`, every `c_d=h_{B_d}a_d` with `a_d ∈ 𝒜` is a positive integer and
`c_u/c_d ∈ Wℕ` for `u<d`. The threshold depends only on `𝒜` (its denominators and numerators
become `w`-smooth with valuations at most `w-1`), so it is uniform over all chains. At small
`w` this fails: at `N=0` every height is `1` and `c_d=a_d` need not be an integer. -/
theorem master_chain_coefficients (n : ℕ) (Aset : Finset ℚ) (hA : ∀ a ∈ Aset, 0 < a) :
    ∀ᶠ N in atTop, ∀ r (C : MasterChain n r) (a : Fin r → ℚ), (∀ d, a d ∈ Aset) →
      ∃ c : Fin r → ℤ,
        (∀ d, (c d : ℚ) =
          (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (masterHeight n N) (C.block d).set : ℚ) * a d) ∧
        (∀ d, 0 < c d) ∧
        (∀ u d, u < d → ∃ k : ℕ, c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d) := by
  sorry

/-- Every product of heights is at most `M` (§3 lines 205–207): `h_S ≤ W^{w(2^n-1)}`. -/
theorem master_height_le_modulus (n N e0 : ℕ) (S : Finset (Fin n)) :
    OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (masterHeight n N) S ≤ (masterModulus n N e0 : ℤ) := by
  sorry

/-- `W^{e₀+1}c_d ∣ M` for every possible chain coefficient, for all sufficiently large `w`
(§3 line 219, 280–281): once every numerator of `𝒜` divides `W^w`, `c_d` divides
`W^{w(2^n-1)+w}`. Uniform in the function `e₀`. Positivity of `𝒜` excludes `a_d=0`, for which
`c_d=0` does not divide `M`. -/
theorem master_coefficient_divides_modulus (n : ℕ) (Aset : Finset ℚ)
    (hA : ∀ a ∈ Aset, 0 < a) (e0 : ℕ → ℕ) :
    ∀ᶠ N in atTop, ∀ r (C : MasterChain n r) (a : Fin r → ℚ), (∀ d, a d ∈ Aset) →
      ∀ c : Fin r → ℤ,
      (∀ d, (c d : ℚ) =
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) (C.block d).set : ℚ) * a d) →
      ∀ d, ((primorial (N + 1) ^ (e0 N + 1) : ℕ) : ℤ) * c d ∣
        (masterModulus n N (e0 N) : ℤ) := by
  sorry

/-! ### Item (2): the small-prime exponent `e₀` (§3 lines 212–219, 268–280) -/

/-- A nonzero integer polynomial has zero Haar measure on a product of p-adic unit groups;
in the finite quotient form, its divisibility probability tends to zero with the modulus
(§3 lines 268–280). -/
theorem p_adic_polynomial_unit_zero_set {m : ℕ} (p : ℕ) (hp : p.Prime)
    (Q : IntegerPolynomial m) (hQ : Q ≠ 0) :
    Tendsto
      (fun e => uniformUnitTupleProbability (p ^ e) m
        (fun x => ((p ^ e : ℕ) : ℤ) ∣
          evalIntegerPolynomial Q (fun i => ((x i).val : ℤ))))
      atTop (𝓝 0) := by
  sorry

/-- Finite union bound choosing one common exponent for all prescribed small-prime tests
(§3 lines 276–280). The polynomials must be nonzero (§3 line 200); for `D={0}` the event
always holds. -/
theorem choose_small_prime_exception_exponent {m : ℕ}
    (w : ℕ) (hw : 1 ≤ w) (D : Finset (IntegerPolynomial m)) (hD : ∀ P ∈ D, P ≠ 0) :
    ∃ e : ℕ, 1 ≤ e ∧
      uniformUnitTupleProbability ((primorial w) ^ e) m
        (uniformSmallPrimeException D w e) ≤ 1 / (w : ℝ) := by
  sorry

/-! ### Item (3): prime pools (§3 lines 220–238, 283–294, 304–315) -/

/-- Elementary product-grid zero bound (§3 lines 304–310): if independent coordinates have
probability laws with every atom at most `a`, a nonzero polynomial of total degree `d`
vanishes with probability at most `d·a`. The laws must be nonnegative: with signed masses the
bound fails (`P=X₀-X₁`, masses `2,-1`). -/
theorem polynomial_zero_product_grid_bound {m : ℕ}
    (P : IntegerPolynomial m) (hP : P ≠ 0)
    (μ : Fin m → ℕ → ℝ) (a : ℝ)
    (hnonneg : ∀ i x, 0 ≤ μ i x)
    (hmax : ∀ i x, μ i x ≤ a)
    (hprob : ∀ i, ∑' x : ℕ, μ i x = 1) :
    ∑' x : Fin m → ℕ,
      (∏ i, μ i (x i)) *
        (if evalIntegerPolynomial P (fun i => (x i : ℤ)) = 0 then (1 : ℝ) else 0)
      ≤ (MvPolynomial.totalDegree P : ℝ) * a := by
  sorry

/-- One gap's pool (§3 lines 283–294): for a fixed modulus `Q` (at this stage `Q_l` is a fixed
integer), a finite union of consecutive complete dyadic intervals, starting at any prescribed
height `B`, with harmonic mass at least `B` and residue law modulo `Q` within `ε` of uniform
measure on the units. Uses the prime number theorem in progressions on each dyadic interval,
convexity of the total-mass distance under mixtures, and divergence of `∑1/p`. -/
theorem choose_master_pool (Q B : ℕ) (hQ : 0 < Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ pool : PrimePool, B ≤ pool.lower ∧
      (B : ℝ) ≤ primePoolMass pool.lower pool.upper ∧
      finiteL1 (primePoolResidueLaw pool.lower pool.upper Q)
        (uniformUnitResidueLaw Q) ≤ ε := by
  sorry

/-- CRT transfer of the small-prime exception to actual pool slots (§3 lines 278–280,
313–315): the event depends only on the residues modulo `W^e ∣ Q`; uniform units modulo `Q`
reduce to uniform units modulo `W^e`, and the `m` independent slots cost at most `m` times
the residue error. -/
theorem pool_small_prime_exception_transfer {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e Q lo hi : ℕ) (hQ : 0 < Q) (hdiv : (primorial w) ^ e ∣ Q) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ : Fin m => hi)
        (primeSmallDivisibilityEvent D w e) ≤
      uniformUnitTupleProbability ((primorial w) ^ e) m
          (uniformSmallPrimeException D w e) +
        (m : ℝ) * finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
  sorry

/-- Zero values and repeated slots in one pool (§3 lines 247–251, 304–313): the maximum atom
of the pool law is at most `1/(P^-·H^{pr})`, so the grid bound for each polynomial and for
each difference `x_i-x_j` gives this bound. -/
theorem pool_zero_or_repeat_bound {m : ℕ} (D : Finset (IntegerPolynomial m))
    (hD : ∀ P ∈ D, P ≠ 0) (lo hi : ℕ) (hlo : 0 < lo) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ : Fin m => hi)
        (polynomialZeroOrRepeated D) ≤
      (((∑ P ∈ D, MvPolynomial.totalDegree P) + m ^ 2 : ℕ) : ℝ) /
        ((lo : ℝ) * primePoolMass lo hi) := by
  sorry

/-! ### Item (4): gap lengths (§3 lines 239–246, 296–302) -/

/-- One gap length (§3 lines 296–300): only finitely many polynomial values occur in a finite
pool, so a common multiple of `M`, of the earlier gap lengths (through `L`) and of every
nonzero `M|D(p)|` can be chosen above any prescribed bound. -/
theorem choose_master_gap_length {m : ℕ} (D : Finset (IntegerPolynomial m))
    (lo hi M L B : ℕ) (hM : 0 < M) (hL : 0 < L) :
    ∃ R : ℕ, 0 < R ∧ B ≤ R ∧ M ∣ R ∧ L ∣ R ∧
      ∀ (p : Fin m → ℕ) (Q : IntegerPolynomial m), Q ∈ D →
        (∀ i, lo ≤ p i ∧ p i < hi ∧ (p i).Prime) →
        evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0 →
        M * (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∣ R := by
  sorry

/-- Lemma `lem:master-scales` (§3 lines 197–316): for every fixed master length, positive
rational template set and finite list of nonzero polynomials, there are OAI admissible
parameters with all additional prime-pool, smooth-divisibility, gap and cutoff data.

Construction, at each `N` (`w=N+1`, `W=primorial w`), in the paper's order of choices:
`e₀` by `choose_small_prime_exception_exponent` (so the uniform exception is at most `1/w`);
`M=masterModulus n N e₀`; `h_j=masterHeight n N j`; then for `l=0,1,…` in turn:
`V_l` from `M` and the earlier `X_j`, `Q_l=masterCRTModulus w e₀ V_l`, the pool by
`choose_master_pool Q_l (w·V_l^w) (V_l^{-w})`, `R_l=H_l` by `choose_master_gap_length` with
`L=R_{l-1}` and bound `w(P_l^++V_l)^w`, and `X_l=2^k` with `log X_l ≥ wR_l^w` and
`X_l ≥ 4W`. The asymptotic fields follow from these explicit bounds (`V_l ≥ 2`), the
`∀ᶠ` fields from `master_chain_coefficients` and `master_coefficient_divides_modulus`,
`ratio` from `master_height_adding_ratio`, the exception fields from
`pool_small_prime_exception_transfer` and `pool_zero_or_repeat_bound`. -/
theorem lem_master_scales (n : ℕ) (Aset : Finset ℚ)
    (hA : ∀ a ∈ Aset, 0 < a) (m : ℕ)
    (D : Finset (IntegerPolynomial m)) (hD : ∀ P ∈ D, P ≠ 0) :
    Nonempty (MasterScales n Aset m D) := by
  sorry

/-- Remark `rem:arithmetic-diagonal`: diagonalize a countable fixed family of templates and
auxiliary parameters before any test functions are selected (§3 lines 325–341): increasing
thresholds `w_j` such that the stage-`j` errors are at most `1/j` once `w ≥ w_j`. -/
theorem arithmetic_countable_test_diagonal
    (requiredError : ℕ → ℕ → ℝ)
    (hsmall : ∀ j, Tendsto (requiredError j) atTop (𝓝 0)) :
    ∃ threshold : ℕ → ℕ, StrictMono threshold ∧
      ∀ j N, threshold j ≤ N →
        requiredError j N ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
  have hbound : ∀ j, ∀ᶠ N : ℕ in atTop,
      requiredError j N ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
    intro j
    have heps : 0 < (1 / ((j + 1 : ℕ) : ℝ)) := by positivity
    filter_upwards [(hsmall j).eventually (Metric.ball_mem_nhds 0 heps)] with N hN
    change dist (requiredError j N) 0 < 1 / ((j + 1 : ℕ) : ℝ) at hN
    have habs : |requiredError j N| < 1 / ((j + 1 : ℕ) : ℝ) := by
      simpa [Real.dist_eq] using hN
    exact le_of_lt (abs_lt.mp habs).2
  let start : ℕ → ℕ := fun j => Classical.choose (eventually_atTop.mp (hbound j))
  have hstart : ∀ j N, start j ≤ N →
      requiredError j N ≤ 1 / ((j + 1 : ℕ) : ℝ) := by
    intro j N hN
    exact (Classical.choose_spec (eventually_atTop.mp (hbound j))) N hN
  let threshold : ℕ → ℕ := Nat.rec (start 0)
    (fun j t => max (t + 1) (start (j + 1)))
  have hthreshold : ∀ j, start j ≤ threshold j := by
    intro j
    induction j with
    | zero => exact Nat.le_refl _
    | succ j ih =>
        change start (j + 1) ≤ max (threshold j + 1) (start (j + 1))
        exact Nat.le_max_right _ _
  refine ⟨threshold, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    change threshold j < max (threshold j + 1) (start (j + 1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
  · intro j N hN
    exact hstart j N ((hthreshold j).trans hN)

end
end HindmanSumsProducts
