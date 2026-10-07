import HindmanSumsProducts.Arithmetic.Outside

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- `V_l=2+M+∏_{j<l}X_j²` from §3. -/
def masterScaleV {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (N : ℕ) (l : Fin n) : ℕ :=
  2 + A.M N + ∏ j ∈ (Finset.univ.filter (fun j : Fin n => j < l)), (A.X N j) ^ 2

/-- `Q_l=W^{e₀}∏_{w<p≤V_l}p`, with the paper's `w=N+1`. -/
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

/-- The algebraic and admissibility stage of the master-scale construction. -/
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
  chain_coefficients : ∀ N r (C : MasterChain n r) (a : Fin r → ℚ),
    (∀ d, a d ∈ Aset) →
    ∃ c : Fin r → ℤ,
      (∀ d, (c d : ℚ) =
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (parameters.ht N) (C.block d).set : ℚ) * a d) ∧
      (∀ d, 0 < c d) ∧
      (∀ u d, u < d →
        ∃ k : ℕ, c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d)

/-- The prime-pool stage, including its CRT accuracy and its polynomial exceptional events. -/
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

/-- Completion of the master scales by gap lengths and raw cutoffs. -/
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
  coefficient_divides_modulus : ∀ N r (chain : MasterChain n r)
      (a : Fin r → ℚ) (ha : ∀ d, a d ∈ Aset) (c : Fin r → ℤ),
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

/-- Finite union bound choosing one common exponent for all prescribed small-prime tests. -/
theorem choose_small_prime_exception_exponent {m : ℕ}
    (w : ℕ) (hw : 1 ≤ w) (D : Finset (IntegerPolynomial m)) :
    ∃ e : ℕ, 1 ≤ e ∧
      uniformUnitTupleProbability ((primorial w) ^ e) m
        (uniformSmallPrimeException D w e) ≤ 1 / (w : ℝ) := by
  sorry

private theorem small_prime_exponent_counterexample :
    ¬ ∃ e : ℕ, 1 ≤ e ∧
      uniformUnitTupleProbability ((primorial 2) ^ e) 0
        (uniformSmallPrimeException ({0} : Finset (IntegerPolynomial 0)) 2 e) ≤
          1 / (2 : ℝ) := by
  rintro ⟨e, he, hprob⟩
  have hevent : ∀ u : Fin 0 → Fin ((primorial 2) ^ e),
      uniformSmallPrimeException ({0} : Finset (IntegerPolynomial 0)) 2 e u := by
    intro u
    refine ⟨2, by norm_num, by norm_num, 0, by simp, ?_⟩
    simp [evalIntegerPolynomial]
  have hmass : uniformUnitTupleProbability ((primorial 2) ^ e) 0
      (uniformSmallPrimeException ({0} : Finset (IntegerPolynomial 0)) 2 e) = 1 := by
    simp [uniformUnitTupleProbability, uniformUnitTupleMass, hevent]
  rw [hmass] at hprob
  norm_num at hprob

/-- Elementary product-grid zero bound used to show polynomial zeros and repeated prime
slots have super-polynomially small probability in the constructed pools. -/
theorem polynomial_zero_product_grid_bound {m : ℕ}
    (P : IntegerPolynomial m) (hP : P ≠ 0)
    (μ : Fin m → ℕ → ℝ) (a : ℝ)
    (hmax : ∀ i x, μ i x ≤ a)
    (hprob : ∀ i, ∑' x : ℕ, μ i x = 1) :
    ∑' x : Fin m → ℕ,
      (∏ i, μ i (x i)) *
        (if evalIntegerPolynomial P (fun i => (x i : ℤ)) = 0 then (1 : ℝ) else 0)
      ≤ (MvPolynomial.totalDegree P : ℝ) * a := by
  sorry

private theorem no_master_scale_core_for_half :
    ¬ Nonempty (MasterScaleCore 3 ({(1 / 2 : ℚ)} : Finset ℚ)) := by
  rintro ⟨C⟩
  classical
  let zero : Fin 3 := ⟨0, by omega⟩
  let gap : Fin 3 := ⟨1, by omega⟩
  let pivot : Fin 3 := ⟨2, by omega⟩
  let tail : OAI.SourceBlocks.Tail pivot := ⟨{zero}, by
    constructor
    · simp
    · intro i hi
      have h : i = zero := Finset.mem_singleton.mp hi
      subst i
      norm_num [zero, pivot]
  ⟩
  let block : OAI.SourceBlocks.Block 3 := ⟨pivot, tail⟩
  let chain : MasterChain 3 1 := {
    gap := gap
    block := fun _ => block
    tails_before_gap := by
      intro d i hi
      simp [block, tail] at hi
      subst i
      norm_num [zero, gap]
    tails_ordered := by
      intro u d hud i hi k hk
      fin_cases u
      fin_cases d
      simp at hud
    pivots_after_gap := by
      intro d
      fin_cases d
      norm_num [gap, block, pivot]
    pivots_ordered := by
      intro u d hud
      fin_cases u
      fin_cases d
      simp at hud
  }
  have hht : ∀ i : Fin 3, C.parameters.ht 0 i = 1 := by
    intro i
    rw [C.height_formula 0 i]
    simp [primorial_one]
  have hheight :
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (C.parameters.ht 0) (chain.block 0).set = 1 := by
    unfold OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
    simp_rw [hht]
    simp
  obtain ⟨c, hc, -, -⟩ := C.chain_coefficients 0 1 chain
      (fun _ => (1 / 2 : ℚ)) (by intro d; simp)
  have hhalf : (c 0 : ℚ) = 1 / 2 := by
    simpa [hheight] using hc 0
  have hcast : ((c 0 : ℤ) : ℚ) * 2 = 1 := by
    simpa using congrArg (fun x : ℚ => x * 2) hhalf
  have hz : c 0 * 2 = 1 := by exact_mod_cast hcast
  omega

private theorem no_master_scales_for_half :
    ¬ Nonempty (MasterScales 3 ({(1 / 2 : ℚ)} : Finset ℚ) 0
      (∅ : Finset (IntegerPolynomial 0))) := by
  rintro ⟨S⟩
  exact no_master_scale_core_for_half ⟨S.core⟩

/-- Algebraic master-scale stage: constructs `OAI.SourceAdmissible.Parameters n` with the
paper's binary `h_j`, a power-of-W modulus, and all rational chain divisibilities. -/
theorem choose_master_scale_core (n : ℕ) (Aset : Finset ℚ)
    (hA : ∀ a ∈ Aset, 0 < a) : Nonempty (MasterScaleCore n Aset) := by
  sorry

/-- Prime-pool stage: choose the common small-prime exponent and the harmonic prime pools,
with residue equidistribution, harmonic mass, and nonvanishing/repetition bounds. -/
theorem choose_master_prime_stage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) (m : ℕ) (D : Finset (IntegerPolynomial m))
    (hD : ∀ P ∈ D, P ≠ 0) : Nonempty (MasterScalePrimeStage C m D) := by
  sorry

/-- Sequential gap completion: choose each `R_l` divisible by every earlier requirement, then
choose its power-of-two raw cutoff after the gap is fixed. -/
theorem choose_master_gap_stage {n : ℕ} {Aset : Finset ℚ}
    (C : MasterScaleCore n Aset) {m : ℕ} {D : Finset (IntegerPolynomial m)}
    (P : MasterScalePrimeStage C m D) : Nonempty (MasterScaleGapStage C P) := by
  sorry

/-- Lemma `lem:master-scales`: for every fixed master length, block-size/rational templates,
and finite nonzero polynomial list, choose OAI admissible parameters and all additional
prime-pool, smooth divisibility, gap, and cutoff data from §§3 lines 197–316. -/
theorem lem_master_scales (n : ℕ) (Aset : Finset ℚ)
    (hA : ∀ a ∈ Aset, 0 < a) (m : ℕ)
    (D : Finset (IntegerPolynomial m)) (hD : ∀ P ∈ D, P ≠ 0) :
    Nonempty (MasterScales n Aset m D) := by
  obtain ⟨C⟩ := choose_master_scale_core n Aset hA
  obtain ⟨P⟩ := choose_master_prime_stage C m D hD
  obtain ⟨G⟩ := choose_master_gap_stage C P
  exact ⟨⟨C, P, G⟩⟩

/-- Remark `rem:arithmetic-diagonal`: diagonalize a countable fixed family of templates and
auxiliary parameters before any test functions are selected (§3 lines 325–341). -/
theorem arithmetic_countable_test_diagonal
    (requiredError : ℕ → ℕ → ℝ)
    (hsmall : ∀ j, Tendsto (requiredError j) atTop (𝓝 0)) :
    ∃ threshold : ℕ → ℕ, StrictMono threshold ∧
      ∀ j, ∀ᶠ N in atTop, threshold j ≤ N →
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
  · intro j
    apply eventually_atTop.2
    refine ⟨threshold j, ?_⟩
    intro N hN hthresholdN
    exact hstart j N ((hthreshold j).trans hthresholdN)

end
end HindmanSumsProducts
