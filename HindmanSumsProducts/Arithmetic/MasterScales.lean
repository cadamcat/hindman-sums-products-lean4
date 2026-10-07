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
theorem binary_subset_weight_separation (n : ℕ)
    (S T : Finset (Fin n)) (j : Fin n) (hjS : j ∈ S) (hjT : j ∉ T)
    (hfirst : ∀ i, i < j → (i ∈ S ↔ i ∈ T)) :
    ∑ i ∈ S, 2 ^ (n - i.val - 1) > ∑ i ∈ T, 2 ^ (n - i.val - 1) := by
  sorry

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
  sorry

end
end HindmanSumsProducts
