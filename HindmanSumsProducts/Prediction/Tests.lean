import HindmanSumsProducts.Prediction.Defs
import HindmanSumsProducts.Prediction.PkgA

/-!
# Cube types and dual tests (§5.1, `05_prediction.tex` 38–61)

A cube type is §4's `HindmanSumsProducts.CubeTemplate` (`Correlation/Defs.lean`): `q` prime
slots, order `d`, modulus polynomial `D` and the finite list of good-tuple tests.  The prime law,
modulus and shift lengths are §4's (`CubeTemplate.Good`, `.modulus`, `.length`,
`goodSlotAverage`): the `q` slots are independent harmonic samples from the pool of the gap,
restricted to the good tuples of Lemma `lem:row-directions` (04:375–384) and renormalized;
`M(p) = M |D(p)|_{>w}`; `L_p = ⌊R_l/(J₀M(p))⌋`; shifts uniform on `[0, L_p)`.

The master scales are §3's `HindmanSumsProducts.MasterScales K As sl Dm` in `s` slots.  §4 states
its results for the verbatim copy `FromArithmetic.MasterScales`; `corrScales` converts (field by
field, no new content) and disappears when §4 is unified onto §3.  A type is allowed when its tests,
renamed into the master slots by some embedding, lie in the master list (§4 `TestsListed`,
REPAIR-S4.md §4 item 2).
-/

open scoped BigOperators NNReal Topology
open Filter

namespace HindmanSumsProducts.Prediction

noncomputable section

variable {K sl : ℕ} {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}

/-- §3 master scales viewed as §4's verbatim copy `FromArithmetic.MasterScales`. -/
def corrScales (MS : MasterScales K As sl Dm) : FromArithmetic.MasterScales K As sl Dm where
  core :=
    { parameters := MS.core.parameters
      height_formula := MS.core.height_formula
      modulus_power := MS.core.modulus_power
      adding_pair_ratio := MS.core.adding_pair_ratio
      chain_coefficients := MS.core.chain_coefficients }
  primeStage :=
    { e0 := MS.primeStage.e0
      pool := MS.primeStage.pool
      e0_pos := MS.primeStage.e0_pos
      uniform_small_prime_exception := MS.primeStage.uniform_small_prime_exception
      pool_lower_dominates := MS.primeStage.pool_lower_dominates
      pool_harmonic_mass_dominates := MS.primeStage.pool_harmonic_mass_dominates
      pool_residue_error := MS.primeStage.pool_residue_error
      actual_small_prime_exception := MS.primeStage.actual_small_prime_exception
      zero_and_repeat_probability := MS.primeStage.zero_and_repeat_probability }
  gapStage :=
    { gap_dominates_pool_and_bound := MS.gapStage.gap_dominates_pool_and_bound
      gap_modulus_divides := MS.gapStage.gap_modulus_divides
      earlier_gaps_divide := MS.gapStage.earlier_gaps_divide
      polynomial_values_divide_gap := MS.gapStage.polynomial_values_divide_gap
      raw_cutoff_log_dominates_gap := MS.gapStage.raw_cutoff_log_dominates_gap
      coefficient_divides_modulus := MS.gapStage.coefficient_divides_modulus
      valid_raw_cutoffs := MS.gapStage.valid_raw_cutoffs }

/-- A cube type is allowed at master scales with polynomial list `Dm` when its tests, renamed
by some slot embedding, belong to `Dm`. -/
def Allowed (Dm : Finset (IntegerPolynomial sl)) (T : CubeTemplate) : Prop :=
  ∃ ι : Fin T.q ↪ Fin sl, TestsListed Dm ι T.tests

/-- The extra type of dimension `s' + 1` with modulus `M` and no prime variables (05:42–43):
`q = 0`, `D = 1`, tests `{1}` (REPAIR-S4.md §1, last paragraph).  It is allowed iff `1 ∈ Dm`. -/
def extraTemplate (s' : ℕ) : CubeTemplate where
  q := 0
  d := s' + 1
  D := 1
  tests := {1}
  D_mem := Finset.mem_singleton_self 1
  tests_ne_zero := by simp

/-- Inputs of a dual test at block `B` and asymptotic index `N` (05:52–60): a bounded prime
factor `e` and functions `g_{ω,p}` with `|g| ≤ 1 + ν_B`.  They may vary arbitrarily with `N`. -/
structure DualInput (MS : MasterScales K As sl Dm) (B : Block K) (T : CubeTemplate) (N : ℕ) where
  e : (Fin T.q → ℕ) → ℝ
  g : Finset (Fin T.d) → (Fin T.q → ℕ) → ℤ → ℝ
  e_bound : ∀ p, |e p| ≤ 1
  g_bound : ∀ ω p y, |g ω p y| ≤ 1 + nu MS.core.parameters N B y

/-- The dual test (eq:prediction-dual-test) of type `T` at gap `l`:
`𝒟(y) = E_{p,u} e(p) ∏_{∅ ≠ ω ⊆ [d]} g_{ω,p}(y + M(p) ∑_{j∈ω}(u_j^1 − u_j^0))`. -/
def dualTest (MS : MasterScales K As sl Dm) (B : Block K) (T : CubeTemplate) (l : Fin K)
    (J0 N : ℕ) (I : DualInput MS B T N) (y : ℤ) : ℝ :=
  goodSlotAverage (corrScales MS) l N (T.Good (corrScales MS) l N) fun p =>
    I.e p * shiftAverage (Fin T.d) (T.length (corrScales MS) l J0 N p) fun u =>
      ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
        I.g ω p (y + (T.modulus (corrScales MS) N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))

/-- The rooted cube average `E_{p,y,u} ∏_{ω ⊆ [d]} h(y + M(p) ∑_{j∈ω}(u_j^1 − u_j^0))`, `y ∼ μ_i`:
§4's `CubeTemplate.cubeTest`, the quantity of (eq:correlation-test) and
(eq:prediction-subgroup-conclusion). -/
def cubeAverage (MS : MasterScales K As sl Dm) (T : CubeTemplate) (l i : Fin K) (J0 N : ℕ)
    (h : ℤ → ℝ) : ℝ :=
  T.cubeTest (corrScales MS) l i J0 N h

/-- Remark `rem:correlation-dual-interface` (04:708–727): with `e = 1` and every input equal to
`h`, the cube average is the pairing `E_{μ_i} h 𝒟`.  Requires only `|h| ≤ 1 + ν_B`. -/
theorem cubeAverage_eq_dualPairing (MS : MasterScales K As sl Dm) (B : Block K)
    (T : CubeTemplate) (l : Fin K) (J0 N : ℕ) (h : ℤ → ℝ)
    (hh : ∀ y, |h y| ≤ 1 + nu MS.core.parameters N B y) :
    cubeAverage MS T l B.1 J0 N h =
      Emu MS.core.parameters N B.1 (fun y => h y *
        dualTest MS B T l J0 N
          ⟨fun _ => 1, fun _ _ => h, fun _ => by simp, fun _ _ y => hh y⟩ y) := by
  classical
  let S := corrScales MS
  let G : (Fin T.q → ℕ) → Prop := fun p => T.Good S l N p
  let μ : ℤ → ℝ := harmonicLaw (MS.core.parameters.X N B.1) (primorial (N + 1))
  let fullShift : (Fin T.q → ℕ) → ℤ → ℝ := fun p y =>
    shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
      ∏ ω : Finset (Fin T.d),
        h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))
  let shortShift : (Fin T.q → ℕ) → ℤ → ℝ := fun p y =>
    shiftAverage (Fin T.d) (T.length S l J0 N p) fun u =>
      ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
        h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))
  let I : DualInput MS B T N :=
    ⟨fun _ => 1, fun _ _ => h, fun _ => by simp, fun _ _ y => hh y⟩
  let prob := gapSlotProbability S l N G
  have hvertex (p : Fin T.q → ℕ) (y : ℤ) (u : Fin T.d → Fin 2 → ℕ) :
      (∏ ω : Finset (Fin T.d),
        h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) =
      h y * ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
        h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) := by
    let f : Finset (Fin T.d) → ℝ := fun ω =>
      h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))
    have hempty' : (∅ : Finset (Fin T.d)) ∈ (Finset.univ : Finset (Finset (Fin T.d))) :=
      Finset.mem_univ _
    calc
      (∏ ω : Finset (Fin T.d), f ω) =
          (∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅, f ω) * f ∅ :=
            (Finset.prod_erase_mul (Finset.univ : Finset (Finset (Fin T.d))) f hempty').symm
      _ = h y * ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅, f ω := by
        rw [show f ∅ = h y by simp [f, Finset.sum_empty]]
        ring
      _ = _ := by simp [f]
  have hshift (p : Fin T.q → ℕ) (y : ℤ) :
      shiftAverage (Fin T.d) (T.length S l J0 N p) (fun u =>
          ∏ ω : Finset (Fin T.d),
            h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) =
        h y * shortShift p y := by
    let L := T.length S l J0 N p
    let shifts := Fintype.piFinset (fun _ : Fin T.d => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
    have hsum :
        (∑ u ∈ shifts, ∏ ω : Finset (Fin T.d),
            h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) =
          h y * ∑ u ∈ shifts, ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
            h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) := by
      calc
        _ = ∑ u ∈ shifts, h y * ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
              h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0)) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hvertex p y u
        _ = _ := (Finset.mul_sum shifts (fun u =>
          ∏ ω ∈ (Finset.univ : Finset (Finset (Fin T.d))).erase ∅,
            h (y + (T.modulus S N p : ℤ) * ∑ j ∈ ω, ((u j 1 : ℤ) - u j 0))) (h y)).symm
    unfold shortShift
    unfold shiftAverage
    rw [hsum]
    have hcard : 2 * Fintype.card (Fin T.d) = Fintype.card (Fin T.d) * 2 := by omega
    rw [hcard]
    ring
  have hdual (y : ℤ) : dualTest MS B T l J0 N I y =
      prob⁻¹ * ∑' p : Fin T.q → ℕ,
        gapSlotMass S l N p * (if G p then shortShift p y else 0) := by
    simp [dualTest, goodSlotAverage, I, prob, G, S, shortShift]
  change prob⁻¹ * ∑' p : Fin T.q → ℕ,
      gapSlotMass S l N p * (if G p then ∑' y : ℤ, μ y * fullShift p y else 0) =
    ∑' y : ℤ, μ y * (h y * dualTest MS B T l J0 N I y)
  simp_rw [hdual]
  have hinner (p : Fin T.q → ℕ) :
      (if G p then ∑' y : ℤ, μ y * fullShift p y else 0) =
        ∑' y : ℤ, μ y * (h y * (if G p then shortShift p y else 0)) := by
    by_cases hp : G p
    · simp [hp]
      apply tsum_congr
      intro y
      simpa [fullShift] using congrArg (fun z : ℝ => μ y * z) (hshift p y)
    · simp [hp]
  have hpull (y : ℤ) :
      (∑' p : Fin T.q → ℕ, gapSlotMass S l N p *
          (h y * (if G p then shortShift p y else 0))) =
        h y * ∑' p : Fin T.q → ℕ,
          gapSlotMass S l N p * (if G p then shortShift p y else 0) := by
    calc
      _ = ∑' p : Fin T.q → ℕ,
          h y * (gapSlotMass S l N p * (if G p then shortShift p y else 0)) := by
            apply tsum_congr
            intro p
            ring
      _ = _ := tsum_mul_left
  calc
    prob⁻¹ * ∑' p : Fin T.q → ℕ,
        gapSlotMass S l N p * (if G p then ∑' y : ℤ, μ y * fullShift p y else 0) =
      prob⁻¹ * ∑' p : Fin T.q → ℕ,
        gapSlotMass S l N p * ∑' y : ℤ,
          μ y * (h y * (if G p then shortShift p y else 0)) := by
            congr 1
            apply tsum_congr
            intro p
            rw [hinner p]
    _ = prob⁻¹ * ∑' y : ℤ,
        μ y * (h y * ∑' p : Fin T.q → ℕ,
          gapSlotMass S l N p * (if G p then shortShift p y else 0)) := by
            calc
              _ = prob⁻¹ * ∑' y : ℤ,
                  μ y * ∑' p : Fin T.q → ℕ, gapSlotMass S l N p *
                    (h y * (if G p then shortShift p y else 0)) := by
                  congr 1
                  simpa [gapSlotMass] using independentPrimePool_harmonic_tsum_comm
                    (fun _ : Fin T.q => (S.primeStage.pool N l).lower)
                    (fun _ => (S.primeStage.pool N l).upper)
                    (MS.core.parameters.X N B.1) (primorial (N + 1))
                    (fun p y => h y * (if G p then shortShift p y else 0))
              _ = _ := by
                  congr 1
                  apply tsum_congr
                  intro y
                  rw [hpull y]
    _ = ∑' y : ℤ, μ y * (h y *
        (prob⁻¹ * ∑' p : Fin T.q → ℕ,
          gapSlotMass S l N p * (if G p then shortShift p y else 0))) := by
            calc
              _ = ∑' y : ℤ, prob⁻¹ *
                  (μ y * (h y * ∑' p : Fin T.q → ℕ,
                    gapSlotMass S l N p * (if G p then shortShift p y else 0))) :=
                    tsum_mul_left.symm
              _ = _ := by
                apply tsum_congr
                intro y
                ring

/-- For an allowed type the good event has probability tending to one (04:378–384, from
`MasterScalePrimeStage.zero_and_repeat_probability`, `actual_small_prime_exception` and the
pool mass, marginalized from the master `s` slots to the type's `q` slots). -/
theorem good_probability_tendsto_one (MS : MasterScales K As sl Dm) (T : CubeTemplate)
    (hT : Allowed Dm T) (l : Fin K) :
    Tendsto (fun N => gapSlotProbability (corrScales MS) l N (T.Good (corrScales MS) l N))
      atTop (𝓝 1) := by
  classical
  rcases hT with ⟨ι, hListed⟩
  let S := corrScales MS
  let poolLo : ℕ → ℕ := fun N => (S.primeStage.pool N l).lower
  let poolHi : ℕ → ℕ := fun N => (S.primeStage.pool N l).upper
  let failSeq : ℕ → ℝ := fun N =>
    independentPrimePoolProbability (fun _ : Fin T.q => poolLo N) (fun _ => poolHi N)
      (fun p => ¬ T.Good S l N p)
  let zeroSeq : ℕ → ℝ := fun N =>
    independentPrimePoolProbability (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
      (FromArithmetic.polynomialZeroOrRepeated Dm)
  let smallSeq : ℕ → ℝ := fun N =>
    independentPrimePoolProbability (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
      (FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N))
  let badSeq : ℕ → ℝ := fun N =>
    independentPrimePoolProbability (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
      (fun p => FromArithmetic.polynomialZeroOrRepeated Dm p ∨
        FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N) p)
  have hpoolPos : ∀ᶠ N : ℕ in atTop, 0 < primePoolMass (poolLo N) (poolHi N) := by
    have hratio := S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)
    filter_upwards [hratio.eventually_ge_atTop 1] with N hN
    have hV : 0 < (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
      unfold FromArithmetic.masterScaleV
      positivity
    have hratio' : (1 : ℝ) ≤
        primePoolMass (poolLo N) (poolHi N) / (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
      simpa [poolLo, poolHi, pow_one] using hN
    have hle : (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ≤
        primePoolMass (poolLo N) (poolHi N) := by
      have hm := (le_div_iff₀ hV).mp hratio'
      nlinarith
    exact lt_of_lt_of_le hV hle
  have hzeroWeighted : Tendsto
      (fun N => zeroSeq N * (FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) atTop (𝓝 0) := by
    simpa [zeroSeq, poolLo, poolHi, pow_one] using
      (S.primeStage.zero_and_repeat_probability l) 1 (by norm_num)
  have hzeroNonneg : ∀ N, 0 ≤ zeroSeq N := by
    intro N
    exact independentPrimePoolProbability_nonneg
      (fun _ : Fin sl => poolLo N) (fun _ => poolHi N) (FromArithmetic.polynomialZeroOrRepeated Dm)
  have hzero : Tendsto zeroSeq atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzeroWeighted
    · exact Filter.Eventually.of_forall hzeroNonneg
    · filter_upwards with N
      have hVnat : 1 ≤ FromArithmetic.masterScaleV S.core.parameters N l := by
        unfold FromArithmetic.masterScaleV
        omega
      have hV : (1 : ℝ) ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
        exact_mod_cast hVnat
      have hmul : 0 ≤ zeroSeq N * ((FromArithmetic.masterScaleV S.core.parameters N l : ℝ) - 1) :=
        mul_nonneg (hzeroNonneg N) (sub_nonneg.mpr hV)
      nlinarith
  have hsmall : Tendsto smallSeq atTop (𝓝 0) := by
    simpa [smallSeq, poolLo, poolHi] using S.primeStage.actual_small_prime_exception l
  have hbadBound : ∀ N, badSeq N ≤ zeroSeq N + smallSeq N := by
    intro N
    simpa [badSeq, zeroSeq, smallSeq, poolLo, poolHi] using
      independentPrimePoolProbability_union_le
        (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
        (FromArithmetic.polynomialZeroOrRepeated Dm)
        (FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N))
  have hbadNonneg : ∀ N, 0 ≤ badSeq N := by
    intro N
    exact independentPrimePoolProbability_nonneg
      (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
      (fun p => FromArithmetic.polynomialZeroOrRepeated Dm p ∨
        FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N) p)
  have hbad : Tendsto badSeq atTop (𝓝 0) := by
    simpa only [zero_add] using
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := badSeq)
        tendsto_const_nhds (hzero.add hsmall)
        (Filter.Eventually.of_forall (fun N => by simpa using hbadNonneg N))
        (Filter.Eventually.of_forall hbadBound))
  have hfailBound : ∀ᶠ N : ℕ in atTop, failSeq N ≤ badSeq N := by
    filter_upwards [hpoolPos] with N hpos
    let E : (Fin T.q → ℕ) → Prop := fun p => ¬ T.Good S l N p
    let F : (Fin sl → ℕ) → Prop := fun p =>
      FromArithmetic.polynomialZeroOrRepeated Dm p ∨
        FromArithmetic.primeSmallDivisibilityEvent Dm (N + 1) (S.primeStage.e0 N) p
    change independentPrimePoolProbability (fun _ : Fin T.q => poolLo N) (fun _ => poolHi N) E ≤
      independentPrimePoolProbability (fun _ : Fin sl => poolLo N) (fun _ => poolHi N) F
    rw [independentPrimePoolProbability_iid_marginal
      (poolLo N) (poolHi N) hpos ι E]
    apply independentPrimePoolProbability_mono_of_support
      (fun _ : Fin sl => poolLo N) (fun _ => poolHi N)
      (fun p => E (fun i => p (ι i))) F
    intro p hpMass hfail
    have hslot (j : Fin sl) :
        poolLo N ≤ p j ∧ p j < poolHi N ∧ (p j).Prime := by
      have hlaw : primePoolLaw (poolLo N) (poolHi N) (p j) ≠ 0 := by
        intro hzero
        apply hpMass
        unfold independentPrimePoolMass
        exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
      unfold primePoolLaw at hlaw
      split_ifs at hlaw with h
      · exact h
      · exact False.elim (hlaw rfl)
    let q : Fin T.q → ℕ := fun i => p (ι i)
    have hbadQ :
        FromArithmetic.polynomialZeroOrRepeated T.tests q ∨
          FromArithmetic.primeSmallDivisibilityEvent T.tests (N + 1) (S.primeStage.e0 N) q := by
      by_contra hnot
      have hnZ : ¬ FromArithmetic.polynomialZeroOrRepeated T.tests q := fun hz => hnot (Or.inl hz)
      have hnS : ¬ FromArithmetic.primeSmallDivisibilityEvent T.tests (N + 1) (S.primeStage.e0 N) q :=
        fun hs => hnot (Or.inr hs)
      have hgood : T.Good S l N q := by
        unfold CubeTemplate.Good GoodTuple
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          exact hslot (ι i)
        · intro i j hij
          by_contra hne
          apply hnZ
          exact Or.inr ⟨i, j, hne, hij⟩
        · intro P hP hzero
          apply hnZ
          exact Or.inl ⟨P, hP, hzero⟩
        · intro π hπ hle hdiv
          apply hnS
          exact ⟨π, hπ, hle, T.D, T.D_mem, hdiv⟩
      exact hfail hgood
    have hEval (P : IntegerPolynomial T.q) :
        evalIntegerPolynomial (MvPolynomial.rename ι P) (fun j => (p j : ℤ)) =
          evalIntegerPolynomial P (fun i => (p (ι i) : ℤ)) := by
      simp [evalIntegerPolynomial, MvPolynomial.eval_rename, Function.comp_def]
    rcases hbadQ with hzero | hsmall
    · rcases hzero with hpoly | hrep
      · rcases hpoly with ⟨P, hP, hzero⟩
        left
        left
        exact ⟨MvPolynomial.rename ι P, hListed P hP, by rw [hEval]; exact hzero⟩
      · rcases hrep with ⟨i, j, hij, hEq⟩
        left
        right
        refine ⟨ι i, ι j, ?_, hEq⟩
        intro h
        exact hij (ι.injective h)
    · rcases hsmall with ⟨π, hπ, hle, P, hP, hdiv⟩
      right
      exact ⟨π, hπ, hle, MvPolynomial.rename ι P, hListed P hP, by rw [hEval]; exact hdiv⟩
  have hfailNonneg : ∀ N, 0 ≤ failSeq N := by
    intro N
    exact independentPrimePoolProbability_nonneg
      (fun _ : Fin T.q => poolLo N) (fun _ => poolHi N)
      (fun p => ¬ T.Good S l N p)
  have hfail : Tendsto failSeq atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    · exact Filter.Eventually.of_forall hfailNonneg
    · exact hfailBound
  have hgoodEq :
      (fun N => gapSlotProbability S l N (T.Good S l N)) =ᶠ[atTop]
        (fun N => 1 - failSeq N) := by
    filter_upwards [hpoolPos] with N hpos
    have hsum := independentPrimePoolProbability_add_compl
      (poolLo N) (poolHi N) hpos (T.Good S l N)
    have hsum' : gapSlotProbability S l N (T.Good S l N) + failSeq N = 1 := by
      simpa [failSeq, gapSlotProbability] using hsum
    linarith
  have hlim : Tendsto (fun N => 1 - failSeq N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hfail
  exact hlim.congr' hgoodEq.symm

/-- Clipping a real number to `[-K, K]`. -/
def clip (Kc x : ℝ) : ℝ := max (-Kc) (min Kc x)

end

end HindmanSumsProducts.Prediction
