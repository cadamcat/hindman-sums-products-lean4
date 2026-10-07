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
  sorry

/-- For an allowed type the good event has probability tending to one (04:378–384, from
`MasterScalePrimeStage.zero_and_repeat_probability`, `actual_small_prime_exception` and the
pool mass, marginalized from the master `s` slots to the type's `q` slots). -/
theorem good_probability_tendsto_one (MS : MasterScales K As sl Dm) (T : CubeTemplate)
    (hT : Allowed Dm T) (l : Fin K) :
    Tendsto (fun N => gapSlotProbability (corrScales MS) l N (T.Good (corrScales MS) l N))
      atTop (𝓝 1) := by
  sorry

/-- Clipping a real number to `[-K, K]`. -/
def clip (Kc x : ℝ) : ℝ := max (-Kc) (min Kc x)

end

end HindmanSumsProducts.Prediction
