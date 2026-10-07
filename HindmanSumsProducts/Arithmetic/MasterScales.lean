import HindmanSumsProducts.Arithmetic.Outside
import HindmanSumsProducts.Arithmetic.Sampling
import HindmanSumsProducts.Arithmetic.MasterScales.PadicNullity

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

private theorem master_height_sum (n N : ℕ) (S : Finset (Fin n)) :
    OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (masterHeight n N) S =
      (primorial (N + 1) : ℤ) ^
        ((N + 1) * ∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1)) := by
  simp [OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height,
    masterHeight, Finset.prod_pow_eq_pow_sum, Finset.mul_sum]

private theorem master_weight_sum_univ (n : ℕ) :
    (∑ i ∈ (Finset.univ : Finset (Fin n)), (2 : ℕ) ^ (n - i.val - 1)) = 2 ^ n - 1 := by
  calc
    (∑ i ∈ (Finset.univ : Finset (Fin n)), (2 : ℕ) ^ (n - i.val - 1)) =
        ∑ i : Fin n, (2 : ℕ) ^ (Fin.rev i).val := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Fin.val_rev, Nat.sub_sub]
    _ = ∑ i : Fin n, (2 : ℕ) ^ i.val := by
      simpa only [Fin.revPerm_apply] using
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
          (fun i : Fin n => (2 : ℕ) ^ i.val))
    _ = ∑ i ∈ Finset.range n, (2 : ℕ) ^ i := Fin.sum_univ_eq_sum_range _ _
    _ = 2 ^ n - 1 := sum_pow_two_range n
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
  obtain ⟨P, j, hP, hPT, hTj, hji, hEq⟩ := hS
  let k := P.min' hP
  have hkP : k ∈ P := Finset.min'_mem P hP
  have hkT (t : Fin n) (ht : t ∈ B.2.val) : k < t := hPT k hkP t ht
  have hkj : k < j := by
    obtain ⟨t, ht⟩ := B.2.property.1
    exact (hkT t ht).trans (hTj t ht)
  have hki : k < B.1 := hkj.trans hji
  have hkS : k ∈ S := by rw [hEq]; exact Finset.mem_insert_of_mem hkP
  have hknotB : k ∉ B.set := by
    simp only [OAI.SourceBlocks.Block.set, Finset.mem_insert]
    rintro (hk | hk)
    · exact (ne_of_lt hki) hk
    · exact (lt_irrefl _ (hPT k hkP k hk))
  have hfirst : ∀ i, i < k → (i ∈ S ↔ i ∈ B.set) := by
    intro i hik
    have hiP : i ∉ P := by
      intro hi
      exact (not_le_of_gt hik) (Finset.min'_le P i hi)
    have hijn : i ≠ j := ne_of_lt (hik.trans hkj)
    have hiS : i ∉ S := by rw [hEq]; simp [hijn, hiP]
    have hiB : i ∉ B.set := by
      simp only [OAI.SourceBlocks.Block.set, Finset.mem_insert]
      rintro (rfl | hiT)
      · exact (not_lt_of_ge (le_of_lt hki)) hik
      · exact (not_lt_of_ge (le_of_lt (hkT i hiT))) hik
    exact iff_of_false hiS hiB
  have hsum := binary_subset_weight_separation n S B.set k hkS hknotB hfirst
  have hsum' :
      ∑ i ∈ B.set, (2 : ℕ) ^ (n - i.val - 1) <
        ∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1) := hsum
  let sumB := ∑ i ∈ B.set, (2 : ℕ) ^ (n - i.val - 1)
  let sumS := ∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1)
  let gap := sumS - sumB - 1
  have hgap : 1 ≤ sumS - sumB := by dsimp [sumB, sumS]; omega
  have hgapEq : sumB + (gap + 1) = sumS := by
    dsimp [gap]
    omega
  have hpow : (N + 1) * sumB + (N + 1) + (N + 1) * gap =
      (N + 1) * sumS := by
    calc
      (N + 1) * sumB + (N + 1) + (N + 1) * gap =
          (N + 1) * (sumB + (gap + 1)) := by ring
      _ = (N + 1) * sumS := by rw [hgapEq]
  refine ⟨(primorial (N + 1) : ℤ) ^ ((N + 1) * gap), ?_⟩
  rw [master_height_sum, master_height_sum]
  rw [show (N + 1) * sumS =
    ((N + 1) * sumB + (N + 1)) + (N + 1) * gap by omega]
  rw [pow_add, pow_add]
  ring

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
  let Tu := (C.block u).2.val
  let Td := (C.block d).2.val
  let j := Tu.min' (C.block u).2.property.1
  have hjTu : j ∈ Tu := Finset.min'_mem Tu (C.block u).2.property.1
  have hjgap : j < C.gap := C.tails_before_gap u j hjTu
  have hjpu : j < (C.block u).1 := hjgap.trans (C.pivots_after_gap u)
  have hjpd : j < (C.block d).1 := hjgap.trans (C.pivots_after_gap d)
  have hjnotTd : j ∉ Td := by
    intro hj
    have hlt := C.tails_ordered u d hud j hjTu j hj
    exact (lt_irrefl _ hlt)
  have hjnotBd : j ∉ (C.block d).set := by
    simp only [OAI.SourceBlocks.Block.set, Finset.mem_insert]
    rintro (hj | hj)
    · exact (ne_of_lt hjpd) hj
    · exact hjnotTd hj
  have hfirst : ∀ i, i < j → (i ∈ (C.block u).set ↔ i ∈ (C.block d).set) := by
    intro i hij
    have hiTu : i ∉ Tu := by
      intro hi
      exact (not_le_of_gt hij) (Finset.min'_le Tu i hi)
    have hiTd : i ∉ Td := by
      intro hi
      have hji : j < i := C.tails_ordered u d hud j hjTu i hi
      exact (not_lt_of_ge (le_of_lt hji)) hij
    have hipu : i ≠ (C.block u).1 := ne_of_lt (hij.trans hjpu)
    have hipd : i ≠ (C.block d).1 := ne_of_lt (hij.trans hjpd)
    simp [OAI.SourceBlocks.Block.set, Tu, Td, hiTu, hiTd, hipu, hipd]
  have hsum := binary_subset_weight_separation n (C.block u).set (C.block d).set
    j (Finset.mem_insert_of_mem hjTu) hjnotBd hfirst
  have hsum' :
      ∑ i ∈ (C.block d).set, (2 : ℕ) ^ (n - i.val - 1) <
        ∑ i ∈ (C.block u).set, (2 : ℕ) ^ (n - i.val - 1) := hsum
  let sumD := ∑ i ∈ (C.block d).set, (2 : ℕ) ^ (n - i.val - 1)
  let sumU := ∑ i ∈ (C.block u).set, (2 : ℕ) ^ (n - i.val - 1)
  let k := sumU - sumD
  have hk : 0 < k := by dsimp [k, sumU, sumD]; omega
  have hgapEq : sumD + k = sumU := by
    dsimp [k, sumU, sumD]
    omega
  have hpow : (N + 1) * sumD + (N + 1) * k = (N + 1) * sumU := by
    rw [← Nat.mul_add, hgapEq]
  refine ⟨k, hk, ?_⟩
  rw [master_height_sum, master_height_sum]
  calc
    (primorial (N + 1) : ℤ) ^ ((N + 1) * sumU) =
        (primorial (N + 1) : ℤ) ^ ((N + 1) * sumD + (N + 1) * k) := by rw [hpow]
    _ = (primorial (N + 1) : ℤ) ^ ((N + 1) * sumD) *
        ((primorial (N + 1) : ℤ) ^ (N + 1)) ^ k := by
          rw [pow_add, pow_mul, pow_mul]

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
  classical
  let nums := Aset.image (fun a : ℚ => a.num.natAbs)
  let dens := Aset.image (fun a : ℚ => a.den)
  let K : ℕ := max (nums.sup id) (dens.sup id)
  have hnumBound (a : ℚ) (ha : a ∈ Aset) : a.num.natAbs ≤ K := by
    exact (Finset.le_sup (s := nums) (f := id) (b := a.num.natAbs)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans (le_max_left _ _)
  have hdenBound (a : ℚ) (ha : a ∈ Aset) : a.den ≤ K := by
    exact (Finset.le_sup (s := dens) (f := id) (b := a.den)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)).trans (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (K * K + K + 2)] with N hN
  intro r C a ha
  let W := primorial (N + 1)
  let E (d : Fin r) := (N + 1) *
    ∑ i ∈ (C.block d).set, (2 : ℕ) ^ (n - i.val - 1)
  let q (d : Fin r) : ℚ :=
    (((a d).num * (W ^ E d : ℤ) : ℤ) : ℚ) / (a d).den
  let c : Fin r → ℤ := fun d => (q d).num
  have hsmall (d : Fin r) : (a d).den ≤ N ∧ (a d).num.natAbs ≤ N := by
    have hd := hdenBound (a d) (ha d)
    have hn := hnumBound (a d) (ha d)
    have hK : K ≤ N := by
      calc
        K ≤ K + (K * K + 2) := Nat.le_add_right _ _
        _ = K * K + K + 2 := by ring
        _ ≤ N := hN
    exact ⟨hd.trans hK, hn.trans hK⟩
  have hsumLower (d : Fin r) :
      1 ≤ ∑ i ∈ (C.block d).set, (2 : ℕ) ^ (n - i.val - 1) := by
    have hmem : (C.block d).1 ∈ (C.block d).set :=
      Finset.mem_insert_self _ _
    have hterm : 1 ≤ (2 : ℕ) ^ (n - (C.block d).1.val - 1) :=
      Nat.one_le_pow _ _ (by omega)
    exact le_trans hterm (Finset.single_le_sum
      (f := fun i : Fin n => (2 : ℕ) ^ (n - i.val - 1))
      (by intro i hi; exact Nat.zero_le _) hmem)
  have hEN (d : Fin r) : N ≤ E d := by
    dsimp [E]
    have hmul := Nat.mul_le_mul_left (N + 1) (hsumLower d)
    calc
      N ≤ N + 1 := Nat.le_succ _
      _ ≤ (N + 1) * ∑ i ∈ (C.block d).set, (2 : ℕ) ^ (n - i.val - 1) := by
        simpa using hmul
  have hdenPow (d : Fin r) : (a d).den ∣ W ^ N := by
    apply OAI.IntegerAlignment.fixed_dvd_primorial_pow
      (n := (a d).den) (w := N + 1) (k := N)
    · exact (Rat.den_pos (a d))
    · exact Nat.le_trans (hsmall d).1 (Nat.le_succ _)
    · exact hsmall d |>.1
  have hqden (d : Fin r) : (q d).den = 1 := by
    have hpow : W ^ N ∣ W ^ E d := pow_dvd_pow _ (hEN d)
    have hdenNat : (a d).den ∣ W ^ E d := hdenPow d |>.trans hpow
    have hdenInt : ((a d).den : ℤ) ∣ (W ^ E d : ℤ) :=
      Int.natCast_dvd_natCast.mpr hdenNat
    have hdiv : ((a d).den : ℤ) ∣ (a d).num * (W ^ E d : ℤ) :=
      dvd_mul_of_dvd_right hdenInt _
    dsimp [q]
    exact (Rat.den_div_intCast_eq_one_iff _ _
      (by exact_mod_cast (Nat.ne_of_gt (Rat.den_pos (a d))))).2 hdiv
  have hqInt (d : Fin r) : ((c d : ℤ) : ℚ) = q d :=
    Rat.coe_int_num_of_den_eq_one (hqden d)
  have hqFormula (d : Fin r) :
      q d = ((W : ℚ) ^ E d) * a d := by
    dsimp [q]
    conv_rhs => rw [← Rat.num_div_den (a d)]
    push_cast
    field_simp [Rat.den_pos (a d)]
  have hheightFormula (d : Fin r) :
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) (C.block d).set : ℤ) : ℚ) =
        (W : ℚ) ^ E d := by
    rw [master_height_sum]
    simp [W, E, Finset.mul_sum]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro d
    calc
      (c d : ℚ) = q d := hqInt d
      _ = (W : ℚ) ^ E d * a d := hqFormula d
      _ = ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (masterHeight n N) (C.block d).set : ℤ) : ℚ) * a d := by
            rw [hheightFormula]
  · intro d
    have hpos : 0 < (c d : ℚ) := by
      rw [hqInt, hqFormula]
      have hWpos : 0 < (W : ℚ) := by exact_mod_cast (primorial_pos (N + 1))
      have haPos : 0 < a d := hA (a d) (ha d)
      positivity
    exact_mod_cast hpos
  · intro u d hud
    obtain ⟨k, hk, hratio⟩ := master_chain_height_ratio n N r C u d hud
    let epow := (N + 1) * k - 1
    let den := (a u).den * (a d).num.natAbs
    let qratio : ℚ :=
      (((((W ^ epow : ℕ) : ℤ) * (a u).num * (a d).den : ℤ) : ℚ) /
        (den : ℤ))
    have hEp : N ≤ epow := by
      have hmul : N + 1 ≤ (N + 1) * k := by
        simpa using Nat.mul_le_mul_left (N + 1) hk
      dsimp [epow]
      omega
    have hdenle : den ≤ N := by
      dsimp [den]
      have hu : (a u).den ≤ K := hdenBound (a u) (ha u)
      have hd : (a d).num.natAbs ≤ K := hnumBound (a d) (ha d)
      calc
        (a u).den * (a d).num.natAbs ≤ K * K := Nat.mul_le_mul hu hd
        _ ≤ N := by
          calc
            K * K ≤ K * K + K := Nat.le_add_right _ _
            _ ≤ K * K + K + 2 := Nat.le_add_right _ _
            _ ≤ N := hN
    have hdenPos : 0 < den := by
      have hnumd : 0 < (a d).num := Rat.num_pos.mpr (hA (a d) (ha d))
      have hnumAbs : 0 < (a d).num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnumd)
      dsimp [den]
      exact Nat.mul_pos (Rat.den_pos _) hnumAbs
    have hdenRatio : den ∣ W ^ N := by
      apply OAI.IntegerAlignment.fixed_dvd_primorial_pow
        (n := den) (w := N + 1) (k := N)
      · exact hdenPos
      · exact Nat.le_trans hdenle (Nat.le_succ _)
      · exact hdenle
    have hqratioDen : qratio.den = 1 := by
      have hdenInt : (den : ℤ) ∣ (W ^ epow : ℤ) := by
        exact Int.natCast_dvd_natCast.mpr
          (hdenRatio.trans (pow_dvd_pow _ hEp))
      have hnumDiv : (den : ℤ) ∣
          ((W ^ epow : ℕ) : ℤ) * (a u).num * (a d).den := by
        simpa [mul_assoc] using
          (dvd_mul_of_dvd_left hdenInt ((a u).num * (a d).den))
      dsimp [qratio]
      exact (Rat.den_div_intCast_eq_one_iff _ _ (by
        exact_mod_cast hdenPos.ne')).2 hnumDiv
    have hqratioPos : 0 < qratio := by
      have hposu : 0 < (a u).num := Rat.num_pos.mpr (hA (a u) (ha u))
      have hnumInt : 0 < ((W ^ epow : ℕ) : ℤ) * (a u).num * (a d).den := by
        apply mul_pos
        · apply mul_pos
          · exact_mod_cast (Nat.pow_pos (primorial_pos (N + 1)))
          · exact hposu
        · exact_mod_cast (Rat.den_pos (a d))
      have hnumQ : 0 <
          ((((W ^ epow : ℕ) : ℤ) * (a u).num * (a d).den : ℤ) : ℚ) := by
        exact_mod_cast hnumInt
      have hdenQ : 0 < (den : ℚ) := by exact_mod_cast hdenPos
      change 0 <
        ((((W ^ epow : ℕ) : ℤ) * (a u).num * (a d).den : ℤ) : ℚ) / (den : ℚ)
      exact div_pos hnumQ hdenQ
    let k' := qratio.num.natAbs
    have hk' : (k' : ℚ) = qratio := by
      rw [← Rat.coe_int_num_of_den_eq_one (hqratioDen)]
      have hcast : (k' : ℤ) = qratio.num :=
        Int.natAbs_of_nonneg (le_of_lt (Rat.num_pos.mpr hqratioPos))
      exact_mod_cast hcast
    have hqratioFormula : qratio =
        (W : ℚ) ^ epow * (a u) / (a d) := by
      dsimp [qratio, den]
      have hu : a u = (a u).num / (a u).den := (Rat.num_div_den _).symm
      have hd : a d = (a d).num / (a d).den := (Rat.num_div_den _).symm
      conv_rhs => rw [hu, hd]
      push_cast
      have hdenu : 0 < (a u).den := Rat.den_pos _
      have hdend : 0 < (a d).den := Rat.den_pos _
      have hnumd : 0 < (a d).num := Rat.num_pos.mpr (hA (a d) (ha d))
      have hnumdQ : 0 < ((a d).num : ℚ) := by exact_mod_cast hnumd
      have hdenpos : 0 < den := by dsimp [den]; positivity
      rw [abs_of_pos hnumdQ]
      field_simp [hdenu.ne', hdend.ne', hnumd.ne', hdenpos.ne']
      <;> ring
    have hpowExtract : (W : ℚ) * (W : ℚ) ^ epow =
        ((W : ℚ) ^ (N + 1)) ^ k := by
      calc
        (W : ℚ) * (W : ℚ) ^ epow = (W : ℚ) ^ (epow + 1) := by
          rw [pow_succ]
          ring
        _ = (W : ℚ) ^ ((N + 1) * k) := by
          congr 1
          dsimp [epow]
          omega
        _ = ((W : ℚ) ^ (N + 1)) ^ k :=
          pow_mul (W : ℚ) (N + 1) k
    have hratioQ : (c u : ℚ) =
        (W : ℚ) * (k' : ℚ) * (c d : ℚ) := by
      rw [hqInt, hqInt, hqFormula, hqFormula, hk']
      have hheightQ : (W : ℚ) ^ E u =
          (W : ℚ) ^ E d * ((W : ℚ) ^ (N + 1)) ^ k := by
        rw [← hheightFormula u, ← hheightFormula d]
        exact_mod_cast hratio
      rw [hheightQ, hqratioFormula]
      field_simp [ne_of_gt (hA (a d) (ha d))]
      rw [← hpowExtract]
      ring
    refine ⟨k', ?_⟩
    exact_mod_cast hratioQ

/-- Every product of heights is at most `M` (§3 lines 205–207): `h_S ≤ W^{w(2^n-1)}`. -/
theorem master_height_le_modulus (n N e0 : ℕ) (S : Finset (Fin n)) :
    OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (masterHeight n N) S ≤ (masterModulus n N e0 : ℤ) := by
  rw [master_height_sum]
  have hsum :
      ∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1) ≤ 2 ^ n - 1 := by
    calc
      ∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin n)), (2 : ℕ) ^ (n - i.val - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intro i hi hni; exact Nat.zero_le _)
      _ = 2 ^ n - 1 := master_weight_sum_univ n
  have hexp : (N + 1) * (∑ i ∈ S, (2 : ℕ) ^ (n - i.val - 1)) ≤
      e0 + 1 + (N + 1) * 2 ^ n := by
    calc
      _ ≤ (N + 1) * (2 ^ n - 1) := Nat.mul_le_mul_left _ hsum
      _ ≤ (N + 1) * 2 ^ n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ e0 + 1 + (N + 1) * 2 ^ n := Nat.le_add_left _ _
  have hw : (1 : ℤ) ≤ primorial (N + 1) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (primorial_pos (N + 1)).ne')
  have hpow := pow_le_pow_right₀ hw hexp
  simpa [masterModulus, Nat.cast_pow] using hpow

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
  classical
  let nums := Aset.image (fun a : ℚ => a.num.natAbs)
  let K : ℕ := nums.sup id
  have hnumBound (a : ℚ) (ha : a ∈ Aset) : a.num.natAbs ≤ K :=
    Finset.le_sup (s := nums) (f := id) (b := a.num.natAbs)
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  filter_upwards [eventually_ge_atTop (K + 1)] with N hN
  intro r chain a ha c hc d
  let W := primorial (N + 1)
  let E := (N + 1) *
    ∑ i ∈ (chain.block d).set, (2 : ℕ) ^ (n - i.val - 1)
  have hnumSmall : (a d).num.natAbs ≤ N := by
    exact (hnumBound (a d) (ha d)).trans (by omega)
  have hnumPos : 0 < (a d).num := Rat.num_pos.mpr (hA (a d) (ha d))
  have hnumAbsPos : 0 < (a d).num.natAbs :=
    Int.natAbs_pos.mpr (ne_of_gt hnumPos)
  have hnumPow : (a d).num.natAbs ∣ W ^ N := by
    apply OAI.IntegerAlignment.fixed_dvd_primorial_pow
      (n := (a d).num.natAbs) (w := N + 1) (k := N)
    · exact hnumAbsPos
    · exact Nat.le_trans hnumSmall (Nat.le_succ _)
    · exact hnumSmall
  have hnumPowW : (a d).num ∣ (W ^ (N + 1) : ℤ) := by
    have hcast : ((a d).num.natAbs : ℤ) ∣ (W ^ (N + 1) : ℤ) := by
      exact Int.natCast_dvd_natCast.mpr
        (hnumPow.trans (pow_dvd_pow _ (Nat.le_succ N)))
    rw [Int.natAbs_of_nonneg (le_of_lt hnumPos)] at hcast
    exact hcast
  have hsum :
      ∑ i ∈ (chain.block d).set, (2 : ℕ) ^ (n - i.val - 1) ≤ 2 ^ n - 1 := by
    calc
      ∑ i ∈ (chain.block d).set, (2 : ℕ) ^ (n - i.val - 1) ≤
          ∑ i ∈ (Finset.univ : Finset (Fin n)), (2 : ℕ) ^ (n - i.val - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (by intro i hi hni; exact Nat.zero_le _)
      _ = 2 ^ n - 1 := master_weight_sum_univ n
  have hE : E ≤ (N + 1) * (2 ^ n - 1) := by
    dsimp [E]
    exact Nat.mul_le_mul_left _ hsum
  have hEplus : E + (N + 1) ≤ (N + 1) * 2 ^ n := by
    calc
      E + (N + 1) ≤ (N + 1) * (2 ^ n - 1) + (N + 1) :=
        Nat.add_le_add_right hE _
      _ = (N + 1) * (2 ^ n - 1) + (N + 1) * 1 := by simp
      _ = (N + 1) * ((2 ^ n - 1) + 1) := (Nat.mul_add _ _ _).symm
      _ = (N + 1) * 2 ^ n := by
        rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
  have hheight :
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (masterHeight n N) (chain.block d).set : ℤ) : ℚ) = (W : ℚ) ^ E := by
    rw [master_height_sum]
    simp [W, E, Finset.mul_sum]
  have hcMulQ : (c d : ℚ) * (a d).den =
      (a d).num * (W : ℚ) ^ E := by
    calc
      (c d : ℚ) * (a d).den =
          ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (masterHeight n N) (chain.block d).set : ℤ) : ℚ) * a d * (a d).den := by
              rw [hc d]
      _ = (W : ℚ) ^ E * (a d) * (a d).den := by rw [hheight]
      _ = (W : ℚ) ^ E * (a d).num := by
        have haDen : a d * (a d).den = (a d).num := by
          calc
            a d * (a d).den =
                ((a d).num : ℚ) / (a d).den * (a d).den := by
                  conv_lhs => arg 1; rw [← Rat.num_div_den (a d)]
            _ = (a d).num := by field_simp [Rat.den_pos (a d)]
        calc
          (W : ℚ) ^ E * a d * (a d).den =
              (W : ℚ) ^ E * (a d * (a d).den) := by ring
          _ = (W : ℚ) ^ E * (a d).num := by rw [haDen]
      _ = (a d).num * (W : ℚ) ^ E := by ring
  have hcMul : c d * (a d).den = (a d).num * (W ^ E : ℤ) := by
    exact_mod_cast hcMulQ
  have hcdvd : c d ∣ (W ^ E : ℤ) * (a d).num := by
    refine ⟨(a d).den, ?_⟩
    rw [hcMul]
    ring
  have htail : (W ^ E : ℤ) * (a d).num ∣ (W ^ (E + (N + 1)) : ℤ) := by
    have hmul := mul_dvd_mul_left (W ^ E : ℤ) hnumPowW
    simpa [pow_add] using hmul
  have hcPow : c d ∣ (W ^ (E + (N + 1)) : ℤ) := hcdvd.trans htail
  have hscaled := mul_dvd_mul_left
    ((W ^ (e0 N + 1) : ℕ) : ℤ) hcPow
  have hexp : e0 N + 1 + (E + (N + 1)) ≤
      e0 N + 1 + (N + 1) * 2 ^ n := by
    exact Nat.add_le_add_left hEplus _
  have hpowdiv := pow_dvd_pow (W : ℤ) hexp
  have hfinal : ((W ^ (e0 N + 1) : ℕ) : ℤ) * c d ∣
      (W : ℤ) ^ (e0 N + 1 + (N + 1) * 2 ^ n) := by
    have hscaled' : ((W ^ (e0 N + 1) : ℕ) : ℤ) * c d ∣
        (W : ℤ) ^ (e0 N + 1) * (W : ℤ) ^ (E + (N + 1)) := by
      simpa [Nat.cast_pow] using hscaled
    have hscaled'' : ((W ^ (e0 N + 1) : ℕ) : ℤ) * c d ∣
        (W : ℤ) ^ (e0 N + 1 + (E + (N + 1))) := by
      simpa [pow_add, Nat.cast_pow] using hscaled'
    exact hscaled''.trans hpowdiv
  simpa [masterModulus, W, Nat.cast_pow] using hfinal

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
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let C : ℝ := (p : ℝ) / ((p - 1 : ℕ) : ℝ)
  have hp2 : 2 ≤ p := hp.two_le
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (by exact_mod_cast hp.pos) (by exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt))
  have hsmall : Tendsto
      (fun e => (masterPadicProductMeasure p m).real
        (masterPadicDivisibilitySet p e Q)) atTop (𝓝 0) :=
    masterPadicDivisibilitySet_real_tendsto_zero p Q hQ
  have hscaled : Tendsto
      (fun e => C ^ m * (masterPadicProductMeasure p m).real
        (masterPadicDivisibilitySet p e Q)) atTop (𝓝 0) := by
    simpa [mul_comm] using hsmall.const_mul (C ^ m)
  have hbound : ∀ᶠ e : ℕ in atTop,
      uniformUnitTupleProbability (p ^ e) m
        (fun x => ((p ^ e : ℕ) : ℤ) ∣
          evalIntegerPolynomial Q (fun i => ((x i).val : ℤ))) ≤
        C ^ m * (masterPadicProductMeasure p m).real
          (masterPadicDivisibilitySet p e Q) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun e he => he⟩] with e he
    have htot : Nat.totient (p ^ e) = p ^ (e - 1) * (p - 1) :=
      Nat.totient_prime_pow hp (Nat.pos_of_ne_zero (by omega))
    have hexp : p ^ e = p ^ (e - 1) * p := by
      calc
        p ^ e = p ^ ((e - 1) + 1) := by congr 1; omega
        _ = p ^ (e - 1) * p := by rw [pow_succ]
    have hpcast : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpminus : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hp.one_lt))
    have hratio : ((p ^ e : ℕ) : ℝ) / (Nat.totient (p ^ e) : ℝ) = C := by
      dsimp [C]
      rw [htot, hexp]
      push_cast
      field_simp [hpcast, hpminus]
      <;> ring
    have hratioPow : ((p ^ e : ℕ) : ℝ) ^ m /
        (Nat.totient (p ^ e) : ℝ) ^ m = C ^ m := by
      rw [← div_pow, hratio]
    have hprob := masterUniformUnitProbability_le p e m Q
    change uniformUnitTupleProbability (p ^ e) m
      (fun x => ((p ^ e : ℕ) : ℤ) ∣
        evalIntegerPolynomial Q (fun i => ((x i).val : ℤ))) ≤ _ at hprob
    rw [hratioPow] at hprob
    exact hprob
  have hnonneg (e : ℕ) : 0 ≤ uniformUnitTupleProbability (p ^ e) m
      (fun x => ((p ^ e : ℕ) : ℤ) ∣
        evalIntegerPolynomial Q (fun i => ((x i).val : ℤ))) := by
    unfold uniformUnitTupleProbability
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · unfold uniformUnitTupleMass
      split_ifs <;> positivity
    · split_ifs <;> norm_num
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound hscaled

/-! ### Item (3): prime pools (§3 lines 220–238, 283–294, 304–315) -/

private lemma probability_law_summable (μ : ℕ → ℝ)
    (hsum : ∑' x, μ x = 1) : Summable μ := by
  by_contra hnot
  rw [tsum_eq_zero_of_not_summable hnot] at hsum
  norm_num at hsum

private theorem product_weight_probability {m : ℕ} (μ : Fin m → ℕ → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x) (hsum : ∀ i, ∑' x, μ i x = 1) :
    Summable (fun x : Fin m → ℕ => ∏ i, μ i (x i)) ∧
      ∑' x : Fin m → ℕ, ∏ i, μ i (x i) = 1 := by
  classical
  induction m with
  | zero =>
      letI : Unique (Fin 0 → ℕ) := {
        default := fun i => Fin.elim0 i
        uniq := by intro x; funext i; exact Fin.elim0 i }
      constructor
      · apply summable_of_ne_finset_zero (s := {default})
        intro x hx
        have hx' : x = default := Subsingleton.elim _ _
        subst x
        simpa using hx
      · rw [tsum_eq_single (default : Fin 0 → ℕ) (by
          intro x hx
          exact False.elim (hx (Subsingleton.elim _ _)))]
        simp
  | succ m ih =>
      let ν : Fin m → ℕ → ℝ := fun i x => μ i.succ x
      have htail := ih ν (by intro i x; exact hμ i.succ x)
        (by intro i; exact hsum i.succ)
      have hzero : Summable (μ 0) :=
        probability_law_summable (μ 0) (hsum 0)
      let e : (ℕ × (Fin m → ℕ)) ≃ (Fin (m + 1) → ℕ) :=
        Fin.consEquiv (fun _ : Fin (m + 1) => ℕ)
      let wt : (Fin m → ℕ) → ℝ := fun x => ∏ i, ν i (x i)
      have hwt_nonneg (x : Fin m → ℕ) : 0 ≤ wt x := by
        dsimp [wt]
        exact Finset.prod_nonneg (by intro i hi; exact hμ i.succ (x i))
      have hpair : Summable (fun z : ℕ × (Fin m → ℕ) => μ 0 z.1 * wt z.2) :=
        hzero.mul_of_nonneg htail.1 (fun x => hμ 0 x) hwt_nonneg
      have hsection (x : ℕ) :
          Summable (fun y : Fin m → ℕ => μ 0 x * wt y) :=
        htail.1.mul_left _
      have hfull : Summable (fun x : Fin (m + 1) → ℕ => ∏ i, μ i (x i)) := by
        have hc := hpair.comp_injective e.symm.injective
        apply hc.congr
        intro x
        have heq := (Fin.prod_univ_succ
          (fun i : Fin (m + 1) => μ i (e (e.symm x) i)))
        simpa [e, wt, ν] using heq.symm
      have hsumFull :
          ∑' x : Fin (m + 1) → ℕ, ∏ i, μ i (x i) = 1 := by
        calc
          _ = ∑' z : ℕ × (Fin m → ℕ), ∏ i, μ i (e z i) := (e.tsum_eq _).symm
          _ = ∑' z : ℕ × (Fin m → ℕ), μ 0 z.1 * wt z.2 := by
            apply tsum_congr
            intro z
            simp [e, wt, ν, Fin.prod_univ_succ]
          _ = ∑' x : ℕ, ∑' y : Fin m → ℕ, μ 0 x * wt y :=
            hpair.tsum_prod' hsection
          _ = (∑' x : ℕ, μ 0 x) * (∑' y : Fin m → ℕ, wt y) := by
            calc
              _ = ∑' x : ℕ, μ 0 x * (∑' y : Fin m → ℕ, wt y) := by
                apply tsum_congr
                intro x
                exact htail.1.tsum_mul_left _
              _ = _ := hzero.tsum_mul_right _
          _ = 1 := by simp [wt, ν, hsum, htail.2]
      exact ⟨hfull, hsumFull⟩

private theorem polynomial_root_mass_bound (f : Polynomial ℤ) (hf : f ≠ 0)
    (μ : ℕ → ℝ) (a : ℝ) (hμ : ∀ x, 0 ≤ μ x) (hmax : ∀ x, μ x ≤ a) :
    ∑' x : ℕ, μ x * (if f.eval (x : ℤ) = 0 then (1 : ℝ) else 0) ≤
      (f.natDegree : ℝ) * a := by
  classical
  let rootsZ := f.roots.toFinset.filter (fun z : ℤ => 0 ≤ z)
  let rootsN := rootsZ.image Int.toNat
  have hrootZ (z : ℤ) : z ∈ f.roots.toFinset ↔ f.eval z = 0 := by
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hf, Polynomial.IsRoot]
  have hroots (x : ℕ) : x ∈ rootsN ↔ f.eval (x : ℤ) = 0 := by
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, hzx⟩
      have hz0 := (hrootZ z).mp (Finset.mem_filter.mp hz).1
      have hzn := (Finset.mem_filter.mp hz).2
      have hcast : (x : ℤ) = z := by
        have h := congrArg (fun t : ℕ => (t : ℤ)) hzx
        rw [Int.toNat_of_nonneg hzn] at h
        exact h.symm
      simpa [hcast] using hz0
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨(x : ℤ), ?_, by simp⟩
      apply Finset.mem_filter.mpr
      exact ⟨(hrootZ _).mpr hx, by positivity⟩
  have hcard : rootsN.card ≤ f.natDegree := by
    calc
      rootsN.card ≤ rootsZ.card := Finset.card_image_le
      _ ≤ f.roots.toFinset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := f.card_roots'
  have hzero (x : ℕ) (hx : x ∉ rootsN) :
      μ x * (if f.eval (x : ℤ) = 0 then (1 : ℝ) else 0) = 0 := by
    by_cases he : f.eval (x : ℤ) = 0
    · exact (hx ((hroots x).2 he)).elim
    · simp [he]
  rw [tsum_eq_sum hzero]
  calc
    (∑ x ∈ rootsN, μ x * (if f.eval (x : ℤ) = 0 then (1 : ℝ) else 0)) ≤
        ∑ x ∈ rootsN, a := by
      apply Finset.sum_le_sum
      intro x hx
      rw [if_pos ((hroots x).1 hx), mul_one]
      exact hmax x
    _ = (rootsN.card : ℝ) * a := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (f.natDegree : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (le_trans (hμ 0) (hmax 0))

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
  classical
  induction m with
  | zero =>
      have hc : P.coeff 0 ≠ 0 := by
        intro hzero
        apply hP
        rw [P.eq_C_of_isEmpty, hzero]
        simp
      have hdeg : MvPolynomial.totalDegree P = 0 := by
        rw [P.eq_C_of_isEmpty]
        exact MvPolynomial.totalDegree_C _
      have heval (x : Fin 0 → ℕ) :
          evalIntegerPolynomial P (fun i => (x i : ℤ)) ≠ 0 := by
        rw [P.eq_C_of_isEmpty]
        simp [evalIntegerPolynomial, hc]
      rw [hdeg]
      simp [heval]
  | succ m ih =>
      let ν : Fin m → ℕ → ℝ := fun i x => μ i.succ x
      let tailWeight : (Fin m → ℕ) → ℝ := fun x => ∏ i, ν i (x i)
      let p' : Polynomial (MvPolynomial (Fin m) ℤ) := MvPolynomial.finSuccEquiv ℤ m P
      let k : ℕ := p'.natDegree
      let pk : MvPolynomial (Fin m) ℤ := p'.leadingCoeff
      let evalTail (x : Fin m → ℕ) : MvPolynomial (Fin m) ℤ →+* ℤ :=
        MvPolynomial.eval (fun i => (x i : ℤ))
      let px (x : Fin m → ℕ) : Polynomial ℤ := p'.map (evalTail x)
      let inner (x : Fin m → ℕ) : ℝ :=
        ∑' y : ℕ, μ 0 y *
          (if (px x).eval (y : ℤ) = 0 then (1 : ℝ) else 0)
      let fullMass (x : Fin (m + 1) → ℕ) : ℝ :=
        (∏ i, μ i (x i)) *
          (if evalIntegerPolynomial P (fun i => (x i : ℤ)) = 0 then (1 : ℝ) else 0)
      let e : (Fin m → ℕ) × ℕ ≃ (Fin (m + 1) → ℕ) :=
        (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (m + 1) => ℕ))
      have htail := product_weight_probability ν
        (by intro i x; exact hnonneg i.succ x)
        (by intro i; exact hprob i.succ)
      have hzero : Summable (μ 0) := probability_law_summable (μ 0) (hprob 0)
      have ha : 0 ≤ a := le_trans (hnonneg 0 0) (hmax 0 0)
      have hp' : p' ≠ 0 := by
        have hh := (MvPolynomial.finSuccEquiv ℤ m).map_ne_zero_iff.mpr hP
        simpa [p'] using hh
      have hpk : pk ≠ 0 := by
        dsimp [pk]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp'
      have hcoeff : p'.coeff k ≠ 0 := by
        change p'.leadingCoeff ≠ 0
        exact hpk
      have hdegree : pk.totalDegree + k ≤ MvPolynomial.totalDegree P := by
        apply MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k
        simpa [p', k, pk] using hcoeff
      have hweightTotal :
          Summable (fun x : Fin (m + 1) → ℕ => ∏ i, μ i (x i)) ∧
            ∑' x : Fin (m + 1) → ℕ, ∏ i, μ i (x i) = 1 :=
        product_weight_probability μ hnonneg hprob
      have htailNonneg (x : Fin m → ℕ) : 0 ≤ tailWeight x := by
        dsimp [tailWeight, ν]
        exact Finset.prod_nonneg (by intro i hi; exact hnonneg i.succ (x i))
      have hinnerSummable (x : Fin m → ℕ) :
          Summable (fun y : ℕ => μ 0 y *
            (if (px x).eval (y : ℤ) = 0 then (1 : ℝ) else 0)) := by
        refine Summable.of_nonneg_of_le (f := μ 0)
          (g := fun y : ℕ => μ 0 y *
            (if (px x).eval (y : ℤ) = 0 then (1 : ℝ) else 0)) ?_ ?_ hzero
        · intro y
          by_cases hy : (px x).eval (y : ℤ) = 0 <;>
            simp [hy, hnonneg 0 y]
        · intro y
          by_cases hy : (px x).eval (y : ℤ) = 0 <;>
            simp [hy, hnonneg 0 y]
      have hinnerOne (x : Fin m → ℕ) : inner x ≤ 1 := by
        calc
          inner x ≤ ∑' y : ℕ, μ 0 y :=
            (hinnerSummable x).tsum_le_tsum (fun y => by
              by_cases hy : (px x).eval (y : ℤ) = 0 <;>
                simp [hy, hnonneg 0 y]) hzero
          _ = 1 := hprob 0
      have hpxDegree (x : Fin m → ℕ)
          (hgood : evalTail x pk ≠ 0) : (px x).natDegree = k := by
        dsimp [px, k]
        exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero (evalTail x) hgood
      have hpxLeading (x : Fin m → ℕ)
          (hgood : evalTail x pk ≠ 0) :
          (px x).leadingCoeff = evalTail x pk := by
        dsimp [px, pk]
        exact Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero (evalTail x) hgood
      have hpxNonzero (x : Fin m → ℕ)
          (hgood : evalTail x pk ≠ 0) : px x ≠ 0 := by
        apply Polynomial.leadingCoeff_ne_zero.mp
        rw [hpxLeading x hgood]
        exact hgood
      have hinnerGood (x : Fin m → ℕ)
          (hgood : evalTail x pk ≠ 0) : inner x ≤ (k : ℝ) * a := by
        have hroot := polynomial_root_mass_bound (px x) (hpxNonzero x hgood)
          (μ 0) a (hnonneg 0) (hmax 0)
        simpa [inner, hpxDegree x hgood] using hroot
      have hinnerBound (x : Fin m → ℕ) :
          inner x ≤ if evalTail x pk = 0 then 1 else (k : ℝ) * a := by
        by_cases hbad : evalTail x pk = 0
        · simpa [hbad] using hinnerOne x
        · simpa [hbad] using hinnerGood x hbad
      have heval (x : Fin m → ℕ) (y : ℕ) :
          (px x).eval (y : ℤ) =
            evalIntegerPolynomial P (Fin.cases (y : ℤ) (fun i => (x i : ℤ))) := by
        dsimp [px, p', evalIntegerPolynomial, evalTail]
        rw [Polynomial.eval_map]
        calc
          _ = MvPolynomial.eval (fun i => (x i : ℤ))
              (Polynomial.eval (MvPolynomial.C (y : ℤ))
                (MvPolynomial.finSuccEquiv ℤ m P)) := by
                  simpa using (Polynomial.eval₂_at_apply
                    (p := MvPolynomial.finSuccEquiv ℤ m P)
                    (MvPolynomial.eval (fun i => (x i : ℤ))) (MvPolynomial.C (y : ℤ)))
          _ = MvPolynomial.eval (Fin.cases (y : ℤ) (fun i => (x i : ℤ))) P :=
            by simpa using (MvPolynomial.eval_polynomial_eval_finSuccEquiv
              (x := fun i => (x i : ℤ)) P (MvPolynomial.C (y : ℤ)))
      have hinnerSummable' (x : Fin m → ℕ) :
          Summable (fun y : ℕ => μ 0 y *
            (if evalTail x pk = 0 then (1 : ℝ) else 0)) := by
        apply Summable.of_nonneg_of_le (f := μ 0)
          (g := fun y : ℕ => μ 0 y * (if evalTail x pk = 0 then (1 : ℝ) else 0))
        · intro y
          by_cases hy : evalTail x pk = 0 <;> simp [hy, hnonneg 0 y]
        · intro y
          by_cases hy : evalTail x pk = 0 <;> simp [hy, hnonneg 0 y]
        · exact hzero
      have hinnerOne' (x : Fin m → ℕ) :
          (∑' y : ℕ, μ 0 y * (if evalTail x pk = 0 then (1 : ℝ) else 0)) ≤ 1 := by
        calc
          _ ≤ ∑' y : ℕ, μ 0 y :=
            (hinnerSummable' x).tsum_le_tsum (fun y => by
              by_cases hy : evalTail x pk = 0 <;> simp [hy, hnonneg 0 y]) hzero
          _ = 1 := hprob 0
      let badTerm : (Fin m → ℕ) → ℝ := fun x =>
        tailWeight x * (if evalTail x pk = 0 then (1 : ℝ) else 0)
      let goodTerm : (Fin m → ℕ) → ℝ := fun x =>
        tailWeight x * (if evalTail x pk = 0 then (0 : ℝ) else 1)
      have hbadSummable : Summable badTerm := by
        apply Summable.of_nonneg_of_le (f := tailWeight) (g := badTerm)
        · intro x
          dsimp [badTerm]
          exact mul_nonneg (htailNonneg x) (by split_ifs <;> norm_num)
        · intro x
          dsimp [badTerm]
          by_cases hx : evalTail x pk = 0 <;> simp [hx, htailNonneg x]
        · exact htail.1
      have hgoodSummable : Summable goodTerm := by
        apply Summable.of_nonneg_of_le (f := tailWeight) (g := goodTerm)
        · intro x
          dsimp [goodTerm]
          exact mul_nonneg (htailNonneg x) (by split_ifs <;> norm_num)
        · intro x
          dsimp [goodTerm]
          by_cases hx : evalTail x pk = 0 <;> simp [hx, htailNonneg x]
        · exact htail.1
      have hbadProb : ∑' x : Fin m → ℕ, badTerm x ≤
          (MvPolynomial.totalDegree pk : ℝ) * a := by
        have h := ih pk hpk ν
          (by intro i x; exact hnonneg i.succ x)
          (by intro i x; exact hmax i.succ x)
          (by intro i; exact hprob i.succ)
        change (∑' x : Fin m → ℕ, (∏ i, ν i (x i)) *
          (if evalTail x pk = 0 then (1 : ℝ) else 0)) ≤ _
        exact h
      have hgoodProb : ∑' x : Fin m → ℕ, goodTerm x ≤ 1 := by
        calc
          _ ≤ ∑' x : Fin m → ℕ, tailWeight x :=
            hgoodSummable.tsum_le_tsum (by
              intro x
              by_cases hx : evalTail x pk = 0
              · simp [goodTerm, hx, htailNonneg x]
              · simp [goodTerm, hx])
              htail.1
          _ = 1 := htail.2
      have hinnerEvent (x : Fin m → ℕ) : inner x ≤
          (if evalTail x pk = 0 then 1 else (k : ℝ) * a) := by
        by_cases hbad : evalTail x pk = 0
        · simpa [inner, hbad] using hinnerOne x
        · have hroot := polynomial_root_mass_bound (px x) (hpxNonzero x hbad)
            (μ 0) a (hnonneg 0) (hmax 0)
          simpa [inner, hbad, hpxDegree x hbad] using hroot
      have hEqFull (x : Fin m → ℕ) (y : ℕ) :
          fullMass (e (x, y)) = tailWeight x *
            (μ 0 y * (if (px x).eval (y : ℤ) = 0 then (1 : ℝ) else 0)) := by
        have he : e (x, y) = Fin.cons (α := fun _ : Fin (m + 1) => ℕ) y x := rfl
        have hfun : (fun i : Fin (m + 1) =>
            ((Fin.cons (α := fun _ : Fin (m + 1) => ℕ) y x i : ℕ) : ℤ)) =
            Fin.cases (y : ℤ) (fun i => (x i : ℤ)) := by
          funext i
          change ((Fin.cases y x i : ℕ) : ℤ) = _
          cases i using Fin.cases <;> rfl
        simp [fullMass, he, hfun, tailWeight, ν, Fin.prod_univ_succ, heval,
          mul_assoc, mul_comm, mul_left_comm]
      have htotal :
          (∑' x : Fin (m + 1) → ℕ, fullMass x) =
            ∑' x : Fin m → ℕ, tailWeight x * inner x := by
        calc
          _ = ∑' z : (Fin m → ℕ) × ℕ, fullMass (e z) := (e.tsum_eq fullMass).symm
          _ = ∑' x : Fin m → ℕ, ∑' y : ℕ, fullMass (e (x, y)) := by
            have hpair : Summable (fun z : (Fin m → ℕ) × ℕ => fullMass (e z)) := by
              apply Summable.of_nonneg_of_le
                (f := fun z => ∏ i, μ i (e z i))
                (g := fun z => fullMass (e z))
              · intro z
                exact mul_nonneg
                  (Finset.prod_nonneg (by intro i hi; exact hnonneg i (e z i)))
                  (by split_ifs <;> norm_num)
              · intro z
                dsimp [fullMass]
                have hprod : 0 ≤ ∏ i, μ i (e z i) :=
                  Finset.prod_nonneg (by intro i hi; exact hnonneg i (e z i))
                split_ifs <;> simp [hprod]
              · exact hweightTotal.1.comp_injective e.injective
            have hsection (x : Fin m → ℕ) :
                Summable (fun y : ℕ => fullMass (e (x, y))) := by
              apply Summable.of_nonneg_of_le
                (f := fun y : ℕ => tailWeight x * μ 0 y)
                (g := fun y : ℕ => fullMass (e (x, y)))
              · intro y
                rw [hEqFull]
                exact mul_nonneg (htailNonneg x)
                  (mul_nonneg (hnonneg 0 y) (by split_ifs <;> norm_num))
              · intro y
                rw [hEqFull]
                by_cases hy : (px x).eval (y : ℤ) = 0
                · simp [hy]
                · simp [hy]
                  exact mul_nonneg (htailNonneg x) (hnonneg 0 y)
              · exact hzero.mul_left (tailWeight x)
            exact hpair.tsum_prod' hsection
          _ = ∑' x : Fin m → ℕ, tailWeight x * inner x := by
            apply tsum_congr
            intro x
            calc
              _ = ∑' y : ℕ, tailWeight x *
                    (μ 0 y * (if (px x).eval (y : ℤ) = 0 then (1 : ℝ) else 0)) := by
                  apply tsum_congr
                  intro y
                  exact hEqFull x y
              _ = _ := (hinnerSummable x).tsum_mul_left (tailWeight x)
      change ∑' x : Fin (m + 1) → ℕ, fullMass x ≤
        (MvPolynomial.totalDegree P : ℝ) * a
      rw [htotal]
      let c : ℝ := (k : ℝ) * a
      have hc : 0 ≤ c := mul_nonneg (by positivity) ha
      have hscaledGood : Summable (fun x => c * goodTerm x) :=
        hgoodSummable.mul_left c
      have hpoint (x : Fin m → ℕ) : tailWeight x * inner x ≤
          badTerm x + c * goodTerm x := by
        by_cases hbad : evalTail x pk = 0
        · have hi := hinnerOne x
          simpa [badTerm, goodTerm, c, evalIntegerPolynomial, evalTail, hbad] using
            (mul_le_mul_of_nonneg_left hi (htailNonneg x))
        · have hi := hinnerGood x hbad
          simp [badTerm, goodTerm, c, evalIntegerPolynomial, evalTail, hbad]
          calc
            tailWeight x * inner x ≤ tailWeight x * ((k : ℝ) * a) :=
              mul_le_mul_of_nonneg_left hi (htailNonneg x)
            _ = c * tailWeight x := by dsimp [c]; ring
      calc
        (∑' x : Fin m → ℕ, tailWeight x * inner x) ≤
            ∑' x : Fin m → ℕ, (badTerm x + c * goodTerm x) :=
          (by
            have hf : Summable (fun x : Fin m → ℕ => tailWeight x * inner x) := by
              apply Summable.of_nonneg_of_le (f := tailWeight)
                (g := fun x => tailWeight x * inner x)
              · intro x
                have hi : 0 ≤ inner x := by
                  apply tsum_nonneg
                  intro y
                  by_cases hy : (px x).eval (y : ℤ) = 0 <;>
                    simp [hy, hnonneg 0 y]
                exact mul_nonneg (htailNonneg x) hi
              · intro x
                simpa using mul_le_mul_of_nonneg_left (hinnerOne x) (htailNonneg x)
              · exact htail.1
            exact hf.tsum_le_tsum hpoint (hbadSummable.add hscaledGood))
        _ = (∑' x : Fin m → ℕ, badTerm x) +
              c * (∑' x : Fin m → ℕ, goodTerm x) := by
          rw [Summable.tsum_add hbadSummable hscaledGood]
          rw [hgoodSummable.tsum_mul_left c]
        _ ≤ (MvPolynomial.totalDegree pk : ℝ) * a + (k : ℝ) * a := by
          calc
            (∑' x : Fin m → ℕ, badTerm x) +
                c * (∑' x : Fin m → ℕ, goodTerm x) ≤
                (MvPolynomial.totalDegree pk : ℝ) * a + c :=
              by
                simpa using add_le_add hbadProb
                  (mul_le_mul_of_nonneg_left hgoodProb hc)
            _ = (MvPolynomial.totalDegree pk : ℝ) * a + (k : ℝ) * a := by
              dsimp [c]
        _ ≤ (MvPolynomial.totalDegree P : ℝ) * a := by
          calc
            (MvPolynomial.totalDegree pk : ℝ) * a + (k : ℝ) * a =
                ((MvPolynomial.totalDegree pk + k : ℕ) : ℝ) * a := by
                  rw [Nat.cast_add]
                  ring
            _ ≤ (MvPolynomial.totalDegree P : ℝ) * a :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) ha

/-- CRT transfer of the small-prime exception to actual pool slots (§3 lines 278–280,
313–315): the event depends only on the residues modulo `W^e ∣ Q`; uniform units modulo `Q`
reduce to uniform units modulo `W^e`, and the `m` independent slots cost at most `m` times
the residue error. -/
private def masterResidue (Q : ℕ) (hQ : 0 < Q) (p : ℕ) : Fin Q :=
  ⟨p % Q, Nat.mod_lt _ hQ⟩

private theorem primePoolLaw_residue_sum (lo hi Q : ℕ) (hQ : 0 < Q) (a : Fin Q) :
    ∑' p : ℕ, primePoolLaw lo hi p *
      (if masterResidue Q hQ p = a then (1 : ℝ) else 0) =
      primePoolResidueLaw lo hi Q a := by
  classical
  let S := (Finset.Ico lo hi).filter Nat.Prime
  have hzero (p : ℕ) (hp : p ∉ S) :
      primePoolLaw lo hi p * (if masterResidue Q hQ p = a then (1 : ℝ) else 0) = 0 := by
    have hcond : ¬ (lo ≤ p ∧ p < hi ∧ p.Prime) := by
      intro h
      apply hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    simp [primePoolLaw, hcond]
  rw [tsum_eq_sum (s := S) hzero]
  have hpoint (p : ℕ) (hp : p ∈ S) :
      primePoolLaw lo hi p * (if masterResidue Q hQ p = a then (1 : ℝ) else 0) =
        (if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi := by
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Ico.mp hp'.1
    have hpcond : lo ≤ p ∧ p < hi ∧ p.Prime := ⟨hpI.1, hpI.2, hp'.2⟩
    have heq : masterResidue Q hQ p = a ↔ p % Q = a.val := by
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simpa [masterResidue] using hv
      · intro h
        exact Fin.ext (by simpa [masterResidue] using h)
    by_cases hres : p % Q = a.val
    · simp [primePoolLaw, hpcond, heq, hres]
    · simp [primePoolLaw, hpcond, heq, hres]
  calc
    (∑ p ∈ S, primePoolLaw lo hi p *
        if masterResidue Q hQ p = a then 1 else 0) =
      ∑ p ∈ S,
        (if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hpoint p hp
    _ = (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
        if p % Q = a.val then 1 / (p : ℝ) else 0) / primePoolMass lo hi := by
          rw [Finset.sum_div]

private theorem primePoolResidueLaw_sum_eq_one (lo hi Q : ℕ) (hQ : 0 < Q)
    (hm : 0 < primePoolMass lo hi) :
    ∑ a : Fin Q, primePoolResidueLaw lo hi Q a = 1 := by
  classical
  let S := (Finset.Ico lo hi).filter Nat.Prime
  have hmassEq : primePoolMass lo hi = ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := rfl
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (∑ a : Fin Q, if p % Q = a.val then (1 : ℝ) / p else 0) = 1 / p := by
    let r := masterResidue Q hQ p
    rw [Finset.sum_eq_single r]
    · simp [r, masterResidue]
    · intro a ha hne
      have hval : p % Q ≠ a.val := by
        intro hv
        apply hne
        apply Fin.ext
        simpa [r, masterResidue] using hv.symm
      simp [hval]
    · simp
  unfold primePoolResidueLaw
  rw [← Finset.sum_div, Finset.sum_comm]
  calc
    (∑ p ∈ S, ∑ a : Fin Q,
        if p % Q = a.val then (1 : ℝ) / p else 0) / primePoolMass lo hi =
      (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) / primePoolMass lo hi := by
        apply congrArg (fun x : ℝ => x / primePoolMass lo hi)
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p hp
    _ = 1 := by
        rw [← hmassEq]
        exact div_self hm.ne'

private theorem primePoolResidueLaw_nonneg_master (lo hi Q : ℕ)
    (hm : 0 < primePoolMass lo hi) (a : Fin Q) :
    0 ≤ primePoolResidueLaw lo hi Q a := by
  unfold primePoolResidueLaw
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro p hp
    by_cases h : p % Q = a.val <;> simp [h]
  · exact le_of_lt hm

private theorem uniformUnitResidueLaw_sum_eq_one (Q : ℕ) (hQ : 0 < Q) :
    ∑ a : Fin Q, uniformUnitResidueLaw Q a = 1 := by
  classical
  let S : Finset (Fin Q) := Finset.univ.filter (fun a => Nat.Coprime a.val Q)
  let e : {a : Fin Q // Nat.Coprime a.val Q} ≃
      {a : ℕ // a < Q ∧ Nat.Coprime Q a} := {
    toFun := fun a => ⟨a.1.val, ⟨a.1.isLt, Nat.coprime_comm.mp a.2⟩⟩
    invFun := fun a => ⟨⟨a.1, a.2.1⟩, Nat.coprime_comm.mpr a.2.2⟩
    left_inv := by intro a; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro a; apply Subtype.ext; rfl }
  have hcard : S.card = Nat.totient Q := by
    calc
      S.card = Fintype.card {a : Fin Q // Nat.Coprime a.val Q} :=
        (Fintype.card_of_subtype S (by intro a; simp [S])).symm
      _ = Nat.card {a : Fin Q // Nat.Coprime a.val Q} := Nat.card_eq_fintype_card.symm
      _ = Nat.card {a : ℕ // a < Q ∧ Nat.Coprime Q a} := Nat.card_congr e
      _ = Nat.totient Q := (Nat.totient_eq_card_lt_and_coprime Q).symm
  have hsum :
      (∑ a : Fin Q, if Nat.Coprime a.val Q then (1 : ℝ) else 0) =
        (Nat.totient Q : ℝ) := by
    rw [← Finset.sum_filter]
    simp [S, hcard]
  calc
    (∑ a : Fin Q, uniformUnitResidueLaw Q a) =
        (∑ a : Fin Q, if Nat.Coprime a.val Q then (1 : ℝ) else 0) /
          (Nat.totient Q : ℝ) := by
          unfold uniformUnitResidueLaw
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : Nat.Coprime a.val Q
          · simp only [if_pos h]
          · simp [h]
    _ = 1 := by
      rw [hsum]
      have hφ : (Nat.totient Q : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Nat.totient_pos.mpr hQ))
      exact div_self hφ

private noncomputable def masterFinUnitEquiv (Q : ℕ) (hQ : 0 < Q) :
    {a : Fin Q // Nat.Coprime a.val Q} ≃ (ZMod Q)ˣ := by
  cases Q with
  | zero => omega
  | succ q =>
      letI : NeZero (q + 1) := ⟨by omega⟩
      refine {
        toFun := fun a => (ZMod.unitsEquivCoprime).symm
          ⟨(ZMod.finEquiv (q + 1)) a.1, ?_⟩
        invFun := fun u => ⟨(ZMod.finEquiv (q + 1)).symm u.val, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
      · change Nat.Coprime a.1.val (q + 1)
        exact a.2
      · change Nat.Coprime u.val.val (q + 1)
        exact ZMod.val_coe_unit_coprime u
      · intro a
        apply Subtype.ext
        simpa [ZMod.finEquiv, ZMod.unitsEquivCoprime, ZMod.coe_unitOfCoprime] using
          (ZMod.finEquiv (q + 1)).symm_apply_apply a.1
      · intro u
        apply Units.ext
        simpa [ZMod.finEquiv, ZMod.unitsEquivCoprime, ZMod.coe_unitOfCoprime] using
          (ZMod.finEquiv (q + 1)).apply_symm_apply u.val

section
attribute [local instance] Classical.propDecidable

private theorem uniformGroupHomFiberProbability {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (y : H) :
    (∑ x : G, if f x = y then (1 : ℝ) / (Fintype.card G : ℝ) else 0) =
      1 / (Fintype.card H : ℝ) := by
  classical
  let Fib (z : H) := {x : G // f x = z}
  letI (z : H) : Fintype (Fib z) := Fintype.ofFinite _
  let fiberSetEquiv (z : H) : Fib z ≃ f ⁻¹' ({z} : Set H) := {
    toFun := fun x => ⟨x.1, by simpa [Set.preimage, Set.mem_singleton_iff] using x.2⟩
    invFun := fun x => ⟨x.1, by simpa [Set.preimage, Set.mem_singleton_iff] using x.2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; rfl }
  have hsumFiber : Fintype.card G = ∑ z : H, Fintype.card (Fib z) := by
    calc
      Fintype.card G = Fintype.card (Σ z : H, Fib z) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
      _ = ∑ z : H, Fintype.card (Fib z) := Fintype.card_sigma
  let c := Fintype.card (Fib (1 : H))
  have hfib (z : H) : Fintype.card (Fib z) = c := by
    calc
      Fintype.card (Fib z) = Nat.card (Fib z) := by rw [Nat.card_eq_fintype_card]
      _ = Nat.card (f ⁻¹' ({z} : Set H)) := Nat.card_congr (fiberSetEquiv z)
      _ = Nat.card (f ⁻¹' ({1} : Set H)) :=
        Nat.card_congr (f.fiberEquivOfSurjective hf z (1 : H))
      _ = Nat.card (Fib (1 : H)) := Nat.card_congr (fiberSetEquiv (1 : H)).symm
      _ = c := by rw [Nat.card_eq_fintype_card]
  have hcard : Fintype.card G = Fintype.card H * c := by
    calc
      Fintype.card G = ∑ z : H, Fintype.card (Fib z) := hsumFiber
      _ = ∑ z : H, c := by apply Finset.sum_congr rfl; intro z hz; exact hfib z
      _ = _ := by simp [c]
  have hfiberSum :
      (∑ x : G, if f x = y then (1 : ℝ) else 0) = (Fintype.card (Fib y) : ℝ) := by
    have hsub : Fintype.card (Fib y) =
        (Finset.univ.filter (fun x : G => f x = y)).card := by
      simpa [Fib] using
        (Fintype.card_of_subtype (Finset.univ.filter (fun x : G => f x = y))
          (fun x => by simp))
    rw [← Finset.sum_filter]
    calc
      (∑ x ∈ Finset.univ.filter (fun x : G => f x = y), (1 : ℝ)) =
          (Finset.univ.filter (fun x : G => f x = y)).card := by simp
      _ = Fintype.card (Fib y) := by rw [hsub]
  have hGpos : 0 < Fintype.card G := Fintype.card_pos
  have hHpos : 0 < Fintype.card H := Fintype.card_pos
  calc
    (∑ x : G, if f x = y then (1 : ℝ) / (Fintype.card G : ℝ) else 0) =
        (∑ x : G, if f x = y then (1 : ℝ) else 0) / (Fintype.card G : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : f x = y <;> simp [h]
    _ = (c : ℝ) / (Fintype.card G : ℝ) := by rw [hfiberSum, hfib]
    _ = 1 / (Fintype.card H : ℝ) := by
          have hcast : (Fintype.card G : ℝ) =
              (Fintype.card H : ℝ) * (c : ℝ) := by exact_mod_cast hcard
          have hcpos : 0 < c := by
            haveI : Nonempty (Fib (1 : H)) := ⟨⟨1, by simp⟩⟩
            exact Fintype.card_pos
          field_simp [Nat.cast_ne_zero.mpr hGpos.ne', Nat.cast_ne_zero.mpr hHpos.ne',
            Nat.cast_ne_zero.mpr hcpos.ne']
          nlinarith

end

private theorem masterFinUnitEquiv_val (Q : ℕ) [NeZero Q] (hQ : 0 < Q)
    (a : {x : Fin Q // Nat.Coprime x.val Q}) :
    (masterFinUnitEquiv Q hQ a).val = (ZMod.finEquiv Q) a.1 := by
  cases Q with
  | zero => omega
  | succ q =>
      letI : NeZero (q + 1) := ⟨by omega⟩
      simp [masterFinUnitEquiv, ZMod.finEquiv, ZMod.unitsEquivCoprime,
        ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]

private def masterResidueReduce {K Q : ℕ} (hK : 0 < K) (x : Fin Q) : Fin K :=
  ⟨x.val % K, Nat.mod_lt _ hK⟩

private noncomputable def masterUnitResidueReduce {K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) : {x : Fin Q // Nat.Coprime x.val Q} → {y : Fin K // Nat.Coprime y.val K} := by
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  exact (masterFinUnitEquiv K hK).symm ∘ ZMod.unitsMap hKQ ∘ masterFinUnitEquiv Q hQ

private theorem masterUnitResidueReduce_surjective {K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) : Function.Surjective (masterUnitResidueReduce hK hQ hKQ) := by
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  intro y
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hKQ (masterFinUnitEquiv K hK y)
  refine ⟨(masterFinUnitEquiv Q hQ).symm u, ?_⟩
  simp [masterUnitResidueReduce, hu]

private theorem masterUnitResidueReduce_val {K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) (x : {x : Fin Q // Nat.Coprime x.val Q}) :
    (masterUnitResidueReduce hK hQ hKQ x).1 = masterResidueReduce hK x.1 := by
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  apply (ZMod.finEquiv K).injective
  have hunit : masterFinUnitEquiv K hK (masterUnitResidueReduce hK hQ hKQ x) =
      ZMod.unitsMap hKQ (masterFinUnitEquiv Q hQ x) := by
    simp [masterUnitResidueReduce]
  have hcoe := congrArg (fun u : (ZMod K)ˣ => (u : ZMod K)) hunit
  rw [masterFinUnitEquiv_val K hK, ZMod.unitsMap_val,
    masterFinUnitEquiv_val Q hQ] at hcoe
  change (ZMod.finEquiv K) (masterUnitResidueReduce hK hQ hKQ x).1 =
      (ZMod.finEquiv K) (masterResidueReduce hK x.1)
  calc
    (ZMod.finEquiv K) (masterUnitResidueReduce hK hQ hKQ x).1 =
        ((ZMod.finEquiv Q) x.1).cast := hcoe
    _ = (ZMod.finEquiv K) (masterResidueReduce hK x.1) := by
          have hsource : (ZMod.finEquiv Q) x.1 = (x.1.val : ZMod Q) := by
            cases Q with
            | zero => omega
            | succ q =>
                letI : NeZero (q + 1) := ⟨by omega⟩
                apply Fin.ext
                change x.1.val = x.1.val % (q + 1)
                exact (Nat.mod_eq_of_lt x.1.isLt).symm
          have hcastNat :
              ((x.1.val : ZMod Q).cast : ZMod K) = (x.1.val : ZMod K) := by
            exact ZMod.cast_natCast hKQ x.1.val
          have hmod : (x.1.val : ZMod K) = ((x.1.val % K : ℕ) : ZMod K) := by
            apply (ZMod.natCast_eq_natCast_iff' _ _ _).2
            simp
          have htarget :
              (ZMod.finEquiv K) (masterResidueReduce hK x.1) =
                ((x.1.val % K : ℕ) : ZMod K) := by
            cases K with
            | zero => omega
            | succ k =>
                letI : NeZero (k + 1) := ⟨by omega⟩
                apply Fin.ext
                change x.1.val % (k + 1) =
                  (x.1.val % (k + 1)) % (k + 1)
                exact (Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos k))).symm
          rw [hsource, hcastNat, hmod, htarget]

section
attribute [local instance] Classical.propDecidable

private theorem uniformUnitResidueLaw_reduce {K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) (b : Fin K) :
    ∑ x : Fin Q, uniformUnitResidueLaw Q x *
      (if masterResidueReduce hK x = b then (1 : ℝ) else 0) =
      uniformUnitResidueLaw K b := by
  classical
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  letI : NeZero K := ⟨Nat.ne_of_gt hK⟩
  by_cases hb : Nat.Coprime b.val K
  · let bU : {y : Fin K // Nat.Coprime y.val K} := ⟨b, hb⟩
    have htest (x : {x : Fin Q // Nat.Coprime x.val Q}) :
        (masterResidueReduce hK x.1 = b) ↔
          masterUnitResidueReduce hK hQ hKQ x = bU := by
      constructor
      · intro hx
        apply Subtype.ext
        rw [masterUnitResidueReduce_val]
        exact hx
      · intro hx
        have hv := congrArg Subtype.val hx
        rw [masterUnitResidueReduce_val] at hv
        exact hv
    have hsplit :
        (∑ x : Fin Q, uniformUnitResidueLaw Q x *
          (if masterResidueReduce hK x = b then (1 : ℝ) else 0)) =
        ∑ x : {x : Fin Q // Nat.Coprime x.val Q},
          (1 / (Nat.totient Q : ℝ)) *
            (if masterUnitResidueReduce hK hQ hKQ x = bU then (1 : ℝ) else 0) := by
      calc
        _ = ∑ x : Fin Q,
            if Nat.Coprime x.val Q then
              (1 / (Nat.totient Q : ℝ)) *
                (if masterResidueReduce hK x = b then (1 : ℝ) else 0)
            else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              by_cases hxC : Nat.Coprime x.val Q
              · by_cases hred : masterResidueReduce hK x = b
                · simp [uniformUnitResidueLaw, hxC, hred]
                · simp [uniformUnitResidueLaw, hxC, hred]
              · simp [uniformUnitResidueLaw, hxC]
        _ = ∑ x : {x : Fin Q // Nat.Coprime x.val Q},
            (1 / (Nat.totient Q : ℝ)) *
              (if masterUnitResidueReduce hK hQ hKQ x = bU then (1 : ℝ) else 0) := by
              let p : Fin Q → Prop := fun x => Nat.Coprime x.val Q
              let f : Fin Q → ℝ := fun x =>
                if p x then (1 / (Nat.totient Q : ℝ)) *
                  (if masterResidueReduce hK x = b then (1 : ℝ) else 0) else 0
              have hpos :
                  (∑ x : {x : Fin Q // p x}, f x.1) =
                    ∑ x : {x : Fin Q // p x},
                      (1 / (Nat.totient Q : ℝ)) *
                        (if masterUnitResidueReduce hK hQ hKQ x = bU then (1 : ℝ) else 0) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hpoint : f x.1 =
                    (1 / (Nat.totient Q : ℝ)) *
                      (if masterUnitResidueReduce hK hQ hKQ x = bU then (1 : ℝ) else 0) := by
                  dsimp [f, p]
                  rw [if_pos x.property]
                  by_cases hred : masterResidueReduce hK x.1 = b
                  · have hmap := (htest x).mp hred
                    simp [hred, hmap]
                  · have hmap : masterUnitResidueReduce hK hQ hKQ x ≠ bU := by
                      intro hmap
                      exact hred ((htest x).mpr hmap)
                    simp [hred, hmap]
                exact hpoint
              have hneg : (∑ x : {x : Fin Q // ¬ p x}, f x.1) = 0 := by
                apply Finset.sum_eq_zero
                intro x hx
                simp [f, p, x.property]
              calc
                (∑ x : Fin Q, f x) =
                    (∑ x : {x : Fin Q // p x}, f x.1) +
                      ∑ x : {x : Fin Q // ¬ p x}, f x.1 :=
                  (Fintype.sum_subtype_add_sum_subtype p f).symm
                _ = _ := by rw [hpos, hneg, add_zero]
    have hgroup := uniformGroupHomFiberProbability (ZMod.unitsMap hKQ)
      (ZMod.unitsMap_surjective hKQ) (masterFinUnitEquiv K hK bU)
    let F : (ZMod Q)ˣ → ℝ := fun u =>
      if ZMod.unitsMap hKQ u = masterFinUnitEquiv K hK bU then
        1 / (Nat.totient Q : ℝ) else 0
    have hgroupLaw : (∑ u : (ZMod Q)ˣ, F u) =
        1 / (Nat.totient K : ℝ) := by
      simpa [F, ZMod.card_units_eq_totient] using hgroup
    have hreindex :
        (∑ x : {x : Fin Q // Nat.Coprime x.val Q},
          (1 / (Nat.totient Q : ℝ)) *
            (if masterUnitResidueReduce hK hQ hKQ x = bU then (1 : ℝ) else 0)) =
        ∑ u : (ZMod Q)ˣ, F u := by
      calc
        _ = ∑ x : {x : Fin Q // Nat.Coprime x.val Q},
            F (masterFinUnitEquiv Q hQ x) := by
              apply Finset.sum_congr rfl
              intro x hx
              have htestGroup :
                  masterUnitResidueReduce hK hQ hKQ x = bU ↔
                    ZMod.unitsMap hKQ (masterFinUnitEquiv Q hQ x) =
                      masterFinUnitEquiv K hK bU := by
                constructor
                · intro h
                  simpa [masterUnitResidueReduce] using
                    congrArg (masterFinUnitEquiv K hK) h
                · intro h
                  apply (masterFinUnitEquiv K hK).injective
                  simpa [masterUnitResidueReduce] using h
              simp [F, htestGroup]
        _ = ∑ u : (ZMod Q)ˣ, F u :=
              Equiv.sum_comp (masterFinUnitEquiv Q hQ) F
    rw [hsplit, hreindex, hgroupLaw]
    simp [uniformUnitResidueLaw, hb]
  · have hzero (x : Fin Q) :
        uniformUnitResidueLaw Q x *
          (if masterResidueReduce hK x = b then (1 : ℝ) else 0) = 0 := by
      by_cases hx : Nat.Coprime x.val Q
      · by_cases hr : masterResidueReduce hK x = b
        · have hcop := (masterUnitResidueReduce hK hQ hKQ ⟨x, hx⟩).property
          have hv := masterUnitResidueReduce_val hK hQ hKQ ⟨x, hx⟩
          rw [hv, hr] at hcop
          exact (hb hcop).elim
        · simp [uniformUnitResidueLaw, hx, hr]
      · simp [uniformUnitResidueLaw, hx]
    calc
      (∑ x : Fin Q, uniformUnitResidueLaw Q x *
        (if masterResidueReduce hK x = b then (1 : ℝ) else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          exact hzero x
      _ = uniformUnitResidueLaw K b := by simp [uniformUnitResidueLaw, hb]

end

section
attribute [local instance] Classical.propDecidable

private theorem uniformTuple_event_indicator_sum {α : Type*} [Fintype α]
    [DecidableEq α] (r : α) (E : α → Prop) :
    (∑ y : α, (if r = y then (1 : ℝ) else 0) *
      (if E y then 1 else 0)) = if E r then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single r]
  · simp
  · intro y hy hyr
    simp [hyr.symm]
  · simp

private theorem uniformUnitTupleMass_prod {Q m : ℕ} (x : Fin m → Fin Q) :
    uniformUnitTupleMass Q m x = ∏ i, uniformUnitResidueLaw Q (x i) := by
  classical
  by_cases hall : ∀ i : Fin m, Nat.Coprime (x i).val Q
  · have hprod :
      (∏ i, uniformUnitResidueLaw Q (x i)) =
        1 / (Nat.totient Q : ℝ) ^ m := by
      calc
        _ = ∏ i : Fin m, (1 / (Nat.totient Q : ℝ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [uniformUnitResidueLaw, hall i]
        _ = _ := by simp [Finset.prod_const, Fintype.card_fin]
    simp [uniformUnitTupleMass, hall, hprod]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hprod : ∏ j, uniformUnitResidueLaw Q (x j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [uniformUnitResidueLaw, hi]
    simp [uniformUnitTupleMass, hall, hprod]

private theorem uniformUnitTupleProbability_prod {Q m : ℕ}
    (E : (Fin m → Fin Q) → Prop) :
    uniformUnitTupleProbability Q m E =
      ∑ x : Fin m → Fin Q,
        (∏ i, uniformUnitResidueLaw Q (x i)) * (if E x then 1 else 0) := by
  classical
  unfold uniformUnitTupleProbability
  apply Finset.sum_congr rfl
  intro x hx
  rw [uniformUnitTupleMass_prod]

private def masterResidueTupleReduce {m K Q : ℕ} (hK : 0 < K)
    (x : Fin m → Fin Q) : Fin m → Fin K := fun i => masterResidueReduce hK (x i)

private theorem uniformUnitTupleResidueMass {m K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) (y : Fin m → Fin K) :
    (∑ x : Fin m → Fin Q,
      (∏ i, uniformUnitResidueLaw Q (x i)) *
        (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0)) =
      ∏ i, uniformUnitResidueLaw K (y i) := by
  classical
  have hindicator (x : Fin m → Fin Q) :
      (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0) =
        ∏ i, (if masterResidueReduce hK (x i) = y i then (1 : ℝ) else 0) := by
    have heq : masterResidueTupleReduce hK x = y ↔
        ∀ i : Fin m, masterResidueReduce hK (x i) = y i := by
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        exact funext h
    by_cases hall : ∀ i : Fin m, masterResidueReduce hK (x i) = y i
    · simp [heq.mpr hall, hall]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hprod :
          ∏ j, (if masterResidueReduce hK (x j) = y j then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
      have hnotEq : masterResidueTupleReduce hK x ≠ y := by
        intro h
        exact hall (fun j => congrFun h j)
      simp [hnotEq, hprod]
  have hfactor (x : Fin m → Fin Q) :
      (∏ i, uniformUnitResidueLaw Q (x i)) *
        (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0) =
      ∏ i, (uniformUnitResidueLaw Q (x i) *
        (if masterResidueReduce hK (x i) = y i then (1 : ℝ) else 0)) := by
    calc
      _ = (∏ i, uniformUnitResidueLaw Q (x i)) *
          (∏ i, (if masterResidueReduce hK (x i) = y i then (1 : ℝ) else 0)) := by
            rw [hindicator]
      _ = _ := by rw [← Finset.prod_mul_distrib]
  calc
    (∑ x : Fin m → Fin Q,
        (∏ i, uniformUnitResidueLaw Q (x i)) *
          (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0)) =
      ∑ x : Fin m → Fin Q, ∏ i,
        (uniformUnitResidueLaw Q (x i) *
          (if masterResidueReduce hK (x i) = y i then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hfactor x
    _ = ∏ i : Fin m, ∑ a : Fin Q,
        uniformUnitResidueLaw Q a *
          (if masterResidueReduce hK a = y i then (1 : ℝ) else 0) := by
            simpa using (Finset.sum_prod_piFinset (Finset.univ : Finset (Fin Q))
              (fun i a => uniformUnitResidueLaw Q a *
                (if masterResidueReduce hK a = y i then (1 : ℝ) else 0)))
    _ = ∏ i, uniformUnitResidueLaw K (y i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact uniformUnitResidueLaw_reduce hK hQ hKQ (y i)

private theorem uniformUnitTupleProbability_reduce {m K Q : ℕ} (hK : 0 < K) (hQ : 0 < Q)
    (hKQ : K ∣ Q) (E : (Fin m → Fin K) → Prop) :
    uniformUnitTupleProbability Q m (fun x => E (masterResidueTupleReduce hK x)) =
      uniformUnitTupleProbability K m E := by
  classical
  rw [uniformUnitTupleProbability_prod, uniformUnitTupleProbability_prod]
  calc
    (∑ x : Fin m → Fin Q,
        (∏ i, uniformUnitResidueLaw Q (x i)) *
          (if E (masterResidueTupleReduce hK x) then (1 : ℝ) else 0)) =
      ∑ y : Fin m → Fin K,
        (∏ i, uniformUnitResidueLaw K (y i)) * (if E y then 1 else 0) := by
          calc
            _ = ∑ x : Fin m → Fin Q,
                ∑ y : Fin m → Fin K,
                  (∏ i, uniformUnitResidueLaw Q (x i)) *
                    ((if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0) *
                      (if E y then 1 else 0)) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [← uniformTuple_event_indicator_sum
                      (masterResidueTupleReduce hK x) E]
                    rw [Finset.mul_sum]
            _ = ∑ y : Fin m → Fin K,
                ∑ x : Fin m → Fin Q,
                  (∏ i, uniformUnitResidueLaw Q (x i)) *
                    ((if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0) *
                      (if E y then 1 else 0)) := by rw [Finset.sum_comm]
            _ = ∑ y : Fin m → Fin K,
                (∏ i, uniformUnitResidueLaw K (y i)) * (if E y then 1 else 0) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    calc
                      (∑ x : Fin m → Fin Q,
                          (∏ i, uniformUnitResidueLaw Q (x i)) *
                            ((if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0) *
                              (if E y then 1 else 0))) =
                        ∑ x : Fin m → Fin Q,
                          ((∏ i, uniformUnitResidueLaw Q (x i)) *
                            (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0)) *
                            (if E y then 1 else 0) := by
                            apply Finset.sum_congr rfl
                            intro x hx
                            ring
                      _ = (∑ x : Fin m → Fin Q,
                            (∏ i, uniformUnitResidueLaw Q (x i)) *
                              (if masterResidueTupleReduce hK x = y then (1 : ℝ) else 0)) *
                            (if E y then 1 else 0) := by rw [Finset.sum_mul]
                      _ = _ := by rw [uniformUnitTupleResidueMass hK hQ hKQ y]

end

private def masterResidueTuple {m Q : ℕ} (hQ : 0 < Q) (p : Fin m → ℕ) :
    Fin m → Fin Q := fun i => masterResidue Q hQ (p i)

private theorem independentPrimePoolResidueTupleMass {m Q : ℕ} (lo hi : ℕ)
    (hQ : 0 < Q) (r : Fin m → Fin Q) :
    ∑' p : Fin m → ℕ, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
      (if masterResidueTuple hQ p = r then (1 : ℝ) else 0) =
      ∏ i, primePoolResidueLaw lo hi Q (r i) := by
  classical
  let T := (Finset.Ico lo hi).filter Nat.Prime
  let S := Fintype.piFinset (fun _ : Fin m => T)
  have hzero (p : Fin m → ℕ) (hp : p ∉ S) :
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if masterResidueTuple hQ p = r then (1 : ℝ) else 0) = 0 := by
    have hnot : ¬ ∀ i : Fin m, p i ∈ T := by
      intro h
      apply hp
      simpa [S] using h
    obtain ⟨i, hnotMem⟩ := not_forall.mp hnot
    have hcond : ¬ (lo ≤ p i ∧ p i < hi ∧ (p i).Prime) := by
      intro h
      apply hnotMem
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    have hmass : independentPrimePoolMass (fun _ => lo) (fun _ => hi) p = 0 := by
      unfold independentPrimePoolMass
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [primePoolLaw, hcond]
    simp [hmass]
  rw [tsum_eq_sum (s := S) hzero]
  have hfactor (p : Fin m → ℕ) :
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if masterResidueTuple hQ p = r then 1 else 0) =
      ∏ i, (primePoolLaw lo hi (p i) *
        if masterResidue Q hQ (p i) = r i then 1 else 0) := by
    have hindicator :
        (if masterResidueTuple hQ p = r then (1 : ℝ) else 0) =
          ∏ i, (if masterResidue Q hQ (p i) = r i then (1 : ℝ) else 0) := by
      have heq : masterResidueTuple hQ p = r ↔
          ∀ i : Fin m, masterResidue Q hQ (p i) = r i := by
        constructor
        · intro h i
          exact congrFun h i
        · intro h
          exact funext h
      by_cases hall : ∀ i : Fin m, masterResidue Q hQ (p i) = r i
      · simp [heq.mpr hall, hall]
      · obtain ⟨i, hi⟩ := not_forall.mp hall
        have hprod :
            ∏ j, (if masterResidue Q hQ (p j) = r j then (1 : ℝ) else 0) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
        have hnotEq : masterResidueTuple hQ p ≠ r := by
          intro h
          exact hall (fun j => congrFun h j)
        simp [hnotEq, hprod]
    calc
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          (if masterResidueTuple hQ p = r then 1 else 0) =
        (∏ i, primePoolLaw lo hi (p i)) *
          (∏ i, (if masterResidue Q hQ (p i) = r i then (1 : ℝ) else 0)) := by
            unfold independentPrimePoolMass
            exact congrArg (fun z : ℝ => (∏ i, primePoolLaw lo hi (p i)) * z) hindicator
      _ = ∏ i, (primePoolLaw lo hi (p i) *
          if masterResidue Q hQ (p i) = r i then 1 else 0) := by
            rw [← Finset.prod_mul_distrib]
  have hsingleZero (p : ℕ) (hp : p ∉ T) (a : Fin Q) :
      primePoolLaw lo hi p * (if masterResidue Q hQ p = a then (1 : ℝ) else 0) = 0 := by
    have hcond : ¬ (lo ≤ p ∧ p < hi ∧ p.Prime) := by
      intro h
      apply hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    simp [primePoolLaw, hcond]
  have hmarg (i : Fin m) :
      (∑ p ∈ T, primePoolLaw lo hi p *
        if masterResidue Q hQ p = r i then 1 else 0) =
        primePoolResidueLaw lo hi Q (r i) := by
    have h := primePoolLaw_residue_sum lo hi Q hQ (r i)
    rw [tsum_eq_sum (s := T) (fun p hp => hsingleZero p hp (r i))] at h
    exact h
  calc
    (∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        if masterResidueTuple hQ p = r then 1 else 0) =
      ∑ p ∈ S, ∏ i, (primePoolLaw lo hi (p i) *
        if masterResidue Q hQ (p i) = r i then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hfactor p
    _ = ∏ i, ∑ p ∈ T, primePoolLaw lo hi p *
        if masterResidue Q hQ p = r i then 1 else 0 := by
          simpa [S, T] using
            (Finset.sum_prod_piFinset T
              (fun i p => primePoolLaw lo hi p *
                if masterResidue Q hQ p = r i then 1 else 0))
    _ = ∏ i, primePoolResidueLaw lo hi Q (r i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hmarg i

private theorem finiteL1_event_bound {α : Type*} [Fintype α]
    (μ ν : α → ℝ) (E : α → Prop) [DecidablePred E] :
    (∑ x, μ x * (if E x then (1 : ℝ) else 0)) ≤
      (∑ x, ν x * (if E x then (1 : ℝ) else 0)) + finiteL1 μ ν := by
  classical
  unfold finiteL1
  calc
    (∑ x, μ x * (if E x then (1 : ℝ) else 0)) ≤
        ∑ x, (ν x * (if E x then (1 : ℝ) else 0) + |μ x - ν x|) := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hE : E x
          · simp [hE]
            linarith [le_abs_self (μ x - ν x)]
          · simp [hE]
    _ = (∑ x, ν x * (if E x then (1 : ℝ) else 0)) + ∑ x, |μ x - ν x| := by
          rw [Finset.sum_add_distrib]

private theorem masterResidue_event_indicator_sum {α : Type*} [Fintype α]
    [DecidableEq α] (r : α) (E : α → Prop) [DecidablePred E] :
    (∑ y : α, (if r = y then (1 : ℝ) else 0) *
      (if E y then 1 else 0)) = if E r then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single r]
  · simp
  · intro y hy hyr
    simp [hyr.symm]
  · simp

private def masterResidueTupleSupport {m : ℕ} (lo hi : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.Ico lo hi)

private lemma independentPrimePoolMass_zero_of_not_residueSupport {m : ℕ}
    (lo hi : ℕ) (p : Fin m → ℕ) (hp : p ∉ masterResidueTupleSupport lo hi) :
    independentPrimePoolMass (fun _ => lo) (fun _ => hi) p = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin m, p i ∈ Finset.Ico lo hi := by
    intro h
    apply hp
    simpa [masterResidueTupleSupport] using h
  obtain ⟨i, hnotMem⟩ := not_forall.mp hnot
  have hcond : ¬ (lo ≤ p i ∧ p i < hi ∧ (p i).Prime) := by
    intro h
    apply hnotMem
    exact Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [primePoolLaw, hcond]

section
attribute [local instance] Classical.propDecidable

private theorem independentPrimePoolProbability_residue {m Q : ℕ} (lo hi : ℕ)
    (hQ : 0 < Q) (E : (Fin m → Fin Q) → Prop) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
        (fun p => E (masterResidueTuple hQ p)) =
      ∑ r : Fin m → Fin Q,
        (∏ i, primePoolResidueLaw lo hi Q (r i)) *
          (if E r then 1 else 0) := by
  classical
  let S := masterResidueTupleSupport (m := m) lo hi
  have hzero (p : Fin m → ℕ) (hp : p ∉ S) :
      independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if E (masterResidueTuple hQ p) then (1 : ℝ) else 0) = 0 := by
    simpa [independentPrimePoolMass_zero_of_not_residueSupport lo hi p hp]
  unfold independentPrimePoolProbability
  rw [tsum_eq_sum (s := S) hzero]
  have htuple (r : Fin m → Fin Q) :
      (∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if masterResidueTuple hQ p = r then (1 : ℝ) else 0)) =
        ∏ i, primePoolResidueLaw lo hi Q (r i) := by
    have h := independentPrimePoolResidueTupleMass lo hi hQ r
    rw [tsum_eq_sum (s := S) (fun p hp => by
      simpa [independentPrimePoolMass_zero_of_not_residueSupport lo hi p hp])] at h
    exact h
  calc
    (∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
        (if E (masterResidueTuple hQ p) then 1 else 0)) =
      ∑ p ∈ S, ∑ r : Fin m → Fin Q,
        independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          ((if masterResidueTuple hQ p = r then (1 : ℝ) else 0) *
            (if E r then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← masterResidue_event_indicator_sum (masterResidueTuple hQ p) E]
          rw [Finset.mul_sum]
    _ = ∑ r : Fin m → Fin Q,
        ∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
          ((if masterResidueTuple hQ p = r then (1 : ℝ) else 0) *
            (if E r then 1 else 0)) := by
          rw [Finset.sum_comm]
    _ = ∑ r : Fin m → Fin Q,
        (∏ i, primePoolResidueLaw lo hi Q (r i)) *
          (if E r then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          calc
            (∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
                ((if masterResidueTuple hQ p = r then (1 : ℝ) else 0) *
                  (if E r then 1 else 0))) =
              ∑ p ∈ S,
                (independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
                  (if masterResidueTuple hQ p = r then (1 : ℝ) else 0)) *
                    (if E r then 1 else 0) := by
                      apply Finset.sum_congr rfl
                      intro p hp
                      ring
            _ = (∑ p ∈ S, independentPrimePoolMass (fun _ => lo) (fun _ => hi) p *
                  (if masterResidueTuple hQ p = r then (1 : ℝ) else 0)) *
                    (if E r then 1 else 0) := by
                      rw [Finset.sum_mul]
            _ = _ := by rw [htuple r]

private theorem product_finiteL1_bound {m Q : ℕ} (μ ν : Fin Q → ℝ)
    (hμ : ∑ a, |μ a| = 1) (hν : ∑ a, |ν a| = 1) :
    finiteL1 (fun x : Fin m → Fin Q => ∏ i, μ (x i))
      (fun x => ∏ i, ν (x i)) ≤ (m : ℝ) * finiteL1 μ ν := by
  calc
    finiteL1 (fun x : Fin m → Fin Q => ∏ i, μ (x i))
        (fun x => ∏ i, ν (x i)) ≤
      ∑ i, finiteL1 μ ν * ∏ j ∈ Finset.univ.erase i,
        max (∑ a, |μ a|) (∑ a, |ν a|) :=
      finite_product_l1_telescoping (fun _ : Fin m => μ) (fun _ => ν)
    _ = (m : ℝ) * finiteL1 μ ν := by simp [hμ, hν]

end

private theorem natCast_zmod_eq_mod_of_dvd {t K n : ℕ} (htK : t ∣ K) :
    (n : ZMod t) = (n % K : ZMod t) := by
  have hK0 : (K : ZMod t) = 0 := (ZMod.natCast_eq_zero_iff K t).2 htK
  have hdecomp : n = n % K + K * (n / K) := (Nat.mod_add_div n K).symm
  have hcast := congrArg (fun a : ℕ => (a : ZMod t)) hdecomp
  simpa [Nat.cast_add, Nat.cast_mul, hK0] using hcast

private theorem evalIntegerPolynomial_zmod {m : ℕ} (P : IntegerPolynomial m)
    (x : Fin m → ℤ) (t : ℕ) :
    ((evalIntegerPolynomial P x : ℤ) : ZMod t) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod t))
        (fun i => ((x i : ℤ) : ZMod t)) P := by
  change (Int.castRingHom (ZMod t)) (MvPolynomial.eval x P) = _
  simpa [Function.comp_def] using
    (MvPolynomial.eval₂_comp (Int.castRingHom (ZMod t)) x P)

private theorem evalIntegerPolynomial_zmod_congr {m : ℕ} (P : IntegerPolynomial m)
    (x y : Fin m → ℤ) (t : ℕ)
    (hxy : ∀ i, ((x i : ℤ) : ZMod t) = ((y i : ℤ) : ZMod t)) :
    ((evalIntegerPolynomial P x : ℤ) : ZMod t) =
      ((evalIntegerPolynomial P y : ℤ) : ZMod t) := by
  rw [evalIntegerPolynomial_zmod, evalIntegerPolynomial_zmod]
  have hfun : (fun i => ((x i : ℤ) : ZMod t)) =
      (fun i => ((y i : ℤ) : ZMod t)) := funext hxy
  rw [hfun]

private theorem evalIntegerPolynomial_dvd_iff_zmod {m : ℕ} (P : IntegerPolynomial m)
    (x y : Fin m → ℤ) (t : ℕ)
    (hxy : ∀ i, ((x i : ℤ) : ZMod t) = ((y i : ℤ) : ZMod t)) :
    ((t : ℤ) ∣ evalIntegerPolynomial P x) ↔
      ((t : ℤ) ∣ evalIntegerPolynomial P y) := by
  have hev := evalIntegerPolynomial_zmod_congr P x y t hxy
  constructor
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (evalIntegerPolynomial P x) t).2 h
    rw [hev] at hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (evalIntegerPolynomial P y) t).1 hz
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (evalIntegerPolynomial P y) t).2 h
    rw [← hev] at hz
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (evalIntegerPolynomial P x) t).1 hz

private theorem primeSmallDivisibilityEvent_residue {m w e Q : ℕ}
    (hQ : 0 < Q) (hdiv : (primorial w) ^ e ∣ Q) (D : Finset (IntegerPolynomial m))
    (p : Fin m → ℕ) :
    primeSmallDivisibilityEvent D w e p ↔
      uniformSmallPrimeException D w e
        (fun i => masterResidueReduce
          (pow_pos (primorial_pos w) e) (masterResidueTuple (Q := Q) hQ p i)) := by
  classical
  let K := (primorial w) ^ e
  have hK : 0 < K := by
    dsimp [K]
    exact pow_pos (primorial_pos w) e
  have hKQ : K ∣ Q := hdiv
  let u : Fin m → Fin K := fun i =>
    masterResidueReduce hK (masterResidueTuple (Q := Q) hQ p i)
  have hEval (q : ℕ) (hq : q.Prime) (hqle : q ≤ w) (P : IntegerPolynomial m) :
      ((q ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => (p i : ℤ)) ↔
        ((q ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial P (fun i => ((u i).val : ℤ)) := by
    have hqPrim : q ∣ primorial w := hq.dvd_primorial_iff.mpr hqle
    have hqK : q ^ e ∣ K := by
      dsimp [K]
      exact pow_dvd_pow_of_dvd hqPrim e
    have hredval (i : Fin m) : (u i).val = p i % K := by
      dsimp [u]
      simp [masterResidueReduce, masterResidueTuple, masterResidue,
        Nat.mod_mod_of_dvd (p i) hKQ]
    apply evalIntegerPolynomial_dvd_iff_zmod P
      (fun i => (p i : ℤ)) (fun i => ((u i).val : ℤ)) (q ^ e)
    intro i
    have hnat := natCast_zmod_eq_mod_of_dvd (t := q ^ e) (K := K) (n := p i) hqK
    rw [Int.cast_natCast, Int.cast_natCast, hredval]
    exact hnat
  constructor
  · rintro ⟨q, hq, hqle, P, hP, hdivP⟩
    refine ⟨q, hq, hqle, P, hP, ?_⟩
    exact (hEval q hq hqle P).mp hdivP
  · rintro ⟨q, hq, hqle, P, hP, hdivP⟩
    refine ⟨q, hq, hqle, P, hP, ?_⟩
    exact (hEval q hq hqle P).mpr hdivP

/-- Finite union bound choosing one common exponent for all prescribed small-prime tests
(§3 lines 276–280). The polynomials must be nonzero (§3 line 200); for `D={0}` the event
always holds. -/
private theorem uniformUnitTupleProbability_finset_union_bound {Q m : ℕ} {β : Type*}
    (T : Finset β) (E : β → (Fin m → Fin Q) → Prop) :
    uniformUnitTupleProbability Q m (fun x => ∃ t ∈ T, E t x) ≤
      ∑ t ∈ T, uniformUnitTupleProbability Q m (E t) := by
  classical
  letI : DecidablePred (fun x : Fin m → Fin Q => ∃ t ∈ T, E t x) :=
    fun x => Classical.propDecidable _
  have hmass (x : Fin m → Fin Q) : 0 ≤ uniformUnitTupleMass Q m x := by
    unfold uniformUnitTupleMass
    split_ifs <;> positivity
  have hindicator (x : Fin m → Fin Q) :
      @ite ℝ (∃ t ∈ T, E t x) (Classical.propDecidable _) (1 : ℝ) 0 ≤
        ∑ t ∈ T, @ite ℝ (E t x) (Classical.propDecidable _) (1 : ℝ) 0 := by
    by_cases hx : ∃ t ∈ T, E t x
    · obtain ⟨t, ht, hEt⟩ := hx
      let S := T.filter fun a => E a x
      have hS : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨ht, hEt⟩⟩
      have hcard : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
      have hsum :
          (∑ t ∈ T, if E t x then (1 : ℝ) else 0) = (S.card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [S]
      have hs : 1 ≤ ∑ t ∈ T, if E t x then (1 : ℝ) else 0 := by
        calc
          (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
          _ = _ := hsum.symm
      rw [if_pos ⟨t, ht, hEt⟩]
      exact hs
    · rw [if_neg hx]
      exact Finset.sum_nonneg (by intro t ht; split_ifs <;> positivity)
  calc
    uniformUnitTupleProbability Q m (fun x => ∃ t ∈ T, E t x) ≤
        ∑ x : Fin m → Fin Q,
          uniformUnitTupleMass Q m x *
            (∑ t ∈ T, if E t x then (1 : ℝ) else 0) := by
              unfold uniformUnitTupleProbability
              apply Finset.sum_le_sum
              intro x hx
              exact mul_le_mul_of_nonneg_left (hindicator x) (hmass x)
    _ = ∑ t ∈ T, ∑ x : Fin m → Fin Q,
          uniformUnitTupleMass Q m x * if E t x then (1 : ℝ) else 0 := by
            calc
              _ = ∑ x : Fin m → Fin Q, ∑ t ∈ T,
                  uniformUnitTupleMass Q m x * (if E t x then (1 : ℝ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.mul_sum]
              _ = _ := by rw [Finset.sum_comm]
    _ = ∑ t ∈ T, uniformUnitTupleProbability Q m (E t) := by
          rfl

theorem choose_small_prime_exception_exponent {m : ℕ}
    (w : ℕ) (hw : 1 ≤ w) (D : Finset (IntegerPolynomial m)) (hD : ∀ P ∈ D, P ≠ 0) :
    ∃ e : ℕ, 1 ≤ e ∧
      uniformUnitTupleProbability ((primorial w) ^ e) m
        (uniformSmallPrimeException D w e) ≤ 1 / (w : ℝ) := by
  classical
  let W := primorial w
  let Q := (Finset.Icc 2 w).filter Nat.Prime
  let T : Finset (ℕ × IntegerPolynomial m) := Q.product D
  let E (e : ℕ) (t : ℕ × IntegerPolynomial m) (x : Fin m → Fin (W ^ e)) : Prop :=
    ((t.1 ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial t.2 (fun i => ((x i).val : ℤ))
  let E₀ (e : ℕ) (t : ℕ × IntegerPolynomial m)
      (x : Fin m → Fin (t.1 ^ e)) : Prop :=
    ((t.1 ^ e : ℕ) : ℤ) ∣ evalIntegerPolynomial t.2 (fun i => ((x i).val : ℤ))
  have hunion (e : ℕ) (x : Fin m → Fin (W ^ e)) :
      uniformSmallPrimeException D w e x ↔ ∃ t ∈ T, E e t x := by
    constructor
    · rintro ⟨q, hq, hqle, P, hP, hdiv⟩
      have hqmem : q ∈ Q := by
        dsimp [Q]
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr ⟨hq.two_le, hqle⟩, hq⟩
      refine ⟨(q, P), Finset.mem_product.mpr ⟨hqmem, hP⟩, ?_⟩
      exact hdiv
    · rintro ⟨⟨q, P⟩, ht, hdiv⟩
      rcases Finset.mem_product.mp ht with ⟨hqmem, hP⟩
      have hqmem' : q ∈ Q := hqmem
      dsimp [Q] at hqmem'
      have ⟨hqIcc, hq⟩ := Finset.mem_filter.mp hqmem'
      have ⟨_, hqle⟩ := Finset.mem_Icc.mp hqIcc
      exact ⟨q, hq, hqle, P, hP, hdiv⟩
  have hunionProb (e : ℕ) :
      uniformUnitTupleProbability (W ^ e) m (uniformSmallPrimeException D w e) ≤
        ∑ t ∈ T, uniformUnitTupleProbability (W ^ e) m (E e t) := by
    calc
      uniformUnitTupleProbability (W ^ e) m (uniformSmallPrimeException D w e) =
          uniformUnitTupleProbability (W ^ e) m (fun x => ∃ t ∈ T, E e t x) := by
            unfold uniformUnitTupleProbability
            apply Finset.sum_congr rfl
            intro x hx
            have h := hunion e x
            by_cases he : uniformSmallPrimeException D w e x
            · have h' := h.mp he
              simp [he, h']
            · have h' : ¬ ∃ t ∈ T, E e t x := fun h' => he (h.mpr h')
              simp [he, h']
      _ ≤ _ := uniformUnitTupleProbability_finset_union_bound T (E e)
  have hpush (e : ℕ) (t : ℕ × IntegerPolynomial m) (ht : t ∈ T) :
    uniformUnitTupleProbability (W ^ e) m (E e t) =
        uniformUnitTupleProbability (t.1 ^ e) m (E₀ e t) := by
    let K := t.1 ^ e
    rcases Finset.mem_filter.mp (Finset.mem_product.mp ht).1 with ⟨hIcc, htPrime⟩
    have htle : t.1 ≤ w := (Finset.mem_Icc.mp hIcc).2
    have hPD : t.2 ∈ D := (Finset.mem_product.mp ht).2
    have hK : 0 < K := by dsimp [K]; exact pow_pos htPrime.pos e
    have hW : 0 < W ^ e := pow_pos (primorial_pos w) e
    letI : NeZero K := ⟨hK.ne'⟩
    letI : NeZero (W ^ e) := ⟨hW.ne'⟩
    have hprimeW : t.1 ∣ W := by
      dsimp [W]
      exact htPrime.dvd_primorial_iff.mpr (by omega)
    have hdiv : K ∣ W ^ e := by
      dsimp [K, W]
      exact pow_dvd_pow_of_dvd hprimeW e
    have hred (x : Fin m → Fin (W ^ e)) :
        E e t x ↔ E₀ e t (masterResidueTupleReduce hK x) := by
      dsimp [E, E₀, K]
      apply evalIntegerPolynomial_dvd_iff_zmod
      intro i
      dsimp [masterResidueTupleReduce, masterResidueReduce]
      norm_cast
      simpa only [ZMod.val_natCast] using
        (ZMod.natCast_zmod_val ((x i).val : ZMod K)).symm
    calc
      uniformUnitTupleProbability (W ^ e) m (E e t) =
          uniformUnitTupleProbability (W ^ e) m
            (fun x => E₀ e t (masterResidueTupleReduce hK x)) := by
              unfold uniformUnitTupleProbability
              apply Finset.sum_congr rfl
              intro x hx
              have h := hred x
              by_cases he : E e t x
              · have h' := h.mp he
                simp [he, h']
              · have h' : ¬ E₀ e t (masterResidueTupleReduce hK x) :=
                  fun h' => he (h.mpr h')
                simp [he, h']
      _ = uniformUnitTupleProbability K m (E₀ e t) :=
        uniformUnitTupleProbability_reduce hK hW hdiv (E₀ e t)
  have hsumLimit : Tendsto
      (fun e => ∑ u ∈ T, uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u))
      atTop (𝓝 0) := by
    have haux : ∀ S : Finset (ℕ × IntegerPolynomial m), S ⊆ T →
        Tendsto (fun e => ∑ u ∈ S, uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u))
          atTop (𝓝 0) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          intro hS
          simp
      | @insert t S hnot ih =>
          intro hS
          have ht0 : t ∈ T := hS (Finset.mem_insert_self _ _)
          have hSsub : S ⊆ T := by
            intro a ha
            exact hS (Finset.mem_insert_of_mem ha)
          rcases Finset.mem_product.mp ht0 with ⟨hqmem, hPmem⟩
          dsimp [Q] at hqmem
          rcases Finset.mem_filter.mp hqmem with ⟨hIcc, hq⟩
          have hP : t.2 ≠ 0 := hD t.2 hPmem
          have hterm := p_adic_polynomial_unit_zero_set t.1 hq t.2 hP
          have hsumInsert (e : ℕ) :
              (∑ u ∈ insert t S,
                uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u)) =
                uniformUnitTupleProbability (t.1 ^ e) m (E₀ e t) +
                  ∑ u ∈ S, uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u) := by
            exact Finset.sum_insert hnot
          have hfun :
              (fun e => ∑ u ∈ insert t S,
                uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u)) =
              fun e => uniformUnitTupleProbability (t.1 ^ e) m (E₀ e t) +
                ∑ u ∈ S, uniformUnitTupleProbability (u.1 ^ e) m (E₀ e u) := by
            funext e
            exact hsumInsert e
          rw [hfun]
          simpa [E₀] using hterm.add (ih hSsub)
    exact haux T (fun _ ht => ht)
  have hnonneg (e : ℕ) : 0 ≤ uniformUnitTupleProbability (W ^ e) m
      (uniformSmallPrimeException D w e) := by
    unfold uniformUnitTupleProbability
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · unfold uniformUnitTupleMass
      split_ifs <;> positivity
    · split_ifs <;> norm_num
  have hsmall : Tendsto
      (fun e => uniformUnitTupleProbability (W ^ e) m
        (uniformSmallPrimeException D w e)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall hnonneg)
    · filter_upwards with e
      calc
        uniformUnitTupleProbability (W ^ e) m (uniformSmallPrimeException D w e) ≤
          ∑ t ∈ T, uniformUnitTupleProbability (W ^ e) m (E e t) := hunionProb e
        _ = ∑ t ∈ T, uniformUnitTupleProbability (t.1 ^ e) m (E₀ e t) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact hpush e t ht
    · exact hsumLimit
  have hε : 0 < 1 / (w : ℝ) := by positivity
  have hbound : ∀ᶠ e : ℕ in atTop,
      uniformUnitTupleProbability (W ^ e) m (uniformSmallPrimeException D w e) ≤
        1 / (w : ℝ) := by
    filter_upwards [hsmall.eventually (Metric.ball_mem_nhds 0 hε)] with e he
    change dist (uniformUnitTupleProbability (W ^ e) m
      (uniformSmallPrimeException D w e)) 0 < 1 / (w : ℝ) at he
    have habs : |uniformUnitTupleProbability (W ^ e) m
      (uniformSmallPrimeException D w e)| < 1 / (w : ℝ) := by
        simpa [Real.dist_eq] using he
    exact le_of_lt (abs_lt.mp habs).2
  obtain ⟨E₀, hE₀⟩ := eventually_atTop.mp hbound
  let e := max E₀ 1
  refine ⟨e, Nat.le_max_right _ _, ?_⟩
  exact hE₀ e (Nat.le_max_left _ _)


theorem pool_small_prime_exception_transfer {m : ℕ} (D : Finset (IntegerPolynomial m))
    (w e Q lo hi : ℕ) (hQ : 0 < Q) (hdiv : (primorial w) ^ e ∣ Q) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ : Fin m => hi)
        (primeSmallDivisibilityEvent D w e) ≤
      uniformUnitTupleProbability ((primorial w) ^ e) m
          (uniformSmallPrimeException D w e) +
        (m : ℝ) * finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) := by
  classical
  let K := (primorial w) ^ e
  have hK : 0 < K := by dsimp [K]; exact pow_pos (primorial_pos w) e
  let Eres : (Fin m → Fin Q) → Prop := fun r =>
    uniformSmallPrimeException D w e (fun i => masterResidueReduce hK (r i))
  have hEvent (p : Fin m → ℕ) :
      primeSmallDivisibilityEvent D w e p ↔ Eres (masterResidueTuple hQ p) := by
    simpa [Eres, K] using (primeSmallDivisibilityEvent_residue hQ hdiv D p)
  have hprob :
      independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
          (primeSmallDivisibilityEvent D w e) =
        ∑ r : Fin m → Fin Q,
          (∏ i, primePoolResidueLaw lo hi Q (r i)) * (if Eres r then 1 else 0) := by
    calc
      _ = independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
          (fun p => Eres (masterResidueTuple hQ p)) := by
            unfold independentPrimePoolProbability
            apply tsum_congr
            intro p
            simp [hEvent p]
      _ = _ := independentPrimePoolProbability_residue lo hi hQ Eres
  have hUniform :
      (∑ r : Fin m → Fin Q,
        (∏ i, uniformUnitResidueLaw Q (r i)) * (if Eres r then 1 else 0)) =
      uniformUnitTupleProbability K m (uniformSmallPrimeException D w e) := by
    calc
      _ = uniformUnitTupleProbability Q m Eres :=
        (uniformUnitTupleProbability_prod Eres).symm
      _ = uniformUnitTupleProbability K m (uniformSmallPrimeException D w e) := by
        change uniformUnitTupleProbability Q m
          (fun x => uniformSmallPrimeException D w e
            (fun i => masterResidueReduce hK (x i))) = _
        exact uniformUnitTupleProbability_reduce hK hQ hdiv
          (uniformSmallPrimeException D w e)
  let μ : Fin Q → ℝ := primePoolResidueLaw lo hi Q
  let ν : Fin Q → ℝ := uniformUnitResidueLaw Q
  by_cases hm0 : m = 0
  · subst m
    have hprodZero :
        finiteL1 (fun x : Fin 0 → Fin Q => ∏ i, μ (x i))
          (fun x => ∏ i, ν (x i)) = 0 := by
      classical
      unfold finiteL1
      apply Finset.sum_eq_zero
      intro x hx
      simp
    have hTV := finiteL1_event_bound
      (fun x : Fin 0 → Fin Q => ∏ i, μ (x i))
      (fun x => ∏ i, ν (x i)) Eres
    have hA : independentPrimePoolProbability (fun _ : Fin 0 => lo) (fun _ => hi)
          (primeSmallDivisibilityEvent D w e) ≤
        uniformUnitTupleProbability K 0 (uniformSmallPrimeException D w e) := by
      calc
        independentPrimePoolProbability (fun _ : Fin 0 => lo) (fun _ => hi)
            (primeSmallDivisibilityEvent D w e) =
          ∑ r : Fin 0 → Fin Q,
            (∏ i, μ (r i)) * (if Eres r then 1 else 0) := hprob
        _ ≤ (∑ r : Fin 0 → Fin Q,
            (∏ i, ν (r i)) * (if Eres r then 1 else 0)) +
              finiteL1 (fun x : Fin 0 → Fin Q => ∏ i, μ (x i))
                (fun x => ∏ i, ν (x i)) := hTV
        _ = uniformUnitTupleProbability K 0 (uniformSmallPrimeException D w e) := by
              rw [hUniform, hprodZero]
              simp
    simpa [K] using hA
  · have hmassNonneg : 0 ≤ primePoolMass lo hi := by
      unfold primePoolMass
      apply Finset.sum_nonneg
      intro p hp
      have hpP : p.Prime := (Finset.mem_filter.mp hp).2
      exact div_nonneg (by norm_num)
        (le_of_lt (by exact_mod_cast hpP.pos : (0 : ℝ) < (p : ℝ)))
    by_cases hmass0 : primePoolMass lo hi = 0
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hLawZero (x : ℕ) : primePoolLaw lo hi x = 0 := by
        unfold primePoolLaw
        by_cases hx : lo ≤ x ∧ x < hi ∧ x.Prime <;> simp [hx, hmass0]
      let i : Fin m := ⟨0, hmpos⟩
      have hMassZero (p : Fin m → ℕ) :
          independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p = 0 := by
        unfold independentPrimePoolMass
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact hLawZero (p i)
      have hLeft :
          independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
            (primeSmallDivisibilityEvent D w e) = 0 := by
        simp [independentPrimePoolProbability, hMassZero]
      have hProbNonneg :
          0 ≤ uniformUnitTupleProbability K m (uniformSmallPrimeException D w e) := by
        unfold uniformUnitTupleProbability
        apply Finset.sum_nonneg
        intro x hx
        apply mul_nonneg
        · unfold uniformUnitTupleMass
          split_ifs <;> positivity
        · split_ifs <;> norm_num
      have hL1Nonneg : 0 ≤ finiteL1 (primePoolResidueLaw lo hi Q)
          (uniformUnitResidueLaw Q) := by
        unfold finiteL1
        apply Finset.sum_nonneg
        intro x hx
        exact abs_nonneg _
      have hErrNonneg : 0 ≤ (m : ℝ) *
          finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) :=
        mul_nonneg (by positivity) hL1Nonneg
      rw [hLeft]
      exact add_nonneg hProbNonneg hErrNonneg
    · have hmassPos : 0 < primePoolMass lo hi := lt_of_le_of_ne hmassNonneg (Ne.symm hmass0)
      have hμnonneg (a : Fin Q) : 0 ≤ μ a := by
        dsimp [μ]
        exact primePoolResidueLaw_nonneg_master lo hi Q hmassPos a
      have hνnonneg (a : Fin Q) : 0 ≤ ν a := by
        dsimp [ν, uniformUnitResidueLaw]
        split_ifs <;> positivity
      have hμsum : ∑ a, |μ a| = 1 := by
        calc
          _ = ∑ a, μ a := by
            apply Finset.sum_congr rfl
            intro a ha
            exact abs_of_nonneg (hμnonneg a)
          _ = 1 := by
            dsimp [μ]
            exact primePoolResidueLaw_sum_eq_one lo hi Q hQ hmassPos
      have hνsum : ∑ a, |ν a| = 1 := by
        calc
          _ = ∑ a, ν a := by
            apply Finset.sum_congr rfl
            intro a ha
            exact abs_of_nonneg (hνnonneg a)
          _ = 1 := by
            dsimp [ν]
            exact uniformUnitResidueLaw_sum_eq_one Q hQ
      have hProdTV := product_finiteL1_bound (m := m) (Q := Q) μ ν hμsum hνsum
      have hTV := finiteL1_event_bound
        (fun x : Fin m → Fin Q => ∏ i, μ (x i))
        (fun x => ∏ i, ν (x i)) Eres
      calc
        independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
            (primeSmallDivisibilityEvent D w e) =
          ∑ r : Fin m → Fin Q,
            (∏ i, μ (r i)) * (if Eres r then 1 else 0) := hprob
        _ ≤ (∑ r : Fin m → Fin Q,
            (∏ i, ν (r i)) * (if Eres r then 1 else 0)) +
              finiteL1 (fun x : Fin m → Fin Q => ∏ i, μ (x i))
                (fun x => ∏ i, ν (x i)) := hTV
        _ ≤ (∑ r : Fin m → Fin Q,
            (∏ i, ν (r i)) * (if Eres r then 1 else 0)) +
              (m : ℝ) * finiteL1 μ ν := by
                simpa [add_comm] using add_le_add_left hProdTV
                  (∑ r : Fin m → Fin Q,
                    (∏ i, ν (r i)) * (if Eres r then 1 else 0))
        _ = uniformUnitTupleProbability K m (uniformSmallPrimeException D w e) +
              (m : ℝ) * finiteL1 (primePoolResidueLaw lo hi Q)
                (uniformUnitResidueLaw Q) := by
              rw [hUniform]

private def masterPrimeTupleSupport {m : ℕ} (lo hi : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.Ico lo hi)

private lemma independentPrimePoolMass_zero_of_not_mem_masterSupport {m : ℕ}
    (lo hi : ℕ) (p : Fin m → ℕ) (hp : p ∉ masterPrimeTupleSupport lo hi) :
    independentPrimePoolMass (fun _ : Fin m => lo) (fun _ : Fin m => hi) p = 0 := by
  classical
  have hnot : ¬ ∀ i : Fin m, p i ∈ Finset.Ico lo hi := by
    intro h
    apply hp
    simpa [masterPrimeTupleSupport] using h
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma independentPrimePoolMass_summable_masterSupport {m : ℕ} (lo hi : ℕ) :
    Summable (independentPrimePoolMass (fun _ : Fin m => lo) (fun _ : Fin m => hi)) := by
  classical
  apply summable_of_ne_finset_zero (s := masterPrimeTupleSupport lo hi)
  intro p hp
  exact independentPrimePoolMass_zero_of_not_mem_masterSupport lo hi p hp

private lemma independentPrimePoolProbability_summable_masterSupport {m : ℕ} (lo hi : ℕ)
    (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    Summable (fun p =>
      independentPrimePoolMass (fun _ : Fin m => lo) (fun _ : Fin m => hi) p *
        if E p then (1 : ℝ) else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := masterPrimeTupleSupport lo hi)
  intro p hp
  rw [independentPrimePoolMass_zero_of_not_mem_masterSupport lo hi p hp]
  simp

private lemma primePoolLaw_nonneg_master (lo hi p : ℕ) : 0 ≤ primePoolLaw lo hi p := by
  have hm : 0 ≤ primePoolMass lo hi := by
    unfold primePoolMass
    exact Finset.sum_nonneg (by intro q hq; exact div_nonneg (by norm_num) (by positivity))
  unfold primePoolLaw
  split_ifs <;> positivity

private lemma primePoolMass_nonneg_master (lo hi : ℕ) : 0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  exact Finset.sum_nonneg (by intro p hp; exact div_nonneg (by norm_num) (by positivity))

private lemma primePoolLaw_tsum_eq_one_master {lo hi : ℕ}
    (hm : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  classical
  let s := (Finset.Ico lo hi).filter Nat.Prime
  have hzero (p : ℕ) (hp : p ∉ s) : primePoolLaw lo hi p = 0 := by
    by_contra hne
    have hp' : p ∈ s := by
      unfold primePoolLaw at hne
      split_ifs at hne with h
      · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
      · simp at hne
    exact hp hp'
  rw [tsum_eq_sum (s := s) hzero]
  have hmass : primePoolMass lo hi =
      ∑ p ∈ s, 1 / (p : ℝ) := rfl
  have hfinite :
      (∑ p ∈ s, primePoolLaw lo hi p) =
        (∑ p ∈ s, 1 / (p : ℝ)) / primePoolMass lo hi := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpcond : lo ≤ p ∧ p < hi ∧ p.Prime := by
      rcases Finset.mem_Ico.mp hp'.1 with ⟨hlo, hhi⟩
      exact ⟨hlo, hhi, hp'.2⟩
    simp [primePoolLaw, hpcond]
  rw [hfinite, ← hmass, div_self hm.ne']

private def primePoolResidueNumerator (lo hi Q : ℕ) (a : Fin Q) : ℝ :=
  ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
    if p % Q = a.val then 1 / (p : ℝ) else 0

private lemma primePoolMass_split (lo mid hi : ℕ) (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    primePoolMass lo hi = primePoolMass lo mid + primePoolMass mid hi := by
  let s₁ := (Finset.Ico lo mid).filter Nat.Prime
  let s₂ := (Finset.Ico mid hi).filter Nat.Prime
  have hIco : Finset.Ico lo hi = Finset.Ico lo mid ∪ Finset.Ico mid hi :=
    (Finset.Ico_union_Ico_eq_Ico hlm hmh).symm
  have hdisj : Disjoint s₁ s₂ := by
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have h₁ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₁).1
    have h₂ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₂).1
    omega
  unfold primePoolMass
  rw [hIco, Finset.filter_union, Finset.sum_union hdisj]

private lemma primePoolResidueNumerator_split (lo mid hi Q : ℕ) (a : Fin Q)
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    primePoolResidueNumerator lo hi Q a =
      primePoolResidueNumerator lo mid Q a + primePoolResidueNumerator mid hi Q a := by
  let s₁ := (Finset.Ico lo mid).filter Nat.Prime
  let s₂ := (Finset.Ico mid hi).filter Nat.Prime
  have hIco : Finset.Ico lo hi = Finset.Ico lo mid ∪ Finset.Ico mid hi :=
    (Finset.Ico_union_Ico_eq_Ico hlm hmh).symm
  have hdisj : Disjoint s₁ s₂ := by
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have h₁ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₁).1
    have h₂ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₂).1
    omega
  unfold primePoolResidueNumerator
  rw [hIco, Finset.filter_union, Finset.sum_union hdisj]

private lemma finiteL1_weighted_mix_bound {Q : ℕ} (μ₁ μ₂ ν : Fin Q → ℝ)
    (m₁ m₂ ε : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h₁ : finiteL1 μ₁ ν ≤ ε) (h₂ : finiteL1 μ₂ ν ≤ ε) :
    finiteL1 (fun a => (m₁ * μ₁ a + m₂ * μ₂ a) / (m₁ + m₂)) ν ≤ ε := by
  have hden : 0 < m₁ + m₂ := by linarith
  unfold finiteL1 at h₁ h₂ ⊢
  calc
    (∑ a, |(m₁ * μ₁ a + m₂ * μ₂ a) / (m₁ + m₂) - ν a|) ≤
        ∑ a, (m₁ * |μ₁ a - ν a| + m₂ * |μ₂ a - ν a|) / (m₁ + m₂) := by
      apply Finset.sum_le_sum
      intro a ha
      have heq :
          (m₁ * μ₁ a + m₂ * μ₂ a) / (m₁ + m₂) - ν a =
            (m₁ * (μ₁ a - ν a) + m₂ * (μ₂ a - ν a)) / (m₁ + m₂) := by
        field_simp [hden.ne']
        <;> ring
      have htri : |m₁ * (μ₁ a - ν a) + m₂ * (μ₂ a - ν a)| ≤
          m₁ * |μ₁ a - ν a| + m₂ * |μ₂ a - ν a| := by
        calc
          _ ≤ |m₁ * (μ₁ a - ν a)| + |m₂ * (μ₂ a - ν a)| := abs_add_le _ _
          _ = m₁ * |μ₁ a - ν a| + m₂ * |μ₂ a - ν a| := by
            rw [abs_mul, abs_mul, abs_of_pos hm₁, abs_of_pos hm₂]
      rw [heq, abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right htri (le_of_lt hden)
    _ = (m₁ * (∑ a, |μ₁ a - ν a|) + m₂ * (∑ a, |μ₂ a - ν a|)) /
          (m₁ + m₂) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ((m₁ + m₂) * ε) / (m₁ + m₂) := by
      gcongr
      nlinarith
    _ = ε := by field_simp [hden.ne']

private lemma primePoolMass_mono {lo hi₁ hi₂ : ℕ} (hh : hi₁ ≤ hi₂) :
    primePoolMass lo hi₁ ≤ primePoolMass lo hi₂ := by
  unfold primePoolMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hprime⟩
    have hpI' := Finset.mem_Ico.mp hpI
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨hpI'.1, hpI'.2.trans_le hh⟩, hprime⟩
  · intro p hp hnot
    exact div_nonneg (by norm_num) (by positivity)

private lemma primePoolResidueLaw_split {lo mid hi Q : ℕ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hm₁ : 0 < primePoolMass lo mid) (hm₂ : 0 < primePoolMass mid hi) :
    ∀ a : Fin Q, primePoolResidueLaw lo hi Q a =
      (primePoolMass lo mid * primePoolResidueLaw lo mid Q a +
        primePoolMass mid hi * primePoolResidueLaw mid hi Q a) /
          (primePoolMass lo mid + primePoolMass mid hi) := by
  intro a
  change primePoolResidueNumerator lo hi Q a / primePoolMass lo hi = _
  rw [primePoolResidueNumerator_split lo mid hi Q a hlm hmh,
    primePoolMass_split lo mid hi hlm hmh]
  dsimp [primePoolResidueLaw, primePoolResidueNumerator]
  field_simp [hm₁.ne', hm₂.ne']
  <;> ring

private theorem dyadicPoolResidueBound (Q a k : ℕ) (ε : ℝ)
    (hErr : ∀ j, a ≤ j →
      finiteL1 (primePoolResidueLaw (2 ^ j) (2 ^ (j + 1)) Q)
        (uniformUnitResidueLaw Q) ≤ ε)
    (hMass : ∀ j, a ≤ j → 0 < primePoolMass (2 ^ j) (2 ^ (j + 1)))
    (hk : 0 < k) :
    finiteL1 (primePoolResidueLaw (2 ^ a) (2 ^ (a + k)) Q)
      (uniformUnitResidueLaw Q) ≤ ε := by
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero =>
          simpa using hErr a le_rfl
      | succ k =>
          have hprev := ih (by omega)
          let j := a + (k + 1)
          have hExp : a + (k + 1) ≤ a + (k + 1 + 1) := by omega
          have hExpLo : a ≤ a + (k + 1) := by omega
          have hExpPrev : a + 1 ≤ a + (k + 1) := by omega
          have hloMid : 2 ^ a ≤ 2 ^ j := by
            dsimp [j]
            exact Nat.pow_le_pow_right (by omega) hExpLo
          have hmidHi : 2 ^ j ≤ 2 ^ (j + 1) := by
            rw [Nat.pow_succ]
            exact Nat.le_mul_of_pos_right _ (by norm_num)
          have hm₁ : 0 < primePoolMass (2 ^ a) (2 ^ j) := by
            have hbase := hMass a le_rfl
            have hblockHi : 2 ^ (a + 1) ≤ 2 ^ j := by
              dsimp [j]
              exact Nat.pow_le_pow_right (by omega) hExpPrev
            exact lt_of_lt_of_le hbase (primePoolMass_mono hblockHi)
          have hm₂ : 0 < primePoolMass (2 ^ j) (2 ^ (j + 1)) := by
            dsimp [j]
            exact hMass (a + (k + 1)) (by omega)
          have hlaw (r : Fin Q) :
              primePoolResidueLaw (2 ^ a) (2 ^ (j + 1)) Q r =
                (primePoolMass (2 ^ a) (2 ^ j) * primePoolResidueLaw (2 ^ a) (2 ^ j) Q r +
                  primePoolMass (2 ^ j) (2 ^ (j + 1)) *
                    primePoolResidueLaw (2 ^ j) (2 ^ (j + 1)) Q r) /
                  (primePoolMass (2 ^ a) (2 ^ j) + primePoolMass (2 ^ j) (2 ^ (j + 1))) := by
            exact primePoolResidueLaw_split hloMid hmidHi hm₁ hm₂ r
          have hlast := hErr j (by dsimp [j]; omega)
          have hmix := finiteL1_weighted_mix_bound
            (primePoolResidueLaw (2 ^ a) (2 ^ j) Q)
            (primePoolResidueLaw (2 ^ j) (2 ^ (j + 1)) Q)
            (uniformUnitResidueLaw Q)
            (primePoolMass (2 ^ a) (2 ^ j))
            (primePoolMass (2 ^ j) (2 ^ (j + 1))) ε
            hm₁ hm₂ hprev hlast
          have hLawFun : primePoolResidueLaw (2 ^ a) (2 ^ (a + Nat.succ (Nat.succ k))) Q =
              fun r => (primePoolMass (2 ^ a) (2 ^ j) * primePoolResidueLaw (2 ^ a) (2 ^ j) Q r +
                primePoolMass (2 ^ j) (2 ^ (j + 1)) * primePoolResidueLaw (2 ^ j) (2 ^ (j + 1)) Q r) /
                (primePoolMass (2 ^ a) (2 ^ j) + primePoolMass (2 ^ j) (2 ^ (j + 1))) := by
            simpa [j, Nat.add_assoc] using funext hlaw
          rw [hLawFun]
          exact hmix

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
  classical
  have hpowLower (n : ℕ) : n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hOne : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
  have hpow : Tendsto (fun n : ℕ => 2 ^ n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [] with n
    exact hpowLower n
  let err (Y : ℕ) :=
    finiteL1 (primePoolResidueLaw Y (2 * Y) Q) (uniformUnitResidueLaw Q)
  have hErrTendsto : Tendsto err atTop (𝓝 0) := by
    simpa [err] using
      (HindmanSumsProducts.Arithmetic.Outside.harmonic_prime_residue_equidistribution Q hQ)
  have hErrEventually : ∀ᶠ Y : ℕ in atTop, err Y ≤ ε := by
    filter_upwards [hErrTendsto.eventually (Metric.ball_mem_nhds 0 hε)] with Y hY
    have habs : |err Y| < ε := by simpa [Real.dist_eq] using hY
    exact le_of_lt (abs_lt.mp habs).2
  obtain ⟨C₀, c₀, hC₀, hc₀, hMassEventually⟩ :=
    HindmanSumsProducts.Arithmetic.Outside.dyadic_harmonic_prime_mass_and_atom_bound
  obtain ⟨Yerr, hYerr⟩ := (eventually_atTop.mp hErrEventually)
  obtain ⟨Ymass, hYmass⟩ := (eventually_atTop.mp hMassEventually)
  let a := max Yerr (max Ymass (max B 1))
  have hYerrA : Yerr ≤ a := by dsimp [a]; exact Nat.le_max_left _ _
  have hYmassA : Ymass ≤ a := by
    dsimp [a]
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hErrAt (j : ℕ) (hj : a ≤ j) :
      err (2 ^ j) ≤ ε := by
    exact hYerr (2 ^ j) ((hYerrA.trans hj).trans (hpowLower j))
  have hMassAt (j : ℕ) (hj : a ≤ j) :
      0 < primePoolMass (2 ^ j) (2 ^ (j + 1)) := by
    have hj1 : 1 ≤ j := by
      dsimp [a] at hj
      omega
    have hpowTwo : 2 ≤ 2 ^ j := by
      cases j with
      | zero => omega
      | succ j =>
          rw [pow_succ]
          have hOne : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
          nlinarith
    have hlog : 0 < Real.log (2 ^ j : ℝ) := Real.log_pos (by exact_mod_cast hpowTwo)
    have hlow : c₀ / Real.log (2 ^ j : ℝ) ≤
        primePoolMass (2 ^ j) (2 * 2 ^ j) := by
      have hJ : Ymass ≤ j := hYmassA.trans hj
      have hY : Ymass ≤ 2 ^ j := hJ.trans (hpowLower j)
      simpa [pow_succ, Nat.mul_comm] using (hYmass (2 ^ j) hY).1
    have hpos : 0 < c₀ / Real.log (2 ^ j : ℝ) := div_pos hc₀ hlog
    have hmass : 0 < primePoolMass (2 ^ j) (2 * 2 ^ j) := lt_of_lt_of_le hpos hlow
    simpa [pow_succ, Nat.mul_comm] using hmass
  have hCum : Tendsto
      (fun Y : ℕ => ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, 1 / (p : ℝ))
      atTop atTop := HindmanSumsProducts.Arithmetic.Outside.reciprocalPrimeSeries_tendsto_atTop
  let Cbelow : ℝ := ∑ p ∈ (Finset.range (2 ^ a)).filter Nat.Prime, 1 / (p : ℝ)
  have hCumLarge : ∀ᶠ Y : ℕ in atTop,
      (B : ℝ) + Cbelow + 2 ≤
        ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, 1 / (p : ℝ) :=
    hCum.eventually_ge_atTop _
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hCumLarge
  let b := max Y₀ (a + 1)
  have hab : a < b := by dsimp [b]; omega
  have hbasePow : B ≤ 2 ^ a := by
    have hBa : B ≤ a := by dsimp [a]; omega
    exact hBa.trans (hpowLower a)
  let lo := 2 ^ a
  let hi := 2 ^ b
  have hpowAB : lo < hi := by
    dsimp [lo, hi]
    exact Nat.pow_lt_pow_right (by norm_num) hab
  have hCumHi : (B : ℝ) + Cbelow + 2 ≤
      ∑ p ∈ (Finset.range (hi + 1)).filter Nat.Prime, 1 / (p : ℝ) := by
    apply hY₀
    dsimp [hi]
    exact (le_trans (Nat.le_max_left _ _) (hpowLower b))
  let s₀ := (Finset.range lo).filter Nat.Prime
  let s₁ := (Finset.Ico lo hi).filter Nat.Prime
  let s₂ := ({hi} : Finset ℕ).filter Nat.Prime
  have hparts :
      (Finset.range (hi + 1)).filter Nat.Prime = s₀ ∪ (s₁ ∪ s₂) := by
    have hlohi : lo ≤ hi := hpowAB.le
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_singleton, s₀, s₁, s₂]
    constructor
    · rintro ⟨hp, hprime⟩
      have hpLe : p ≤ hi := by omega
      by_cases hpLo : p < lo
      · exact Or.inl ⟨hpLo, hprime⟩
      · by_cases hpHi : p < hi
        · exact Or.inr (Or.inl ⟨⟨le_of_not_gt hpLo, hpHi⟩, hprime⟩)
        · have heq : p = hi := by omega
          exact Or.inr (Or.inr ⟨heq, hprime⟩)
    · rintro (⟨hpLo, hprime⟩ | (⟨⟨hlo', hhi'⟩, hprime⟩ | ⟨rfl, hprime⟩))
      · exact ⟨by omega, hprime⟩
      · exact ⟨by omega, hprime⟩
      · exact ⟨by omega, hprime⟩
  have hdisj01 : Disjoint s₀ s₁ := by
    apply Finset.disjoint_left.mpr
    intro p hp₀ hp₁
    have h₀ := Finset.mem_range.mp (Finset.mem_filter.mp hp₀).1
    have h₁ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₁).1
    omega
  have hdisj02 : Disjoint s₀ s₂ := by
    apply Finset.disjoint_left.mpr
    intro p hp₀ hp₂
    have h₀ := Finset.mem_range.mp (Finset.mem_filter.mp hp₀).1
    have h₂ := Finset.mem_singleton.mp (Finset.mem_filter.mp hp₂).1
    have hbelow : a < b := hab
    have hpowlt : lo < hi := hpowAB
    dsimp [lo, hi] at hpowlt
    omega
  have hdisj12 : Disjoint s₁ s₂ := by
    apply Finset.disjoint_left.mpr
    intro p hp₁ hp₂
    have h₁ := Finset.mem_Ico.mp (Finset.mem_filter.mp hp₁).1
    have h₂ := Finset.mem_singleton.mp (Finset.mem_filter.mp hp₂).1
    omega
  have hdisj0 : Disjoint s₀ (s₁ ∪ s₂) := by
    apply Finset.disjoint_left.mpr
    intro p hp₀ hp
    rcases Finset.mem_union.mp hp with hp₁ | hp₂
    · exact (Finset.disjoint_left.mp hdisj01) hp₀ hp₁
    · exact (Finset.disjoint_left.mp hdisj02) hp₀ hp₂
  have hmassSplit :
      (∑ p ∈ (Finset.range (hi + 1)).filter Nat.Prime, 1 / (p : ℝ)) =
        Cbelow + primePoolMass lo hi +
          (if hi.Prime then 1 / (hi : ℝ) else 0) := by
    have hs₀ : (∑ p ∈ s₀, 1 / (p : ℝ)) = Cbelow := rfl
    have hs₁ : (∑ p ∈ s₁, 1 / (p : ℝ)) = primePoolMass lo hi := rfl
    have hs₂ : (∑ p ∈ s₂, 1 / (p : ℝ)) =
        if hi.Prime then 1 / (hi : ℝ) else 0 := by
      change (∑ p ∈ ({hi} : Finset ℕ).filter Nat.Prime, 1 / (p : ℝ)) = _
      rw [Finset.sum_filter]
      by_cases hp : hi.Prime <;> simp [hp]
    calc
      _ = ∑ p ∈ s₀ ∪ (s₁ ∪ s₂), 1 / (p : ℝ) := by rw [hparts]
      _ = (∑ p ∈ s₀, 1 / (p : ℝ)) +
          ((∑ p ∈ s₁, 1 / (p : ℝ)) + ∑ p ∈ s₂, 1 / (p : ℝ)) := by
            rw [Finset.sum_union hdisj0, Finset.sum_union hdisj12]
      _ = Cbelow + primePoolMass lo hi +
          (if hi.Prime then 1 / (hi : ℝ) else 0) := by rw [hs₀, hs₁, hs₂]; ring
  have hend : (if hi.Prime then 1 / (hi : ℝ) else 0) ≤ 1 := by
    by_cases hp : hi.Prime
    · have hhi : 1 ≤ (hi : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by positivity : hi ≠ 0))
      have hpos : 0 < (hi : ℝ) := by positivity
      simp [hp]
      rw [← one_div]
      exact (div_le_one hpos).2 hhi
    · simp [hp]
  have hpoolMass : (B : ℝ) ≤ primePoolMass lo hi := by
    rw [hmassSplit] at hCumHi
    linarith
  have hpoolErr :
      finiteL1 (primePoolResidueLaw lo hi Q) (uniformUnitResidueLaw Q) ≤ ε := by
    have hk : 0 < b - a := Nat.sub_pos_of_lt hab
    have h := dyadicPoolResidueBound Q a (b - a) ε
      (fun j hj => by
        have he := hErrAt j hj
        simpa [err, pow_succ, Nat.mul_comm] using he)
      (fun j hj => hMassAt j hj) hk
    simpa [lo, hi, err, pow_succ, Nat.mul_comm,
      Nat.add_sub_of_le (Nat.le_of_lt hab)] using h
  let pool : PrimePool := {
    lower := lo
    upper := hi
    lower_pos := by dsimp [lo]; positivity
    lower_lt_upper := hpowAB
    lower_pow_two := ⟨a, rfl⟩
    upper_pow_two := ⟨b, rfl⟩
    consecutive_complete_intervals := ⟨b - a, by
      dsimp [lo, hi]
      calc
        2 ^ b = 2 ^ (a + (b - a)) := by congr 1; omega
        _ = 2 ^ a * 2 ^ (b - a) := Nat.pow_add _ _ _⟩
  }
  exact ⟨pool, hbasePow, hpoolMass, hpoolErr⟩


/-- Zero values and repeated slots in one pool (§3 lines 247–251, 304–313): the maximum atom
of the pool law is at most `1/(P^-·H^{pr})`, so the grid bound for each polynomial and for
each difference `x_i-x_j` gives this bound. -/
theorem pool_zero_or_repeat_bound {m : ℕ} (D : Finset (IntegerPolynomial m))
    (hD : ∀ P ∈ D, P ≠ 0) (lo hi : ℕ) (hlo : 0 < lo) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ : Fin m => hi)
        (polynomialZeroOrRepeated D) ≤
      (((∑ P ∈ D, MvPolynomial.totalDegree P) + m ^ 2 : ℕ) : ℝ) /
        ((lo : ℝ) * primePoolMass lo hi) := by
  classical
  by_cases hmass0 : primePoolMass lo hi = 0
  · have hLawZero (p : ℕ) : primePoolLaw lo hi p = 0 := by
      simp [primePoolLaw, hmass0]
    by_cases hm0 : m = 0
    · subst m
      have hEvalConst (Q : IntegerPolynomial 0) (hQ : Q ≠ 0)
          (p : Fin 0 → ℕ) :
          evalIntegerPolynomial Q (fun i => (p i : ℤ)) ≠ 0 := by
        have hc : Q.coeff 0 ≠ 0 := by
          intro hz
          apply hQ
          rw [Q.eq_C_of_isEmpty, hz]
          simp
        rw [Q.eq_C_of_isEmpty]
        simp [evalIntegerPolynomial, hc]
      have hEvent (p : Fin 0 → ℕ) : ¬ polynomialZeroOrRepeated D p := by
        intro h
        rcases h with hzero | hrep
        · rcases hzero with ⟨Q, hQD, hQzero⟩
          exact hEvalConst Q (hD Q hQD) p hQzero
        · rcases hrep with ⟨i, j, _, _⟩
          exact Fin.elim0 i
      have hprobzero :
          independentPrimePoolProbability (fun _ : Fin 0 => lo) (fun _ => hi)
            (polynomialZeroOrRepeated D) = 0 := by
        simp [independentPrimePoolProbability, hEvent]
      rw [hprobzero]
      simp [hmass0]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmassZero (p : Fin m → ℕ) :
          independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p = 0 := by
        unfold independentPrimePoolMass
        apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, hmpos⟩)
        exact hLawZero (p ⟨0, hmpos⟩)
      have hprobzero :
          independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
            (polynomialZeroOrRepeated D) = 0 := by
        unfold independentPrimePoolProbability
        simp [hmassZero]
      rw [hprobzero]
      simp [hmass0]
  · have hmass : 0 < primePoolMass lo hi := lt_of_le_of_ne
      (primePoolMass_nonneg_master lo hi) (Ne.symm hmass0)
    let μ : Fin m → ℕ → ℝ := fun _ => primePoolLaw lo hi
    let atom : ℝ := 1 / ((lo : ℝ) * primePoolMass lo hi)
    let zeroProduct : IntegerPolynomial m := ∏ P ∈ D, P
    let repeatFactor : Fin m → Fin m → IntegerPolynomial m := fun i j =>
      if i = j then 1 else MvPolynomial.X i - MvPolynomial.X j
    let repeatProduct : IntegerPolynomial m := ∏ i, ∏ j, repeatFactor i j
    let F : IntegerPolynomial m := zeroProduct * repeatProduct
    have hden : 0 < (lo : ℝ) * primePoolMass lo hi := by
      exact mul_pos (by exact_mod_cast hlo) hmass
    have hatom : 0 ≤ atom := by dsimp [atom]; positivity
    have hnonneg : ∀ i x, 0 ≤ μ i x := by
      intro i x
      exact primePoolLaw_nonneg_master lo hi x
    have hmax : ∀ i x, μ i x ≤ atom := by
      intro i x
      dsimp [μ]
      unfold primePoolLaw
      split_ifs with hx
      · have hloReal : (0 : ℝ) < lo := by exact_mod_cast hlo
        have hle : (lo : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
        have hinv : 1 / (x : ℝ) ≤ 1 / (lo : ℝ) :=
          one_div_le_one_div_of_le hloReal hle
        have hdiv := div_le_div_of_nonneg_right hinv (le_of_lt hmass)
        simpa [atom, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      · exact le_trans (by simp [primePoolLaw, hx]) hatom
    have hprob : ∀ i, ∑' x : ℕ, μ i x = 1 := by
      intro i
      exact primePoolLaw_tsum_eq_one_master hmass
    have hzeroProduct : zeroProduct ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro Q hQ
      exact hD Q hQ
    have hfactor (i j : Fin m) : repeatFactor i j ≠ 0 := by
      by_cases hij : i = j
      · simp [repeatFactor, hij]
      · have hX : MvPolynomial.X i ≠ (MvPolynomial.X j : IntegerPolynomial m) := by
          intro h
          exact hij ((MvPolynomial.X_inj i j).mp h)
        simpa [repeatFactor, hij] using sub_ne_zero.mpr hX
    have hrepeatProduct : repeatProduct ≠ 0 := by
      dsimp [repeatProduct]
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact hfactor i j
    have hF : F ≠ 0 := by
      dsimp [F]
      exact mul_ne_zero hzeroProduct hrepeatProduct
    have hdegZero : zeroProduct.totalDegree ≤ ∑ Q ∈ D, MvPolynomial.totalDegree Q := by
      dsimp [zeroProduct]
      exact MvPolynomial.totalDegree_finsetProd D id
    have hdegRepeat : repeatProduct.totalDegree ≤ m ^ 2 := by
      dsimp [repeatProduct]
      calc
        (∏ i : Fin m, ∏ j : Fin m, repeatFactor i j).totalDegree ≤
            ∑ i : Fin m, (∏ j : Fin m, repeatFactor i j).totalDegree :=
          MvPolynomial.totalDegree_finsetProd Finset.univ _
        _ ≤ ∑ i : Fin m, ∑ j : Fin m, (repeatFactor i j).totalDegree :=
          Finset.sum_le_sum fun i hi => MvPolynomial.totalDegree_finsetProd Finset.univ _
        _ ≤ ∑ i : Fin m, ∑ j : Fin m, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i = j
          · simp [repeatFactor, hij]
          · have hdegSub := MvPolynomial.totalDegree_sub
              (MvPolynomial.X i : IntegerPolynomial m) (MvPolynomial.X j)
            simpa [repeatFactor, hij] using hdegSub
        _ = m ^ 2 := by simp [Nat.pow_two]
    have hdegreeF : F.totalDegree ≤
        ∑ Q ∈ D, MvPolynomial.totalDegree Q + m ^ 2 := by
      dsimp [F]
      calc
        (zeroProduct * repeatProduct).totalDegree ≤
            zeroProduct.totalDegree + repeatProduct.totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ (∑ Q ∈ D, MvPolynomial.totalDegree Q) + m ^ 2 := Nat.add_le_add hdegZero hdegRepeat
    have hEvalZero (p : Fin m → ℕ) :
        evalIntegerPolynomial zeroProduct (fun i => (p i : ℤ)) = 0 ↔
          ∃ Q ∈ D, evalIntegerPolynomial Q (fun i => (p i : ℤ)) = 0 := by
      dsimp [zeroProduct, evalIntegerPolynomial]
      simp [MvPolynomial.eval_prod, Finset.prod_eq_zero_iff]
    have hEvalRepeat (p : Fin m → ℕ) :
      evalIntegerPolynomial repeatProduct (fun i => (p i : ℤ)) = 0 ↔
          ∃ i j, i ≠ j ∧ p i = p j := by
      dsimp [repeatProduct, repeatFactor, evalIntegerPolynomial]
      simp_rw [MvPolynomial.eval_prod]
      rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨i, hi, houter⟩
        rw [Finset.prod_eq_zero_iff] at houter
        rcases houter with ⟨j, hj, hfactorZero⟩
        by_cases hij : i = j
        · simp [hij] at hfactorZero
        · have hsub : (p i : ℤ) - (p j : ℤ) = 0 := by
            simpa [hij, MvPolynomial.eval_X] using hfactorZero
          exact ⟨i, j, hij, by exact_mod_cast (sub_eq_zero.mp hsub)⟩
      · rintro ⟨i, j, hij, hEq⟩
        refine ⟨i, Finset.mem_univ _, ?_⟩
        apply Finset.prod_eq_zero_iff.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        simp [hij, hEq]
    have hEvalF (p : Fin m → ℕ) :
        evalIntegerPolynomial F (fun i => (p i : ℤ)) = 0 ↔
          polynomialZeroOrRepeated D p := by
      have hmul : evalIntegerPolynomial F (fun i => (p i : ℤ)) =
          evalIntegerPolynomial zeroProduct (fun i => (p i : ℤ)) *
            evalIntegerPolynomial repeatProduct (fun i => (p i : ℤ)) := by
        simp [F, evalIntegerPolynomial, MvPolynomial.eval_mul]
      rw [hmul, mul_eq_zero, hEvalZero, hEvalRepeat]
      rfl
    have hgrid := polynomial_zero_product_grid_bound F hF μ atom hnonneg hmax hprob
    have hbound :
        independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
          (polynomialZeroOrRepeated D) ≤ (F.totalDegree : ℝ) * atom := by
      simpa [independentPrimePoolProbability, independentPrimePoolMass, μ, hEvalF] using hgrid
    calc
      independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi)
          (polynomialZeroOrRepeated D) ≤
          (F.totalDegree : ℝ) * atom := hbound
      _ ≤ (((∑ Q ∈ D, MvPolynomial.totalDegree Q) + m ^ 2 : ℕ) : ℝ) /
          ((lo : ℝ) * primePoolMass lo hi) := by
        dsimp [atom]
        have hcast : (F.totalDegree : ℝ) ≤
            (((∑ Q ∈ D, MvPolynomial.totalDegree Q) + m ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast hdegreeF
        calc
          (F.totalDegree : ℝ) * (1 / ((lo : ℝ) * primePoolMass lo hi)) =
              (F.totalDegree : ℝ) / ((lo : ℝ) * primePoolMass lo hi) := by ring
          _ ≤ (((∑ Q ∈ D, MvPolynomial.totalDegree Q) + m ^ 2 : ℕ) : ℝ) /
              ((lo : ℝ) * primePoolMass lo hi) :=
            div_le_div_of_nonneg_right hcast (le_of_lt hden)

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
  classical
  let tuples₀ : Finset (Fin m → ℕ) :=
    Finset.filter (fun p => ∀ i, lo ≤ p i ∧ p i < hi ∧ (p i).Prime)
      (Finset.univ.image (fun f : Fin m → Fin hi => fun i => (f i).val))
  let pairs := (tuples₀.product D).filter (fun z =>
    evalIntegerPolynomial z.2 (fun i => (z.1 i : ℤ)) ≠ 0)
  let vals := pairs.image (fun z =>
    M * (evalIntegerPolynomial z.2 (fun i => (z.1 i : ℤ))).natAbs)
  let prodVals : ℕ := ∏ v ∈ vals, v
  let R := M * L * (B + 1) * prodVals
  have hvalpos (v : ℕ) (hv : v ∈ vals) : 0 < v := by
    rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
    have hz' := (Finset.mem_filter.mp hz).2
    exact Nat.mul_pos hM (Int.natAbs_pos.mpr hz')
  have hvalsprod : 0 < prodVals := by
    dsimp [prodVals]
    exact Finset.prod_pos hvalpos
  have hRpos : 0 < R := by
    dsimp [R]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM hL) (by omega)) hvalsprod
  have hmult : 1 ≤ M * L * prodVals := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      have hp : 0 < M * L * prodVals := Nat.mul_pos (Nat.mul_pos hM hL) hvalsprod
      exact hp.ne')
  have hRlower : B ≤ R := by
    have hBmul : B + 1 ≤ (B + 1) * (M * L * prodVals) := by
      calc
        B + 1 = (B + 1) * 1 := by simp
        _ ≤ (B + 1) * (M * L * prodVals) := Nat.mul_le_mul_left _ hmult
    dsimp [R]
    nlinarith [hBmul]
  have hMdiv : M ∣ R := by
    refine ⟨L * (B + 1) * prodVals, ?_⟩
    dsimp [R]
    ring
  have hLdiv : L ∣ R := by
    refine ⟨M * (B + 1) * prodVals, ?_⟩
    dsimp [R]
    ring
  have hproddiv : prodVals ∣ R := by
    refine ⟨M * L * (B + 1), ?_⟩
    dsimp [R]
    ring
  refine ⟨R, hRpos, hRlower, hMdiv, hLdiv, ?_⟩
  intro p Q hQ hp hne
  have htuple : p ∈ tuples₀ := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨(fun i => ⟨p i, (hp i).2.1⟩), Finset.mem_univ _, ?_⟩
    rfl
  have hpair : (p, Q) ∈ pairs := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨htuple, hQ⟩, ?_⟩
    exact hne
  have hval :
      M * (evalIntegerPolynomial Q (fun i => (p i : ℤ))).natAbs ∈ vals := by
    apply Finset.mem_image.mpr
    exact ⟨(p, Q), hpair, rfl⟩
  exact (Finset.dvd_prod_of_mem (s := vals) (f := id) hval).trans hproddiv

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
