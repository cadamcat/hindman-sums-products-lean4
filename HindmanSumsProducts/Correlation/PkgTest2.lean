import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the uniform correlation test proof (lane `c-test2`). -/

namespace HindmanSumsProducts

attribute [local instance] Classical.propDecidable

open scoped BigOperators Topology
open Filter

theorem c_test2_nonTarget_card {m q r : ℕ} (Sh : RowShape m q r) :
    Fintype.card (NonTarget Sh) = r - 1 := by
  classical
  simp [NonTarget, Fintype.card_subtype_compl]

/-- If every sequence of parameters eventually satisfies a property, the property eventually
holds uniformly for all parameters. -/
theorem c_test2_eventually_forall_of_sequences {α : Type*} [Inhabited α]
    (P : ℕ → α → Prop)
    (hseq : ∀ a : ℕ → α, ∀ᶠ N in atTop, P N (a N)) :
    ∀ᶠ N in atTop, ∀ x : α, P N x := by
  classical
  by_contra h
  have hbad : ∀ N₀, ∃ N, N₀ ≤ N ∧ ∃ x, ¬ P N x := by
    intro N₀
    by_contra hN
    apply h
    apply eventually_atTop.2
    refine ⟨N₀, ?_⟩
    intro N hN₀ x
    by_contra hx
    exact hN ⟨N, hN₀, x, hx⟩
  let a : ℕ → α := fun N =>
    if hN : ∃ x, ¬ P N x then Classical.choose hN else default
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hseq a)
  obtain ⟨N, hN₀N, x, hx⟩ := hbad N₀
  have hp : P N (a N) := hN₀ N hN₀N
  have hnot : ¬ P N (a N) := by
    dsimp [a]
    by_cases hN : ∃ x, ¬ P N x
    · simp only [dif_pos hN]
      exact Classical.choose_spec hN
    · simp only [dif_neg hN]
      exact False.elim (hN ⟨x, hx⟩)
  exact hnot hp

def c_test2_harmonicIntSupport (X : ℕ) : Finset ℤ :=
  Finset.Ico (X : ℤ) (X ^ 2 : ℤ)

theorem c_test2_harmonicLaw_support {X W : ℕ} {z : ℤ}
    (hz : harmonicLaw X W z ≠ 0) :
    0 ≤ z ∧ (X : ℤ) ≤ z ∧ z < (X ^ 2 : ℤ) := by
  unfold harmonicLaw at hz
  by_cases hc : 0 ≤ z ∧ X ≤ z.toNat ∧ z.toNat < X ^ 2 ∧ Nat.Coprime z.toNat W
  · rcases hc with ⟨hz0, hX, htop, _⟩
    have hcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hX' : (X : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hX
    have htop' : (z.toNat : ℤ) < (X ^ 2 : ℤ) := by exact_mod_cast htop
    exact ⟨hz0, hcast ▸ hX', hcast ▸ htop'⟩
  · simp [hc] at hz

private theorem c_test2_harmonicLaw_zero_outside {X W : ℕ} {z : ℤ}
    (hz : z ∉ c_test2_harmonicIntSupport X) : harmonicLaw X W z = 0 := by
  by_contra hne
  have hs := c_test2_harmonicLaw_support hne
  have hm : z ∈ c_test2_harmonicIntSupport X := by
    simp only [c_test2_harmonicIntSupport, Finset.mem_Ico]
    exact ⟨hs.2.1, hs.2.2⟩
  exact hz hm

theorem c_test2_harmonicLaw_nonneg_of_normalizer_pos {X W : ℕ}
    (hZ : 0 < harmonicNormalizer X W) (z : ℤ) : 0 ≤ harmonicLaw X W z := by
  unfold harmonicLaw
  split_ifs <;> positivity

private theorem c_test2_sum_intIco_natCast (A B : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Ico (A : ℤ) (B : ℤ), f z) =
      ∑ n ∈ Finset.Ico A B, f (n : ℤ) := by
  classical
  have hmap : (Finset.Ico A B).map Nat.castEmbedding = Finset.Ico (A : ℤ) (B : ℤ) := by
    simpa [Nat.ModEq, Int.ModEq, Nat.mod_one, Int.emod_one] using
      (Nat.Ico_filter_modEq_cast A B (r := 1) (v := 0))
  rw [← hmap]
  simp

private theorem c_test2_tsum_intIco_natCast (A B : ℕ) (f : ℤ → ℝ)
    (hzero : ∀ z, z ∉ Finset.Ico (A : ℤ) (B : ℤ) → f z = 0) :
    (∑' z : ℤ, f z) = ∑ n ∈ Finset.Ico A B, f (n : ℤ) := by
  calc
    (∑' z : ℤ, f z) = ∑ z ∈ Finset.Ico (A : ℤ) (B : ℤ), f z :=
      tsum_eq_sum (s := Finset.Ico (A : ℤ) (B : ℤ)) hzero
    _ = ∑ n ∈ Finset.Ico A B, f (n : ℤ) := c_test2_sum_intIco_natCast A B f

theorem c_test2_harmonicLaw_tsum_one {X W : ℕ} (hX : 0 < X)
    (hZ : 0 < harmonicNormalizer X W) :
    ∑' z : ℤ, harmonicLaw X W z = 1 := by
  have hzero : ∀ z, z ∉ c_test2_harmonicIntSupport X → harmonicLaw X W z = 0 :=
    fun z hz => c_test2_harmonicLaw_zero_outside hz
  calc
    (∑' z : ℤ, harmonicLaw X W z) =
        ∑ n ∈ Finset.Ico X (X ^ 2), harmonicLaw X W (n : ℤ) := by
          simpa [c_test2_harmonicIntSupport] using
            c_test2_tsum_intIco_natCast X (X ^ 2) (harmonicLaw X W) hzero
    _ = ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
          1 / ((n : ℝ) * harmonicNormalizer X W) := by
        calc
          _ = ∑ n ∈ Finset.Ico X (X ^ 2),
                if Nat.Coprime n W then
                  1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn' := Finset.mem_Ico.mp hn
            have hformula : harmonicLaw X W (n : ℤ) =
                if Nat.Coprime n W then
                  1 / ((n : ℝ) * harmonicNormalizer X W) else 0 := by
              unfold harmonicLaw
              simp [hn'.1, hn'.2, Int.toNat_natCast]
            exact hformula
          _ = ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
                1 / ((n : ℝ) * harmonicNormalizer X W) := by
            rw [← Finset.sum_filter]
    _ = (1 / harmonicNormalizer X W) *
          ∑ n ∈ (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W),
            1 / (n : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnI : n ∈ Finset.Ico X (X ^ 2) := (Finset.mem_filter.mp hn).1
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le hX (Finset.mem_Ico.mp hnI).1)
      field_simp [ne_of_gt hZ, ne_of_gt hnpos]
    _ = 1 := by
      change (1 / harmonicNormalizer X W) * harmonicNormalizer X W = 1
      field_simp [ne_of_gt hZ]

private def c_test2_piFinsetSubtypeEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {β : Type*} (S : α → Finset β) :
    {f : α → β // f ∈ Fintype.piFinset S} ≃ (∀ i, {x : β // x ∈ S i}) where
  toFun f i := ⟨f.1 i, (Fintype.mem_piFinset.mp f.2 i)⟩
  invFun f := ⟨fun i => (f i).1, Fintype.mem_piFinset.mpr (fun i => (f i).2)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro f
    funext i
    apply Subtype.ext
    rfl

theorem c_test2_harmonicProductMass_tsum_one {α : Type*} [Fintype α] [DecidableEq α]
    (X : α → ℕ) (W : ℕ) (hX : ∀ i, 0 < X i)
    (hZ : ∀ i, 0 < harmonicNormalizer (X i) W) :
    ∑' z : α → ℤ, ∏ i, harmonicLaw (X i) W (z i) = 1 := by
  classical
  let support : α → Finset ℤ := fun i => c_test2_harmonicIntSupport (X i)
  let domain : Finset (α → ℤ) := Fintype.piFinset support
  have hzero : ∀ z ∉ domain, ∏ i, harmonicLaw (X i) W (z i) = 0 := by
    intro z hz
    have hnot : ¬ ∀ i, z i ∈ support i := by
      intro hall
      exact hz (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hLaw : harmonicLaw (X i) W (z i) = 0 :=
      c_test2_harmonicLaw_zero_outside (by simpa [support] using hi)
    exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
  have hsum :
      (∑' z : α → ℤ, ∏ i, harmonicLaw (X i) W (z i)) =
        ∑ z ∈ domain, ∏ i, harmonicLaw (X i) W (z i) :=
    tsum_eq_sum (s := domain) hzero
  have hattach : (∑ z ∈ domain, ∏ i, harmonicLaw (X i) W (z i)) =
      ∑ z : domain, ∏ i, harmonicLaw (X i) W (z.1 i) := by
    rw [← Finset.sum_attach]
    simp
  rw [hsum, hattach]
  let e := c_test2_piFinsetSubtypeEquiv support
  have htransport :
      (∑ z : domain, ∏ i, harmonicLaw (X i) W (z.1 i)) =
        ∑ z : (∀ i, {x : ℤ // x ∈ support i}),
          ∏ i, harmonicLaw (X i) W (z i).1 := by
    apply Fintype.sum_equiv e
    intro z
    simp [e, c_test2_piFinsetSubtypeEquiv]
  rw [htransport]
  have hfactor : ∀ i, (∑ x : {x : ℤ // x ∈ support i},
      harmonicLaw (X i) W x.1) = 1 := by
    intro i
    let f : ℤ → ℝ := harmonicLaw (X i) W
    have hsumi : (∑ x : {x : ℤ // x ∈ support i}, f x.1) =
        ∑ x ∈ support i, f x := by
      rw [← Finset.sum_subtype (s := support i) (h := fun _ => Iff.rfl)]
    have htsum : (∑' x : ℤ, f x) = ∑ x ∈ support i, f x := by
      apply tsum_eq_sum (s := support i)
      intro x hx
      exact c_test2_harmonicLaw_zero_outside (by simpa [f, support] using hx)
    rw [hsumi, ← htsum]
    exact c_test2_harmonicLaw_tsum_one (hX i) (hZ i)
  calc
    (∑ x : ∀ i, {x : ℤ // x ∈ support i},
        ∏ i, harmonicLaw (X i) W (x i).1) =
      ∏ i, ∑ x : {x : ℤ // x ∈ support i}, harmonicLaw (X i) W x.1 := by
        symm
        exact Fintype.prod_sum fun i (x : {x : ℤ // x ∈ support i}) =>
          harmonicLaw (X i) W x.1
    _ = 1 := by
      have hfactorAttach : ∀ i, (∑ x ∈ (support i).attach,
          harmonicLaw (X i) W x.1) = 1 := by
        intro i
        simpa using hfactor i
      simp [hfactorAttach]

private theorem c_test2_productMass_tsum_one {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℕ → ℝ) (S : α → Finset ℕ)
    (hzero : ∀ i n, n ∉ S i → f i n = 0)
    (hmass : ∀ i, ∑' n : ℕ, f i n = 1) :
    ∑' z : α → ℕ, ∏ i, f i (z i) = 1 := by
  classical
  let domain : Finset (α → ℕ) := Fintype.piFinset S
  have hzeroProd : ∀ z ∉ domain, ∏ i, f i (z i) = 0 := by
    intro z hz
    have hnot : ¬ ∀ i, z i ∈ S i := by
      intro hall
      exact hz (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (z i) hi)
  have hsum : (∑' z : α → ℕ, ∏ i, f i (z i)) =
      ∑ z ∈ domain, ∏ i, f i (z i) := tsum_eq_sum (s := domain) hzeroProd
  have hattach : (∑ z ∈ domain, ∏ i, f i (z i)) =
      ∑ z : domain, ∏ i, f i (z.1 i) := by
    rw [← Finset.sum_attach]
    simp
  rw [hsum, hattach]
  let e := c_test2_piFinsetSubtypeEquiv S
  have htransport :
      (∑ z : domain, ∏ i, f i (z.1 i)) =
        ∑ z : (∀ i, {x : ℕ // x ∈ S i}), ∏ i, f i (z i).1 := by
    apply Fintype.sum_equiv e
    intro z
    simp [e, c_test2_piFinsetSubtypeEquiv]
  rw [htransport]
  have hfactor : ∀ i, (∑ x : {x : ℕ // x ∈ S i}, f i x.1) = 1 := by
    intro i
    have hsumI : (∑ x : {x : ℕ // x ∈ S i}, f i x.1) =
        ∑ x ∈ S i, f i x := by
      rw [← Finset.sum_subtype (s := S i) (h := fun _ => Iff.rfl)]
    have htsum : (∑' x : ℕ, f i x) = ∑ x ∈ S i, f i x := by
      apply tsum_eq_sum (s := S i)
      intro x hx
      exact hzero i x hx
    rw [hsumI, ← htsum]
    exact hmass i
  calc
    (∑ x : ∀ i, {x : ℕ // x ∈ S i}, ∏ i, f i (x i).1) =
      ∏ i, ∑ x : {x : ℕ // x ∈ S i}, f i x.1 := by
        symm
        exact Fintype.prod_sum fun i (x : {x : ℕ // x ∈ S i}) => f i x.1
    _ = 1 := by
      have hfactorAttach : ∀ i, (∑ x ∈ (S i).attach, f i x.1) = 1 := by
        intro i
        simpa using hfactor i
      simp [hfactorAttach]

private theorem c_test2_primePoolLaw_zero_outside (lo hi p : ℕ)
    (hp : p ∉ Finset.Ico lo hi) : primePoolLaw lo hi p = 0 := by
  unfold primePoolLaw
  split_ifs with h
  · exact (hp (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)).elim
  · rfl

private theorem c_test2_primePoolLaw_tsum_one (lo hi : ℕ)
    (hpos : 0 < primePoolMass lo hi) :
    ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  have hzero : ∀ p, p ∉ Finset.Ico lo hi → primePoolLaw lo hi p = 0 :=
    fun p hp => c_test2_primePoolLaw_zero_outside lo hi p hp
  calc
    (∑' p : ℕ, primePoolLaw lo hi p) =
        ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p :=
      tsum_eq_sum (s := Finset.Ico lo hi) hzero
    _ = ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
          (1 / (p : ℝ)) / primePoolMass lo hi := by
      calc
        _ = ∑ p ∈ Finset.Ico lo hi,
              if p.Prime then (1 / (p : ℝ)) / primePoolMass lo hi else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [primePoolLaw, Finset.mem_Ico.mp hp]
        _ = ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
              (1 / (p : ℝ)) / primePoolMass lo hi := by
          rw [← Finset.sum_filter]
    _ = (∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime, 1 / (p : ℝ)) /
          primePoolMass lo hi := by rw [Finset.sum_div]
    _ = 1 := by
      change primePoolMass lo hi / primePoolMass lo hi = 1
      exact div_self (ne_of_gt hpos)

private theorem c_test2_primePoolLaw_nonneg (lo hi p : ℕ)
    (hpos : 0 < primePoolMass lo hi) : 0 ≤ primePoolLaw lo hi p := by
  unfold primePoolLaw
  split_ifs with h
  · rcases h with ⟨_, _, hp⟩
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    exact div_nonneg (div_nonneg (by positivity) (le_of_lt hpR)) (le_of_lt hpos)
  · simp

private theorem c_test2_primePoolMass_nonneg (lo hi : ℕ) :
    0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  apply Finset.sum_nonneg
  intro p hp
  exact one_div_nonneg.mpr (Nat.cast_nonneg p)

private theorem c_test2_primePoolLaw_nonneg_any (lo hi p : ℕ) :
    0 ≤ primePoolLaw lo hi p := by
  unfold primePoolLaw
  split_ifs with h
  · exact div_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg p))
      (c_test2_primePoolMass_nonneg lo hi)
  · simp

theorem c_test2_independentPrimePoolMass_zero_outside {q : ℕ}
    (lo hi : Fin q → ℕ) (p : Fin q → ℕ)
    (hp : p ∉ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnot : ¬ ∀ i, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    exact hp (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hidx⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact c_test2_primePoolLaw_zero_outside (lo i) (hi i) (p i) hidx

theorem c_test2_independentPrimePoolMass_nonneg {q : ℕ}
    (lo hi : Fin q → ℕ) (hpos : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (p : Fin q → ℕ) : 0 ≤ independentPrimePoolMass lo hi p := by
  unfold independentPrimePoolMass
  apply Finset.prod_nonneg
  intro i _
  exact c_test2_primePoolLaw_nonneg (lo i) (hi i) (p i) (hpos i)

theorem c_test2_independentPrimePoolProbability_nonneg {q : ℕ}
    (lo hi : Fin q → ℕ) (E : (Fin q → ℕ) → Prop) :
    0 ≤ independentPrimePoolProbability lo hi E := by
  classical
  unfold independentPrimePoolProbability
  apply tsum_nonneg
  intro p
  unfold independentPrimePoolMass
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i _
    exact c_test2_primePoolLaw_nonneg_any (lo i) (hi i) (p i)
  · split_ifs <;> positivity

private theorem c_test2_independentProbability_summable {q : ℕ}
    (lo hi : Fin q → ℕ) (E : (Fin q → ℕ) → Prop) :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero
    (s := Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))
  intro p hp
  rw [c_test2_independentPrimePoolMass_zero_outside lo hi p hp]
  simp

private theorem c_test2_independentMass_tsum_one {q : ℕ}
    (lo hi : Fin q → ℕ) (hpos : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    ∑' p : Fin q → ℕ, independentPrimePoolMass lo hi p = 1 := by
  let f : Fin q → ℕ → ℝ := fun i n => primePoolLaw (lo i) (hi i) n
  let S : Fin q → Finset ℕ := fun i => Finset.Ico (lo i) (hi i)
  have hzero : ∀ i n, n ∉ S i → f i n = 0 := by
    intro i n hn
    exact c_test2_primePoolLaw_zero_outside (lo i) (hi i) n (by simpa [S] using hn)
  have hsum : ∀ i, ∑' n : ℕ, f i n = 1 := by
    intro i
    exact c_test2_primePoolLaw_tsum_one (lo i) (hi i) (hpos i)
  simpa [independentPrimePoolMass, f] using c_test2_productMass_tsum_one f S hzero hsum

private theorem c_test2_independentProbability_add_compl {q : ℕ}
    (lo hi : Fin q → ℕ) (hpos : ∀ i, 0 < primePoolMass (lo i) (hi i))
    (E : (Fin q → ℕ) → Prop) :
    independentPrimePoolProbability lo hi E +
      independentPrimePoolProbability lo hi (fun p => ¬ E p) = 1 := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  letI : DecidablePred (fun p : Fin q → ℕ => ¬ E p) :=
    fun p => Classical.propDecidable (¬ E p)
  have hE := c_test2_independentProbability_summable lo hi E
  have hNot := c_test2_independentProbability_summable lo hi (fun p => ¬ E p)
  calc
    independentPrimePoolProbability lo hi E +
        independentPrimePoolProbability lo hi (fun p => ¬ E p) =
      ∑' p, ((independentPrimePoolMass lo hi p * if E p then 1 else 0) +
        (independentPrimePoolMass lo hi p * if ¬ E p then 1 else 0)) := by
          unfold independentPrimePoolProbability
          exact (hE.tsum_add hNot).symm
    _ = ∑' p, independentPrimePoolMass lo hi p := by
      apply tsum_congr
      intro p
      by_cases hp : E p <;> simp [hp]
    _ = 1 := c_test2_independentMass_tsum_one lo hi hpos

theorem c_test2_goodSlotProbability_pos_eventually {K s q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K)
    (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (hbad : Tendsto (fun N => gapSlotProbability S l N
      (fun p => ¬ GoodTuple S l N tests Dpoly p)) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, 0 < gapSlotProbability S l N
      (fun p => GoodTuple S l N tests Dpoly p) := by
  have hpool : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper := by
    have hlarge :=
      (S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)).eventually_ge_atTop 1
    filter_upwards [hlarge] with N hN
    have hV : 0 < (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
      unfold FromArithmetic.masterScaleV
      positivity
    have hratio : 1 ≤ (primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper : ℝ) /
        (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
      simpa [Real.rpow_one] using hN
    have hm := (le_div_iff₀ hV).mp hratio
    have hm' : (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ≤
        primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper := by
      simpa using hm
    have hmpos : 0 < (primePoolMass (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper : ℝ) := lt_of_lt_of_le hV hm'
    exact_mod_cast hmpos
  have hbadlt : ∀ᶠ N in atTop,
      gapSlotProbability S l N (fun p => ¬ GoodTuple S l N tests Dpoly p) < 1 := by
    have h := hbad.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact h
  filter_upwards [hpool, hbadlt] with N hpoolN hbadN
  have hsplit := c_test2_independentProbability_add_compl
    (fun _ : Fin q => (S.primeStage.pool N l).lower)
    (fun _ => (S.primeStage.pool N l).upper) (fun _ => hpoolN)
    (fun p => GoodTuple S l N tests Dpoly p)
  have hsplit' :
      gapSlotProbability S l N (fun p => GoodTuple S l N tests Dpoly p) +
        gapSlotProbability S l N (fun p => ¬ GoodTuple S l N tests Dpoly p) = 1 := by
    simpa [gapSlotProbability] using hsplit
  linarith

/-- A one-row witness can be padded by a harmless singleton row. The singleton support differs
from the distinguished support, which has at least two coordinates. -/
def c_test2_singletonRow {m q : ℕ} (i : Fin m) : RowTemplate m q where
  entry := fun k => if k = i then some (fun _ => 0) else none
  support_nonempty := ⟨i, by simp [RowTemplate.support]⟩
  slots_disjoint := by
    intro k k' e e' hkk he he' slot
    by_cases hk : k = i <;> by_cases hk' : k' = i <;>
      simp_all

@[simp]
theorem c_test2_singletonRow_support {m q : ℕ} (i : Fin m) :
    (c_test2_singletonRow (q := q) i).support = {i} := by
  ext k
  simp [c_test2_singletonRow, RowTemplate.support]

@[simp]
theorem c_test2_singletonRow_anchor {m q : ℕ} (i : Fin m) :
    (c_test2_singletonRow (q := q) i).anchor = i := by
  unfold RowTemplate.anchor
  simp [c_test2_singletonRow_support]

/-- Add one harmless row to a one-row shape. -/
def c_test2_padSingletonShape {m q : ℕ} (Sh : RowShape m q 1) (i : Fin m)
    (Jstar : Finset (Fin m)) (hJcard : 2 ≤ Jstar.card)
    (hstar : (Sh.row Sh.star).support = Jstar) : RowShape m q 2 where
  row := fun R => if R = 0 then Sh.row Sh.star else c_test2_singletonRow i
  star := 0
  nonparallel := by
    intro R I hRI
    fin_cases R <;> fin_cases I
    · exact (hRI rfl).elim
    · intro hpar
      have hs : Jstar = {i} := by
        calc
          Jstar = (Sh.row Sh.star).support := hstar.symm
          _ = (c_test2_singletonRow (q := q) i).support := by simpa using hpar.1
          _ = {i} := c_test2_singletonRow_support (q := q) i
      have hc := congrArg Finset.card hs
      simp at hc
      omega
    · intro hpar
      have hs : Jstar = {i} := by
        calc
          Jstar = (Sh.row Sh.star).support := hstar.symm
          _ = (c_test2_singletonRow (q := q) i).support := by simpa using hpar.1.symm
          _ = {i} := c_test2_singletonRow_support (q := q) i
      have hc := congrArg Finset.card hs
      simp at hc
      omega
    · exact (hRI rfl).elim

@[simp]
theorem c_test2_padSingletonShape_star_row {m q : ℕ} (Sh : RowShape m q 1)
    (i : Fin m) (Jstar : Finset (Fin m)) (hJcard : 2 ≤ Jstar.card)
    (hstar : (Sh.row Sh.star).support = Jstar) :
    (c_test2_padSingletonShape Sh i Jstar hJcard hstar).row 0 = Sh.row Sh.star := by
  simp [c_test2_padSingletonShape]

private theorem c_test2_singletonRow_form_integral {m q : ℕ} (c : Fin m → ℚ)
    (i : Fin m) (p : Fin q → ℕ) (z : Fin m → ℤ) :
    (rowForm c (c_test2_singletonRow (q := q) i) p (fun k => (z k : ℚ))).den = 1 := by
  classical
  let D := c_test2_singletonRow (q := q) i
  have hanchor : D.anchor = i := by
    simp [D, RowTemplate.anchor, c_test2_singletonRow_support]
  have hvalue (k : Fin m) : D.value p k = if k = i then 1 else 0 := by
    by_cases hk : k = i
    · rw [hk]
      simp [D, RowTemplate.value, c_test2_singletonRow]
    · simp [D, RowTemplate.value, c_test2_singletonRow, hk]
  unfold rowForm
  change (∑ k, c k / c D.anchor * D.value p k * (z k : ℚ)).den = 1
  rw [hanchor]
  simp_rw [hvalue]
  rw [Finset.sum_eq_single i]
  · by_cases hc : c i = 0
    · simp [hc]
    · simp [hc]
  · intro k hk hki
    simp [hki]
  · simp

def c_test2_padSingletonFunction {q : ℕ}
    (f : Fin 1 → (Fin q → ℕ) → ℤ → ℝ) : Fin 2 → (Fin q → ℕ) → ℤ → ℝ :=
  fun R => if R = 0 then f 0 else fun _ _ => 1

theorem c_test2_rowCorrelation_padSingleton
    {K m q s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (Sh : RowShape m q 1)
    (Jstar : Finset (Fin m)) (hJcard : 2 ≤ Jstar.card)
    (hstar : (Sh.row Sh.star).support = Jstar) (i : Fin m)
    (f : Fin 1 → (Fin q → ℕ) → ℤ → ℝ) :
    rowCorrelation S C a N (c_test2_padSingletonShape Sh i Jstar hJcard hstar)
      (c_test2_padSingletonFunction f) = rowCorrelation S C a N Sh f := by
  classical
  have hstarFin : Sh.star = 0 := Subsingleton.elim _ _
  unfold rowCorrelation
  apply congrArg (fun F : (Fin q → ℕ) → ℝ => gapSlotAverage S C.gap N F)
  funext p
  apply tsum_congr
  intro z
  have hrow0 :
      (c_test2_padSingletonShape Sh i Jstar hJcard hstar).row 0 = Sh.row Sh.star := by
    simp [c_test2_padSingletonShape]
  have hdummy :
      (rowForm (chainScale S.core.parameters C a N)
        (c_test2_singletonRow (q := q) i) p (fun k => (z k : ℚ))).den = 1 :=
    c_test2_singletonRow_form_integral _ _ _ _
  simp [c_test2_padSingletonShape, c_test2_padSingletonFunction,
    hstarFin, hrow0, hdummy, atQ, Fin.prod_univ_two]

/-- Turn an arbitrarily small error in an integer-power bound into the desired fractional-power
bound. -/
theorem c_test2_root_power_bound {n : ℕ} (hn : 0 < n)
    (x z A δ ε : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) (hA : 0 < A) (hε : 0 < ε)
    (hpow : x ^ n ≤ A * z + δ) (hδ : δ ≤ (ε / 2) ^ n) :
    x ≤ ε + (2 * A) ^ (1 / (n : ℝ)) * z ^ (1 / (n : ℝ)) := by
  by_cases hxe : x ≤ ε
  · calc
      x ≤ ε := hxe
      _ ≤ ε + (2 * A) ^ (1 / (n : ℝ)) * z ^ (1 / (n : ℝ)) := by
        have hrootA : 0 ≤ (2 * A) ^ (1 / (n : ℝ)) :=
          Real.rpow_nonneg (by positivity) _
        have hrootZ : 0 ≤ z ^ (1 / (n : ℝ)) := Real.rpow_nonneg hz _
        have hprod : 0 ≤ (2 * A) ^ (1 / (n : ℝ)) * z ^ (1 / (n : ℝ)) :=
          mul_nonneg hrootA hrootZ
        linarith
  · have hxe' : ε < x := lt_of_not_ge hxe
    have hhalf : ε / 2 ≤ x / 2 := by linarith
    have hhalfPow : (ε / 2) ^ n ≤ (x / 2) ^ n := by
      exact pow_le_pow_left₀ (by positivity) hhalf n
    have hpow2 : 2 ≤ (2 : ℝ) ^ n := by
      cases n with
      | zero => omega
      | succ n =>
        simp [pow_succ]
        have hnat : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
        exact_mod_cast hnat
    have hdivide : (x / 2) ^ n ≤ x ^ n / 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_left (by positivity : 0 ≤ x ^ n) (by norm_num)
        (by exact_mod_cast hpow2)
    have hdelta : δ ≤ x ^ n / 2 := hδ.trans (hhalfPow.trans hdivide)
    have hpow' : x ^ n ≤ 2 * A * z := by linarith
    have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ x ^ n) hpow'
      (by positivity : 0 ≤ 1 / (n : ℝ))
    have hleft : (x ^ n) ^ (1 / (n : ℝ)) = x := by
      simpa [one_div] using
        (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ x) (Nat.ne_of_gt hn))
    have hright : (2 * A * z) ^ (1 / (n : ℝ)) =
        (2 * A) ^ (1 / (n : ℝ)) * z ^ (1 / (n : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hz]
    rw [hleft, hright] at hroot
    exact le_trans hroot (by linarith)

theorem c_test2_dominates_of_power_bound {f S T : ℕ → ℝ}
    (hF : ∀ n, 0 ≤ f n) (hS : ∀ n, 0 < S n) (hT : ∀ n, 0 < T n)
    (P : ℝ) (hP : 0 < P)
    (hTS : ∀ᶠ n in atTop, T n ≤ (S n) ^ P)
    (hDom : OAI.MicrocellScale.Dominates f S) :
    OAI.MicrocellScale.Dominates f T := by
  intro C hC
  have hDom' := hDom (P * C) (mul_pos hP hC)
  have hle : (fun n => f n / (S n) ^ (P * C)) ≤ᶠ[atTop]
      (fun n => f n / (T n) ^ C) := by
    filter_upwards [hTS] with n hn
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos (hS n) (P * C))
      (Real.rpow_pos_of_pos (hT n) C)]
    have hp : (T n) ^ C ≤ ((S n) ^ P) ^ C :=
      Real.rpow_le_rpow (le_of_lt (hT n)) hn hC.le
    have hp' : (T n) ^ C ≤ (S n) ^ (P * C) := by
      calc
        (T n) ^ C ≤ ((S n) ^ P) ^ C := hp
        _ = (S n) ^ (P * C) := (Real.rpow_mul (le_of_lt (hS n)) P C).symm
    exact mul_le_mul_of_nonneg_left hp' (hF n)
  exact Filter.tendsto_atTop_mono' atTop hle hDom'

theorem c_test2_natSamplerTargetBound {x c e : ℕ} (hx : 4 ≤ x) (hc : c + 2 ≤ x) :
    2 + 2 * x + x ^ e + c * x ^ (e + 3) ≤ x ^ (e + 4) := by
  have hx2 : 2 ≤ x := by omega
  have hxpos : 0 < x := by omega
  have hx2sq : 4 ≤ x ^ 2 := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ x * x := Nat.mul_le_mul hx2 hx2
      _ = x ^ 2 := by simp [pow_two]
  have hx3 : 4 * x ≤ x ^ 3 := by
    calc
      4 * x ≤ x ^ 2 * x := Nat.mul_le_mul_right x hx2sq
      _ = x ^ 3 := by simp [pow_succ, pow_two, Nat.mul_assoc, Nat.mul_comm]
  have h3e : x ^ 3 ≤ x ^ (e + 3) :=
    Nat.pow_le_pow_right hxpos (by omega)
  have he : x ^ e ≤ x ^ (e + 3) :=
    Nat.pow_le_pow_right hxpos (by omega)
  have hsmall : 2 + 2 * x ≤ x ^ (e + 3) := by
    have hlin : 2 + 2 * x ≤ 4 * x := by omega
    exact hlin.trans (hx3.trans h3e)
  have htwo : 2 + 2 * x + x ^ e ≤ 2 * x ^ (e + 3) := by omega
  calc
    2 + 2 * x + x ^ e + c * x ^ (e + 3) ≤
        (c + 2) * x ^ (e + 3) := by nlinarith [htwo]
    _ ≤ x * x ^ (e + 3) := Nat.mul_le_mul_right _ hc
    _ = x ^ (e + 4) := by rw [pow_succ]; ring

theorem c_test2_cutoffLog_dominates_powerTarget {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n)
    (T : ℕ → ℕ) (hTpos : ∀ N, 0 < T N) (P : ℕ) (hP : 0 < P)
    (hbound : ∀ᶠ N in atTop, T N ≤ (A.H N i) ^ P) :
    OAI.MicrocellScale.Dominates (fun N => Real.log (A.X N i : ℝ))
      (fun N => (T N : ℝ)) := by
  have hF : ∀ N, 0 ≤ Real.log (A.X N i : ℝ) := by
    intro N
    obtain ⟨e, he⟩ := A.Xpow N i
    rw [he]
    have hone : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast hone)
  have hS : ∀ N, 0 < (A.H N i : ℝ) := fun N => by exact_mod_cast A.Hpos N i
  have hT : ∀ N, 0 < (T N : ℝ) := fun N => by exact_mod_cast hTpos N
  have hboundR : ∀ᶠ N in atTop,
      (T N : ℝ) ≤ (A.H N i : ℝ) ^ (P : ℝ) := by
    filter_upwards [hbound] with N hN
    exact_mod_cast hN
  exact c_test2_dominates_of_power_bound hF hS hT (P : ℝ)
    (by exact_mod_cast hP) hboundR (A.Xdom i)

def c_test2_rowExponent {m q : ℕ} (T : RowTemplate m q) : ℕ :=
  ∑ k : Fin m, ∑ i : Fin q, (T.entry k).elim 0 fun e => e i

def c_test2_rowValueNat {m q : ℕ} (T : RowTemplate m q) (p : Fin q → ℕ)
    (k : Fin m) : ℕ := (T.entry k).elim 0 fun e => ∏ i, p i ^ e i

theorem c_test2_rowValue_eq_cast {m q : ℕ} (T : RowTemplate m q) (p : Fin q → ℕ)
    (k : Fin m) : T.value p k = (c_test2_rowValueNat T p k : ℚ) := by
  cases he : T.entry k <;>
    simp [RowTemplate.value, c_test2_rowValueNat, he, map_prod, Nat.cast_pow]

private lemma c_test2_rowTemplate_value_eq_eval_poly {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (p : Fin q → ℕ) :
    (evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) : ℚ) = T.value p k := by
  cases h : T.entry k with
  | none => simp [RowTemplate.poly, RowTemplate.value, h, evalIntegerPolynomial]
  | some e =>
      simp only [RowTemplate.poly, RowTemplate.value, h]
      change (MvPolynomial.eval (fun i => (p i : ℤ))
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1) : ℚ) =
          ∏ i, (p i : ℚ) ^ e i
      have he : ∀ i, (Finsupp.equivFunOnFinite.symm e) i = e i := by
        intro i
        exact congrFun (Finsupp.coe_equivFunOnFinite_symm e) i
      rw [MvPolynomial.eval_monomial]
      simp [Finsupp.prod_fintype, he]

theorem c_test2_rowTemplate_poly_eval_nat {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (k : Fin m) :
    evalIntegerPolynomial (T.poly k) (fun i => (p i : ℤ)) =
      (c_test2_rowValueNat T p k : ℤ) := by
  have hq := c_test2_rowTemplate_value_eq_eval_poly T k p
  rw [c_test2_rowValue_eq_cast T p k] at hq
  exact_mod_cast hq

theorem c_test2_rowTemplate_minor_eval {m q : ℕ} (T U : RowTemplate m q)
    (p : Fin q → ℕ) (i j : Fin m) :
    evalIntegerPolynomial (T.poly i * U.poly j - T.poly j * U.poly i)
      (fun k => (p k : ℤ)) =
      (c_test2_rowValueNat T p i * c_test2_rowValueNat U p j -
        c_test2_rowValueNat T p j * c_test2_rowValueNat U p i : ℤ) := by
  change MvPolynomial.eval (fun k => (p k : ℤ))
      (T.poly i * U.poly j - T.poly j * U.poly i) = _
  simp only [map_sub, map_mul]
  have hTi : MvPolynomial.eval (fun k => (p k : ℤ)) (T.poly i) =
      (c_test2_rowValueNat T p i : ℤ) := by
    simpa [evalIntegerPolynomial] using c_test2_rowTemplate_poly_eval_nat T p i
  have hUj : MvPolynomial.eval (fun k => (p k : ℤ)) (U.poly j) =
      (c_test2_rowValueNat U p j : ℤ) := by
    simpa [evalIntegerPolynomial] using c_test2_rowTemplate_poly_eval_nat U p j
  have hTj : MvPolynomial.eval (fun k => (p k : ℤ)) (T.poly j) =
      (c_test2_rowValueNat T p j : ℤ) := by
    simpa [evalIntegerPolynomial] using c_test2_rowTemplate_poly_eval_nat T p j
  have hUi : MvPolynomial.eval (fun k => (p k : ℤ)) (U.poly i) =
      (c_test2_rowValueNat U p i : ℤ) := by
    simpa [evalIntegerPolynomial] using c_test2_rowTemplate_poly_eval_nat U p i
  rw [hTi, hUj, hTj, hUi]

theorem c_test2_rowValueNat_le {m q : ℕ} (T : RowTemplate m q) (p : Fin q → ℕ)
    (size : ℕ) (hsize : 0 < size) (hp : ∀ i, p i ≤ size) (k : Fin m) :
    c_test2_rowValueNat T p k ≤ size ^ c_test2_rowExponent T := by
  classical
  by_cases hk : T.entry k = none
  · simp [c_test2_rowValueNat, hk]
  · obtain ⟨e, he⟩ : ∃ e, T.entry k = some e := by
      cases h : T.entry k with
      | none => exact (hk h).elim
      | some e => exact ⟨e, rfl⟩
    have hprod : (∏ i : Fin q, p i ^ e i) ≤ ∏ i : Fin q, size ^ e i := by
      apply Finset.prod_le_prod
      intro i hi
      exact Nat.pow_le_pow_left (hp i) _
    have hsum : (∑ i : Fin q, e i) ≤ c_test2_rowExponent T := by
      calc
        (∑ i : Fin q, e i) = ∑ i : Fin q, (T.entry k).elim 0 (fun e => e i) := by
          simp [he]
        _ ≤ ∑ j : Fin m, ∑ i : Fin q, (T.entry j).elim 0 (fun e => e i) :=
          Finset.single_le_sum (f := fun j : Fin m =>
            ∑ i : Fin q, (T.entry j).elim 0 (fun e => e i))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    calc
      c_test2_rowValueNat T p k = ∏ i : Fin q, p i ^ e i := by
        simp [c_test2_rowValueNat, he]
      _ ≤ ∏ i : Fin q, size ^ e i := hprod
      _ = size ^ (∑ i : Fin q, e i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ size ^ c_test2_rowExponent T :=
        Nat.pow_le_pow_right hsize hsum

theorem c_test2_monomials_coprime {q : ℕ} (e f : Fin q → ℕ) (p : Fin q → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hdisj : ∀ i, e i = 0 ∨ f i = 0) :
    Nat.Coprime (∏ i, p i ^ e i) (∏ i, p i ^ f i) := by
  classical
  rw [Nat.coprime_fintype_prod_left_iff]
  intro i
  rw [Nat.coprime_fintype_prod_right_iff]
  intro j
  by_cases hij : i = j
  · subst j
    rcases hdisj i with he | hf
    · simp [he]
    · simp [hf]
  · have hne : p i ≠ p j := fun heq => hij (hinj heq)
    exact Nat.coprime_pow_primes (e i) (f j) (hp i) (hp j) hne

theorem c_test2_rowValues_coprime {m q : ℕ} (T : RowTemplate m q)
    (j k : Fin m) (p : Fin q → ℕ) (hj : ∃ e, T.entry j = some e)
    (hk : ∃ f, T.entry k = some f) (hjk : j ≠ k)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) :
    Nat.Coprime (c_test2_rowValueNat T p j) (c_test2_rowValueNat T p k) := by
  obtain ⟨e, he⟩ := hj
  obtain ⟨f, hf⟩ := hk
  have hdisj : ∀ i, e i = 0 ∨ f i = 0 := T.slots_disjoint j k e f hjk he hf
  simpa [c_test2_rowValueNat, he, hf] using
    c_test2_monomials_coprime e f p hp hinj hdisj 

theorem c_test2_rowValueNat_pos_of_entry {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (i : Fin m) (hi : ∃ e, T.entry i = some e)
    (hp : ∀ j, 0 < p j) : 0 < c_test2_rowValueNat T p i := by
  obtain ⟨e, he⟩ := hi
  change 0 < (T.entry i).elim 0 (fun e => ∏ j : Fin q, p j ^ e j)
  rw [he]
  exact Finset.prod_pos (fun j hj => Nat.pow_pos (hp j))

private theorem c_test2_harmonicNatLaw_nonneg (X W n : ℕ) :
    0 ≤ harmonicNatLaw X W n := by
  have hZ : 0 ≤ harmonicNormalizer X W := by
    unfold harmonicNormalizer
    apply Finset.sum_nonneg
    intro x hx
    exact div_nonneg (by positivity) (by positivity)
  unfold harmonicNatLaw
  split_ifs <;> positivity

private theorem c_test2_parameterTailProductLaw_nonneg {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) (σ : ℕ) :
    0 ≤ FromArithmetic.parameterTailProductLaw A N T σ := by
  classical
  unfold FromArithmetic.parameterTailProductLaw
  apply tsum_nonneg
  intro t
  by_cases hprod : (∏ j ∈ T, t j) = σ
  · simp [hprod]
    apply Finset.prod_nonneg
    intro j hj
    exact c_test2_harmonicNatLaw_nonneg _ _ _
  · simp [hprod]

def c_test2_ScaleData {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) : Prop :=
  ∃ c : Fin m → ℤ,
    (∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d) ∧
    (∀ d, 0 < c d) ∧
    (∀ u d, u < d → ∃ k : ℕ,
      c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d) ∧
    ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ)

theorem c_test2_chainCoefficientData_eventually {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, c_test2_ScaleData S C a N := by
  filter_upwards [S.core.chain_coefficients, S.gapStage.coefficient_divides_modulus]
    with N hchain hdiv
  obtain ⟨c, hc, hcpos, hratio⟩ := hchain m C a ha
  refine ⟨c, ?_, hcpos, hratio, ?_⟩
  · simpa [chainScale] using hc
  · exact hdiv m C a ha c hc

private theorem c_test2_scaleRatioNat {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ) (c : Fin m → ℤ)
    (hpos : ∀ d, 0 < c d)
    (hratio : ∀ u d, u < d → ∃ t : ℕ,
      c u = (primorial (N + 1) : ℤ) * (t : ℤ) * c d)
    (hmod : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    (i d : Fin m) (hid : i < d) :
    ∃ ρ : ℕ, 0 < ρ ∧ (ρ : ℚ) = (c i : ℚ) / (c d : ℚ) ∧
      primorial (N + 1) ∣ ρ ∧ ρ ∣ S.core.parameters.M N := by
  obtain ⟨t, ht⟩ := hratio i d hid
  have htpos : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0] at ht
    simp at ht
    exact (ne_of_gt (hpos i)) ht
  let ρ : ℕ := primorial (N + 1) * t
  have hρpos : 0 < ρ := Nat.mul_pos (primorial_pos _) htpos
  have hrel : c i = (ρ : ℤ) * c d := by
    dsimp [ρ]
    rw [ht]
  have hrelQ : (c i : ℚ) = (ρ : ℚ) * (c d : ℚ) := by exact_mod_cast hrel
  have hcd : (c d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (hpos d)
  have hratioQ : (ρ : ℚ) = (c i : ℚ) / (c d : ℚ) := by
    rw [hrelQ]
    field_simp [hcd]
  have hW : primorial (N + 1) ∣ ρ := ⟨t, rfl⟩
  have hciM : c i ∣ (S.core.parameters.M N : ℤ) := by
    have hdvd : c i ∣
        ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c i :=
      ⟨(primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ), by ring⟩
    exact hdvd.trans (hmod i)
  have hρci : (ρ : ℤ) ∣ c i := ⟨c d, hrel⟩
  have hρMInt : (ρ : ℤ) ∣ (S.core.parameters.M N : ℤ) := hρci.trans hciM
  have hρM : ρ ∣ S.core.parameters.M N := Int.natCast_dvd_natCast.mp hρMInt
  exact ⟨ρ, hρpos, hratioQ, hW, hρM⟩

theorem c_test2_scaleRatioNat_public {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ) (c : Fin m → ℤ)
    (hpos : ∀ d, 0 < c d)
    (hratio : ∀ u d, u < d → ∃ t : ℕ,
      c u = (primorial (N + 1) : ℤ) * (t : ℤ) * c d)
    (hmod : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    (i d : Fin m) (hid : i < d) :
    ∃ ρ : ℕ, 0 < ρ ∧ (ρ : ℚ) = (c i : ℚ) / (c d : ℚ) ∧
      primorial (N + 1) ∣ ρ ∧ ρ ∣ S.core.parameters.M N :=
  c_test2_scaleRatioNat S N c hpos hratio hmod i d hid

theorem c_test2_evalIntegerPolynomial_rename {q s : ℕ}
    (ι : Fin q ↪ Fin s) (P : IntegerPolynomial q) (p : Fin s → ℕ) :
    evalIntegerPolynomial (MvPolynomial.rename ι P) (fun i => (p i : ℤ)) =
      evalIntegerPolynomial P (fun i => (p (ι i) : ℤ)) := by
  change MvPolynomial.eval (fun i => (p i : ℤ)) (MvPolynomial.rename ι P) =
    MvPolynomial.eval (fun i => (p (ι i) : ℤ)) P
  rw [MvPolynomial.eval_rename]
  rfl

theorem c_test2_rationalResidue_natCast {r : ℕ} (hr : r.Prime) (n : ℕ) :
    FromArithmetic.rationalResidue r hr (n : ℚ) = (n : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  simp [FromArithmetic.rationalResidue]

theorem c_test2_prime_not_divides_masterModulus {K s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N r : ℕ)
    (hr : r.Prime) (hlarge : N + 1 < r) :
    ¬ (r : ℤ) ∣ (S.core.parameters.M N : ℤ) := by
  obtain ⟨e, he⟩ := S.core.modulus_power N
  have hW : ¬ r ∣ primorial (N + 1) := by
    intro hdiv
    exact Nat.not_le_of_gt hlarge (hr.dvd_primorial_iff.mp hdiv)
  intro hdiv
  have hdivNat : r ∣ S.core.parameters.M N := Int.natCast_dvd.mp hdiv
  rw [he] at hdivNat
  exact hW (hr.dvd_of_dvd_pow hdivNat)

theorem c_test2_scaleRatio_rationalResidue_ne_zero {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ) (c : Fin m → ℤ)
    (hpos : ∀ d, 0 < c d)
    (hratio : ∀ u d, u < d → ∃ t : ℕ,
      c u = (primorial (N + 1) : ℤ) * (t : ℤ) * c d)
    (hmod : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    (i d : Fin m) (hid : i < d) (r : ℕ) (hr : r.Prime)
    (hlarge : N + 1 < r) :
    FromArithmetic.rationalResidue r hr ((c i : ℚ) / (c d : ℚ)) ≠ 0 := by
  obtain ⟨rho, hrhoPos, hrhoQ, hWrho, hrhoM⟩ :=
    c_test2_scaleRatioNat_public S N c hpos hratio hmod i d hid
  have hMnot := c_test2_prime_not_divides_masterModulus S N r hr hlarge
  have hrhoNot : ¬ r ∣ rho := by
    intro hdiv
    apply hMnot
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdiv) (Int.natCast_dvd_natCast.mpr hrhoM)
  have hcastNZ : (rho : ZMod r) ≠ 0 := by
    intro hz
    exact hrhoNot ((ZMod.natCast_eq_zero_iff rho r).mp hz)
  have hres := c_test2_rationalResidue_natCast hr rho
  rw [hrhoQ] at hres
  rw [hres]
  exact hcastNZ

-- Adapted from HindmanSumsProducts/Correlation/PkgRows.lean.
private lemma c_test2_rowPoly_ne_zero_of_some {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) : T.poly k ≠ 0 := by
  simp [RowTemplate.poly, he]

private lemma c_test2_rowPoly_mul_entry {m q : ℕ} (T : RowTemplate m q)
    (k : Fin m) (e : Fin q → ℕ) (he : T.entry k = some e) :
    T.poly k = MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) (1 : ℤ) := by
  simp [RowTemplate.poly, he]

private lemma c_test2_parallel_of_all_minors_zero {m q : ℕ} (T U : RowTemplate m q)
    (hminor : ∀ j k, T.poly j * U.poly k - T.poly k * U.poly j = 0) :
    T.Parallel U := by
  classical
  have hentry : ∀ k, (T.entry k).isSome ↔ (U.entry k).isSome := by
    intro k
    constructor
    · intro hk
      by_contra hkU
      obtain ⟨e, he⟩ := (Option.isSome_iff_exists).mp hk
      obtain ⟨j, hjmem⟩ := U.support_nonempty
      have hj : (U.entry j).isSome := by simpa [RowTemplate.support] using hjmem
      obtain ⟨f, hf⟩ := (Option.isSome_iff_exists).mp hj
      have hprod : T.poly k * U.poly j ≠ 0 :=
        mul_ne_zero (c_test2_rowPoly_ne_zero_of_some T k e he)
          (c_test2_rowPoly_ne_zero_of_some U j f hf)
      have hkU0 : U.poly k = 0 := by
        cases h : U.entry k with
        | none => simp [RowTemplate.poly, h]
        | some f' => exact (hkU (by simp [h])).elim
      have hz := hminor k j
      exact hprod (by simpa [hkU0] using hz)
    · intro hk
      by_contra hkT
      obtain ⟨e, he⟩ := (Option.isSome_iff_exists).mp hk
      obtain ⟨j, hjmem⟩ := T.support_nonempty
      have hj : (T.entry j).isSome := by simpa [RowTemplate.support] using hjmem
      obtain ⟨f, hf⟩ := (Option.isSome_iff_exists).mp hj
      have hprod : U.poly k * T.poly j ≠ 0 :=
        mul_ne_zero (c_test2_rowPoly_ne_zero_of_some U k e he)
          (c_test2_rowPoly_ne_zero_of_some T j f hf)
      have hkT0 : T.poly k = 0 := by
        cases h : T.entry k with
        | none => simp [RowTemplate.poly, h]
        | some f' => exact (hkT (by simp [h])).elim
      have hz := hminor j k
      exact hprod (by
        have hz' : T.poly j * U.poly k = 0 := by simpa [hkT0] using hz
        simpa [mul_comm] using hz')
  have hsupport : T.support = U.support := by
    ext k
    simp [RowTemplate.support, hentry k]
  have hdelta : ∃ δ : Fin q → ℤ, ∀ k e e', T.entry k = some e → U.entry k = some e' →
      ∀ i, (e' i : ℤ) = e i + δ i := by
    obtain ⟨k₀, hk₀mem⟩ := T.support_nonempty
    have hk₀ : (T.entry k₀).isSome := by simpa [RowTemplate.support] using hk₀mem
    obtain ⟨e₀, he₀⟩ := (Option.isSome_iff_exists).mp hk₀
    have hu₀ : (U.entry k₀).isSome := by
      have : k₀ ∈ U.support := by rw [← hsupport]; exact hk₀mem
      simpa [RowTemplate.support] using this
    obtain ⟨f₀, hf₀⟩ := (Option.isSome_iff_exists).mp hu₀
    refine ⟨fun i => (f₀ i : ℤ) - e₀ i, ?_⟩
    intro k e f he hf i
    have hminor' := hminor k₀ k
    have hmon : T.poly k₀ * U.poly k = T.poly k * U.poly k₀ := sub_eq_zero.mp hminor'
    rw [c_test2_rowPoly_mul_entry T k₀ e₀ he₀, c_test2_rowPoly_mul_entry U k f hf,
      c_test2_rowPoly_mul_entry T k e he, c_test2_rowPoly_mul_entry U k₀ f₀ hf₀] at hmon
    have hexp : Finsupp.equivFunOnFinite.symm e₀ + Finsupp.equivFunOnFinite.symm f =
        Finsupp.equivFunOnFinite.symm e + Finsupp.equivFunOnFinite.symm f₀ := by
      rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial] at hmon
      exact (MvPolynomial.monomial_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)) hmon
    have hcoords := congrArg Finsupp.equivFunOnFinite hexp
    have hcoords' : e₀ + f = e + f₀ := by
      ext i
      simpa [Finsupp.equivFunOnFinite] using congrFun hcoords i
    have hcast : (e₀ i : ℤ) + f i = e i + f₀ i := by
      exact_mod_cast congrFun hcoords' i
    change (f i : ℤ) = (e i : ℤ) + ((f₀ i : ℤ) - e₀ i)
    omega
  exact ⟨hsupport, hdelta⟩

private lemma c_test2_exists_separating_minor {m q : ℕ} (T U : RowTemplate m q)
    (hpar : ¬ T.Parallel U) :
    ∃ j k, U.poly j * T.poly k - U.poly k * T.poly j ≠ 0 := by
  obtain ⟨j, k, h⟩ : ∃ j k, T.poly j * U.poly k - T.poly k * U.poly j ≠ 0 := by
    by_contra h
    apply hpar
    apply c_test2_parallel_of_all_minors_zero T U
    intro j k
    by_contra hz
    exact h ⟨j, k, hz⟩
  refine ⟨j, k, ?_⟩
  intro hz
  apply h
  calc
    T.poly j * U.poly k - T.poly k * U.poly j =
        -(U.poly j * T.poly k - U.poly k * T.poly j) := by ring
    _ = 0 := by rw [hz]; simp

private lemma c_test2_rowPoly_zero_of_not_mem_support {m q : ℕ}
    (T : RowTemplate m q) (i : Fin m) (hi : i ∉ T.support) : T.poly i = 0 := by
  cases he : T.entry i with
  | none => simp [RowTemplate.poly, he]
  | some e =>
      have : i ∈ T.support := by simp [RowTemplate.support, he]
      exact (hi this).elim

theorem c_test2_nonparallel_minor_witness {m q : ℕ} (T U : RowTemplate m q)
    (hpar : ¬ T.Parallel U) :
    ∃ i j,
      (i ∈ T.support ∧ i ∈ U.support ∧ j ∈ T.support ∧ j ∈ U.support ∧
        T.poly i * U.poly j - T.poly j * U.poly i ≠ 0) ∨
      (i ∈ T.support ∧ i ∉ U.support ∧ j ∈ U.support ∧
        T.poly i * U.poly j - T.poly j * U.poly i ≠ 0) ∨
      (i ∈ U.support ∧ i ∉ T.support ∧ j ∈ T.support ∧
        T.poly i * U.poly j - T.poly j * U.poly i ≠ 0) := by
  classical
  by_cases hs : T.support = U.support
  · obtain ⟨i, j, hminor⟩ := c_test2_exists_separating_minor T U hpar
    have hminor' : T.poly i * U.poly j - T.poly j * U.poly i ≠ 0 := by
      have hflip : T.poly i * U.poly j - T.poly j * U.poly i =
          -(U.poly i * T.poly j - U.poly j * T.poly i) := by ring
      rw [hflip]
      exact neg_ne_zero.mpr hminor
    have hiT : i ∈ T.support := by
      by_contra hi
      have hiU : i ∉ U.support := by simpa [hs] using hi
      simp [c_test2_rowPoly_zero_of_not_mem_support T i hi,
        c_test2_rowPoly_zero_of_not_mem_support U i hiU] at hminor
    have hjT : j ∈ T.support := by
      by_contra hj
      have hjU : j ∉ U.support := by simpa [hs] using hj
      simp [c_test2_rowPoly_zero_of_not_mem_support T j hj,
        c_test2_rowPoly_zero_of_not_mem_support U j hjU] at hminor
    exact ⟨i, j, Or.inl ⟨hiT, by simpa [hs] using hiT,
      hjT, by simpa [hs] using hjT, hminor'⟩⟩
  · have hdiff : T.support ≠ U.support := hs
    have hne : ∃ i, (i ∈ T.support ∧ i ∉ U.support) ∨
        (i ∈ U.support ∧ i ∉ T.support) := by
      by_contra h
      apply hdiff
      ext i
      constructor
      · intro hi
        by_cases hu : i ∈ U.support
        · exact hu
        · exact False.elim (h ⟨i, Or.inl ⟨hi, hu⟩⟩)
      · intro hi
        by_cases ht : i ∈ T.support
        · exact ht
        · exact False.elim (h ⟨i, Or.inr ⟨hi, ht⟩⟩)
    obtain ⟨i, hi⟩ := hne
    rcases hi with hi | hi
    · obtain ⟨j, hj⟩ := U.support_nonempty
      have hiSome : (T.entry i).isSome := by simpa [RowTemplate.support] using hi.1
      obtain ⟨ei, hei⟩ := (Option.isSome_iff_exists).mp hiSome
      have hpolyI : T.poly i ≠ 0 := c_test2_rowPoly_ne_zero_of_some T i ei hei
      have hjSome : (U.entry j).isSome := by simpa [RowTemplate.support] using hj
      obtain ⟨ej, hej⟩ := (Option.isSome_iff_exists).mp hjSome
      have hpolyJ : U.poly j ≠ 0 := c_test2_rowPoly_ne_zero_of_some U j ej hej
      have hzeroUi : U.poly i = 0 :=
        c_test2_rowPoly_zero_of_not_mem_support U i hi.2
      have hminor : T.poly i * U.poly j - T.poly j * U.poly i ≠ 0 := by
        rw [hzeroUi, mul_zero, sub_zero]
        exact mul_ne_zero hpolyI hpolyJ
      exact ⟨i, j, Or.inr (Or.inl ⟨hi.1, hi.2, hj, hminor⟩)⟩
    · obtain ⟨j, hj⟩ := T.support_nonempty
      have hiSome : (U.entry i).isSome := by simpa [RowTemplate.support] using hi.1
      obtain ⟨ei, hei⟩ := (Option.isSome_iff_exists).mp hiSome
      have hpolyI : U.poly i ≠ 0 := c_test2_rowPoly_ne_zero_of_some U i ei hei
      have hjSome : (T.entry j).isSome := by simpa [RowTemplate.support] using hj
      obtain ⟨ej, hej⟩ := (Option.isSome_iff_exists).mp hjSome
      have hpolyJ : T.poly j ≠ 0 := c_test2_rowPoly_ne_zero_of_some T j ej hej
      have hzeroTi : T.poly i = 0 :=
        c_test2_rowPoly_zero_of_not_mem_support T i hi.2
      have hprod : T.poly j * U.poly i ≠ 0 := mul_ne_zero hpolyJ hpolyI
      have hminor : T.poly i * U.poly j - T.poly j * U.poly i ≠ 0 := by
        simpa [hzeroTi] using (neg_ne_zero.mpr hprod)
      exact ⟨i, j, Or.inr (Or.inr ⟨hi.1, hi.2, hj, hminor⟩)⟩

theorem c_test2_rowCoefficientRepresentation {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (hscale : c_test2_ScaleData S C a N)
    (T : RowTemplate m q) (p : Fin q → ℕ) :
    ∃ alpha : Fin m → ℕ, ∀ i,
      chainScale S.core.parameters C a N i / chainScale S.core.parameters C a N T.anchor *
        T.value p i = (alpha i : ℚ) := by
  classical
  rcases Classical.choose_spec hscale with ⟨hc, hcpos, hratio, hmod⟩
  let cint := Classical.choose hscale
  let c : Fin m → ℚ := chainScale S.core.parameters C a N
  let rho : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then
      Classical.choose (c_test2_scaleRatioNat S N cint hcpos hratio hmod i T.anchor hi)
    else 1
  let alpha : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then rho i * c_test2_rowValueNat T p i
    else if i = T.anchor then c_test2_rowValueNat T p i else 0
  have hrho (i : Fin m) (hi : i < T.anchor) :
      (rho i : ℚ) = (cint i : ℚ) / (cint T.anchor : ℚ) := by
    simpa [rho, hi] using (Classical.choose_spec
      (c_test2_scaleRatioNat S N cint hcpos hratio hmod i T.anchor hi)).2.1
  have hnone (i : Fin m) (hi : T.anchor < i) : T.entry i = none := by
    by_contra hsome
    obtain ⟨e, he⟩ : ∃ e, T.entry i = some e := by
      cases h : T.entry i with
      | none => exact (hsome h).elim
      | some e => exact ⟨e, rfl⟩
    have hmem : i ∈ T.support := by simpa [RowTemplate.support, he]
    have hle := Finset.le_max' T.support i hmem
    change i ≤ T.anchor at hle
    omega
  refine ⟨alpha, ?_⟩
  intro i
  have hc' (j : Fin m) : (cint j : ℚ) = c j := by
    simpa [c, cint, chainScale] using hc j
  by_cases hi : i < T.anchor
  · calc
      c i / c T.anchor * T.value p i =
          ((cint i : ℚ) / (cint T.anchor : ℚ)) * T.value p i := by
            rw [hc' i, hc' T.anchor]
      _ = (rho i : ℚ) * (c_test2_rowValueNat T p i : ℚ) := by
            rw [hrho i hi, c_test2_rowValue_eq_cast]
      _ = (alpha i : ℚ) := by simp [alpha, hi]
  · by_cases hEq : i = T.anchor
    · subst i
      have hcne : c T.anchor ≠ 0 := by
        rw [← hc' T.anchor]
        exact_mod_cast ne_of_gt (hcpos T.anchor)
      calc
        c T.anchor / c T.anchor * T.value p T.anchor = T.value p T.anchor := by
          field_simp
        _ = (c_test2_rowValueNat T p T.anchor : ℚ) := c_test2_rowValue_eq_cast T p T.anchor
        _ = (alpha T.anchor : ℚ) := by simp [alpha]
    · have hgt : T.anchor < i := by omega
      have hval : T.value p i = 0 := by simp [RowTemplate.value, hnone i hgt]
      rw [hval]
      simp [alpha, hi, hEq]

theorem c_test2_masterSize_le_pivotGap_eventually {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (d : Fin m) (hgap : C.gap < (C.block d).1) :
    ∀ᶠ N in atTop,
      (S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
        S.core.parameters.H N (C.block d).1 := by
  let A := S.core.parameters
  have hlarge :=
    (S.gapStage.gap_dominates_pool_and_bound C.gap 1 (by norm_num)).eventually_ge_atTop 1
  filter_upwards [hlarge] with N hN
  let size := (S.primeStage.pool N C.gap).upper +
    FromArithmetic.masterScaleV A N C.gap
  have hsizePos : 0 < (size : ℝ) := by
    dsimp [size, FromArithmetic.masterScaleV]
    positivity
  have hratio : 1 ≤ (A.H N C.gap : ℝ) / (size : ℝ) := by
    simpa [size, Real.rpow_one] using hN
  have hsizeLeReal : (size : ℝ) ≤ A.H N C.gap := (one_le_div hsizePos).mp hratio
  have hsizeLe : size ≤ A.H N C.gap := by exact_mod_cast hsizeLeReal
  have hdiv : A.H N C.gap ∣ A.H N (C.block d).1 :=
    S.gapStage.earlier_gaps_divide N C.gap (C.block d).1 hgap
  exact hsizeLe.trans (Nat.le_of_dvd (A.Hpos N (C.block d).1) hdiv)

theorem c_test2_previous_le_gap_eventually {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) :
    ∀ᶠ N in atTop,
      OAI.SourceAdmissible.previous (A.X N) i ≤ A.H N i := by
  let E : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale A.M
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hlarge := (A.Hdom i 1 (by norm_num)).eventually_ge_atTop 1
  filter_upwards [hlarge] with N hN
  have hEpos : 0 < E N := by
    dsimp [E, OAI.AdmissibleMicrocellBoundary.earlierScale]
    positivity
  have hratio : 1 ≤ (A.H N i : ℝ) / E N := by
    simpa [E, Real.rpow_one] using hN
  have hle := (one_le_div hEpos).mp hratio
  have hprev : (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ≤ A.H N i := by
    dsimp [E, OAI.AdmissibleMicrocellBoundary.earlierScale] at hle
    linarith
  exact_mod_cast hprev

theorem c_test2_pivot_cutoff_le_previous {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m)
    (u d : Fin m) (hud : u < d) (N : ℕ) :
    A.X N (C.block u).1 ≤ OAI.SourceAdmissible.previous (A.X N) (C.block d).1 := by
  let E := Finset.univ.filter fun i : Fin n => i < (C.block d).1
  have hindex : (C.block u).1 ∈ E :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.pivots_ordered u d hud⟩
  have hsubset : { (C.block u).1 } ⊆ E := by
    intro i hi
    simpa using (Finset.mem_singleton.mp hi).symm ▸ hindex
  have hprod :
      (∏ i ∈ ({(C.block u).1} : Finset (Fin n)), A.X N i) ≤
        ∏ i ∈ E, A.X N i := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsubset
    intro i hi hin
    exact Nat.one_le_iff_ne_zero.mpr (A.Xpos N i).ne'
  have hone :
      (∏ i ∈ ({(C.block u).1} : Finset (Fin n)), A.X N i) = A.X N (C.block u).1 := by
    simp
  simpa [OAI.SourceAdmissible.previous, E, hone] using hprod

theorem c_test2_targetCoeffData {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (N : ℕ)
    (c : Fin m → ℤ) (hcpos : ∀ d, 0 < c d)
    (hratio : ∀ u d, u < d → ∃ t : ℕ,
      c u = (primorial (N + 1) : ℤ) * (t : ℤ) * c d)
    (hmod : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ))
    (T : RowTemplate m q) (j : Fin m) (hj : j ∈ T.support) (hja : j < T.anchor)
    (p : Fin q → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hpinj : Function.Injective p)
    (hlarge : ∀ i, primorial (N + 1) < p i)
    (size : ℕ) (hsize : 0 < size) (hpbound : ∀ i, p i ≤ size)
    (hMle : S.core.parameters.M N ≤ size) :
    ∃ alpha : Fin m → ℕ,
      (∀ i, alpha i ≤ size ^ (c_test2_rowExponent T + 1)) ∧
      (∀ i, i < T.anchor → primorial (N + 1) ∣ alpha i) ∧
      0 < alpha T.anchor ∧ 0 < alpha j ∧
      primorial (N + 1) ∣ alpha j ∧
      Nat.Coprime (alpha T.anchor) (primorial (N + 1)) ∧
      Nat.Coprime (alpha j) (alpha T.anchor) ∧
      alpha T.anchor ≤ size ^ c_test2_rowExponent T ∧
      alpha j ≤ size ^ (c_test2_rowExponent T + 1) ∧
      ∀ i, (c i : ℚ) / (c T.anchor : ℚ) * T.value p i = (alpha i : ℚ) := by
  classical
  let rho : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then
      Classical.choose (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
    else 1
  let alpha : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then rho i * c_test2_rowValueNat T p i
    else if i = T.anchor then c_test2_rowValueNat T p i else 0
  have hentryA : ∃ e, T.entry T.anchor = some e := by
    have hmem : T.anchor ∈ T.support := Finset.max'_mem T.support T.support_nonempty
    have hisSome : (T.entry T.anchor).isSome := by
      simpa [RowTemplate.support] using hmem
    exact Option.isSome_iff_exists.mp hisSome
  have hentryJ : ∃ e, T.entry j = some e := by
    have hisSome : (T.entry j).isSome := by
      simpa [RowTemplate.support] using hj
    exact Option.isSome_iff_exists.mp hisSome
  have hvalA : 0 < c_test2_rowValueNat T p T.anchor :=
    c_test2_rowValueNat_pos_of_entry T p T.anchor hentryA (fun i => (hp i).pos)
  have hvalJ : 0 < c_test2_rowValueNat T p j :=
    c_test2_rowValueNat_pos_of_entry T p j hentryJ (fun i => (hp i).pos)
  have hWpos : 0 < primorial (N + 1) := primorial_pos _
  have hpW : ∀ i, Nat.Coprime (p i) (primorial (N + 1)) := by
    intro i
    apply (hp i).coprime_iff_not_dvd.mpr
    intro hd
    have hle := Nat.le_of_dvd hWpos hd
    have hgt := hlarge i
    omega
  have hKcop : Nat.Coprime (c_test2_rowValueNat T p T.anchor) (primorial (N + 1)) := by
    obtain ⟨e, he⟩ := hentryA
    have hprod : Nat.Coprime (∏ i, p i ^ e i) (primorial (N + 1)) := by
      rw [Nat.coprime_fintype_prod_left_iff]
      intro i
      by_cases hei : e i = 0
      · simp [hei]
      · exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hei) (p i)
          (primorial (N + 1))).2 (hpW i)
    simpa [c_test2_rowValueNat, he] using hprod
  have hrowCop : Nat.Coprime (c_test2_rowValueNat T p j)
      (c_test2_rowValueNat T p T.anchor) :=
    c_test2_rowValues_coprime T j T.anchor p hentryJ hentryA (by omega) hp hpinj
  have hAnchorAlpha : alpha T.anchor = c_test2_rowValueNat T p T.anchor := by
    simp [alpha]
  have hLowerAlpha : alpha j = rho j * c_test2_rowValueNat T p j := by
    simp [alpha, hja]
  have hKpos : 0 < alpha T.anchor := by rw [hAnchorAlpha]; exact hvalA
  let ρj := Classical.choose (c_test2_scaleRatioNat S N c hcpos hratio hmod j T.anchor hja)
  have hρjSpec := Classical.choose_spec
    (c_test2_scaleRatioNat S N c hcpos hratio hmod j T.anchor hja)
  have hρjEq : rho j = ρj := by simp [rho, hja, ρj]
  have hBpos : 0 < alpha j := by
    rw [hLowerAlpha, hρjEq]
    exact Nat.mul_pos hρjSpec.1 hvalJ
  have hAlphaBound : ∀ i, alpha i ≤ size ^ (c_test2_rowExponent T + 1) := by
    intro i
    by_cases hi : i < T.anchor
    · let ρi := Classical.choose (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
      have hρspec := Classical.choose_spec
        (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
      have hρeq' : rho i = ρi := by simp [rho, hi, ρi]
      have hρle : rho i ≤ S.core.parameters.M N := by
        rw [hρeq']
        exact Nat.le_of_dvd (S.core.parameters.Mpos N) hρspec.2.2.2
      have hvalle := c_test2_rowValueNat_le T p size hsize hpbound i
      have hmul := Nat.mul_le_mul (hρle.trans hMle) hvalle
      calc
        alpha i = rho i * c_test2_rowValueNat T p i := by simp [alpha, hi]
        _ ≤ size * size ^ c_test2_rowExponent T := hmul
        _ = size ^ (c_test2_rowExponent T + 1) := by
          rw [Nat.pow_succ]
          ring
    · by_cases hia : i = T.anchor
      · subst i
        rw [hAnchorAlpha]
        calc
          c_test2_rowValueNat T p T.anchor ≤ size ^ c_test2_rowExponent T :=
            c_test2_rowValueNat_le T p size hsize hpbound T.anchor
          _ ≤ size ^ (c_test2_rowExponent T + 1) :=
            Nat.pow_le_pow_right hsize (by omega)
      · simp [alpha, hi, hia]
  refine ⟨alpha, hAlphaBound, ?_, hKpos, hBpos, ?_, ?_, ?_, ?_, hAlphaBound j, ?_⟩
  · intro i hi
    let ρi := Classical.choose (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
    have hρspec := Classical.choose_spec
      (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
    have hρeq' : rho i = ρi := by simp [rho, hi, ρi]
    rw [show alpha i = rho i * c_test2_rowValueNat T p i by simp [alpha, hi], hρeq']
    exact dvd_mul_of_dvd_left hρspec.2.2.1 _
  · have hρeq' : rho j = ρj := by simp [rho, hja, ρj]
    rw [hLowerAlpha, hρeq']
    exact dvd_mul_of_dvd_left hρjSpec.2.2.1 _
  · simpa [hAnchorAlpha] using hKcop
  · have hρM := hρjSpec.2.2.2
    obtain ⟨e, heM⟩ := S.core.modulus_power N
    have hKM : Nat.Coprime (c_test2_rowValueNat T p T.anchor)
        (S.core.parameters.M N) := by
      rw [heM]
      exact hKcop.pow_right e
    have hρK : Nat.Coprime ρj (c_test2_rowValueNat T p T.anchor) :=
      (hKM.coprime_dvd_right hρM).symm
    rw [hLowerAlpha]
    have hρeq' : rho j = ρj := by simp [rho, hja, ρj]
    rw [hρeq']
    rw [hAnchorAlpha]
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hρK, hrowCop⟩
  · rw [hAnchorAlpha]
    exact c_test2_rowValueNat_le T p size hsize hpbound T.anchor
  · intro i
    by_cases hi : i < T.anchor
    · let ρi := Classical.choose (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
      have hρspec := Classical.choose_spec
        (c_test2_scaleRatioNat S N c hcpos hratio hmod i T.anchor hi)
      have hρeq' : rho i = ρi := by simp [rho, hi, ρi]
      calc
        (c i : ℚ) / (c T.anchor : ℚ) * T.value p i =
            (ρi : ℚ) * (c_test2_rowValueNat T p i : ℚ) := by
              rw [hρspec.2.1, c_test2_rowValue_eq_cast]
        _ = (alpha i : ℚ) := by
          rw [show alpha i = rho i * c_test2_rowValueNat T p i by simp [alpha, hi], hρeq']
          simp [Nat.cast_mul]
    · by_cases hia : i = T.anchor
      · subst i
        have hca : (c T.anchor : ℚ) ≠ 0 := by
          exact_mod_cast ne_of_gt (hcpos T.anchor)
        rw [div_self hca, c_test2_rowValue_eq_cast, hAnchorAlpha]
        simp
      · have hnone : T.entry i = none := by
          by_contra hsome
          obtain ⟨e, he⟩ : ∃ e, T.entry i = some e := by
            cases h : T.entry i with
            | none => exact (hsome h).elim
            | some e => exact ⟨e, rfl⟩
          have hmem : i ∈ T.support := by
            simpa [RowTemplate.support, he]
          have hle : i ≤ T.anchor := Finset.le_max' T.support i hmem
          omega
        have hval0 : T.value p i = 0 := by simp [RowTemplate.value, hnone]
        simp [hval0, alpha, hi, hia]

theorem c_test2_goodTupleCoeffData {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (T : RowTemplate m q)
    (Jstar : Finset (Fin m)) (hstar : T.support = Jstar)
    (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (p : Fin q → ℕ) (tests : Finset (IntegerPolynomial q))
    (Dpoly : IntegerPolynomial q)
    (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (c : Fin m → ℤ) (hcpos : ∀ d, 0 < c d)
    (hratio : ∀ u d, u < d → ∃ t : ℕ,
      c u = (primorial (N + 1) : ℤ) * (t : ℤ) * c d)
    (hmod : ∀ d,
      ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
        (S.core.parameters.M N : ℤ)) :
    ∃ alpha : Fin m → ℕ,
      (∀ i, alpha i ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
            (c_test2_rowExponent T + 1)) ∧
      (∀ i, i < T.anchor → primorial (N + 1) ∣ alpha i) ∧
      0 < alpha T.anchor ∧ 0 < alpha j ∧
      primorial (N + 1) ∣ alpha j ∧
      Nat.Coprime (alpha T.anchor) (primorial (N + 1)) ∧
      Nat.Coprime (alpha j) (alpha T.anchor) ∧
      alpha T.anchor ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ c_test2_rowExponent T ∧
      alpha j ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
            (c_test2_rowExponent T + 1) ∧
      ∀ i, (c i : ℚ) / (c T.anchor : ℚ) * T.value p i = (alpha i : ℚ) := by
  have hWleV : primorial (N + 1) ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    have hWM := S.core.parameters.Wle N
    unfold FromArithmetic.masterScaleV
    omega
  have hsize : 0 < (S.primeStage.pool N C.gap).upper +
      FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    unfold FromArithmetic.masterScaleV
    omega
  have hpprime : ∀ i, Nat.Prime (p i) := fun i => (hgood.1 i).2.2
  have hpinj : Function.Injective p := hgood.2.1
  have hlarge : ∀ i, primorial (N + 1) < p i := by
    intro i
    have hlow := (hgood.1 i).1
    have hV : 2 ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
      unfold FromArithmetic.masterScaleV
      omega
    have hWlower : primorial (N + 1) < (S.primeStage.pool N C.gap).lower := by
      omega
    exact hWlower.trans_le hlow
  have hpbound : ∀ i,
      p i ≤ (S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    intro i
    exact (Nat.le_of_lt ((hgood.1 i).2.1)).trans (Nat.le_add_right _ _)
  have hMle : S.core.parameters.M N ≤
      (S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    have : S.core.parameters.M N ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
      unfold FromArithmetic.masterScaleV
      omega
    exact this.trans (Nat.le_add_left _ _)
  have hjT : j ∈ T.support := by rw [hstar]; exact hj
  exact c_test2_targetCoeffData S N c hcpos hratio hmod T j hjT hja p hpprime hpinj
    hlarge _ hsize hpbound hMle

noncomputable def c_test2_alphaFromGoodTuple {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (T : RowTemplate m q)
    (Jstar : Finset (Fin m)) (hstar : T.support = Jstar)
    (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (p : Fin q → ℕ) (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (hscale : c_test2_ScaleData S C a N) : Fin m → ℕ :=
  let c := Classical.choose hscale
  let hc := Classical.choose_spec hscale
  Classical.choose (c_test2_goodTupleCoeffData S C a N T Jstar hstar j hj hja
    p tests Dpoly hgood hpool c hc.2.1 hc.2.2.1 hc.2.2.2)

theorem c_test2_alphaFromGoodTuple_eq_choose {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (T : RowTemplate m q)
    (Jstar : Finset (Fin m)) (hstar : T.support = Jstar)
    (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (p : Fin q → ℕ) (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (hscale : c_test2_ScaleData S C a N) :
    c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale =
      Classical.choose (c_test2_goodTupleCoeffData S C a N T Jstar hstar j hj hja
        p tests Dpoly hgood hpool (Classical.choose hscale)
        (Classical.choose_spec hscale).2.1 (Classical.choose_spec hscale).2.2.1
        (Classical.choose_spec hscale).2.2.2) := by
  rfl

theorem c_test2_alphaFromGoodTuple_spec {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (T : RowTemplate m q)
    (Jstar : Finset (Fin m)) (hstar : T.support = Jstar)
    (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (p : Fin q → ℕ) (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (hscale : c_test2_ScaleData S C a N) :
    0 < c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale T.anchor ∧
    0 < c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale j ∧
    primorial (N + 1) ∣ c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale j ∧
    Nat.Coprime (c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale T.anchor) (primorial (N + 1)) ∧
    Nat.Coprime (c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale j)
      (c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale T.anchor) ∧
    c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale T.anchor ≤
          ((S.primeStage.pool N C.gap).upper +
            FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ c_test2_rowExponent T ∧
    c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale j ≤
          ((S.primeStage.pool N C.gap).upper +
            FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
              (c_test2_rowExponent T + 1) := by
  rw [c_test2_alphaFromGoodTuple_eq_choose]
  let hcoeff := c_test2_goodTupleCoeffData S C a N T Jstar hstar j hj hja p tests Dpoly
    hgood hpool (Classical.choose hscale)
      (Classical.choose_spec hscale).2.1 (Classical.choose_spec hscale).2.2.1
      (Classical.choose_spec hscale).2.2.2
  rcases Classical.choose_spec hcoeff with
    ⟨_, _, hkpos, hbpos, hWb, hkW, hbk, hkbound, hbBound, _⟩
  exact ⟨hkpos, hbpos, hWb, hkW, hbk, hkbound, hbBound⟩

theorem c_test2_alphaFromGoodTuple_coefficients {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (T : RowTemplate m q)
    (Jstar : Finset (Fin m)) (hstar : T.support = Jstar)
    (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (p : Fin q → ℕ) (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (hscale : c_test2_ScaleData S C a N) :
    (∀ i, c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale i ≤
      ((S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
          (c_test2_rowExponent T + 1)) ∧
    (∀ i, i < T.anchor → primorial (N + 1) ∣
      c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
        hgood hpool hscale i) ∧
    ∀ i, (Classical.choose hscale i : ℚ) /
        (Classical.choose hscale T.anchor : ℚ) * T.value p i =
          (c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
            hgood hpool hscale i : ℚ) := by
  classical
  rw [c_test2_alphaFromGoodTuple_eq_choose]
  let hcoeff := c_test2_goodTupleCoeffData S C a N T Jstar hstar j hj hja p tests Dpoly
    hgood hpool (Classical.choose hscale)
      (Classical.choose_spec hscale).2.1 (Classical.choose_spec hscale).2.2.1
      (Classical.choose_spec hscale).2.2.2
  rcases Classical.choose_spec hcoeff with
    ⟨hbound, hdiv, _, _, _, _, _, _, _, hidentity⟩
  exact ⟨hbound, hdiv, hidentity⟩

theorem c_test2_rowForm_eq_coeff_sum {m q : ℕ} (c : Fin m → ℚ)
    (T : RowTemplate m q) (p : Fin q → ℕ) (z : Fin m → ℤ)
    (alpha : Fin m → ℕ)
    (hcoeff : ∀ i, c i / c T.anchor * T.value p i = (alpha i : ℚ)) :
    rowForm c T p (fun i => (z i : ℚ)) =
      ∑ i, (alpha i : ℚ) * (z i : ℚ) := by
  unfold rowForm
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoeff i]

theorem c_test2_targetAlpha_zero_after_anchor {m q : ℕ} (T : RowTemplate m q)
    (p : Fin q → ℕ) (c : Fin m → ℚ) (alpha : Fin m → ℕ)
    (hcoeff : ∀ i, c i / c T.anchor * T.value p i = (alpha i : ℚ))
    (i : Fin m) (hi : T.anchor < i) : alpha i = 0 := by
  have hnone : T.entry i = none := by
    by_contra hsome
    obtain ⟨e, he⟩ : ∃ e, T.entry i = some e := by
      cases h : T.entry i with
      | none => exact (hsome h).elim
      | some e => exact ⟨e, rfl⟩
    have hmem : i ∈ T.support := by
      simpa [RowTemplate.support, he]
    have hle : i ≤ T.anchor := Finset.le_max' T.support i hmem
    omega
  have hval : T.value p i = 0 := by simp [RowTemplate.value, hnone]
  have hcast : (alpha i : ℚ) = 0 := by simpa [hval] using (hcoeff i).symm
  exact_mod_cast hcast

structure CTest2RootPair {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (T : RowTemplate m q) (aStar j : Fin m) (N : ℕ) (p : Fin q → ℕ) where
  k : ℕ
  b : ℕ
  k_pos : 0 < k
  b_pos : 0 < b
  W_dvd_b : primorial (N + 1) ∣ b
  k_coprime_W : Nat.Coprime k (primorial (N + 1))
  b_coprime_k : Nat.Coprime b k
  k_bound : k ≤ ((S.primeStage.pool N C.gap).upper +
    FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ c_test2_rowExponent T
  b_bound : b ≤ ((S.primeStage.pool N C.gap).upper +
    FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ (c_test2_rowExponent T + 1)

private def c_test2_defaultRootPair {K s m q : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (T : RowTemplate m q) (aStar j : Fin m) (N : ℕ) (p : Fin q → ℕ) :
    CTest2RootPair S C T aStar j N p := by
  have hsize : 2 ≤ (S.primeStage.pool N C.gap).upper +
      FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    unfold FromArithmetic.masterScaleV
    omega
  have hWle : primorial (N + 1) ≤
      (S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap := by
    calc
      primorial (N + 1) ≤ S.core.parameters.M N := S.core.parameters.Wle N
      _ ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
        unfold FromArithmetic.masterScaleV
        omega
      _ ≤ (S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap := Nat.le_add_left _ _
  let size := (S.primeStage.pool N C.gap).upper +
    FromArithmetic.masterScaleV S.core.parameters N C.gap
  have hkbound : 1 ≤
      ((S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ c_test2_rowExponent T :=
    Nat.one_le_pow _ _ (by omega)
  have hbBound : primorial (N + 1) ≤
      ((S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
          (c_test2_rowExponent T + 1) := by
    calc
      _ ≤ (S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap := hWle
      _ = size * 1 := by simp [size]
      _ ≤ size * size ^ c_test2_rowExponent T :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
      _ = size ^ (c_test2_rowExponent T + 1) := by
        rw [Nat.pow_succ]
        ring
  exact ⟨1, primorial (N + 1), by norm_num, primorial_pos _, dvd_rfl,
    by simp, by simp, hkbound, hbBound⟩

noncomputable def c_test2_rootPairAt {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (T : RowTemplate m q) (Jstar : Finset (Fin m))
    (hstar : T.support = Jstar) (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (N : ℕ) (p : Fin q → ℕ) : CTest2RootPair S C T T.anchor j N p := by
  classical
  by_cases hg : GoodTuple S C.gap N tests Dpoly p
  · by_cases hs : c_test2_ScaleData S C a N
    · by_cases hp : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
        (S.primeStage.pool N C.gap).lower
      · let alpha := c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja
          p tests Dpoly hg hp hs
        have hspec := c_test2_alphaFromGoodTuple_spec S C a N T Jstar hstar j hj hja
          p tests Dpoly hg hp hs
        exact ⟨alpha T.anchor, alpha j, hspec.1, hspec.2.1, hspec.2.2.1,
          hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2.1,
          hspec.2.2.2.2.2.2⟩
      · exact c_test2_defaultRootPair S C T T.anchor j N p
    · exact c_test2_defaultRootPair S C T T.anchor j N p
  · exact c_test2_defaultRootPair S C T T.anchor j N p

theorem c_test2_rootPairAt_properties {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (T : RowTemplate m q) (Jstar : Finset (Fin m))
    (hstar : T.support = Jstar) (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q) :
    ∀ N p,
      0 < (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k ∧
      0 < (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b ∧
      primorial (N + 1) ∣ (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b ∧
      Nat.Coprime (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k
        (primorial (N + 1)) ∧
      Nat.Coprime (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b
        (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k ∧
      (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ c_test2_rowExponent T ∧
      (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b ≤
        ((S.primeStage.pool N C.gap).upper +
          FromArithmetic.masterScaleV S.core.parameters N C.gap) ^
            (c_test2_rowExponent T + 1) := by
  intro N p
  exact ⟨(c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k_pos,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b_pos,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).W_dvd_b,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k_coprime_W,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b_coprime_k,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k_bound,
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b_bound⟩

theorem c_test2_rootPairAt_matches_good_alpha {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (T : RowTemplate m q) (Jstar : Finset (Fin m))
    (hstar : T.support = Jstar) (j : Fin m) (hj : j ∈ Jstar) (hja : j < T.anchor)
    (tests : Finset (IntegerPolynomial q)) (Dpoly : IntegerPolynomial q)
    (N : ℕ) (p : Fin q → ℕ) (hgood : GoodTuple S C.gap N tests Dpoly p)
    (hscale : c_test2_ScaleData S C a N)
    (hpool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower) :
    (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).k =
        c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
          hgood hpool hscale T.anchor ∧
      (c_test2_rootPairAt S C a T Jstar hstar j hj hja tests Dpoly N p).b =
        c_test2_alphaFromGoodTuple S C a N T Jstar hstar j hj hja p tests Dpoly
          hgood hpool hscale j := by
  simp [c_test2_rootPairAt, hgood, hscale, hpool]

abbrev CTest2OtherPivot {m : ℕ} (a j : Fin m) :=
  {i : Fin m // i ≠ a ∧ i ≠ j}

noncomputable def c_test2_pivotIndexEquiv {m : ℕ} (a j : Fin m) (haj : a ≠ j) :
    Fin m ≃ Fin 2 ⊕ CTest2OtherPivot a j := by
  classical
  let encode : Fin m → Fin 2 ⊕ CTest2OtherPivot a j := fun i =>
    if ha : i = a then Sum.inl 0
    else if hj : i = j then Sum.inl 1
    else Sum.inr ⟨i, ha, hj⟩
  refine {
    toFun := encode
    invFun := fun x => match x with
      | Sum.inl b => if b = 0 then a else j
      | Sum.inr i => i.1
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    by_cases hia : i = a
    · simp [encode, hia]
    · by_cases hij : i = j
      · subst i
        simp [encode, haj.symm]
      · simp [encode, hia, hij]
  · intro x
    rcases x with b | i
    · fin_cases b <;> simp [encode, haj.symm]
    · simp [encode, i.2.1, i.2.2]

noncomputable def c_test2_pivotPairRestEquiv {m : ℕ} (a j : Fin m) (haj : a ≠ j) :
    (Fin m → ℤ) ≃ ((ℤ × ℤ) × (CTest2OtherPivot a j → ℤ)) := by
  let idx := c_test2_pivotIndexEquiv a j haj
  exact (Equiv.arrowCongr idx (Equiv.refl ℤ)).trans
    ((Equiv.sumArrowEquivProdArrow (Fin 2) (CTest2OtherPivot a j) ℤ).trans
      ((piFinTwoEquiv (fun _ : Fin 2 => ℤ)).prodCongr (Equiv.refl _)))

@[simp]
theorem c_test2_pivotPairRestEquiv_apply_anchor {m : ℕ} (a j : Fin m) (haj : a ≠ j)
    (z : Fin m → ℤ) :
    (c_test2_pivotPairRestEquiv a j haj z).1.1 = z a := by
  simp [c_test2_pivotPairRestEquiv, c_test2_pivotIndexEquiv, haj]

@[simp]
theorem c_test2_pivotPairRestEquiv_apply_j {m : ℕ} (a j : Fin m) (haj : a ≠ j)
    (z : Fin m → ℤ) :
    (c_test2_pivotPairRestEquiv a j haj z).1.2 = z j := by
  simp [c_test2_pivotPairRestEquiv, c_test2_pivotIndexEquiv, haj]

@[simp]
theorem c_test2_pivotPairRestEquiv_apply_other {m : ℕ} (a j : Fin m) (haj : a ≠ j)
    (z : Fin m → ℤ) (i : CTest2OtherPivot a j) :
    (c_test2_pivotPairRestEquiv a j haj z).2 i = z i.1 := by
  simp [c_test2_pivotPairRestEquiv, c_test2_pivotIndexEquiv, i.2]

theorem c_test2_pivotMass_factor {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (C : MasterChain n m) (N : ℕ) (a j : Fin m) (haj : a ≠ j)
    (z : Fin m → ℤ) :
    pivotMass A C N z =
      harmonicLaw (A.X N (C.block a).1) (primorial (N + 1)) (z a) *
        harmonicLaw (A.X N (C.block j).1) (primorial (N + 1)) (z j) *
          ∏ i : CTest2OtherPivot a j,
            harmonicLaw (A.X N (C.block i.1).1) (primorial (N + 1)) (z i.1) := by
  classical
  let idx := c_test2_pivotIndexEquiv a j haj
  unfold pivotMass
  rw [← idx.symm.prod_comp (fun i : Fin m =>
    harmonicLaw (A.X N (C.block i).1) (primorial (N + 1)) (z i))]
  rw [Fintype.prod_sum_type]
  simp [idx, c_test2_pivotIndexEquiv, haj, Fin.prod_univ_two]

theorem c_test2_alphaWeightedSum_split {m : ℕ} (a j : Fin m) (haj : a ≠ j)
    (alpha : Fin m → ℕ) (z : Fin m → ℤ) :
    (∑ i : Fin m, (alpha i : ℤ) * z i) =
      (alpha a : ℤ) * z a + (alpha j : ℤ) * z j +
        ∑ i : CTest2OtherPivot a j, (alpha i.1 : ℤ) * z i.1 := by
  classical
  let idx := c_test2_pivotIndexEquiv a j haj
  rw [← Equiv.sum_comp idx.symm (fun i : Fin m => (alpha i : ℤ) * z i)]
  rw [Fintype.sum_sum_type]
  simp [idx, c_test2_pivotIndexEquiv, haj, Fin.sum_univ_two, add_assoc, add_comm, add_left_comm]

noncomputable def c_test2_restPivotMass {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (C : MasterChain n m) (N : ℕ) (a j : Fin m)
    (r : CTest2OtherPivot a j → ℤ) : ℝ :=
  ∏ i : CTest2OtherPivot a j,
    harmonicLaw (A.X N (C.block i.1).1) (primorial (N + 1)) (r i)

theorem c_test2_restPivotMass_tsum_one {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (haj : a ≠ j)
    (hZ : ∀ i : CTest2OtherPivot a j,
      0 < harmonicNormalizer (A.X N (C.block i.1).1) (primorial (N + 1))) :
    ∑' r : CTest2OtherPivot a j → ℤ, c_test2_restPivotMass A C N a j r = 1 := by
  unfold c_test2_restPivotMass
  apply c_test2_harmonicProductMass_tsum_one
  · intro i
    exact A.Xpos N (C.block i.1).1
  · exact hZ

theorem c_test2_restPivotMass_nonneg {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (haj : a ≠ j)
    (hZ : ∀ i : CTest2OtherPivot a j,
      0 < harmonicNormalizer (A.X N (C.block i.1).1) (primorial (N + 1)))
    (r : CTest2OtherPivot a j → ℤ) : 0 ≤ c_test2_restPivotMass A C N a j r := by
  unfold c_test2_restPivotMass
  apply Finset.prod_nonneg
  intro i _
  exact c_test2_harmonicLaw_nonneg_of_normalizer_pos (hZ i) (r i)

theorem c_test2_restPivotMass_zero_outside {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (r : CTest2OtherPivot a j → ℤ)
    (hr : r ∉ Fintype.piFinset (fun i : CTest2OtherPivot a j =>
      c_test2_harmonicIntSupport (A.X N (C.block i.1).1))) :
    c_test2_restPivotMass A C N a j r = 0 := by
  classical
  have hnot : ¬ ∀ i : CTest2OtherPivot a j, r i ∈
      c_test2_harmonicIntSupport (A.X N (C.block i.1).1) := by
    intro hall
    exact hr (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hLaw : harmonicLaw (A.X N (C.block i.1).1) (primorial (N + 1)) (r i) = 0 :=
    c_test2_harmonicLaw_zero_outside hi
  unfold c_test2_restPivotMass
  exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw

theorem c_test2_restPivotMass_summable {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (haj : a ≠ j) :
    Summable (c_test2_restPivotMass A C N a j) := by
  classical
  let support : CTest2OtherPivot a j → Finset ℤ := fun i =>
    c_test2_harmonicIntSupport (A.X N (C.block i.1).1)
  apply summable_of_ne_finset_zero (s := Fintype.piFinset support)
  intro r hr
  exact c_test2_restPivotMass_zero_outside A C N a j r (by simpa [support] using hr)

theorem c_test2_pivotMass_tsum_split {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (haj : a ≠ j) (F : (Fin m → ℤ) → ℝ) :
    (∑' z : Fin m → ℤ, pivotMass A C N z * F z) =
      ∑' r : CTest2OtherPivot a j → ℤ,
        c_test2_restPivotMass A C N a j r *
          ∑' za : ℤ, ∑' zj : ℤ,
            harmonicLaw (A.X N (C.block a).1) (primorial (N + 1)) za *
              harmonicLaw (A.X N (C.block j).1) (primorial (N + 1)) zj *
                F ((c_test2_pivotPairRestEquiv a j haj).symm ((za, zj), r)) := by
  classical
  let Rest := CTest2OtherPivot a j
  let e0 := c_test2_pivotPairRestEquiv a j haj
  let e : (Fin m → ℤ) ≃ ((Rest → ℤ) × (ℤ × ℤ)) :=
    e0.trans (Equiv.prodComm _ _)
  let μa : ℤ → ℝ := harmonicLaw (A.X N (C.block a).1) (primorial (N + 1))
  let μj : ℤ → ℝ := harmonicLaw (A.X N (C.block j).1) (primorial (N + 1))
  let μr : (Rest → ℤ) → ℝ := c_test2_restPivotMass A C N a j
  let supportR : Finset (Rest → ℤ) := Fintype.piFinset fun i : Rest =>
    c_test2_harmonicIntSupport (A.X N (C.block i.1).1)
  let supportA := c_test2_harmonicIntSupport (A.X N (C.block a).1)
  let supportJ := c_test2_harmonicIntSupport (A.X N (C.block j).1)
  let support : Finset ((Rest → ℤ) × (ℤ × ℤ)) :=
    supportR.product (supportA.product supportJ)
  let integrand : (Rest → ℤ) × (ℤ × ℤ) → ℝ := fun t =>
    μr t.1 * μa t.2.1 * μj t.2.2 * F (e.symm t)
  have hcoords (r : Rest → ℤ) (za zj : ℤ) :
      e0 (e.symm (r, (za, zj))) = ((za, zj), r) := by
    have h := e.apply_symm_apply (r, (za, zj))
    have h' : Equiv.prodComm (ℤ × ℤ) (Rest → ℤ)
        (e0 (e.symm (r, (za, zj)))) = (r, (za, zj)) := by
      simpa [e] using h
    exact (Equiv.prodComm (ℤ × ℤ) (Rest → ℤ)).injective h'
  have hfactor (r : Rest → ℤ) (za zj : ℤ) :
      pivotMass A C N (e.symm (r, (za, zj))) =
        μr r * μa za * μj zj := by
    calc
      pivotMass A C N (e.symm (r, (za, zj))) = μa za * μj zj * μr r := by
        rw [c_test2_pivotMass_factor A C N a j haj]
        have h := hcoords r za zj
        have hza : (e.symm (r, (za, zj))) a = za := by
          have h' := congrArg (fun x => x.1.1) h
          change (c_test2_pivotPairRestEquiv a j haj (e.symm (r, (za, zj)))).1.1 = za at h'
          simpa using h'
        have hzj : (e.symm (r, (za, zj))) j = zj := by
          have h' := congrArg (fun x => x.1.2) h
          change (c_test2_pivotPairRestEquiv a j haj (e.symm (r, (za, zj)))).1.2 = zj at h'
          simpa using h'
        have hrest (i : Rest) : (e.symm (r, (za, zj))) i.1 = r i := by
          have h' := congrArg (fun x => x.2 i) h
          change (c_test2_pivotPairRestEquiv a j haj (e.symm (r, (za, zj)))).2 i = r i at h'
          simpa using h'
        simp [μa, μj, μr, hza, hzj, hrest, c_test2_restPivotMass]
      _ = μr r * μa za * μj zj := by ring
  have hzeroR (r : Rest → ℤ) (hr : r ∉ supportR) : μr r = 0 := by
    have hnot : ¬ ∀ i : Rest, r i ∈ c_test2_harmonicIntSupport
        (A.X N (C.block i.1).1) := by
      intro hall
      exact hr (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hLaw : harmonicLaw (A.X N (C.block i.1).1) (primorial (N + 1)) (r i) = 0 :=
      c_test2_harmonicLaw_zero_outside hi
    change c_test2_restPivotMass A C N a j r = 0
    unfold c_test2_restPivotMass
    exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
  have hzero : ∀ t ∉ support, integrand t = 0 := by
    intro t ht
    by_cases hr : t.1 ∉ supportR
    · simp [integrand, hzeroR t.1 hr]
    · have hnotPair : t.2 ∉ supportA.product supportJ := by
        have hrmem : t.1 ∈ supportR := by
          by_contra hnotR
          exact hr hnotR
        intro hmem
        exact ht (Finset.mem_product.mpr ⟨hrmem, hmem⟩)
      have hnotAJ : t.2.1 ∉ supportA ∨ t.2.2 ∉ supportJ := by
        have hmem : ¬ (t.2.1 ∈ supportA ∧ t.2.2 ∈ supportJ) := by
          simpa [Finset.mem_product] using hnotPair
        exact not_and_or.mp hmem
      rcases hnotAJ with hA | hJ
      · have hLaw : μa t.2.1 = 0 := by
          exact c_test2_harmonicLaw_zero_outside (by simpa [μa, supportA] using hA)
        simp [integrand, hLaw]
      · have hLaw : μj t.2.2 = 0 := by
          exact c_test2_harmonicLaw_zero_outside (by simpa [μj, supportJ] using hJ)
        simp [integrand, hLaw]
  have hsum : Summable integrand := summable_of_ne_finset_zero (s := support) hzero
  have hpairSummable (r : Rest → ℤ) :
      Summable (fun pair : ℤ × ℤ => μa pair.1 * μj pair.2 *
        F (e.symm (r, pair))) := by
    apply summable_of_ne_finset_zero (s := supportA.product supportJ)
    intro pair hp
    have hnotPair : pair.1 ∉ supportA ∨ pair.2 ∉ supportJ := by
      have hmem : ¬ (pair.1 ∈ supportA ∧ pair.2 ∈ supportJ) := by
        simpa [Finset.mem_product] using hp
      exact not_and_or.mp hmem
    rcases hnotPair with hA | hJ
    · have hLaw : μa pair.1 = 0 := by
        exact c_test2_harmonicLaw_zero_outside (by simpa [μa, supportA] using hA)
      simp [hLaw]
    · have hLaw : μj pair.2 = 0 := by
        exact c_test2_harmonicLaw_zero_outside (by simpa [μj, supportJ] using hJ)
      simp [hLaw]
  have hinner (r : Rest → ℤ) :
      (∑' pair : ℤ × ℤ, integrand (r, pair)) =
        μr r * ∑' za : ℤ, ∑' zj : ℤ,
          μa za * μj zj * F (e.symm (r, (za, zj))) := by
    calc
      _ = ∑' pair : ℤ × ℤ,
          μr r * (μa pair.1 * μj pair.2 * F (e.symm (r, pair))) := by
            apply tsum_congr
            intro pair
            simp only [integrand]
            ring
      _ = μr r * ∑' pair : ℤ × ℤ,
          μa pair.1 * μj pair.2 * F (e.symm (r, pair)) := by
            rw [tsum_mul_left]
      _ = μr r * ∑' za : ℤ, ∑' zj : ℤ,
          μa za * μj zj * F (e.symm (r, (za, zj))) := by
            rw [(hpairSummable r).tsum_prod]
  calc
    (∑' z : Fin m → ℤ, pivotMass A C N z * F z) =
        ∑' t : (Rest → ℤ) × (ℤ × ℤ),
          pivotMass A C N (e.symm t) * F (e.symm t) := by
            simpa [e] using (e.symm.tsum_eq (fun z => pivotMass A C N z * F z)).symm
    _ = ∑' t : (Rest → ℤ) × (ℤ × ℤ), integrand t := by
      apply tsum_congr
      intro t
      rcases t with ⟨r, za, zj⟩
      simpa [integrand, μa, μj, μr] using congrArg
        (fun x => x * F (e.symm (r, (za, zj)))) (hfactor r za zj)
    _ = ∑' r : Rest → ℤ, ∑' pair : ℤ × ℤ, integrand (r, pair) := hsum.tsum_prod
    _ = ∑' r : Rest → ℤ, μr r * ∑' za : ℤ, ∑' zj : ℤ,
          μa za * μj zj * F (e.symm (r, (za, zj))) := by
        apply tsum_congr
        intro r
        simpa [e, e0, c_test2_pivotPairRestEquiv] using hinner r

theorem c_test2_chainWeight_nonneg {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (d : Fin m) (y : ℤ) : 0 ≤ chainWeight A C N d y := by
  change 0 ≤ nuB (FromArithmetic.parameterTailProductLaw A N (C.block d).2.val) y
  unfold nuB
  apply tsum_nonneg
  intro σ
  by_cases hdiv : (σ : ℤ) ∣ y
  · simp [hdiv]
    exact mul_nonneg
      (c_test2_parameterTailProductLaw_nonneg A N (C.block d).2.val σ)
      (Nat.cast_nonneg σ)
  · simp [hdiv]

private theorem c_test2_harmonicNatLaw_support_upper (X W n : ℕ)
    (h : harmonicNatLaw X W n ≠ 0) : n < X ^ 2 := by
  by_contra hlt
  have hnot : ¬ (X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W) := by
    intro hcond
    exact hlt hcond.2.1
  exact h (by simp [harmonicNatLaw, hnot])

theorem c_test2_harmonicNatLaw_support_lower (X W n : ℕ)
    (h : harmonicNatLaw X W n ≠ 0) : X ≤ n := by
  unfold harmonicNatLaw at h
  by_cases hc : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W
  · exact hc.1
  · simp [hc] at h

theorem c_test2_harmonicNatLaw_coprime_of_nonzero (X W n : ℕ)
    (h : harmonicNatLaw X W n ≠ 0) : Nat.Coprime n W := by
  unfold harmonicNatLaw at h
  split_ifs at h with hc
  · exact hc.2.2
  · simp at h

theorem c_test2_parameterTailProductLaw_pos_of_nonzero {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N T σ ≠ 0) : 1 ≤ σ := by
  classical
  by_contra hnot
  have hσlt : σ < 1 := Nat.lt_of_not_ge hnot
  have hterm (t : Fin n → ℕ) :
      (if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    by_cases hp : (∏ j ∈ T, t j) = σ
    · by_cases hall : ∀ j ∈ T,
          harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) ≠ 0
      · have hprod : 1 ≤ ∏ j ∈ T, t j := by
          apply Finset.one_le_prod
          intro j hj
          have hNZ := hall j hj
          have hXle := c_test2_harmonicNatLaw_support_lower
            (A.X N j) (primorial (N + 1)) (t j) hNZ
          exact Nat.one_le_of_lt (lt_of_lt_of_le (A.Xpos N j) hXle)
        have : 1 ≤ σ := by rw [← hp]; exact hprod
        exact False.elim ((not_le_of_gt hσlt) this)
      · push_neg at hall
        obtain ⟨j, hjT, hj0⟩ := hall
        have hzero : ∏ k, harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hj0
        simp [hp, hzero]
    · simp [hp]
  apply hσ
  unfold FromArithmetic.parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem c_test2_parameterTailProductLaw_coprime_of_nonzero {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N T σ ≠ 0) :
    Nat.Coprime σ (primorial (N + 1)) := by
  classical
  by_contra hcop
  obtain ⟨p, hp, hpsigma, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hterm (t : Fin n → ℕ) :
      (if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    by_cases hprod : (∏ j ∈ T, t j) = σ
    · have hpProd : p ∣ ∏ j ∈ T, t j := by rw [hprod]; exact hpsigma
      obtain ⟨j, hjT, hpj⟩ :=
        (Prime.dvd_finsetProd_iff (p := p) hp.prime (fun j => t j)).mp hpProd
      have hLawZero : harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
        by_contra hNZ
        have hcoprime := c_test2_harmonicNatLaw_coprime_of_nonzero
          (A.X N j) (primorial (N + 1)) (t j) hNZ
        have hbad : ¬ Nat.Coprime (t j) (primorial (N + 1)) := by
          apply Nat.Prime.not_coprime_iff_dvd.mpr
          exact ⟨p, hp, hpj, hpW⟩
        exact hbad hcoprime
      have hMassZero :
          (∏ k : Fin n, harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hLawZero
      simp [hprod, hMassZero]
    · simp [hprod]
  apply hσ
  unfold FromArithmetic.parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem c_test2_parameterTailProductLaw_support_le {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N T σ ≠ 0) :
    σ ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by
  classical
  by_contra hnot
  have hlarge : (∏ j ∈ T, (A.X N j) ^ 2) < σ := Nat.lt_of_not_ge hnot
  have hterm (t : Fin n → ℕ) :
      (if (∏ j ∈ T, t j) = σ then 1 else 0) *
        ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    by_cases hprod : (∏ j ∈ T, t j) = σ
    · by_cases hall : ∀ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) ≠ 0
      · have hbound : (∏ j ∈ T, t j) ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by
          apply Finset.prod_le_prod
          intro j hj
          exact Nat.le_of_lt (c_test2_harmonicNatLaw_support_upper _ _ _ (hall j))
        have hsigma : σ ≤ ∏ j ∈ T, (A.X N j) ^ 2 := by rw [← hprod]; exact hbound
        exact False.elim (not_le_of_gt hlarge hsigma)
      · push_neg at hall
        obtain ⟨j, hj⟩ := hall
        have hprodZero :
            (∏ k : Fin n, harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k)) = 0 := by
          exact Finset.prod_eq_zero (s := Finset.univ)
            (f := fun k => harmonicNatLaw (A.X N k) (primorial (N + 1)) (t k))
            (Finset.mem_univ j) hj
        simp [hprod, hprodZero]
    · simp [hprod]
  apply hσ
  unfold FromArithmetic.parameterTailProductLaw
  simp_rw [hterm]
  simp

theorem c_test2_chainTail_support_le_masterScaleV {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (C : MasterChain n m)
    (d : Fin m) (σ : ℕ)
    (hσ : FromArithmetic.parameterTailProductLaw A N (C.block d).2.val σ ≠ 0) :
    σ ≤ FromArithmetic.masterScaleV A N C.gap := by
  let T := (C.block d).2.val
  let E := Finset.univ.filter (fun j : Fin n => j < C.gap)
  have hsubset : T ⊆ E := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, C.tails_before_gap d j hj⟩
  have hprod_le :
      (∏ j ∈ T, (A.X N j) ^ 2) ≤ ∏ j ∈ E, (A.X N j) ^ 2 := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsubset
    intro j hj hjnot
    exact Nat.one_le_pow 2 (A.X N j) (A.Xpos N j)
  have hmaster :
      (∏ j ∈ E, (A.X N j) ^ 2) ≤ FromArithmetic.masterScaleV A N C.gap := by
    dsimp [FromArithmetic.masterScaleV, E]
    omega
  exact (c_test2_parameterTailProductLaw_support_le A N T σ hσ).trans
    (hprod_le.trans hmaster)

theorem c_test2_harmonicNormalizer_pos_of_cutoff (X W : ℕ) (hW : 0 < W)
    (hX : 4 * W ≤ X) : 0 < harmonicNormalizer X W := by
  classical
  have hXge4 : 4 ≤ X := by omega
  let n₀ : ℕ := (X / W + 1) * W + 1
  have hdiv : X / W * W + X % W = X := Nat.div_add_mod' X W
  have hmod : X % W < W := Nat.mod_lt X hW
  have hn₀eq : n₀ = X / W * W + W + 1 := by simp [n₀, Nat.add_mul]
  have hn₀lo : X < n₀ := by rw [hn₀eq]; omega
  have hquot : X / W * W ≤ X := Nat.div_mul_le_self X W
  have hn₀upper : n₀ ≤ 2 * X + 1 := by rw [hn₀eq]; omega
  have hXsqr : 2 * X + 1 < X ^ 2 := by
    have hXr : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
    have hmul : 0 ≤ (X : ℝ) * ((X : ℝ) - 3) :=
      mul_nonneg (by positivity) (by linarith)
    have h : (2 : ℝ) * X + 1 < (X : ℝ) ^ 2 := by nlinarith [hmul]
    exact_mod_cast h
  have hn₀hi : n₀ < X ^ 2 := lt_of_le_of_lt hn₀upper hXsqr
  have hn₀cop : Nat.Coprime n₀ W := by
    have h : Nat.Coprime (W * (X / W + 1) + 1) W :=
      (Nat.coprime_mul_left_add_left 1 W (X / W + 1)).2 (by simp)
    simpa [n₀, Nat.mul_comm] using h
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  have hn₀mem : n₀ ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hn₀lo.le, hn₀hi⟩, hn₀cop⟩
  have hn₀pos : 0 < n₀ := by omega
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀pos
  have hterm : (0 : ℝ) < 1 / (n₀ : ℝ) := one_div_pos.mpr hn₀R
  unfold harmonicNormalizer
  have hsum := Finset.single_le_sum (s := S) (f := fun n : ℕ => 1 / (n : ℝ))
    (fun n _ => one_div_nonneg.mpr (Nat.cast_nonneg n)) hn₀mem
  simpa [S] using lt_of_lt_of_le hterm hsum

theorem c_test2_samplingDenominator_of_cutoff {X W : ℕ} (hW : 0 < W)
    (hcut : 4 * W ≤ X) : Real.log X > (W : ℝ) / X := by
  have hWone : 1 ≤ W := by omega
  have hX : 4 ≤ X := by omega
  have hXreal : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hdiv : (W : ℝ) / X ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ hXreal).2
    have hcutR : (4 : ℝ) * (W : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcut
    nlinarith
  have hlog4 : (1 / 4 : ℝ) < Real.log 4 := by
    have hlog2 := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith
  have hlog : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) (by exact_mod_cast hX)
  exact lt_of_le_of_lt hdiv (lt_of_lt_of_le hlog4 hlog)

theorem c_test2_harmonicNatLaw_tsum_one_of_normalizer_pos (X W : ℕ)
    (hX : 0 < X) (hNorm : 0 < harmonicNormalizer X W) :
    ∑' n : ℕ, harmonicNatLaw X W n = 1 := by
  classical
  let S : Finset ℕ := (Finset.Ico X (X ^ 2)).filter (fun n => Nat.Coprime n W)
  have hzero (n : ℕ) (hn : n ∉ S) : harmonicNatLaw X W n = 0 := by
    by_contra hne
    have hcond : X ≤ n ∧ n < X ^ 2 ∧ Nat.Coprime n W := by
      by_contra hnot
      have : harmonicNatLaw X W n = 0 := by simp [harmonicNatLaw, hnot]
      exact hne this
    apply hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hcond.1, hcond.2.1⟩, hcond.2.2⟩
  have hterm (n : ℕ) (hn : n ∈ S) :
      harmonicNatLaw X W n = (1 / (n : ℝ)) / harmonicNormalizer X W := by
    rcases Finset.mem_filter.mp hn with ⟨hnIco, hcop⟩
    rcases Finset.mem_Ico.mp hnIco with ⟨hXn, hnX2⟩
    have hnpos : 0 < n := lt_of_lt_of_le hX hXn
    have hnum : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnpos).ne'
    unfold harmonicNatLaw
    rw [if_pos ⟨hXn, hnX2, hcop⟩]
    field_simp
  calc
    (∑' n : ℕ, harmonicNatLaw X W n) = ∑ n ∈ S, harmonicNatLaw X W n :=
      tsum_eq_sum (s := S) hzero
    _ = ∑ n ∈ S, (1 / (n : ℝ)) / harmonicNormalizer X W := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hterm n hn
    _ = (∑ n ∈ S, 1 / (n : ℝ)) / harmonicNormalizer X W := by
      rw [Finset.sum_div]
    _ = 1 := by
      have hsum : (∑ n ∈ S, 1 / (n : ℝ)) = harmonicNormalizer X W := by
        rfl
      rw [hsum]
      exact div_self hNorm.ne'

theorem c_test2_parameterTailProductLaw_summable {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n)) :
    Summable (FromArithmetic.parameterTailProductLaw A N T) := by
  classical
  let Q := ∏ j ∈ T, (A.X N j) ^ 2
  apply summable_of_ne_finset_zero (s := Finset.range (Q + 1))
  intro σ hσ
  have hQlt : Q < σ := by
    have hnot : ¬ σ < Q + 1 := by simpa only [Finset.mem_range, not_lt] using hσ
    omega
  by_contra hne
  have hbound := c_test2_parameterTailProductLaw_support_le A N T σ hne
  exact (not_le_of_gt (show Q < σ by simpa [Q] using hQlt)) hbound

theorem c_test2_parameterTailProductLaw_tsum_one {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hX : ∀ j, 0 < A.X N j)
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) :
    ∑' σ : ℕ, FromArithmetic.parameterTailProductLaw A N T σ = 1 := by
  classical
  let D : Finset (Fin n → ℕ) :=
    Fintype.piFinset fun j => Finset.range ((A.X N j) ^ 2)
  let Q := ∏ j ∈ T, (A.X N j) ^ 2
  have hrawZero (t : Fin n → ℕ) (ht : t ∉ D) :
      ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
    have hnot : ¬ ∀ j, t j < (A.X N j) ^ 2 := by
      intro hall
      apply ht
      apply Fintype.mem_piFinset.mpr
      intro j
      simpa only [Finset.mem_range] using hall j
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero : harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) = 0 := by
      have hlt : ¬ t j < (A.X N j) ^ 2 := by omega
      simp [harmonicNatLaw, hlt]
    exact Finset.prod_eq_zero (s := Finset.univ)
      (f := fun j => harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j))
      (Finset.mem_univ j) hzero
  have hrawSum :
      (∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) = 1 := by
    calc
      (∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j)) =
          ∏ j, ∑ x ∈ Finset.range ((A.X N j) ^ 2),
            harmonicNatLaw (A.X N j) (primorial (N + 1)) x := by
        symm
        exact Finset.prod_univ_sum
          (t := fun j => Finset.range ((A.X N j) ^ 2))
          (f := fun j x => harmonicNatLaw (A.X N j) (primorial (N + 1)) x)
      _ = ∏ j, 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        have hnorm := c_test2_harmonicNatLaw_tsum_one_of_normalizer_pos
          (A.X N j) (primorial (N + 1)) (hX j) (hNorm j)
        have hzero (x : ℕ) (hx : x ∉ Finset.range ((A.X N j) ^ 2)) :
            harmonicNatLaw (A.X N j) (primorial (N + 1)) x = 0 := by
          have hxlo : (A.X N j) ^ 2 ≤ x := by
            simpa only [Finset.mem_range, not_lt] using hx
          simp [harmonicNatLaw, hxlo]
        calc
          (∑ x ∈ Finset.range ((A.X N j) ^ 2),
              harmonicNatLaw (A.X N j) (primorial (N + 1)) x) =
              ∑' x : ℕ, harmonicNatLaw (A.X N j) (primorial (N + 1)) x :=
            (tsum_eq_sum (s := Finset.range ((A.X N j) ^ 2)) hzero).symm
          _ = 1 := hnorm
      _ = 1 := by simp
  have htailZero (σ : ℕ) (hσ : σ ∉ Finset.range (Q + 1)) :
      FromArithmetic.parameterTailProductLaw A N T σ = 0 := by
    have hQlt : Q < σ := by
      have hnot : ¬ σ < Q + 1 := by simpa only [Finset.mem_range, not_lt] using hσ
      omega
    by_contra hne
    have hbound := c_test2_parameterTailProductLaw_support_le A N T σ hne
    exact (not_le_of_gt hQlt) (by simpa [Q] using hbound)
  have hinner (σ : ℕ) : FromArithmetic.parameterTailProductLaw A N T σ =
      ∑ t ∈ D,
        (if (∏ j ∈ T, t j) = σ then 1 else 0) *
          ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
    unfold FromArithmetic.parameterTailProductLaw
    apply tsum_eq_sum (s := D)
    intro t ht
    simp [hrawZero t ht]
  calc
    (∑' σ : ℕ, FromArithmetic.parameterTailProductLaw A N T σ) =
        ∑ σ ∈ Finset.range (Q + 1), FromArithmetic.parameterTailProductLaw A N T σ :=
      tsum_eq_sum (s := Finset.range (Q + 1)) htailZero
    _ = ∑ σ ∈ Finset.range (Q + 1), ∑ t ∈ D,
          (if (∏ j ∈ T, t j) = σ then 1 else 0) *
            ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hinner σ
    _ = ∑ t ∈ D, ∏ j, harmonicNatLaw (A.X N j) (primorial (N + 1)) (t j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      have hmem : (∏ j ∈ T, t j) ∈ Finset.range (Q + 1) := by
        have hle : (∏ j ∈ T, t j) ≤ Q := by
          apply Finset.prod_le_prod
          intro j hj
          have hjt : t j < (A.X N j) ^ 2 := by
            have := Fintype.mem_piFinset.mp ht j
            simpa only [Finset.mem_range] using this
          exact Nat.le_of_lt hjt
        simp [Finset.mem_range, hle]
      simp [Finset.sum_ite_eq', hmem]
    _ = 1 := hrawSum

theorem c_test2_nuB_le_of_probability_support (tailLaw : TailProductLaw)
    (hNonneg : ∀ σ, 0 ≤ tailLaw σ) (hSummable : Summable tailLaw)
    (hMass : ∑' σ, tailLaw σ = 1) (V : ℕ)
    (hSupport : ∀ σ, tailLaw σ ≠ 0 → σ ≤ V) (y : ℤ) :
    nuB tailLaw y ≤ (V : ℝ) := by
  let term : ℕ → ℝ := fun σ => tailLaw σ * (σ : ℝ) * if (σ : ℤ) ∣ y then 1 else 0
  have hterm_nonneg (σ : ℕ) : 0 ≤ term σ := by
    dsimp [term]
    by_cases hdiv : (σ : ℤ) ∣ y
    · simp [hdiv]
      exact mul_nonneg (hNonneg σ) (by positivity)
    · simp [hdiv]
  have hterm_le (σ : ℕ) : term σ ≤ tailLaw σ * (V : ℝ) := by
    dsimp [term]
    by_cases hzero : tailLaw σ = 0
    · simp [hzero]
    · have hσ := hSupport σ hzero
      have hσR : (σ : ℝ) ≤ (V : ℝ) := by exact_mod_cast hσ
      by_cases hdiv : (σ : ℤ) ∣ y
      · simp [hdiv]
        exact mul_le_mul_of_nonneg_left hσR (hNonneg σ)
      · simp [hdiv]
        exact mul_nonneg (hNonneg σ) (by positivity)
  have hdom : Summable fun σ => tailLaw σ * (V : ℝ) := hSummable.mul_right _
  have hterm_summable : Summable term := by
    apply hdom.of_norm_bounded
    intro σ
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg σ)]
    exact hterm_le σ
  calc
    nuB tailLaw y = ∑' σ, term σ := by simp [nuB, term]
    _ ≤ ∑' σ, tailLaw σ * (V : ℝ) :=
      hterm_summable.tsum_le_tsum (fun σ => hterm_le σ) hdom
    _ = (∑' σ, tailLaw σ) * (V : ℝ) := hSummable.tsum_mul_right _
    _ = (V : ℝ) := by rw [hMass]; ring

theorem c_test2_chainWeight_le_masterScaleV {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)} (S : FromArithmetic.MasterScales K Aset s Dm)
    (C : MasterChain K m) (N : ℕ) (d : Fin m) (y : ℤ) :
    chainWeight S.core.parameters C N d y ≤
      (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ) := by
  let A := S.core.parameters
  let T := (C.block d).2.val
  have hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1)) := by
    intro j
    exact c_test2_harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N j)
  change nuB (FromArithmetic.parameterTailProductLaw A N T) y ≤
    (FromArithmetic.masterScaleV A N C.gap : ℝ)
  apply c_test2_nuB_le_of_probability_support
    (tailLaw := FromArithmetic.parameterTailProductLaw A N T)
    (V := FromArithmetic.masterScaleV A N C.gap)
  · intro σ
    exact c_test2_parameterTailProductLaw_nonneg A N T σ
  · exact c_test2_parameterTailProductLaw_summable A N T
  · exact c_test2_parameterTailProductLaw_tsum_one A N T (fun j => A.Xpos N j) hNorm
  · intro σ hσ
    exact c_test2_chainTail_support_le_masterScaleV A N C d σ hσ

structure CTest2RowCompletion {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hJcard : 2 ≤ Jstar.card)
    (hstar : (Sh.row Sh.star).support = Jstar) (hr : r ≤ maskRowBound m) where
  r' : ℕ
  shape : RowShape m q r'
  map : Fin r → Fin r'
  row_eq : ∀ R, shape.row (map R) = Sh.row R
  star_eq : shape.star = map Sh.star
  two_rows : 2 ≤ r'
  row_bound : r' ≤ maskRowBound m
  extend : (Fin r → (Fin q → ℕ) → ℤ → ℝ) → Fin r' → (Fin q → ℕ) → ℤ → ℝ
  extend_map : ∀ f R, extend f (map R) = f R
  extend_bound : ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ),
    (∀ R p y, |f R p y| ≤ 1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
    ∀ R' p y, |extend f R' p y| ≤
      1 + chainWeight S.core.parameters C N (shape.row R').anchor y
  rowCorrelation_eq : ∀ {K s : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (f : Fin r → (Fin q → ℕ) → ℤ → ℝ),
    rowCorrelation S C a N shape (extend f) = rowCorrelation S C a N Sh f

noncomputable def c_test2_completeRows {m q r : ℕ} (Sh : RowShape m q r)
    (Jstar : Finset (Fin m)) (hJcard : 2 ≤ Jstar.card)
    (hstar : (Sh.row Sh.star).support = Jstar) (hr : r ≤ maskRowBound m) :
    CTest2RowCompletion Sh Jstar hJcard hstar hr := by
  classical
  by_cases hone : r = 1
  · subst r
    have hcard : Jstar.card ≤ m := by simpa using (Finset.card_le_univ Jstar)
    have hm : 2 ≤ m := hJcard.trans hcard
    let i : Fin m := ⟨0, by omega⟩
    let Sh' := c_test2_padSingletonShape Sh i Jstar hJcard hstar
    have hstarFin : Sh.star = 0 := Subsingleton.elim _ _
    have hpow : 4 ≤ 2 ^ m := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hmc : 3 ≤ maskCount m := by
      unfold maskCount
      omega
    have hbound : 2 ≤ maskRowBound m := by
      unfold maskRowBound
      calc
        2 ≤ maskCount m := by omega
        _ ≤ maskCount m * 2 ^ maskCount m :=
          Nat.le_mul_of_pos_right _ (Nat.pow_pos (by norm_num))
    refine ⟨2, Sh', (fun _ => 0), ?_, ?_, by norm_num, hbound,
      c_test2_padSingletonFunction, ?_, ?_, ?_⟩
    · intro R
      have hR : R = 0 := Subsingleton.elim _ _
      subst R
      simp [Sh', c_test2_padSingletonShape, hstarFin]
    · simp [Sh', c_test2_padSingletonShape]
    · intro f R
      have hR : R = 0 := Subsingleton.elim _ _
      subst R
      simp [Sh', c_test2_padSingletonShape, c_test2_padSingletonFunction]
    · intro K s Aset Dm S C N f hvalid R' p y
      fin_cases R'
      · have hrow : Sh'.row 0 = Sh.row Sh.star := by
          simp [Sh', c_test2_padSingletonShape, hstarFin]
        simpa [Sh', c_test2_padSingletonShape, c_test2_padSingletonFunction,
          hstarFin, hrow] using hvalid 0 p y
      · have hanchor : (Sh'.row 1).anchor = i := by
          simpa [Sh', c_test2_padSingletonShape] using c_test2_singletonRow_anchor (q := q) i
        have hν := c_test2_chainWeight_nonneg S.core.parameters C N i y
        simp [Sh', c_test2_padSingletonFunction, hanchor]
        linarith
    · intro K s Aset Dm S C a N f
      exact c_test2_rowCorrelation_padSingleton S C a N Sh Jstar hJcard hstar i f
  · have hrne : r ≠ 0 := by
      intro hz
      subst r
      exact Fin.elim0 Sh.star
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
    have htwo : 2 ≤ r := by omega
    refine ⟨r, Sh, id, (fun _ => rfl), rfl, htwo, hr, id, (fun _ _ => rfl), ?_, ?_⟩
    · intro K s Aset Dm S C N f hvalid R' p y
      exact hvalid R' p y
    · intro K s Aset Dm S C a N f
      rfl

def c_test2_rootOffsetScale {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a j : Fin m) (E N : ℕ) : ℕ :=
  (m + maskRowBound m + 2) *
      (S.core.parameters.H N (C.block a).1) ^ (E + 3) +
    ((S.primeStage.pool N C.gap).upper +
      FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ (E + 1) *
      (S.core.parameters.X N (C.block j).1) ^ 2

private theorem c_test2_pivotGap_eventually_large {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) (B : ℕ) :
    ∀ᶠ N in atTop, B ≤ A.H N i := by
  let E : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale A.M
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hlarge := (A.Hdom i 1 (by norm_num)).eventually_ge_atTop (B : ℝ)
  filter_upwards [hlarge] with N hN
  have hEone : 1 ≤ E N := by
    dsimp [E, OAI.AdmissibleMicrocellBoundary.earlierScale]
    have hM : 0 ≤ (A.M N : ℝ) := Nat.cast_nonneg _
    have hP : 0 ≤ (OAI.SourceAdmissible.previous (A.X N) i : ℝ) := Nat.cast_nonneg _
    linarith
  have hN' : (B : ℝ) ≤ (A.H N i : ℝ) / E N := by
    simpa [E, Real.rpow_one] using hN
  have hHnonneg : 0 ≤ (A.H N i : ℝ) := by positivity
  have hdiv : (A.H N i : ℝ) / E N ≤ A.H N i := div_le_self hHnonneg hEone
  exact_mod_cast le_trans hN' hdiv

theorem c_test2_poolLower_ge_twiceMasterV_eventually {K s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop,
      2 * FromArithmetic.masterScaleV S.core.parameters N l ≤
        (S.primeStage.pool N l).lower := by
  have hlarge :=
    (S.primeStage.pool_lower_dominates l 1 (by norm_num)).eventually_ge_atTop 2
  filter_upwards [hlarge] with N hN
  have hV : 0 < (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    unfold FromArithmetic.masterScaleV
    positivity
  have hratio : 2 ≤ (S.primeStage.pool N l).lower /
      (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    simpa [Real.rpow_one] using hN
  have hle := (le_div_iff₀ hV).mp hratio
  exact_mod_cast hle

theorem c_test2_rootSamplerScaleFacts {K s m : ℕ} {Aset : Finset ℚ}
    {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a j : Fin m) (hja : j < a) (E : ℕ) (k b : ℕ → ℕ)
    (hkbound : ∀ N, k N ≤
      ((S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ E)
    (hbBound : ∀ N, b N ≤
      ((S.primeStage.pool N C.gap).upper +
        FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ (E + 1)) :
    (∀ N, b N * (S.core.parameters.X N (C.block j).1) ^ 2 ≤
      c_test2_rootOffsetScale S C a j E N) ∧
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (S.core.parameters.X N (C.block a).1 : ℝ))
      (fun N => ((2 + primorial (N + 1) + k N +
        c_test2_rootOffsetScale S C a j E N +
        FromArithmetic.masterScaleV S.core.parameters N C.gap : ℕ) : ℝ)) ∧
    OAI.MicrocellScale.Dominates
      (fun N => Real.log (S.core.parameters.X N (C.block j).1 : ℝ))
      (fun N => ((2 + primorial (N + 1) + k N +
        FromArithmetic.masterScaleV S.core.parameters N C.gap : ℕ) : ℝ)) := by
  let A := S.core.parameters
  let size : ℕ → ℕ := fun N =>
    (S.primeStage.pool N C.gap).upper + FromArithmetic.masterScaleV A N C.gap
  have hsizeA := c_test2_masterSize_le_pivotGap_eventually S C a
    (C.pivots_after_gap a)
  have hsizeJ := c_test2_masterSize_le_pivotGap_eventually S C j
    (C.pivots_after_gap j)
  have hprevA := c_test2_previous_le_gap_eventually A (C.block a).1
  have hXjPrev : ∀ N,
      A.X N (C.block j).1 ≤ OAI.SourceAdmissible.previous (A.X N) (C.block a).1 :=
    c_test2_pivot_cutoff_le_previous A C j a hja
  have hAlarge := c_test2_pivotGap_eventually_large A (C.block a).1
    (m + maskRowBound m + 5)
  have hJlarge := c_test2_pivotGap_eventually_large A (C.block j).1 4
  have hWleV : ∀ N, primorial (N + 1) ≤ FromArithmetic.masterScaleV A N C.gap := by
    intro N
    have hWM := A.Wle N
    unfold FromArithmetic.masterScaleV
    omega
  have hBoundA : ∀ᶠ N in atTop,
      2 + primorial (N + 1) + k N + c_test2_rootOffsetScale S C a j E N +
          FromArithmetic.masterScaleV A N C.gap ≤
        (A.H N (C.block a).1) ^ (E + 4) := by
    filter_upwards [hsizeA, hprevA, hAlarge] with N hsize hprev hlarge
    let x := A.H N (C.block a).1
    have hx4 : 4 ≤ x := by omega
    have hsizeLe : size N ≤ x := by simpa [size] using hsize
    have hXjLe : A.X N (C.block j).1 ≤ x :=
      (hXjPrev N).trans (by simpa using hprev)
    have hVle : FromArithmetic.masterScaleV A N C.gap ≤ x := by
      have htmp : size N ≤ x := hsizeLe
      dsimp [size] at htmp
      omega
    have hWle : primorial (N + 1) ≤ x := (hWleV N).trans hVle
    have hkx : k N ≤ x ^ E := by
      calc
        k N ≤ size N ^ E := hkbound N
        _ ≤ x ^ E := Nat.pow_le_pow_left hsizeLe E
    have hrootTerm :
        size N ^ (E + 1) * (A.X N (C.block j).1) ^ 2 ≤ x ^ (E + 3) := by
      calc
        _ ≤ x ^ (E + 1) * x ^ 2 := by
          exact Nat.mul_le_mul
            (Nat.pow_le_pow_left hsizeLe (E + 1))
            (Nat.pow_le_pow_left hXjLe 2)
        _ = x ^ (E + 3) := by rw [← Nat.pow_add]
    have hrootLe : c_test2_rootOffsetScale S C a j E N ≤
        (m + maskRowBound m + 3) * x ^ (E + 3) := by
      change (m + maskRowBound m + 2) * x ^ (E + 3) +
          size N ^ (E + 1) * (A.X N (C.block j).1) ^ 2 ≤
        (m + maskRowBound m + 3) * x ^ (E + 3)
      calc
        _ ≤ (m + maskRowBound m + 2) * x ^ (E + 3) + x ^ (E + 3) :=
          Nat.add_le_add_left hrootTerm _
        _ = ((m + maskRowBound m + 2) + 1) * x ^ (E + 3) := by
          ring
        _ = (m + maskRowBound m + 3) * x ^ (E + 3) := by congr 1 <;> omega
    have htarget :
        2 + primorial (N + 1) + k N + c_test2_rootOffsetScale S C a j E N +
          FromArithmetic.masterScaleV A N C.gap ≤
        2 + 2 * x + x ^ E + (m + maskRowBound m + 3) * x ^ (E + 3) := by
      omega
    exact htarget.trans (by
      simpa [x] using c_test2_natSamplerTargetBound
        (x := x) (c := m + maskRowBound m + 3) (e := E) hx4 (by omega))
  have hBoundJ : ∀ᶠ N in atTop,
      2 + primorial (N + 1) + k N + FromArithmetic.masterScaleV A N C.gap ≤
        (A.H N (C.block j).1) ^ (E + 4) := by
    filter_upwards [hsizeJ, hJlarge] with N hsize hlarge
    let x := A.H N (C.block j).1
    have hx4 : 4 ≤ x := by omega
    have hsizeLe : size N ≤ x := by simpa [size] using hsize
    have hVle : FromArithmetic.masterScaleV A N C.gap ≤ x := by
      dsimp [size] at hsizeLe
      omega
    have hWle : primorial (N + 1) ≤ x := (hWleV N).trans hVle
    have hkx : k N ≤ x ^ E := by
      calc
        k N ≤ size N ^ E := hkbound N
        _ ≤ x ^ E := Nat.pow_le_pow_left hsizeLe E
    have htarget :
        2 + primorial (N + 1) + k N + FromArithmetic.masterScaleV A N C.gap ≤
          2 + 2 * x + x ^ E := by omega
    exact htarget.trans (by
      simpa [x] using c_test2_natSamplerTargetBound
        (x := x) (c := 0) (e := E) hx4 (by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro N
    have hsizePos : 0 < size N := by
      dsimp [size, FromArithmetic.masterScaleV]
      omega
    exact (Nat.mul_le_mul_right _ (hbBound N)).trans (Nat.le_add_left _ _)
  · exact c_test2_cutoffLog_dominates_powerTarget A (C.block a).1
      (fun N => 2 + primorial (N + 1) + k N + c_test2_rootOffsetScale S C a j E N +
        FromArithmetic.masterScaleV A N C.gap)
      (fun _ => by omega) (E + 4) (by omega) hBoundA
  · exact c_test2_cutoffLog_dominates_powerTarget A (C.block j).1
      (fun N => 2 + primorial (N + 1) + k N + FromArithmetic.masterScaleV A N C.gap)
      (fun _ => by omega) (E + 4) (by omega) hBoundJ

def c_test2_subsetToBits {d : ℕ} (s : Finset (Fin d)) : Fin d → Fin 2 :=
  fun i => if i ∈ s then 1 else 0

def c_test2_bitsToSubset {d : ℕ} (v : Fin d → Fin 2) : Finset (Fin d) :=
  Finset.univ.filter fun i => v i = 1

noncomputable def c_test2_subsetBitsEquiv (d : ℕ) :
    Finset (Fin d) ≃ (Fin d → Fin 2) where
  toFun := c_test2_subsetToBits
  invFun := c_test2_bitsToSubset
  left_inv := by
    intro s
    ext i
    simp [c_test2_subsetToBits, c_test2_bitsToSubset]
  right_inv := by
    intro v
    funext i
    have hv : v i = 0 ∨ v i = 1 := by
      have hvval : (v i).val = 0 ∨ (v i).val = 1 := by omega
      rcases hvval with h0 | h1
      · exact Or.inl (Fin.ext (by simpa using h0))
      · exact Or.inr (Fin.ext (by simpa using h1))
    rcases hv with h0 | h1
    · simp [c_test2_subsetToBits, c_test2_bitsToSubset, h0]
    · simp [c_test2_subsetToBits, c_test2_bitsToSubset, h1]

theorem c_test2_shiftAverage_reindex {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (L : ℕ)
    (F : (α → Fin 2 → ℕ) → ℝ) :
    shiftAverage α L F =
      shiftAverage β L (fun u => F (fun a => u (e a))) := by
  classical
  let eFun : (α → Fin 2 → ℕ) ≃ (β → Fin 2 → ℕ) :=
    Equiv.piCongrLeft (fun _ : β => Fin 2 → ℕ) e
  let sα := Fintype.piFinset (fun _ : α =>
    Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  let sβ := Fintype.piFinset (fun _ : β =>
    Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hsum : ∑ u ∈ sα, F u =
      ∑ u ∈ sβ, F (fun a => u (e a)) := by
    apply Finset.sum_equiv eFun
    · intro u
      simp only [sα, sβ, Fintype.mem_piFinset]
      change (∀ a : α, ∀ bit : Fin 2, u a bit ∈ Finset.range L) ↔
        (∀ b : β, ∀ bit : Fin 2, eFun u b bit ∈ Finset.range L)
      constructor
      · intro h b
        intro bit
        simpa [eFun, Equiv.piCongrLeft] using h (e.symm b) bit
      · intro h a
        intro bit
        have hh := h (e a) bit
        simpa [eFun, Equiv.piCongrLeft] using hh
    · intro u hu
      simp [eFun, Equiv.piCongrLeft]
  unfold shiftAverage
  rw [← hcard, hsum]

theorem c_test2_cubeProduct_reindex {d : ℕ} (g : ℤ → ℝ) (y M : ℤ)
    (u : Fin d → Fin 2 → ℕ) :
    (∏ v : Fin d → Fin 2,
      g (y + M * ∑ j : Fin d,
        if v j = 1 then (u j 1 : ℤ) - u j 0 else 0)) =
      ∏ s : Finset (Fin d), g (y + M * ∑ j ∈ s, ((u j 1 : ℤ) - u j 0)) := by
  classical
  let e := c_test2_subsetBitsEquiv d
  apply Fintype.prod_equiv e.symm
  intro v
  congr 2
  have hs : e.symm v = Finset.univ.filter fun j => v j = 1 := rfl
  rw [hs, Finset.sum_filter]

theorem c_test2_cubeProduct_reindex_equiv {α : Type*} [Fintype α] [DecidableEq α]
    {d : ℕ} (e : α ≃ Fin d) (g : ℤ → ℝ) (y M : ℤ)
    (u : α → Fin 2 → ℕ) :
    (∏ v : α → Fin 2,
      g (y + M * ∑ i : α,
        if v i = 1 then (u i 1 : ℤ) - u i 0 else 0)) =
      ∏ s : Finset (Fin d),
        g (y + M * ∑ j ∈ s, ((u (e.symm j) 1 : ℤ) - u (e.symm j) 0)) := by
  classical
  let eFun : (α → Fin 2) ≃ (Fin d → Fin 2) :=
    Equiv.piCongrLeft (fun _ : Fin d => Fin 2) e
  let eTotal : (α → Fin 2) ≃ Finset (Fin d) :=
    eFun.trans (c_test2_subsetBitsEquiv d).symm
  have hsum (v : α → Fin 2) :
      (∑ i : α, if v i = 1 then (u i 1 : ℤ) - u i 0 else 0) =
        ∑ j : Fin d, if v (e.symm j) = 1 then
          (u (e.symm j) 1 : ℤ) - u (e.symm j) 0 else 0 := by
    apply Fintype.sum_equiv e
    intro i
    simp [e.left_inv i]
  apply Fintype.prod_equiv eTotal
  intro v
  congr 2
  have hs : eTotal v = Finset.univ.filter fun j => v (e.symm j) = 1 := by
    ext j
    simp [eTotal, eFun, Equiv.piCongrLeft, c_test2_subsetBitsEquiv,
      c_test2_bitsToSubset]
  rw [hs, Finset.sum_filter, ← hsum]

theorem c_test2_targetVertex_decomposition {m q r : ℕ} (c : Fin m → ℚ)
    (Sh : RowShape m q r) (p : Fin q → ℕ) (M : ℕ) (z : Fin m → ℤ)
    (u : NonTarget Sh → Fin 2 → ℕ) (ω : NonTarget Sh → Fin 2)
    (alpha : Fin m → ℕ) (aStar j : Fin m) (haj : aStar ≠ j)
    (hcoeff : ∀ i, c i / c (Sh.row Sh.star).anchor *
      (Sh.row Sh.star).value p i = (alpha i : ℚ))
    (k b : ℕ) (hk : k = alpha aStar) (hb : b = alpha j) :
    targetVertex c Sh p M (fun i => (z i : ℚ)) u ω =
      ((k : ℤ) * z aStar + (b : ℤ) * z j +
        ∑ i : CTest2OtherPivot aStar j, (alpha i.1 : ℤ) * z i.1 +
        (M : ℤ) * ∑ R : NonTarget Sh, (u R 0 : ℤ) +
        (M : ℤ) * (∑ R : NonTarget Sh,
          (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0)) : ℚ) := by
  classical
  let T := Sh.row Sh.star
  have hrow := c_test2_rowForm_eq_coeff_sum c T p z alpha hcoeff
  have hsum := c_test2_alphaWeightedSum_split aStar j haj alpha z
  have hsumQ :
      (∑ i : Fin m, (alpha i : ℚ) * (z i : ℚ)) =
        ((∑ i : Fin m, (alpha i : ℤ) * z i : ℤ) : ℚ) := by
    norm_cast
  have hbits (R : NonTarget Sh) :
      (u R (ω R) : ℤ) = (u R 0 : ℤ) +
        (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0) := by
    generalize hω : ω R = v
    fin_cases v <;> simp [hω]
  have hsumBits :
      (∑ R : NonTarget Sh, (u R (ω R) : ℤ)) =
        (∑ R : NonTarget Sh, (u R 0 : ℤ)) +
          ∑ R : NonTarget Sh,
            (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0) := by
    calc
      _ = ∑ R : NonTarget Sh,
          ((u R 0 : ℤ) + (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0)) := by
            apply Finset.sum_congr rfl
            intro R hR
            exact hbits R
      _ = _ := Finset.sum_add_distrib
  have hshift :
      (M : ℚ) * ∑ R : NonTarget Sh, (u R (ω R) : ℚ) =
        (((M : ℤ) * ∑ R : NonTarget Sh, (u R 0 : ℤ) +
          (M : ℤ) * ∑ R : NonTarget Sh,
            (if ω R = 1 then (u R 1 : ℤ) - u R 0 else 0) : ℤ) : ℚ) := by
    have hsumBitsQ :
        (∑ R : NonTarget Sh, (u R (ω R) : ℚ)) =
          (∑ R : NonTarget Sh, (u R 0 : ℚ)) +
            ∑ R : NonTarget Sh,
              (if ω R = 1 then (u R 1 : ℚ) - u R 0 else 0) := by
      exact_mod_cast hsumBits
    calc
      _ = (M : ℚ) *
          ((∑ R : NonTarget Sh, (u R 0 : ℚ)) +
            ∑ R : NonTarget Sh,
              (if ω R = 1 then (u R 1 : ℚ) - u R 0 else 0)) := by rw [hsumBitsQ]
      _ = _ := by push_cast; ring
  unfold targetVertex
  rw [hrow, hsumQ, hsum, hk, hb, hshift]
  push_cast
  ring

theorem c_test2_weighted_tsum_error {α : Type*} (μ F G : α → ℝ) (δ : ℝ)
    (hμnonneg : ∀ x, 0 ≤ μ x) (hμsum : Summable μ)
    (hμone : ∑' x, μ x = 1) (hF : Summable (fun x => μ x * F x))
    (hG : Summable (fun x => μ x * G x))
    (hpoint : ∀ x, |F x - G x| ≤ δ) (hδ : 0 ≤ δ) :
    |(∑' x, μ x * F x) - ∑' x, μ x * G x| ≤ δ := by
  have hdiff : Summable (fun x => μ x * (F x - G x)) := by
    simpa only [mul_sub] using hF.sub hG
  have hsum :
      (∑' x, μ x * F x) - ∑' x, μ x * G x =
        ∑' x, μ x * (F x - G x) := by
    rw [← hF.tsum_sub hG]
    exact tsum_congr fun x => by ring
  have hdom : Summable (fun x => μ x * δ) := hμsum.mul_right δ
  have hterm : ∀ x, ‖μ x * (F x - G x)‖ ≤ μ x * δ := by
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμnonneg x)]
    exact mul_le_mul_of_nonneg_left (hpoint x) (hμnonneg x)
  calc
    |(∑' x, μ x * F x) - ∑' x, μ x * G x| =
        |∑' x, μ x * (F x - G x)| := by rw [hsum]
    _ ≤ ∑' x, ‖μ x * (F x - G x)‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' x, μ x * δ := hdiff.norm.tsum_le_tsum hterm hdom
    _ = δ := by rw [tsum_mul_right, hμone]; ring

theorem c_test2_weighted_tsum_error_of_zero_or {α : Type*} (μ F G : α → ℝ) (δ : ℝ)
    (hμnonneg : ∀ x, 0 ≤ μ x) (hμsum : Summable μ)
    (hμone : ∑' x, μ x = 1) (hF : Summable (fun x => μ x * F x))
    (hG : Summable (fun x => μ x * G x))
    (hpoint : ∀ x, μ x = 0 ∨ |F x - G x| ≤ δ) (hδ : 0 ≤ δ) :
    |(∑' x, μ x * F x) - ∑' x, μ x * G x| ≤ δ := by
  have hpoint' : ∀ x, |μ x * (F x - G x)| ≤ μ x * δ := by
    intro x
    rcases hpoint x with hzero | hbound
    · simp [hzero]
    · rw [abs_mul, abs_of_nonneg (hμnonneg x)]
      exact mul_le_mul_of_nonneg_left hbound (hμnonneg x)
  have hdiff : Summable (fun x => μ x * (F x - G x)) := by
    simpa only [mul_sub] using hF.sub hG
  have hsum :
      (∑' x, μ x * F x) - ∑' x, μ x * G x =
        ∑' x, μ x * (F x - G x) := by
    rw [← hF.tsum_sub hG]
    exact tsum_congr fun x => by ring
  have hdom : Summable (fun x => μ x * δ) := hμsum.mul_right δ
  calc
    |(∑' x, μ x * F x) - ∑' x, μ x * G x| =
        |∑' x, μ x * (F x - G x)| := by rw [hsum]
    _ ≤ ∑' x, ‖μ x * (F x - G x)‖ := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' x, μ x * δ := hdiff.norm.tsum_le_tsum (fun x => by
      rw [Real.norm_eq_abs]
      exact hpoint' x) hdom
    _ = δ := by rw [tsum_mul_right, hμone]; ring

theorem c_test2_pivotSampling_expectation_error {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (a j : Fin m) (haj : a ≠ j) (Xa Xj k b : ℕ)
    (hXa : Xa = A.X N (C.block a).1) (hXj : Xj = A.X N (C.block j).1)
    (Fbase : ℤ → ℝ) (Fwhole : (Fin m → ℤ) → ℝ)
    (offset : (CTest2OtherPivot a j → ℤ) → ℤ)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hdecomp : ∀ r za zj,
      Fwhole ((c_test2_pivotPairRestEquiv a j haj).symm ((za, zj), r)) =
        Fbase ((k : ℤ) * za + (b : ℤ) * zj + offset r))
    (hsample : ∀ r,
      c_test2_restPivotMass A C N a j r = 0 ∨
        |(∑' za : ℤ, ∑' zj : ℤ,
            harmonicLaw Xa (primorial (N + 1)) za *
              harmonicLaw Xj (primorial (N + 1)) zj *
              Fbase ((k : ℤ) * za + (b : ℤ) * zj + offset r)) -
          ∑' y : ℤ, harmonicLaw Xa (primorial (N + 1)) y * Fbase y| ≤ δ)
    (hRestNonneg : ∀ r, 0 ≤ c_test2_restPivotMass A C N a j r)
    (hRestSummable : Summable (c_test2_restPivotMass A C N a j))
    (hRestOne : ∑' r, c_test2_restPivotMass A C N a j r = 1)
    (hAvgSummable : Summable (fun r => c_test2_restPivotMass A C N a j r *
      (∑' za : ℤ, ∑' zj : ℤ,
        harmonicLaw Xa (primorial (N + 1)) za *
          harmonicLaw Xj (primorial (N + 1)) zj *
          Fbase ((k : ℤ) * za + (b : ℤ) * zj + offset r)))) :
    |(∑' z : Fin m → ℤ, pivotMass A C N z * Fwhole z) -
      ∑' y : ℤ, harmonicLaw Xa (primorial (N + 1)) y * Fbase y| ≤ δ := by
  let μr := c_test2_restPivotMass A C N a j
  let ref : ℝ := ∑' y : ℤ, harmonicLaw Xa (primorial (N + 1)) y * Fbase y
  let pairAvg : (CTest2OtherPivot a j → ℤ) → ℝ := fun r =>
    ∑' za : ℤ, ∑' zj : ℤ,
      harmonicLaw Xa (primorial (N + 1)) za *
        harmonicLaw Xj (primorial (N + 1)) zj *
          Fbase ((k : ℤ) * za + (b : ℤ) * zj + offset r)
  have hpair (r : CTest2OtherPivot a j → ℤ) :
      (∑' za : ℤ, ∑' zj : ℤ,
        harmonicLaw Xa (primorial (N + 1)) za *
          harmonicLaw Xj (primorial (N + 1)) zj *
            Fwhole ((c_test2_pivotPairRestEquiv a j haj).symm ((za, zj), r))) =
      pairAvg r := by
    calc
      _ = ∑' za : ℤ, ∑' zj : ℤ,
          harmonicLaw Xa (primorial (N + 1)) za *
            harmonicLaw Xj (primorial (N + 1)) zj *
              Fbase ((k : ℤ) * za + (b : ℤ) * zj + offset r) := by
        apply tsum_congr
        intro za
        apply tsum_congr
        intro zj
        rw [hdecomp r za zj]
      _ = pairAvg r := rfl
  have hsplit := c_test2_pivotMass_tsum_split A C N a j haj Fwhole
  have hleft :
      (∑' z : Fin m → ℤ, pivotMass A C N z * Fwhole z) =
        ∑' r, c_test2_restPivotMass A C N a j r * pairAvg r := by
    calc
      _ = ∑' r, c_test2_restPivotMass A C N a j r *
            ∑' za : ℤ, ∑' zj : ℤ,
              harmonicLaw Xa (primorial (N + 1)) za *
                harmonicLaw Xj (primorial (N + 1)) zj *
                  Fwhole ((c_test2_pivotPairRestEquiv a j haj).symm ((za, zj), r)) := by
        simpa [hXa, hXj] using hsplit
      _ = ∑' r, c_test2_restPivotMass A C N a j r * pairAvg r := by
        apply tsum_congr
        intro r
        rw [hpair r]
  have hRefSum : Summable (fun r => c_test2_restPivotMass A C N a j r * ref) :=
    hRestSummable.mul_right _
  have hRef : (∑' r, c_test2_restPivotMass A C N a j r * ref) = ref := by
    rw [tsum_mul_right, hRestOne]
    ring
  have hpoint : ∀ r, c_test2_restPivotMass A C N a j r = 0 ∨
      |pairAvg r - ref| ≤ δ := by
    intro r
    rcases hsample r with hz | hbound
    · exact Or.inl hz
    · exact Or.inr (by simpa [pairAvg, ref] using hbound)
  have hweighted := c_test2_weighted_tsum_error_of_zero_or
    (c_test2_restPivotMass A C N a j) pairAvg
    (fun _ => ref) δ hRestNonneg hRestSummable hRestOne hAvgSummable hRefSum
    hpoint hδ
  rw [hleft]
  change |∑' r, μr r * pairAvg r - ref| ≤ δ
  rw [← hRef]
  exact hweighted

theorem c_test2_shiftAverage_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (F G : (ι → Fin 2 → ℕ) → ℝ) (δ : ℝ) (hL : 0 < L)
    (hpoint : ∀ u, |F u - G u| ≤ δ) :
    |shiftAverage ι L F - shiftAverage ι L G| ≤ δ := by
  classical
  let U := Fintype.piFinset (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  have hcard : (U.card : ℝ) = (L : ℝ) ^ (2 * Fintype.card ι) := by
    simp [U, Fintype.card_piFinset, pow_mul]
  have hden : 0 < (L : ℝ) ^ (2 * Fintype.card ι) := by positivity
  have hsum :
      |(∑ u ∈ U, F u) - ∑ u ∈ U, G u| ≤ (U.card : ℝ) * δ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ u ∈ U, (F u - G u)| ≤ ∑ u ∈ U, |F u - G u| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ u ∈ U, δ := Finset.sum_le_sum fun u hu => hpoint u
      _ = (U.card : ℝ) * δ := by simp
  unfold shiftAverage
  rw [← mul_sub]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hden.le)]
  calc
    ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ *
        |(∑ u ∈ U, F u) - ∑ u ∈ U, G u| ≤
      ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹ * ((U.card : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hden.le)
    _ = δ := by rw [hcard]; field_simp [ne_of_gt hden]

theorem c_test2_shiftAverage_tsum_commute {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (L : ℕ) (μ : β → ℝ) (F : (ι → Fin 2 → ℕ) → β → ℝ)
    (hSummable : ∀ u, Summable (fun b => μ b * F u b)) :
    shiftAverage ι L (fun u => ∑' b, μ b * F u b) =
      ∑' b, μ b * shiftAverage ι L (fun u => F u b) := by
  classical
  let U := Fintype.piFinset (fun _ : ι => Fintype.piFinset fun _ : Fin 2 => Finset.range L)
  let D : ℝ := ((L : ℝ) ^ (2 * Fintype.card ι))⁻¹
  have hswap :
      (∑' b, μ b * ∑ u ∈ U, F u b) =
        ∑ u ∈ U, ∑' b, μ b * F u b := by
    calc
      _ = ∑' b, ∑ u ∈ U, μ b * F u b := by
        apply tsum_congr
        intro b
        rw [Finset.mul_sum]
      _ = ∑ u ∈ U, ∑' b, μ b * F u b :=
        Summable.tsum_finsetSum (fun u hu => hSummable u)
  change D * (∑ u ∈ U, ∑' b, μ b * F u b) =
    ∑' b, μ b * (D * ∑ u ∈ U, F u b)
  calc
    _ = D * (∑' b, μ b * ∑ u ∈ U, F u b) := by rw [hswap.symm]
    _ = ∑' b, D * (μ b * ∑ u ∈ U, F u b) := by
      rw [← tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro b
      ring

theorem c_test2_integerResidue_natMod {K : ℕ} (hK : 0 < K) {z : ℤ}
    (hz : 0 ≤ z) :
    FromArithmetic.integerResidue K hK z = ⟨z.toNat % K, Nat.mod_lt _ hK⟩ := by
  apply Fin.ext
  have hKz : (0 : ℤ) < (K : ℤ) := by exact_mod_cast hK
  have hleft := Int.toNat_of_nonneg (Int.emod_nonneg z (Int.ne_of_gt hKz))
  have hright : (((z.toNat % K : ℕ) : ℤ)) = z % (K : ℤ) := by
    rw [Int.natCast_mod, Int.toNat_of_nonneg hz]
  have hcast : ((z % (K : ℤ)).toNat : ℤ) = ((z.toNat % K : ℕ) : ℤ) := by
    rw [hleft, hright]
  exact_mod_cast hcast

theorem c_test2_harmonicResidueLaw_tsum_one {X W K : ℕ} (hK : 0 < K)
    (hX : 0 < X) (hZ : 0 < harmonicNormalizer X W) :
    ∑ a : Fin K, harmonicResidueLaw (harmonicLaw X W) K a = 1 := by
  classical
  let support := c_test2_harmonicIntSupport X
  have hzero (a : Fin K) (z : ℤ) (hz : z ∉ support) :
      (if 0 ≤ z ∧ z.toNat % K = a.val then harmonicLaw X W z else 0) = 0 := by
    by_cases hc : 0 ≤ z ∧ z.toNat % K = a.val
    · rw [if_pos hc, c_test2_harmonicLaw_zero_outside (by simpa [support] using hz)]
    · simp [hc]
  have hsum (a : Fin K) :
      harmonicResidueLaw (harmonicLaw X W) K a =
        ∑ z ∈ support,
          if 0 ≤ z ∧ z.toNat % K = a.val then harmonicLaw X W z else 0 := by
    unfold harmonicResidueLaw
    exact tsum_eq_sum (s := support) (hzero a)
  have hpartition (z : ℤ) (hz : z ∈ support) :
      (∑ a : Fin K,
        if 0 ≤ z ∧ z.toNat % K = a.val then harmonicLaw X W z else 0) =
        harmonicLaw X W z := by
    have hzIco : z ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℤ) := by
      simpa [support, c_test2_harmonicIntSupport] using hz
    have hX0 : (0 : ℤ) ≤ (X : ℤ) := by exact_mod_cast Nat.zero_le X
    have hz0 : 0 ≤ z := hX0.trans (Finset.mem_Ico.mp hzIco).1
    let a : Fin K := ⟨z.toNat % K, Nat.mod_lt _ hK⟩
    rw [Finset.sum_eq_single a]
    · simp [hz0, a]
    · intro b hb hba
      have hneq : z.toNat % K ≠ b.val := by
        intro hv
        exact hba (Fin.ext hv.symm)
      simp [hz0, hneq]
    · simp
  calc
    _ = ∑ a : Fin K, ∑ z ∈ support,
          if 0 ≤ z ∧ z.toNat % K = a.val then harmonicLaw X W z else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hsum a
    _ = ∑ z ∈ support, ∑ a : Fin K,
          if 0 ≤ z ∧ z.toNat % K = a.val then harmonicLaw X W z else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ z ∈ support, harmonicLaw X W z := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hpartition z hz
    _ = 1 := by
          have hLaw := c_test2_harmonicLaw_tsum_one hX hZ
          rw [← hLaw]
          symm
          apply tsum_eq_sum (s := support)
          intro z hz
          exact c_test2_harmonicLaw_zero_outside (by simpa [support] using hz)

theorem c_test2_productPushforwardLaw {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [Countable α] [DecidableEq β]
    (μ : ι → α → ℝ) (support : ι → Finset α)
    (hzero : ∀ i x, x ∉ support i → μ i x = 0)
    (f : ι → α → β) (r : ι → β) :
    (∑' x : ι → α, (∏ i, μ i (x i)) *
      (if (fun i => f i (x i)) = r then (1 : ℝ) else 0)) =
      ∏ i, ∑' x : α, μ i x * (if f i x = r i then (1 : ℝ) else 0) := by
  classical
  let domain : Finset (ι → α) := Fintype.piFinset support
  let e := c_test2_piFinsetSubtypeEquiv support
  have hzeroProd (x : ι → α) (hx : x ∉ domain) :
      (∏ i, μ i (x i)) * (if (fun i => f i (x i)) = r then (1 : ℝ) else 0) = 0 := by
    have hnot : ¬ ∀ i, x i ∈ support i := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (hzero i (x i) hi)]
    simp
  have htsum :
      (∑' x : ι → α, (∏ i, μ i (x i)) *
        (if (fun i => f i (x i)) = r then (1 : ℝ) else 0)) =
        ∑ x ∈ domain, (∏ i, μ i (x i)) *
          (if (fun i => f i (x i)) = r then (1 : ℝ) else 0) :=
    tsum_eq_sum (s := domain) hzeroProd
  have hattach :
      (∑ x ∈ domain, (∏ i, μ i (x i)) *
        (if (fun i => f i (x i)) = r then (1 : ℝ) else 0)) =
        ∑ x : domain, (∏ i, μ i (x.1 i)) *
          (if (fun i => f i (x.1 i)) = r then (1 : ℝ) else 0) := by
    rw [← Finset.sum_attach]
    simp
  have htransport :
      (∑ x : domain, (∏ i, μ i (x.1 i)) *
        (if (fun i => f i (x.1 i)) = r then (1 : ℝ) else 0)) =
        ∑ x : ∀ i, {a : α // a ∈ support i},
          ∏ i, μ i (x i).1 * (if f i (x i).1 = r i then (1 : ℝ) else 0) := by
    apply Fintype.sum_equiv e
    intro x
    by_cases hx : (fun i => f i (x.1 i)) = r
    · have hcoord : ∀ i, f i (x.1 i) = r i := fun i => congrFun hx i
      simp [e, c_test2_piFinsetSubtypeEquiv, hx, hcoord]
    · have hcoord : ∃ i, f i (x.1 i) ≠ r i := by
        by_contra h
        apply hx
        funext i
        exact Classical.not_not.mp (fun hn : f i (x.1 i) ≠ r i => h ⟨i, hn⟩)
      obtain ⟨i, hi⟩ := hcoord
      have hprodZero :
          (∏ j, μ j (x.1 j) * (if f j (x.1 j) = r j then (1 : ℝ) else 0)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
      have hprodZero' :
          (∏ j, if f j (x.1 j) = r j then μ j (x.1 j) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
      simp [e, c_test2_piFinsetSubtypeEquiv, hx, hprodZero, hprodZero']
  have hprodSum :
      (∑ x : ∀ i, {a : α // a ∈ support i},
        ∏ i, μ i (x i).1 * (if f i (x i).1 = r i then (1 : ℝ) else 0)) =
        ∏ i, ∑ x : {a : α // a ∈ support i},
          μ i x.1 * (if f i x.1 = r i then (1 : ℝ) else 0) := by
    symm
    exact Fintype.prod_sum fun i (x : {a : α // a ∈ support i}) =>
      μ i x.1 * (if f i x.1 = r i then (1 : ℝ) else 0)
  have hcoordSum (i : ι) :
      (∑ x : {a : α // a ∈ support i},
        μ i x.1 * (if f i x.1 = r i then (1 : ℝ) else 0)) =
        ∑' x : α, μ i x * (if f i x = r i then (1 : ℝ) else 0) := by
    let term : α → ℝ := fun x => μ i x * (if f i x = r i then (1 : ℝ) else 0)
    calc
      _ = ∑ x ∈ support i, term x := by
        change (∑ x : {a : α // a ∈ support i}, term x.1) =
          ∑ x ∈ support i, term x
        rw [← Finset.sum_subtype (s := support i) (h := fun _ => Iff.rfl)]
      _ = ∑' x : α, term x := (tsum_eq_sum (s := support i) (by
        intro x hx
        simp [term, hzero i x hx])).symm
  calc
    _ = ∑ x ∈ domain, (∏ i, μ i (x i)) *
          (if (fun i => f i (x i)) = r then (1 : ℝ) else 0) := htsum
    _ = ∑ x : domain, (∏ i, μ i (x.1 i)) *
          (if (fun i => f i (x.1 i)) = r then (1 : ℝ) else 0) := hattach
    _ = ∑ x : ∀ i, {a : α // a ∈ support i},
          ∏ i, μ i (x i).1 * (if f i (x i).1 = r i then (1 : ℝ) else 0) := htransport
    _ = ∏ i, ∑ x : {a : α // a ∈ support i},
          μ i x.1 * (if f i x.1 = r i then (1 : ℝ) else 0) := hprodSum
    _ = ∏ i, ∑' x : α, μ i x * (if f i x = r i then (1 : ℝ) else 0) := by
      congr 1
      funext i
      exact hcoordSum i

theorem c_test2_pivotBaseResidueLaw_eq_product {n m K : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (hK : 0 < K) (r : Fin m → Fin K) :
    FromArithmetic.baseResidueLaw K hK (pivotMass A C N) r =
      ∏ i, harmonicResidueLaw
        (harmonicLaw (A.X N (C.block i).1) (primorial (N + 1))) K (r i) := by
  classical
  let μ : Fin m → ℤ → ℝ := fun i z =>
    harmonicLaw (A.X N (C.block i).1) (primorial (N + 1)) z
  let support : Fin m → Finset ℤ := fun i =>
    c_test2_harmonicIntSupport (A.X N (C.block i).1)
  have hzero (i : Fin m) (z : ℤ) (hz : z ∉ support i) : μ i z = 0 := by
    exact c_test2_harmonicLaw_zero_outside (by simpa [μ, support] using hz)
  have hpush := c_test2_productPushforwardLaw μ support hzero
    (fun _ z => FromArithmetic.integerResidue K hK z) r
  have hcoord (i : Fin m) :
      (∑' z : ℤ, μ i z *
        (if FromArithmetic.integerResidue K hK z = r i then (1 : ℝ) else 0)) =
        harmonicResidueLaw (μ i) K (r i) := by
    apply tsum_congr
    intro z
    by_cases hz : z ∈ support i
    · have hz0 : 0 ≤ z := by
        have hm : z ∈ c_test2_harmonicIntSupport (A.X N (C.block i).1) := by
          simpa [support] using hz
        have hX0 : (0 : ℤ) ≤ (A.X N (C.block i).1 : ℤ) := by
          exact_mod_cast Nat.zero_le (A.X N (C.block i).1)
        exact hX0.trans (Finset.mem_Ico.mp
          (by simpa [c_test2_harmonicIntSupport] using hm)).1
      have hres := c_test2_integerResidue_natMod hK hz0
      rw [hres]
      have hfin : (⟨z.toNat % K, Nat.mod_lt _ hK⟩ : Fin K) = r i ↔
          z.toNat % K = (r i).val := Fin.ext_iff
      simp [harmonicResidueLaw, μ, hz0, hfin]
    · rw [hzero i z hz]
      simp [harmonicResidueLaw]
  have hbase :
      FromArithmetic.baseResidueLaw K hK (pivotMass A C N) r =
        (∑' x : Fin m → ℤ, (∏ i, μ i (x i)) *
          (if (fun i => FromArithmetic.integerResidue K hK (x i)) = r then (1 : ℝ) else 0)) := by
    unfold FromArithmetic.baseResidueLaw pivotMass
    simp [μ]
  rw [hbase, hpush]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hcoord i]

theorem c_test2_pivotBaseResidueLaw_finiteL1_bound {n m K : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (C : MasterChain n m) (N : ℕ)
    (hK : 0 < K) (hNorm : ∀ i, 0 < harmonicNormalizer
      (A.X N (C.block i).1) (primorial (N + 1))) (hErr : Fin m → ℝ)
    (herr : ∀ i, finiteL1
      (harmonicResidueLaw
        (harmonicLaw (A.X N (C.block i).1) (primorial (N + 1))) K)
      (uniformResidueLaw K) ≤ hErr i) :
    finiteL1
      (FromArithmetic.baseResidueLaw K hK (pivotMass A C N))
      (FromArithmetic.uniformBaseResidueLaw K m) ≤ ∑ i, hErr i := by
  classical
  let law : Fin m → Fin K → ℝ := fun i a =>
    harmonicResidueLaw
      (harmonicLaw (A.X N (C.block i).1) (primorial (N + 1))) K a
  let unif : Fin m → Fin K → ℝ := fun _ a => uniformResidueLaw K a
  have hLawNonneg (i : Fin m) (a : Fin K) : 0 ≤ law i a := by
    unfold law harmonicResidueLaw
    apply tsum_nonneg
    intro z
    split_ifs
    · exact c_test2_harmonicLaw_nonneg_of_normalizer_pos (hNorm i) z
    · positivity
  have hLawSum (i : Fin m) : ∑ a : Fin K, law i a = 1 := by
    exact c_test2_harmonicResidueLaw_tsum_one hK (A.Xpos N (C.block i).1)
      (hNorm i)
  have hUnifNonneg (i : Fin m) (a : Fin K) : 0 ≤ unif i a := by
    simp [unif, uniformResidueLaw]
  have hUnifSum (i : Fin m) : ∑ a : Fin K, unif i a = 1 := by
    have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    simp only [unif, uniformResidueLaw, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hAbsLaw (i : Fin m) : ∑ a : Fin K, |law i a| = 1 := by
    calc
      _ = ∑ a : Fin K, law i a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [abs_of_nonneg (hLawNonneg i a)]
      _ = 1 := hLawSum i
  have hAbsUnif (i : Fin m) : ∑ a : Fin K, |unif i a| = 1 := by
    calc
      _ = ∑ a : Fin K, unif i a := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [abs_of_nonneg (hUnifNonneg i a)]
      _ = 1 := hUnifSum i
  have hFactorLaw (r : Fin m → Fin K) :
      FromArithmetic.baseResidueLaw K hK (pivotMass A C N) r = ∏ i, law i (r i) := by
    rw [c_test2_pivotBaseResidueLaw_eq_product]
  have hFactorUnif (r : Fin m → Fin K) :
      FromArithmetic.uniformBaseResidueLaw K m r = ∏ i, unif i (r i) := by
    simp [FromArithmetic.uniformBaseResidueLaw, uniformResidueLaw, unif,
      Finset.prod_const, Fintype.card_fin]
  have htel := FromArithmetic.finite_product_l1_telescoping law unif
  have htel' :
      finiteL1 (fun r : Fin m → Fin K => ∏ i, law i (r i))
        (fun r => ∏ i, unif i (r i)) ≤ ∑ i, finiteL1 (law i) (unif i) := by
    simpa [hAbsLaw, hAbsUnif] using htel
  calc
    _ = finiteL1 (fun r : Fin m → Fin K => ∏ i, law i (r i))
          (fun r => ∏ i, unif i (r i)) := by
            apply Finset.sum_congr rfl
            intro r hr
            simp_rw [hFactorLaw r, hFactorUnif r]
    _ ≤ ∑ i, finiteL1 (law i) (unif i) := htel'
    _ ≤ ∑ i, hErr i := Finset.sum_le_sum fun i hi => herr i

theorem c_test2_natCutoff_dominates_of_log {X V : ℕ → ℕ}
    (hX : ∀ᶠ N in atTop, 1 ≤ X N)
    (hDom : OAI.MicrocellScale.Dominates
      (fun N => Real.log (X N : ℝ)) (fun N => (V N : ℝ))) :
    OAI.MicrocellScale.Dominates (fun N => (X N : ℝ)) (fun N => (V N : ℝ)) := by
  intro C hC
  have h := hDom C hC
  have hle : (fun N => Real.log (X N : ℝ) / (V N : ℝ) ^ C) ≤ᶠ[atTop]
      (fun N => (X N : ℝ) / (V N : ℝ) ^ C) := by
    filter_upwards [hX] with N hXN
    have hXpos : (0 : ℝ) < (X N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hXN)
    have hlog : Real.log (X N : ℝ) ≤ (X N : ℝ) := by
      have h := Real.log_le_sub_one_of_pos hXpos
      linarith
    exact div_le_div_of_nonneg_right hlog (Real.rpow_nonneg (by positivity) C)
  exact Filter.tendsto_atTop_mono' atTop hle h

theorem c_test2_samplingResidueError_superpoly {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (i : Fin m) (R : ℕ) :
    SuperPolynomialSmall
      (fun N => FromArithmetic.harmonicResidueUniformError
        (S.core.parameters.X N (C.block i).1) (primorial (N + 1)
          ) ((FromArithmetic.masterScaleV S.core.parameters N C.gap) ^ R))
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N C.gap : ℝ)) := by
  classical
  let A := S.core.parameters
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV A N C.gap
  let Ksam : ℕ → ℕ := fun N => V N ^ R
  let Hsam : ℕ → ℕ := fun _ => 1
  let Xsam : ℕ → ℕ := fun N => A.X N (C.block i).1
  let logTarget : ℕ → ℕ := fun N => 2 + primorial (N + 1) + Ksam N + V N
  let target : ℕ → ℕ := fun N => 2 + primorial (N + 1) + Ksam N + Hsam N + V N
  have hV4 : ∀ᶠ N in atTop, 4 ≤ V N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hW2 : 2 ≤ primorial (N + 1) := by
      calc
        2 = primorial 2 := by norm_num
        _ ≤ primorial (N + 1) := primorial_mono (by omega)
    have hM := A.Wle N
    dsimp [V, FromArithmetic.masterScaleV]
    omega
  have hVpos (N : ℕ) : 1 ≤ V N := by
    dsimp [V, FromArithmetic.masterScaleV]
    have hM := A.Mpos N
    omega
  have hWleV (N : ℕ) : primorial (N + 1) ≤ V N := by
    dsimp [V, FromArithmetic.masterScaleV]
    exact (A.Wle N).trans (by omega)
  have hsize : ∀ᶠ N in atTop,
      (S.primeStage.pool N C.gap).upper + V N ≤ A.H N (C.block i).1 :=
    c_test2_masterSize_le_pivotGap_eventually S C i (C.pivots_after_gap i)
  have htarget : ∀ᶠ N in atTop, target N ≤ V N ^ (R + 4) := by
    filter_upwards [hV4] with N hV
    dsimp [target, logTarget, Ksam, Hsam]
    have hV1 := hVpos N
    have hW := hWleV N
    have hWplus : primorial (N + 1) + 1 ≤ V N := by
      dsimp [V, FromArithmetic.masterScaleV]
      have hM := A.Wle N
      omega
    have hsmall : 2 + primorial (N + 1) + V N ^ R + 1 + V N ≤
        2 + 2 * V N + V N ^ R := by
      omega
    calc
      _ ≤ 2 + 2 * V N + V N ^ R := hsmall
      _ ≤ V N ^ (R + 4) := by
        simpa using c_test2_natSamplerTargetBound (x := V N) (c := 0) (e := R) hV (by omega)
  have htargetPos (N : ℕ) : 0 < target N := by
    dsimp [target, Ksam, Hsam]
    omega
  have hHpos : ∀ N, 0 < A.H N (C.block i).1 := fun N => A.Hpos N (C.block i).1
  have hVleH : ∀ᶠ N in atTop, V N ≤ A.H N (C.block i).1 := by
    filter_upwards [hsize] with N hN
    have : V N ≤ (S.primeStage.pool N C.gap).upper + V N := Nat.le_add_left _ _
    exact this.trans hN
  have hlogV : OAI.MicrocellScale.Dominates
      (fun N => Real.log (Xsam N : ℝ)) (fun N => (V N : ℝ)) := by
    exact c_test2_dominates_of_power_bound
      (fun N => by
        have hX : 1 ≤ Xsam N := by
          have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
          have hWpos : 1 ≤ primorial (N + 1) := by
            exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
          have hXfour : 4 ≤ A.X N (C.block i).1 := by
            calc
              4 = 4 * 1 := by norm_num
              _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
              _ ≤ A.X N (C.block i).1 := hraw
          have hXone : 1 ≤ A.X N (C.block i).1 := by omega
          simpa [Xsam] using hXone
        have hXreal : (1 : ℝ) ≤ (Xsam N : ℝ) := by exact_mod_cast hX
        exact Real.log_nonneg hXreal)
      (fun N => by exact_mod_cast hHpos N)
      (fun N => by exact_mod_cast hVpos N)
      1 (by norm_num)
      (by
        filter_upwards [hVleH] with N hN
        have hN' : (V N : ℝ) ≤ (A.H N (C.block i).1 : ℝ) := by exact_mod_cast hN
        simpa [Real.rpow_one] using hN')
      (A.Xdom (C.block i).1)
  have hlogTargetBound : ∀ᶠ N in atTop, logTarget N ≤ V N ^ (R + 4) := by
    filter_upwards [htarget] with N hN
    dsimp [logTarget, target, Hsam] at *
    omega
  have hlogTargetPos (N : ℕ) : 0 < logTarget N := by
    dsimp [logTarget]
    omega
  have hlogTarget : OAI.MicrocellScale.Dominates
      (fun N => Real.log (Xsam N : ℝ)) (fun N => (logTarget N : ℝ)) := by
    exact c_test2_dominates_of_power_bound
      (fun N => by
        have hX : 1 ≤ Xsam N := by
          have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
          have hWpos : 1 ≤ primorial (N + 1) := by
            exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
          have hXfour : 4 ≤ A.X N (C.block i).1 := by
            calc
              4 = 4 * 1 := by norm_num
              _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
              _ ≤ A.X N (C.block i).1 := hraw
          have hXone : 1 ≤ A.X N (C.block i).1 := by omega
          simpa [Xsam] using hXone
        have hXreal : (1 : ℝ) ≤ (Xsam N : ℝ) := by exact_mod_cast hX
        exact Real.log_nonneg hXreal)
      (fun N => by exact_mod_cast hVpos N)
      (fun N => by exact_mod_cast (hlogTargetPos N))
      (R + 4) (by positivity)
      (by
        filter_upwards [hlogTargetBound] with N hN
        exact_mod_cast hN)
      hlogV
  have htargetLeLogTargetSq (N : ℕ) : target N ≤ (logTarget N) ^ 2 := by
    have hlog2 : 2 ≤ logTarget N := by dsimp [logTarget]; omega
    have hmul : 2 * logTarget N ≤ logTarget N * logTarget N :=
      Nat.mul_le_mul_right (logTarget N) hlog2
    have hrel : target N = logTarget N + 1 := by
      dsimp [target, logTarget, Hsam, Ksam]
      omega
    rw [hrel, pow_two]
    exact (by omega : logTarget N + 1 ≤ 2 * logTarget N).trans hmul
  have htargetLeLogTargetSqEventually : ∀ᶠ N in atTop,
      target N ≤ (logTarget N) ^ 2 := Filter.Eventually.of_forall htargetLeLogTargetSq
  have hlogFull : OAI.MicrocellScale.Dominates
      (fun N => Real.log (Xsam N : ℝ)) (fun N => (target N : ℝ)) := by
    exact c_test2_dominates_of_power_bound
      (fun N => by
        have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
        have hWpos : 1 ≤ primorial (N + 1) := by
          exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
        have hXfour : 4 ≤ A.X N (C.block i).1 := by
          calc
            4 = 4 * 1 := by norm_num
            _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
            _ ≤ A.X N (C.block i).1 := hraw
        have hXone : 1 ≤ Xsam N := by dsimp [Xsam]; omega
        have hXreal : (1 : ℝ) ≤ (Xsam N : ℝ) := by exact_mod_cast hXone
        exact Real.log_nonneg hXreal)
      (fun N => by exact_mod_cast hlogTargetPos N)
      (fun N => by exact_mod_cast htargetPos N)
      2 (by norm_num)
      (by
        filter_upwards [htargetLeLogTargetSqEventually] with N hN
        exact_mod_cast hN)
      hlogTarget
  have hDomX : OAI.MicrocellScale.Dominates (fun N => (Xsam N : ℝ))
      (fun N => (target N : ℝ)) :=
    c_test2_natCutoff_dominates_of_log (by
      filter_upwards [] with N
      have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
      have hWpos : 1 ≤ primorial (N + 1) := by
        exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
      have hXfour : 4 ≤ A.X N (C.block i).1 := by
        calc
          4 = 4 * 1 := by norm_num
          _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
          _ ≤ A.X N (C.block i).1 := hraw
      have hXone : 1 ≤ A.X N (C.block i).1 := by omega
      simpa [Xsam] using hXone) hlogFull
  have hXevent : ∀ᶠ N in atTop, 2 ≤ Xsam N := by
    filter_upwards [] with N
    have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
    have hWpos : 1 ≤ primorial (N + 1) := by
      exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
    have hXfour : 4 ≤ A.X N (C.block i).1 := by
      calc
        4 = 4 * 1 := by norm_num
        _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
        _ ≤ A.X N (C.block i).1 := hraw
    have hXtwo : 2 ≤ A.X N (C.block i).1 := by omega
    simpa [Xsam] using hXtwo
  have hden : ∀ᶠ N in atTop,
      Real.log (Xsam N : ℝ) > (primorial (N + 1) : ℝ) / Xsam N := by
    have hlogH := (A.Xdom (C.block i).1) 1 (by norm_num)
    have hgt : ∀ᶠ N in atTop, (A.H N (C.block i).1 : ℝ) <
        Real.log (Xsam N : ℝ) := by
      filter_upwards [hlogH.eventually (eventually_gt_atTop 1)] with N hN
      have hHp : (0 : ℝ) < (A.H N (C.block i).1 : ℝ) := by exact_mod_cast hHpos N
      have hN' : 1 < Real.log (Xsam N : ℝ) / (A.H N (C.block i).1 : ℝ) := by
        simpa [Xsam, Real.rpow_one] using hN
      have hlt : (A.H N (C.block i).1 : ℝ) < Real.log (Xsam N : ℝ) := by
        simpa using (lt_div_iff₀ hHp).mp hN'
      exact hlt
    filter_upwards [hgt, hsize] with N hN hSN
    have hW : primorial (N + 1) ≤ V N := hWleV N
    have hVH : V N ≤ A.H N (C.block i).1 :=
      (Nat.le_add_left _ _).trans hSN
    have hWX : (primorial (N + 1) : ℝ) / (Xsam N : ℝ) ≤
        (A.H N (C.block i).1 : ℝ) := by
      have hXge : (1 : ℝ) ≤ (Xsam N : ℝ) := by
        have hraw := S.gapStage.valid_raw_cutoffs N (C.block i).1
        have hWpos : 1 ≤ primorial (N + 1) := by
          exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
        have hXfour : 4 ≤ A.X N (C.block i).1 := by
          calc
            4 = 4 * 1 := by norm_num
            _ ≤ 4 * primorial (N + 1) := Nat.mul_le_mul_left 4 hWpos
            _ ≤ A.X N (C.block i).1 := hraw
        have hXnat : 1 ≤ Xsam N := by dsimp [Xsam]; omega
        exact_mod_cast hXnat
      have hdiv : (primorial (N + 1) : ℝ) / (Xsam N : ℝ) ≤
          (primorial (N + 1) : ℝ) := by
        exact div_le_self (by positivity) hXge
      exact hdiv.trans (by exact_mod_cast hW.trans hVH)
    exact lt_of_le_of_lt hWX hN
  have hK : ∀ N, 1 ≤ Ksam N := by
    intro N
    dsimp [Ksam]
    exact Nat.one_le_pow R (V N) (hVpos N)
  have hH : ∀ N, 1 ≤ Hsam N := by intro N; simp [Hsam]
  have hV : ∀ N, 1 ≤ V N := hVpos
  have hW : ∀ N, (fun n => primorial (n + 1)) N = primorial (N + 1) := by intro N; rfl
  have hsamp := FromArithmetic.sampling_asymptotics
    (fun N => primorial (N + 1)) Ksam Hsam V Xsam hK hH hV hW hXevent hden
    (by simpa [target, logTarget, Ksam, Hsam] using hDomX)
    (by simpa [logTarget, Ksam] using hlogTarget)
  change SuperPolynomialSmall
    (fun N => FromArithmetic.harmonicResidueUniformError
      (Xsam N) (primorial (N + 1)) (Ksam N)) (fun N => (V N : ℝ))
  exact hsamp.1

theorem c_test2_masterScaleV_tendsto {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (l : Fin n) :
    Tendsto (fun N => (FromArithmetic.masterScaleV A N l : ℝ)) atTop atTop := by
  have hpow : Tendsto (fun N : ℕ => (2 : ℝ) ^ (N + 1)) atTop atTop := by
    have hNplus : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
      apply Filter.tendsto_atTop_mono' atTop
        (by filter_upwards [] with N; exact Nat.le_add_right N 1) tendsto_id
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      hNplus
  have hM : ∀ᶠ N in atTop, (2 : ℝ) ^ (N + 1) ≤ (A.M N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hW : 2 ≤ primorial (N + 1) := by
      calc
        2 = primorial 2 := by norm_num
        _ ≤ primorial (N + 1) := primorial_mono (by omega)
    have hpowNat : 2 ^ (N + 1) ≤ primorial (N + 1) ^ (N + 1) :=
      Nat.pow_le_pow_left hW _
    have hMdiv := A.Mdiv N
    have hMle := Nat.le_of_dvd (A.Mpos N) hMdiv
    exact_mod_cast hpowNat.trans hMle
  have hV : ∀ᶠ N in atTop, (A.M N : ℝ) ≤
      (FromArithmetic.masterScaleV A N l : ℝ) := by
    filter_upwards [] with N
    unfold FromArithmetic.masterScaleV
    exact_mod_cast (by omega : A.M N ≤ 2 + A.M N + ∏ j ∈ Finset.univ.filter (fun j : Fin n => j < l), (A.X N j) ^ 2)
  have hle : (fun N => (2 : ℝ) ^ (N + 1)) ≤ᶠ[atTop]
      (fun N => (FromArithmetic.masterScaleV A N l : ℝ)) := by
    filter_upwards [hM, hV] with N hMN hVN
    exact hMN.trans hVN
  exact Filter.tendsto_atTop_mono' atTop hle hpow

theorem c_test2_superPolynomialSmall_finset_sum {ι : Type*} [Fintype ι]
    (e : ι → ℕ → ℝ) (V : ℕ → ℝ)
    (hsmall : ∀ i, SuperPolynomialSmall (e i) V) :
    SuperPolynomialSmall (fun N => ∑ i, e i N) V := by
  intro C hC
  have hsum : Tendsto (fun N => ∑ i, e i N * V N ^ C) atTop
      (𝓝 (∑ _i : ι, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro i hi
    exact hsmall i C hC
  have hrewrite (N : ℕ) :
      (∑ i, e i N) * V N ^ C = ∑ i, e i N * V N ^ C := by
    rw [Finset.sum_mul]
  have hEq : (fun N => (∑ i, e i N) * V N ^ C) =
      (fun N => ∑ i, e i N * V N ^ C) := funext hrewrite
  rw [hEq]
  simpa using hsum

abbrev CTest2TailIndex {n : ℕ} (T : Finset (Fin n)) := {i : Fin n // i ∈ T}
abbrev CTest2RestIndex {n : ℕ} (T : Finset (Fin n)) := {i : Fin n // i ∉ T}

noncomputable def c_test2_finsetPartitionEquiv {n : ℕ} (T : Finset (Fin n)) :
    Fin n ≃ CTest2TailIndex T ⊕ CTest2RestIndex T := by
  classical
  let code : Fin n → CTest2TailIndex T ⊕ CTest2RestIndex T := fun i =>
    if hi : i ∈ T then Sum.inl ⟨i, hi⟩ else Sum.inr ⟨i, hi⟩
  refine {
    toFun := code
    invFun := fun x => match x with | Sum.inl i => i.1 | Sum.inr i => i.1
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    by_cases hi : i ∈ T <;> simp [code, hi]
  · intro x
    rcases x with i | i
    · simp [code, i.2]
    · simp [code, i.2]

noncomputable def c_test2_divisorTemplateOfTail {n : ℕ} (T : Finset (Fin n)) :
    FromArithmetic.DivisorTemplate n n := by
  classical
  let Tail := CTest2TailIndex T
  let e : Tail ≃ Fin (Fintype.card Tail) := Fintype.equivFin Tail
  have hcard := Fintype.card_le_of_injective (fun i : Tail => i.1) Subtype.val_injective
  have hcard' : Fintype.card Tail ≤ n := by simpa [Tail, Fintype.card_fin] using hcard
  exact ⟨Fintype.card Tail, hcard', fun i => (e.symm i).1⟩

theorem c_test2_parameterTailProductLaw_eq_harmonicProductLaw {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1))) (σ : ℕ) :
    FromArithmetic.parameterTailProductLaw A N T σ =
      harmonicProductLaw (primorial (N + 1))
        (fun i => A.X N ((Fintype.equivFin (CTest2TailIndex T)).symm i).1) σ := by
  classical
  let Tail := CTest2TailIndex T
  let Rest := CTest2RestIndex T
  let part := c_test2_finsetPartitionEquiv T
  let eFun : (Fin n → ℕ) ≃ ((Tail → ℕ) × (Rest → ℕ)) :=
    (Equiv.arrowCongr part (Equiv.refl ℕ)).trans
      (Equiv.sumArrowEquivProdArrow Tail Rest ℕ)
  let W := primorial (N + 1)
  let law : Fin n → ℕ → ℝ := fun j x => harmonicNatLaw (A.X N j) W x
  let tailLaw : Tail → ℕ → ℝ := fun j x => law j.1 x
  let restLaw : Rest → ℕ → ℝ := fun j x => law j.1 x
  let tailSupport : Tail → Finset ℕ := fun j => Finset.range ((A.X N j.1) ^ 2)
  let restSupport : Rest → Finset ℕ := fun j => Finset.range ((A.X N j.1) ^ 2)
  let tailMass : (Tail → ℕ) → ℝ := fun x => ∏ j, tailLaw j (x j)
  let restMass : (Rest → ℕ) → ℝ := fun x => ∏ j, restLaw j (x j)
  let tailTerm : (Tail → ℕ) → ℝ := fun x =>
    (if (∏ j, x j) = σ then 1 else 0) * tailMass x
  let integrand : (Tail → ℕ) × (Rest → ℕ) → ℝ := fun x => tailTerm x.1 * restMass x.2
  let tailDomain : Finset (Tail → ℕ) := Fintype.piFinset tailSupport
  let restDomain : Finset (Rest → ℕ) := Fintype.piFinset restSupport
  let pairDomain : Finset ((Tail → ℕ) × (Rest → ℕ)) := tailDomain.product restDomain
  have hzeroLaw (j : Fin n) (x : ℕ) (hx : x ∉ Finset.range ((A.X N j) ^ 2)) :
      law j x = 0 := by
    simp [law, harmonicNatLaw, Finset.mem_range] at hx ⊢
    omega
  have hzeroTail (x : Tail → ℕ) (hx : x ∉ tailDomain) : tailMass x = 0 := by
    have hnot : ¬ ∀ j : Tail, x j ∈ tailSupport j := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hz := hzeroLaw j.1 (x j) (by simpa [tailSupport] using hj)
    unfold tailMass
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [tailLaw] using hz)
  have hzeroRest (x : Rest → ℕ) (hx : x ∉ restDomain) : restMass x = 0 := by
    have hnot : ¬ ∀ j : Rest, x j ∈ restSupport j := by
      intro hall
      exact hx (Fintype.mem_piFinset.mpr hall)
    obtain ⟨j, hj⟩ := not_forall.mp hnot
    have hz := hzeroLaw j.1 (x j) (by simpa [restSupport] using hj)
    unfold restMass
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simpa [restLaw] using hz)
  have hzeroPair (x : (Tail → ℕ) × (Rest → ℕ)) (hx : x ∉ pairDomain) :
      integrand x = 0 := by
    have hnot : ¬ (x.1 ∈ tailDomain ∧ x.2 ∈ restDomain) := by
      simpa [pairDomain, Finset.mem_product] using hx
    have hnot' : x.1 ∉ tailDomain ∨ x.2 ∉ restDomain := not_and_or.mp hnot
    rcases hnot' with h | h
    · simp [integrand, tailTerm, hzeroTail x.1 h]
    · simp [integrand, tailTerm, hzeroRest x.2 h]
  have hsumRest : ∑' x : Rest → ℕ, restMass x = 1 := by
    apply c_test2_productMass_tsum_one restLaw restSupport
    · intro j x hx
      exact hzeroLaw j.1 x (by simpa [restSupport] using hx)
    · intro j
      exact c_test2_harmonicNatLaw_tsum_one_of_normalizer_pos
        (A.X N j.1) W (A.Xpos N j.1) (hNorm j.1)
  have hsumTail : Summable tailTerm := by
    apply summable_of_ne_finset_zero (s := tailDomain)
    intro x hx
    simp [tailTerm, hzeroTail x hx]
  have hsumRestSummable : Summable restMass := by
    exact summable_of_ne_finset_zero (s := restDomain) (by
      intro x hx
      simp [hzeroRest x hx])
  have hsumPair : Summable integrand := summable_of_ne_finset_zero (s := pairDomain) hzeroPair
  have htailSplit : ∀ x : Tail → ℕ,
      (∑' y : Rest → ℕ, integrand (x, y)) = tailTerm x := by
    intro x
    calc
      _ = ∑' y : Rest → ℕ, tailTerm x * restMass y := by
        apply tsum_congr
        intro y
        rfl
      _ = tailTerm x * ∑' y : Rest → ℕ, restMass y := by
        rw [tsum_mul_left]
      _ = tailTerm x := by simp [hsumRest]
  have htailLawReindex :
      (∑' x : Tail → ℕ, tailTerm x) =
        harmonicProductLaw W
          (fun i => A.X N ((Fintype.equivFin Tail).symm i).1) σ := by
    let eFin : Tail ≃ Fin (Fintype.card Tail) := Fintype.equivFin Tail
    let ePi : (Tail → ℕ) ≃ (Fin (Fintype.card Tail) → ℕ) :=
      Equiv.arrowCongr eFin (Equiv.refl ℕ)
    have hreindex :
        (∑' x : Tail → ℕ, tailTerm x) =
          ∑' y : Fin (Fintype.card Tail) → ℕ, tailTerm (ePi.symm y) :=
      (ePi.symm.tsum_eq (fun x : Tail → ℕ => tailTerm x)).symm
    have hprod (y : Fin (Fintype.card Tail) → ℕ) :
        tailMass (ePi.symm y) =
          ∏ i : Fin (Fintype.card Tail),
            harmonicNatLaw (A.X N (eFin.symm i).1) W (y i) := by
      unfold tailMass tailLaw
      apply Fintype.prod_equiv eFin
      intro j
      simp [law, ePi, Equiv.arrowCongr, eFin]
    have hprodCoord (y : Fin (Fintype.card Tail) → ℕ) :
        (∏ j : Tail, ePi.symm y j) = ∏ i : Fin (Fintype.card Tail), y i := by
      apply Fintype.prod_equiv eFin
      intro j
      simp [ePi, Equiv.arrowCongr]
    have hprodCoord (y : Fin (Fintype.card Tail) → ℕ) :
        (∏ j : Tail, ePi.symm y j) = ∏ i : Fin (Fintype.card Tail), y i := by
      apply Fintype.prod_equiv eFin
      intro j
      simp [ePi, Equiv.arrowCongr]
    unfold harmonicProductLaw
    calc
      _ = ∑' y : Fin (Fintype.card Tail) → ℕ, tailTerm (ePi.symm y) := hreindex
      _ = ∑' y : Fin (Fintype.card Tail) → ℕ,
            (if (∏ i, y i) = σ then (1 : ℝ) else 0) *
              ∏ i, harmonicNatLaw (A.X N (eFin.symm i).1) W (y i) := by
          apply tsum_congr
          intro y
          unfold tailTerm
          rw [hprodCoord y, hprod y]
  have hparamReindex :
      FromArithmetic.parameterTailProductLaw A N T σ = ∑' x, integrand x := by
    unfold FromArithmetic.parameterTailProductLaw
    let term : (Fin n → ℕ) → ℝ := fun t =>
      (if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) * ∏ j, law j (t j)
    have hprodT (t : Fin n → ℕ) :
        (∏ j ∈ T, t j) = ∏ j : Tail, t j.1 := by
      rw [← Finset.prod_subtype (s := T) (h := fun _ => Iff.rfl)]
    have hpartL (j : Tail) : part.symm (Sum.inl j) = j.1 := by
      simp [part, c_test2_finsetPartitionEquiv]
    have hpartR (j : Rest) : part.symm (Sum.inr j) = j.1 := by
      simp [part, c_test2_finsetPartitionEquiv]
    have htailMap (t : Fin n → ℕ) (j : Tail) : (eFun t).1 j = t j.1 := by
      change t (part.symm (Sum.inl j)) = t j.1
      rw [hpartL]
    have hrestMap (t : Fin n → ℕ) (j : Rest) : (eFun t).2 j = t j.1 := by
      change t (part.symm (Sum.inr j)) = t j.1
      rw [hpartR]
    have htailProdMap (t : Fin n → ℕ) :
        (∏ j : Tail, t j.1) = (∏ j : Tail, (eFun t).1 j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [htailMap]
    have hrestProdMap (t : Fin n → ℕ) :
        (∏ j : Rest, t j.1) = (∏ j : Rest, (eFun t).2 j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [hrestMap]
    have hprodLaw (t : Fin n → ℕ) :
        (∏ j : Fin n, law j (t j)) =
          tailMass (eFun t).1 * restMass (eFun t).2 := by
      unfold tailMass restMass tailLaw restLaw
      calc
        _ = ∏ j : Tail ⊕ Rest, law (part.symm j) (t (part.symm j)) := by
          apply Fintype.prod_equiv part
          intro j
          rw [part.symm_apply_apply]
        _ = (∏ j : Tail, law j.1 (t j.1)) *
              ∏ j : Rest, law j.1 (t j.1) := by
          let f : Tail → ℝ := fun j => law j.1 (t j.1)
          let g : Rest → ℝ := fun j => law j.1 (t j.1)
          have heq : (fun j : Tail ⊕ Rest => law (part.symm j) (t (part.symm j))) =
              Sum.elim f g := by
            funext j
            rcases j with j | j
            · simp [f, hpartL]
            · simp [g, hpartR]
          rw [heq]
          simp [Finset.prod_sumElim, f, g]
        _ = _ := by
          congr 1
    have hterm (t : Fin n → ℕ) : term t = integrand (eFun t) := by
      change (if (∏ j ∈ T, t j) = σ then (1 : ℝ) else 0) *
          ∏ j, law j (t j) =
        (if (∏ j : Tail, (eFun t).1 j) = σ then (1 : ℝ) else 0) *
          tailMass (eFun t).1 * restMass (eFun t).2
      rw [hprodT t, htailProdMap t, hprodLaw t]
      simp [integrand, tailTerm]
    change (∑' t : Fin n → ℕ, term t) = ∑' x, integrand x
    calc
      _ = ∑' x : (Tail → ℕ) × (Rest → ℕ), term (eFun.symm x) := by
        simpa [eFun] using (eFun.symm.tsum_eq (fun t : Fin n → ℕ => term t)).symm
      _ = ∑' x : (Tail → ℕ) × (Rest → ℕ), integrand x := by
        apply tsum_congr
        intro x
        simpa only [Equiv.apply_symm_apply] using hterm (eFun.symm x)
  calc
    FromArithmetic.parameterTailProductLaw A N T σ = ∑' x, integrand x := hparamReindex
    _ = ∑' x : Tail → ℕ, tailTerm x := by
      calc
        _ = ∑' x : Tail → ℕ, ∑' y : Rest → ℕ, integrand (x, y) := hsumPair.tsum_prod
        _ = ∑' x : Tail → ℕ, tailTerm x := by
          apply tsum_congr
          intro x
          exact htailSplit x
    _ = harmonicProductLaw W (fun i => A.X N ((Fintype.equivFin Tail).symm i).1) σ := htailLawReindex

theorem c_test2_divisorTemplateLaw_eq_parameterTailProductLaw {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (T : Finset (Fin n))
    (hNorm : ∀ j, 0 < harmonicNormalizer (A.X N j) (primorial (N + 1)))
    (σ : ℕ) :
    FromArithmetic.divisorTemplateLaw A N (c_test2_divisorTemplateOfTail T) σ =
      FromArithmetic.parameterTailProductLaw A N T σ := by
  rw [c_test2_parameterTailProductLaw_eq_harmonicProductLaw A N T hNorm σ]
  rfl

private theorem c_test2_nat_finset_product_dvd {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    {d : ℕ} (hdvd : ∀ i ∈ s, f i ∣ d) : (∏ i ∈ s, f i) ∣ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hcop' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j) := by
        intro i hi j hj hij
        exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hdvd' : ∀ i ∈ s, f i ∣ d := by
        intro i hi
        exact hdvd i (Finset.mem_insert_of_mem hi)
      have hrest : (∏ i ∈ s, f i) ∣ d := ih hcop' hdvd'
      have hcopProd : Nat.Coprime (f a) (∏ i ∈ s, f i) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by intro h; subst i; exact ha hi)
      have hfirst : f a ∣ d := hdvd a (Finset.mem_insert_self a s)
      simpa [Finset.prod_insert, ha] using hcopProd.mul_dvd_of_dvd_of_dvd hfirst hrest

theorem c_test2_totient_prime_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (p i) (p j)) :
    Nat.totient (∏ i ∈ s, p i) = ∏ i ∈ s, (p i - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hcop' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (p i) (p j) := by
        intro i hi j hj hij
        exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hp' : ∀ i ∈ s, (p i).Prime := by
        intro i hi
        exact hp i (Finset.mem_insert_of_mem hi)
      have hcopProd : Nat.Coprime (p a) (∏ i ∈ s, p i) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by intro h; subst i; exact ha hi)
      rw [Finset.prod_insert ha, Nat.totient_mul hcopProd,
        Nat.totient_prime (hp a (Finset.mem_insert_self a s)), ih hp' hcop']
      simp [Finset.prod_insert, ha]

noncomputable def c_test2_finsetCRTEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (modulus : ι → ℕ)
    (hpos : ∀ i ∈ s, 0 < modulus i)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (modulus i) (modulus j)) :
    Fin (∏ i ∈ s, modulus i) ≃ (∀ i : {x // x ∈ s}, Fin (modulus i.1)) := by
  classical
  let Q := ∏ i ∈ s, modulus i
  let solve (r : ∀ i : {x // x ∈ s}, Fin (modulus i.1)) : Fin Q := by
    let residues : ι → ℕ := fun i => if hi : i ∈ s then (r ⟨i, hi⟩).val else 0
    let crt := Nat.chineseRemainderOfFinset residues
      modulus s (by intro i hi; exact (hpos i hi).ne') hcop
    have hlt : crt.val < Q := by
      simpa [Q] using Nat.chineseRemainderOfFinset_lt_prod
        (a := residues) (s := modulus) (fun i hi => (hpos i hi).ne') hcop
    exact ⟨crt.val, hlt⟩
  refine {
    toFun := fun x i => ⟨x.val % modulus i.1, Nat.mod_lt _ (hpos i.1 i.2)⟩
    invFun := solve
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Fin.ext
    dsimp [solve]
    let residues : ι → ℕ := fun i => if hi : i ∈ s then x.val % modulus i else 0
    let crt := Nat.chineseRemainderOfFinset residues modulus s
      (by intro i hi; exact (hpos i hi).ne') hcop
    change crt.val = x.val
    have hcrt : ∀ i ∈ s,
        Nat.ModEq (modulus i) x.val crt.val := by
      intro i hi
      have h := crt.property i hi
      change crt.val % modulus i = residues i % modulus i at h
      simp [residues, hi] at h
      exact h.symm
    have hcrtLt : crt.val < Q := by
      simpa [Q] using Nat.chineseRemainderOfFinset_lt_prod
        (a := residues) (s := modulus) (fun i hi => (hpos i hi).ne') hcop
    by_cases hxy : x.val ≤ crt.val
    · have hd : Q ∣ crt.val - x.val := by
        apply c_test2_nat_finset_product_dvd s modulus hcop
        intro i hi
        exact (hcrt i hi).dvd'
      have hlt : crt.val - x.val < Q := lt_of_le_of_lt (Nat.sub_le _ _) hcrtLt
      have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
      have hcx : crt.val ≤ x.val := (Nat.sub_eq_zero_iff_le.mp hz)
      exact Nat.le_antisymm hcx hxy
    · have hyx : crt.val ≤ x.val := by omega
      have hd : Q ∣ x.val - crt.val := by
        apply c_test2_nat_finset_product_dvd s modulus hcop
        intro i hi
        exact (hcrt i hi).symm.dvd'
      have hlt : x.val - crt.val < Q := lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
      have hz := Nat.eq_zero_of_dvd_of_lt hd hlt
      have hxc : x.val ≤ crt.val := (Nat.sub_eq_zero_iff_le.mp hz)
      exact Nat.le_antisymm hyx hxc
  · intro r
    funext i
    apply Fin.ext
    dsimp [solve]
    let residues : ι → ℕ := fun j => if hj : j ∈ s then (r ⟨j, hj⟩).val else 0
    let crt := Nat.chineseRemainderOfFinset residues
      modulus s (by intro i hi; exact (hpos i hi).ne') hcop
    change crt.val % modulus i.1 = (r i).val
    have h := crt.property i.1 i.2
    change crt.val % modulus i.1 = residues i.1 % modulus i.1 at h
    simpa [residues, i.2, Nat.mod_eq_of_lt (r i).isLt] using h

@[simp] theorem c_test2_finCast_val {n m : ℕ} (h : n = m) (x : Fin n) :
    (Equiv.cast (congrArg Fin h) x).val = x.val := by
  cases h
  rfl

noncomputable def c_test2_crtFactorEquiv (w e V : ℕ) :
    Fin (FromArithmetic.masterCRTModulus w e V) ≃
      Fin ((primorial w) ^ e) × FromArithmetic.CRTResidues w V := by
  classical
  let Range := FromArithmetic.CRTPrimeRange w V
  let Idx := Option Range
  let B := (primorial w) ^ e
  let mod : Idx → ℕ := fun i => i.elim B fun p => p.1
  let eOption : Option Range ≃ Range ⊕ PUnit.{1} :=
    Equiv.optionEquivSumPUnit.{0, 0} Range
  have hmodProd : (∏ i : Idx, mod i) = FromArithmetic.masterCRTModulus w e V := by
    let Pset := (Finset.Ioc w (V + 1)).filter Nat.Prime
    have hsub : (∏ p : Range, p.1) = ∏ p ∈ Pset, p := by
      change (∏ p : {x : ℕ // x ∈ Pset}, p.1) = ∏ p ∈ Pset, p
      exact (Finset.prod_subtype Pset (fun _ => Iff.rfl) fun x : ℕ => x).symm
    have hmodfun (i : Idx) : mod i =
        Sum.elim (fun p : Range => p.1) (fun _ : PUnit.{1} => B) (eOption i) := by
      cases i <;> simp [mod, eOption, Equiv.optionEquivSumPUnit]
    calc
      _ = ∏ p : Range ⊕ PUnit.{1},
            Sum.elim (fun p : Range => p.1) (fun _ : PUnit.{1} => B) p := by
          apply Fintype.prod_equiv eOption
          intro i
          exact hmodfun i
      _ = (∏ p : Range, p.1) * B := by simp [Finset.prod_sumElim]
      _ = B * ∏ p ∈ Pset, p := by rw [hsub]; ring
      _ = FromArithmetic.masterCRTModulus w e V := by
        rfl
  have hpos : ∀ i : Idx, 0 < mod i := by
    intro i
    cases i with
    | none => exact pow_pos (primorial_pos w) e
    | some p => exact (Finset.mem_filter.mp p.2).2.pos
  have hbaseCop (p : Range) : Nat.Coprime B p.1 := by
    have hp : p.1.Prime := (Finset.mem_filter.mp p.2).2
    have hw : w < p.1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.2).1).1
    have hpW : ¬ p.1 ∣ primorial w := by
      intro h
      exact (Nat.not_le_of_gt hw) (hp.dvd_primorial_iff.mp h)
    have hpB : Nat.Coprime p.1 B := hp.coprime_iff_not_dvd.mpr (by
      intro h
      exact hpW (hp.dvd_of_dvd_pow h))
    exact hpB.symm
  have hcop : ∀ i ∈ (Finset.univ : Finset Idx), ∀ j ∈ Finset.univ,
      i ≠ j → Nat.Coprime (mod i) (mod j) := by
    intro i hi j hj hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some p => exact hbaseCop p
    | some p =>
      cases j with
      | none => exact (hbaseCop p).symm
      | some q =>
        have hp : p.1.Prime := (Finset.mem_filter.mp p.2).2
        have hq : q.1.Prime := (Finset.mem_filter.mp q.2).2
        have hpq : p.1 ≠ q.1 := by
          intro heq
          apply hij
          exact congrArg Option.some (Subtype.ext heq)
        apply hp.coprime_iff_not_dvd.mpr
        intro hdiv
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv)
  let e0 := c_test2_finsetCRTEquiv (Finset.univ : Finset Idx) mod
    (by intro i hi; exact hpos i) hcop
  have e1 : Fin (FromArithmetic.masterCRTModulus w e V) ≃
      (∀ i : {x : Idx // x ∈ Finset.univ}, Fin (mod i.1)) := by
    refine {
      toFun := fun a => e0 ⟨a.val, by simpa [hmodProd] using a.isLt⟩
      invFun := fun x => ⟨(e0.symm x).val, by simpa [hmodProd] using (e0.symm x).isLt⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro a
      apply Fin.ext
      simpa using congrArg Fin.val (e0.symm_apply_apply ⟨a.val, by simpa [hmodProd] using a.isLt⟩)
    · intro x
      change e0 ⟨(e0.symm x).val, by simpa [hmodProd] using (e0.symm x).isLt⟩ = x
      calc
        _ = e0 (e0.symm x) := by
          congr 1
        _ = x := e0.apply_symm_apply x
  let e2 : (∀ i : {x : Idx // x ∈ Finset.univ}, Fin (mod i.1)) ≃
      Fin B × FromArithmetic.CRTResidues w V := by
    refine {
      toFun := fun f => (f ⟨none, Finset.mem_univ _⟩, fun p => f ⟨some p, Finset.mem_univ _⟩)
      invFun := fun x i => match i.1 with
        | none => x.1
        | some p => x.2 p
      left_inv := ?_
      right_inv := ?_ }
    · intro f
      funext i
      rcases i with ⟨i, hi⟩
      cases i <;> rfl
    · intro x
      rcases x with ⟨b, r⟩
      apply Prod.ext
      · rfl
      · funext p
        rfl
  exact e1.trans e2

theorem c_test2_masterCRTModulus_factor (w e V : ℕ) :
    FromArithmetic.masterCRTModulus w e V =
      (primorial w) ^ e * ∏ p : FromArithmetic.CRTPrimeRange w V, p.1 := by
  classical
  let Pset := (Finset.Ioc w (V + 1)).filter Nat.Prime
  have hsub : (∏ p : FromArithmetic.CRTPrimeRange w V, p.1) = ∏ p ∈ Pset, p := by
    change (∏ p : {x : ℕ // x ∈ Pset}, p.1) = ∏ p ∈ Pset, p
    exact (Finset.prod_subtype Pset (fun _ => Iff.rfl) fun x : ℕ => x).symm
  unfold FromArithmetic.masterCRTModulus
  rw [hsub.symm]

@[simp] theorem c_test2_crtFactorEquiv_base_apply (w e V : ℕ)
    (a : Fin (FromArithmetic.masterCRTModulus w e V)) :
    ((c_test2_crtFactorEquiv w e V a).1).val = a.val % ((primorial w) ^ e) := by
  simp [c_test2_crtFactorEquiv, c_test2_finsetCRTEquiv, c_test2_finCast_val]

@[simp] theorem c_test2_crtFactorEquiv_prime_apply (w e V : ℕ)
    (a : Fin (FromArithmetic.masterCRTModulus w e V)) (p : FromArithmetic.CRTPrimeRange w V) :
    ((c_test2_crtFactorEquiv w e V a).2 p).val = a.val % p.1 := by
  simp [c_test2_crtFactorEquiv, c_test2_finsetCRTEquiv, c_test2_finCast_val]

theorem c_test2_uniformUnitResidueLaw_sum (Q : ℕ) (hQ : 0 < Q) :
    (∑ a : Fin Q, uniformUnitResidueLaw Q a) = 1 := by
  classical
  let U := Finset.univ.filter (fun a : Fin Q => Nat.Coprime a.val Q)
  have hcard : U.card = Q.totient := by
    have hcard' : U.card = ((Finset.range Q).filter
        (fun n => Nat.Coprime Q n)).card := by
      apply Finset.card_bij (fun (a : Fin Q) _ => a.val)
      · intro a ha
        have ha' := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha'.symm⟩
      · intro a ha b hb hab
        exact Fin.ext hab
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        refine ⟨⟨n, Finset.mem_range.mp hn'.1⟩, ?_, rfl⟩
        simpa [U] using hn'.2.symm
    calc
      U.card = ((Finset.range Q).filter (fun n => Nat.Coprime Q n)).card := hcard'
      _ = Q.totient := (Nat.totient_eq_card_coprime Q).symm
  have hphi : 0 < (Q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hQ
  unfold uniformUnitResidueLaw
  calc
    _ = (U.card : ℝ) * (1 / (Q.totient : ℝ)) := by
      rw [← Finset.sum_filter]
      simp [U, Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by rw [hcard]; field_simp [hphi.ne']

theorem c_test2_uniformUnitCRT_projection (w e V : ℕ)
    (r : FromArithmetic.CRTResidues w V) :
    (∑ a : Fin (FromArithmetic.masterCRTModulus w e V),
      uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V) a *
        if (c_test2_crtFactorEquiv w e V a).2 = r then 1 else 0) =
      ∏ p : FromArithmetic.CRTPrimeRange w V,
        if Nat.Coprime (r p).val p.1 then 1 / ((p.1 - 1 : ℕ) : ℝ) else 0 := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let B := (primorial w) ^ e
  let R := FromArithmetic.CRTPrimeRange w V
  let crt := c_test2_crtFactorEquiv w e V
  have hB : 0 < B := pow_pos (primorial_pos w) e
  have hphiB : 0 < (Nat.totient B : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hB
  have hprime (p : R) : p.1.Prime := (Finset.mem_filter.mp p.2).2
  have hbaseCop (p : R) : Nat.Coprime B p.1 := by
    have hw : w < p.1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp p.2).1).1
    apply ((hprime p).coprime_iff_not_dvd.mpr ?_).symm
    intro hdiv
    have hprimorial : p.1 ≤ w := (hprime p).dvd_primorial_iff.mp
      ((hprime p).dvd_of_dvd_pow hdiv)
    exact (Nat.not_le_of_gt hw) hprimorial
  have hbaseProd : Nat.Coprime B (∏ p : R, p.1) := by
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    exact hbaseCop p
  have hprimePair (p q : R) (hpq : p ≠ q) : Nat.Coprime p.1 q.1 := by
    apply (hprime p).coprime_iff_not_dvd.mpr
    intro hdiv
    have heq : p.1 = q.1 := (Nat.prime_dvd_prime_iff_eq (hprime p) (hprime q)).mp hdiv
    exact hpq (Subtype.ext heq)
  have hphiPrime : Nat.totient (∏ p : R, p.1) = ∏ p : R, (p.1 - 1) := by
    simpa using c_test2_totient_prime_product (Finset.univ : Finset R)
      (fun p => p.1) (by intro p hp; exact hprime p)
      (by intro p hp q hq hpq; exact hprimePair p q hpq)
  have hphiQ : Nat.totient Q = Nat.totient B * ∏ p : R, (p.1 - 1) := by
    dsimp [Q, B]
    rw [c_test2_masterCRTModulus_factor, Nat.totient_mul hbaseProd, hphiPrime]
  have hQfactor : Q = B * ∏ p : R, p.1 := by
    dsimp [Q, B]
    exact c_test2_masterCRTModulus_factor w e V
  have hunit (a : Fin Q) :
      Nat.Coprime a.val Q ↔
        Nat.Coprime (crt a).1.val B ∧ ∀ p : R, Nat.Coprime ((crt a).2 p).val p.1 := by
    have hprod :
        Nat.Coprime a.val (B * ∏ p : R, p.1) ↔
          Nat.Coprime (crt a).1.val B ∧
            ∀ p : R, Nat.Coprime ((crt a).2 p).val p.1 := by
      rw [Nat.coprime_comm, Nat.coprime_mul_iff_left]
      constructor
      · rintro ⟨hbase, hprimes⟩
        refine ⟨?_, ?_⟩
        · have hmod := (ZMod.coprime_mod_iff_coprime a.val B).mpr hbase.symm
          simpa only [crt, c_test2_crtFactorEquiv_base_apply] using hmod
        · have hprimes' : ∀ p : R, Nat.Coprime p.1 a.val :=
            (Nat.coprime_fintype_prod_left_iff).mp hprimes
          intro p
          have hmod := (ZMod.coprime_mod_iff_coprime a.val p.1).mpr (hprimes' p).symm
          simpa only [crt, c_test2_crtFactorEquiv_prime_apply] using hmod
      · rintro ⟨hbase, hprimes⟩
        refine ⟨?_, ?_⟩
        · have hmod := (ZMod.coprime_mod_iff_coprime a.val B).mp hbase
          exact hmod.symm
        · apply (Nat.coprime_fintype_prod_left_iff).mpr
          intro p
          have hmod := (ZMod.coprime_mod_iff_coprime a.val p.1).mp (hprimes p)
          exact hmod.symm
    constructor
    · intro ha
      apply hprod.mp
      simpa [hQfactor] using ha
    · intro ha
      have h := hprod.mpr ha
      simpa [hQfactor] using h
  have hsumBase :
      (∑ b : Fin B, if Nat.Coprime b.val B then 1 / (Nat.totient Q : ℝ) else 0) =
        (Nat.totient B : ℝ) / (Nat.totient Q : ℝ) := by
    calc
      _ = ((Nat.totient B : ℝ) / (Nat.totient Q : ℝ)) *
          ∑ b : Fin B, uniformUnitResidueLaw B b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hb' : Nat.Coprime b.val B
        · simp only [if_pos hb', uniformUnitResidueLaw]
          field_simp [hphiB.ne']
        · simp [hb', uniformUnitResidueLaw]
      _ = (Nat.totient B : ℝ) / (Nat.totient Q : ℝ) := by
        rw [c_test2_uniformUnitResidueLaw_sum B hB]
        ring
  have hunitProj (b : Fin B) :
      uniformUnitResidueLaw Q (crt.symm (b, r)) =
        if Nat.Coprime b.val B ∧ ∀ p : R, Nat.Coprime (r p).val p.1 then
          1 / (Nat.totient Q : ℝ) else 0 := by
    rw [uniformUnitResidueLaw]
    have h := hunit (crt.symm (b, r))
    have heq := congrArg (fun P : Prop => if P then (1 / (Nat.totient Q : ℝ)) else 0)
      (propext h)
    simpa [crt] using heq
  have hsumCRT :
      (∑ a : Fin Q, uniformUnitResidueLaw Q a *
        if (crt a).2 = r then 1 else 0) =
      ∑ b : Fin B, uniformUnitResidueLaw Q (crt.symm (b, r)) := by
    calc
      _ = ∑ x : Fin B × FromArithmetic.CRTResidues w V,
            uniformUnitResidueLaw Q (crt.symm x) * if x.2 = r then 1 else 0 := by
        apply Fintype.sum_equiv crt
        intro a
        simp [crt]
      _ = ∑ b : Fin B, uniformUnitResidueLaw Q (crt.symm (b, r)) := by
        rw [Fintype.sum_prod_type]
        simp
  by_cases hR : ∀ p : R, Nat.Coprime (r p).val p.1
  · have hratio : (Nat.totient B : ℝ) / (Nat.totient Q : ℝ) =
        1 / (∏ p : R, (p.1 - 1 : ℕ) : ℝ) := by
      have hphiQR : (Nat.totient Q : ℝ) =
          (Nat.totient B : ℝ) * ∏ p : R, ((p.1 - 1 : ℕ) : ℝ) := by
        exact_mod_cast hphiQ
      rw [hphiQR]
      have hprodpos : 0 < (∏ p : R, (p.1 - 1 : ℕ) : ℝ) := by
        apply Finset.prod_pos
        intro p hp
        have hp2 : 2 ≤ p.1 := (hprime p).two_le
        exact_mod_cast Nat.sub_pos_of_lt hp2
      have hphiB' : (Nat.totient B : ℝ) ≠ 0 := ne_of_gt hphiB
      field_simp [hphiB', hprodpos.ne']
    calc
      _ = ∑ b : Fin B, uniformUnitResidueLaw Q (crt.symm (b, r)) := hsumCRT
      _ = (Nat.totient B : ℝ) / (Nat.totient Q : ℝ) := by
        have hsum :
            (∑ b : Fin B, uniformUnitResidueLaw Q (crt.symm (b, r))) =
              ∑ b : Fin B, if Nat.Coprime b.val B then
                1 / (Nat.totient Q : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hunitProj]
          by_cases hb' : Nat.Coprime b.val B
          · rw [if_pos ⟨hb', hR⟩, if_pos hb']
          · rw [if_neg (fun hh => hb' hh.1), if_neg hb']
        rw [hsum, hsumBase]
      _ = ∏ p : R, 1 / ((p.1 - 1 : ℕ) : ℝ) := by
        rw [hratio]
        symm
        simpa [one_div] using
          (Finset.prod_inv_distrib (s := Finset.univ)
            (f := fun p : R => ((p.1 - 1 : ℕ) : ℝ)))
      _ = ∏ p : R, if Nat.Coprime (r p).val p.1 then
            1 / ((p.1 - 1 : ℕ) : ℝ) else 0 := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [hR p]
  · have hzero : ∃ p : R, ¬ Nat.Coprime (r p).val p.1 := by
      by_contra h
      apply hR
      intro p
      by_contra hp
      exact h ⟨p, hp⟩
    obtain ⟨p0, hp0⟩ := hzero
    rw [hsumCRT]
    have hnotAll : ¬ ∀ p : R, Nat.Coprime (r p).val p.1 :=
      fun hall => hp0 (hall p0)
    have hleft : (∑ b : Fin B, uniformUnitResidueLaw Q (crt.symm (b, r))) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [hunitProj]
      simp [hnotAll]
    rw [hleft]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ p0)
    simp [hp0]

noncomputable def c_test2_finitePushforwardLaw {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (μ : α → ℝ) (y : β) : ℝ :=
  ∑ x, μ x * if f x = y then 1 else 0

theorem c_test2_finiteL1_pushforward_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (μ ν : α → ℝ) :
    finiteL1 (c_test2_finitePushforwardLaw f μ)
      (c_test2_finitePushforwardLaw f ν) ≤ finiteL1 μ ν := by
  classical
  have hsub (y : β) :
      c_test2_finitePushforwardLaw f μ y -
        c_test2_finitePushforwardLaw f ν y =
      ∑ x, (μ x - ν x) * if f x = y then 1 else 0 := by
    unfold c_test2_finitePushforwardLaw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : f x = y <;> simp [h] <;> ring
  unfold finiteL1
  calc
    _ = ∑ y, |∑ x, (μ x - ν x) * if f x = y then 1 else 0| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← hsub y]
    _ ≤ ∑ y, ∑ x, |(μ x - ν x) * if f x = y then 1 else 0| := by
      apply Finset.sum_le_sum
      intro y hy
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y, |(μ x - ν x) * if f x = y then 1 else 0| := by
      rw [Finset.sum_comm]
    _ = ∑ x, |μ x - ν x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro y hy hne
        simp [show f x ≠ y from fun h => hne h.symm]
      · simp

theorem c_test2_fintype_sum_div_mul {α : Type*} [Fintype α]
    (f g : α → ℝ) (c : ℝ) :
    (∑ x, f x / c * g x) = (∑ x, f x * g x) / c := by
  calc
    _ = ∑ x, (f x * g x) / c := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by
      simpa using
        (Finset.sum_div (Finset.univ : Finset α) (fun x => f x * g x) c).symm

theorem c_test2_crtProjection_of_integer (w e V x : ℕ) :
    (c_test2_crtFactorEquiv w e V
      ⟨x % FromArithmetic.masterCRTModulus w e V,
        Nat.mod_lt _ (by
          rw [c_test2_masterCRTModulus_factor]
          apply Nat.mul_pos
          · exact pow_pos (primorial_pos w) e
          · apply Finset.prod_pos
            intro p hp
            exact (Finset.mem_filter.mp p.2).2.pos)⟩).2 =
      FromArithmetic.integerCRTResidues w V x := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let R := FromArithmetic.CRTPrimeRange w V
  have hQfactor : Q = (primorial w) ^ e * ∏ p : R, p.1 := by
    dsimp [Q]
    exact c_test2_masterCRTModulus_factor w e V
  have hQpos : 0 < Q := by
    rw [hQfactor]
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp p.2).2.pos
  have hdiv (p : R) : p.1 ∣ Q := by
    have hpProd : p.1 ∣ ∏ q : R, q.1 :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    rw [hQfactor]
    rcases hpProd with ⟨k, hk⟩
    refine ⟨(primorial w) ^ e * k, ?_⟩
    calc
      (primorial w) ^ e * ∏ q : R, q.1 =
          (primorial w) ^ e * (p.1 * k) := by rw [hk]
      _ = p.1 * ((primorial w) ^ e * k) := by ring
  have hQlt : x % Q < Q := Nat.mod_lt _ hQpos
  have hres :
      (c_test2_crtFactorEquiv w e V ⟨x % Q, hQlt⟩).2 =
        FromArithmetic.integerCRTResidues w V x := by
    funext p
    apply Fin.ext
    rw [c_test2_crtFactorEquiv_prime_apply, FromArithmetic.integerCRTResidues]
    exact Nat.mod_mod_of_dvd x (hdiv p)
  simpa [Q] using hres

theorem c_test2_primePoolCRT_pushforward (w e V lo hi : ℕ)
    (r : FromArithmetic.CRTResidues w V) :
    c_test2_finitePushforwardLaw
      (fun a : Fin (FromArithmetic.masterCRTModulus w e V) =>
        (c_test2_crtFactorEquiv w e V a).2)
      (primePoolResidueLaw lo hi (FromArithmetic.masterCRTModulus w e V)) r =
      ∑' x : ℕ, primePoolLaw lo hi x *
        if FromArithmetic.integerCRTResidues w V x = r then 1 else 0 := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let R := FromArithmetic.CRTPrimeRange w V
  let crt : Fin Q → FromArithmetic.CRTResidues w V := fun a =>
    (c_test2_crtFactorEquiv w e V a).2
  let pool := (Finset.Ico lo hi).filter Nat.Prime
  have hQpos : 0 < Q := by
    rw [show Q = (primorial w) ^ e * ∏ p : R, p.1 from by
      dsimp [Q]
      exact c_test2_masterCRTModulus_factor w e V]
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp p.2).2.pos
  have hzero (x : ℕ) (hx : x ∉ pool) : primePoolLaw lo hi x = 0 := by
    unfold primePoolLaw
    by_cases h : lo ≤ x ∧ x < hi ∧ x.Prime
    · have hxpool : x ∈ pool := by
        simp [pool, Finset.mem_filter, Finset.mem_Ico, h]
      exact (hx hxpool).elim
    · simp [h]
  have htsum :
      (∑' x : ℕ, primePoolLaw lo hi x *
        if FromArithmetic.integerCRTResidues w V x = r then 1 else 0) =
      ∑ x ∈ pool, primePoolLaw lo hi x *
        if FromArithmetic.integerCRTResidues w V x = r then 1 else 0 := by
    apply tsum_eq_sum (s := pool)
    intro x hx
    rw [hzero x hx]
    simp
  have hsumReindex :
      (∑ a : Fin Q, (∑ x ∈ pool,
          (if x % Q = a.val then 1 / (x : ℝ) else 0)) *
          (if crt a = r then 1 else 0)) =
        ∑ x ∈ pool, (1 / (x : ℝ)) *
          (if FromArithmetic.integerCRTResidues w V x = r then 1 else 0) := by
    calc
      _ = ∑ a : Fin Q, ∑ x ∈ pool,
          (if x % Q = a.val then 1 / (x : ℝ) else 0) *
            (if crt a = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
      _ = ∑ x ∈ pool, ∑ a : Fin Q,
          (if x % Q = a.val then 1 / (x : ℝ) else 0) *
            (if crt a = r then 1 else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ pool, (1 / (x : ℝ)) *
          (if FromArithmetic.integerCRTResidues w V x = r then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        let a₀ : Fin Q := ⟨x % Q, Nat.mod_lt _ hQpos⟩
        have hcrt : crt a₀ = FromArithmetic.integerCRTResidues w V x := by
          simpa [crt, Q] using c_test2_crtProjection_of_integer w e V x
        rw [Finset.sum_eq_single a₀]
        · simp [a₀, hcrt]
        · intro a ha hne
          have hneq : x % Q ≠ a.val := by
            intro h
            apply hne
            exact Fin.ext h.symm
          simp [hneq]
        · simp
  calc
    _ = (∑ a : Fin Q, (∑ x ∈ pool,
          (if x % Q = a.val then 1 / (x : ℝ) else 0)) *
          (if crt a = r then 1 else 0)) / primePoolMass lo hi := by
      simpa [c_test2_finitePushforwardLaw, primePoolResidueLaw, Q, crt, pool] using
        c_test2_fintype_sum_div_mul
          (fun a : Fin Q => ∑ x ∈ pool,
            if x % Q = a.val then 1 / (x : ℝ) else 0)
          (fun a => if crt a = r then 1 else 0) (primePoolMass lo hi)
    _ = (∑ x ∈ pool, (1 / (x : ℝ)) *
          (if FromArithmetic.integerCRTResidues w V x = r then 1 else 0)) /
          primePoolMass lo hi := by rw [hsumReindex]
    _ = ∑ x ∈ pool, ((1 / (x : ℝ)) / primePoolMass lo hi) *
          (if FromArithmetic.integerCRTResidues w V x = r then 1 else 0) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ∑ x ∈ pool, primePoolLaw lo hi x *
          (if FromArithmetic.integerCRTResidues w V x = r then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      simp [primePoolLaw, Finset.mem_Ico.mp hx'.1, hx'.2]
    _ = _ := htsum.symm

theorem c_test2_primePoolResidueLaw_sum (lo hi Q : ℕ)
    (hQ : 0 < Q) (hMass : 0 < primePoolMass lo hi) :
    (∑ a : Fin Q, primePoolResidueLaw lo hi Q a) = 1 := by
  classical
  let pool := (Finset.Ico lo hi).filter Nat.Prime
  have hpartition (x : ℕ) :
      (∑ a : Fin Q, if x % Q = a.val then 1 / (x : ℝ) else 0) =
        1 / (x : ℝ) := by
    let a₀ : Fin Q := ⟨x % Q, Nat.mod_lt _ hQ⟩
    rw [Finset.sum_eq_single a₀]
    · simp [a₀]
    · intro a ha hne
      have hneq : x % Q ≠ a.val := by
        intro h
        apply hne
        exact Fin.ext h.symm
      simp [hneq]
    · simp
  unfold primePoolResidueLaw
  calc
    _ = (∑ a : Fin Q, ∑ x ∈ pool,
          if x % Q = a.val then 1 / (x : ℝ) else 0) / primePoolMass lo hi := by
      rw [← Finset.sum_div]
    _ = (∑ x ∈ pool, ∑ a : Fin Q,
          if x % Q = a.val then 1 / (x : ℝ) else 0) / primePoolMass lo hi := by
      congr 1
      rw [Finset.sum_comm]
    _ = primePoolMass lo hi / primePoolMass lo hi := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      exact hpartition x
    _ = 1 := div_self hMass.ne'

theorem c_test2_primePoolResidueLaw_nonneg (lo hi Q : ℕ) (a : Fin Q)
    (hMass : 0 < primePoolMass lo hi) : 0 ≤ primePoolResidueLaw lo hi Q a := by
  unfold primePoolResidueLaw
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro p hp
    split_ifs <;> positivity
  · exact le_of_lt hMass

theorem c_test2_finitePushforwardLaw_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (μ : α → ℝ) :
    (∑ y, c_test2_finitePushforwardLaw f μ y) = ∑ x, μ x := by
  classical
  unfold c_test2_finitePushforwardLaw
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

theorem c_test2_primeTupleCRTLaw_eq_product {m : ℕ}
    (lo hi : Fin m → ℕ) (w e V : ℕ)
    (r : Fin m → FromArithmetic.CRTResidues w V) :
    FromArithmetic.primeTupleCRTLaw lo hi w V r =
      ∏ i, c_test2_finitePushforwardLaw
        (fun a : Fin (FromArithmetic.masterCRTModulus w e V) =>
          (c_test2_crtFactorEquiv w e V a).2)
        (primePoolResidueLaw (lo i) (hi i)
          (FromArithmetic.masterCRTModulus w e V)) (r i) := by
  classical
  let μ : Fin m → ℕ → ℝ := fun i x => primePoolLaw (lo i) (hi i) x
  let support : Fin m → Finset ℕ := fun i =>
    (Finset.Ico (lo i) (hi i)).filter Nat.Prime
  have hzero : ∀ i x, x ∉ support i → μ i x = 0 := by
    intro i x hx
    unfold μ primePoolLaw
    by_cases h : lo i ≤ x ∧ x < hi i ∧ x.Prime
    · have hx' : x ∈ support i := by
        simp [support, Finset.mem_filter, Finset.mem_Ico, h]
      exact (hx hx').elim
    · simp [h]
  have hprod := c_test2_productPushforwardLaw μ support hzero
    (fun _ x => FromArithmetic.integerCRTResidues w V x) r
  have hactual :
      FromArithmetic.primeTupleCRTLaw lo hi w V r =
        ∏ i, ∑' x : ℕ, primePoolLaw (lo i) (hi i) x *
          if FromArithmetic.integerCRTResidues w V x = r i then 1 else 0 := by
    simpa [FromArithmetic.primeTupleCRTLaw, independentPrimePoolMass, μ] using hprod
  calc
    _ = ∏ i, ∑' x : ℕ, primePoolLaw (lo i) (hi i) x *
          if FromArithmetic.integerCRTResidues w V x = r i then 1 else 0 := hactual
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hmem
      symm
      exact c_test2_primePoolCRT_pushforward w e V (lo i) (hi i) (r i)

theorem c_test2_uniformPrimeTupleCRTLaw_eq_product {m : ℕ}
    (w e V : ℕ) (r : Fin m → FromArithmetic.CRTResidues w V) :
    FromArithmetic.uniformPrimeTupleCRTLaw w V r =
      ∏ i, c_test2_finitePushforwardLaw
        (fun a : Fin (FromArithmetic.masterCRTModulus w e V) =>
          (c_test2_crtFactorEquiv w e V a).2)
        (uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V)) (r i) := by
  classical
  have hslot (i : Fin m) :
      c_test2_finitePushforwardLaw
        (fun a : Fin (FromArithmetic.masterCRTModulus w e V) =>
          (c_test2_crtFactorEquiv w e V a).2)
        (uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V)) (r i) =
        ∏ p : FromArithmetic.CRTPrimeRange w V,
          if Nat.Coprime ((r i) p).val p.1 then
            1 / ((p.1 - 1 : ℕ) : ℝ) else 0 := by
    simpa [c_test2_finitePushforwardLaw] using
      c_test2_uniformUnitCRT_projection w e V (r i)
  unfold FromArithmetic.uniformPrimeTupleCRTLaw
  symm
  apply Finset.prod_congr rfl
  intro i hmem
  exact hslot i

theorem c_test2_primeTupleCRTLaw_finiteL1_bound {m : ℕ}
    (lo hi : Fin m → ℕ) (w e V : ℕ)
    (hMass : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    finiteL1 (FromArithmetic.primeTupleCRTLaw lo hi w V)
      (FromArithmetic.uniformPrimeTupleCRTLaw w V) ≤
        ∑ i, finiteL1
          (primePoolResidueLaw (lo i) (hi i)
            (FromArithmetic.masterCRTModulus w e V))
          (uniformUnitResidueLaw (FromArithmetic.masterCRTModulus w e V)) := by
  classical
  let Q := FromArithmetic.masterCRTModulus w e V
  let crt : Fin Q → FromArithmetic.CRTResidues w V := fun a =>
    (c_test2_crtFactorEquiv w e V a).2
  let μ : Fin m → Fin Q → ℝ := fun i a => primePoolResidueLaw (lo i) (hi i) Q a
  let ν : Fin m → Fin Q → ℝ := fun _ a => uniformUnitResidueLaw Q a
  let pushμ : Fin m → FromArithmetic.CRTResidues w V → ℝ := fun i =>
    c_test2_finitePushforwardLaw crt (μ i)
  let pushν : Fin m → FromArithmetic.CRTResidues w V → ℝ := fun i =>
    c_test2_finitePushforwardLaw crt (ν i)
  have hQpos : 0 < Q := by
    dsimp [Q]
    rw [c_test2_masterCRTModulus_factor]
    apply Nat.mul_pos
    · exact pow_pos (primorial_pos w) e
    · apply Finset.prod_pos
      intro p hp
      exact (Finset.mem_filter.mp p.2).2.pos
  have hμnonneg (i : Fin m) (a : Fin Q) : 0 ≤ μ i a :=
    c_test2_primePoolResidueLaw_nonneg _ _ _ _ (hMass i)
  have hνnonneg (i : Fin m) (a : Fin Q) : 0 ≤ ν i a := by
    by_cases h : Nat.Coprime a.val Q
    · simp [ν, uniformUnitResidueLaw, h]
      positivity
    · simp [ν, uniformUnitResidueLaw, h]
  have hμsum (i : Fin m) : ∑ a : Fin Q, μ i a = 1 := by
    exact c_test2_primePoolResidueLaw_sum _ _ _ (by
      exact hQpos) (hMass i)
  have hνsum (i : Fin m) : ∑ a : Fin Q, ν i a = 1 := by
    exact c_test2_uniformUnitResidueLaw_sum Q hQpos
  have hpushμnonneg (i : Fin m) (r : FromArithmetic.CRTResidues w V) :
      0 ≤ pushμ i r := by
    apply Finset.sum_nonneg
    intro a ha
    by_cases h : crt a = r <;> simp [pushμ, c_test2_finitePushforwardLaw, h, hμnonneg]
  have hpushνnonneg (i : Fin m) (r : FromArithmetic.CRTResidues w V) :
      0 ≤ pushν i r := by
    apply Finset.sum_nonneg
    intro a ha
    by_cases h : crt a = r <;> simp [pushν, c_test2_finitePushforwardLaw, h, hνnonneg]
  have hpushμsum (i : Fin m) :
      ∑ r : FromArithmetic.CRTResidues w V, pushμ i r = 1 := by
    rw [c_test2_finitePushforwardLaw_sum]
    exact hμsum i
  have hpushνsum (i : Fin m) :
      ∑ r : FromArithmetic.CRTResidues w V, pushν i r = 1 := by
    rw [c_test2_finitePushforwardLaw_sum]
    exact hνsum i
  have hpushμabs (i : Fin m) :
      ∑ r : FromArithmetic.CRTResidues w V, |pushμ i r| = 1 := by
    calc
      _ = ∑ r : FromArithmetic.CRTResidues w V, pushμ i r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_of_nonneg (hpushμnonneg i r)]
      _ = 1 := hpushμsum i
  have hpushνabs (i : Fin m) :
      ∑ r : FromArithmetic.CRTResidues w V, |pushν i r| = 1 := by
    calc
      _ = ∑ r : FromArithmetic.CRTResidues w V, pushν i r := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [abs_of_nonneg (hpushνnonneg i r)]
      _ = 1 := hpushνsum i
  have htel := FromArithmetic.finite_product_l1_telescoping pushμ pushν
  have hactualFun :
      FromArithmetic.primeTupleCRTLaw lo hi w V =
        fun r : Fin m → FromArithmetic.CRTResidues w V => ∏ i, pushμ i (r i) := by
    funext r
    simpa [Q, crt, μ, pushμ] using c_test2_primeTupleCRTLaw_eq_product lo hi w e V r
  have huniformFun :
      FromArithmetic.uniformPrimeTupleCRTLaw w V =
        fun r : Fin m → FromArithmetic.CRTResidues w V => ∏ i, pushν i (r i) := by
    funext r
    simpa [Q, crt, ν, pushν] using c_test2_uniformPrimeTupleCRTLaw_eq_product w e V r
  have hfactor :
      finiteL1 (FromArithmetic.primeTupleCRTLaw lo hi w V)
        (FromArithmetic.uniformPrimeTupleCRTLaw w V) =
      finiteL1 (fun r : Fin m → FromArithmetic.CRTResidues w V => ∏ i, pushμ i (r i))
        (fun r => ∏ i, pushν i (r i)) := by
    rw [hactualFun, huniformFun]
  have htel' :
      finiteL1 (fun r : Fin m → FromArithmetic.CRTResidues w V => ∏ i, pushμ i (r i))
        (fun r => ∏ i, pushν i (r i)) ≤ ∑ i, finiteL1 (pushμ i) (pushν i) := by
    simpa [hpushμabs, hpushνabs] using htel
  calc
    _ = finiteL1 (fun r : Fin m → FromArithmetic.CRTResidues w V => ∏ i, pushμ i (r i))
          (fun r => ∏ i, pushν i (r i)) := hfactor
    _ ≤ ∑ i, finiteL1 (pushμ i) (pushν i) := htel'
    _ ≤ ∑ i, finiteL1 (μ i) (ν i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact c_test2_finiteL1_pushforward_le crt (μ i) (ν i)
    _ = _ := by rfl

theorem c_test2_superPolynomialSmall_of_eventually_le
    {e f V : ℕ → ℝ} (he : ∀ N, 0 ≤ e N) (hV : ∀ N, 0 ≤ V N)
    (hle : e ≤ᶠ[atTop] f)
    (hsmall : SuperPolynomialSmall f V) : SuperPolynomialSmall e V := by
  intro C hC
  have hupper := hsmall C hC
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall (fun N => mul_nonneg (he N) (Real.rpow_nonneg (hV N) C))
  · filter_upwards [hle] with N hN
    exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg (hV N) C)

theorem c_test2_poolMass_positive_eventually {K s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper := by
  have hlarge :=
    (S.primeStage.pool_harmonic_mass_dominates l 1 (by norm_num)).eventually_ge_atTop 1
  filter_upwards [hlarge] with N hN
  have hV : 0 < (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    unfold FromArithmetic.masterScaleV
    positivity
  have hratio : 1 ≤
      (primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper : ℝ) /
        (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by
    simpa [Real.rpow_one] using hN
  have hmass := (le_div_iff₀ hV).mp hratio
  have hmass' : (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) ≤
      primePoolMass (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper := by
    simpa using hmass
  exact_mod_cast lt_of_lt_of_le hV hmass'

theorem c_test2_masterCRT_error_superpoly {K s : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) :
    SuperPolynomialSmall
      (fun N => finiteL1
        (FromArithmetic.primeTupleCRTLaw
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper) (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l))
        (FromArithmetic.uniformPrimeTupleCRTLaw (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l)))
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
  classical
  let err : ℕ → ℝ := fun N =>
    finiteL1
      (primePoolResidueLaw (S.primeStage.pool N l).lower
        (S.primeStage.pool N l).upper
        (FromArithmetic.masterCRTModulus (N + 1) (S.primeStage.e0 N)
          (FromArithmetic.masterScaleV S.core.parameters N l)))
      (uniformUnitResidueLaw
        (FromArithmetic.masterCRTModulus (N + 1) (S.primeStage.e0 N)
          (FromArithmetic.masterScaleV S.core.parameters N l)))
  have herr : SuperPolynomialSmall err
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) := by
    simpa [err] using S.primeStage.pool_residue_error l
  have herrSum : SuperPolynomialSmall
      (fun N => ∑ _i : Fin s, err N)
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N l : ℝ)) :=
    c_test2_superPolynomialSmall_finset_sum (fun _ : Fin s => err)
      (fun N => (FromArithmetic.masterScaleV S.core.parameters N l : ℝ))
      (fun _ => herr)
  have hmass := c_test2_poolMass_positive_eventually S l
  have hbound : ∀ᶠ N in atTop,
      finiteL1
        (FromArithmetic.primeTupleCRTLaw
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper) (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l))
        (FromArithmetic.uniformPrimeTupleCRTLaw (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l)) ≤
        ∑ _i : Fin s, err N := by
    filter_upwards [hmass] with N hmassN
    have htuple := c_test2_primeTupleCRTLaw_finiteL1_bound
      (fun _ : Fin s => (S.primeStage.pool N l).lower)
      (fun _ => (S.primeStage.pool N l).upper) (N + 1) (S.primeStage.e0 N)
      (FromArithmetic.masterScaleV S.core.parameters N l)
      (fun _ => hmassN)
    simpa [err] using htuple
  have hnonneg : ∀ N, 0 ≤
      finiteL1
        (FromArithmetic.primeTupleCRTLaw
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper) (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l))
        (FromArithmetic.uniformPrimeTupleCRTLaw (N + 1)
          (FromArithmetic.masterScaleV S.core.parameters N l)) := by
    intro N
    unfold finiteL1
    apply Finset.sum_nonneg
    intro x hx
    exact abs_nonneg _
  have hVnonneg (N : ℕ) :
      0 ≤ (FromArithmetic.masterScaleV S.core.parameters N l : ℝ) := by positivity
  exact c_test2_superPolynomialSmall_of_eventually_le hnonneg hVnonneg hbound herrSum

theorem c_test2_rowCoefficientNatFactors {K s m q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (N : ℕ) (hscale : c_test2_ScaleData S C a N)
    (T : RowTemplate m q) (p : Fin q → ℕ) :
    ∃ alpha rho : Fin m → ℕ,
      (∀ i, chainScale S.core.parameters C a N i /
          chainScale S.core.parameters C a N T.anchor * T.value p i =
            (alpha i : ℚ)) ∧
      (∀ i, i < T.anchor →
        (rho i : ℚ) = chainScale S.core.parameters C a N i /
          chainScale S.core.parameters C a N T.anchor) ∧
      (∀ i, T.anchor ≤ i → rho i = 1) ∧
      (∀ i, alpha i =
        if hi : i < T.anchor then rho i * c_test2_rowValueNat T p i
        else if i = T.anchor then c_test2_rowValueNat T p i else 0) := by
  classical
  rcases Classical.choose_spec hscale with ⟨hc, hcpos, hratio, hmod⟩
  let cint := Classical.choose hscale
  let rho : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then
      Classical.choose (c_test2_scaleRatioNat S N cint hcpos hratio hmod i T.anchor hi)
    else 1
  let alpha : Fin m → ℕ := fun i =>
    if hi : i < T.anchor then rho i * c_test2_rowValueNat T p i
    else if i = T.anchor then c_test2_rowValueNat T p i else 0
  have hrho (i : Fin m) (hi : i < T.anchor) :
      (rho i : ℚ) = chainScale S.core.parameters C a N i /
        chainScale S.core.parameters C a N T.anchor := by
    have hspec := Classical.choose_spec
      (c_test2_scaleRatioNat S N cint hcpos hratio hmod i T.anchor hi)
    have hc' (d : Fin m) :
        (cint d : ℚ) = chainScale S.core.parameters C a N d := by
      simpa [cint, chainScale] using hc d
    calc
      (rho i : ℚ) = (cint i : ℚ) / (cint T.anchor : ℚ) := by
        simpa [rho, hi] using hspec.2.1
      _ = _ := by rw [hc' i, hc' T.anchor]
  have hnone (i : Fin m) (hi : T.anchor < i) : T.entry i = none := by
    by_contra hsome
    obtain ⟨e, he⟩ : ∃ e, T.entry i = some e := by
      cases h : T.entry i with
      | none => exact (hsome h).elim
      | some e => exact ⟨e, rfl⟩
    have hmem : i ∈ T.support := by simpa [RowTemplate.support, he]
    have hle := Finset.le_max' T.support i hmem
    change i ≤ T.anchor at hle
    omega
  refine ⟨alpha, rho, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i < T.anchor
    · simp only [alpha, dif_pos hi, Nat.cast_mul]
      rw [hrho i hi, c_test2_rowValue_eq_cast]
    · by_cases hEq : i = T.anchor
      · subst i
        have hcne : chainScale S.core.parameters C a N T.anchor ≠ 0 := by
          rcases Classical.choose_spec hscale with ⟨hc, hcpos, _, _⟩
          have hc' : (cint T.anchor : ℚ) =
              chainScale S.core.parameters C a N T.anchor := by
            simpa [cint, chainScale] using hc T.anchor
          have hpos : (0 : ℚ) < chainScale S.core.parameters C a N T.anchor := by
            rw [← hc']
            exact_mod_cast hcpos T.anchor
          exact ne_of_gt hpos
        rw [div_self hcne, c_test2_rowValue_eq_cast]
        simp [alpha]
      · have hi' : T.anchor < i := by omega
        have hzero : T.value p i = 0 := by
          simp [RowTemplate.value, hnone i hi']
        simp [alpha, hi, hEq, hzero]
  · exact fun i hi => hrho i hi
  · intro i hi
    have hnot : ¬ i < T.anchor := Nat.not_lt.mpr hi
    simp [rho, hnot]
  · intro i
    by_cases hi : i < T.anchor <;> simp [alpha, rho, hi]

theorem c_test2_harmonicResidueUniformError_mono {X W k K : ℕ}
    (hkK : k ≤ K) (hX : 2 ≤ X) (hlog : Real.log X > (W : ℝ) / X) :
    FromArithmetic.harmonicResidueUniformError X W k ≤
      FromArithmetic.harmonicResidueUniformError X W K := by
  have hden : 0 < (X : ℝ) * (Real.log X - (W : ℝ) / X) := by
    apply mul_pos
    · exact_mod_cast (by omega : 0 < X)
    · exact sub_pos.mpr hlog
  have hnum : (W : ℝ) * (k + 1 : ℕ) ≤ (W : ℝ) * (K + 1 : ℕ) := by
    have hcast : (k + 1 : ℕ) ≤ (K + 1 : ℕ) := Nat.add_le_add_right hkK 1
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcast) (by positivity)
  unfold FromArithmetic.harmonicResidueUniformError FromArithmetic.harmonicResidueError
  exact div_le_div_of_nonneg_right hnum hden.le

def c_test2_rowWeightedGoodDomain {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ι : Fin q ↪ Fin s) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (tests : Finset (IntegerPolynomial q))
    (N : ℕ) (p : Fin s → ℕ) : Prop :=
  c_test2_ScaleData S C a N ∧
    2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower ∧
    ∀ i : Fin q,
      (S.primeStage.pool N C.gap).lower ≤ p (ι i) ∧
      p (ι i) < (S.primeStage.pool N C.gap).upper ∧ (p (ι i)).Prime

def c_test2_rowWeightedCoeff {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ι : Fin q ↪ Fin s) (Sh : RowShape m q r)
    (N : ℕ) (p : Fin s → ℕ) (u : Fin r) (j : Fin m) : ℚ :=
  chainScale S.core.parameters C a N j /
      chainScale S.core.parameters C a N (Sh.row u).anchor *
    (Sh.row u).value (fun i => p (ι i)) j

theorem c_test2_rowWeighted_linearRowValue_eq {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ι : Fin q ↪ Fin s) (Sh : RowShape m q r)
    (N : ℕ) (p : Fin s → ℕ) (u : Fin r) (x : Fin m → ℤ) :
    FromArithmetic.linearRowValue
      (c_test2_rowWeightedCoeff S C a ι Sh) N p u x =
    rowForm (chainScale S.core.parameters C a N) (Sh.row u)
      (fun i => p (ι i)) (fun k => (x k : ℚ)) := by
  unfold FromArithmetic.linearRowValue rowForm c_test2_rowWeightedCoeff
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem c_test2_rowWeighted_primitive {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (ι : Fin q ↪ Fin s) (tests : Finset (IntegerPolynomial q))
    (N : ℕ) (p : Fin s → ℕ)
    (hgood : c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p)
    (r' : ℕ) (hr : r'.Prime) (hlarge : N + 1 < r')
    (hrV : r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap) (u : Fin r) :
    ∃ j, FromArithmetic.rationalResidue r' hr
      (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0 := by
  classical
  have hscale := hgood.1
  have hpool := hgood.2.1
  have hslots := hgood.2.2
  let T := Sh.row u
  let p' : Fin q → ℕ := fun i => p (ι i)
  have hentry : ∃ e, T.entry T.anchor = some e := by
    have hm := Finset.max'_mem T.support T.support_nonempty
    have hs : T.anchor ∈ T.support := by simpa [RowTemplate.anchor] using hm
    exact Option.isSome_iff_exists.mp (by simpa [RowTemplate.support] using hs)
  have hslotAbove (i : Fin q) : r' < p' i := by
    have hlow := (hslots i).1
    have hlow' : (S.primeStage.pool N C.gap).lower ≤ p (ι i) := by
      simpa [p'] using hlow
    have hVone : 1 ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap := by
      unfold FromArithmetic.masterScaleV
      omega
    have hsum : r' + 1 ≤
        FromArithmetic.masterScaleV S.core.parameters N C.gap +
          FromArithmetic.masterScaleV S.core.parameters N C.gap :=
      Nat.add_le_add hrV hVone
    have htwice : r' + 1 ≤
        2 * FromArithmetic.masterScaleV S.core.parameters N C.gap := by
      nlinarith
    have hupper : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
        p (ι i) := hpool.trans hlow'
    exact Nat.lt_of_succ_le (htwice.trans hupper)
  have hprimeCoprime (i : Fin q) : Nat.Coprime (p' i) r' := by
    apply (hr.coprime_iff_not_dvd.mpr ?_).symm
    intro hdiv
    have heq : r' = p' i :=
      (Nat.prime_dvd_prime_iff_eq hr (hslots i).2.2).mp hdiv
    exact (ne_of_gt (hslotAbove i)) heq.symm
  have hmonCoprime :
      Nat.Coprime (c_test2_rowValueNat T p' T.anchor) r' := by
    obtain ⟨e, he⟩ := hentry
    have hprod : Nat.Coprime (∏ i : Fin q, p' i ^ e i) r' := by
      rw [Nat.coprime_fintype_prod_left_iff]
      intro i
      by_cases hei : e i = 0
      · simp [hei]
      · exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hei) (p' i) r').2
          (hprimeCoprime i)
    simpa [c_test2_rowValueNat, he] using hprod
  obtain ⟨alpha, rho, hrep, _, hRhoAnchor, hformula⟩ :=
    c_test2_rowCoefficientNatFactors S C a N hscale T p'
  have hAnchorAlpha : alpha T.anchor = c_test2_rowValueNat T p' T.anchor := by
    simpa using hformula T.anchor
  have hres :
      FromArithmetic.rationalResidue r' hr
        (c_test2_rowWeightedCoeff S C a ι Sh N p u T.anchor) =
          (alpha T.anchor : ZMod r') := by
    rw [c_test2_rowWeightedCoeff, hrep T.anchor, c_test2_rationalResidue_natCast]
  refine ⟨T.anchor, ?_⟩
  rw [hres, hAnchorAlpha]
  intro hz
  have hdiv : r' ∣ c_test2_rowValueNat T p' T.anchor :=
    (ZMod.natCast_eq_zero_iff _ _).mp hz
  exact (hr.coprime_iff_not_dvd.mp hmonCoprime.symm) hdiv

theorem c_test2_rowWeighted_pairwise {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (ι : Fin q ↪ Fin s) (tests : Finset (IntegerPolynomial q))
    (hlisted : TestsListed Dm ι tests) (hdirsTests : dirs.tests ⊆ tests)
    (N : ℕ) (p : Fin s → ℕ)
    (hgood : c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p)
    (r' : ℕ) (hr : r'.Prime) (hlarge : N + 1 < r')
    (hrV : r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap)
    (hnoD : ∀ Q ∈ Dm,
      ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ))))
    (u v : Fin r) (huv : u ≠ v) :
    ∃ i j,
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
        FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
        FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p v i) := by
  classical
  letI : Fact r'.Prime := ⟨hr⟩
  have hscale : c_test2_ScaleData S C a N := hgood.1
  have hslots := hgood.2.2
  let p' : Fin q → ℕ := fun i => p (ι i)
  let T := Sh.row u
  let U := Sh.row v
  have hnonparallel : ¬ T.Parallel U := Sh.nonparallel u v huv
  obtain ⟨i, j, hwitness⟩ := c_test2_nonparallel_minor_witness T U hnonparallel
  let Q : IntegerPolynomial q := T.poly i * U.poly j - T.poly j * U.poly i
  have hminorNe : T.poly i * U.poly j - T.poly j * U.poly i ≠ 0 := by
    rcases hwitness with h | h | h
    · exact h.2.2.2.2
    · exact h.2.2.2
    · exact h.2.2.2
  have hQne : Q ≠ 0 := by simpa [Q] using hminorNe
  have hQmem : Q ∈ templateMinors Sh := by
    unfold templateMinors
    apply Finset.mem_filter.mpr
    refine ⟨?_, hQne⟩
    let z : Fin r × Fin r × Fin m × Fin m := ⟨u, ⟨v, ⟨i, j⟩⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ z, ?_⟩
    rfl
  have hQdirs : Q ∈ dirs.tests := by
    unfold RowDirections.tests
    simp [hQmem]
  have hQtest : Q ∈ tests := hdirsTests hQdirs
  have hQnoDiv : ¬ ((r' : ℤ) ∣
      evalIntegerPolynomial Q (fun i => (p' i : ℤ))) := by
    intro hdiv
    apply hnoD (MvPolynomial.rename ι Q) (hlisted Q hQtest)
    rw [c_test2_evalIntegerPolynomial_rename]
    exact hdiv
  have hQmod :
      (evalIntegerPolynomial Q (fun i => (p' i : ℤ)) : ZMod r') ≠ 0 := by
    intro hz
    apply hQnoDiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hQmod' :
      ((c_test2_rowValueNat T p' i * c_test2_rowValueNat U p' j -
        c_test2_rowValueNat T p' j * c_test2_rowValueNat U p' i : ℤ) : ZMod r') ≠ 0 := by
    simpa [Q, c_test2_rowTemplate_minor_eval] using hQmod
  obtain ⟨alphaT, rhoT, hrepT, hrhoT, hRhoAnchorT, hformT⟩ :=
    c_test2_rowCoefficientNatFactors S C a N hscale T p'
  obtain ⟨alphaU, rhoU, hrepU, hrhoU, hRhoAnchorU, hformU⟩ :=
    c_test2_rowCoefficientNatFactors S C a N hscale U p'
  have hresT (k : Fin m) :
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p u k) =
        (alphaT k : ZMod r') := by
    have hval : c_test2_rowWeightedCoeff S C a ι Sh N p u k =
        (alphaT k : ℚ) := by
      simpa [c_test2_rowWeightedCoeff, p', T] using hrepT k
    rw [hval, c_test2_rationalResidue_natCast]
  have hresU (k : Fin m) :
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p v k) =
        (alphaU k : ZMod r') := by
    have hval : c_test2_rowWeightedCoeff S C a ι Sh N p v k =
        (alphaU k : ℚ) := by
      simpa [c_test2_rowWeightedCoeff, p', U] using hrepU k
    rw [hval, c_test2_rationalResidue_natCast]
  have hmonZeroT (k : Fin m) (hk : k ∉ T.support) :
      c_test2_rowValueNat T p' k = 0 := by
    cases he : T.entry k with
    | none => simp [c_test2_rowValueNat, he]
    | some e =>
        have hmem : k ∈ T.support := by simp [RowTemplate.support, he]
        exact (hk hmem).elim
  have hmonZeroU (k : Fin m) (hk : k ∉ U.support) :
      c_test2_rowValueNat U p' k = 0 := by
    cases he : U.entry k with
    | none => simp [c_test2_rowValueNat, he]
    | some e =>
        have hmem : k ∈ U.support := by simp [RowTemplate.support, he]
        exact (hk hmem).elim
  have hfactorT (k : Fin m) :
      (alphaT k : ZMod r') =
        (rhoT k : ZMod r') * (c_test2_rowValueNat T p' k : ZMod r') := by
    by_cases hlt : k < T.anchor
    · have h := hformT k
      simp only [dif_pos hlt] at h
      rw [h]
      simp
    · by_cases heq : k = T.anchor
      · subst k
        have hρ : rhoT T.anchor = 1 := hRhoAnchorT T.anchor le_rfl
        have hNat : alphaT T.anchor =
            c_test2_rowValueNat T p' T.anchor := by simpa [hρ] using hformT T.anchor
        simpa [hρ] using congrArg (fun n : ℕ => (n : ZMod r')) hNat
      · have hnot : k ∉ T.support := by
          intro hk
          have hle := Finset.le_max' T.support k hk
          change k ≤ T.anchor at hle
          omega
        have h := hformT k
        have hz := hmonZeroT k hnot
        simp [h, hlt, heq, hz]
  have hfactorU (k : Fin m) :
      (alphaU k : ZMod r') =
        (rhoU k : ZMod r') * (c_test2_rowValueNat U p' k : ZMod r') := by
    by_cases hlt : k < U.anchor
    · have h := hformU k
      simp only [dif_pos hlt] at h
      rw [h]
      simp
    · by_cases heq : k = U.anchor
      · subst k
        have hρ : rhoU U.anchor = 1 := hRhoAnchorU U.anchor le_rfl
        have hNat : alphaU U.anchor =
            c_test2_rowValueNat U p' U.anchor := by simpa [hρ] using hformU U.anchor
        simpa [hρ] using congrArg (fun n : ℕ => (n : ZMod r')) hNat
      · have hnot : k ∉ U.support := by
          intro hk
          have hle := Finset.le_max' U.support k hk
          change k ≤ U.anchor at hle
          omega
        have h := hformU k
        have hz := hmonZeroU k hnot
        simp [h, hlt, heq, hz]
  let cint := Classical.choose hscale
  rcases Classical.choose_spec hscale with ⟨hc, hcpos, hratio, hmod⟩
  have hratioCastT (k : Fin m) (hk : k ∈ T.support) :
      (rhoT k : ℚ) =
        chainScale S.core.parameters C a N k /
          chainScale S.core.parameters C a N T.anchor := by
    by_cases hlt : k < T.anchor
    · exact hrhoT k hlt
    · have heq : k = T.anchor := by
        have hle := Finset.le_max' T.support k hk
        change k ≤ T.anchor at hle
        omega
      subst k
      have hcQ : (cint T.anchor : ℚ) =
          chainScale S.core.parameters C a N T.anchor := by
        simpa [cint, chainScale] using hc T.anchor
      have hcne : chainScale S.core.parameters C a N T.anchor ≠ 0 := by
        have hp : (0 : ℚ) < chainScale S.core.parameters C a N T.anchor := by
          rw [← hcQ]
          exact_mod_cast hcpos T.anchor
        exact ne_of_gt hp
      rw [hRhoAnchorT T.anchor le_rfl, div_self hcne]
      norm_num
  have hratioCastU (k : Fin m) (hk : k ∈ U.support) :
      (rhoU k : ℚ) =
        chainScale S.core.parameters C a N k /
          chainScale S.core.parameters C a N U.anchor := by
    by_cases hlt : k < U.anchor
    · exact hrhoU k hlt
    · have heq : k = U.anchor := by
        have hle := Finset.le_max' U.support k hk
        change k ≤ U.anchor at hle
        omega
      subst k
      have hcQ : (cint U.anchor : ℚ) =
          chainScale S.core.parameters C a N U.anchor := by
        simpa [cint, chainScale] using hc U.anchor
      have hcne : chainScale S.core.parameters C a N U.anchor ≠ 0 := by
        have hp : (0 : ℚ) < chainScale S.core.parameters C a N U.anchor := by
          rw [← hcQ]
          exact_mod_cast hcpos U.anchor
        exact ne_of_gt hp
      rw [hRhoAnchorU U.anchor le_rfl, div_self hcne]
      norm_num
  have hrhoNZT (k : Fin m) (hk : k ∈ T.support) :
      (rhoT k : ZMod r') ≠ 0 := by
    by_cases hlt : k < T.anchor
    · have hratioNZ := c_test2_scaleRatio_rationalResidue_ne_zero
        S N cint hcpos hratio hmod k T.anchor hlt r' hr hlarge
      have hcQ (d : Fin m) :
          (cint d : ℚ) = chainScale S.core.parameters C a N d := by
        simpa [cint, chainScale] using hc d
      rw [hcQ k, hcQ T.anchor] at hratioNZ
      have hres : FromArithmetic.rationalResidue r' hr ((rhoT k : ℕ) : ℚ) ≠ 0 := by
        rw [hratioCastT k hk]
        exact hratioNZ
      rw [c_test2_rationalResidue_natCast] at hres
      exact hres
    · have heq : k = T.anchor := by
        have hle := Finset.le_max' T.support k hk
        change k ≤ T.anchor at hle
        omega
      subst k
      rw [hRhoAnchorT T.anchor le_rfl]
      simp
  have hrhoNZU (k : Fin m) (hk : k ∈ U.support) :
      (rhoU k : ZMod r') ≠ 0 := by
    by_cases hlt : k < U.anchor
    · have hratioNZ := c_test2_scaleRatio_rationalResidue_ne_zero
        S N cint hcpos hratio hmod k U.anchor hlt r' hr hlarge
      have hcQ (d : Fin m) :
          (cint d : ℚ) = chainScale S.core.parameters C a N d := by
        simpa [cint, chainScale] using hc d
      rw [hcQ k, hcQ U.anchor] at hratioNZ
      have hres : FromArithmetic.rationalResidue r' hr ((rhoU k : ℕ) : ℚ) ≠ 0 := by
        rw [hratioCastU k hk]
        exact hratioNZ
      rw [c_test2_rationalResidue_natCast] at hres
      exact hres
    · have heq : k = U.anchor := by
        have hle := Finset.le_max' U.support k hk
        change k ≤ U.anchor at hle
        omega
      subst k
      rw [hRhoAnchorU U.anchor le_rfl]
      simp
  have hCross (i j : Fin m) (hiT : i ∈ T.support) (hjT : j ∈ T.support)
      (hiU : i ∈ U.support) (hjU : j ∈ U.support) :
      (rhoT i : ZMod r') * (rhoU j : ZMod r') =
        (rhoT j : ZMod r') * (rhoU i : ZMod r') := by
    have hrat :
        (rhoT i : ℚ) * (rhoU j : ℚ) =
          (rhoT j : ℚ) * (rhoU i : ℚ) := by
      rw [hratioCastT i hiT, hratioCastU j hjU, hratioCastT j hjT, hratioCastU i hiU]
      ring
    have hnat : rhoT i * rhoU j = rhoT j * rhoU i := by exact_mod_cast hrat
    simpa using congrArg (fun z : ℕ => (z : ZMod r')) hnat
  have hdetResidue :
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
        FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p v j) -
      FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
        FromArithmetic.rationalResidue r' hr
          (c_test2_rowWeightedCoeff S C a ι Sh N p v i) =
        (alphaT i : ZMod r') * (alphaU j : ZMod r') -
          (alphaT j : ZMod r') * (alphaU i : ZMod r') := by
    rw [hresT i, hresU j, hresT j, hresU i]
  have hbaseMinor :
      ((c_test2_rowValueNat T p' i * c_test2_rowValueNat U p' j -
        c_test2_rowValueNat T p' j * c_test2_rowValueNat U p' i : ℤ) : ZMod r') ≠ 0 :=
    hQmod'
  have hbaseMinorZ :
      (c_test2_rowValueNat T p' i : ZMod r') *
          (c_test2_rowValueNat U p' j : ZMod r') -
        (c_test2_rowValueNat T p' j : ZMod r') *
          (c_test2_rowValueNat U p' i : ZMod r') ≠ 0 := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] using hbaseMinor
  rcases hwitness with hcommon | hexcl | hexcl
  · rcases hcommon with ⟨hiT, hiU, hjT, hjU, hminor⟩
    have hdetEq :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') -
          (alphaT j : ZMod r') * (alphaU i : ZMod r') =
        (rhoT i : ZMod r') * (rhoU j : ZMod r') *
          ((c_test2_rowValueNat T p' i : ZMod r') *
              (c_test2_rowValueNat U p' j : ZMod r') -
            (c_test2_rowValueNat T p' j : ZMod r') *
              (c_test2_rowValueNat U p' i : ZMod r')) := by
      rw [hfactorT i, hfactorU j, hfactorT j, hfactorU i]
      calc
        _ = (rhoT i : ZMod r') * (rhoU j : ZMod r') *
              (c_test2_rowValueNat T p' i : ZMod r') *
              (c_test2_rowValueNat U p' j : ZMod r') -
            (rhoT j : ZMod r') * (rhoU i : ZMod r') *
              (c_test2_rowValueNat T p' j : ZMod r') *
              (c_test2_rowValueNat U p' i : ZMod r') := by ring
        _ = (rhoT j : ZMod r') * (rhoU i : ZMod r') *
              (c_test2_rowValueNat T p' i : ZMod r') *
              (c_test2_rowValueNat U p' j : ZMod r') -
            (rhoT j : ZMod r') * (rhoU i : ZMod r') *
              (c_test2_rowValueNat T p' j : ZMod r') *
              (c_test2_rowValueNat U p' i : ZMod r') := by
          rw [hCross i j hiT hjT hiU hjU]
        _ = (rhoT j : ZMod r') * (rhoU i : ZMod r') *
              ((c_test2_rowValueNat T p' i : ZMod r') *
                  (c_test2_rowValueNat U p' j : ZMod r') -
                (c_test2_rowValueNat T p' j : ZMod r') *
                  (c_test2_rowValueNat U p' i : ZMod r')) := by ring
        _ = (rhoT i : ZMod r') * (rhoU j : ZMod r') *
              ((c_test2_rowValueNat T p' i : ZMod r') *
                  (c_test2_rowValueNat U p' j : ZMod r') -
                (c_test2_rowValueNat T p' j : ZMod r') *
                  (c_test2_rowValueNat U p' i : ZMod r')) := by
          rw [← hCross i j hiT hjT hiU hjU]
    have hdetNZ :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') ≠
          (alphaT j : ZMod r') * (alphaU i : ZMod r') := by
      apply sub_ne_zero.mp
      rw [hdetEq]
      exact mul_ne_zero (mul_ne_zero (hrhoNZT i hiT) (hrhoNZU j hjU)) hbaseMinorZ
    refine ⟨i, j, ?_⟩
    apply sub_ne_zero.mp
    rw [hdetResidue]
    exact sub_ne_zero.mpr hdetNZ

  · rcases hexcl with ⟨hiT, hiNotU, hjU, hminor⟩
    have hdetEq :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') -
          (alphaT j : ZMod r') * (alphaU i : ZMod r') =
        (rhoT i : ZMod r') * (rhoU j : ZMod r') *
          ((c_test2_rowValueNat T p' i : ZMod r') *
              (c_test2_rowValueNat U p' j : ZMod r')) := by
      rw [hfactorT i, hfactorU j, hfactorT j, hfactorU i,
        hmonZeroU i hiNotU]
      simp
      ring
    have hbase :
        ((c_test2_rowValueNat T p' i * c_test2_rowValueNat U p' j : ℕ) : ZMod r') ≠ 0 := by
      have hzero := hmonZeroU i hiNotU
      simpa [hzero] using hbaseMinor
    have hbaseZ :
        (c_test2_rowValueNat T p' i : ZMod r') *
          (c_test2_rowValueNat U p' j : ZMod r') ≠ 0 := by
      simpa only [Nat.cast_mul] using hbase
    have hdetNZ :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') ≠
          (alphaT j : ZMod r') * (alphaU i : ZMod r') := by
      apply sub_ne_zero.mp
      rw [hdetEq]
      exact mul_ne_zero (mul_ne_zero (hrhoNZT i hiT) (hrhoNZU j hjU)) hbaseZ
    refine ⟨i, j, ?_⟩
    apply sub_ne_zero.mp
    rw [hdetResidue]
    exact sub_ne_zero.mpr hdetNZ
  · rcases hexcl with ⟨hiU, hiNotT, hjT, hminor⟩
    have hdetEq :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') -
          (alphaT j : ZMod r') * (alphaU i : ZMod r') =
        -((rhoT j : ZMod r') * (rhoU i : ZMod r') *
          ((c_test2_rowValueNat T p' j : ZMod r') *
            (c_test2_rowValueNat U p' i : ZMod r'))) := by
      rw [hfactorT i, hfactorU j, hfactorT j, hfactorU i,
        hmonZeroT i hiNotT]
      simp
      ring
    have hbase :
        ((c_test2_rowValueNat T p' j * c_test2_rowValueNat U p' i : ℕ) : ZMod r') ≠ 0 := by
      have hzero := hmonZeroT i hiNotT
      simpa [hzero] using hbaseMinor
    have hbaseZ :
        (c_test2_rowValueNat T p' j : ZMod r') *
          (c_test2_rowValueNat U p' i : ZMod r') ≠ 0 := by
      simpa only [Nat.cast_mul] using hbase
    have hdetNZ :
        (alphaT i : ZMod r') * (alphaU j : ZMod r') ≠
          (alphaT j : ZMod r') * (alphaU i : ZMod r') := by
      apply sub_ne_zero.mp
      rw [hdetEq]
      exact neg_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (hrhoNZT j hjT) (hrhoNZU i hiU)) hbaseZ)
    refine ⟨i, j, ?_⟩
    apply sub_ne_zero.mp
    rw [hdetResidue]
    exact sub_ne_zero.mpr hdetNZ

private def c_test2_constantPrimePoolSupport {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) : Finset (α → ℕ) :=
  Fintype.piFinset (fun _ : α => Finset.Ico lo hi)

private noncomputable def c_test2_constantPrimePoolMass {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (p : α → ℕ) : ℝ :=
  ∏ i, primePoolLaw lo hi (p i)

private noncomputable def c_test2_constantPrimePoolAverage {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (F : (α → ℕ) → ℝ) : ℝ :=
  ∑' p, c_test2_constantPrimePoolMass lo hi p * F p

private lemma c_test2_constantPrimePoolMass_zero {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (p : α → ℕ)
    (hp : p ∉ c_test2_constantPrimePoolSupport lo hi) :
    c_test2_constantPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : α, p i ∈ Finset.Ico lo hi := by
    intro hall
    apply hp
    simpa [c_test2_constantPrimePoolSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold c_test2_constantPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma c_test2_constantPrimePoolMass_tsum_one {α : Type*} [Fintype α]
    [DecidableEq α] (lo hi : ℕ) (hpos : 0 < primePoolMass lo hi) :
    ∑' p : α → ℕ, c_test2_constantPrimePoolMass lo hi p = 1 := by
  let μ : α → ℕ → ℝ := fun _ n => primePoolLaw lo hi n
  let support : α → Finset ℕ := fun _ => Finset.Ico lo hi
  have hzero : ∀ i n, n ∉ support i → μ i n = 0 := by
    intro i n hn
    exact c_test2_primePoolLaw_zero_outside lo hi n (by simpa [support] using hn)
  have hsum : ∀ i, ∑' n : ℕ, μ i n = 1 := by
    intro i
    exact c_test2_primePoolLaw_tsum_one lo hi hpos
  simpa [c_test2_constantPrimePoolMass, μ] using
    c_test2_productMass_tsum_one μ support hzero hsum

theorem c_test2_constantPrimePoolAverage_cylinder {q s : ℕ}
    (ι : Fin q ↪ Fin s) (lo hi : ℕ)
    (hpos : 0 < primePoolMass lo hi)
    (F : (Fin q → ℕ) → ℝ) :
    c_test2_constantPrimePoolAverage lo hi F =
      c_test2_constantPrimePoolAverage lo hi (fun p => F (fun i => p (ι i))) := by
  classical
  let extra := {j : Fin s // j ∉ Set.range ι}
  let eRange : Fin q ≃ {j : Fin s // j ∈ Set.range ι} :=
    { toFun := fun i => ⟨ι i, ⟨i, rfl⟩⟩
      invFun := fun j => Classical.choose j.2
      left_inv := by
        intro i
        apply ι.injective
        exact Classical.choose_spec (show ∃ k, ι k = ι i from ⟨i, rfl⟩)
      right_inv := by
        intro j
        apply Subtype.ext
        exact Classical.choose_spec j.2 }
  let eIndex : Fin q ⊕ extra ≃ Fin s :=
    (Equiv.sumCongr eRange (Equiv.refl extra)).trans
      (Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s)))
  let eTuple : (Fin q → ℕ) × (extra → ℕ) ≃ (Fin s → ℕ) :=
    (Equiv.sumArrowEquivProdArrow (Fin q) extra ℕ).symm.trans
      (Equiv.piCongrLeft (fun _ : Fin s => ℕ) eIndex)
  have heIndexL (i : Fin q) : eIndex (Sum.inl i) = ι i := by
    change Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s))
      (Sum.inl (eRange i)) = ι i
    exact Equiv.Set.sumCompl_apply_inl _ _
  have heIndexR (j : extra) : eIndex (Sum.inr j) = j.1 := by
    change Equiv.Set.sumCompl (Set.range (ι : Fin q → Fin s)) (Sum.inr j) = j.1
    exact Equiv.Set.sumCompl_apply_inr _ _
  have hcoordL (x : Fin q → ℕ) (y : extra → ℕ) (i : Fin q) :
      eTuple (x, y) (ι i) = x i := by
    have hi : eIndex.symm (ι i) = Sum.inl i := by
      apply eIndex.injective
      calc
        eIndex (eIndex.symm (ι i)) = ι i := eIndex.apply_symm_apply _
        _ = eIndex (Sum.inl i) := (heIndexL i).symm
    simp [eTuple, Equiv.piCongrLeft, hi]
  have hcoordR (x : Fin q → ℕ) (y : extra → ℕ) (j : extra) :
      eTuple (x, y) j.1 = y j := by
    have hj : eIndex.symm j.1 = Sum.inr j := by
      apply eIndex.injective
      calc
        eIndex (eIndex.symm j.1) = j.1 := eIndex.apply_symm_apply _
        _ = eIndex (Sum.inr j) := (heIndexR j).symm
    simp [eTuple, Equiv.piCongrLeft, hj]
  have hmass (x : Fin q → ℕ) (y : extra → ℕ) :
      c_test2_constantPrimePoolMass lo hi (eTuple (x, y)) =
        c_test2_constantPrimePoolMass lo hi x *
          c_test2_constantPrimePoolMass lo hi y := by
    unfold c_test2_constantPrimePoolMass
    rw [← Fintype.prod_equiv eIndex
      (fun k : Fin q ⊕ extra => primePoolLaw lo hi (eTuple (x, y) (eIndex k)))
      (fun k : Fin s => primePoolLaw lo hi (eTuple (x, y) k)) (fun _ => rfl)]
    rw [Fintype.prod_sum_type]
    simp_rw [heIndexL, heIndexR, hcoordL, hcoordR]
  have hextraTotal :
      ∑' y : extra → ℕ, c_test2_constantPrimePoolMass lo hi y = 1 :=
    c_test2_constantPrimePoolMass_tsum_one lo hi hpos
  have hFsum : Summable (fun x : Fin q → ℕ =>
      c_test2_constantPrimePoolMass lo hi x * F x) := by
    apply summable_of_ne_finset_zero
      (s := c_test2_constantPrimePoolSupport lo hi)
    intro x hx
    rw [c_test2_constantPrimePoolMass_zero lo hi x hx]
    simp
  have hextraSum : Summable (c_test2_constantPrimePoolMass lo hi :
      (extra → ℕ) → ℝ) := by
    apply summable_of_ne_finset_zero
      (s := c_test2_constantPrimePoolSupport lo hi)
    intro y hy
    exact c_test2_constantPrimePoolMass_zero lo hi y hy
  have hprodSum : Summable (fun z : (Fin q → ℕ) × (extra → ℕ) =>
      c_test2_constantPrimePoolMass lo hi z.1 *
        c_test2_constantPrimePoolMass lo hi z.2 * F z.1) := by
    apply summable_of_ne_finset_zero
      (s := (c_test2_constantPrimePoolSupport lo hi).product
        (c_test2_constantPrimePoolSupport lo hi))
    intro z hz
    have hnot : z.1 ∉ c_test2_constantPrimePoolSupport lo hi ∨
        z.2 ∉ c_test2_constantPrimePoolSupport lo hi := by
      by_contra h
      push_neg at h
      exact hz (Finset.mem_product.mpr h)
    rcases hnot with hx | hy
    · rw [c_test2_constantPrimePoolMass_zero lo hi z.1 hx]
      simp
    · rw [c_test2_constantPrimePoolMass_zero lo hi z.2 hy]
      simp
  have hPair :
      (∑' z : (Fin q → ℕ) × (extra → ℕ),
        c_test2_constantPrimePoolMass lo hi z.1 *
          c_test2_constantPrimePoolMass lo hi z.2 * F z.1) =
        c_test2_constantPrimePoolAverage lo hi F := by
    rw [hprodSum.tsum_prod]
    have hinner (x : Fin q → ℕ) :
        (∑' y : extra → ℕ,
          c_test2_constantPrimePoolMass lo hi x *
            c_test2_constantPrimePoolMass lo hi y * F x) =
          (c_test2_constantPrimePoolMass lo hi x * F x) *
            ∑' y : extra → ℕ, c_test2_constantPrimePoolMass lo hi y := by
      calc
        _ = ∑' y : extra → ℕ,
            (c_test2_constantPrimePoolMass lo hi x * F x) *
              c_test2_constantPrimePoolMass lo hi y := by
                apply tsum_congr
                intro y
                ring
        _ = _ := tsum_mul_left
    rw [show (∑' x : Fin q → ℕ,
          ∑' y : extra → ℕ,
            c_test2_constantPrimePoolMass lo hi x *
              c_test2_constantPrimePoolMass lo hi y * F x) =
        ∑' x : Fin q → ℕ,
          (c_test2_constantPrimePoolMass lo hi x * F x) *
            ∑' y : extra → ℕ, c_test2_constantPrimePoolMass lo hi y by
          apply tsum_congr
          exact hinner]
    rw [hextraTotal]
    simp [c_test2_constantPrimePoolAverage]
  have hFull :
      c_test2_constantPrimePoolAverage lo hi (fun p => F (fun i => p (ι i))) =
        ∑' z : (Fin q → ℕ) × (extra → ℕ),
          c_test2_constantPrimePoolMass lo hi z.1 *
            c_test2_constantPrimePoolMass lo hi z.2 * F z.1 := by
    unfold c_test2_constantPrimePoolAverage
    rw [← eTuple.symm.tsum_eq]
    apply tsum_congr
    intro z
    have hz : eTuple ((eTuple.symm z).1, (eTuple.symm z).2) = z := by
      simpa using eTuple.apply_symm_apply z
    rw [← hz]
    simp only [Equiv.symm_apply_apply]
    rw [hmass]
    simp [hcoordL]
  exact hPair.symm.trans hFull.symm

theorem c_test2_gapSlotAverage_cylinder {K s q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ)
    (ι : Fin q ↪ Fin s)
    (hpos : 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper)
    (F : (Fin q → ℕ) → ℝ) :
    gapSlotAverage S l N F =
    ∑' p : Fin s → ℕ,
        independentPrimePoolMass
          (fun _ : Fin s => (S.primeStage.pool N l).lower)
          (fun _ => (S.primeStage.pool N l).upper) p *
          F (fun i => p (ι i)) := by
  change c_test2_constantPrimePoolAverage
      (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper F =
    c_test2_constantPrimePoolAverage
      (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper
        (fun p => F (fun i => p (ι i)))
  exact c_test2_constantPrimePoolAverage_cylinder ι
    (S.primeStage.pool N l).lower (S.primeStage.pool N l).upper hpos F

theorem c_test2_gapSlotProbability_cylinder {K s q : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (l : Fin K) (N : ℕ)
    (ι : Fin q ↪ Fin s)
    (hpos : 0 < primePoolMass (S.primeStage.pool N l).lower
      (S.primeStage.pool N l).upper)
    (E : (Fin q → ℕ) → Prop) :
    gapSlotProbability S l N E =
    independentPrimePoolProbability
        (fun _ : Fin s => (S.primeStage.pool N l).lower)
        (fun _ => (S.primeStage.pool N l).upper)
        (fun p => E (fun i => p (ι i))) := by
  calc
    gapSlotProbability S l N E =
        gapSlotAverage S l N (fun p => if E p then 1 else 0) := by
          rfl
    _ = ∑' p : Fin s → ℕ,
          independentPrimePoolMass
            (fun _ : Fin s => (S.primeStage.pool N l).lower)
            (fun _ => (S.primeStage.pool N l).upper) p *
            (if E (fun i => p (ι i)) then 1 else 0) :=
      c_test2_gapSlotAverage_cylinder S l N ι hpos
        (fun p => if E p then 1 else 0)
    _ = _ := by
      rfl

theorem c_test2_parameterTailProductLaw_empty {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N σ : ℕ)
    (hNorm : ∀ i, 0 < harmonicNormalizer (A.X N i) (primorial (N + 1))) :
    FromArithmetic.parameterTailProductLaw A N ∅ σ =
      if σ = 1 then 1 else 0 := by
  classical
  let μ : Fin n → ℕ → ℝ := fun i t =>
    harmonicNatLaw (A.X N i) (primorial (N + 1)) t
  let support : Fin n → Finset ℕ := fun i => Finset.Ico (A.X N i) ((A.X N i) ^ 2)
  have hzero : ∀ i t, t ∉ support i → μ i t = 0 := by
    intro i t ht
    by_contra hne
    have hcond : A.X N i ≤ t ∧ t < (A.X N i) ^ 2 ∧
        Nat.Coprime t (primorial (N + 1)) := by
      by_contra h
      have hz : harmonicNatLaw (A.X N i) (primorial (N + 1)) t = 0 := by
        simp [harmonicNatLaw, h]
      exact hne (by simpa [μ] using hz)
    apply ht
    exact Finset.mem_Ico.mpr ⟨hcond.1, hcond.2.1⟩
  have hsum : ∀ i, ∑' t : ℕ, μ i t = 1 := by
    intro i
    exact c_test2_harmonicNatLaw_tsum_one_of_normalizer_pos
      (A.X N i) (primorial (N + 1)) (A.Xpos N i) (hNorm i)
  have hmass : ∑' t : Fin n → ℕ, ∏ i, μ i (t i) = 1 :=
    c_test2_productMass_tsum_one μ support hzero hsum
  unfold FromArithmetic.parameterTailProductLaw
  by_cases hσ : σ = 1
  · subst σ
    simpa [Finset.prod_empty, μ] using hmass
  · have hne : 1 ≠ σ := fun h => hσ h.symm
    simp [Finset.prod_empty, hne, hσ]

theorem c_test2_nuB_parameterTailProductLaw_empty {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hNorm : ∀ i, 0 < harmonicNormalizer (A.X N i) (primorial (N + 1)))
    (y : ℤ) :
    nuB (FromArithmetic.parameterTailProductLaw A N ∅) y = 1 := by
  classical
  unfold nuB
  simp_rw [c_test2_parameterTailProductLaw_empty A N _ hNorm]
  rw [tsum_eq_single 1]
  · simp [Int.one_dvd]
  · intro σ hσ
    simp [hσ, eq_comm]
noncomputable def c_test2_weightedRowData {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) {Sh : RowShape m q r} (dirs : RowDirections Sh)
    (ι : Fin q ↪ Fin s) (tests : Finset (IntegerPolynomial q))
    (included : Finset (Fin r))
    (hlisted : TestsListed Dm ι tests)
    (hPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ j,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0)
    (hPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ i j,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v i)) :
    FromArithmetic.WeightedLinearFormsData (q := r) (d := m) (b := K) S := by
  classical
  let A := S.core.parameters
  let W : ℕ → ℕ := fun N => primorial (N + 1)
  let V : ℕ → ℕ := fun N => FromArithmetic.masterScaleV A N C.gap
  let goodDomain : ℕ → (Fin s → ℕ) → Prop :=
    c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests
  let rowCoeff : ℕ → (Fin s → ℕ) → Fin r → Fin m → ℚ :=
    c_test2_rowWeightedCoeff S C a ι Sh
  let tail : Fin r → Finset (Fin K) :=
    fun u => (C.block (Sh.row u).anchor).2.val
  let selectedTail : Fin r → Finset (Fin K) :=
    fun u => if u ∈ included then tail u else ∅
  let divisor : Fin r → FromArithmetic.DivisorTemplate K K :=
    fun u => c_test2_divisorTemplateOfTail (selectedTail u)
  let epsilonBase : ℕ → ℝ := fun N =>
    ∑ i : Fin m, FromArithmetic.harmonicResidueUniformError
      (A.X N (C.block i).1) (primorial (N + 1)) (V N ^ r)
  let epsilonCRT : ℕ → ℝ := fun N =>
    finiteL1
      (FromArithmetic.primeTupleCRTLaw
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ => (S.primeStage.pool N C.gap).upper) (N + 1) (V N))
      (FromArithmetic.uniformPrimeTupleCRTLaw (N + 1) (V N))
  let baseMass : ℕ → (Fin s → ℕ) → (Fin m → ℤ) → ℝ :=
    fun N _ x => pivotMass A C N x
  have hnorm (N : ℕ) (i : Fin m) :
      0 < harmonicNormalizer (A.X N (C.block i).1) (primorial (N + 1)) :=
    c_test2_harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block i).1)
  have hnormAll (N : ℕ) (i : Fin K) :
      0 < harmonicNormalizer (A.X N i) (primorial (N + 1)) :=
    c_test2_harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N i)
  have hVpos (N : ℕ) : 1 ≤ V N := by
    dsimp [V, FromArithmetic.masterScaleV]
    omega
  have htailLaw (N : ℕ) (u : Fin r) (σ : ℕ) :
      FromArithmetic.divisorTemplateLaw A N (divisor u) σ =
        FromArithmetic.parameterTailProductLaw A N (selectedTail u) σ := by
    simpa [divisor, selectedTail] using
      c_test2_divisorTemplateLaw_eq_parameterTailProductLaw A N (selectedTail u)
        (fun i => hnormAll N i) σ
  refine
    { gap := fun _ => C.gap
      rowCoeff := rowCoeff
      divisor := divisor
      V := V
      epsilonBase := epsilonBase
      epsilonCRT := epsilonCRT
      baseMass := baseMass
      goodDomain := goodDomain
      epsilonBase_nonnegative := ?_
      V_lower := ?_
      V_tendsto := ?_
      slot_gap_bound := ?_
      base_nonnegative := ?_
      base_normalized := ?_
      divisor_positive := ?_
      divisor_bounded := ?_
      base_residue_uniform := ?_
      row_integer_on_support := ?_
      row_denominators_are_units := ?_
      row_primitive := ?_
      pairwise_row_tests := ?_
      crt_error_bound := ?_
      epsilonBase_superpolynomial := ?_
      epsilonCRT_superpolynomial := ?_ }
  · intro N
    unfold epsilonBase
    apply Finset.sum_nonneg
    intro i hi
    unfold FromArithmetic.harmonicResidueUniformError FromArithmetic.harmonicResidueError
    apply div_nonneg
    · positivity
    · apply mul_nonneg
      · positivity
      · have hlog := c_test2_samplingDenominator_of_cutoff
          (primorial_pos (N + 1))
          (S.gapStage.valid_raw_cutoffs N (C.block i).1)
        exact le_of_lt (sub_pos.mpr hlog)
  · intro N
    change A.M N ≤ FromArithmetic.masterScaleV A N C.gap
    unfold FromArithmetic.masterScaleV
    omega
  · apply Filter.tendsto_atTop.2
    intro b
    have hV := (Filter.tendsto_atTop.1 (c_test2_masterScaleV_tendsto A C.gap)) (b : ℝ)
    filter_upwards [hV] with N hN
    exact_mod_cast hN
  · intro N i
    rfl
  · intro N p x
    unfold baseMass pivotMass
    apply Finset.prod_nonneg
    intro i hi
    exact c_test2_harmonicLaw_nonneg_of_normalizer_pos (hnorm N i) (x i)
  · intro N p
    unfold baseMass pivotMass
    exact c_test2_harmonicProductMass_tsum_one
      (fun i : Fin m => A.X N (C.block i).1) (primorial (N + 1))
      (fun i => A.Xpos N (C.block i).1) (fun i => hnorm N i)
  · intro N u σ hσ
    have htailNZ : FromArithmetic.parameterTailProductLaw A N (selectedTail u) σ ≠ 0 := by
      intro hz
      apply hσ
      rw [htailLaw N u σ, hz]
    exact c_test2_parameterTailProductLaw_pos_of_nonzero A N (selectedTail u) σ htailNZ
  · intro N u σ hσ
    have htailNZ : FromArithmetic.parameterTailProductLaw A N (selectedTail u) σ ≠ 0 := by
      intro hz
      apply hσ
      rw [htailLaw N u σ, hz]
    by_cases hu : u ∈ included
    · simpa [selectedTail, hu, tail] using
        c_test2_chainTail_support_le_masterScaleV A N C (Sh.row u).anchor σ
          (by simpa [selectedTail, hu] using htailNZ)
    · have hle := c_test2_parameterTailProductLaw_support_le A N ∅ σ
        (by simpa [selectedTail, hu] using htailNZ)
      have hleOne : σ ≤ 1 := by simpa using hle
      exact hleOne.trans (hVpos N)
  · intro N p σ hgood hdivNZ hσ
    let Kprod : ℕ := ∏ u : Fin r, σ u
    have hK : 0 < Kprod := by
      dsimp [Kprod]
      exact Finset.prod_pos fun u _ => hσ u
    have htailNZ (u : Fin r) :
        FromArithmetic.parameterTailProductLaw A N (selectedTail u) (σ u) ≠ 0 := by
      intro hz
      have heq := htailLaw N u (σ u)
      apply hdivNZ u
      rw [heq, hz]
    have hKcop : Nat.Coprime Kprod (primorial (N + 1)) := by
      dsimp [Kprod]
      rw [Nat.coprime_fintype_prod_left_iff]
      intro u
      exact c_test2_parameterTailProductLaw_coprime_of_nonzero A N
        (selectedTail u) (σ u) (htailNZ u)
    have hσle (u : Fin r) : σ u ≤ V N := by
      by_cases hu : u ∈ included
      · simpa [selectedTail, hu, tail] using
          c_test2_chainTail_support_le_masterScaleV A N C (Sh.row u).anchor
            (σ u) (by simpa [selectedTail, hu] using htailNZ u)
      · have hle := c_test2_parameterTailProductLaw_support_le A N ∅ (σ u)
          (by simpa [selectedTail, hu] using htailNZ u)
        have hleOne : σ u ≤ 1 := by simpa using hle
        exact hleOne.trans (hVpos N)
    have hKbound : Kprod ≤ V N ^ r := by
      calc
        _ ≤ ∏ _u : Fin r, V N := by
          apply Finset.prod_le_prod
          · intro u hu
            exact hσle u
        _ = V N ^ r := by simp
    have hErr (i : Fin m) :
        finiteL1
          (harmonicResidueLaw
            (harmonicLaw (A.X N (C.block i).1) (primorial (N + 1))) Kprod)
          (uniformResidueLaw Kprod) ≤
          FromArithmetic.harmonicResidueUniformError
            (A.X N (C.block i).1) (primorial (N + 1)) (V N ^ r) := by
      have hcut := S.gapStage.valid_raw_cutoffs N (C.block i).1
      have hX : 2 ≤ A.X N (C.block i).1 := by
        have hW : 1 ≤ primorial (N + 1) :=
          Nat.one_le_iff_ne_zero.mpr (ne_of_gt (primorial_pos (N + 1)))
        have hX4 : 4 ≤ A.X N (C.block i).1 := by
          calc
            4 = 4 * 1 := by norm_num
            _ ≤ 4 * primorial (N + 1) :=
              Nat.mul_le_mul_left 4 hW
            _ ≤ A.X N (C.block i).1 :=
              S.gapStage.valid_raw_cutoffs N (C.block i).1
        omega
      have hlog := c_test2_samplingDenominator_of_cutoff
        (primorial_pos (N + 1)) hcut
      have hsamp := FromArithmetic.sampling_pointwise_claim
        (A.X N (C.block i).1) (primorial (N + 1))
        (primorial_pos (N + 1)) hX hlog
      have htotal := hsamp.residue_total_mass hX hlog Kprod hKcop hK
      exact htotal.trans
        (c_test2_harmonicResidueUniformError_mono hKbound hX hlog)
    exact c_test2_pivotBaseResidueLaw_finiteL1_bound A C N
      hK (fun i => hnorm N i)
      (fun i => FromArithmetic.harmonicResidueUniformError
        (A.X N (C.block i).1) (primorial (N + 1)) (V N ^ r)) hErr
  · intro N p x hgood hNZ u
    have hscale : c_test2_ScaleData S C a N := hgood.1
    obtain ⟨alpha, rho, hrep, _, _, _⟩ := c_test2_rowCoefficientNatFactors
      S C a N hscale (Sh.row u) (fun i => p (ι i))
    have hcoeff : ∀ j, rowCoeff N p u j = (alpha j : ℚ) := by
      intro j
      simpa [rowCoeff, c_test2_rowWeightedCoeff] using hrep j
    change (FromArithmetic.linearRowValue rowCoeff N p u x).den = 1
    rw [show FromArithmetic.linearRowValue rowCoeff N p u x =
        ((∑ j, (alpha j : ℤ) * x j : ℤ) : ℚ) by
          unfold FromArithmetic.linearRowValue
          simp_rw [hcoeff]
          norm_cast]
    simp only [Rat.den_intCast]
  · intro N p hgood r' hr hlarge hrV u j
    have hscale : c_test2_ScaleData S C a N := hgood.1
    obtain ⟨alpha, rho, hrep, _, _, _⟩ := c_test2_rowCoefficientNatFactors
      S C a N hscale (Sh.row u) (fun i => p (ι i))
    have hcoeff : rowCoeff N p u j = (alpha j : ℚ) := by
      simpa [rowCoeff, c_test2_rowWeightedCoeff] using hrep j
    rw [hcoeff]
    simp
  · exact hPrimitive
  · exact hPairwise
  · intro N
    rfl
  · have hsmall :
        SuperPolynomialSmall
          (fun N => ∑ i : Fin m,
            FromArithmetic.harmonicResidueUniformError
              (A.X N (C.block i).1) (primorial (N + 1))
              (FromArithmetic.masterScaleV A N C.gap ^ r))
          (fun N => (FromArithmetic.masterScaleV A N C.gap : ℝ)) :=
      c_test2_superPolynomialSmall_finset_sum
        (fun i N => FromArithmetic.harmonicResidueUniformError
          (A.X N (C.block i).1) (primorial (N + 1))
          (FromArithmetic.masterScaleV A N C.gap ^ r))
        (fun N => (FromArithmetic.masterScaleV A N C.gap : ℝ))
        (fun i => c_test2_samplingResidueError_superpoly S C i r)
    simpa [epsilonBase, V] using hsmall
  · simpa [epsilonCRT, V] using c_test2_masterCRT_error_superpoly S C.gap

noncomputable def c_test2_subsetRowEventAverage {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (I : Finset (Fin r))
    (N : ℕ) (E : (Fin q → ℕ) → Prop) : ℝ :=
  gapSlotAverage S C.gap N fun p => if E p then
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          (fun k => (z k : ℚ))) else 0

theorem c_test2_weightedSubsetEventIdentity {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (ι : Fin q ↪ Fin s) (tests : Finset (IntegerPolynomial q))
    (included : Finset (Fin r))
    (hlisted : TestsListed Dm ι tests)
    (hPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ j,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0)
    (hPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ i j,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v i))
    (N : ℕ) (hScale : c_test2_ScaleData S C a N)
    (hPool : 2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
      (S.primeStage.pool N C.gap).lower)
    (hMass : 0 < primePoolMass
      (S.primeStage.pool N C.gap).lower (S.primeStage.pool N C.gap).upper)
    (E : (Fin q → ℕ) → Prop) :
    FromArithmetic.weightedLinearFormsAverage
      (c_test2_weightedRowData (Sh := Sh) S C a dirs ι tests included hlisted
          hPrimitive hPairwise)
        N
        (fun p => c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p ∧
          E (fun i => p (ι i))) =
      c_test2_subsetRowEventAverage S C a Sh included N E := by
  classical
  let D := c_test2_weightedRowData (Sh := Sh) S C a dirs ι tests included hlisted
    hPrimitive hPairwise
  let tail : Fin r → Finset (Fin K) :=
    fun R => (C.block (Sh.row R).anchor).2.val
  let inner (p : Fin q → ℕ) : ℝ :=
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      ∏ R ∈ included, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          (fun k => (z k : ℚ)))
  let innerFull (p : Fin s → ℕ) : ℝ :=
    ∑' z : Fin m → ℤ, D.baseMass N p z *
      ∏ R, nuB
        (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
        (FromArithmetic.linearRowValue D.rowCoeff N p R z).num
  have hnormAll (i : Fin K) :
      0 < harmonicNormalizer (S.core.parameters.X N i) (primorial (N + 1)) :=
    c_test2_harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N i)
  have hDivisor (R : Fin r) :
      D.divisor R =
        c_test2_divisorTemplateOfTail (if R ∈ included then tail R else ∅) := by
    rfl
  have hdivLaw (R : Fin r) :
      FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R) =
        fun σ => if R ∈ included then
          FromArithmetic.parameterTailProductLaw S.core.parameters N (tail R) σ
        else FromArithmetic.parameterTailProductLaw S.core.parameters N ∅ σ := by
    funext σ
    by_cases hR : R ∈ included
    · simpa [hDivisor R, hR] using
        c_test2_divisorTemplateLaw_eq_parameterTailProductLaw
          S.core.parameters N (tail R) hnormAll σ
    · simpa [hDivisor R, hR] using
        c_test2_divisorTemplateLaw_eq_parameterTailProductLaw
          S.core.parameters N ∅ hnormAll σ
  have hrow (p : Fin s → ℕ) (R : Fin r) (z : Fin m → ℤ) :
      FromArithmetic.linearRowValue D.rowCoeff N p R z =
        rowForm (chainScale S.core.parameters C a N) (Sh.row R)
          (fun i => p (ι i)) (fun k => (z k : ℚ)) := by
    simpa [D, c_test2_weightedRowData] using
      c_test2_rowWeighted_linearRowValue_eq S C a ι Sh N p R z
  let Efull : (Fin s → ℕ) → Prop := fun p =>
    D.goodDomain N p ∧ E (fun i => p (ι i))
  have hweight (p : Fin s → ℕ) (z : Fin m → ℤ)
      (hgood : D.goodDomain N p) (hz : D.baseMass N p z ≠ 0) (R : Fin r) :
      nuB (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
          (FromArithmetic.linearRowValue D.rowCoeff N p R z).num =
        if R ∈ included then
          atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ)))
        else 1 := by
    have hden : (FromArithmetic.linearRowValue D.rowCoeff N p R z).den = 1 :=
      D.row_integer_on_support N p z hgood hz R
    have hrowDen :
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
          (fun i => p (ι i)) (fun k => (z k : ℚ))).den = 1 := by
      rw [← hrow p R z]
      exact hden
    have hnum :
        ((FromArithmetic.linearRowValue D.rowCoeff N p R z).num : ℚ) =
          rowForm (chainScale S.core.parameters C a N) (Sh.row R)
            (fun i => p (ι i)) (fun k => (z k : ℚ)) := by
      calc
        _ = FromArithmetic.linearRowValue D.rowCoeff N p R z :=
          Rat.coe_int_num_of_den_eq_one hden
        _ = _ := hrow p R z
    by_cases hR : R ∈ included
    · rw [hdivLaw R]
      simp only [if_pos hR]
      have hnumCast :
          ((FromArithmetic.linearRowValue D.rowCoeff N p R z).num : ℚ) =
            ((rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num : ℚ) := by
        calc
          ((FromArithmetic.linearRowValue D.rowCoeff N p R z).num : ℚ) =
              FromArithmetic.linearRowValue D.rowCoeff N p R z :=
            Rat.coe_int_num_of_den_eq_one hden
          _ = rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ)) := hrow p R z
          _ = ((rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num : ℚ) :=
            (Rat.coe_int_num_of_den_eq_one hrowDen).symm
      have hnumEq :
          (FromArithmetic.linearRowValue D.rowCoeff N p R z).num =
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
              (fun i => p (ι i)) (fun k => (z k : ℚ))).num := by
        exact_mod_cast hnumCast
      rw [hnumEq]
      have htail : tail R = (C.block (Sh.row R).anchor).2.val := rfl
      rw [htail, chainWeight]
      simp [atQ, hrowDen]
    · rw [hdivLaw R]
      simp only [if_neg hR]
      rw [c_test2_nuB_parameterTailProductLaw_empty
        S.core.parameters N hnormAll (FromArithmetic.linearRowValue D.rowCoeff N p R z).num]
  have hinnerFull (p : Fin s → ℕ) (hgood : D.goodDomain N p) :
      innerFull p = inner (fun i => p (ι i)) := by
    unfold innerFull inner
    apply tsum_congr
    intro z
    have hbase : D.baseMass N p z = pivotMass S.core.parameters C N z := by rfl
    by_cases hz : pivotMass S.core.parameters C N z = 0
    · simp [hbase, hz]
    · rw [hbase]
      simp_rw [hweight p z hgood (by simpa [hbase] using hz)]
      simp
  have houter :
      FromArithmetic.weightedLinearFormsAverage D N Efull =
        ∑' p : Fin s → ℕ,
          independentPrimePoolMass
            (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
            (fun _ => (S.primeStage.pool N C.gap).upper) p *
          (if E (fun i => p (ι i)) then inner (fun i => p (ι i)) else 0) := by
    unfold FromArithmetic.weightedLinearFormsAverage Efull
    apply tsum_congr
    intro p
    have hmassEq :
        independentPrimePoolMass
          (fun i => (S.primeStage.pool N (D.gap i)).lower)
          (fun i => (S.primeStage.pool N (D.gap i)).upper) p =
        independentPrimePoolMass
          (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
          (fun _ => (S.primeStage.pool N C.gap).upper) p := by
      rfl
    rw [hmassEq]
    let mass := independentPrimePoolMass
      (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
      (fun _ => (S.primeStage.pool N C.gap).upper) p
    by_cases hmass : mass = 0
    · simp [mass, hmass]
    · have hslots (i : Fin s) :
        (S.primeStage.pool N C.gap).lower ≤ p i ∧
          p i < (S.primeStage.pool N C.gap).upper ∧ (p i).Prime := by
        have hfactor : primePoolLaw (S.primeStage.pool N C.gap).lower
            (S.primeStage.pool N C.gap).upper (p i) ≠ 0 := by
          apply (Finset.prod_ne_zero_iff.mp ?_) i (Finset.mem_univ i)
          simpa [mass, independentPrimePoolMass] using hmass
        unfold primePoolLaw at hfactor
        split_ifs at hfactor with hh
        · exact hh
        · simp at hfactor
      have hgood : D.goodDomain N p := by
        change c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p
        exact ⟨hScale, hPool, fun i => hslots (ι i)⟩
      by_cases hE : E (fun i => p (ι i))
      · rw [if_pos (show D.goodDomain N p ∧ E (fun i => p (ι i)) from ⟨hgood, hE⟩),
          if_pos hE]
        have hinnerFull' :
            (∑' z : Fin m → ℤ, D.baseMass N p z *
              ∏ R, nuB
                (FromArithmetic.divisorTemplateLaw S.core.parameters N (D.divisor R))
                (FromArithmetic.linearRowValue D.rowCoeff N p R z).num) =
              inner (fun i => p (ι i)) := by
          simpa only [innerFull] using hinnerFull p hgood
        rw [hinnerFull']
        simp
      ·
        have hnot : ¬ (D.goodDomain N p ∧ E (fun i => p (ι i))) :=
          fun h => hE h.2
        rw [if_neg hnot, if_neg hE]
        simp
  calc
    _ = FromArithmetic.weightedLinearFormsAverage D N Efull := rfl
    _ = ∑' p : Fin s → ℕ,
          independentPrimePoolMass
            (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
            (fun _ => (S.primeStage.pool N C.gap).upper) p *
          (if E (fun i => p (ι i)) then inner (fun i => p (ι i)) else 0) := houter
    _ = c_test2_subsetRowEventAverage S C a Sh included N E := by
      symm
      simpa [c_test2_subsetRowEventAverage, inner] using
        c_test2_gapSlotAverage_cylinder S C.gap N ι hMass
          (fun p => if E p then inner p else 0)

theorem c_test2_weightedLinearFormsError_tendsto_zero
    {K q d b m : ℕ} {Aset : Finset ℚ} {tests : Finset (IntegerPolynomial m)}
    {S : FromArithmetic.MasterScales K Aset m tests}
    (D : FromArithmetic.WeightedLinearFormsData (q := q) (d := d) (b := b) S) :
    Tendsto (fun N : ℕ => 1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ q *
      (D.epsilonBase N + D.epsilonCRT N)) atTop (𝓝 0) := by
  have hVreal : Tendsto (fun N : ℕ => (D.V N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp D.V_tendsto
  have hinvV : Tendsto (fun N : ℕ => (D.V N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hVreal
  have hVpos : ∀ᶠ N : ℕ in atTop, 0 < (D.V N : ℝ) :=
    hVreal.eventually (eventually_gt_atTop 0)
  have hweighted (e : ℕ → ℝ)
      (he : SuperPolynomialSmall e (fun N => (D.V N : ℝ))) :
      Tendsto (fun N => (D.V N : ℝ) ^ q * e N) atTop (𝓝 0) := by
    have hs := he ((q : ℝ) + 1) (by positivity)
    have hpow (N : ℕ) : (D.V N : ℝ) ^ ((q : ℝ) + 1) =
        (D.V N : ℝ) ^ q * (D.V N : ℝ) := by
      have hexp : (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) := by norm_num
      rw [hexp, Real.rpow_natCast]
      simp [pow_succ]
    have hbase : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ))) atTop (𝓝 0) := by
      exact hs.congr fun N => by rw [hpow]
    have heq : (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) *
        (D.V N : ℝ)⁻¹) =ᶠ[atTop]
        (fun N => (D.V N : ℝ) ^ q * e N) := by
      filter_upwards [hVpos] with N hN
      field_simp [ne_of_gt hN]
    have hprod : Tendsto
        (fun N => e N * ((D.V N : ℝ) ^ q * (D.V N : ℝ)) *
          (D.V N : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa using hbase.mul hinvV
    exact hprod.congr' heq
  have hbase := hweighted D.epsilonBase D.epsilonBase_superpolynomial
  have hcrt := hweighted D.epsilonCRT D.epsilonCRT_superpolynomial
  have hweightedSum : Tendsto
      (fun N => (D.V N : ℝ) ^ q * (D.epsilonBase N + D.epsilonCRT N))
      atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun N => (D.V N : ℝ) ^ q * D.epsilonBase N +
          (D.V N : ℝ) ^ q * D.epsilonCRT N) atTop (𝓝 0) := by
      simpa using hbase.add hcrt
    apply hsum.congr'
    filter_upwards with N
    ring
  have hNplus : Tendsto (fun N : ℕ => (N + 1 : ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro x
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x)] with N hN
    exact le_trans hN (by norm_num)
  have hinvN : Tendsto (fun N : ℕ => (N + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNplus
  simpa [one_div] using hinvN.add hweightedSum

theorem c_test2_weightedSubsetEventAverage_tendsto_zero
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (ι : Fin q ↪ Fin s)
    (tests : Finset (IntegerPolynomial q)) (included : Finset (Fin r))
    (hlisted : TestsListed Dm ι tests)
    (hPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ j,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0)
    (hPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ i j,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v i))
    (hScaleEventually : ∀ᶠ N in atTop, c_test2_ScaleData S C a N)
    (hPoolEventually : ∀ᶠ N in atTop,
      2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
        (S.primeStage.pool N C.gap).lower)
    (hMassEventually : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper)
    (E : ℕ → (Fin q → ℕ) → Prop)
    (hprob : Tendsto (fun N => gapSlotProbability S C.gap N (E N)) atTop (𝓝 0)) :
    Tendsto (fun N => c_test2_subsetRowEventAverage S C a Sh included N (E N))
      atTop (𝓝 0) := by
  classical
  let D : FromArithmetic.WeightedLinearFormsData (q := r) (d := m) (b := K) S :=
    c_test2_weightedRowData (Sh := Sh) S C a dirs ι tests included hlisted
      hPrimitive hPairwise
  let Efull (N : ℕ) (p : Fin s → ℕ) : Prop :=
    D.goodDomain N p ∧ E N (fun i => p (ι i))
  let lo (N : ℕ) : Fin s → ℕ := fun _ => (S.primeStage.pool N C.gap).lower
  let hi (N : ℕ) : Fin s → ℕ := fun _ => (S.primeStage.pool N C.gap).upper
  have herror := c_test2_weightedLinearFormsError_tendsto_zero D
  obtain ⟨Cerr, hCerr, hbound⟩ := FromArithmetic.prop_linear_forms D
  let err (N : ℕ) : ℝ :=
    1 / (N + 1 : ℝ) + (D.V N : ℝ) ^ r * (D.epsilonBase N + D.epsilonCRT N)
  have hupper : Tendsto (fun N => Cerr * err N) atTop (𝓝 0) := by
    simpa [err, mul_comm] using herror.const_mul Cerr
  let average (N : ℕ) : ℝ :=
    FromArithmetic.weightedLinearFormsAverage D N (Efull N)
  let probability (N : ℕ) : ℝ :=
    FromArithmetic.weightedLinearFormsEventProbability D N (Efull N)
  have haverageProbability : Tendsto (fun N => |average N - probability N|)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall (fun _ => abs_nonneg _)
    · filter_upwards with N
      exact hbound N (Efull N) (fun p hp => hp.1)
  have hdiff : Tendsto (fun N => average N - probability N) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using haverageProbability.neg) haverageProbability
    · filter_upwards with N
      exact neg_abs_le _
    · filter_upwards with N
      exact le_abs_self _
  have hprobEq : ∀ᶠ N in atTop, probability N = gapSlotProbability S C.gap N (E N) := by
    filter_upwards [hScaleEventually, hPoolEventually, hMassEventually] with N hScaleN hPoolN hMassN
    calc
      probability N = independentPrimePoolProbability (lo N) (hi N)
          (fun p => E N (fun i => p (ι i))) := by
        unfold probability FromArithmetic.weightedLinearFormsEventProbability
          independentPrimePoolProbability
        apply tsum_congr
        intro p
        have hmassEq :
            independentPrimePoolMass
              (fun i => (S.primeStage.pool N (D.gap i)).lower)
              (fun i => (S.primeStage.pool N (D.gap i)).upper) p =
            independentPrimePoolMass (lo N) (hi N) p := by rfl
        rw [hmassEq]
        let mass := independentPrimePoolMass (lo N) (hi N) p
        by_cases hmass : mass = 0
        · simp [mass, hmass]
        · have hslot (i : Fin s) :
              (S.primeStage.pool N C.gap).lower ≤ p i ∧
                p i < (S.primeStage.pool N C.gap).upper ∧ (p i).Prime := by
            have hfactor : primePoolLaw (lo N i) (hi N i) (p i) ≠ 0 := by
              apply (Finset.prod_ne_zero_iff.mp ?_) i (Finset.mem_univ i)
              simpa [mass, independentPrimePoolMass] using hmass
            unfold primePoolLaw at hfactor
            split_ifs at hfactor with hsupp
            · exact hsupp
            · simp at hfactor
          have hgood : D.goodDomain N p := by
            change c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p
            exact ⟨hScaleN, hPoolN, fun i => hslot (ι i)⟩
          by_cases hE : E N (fun i => p (ι i))
          · simp [mass, Efull, hgood, hE]
          · simp [mass, Efull, hgood, hE]
      _ = gapSlotProbability S C.gap N (E N) := by
        symm
        exact c_test2_gapSlotProbability_cylinder S C.gap N ι hMassN (E N)
  have hprobEq' : (fun N => gapSlotProbability S C.gap N (E N)) =ᶠ[atTop] probability :=
    hprobEq.mono fun N hN => hN.symm
  have hprobD : Tendsto probability atTop (𝓝 0) := hprob.congr' hprobEq'
  have haverage : Tendsto average atTop (𝓝 0) := by
    have hsum := hdiff.add hprobD
    simpa [average, probability, sub_add_cancel] using hsum
  have hidentity : ∀ᶠ N in atTop,
      c_test2_subsetRowEventAverage S C a Sh included N (E N) = average N := by
    filter_upwards [hScaleEventually, hPoolEventually, hMassEventually]
      with N hScaleN hPoolN hMassN
    exact (c_test2_weightedSubsetEventIdentity S C a Sh dirs ι tests included
      hlisted hPrimitive hPairwise N hScaleN hPoolN hMassN (E N)).symm
  have hidentity' : (fun N => average N) =ᶠ[atTop]
      (fun N => c_test2_subsetRowEventAverage S C a Sh included N (E N)) :=
    hidentity.mono fun N hN => hN.symm
  exact haverage.congr' hidentity'

noncomputable def c_test2_rowEnvelope {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (N : ℕ)
    (p : Fin q → ℕ) (z : Fin m → ℤ) : ℝ :=
  ∏ R, (1 + atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
    (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
      (fun k => (z k : ℚ))))

noncomputable def c_test2_rowEnvelopeEventAverage {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (N : ℕ)
    (E : (Fin q → ℕ) → Prop) : ℝ :=
  gapSlotAverage S C.gap N fun p => if E p then
    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
      c_test2_rowEnvelope S C a Sh N p z else 0

theorem c_test2_rowEnvelopeEventAverage_eq_powersetSum
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (ι : Fin q ↪ Fin s)
    (N : ℕ) (E : (Fin q → ℕ) → Prop)
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper) :
    c_test2_rowEnvelopeEventAverage S C a Sh N E =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
        c_test2_subsetRowEventAverage S C a Sh I N E := by
  classical
  let pivotSupport : Finset (Fin m → ℤ) := Fintype.piFinset fun i : Fin m =>
    Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
      ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ)
  have hPivotZero (z : Fin m → ℤ) (hz : z ∉ pivotSupport) :
      pivotMass S.core.parameters C N z = 0 := by
    have hnot : ¬ ∀ i : Fin m, z i ∈
        Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
          ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ) := by
      intro hall
      exact hz (Fintype.mem_piFinset.mpr hall)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hLaw : harmonicLaw (S.core.parameters.X N (C.block i).1)
        (primorial (N + 1)) (z i) = 0 := by
      by_contra hne
      have hs := c_test2_harmonicLaw_support hne
      have hmem : z i ∈ Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
          ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ) := by
        simp [Finset.mem_Ico]
        exact ⟨hs.2.1, hs.2.2⟩
      exact hi hmem
    unfold pivotMass
    exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw
  let slotSupport : Finset (Fin s → ℕ) := Fintype.piFinset fun _ : Fin s =>
    Finset.Ico (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper
  have hSlotZero (p : Fin s → ℕ) (hp : p ∉ slotSupport) :
      independentPrimePoolMass
        (fun _ : Fin s => (S.primeStage.pool N C.gap).lower)
        (fun _ => (S.primeStage.pool N C.gap).upper) p = 0 := by
    apply c_test2_independentPrimePoolMass_zero_outside
    simpa [slotSupport] using hp
  have hPivotExpand (p : Fin q → ℕ) :
      (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
        c_test2_rowEnvelope S C a Sh N p z) =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
        ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
              (fun k => (z k : ℚ))) := by
    let subsets := (Finset.univ : Finset (Fin r)).powerset
    let factor (I : Finset (Fin r)) (z : Fin m → ℤ) : ℝ :=
      ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
        (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
          (fun k => (z k : ℚ)))
    have hsum (z : Fin m → ℤ) :
        c_test2_rowEnvelope S C a Sh N p z = ∑ I ∈ subsets, factor I z := by
      unfold c_test2_rowEnvelope
      simpa [subsets, factor] using
        (Finset.prod_one_add (s := (Finset.univ : Finset (Fin r)))
          (f := fun R => atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
              (fun k => (z k : ℚ)))))
    have hswap :
        (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          ∑ I ∈ subsets, factor I z) =
        ∑ I ∈ subsets, ∑' z : Fin m → ℤ,
          pivotMass S.core.parameters C N z * factor I z := by
      calc
        _ = ∑ z ∈ pivotSupport, pivotMass S.core.parameters C N z *
              ∑ I ∈ subsets, factor I z := by
            apply tsum_eq_sum
            intro z hz
            rw [hPivotZero z hz]
            simp
        _ = ∑ I ∈ subsets, ∑ z ∈ pivotSupport,
              pivotMass S.core.parameters C N z * factor I z := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
        _ = ∑ I ∈ subsets, ∑' z : Fin m → ℤ,
              pivotMass S.core.parameters C N z * factor I z := by
            apply Finset.sum_congr rfl
            intro I hI
            symm
            apply tsum_eq_sum
            intro z hz
            rw [hPivotZero z hz]
            simp
    rw [show (∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
        c_test2_rowEnvelope S C a Sh N p z) =
        ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          ∑ I ∈ subsets, factor I z by
          apply tsum_congr
          intro z
          rw [hsum z]]
    simpa [factor, subsets] using hswap
  have hpoint (p : Fin s → ℕ) :
      (if E (fun i => p (ι i)) then
        ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
          c_test2_rowEnvelope S C a Sh N (fun i => p (ι i)) z else 0) =
      ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
        if E (fun i => p (ι i)) then
          ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
            ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
              (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0 := by
    by_cases hE : E (fun i => p (ι i))
    · simp only [if_pos hE]
      rw [hPivotExpand]
    · simp only [if_neg hE]
      simp
  unfold c_test2_rowEnvelopeEventAverage
  let lo : Fin s → ℕ := fun _ => (S.primeStage.pool N C.gap).lower
  let hi : Fin s → ℕ := fun _ => (S.primeStage.pool N C.gap).upper
  let subsetSet := (Finset.univ : Finset (Fin r)).powerset
  calc
    _ = ∑' p : Fin s → ℕ,
        independentPrimePoolMass lo hi p *
          (if E (fun i => p (ι i)) then
            ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
              c_test2_rowEnvelope S C a Sh N (fun i => p (ι i)) z else 0) := by
          rw [c_test2_gapSlotAverage_cylinder S C.gap N ι hMass
            (fun p => if E p then
              ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                c_test2_rowEnvelope S C a Sh N p z else 0)]
    _ = ∑' p : Fin s → ℕ,
        independentPrimePoolMass lo hi p *
          ∑ I ∈ subsetSet,
            (if E (fun i => p (ι i)) then
              ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                  (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                    (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) := by
          apply tsum_congr
          intro p
          rw [hpoint]
    _ = ∑ I ∈ subsetSet, ∑' p : Fin s → ℕ,
          independentPrimePoolMass lo hi p *
            (if E (fun i => p (ι i)) then
              ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                  (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                    (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) := by
          have hleft : ∀ p, p ∉ slotSupport →
              independentPrimePoolMass lo hi p *
                ∑ I ∈ subsetSet,
                  (if E (fun i => p (ι i)) then
                    ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                      ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                        (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                          (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) = 0 := by
            intro p hp
            rw [hSlotZero p hp]
            simp
          have hright (I : Finset (Fin r)) (p : Fin s → ℕ) (hp : p ∉ slotSupport) :
              independentPrimePoolMass lo hi p *
                (if E (fun i => p (ι i)) then
                  ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                    ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                      (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                        (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) = 0 := by
            rw [hSlotZero p hp]
            simp
          calc
            _ = ∑ p ∈ slotSupport, independentPrimePoolMass lo hi p *
                  ∑ I ∈ subsetSet,
                    (if E (fun i => p (ι i)) then
                      ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                        ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                            (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) := by
              apply tsum_eq_sum
              exact hleft
            _ = ∑ I ∈ subsetSet, ∑ p ∈ slotSupport,
                  independentPrimePoolMass lo hi p *
                    (if E (fun i => p (ι i)) then
                      ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                        ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                            (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) := by
              simp_rw [Finset.mul_sum]
              exact Finset.sum_comm
            _ = ∑ I ∈ subsetSet, ∑' p : Fin s → ℕ,
                  independentPrimePoolMass lo hi p *
                    (if E (fun i => p (ι i)) then
                      ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
                        ∏ R ∈ I, atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
                          (rowForm (chainScale S.core.parameters C a N) (Sh.row R)
                            (fun i => p (ι i)) (fun k => (z k : ℚ))) else 0) := by
              apply Finset.sum_congr rfl
              intro I hI
              symm
              apply tsum_eq_sum
              exact fun p hp => hright I p hp
    _ = ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
          c_test2_subsetRowEventAverage S C a Sh I N E := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [c_test2_subsetRowEventAverage]
          rw [c_test2_gapSlotAverage_cylinder S C.gap N ι hMass]

theorem c_test2_rowEnvelopeEventAverage_tendsto_zero
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (ι : Fin q ↪ Fin s)
    (tests : Finset (IntegerPolynomial q))
    (hlisted : TestsListed Dm ι tests)
    (hPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ j,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0)
    (hPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ i j,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v i))
    (hScaleEventually : ∀ᶠ N in atTop, c_test2_ScaleData S C a N)
    (hPoolEventually : ∀ᶠ N in atTop,
      2 * FromArithmetic.masterScaleV S.core.parameters N C.gap ≤
        (S.primeStage.pool N C.gap).lower)
    (hMassEventually : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper)
    (E : ℕ → (Fin q → ℕ) → Prop)
    (hprob : Tendsto (fun N => gapSlotProbability S C.gap N (E N)) atTop (𝓝 0)) :
    Tendsto (fun N => c_test2_rowEnvelopeEventAverage S C a Sh N (E N))
      atTop (𝓝 0) := by
  let subsetSet := (Finset.univ : Finset (Fin r)).powerset
  have hsum : Tendsto (fun N =>
      ∑ I ∈ subsetSet, c_test2_subsetRowEventAverage S C a Sh I N (E N))
      atTop (𝓝 (∑ I ∈ subsetSet, (0 : ℝ))) := by
    apply tendsto_finsetSum subsetSet
    intro I hI
    exact c_test2_weightedSubsetEventAverage_tendsto_zero S C a ha Sh dirs ι tests I
      hlisted hPrimitive hPairwise hScaleEventually hPoolEventually hMassEventually E hprob
  have hMassEventually' : ∀ᶠ N in atTop,
      0 < primePoolMass (S.primeStage.pool N C.gap).lower
        (S.primeStage.pool N C.gap).upper := hMassEventually
  have hEq : ∀ᶠ N in atTop,
      c_test2_rowEnvelopeEventAverage S C a Sh N (E N) =
        ∑ I ∈ (Finset.univ : Finset (Fin r)).powerset,
          c_test2_subsetRowEventAverage S C a Sh I N (E N) := by
    filter_upwards [hMassEventually'] with N hMassN
    exact c_test2_rowEnvelopeEventAverage_eq_powersetSum S C a Sh ι N (E N) hMassN
  have hEq' : (fun N =>
      ∑ I ∈ subsetSet, c_test2_subsetRowEventAverage S C a Sh I N (E N)) =ᶠ[atTop]
      (fun N => c_test2_rowEnvelopeEventAverage S C a Sh N (E N)) :=
    hEq.mono fun N hN => hN.symm
  have hsum' : Tendsto (fun N =>
      ∑ I ∈ subsetSet, c_test2_subsetRowEventAverage S C a Sh I N (E N))
      atTop (𝓝 0) := by simpa using hsum
  exact hsum'.congr' hEq'

theorem c_test2_weightedTsum_abs_le {α : Type*} (μ F G : α → ℝ)
    (hμnonneg : ∀ x, 0 ≤ μ x)
    (hF : Summable (fun x => μ x * F x))
    (hG : Summable (fun x => μ x * G x))
    (hpoint : ∀ x, |F x| ≤ G x) :
    |∑' x, μ x * F x| ≤ ∑' x, μ x * G x := by
  have hAbs : Summable (fun x => μ x * |F x|) := by
    apply hF.norm.congr
    intro x
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμnonneg x)]
  calc
    |∑' x, μ x * F x| = ‖∑' x, μ x * F x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' x, ‖μ x * F x‖ := norm_tsum_le_tsum_norm hF.norm
    _ = ∑' x, μ x * |F x| := by
      apply tsum_congr
      intro x
      simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμnonneg x)]
    _ ≤ ∑' x, μ x * G x := hAbs.tsum_le_tsum (fun x =>
      mul_le_mul_of_nonneg_left (hpoint x) (hμnonneg x)) hG

theorem c_test2_pivotMass_zero_outside_support
    {K s m : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m) (N : ℕ)
    (z : Fin m → ℤ)
    (hz : z ∉ Fintype.piFinset (fun i : Fin m =>
      Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
        ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ))) :
    pivotMass S.core.parameters C N z = 0 := by
  have hnot : ¬ ∀ i : Fin m, z i ∈
      Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
        ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ) := by
    intro hall
    exact hz (Fintype.mem_piFinset.mpr hall)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hLaw : harmonicLaw (S.core.parameters.X N (C.block i).1)
      (primorial (N + 1)) (z i) = 0 := by
    by_contra hne
    have hs := c_test2_harmonicLaw_support hne
    have hmem : z i ∈ Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
        ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ) := by
      simp [Finset.mem_Ico]
      exact ⟨hs.2.1, hs.2.2⟩
    exact hi hmem
  unfold pivotMass
  exact Finset.prod_eq_zero (Finset.mem_univ i) hLaw

noncomputable def c_test2_rowPivotAverage {K s m q r : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (N : ℕ)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ) (p : Fin q → ℕ) : ℝ :=
  ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
    ∏ R, atQ (f R p)
      (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
        (fun k => (z k : ℚ)))

theorem c_test2_rowPivotAverage_abs_le_envelope
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (N : ℕ)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ)
    (hNorm : ∀ i : Fin m, 0 < harmonicNormalizer
      (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
    (hF : ∀ R p y, |f R p y| ≤
      1 + chainWeight S.core.parameters C N (Sh.row R).anchor y)
    (p : Fin q → ℕ) :
    |c_test2_rowPivotAverage S C a Sh N f p| ≤
      ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
        c_test2_rowEnvelope S C a Sh N p z := by
  classical
  let support : Finset (Fin m → ℤ) := Fintype.piFinset fun i : Fin m =>
    Finset.Ico (S.core.parameters.X N (C.block i).1 : ℤ)
      ((S.core.parameters.X N (C.block i).1) ^ 2 : ℤ)
  let F (z : Fin m → ℤ) : ℝ :=
    ∏ R, atQ (f R p)
      (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
        (fun k => (z k : ℚ)))
  let G (z : Fin m → ℤ) : ℝ := c_test2_rowEnvelope S C a Sh N p z
  have hμnonneg (z : Fin m → ℤ) : 0 ≤ pivotMass S.core.parameters C N z := by
    unfold pivotMass
    apply Finset.prod_nonneg
    intro i _
    exact c_test2_harmonicLaw_nonneg_of_normalizer_pos (hNorm i) (z i)
  have hpoint (z : Fin m → ℤ) : |F z| ≤ G z := by
    have hfactor (R : Fin r) :
        |atQ (f R p)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
              (fun k => (z k : ℚ)))| ≤
          1 + atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
            (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
              (fun k => (z k : ℚ))) := by
      let x := rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
        (fun k => (z k : ℚ))
      by_cases hx : x.den = 1
      · simpa [x, atQ, hx] using hF R p x.num
      · simp [x, atQ, hx]
    unfold F G c_test2_rowEnvelope
    calc
      |∏ R, atQ (f R p)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
            (fun k => (z k : ℚ)))| =
        ∏ R, |atQ (f R p)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
            (fun k => (z k : ℚ)))| := by
          rw [Finset.abs_prod]
      _ ≤ ∏ R, (1 + atQ (chainWeight S.core.parameters C N (Sh.row R).anchor)
          (rowForm (chainScale S.core.parameters C a N) (Sh.row R) p
            (fun k => (z k : ℚ)))) := by
          apply Finset.prod_le_prod₀
          · intro R hR
            exact abs_nonneg _
          · intro R hR
            exact hfactor R
  have hFsum : Summable (fun z : Fin m → ℤ => pivotMass S.core.parameters C N z * F z) := by
    apply summable_of_ne_finset_zero (s := support)
    intro z hz
    rw [c_test2_pivotMass_zero_outside_support S C N z (by simpa [support] using hz)]
    simp
  have hGsum : Summable (fun z : Fin m → ℤ => pivotMass S.core.parameters C N z * G z) := by
    apply summable_of_ne_finset_zero (s := support)
    intro z hz
    rw [c_test2_pivotMass_zero_outside_support S C N z (by simpa [support] using hz)]
    simp
  simpa [c_test2_rowPivotAverage, F, G] using
    c_test2_weightedTsum_abs_le (pivotMass S.core.parameters C N) F G
      hμnonneg hFsum hGsum hpoint

theorem c_test2_rowBadAverage_abs_le_envelope
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (N : ℕ)
    (good : (Fin q → ℕ) → Prop)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ)
    (hNorm : ∀ i : Fin m, 0 < harmonicNormalizer
      (S.core.parameters.X N (C.block i).1) (primorial (N + 1)))
    (hMass : 0 < primePoolMass (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper)
    (hF : ∀ R p y, |f R p y| ≤
      1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) :
    |gapSlotAverage S C.gap N (fun p =>
        if good p then 0 else c_test2_rowPivotAverage S C a Sh N f p)| ≤
      c_test2_rowEnvelopeEventAverage S C a Sh N (fun p => ¬ good p) := by
  classical
  let lo : Fin q → ℕ := fun _ => (S.primeStage.pool N C.gap).lower
  let hi : Fin q → ℕ := fun _ => (S.primeStage.pool N C.gap).upper
  let μ (p : Fin q → ℕ) : ℝ := independentPrimePoolMass lo hi p
  let F (p : Fin q → ℕ) : ℝ :=
    if good p then 0 else c_test2_rowPivotAverage S C a Sh N f p
  let G (p : Fin q → ℕ) : ℝ :=
    if ¬ good p then
      ∑' z : Fin m → ℤ, pivotMass S.core.parameters C N z *
        c_test2_rowEnvelope S C a Sh N (fun i => p i) z
    else 0
  have hμnonneg (p : Fin q → ℕ) : 0 ≤ μ p := by
    apply c_test2_independentPrimePoolMass_nonneg lo hi (fun _ => hMass)
  let support : Finset (Fin q → ℕ) := Fintype.piFinset fun _ : Fin q =>
    Finset.Ico (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper
  have hμzero (p : Fin q → ℕ) (hp : p ∉ support) : μ p = 0 := by
    exact c_test2_independentPrimePoolMass_zero_outside lo hi p
      (by simpa [support, lo, hi] using hp)
  have hFsum : Summable (fun p => μ p * F p) := by
    apply summable_of_ne_finset_zero (s := support)
    intro p hp
    rw [hμzero p hp]
    simp
  have hGsum : Summable (fun p => μ p * G p) := by
    apply summable_of_ne_finset_zero (s := support)
    intro p hp
    rw [hμzero p hp]
    simp
  have hpoint (p : Fin q → ℕ) : |F p| ≤ G p := by
    by_cases hp : good p
    · simp [F, G, hp]
    · simpa [F, G, hp] using
        c_test2_rowPivotAverage_abs_le_envelope S C a Sh N f hNorm hF p
  have hweighted := c_test2_weightedTsum_abs_le μ F G hμnonneg hFsum hGsum hpoint
  change |∑' p : Fin q → ℕ, μ p * F p| ≤
    ∑' p : Fin q → ℕ, μ p * G p at hweighted
  simpa [gapSlotAverage, gapSlotMass, c_test2_rowEnvelopeEventAverage, μ, F, G] using hweighted

theorem c_test2_rowCorrelation_decompose
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (Sh : RowShape m q r) (dirs : RowDirections Sh)
    (tests : Finset (IntegerPolynomial q)) (N : ℕ)
    (f : Fin r → (Fin q → ℕ) → ℤ → ℝ)
    (hGoodProb : 0 < gapSlotProbability S C.gap N
      (fun p => GoodTuple S C.gap N tests dirs.poly p)) :
    rowCorrelation S C a N Sh f =
      gapSlotProbability S C.gap N (fun p => GoodTuple S C.gap N tests dirs.poly p) *
        goodRowCorrelation S C a N dirs tests f +
      gapSlotAverage S C.gap N (fun p =>
        if GoodTuple S C.gap N tests dirs.poly p then 0
        else c_test2_rowPivotAverage S C a Sh N f p) := by
  classical
  let good : (Fin q → ℕ) → Prop := fun p => GoodTuple S C.gap N tests dirs.poly p
  let μ : (Fin q → ℕ) → ℝ := gapSlotMass S C.gap N
  let F : (Fin q → ℕ) → ℝ := c_test2_rowPivotAverage S C a Sh N f
  let support : Finset (Fin q → ℕ) := Fintype.piFinset fun _ : Fin q =>
    Finset.Ico (S.primeStage.pool N C.gap).lower
      (S.primeStage.pool N C.gap).upper
  have hμzero (p : Fin q → ℕ) (hp : p ∉ support) : μ p = 0 := by
    apply c_test2_independentPrimePoolMass_zero_outside
    simpa [support, μ, gapSlotMass] using hp
  have hrawSummable : Summable (fun p => μ p * F p) := by
    apply summable_of_ne_finset_zero (s := support)
    intro p hp
    rw [hμzero p hp]
    simp
  have hgoodSummable : Summable (fun p => μ p * if good p then F p else 0) := by
    apply summable_of_ne_finset_zero (s := support)
    intro p hp
    rw [hμzero p hp]
    simp
  have hbadSummable : Summable (fun p => μ p * if good p then 0 else F p) := by
    apply summable_of_ne_finset_zero (s := support)
    intro p hp
    rw [hμzero p hp]
    simp
  have hsplit :
      (∑' p : Fin q → ℕ, μ p * F p) =
        (∑' p, μ p * (if good p then F p else 0)) +
          ∑' p, μ p * (if good p then 0 else F p) := by
    calc
      _ = ∑' p : Fin q → ℕ,
          (μ p * (if good p then F p else 0) +
            μ p * (if good p then 0 else F p)) := by
          apply tsum_congr
          intro p
          by_cases hp : good p <;> simp [hp]
      _ = _ := hgoodSummable.tsum_add hbadSummable
  have hnorm :
      gapSlotProbability S C.gap N good * goodRowCorrelation S C a N dirs tests f =
        ∑' p : Fin q → ℕ, μ p * (if good p then F p else 0) := by
    unfold goodRowCorrelation goodSlotAverage
    dsimp [good, μ, F]
    field_simp [ne_of_gt hGoodProb]
    simp [c_test2_rowPivotAverage]
  calc
    rowCorrelation S C a N Sh f = ∑' p : Fin q → ℕ, μ p * F p := by
      rfl
    _ = _ := by rw [hsplit, ← hnorm]; rfl

theorem c_test2_rowCorrelation_le_good_eventually
    {K s m q r : ℕ} {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) (Sh : RowShape m q r)
    (dirs : RowDirections Sh) (ι : Fin q ↪ Fin s)
    (tests : Finset (IntegerPolynomial q)) (hlisted : TestsListed Dm ι tests)
    (hPrimitive : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        ∀ u, ∃ j,
          FromArithmetic.rationalResidue r' hr
            (c_test2_rowWeightedCoeff S C a ι Sh N p u j) ≠ 0)
    (hPairwise : ∀ N p,
      c_test2_rowWeightedGoodDomain S C a ι Sh dirs tests N p →
      ∀ r' (hr : r'.Prime), N + 1 < r' →
        r' ≤ FromArithmetic.masterScaleV S.core.parameters N C.gap →
        (∀ Q ∈ Dm, ¬ ((r' : ℤ) ∣ evalIntegerPolynomial Q (fun i => (p i : ℤ)))) →
        ∀ u v, u ≠ v → ∃ i j,
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u i) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v j) ≠
          FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p u j) *
            FromArithmetic.rationalResidue r' hr
              (c_test2_rowWeightedCoeff S C a ι Sh N p v i))
    (hbad : Tendsto (fun N => gapSlotProbability S C.gap N
      (fun p => ¬ GoodTuple S C.gap N tests dirs.poly p)) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ N in atTop,
      ∀ f : Fin r → (Fin q → ℕ) → ℤ → ℝ,
        (∀ R p y, |f R p y| ≤
          1 + chainWeight S.core.parameters C N (Sh.row R).anchor y) →
        |rowCorrelation S C a N Sh f| ≤
          |goodRowCorrelation S C a N dirs tests f| + η := by
  have hScaleEventually := c_test2_chainCoefficientData_eventually S C a ha
  have hPoolEventually := c_test2_poolLower_ge_twiceMasterV_eventually S C.gap
  have hMassEventually := c_test2_poolMass_positive_eventually S C.gap
  have hGoodEventually := c_test2_goodSlotProbability_pos_eventually S C.gap
    tests dirs.poly hbad
  have hEnvelope := c_test2_rowEnvelopeEventAverage_tendsto_zero S C a ha Sh dirs ι
    tests hlisted hPrimitive hPairwise hScaleEventually hPoolEventually hMassEventually
    (fun N p => ¬ GoodTuple S C.gap N tests dirs.poly p) hbad
  intro η hη
  have hEnvLT : ∀ᶠ N in atTop,
      c_test2_rowEnvelopeEventAverage S C a Sh N
        (fun p => ¬ GoodTuple S C.gap N tests dirs.poly p) < η :=
    hEnvelope.eventually (Iio_mem_nhds hη)
  filter_upwards [hEnvLT, hGoodEventually, hMassEventually] with N hEnvN hGoodN hMassN
  intro f hf
  have hNorm (i : Fin m) : 0 < harmonicNormalizer
      (S.core.parameters.X N (C.block i).1) (primorial (N + 1)) :=
    c_test2_harmonicNormalizer_pos_of_cutoff _ _ (primorial_pos (N + 1))
      (S.gapStage.valid_raw_cutoffs N (C.block i).1)
  let good : (Fin q → ℕ) → Prop :=
    fun p => GoodTuple S C.gap N tests dirs.poly p
  let P : ℝ := gapSlotProbability S C.gap N good
  let badAverage : ℝ := gapSlotAverage S C.gap N (fun p =>
    if good p then 0 else c_test2_rowPivotAverage S C a Sh N f p)
  have hprobSplit : P + gapSlotProbability S C.gap N (fun p => ¬ good p) = 1 := by
    have h := c_test2_independentProbability_add_compl
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ => (S.primeStage.pool N C.gap).upper) (fun _ => hMassN) good
    simpa [P, good, gapSlotProbability] using h
  have hbadNonneg : 0 ≤ gapSlotProbability S C.gap N (fun p => ¬ good p) :=
    c_test2_independentPrimePoolProbability_nonneg
      (fun _ : Fin q => (S.primeStage.pool N C.gap).lower)
      (fun _ => (S.primeStage.pool N C.gap).upper) (fun p => ¬ good p)
  have hPle : P ≤ 1 := by linarith
  have hbadBound : |badAverage| ≤
      c_test2_rowEnvelopeEventAverage S C a Sh N (fun p => ¬ good p) :=
    c_test2_rowBadAverage_abs_le_envelope S C a Sh N good f hNorm hMassN hf
  rw [c_test2_rowCorrelation_decompose S C a Sh dirs tests N f hGoodN]
  calc
    |P * goodRowCorrelation S C a N dirs tests f + badAverage| ≤
        |P * goodRowCorrelation S C a N dirs tests f| + |badAverage| := abs_add_le _ _
    _ = P * |goodRowCorrelation S C a N dirs tests f| + |badAverage| := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hGoodN)]
    _ ≤ |goodRowCorrelation S C a N dirs tests f| + η := by
      calc
        _ ≤ P * |goodRowCorrelation S C a N dirs tests f| +
            c_test2_rowEnvelopeEventAverage S C a Sh N (fun p => ¬ good p) :=
          add_le_add le_rfl hbadBound
        _ ≤ |goodRowCorrelation S C a N dirs tests f| + η := by
          calc
            _ ≤ 1 * |goodRowCorrelation S C a N dirs tests f| +
                c_test2_rowEnvelopeEventAverage S C a Sh N (fun p => ¬ good p) :=
              by
                nlinarith [mul_le_mul_of_nonneg_right hPle (abs_nonneg
                  (goodRowCorrelation S C a N dirs tests f))]
            _ = |goodRowCorrelation S C a N dirs tests f| +
                c_test2_rowEnvelopeEventAverage S C a Sh N (fun p => ¬ good p) := by ring
            _ ≤ |goodRowCorrelation S C a N dirs tests f| + η := by
              nlinarith [hEnvN]

end HindmanSumsProducts
