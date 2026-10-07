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

end HindmanSumsProducts
