import HindmanSumsProducts.Prediction.Defs

/-! Helper lemmas for the §5 proof package S5-A (owned by its proof lane). -/

namespace HindmanSumsProducts

open scoped BigOperators Topology
open Filter

noncomputable section

private def primeTupleSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private lemma independentPrimePoolMass_zero_of_not_mem_support {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hp : p ∉ primeTupleSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnot : ¬ ∀ i, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    exact Fintype.mem_piFinset.mpr hall
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)).elim
  · rfl

private lemma pkgA_independentPrimePoolMass_summable {m : ℕ}
    (lo hi : Fin m → ℕ) : Summable (independentPrimePoolMass lo hi) := by
  apply summable_of_ne_finset_zero (s := primeTupleSupport lo hi)
  intro p hp
  exact independentPrimePoolMass_zero_of_not_mem_support lo hi p hp

private lemma independentPrimePoolMass_nonneg {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ) :
    0 ≤ independentPrimePoolMass lo hi p := by
  unfold independentPrimePoolMass
  apply Finset.prod_nonneg
  intro i hi
  unfold primePoolLaw
  split_ifs with h
  · unfold primePoolMass
    apply div_nonneg
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · apply Finset.sum_nonneg
      intro p hp
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · simp

private lemma independentPrimePoolProbability_summable {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := primeTupleSupport lo hi)
  intro p hp
  rw [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp]
  simp

/-- Monotonicity of the iid prime-pool event probability, allowing predicates which differ
only outside the support of the sampling law. -/
theorem independentPrimePoolProbability_mono_of_support {m : ℕ}
    (lo hi : Fin m → ℕ) (E F : (Fin m → ℕ) → Prop)
    (hEF : ∀ p, independentPrimePoolMass lo hi p ≠ 0 → E p → F p) :
    independentPrimePoolProbability lo hi E ≤ independentPrimePoolProbability lo hi F := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  letI : DecidablePred F := fun p => Classical.propDecidable (F p)
  have hE := independentPrimePoolProbability_summable lo hi E
  have hF := independentPrimePoolProbability_summable lo hi F
  unfold independentPrimePoolProbability
  apply hE.tsum_le_tsum ?_ hF
  intro p
  by_cases hmass : independentPrimePoolMass lo hi p = 0
  · simp [hmass]
  by_cases hE' : E p
  · have hF' := hEF p hmass hE'
    simp [hE', hF']
  · by_cases hF' : F p
    · simpa [hE', hF'] using independentPrimePoolMass_nonneg lo hi p
    · simp [hE', hF']

/-- The union bound for two events under the independent prime-pool law. -/
theorem independentPrimePoolProbability_union_le {m : ℕ}
    (lo hi : Fin m → ℕ) (E F : (Fin m → ℕ) → Prop)
    : independentPrimePoolProbability lo hi (fun p => E p ∨ F p) ≤
      independentPrimePoolProbability lo hi E + independentPrimePoolProbability lo hi F := by
  classical
  letI : DecidablePred E := fun p => Classical.propDecidable (E p)
  letI : DecidablePred F := fun p => Classical.propDecidable (F p)
  letI : DecidablePred (fun p => E p ∨ F p) := fun p => Classical.propDecidable (E p ∨ F p)
  have hE := independentPrimePoolProbability_summable lo hi E
  have hF := independentPrimePoolProbability_summable lo hi F
  have hU := independentPrimePoolProbability_summable lo hi (fun p => E p ∨ F p)
  unfold independentPrimePoolProbability
  calc
    (∑' p, independentPrimePoolMass lo hi p * if E p ∨ F p then 1 else 0) ≤
        ∑' p, ((independentPrimePoolMass lo hi p * if E p then 1 else 0) +
          (independentPrimePoolMass lo hi p * if F p then 1 else 0)) := by
      apply hU.tsum_le_tsum ?_ (hE.add hF)
      intro p
      by_cases hE' : E p
      · by_cases hF' : F p
        · have hm := independentPrimePoolMass_nonneg lo hi p
          simp [hE', hF']
          linarith
        · simp [hE', hF']
      · by_cases hF' : F p <;> simp [hE', hF']
    _ = (∑' p, independentPrimePoolMass lo hi p * if E p then 1 else 0) +
        ∑' p, independentPrimePoolMass lo hi p * if F p then 1 else 0 := hE.tsum_add hF

private abbrev PoolValue (lo hi : ℕ) := {x : ℕ // x ∈ Finset.Ico lo hi}

private def poolTupleEquiv {m : ℕ} (lo hi : ℕ) :
    {p : Fin m → ℕ // p ∈ Fintype.piFinset (fun _ : Fin m => Finset.Ico lo hi)} ≃
      (Fin m → PoolValue lo hi) where
  toFun p i := ⟨p.1 i, (Fintype.mem_piFinset.mp p.2 i)⟩
  invFun p := ⟨fun i => (p i).1, Fintype.mem_piFinset.mpr (fun i => (p i).2)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro p
    funext i
    apply Subtype.ext
    rfl

private lemma independentPrimePoolProbability_finite {m : ℕ} (lo hi : ℕ)
    (E : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) E =
      ∑ p : Fin m → PoolValue lo hi,
        (∏ i, primePoolLaw lo hi (p i).1) *
          @ite ℝ (E (fun i => (p i).1)) (Classical.propDecidable _) 1 0 := by
  classical
  let S : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ : Fin m => Finset.Ico lo hi)
  have hsum : independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) E =
      ∑ p ∈ S,
        independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p * if E p then 1 else 0 := by
    unfold independentPrimePoolProbability
    have hzero : ∀ p ∉ S,
        independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p *
          (if E p then 1 else 0) = 0 := by
      intro p hp
      have hnot : ¬ ∀ i, p i ∈ Finset.Ico lo hi := by
        intro h
        exact hp (Fintype.mem_piFinset.mpr h)
      obtain ⟨i, hi'⟩ := not_forall.mp hnot
      have hmass : independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p = 0 := by
        unfold independentPrimePoolMass
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        unfold primePoolLaw
        split_ifs with h
        · exact (hi' (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩)).elim
        · rfl
      simp [hmass]
    exact tsum_eq_sum (L := SummationFilter.unconditional (Fin m → ℕ)) (s := S) hzero
  rw [hsum]
  have hattach :
      (∑ p ∈ S, independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p *
          if E p then 1 else 0) =
        ∑ p : S, independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p.1 *
          if E p.1 then 1 else 0 := by
    rw [← Finset.sum_attach]
    simp
  rw [hattach]
  exact Fintype.sum_equiv (poolTupleEquiv lo hi)
    (fun p : S => independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p.1 *
      if E p.1 then 1 else 0)
    (fun p : Fin m → PoolValue lo hi =>
      (∏ i, primePoolLaw lo hi (p i).1) *
        @ite ℝ (E (fun i => (p i).1)) (Classical.propDecidable _) 1 0)
    (by
      intro p
      by_cases hp : E p.1 <;> simp [hp, poolTupleEquiv, independentPrimePoolMass])

private lemma primePoolLaw_sum_eq_one (lo hi : ℕ) (hpos : 0 < primePoolMass lo hi) :
    ∑ p : PoolValue lo hi, primePoolLaw lo hi p.1 = 1 := by
  classical
  have hsum : ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p = 1 := by
    calc
      ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p =
          ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
            (1 / (p : ℝ)) / primePoolMass lo hi := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p hp
        simp [primePoolLaw, Finset.mem_Ico.mp hp]
      _ = primePoolMass lo hi / primePoolMass lo hi := by
        rw [← Finset.sum_div]
        rfl
      _ = 1 := div_self (ne_of_gt hpos)
  rw [← Finset.sum_subtype (s := Finset.Ico lo hi) (h := fun _ => Iff.rfl)]
  exact hsum

private lemma independentPrimePoolProbability_finite_true {m : ℕ} (lo hi : ℕ)
    (hpos : 0 < primePoolMass lo hi) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) (fun _ => True) = 1 := by
  classical
  rw [independentPrimePoolProbability_finite]
  simp only [ite_true, mul_one]
  have hsingle : ∑ x : PoolValue lo hi, primePoolLaw lo hi x.1 = 1 :=
    primePoolLaw_sum_eq_one lo hi hpos
  calc
    ∑ p : Fin m → PoolValue lo hi, ∏ i, primePoolLaw lo hi (p i).1 =
        ∏ i : Fin m, ∑ x : PoolValue lo hi, primePoolLaw lo hi x.1 := by
          symm
          exact Fintype.prod_sum
            (fun (_ : Fin m) (x : PoolValue lo hi) => primePoolLaw lo hi x.1)
    _ = 1 := by rw [hsingle]; simp

theorem independentPrimePoolProbability_nonneg {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) :
    0 ≤ independentPrimePoolProbability lo hi E := by
  classical
  unfold independentPrimePoolProbability
  apply tsum_nonneg
  intro p
  exact mul_nonneg (independentPrimePoolMass_nonneg lo hi p) (by split_ifs <;> positivity)

/-- A normalized prime-pool law splits into an event and its complement. -/
theorem independentPrimePoolProbability_add_compl {m : ℕ} (lo hi : ℕ)
    (hpos : 0 < primePoolMass lo hi) (E : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) E +
      independentPrimePoolProbability (fun _ => lo) (fun _ => hi) (fun p => ¬ E p) = 1 := by
  classical
  letI : DecidablePred (fun p : Fin m → ℕ => ¬ E p) :=
    fun p => Classical.propDecidable (¬ E p)
  have hE := independentPrimePoolProbability_summable (fun _ : Fin m => lo) (fun _ => hi) E
  have hNot := independentPrimePoolProbability_summable
    (fun _ : Fin m => lo) (fun _ => hi) (fun p => ¬ E p)
  calc
    independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) E +
        independentPrimePoolProbability (fun _ => lo) (fun _ => hi) (fun p => ¬ E p) =
      ∑' p, ((independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p * if E p then 1 else 0) +
        (independentPrimePoolMass (fun _ : Fin m => lo) (fun _ => hi) p * if ¬ E p then 1 else 0)) := by
          unfold independentPrimePoolProbability
          exact (hE.tsum_add hNot).symm
    _ = independentPrimePoolProbability (fun _ : Fin m => lo) (fun _ => hi) (fun _ => True) := by
      unfold independentPrimePoolProbability
      apply tsum_congr
      intro p
      by_cases h : E p <;> simp [h]
    _ = 1 := independentPrimePoolProbability_finite_true lo hi hpos

private def slotRangeEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    Fin q ≃ {j : Fin s // j ∈ Set.range ι} where
  toFun i := ⟨ι i, ⟨i, rfl⟩⟩
  invFun j := Classical.choose j.2
  left_inv := by
    intro i
    apply ι.injective
    exact Classical.choose_spec (⟨i, rfl⟩ : ι i ∈ Set.range ι)
  right_inv := by
    intro j
    apply Subtype.ext
    exact Classical.choose_spec j.2

private def slotIndexEquiv {q s : ℕ} (ι : Fin q ↪ Fin s) :
    (Fin q ⊕ {j : Fin s // j ∉ Set.range ι}) ≃ Fin s :=
  (Equiv.sumCongr (slotRangeEquiv ι) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range ι))

private theorem slotIndexEquiv_inl {q s : ℕ} (ι : Fin q ↪ Fin s) (i : Fin q) :
    slotIndexEquiv ι (Sum.inl i) = ι i := by
  change (slotRangeEquiv ι i).1 = ι i
  rfl

private theorem slotIndexEquiv_inr {q s : ℕ} (ι : Fin q ↪ Fin s)
    (j : {j : Fin s // j ∉ Set.range ι}) : slotIndexEquiv ι (Sum.inr j) = j.1 := by
  change j.1 = j.1
  rfl

private def slotTupleSplit {q s : ℕ} (ι : Fin q ↪ Fin s) (A : Type*) :
    (Fin s → A) ≃ ((Fin q → A) × ({j : Fin s // j ∉ Set.range ι} → A)) :=
  (Equiv.arrowCongr (slotIndexEquiv ι).symm (Equiv.refl A)).trans
    (Equiv.sumArrowEquivProdArrow (Fin q) {j : Fin s // j ∉ Set.range ι} A)

private theorem slotTupleSplit_left {q s : ℕ} (ι : Fin q ↪ Fin s) (A : Type*)
    (p : Fin s → A) (i : Fin q) : (slotTupleSplit ι A p).1 i = p (ι i) := by
  simp [slotTupleSplit, slotIndexEquiv_inl]

private theorem slotTupleSplit_right {q s : ℕ} (ι : Fin q ↪ Fin s) (A : Type*)
    (p : Fin s → A) (j : {j : Fin s // j ∉ Set.range ι}) :
    (slotTupleSplit ι A p).2 j = p j.1 := by
  simp [slotTupleSplit, slotIndexEquiv_inr]

/-- An event on an embedded group of iid slots has exactly its own iid prime-pool probability.
The complementary slots integrate to one. -/
theorem independentPrimePoolProbability_iid_marginal {q s : ℕ}
    (lo hi : ℕ) (hpos : 0 < primePoolMass lo hi) (ι : Fin q ↪ Fin s)
    (E : (Fin q → ℕ) → Prop) :
    independentPrimePoolProbability (fun _ : Fin q => lo) (fun _ => hi) E =
      independentPrimePoolProbability (fun _ : Fin s => lo) (fun _ => hi)
        (fun p => E (fun i => p (ι i))) := by
  classical
  rw [independentPrimePoolProbability_finite, independentPrimePoolProbability_finite]
  let C := {j : Fin s // j ∉ Set.range ι}
  let A := PoolValue lo hi
  let w : A → ℝ := fun x => primePoolLaw lo hi x.1
  have hw : ∑ x : A, w x = 1 := primePoolLaw_sum_eq_one lo hi hpos
  have hctotal : ∑ z : C → A, ∏ j, w (z j) = 1 := by
    calc
      ∑ z : C → A, ∏ j, w (z j) = ∏ j : C, ∑ x : A, w x := by
        symm
        exact Fintype.prod_sum (fun (_ : C) (x : A) => w x)
      _ = 1 := by simp [hw]
  let split := slotTupleSplit ι A
  have hprod (p : Fin s → A) :
      (∏ j : Fin s, w (p j)) =
        (∏ i : Fin q, w ((split p).1 i)) * ∏ j : C, w ((split p).2 j) := by
    calc
      ∏ j : Fin s, w (p j) = ∏ k : Fin q ⊕ C, w (p (slotIndexEquiv ι k)) := by
        symm
        exact Fintype.prod_equiv (slotIndexEquiv ι)
          (fun k => w (p (slotIndexEquiv ι k))) (fun j => w (p j)) (by intro k; rfl)
      _ = (∏ i : Fin q, w (p (ι i))) * ∏ j : C, w (p j.1) := by
        rw [Fintype.prod_sum_type]
        have hleft : ∏ i : Fin q, w (p (slotIndexEquiv ι (Sum.inl i))) =
            ∏ i : Fin q, w (p (ι i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [slotIndexEquiv_inl]
        have hright : ∏ j : C, w (p (slotIndexEquiv ι (Sum.inr j))) =
            ∏ j : C, w (p j.1) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [slotIndexEquiv_inr]
        exact congrArg₂ (fun a b : ℝ => a * b) hleft hright
      _ = _ := by
        have hleft : ∏ i : Fin q, w ((split p).1 i) = ∏ i : Fin q, w (p (ι i)) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [slotTupleSplit_left]
        have hright : ∏ j : C, w ((split p).2 j) = ∏ j : C, w (p j.1) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [slotTupleSplit_right]
        exact congrArg₂ (fun a b : ℝ => a * b) hleft.symm hright.symm
  let f : (Fin s → A) → ℝ := fun p =>
    (∏ j, w (p j)) * if E (fun i => (p (ι i)).1) then 1 else 0
  let g : ((Fin q → A) × (C → A)) → ℝ := fun x =>
    ((∏ i, w (x.1 i)) * ∏ j, w (x.2 j)) *
      if E (fun i => (x.1 i).1) then 1 else 0
  have hsum : (∑ p : Fin s → A, f p) = ∑ x : (Fin q → A) × (C → A), g x := by
    apply Fintype.sum_equiv split f g
    intro p
    dsimp [f, g]
    rw [hprod p]
    have hleft : (split p).1 = fun i => p (ι i) := by
      funext i
      exact slotTupleSplit_left ι A p i
    simp [hleft]
  have hfactor :
      (∑ x : (Fin q → A) × (C → A), g x) =
        ∑ x : Fin q → A,
          (∏ i, w (x i)) * if E (fun i => (x i).1) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : Fin q → A, ∑ z : C → A, g (x, z)) =
          ∑ x : Fin q → A,
            ((∏ i, w (x i)) * if E (fun i => (x i).1) then 1 else 0) *
              (∑ z : C → A, ∏ j, w (z j)) := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          ∑ z : C → A, g (x, z) =
              ∑ z : C → A,
                ((∏ i, w (x i)) * if E (fun i => (x i).1) then 1 else 0) *
                  ∏ j, w (z j) := by
            apply Finset.sum_congr rfl
            intro z hz
            dsimp [g]
            ring
          _ = _ := by rw [← Finset.mul_sum]
      _ = _ := by simp [hctotal]
  simpa [f, g, w, A, C] using hfactor.symm.trans hsum.symm

private def harmonicSupport (X : ℕ) : Finset ℤ := Finset.Icc 0 (X ^ 2 : ℤ)

private lemma harmonicLaw_zero_of_not_mem_support {X W : ℕ} {y : ℤ}
    (hy : y ∉ harmonicSupport X) : harmonicLaw X W y = 0 := by
  classical
  unfold harmonicLaw
  split_ifs with h
  · apply False.elim (hy (Finset.mem_Icc.mpr ⟨h.1, ?_⟩))
    have hlt : y.toNat < X ^ 2 := h.2.2.1
    rw [← Int.toNat_of_nonneg h.1]
    exact_mod_cast hlt.le
  · rfl

private lemma harmonicPrimePairSummable {m : ℕ} (lo hi : Fin m → ℕ) (X W : ℕ)
    (F : (Fin m → ℕ) → ℤ → ℝ) :
    Summable (Function.uncurry fun p y =>
      independentPrimePoolMass lo hi p * (harmonicLaw X W y * F p y)) := by
  classical
  apply summable_of_ne_finset_zero
    (s := primeTupleSupport lo hi ×ˢ harmonicSupport X)
  intro x hx
  rcases x with ⟨p, y⟩
  change independentPrimePoolMass lo hi p * (harmonicLaw X W y * F p y) = 0
  by_cases hp' : p ∈ primeTupleSupport lo hi
  · have hy' : y ∉ harmonicSupport X := by
      intro hmem
      exact hx (Finset.mem_product.mpr ⟨hp', hmem⟩)
    rw [harmonicLaw_zero_of_not_mem_support hy']
    simp
  · rw [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp']
    simp

/-- Fubini for the finite-support prime-pool law and harmonic law. -/
theorem independentPrimePool_harmonic_tsum_comm {m : ℕ}
    (lo hi : Fin m → ℕ) (X W : ℕ) (F : (Fin m → ℕ) → ℤ → ℝ) :
    (∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
      ∑' y : ℤ, harmonicLaw X W y * F p y) =
    ∑' y : ℤ, harmonicLaw X W y *
      ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p * F p y := by
  classical
  have hsum := harmonicPrimePairSummable lo hi X W F
  calc
    (∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p *
      ∑' y : ℤ, harmonicLaw X W y * F p y) =
      ∑' p : Fin m → ℕ, ∑' y : ℤ,
        independentPrimePoolMass lo hi p * (harmonicLaw X W y * F p y) := by
          apply tsum_congr
          intro p
          rw [← tsum_mul_left]
    _ = ∑' y : ℤ, ∑' p : Fin m → ℕ,
        independentPrimePoolMass lo hi p * (harmonicLaw X W y * F p y) := hsum.tsum_comm.symm
    _ = ∑' y : ℤ, harmonicLaw X W y *
        ∑' p : Fin m → ℕ, independentPrimePoolMass lo hi p * F p y := by
          apply tsum_congr
          intro y
          calc
            (∑' p : Fin m → ℕ,
              independentPrimePoolMass lo hi p * (harmonicLaw X W y * F p y)) =
              ∑' p : Fin m → ℕ,
                harmonicLaw X W y * (independentPrimePoolMass lo hi p * F p y) := by
                  apply tsum_congr
                  intro p
                  ring
            _ = _ := tsum_mul_left

end
end HindmanSumsProducts
