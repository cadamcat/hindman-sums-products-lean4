import HindmanSumsProducts.Arithmetic.MasterScales

open scoped BigOperators Topology
open Filter

namespace HindmanSumsProducts
noncomputable section

/-- Smallest lower endpoint in one finite tuple of dyadic prime intervals. -/
noncomputable def smallestPrimeEndpoint {k : ℕ} (Y : Fin k → ℕ) : ℕ :=
  if h : (Finset.univ.image Y).Nonempty then (Finset.univ.image Y).min' h else 1

/-- Finite set of all dyadic lower endpoints in two independent prime tuples. -/
def roughEndpointSet {kF kG : ℕ} (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : Finset ℕ :=
  Finset.univ.image YF ∪ Finset.univ.image YG

/-- The smallest lower endpoint in two independent prime tuples (1 if both are constant). -/
noncomputable def roughSmallestEndpoint {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) : ℕ :=
  if h : (roughEndpointSet YF YG).Nonempty then
    (roughEndpointSet YF YG).min' h
  else 1

private lemma primePoolMass_nonneg (lo hi : ℕ) : 0 ≤ primePoolMass lo hi := by
  unfold primePoolMass
  apply Finset.sum_nonneg
  intro p hp
  exact one_div_nonneg.mpr (Nat.cast_nonneg p)

private lemma primePoolLaw_nonneg (lo hi p : ℕ) : 0 ≤ primePoolLaw lo hi p := by
  unfold primePoolLaw
  split_ifs with h
  · exact div_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg p)) (primePoolMass_nonneg lo hi)
  · simp

private lemma dyadicPrimePoolMass_pos (Y : ℕ) (hY : 2 ≤ Y) :
    0 < primePoolMass Y (2 * Y) := by
  obtain ⟨p, hp, hYp, hp2Y⟩ := Nat.exists_prime_lt_and_le_two_mul Y (by omega)
  have htwoY_not_prime : ¬ Nat.Prime (2 * Y) := by
    apply Nat.not_prime_mul (by norm_num) (by omega)
  have hp_lt : p < 2 * Y := by
    by_contra hnot
    have heq : p = 2 * Y := by omega
    exact htwoY_not_prime (heq ▸ hp)
  have hmem : p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hYp.le, hp_lt⟩, hp⟩
  unfold primePoolMass
  have hle := Finset.single_le_sum (f := fun q : ℕ => 1 / (q : ℝ))
    (fun q hq => by positivity) hmem
  have hp_pos : 0 < (1 / (p : ℝ)) := one_div_pos.mpr (by exact_mod_cast hp.pos)
  linarith

private lemma dyadicPrimePoolLaw_tsum_eq_one (Y : ℕ) (hY : 2 ≤ Y) :
    ∑' p : ℕ, primePoolLaw Y (2 * Y) p = 1 := by
  classical
  have hmpos := dyadicPrimePoolMass_pos Y hY
  have hms : primePoolMass Y (2 * Y) ≠ 0 := ne_of_gt hmpos
  calc
    ∑' p : ℕ, primePoolLaw Y (2 * Y) p =
        ∑ p ∈ Finset.Ico Y (2 * Y), primePoolLaw Y (2 * Y) p := by
          apply tsum_eq_sum (s := Finset.Ico Y (2 * Y))
          intro p hp
          simp only [primePoolLaw]
          split_ifs with h
          · exact False.elim (hp (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
          · rfl
    _ = ∑ p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
          (1 / (p : ℝ)) / primePoolMass Y (2 * Y) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p hp
          simp [primePoolLaw, Finset.mem_Ico.mp hp]
    _ = 1 := by
          rw [← Finset.sum_div]
          change primePoolMass Y (2 * Y) / primePoolMass Y (2 * Y) = 1
          exact div_self hms

private lemma dyadicPrimePoolLaw_le_one (Y : ℕ) (hY : 2 ≤ Y) (p : ℕ) :
    primePoolLaw Y (2 * Y) p ≤ 1 := by
  have hmpos := dyadicPrimePoolMass_pos Y hY
  unfold primePoolLaw
  split_ifs with h
  · rcases h with ⟨hlo, hhi, hp⟩
    have hmem : p ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime := by
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hlo, hhi⟩, hp⟩
    have hle := Finset.single_le_sum (f := fun q : ℕ => 1 / (q : ℝ))
      (fun q hq => by positivity) hmem
    have hden : 0 < primePoolMass Y (2 * Y) := hmpos
    rw [div_le_one hden]
    exact hle
  · simp

private lemma dyadic_log_ratio_le_two {L Y : ℕ} (hL : 2 ≤ L) (hLY : L ≤ Y) :
    Real.log (Y : ℝ) / Y ≤ 2 * (Real.log (L : ℝ) / L) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLYreal : (L : ℝ) ≤ Y := by exact_mod_cast hLY
  by_cases hLtwo : L = 2
  · subst L
    by_cases hYtwo : Y = 2
    · subst Y
      have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      nlinarith
    · have hYthree : (3 : ℝ) ≤ Y := by
        have : 2 < Y := by omega
        exact_mod_cast this
      have hexp3 : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
      have hexpY : Real.exp 1 ≤ (Y : ℝ) := hexp3.trans (by exact_mod_cast hYthree)
      have hanti := Real.log_div_self_antitoneOn hexp3 hexpY hYthree
      have hlog3 : Real.log (3 : ℝ) ≤ 3 * Real.log 2 := by
        calc
          Real.log 3 ≤ Real.log (2 ^ 3 : ℝ) := Real.log_le_log (by norm_num) (by norm_num)
          _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
      have hratio : Real.log (3 : ℝ) / 3 ≤ Real.log 2 :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by nlinarith)
      calc
        Real.log (Y : ℝ) / Y ≤ Real.log 2 := hanti.trans hratio
        _ = 2 * (Real.log 2 / 2) := by ring
  · have hLthree : (3 : ℝ) ≤ L := by
      have : 3 ≤ L := by omega
      exact_mod_cast this
    have hexpL : Real.exp 1 ≤ (L : ℝ) := Real.exp_one_lt_three.le.trans hLthree
    have hexpY : Real.exp 1 ≤ (Y : ℝ) := hexpL.trans hLYreal
    have hanti := Real.log_div_self_antitoneOn hexpL hexpY hLYreal
    have hlogL : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    have hratio : 0 ≤ Real.log (L : ℝ) / L := div_nonneg hlogL (by positivity)
    nlinarith

private lemma dyadicPrimePoolLaw_global_atom_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (Y p : ℕ), 2 ≤ Y →
      primePoolLaw Y (2 * Y) p ≤ A * Real.log (Y : ℝ) / Y := by
  obtain ⟨C, c, hC, hc, hEventual⟩ :=
    HindmanSumsProducts.Arithmetic.Outside.dyadic_harmonic_prime_mass_and_atom_bound
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hEventual
  let A : ℝ := C + (Y₀ : ℝ) / Real.log 2 + 1
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro Y p hY
    by_cases hlarge : Y₀ ≤ Y
    · by_cases hmem : Y ≤ p ∧ p < 2 * Y ∧ p.Prime
      · have hout := (hY₀ Y hlarge).2.2 p hmem.1 hmem.2.1 hmem.2.2
        have hratio : 0 ≤ Real.log (Y : ℝ) / Y :=
          div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))) (by positivity)
        have hCA : C ≤ A := by
          have hterm : 0 ≤ (Y₀ : ℝ) / Real.log 2 :=
            div_nonneg (Nat.cast_nonneg Y₀) hlog2pos.le
          dsimp [A]
          linarith
        calc
          primePoolLaw Y (2 * Y) p ≤ C * Real.log (Y : ℝ) / Y := hout
          _ = C * (Real.log (Y : ℝ) / Y) := by ring
          _ ≤ A * (Real.log (Y : ℝ) / Y) := mul_le_mul_of_nonneg_right hCA hratio
          _ = A * Real.log (Y : ℝ) / Y := by ring
      · have hzero : primePoolLaw Y (2 * Y) p = 0 := by
          simp [primePoolLaw, hmem]
        rw [hzero]
        have hlog : 0 ≤ Real.log (Y : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
        positivity
    · have hY₀ : (Y₀ : ℝ) / Real.log 2 ≤ A := by dsimp [A]; linarith
      have hYlt : (Y : ℝ) < Y₀ := by exact_mod_cast (lt_of_not_ge hlarge)
      have hYreal : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
      have hY₀real : (0 : ℝ) < Y₀ := by exact_mod_cast (by omega : 0 < Y₀)
      have hlogY : Real.log 2 ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hY)
      have hYfrac : 1 ≤ (Y₀ : ℝ) / Y :=
        (le_div_iff₀ hYreal).2 (by simpa using hYlt.le)
      have hlogfrac : 1 ≤ Real.log (Y : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2pos).2 (by simpa using hlogY)
      have hprod : 1 ≤ ((Y₀ : ℝ) / Y) * (Real.log (Y : ℝ) / Real.log 2) :=
        one_le_mul_of_one_le_of_one_le hYfrac hlogfrac
      have hratio : 1 ≤ ((Y₀ : ℝ) / Real.log 2) * (Real.log (Y : ℝ) / Y) := by
        convert hprod using 1 <;> field_simp <;> ring
      have hratio_nonneg : 0 ≤ Real.log (Y : ℝ) / Y :=
        div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))) (by positivity)
      have hbound : 1 ≤ A * (Real.log (Y : ℝ) / Y) :=
        le_trans hratio (mul_le_mul_of_nonneg_right hY₀ hratio_nonneg)
      exact (dyadicPrimePoolLaw_le_one Y hY p).trans (by
        convert hbound using 1 <;> ring)

private lemma smallestPrimeEndpoint_le {k : ℕ} (Y : Fin k → ℕ) (i : Fin k) :
    smallestPrimeEndpoint Y ≤ Y i := by
  unfold smallestPrimeEndpoint
  split_ifs with h
  · exact (Finset.univ.image Y).min'_le (Y i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · exact False.elim (h ⟨Y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

private lemma smallestPrimeEndpoint_ge_two {k : ℕ} (Y : Fin k → ℕ)
    (hY : ∀ i, 2 ≤ Y i) (i : Fin k) :
    2 ≤ smallestPrimeEndpoint Y := by
  unfold smallestPrimeEndpoint
  split_ifs with h
  · rw [Finset.le_min'_iff]
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨j, _, rfl⟩
    exact hY j
  · exact False.elim (h ⟨Y i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

private lemma lower_le_smallestPrimeEndpoint {k : ℕ} (Y : Fin k → ℕ)
    (L : ℕ) (hk : 0 < k) (hY : ∀ i, L ≤ Y i) :
    L ≤ smallestPrimeEndpoint Y := by
  classical
  unfold smallestPrimeEndpoint
  split_ifs with hS
  · rw [Finset.le_min'_iff]
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
    exact hY i
  · exact False.elim (hS ⟨Y ⟨0, hk⟩,
      Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩)

private lemma roughSmallestEndpoint_le_left {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (i : Fin kF) :
    roughSmallestEndpoint YF YG ≤ YF i := by
  let S := roughEndpointSet YF YG
  have hi : YF i ∈ S := Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hS : S.Nonempty := ⟨YF i, hi⟩
  change (if h : S.Nonempty then S.min' h else 1) ≤ YF i
  rw [dif_pos hS]
  exact S.min'_le (YF i) hi

private lemma roughSmallestEndpoint_le_right {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (j : Fin kG) :
    roughSmallestEndpoint YF YG ≤ YG j := by
  let S := roughEndpointSet YF YG
  have hj : YG j ∈ S := Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hS : S.Nonempty := ⟨YG j, hj⟩
  change (if h : S.Nonempty then S.min' h else 1) ≤ YG j
  rw [dif_pos hS]
  exact S.min'_le (YG j) hj

private lemma roughSmallestEndpoint_ge_two {kF kG : ℕ}
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ)
    (hYF : ∀ i, 2 ≤ YF i) (hYG : ∀ j, 2 ≤ YG j)
    (hvars : 0 < kF ∨ 0 < kG) :
    2 ≤ roughSmallestEndpoint YF YG := by
  let S := roughEndpointSet YF YG
  have hS : S.Nonempty := by
    rcases hvars with hkF | hkG
    · exact ⟨YF ⟨0, hkF⟩, Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨⟨0, hkF⟩, Finset.mem_univ _, rfl⟩)⟩
    · exact ⟨YG ⟨0, hkG⟩, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨⟨0, hkG⟩, Finset.mem_univ _, rfl⟩)⟩
  change 2 ≤ if h : S.Nonempty then S.min' h else 1
  rw [dif_pos hS, Finset.le_min'_iff]
  intro a ha
  rcases Finset.mem_union.mp ha with hleft | hright
  · rcases Finset.mem_image.mp hleft with ⟨i, _, rfl⟩
    exact hYF i
  · rcases Finset.mem_image.mp hright with ⟨j, _, rfl⟩
    exact hYG j

private lemma finSuccEquiv_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    {n : ℕ} (f : R →+* S) (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv S n (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f) (MvPolynomial.finSuccEquiv R n P) := by
  let mapTail : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S :=
    MvPolynomial.map f
  let f₁ : MvPolynomial (Fin (n + 1)) R →+*
      Polynomial (MvPolynomial (Fin n) S) :=
    (MvPolynomial.finSuccEquiv S n).toRingEquiv.toRingHom.comp (MvPolynomial.map f)
  let f₂ : MvPolynomial (Fin (n + 1)) R →+*
      Polynomial (MvPolynomial (Fin n) S) :=
    (Polynomial.mapRingHom mapTail).comp
      (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom
  have hhom : f₁ = f₂ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f₁, f₂, mapTail, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp [f₁, f₂, mapTail, MvPolynomial.finSuccEquiv_apply]
      · intro j
        simp [f₁, f₂, mapTail, MvPolynomial.finSuccEquiv_apply]
  simpa [f₁, f₂] using congrArg (fun h => h P) hhom

private lemma finSuccEquiv_specialized_coeff {R S : Type*} [CommSemiring R] [CommSemiring S]
    {n : ℕ} (f : R →+* S) (z : Fin n → S)
    (P : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    (Polynomial.map (MvPolynomial.eval z)
      (MvPolynomial.finSuccEquiv S n (MvPolynomial.map f P))).coeff d =
    MvPolynomial.eval z
      (MvPolynomial.map f ((MvPolynomial.finSuccEquiv R n P).coeff d)) := by
  rw [finSuccEquiv_map]
  rw [Polynomial.map_map]
  simp [Polynomial.coeff_map]

private lemma totalDegree_fin_one {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 1) R) : P.totalDegree = P.degreeOf 0 := by
  rw [MvPolynomial.totalDegree, MvPolynomial.degreeOf_eq_sup]
  apply Finset.sup_congr rfl
  intro s hs
  have hsupp : s.support ⊆ ({0} : Finset (Fin 1)) := by
    intro i hi
    have h : i = 0 := Subsingleton.elim i 0
    simpa [h]
  calc
    s.sum (fun _ e => e) =
        ∑ i ∈ ({0} : Finset (Fin 1)), (fun _ e => e) i (s i) :=
      Finsupp.sum_of_support_subset _ hsupp _ (by simp)
    _ = s 0 := by simp

private lemma finSuccEquiv_toMvPolynomial_fin_one {R : Type*} [CommSemiring R]
    (Q : Polynomial R) :
    MvPolynomial.finSuccEquiv R 0 (Polynomial.toMvPolynomial (0 : Fin 1) Q) =
      Polynomial.map MvPolynomial.C Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial d a =>
      simp [Polynomial.toMvPolynomial, MvPolynomial.finSuccEquiv_apply,
        Polynomial.C_mul_X_pow_eq_monomial]

private lemma totalDegree_toMvPolynomial_fin_one {R : Type*} [CommSemiring R]
    (Q : Polynomial R) :
    (Polynomial.toMvPolynomial (0 : Fin 1) Q).totalDegree = Q.natDegree := by
  rw [totalDegree_fin_one, ← MvPolynomial.natDegree_finSuccEquiv,
    finSuccEquiv_toMvPolynomial_fin_one]
  exact Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.C_injective (Fin 0) R) Q

private def finOneFunEquiv (α : Type*) : (Fin 1 → α) ≃ α where
  toFun f := f 0
  invFun a _ := a
  left_inv f := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [hi]
  right_inv _ := rfl

/-- Probability of a polynomial zero under independent harmonic prime samples in dyadic
intervals; this is the first estimate in `lem:rough-coprimality`. -/
theorem polynomial_zero_dyadic_prime_bound {k : ℕ}
    (F : IntegerPolynomial k) (hF : F ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : Fin k → ℕ, (∀ i, 2 ≤ Y i) →
      independentPrimePoolProbability Y (fun i => 2 * Y i)
        (fun p => evalIntegerPolynomial F (fun i => (p i : ℤ)) = 0) ≤
      C * Real.log (smallestPrimeEndpoint Y : ℝ) /
        smallestPrimeEndpoint Y := by
  obtain ⟨A, hA, hAtom⟩ := dyadicPrimePoolLaw_global_atom_bound
  let d : ℝ := (MvPolynomial.totalDegree F : ℝ)
  let C : ℝ := (d + 1) * (2 * A)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro Y hY
    let L := smallestPrimeEndpoint Y
    let α : ℝ := 2 * A * (Real.log (L : ℝ) / L)
    have hLone : 1 ≤ L := by
      by_cases hk : k = 0
      · subst k
        simp [L, smallestPrimeEndpoint]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        exact (by norm_num : 1 ≤ 2).trans
          (smallestPrimeEndpoint_ge_two Y hY ⟨0, hkpos⟩)
    have hlogL : 0 ≤ Real.log (L : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hLone)
    have hratio : 0 ≤ Real.log (L : ℝ) / L := div_nonneg hlogL (by positivity)
    have hmax : ∀ i p, primePoolLaw (Y i) (2 * Y i) p ≤ α := by
      intro i p
      have hYi := hAtom (Y i) p (hY i)
      have hratioYi := dyadic_log_ratio_le_two
        (smallestPrimeEndpoint_ge_two Y hY i) (smallestPrimeEndpoint_le Y i)
      calc
        primePoolLaw (Y i) (2 * Y i) p ≤ A * Real.log (Y i : ℝ) / Y i := hYi
        _ = A * (Real.log (Y i : ℝ) / Y i) := by ring
        _ ≤ A * (2 * (Real.log (L : ℝ) / L)) :=
          mul_le_mul_of_nonneg_left hratioYi hA.le
        _ = α := by dsimp [α]; ring
    have hprob : ∀ i, ∑' p : ℕ, primePoolLaw (Y i) (2 * Y i) p = 1 := by
      intro i
      exact dyadicPrimePoolLaw_tsum_eq_one (Y i) (hY i)
    have hgrid := polynomial_zero_product_grid_bound F hF
      (fun i p => primePoolLaw (Y i) (2 * Y i) p) α
      (fun i p => primePoolLaw_nonneg (Y i) (2 * Y i) p) hmax hprob
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have halpha : 0 ≤ α := by dsimp [α]; positivity
    have hbound : d * α ≤ C * (Real.log (L : ℝ) / L) := by
      calc
        d * α ≤ (d + 1) * α := by nlinarith [hd, halpha]
        _ = C * (Real.log (L : ℝ) / L) := by dsimp [C, α]; ring
    have hbound' : (MvPolynomial.totalDegree F : ℝ) * α ≤
        C * Real.log (L : ℝ) / L := by
      convert hbound using 1 <;> ring
    have hbound'' : (MvPolynomial.totalDegree F : ℝ) * α ≤
        C * Real.log (smallestPrimeEndpoint Y : ℝ) / smallestPrimeEndpoint Y := by
      simpa [L] using hbound'
    simpa [independentPrimePoolProbability, independentPrimePoolMass, α, L] using
      hgrid.trans hbound''

private lemma polynomial_zero_dyadic_prime_bound_sqrt {k : ℕ}
    (F : IntegerPolynomial k) (hF : F ≠ 0) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Y : Fin k → ℕ) (L : ℕ), 2 ≤ L → (∀ i, L ≤ Y i) →
        independentPrimePoolProbability Y (fun i => 2 * Y i)
          (fun p => evalIntegerPolynomial F (fun i => (p i : ℤ)) = 0) ≤
          C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
  obtain ⟨C₀, hC₀, hzero⟩ := polynomial_zero_dyadic_prime_bound F hF
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro Y L hL hY
  have hYtwo : ∀ i, 2 ≤ Y i := fun i => le_trans hL (hY i)
  have hzero' := hzero Y hYtwo
  have hmin : L ≤ smallestPrimeEndpoint Y :=
    lower_le_smallestPrimeEndpoint Y L hk hY
  have hratio := dyadic_log_ratio_le_two hL hmin
  have hlogL : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  have hsqrtLpos : 0 < Real.sqrt (L : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (by omega : 0 < L)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hsqrtLe : Real.sqrt (L : ℝ) ≤ (L : ℝ) := by
    rw [Real.sqrt_le_left hLpos.le]
    exact_mod_cast (by nlinarith [hL] : L ≤ L ^ 2)
  have hratio' : Real.log (L : ℝ) / L ≤
      Real.log (L : ℝ) / Real.sqrt (L : ℝ) :=
    div_le_div_of_nonneg_left hlogL hsqrtLpos hsqrtLe
  calc
    _ ≤ C₀ * Real.log (smallestPrimeEndpoint Y : ℝ) /
          smallestPrimeEndpoint Y := hzero'
    _ = C₀ * (Real.log (smallestPrimeEndpoint Y : ℝ) /
          smallestPrimeEndpoint Y) := by ring
    _ ≤ C₀ * (2 * (Real.log (L : ℝ) / L)) :=
          mul_le_mul_of_nonneg_left hratio hC₀.le
    _ = 2 * C₀ * (Real.log (L : ℝ) / L) := by ring
    _ ≤ 2 * C₀ * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio' (by positivity)
    _ = _ := by ring

private def primeTupleSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private lemma primeTupleSupport_coordinate {m : ℕ}
    (lo hi : Fin m → ℕ) (x : Fin m → ℕ)
    (hx : x ∈ primeTupleSupport lo hi) (i : Fin m) :
    x i ∈ Finset.Ico (lo i) (hi i) := by
  exact Fintype.mem_piFinset.mp hx i

private lemma independentPrimePoolMass_zero_of_not_mem_support {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hp : p ∉ primeTupleSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin m, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [primeTupleSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private lemma independentPrimePoolMass_summable {m : ℕ}
    (lo hi : Fin m → ℕ) : Summable (independentPrimePoolMass lo hi) := by
  apply summable_of_ne_finset_zero (s := primeTupleSupport lo hi)
  intro p hp
  exact independentPrimePoolMass_zero_of_not_mem_support lo hi p hp

private lemma independentPrimePoolProbability_summable {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    Summable (fun p => independentPrimePoolMass lo hi p * if E p then 1 else 0) := by
  classical
  apply summable_of_ne_finset_zero (s := primeTupleSupport lo hi)
  intro p hp
  rw [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp]
  simp

private lemma independentPrimePairOuter_summable {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    Summable (fun x => independentPrimePoolMass loF hiF x *
      (∑' y : Fin kG → ℕ,
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) := by
  classical
  apply summable_of_ne_finset_zero (s := primeTupleSupport loF hiF)
  intro x hx
  rw [independentPrimePoolMass_zero_of_not_mem_support loF hiF x hx]
  simp

private lemma independentPrimePairProbability_eq_sum_support {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    independentPrimePairProbability loF hiF loG hiG E =
      ∑ x ∈ primeTupleSupport loF hiF,
        ∑ y ∈ primeTupleSupport loG hiG,
          independentPrimePoolMass loF hiF x *
            independentPrimePoolMass loG hiG y * (if E x y then 1 else 0) := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  let Sx := primeTupleSupport loF hiF
  let Sy := primeTupleSupport loG hiG
  unfold independentPrimePairProbability
  rw [tsum_eq_sum (s := Sx)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [tsum_eq_sum (s := Sy)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    · intro y hy
      rw [independentPrimePoolMass_zero_of_not_mem_support loG hiG y hy]
      simp
  · intro x hx
    rw [independentPrimePoolMass_zero_of_not_mem_support loF hiF x hx]
    simp

private lemma independentPrimePairProbability_swap {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    independentPrimePairProbability loF hiF loG hiG E =
      independentPrimePairProbability loG hiG loF hiF (fun y x => E x y) := by
  classical
  rw [independentPrimePairProbability_eq_sum_support loF hiF loG hiG E,
    independentPrimePairProbability_eq_sum_support loG hiG loF hiF (fun y x => E x y)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  ring

private lemma independentPrimePairProbability_product {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (EF : (Fin kF → ℕ) → Prop) (EG : (Fin kG → ℕ) → Prop)
    [DecidablePred EF] [DecidablePred EG] :
    independentPrimePairProbability loF hiF loG hiG (fun x y => EF x ∧ EG y) =
      independentPrimePoolProbability loF hiF EF *
        independentPrimePoolProbability loG hiG EG := by
  classical
  let f : (Fin kF → ℕ) → ℝ := fun x =>
    independentPrimePoolMass loF hiF x * if EF x then 1 else 0
  let g : (Fin kG → ℕ) → ℝ := fun y =>
    independentPrimePoolMass loG hiG y * if EG y then 1 else 0
  have hf : Summable f := by
    apply summable_of_ne_finset_zero (s := primeTupleSupport loF hiF)
    intro x hx
    change independentPrimePoolMass loF hiF x * (if EF x then 1 else 0) = 0
    rw [independentPrimePoolMass_zero_of_not_mem_support loF hiF x hx]
    simp
  have hg : Summable g := by
    apply summable_of_ne_finset_zero (s := primeTupleSupport loG hiG)
    intro y hy
    change independentPrimePoolMass loG hiG y * (if EG y then 1 else 0) = 0
    rw [independentPrimePoolMass_zero_of_not_mem_support loG hiG y hy]
    simp
  calc
    independentPrimePairProbability loF hiF loG hiG (fun x y => EF x ∧ EG y) =
        ∑' x, f x * ∑' y, g y := by
          unfold independentPrimePairProbability
          apply tsum_congr
          intro x
          by_cases hEx : EF x
          · simp [f, g, hEx]
          · simp [f, g, hEx]
    _ = (∑' x, f x) * (∑' y, g y) := hf.tsum_mul_right _
    _ = independentPrimePoolProbability loF hiF EF *
        independentPrimePoolProbability loG hiG EG := by
          simp [f, g, independentPrimePoolProbability]

private def roughTupleReindex {m : ℕ} (e : Equiv.Perm (Fin m)) :
    (Fin m → ℕ) ≃ (Fin m → ℕ) where
  toFun x i := x (e.symm i)
  invFun x i := x (e i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

private lemma independentPrimePoolMass_reindex {m : ℕ}
    (e : Equiv.Perm (Fin m)) (lo hi : Fin m → ℕ) (x : Fin m → ℕ) :
    independentPrimePoolMass (fun i => lo (e i)) (fun i => hi (e i)) x =
      independentPrimePoolMass lo hi (roughTupleReindex e x) := by
  unfold independentPrimePoolMass
  apply Fintype.prod_equiv e
  intro i
  simp [roughTupleReindex]

private lemma independentPrimePoolProbability_reindex {m : ℕ}
    (e : Equiv.Perm (Fin m)) (lo hi : Fin m → ℕ)
    (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    independentPrimePoolProbability (fun i => lo (e i)) (fun i => hi (e i))
      (fun x => E (roughTupleReindex e x)) =
      independentPrimePoolProbability lo hi E := by
  classical
  letI : DecidablePred E := fun x => Classical.propDecidable (E x)
  unfold independentPrimePoolProbability
  calc
    _ = ∑' x : Fin m → ℕ,
        independentPrimePoolMass lo hi (roughTupleReindex e x) *
          if E (roughTupleReindex e x) then 1 else 0 := by
            apply tsum_congr
            intro x
            rw [independentPrimePoolMass_reindex]
    _ = ∑' x : Fin m → ℕ,
        independentPrimePoolMass lo hi x * if E x then 1 else 0 := by
            simpa using (roughTupleReindex e).tsum_eq
              (fun x => independentPrimePoolMass lo hi x * if E x then 1 else 0)

private lemma independentPrimePairProbability_reindex_left {kF kG : ℕ}
    (e : Equiv.Perm (Fin kF)) (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    independentPrimePairProbability (fun i => loF (e i)) (fun i => hiF (e i)) loG hiG
      (fun x y => E (roughTupleReindex e x) y) =
      independentPrimePairProbability loF hiF loG hiG E := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  let I : (Fin kF → ℕ) ≃ (Fin kF → ℕ) := roughTupleReindex e
  unfold independentPrimePairProbability
  calc
    _ = ∑' x : Fin kF → ℕ,
        independentPrimePoolMass loF hiF (I x) *
          (∑' y : Fin kG → ℕ,
            independentPrimePoolMass loG hiG y * if E (I x) y then 1 else 0) := by
              apply tsum_congr
              intro x
              rw [independentPrimePoolMass_reindex]
    _ = ∑' x : Fin kF → ℕ,
        independentPrimePoolMass loF hiF x *
          (∑' y : Fin kG → ℕ,
            independentPrimePoolMass loG hiG y * if E x y then 1 else 0) := by
              simpa [I] using I.tsum_eq (fun x => independentPrimePoolMass loF hiF x *
              (∑' y : Fin kG → ℕ,
                  independentPrimePoolMass loG hiG y * if E x y then 1 else 0))

private lemma independentPrimePairProbability_reindex_right {kF kG : ℕ}
    (e : Equiv.Perm (Fin kG)) (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    independentPrimePairProbability loF hiF (fun j => loG (e j)) (fun j => hiG (e j))
      (fun x y => E x (roughTupleReindex e y)) =
      independentPrimePairProbability loF hiF loG hiG E := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  let I : (Fin kG → ℕ) ≃ (Fin kG → ℕ) := roughTupleReindex e
  unfold independentPrimePairProbability
  apply tsum_congr
  intro x
  congr 1
  calc
    _ = ∑' y : Fin kG → ℕ,
          independentPrimePoolMass loG hiG (I y) * if E x (I y) then 1 else 0 := by
            apply tsum_congr
            intro y
            rw [independentPrimePoolMass_reindex]
    _ = ∑' y : Fin kG → ℕ,
          independentPrimePoolMass loG hiG y * if E x y then 1 else 0 := by
            simpa [I] using I.tsum_eq (fun y =>
              independentPrimePoolMass loG hiG y * if E x y then 1 else 0)

private lemma independentPrimePairProbability_reindex_both {kF kG : ℕ}
    (eF : Equiv.Perm (Fin kF)) (eG : Equiv.Perm (Fin kG))
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) [DecidableRel E] :
    independentPrimePairProbability (fun i => loF (eF i)) (fun i => hiF (eF i))
      (fun j => loG (eG j)) (fun j => hiG (eG j))
      (fun x y => E (roughTupleReindex eF x) (roughTupleReindex eG y)) =
      independentPrimePairProbability loF hiF loG hiG E := by
  classical
  calc
    _ = independentPrimePairProbability loF hiF
          (fun j => loG (eG j)) (fun j => hiG (eG j))
          (fun x y => E x (roughTupleReindex eG y)) :=
        independentPrimePairProbability_reindex_left eF loF hiF
          (fun j => loG (eG j)) (fun j => hiG (eG j))
          (fun x y => E x (roughTupleReindex eG y))
    _ = independentPrimePairProbability loF hiF loG hiG E :=
        independentPrimePairProbability_reindex_right eG loF hiF loG hiG E

private lemma totalDegree_rename_perm {m : ℕ} (e : Equiv.Perm (Fin m))
    (P : IntegerPolynomial m) :
    (MvPolynomial.rename e P).totalDegree = P.totalDegree := by
  apply le_antisymm
  · exact MvPolynomial.totalDegree_rename_le e P
  · have h := MvPolynomial.totalDegree_rename_le e.symm (MvPolynomial.rename e P)
    simpa [MvPolynomial.rename_rename] using h

private lemma evalIntegerPolynomial_roughTupleReindex {m : ℕ}
    (e : Equiv.Perm (Fin m)) (P : IntegerPolynomial m) (x : Fin m → ℕ) :
    evalIntegerPolynomial P (fun i => (roughTupleReindex e x i : ℤ)) =
      evalIntegerPolynomial (MvPolynomial.rename e.symm P) (fun i => (x i : ℤ)) := by
  change MvPolynomial.eval (fun i => ((x (e.symm i) : ℕ) : ℤ)) P =
    MvPolynomial.eval (fun i => (x i : ℤ)) (MvPolynomial.rename e.symm P)
  rw [MvPolynomial.eval_rename]
  rfl

private def roughMoveMainPerm {m : ℕ} (zero i : Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap zero i

private lemma roughMoveMain_active_endpoint {m : ℕ} (P : IntegerPolynomial m)
    (Y : Fin m → ℕ) (zero i : Fin m) (hi : i ∈ P.vars)
    (hmax : ∀ j ∈ P.vars, Y j ≤ Y i) :
    zero ∈ (MvPolynomial.rename (roughMoveMainPerm zero i).symm P).vars ∧
      ∀ j ∈ (MvPolynomial.rename (roughMoveMainPerm zero i).symm P).vars,
        Y (roughMoveMainPerm zero i j) ≤ Y i := by
  classical
  let e := roughMoveMainPerm zero i
  let P' := MvPolynomial.rename e.symm P
  have heq : P = MvPolynomial.rename e P' := by
    dsimp [P']
    rw [MvPolynomial.rename_rename]
    simp [e]
  have hmem : i ∈ (MvPolynomial.rename e P').vars := by
    rw [← heq]
    exact hi
  obtain ⟨j, hj, hji⟩ := MvPolynomial.mem_vars_rename e P' hmem
  have hjzero : j = zero := by
    have hji' : j = e.symm i := by simpa using congrArg e.symm hji
    have he : e.symm i = zero := by
      change (Equiv.swap zero i).symm i = zero
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    exact hji'.trans he
  constructor
  · simpa [P', hjzero] using hj
  · intro k hk
    obtain ⟨a, ha, hak⟩ := MvPolynomial.mem_vars_rename e.symm P hk
    have hae : a = e k := by
      have h := congrArg e hak
      simpa using h
    rw [← hae]
    exact hmax a ha

private lemma mvPolynomial_vars_nonempty_of_totalDegree_pos {m : ℕ}
    (P : IntegerPolynomial m) (hdeg : 0 < P.totalDegree) : P.vars.Nonempty := by
  by_contra hvars
  have hvarsEmpty : P.vars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hvars
  have hconst := (MvPolynomial.vars_eq_empty_iff_eq_C).mp hvarsEmpty
  rw [hconst, MvPolynomial.totalDegree_C] at hdeg
  omega

private lemma exists_max_active_endpoint {m : ℕ} (P : IntegerPolynomial m)
    (Y : Fin m → ℕ) (hvars : P.vars.Nonempty) :
    ∃ i, i ∈ P.vars ∧ ∀ j ∈ P.vars, Y j ≤ Y i := by
  classical
  let S := P.vars.image Y
  have hS : S.Nonempty := Finset.image_nonempty.mpr hvars
  rcases Finset.mem_image.mp (Finset.max'_mem S hS) with ⟨i, hi, hYi⟩
  refine ⟨i, hi, ?_⟩
  intro j hj
  have hle := S.le_max' (Y j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  simpa [S, hYi]

private def roughMainDegree {n : ℕ} (P : IntegerPolynomial (n + 1)) : ℕ :=
  P.degreeOf 0

private def roughMainCoefficientTail {n : ℕ} (P : IntegerPolynomial (n + 1)) :
    IntegerPolynomial n :=
  (MvPolynomial.finSuccEquiv ℤ n P).coeff (roughMainDegree P)

private def roughMainCoefficient {n : ℕ} (P : IntegerPolynomial (n + 1)) :
    IntegerPolynomial (n + 1) :=
  MvPolynomial.rename Fin.succ (roughMainCoefficientTail P)

private lemma eval_roughMainCoefficient {n : ℕ} (P : IntegerPolynomial (n + 1))
    (x : Fin (n + 1) → ℕ) :
    evalIntegerPolynomial (roughMainCoefficient P) (fun i => (x i : ℤ)) =
      evalIntegerPolynomial (roughMainCoefficientTail P)
        (fun j => (x j.succ : ℤ)) := by
  change MvPolynomial.eval (fun i => (x i : ℤ))
      (MvPolynomial.rename Fin.succ (roughMainCoefficientTail P)) = _
  rw [MvPolynomial.eval_rename]
  rfl

private lemma roughMainCoefficientTail_ne_zero {n : ℕ}
    (P : IntegerPolynomial (n + 1)) (hP : P ≠ 0) :
    roughMainCoefficientTail P ≠ 0 := by
  have hpoly : MvPolynomial.finSuccEquiv ℤ n P ≠ 0 := by
    intro h
    apply hP
    exact (MvPolynomial.finSuccEquiv ℤ n).injective h
  have hcoeff : (MvPolynomial.finSuccEquiv ℤ n P).coeff
      (MvPolynomial.finSuccEquiv ℤ n P).natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hpoly
  simpa [roughMainCoefficientTail, roughMainDegree,
    MvPolynomial.natDegree_finSuccEquiv] using hcoeff

private lemma roughMainCoefficient_ne_zero {n : ℕ}
    (P : IntegerPolynomial (n + 1)) (hP : P ≠ 0) :
    roughMainCoefficient P ≠ 0 := by
  intro h
  have htail : roughMainCoefficientTail P = 0 :=
    MvPolynomial.rename_injective Fin.succ (Fin.succ_injective n) h
  exact roughMainCoefficientTail_ne_zero P hP htail

private lemma roughMainCoefficient_totalDegree_lt {n : ℕ}
    (P : IntegerPolynomial (n + 1)) (hP : P ≠ 0) (hd : 0 < P.degreeOf 0) :
    (roughMainCoefficient P).totalDegree < P.totalDegree := by
  have htail := roughMainCoefficientTail_ne_zero P hP
  have hcoeff := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P (P.degreeOf 0) htail
  have hrename := MvPolynomial.totalDegree_rename_le Fin.succ
    (roughMainCoefficientTail P)
  calc
    (roughMainCoefficient P).totalDegree ≤
        (roughMainCoefficientTail P).totalDegree := hrename
    _ < P.totalDegree := by
      have hcoeff' : (roughMainCoefficientTail P).totalDegree + P.degreeOf 0 ≤
          P.totalDegree := by
        simpa [roughMainCoefficientTail, roughMainDegree] using hcoeff
      omega

private lemma roughMainDegree_map_eq {n p : ℕ} [NeZero p]
    (P : IntegerPolynomial (n + 1))
    (hcoeff : MvPolynomial.map (Int.castRingHom (ZMod p))
      (roughMainCoefficientTail P) ≠ 0) :
    (MvPolynomial.map (Int.castRingHom (ZMod p)) P).degreeOf 0 = P.degreeOf 0 := by
  let cast : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Ppoly : Polynomial (MvPolynomial (Fin n) ℤ) := MvPolynomial.finSuccEquiv ℤ n P
  have hdeg : Ppoly.natDegree = P.degreeOf 0 := by
    dsimp [Ppoly]
    exact MvPolynomial.natDegree_finSuccEquiv P
  have hlc : Ppoly.leadingCoeff = roughMainCoefficientTail P := by
    rw [Polynomial.leadingCoeff, hdeg]
    rfl
  have hmapLC : MvPolynomial.map cast Ppoly.leadingCoeff ≠ 0 := by
    rw [hlc]
    exact hcoeff
  have hmapDeg := Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    (MvPolynomial.map cast) hmapLC
  have hcomm := finSuccEquiv_map cast P
  rw [← MvPolynomial.natDegree_finSuccEquiv (MvPolynomial.map cast P)]
  rw [hcomm, hmapDeg, hdeg]

private def roughCoefficientMass {m : ℕ} (P : IntegerPolynomial m) : ℕ :=
  ∑ s ∈ P.support, (P.coeff s).natAbs

private lemma int_natAbs_cast_real (a : ℤ) :
    (a.natAbs : ℝ) = |(a : ℝ)| := by
  rw [← Int.cast_abs]
  have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs a)
  simpa using h

private lemma evalIntegerPolynomial_natAbs_le_of_vars {m : ℕ}
    (P : IntegerPolynomial m) (x : Fin m → ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hactive : ∀ i ∈ P.vars, x i ≤ M) :
    (evalIntegerPolynomial P (fun i => (x i : ℤ))).natAbs ≤
      roughCoefficientMass P * M ^ P.totalDegree := by
  classical
  let f : (Fin m →₀ ℕ) → ℝ := fun s =>
    (P.coeff s : ℝ) * ∏ i ∈ s.support, (x i : ℝ) ^ s i
  have hevalInt : evalIntegerPolynomial P (fun i => (x i : ℤ)) =
      ∑ s ∈ P.support, P.coeff s * ∏ i ∈ s.support,
        (x i : ℤ) ^ s i := by
    rw [evalIntegerPolynomial, MvPolynomial.eval_eq]
  have hevalReal :
      ((evalIntegerPolynomial P (fun i => (x i : ℤ)) : ℤ) : ℝ) =
        ∑ s ∈ P.support, f s := by
    rw [hevalInt]
    simp [f, Int.cast_sum, Int.cast_mul, Int.cast_prod, Int.cast_pow]
  have hterm : ∀ s ∈ P.support, |f s| ≤
      ((P.coeff s).natAbs : ℝ) * (M : ℝ) ^ P.totalDegree := by
    intro s hs
    have hsvars : s.support ⊆ P.vars :=
      MvPolynomial.support_subset_vars_of_mem_support hs
    have hprod_nonneg : 0 ≤ ∏ i ∈ s.support, (x i : ℝ) ^ s i := by
      apply Finset.prod_nonneg
      intro i hi
      positivity
    have hprod :
        (∏ i ∈ s.support, (x i : ℝ) ^ s i) ≤ (M : ℝ) ^ P.totalDegree := by
      calc
        _ ≤ ∏ i ∈ s.support, (M : ℝ) ^ s i := by
          apply Finset.prod_le_prod₀
          · intro i hi
            positivity
          · intro i hi
            have hxi : x i ≤ M := hactive i (hsvars hi)
            have hxiR : (x i : ℝ) ≤ M := by exact_mod_cast hxi
            exact pow_le_pow_left₀ (by positivity) hxiR _
        _ = (M : ℝ) ^ ∑ i ∈ s.support, s i := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ (M : ℝ) ^ P.totalDegree := by
          apply pow_le_pow_right₀ (by exact_mod_cast hM)
          exact MvPolynomial.le_totalDegree hs
    have hcoeffAbs : |(P.coeff s : ℝ)| = (P.coeff s).natAbs := by
      exact (int_natAbs_cast_real (P.coeff s)).symm
    change |(P.coeff s : ℝ) * ∏ i ∈ s.support, (x i : ℝ) ^ s i| ≤ _
    rw [abs_mul, hcoeffAbs, abs_of_nonneg hprod_nonneg]
    exact mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
  have habs :
      |∑ s ∈ P.support, f s| ≤
        ∑ s ∈ P.support, |f s| := Finset.abs_sum_le_sum_abs (fun s => f s) P.support
  have hsum :
      |∑ s ∈ P.support, f s| ≤
        (roughCoefficientMass P : ℝ) * (M : ℝ) ^ P.totalDegree := by
    calc
      _ ≤ ∑ s ∈ P.support, |f s| := habs
      _ ≤ ∑ s ∈ P.support,
          ((P.coeff s).natAbs : ℝ) * (M : ℝ) ^ P.totalDegree := by
            apply Finset.sum_le_sum
            intro s hs
            exact hterm s hs
      _ = _ := by
            rw [← Finset.sum_mul]
            simp [roughCoefficientMass]
  have hnat :
      ((evalIntegerPolynomial P (fun i => (x i : ℤ))).natAbs : ℝ) =
        |((evalIntegerPolynomial P (fun i => (x i : ℤ)) : ℤ) : ℝ)| := by
    exact int_natAbs_cast_real _
  have hleR := hnat ▸ (hevalReal ▸ hsum)
  exact_mod_cast hleR

private def roughLargePrimeFactors (n Y : ℕ) : Finset ℕ :=
  n.primeFactors.filter (fun p => Y ≤ p ^ 2)

private lemma roughLargePrimeFactors_card_le (n Y d : ℕ)
    (hY : 2 ≤ Y) (hn : 0 < n) (hbound : n ≤ Y ^ (d + 1)) :
    (roughLargePrimeFactors n Y).card ≤ 2 * (d + 1) := by
  classical
  let S := roughLargePrimeFactors n Y
  have hSsub : S ⊆ n.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hprodDvd : (∏ p ∈ S, p) ∣ n := by
    apply dvd_trans (Finset.prod_dvd_prod_of_subset S n.primeFactors id hSsub)
    exact Nat.prod_primeFactors_dvd n
  have hprodLe : (∏ p ∈ S, p) ≤ n := Nat.le_of_dvd hn hprodDvd
  have hprodIneq : (∏ p ∈ S, Y) ≤ ∏ p ∈ S, p ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
  have hprodEq : (∏ p ∈ S, p ^ 2) = (∏ p ∈ S, p) ^ 2 :=
    Finset.prod_pow S 2 id
  have hprodLower : Y ^ S.card ≤ (∏ p ∈ S, p) ^ 2 := by
    calc
      Y ^ S.card = ∏ p ∈ S, Y := by simp
      _ ≤ ∏ p ∈ S, p ^ 2 := hprodIneq
      _ = (∏ p ∈ S, p) ^ 2 := hprodEq
  have hprodSq : (∏ p ∈ S, p) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hprodLe 2
  have hnSq : n ^ 2 ≤ Y ^ ((d + 1) * 2) := by
    calc
      n ^ 2 ≤ (Y ^ (d + 1)) ^ 2 := Nat.pow_le_pow_left hbound 2
      _ = Y ^ ((d + 1) * 2) := by rw [pow_mul]
  have hpow : Y ^ S.card ≤ Y ^ ((d + 1) * 2) := hprodLower.trans (hprodSq.trans hnSq)
  have hcard := (Nat.pow_le_pow_iff_right (by omega : 1 < Y)).mp hpow
  simpa [S, Nat.mul_comm] using hcard

private lemma nat_lt_of_squares_cut {K L p : ℕ}
    (hKL : (K + 1) ^ 2 ≤ L) (hLp : L ≤ p ^ 2) : K < p := by
  by_contra h
  have hpK : p ≤ K := by omega
  have hp2 : p ^ 2 ≤ K ^ 2 := Nat.pow_le_pow_left hpK 2
  have hKsq : K ^ 2 < (K + 1) ^ 2 := by nlinarith
  omega

private lemma independentPrimePairProbability_add_disjoint {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E F : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop)
    [DecidableRel E] [DecidableRel F]
    [DecidableRel (fun (x : Fin kF → ℕ) (y : Fin kG → ℕ) => E x y ∨ F x y)]
    (hdisj : ∀ x y, ¬ (E x y ∧ F x y)) :
    independentPrimePairProbability loF hiF loG hiG (fun x y => E x y ∨ F x y) =
    independentPrimePairProbability loF hiF loG hiG E +
        independentPrimePairProbability loF hiF loG hiG F := by
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  letI : DecidableRel F := fun x y => Classical.propDecidable (F x y)
  letI : DecidableRel (fun (x : Fin kF → ℕ) (y : Fin kG → ℕ) => E x y ∨ F x y) :=
    fun x y => Classical.propDecidable (E x y ∨ F x y)
  have hinner (x : Fin kF → ℕ) :
      (∑' y : Fin kG → ℕ,
        independentPrimePoolMass loG hiG y * if E x y ∨ F x y then 1 else 0) =
      (∑' y : Fin kG → ℕ,
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
      (∑' y : Fin kG → ℕ,
        independentPrimePoolMass loG hiG y * if F x y then 1 else 0) := by
    have hE : Summable (fun y : Fin kG → ℕ =>
        independentPrimePoolMass loG hiG y * if E x y then 1 else 0) :=
      independentPrimePoolProbability_summable loG hiG (E x)
    have hF : Summable (fun y : Fin kG → ℕ =>
        independentPrimePoolMass loG hiG y * if F x y then 1 else 0) :=
      independentPrimePoolProbability_summable loG hiG (F x)
    calc
      _ = ∑' y : Fin kG → ℕ,
          ((independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
            (independentPrimePoolMass loG hiG y * if F x y then 1 else 0)) := by
          apply tsum_congr
          intro y
          by_cases hEx : E x y
          · have hEF : ¬ F x y := fun hFy => hdisj x y ⟨hEx, hFy⟩
            simp [hEx, hEF]
          · simp [hEx]
      _ = _ := hE.tsum_add hF
  have hOuterE := independentPrimePairOuter_summable loF hiF loG hiG E
  have hOuterF := independentPrimePairOuter_summable loF hiF loG hiG F
  unfold independentPrimePairProbability
  calc
    (∑' x : Fin kF → ℕ,
      independentPrimePoolMass loF hiF x *
        (∑' y : Fin kG → ℕ,
          independentPrimePoolMass loG hiG y * if E x y ∨ F x y then 1 else 0)) =
      ∑' x : Fin kF → ℕ,
        independentPrimePoolMass loF hiF x *
          ((∑' y : Fin kG → ℕ,
            independentPrimePoolMass loG hiG y * if E x y then 1 else 0) +
           (∑' y : Fin kG → ℕ,
            independentPrimePoolMass loG hiG y * if F x y then 1 else 0)) := by
            apply tsum_congr
            intro x
            rw [hinner x]
    _ = ∑' x : Fin kF → ℕ,
        ((independentPrimePoolMass loF hiF x *
            (∑' y : Fin kG → ℕ,
              independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) +
          (independentPrimePoolMass loF hiF x *
            (∑' y : Fin kG → ℕ,
              independentPrimePoolMass loG hiG y * if F x y then 1 else 0))) := by
            apply tsum_congr
            intro x
            ring
    _ = (∑' x : Fin kF → ℕ,
          independentPrimePoolMass loF hiF x *
            (∑' y : Fin kG → ℕ,
              independentPrimePoolMass loG hiG y * if E x y then 1 else 0)) +
        ∑' x : Fin kF → ℕ,
          independentPrimePoolMass loF hiF x *
            (∑' y : Fin kG → ℕ,
              independentPrimePoolMass loG hiG y * if F x y then 1 else 0) :=
            hOuterE.tsum_add hOuterF

private lemma independentPrimePoolMass_nonneg {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ) :
    0 ≤ independentPrimePoolMass lo hi p := by
  unfold independentPrimePoolMass
  apply Finset.prod_nonneg
  intro i hiMem
  exact primePoolLaw_nonneg (lo i) (hi i) (p i)

private lemma independentPrimePairProbability_mono {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E F : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop)
    [DecidableRel E] [DecidableRel F]
    (hEF : ∀ x y, E x y → F x y) :
    independentPrimePairProbability loF hiF loG hiG E ≤
    independentPrimePairProbability loF hiF loG hiG F := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  letI : DecidableRel F := fun x y => Classical.propDecidable (F x y)
  have houterE := independentPrimePairOuter_summable loF hiF loG hiG E
  have houterF := independentPrimePairOuter_summable loF hiF loG hiG F
  unfold independentPrimePairProbability
  apply houterE.tsum_le_tsum ?_ houterF
  intro x
  have hinnerE : Summable (fun y : Fin kG → ℕ =>
      independentPrimePoolMass loG hiG y * if E x y then 1 else 0) :=
    independentPrimePoolProbability_summable loG hiG (E x)
  have hinnerF : Summable (fun y : Fin kG → ℕ =>
      independentPrimePoolMass loG hiG y * if F x y then 1 else 0) :=
    independentPrimePoolProbability_summable loG hiG (F x)
  have hsum : (∑' y, independentPrimePoolMass loG hiG y * if E x y then 1 else 0) ≤
      ∑' y, independentPrimePoolMass loG hiG y * if F x y then 1 else 0 := by
    apply hinnerE.tsum_le_tsum ?_ hinnerF
    intro y
    by_cases h : E x y
    · simp [h, hEF x y h]
    · by_cases hFy : F x y
      · simpa [h, hFy] using independentPrimePoolMass_nonneg loG hiG y
      · simp [h, hFy]
  exact mul_le_mul_of_nonneg_left hsum (independentPrimePoolMass_nonneg loF hiF x)

private lemma independentPrimePairProbability_finset_union_le {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (s : Finset ℕ) (E : ℕ → (Fin kF → ℕ) → (Fin kG → ℕ) → Prop)
    [∀ p, DecidableRel (E p)] :
    independentPrimePairProbability loF hiF loG hiG
      (fun x y => ∃ p ∈ s, E p x y) ≤
      ∑ p ∈ s, independentPrimePairProbability loF hiF loG hiG (E p) := by
  classical
  induction s using Finset.induction with
  | empty => simp [independentPrimePairProbability]
  | @insert a s ha ih =>
    let A : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y => ∃ p ∈ s, E p x y
    let B : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := E a
    let D : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y => A x y ∧ ¬ B x y
    letI : DecidableRel A := fun x y => Classical.propDecidable (A x y)
    letI : DecidableRel B := fun x y => Classical.propDecidable (B x y)
    letI : DecidableRel D := fun x y => Classical.propDecidable (D x y)
    letI : DecidableRel (fun x y => D x y ∨ B x y) := fun x y =>
      Classical.propDecidable (D x y ∨ B x y)
    letI : DecidableRel (fun x y => ∃ p ∈ insert a s, E p x y) := fun x y =>
      Classical.propDecidable (∃ p ∈ insert a s, E p x y)
    have hPred (x : Fin kF → ℕ) (y : Fin kG → ℕ) :
        (B x y ∨ A x y) ↔ (D x y ∨ B x y) := by
      constructor
      · intro h
        rcases h with hB | hA
        · exact Or.inr hB
        · by_cases hB : B x y
          · exact Or.inr hB
          · exact Or.inl ⟨hA, hB⟩
      · intro h
        rcases h with ⟨hA, _⟩ | hB
        · exact Or.inr hA
        · exact Or.inl hB
    have hEqProb :
        independentPrimePairProbability loF hiF loG hiG
          (fun x y => ∃ p ∈ insert a s, E p x y) =
        independentPrimePairProbability loF hiF loG hiG (fun x y => D x y ∨ B x y) := by
      unfold independentPrimePairProbability
      apply tsum_congr
      intro x
      congr 1
      apply tsum_congr
      intro y
      by_cases hleft : E a x y ∨ ∃ q ∈ s, E q x y
      · have hright : D x y ∨ B x y := by
          apply (hPred x y).1
          simpa [A, B, or_comm] using hleft
        simp [hleft, hright]
      · have hright : ¬ (D x y ∨ B x y) := by
          intro h
          apply hleft
          have hba : B x y ∨ A x y := (hPred x y).2 h
          simpa [A, B, or_comm] using hba
        simp [hleft, hright]
    have hdisj : ∀ x y, ¬ (D x y ∧ B x y) := by
      intro x y h
      exact h.1.2 h.2
    have hadd := independentPrimePairProbability_add_disjoint
      loF hiF loG hiG D B hdisj
    have hmono := independentPrimePairProbability_mono loF hiF loG hiG D A
      (by intro x y hD; exact hD.1)
    calc
      independentPrimePairProbability loF hiF loG hiG
          (fun x y => ∃ p ∈ insert a s, E p x y) =
        independentPrimePairProbability loF hiF loG hiG (fun x y => D x y ∨ B x y) := hEqProb
      _ = independentPrimePairProbability loF hiF loG hiG D +
            independentPrimePairProbability loF hiF loG hiG B := hadd
      _ ≤ independentPrimePairProbability loF hiF loG hiG A +
            independentPrimePairProbability loF hiF loG hiG B :=
              add_le_add hmono le_rfl
      _ ≤ (∑ p ∈ s, independentPrimePairProbability loF hiF loG hiG (E p)) +
            independentPrimePairProbability loF hiF loG hiG B :=
              add_le_add ih le_rfl
      _ = ∑ p ∈ insert a s, independentPrimePairProbability loF hiF loG hiG (E p) := by
              rw [Finset.sum_insert ha]
              simp [B, add_comm]

private lemma independentPrimePairProbability_or_le {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (E F : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop)
    [DecidableRel E] [DecidableRel F] :
    independentPrimePairProbability loF hiF loG hiG (fun x y => E x y ∨ F x y) ≤
      independentPrimePairProbability loF hiF loG hiG E +
        independentPrimePairProbability loF hiF loG hiG F := by
  classical
  let D : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y => E x y ∧ ¬ F x y
  letI : DecidableRel D := fun x y => Classical.propDecidable (D x y)
  letI : DecidableRel (fun x y => D x y ∨ F x y) := fun x y =>
    Classical.propDecidable (D x y ∨ F x y)
  have hEq : independentPrimePairProbability loF hiF loG hiG
      (fun x y => E x y ∨ F x y) =
      independentPrimePairProbability loF hiF loG hiG (fun x y => D x y ∨ F x y) := by
    unfold independentPrimePairProbability
    apply tsum_congr
    intro x
    congr 1
    apply tsum_congr
    intro y
    by_cases hE : E x y <;> by_cases hF : F x y <;> simp [D, hE, hF]
  have hdisj : ∀ x y, ¬ (D x y ∧ F x y) := by
    intro x y h
    exact h.1.2 h.2
  have hadd := independentPrimePairProbability_add_disjoint
    loF hiF loG hiG D F hdisj
  have hmono := independentPrimePairProbability_mono loF hiF loG hiG D E
    (by intro x y h; exact h.1)
  calc
    independentPrimePairProbability loF hiF loG hiG (fun x y => E x y ∨ F x y) =
        independentPrimePairProbability loF hiF loG hiG (fun x y => D x y ∨ F x y) := hEq
    _ = independentPrimePairProbability loF hiF loG hiG D +
          independentPrimePairProbability loF hiF loG hiG F := hadd
    _ ≤ independentPrimePairProbability loF hiF loG hiG E +
          independentPrimePairProbability loF hiF loG hiG F := add_le_add hmono le_rfl

private lemma primePoolLaw_tsum_eq_one {lo hi : ℕ}
    (hm : 0 < primePoolMass lo hi) : ∑' p : ℕ, primePoolLaw lo hi p = 1 := by
  have hmass : primePoolMass lo hi ≠ 0 := ne_of_gt hm
  calc
    ∑' p : ℕ, primePoolLaw lo hi p =
        ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p := by
          apply tsum_eq_sum (s := Finset.Ico lo hi)
          intro p hp
          simp only [primePoolLaw]
          split_ifs with h
          · exact False.elim (hp (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
          · rfl
    _ = ∑ p ∈ (Finset.Ico lo hi).filter Nat.Prime,
          (1 / (p : ℝ)) / primePoolMass lo hi := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro p hp
          simp [primePoolLaw, Finset.mem_Ico.mp hp]
    _ = 1 := by
          rw [← Finset.sum_div]
          change primePoolMass lo hi / primePoolMass lo hi = 1
          exact div_self hmass

private lemma primePoolLaw_sum_Ico_eq_one {lo hi : ℕ}
    (hm : 0 < primePoolMass lo hi) :
    ∑ p ∈ Finset.Ico lo hi, primePoolLaw lo hi p = 1 := by
  have h := primePoolLaw_tsum_eq_one hm
  rw [tsum_eq_sum (s := Finset.Ico lo hi)] at h
  · exact h
  · intro p hp
    simp only [primePoolLaw]
    split_ifs with h
    · exact False.elim (hp (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
    · rfl

private lemma independentPrimePoolProbability_true {m : ℕ}
    (lo hi : Fin m → ℕ) (hm : ∀ i, 0 < primePoolMass (lo i) (hi i)) :
    independentPrimePoolProbability lo hi (fun _ => True) = 1 := by
  classical
  unfold independentPrimePoolProbability
  rw [tsum_eq_sum (s := primeTupleSupport lo hi)]
  · simp only [primeTupleSupport, independentPrimePoolMass, mul_one]
    calc
      _ = ∏ i, ∑ p ∈ Finset.Ico (lo i) (hi i), primePoolLaw (lo i) (hi i) p := by
        simpa using (Finset.prod_univ_sum
          (t := fun i : Fin m => Finset.Ico (lo i) (hi i))
          (f := fun i p => primePoolLaw (lo i) (hi i) p)).symm
      _ = 1 := by simp [primePoolLaw_sum_Ico_eq_one, hm]
  · intro p hp
    rw [independentPrimePoolMass_zero_of_not_mem_support lo hi p hp]
    simp

private lemma independentPrimePoolProbability_or_le {m : ℕ}
    (lo hi : Fin m → ℕ)
    (E F : (Fin m → ℕ) → Prop) [DecidablePred E] [DecidablePred F] :
    independentPrimePoolProbability lo hi (fun x => E x ∨ F x) ≤
      independentPrimePoolProbability lo hi E + independentPrimePoolProbability lo hi F := by
  classical
  letI : DecidablePred (fun x => E x ∨ F x) := fun x => Classical.propDecidable _
  have hE := independentPrimePoolProbability_summable lo hi E
  have hF := independentPrimePoolProbability_summable lo hi F
  have hEF := independentPrimePoolProbability_summable lo hi (fun x => E x ∨ F x)
  have hpoint (x : Fin m → ℕ) :
      independentPrimePoolMass lo hi x * (if E x ∨ F x then 1 else 0) ≤
        independentPrimePoolMass lo hi x * (if E x then 1 else 0) +
          independentPrimePoolMass lo hi x * (if F x then 1 else 0) := by
    have hite : (if E x ∨ F x then (1 : ℝ) else 0) ≤
        (if E x then 1 else 0) + if F x then 1 else 0 := by
      by_cases hE' : E x <;> by_cases hF' : F x <;> simp [hE', hF']
    calc
      _ ≤ independentPrimePoolMass lo hi x *
            ((if E x then 1 else 0) + if F x then 1 else 0) :=
          mul_le_mul_of_nonneg_left hite (independentPrimePoolMass_nonneg lo hi x)
      _ = _ := by rw [mul_add]
  calc
    _ = ∑' x, independentPrimePoolMass lo hi x * if E x ∨ F x then 1 else 0 := rfl
    _ ≤ ∑' x,
          ((independentPrimePoolMass lo hi x * if E x then 1 else 0) +
            (independentPrimePoolMass lo hi x * if F x then 1 else 0)) :=
              hEF.tsum_le_tsum hpoint (hE.add hF)
    _ = independentPrimePoolProbability lo hi E + independentPrimePoolProbability lo hi F := by
          simpa [independentPrimePoolProbability] using hE.tsum_add hF

private lemma independentPrimePoolProbability_exists_finset_le {m : ℕ} {α : Type*}
    [DecidableEq α] (lo hi : Fin m → ℕ) (s : Finset α)
    (E : α → (Fin m → ℕ) → Prop) (B : ℝ)
    (hB : ∀ a ∈ s, independentPrimePoolProbability lo hi (E a) ≤ B) :
    independentPrimePoolProbability lo hi (fun x => ∃ a ∈ s, E a x) ≤ s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [independentPrimePoolProbability]
  | @insert a s ha ih =>
      have hEa : independentPrimePoolProbability lo hi (E a) ≤ B :=
        hB a (Finset.mem_insert_self a s)
      have hrest : ∀ b ∈ s, independentPrimePoolProbability lo hi (E b) ≤ B := by
        intro b hb
        exact hB b (Finset.mem_insert_of_mem hb)
      have hunion : (fun x => ∃ b ∈ insert a s, E b x) =
          (fun x => E a x ∨ ∃ b ∈ s, E b x) := by
        funext x
        apply propext
        simp [Finset.mem_insert, ha, or_comm, or_left_comm, or_assoc]
      rw [hunion]
      calc
        _ ≤ independentPrimePoolProbability lo hi (E a) +
              independentPrimePoolProbability lo hi (fun x => ∃ b ∈ s, E b x) :=
                independentPrimePoolProbability_or_le lo hi _ _
        _ ≤ B + s.card * B := add_le_add hEa (ih hrest)
        _ = (insert a s).card * B := by simp [ha]; ring

private lemma independentPrimePairProbability_fiberwise_le {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (hmassF : ∀ i, 0 < primePoolMass (loF i) (hiF i))
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hfiber : ∀ x, x ∈ primeTupleSupport loF hiF →
      independentPrimePoolProbability loG hiG (E x) ≤ B) :
    independentPrimePairProbability loF hiF loG hiG E ≤ B := by
  classical
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  have houter := independentPrimePairOuter_summable loF hiF loG hiG E
  have hmass := independentPrimePoolMass_summable loF hiF
  have hconst : Summable (fun x => independentPrimePoolMass loF hiF x * B) :=
    hmass.mul_right B
  have hpoint (x : Fin kF → ℕ) :
      independentPrimePoolMass loF hiF x *
        (∑' y, independentPrimePoolMass loG hiG y * if E x y then 1 else 0) ≤
      independentPrimePoolMass loF hiF x * B := by
    by_cases hx : x ∈ primeTupleSupport loF hiF
    · exact mul_le_mul_of_nonneg_left (hfiber x hx)
        (independentPrimePoolMass_nonneg loF hiF x)
    · rw [independentPrimePoolMass_zero_of_not_mem_support loF hiF x hx]
      simp
  have htrue := independentPrimePoolProbability_true loF hiF hmassF
  have htotal : (∑' x, independentPrimePoolMass loF hiF x) = 1 := by
    simpa [independentPrimePoolProbability, independentPrimePoolMass] using htrue
  calc
    _ = ∑' x, independentPrimePoolMass loF hiF x *
          (∑' y, independentPrimePoolMass loG hiG y * if E x y then 1 else 0) := rfl
    _ ≤ ∑' x, independentPrimePoolMass loF hiF x * B := houter.tsum_le_tsum hpoint hconst
    _ = B := by rw [hmass.tsum_mul_right, htotal]; ring

private lemma independentPrimePairProbability_left_event {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (hMassG : ∀ j, 0 < primePoolMass (loG j) (hiG j))
    (E : (Fin kF → ℕ) → Prop) [DecidablePred E] :
    independentPrimePairProbability loF hiF loG hiG (fun x _ => E x) =
      independentPrimePoolProbability loF hiF E := by
  classical
  have hprod := independentPrimePairProbability_product loF hiF loG hiG E
    (fun _ : Fin kG → ℕ => True)
  have hevent : (fun x y => E x ∧ (fun _ : Fin kG → ℕ => True) y) =
      (fun x _ => E x) := by
    funext x y
    simp
  rw [← hevent, hprod, independentPrimePoolProbability_true loG hiG hMassG]
  simp

private lemma independentPrimePairProbability_right_event {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (hMassF : ∀ i, 0 < primePoolMass (loF i) (hiF i))
    (E : (Fin kG → ℕ) → Prop) [DecidablePred E] :
    independentPrimePairProbability loF hiF loG hiG (fun _ y => E y) =
      independentPrimePoolProbability loG hiG E := by
  classical
  have hprod := independentPrimePairProbability_product loF hiF loG hiG
    (fun _ : Fin kF → ℕ => True) E
  have hevent : (fun x y => (fun _ : Fin kF → ℕ => True) x ∧ E y) =
      (fun _ y => E y) := by
    funext x y
    simp
  rw [← hevent, hprod, independentPrimePoolProbability_true loF hiF hMassF]
  simp

private lemma independentPrimePairProbability_le_one {kF kG : ℕ}
    (loF hiF : Fin kF → ℕ) (loG hiG : Fin kG → ℕ)
    (hF : ∀ i, 0 < primePoolMass (loF i) (hiF i))
    (hG : ∀ j, 0 < primePoolMass (loG j) (hiG j))
    (E : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop)
    [DecidableRel E] :
    independentPrimePairProbability loF hiF loG hiG E ≤ 1 := by
  letI : DecidableRel E := fun x y => Classical.propDecidable (E x y)
  have hmono := independentPrimePairProbability_mono loF hiF loG hiG E
    (fun _ _ => True) (by intro x y h; trivial)
  have htrue : independentPrimePairProbability loF hiF loG hiG (fun _ _ => True) = 1 := by
    calc
      independentPrimePairProbability loF hiF loG hiG (fun _ _ => True) =
          independentPrimePairProbability loF hiF loG hiG
            (fun x y => (fun _ : Fin kF → ℕ => True) x ∧ (fun _ : Fin kG → ℕ => True) y) := by
              congr 1
              funext x y
              simp
      _ = independentPrimePoolProbability loF hiF (fun _ => True) *
          independentPrimePoolProbability loG hiG (fun _ => True) :=
            independentPrimePairProbability_product ..
      _ = 1 := by rw [independentPrimePoolProbability_true loF hiF hF,
          independentPrimePoolProbability_true loG hiG hG]; norm_num
  rw [htrue] at hmono
  exact hmono

private def primePoolResidueMass {m : ℕ} (lo hi : Fin m → ℕ)
    (p : ℕ) (i : Fin m) (a : ZMod p) : ℝ :=
  ∑ n ∈ Finset.Ico (lo i) (hi i),
    if (n : ZMod p) = a then primePoolLaw (lo i) (hi i) n else 0

private lemma independentPrimePoolProbability_mod_map {m : ℕ}
    (lo hi : Fin m → ℕ) (p : ℕ) [NeZero p]
    (E : (Fin m → ZMod p) → Prop) [DecidablePred E] :
    independentPrimePoolProbability lo hi (fun x => E (fun i => (x i : ZMod p))) =
      ∑ r : Fin m → ZMod p,
        (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := by
  classical
  unfold independentPrimePoolProbability
  rw [tsum_eq_sum (s := primeTupleSupport lo hi)]
  · let ρ : (Fin m → ℕ) → (Fin m → ZMod p) := fun x i => (x i : ZMod p)
    have hpart := Finset.sum_fiberwise_eq_sum_filter
      (primeTupleSupport lo hi) Finset.univ ρ
      (fun x => independentPrimePoolMass lo hi x * if E (ρ x) then 1 else 0)
    have hfiberEvent (r : Fin m → ZMod p) :
        (∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x = r),
          independentPrimePoolMass lo hi x * if E r then 1 else 0) =
        ∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x = r),
          independentPrimePoolMass lo hi x * if E (ρ x) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter] at hx
      rw [hx.2]
    have hsum :
        (∑ r ∈ Finset.univ, ∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x = r),
          independentPrimePoolMass lo hi x * if E r then 1 else 0) =
        ∑ x ∈ primeTupleSupport lo hi,
          independentPrimePoolMass lo hi x * if E (ρ x) then 1 else 0 := by
      calc
        _ = ∑ r ∈ Finset.univ, ∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x = r),
              independentPrimePoolMass lo hi x * if E (ρ x) then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro r hr
                exact hfiberEvent r
        _ = ∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x ∈ Finset.univ),
              independentPrimePoolMass lo hi x * if E (ρ x) then 1 else 0 := by
                simpa only [Finset.mem_univ, if_true] using hpart
        _ = _ := by simp
    calc
      _ = ∑ r ∈ Finset.univ, ∑ x ∈ (primeTupleSupport lo hi).filter (fun x => ρ x = r),
            independentPrimePoolMass lo hi x * if E r then 1 else 0 := by
              simpa [ρ] using hsum.symm
      _ = ∑ r : Fin m → ZMod p,
            (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hfiber :
            (primeTupleSupport lo hi).filter (fun x => ρ x = r) =
              Fintype.piFinset (fun i =>
                    (Finset.Ico (lo i) (hi i)).filter (fun n : ℕ => (n : ZMod p) = r i)) := by
          ext x
          simp only [Finset.mem_filter, primeTupleSupport, Fintype.mem_piFinset,
            Finset.mem_Ico, ρ]
          constructor
          · rintro ⟨hmem, hres⟩ i
            exact ⟨hmem i, congrFun hres i⟩
          · intro h
            refine ⟨(fun i => (h i).1), ?_⟩
            funext i
            exact (h i).2
        rw [hfiber]
        simp only [independentPrimePoolMass]
        calc
          _ = (∑ x ∈ Fintype.piFinset (fun i =>
                  (Finset.Ico (lo i) (hi i)).filter
                    (fun n : ℕ => (n : ZMod p) = r i)),
                ∏ i, primePoolLaw (lo i) (hi i) (x i)) * if E r then 1 else 0 := by
                rw [← Finset.sum_mul]
          _ = (∏ i, ∑ n ∈ (Finset.Ico (lo i) (hi i)).filter
                (fun n : ℕ => (n : ZMod p) = r i), primePoolLaw (lo i) (hi i) n) *
                if E r then 1 else 0 := by
                congr 1
                exact (Finset.prod_univ_sum
                  (t := fun i : Fin m =>
                    (Finset.Ico (lo i) (hi i)).filter
                      (fun n : ℕ => (n : ZMod p) = r i))
                  (f := fun i n => primePoolLaw (lo i) (hi i) n)).symm
          _ = (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := by
                congr 1
                apply Finset.prod_congr rfl
                intro i hi
                simp [primePoolResidueMass, Finset.sum_filter]
  · intro x hx
    rw [independentPrimePoolMass_zero_of_not_mem_support lo hi x hx]
    simp

private lemma independentPrimePoolMass_finCons {n : ℕ}
    (lo hi : Fin (n + 1) → ℕ) (q : ℕ) (x : Fin n → ℕ) :
    independentPrimePoolMass lo hi (Fin.cons q x) =
      primePoolLaw (lo 0) (hi 0) q *
        independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x := by
  unfold independentPrimePoolMass
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, mul_comm]

private lemma independentPrimePoolProbability_finCons {n : ℕ}
    (lo hi : Fin (n + 1) → ℕ)
    (E : (Fin (n + 1) → ℕ) → Prop) [decE : DecidablePred E] :
    independentPrimePoolProbability lo hi E =
      ∑ x ∈ primeTupleSupport (fun i => lo i.succ) (fun i => hi i.succ),
        independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x *
          ∑ q ∈ Finset.Ico (lo 0) (hi 0),
            primePoolLaw (lo 0) (hi 0) q * if E (Fin.cons q x) then 1 else 0 := by
  let S : Finset (Fin n → ℕ) := primeTupleSupport (fun i => lo i.succ) (fun i => hi i.succ)
  let T : Finset ℕ := Finset.Ico (lo 0) (hi 0)
  let e : (ℕ × (Fin n → ℕ)) ≃ (Fin (n + 1) → ℕ) :=
    Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)
  have hsupport : ∀ q x, (q, x) ∈ T ×ˢ S ↔ e (q, x) ∈ primeTupleSupport lo hi := by
    intro q x
    simp [e, T, S, primeTupleSupport, Fin.forall_iff_succ]
  have hfinite :
      independentPrimePoolProbability lo hi E =
        ∑ z ∈ primeTupleSupport lo hi,
          independentPrimePoolMass lo hi z * if E z then 1 else 0 := by
    letI : DecidablePred E := decE
    unfold independentPrimePoolProbability
    calc
      _ = ∑' z : Fin (n + 1) → ℕ,
          independentPrimePoolMass lo hi z * if E z then 1 else 0 := by
            apply tsum_congr
            intro z
            by_cases hz : E z <;> simp [hz]
      _ = ∑ z ∈ primeTupleSupport lo hi,
          independentPrimePoolMass lo hi z * if E z then 1 else 0 :=
            tsum_eq_sum (s := primeTupleSupport lo hi) (fun z hz => by
              rw [independentPrimePoolMass_zero_of_not_mem_support lo hi z hz]
              simp)
  rw [hfinite]
  calc
    _ = ∑ qx ∈ T ×ˢ S,
          independentPrimePoolMass lo hi (e qx) * if E (e qx) then 1 else 0 := by
            symm
            apply Finset.sum_bijective e e.bijective (by
              intro qx
              exact hsupport qx.1 qx.2)
            intro qx hqx
            rfl
    _ = ∑ qx ∈ T ×ˢ S,
          (primePoolLaw (lo 0) (hi 0) qx.1 *
            independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) qx.2) *
              if E (Fin.cons qx.1 qx.2) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro qx hqx
            change independentPrimePoolMass lo hi (Fin.cons qx.1 qx.2) *
                (if E (Fin.cons qx.1 qx.2) then (1 : ℝ) else 0) = _
            rw [independentPrimePoolMass_finCons]
    _ = ∑ x ∈ S,
          independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x *
            ∑ q ∈ T, primePoolLaw (lo 0) (hi 0) q * if E (Fin.cons q x) then 1 else 0 := by
            calc
              _ = ∑ q ∈ T, ∑ x ∈ S,
                    (primePoolLaw (lo 0) (hi 0) q *
                      independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x) *
                      if E (Fin.cons q x) then 1 else 0 := by
                    rw [Finset.sum_product]
              _ = ∑ x ∈ S, ∑ q ∈ T,
                    (primePoolLaw (lo 0) (hi 0) q *
                      independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x) *
                      if E (Fin.cons q x) then 1 else 0 := by
                    rw [Finset.sum_comm]
              _ = ∑ x ∈ S,
                    independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x *
                      ∑ q ∈ T, primePoolLaw (lo 0) (hi 0) q *
                        if E (Fin.cons q x) then 1 else 0 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    calc
                      _ = ∑ q ∈ T,
                          independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x *
                            (primePoolLaw (lo 0) (hi 0) q * if E (Fin.cons q x) then 1 else 0) := by
                              apply Finset.sum_congr rfl
                              intro q hq
                              ring
                      _ = _ := by rw [Finset.mul_sum]
    _ = ∑ x ∈ primeTupleSupport (fun i => lo i.succ) (fun i => hi i.succ),
          independentPrimePoolMass (fun i => lo i.succ) (fun i => hi i.succ) x *
            ∑ q ∈ Finset.Ico (lo 0) (hi 0),
              primePoolLaw (lo 0) (hi 0) q * if E (Fin.cons q x) then 1 else 0 := by
          simp only [S, T]

private lemma primePoolResidueMass_nonneg {m : ℕ} (lo hi : Fin m → ℕ)
    (p : ℕ) (i : Fin m) (a : ZMod p) :
    0 ≤ primePoolResidueMass lo hi p i a := by
  unfold primePoolResidueMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact primePoolLaw_nonneg (lo i) (hi i) n
  · exact le_rfl

private lemma independentPrimePoolProbability_mod_zero_le {m : ℕ}
    (lo hi : Fin m → ℕ) (p : ℕ) [NeZero p] (hp : p.Prime)
    (P : MvPolynomial (Fin m) (ZMod p)) (hP : P ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hmax : ∀ i a, primePoolResidueMass lo hi p i a ≤ A / (p : ℝ)) :
    independentPrimePoolProbability lo hi
      (fun x => MvPolynomial.eval (fun i => (x i : ZMod p)) P = 0) ≤
      (P.totalDegree : ℝ) * A ^ m / p := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let E : (Fin m → ZMod p) → Prop := fun r => MvPolynomial.eval r P = 0
  letI : DecidablePred E := fun r => by
    change Decidable (MvPolynomial.eval r P = 0)
    infer_instance
  have hformula := independentPrimePoolProbability_mod_map lo hi p E
  have hprod (r : Fin m → ZMod p) :
      (∏ i, primePoolResidueMass lo hi p i (r i)) ≤ (A / (p : ℝ)) ^ m := by
    calc
      ∏ i, primePoolResidueMass lo hi p i (r i) ≤ ∏ _i : Fin m, A / (p : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hmem
          exact primePoolResidueMass_nonneg lo hi p i (r i)
        · intro i hmem
          exact hmax i (r i)
      _ = (A / (p : ℝ)) ^ m := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumle :
      (∑ r : Fin m → ZMod p,
        (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0) ≤
      ∑ r : Fin m → ZMod p, (A / (p : ℝ)) ^ m * if E r then 1 else 0 := by
    apply Finset.sum_le_sum
    intro r hr
    by_cases he : E r
    · simpa [he] using hprod r
    · simp [he]
  have hzeroSet : Finset.univ.filter E =
      {f ∈ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (ZMod p))) |
        MvPolynomial.eval f P = 0} := by
    ext r
    simp [E, Fintype.mem_piFinset]
  have hcountQ :
      ((Finset.univ.filter E).card : ℚ≥0) / (p : ℚ≥0) ^ m ≤
        (P.totalDegree : ℚ≥0) / (p : ℚ≥0) := by
    have hz := MvPolynomial.schwartz_zippel_totalDegree hP Finset.univ
    rw [congrArg Finset.card hzeroSet]
    simpa [ZMod.card] using hz
  have hcountR :
      ((Finset.univ.filter E).card : ℝ) / (p : ℝ) ^ m ≤
        (P.totalDegree : ℝ) / (p : ℝ) := by
    have hc := (NNRat.cast_le (K := ℝ)).2 hcountQ
    simpa using hc
  have hfactor :
      ((Finset.univ.filter E).card : ℝ) * (A / (p : ℝ)) ^ m ≤
        (P.totalDegree : ℝ) * A ^ m / p := by
    have hpR : 0 < (p : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
    have hpow : 0 ≤ A ^ m := pow_nonneg hA _
    calc
      ((Finset.univ.filter E).card : ℝ) * (A / (p : ℝ)) ^ m =
          (((Finset.univ.filter E).card : ℝ) / (p : ℝ) ^ m) * A ^ m := by
            rw [div_pow]
            ring
      _ ≤ ((P.totalDegree : ℝ) / (p : ℝ)) * A ^ m :=
        mul_le_mul_of_nonneg_right hcountR hpow
      _ = (P.totalDegree : ℝ) * A ^ m / p := by ring
  calc
    _ = ∑ r : Fin m → ZMod p,
        (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := by
          simpa [E] using hformula
    _ ≤ ∑ r : Fin m → ZMod p, (A / (p : ℝ)) ^ m * if E r then 1 else 0 := hsumle
    _ = ((Finset.univ.filter E).card : ℝ) * (A / (p : ℝ)) ^ m := by
          calc
            _ = ∑ r : Fin m → ZMod p, if E r then (A / (p : ℝ)) ^ m else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [mul_ite]
            _ = ∑ r ∈ Finset.univ.filter E, (A / (p : ℝ)) ^ m := by
              symm
              rw [Finset.sum_filter]
            _ = _ := by simp
    _ ≤ (P.totalDegree : ℝ) * A ^ m / p := hfactor

private def dyadicPrimeResidueMass (Y p : ℕ) (a : ZMod p) : ℝ :=
  ∑ q ∈ Finset.Ico Y (2 * Y),
    if (q : ZMod p) = a then primePoolLaw Y (2 * Y) q else 0

private lemma dyadicPrimeResidueMass_le_brun_titchmarsh {Y p : ℕ}
    [NeZero p] (hp : p.Prime) (hpY : p ^ 2 ≤ Y) (C : ℝ) (hC : 0 ≤ C)
    (hBT : ∀ a : Fin p, 0 < a.val →
      (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
        if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ C / p)
    (a : ZMod p) : dyadicPrimeResidueMass Y p a ≤ C / p := by
  classical
  by_cases ha : a = 0
  · subst a
    have hzero : dyadicPrimeResidueMass Y p 0 = 0 := by
      unfold dyadicPrimeResidueMass
      apply Finset.sum_eq_zero
      intro q hq
      by_cases hqp : q.Prime
      · by_cases hres : (q : ZMod p) = 0
        · have hdiv : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp hres
          have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hdiv
          have hpLtY : p < Y := by
            calc
              p = 1 * p := by simp
              _ < p * p := Nat.mul_lt_mul_of_pos_right (by have := hp.two_le; omega) hp.pos
              _ = p ^ 2 := by rw [pow_two]
              _ ≤ Y := hpY
          have hqY : Y ≤ q := (Finset.mem_Ico.mp hq).1
          omega
        · simp [hres]
      · simp [hqp, primePoolLaw]
    rw [hzero]
    exact div_nonneg hC (by positivity)
  · have hclass (q : ℕ) : (q : ZMod p) = a ↔ q % p = a.val := by
      rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_natCast_iff']
      simp [Nat.mod_eq_of_lt a.val_lt]
    have haPos : 0 < a.val := by
      by_contra hn
      have hzero : a.val = 0 := by omega
      apply ha
      rw [← ZMod.natCast_zmod_val a, hzero]
      simp
    have hsum : dyadicPrimeResidueMass Y p a =
        ∑ q ∈ Finset.Ico Y (2 * Y),
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0 := by
      unfold dyadicPrimeResidueMass
      apply Finset.sum_congr rfl
      intro q hq
      simp only [hclass q]
    have hfilter :
        (∑ q ∈ Finset.Ico Y (2 * Y),
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) =
        ∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0 := by
      symm
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hqp : q.Prime
      · simp [hqp, primePoolLaw, Finset.mem_Ico.mp hq]
      · simp [hqp, primePoolLaw]
    rw [hsum, hfilter]
    exact hBT ⟨a.val, a.val_lt⟩ haPos

private lemma dyadicPrimeResidueClass_card_le (Y p r : ℕ) (hp : 0 < p) :
    ((Finset.Ico Y (2 * Y)).filter (fun q => q % p = r)).card ≤ 2 * Y / p + 1 := by
  classical
  let S := (Finset.Ico Y (2 * Y)).filter (fun q => q % p = r)
  let T := Finset.range (2 * Y / p + 1)
  have hmaps : ∀ q ∈ S, q / p ∈ T := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hlt : q < 2 * Y := (Finset.mem_Ico.mp hq'.1).2
    rw [Finset.mem_range]
    apply (Nat.div_lt_iff_lt_mul hp).2
    have hmul : 2 * Y ≤ (2 * Y / p + 1) * p := by
      have hrem := Nat.mod_add_div (2 * Y) p
      have hrem_lt := Nat.mod_lt (2 * Y) hp
      nlinarith [hrem]
    exact lt_of_lt_of_le hlt hmul
  have hinj : (S : Set ℕ).InjOn (fun q => q / p) := by
    intro q hq r' hr hEq
    change q / p = r' / p at hEq
    have hqmod := (Finset.mem_filter.mp hq).2
    have hrmod := (Finset.mem_filter.mp hr).2
    calc
      q = q % p + p * (q / p) := (Nat.mod_add_div q p).symm
      _ = r' % p + p * (r' / p) := by rw [hqmod, hrmod, hEq]
      _ = r' := Nat.mod_add_div r' p
  have hcard := Finset.card_le_card_of_injOn (fun q => q / p) hmaps hinj
  simpa [S, T] using hcard

private lemma dyadicPrimeResidueMass_le_large_prime {Y p : ℕ} [NeZero p]
    (hp : p.Prime) (hY : 2 ≤ Y) (hsqrt : Real.sqrt (Y : ℝ) < (p : ℝ))
    (A : ℝ) (hA : 0 < A)
    (hAtom : ∀ (Y p : ℕ), 2 ≤ Y →
      primePoolLaw Y (2 * Y) p ≤ A * Real.log (Y : ℝ) / Y)
    (a : ZMod p) :
    dyadicPrimeResidueMass Y p a ≤
      3 * A * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) := by
  classical
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hsqrtPos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hYpos
  have hpPos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y))
  have hAtomNonneg : 0 ≤ A * Real.log (Y : ℝ) / Y := by positivity
  have hclass : ∀ q : ℕ, (q : ZMod p) = a ↔ q % p = a.val := by
    intro q
    rw [← ZMod.natCast_zmod_val a, ZMod.natCast_eq_natCast_iff']
    simp [Nat.mod_eq_of_lt a.val_lt]
  have hmassEq : dyadicPrimeResidueMass Y p a =
      ∑ q ∈ Finset.Ico Y (2 * Y),
        if q % p = a.val then primePoolLaw Y (2 * Y) q else 0 := by
    unfold dyadicPrimeResidueMass
    apply Finset.sum_congr rfl
    intro q hq
    simp only [hclass q]
  have hcard := dyadicPrimeResidueClass_card_le Y p a.val hp.pos
  have hcardReal : (((Finset.Ico Y (2 * Y)).filter
      (fun q => q % p = a.val)).card : ℝ) ≤ (2 * Y / p + 1 : ℕ) := by
    exact_mod_cast hcard
  have hsum :
      (∑ q ∈ Finset.Ico Y (2 * Y),
        if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤
      ((Finset.Ico Y (2 * Y)).filter (fun q => q % p = a.val)).card *
        (A * Real.log (Y : ℝ) / Y) := by
    calc
      _ = ∑ q ∈ (Finset.Ico Y (2 * Y)).filter (fun q => q % p = a.val),
          primePoolLaw Y (2 * Y) q := by rw [← Finset.sum_filter]
      _ ≤ ∑ q ∈ (Finset.Ico Y (2 * Y)).filter (fun q => q % p = a.val),
          A * Real.log (Y : ℝ) / Y := by
            apply Finset.sum_le_sum
            intro q hq
            exact hAtom Y q hY
      _ = _ := by simp
  have hcount : ((2 * Y / p + 1 : ℕ) : ℝ) ≤ 3 * Real.sqrt (Y : ℝ) := by
    have hdiv : ((2 * Y / p : ℕ) : ℝ) ≤ (2 * (Y : ℝ)) / (p : ℝ) := by
      simpa [Nat.cast_mul] using (Nat.cast_div_le (m := 2 * Y) (n := p))
    have hsmall : (2 * (Y : ℝ)) / p < 2 * Real.sqrt (Y : ℝ) := by
      apply (div_lt_iff₀ hpPos).2
      have hsquare : Real.sqrt (Y : ℝ) ^ 2 = (Y : ℝ) := Real.sq_sqrt (by positivity)
      nlinarith
    have hone : (1 : ℝ) ≤ Real.sqrt (Y : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ Y))
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hcardBound :
      ((Finset.Ico Y (2 * Y)).filter (fun q => q % p = a.val)).card ≤
        3 * Real.sqrt (Y : ℝ) := by
    exact hcardReal.trans hcount
  have hfinal :
      (3 * Real.sqrt (Y : ℝ)) * (A * Real.log (Y : ℝ) / Y) ≤
        3 * A * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) := by
    have hsquare : Real.sqrt (Y : ℝ) ^ 2 = (Y : ℝ) := Real.sq_sqrt (by positivity)
    have hy0 : (Y : ℝ) ≠ 0 := ne_of_gt hYpos
    field_simp [hy0, ne_of_gt hsqrtPos]
    rw [hsquare]
    nlinarith
  rw [hmassEq]
  calc
    _ ≤ ((Finset.Ico Y (2 * Y)).filter (fun q => q % p = a.val)).card *
          (A * Real.log (Y : ℝ) / Y) := hsum
    _ ≤ (3 * Real.sqrt (Y : ℝ)) * (A * Real.log (Y : ℝ) / Y) :=
          mul_le_mul_of_nonneg_right hcardBound hAtomNonneg
    _ ≤ 3 * A * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) := hfinal

private lemma univariatePrimeRootProbability_le {Y p : ℕ} [NeZero p]
    (hp : p.Prime)
    (Q : Polynomial (ZMod p)) (hQ : Q ≠ 0) (d : ℕ) (hd : Q.natDegree ≤ d)
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤ B) :
    independentPrimePoolProbability (fun _ : Fin 1 => Y) (fun _ => 2 * Y)
      (fun x => Q.eval ((x 0 : ℕ) : ZMod p) = 0) ≤ (d : ℝ) * B := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let lo : Fin 1 → ℕ := fun _ => Y
  let hi : Fin 1 → ℕ := fun _ => 2 * Y
  let E : (Fin 1 → ZMod p) → Prop := fun r => Q.eval (r 0) = 0
  have hmap := independentPrimePoolProbability_mod_map lo hi p E
  have hformula : independentPrimePoolProbability lo hi
      (fun x => Q.eval ((x 0 : ℕ) : ZMod p) = 0) =
      ∑ r : Fin 1 → ZMod p,
        (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := by
    simpa [E, lo, hi] using hmap
  let roots : Finset (ZMod p) := Q.roots.toFinset
  have hrootsCard : roots.card ≤ Q.natDegree := by
    dsimp [roots]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q)
  have hroots : Finset.univ.filter (fun a : ZMod p => Q.eval a = 0) = roots := by
    ext a
    simp [roots, Polynomial.mem_roots hQ]
  have hclassSum :
      (∑ r : Fin 1 → ZMod p,
        (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0) =
      ∑ a : ZMod p, primePoolResidueMass lo hi p 0 a * if Q.eval a = 0 then 1 else 0 := by
    let e := finOneFunEquiv (ZMod p)
    apply Fintype.sum_equiv e
    intro r
    simp [e, finOneFunEquiv, E, lo, hi]
  have hrootsSum :
      (∑ a : ZMod p, primePoolResidueMass lo hi p 0 a * if Q.eval a = 0 then 1 else 0) =
      ∑ a ∈ roots, primePoolResidueMass lo hi p 0 a := by
    calc
      _ = ∑ a ∈ Finset.univ, if Q.eval a = 0 then primePoolResidueMass lo hi p 0 a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : Q.eval a = 0 <;> simp [h]
      _ = ∑ a ∈ Finset.univ.filter (fun a : ZMod p => Q.eval a = 0),
            primePoolResidueMass lo hi p 0 a := by
        rw [← Finset.sum_filter]
      _ = ∑ a ∈ roots, primePoolResidueMass lo hi p 0 a := by rw [hroots]
  have hBnonneg : 0 ≤ B := hB
  have hbound :
      (∑ a ∈ roots, primePoolResidueMass lo hi p 0 a) ≤
      (d : ℝ) * B := by
    calc
      _ ≤ ∑ a ∈ roots, B := by
        apply Finset.sum_le_sum
        intro a ha
        exact hmax a
      _ = (roots.card : ℝ) * B := by simp
      _ ≤ (d : ℝ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (hrootsCard.trans hd)) hBnonneg
  calc
    _ = ∑ r : Fin 1 → ZMod p,
          (∏ i, primePoolResidueMass lo hi p i (r i)) * if E r then 1 else 0 := hformula
    _ = ∑ a : ZMod p,
          primePoolResidueMass lo hi p 0 a * if Q.eval a = 0 then 1 else 0 := hclassSum
    _ = ∑ a ∈ roots, primePoolResidueMass lo hi p 0 a := hrootsSum
    _ ≤ (d : ℝ) * B := hbound

private lemma intPolynomial_map_ne_zero_of_large_coeff {m : ℕ}
    (P : IntegerPolynomial m) {s : Fin m →₀ ℕ} (hs : s ∈ P.support)
    (p : ℕ) [NeZero p] (hp : p.Prime) (habs : (P.coeff s).natAbs < p) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) P ≠ 0 := by
  intro hmap
  have hc : ((P.coeff s : ℤ) : ZMod p) = 0 := by
    have h := congrArg (fun Q : MvPolynomial (Fin m) (ZMod p) => Q.coeff s) hmap
    simpa [MvPolynomial.coeff_map] using h
  have hdvdInt : (p : ℤ) ∣ P.coeff s :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff s) p).mp hc
  have hdvdNat : p ∣ (P.coeff s).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvdInt)
  have hcoeff : P.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hpos : 0 < (P.coeff s).natAbs := Int.natAbs_pos.mpr hcoeff
  have hpLe : p ≤ (P.coeff s).natAbs := Nat.le_of_dvd hpos hdvdNat
  omega

private lemma intPolynomial_map_ne_zero_of_coeffMass_lt {m : ℕ}
    (P : IntegerPolynomial m) (hP : P ≠ 0) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hMass : roughCoefficientMass P < p) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) P ≠ 0 := by
  obtain ⟨s, hs⟩ := P.support_nonempty.mpr hP
  have hcoeff : (P.coeff s).natAbs ≤ roughCoefficientMass P := by
    unfold roughCoefficientMass
    exact Finset.single_le_sum (f := fun t => (P.coeff t).natAbs)
      (fun t ht => Nat.zero_le _) hs
  exact intPolynomial_map_ne_zero_of_large_coeff P hs p hp (hcoeff.trans_lt hMass)

private lemma totalDegree_map_le {m : ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P : MvPolynomial (Fin m) R) :
    (MvPolynomial.map f P).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree]
  exact Finset.sup_mono (MvPolynomial.support_map_subset f P)

private lemma inverse_square_telescoping (w : ℕ) (hw : 1 ≤ w) :
    ∀ L, w ≤ L →
      ∑ p ∈ Finset.Ico (w + 1) (L + 1),
        (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) = 1 / (w : ℝ) - 1 / (L : ℝ) := by
  intro L
  induction L with
  | zero => intro h; omega
  | succ L ih =>
      intro h
      by_cases hwL : w ≤ L
      · rw [Finset.sum_Ico_succ_top (by omega : w + 1 ≤ L + 1)
          (fun p : ℕ => 1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ))]
        rw [ih hwL]
        have hsub : (L + 1 - 1 : ℕ) = L := by omega
        simp only [hsub, Nat.cast_add, Nat.cast_one]
        ring
      · have hwEq : w = L + 1 := by omega
        subst w
        simp

private lemma inverse_square_Ico_tail_bound {w L : ℕ}
    (hw : 1 ≤ w) (hWL : w ≤ L) :
    ∑ p ∈ Finset.Ico (w + 1) (L + 1), 1 / (p : ℝ) ^ 2 ≤ 1 / (w : ℝ) := by
  have htel := inverse_square_telescoping w hw L hWL
  calc
    ∑ p ∈ Finset.Ico (w + 1) (L + 1), 1 / (p : ℝ) ^ 2 ≤
      ∑ p ∈ Finset.Ico (w + 1) (L + 1),
        (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpLower := (Finset.mem_Ico.mp hp).1
          have hp2 : 2 ≤ p := by omega
          have hpR : 1 < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
          have hminus : 0 < p - 1 := by omega
          have hdenPos : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hminus
          have hqLe : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast (Nat.sub_le p 1)
          have hpProd : ((p - 1 : ℕ) : ℝ) * p ≤ (p : ℝ) ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_right hqLe (by positivity : 0 ≤ (p : ℝ))]
          have hsub : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
            exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ p))
          calc
            1 / (p : ℝ) ^ 2 ≤ 1 / (((p - 1 : ℕ) : ℝ) * p) := by
              apply (div_le_div_iff₀ (by positivity) (by positivity)).2
              nlinarith
            _ = 1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ) := by
              field_simp
              nlinarith
    _ = 1 / (w : ℝ) - 1 / (L : ℝ) := htel
    _ ≤ 1 / (w : ℝ) := by
      have hLpos : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
      have hnonneg : 0 ≤ 1 / (L : ℝ) := by positivity
      linarith

private lemma natSqrt_recip_le {L : ℕ} (hL : 2 ≤ L) :
    1 / (Nat.sqrt L : ℝ) ≤ 2 / Real.sqrt (L : ℝ) := by
  have hw : 1 ≤ Nat.sqrt L := by
    exact Nat.sqrt_pos.mpr (by omega)
  have hwR : 0 < (Nat.sqrt L : ℝ) := by exact_mod_cast (Nat.sqrt_pos.mpr (by omega))
  have hsqrtPos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hroot : Real.sqrt (L : ℝ) ≤ (Nat.sqrt L : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast (Nat.lt_succ_sqrt' L).le
  have hroot2 : Real.sqrt (L : ℝ) ≤ 2 * (Nat.sqrt L : ℝ) := by
    have hwRone : (1 : ℝ) ≤ (Nat.sqrt L : ℝ) := by exact_mod_cast hw
    nlinarith
  rw [div_le_div_iff₀ hwR hsqrtPos]
  nlinarith

private lemma log_div_sqrt_antitone {L Y : ℕ} (hL : 9 ≤ L) (hLY : L ≤ Y) :
    Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) ≤
      Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
  have hexp2 : Real.exp 2 ≤ 9 := by
    have hsq' := (sq_lt_sq₀ (Real.exp_pos 1).le (by norm_num)).2 Real.exp_one_lt_three
    norm_num at hsq'
    exact hsq'.le
  have hLreal : (9 : ℝ) ≤ L := by exact_mod_cast hL
  have hLYreal : (L : ℝ) ≤ Y := by exact_mod_cast hLY
  have hExpL : Real.exp 2 ≤ (L : ℝ) := hexp2.trans hLreal
  have hExpY : Real.exp 2 ≤ (Y : ℝ) := hExpL.trans hLYreal
  exact Real.log_div_sqrt_antitoneOn (Set.mem_Ici.mpr hExpL)
    (Set.mem_Ici.mpr hExpY) hLYreal

private lemma log_sqrt_lower {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    Real.log (2 : ℝ) / N ≤ Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hLNreal : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hroot : Real.sqrt (L : ℝ) ≤ (L : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hLreal)
  have hNroot : Real.sqrt (L : ℝ) ≤ (N : ℝ) := hroot.trans hLNreal
  have hsqrtPos : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2L : Real.log (2 : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hL)
  have hrecip := one_div_le_one_div_of_le hsqrtPos hNroot
  calc
    _ = Real.log 2 * (1 / (N : ℝ)) := by ring
    _ ≤ Real.log 2 * (1 / Real.sqrt (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip hlog2
    _ = Real.log 2 / Real.sqrt (L : ℝ) := by ring
    _ ≤ Real.log (L : ℝ) / Real.sqrt (L : ℝ) :=
      div_le_div_of_nonneg_right hlog2L hsqrtPos.le

private lemma evalIntegerPolynomial_mod_eq {m : ℕ} (P : IntegerPolynomial m)
    (p : ℕ) [NeZero p] (x : Fin m → ℕ) :
    MvPolynomial.eval (fun i => (x i : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) P) =
      ((evalIntegerPolynomial P (fun i => (x i : ℤ)) : ℤ) : ZMod p) := by
  let q := Int.castRingHom (ZMod p)
  have hfun : (fun i : Fin m => (x i : ZMod p)) =
      q ∘ (fun i => (x i : ℤ)) := by
    funext i
    change (x i : ZMod p) = ((x i : ℤ) : ZMod p)
    norm_cast
  calc
    MvPolynomial.eval (fun i => (x i : ZMod p)) (MvPolynomial.map q P) =
        MvPolynomial.eval₂ q (fun i => (x i : ZMod p)) P := by
          rw [MvPolynomial.eval₂_eq_eval_map]
    _ = MvPolynomial.eval (q ∘ (fun i => (x i : ℤ))) (MvPolynomial.map q P) := by
          rw [hfun]
          exact MvPolynomial.eval₂_eq_eval_map q (q ∘ (fun i => (x i : ℤ))) P
    _ = q (MvPolynomial.eval (fun i => (x i : ℤ)) P) :=
          (MvPolynomial.map_eval q (fun i => (x i : ℤ)) P).symm
    _ = ((evalIntegerPolynomial P (fun i => (x i : ℤ)) : ℤ) : ZMod p) := by
          rfl

private lemma int_dvd_eval_iff_mod_zero {m p : ℕ} [NeZero p]
    (P : IntegerPolynomial m) (x : Fin m → ℕ) :
    (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ↔
      MvPolynomial.eval (fun i => (x i : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) P) = 0 := by
  rw [evalIntegerPolynomial_mod_eq]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

private lemma conditionalMainVariableDivProbability_le {n Y p : ℕ} [NeZero p]
    (hp : p.Prime) (F : IntegerPolynomial (n + 1)) (z : Fin n → ℕ)
    (d : ℕ) (Aint : IntegerPolynomial n)
    (hd : (MvPolynomial.map (Int.castRingHom (ZMod p)) F).degreeOf 0 = d)
    (hAint : Aint = (MvPolynomial.finSuccEquiv ℤ n F).coeff d)
    (hlead : MvPolynomial.eval (fun j => (z j : ZMod p))
      (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤ B) :
    independentPrimePoolProbability (fun _ : Fin 1 => Y) (fun _ => 2 * Y)
      (fun x => (p : ℤ) ∣ evalIntegerPolynomial F
      (fun i => ((Fin.cases (x 0) z i : ℕ) : ℤ))) ≤ (d : ℝ) * B := by
  classical
  let cast : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Pp : MvPolynomial (Fin (n + 1)) (ZMod p) := MvPolynomial.map cast F
  let Ppoly : Polynomial (MvPolynomial (Fin n) (ZMod p)) :=
    MvPolynomial.finSuccEquiv (ZMod p) n Pp
  let tailZ : Fin n → ZMod p := fun j => (z j : ZMod p)
  let Q : Polynomial (ZMod p) := Polynomial.map (MvPolynomial.eval tailZ) Ppoly
  have hPdeg : Ppoly.natDegree = d := by
    dsimp [Ppoly, Pp]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact hd
  have hcoeff : Q.coeff d = MvPolynomial.eval tailZ
      (MvPolynomial.map cast ((MvPolynomial.finSuccEquiv ℤ n F).coeff d)) := by
    simpa [Q, Ppoly, Pp, cast] using
      (finSuccEquiv_specialized_coeff (Int.castRingHom (ZMod p)) tailZ F d)
  have hcoeffNe : Q.coeff d ≠ 0 := by
    rw [hcoeff, ← hAint]
    exact hlead
  have hCoeffP : Ppoly.coeff d = MvPolynomial.map cast Aint := by
    dsimp [Ppoly, Pp, cast]
    rw [finSuccEquiv_map]
    simp only [Polynomial.coeff_map]
    rw [hAint]
  have hleadP : MvPolynomial.eval tailZ Ppoly.leadingCoeff ≠ 0 := by
    rw [Polynomial.leadingCoeff, hPdeg, hCoeffP]
    exact hlead
  have hQdeg : Q.natDegree = d := by
    dsimp [Q]
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (MvPolynomial.eval tailZ) hleadP]
    exact hPdeg
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hcoeffNe
    simp [hzero]
  have hQdegLe : Q.natDegree ≤ d := by rw [hQdeg]
  let lo : Fin 1 → ℕ := fun _ => Y
  let hi : Fin 1 → ℕ := fun _ => 2 * Y
  have hroot := univariatePrimeRootProbability_le (Y := Y) (p := p) hp
    Q hQ d hQdegLe B hB hmax
  have heval (x : Fin 1 → ℕ) :
      (p : ℤ) ∣ evalIntegerPolynomial F
          (fun i => ((Fin.cases (x 0) z i : ℕ) : ℤ)) ↔
        Q.eval ((x 0 : ℕ) : ZMod p) = 0 := by
    have hmod := evalIntegerPolynomial_mod_eq F p (fun i => Fin.cases (x 0) z i)
    have hspec : MvPolynomial.eval
        (fun i => ((Fin.cases (x 0) z i : ℕ) : ZMod p)) Pp =
        Q.eval ((x 0 : ℕ) : ZMod p) := by
      have htuple :
          (fun i : Fin (n + 1) => ((Fin.cases (x 0) z i : ℕ) : ZMod p)) =
            Fin.cons ((x 0 : ℕ) : ZMod p) tailZ := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [htuple]
      simpa [Q, Ppoly, Pp, tailZ, cast] using
        (MvPolynomial.eval_eq_eval_mv_eval' tailZ ((x 0 : ℕ) : ZMod p) Pp)
    calc
      _ ↔ ((evalIntegerPolynomial F
          (fun i => ((Fin.cases (x 0) z i : ℕ) : ℤ)) : ℤ) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
      _ ↔ MvPolynomial.eval
          (fun i => ((Fin.cases (x 0) z i : ℕ) : ZMod p)) Pp = 0 := by
            rw [← hmod]
      _ ↔ Q.eval ((x 0 : ℕ) : ZMod p) = 0 := by rw [hspec]
  have hprob : independentPrimePoolProbability lo hi
      (fun x => (p : ℤ) ∣ evalIntegerPolynomial F
        (fun i => ((Fin.cases (x 0) z i : ℕ) : ℤ))) =
      independentPrimePoolProbability lo hi (fun x => Q.eval ((x 0 : ℕ) : ZMod p) = 0) := by
    classical
    unfold independentPrimePoolProbability
    apply tsum_congr
    intro x
    by_cases hdiv : (p : ℤ) ∣ evalIntegerPolynomial F
        (fun i => ((Fin.cases (x 0) z i : ℕ) : ℤ))
    · have hroot : Q.eval ((x 0 : ℕ) : ZMod p) = 0 := (heval x).1 hdiv
      simp [hdiv, hroot]
    · have hroot : Q.eval ((x 0 : ℕ) : ZMod p) ≠ 0 := by
        intro hz
        exact hdiv ((heval x).2 hz)
      simp [hdiv, hroot]
  calc
    _ = independentPrimePoolProbability lo hi (fun x => Q.eval ((x 0 : ℕ) : ZMod p) = 0) := hprob
    _ ≤ (d : ℝ) * B := hroot

set_option maxHeartbeats 1000000 in
private lemma conditionalMainVariableDivProbability_integrated {n Y p : ℕ}
    [NeZero p] (hp : p.Prime)
    (loTail hiTail : Fin n → ℕ) (hmassTail : ∀ j,
      0 < primePoolMass (loTail j) (hiTail j))
    (F : IntegerPolynomial (n + 1)) (d : ℕ) (Aint : IntegerPolynomial n)
    (hd : (MvPolynomial.map (Int.castRingHom (ZMod p)) F).degreeOf 0 = d)
    (hAint : Aint = (MvPolynomial.finSuccEquiv ℤ n F).coeff d)
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤ B) :
    independentPrimePoolProbability (Fin.cons Y loTail) (Fin.cons (2 * Y) hiTail)
      (fun x =>
        (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
        MvPolynomial.eval (fun j => (x j.succ : ZMod p))
          (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0) ≤ (d : ℝ) * B := by
  classical
  let E : (Fin (n + 1) → ℕ) → Prop := fun x =>
    (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
      MvPolynomial.eval (fun j => (x j.succ : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0
  letI : DecidablePred E := fun x => Classical.propDecidable (E x)
  have hsplit := independentPrimePoolProbability_finCons
    (lo := Fin.cons Y loTail) (hi := Fin.cons (2 * Y) hiTail) E
  have htailsum :
      (∑ z ∈ primeTupleSupport loTail hiTail, independentPrimePoolMass loTail hiTail z) = 1 := by
    have htrue := independentPrimePoolProbability_true loTail hiTail hmassTail
    unfold independentPrimePoolProbability at htrue
    rw [tsum_eq_sum (s := primeTupleSupport loTail hiTail)] at htrue
    · simpa [primeTupleSupport, independentPrimePoolMass] using htrue
    · intro z hz
      rw [independentPrimePoolMass_zero_of_not_mem_support loTail hiTail z hz]
      simp
  have hinner (z : Fin n → ℕ) :
      ∑ q ∈ Finset.Ico Y (2 * Y),
        primePoolLaw Y (2 * Y) q * (if E (Fin.cons q z) then 1 else 0) ≤
          (d : ℝ) * B := by
    let leadNZ : Prop :=
      MvPolynomial.eval (fun j => (z j : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0
    by_cases hlead : leadNZ
    · have hsingle :
          independentPrimePoolProbability (fun _ : Fin 1 => Y) (fun _ => 2 * Y)
            (fun u => (p : ℤ) ∣ evalIntegerPolynomial F
              (fun i => ((Fin.cases (u 0) z i : ℕ) : ℤ))) =
          ∑ q ∈ Finset.Ico Y (2 * Y),
            primePoolLaw Y (2 * Y) q *
              (if (p : ℤ) ∣ evalIntegerPolynomial F
              (fun i => ((Fin.cases q z i : ℕ) : ℤ)) then 1 else 0) := by
        let z0 : Fin 0 → ℕ := Fin.elim0
        have hsupport :
            primeTupleSupport (fun _ : Fin 0 => Y) (fun _ => 2 * Y) = {z0} := by
          ext x
          simp only [primeTupleSupport, Fintype.mem_piFinset, Finset.mem_singleton]
          constructor
          · intro _
            exact Subsingleton.elim _ _
          · intro _
            intro i
            exact Fin.elim0 i
        have h := independentPrimePoolProbability_finCons
          (lo := fun _ : Fin 1 => Y) (hi := fun _ : Fin 1 => 2 * Y)
          (fun u : Fin 1 → ℕ => (p : ℤ) ∣ evalIntegerPolynomial F
            (fun i => ((Fin.cases (u 0) z i : ℕ) : ℤ)))
        rw [hsupport, Finset.sum_singleton] at h
        have hmass0 :
            independentPrimePoolMass (fun _ : Fin 0 => Y) (fun _ => 2 * Y) z0 = 1 := by
          simp [independentPrimePoolMass]
        rw [hmass0, one_mul] at h
        simpa [Fin.cons_zero] using h
      have hcoeff :
          MvPolynomial.eval (fun j => (z j : ZMod p))
            (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0 := hlead
      have hcond := conditionalMainVariableDivProbability_le hp F z d Aint hd hAint
        hcoeff B hB hmax
      rw [hsingle] at hcond
      have hEeq (q : ℕ) : E (Fin.cons q z) ↔
          (p : ℤ) ∣ evalIntegerPolynomial F
            (fun i => ((Fin.cases q z i : ℕ) : ℤ)) := by
        simp only [E, Fin.cons_zero, Fin.cons_succ, leadNZ]
        exact and_iff_left hlead
      have hsumEq :
          (∑ q ∈ Finset.Ico Y (2 * Y),
            primePoolLaw Y (2 * Y) q * (if E (Fin.cons q z) then 1 else 0)) =
          (∑ q ∈ Finset.Ico Y (2 * Y),
            primePoolLaw Y (2 * Y) q *
              (if (p : ℤ) ∣ evalIntegerPolynomial F
                (fun i => ((Fin.cases q z i : ℕ) : ℤ)) then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hE : E (Fin.cons q z)
        · have hdiv := (hEeq q).1 hE
          simp [hE, hdiv]
        · have hdiv : ¬ ((p : ℤ) ∣ evalIntegerPolynomial F
              (fun i => ((Fin.cases q z i : ℕ) : ℤ))) := by
            intro hdiv
            exact hE ((hEeq q).2 hdiv)
          simp [hE, hdiv]
      calc
        _ = ∑ q ∈ Finset.Ico Y (2 * Y),
              primePoolLaw Y (2 * Y) q *
                (if (p : ℤ) ∣ evalIntegerPolynomial F
                  (fun i => ((Fin.cases q z i : ℕ) : ℤ)) then 1 else 0) := hsumEq
        _ ≤ (d : ℝ) * B := hcond
    · have hzero : ∀ q ∈ Finset.Ico Y (2 * Y), ¬ E (Fin.cons q z) := by
        intro q hq hEq
        exact hlead hEq.2
      calc
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro q hq
          simp [hzero q hq]
        _ ≤ (d : ℝ) * B := mul_nonneg (by positivity) hB
  rw [hsplit]
  calc
    _ ≤ ∑ z ∈ primeTupleSupport loTail hiTail,
          independentPrimePoolMass loTail hiTail z * ((d : ℝ) * B) := by
            apply Finset.sum_le_sum
            intro z hz
            exact mul_le_mul_of_nonneg_left (hinner z)
              (independentPrimePoolMass_nonneg loTail hiTail z)
    _ = (d : ℝ) * B := by
          rw [← Finset.sum_mul, htailsum]
          ring

private lemma roughMainDivProbability_with_leading_unit {n Y p : ℕ}
    [NeZero p] (hp : p.Prime)
    (loTail hiTail : Fin n → ℕ) (hmassTail : ∀ j,
      0 < primePoolMass (loTail j) (hiTail j))
    (P : IntegerPolynomial (n + 1))
    (hmap : MvPolynomial.map (Int.castRingHom (ZMod p))
      (roughMainCoefficientTail P) ≠ 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤ B) :
    independentPrimePoolProbability (Fin.cons Y loTail) (Fin.cons (2 * Y) hiTail)
      (fun x =>
        (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient P)
          (fun i => (x i : ℤ))) ≤ (roughMainDegree P : ℝ) * B := by
  classical
  let Aint := roughMainCoefficientTail P
  let Eint : (Fin (n + 1) → ℕ) → Prop := fun x =>
    (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ∧
      ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient P)
        (fun i => (x i : ℤ))
  let Emod : (Fin (n + 1) → ℕ) → Prop := fun x =>
    (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ∧
      MvPolynomial.eval (fun j => (x j.succ : ZMod p))
        (MvPolynomial.map (Int.castRingHom (ZMod p)) Aint) ≠ 0
  letI : DecidablePred Eint := fun x => Classical.propDecidable (Eint x)
  letI : DecidablePred Emod := fun x => Classical.propDecidable (Emod x)
  have hEq (x : Fin (n + 1) → ℕ) : Eint x ↔ Emod x := by
    dsimp [Eint, Emod, Aint]
    rw [eval_roughMainCoefficient]
    have hdiv := int_dvd_eval_iff_mod_zero (p := p) (roughMainCoefficientTail P)
      (fun j => x j.succ)
    simp only [hdiv]
  have hprobEq :
      independentPrimePoolProbability (Fin.cons Y loTail) (Fin.cons (2 * Y) hiTail) Eint =
      independentPrimePoolProbability (Fin.cons Y loTail) (Fin.cons (2 * Y) hiTail) Emod := by
    unfold independentPrimePoolProbability
    apply tsum_congr
    intro x
    by_cases he : Eint x
    · have hm : Emod x := (hEq x).1 he
      simp [he, hm]
    · have hm : ¬ Emod x := fun hm => he ((hEq x).2 hm)
      simp [he, hm]
  have hd := roughMainDegree_map_eq P hmap
  have hroot := conditionalMainVariableDivProbability_integrated hp loTail hiTail
    hmassTail P (roughMainDegree P) Aint hd rfl B hB hmax
  rw [hprobEq]
  exact hroot

private lemma roughMainDivProbability_upper_endpoint {n Y0 Y p : ℕ}
    [NeZero p] (hp : p.Prime) (hY0 : 2 ≤ Y0) (hY0large : 9 ≤ Y0)
    (hY0Y : Y0 ≤ Y)
    (hY0p : Y0 ≤ p ^ 2)
    (loTail hiTail : Fin n → ℕ) (hmassTail : ∀ j,
      0 < primePoolMass (loTail j) (hiTail j))
    (P : IntegerPolynomial (n + 1))
    (hmap : MvPolynomial.map (Int.castRingHom (ZMod p))
      (roughMainCoefficientTail P) ≠ 0)
    (Cbt Aatom : ℝ) (hCbt : 0 < Cbt) (hAatom : 0 < Aatom)
    (hBT : p ^ 2 ≤ Y → ∀ a : Fin p,
      0 < a.val →
      (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
        if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ Cbt / p)
    (hAtom : ∀ Y' q, 2 ≤ Y' →
      primePoolLaw Y' (2 * Y') q ≤ Aatom * Real.log (Y' : ℝ) / Y') :
    independentPrimePoolProbability (Fin.cons Y loTail) (Fin.cons (2 * Y) hiTail)
      (fun x =>
        (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient P)
          (fun i => (x i : ℤ))) ≤
      (roughMainDegree P : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) *
        (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by
  classical
  have hY0pos : (0 : ℝ) < Y0 := by exact_mod_cast (by omega : 0 < Y0)
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hsqrtY0 : 0 < Real.sqrt (Y0 : ℝ) := Real.sqrt_pos.2 hY0pos
  have hlogY0 : 0 ≤ Real.log (Y0 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y0))
  have hTnonneg : 0 ≤ Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ) :=
    div_nonneg hlogY0 (Real.sqrt_nonneg _)
  have hmapCoeff := hmap
  have hdegree := roughMainDegree_map_eq P hmapCoeff
  by_cases hpY : p ^ 2 ≤ Y
  · have hBTi := hBT hpY
    have hmax : ∀ a : ZMod p,
        primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤ Cbt / p := by
      intro a
      have h := dyadicPrimeResidueMass_le_brun_titchmarsh hp hpY Cbt hCbt.le hBTi a
      simpa [primePoolResidueMass, dyadicPrimeResidueMass] using h
    have hroot := roughMainDivProbability_with_leading_unit hp loTail hiTail
      hmassTail P hmap (Cbt / p) (by positivity) hmax
    have hsqrtp : Real.sqrt (Y0 : ℝ) ≤ (p : ℝ) := by
      rw [Real.sqrt_le_left hpPos.le]
      exact_mod_cast hY0p
    have hrecip := one_div_le_one_div_of_le hsqrtY0 hsqrtp
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogCompare : Real.log (2 : ℝ) ≤ Real.log (Y0 : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hY0)
    have hpart : 1 / Real.sqrt (Y0 : ℝ) ≤
        (1 / Real.log 2) * (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by
      field_simp [hlog2pos.ne', hsqrtY0.ne']
      nlinarith
    have hscale : (roughMainDegree P : ℝ) * (Cbt / p) ≤
        (roughMainDegree P : ℝ) * (Cbt / Real.log 2) *
          (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by
      calc
        _ = (roughMainDegree P : ℝ) * Cbt * (1 / (p : ℝ)) := by ring
        _ ≤ (roughMainDegree P : ℝ) * Cbt * (1 / Real.sqrt (Y0 : ℝ)) :=
              mul_le_mul_of_nonneg_left hrecip (by positivity)
        _ ≤ (roughMainDegree P : ℝ) * Cbt *
              ((1 / Real.log 2) * (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) :=
              mul_le_mul_of_nonneg_left hpart (by positivity)
        _ = _ := by ring
    have hcoeffle : (roughMainDegree P : ℝ) * (Cbt / Real.log 2) ≤
        (roughMainDegree P : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · positivity
    exact hroot.trans (hscale.trans
      (mul_le_mul_of_nonneg_right hcoeffle hTnonneg))
  · have hsqrtY : Real.sqrt (Y : ℝ) < (p : ℝ) := by
      apply (Real.sqrt_lt (by positivity) (by positivity)).2
      exact_mod_cast (Nat.lt_of_not_ge hpY)
    have hmax : ∀ a : ZMod p,
        primePoolResidueMass (fun _ : Fin 1 => Y) (fun _ => 2 * Y) p 0 a ≤
          3 * Aatom * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) := by
      intro a
      have h := dyadicPrimeResidueMass_le_large_prime hp
        (by omega : 2 ≤ Y) hsqrtY Aatom hAatom hAtom a
      simpa [primePoolResidueMass, dyadicPrimeResidueMass] using h
    have hroot := roughMainDivProbability_with_leading_unit hp loTail hiTail
      hmassTail P hmap
      (3 * Aatom * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ)) (by positivity) hmax
    have hratio := log_div_sqrt_antitone hY0large (by omega : Y0 ≤ Y)
    have hscale :
        (roughMainDegree P : ℝ) *
          (3 * Aatom * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ)) ≤
        (roughMainDegree P : ℝ) * (3 * Aatom) *
          (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by
      rw [show 3 * Aatom * Real.log (Y : ℝ) / Real.sqrt (Y : ℝ) =
        (3 * Aatom) * (Real.log (Y : ℝ) / Real.sqrt (Y : ℝ)) by ring]
      calc
        _ = ((roughMainDegree P : ℝ) * (3 * Aatom)) *
              (Real.log (Y : ℝ) / Real.sqrt (Y : ℝ)) := by ring
        _ ≤ ((roughMainDegree P : ℝ) * (3 * Aatom)) *
              (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by ring
    have hcoeffle : (roughMainDegree P : ℝ) * (3 * Aatom) ≤
        (roughMainDegree P : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) := by
      apply mul_le_mul_of_nonneg_left
      · exact le_add_of_nonneg_left (div_nonneg hCbt.le (Real.log_pos (by norm_num)).le)
      · positivity
    exact hroot.trans (hscale.trans
      (mul_le_mul_of_nonneg_right hcoeffle hTnonneg))

private lemma roughMainPairDivProbability_with_leading_units
    {nF nG YF YG p : ℕ} [NeZero p] (hp : p.Prime)
    (loFTail hiFTail : Fin nF → ℕ) (hmassFTail : ∀ i,
      0 < primePoolMass (loFTail i) (hiFTail i))
    (loGTail hiGTail : Fin nG → ℕ) (hmassGTail : ∀ j,
      0 < primePoolMass (loGTail j) (hiGTail j))
    (F : IntegerPolynomial (nF + 1)) (G : IntegerPolynomial (nG + 1))
    (hmapF : MvPolynomial.map (Int.castRingHom (ZMod p))
      (roughMainCoefficientTail F) ≠ 0)
    (hmapG : MvPolynomial.map (Int.castRingHom (ZMod p))
      (roughMainCoefficientTail G) ≠ 0)
    (BF BG : ℝ) (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hmaxF : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => YF) (fun _ => 2 * YF) p 0 a ≤ BF)
    (hmaxG : ∀ a : ZMod p,
      primePoolResidueMass (fun _ : Fin 1 => YG) (fun _ => 2 * YG) p 0 a ≤ BG) :
    independentPrimePairProbability (Fin.cons YF loFTail) (Fin.cons (2 * YF) hiFTail)
      (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail)
      (fun x y =>
        ((p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
          ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
            (fun i => (x i : ℤ))) ∧
        ((p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
          ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
            (fun j => (y j : ℤ)))) ≤
      (roughMainDegree F : ℝ) * BF * ((roughMainDegree G : ℝ) * BG) := by
  classical
  let EF : (Fin (nF + 1) → ℕ) → Prop := fun x =>
    (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
      ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
        (fun i => (x i : ℤ))
  let EG : (Fin (nG + 1) → ℕ) → Prop := fun y =>
    (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
      ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
        (fun j => (y j : ℤ))
  letI : DecidablePred EF := fun x => Classical.propDecidable (EF x)
  letI : DecidablePred EG := fun y => Classical.propDecidable (EG y)
  have hF := roughMainDivProbability_with_leading_unit hp loFTail hiFTail
    hmassFTail F hmapF BF hBF hmaxF
  have hG := roughMainDivProbability_with_leading_unit hp loGTail hiGTail
    hmassGTail G hmapG BG hBG hmaxG
  have hprod := independentPrimePairProbability_product
    (Fin.cons YF loFTail) (Fin.cons (2 * YF) hiFTail)
    (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail) EF EG
  have hGnonneg : 0 ≤ independentPrimePoolProbability
      (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail) EG := by
    unfold independentPrimePoolProbability
    apply tsum_nonneg
    intro y
    exact mul_nonneg
      (independentPrimePoolMass_nonneg (Fin.cons YG loGTail)
        (Fin.cons (2 * YG) hiGTail) y) (by positivity)
  have hFboundNonneg : 0 ≤ (roughMainDegree F : ℝ) * BF := by positivity
  calc
    _ = independentPrimePoolProbability (Fin.cons YF loFTail)
          (Fin.cons (2 * YF) hiFTail) EF *
        independentPrimePoolProbability (Fin.cons YG loGTail)
          (Fin.cons (2 * YG) hiGTail) EG := by
            simpa [EF, EG] using hprod
    _ ≤ ((roughMainDegree F : ℝ) * BF) * ((roughMainDegree G : ℝ) * BG) :=
          mul_le_mul hF hG hGnonneg hFboundNonneg

private lemma roughMainMediumPrimeProbability_bound
    {nF nG L Y0 : ℕ} (F : IntegerPolynomial (nF + 1))
    (G : IntegerPolynomial (nG + 1)) (hF : F ≠ 0) (hG : G ≠ 0)
    (YF : Fin (nF + 1) → ℕ) (YG : Fin (nG + 1) → ℕ)
    (hYF : ∀ i, L ≤ YF i) (hYG : ∀ j, L ≤ YG j)
    (hY0 : 9 ≤ L) (hLY0 : L ≤ Y0)
    (hY0F : Y0 ≤ YF 0) (hY0G : Y0 ≤ YG 0)
    (hcutF : (roughCoefficientMass (roughMainCoefficientTail F) + 1) ^ 2 ≤ L)
    (hcutG : (roughCoefficientMass (roughMainCoefficientTail G) + 1) ^ 2 ≤ L)
    (Cbt : ℝ) (hCbt : 0 < Cbt) (Ybt : ℕ) (hYbt : Ybt ≤ L)
    (hBT : ∀ Y, Ybt ≤ Y → ∀ p, p.Prime → p ^ 2 ≤ Y → ∀ a : Fin p,
      0 < a.val →
      (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
        if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ Cbt / p) :
    independentPrimePairProbability YF (fun i => 2 * YF i)
      YG (fun j => 2 * YG j)
      (fun x y =>
        ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧ p ^ 2 ≤ Y0 ∧
          ((p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
              (fun i => (x i : ℤ))) ∧
          ((p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
            ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
              (fun j => (y j : ℤ)))) ≤
      ((F.totalDegree : ℝ) * (G.totalDegree : ℝ) * Cbt ^ 2) *
        ((2 / Real.log 2) * (Real.log (L : ℝ) / Real.sqrt (L : ℝ))) := by
  classical
  let w : ℕ := Nat.sqrt L
  let S : Finset ℕ := Finset.Ico (w + 1) (Y0 + 1)
  let Ep : ℕ → (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop := fun p x y =>
    p.Prime ∧ p ^ 2 ≤ Y0 ∧
      ((p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
          (fun i => (x i : ℤ))) ∧
      ((p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
          (fun j => (y j : ℤ)))
  let Emid : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop := fun x y =>
    ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧ p ^ 2 ≤ Y0 ∧
      ((p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
          (fun i => (x i : ℤ))) ∧
      ((p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
          (fun j => (y j : ℤ)))
  letI : DecidableRel Emid := fun x y => Classical.propDecidable (Emid x y)
  have hWone : 1 ≤ w := by dsimp [w]; exact Nat.sqrt_pos.mpr (by omega)
  have hWY0 : w ≤ Y0 := by
    dsimp [w]
    exact (Nat.sqrt_le_self L).trans hLY0
  have hsubset : ∀ x y, Emid x y → ∃ p ∈ S, Ep p x y := by
    intro x y h
    rcases h with ⟨p, hp, hsqrt, hpY0, hFdiv, hGdiv⟩
    have hLltp : L < p ^ 2 := by
      have h := (Real.sqrt_lt' (by exact_mod_cast hp.pos)).1 hsqrt
      exact_mod_cast h
    have hwltp : w < p := by
      dsimp [w]
      exact (Nat.sqrt_lt').2 hLltp
    have hpLower : w + 1 ≤ p := by omega
    have hpUpper : p < Y0 + 1 := by
      have hp2 : p ≤ p ^ 2 := by
        calc
          p = p * 1 := by simp
          _ ≤ p * p := Nat.mul_le_mul_left p (by omega : 1 ≤ p)
          _ = p ^ 2 := by rw [pow_two]
      omega
    refine ⟨p, Finset.mem_Ico.mpr ⟨hpLower, hpUpper⟩, ?_⟩
    exact ⟨hp, hpY0, hFdiv, hGdiv⟩
  have hmono := independentPrimePairProbability_mono YF (fun i => 2 * YF i)
    YG (fun j => 2 * YG j) Emid (fun x y => ∃ p ∈ S, Ep p x y) hsubset
  have hunion := independentPrimePairProbability_finset_union_le
    YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) S Ep
  let Dbase : ℝ := (F.totalDegree : ℝ) * (G.totalDegree : ℝ) * Cbt ^ 2
  have hDbase : 0 ≤ Dbase := by dsimp [Dbase]; positivity
  have hterm : ∀ p ∈ S,
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (Ep p) ≤ Dbase / (p : ℝ) ^ 2 := by
    intro p hpS
    have hR : 0 ≤ Dbase / (p : ℝ) ^ 2 := div_nonneg hDbase (by positivity)
    by_cases hp : p.Prime
    · by_cases hp2 : p ^ 2 ≤ Y0
      · have hpLower : w < p := by
          have hpLower' : w + 1 ≤ p := (Finset.mem_Ico.mp hpS).1
          omega
        have hLltp : L < p ^ 2 := by
          have hNat : Nat.sqrt L < p := by simpa [w] using hpLower
          exact (Nat.sqrt_lt').1 hNat
        letI : NeZero p := ⟨hp.ne_zero⟩
        have hcutFp : roughCoefficientMass (roughMainCoefficientTail F) < p :=
          nat_lt_of_squares_cut hcutF (Nat.le_of_lt hLltp)
        have hcutGp : roughCoefficientMass (roughMainCoefficientTail G) < p :=
          nat_lt_of_squares_cut hcutG (Nat.le_of_lt hLltp)
        have hmapF : MvPolynomial.map (Int.castRingHom (ZMod p))
            (roughMainCoefficientTail F) ≠ 0 :=
          intPolynomial_map_ne_zero_of_coeffMass_lt (roughMainCoefficientTail F)
            (roughMainCoefficientTail_ne_zero F hF) p hp hcutFp
        have hmapG : MvPolynomial.map (Int.castRingHom (ZMod p))
            (roughMainCoefficientTail G) ≠ 0 :=
          intPolynomial_map_ne_zero_of_coeffMass_lt (roughMainCoefficientTail G)
            (roughMainCoefficientTail_ne_zero G hG) p hp hcutGp
        have hBTi (Yi : ℕ) (hYi : Ybt ≤ Yi) (hpYi : p ^ 2 ≤ Yi) :
            ∀ a : Fin p, 0 < a.val →
              (∑ q ∈ (Finset.Ico Yi (2 * Yi)).filter Nat.Prime,
                if q % p = a.val then primePoolLaw Yi (2 * Yi) q else 0) ≤ Cbt / p :=
          hBT Yi hYi p hp hpYi
        have hmaxF : ∀ a : ZMod p,
            primePoolResidueMass (fun _ : Fin 1 => YF 0)
              (fun _ => 2 * YF 0) p 0 a ≤ Cbt / p := by
          intro a
          have hYi : Ybt ≤ YF 0 := le_trans hYbt (hYF 0)
          have hpYi : p ^ 2 ≤ YF 0 := le_trans hp2 hY0F
          have h := dyadicPrimeResidueMass_le_brun_titchmarsh hp hpYi Cbt hCbt.le
            (hBTi (YF 0) hYi hpYi) a
          simpa [primePoolResidueMass, dyadicPrimeResidueMass] using h
        have hmaxG : ∀ a : ZMod p,
            primePoolResidueMass (fun _ : Fin 1 => YG 0)
              (fun _ => 2 * YG 0) p 0 a ≤ Cbt / p := by
          intro a
          have hYj : Ybt ≤ YG 0 := le_trans hYbt (hYG 0)
          have hpYj : p ^ 2 ≤ YG 0 := le_trans hp2 hY0G
          have h := dyadicPrimeResidueMass_le_brun_titchmarsh hp hpYj Cbt hCbt.le
            (hBTi (YG 0) hYj hpYj) a
          simpa [primePoolResidueMass, dyadicPrimeResidueMass] using h
        have hpair := roughMainPairDivProbability_with_leading_units hp
          (fun i => YF i.succ) (fun i => 2 * YF i.succ)
          (by intro i
              exact dyadicPrimePoolMass_pos (YF i.succ)
                ((by omega : 2 ≤ L).trans (hYF i.succ)))
          (fun j => YG j.succ) (fun j => 2 * YG j.succ)
          (by intro j
              exact dyadicPrimePoolMass_pos (YG j.succ)
                ((by omega : 2 ≤ L).trans (hYG j.succ)))
          F G hmapF hmapG (Cbt / p) (Cbt / p) (by positivity) (by positivity)
          (by intro a; simpa using hmaxF a) (by intro a; simpa using hmaxG a)
        have hdegF : (roughMainDegree F : ℝ) ≤ F.totalDegree := by
          exact_mod_cast MvPolynomial.degreeOf_le_totalDegree F 0
        have hdegG : (roughMainDegree G : ℝ) ≤ G.totalDegree := by
          exact_mod_cast MvPolynomial.degreeOf_le_totalDegree G 0
        have hdegprod : (roughMainDegree F : ℝ) * (roughMainDegree G : ℝ) ≤
            (F.totalDegree : ℝ) * (G.totalDegree : ℝ) :=
          mul_le_mul hdegF hdegG (by positivity) (by positivity)
        have hpair' : independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun j => 2 * YG j) (Ep p) ≤
            ((roughMainDegree F : ℝ) * (roughMainDegree G : ℝ)) *
              (Cbt ^ 2 / (p : ℝ) ^ 2) := by
          have hFLo : Fin.cons (YF 0) (fun i : Fin nF => YF i.succ) = YF := by
            funext i
            exact Fin.cases rfl (fun j => rfl) i
          have hFHi : Fin.cons (2 * YF 0) (fun i : Fin nF => 2 * YF i.succ) =
              (fun i => 2 * YF i) := by
            funext i
            exact Fin.cases rfl (fun j => rfl) i
          have hGLo : Fin.cons (YG 0) (fun j : Fin nG => YG j.succ) = YG := by
            funext j
            exact Fin.cases rfl (fun j => rfl) j
          have hGHi : Fin.cons (2 * YG 0) (fun j : Fin nG => 2 * YG j.succ) =
              (fun j => 2 * YG j) := by
            funext j
            exact Fin.cases rfl (fun j => rfl) j
          have hEqEvent : Ep p = (fun x y =>
              ((p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
                ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient F)
                  (fun i => (x i : ℤ))) ∧
              ((p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
                ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
                  (fun j => (y j : ℤ)))) := by
            funext x y
            simp [Ep, hp, hp2]
          have hpairFull : independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) (Ep p) ≤
              ((roughMainDegree F : ℝ) * (Cbt / p)) *
                ((roughMainDegree G : ℝ) * (Cbt / p)) := by
            simpa [hFLo, hFHi, hGLo, hGHi, hEqEvent] using hpair
          calc
            _ ≤ ((roughMainDegree F : ℝ) * (Cbt / p)) *
                  ((roughMainDegree G : ℝ) * (Cbt / p)) := hpairFull
            _ = ((roughMainDegree F : ℝ) * (roughMainDegree G : ℝ)) *
                  (Cbt ^ 2 / (p : ℝ) ^ 2) := by ring
        calc
          _ ≤ _ := hpair'
          _ ≤ Dbase / (p : ℝ) ^ 2 := by
            dsimp [Dbase]
            calc
              _ = ((roughMainDegree F : ℝ) * (roughMainDegree G : ℝ)) *
                    (Cbt ^ 2 / (p : ℝ) ^ 2) := by ring
              _ ≤ ((F.totalDegree : ℝ) * (G.totalDegree : ℝ)) *
                    (Cbt ^ 2 / (p : ℝ) ^ 2) :=
                    mul_le_mul_of_nonneg_right hdegprod (by positivity)
              _ = (F.totalDegree : ℝ) * (G.totalDegree : ℝ) * Cbt ^ 2 /
                    (p : ℝ) ^ 2 := by ring
      · simpa [Ep, hp, hp2, independentPrimePairProbability] using hR
    · simpa [Ep, hp, independentPrimePairProbability] using hR
  have hsumTerm := Finset.sum_le_sum (s := S) hterm
  have htail := inverse_square_Ico_tail_bound hWone hWY0
  have hrecip := natSqrt_recip_le (by omega : 2 ≤ L)
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogCompare : Real.log (2 : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ L))
  have hpart : 1 / Real.sqrt (L : ℝ) ≤
      (1 / Real.log 2) * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
    field_simp [hlog2pos.ne', (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < L)).ne']
    nlinarith
  have htail' :
      (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤
        (2 / Real.log 2) * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
    calc
      _ ≤ 1 / (w : ℝ) := htail
      _ ≤ 2 / Real.sqrt (L : ℝ) := hrecip
      _ ≤ (2 / Real.log 2) * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
            calc
              _ = 2 * (1 / Real.sqrt (L : ℝ)) := by ring
              _ ≤ 2 * ((1 / Real.log 2) *
                    (Real.log (L : ℝ) / Real.sqrt (L : ℝ))) :=
                    mul_le_mul_of_nonneg_left hpart (by norm_num)
              _ = _ := by ring
  have hsumSq :
      (∑ p ∈ S, independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (Ep p)) ≤
        Dbase * ((2 / Real.log 2) *
          (Real.log (L : ℝ) / Real.sqrt (L : ℝ))) := by
    calc
      _ ≤ ∑ p ∈ S, Dbase / (p : ℝ) ^ 2 := hsumTerm
      _ = Dbase * ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ ≤ Dbase * ((2 / Real.log 2) *
          (Real.log (L : ℝ) / Real.sqrt (L : ℝ))) :=
            mul_le_mul_of_nonneg_left htail' hDbase
  calc
    _ ≤ independentPrimePairProbability YF (fun i => 2 * YF i)
          YG (fun j => 2 * YG j) (fun x y => ∃ p ∈ S, Ep p x y) := hmono
    _ ≤ ∑ p ∈ S, independentPrimePairProbability YF (fun i => 2 * YF i)
          YG (fun j => 2 * YG j) (Ep p) := hunion
    _ ≤ Dbase * ((2 / Real.log 2) *
          (Real.log (L : ℝ) / Real.sqrt (L : ℝ))) := hsumSq
    _ = _ := by ring

private def roughLargeExposureEvent {kF nG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial (nG + 1)) (Y0 : ℕ)
    (x : Fin kF → ℕ) (y : Fin (nG + 1) → ℕ) : Prop :=
  ∃ p ∈ roughLargePrimeFactors
      (evalIntegerPolynomial F (fun i => (x i : ℤ))).natAbs Y0,
    (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
      ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
        (fun j => (y j : ℤ))

private lemma roughLargeExposureProbability_le {kF nG Y0 YG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial (nG + 1)) (hG : G ≠ 0)
    (YF : Fin kF → ℕ) (hMassF : ∀ i, 0 < primePoolMass (YF i) (2 * YF i))
    (loGTail hiGTail : Fin nG → ℕ)
    (hMassGTail : ∀ j, 0 < primePoolMass (loGTail j) (hiGTail j))
    (hActiveMax : ∀ i ∈ F.vars, YF i ≤ Y0)
    (hY0 : 9 ≤ Y0) (hY0G : Y0 ≤ YG)
    (hEvalCut : roughCoefficientMass F * 2 ^ F.totalDegree ≤ Y0)
    (hCoeffCut : (roughCoefficientMass (roughMainCoefficientTail G) + 1) ^ 2 ≤ Y0)
    (Cbt Aatom : ℝ) (hCbt : 0 < Cbt) (hAatom : 0 < Aatom)
    (hBT : ∀ p, p.Prime → p ^ 2 ≤ YG → ∀ a : Fin p, 0 < a.val →
      (∑ q ∈ (Finset.Ico YG (2 * YG)).filter Nat.Prime,
        if q % p = a.val then primePoolLaw YG (2 * YG) q else 0) ≤ Cbt / p)
    (hAtom : ∀ Y p, 2 ≤ Y →
      primePoolLaw Y (2 * Y) p ≤ Aatom * Real.log (Y : ℝ) / Y) :
    independentPrimePairProbability YF (fun i => 2 * YF i)
      (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail)
      (roughLargeExposureEvent F G Y0) ≤
      (2 * (F.totalDegree + 1) : ℝ) *
        ((G.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) *
          (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) := by
  classical
  let Bsingle : ℝ := (G.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) *
    (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))
  let Btotal : ℝ := (2 * (F.totalDegree + 1) : ℝ) * Bsingle
  let Ehigh : (Fin kF → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
    roughLargeExposureEvent F G Y0
  letI : DecidableRel Ehigh := fun x y => Classical.propDecidable (Ehigh x y)
  have hBsingle : 0 ≤ Bsingle := by
    dsimp [Bsingle]
    have hlog : 0 ≤ Real.log (Y0 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y0))
    positivity
  have hBtotal : 0 ≤ Btotal := by dsimp [Btotal]; positivity
  have hfiber : ∀ x, x ∈ primeTupleSupport YF (fun i => 2 * YF i) →
      independentPrimePoolProbability (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail)
        (Ehigh x) ≤ Btotal := by
    intro x hx
    let nval := (evalIntegerPolynomial F (fun i => (x i : ℤ))).natAbs
    let S := roughLargePrimeFactors nval Y0
    have hactiveX : ∀ i ∈ F.vars, x i ≤ 2 * Y0 := by
      intro i hi
      have hslot := primeTupleSupport_coordinate YF (fun i => 2 * YF i) x hx i
      have hlt := (Finset.mem_Ico.mp hslot).2
      exact hlt.le.trans (Nat.mul_le_mul_left 2 (hActiveMax i hi))
    have hvalue := evalIntegerPolynomial_natAbs_le_of_vars F x (2 * Y0) (by omega) hactiveX
    have hvalBound : nval ≤ Y0 ^ (F.totalDegree + 1) := by
      dsimp [nval]
      calc
        _ ≤ roughCoefficientMass F * (2 * Y0) ^ F.totalDegree := hvalue
        _ = (roughCoefficientMass F * 2 ^ F.totalDegree) * Y0 ^ F.totalDegree := by
              rw [Nat.mul_pow]
              ring
        _ ≤ Y0 * Y0 ^ F.totalDegree :=
              Nat.mul_le_mul_right _ hEvalCut
        _ = Y0 ^ (F.totalDegree + 1) := by rw [pow_succ]; ring
    have hcard : S.card ≤ 2 * (F.totalDegree + 1) := by
      dsimp [S, nval]
      by_cases hz : (evalIntegerPolynomial F (fun i => (x i : ℤ))).natAbs = 0
      · simp [hz, roughLargePrimeFactors]
      · have hnval : 0 < (evalIntegerPolynomial F (fun i => (x i : ℤ))).natAbs :=
          Nat.pos_of_ne_zero hz
        exact roughLargePrimeFactors_card_le _ Y0 F.totalDegree (by omega) hnval hvalBound
    have hterm : ∀ p ∈ S,
        independentPrimePoolProbability (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail)
          (fun y => (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
            ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
              (fun j => (y j : ℤ))) ≤ Bsingle := by
      intro p hpS
      rcases Finset.mem_filter.mp hpS with ⟨hpFactor, hpSq⟩
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpFactor
      have hKp : roughCoefficientMass (roughMainCoefficientTail G) < p :=
        nat_lt_of_squares_cut hCoeffCut hpSq
      letI : NeZero p := ⟨hp.ne_zero⟩
      have hmap : MvPolynomial.map (Int.castRingHom (ZMod p))
          (roughMainCoefficientTail G) ≠ 0 :=
        intPolynomial_map_ne_zero_of_coeffMass_lt (roughMainCoefficientTail G)
          (roughMainCoefficientTail_ne_zero G hG) p hp hKp
      have hBTp : p ^ 2 ≤ YG → ∀ a : Fin p, 0 < a.val →
          (∑ q ∈ (Finset.Ico YG (2 * YG)).filter Nat.Prime,
            if q % p = a.val then primePoolLaw YG (2 * YG) q else 0) ≤ Cbt / p :=
        fun hpy => hBT p hp hpy
      have hroot := roughMainDivProbability_upper_endpoint hp (by omega) hY0
        hY0G hpSq loGTail hiGTail hMassGTail G hmap Cbt Aatom hCbt hAatom hBTp hAtom
      have hdegG : (roughMainDegree G : ℝ) ≤ (G.totalDegree : ℝ) := by
        exact_mod_cast MvPolynomial.degreeOf_le_totalDegree G 0
      have hfactorNonneg : 0 ≤
          (Cbt / Real.log 2 + 3 * Aatom) *
            (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by
        positivity
      calc
        _ ≤ (roughMainDegree G : ℝ) *
              ((Cbt / Real.log 2 + 3 * Aatom) *
                (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) := by
              simpa [mul_assoc] using hroot
        _ ≤ (G.totalDegree : ℝ) *
              ((Cbt / Real.log 2 + 3 * Aatom) *
                (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) := by
              exact mul_le_mul_of_nonneg_right hdegG hfactorNonneg
        _ = Bsingle := by dsimp [Bsingle]; ring
    have hunion := independentPrimePoolProbability_exists_finset_le
      (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail) S
      (fun p y => (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
          (fun j => (y j : ℤ))) Bsingle hterm
    have hS : Ehigh x = (fun y => ∃ p ∈ S,
        (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) ∧
        ¬ (p : ℤ) ∣ evalIntegerPolynomial (roughMainCoefficient G)
          (fun j => (y j : ℤ))) := by
      funext y
      rfl
    rw [hS]
    calc
      _ ≤ S.card * Bsingle := hunion
      _ ≤ Btotal := by
        have hcardR : (S.card : ℝ) ≤ ((2 * (F.totalDegree + 1) : ℕ) : ℝ) := by
          exact_mod_cast hcard
        have hcardR' : (S.card : ℝ) ≤ 2 * ((F.totalDegree : ℝ) + 1) := by
          simpa [Nat.cast_mul, Nat.cast_add] using hcardR
        dsimp [Btotal]
        exact mul_le_mul_of_nonneg_right hcardR' hBsingle
  have hpair := independentPrimePairProbability_fiberwise_le
    YF (fun i => 2 * YF i) (Fin.cons YG loGTail) (Fin.cons (2 * YG) hiGTail)
    hMassF Ehigh Btotal hBtotal hfiber
  simpa [Btotal, Bsingle] using hpair

private lemma primeDivProbability_le_of_mod {m : ℕ}
    (lo hi : Fin m → ℕ) (P : IntegerPolynomial m)
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (hP : MvPolynomial.map (Int.castRingHom (ZMod p)) P ≠ 0)
    (A : ℝ) (hA : 0 ≤ A)
    (hmax : ∀ i a, primePoolResidueMass lo hi p i a ≤ A / (p : ℝ)) :
    independentPrimePoolProbability lo hi
      (fun x => (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ))) ≤
      (P.totalDegree : ℝ) * A ^ m / p := by
  classical
  let Pp := MvPolynomial.map (Int.castRingHom (ZMod p)) P
  have hEq (x : Fin m → ℕ) :
      (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ)) ↔
        MvPolynomial.eval (fun i => (x i : ZMod p)) Pp = 0 := by
    rw [evalIntegerPolynomial_mod_eq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
  have hprobEq :
      independentPrimePoolProbability lo hi
        (fun x => (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ))) =
      independentPrimePoolProbability lo hi
        (fun x => MvPolynomial.eval (fun i => (x i : ZMod p)) Pp = 0) := by
    unfold independentPrimePoolProbability
    apply tsum_congr
    intro x
    by_cases hdiv : (p : ℤ) ∣ evalIntegerPolynomial P (fun i => (x i : ℤ))
    · have hmod := (hEq x).1 hdiv
      simp [hdiv, hmod]
    · have hmod : MvPolynomial.eval (fun i => (x i : ZMod p)) Pp ≠ 0 := by
        intro hz
        exact hdiv ((hEq x).2 hz)
      simp [hdiv, hmod]
  calc
    _ = independentPrimePoolProbability lo hi
          (fun x => MvPolynomial.eval (fun i => (x i : ZMod p)) Pp = 0) := hprobEq
    _ ≤ (Pp.totalDegree : ℝ) * A ^ m / p :=
      independentPrimePoolProbability_mod_zero_le lo hi p hp Pp hP A hA hmax
    _ ≤ (P.totalDegree : ℝ) * A ^ m / p := by
      have hdeg := totalDegree_map_le (Int.castRingHom (ZMod p)) P
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg) (pow_nonneg hA _)) (by positivity)

private lemma independentPrimePoolProbability_nonneg {m : ℕ}
    (lo hi : Fin m → ℕ) (E : (Fin m → ℕ) → Prop) [DecidablePred E] :
    0 ≤ independentPrimePoolProbability lo hi E := by
  classical
  unfold independentPrimePoolProbability
  apply tsum_nonneg
  intro x
  exact mul_nonneg (independentPrimePoolMass_nonneg lo hi x) (by split_ifs <;> positivity)

private lemma roughPart_zero (w : ℕ) : roughPart w 0 = 1 := by
  simp [roughPart]

private lemma prime_dvd_roughPart {w p : ℕ} {a : ℤ} (hp : p.Prime)
    (hd : p ∣ roughPart w a) : w < p ∧ (p : ℤ) ∣ a := by
  have ha : a ≠ 0 := by
    intro h
    subst a
    simp [roughPart] at hd
    have hp2 := hp.two_le
    omega
  have haAbs : a.natAbs ≠ 0 := by
    intro h
    have : a = 0 := Int.natAbs_eq_zero.mp h
    exact ha this
  have hprod := (Prime.dvd_finsetProd_iff hp.prime _).mp (by
    simpa only [roughPart] using hd)
  obtain ⟨q, hqmem, hpqpow⟩ := hprod
  rcases Finset.mem_filter.mp hqmem with ⟨hqrange, hqprime, hwq⟩
  have hpq : p ∣ q := hp.dvd_of_dvd_pow hpqpow
  have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  have hqexp : 0 < a.natAbs.factorization q := by
    by_contra hn
    have hzero : a.natAbs.factorization q = 0 := Nat.eq_zero_of_not_pos hn
    apply hp.not_dvd_one
    simpa [hzero, hpqeq] using hpqpow
  have hqdiv : q ∣ a.natAbs :=
    (Nat.Prime.dvd_iff_one_le_factorization hqprime haAbs).2 (by omega)
  refine ⟨?_, ?_⟩
  · simpa [hpqeq] using hwq
  · apply Int.dvd_natAbs.mp
    exact Int.natCast_dvd_natCast.mpr (hpqeq ▸ hqdiv)

private lemma roughGcd_ne_one_implies_common {w : ℕ} {a b : ℤ}
    (h : Nat.gcd (roughPart w a) (roughPart w b) ≠ 1) :
    a ≠ 0 ∧ b ≠ 0 ∧ Nat.gcd (roughPart w a) (roughPart w b) > 1 := by
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, roughPart_zero, Nat.gcd_one_left] at h
    exact h rfl
  have hb : b ≠ 0 := by
    intro hb
    rw [hb, roughPart_zero, Nat.gcd_one_right] at h
    exact h rfl
  have hpa : 0 < roughPart w a := by
    unfold roughPart
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2.1) _
  refine ⟨ha, hb, ?_⟩
  have hpos : 0 < Nat.gcd (roughPart w a) (roughPart w b) :=
    Nat.gcd_pos_of_pos_left _ hpa
  omega

/-- Small common rough prime divisors, `w<p≤√L`, are controlled by two independent
root-class tests and contribute `O(1/w)` (§3 lines 391–411). Here `w ≥ 1`: the paper's
`1/w` is meaningless at `w=0`, where Lean's `C/0=0` makes the bound false for constant
polynomials with a common prime factor. Every variable has lower endpoint at least
`L ≥ p²`, so the Brun–Titchmarsh consequence applies to each slot modulo `p`; primes dividing
a content of `F` or `G`, and small `L`, are absorbed by the constant. -/
theorem rough_coprimality_small_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (w L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → 1 ≤ w → w < L →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤ C / w := by
  classical
  obtain ⟨sF, hsF⟩ := F.support_nonempty.mpr hF
  obtain ⟨sG, hsG⟩ := G.support_nonempty.mpr hG
  obtain ⟨Cbt, hCbt, hBTevent⟩ :=
    HindmanSumsProducts.Arithmetic.Outside.harmonic_prime_brun_titchmarsh
  obtain ⟨Ybt, hYbt⟩ := Filter.eventually_atTop.1 hBTevent
  have hBTall : ∀ Y, Ybt ≤ Y → ∀ p, p.Prime → p ^ 2 ≤ Y →
      ∀ a : Fin p, 0 < a.val →
        (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
          if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ Cbt / p := by
    intro Y hY p hp hp2 a ha
    exact hYbt Y hY p hp hp2 a ha
  let wCut : ℕ := max (F.coeff sF).natAbs (G.coeff sG).natAbs + 1
  have hcF : (F.coeff sF).natAbs < wCut := by dsimp [wCut]; omega
  have hcG : (G.coeff sG).natAbs < wCut := by dsimp [wCut]; omega
  let DF : ℝ := (MvPolynomial.totalDegree F : ℝ) * Cbt ^ kF
  let DG : ℝ := (MvPolynomial.totalDegree G : ℝ) * Cbt ^ kG
  let Ctotal : ℝ := (wCut : ℝ) + (Ybt : ℝ) + DF * DG + 1
  have hDFDG : 0 ≤ DF * DG := mul_nonneg (by dsimp [DF]; positivity)
    (by dsimp [DG]; positivity)
  refine ⟨Ctotal, ?_, ?_⟩
  · dsimp [Ctotal]
    positivity
  · intro YF YG w L hYF hYG hw hwl
    have hLtwo : 2 ≤ L := by omega
    have hmassF : ∀ i, 0 < primePoolMass (YF i) (2 * YF i) := by
      intro i
      exact dyadicPrimePoolMass_pos (YF i) (hLtwo.trans (hYF i))
    have hmassG : ∀ j, 0 < primePoolMass (YG j) (2 * YG j) := by
      intro j
      exact dyadicPrimePoolMass_pos (YG j) (hLtwo.trans (hYG j))
    let divF : ℕ → (Fin kF → ℕ) → Prop := fun p x =>
      (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ))
    let divG : ℕ → (Fin kG → ℕ) → Prop := fun p y =>
      (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))
    let Ep : ℕ → (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun p x y =>
      p.Prime ∧ p ^ 2 ≤ L ∧ divF p x ∧ divG p y
    by_cases hsmall : w < wCut ∨ L < Ybt
    · have hCw : (1 : ℝ) ≤ Ctotal / (w : ℝ) := by
        apply (le_div_iff₀ (by exact_mod_cast (by omega : 0 < w))).2
        dsimp [Ctotal]
        rcases hsmall with hwc | hLsmall
        · have hwR : (w : ℝ) ≤ (wCut : ℝ) := by exact_mod_cast (Nat.le_of_lt hwc)
          linarith [hDFDG]
        · have hwR : (w : ℝ) ≤ (Ybt : ℝ) := by
            exact_mod_cast (Nat.le_of_lt (lt_trans hwl hLsmall))
          linarith [hDFDG]
      have hPairLeOne := independentPrimePairProbability_le_one
        YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) hmassF hmassG
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
          ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)))
      exact hPairLeOne.trans hCw
    · have hwCut : wCut ≤ w := by omega
      have hYbtL : Ybt ≤ L := by omega
      have hFcoeffBound : ∀ p, w < p → (F.coeff sF).natAbs < p := by
        intro p hpw
        exact hcF.trans (lt_of_le_of_lt hwCut hpw)
      have hGcoeffBound : ∀ p, w < p → (G.coeff sG).natAbs < p := by
        intro p hpw
        exact hcG.trans (lt_of_le_of_lt hwCut hpw)
      letI : DecidableRel (fun x y =>
        evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
        evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
        ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧ divF p x ∧ divG p y) :=
          fun x y => Classical.propDecidable _
      have hsubset : ∀ x y,
          (evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
            evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
            ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧ divF p x ∧ divG p y) →
          ∃ p ∈ Finset.Ico (w + 1) (L + 1), Ep p x y := by
        intro x y h
        rcases h.2.2 with ⟨p, hp, hwp, hp2L, hdivF, hdivG⟩
        have hpLe : p ≤ p ^ 2 := by
          calc
            p = p * 1 := by simp
            _ ≤ p * p := Nat.mul_le_mul_left p (by omega : 1 ≤ p)
            _ = p ^ 2 := by rw [pow_two]
        have hpL : p ≤ L := hpLe.trans hp2L
        have hpLower : w + 1 ≤ p := by omega
        have hpUpper : p < L + 1 := by omega
        exact ⟨p, Finset.mem_Ico.mpr ⟨hpLower, hpUpper⟩,
          ⟨hp, hp2L, hdivF, hdivG⟩⟩
      have htargetLe :
          independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun i => 2 * YG i)
            (fun x y =>
              evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
              evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
              ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧ divF p x ∧ divG p y) ≤
          independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun i => 2 * YG i)
            (fun x y => ∃ p ∈ Finset.Ico (w + 1) (L + 1), Ep p x y) :=
        independentPrimePairProbability_mono YF (fun i => 2 * YF i)
          YG (fun i => 2 * YG i)
          (fun x y =>
            evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
            evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
            ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧ divF p x ∧ divG p y)
          (fun x y => ∃ p ∈ Finset.Ico (w + 1) (L + 1), Ep p x y) hsubset
      have hunion := independentPrimePairProbability_finset_union_le
        YF (fun i => 2 * YF i) YG (fun i => 2 * YG i)
        (Finset.Ico (w + 1) (L + 1)) Ep
      have hterm : ∀ p ∈ Finset.Ico (w + 1) (L + 1),
          independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun i => 2 * YG i) (Ep p) ≤ DF * DG / (p : ℝ) ^ 2 := by
        intro p hpS
        by_cases hp : p.Prime
        · by_cases hp2L : p ^ 2 ≤ L
          · have hpw : w < p := by
              have := (Finset.mem_Ico.mp hpS).1
              omega
            letI : NeZero p := ⟨hp.ne_zero⟩
            have hBTi (Yi : ℕ) (hYi : Ybt ≤ Yi) (hpYi : p ^ 2 ≤ Yi) :
                ∀ a : Fin p, 0 < a.val →
                  (∑ q ∈ (Finset.Ico Yi (2 * Yi)).filter Nat.Prime,
                    if q % p = a.val then primePoolLaw Yi (2 * Yi) q else 0) ≤ Cbt / p := by
              intro a ha
              exact hBTall Yi hYi p hp hpYi a ha
            have hmaxF : ∀ i a,
                primePoolResidueMass YF (fun i => 2 * YF i) p i a ≤ Cbt / p := by
              intro i a
              have hYi : Ybt ≤ YF i := hYbtL.trans (hYF i)
              have hpYi : p ^ 2 ≤ YF i := hp2L.trans (hYF i)
              simpa [primePoolResidueMass, dyadicPrimeResidueMass] using
                (dyadicPrimeResidueMass_le_brun_titchmarsh (Y := YF i) (p := p)
                  hp hpYi Cbt hCbt.le
                  (hBTi (YF i) hYi hpYi) a)
            have hmaxG : ∀ j a,
                primePoolResidueMass YG (fun j => 2 * YG j) p j a ≤ Cbt / p := by
              intro j a
              have hYj : Ybt ≤ YG j := hYbtL.trans (hYG j)
              have hpYj : p ^ 2 ≤ YG j := hp2L.trans (hYG j)
              simpa [primePoolResidueMass, dyadicPrimeResidueMass] using
                (dyadicPrimeResidueMass_le_brun_titchmarsh (Y := YG j) (p := p)
                  hp hpYj Cbt hCbt.le
                  (hBTi (YG j) hYj hpYj) a)
            have hmapF :
                MvPolynomial.map (Int.castRingHom (ZMod p)) F ≠ 0 :=
              intPolynomial_map_ne_zero_of_large_coeff F hsF p hp
                (hFcoeffBound p hpw)
            have hmapG :
                MvPolynomial.map (Int.castRingHom (ZMod p)) G ≠ 0 :=
              intPolynomial_map_ne_zero_of_large_coeff G hsG p hp
                (hGcoeffBound p hpw)
            have hPF := primeDivProbability_le_of_mod YF (fun i => 2 * YF i)
              F p hp hmapF Cbt hCbt.le hmaxF
            have hPG := primeDivProbability_le_of_mod YG (fun j => 2 * YG j)
              G p hp hmapG Cbt hCbt.le hmaxG
            have hprodEq :
                independentPrimePairProbability YF (fun i => 2 * YF i)
                  YG (fun j => 2 * YG j) (fun x y => divF p x ∧ divG p y) =
                independentPrimePoolProbability YF (fun i => 2 * YF i) (divF p) *
                  independentPrimePoolProbability YG (fun j => 2 * YG j) (divG p) :=
              independentPrimePairProbability_product ..
            have hmono := independentPrimePairProbability_mono
              YF (fun i => 2 * YF i) YG (fun j => 2 * YG j)
              (Ep p) (fun x y => divF p x ∧ divG p y)
              (by intro x y h; exact h.2.2)
            have hPF0 := independentPrimePoolProbability_nonneg
              YF (fun i => 2 * YF i) (divF p)
            have hPG0 := independentPrimePoolProbability_nonneg
              YG (fun j => 2 * YG j) (divG p)
            have hDR : 0 ≤ DF / (p : ℝ) := by dsimp [DF]; positivity
            calc
              independentPrimePairProbability YF (fun i => 2 * YF i)
                  YG (fun j => 2 * YG j) (Ep p) ≤
                independentPrimePairProbability YF (fun i => 2 * YF i)
                  YG (fun j => 2 * YG j) (fun x y => divF p x ∧ divG p y) := hmono
              _ = independentPrimePoolProbability YF (fun i => 2 * YF i) (divF p) *
                    independentPrimePoolProbability YG (fun j => 2 * YG j) (divG p) := hprodEq
              _ ≤ (DF / (p : ℝ)) * (DG / (p : ℝ)) := mul_le_mul hPF hPG hPG0 hDR
              _ = DF * DG / (p : ℝ) ^ 2 := by ring
          · have hR : 0 ≤ DF * DG / (p : ℝ) ^ 2 := div_nonneg hDFDG (by positivity)
            simpa [Ep, hp, hp2L, independentPrimePairProbability] using hR
        · have hR : 0 ≤ DF * DG / (p : ℝ) ^ 2 := div_nonneg hDFDG (by positivity)
          simpa [Ep, hp, independentPrimePairProbability] using hR
      have hsum :
          independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun i => 2 * YG i)
            (fun x y => ∃ p ∈ Finset.Ico (w + 1) (L + 1), Ep p x y) ≤
          ∑ p ∈ Finset.Ico (w + 1) (L + 1),
            independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun i => 2 * YG i) (Ep p) := hunion
      have hsumTerm := Finset.sum_le_sum (s := Finset.Ico (w + 1) (L + 1)) hterm
      have hsumSq :
          (∑ p ∈ Finset.Ico (w + 1) (L + 1),
            independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun i => 2 * YG i) (Ep p)) ≤ DF * DG / (w : ℝ) := by
        calc
          _ ≤ ∑ p ∈ Finset.Ico (w + 1) (L + 1), DF * DG / (p : ℝ) ^ 2 := hsumTerm
          _ = DF * DG * ∑ p ∈ Finset.Ico (w + 1) (L + 1), 1 / (p : ℝ) ^ 2 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p hp
                ring
          _ ≤ DF * DG * (1 / (w : ℝ)) :=
                mul_le_mul_of_nonneg_left
                  (inverse_square_Ico_tail_bound (by omega) (by omega)) hDFDG
          _ = DF * DG / (w : ℝ) := by ring
      have hDleC : DF * DG ≤ Ctotal := by
        dsimp [Ctotal]
        linarith
      have hwRPos : 0 < (w : ℝ) := by
        exact_mod_cast (by omega : 0 < w)
      have hbound : DF * DG / (w : ℝ) ≤ Ctotal / (w : ℝ) := by
        exact div_le_div_of_nonneg_right hDleC (by positivity)
      exact htargetLe.trans (hsum.trans (hsumSq.trans hbound))

private def roughLargePrimeDivisorEvent {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG) (L : ℕ)
    (x : Fin kF → ℕ) (y : Fin kG → ℕ) : Prop :=
  evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
  evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
  ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
    (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
    (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ))

private def roughLargePrimeDivisorBoundConstant {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG) (C : ℝ) : Prop :=
  ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (L : ℕ),
    (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → 2 ≤ L →
    independentPrimePairProbability YF (fun i => 2 * YF i)
      YG (fun j => 2 * YG j) (roughLargePrimeDivisorEvent F G L) ≤
        C * Real.log L / Real.sqrt L

private def roughZeroPrimeDivisorBoundConstant {k : ℕ}
    (F : IntegerPolynomial k) (C : ℝ) : Prop :=
  ∀ (Y : Fin k → ℕ) (L : ℕ), 2 ≤ L → (∀ i, L ≤ Y i) →
    independentPrimePoolProbability Y (fun i => 2 * Y i)
      (fun p => evalIntegerPolynomial F (fun i => (p i : ℤ)) = 0) ≤
      C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ))

private def roughLargePrimeDivisorBound {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG) : Prop :=
  ∃ C : ℝ, 0 < C ∧ roughLargePrimeDivisorBoundConstant F G C

private lemma roughLargePrimeDivisorBound_of_witnessBound {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) (M : ℕ)
    (hbound : ∀ (x : Fin kF → ℕ) (y : Fin kG → ℕ) (p : ℕ),
      evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 →
      evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 → p.Prime →
      (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) →
      (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ)) → p ≤ M) :
    roughLargePrimeDivisorBound F G := by
  classical
  let N : ℕ := M + 1
  let C : ℝ := (N : ℝ) ^ 2 / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro YF YG L hYF hYG hL
  have hMassF : ∀ i, 0 < primePoolMass (YF i) (2 * YF i) := by
    intro i
    exact dyadicPrimePoolMass_pos (YF i) (hL.trans (hYF i))
  have hMassG : ∀ j, 0 < primePoolMass (YG j) (2 * YG j) := by
    intro j
    exact dyadicPrimePoolMass_pos (YG j) (hL.trans (hYG j))
  have hprob := independentPrimePairProbability_le_one YF (fun i => 2 * YF i)
    YG (fun j => 2 * YG j) hMassF hMassG (roughLargePrimeDivisorEvent F G L)
  by_cases hsmall : L < N ^ 2
  · have hcover : 1 ≤ C * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
      have hT := log_sqrt_lower hL (Nat.le_of_lt hsmall)
      have hmul := mul_le_mul_of_nonneg_left hT (by positivity :
        0 ≤ (N : ℝ) ^ 2 / Real.log 2)
      have hNpos : 0 < (N : ℝ) := by positivity
      have heq : ((N : ℝ) ^ 2 / Real.log 2) *
          (Real.log 2 / (N : ℝ) ^ 2) = 1 := by
        field_simp [hlog2.ne', hNpos.ne']
      calc
        _ = C * (Real.log 2 / (N : ℝ) ^ 2) := by simpa only [C] using heq.symm
        _ ≤ C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
              simpa [C, Nat.cast_pow] using hmul
        _ = C * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by ring
    exact hprob.trans hcover
  · have hNle : N ^ 2 ≤ L := Nat.le_of_not_gt hsmall
    have hfalse : ∀ x y, ¬ roughLargePrimeDivisorEvent F G L x y := by
      intro x y he
      rcases he.2.2 with ⟨p, hp, hsqrt, hdivF, hdivG⟩
      have hpM := hbound x y p he.1 he.2.1 hp hdivF hdivG
      have hpsq : p ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hpM 2
      have hMsq : M ^ 2 < N ^ 2 := by dsimp [N]; nlinarith
      have hPL : (L : ℝ) < (p : ℝ) ^ 2 :=
        (Real.sqrt_lt' (by exact_mod_cast hp.pos)).1 hsqrt
      have hPN : p ^ 2 < L := lt_of_le_of_lt hpsq (hMsq.trans_le hNle)
      have hPNR : (p : ℝ) ^ 2 < (L : ℝ) := by exact_mod_cast hPN
      exact (lt_asymm hPNR hPL)
    have hzero : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (roughLargePrimeDivisorEvent F G L) = 0 := by
      unfold independentPrimePairProbability
      simp [hfalse]
    rw [hzero]
    have hTnonneg : 0 ≤ Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
      apply div_nonneg
      · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
      · exact Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log (L : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
    exact div_nonneg (mul_nonneg (le_of_lt hC) hlog) (Real.sqrt_nonneg _)

private lemma roughLargePrimeDivisorBound_of_constant_left {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) (hdeg : F.totalDegree = 0) :
    roughLargePrimeDivisorBound F G := by
  have hconst : F = MvPolynomial.C (F.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg
  have hc : F.coeff 0 ≠ 0 := by
    intro hz
    apply hF
    rw [hconst, hz]
    simp
  have heval (x : Fin kF → ℕ) :
    evalIntegerPolynomial F (fun i => (x i : ℤ)) = F.coeff 0 := by
    calc
      evalIntegerPolynomial F (fun i => (x i : ℤ)) =
          evalIntegerPolynomial (MvPolynomial.C (F.coeff 0)) (fun i => (x i : ℤ)) :=
            congrArg (fun Q => evalIntegerPolynomial Q (fun i => (x i : ℤ))) hconst
      _ = F.coeff 0 := by simp [evalIntegerPolynomial]
  apply roughLargePrimeDivisorBound_of_witnessBound F G hF hG
    (F.coeff 0).natAbs
  intro x y p hFx hGy hp hdivF hdivG
  have hdiv : (p : ℤ) ∣ F.coeff 0 := by simpa [heval x] using hdivF
  have hdvdNat : p ∣ (F.coeff 0).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hdvdNat

private lemma roughLargePrimeDivisorBound_of_constant_right {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) (hdeg : G.totalDegree = 0) :
    roughLargePrimeDivisorBound F G := by
  have hconst : G = MvPolynomial.C (G.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg
  have hc : G.coeff 0 ≠ 0 := by
    intro hz
    apply hG
    rw [hconst, hz]
    simp
  have heval (y : Fin kG → ℕ) :
    evalIntegerPolynomial G (fun j => (y j : ℤ)) = G.coeff 0 := by
    calc
      evalIntegerPolynomial G (fun j => (y j : ℤ)) =
          evalIntegerPolynomial (MvPolynomial.C (G.coeff 0)) (fun j => (y j : ℤ)) :=
            congrArg (fun Q => evalIntegerPolynomial Q (fun j => (y j : ℤ))) hconst
      _ = G.coeff 0 := by simp [evalIntegerPolynomial]
  apply roughLargePrimeDivisorBound_of_witnessBound F G hF hG
    (G.coeff 0).natAbs
  intro x y p hFx hGy hp hdivF hdivG
  have hdiv : (p : ℤ) ∣ G.coeff 0 := by simpa [heval y] using hdivG
  have hdvdNat : p ∣ (G.coeff 0).natAbs :=
    Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hdvdNat

private lemma roughLargePrimeDivisorEvent_reindex {kF kG : ℕ}
    (eF : Equiv.Perm (Fin kF)) (eG : Equiv.Perm (Fin kG))
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG) (L : ℕ)
    (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) :
    independentPrimePairProbability (fun i => YF (eF i))
      (fun i => 2 * YF (eF i)) (fun j => YG (eG j)) (fun j => 2 * YG (eG j))
      (fun x y => roughLargePrimeDivisorEvent (MvPolynomial.rename eF.symm F)
        (MvPolynomial.rename eG.symm G) L x y) =
    independentPrimePairProbability YF (fun i => 2 * YF i) YG (fun j => 2 * YG j)
      (roughLargePrimeDivisorEvent F G L) := by
  classical
  have hevent :
      (fun x y => roughLargePrimeDivisorEvent (MvPolynomial.rename eF.symm F)
        (MvPolynomial.rename eG.symm G) L x y) =
      (fun x y => roughLargePrimeDivisorEvent F G L
        (roughTupleReindex eF x) (roughTupleReindex eG y)) := by
    funext x y
    simp [roughLargePrimeDivisorEvent, evalIntegerPolynomial_roughTupleReindex]
  rw [hevent]
  exact independentPrimePairProbability_reindex_both eF eG
    YF (fun i => 2 * YF i) YG (fun j => 2 * YG j)
    (roughLargePrimeDivisorEvent F G L)

set_option maxHeartbeats 1000000
/-- Large common rough prime divisors, `p>√L`, contribute `O(log L/√L)` by testing
the finitely many large prime factors of the polynomial with the smaller main endpoint
(§3 lines 413–432), with the leading-coefficient induction of §3 lines 391–403 and the
small-prime count for primes between `√L` and the main endpoints. Here `L ≥ 2`: at `L ≤ 1`
the bound `C·log L/√L` is `0`, false for constant polynomials with a common prime factor;
for bounded `L ≥ 2` the constant absorbs the probability. -/
theorem rough_coprimality_large_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → 2 ≤ L →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤
        C * Real.log L / Real.sqrt L := by
  classical
  have hInduction : ∀ d, ∀ kF kG (F : IntegerPolynomial kF)
      (G : IntegerPolynomial kG), F ≠ 0 → G ≠ 0 →
      F.totalDegree + G.totalDegree = d → roughLargePrimeDivisorBound F G := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro kF kG F G hF hG hdeq
      by_cases hFconst : F.totalDegree = 0
      · exact roughLargePrimeDivisorBound_of_constant_left F G hF hG hFconst
      · by_cases hGconst : G.totalDegree = 0
        · exact roughLargePrimeDivisorBound_of_constant_right F G hF hG hGconst
        · have hFdeg : 0 < F.totalDegree := Nat.pos_of_ne_zero hFconst
          have hGdeg : 0 < G.totalDegree := Nat.pos_of_ne_zero hGconst
          have hvarsF := mvPolynomial_vars_nonempty_of_totalDegree_pos F hFdeg
          have hvarsG := mvPolynomial_vars_nonempty_of_totalDegree_pos G hGdeg
          have hkF : 0 < kF := by
            rcases hvarsF with ⟨i, _⟩
            have hi := i.isLt
            omega
          have hkG : 0 < kG := by
            rcases hvarsG with ⟨j, _⟩
            have hj := j.isLt
            omega
          obtain ⟨nF, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : kF ≠ 0)
          obtain ⟨nG, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : kG ≠ 0)
          let zeroF : Fin (nF + 1) := ⟨0, by omega⟩
          let zeroG : Fin (nG + 1) := ⟨0, by omega⟩
          let moveF : Fin (nF + 1) → IntegerPolynomial (nF + 1) := fun i =>
            MvPolynomial.rename (roughMoveMainPerm zeroF i).symm F
          let moveG : Fin (nG + 1) → IntegerPolynomial (nG + 1) := fun j =>
            MvPolynomial.rename (roughMoveMainPerm zeroG j).symm G
          let leadF : Fin (nF + 1) → IntegerPolynomial (nF + 1) := fun i =>
            roughMainCoefficient (moveF i)
          let leadG : Fin (nG + 1) → IntegerPolynomial (nG + 1) := fun j =>
            roughMainCoefficient (moveG j)
          let complexityF : Fin (nF + 1) → ℕ := fun i =>
            roughCoefficientMass (moveF i) * 2 ^ (moveF i).totalDegree +
              (roughCoefficientMass (roughMainCoefficientTail (moveF i)) + 1) ^ 2
          let complexityG : Fin (nG + 1) → ℕ := fun j =>
            roughCoefficientMass (moveG j) * 2 ^ (moveG j).totalDegree +
              (roughCoefficientMass (roughMainCoefficientTail (moveG j)) + 1) ^ 2
          let sumComplexityF : ℕ := ∑ i : Fin (nF + 1), complexityF i
          let sumComplexityG : ℕ := ∑ j : Fin (nG + 1), complexityG j
          have hcomplexF : ∀ i, complexityF i ≤ sumComplexityF := by
            intro i
            dsimp [sumComplexityF]
            exact Finset.single_le_sum (f := complexityF)
              (fun i hi => Nat.zero_le _) (Finset.mem_univ i)
          have hcomplexG : ∀ j, complexityG j ≤ sumComplexityG := by
            intro j
            dsimp [sumComplexityG]
            exact Finset.single_le_sum (f := complexityG)
              (fun j hj => Nat.zero_le _) (Finset.mem_univ j)
          obtain ⟨Cbt, hCbt, hBTevent⟩ :=
            HindmanSumsProducts.Arithmetic.Outside.harmonic_prime_brun_titchmarsh
          obtain ⟨Ybt, hYbtEvent⟩ := Filter.eventually_atTop.1 hBTevent
          have hBTall : ∀ Y, Ybt ≤ Y → ∀ p, p.Prime → p ^ 2 ≤ Y →
              ∀ a : Fin p, 0 < a.val →
                (∑ q ∈ (Finset.Ico Y (2 * Y)).filter Nat.Prime,
                  if q % p = a.val then primePoolLaw Y (2 * Y) q else 0) ≤ Cbt / p := by
            intro Y hY p hp hpY a ha
            exact hYbtEvent Y hY p hp hpY a ha
          obtain ⟨Aatom, hAatom, hAtom⟩ := dyadicPrimePoolLaw_global_atom_bound
          have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
          let T : ℕ := 9 + Ybt + sumComplexityF + sumComplexityG
          have hT9 : 9 ≤ T := by dsimp [T]; omega
          have hTYbt : Ybt ≤ T := by dsimp [T]; omega
          have hTSF : sumComplexityF ≤ T := by dsimp [T]; omega
          have hTSG : sumComplexityG ≤ T := by dsimp [T]; omega
          let Csmall : ℝ := Real.sqrt (T : ℝ) / Real.log 2
          let Cmed : ℝ := (F.totalDegree : ℝ) * (G.totalDegree : ℝ) *
            Cbt ^ 2 * (2 / Real.log 2)
          let CexpF : ℝ := (2 * (F.totalDegree + 1) : ℝ) *
            (G.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom)
          let CexpG : ℝ := (2 * (G.totalDegree + 1) : ℝ) *
            (F.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom)
          let ActivePair :=
            { ij : Fin (nF + 1) × Fin (nG + 1) // ij.1 ∈ F.vars ∧ ij.2 ∈ G.vars }
          have hActivePairNonempty : Nonempty ActivePair := by
            rcases hvarsF with ⟨i, hi⟩
            rcases hvarsG with ⟨j, hj⟩
            exact ⟨⟨(i, j), ⟨hi, hj⟩⟩⟩
          have hdata : ∀ z : ActivePair,
              ∃ q : ℝ × (ℝ × (ℝ × ℝ)),
                0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2.1 ∧ 0 < q.2.2.2 ∧
                roughLargePrimeDivisorBoundConstant
                  (leadF z.1.1) (moveG z.1.2) q.1 ∧
                roughLargePrimeDivisorBoundConstant
                  (moveF z.1.1) (leadG z.1.2) q.2.1 ∧
                roughZeroPrimeDivisorBoundConstant (leadF z.1.1) q.2.2.1 ∧
                roughZeroPrimeDivisorBoundConstant (leadG z.1.2) q.2.2.2 := by
            intro z
            let i := z.1.1
            let j := z.1.2
            let eF := roughMoveMainPerm zeroF i
            let eG := roughMoveMainPerm zeroG j
            let Fm := moveF i
            let Gm := moveG j
            let A := leadF i
            let B := leadG j
            have hFm : Fm ≠ 0 := by
              intro hz
              apply hF
              have hz' := congrArg (MvPolynomial.rename eF) hz
              simpa [Fm, moveF, eF, MvPolynomial.rename_rename] using hz'
            have hGm : Gm ≠ 0 := by
              intro hz
              apply hG
              have hz' := congrArg (MvPolynomial.rename eG) hz
              simpa [Gm, moveG, eG, MvPolynomial.rename_rename] using hz'
            have hMovedF := roughMoveMain_active_endpoint F (fun _ => 0)
              zeroF i z.2.1 (by intro a ha; omega)
            have hMovedG := roughMoveMain_active_endpoint G (fun _ => 0)
              zeroG j z.2.2 (by intro a ha; omega)
            have hactiveF : zeroF ∈ Fm.vars := by
              simpa [Fm, moveF, eF] using hMovedF.1
            have hactiveG : zeroG ∈ Gm.vars := by
              simpa [Gm, moveG, eG] using hMovedG.1
            have hmainF : 0 < Fm.degreeOf zeroF := by
              have hnz := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).1 hactiveF
              omega
            have hmainG : 0 < Gm.degreeOf zeroG := by
              have hnz := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).1 hactiveG
              omega
            have hA : A ≠ 0 := by
              exact roughMainCoefficient_ne_zero Fm hFm
            have hB : B ≠ 0 := by
              exact roughMainCoefficient_ne_zero Gm hGm
            have hFmDegree : Fm.totalDegree = F.totalDegree := by
              simpa [Fm, moveF, eF] using
                totalDegree_rename_perm eF.symm F
            have hGmDegree : Gm.totalDegree = G.totalDegree := by
              simpa [Gm, moveG, eG] using
                totalDegree_rename_perm eG.symm G
            have hAdegree : A.totalDegree < F.totalDegree := by
              have h := roughMainCoefficient_totalDegree_lt Fm hFm hmainF
              simpa [A, Fm, hFmDegree] using h
            have hBdegree : B.totalDegree < G.totalDegree := by
              have h := roughMainCoefficient_totalDegree_lt Gm hGm hmainG
              simpa [B, Gm, hGmDegree] using h
            have hsumA : A.totalDegree + Gm.totalDegree < d := by
              omega
            have hsumB : Fm.totalDegree + B.totalDegree < d := by
              omega
            have hRecA := ih (A.totalDegree + Gm.totalDegree) hsumA
              (nF + 1) (nG + 1) A Gm hA hGm rfl
            have hRecB := ih (Fm.totalDegree + B.totalDegree) hsumB
              (nF + 1) (nG + 1) Fm B hFm hB rfl
            rcases hRecA with ⟨cA, hcA, hboundA⟩
            rcases hRecB with ⟨cB, hcB, hboundB⟩
            obtain ⟨cZA, hcZA, hboundZA⟩ :=
              polynomial_zero_dyadic_prime_bound_sqrt A hA (by omega)
            obtain ⟨cZB, hcZB, hboundZB⟩ :=
              polynomial_zero_dyadic_prime_bound_sqrt B hB (by omega)
            refine ⟨(cA, (cB, (cZA, cZB))), ?_⟩
            exact ⟨hcA, hcB, hcZA, hcZB, hboundA, hboundB, hboundZA, hboundZB⟩
          let choices : ActivePair → ℝ × (ℝ × (ℝ × ℝ)) := fun z =>
            Classical.choose (hdata z)
          have hchoices (z : ActivePair) :
              0 < (choices z).1 ∧ 0 < (choices z).2.1 ∧
              0 < (choices z).2.2.1 ∧ 0 < (choices z).2.2.2 ∧
              roughLargePrimeDivisorBoundConstant
                (leadF z.1.1) (moveG z.1.2) (choices z).1 ∧
              roughLargePrimeDivisorBoundConstant
                (moveF z.1.1) (leadG z.1.2) (choices z).2.1 ∧
              roughZeroPrimeDivisorBoundConstant
                (leadF z.1.1) (choices z).2.2.1 ∧
              roughZeroPrimeDivisorBoundConstant
                (leadG z.1.2) (choices z).2.2.2 :=
            Classical.choose_spec (hdata z)
          let cRecA : ActivePair → ℝ := fun z => (choices z).1
          let cRecB : ActivePair → ℝ := fun z => (choices z).2.1
          let cZeroA : ActivePair → ℝ := fun z => (choices z).2.2.1
          let cZeroB : ActivePair → ℝ := fun z => (choices z).2.2.2
          have hcRecA : ∀ z, 0 < cRecA z := fun z => (hchoices z).1
          have hcRecB : ∀ z, 0 < cRecB z := fun z => (hchoices z).2.1
          have hcZeroA : ∀ z, 0 < cZeroA z := fun z => (hchoices z).2.2.1
          have hcZeroB : ∀ z, 0 < cZeroB z := fun z => (hchoices z).2.2.2.1
          let CRec : ℝ := ∑ z : ActivePair,
            (cRecA z + cRecB z + cZeroA z + cZeroB z + 1)
          have hCRecNonneg : 0 ≤ CRec := by
            dsimp [CRec]
            apply Finset.sum_nonneg
            intro z hz
            have hA : 0 ≤ cRecA z := (hcRecA z).le
            have hB : 0 ≤ cRecB z := (hcRecB z).le
            have hZA : 0 ≤ cZeroA z := (hcZeroA z).le
            have hZB : 0 ≤ cZeroB z := (hcZeroB z).le
            positivity
          let C : ℝ := Csmall + Cmed + CexpF + CexpG + CRec
          have hCsmallPos : 0 < Csmall := by
            dsimp [Csmall]
            exact div_pos (Real.sqrt_pos.2
              (by exact_mod_cast (by omega : 0 < T))) hlog2
          have hCbaseNonneg : 0 ≤ Cmed + CexpF + CexpG := by
            dsimp [Cmed, CexpF, CexpG]
            positivity
          have hCpos : 0 < C := by
            dsimp [C]
            linarith [hCsmallPos, hCbaseNonneg, hCRecNonneg]
          refine ⟨C, hCpos, ?_⟩
          intro YF YG L hYF hYG hL
          have hMassF : ∀ i, 0 < primePoolMass (YF i) (2 * YF i) := by
            intro i
            exact dyadicPrimePoolMass_pos (YF i)
              ((by omega : 2 ≤ L).trans (hYF i))
          have hMassG : ∀ j, 0 < primePoolMass (YG j) (2 * YG j) := by
            intro j
            exact dyadicPrimePoolMass_pos (YG j)
              ((by omega : 2 ≤ L).trans (hYG j))
          have hprobOne := independentPrimePairProbability_le_one
            YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) hMassF hMassG
            (roughLargePrimeDivisorEvent F G L)
          by_cases hsmall : L < T
          · have hlog2le : Real.log 2 ≤ Real.log (L : ℝ) :=
              Real.log_le_log (by norm_num)
                (by exact_mod_cast (by omega : 2 ≤ L))
            have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
            have hsqrtTpos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
            have hsqrtLpos : 0 < Real.sqrt (L : ℝ) :=
              Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < L))
            have hsqrtLE : Real.sqrt (L : ℝ) ≤ Real.sqrt (T : ℝ) := by
              apply Real.sqrt_le_sqrt
              exact_mod_cast (Nat.le_of_lt hsmall)
            have hprod : Real.log 2 * Real.sqrt (L : ℝ) ≤
                Real.log (L : ℝ) * Real.sqrt (T : ℝ) := by
              calc
                _ ≤ Real.log 2 * Real.sqrt (T : ℝ) :=
                  mul_le_mul_of_nonneg_left hsqrtLE (Real.log_pos (by norm_num)).le
                _ ≤ Real.log (L : ℝ) * Real.sqrt (T : ℝ) :=
                  mul_le_mul_of_nonneg_right hlog2le hsqrtTpos.le
            have hcover : 1 ≤ Csmall *
                (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
              dsimp [Csmall]
              field_simp [hlog2.ne', hsqrtLpos.ne']
              nlinarith
            have hCsmall : Csmall ≤ C := by
              dsimp [C]
              nlinarith [hCbaseNonneg, hCRecNonneg]
            have hratioNonneg : 0 ≤ Real.log (L : ℝ) / Real.sqrt (L : ℝ) :=
              div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L)))
                (Real.sqrt_nonneg _)
            have hcoverCratio : 1 ≤ C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
              exact hcover.trans
                (mul_le_mul_of_nonneg_right hCsmall hratioNonneg)
            have hcoverC : 1 ≤ C * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
              calc
                _ ≤ C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := hcoverCratio
                _ = C * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by ring
            exact hprobOne.trans hcoverC
          · have hTL : T ≤ L := Nat.le_of_not_gt hsmall
            have hLlarge : 9 ≤ L := le_trans hT9 hTL
            have hYbtL : Ybt ≤ L := le_trans hTYbt hTL
            have hYFsmall : ∀ i, L ≤ YF i := hYF
            have hYGsmall : ∀ j, L ≤ YG j := hYG
            obtain ⟨iF, hiF, hmaxF⟩ := exists_max_active_endpoint F YF hvarsF
            obtain ⟨iG, hiG, hmaxG⟩ := exists_max_active_endpoint G YG hvarsG
            let eF := roughMoveMainPerm zeroF iF
            let eG := roughMoveMainPerm zeroG iG
            let Fm := moveF iF
            let Gm := moveG iG
            let A := leadF iF
            let B := leadG iG
            have hFm : Fm ≠ 0 := by
              intro hz
              apply hF
              have hz' := congrArg (MvPolynomial.rename eF) hz
              simpa [Fm, moveF, eF, MvPolynomial.rename_rename] using hz'
            have hGm : Gm ≠ 0 := by
              intro hz
              apply hG
              have hz' := congrArg (MvPolynomial.rename eG) hz
              simpa [Gm, moveG, eG, MvPolynomial.rename_rename] using hz'
            let YF0 : Fin (nF + 1) → ℕ := fun a => YF (eF a)
            let YG0 : Fin (nG + 1) → ℕ := fun b => YG (eG b)
            have hYF0 : ∀ a, L ≤ YF0 a := fun a => hYF (eF a)
            have hYG0 : ∀ b, L ≤ YG0 b := fun b => hYG (eG b)
            have heFzero : eF zeroF = iF := by
              simp [eF, roughMoveMainPerm, zeroF]
            have heGzero : eG zeroG = iG := by
              simp [eG, roughMoveMainPerm, zeroG]
            have hMoveF := roughMoveMain_active_endpoint F YF zeroF iF hiF hmaxF
            have hMoveG := roughMoveMain_active_endpoint G YG zeroG iG hiG hmaxG
            have hActiveMaxF : ∀ a ∈ Fm.vars, YF0 a ≤ YF0 zeroF := by
              intro a ha
              have h := hMoveF.2 a (by simpa [Fm, moveF, eF] using ha)
              change YF (eF a) ≤ YF (eF zeroF)
              rw [heFzero]
              exact h
            have hActiveMaxG : ∀ b ∈ Gm.vars, YG0 b ≤ YG0 zeroG := by
              intro b hb
              have h := hMoveG.2 b (by simpa [Gm, moveG, eG] using hb)
              change YG (eG b) ≤ YG (eG zeroG)
              rw [heGzero]
              exact h
            let Y0 : ℕ := min (YF0 zeroF) (YG0 zeroG)
            have hLY0 : L ≤ Y0 := by
              dsimp [Y0]
              exact Nat.le_min.mpr ⟨hYF0 zeroF, hYG0 zeroG⟩
            have hY0F : Y0 ≤ YF0 zeroF := by dsimp [Y0]; exact Nat.min_le_left _ _
            have hY0G : Y0 ≤ YG0 zeroG := by dsimp [Y0]; exact Nat.min_le_right _ _
            have hY0large : 9 ≤ Y0 := le_trans hLlarge hLY0
            have hYbtY0 : Ybt ≤ Y0 := le_trans hYbtL hLY0
            have hcoeffF :
                (roughCoefficientMass (roughMainCoefficientTail Fm) + 1) ^ 2 ≤ L := by
              have hcomp := hcomplexF iF
              dsimp [complexityF] at hcomp
              have htoL : sumComplexityF ≤ L := le_trans hTSF hTL
              exact (Nat.le_add_left _ _).trans (hcomp.trans htoL)
            have hcoeffG :
                (roughCoefficientMass (roughMainCoefficientTail Gm) + 1) ^ 2 ≤ L := by
              have hcomp := hcomplexG iG
              dsimp [complexityG] at hcomp
              have htoL : sumComplexityG ≤ L := le_trans hTSG hTL
              exact (Nat.le_add_left _ _).trans (hcomp.trans htoL)
            have hEvalCutF : roughCoefficientMass Fm * 2 ^ Fm.totalDegree ≤ Y0 := by
              have hcomp := hcomplexF iF
              dsimp [complexityF] at hcomp
              have htoY : sumComplexityF ≤ Y0 := le_trans hTSF (le_trans hTL hLY0)
              exact (Nat.le_add_right _ _).trans (hcomp.trans htoY)
            have hEvalCutG : roughCoefficientMass Gm * 2 ^ Gm.totalDegree ≤ Y0 := by
              have hcomp := hcomplexG iG
              dsimp [complexityG] at hcomp
              have htoY : sumComplexityG ≤ Y0 := le_trans hTSG (le_trans hTL hLY0)
              exact (Nat.le_add_right _ _).trans (hcomp.trans htoY)
            let q : ℝ := Real.log (L : ℝ) / Real.sqrt (L : ℝ)
            have hqnonneg : 0 ≤ q := by
              dsimp [q]
              exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L)))
                (Real.sqrt_nonneg _)
            have hFdegreeMoved : Fm.totalDegree = F.totalDegree := by
              simpa [Fm, moveF, eF] using totalDegree_rename_perm eF.symm F
            have hGdegreeMoved : Gm.totalDegree = G.totalDegree := by
              simpa [Gm, moveG, eG] using totalDegree_rename_perm eG.symm G
            have hmed := roughMainMediumPrimeProbability_bound Fm Gm hFm hGm
              YF0 YG0 hYF0 hYG0 hLlarge hLY0 hY0F hY0G hcoeffF hcoeffG
              Cbt hCbt Ybt hYbtL hBTall
            have hmed' :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b)
                  (fun x y => ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
                    p ^ 2 ≤ Y0 ∧
                    ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                      ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                    ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                      ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))) ≤
                Cmed * q := by
              convert hmed using 1 <;>
                simp [A, B, leadF, leadG, moveF, moveG, Fm, Gm, eF, eG,
                  Cmed, q, hFdegreeMoved, hGdegreeMoved] <;> ring
            have hMassF0 : ∀ a, 0 < primePoolMass (YF0 a) (2 * YF0 a) := by
              intro a
              exact dyadicPrimePoolMass_pos (YF0 a)
                ((by omega : 2 ≤ L).trans (hYF0 a))
            have hMassG0 : ∀ b, 0 < primePoolMass (YG0 b) (2 * YG0 b) := by
              intro b
              exact dyadicPrimePoolMass_pos (YG0 b)
                ((by omega : 2 ≤ L).trans (hYG0 b))
            let EzeroA : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => evalIntegerPolynomial A (fun a => (x a : ℤ)) = 0
            let EzeroB : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => evalIntegerPolynomial B (fun b => (y b : ℤ)) = 0
            let ErecA := fun x y => roughLargePrimeDivisorEvent A Gm L x y
            let ErecB := fun x y => roughLargePrimeDivisorEvent Fm B L x y
            let Eunit : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop := fun x y =>
              evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ≠ 0 ∧
              evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ≠ 0 ∧
              ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))
            let EunitMed : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop := fun x y =>
              evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ≠ 0 ∧
              evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ≠ 0 ∧
              ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧ p ^ 2 ≤ Y0 ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))
            let EunitHigh : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop := fun x y =>
              evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ≠ 0 ∧
              evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ≠ 0 ∧
              ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧ Y0 < p ^ 2 ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                  ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))
            let Efirst : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => EzeroA x y ∨ EzeroB x y
            let Esecond : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => ErecA x y ∨ ErecB x y
            let Ecombined : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => Efirst x y ∨ Esecond x y
            let Edecomp : (Fin (nF + 1) → ℕ) → (Fin (nG + 1) → ℕ) → Prop :=
              fun x y => Ecombined x y ∨ Eunit x y
            let Etarget := roughLargePrimeDivisorEvent Fm Gm L
            have hsubset : ∀ x y, Etarget x y → Edecomp x y := by
              intro x y h
              rcases h with ⟨hFx, hGy, p, hp, hsqrt, hdivF, hdivG⟩
              change ((EzeroA x y ∨ EzeroB x y) ∨
                (ErecA x y ∨ ErecB x y)) ∨ Eunit x y
              by_cases hAz : evalIntegerPolynomial A (fun a => (x a : ℤ)) = 0
              · exact Or.inl (Or.inl (Or.inl hAz))
              · by_cases hAd : (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))
                · exact Or.inl (Or.inr (Or.inl ⟨hAz, hGy, p, hp, hsqrt, hAd, hdivG⟩))
                · by_cases hBz : evalIntegerPolynomial B (fun b => (y b : ℤ)) = 0
                  · exact Or.inl (Or.inl (Or.inr hBz))
                  · by_cases hBd : (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ))
                    · exact Or.inl (Or.inr (Or.inr ⟨hFx, hBz, p, hp, hsqrt, hdivF, hBd⟩))
                    · apply Or.inr
                      exact ⟨hFx, hGy, p, hp, hsqrt,
                        ⟨hdivF, hAd⟩, ⟨hdivG, hBd⟩⟩
            have hmono := independentPrimePairProbability_mono
              YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
              Etarget Edecomp hsubset
            have hUfirst := independentPrimePairProbability_or_le
              YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
              EzeroA EzeroB
            have hUsecond := independentPrimePairProbability_or_le
              YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
              ErecA ErecB
            have hUcombined := independentPrimePairProbability_or_le
              YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
              Efirst Esecond
            have hUdecomp := independentPrimePairProbability_or_le
              YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
              Ecombined Eunit
            have hUnitMed :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) EunitMed ≤ Cmed * q := by
              have hsubMed : ∀ x y, EunitMed x y →
                  (∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧ p ^ 2 ≤ Y0 ∧
                    ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                      ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                    ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                      ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))) := by
                intro x y hxy
                rcases hxy with ⟨_, _, p, hp, hsqrt, hp2,
                  ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
                exact ⟨p, hp, hsqrt, hp2, ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
              have hmonoMed := independentPrimePairProbability_mono
                YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
                EunitMed
                (fun x y => ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
                  p ^ 2 ≤ Y0 ∧
                  ((p : ℤ) ∣ evalIntegerPolynomial Fm (fun a => (x a : ℤ)) ∧
                    ¬ (p : ℤ) ∣ evalIntegerPolynomial A (fun a => (x a : ℤ))) ∧
                  ((p : ℤ) ∣ evalIntegerPolynomial Gm (fun b => (y b : ℤ)) ∧
                    ¬ (p : ℤ) ∣ evalIntegerPolynomial B (fun b => (y b : ℤ)))) hsubMed
              exact hmonoMed.trans hmed'
            have hupper : independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                YG0 (fun b => 2 * YG0 b) EunitHigh ≤ (CexpF + CexpG) * q := by
              by_cases horder : YF0 zeroF ≤ YG0 zeroG
              · have hFmainComplex : roughCoefficientMass Fm * 2 ^ Fm.totalDegree ≤ Y0 := hEvalCutF
                have hGtailComplex :
                    (roughCoefficientMass (roughMainCoefficientTail Gm) + 1) ^ 2 ≤ Y0 := by
                  have hcomp := hcomplexG iG
                  dsimp [complexityG] at hcomp
                  omega
                have hActiveMaxF0 : ∀ a ∈ Fm.vars, YF0 a ≤ Y0 := by
                  intro a ha
                  rw [show Y0 = YF0 zeroF by
                    dsimp [Y0]
                    exact Nat.min_eq_left horder]
                  exact hActiveMaxF a ha
                have hMassGTail : ∀ b : Fin nG,
                    0 < primePoolMass (YG0 b.succ) (2 * YG0 b.succ) := by
                  intro b
                  exact dyadicPrimePoolMass_pos (YG0 b.succ)
                    ((by omega : 2 ≤ L).trans (hYG0 b.succ))
                have hBTtest : ∀ p, p.Prime → p ^ 2 ≤ YG0 zeroG →
                    ∀ a : Fin p, 0 < a.val →
                      (∑ q ∈ (Finset.Ico (YG0 zeroG) (2 * YG0 zeroG)).filter Nat.Prime,
                        if q % p = a.val then primePoolLaw (YG0 zeroG)
                          (2 * YG0 zeroG) q else 0) ≤ Cbt / p := by
                  intro p hp hp2 a ha
                  exact hBTall (YG0 zeroG) (by omega) p hp hp2 a ha
                have hExpoRaw := roughLargeExposureProbability_le Fm Gm hGm YF0 hMassF0
                  (fun b => YG0 b.succ) (fun b => 2 * YG0 b.succ) hMassGTail
                  hActiveMaxF0 hY0large hY0G hFmainComplex hGtailComplex
                  Cbt Aatom hCbt hAatom hBTtest hAtom
                have hGlo : Fin.cons (YG0 zeroG) (fun b : Fin nG => YG0 b.succ) = YG0 := by
                  funext b
                  exact Fin.cases rfl (fun b => rfl) b
                have hGhi : Fin.cons (2 * YG0 zeroG)
                    (fun b : Fin nG => 2 * YG0 b.succ) = (fun b => 2 * YG0 b) := by
                  funext b
                  exact Fin.cases rfl (fun b => rfl) b
                have hExpo : independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                    YG0 (fun b => 2 * YG0 b) (roughLargeExposureEvent Fm Gm Y0) ≤
                    CexpF * q := by
                  have hratio := log_div_sqrt_antitone hLlarge hLY0
                  have hcoef : (2 * (Fm.totalDegree + 1) : ℝ) *
                      ((Gm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom)) = CexpF := by
                    simp [CexpF, hFdegreeMoved, hGdegreeMoved]
                    ring
                  have hscale : (2 * (Fm.totalDegree + 1) : ℝ) *
                      ((Gm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) *
                        (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) ≤ CexpF * q := by
                    calc
                      _ = ((2 * (Fm.totalDegree + 1) : ℝ) *
                            ((Gm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom))) *
                            (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by ring
                      _ ≤ CexpF * q := by
                            rw [hcoef]
                            dsimp [q]
                            exact mul_le_mul_of_nonneg_left hratio (by positivity)
                  simpa [hGlo, hGhi] using hExpoRaw.trans hscale
                have hsubsetExpo : ∀ x y, EunitHigh x y →
                    roughLargeExposureEvent Fm Gm Y0 x y := by
                  intro x y hxy
                  rcases hxy with ⟨hFx, hGy, p, hp, hsqrt, hpAbove,
                    ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
                  have hdivNat : p ∣ (evalIntegerPolynomial Fm
                      (fun a => (x a : ℤ))).natAbs := by
                    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdivF)
                  have hFabs : (evalIntegerPolynomial Fm
                      (fun a => (x a : ℤ))).natAbs ≠ 0 := by
                    intro hz
                    exact hFx (Int.natAbs_eq_zero.mp hz)
                  have hmem : p ∈
                      roughLargePrimeFactors (evalIntegerPolynomial Fm
                        (fun a => (x a : ℤ))).natAbs Y0 := by
                    apply Finset.mem_filter.mpr
                    refine ⟨?_, ?_⟩
                    · exact hp.mem_primeFactors hdivNat hFabs
                    · omega
                  exact ⟨p, hmem, hdivG, hnotB⟩
                have hmonoExpo := independentPrimePairProbability_mono
                  YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
                  EunitHigh (roughLargeExposureEvent Fm Gm Y0) hsubsetExpo
                have hunitExpo := hmonoExpo.trans hExpo
                have hCexpFnonneg : 0 ≤ CexpF := by dsimp [CexpF]; positivity
                have hCexpFle : CexpF ≤ CexpF + CexpG := by
                  linarith [show 0 ≤ CexpG by dsimp [CexpG]; positivity]
                exact hunitExpo.trans (mul_le_mul_of_nonneg_right hCexpFle hqnonneg)
              · have horder' : YG0 zeroG ≤ YF0 zeroF := by omega
                have hGmainComplex : roughCoefficientMass Gm * 2 ^ Gm.totalDegree ≤ Y0 := hEvalCutG
                have hFtailComplex :
                    (roughCoefficientMass (roughMainCoefficientTail Fm) + 1) ^ 2 ≤ Y0 := by
                  have hcomp := hcomplexF iF
                  dsimp [complexityF] at hcomp
                  omega
                have hActiveMaxG0 : ∀ b ∈ Gm.vars, YG0 b ≤ Y0 := by
                  intro b hb
                  rw [show Y0 = YG0 zeroG by
                    dsimp [Y0]
                    exact Nat.min_eq_right horder']
                  exact hActiveMaxG b hb
                have hMassFTail : ∀ a : Fin nF,
                    0 < primePoolMass (YF0 a.succ) (2 * YF0 a.succ) := by
                  intro a
                  exact dyadicPrimePoolMass_pos (YF0 a.succ)
                    ((by omega : 2 ≤ L).trans (hYF0 a.succ))
                have hBTtest : ∀ p, p.Prime → p ^ 2 ≤ YF0 zeroF →
                    ∀ a : Fin p, 0 < a.val →
                      (∑ q ∈ (Finset.Ico (YF0 zeroF) (2 * YF0 zeroF)).filter Nat.Prime,
                        if q % p = a.val then primePoolLaw (YF0 zeroF)
                          (2 * YF0 zeroF) q else 0) ≤ Cbt / p := by
                  intro p hp hp2 a ha
                  exact hBTall (YF0 zeroF) (by omega) p hp hp2 a ha
                have hExpoRaw := roughLargeExposureProbability_le Gm Fm hFm YG0 hMassG0
                  (fun a => YF0 a.succ) (fun a => 2 * YF0 a.succ) hMassFTail
                  hActiveMaxG0 hY0large hY0F hGmainComplex hFtailComplex
                  Cbt Aatom hCbt hAatom hBTtest hAtom
                have hFlo : Fin.cons (YF0 zeroF) (fun a : Fin nF => YF0 a.succ) = YF0 := by
                  funext a
                  exact Fin.cases rfl (fun a => rfl) a
                have hFhi : Fin.cons (2 * YF0 zeroF)
                    (fun a : Fin nF => 2 * YF0 a.succ) = (fun a => 2 * YF0 a) := by
                  funext a
                  exact Fin.cases rfl (fun a => rfl) a
                have hExpo : independentPrimePairProbability YG0 (fun b => 2 * YG0 b)
                    YF0 (fun a => 2 * YF0 a) (roughLargeExposureEvent Gm Fm Y0) ≤
                    CexpG * q := by
                  have hratio := log_div_sqrt_antitone hLlarge hLY0
                  have hcoef : (2 * (Gm.totalDegree + 1) : ℝ) *
                      ((Fm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom)) = CexpG := by
                    simp [CexpG, hFdegreeMoved, hGdegreeMoved]
                    ring
                  have hscale : (2 * (Gm.totalDegree + 1) : ℝ) *
                      ((Fm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom) *
                        (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ))) ≤ CexpG * q := by
                    calc
                      _ = ((2 * (Gm.totalDegree + 1) : ℝ) *
                            ((Fm.totalDegree : ℝ) * (Cbt / Real.log 2 + 3 * Aatom))) *
                            (Real.log (Y0 : ℝ) / Real.sqrt (Y0 : ℝ)) := by ring
                      _ ≤ CexpG * q := by
                            rw [hcoef]
                            dsimp [q]
                            exact mul_le_mul_of_nonneg_left hratio (by positivity)
                  simpa [hFlo, hFhi] using hExpoRaw.trans hscale
                have hsubsetExpo : ∀ y x, EunitHigh x y →
                    roughLargeExposureEvent Gm Fm Y0 y x := by
                  intro y x hxy
                  rcases hxy with ⟨hFx, hGy, p, hp, hsqrt, hpAbove,
                    ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
                  have hdivNat : p ∣ (evalIntegerPolynomial Gm
                      (fun b => (y b : ℤ))).natAbs := by
                    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdivG)
                  have hGabs : (evalIntegerPolynomial Gm
                      (fun b => (y b : ℤ))).natAbs ≠ 0 := by
                    intro hz
                    exact hGy (Int.natAbs_eq_zero.mp hz)
                  have hmem : p ∈
                      roughLargePrimeFactors (evalIntegerPolynomial Gm
                        (fun b => (y b : ℤ))).natAbs Y0 := by
                    apply Finset.mem_filter.mpr
                    refine ⟨?_, ?_⟩
                    · exact hp.mem_primeFactors hdivNat hGabs
                    · omega
                  exact ⟨p, hmem, hdivF, hnotA⟩
                have hswap := independentPrimePairProbability_swap
                  YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b) EunitHigh
                have hmonoExpo := independentPrimePairProbability_mono
                  YG0 (fun b => 2 * YG0 b) YF0 (fun a => 2 * YF0 a)
                  (fun y x => EunitHigh x y)
                  (roughLargeExposureEvent Gm Fm Y0) hsubsetExpo
                have hunitExpo := (hswap ▸ hmonoExpo).trans hExpo
                have hCexpGnonneg : 0 ≤ CexpG := by dsimp [CexpG]; positivity
                have hCexpGle : CexpG ≤ CexpF + CexpG := by
                  linarith [show 0 ≤ CexpF by dsimp [CexpF]; positivity]
                exact hunitExpo.trans (mul_le_mul_of_nonneg_right hCexpGle hqnonneg)
            have hunitBound :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) Eunit ≤ (Cmed + CexpF + CexpG) * q := by
              have hsubsetUnit : ∀ x y, Eunit x y → EunitMed x y ∨ EunitHigh x y := by
                intro x y hxy
                rcases hxy with ⟨hFx, hGy, p, hp, hsqrt,
                  ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
                by_cases hp2 : p ^ 2 ≤ Y0
                · left
                  exact ⟨hFx, hGy, p, hp, hsqrt, hp2,
                    ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
                · right
                  exact ⟨hFx, hGy, p, hp, hsqrt, Nat.lt_of_not_ge hp2,
                    ⟨hdivF, hnotA⟩, ⟨hdivG, hnotB⟩⟩
              have hmonoUnit := independentPrimePairProbability_mono
                YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
                Eunit (fun x y => EunitMed x y ∨ EunitHigh x y) hsubsetUnit
              have hUUnit := independentPrimePairProbability_or_le
                YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b)
                EunitMed EunitHigh
              calc
                _ ≤ independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b)
                        (fun x y => EunitMed x y ∨ EunitHigh x y) := hmonoUnit
                _ ≤ independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) EunitMed +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) EunitHigh := hUUnit
                _ ≤ Cmed * q + (CexpF + CexpG) * q := add_le_add hUnitMed hupper
                _ = (Cmed + CexpF + CexpG) * q := by ring
            let z : ActivePair := ⟨(iF, iG), ⟨hiF, hiG⟩⟩
            rcases hchoices z with ⟨hcA, hcB, hcZA, hcZB, hBoundA,
              hBoundB, hBoundZA, hBoundZB⟩
            have hzeroA :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) EzeroA ≤ cZeroA z * q := by
              rw [independentPrimePairProbability_left_event
                YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b) hMassG0
                (fun x => evalIntegerPolynomial A (fun a => (x a : ℤ)) = 0)]
              exact hBoundZA YF0 L hL (fun a => hYF0 a)
            have hzeroB :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) EzeroB ≤ cZeroB z * q := by
              rw [independentPrimePairProbability_right_event
                YF0 (fun a => 2 * YF0 a) YG0 (fun b => 2 * YG0 b) hMassF0
                (fun y => evalIntegerPolynomial B (fun b => (y b : ℤ)) = 0)]
              exact hBoundZB YG0 L hL (fun b => hYG0 b)
            have hrecA :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) ErecA ≤ cRecA z * q := by
              have hrecA' :
                  independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                    YG0 (fun b => 2 * YG0 b) ErecA ≤
                    (choices z).1 * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
                simpa [ErecA, A, leadF, moveF, Gm, moveG, z] using
                  hBoundA YF0 YG0 L hYF0 hYG0 hL
              calc
                _ ≤ (choices z).1 * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := hrecA'
                _ = cRecA z * q := by dsimp [cRecA, q]; ring
            have hrecB :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) ErecB ≤ cRecB z * q := by
              have hrecB' :
                  independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                    YG0 (fun b => 2 * YG0 b) ErecB ≤
                    (choices z).2.1 * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
                simpa [ErecB, B, leadG, moveG, Fm, moveF, z] using
                  hBoundB YF0 YG0 L hYF0 hYG0 hL
              calc
                _ ≤ (choices z).2.1 * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := hrecB'
                _ = cRecB z * q := by dsimp [cRecB, q]; ring
            have hsumUnit :
                cZeroA z * q + cZeroB z * q + cRecA z * q + cRecB z * q +
                    (Cmed + CexpF + CexpG) * q ≤ C * q := by
              have hselected :
                  cRecA z + cRecB z + cZeroA z + cZeroB z + 1 ≤ CRec := by
                dsimp [CRec]
                exact Finset.single_le_sum (f := fun z =>
                  cRecA z + cRecB z + cZeroA z + cZeroB z + 1)
                  (fun z hz => by
                    have hA : 0 ≤ cRecA z := (hcRecA z).le
                    have hB : 0 ≤ cRecB z := (hcRecB z).le
                    have hZA : 0 ≤ cZeroA z := (hcZeroA z).le
                    have hZB : 0 ≤ cZeroB z := (hcZeroB z).le
                    nlinarith)
                  (Finset.mem_univ z)
              have hconst : cZeroA z + cZeroB z + cRecA z + cRecB z +
                  (Cmed + CexpF + CexpG) ≤ C := by
                dsimp [C]
                nlinarith [hselected, hCbaseNonneg]
              calc
                _ = (cZeroA z + cZeroB z + cRecA z + cRecB z +
                    (Cmed + CexpF + CexpG)) * q := by ring
                _ ≤ C * q := mul_le_mul_of_nonneg_right hconst hqnonneg
            have hdecompBound :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) Edecomp ≤
                    cZeroA z * q + cZeroB z * q + cRecA z * q + cRecB z * q +
                      (Cmed + CexpF + CexpG) * q := by
              calc
                _ ≤ independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Ecombined +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Eunit := hUdecomp
                _ ≤ (independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Efirst +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Esecond) +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Eunit := by
                        exact add_le_add hUcombined le_rfl
                _ ≤ (independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) EzeroA +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) EzeroB) +
                    (independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) ErecA +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) ErecB) +
                    independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                      YG0 (fun b => 2 * YG0 b) Eunit := by
                        apply add_le_add
                        · exact add_le_add hUfirst hUsecond
                        · exact le_rfl
                _ ≤ cZeroA z * q + cZeroB z * q + cRecA z * q + cRecB z * q +
                    (Cmed + CexpF + CexpG) * q := by
                      calc
                        _ ≤ (cZeroA z * q + cZeroB z * q) +
                            (cRecA z * q + cRecB z * q) +
                            (Cmed + CexpF + CexpG) * q := by
                              apply add_le_add
                              · apply add_le_add
                                · exact add_le_add hzeroA hzeroB
                                · exact add_le_add hrecA hrecB
                              · exact hunitBound
                        _ = _ := by ring
            have htargetBound :
                independentPrimePairProbability YF0 (fun a => 2 * YF0 a)
                  YG0 (fun b => 2 * YG0 b) Etarget ≤ C * q :=
              hmono.trans (hdecompBound.trans hsumUnit)
            have hReindex := roughLargePrimeDivisorEvent_reindex eF eG F G L YF YG
            have hFinal := hReindex ▸ htargetBound
            calc
              _ ≤ C * q := hFinal
              _ = C * Real.log (L : ℝ) / Real.sqrt (L : ℝ) := by
                dsimp [q]
                ring
  have hresult := hInduction (F.totalDegree + G.totalDegree) kF kG F G hF hG rfl
  exact hresult

set_option maxHeartbeats 200000

/-- Lemma `lem:rough-coprimality`: for fixed nonzero integer polynomials in disjoint
independent prime tuples sampled harmonically from dyadic intervals, the polynomial-zero
probability is `O(log L/L)` and the probability of a common rough prime factor is
`O(1/w+log L/√L)`, uniformly in endpoint ratios (§3 lines 353–370). -/
theorem lem_rough_coprimality {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ N₀ : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (w : ℕ),
      N₀ ≤ w → N₀ ≤ roughSmallestEndpoint YF YG →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y => evalIntegerPolynomial F (fun i => (x i : ℤ)) = 0 ∨
          evalIntegerPolynomial G (fun i => (y i : ℤ)) = 0) ≤
          C * Real.log (roughSmallestEndpoint YF YG) /
            roughSmallestEndpoint YF YG ∧
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          Nat.gcd
            (roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))))
            (roughPart w (evalIntegerPolynomial G (fun i => (y i : ℤ)))) > 1) ≤
          C * (1 / w + Real.log (roughSmallestEndpoint YF YG) /
            Real.sqrt (roughSmallestEndpoint YF YG)) := by
  classical
  obtain ⟨CF, hCF, hzeroF⟩ := polynomial_zero_dyadic_prime_bound F hF
  obtain ⟨CG, hCG, hzeroG⟩ := polynomial_zero_dyadic_prime_bound G hG
  obtain ⟨CS, hCS, hsmall⟩ := rough_coprimality_small_prime_divisors F G hF hG
  obtain ⟨CL, hCL, hlarge⟩ := rough_coprimality_large_prime_divisors F G hF hG
  let N₀ : ℕ := 2
  let C : ℝ := 2 * (CF + CG) + CS + CL + 1
  refine ⟨N₀, C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro YF YG w hNw hNL
    let L : ℕ := roughSmallestEndpoint YF YG
    let ZF : (Fin kF → ℕ) → Prop := fun x =>
      evalIntegerPolynomial F (fun i => (x i : ℤ)) = 0
    let ZG : (Fin kG → ℕ) → Prop := fun y =>
      evalIntegerPolynomial G (fun i => (y i : ℤ)) = 0
    let ERough : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y =>
      evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
      evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
      Nat.gcd
        (roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))))
        (roughPart w (evalIntegerPolynomial G (fun j => (y j : ℤ)))) > 1
    let ESmall : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y =>
      evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
      evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
      ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
        (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
        (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ))
    let ELarge : (Fin kF → ℕ) → (Fin kG → ℕ) → Prop := fun x y =>
      evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
      evalIntegerPolynomial G (fun j => (y j : ℤ)) ≠ 0 ∧
      ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
        (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
        (p : ℤ) ∣ evalIntegerPolynomial G (fun j => (y j : ℤ))
    have hL : 2 ≤ L := by
      dsimp [L, N₀] at hNL ⊢
      exact hNL
    have hLleft : ∀ i, L ≤ YF i := by
      intro i
      exact roughSmallestEndpoint_le_left YF YG i
    have hLright : ∀ j, L ≤ YG j := by
      intro j
      exact roughSmallestEndpoint_le_right YF YG j
    have hYF : ∀ i, 2 ≤ YF i := fun i => (hL.trans (hLleft i))
    have hYG : ∀ j, 2 ≤ YG j := fun j => (hL.trans (hLright j))
    have hmassF : ∀ i, 0 < primePoolMass (YF i) (2 * YF i) :=
      fun i => dyadicPrimePoolMass_pos (YF i) (hYF i)
    have hmassG : ∀ j, 0 < primePoolMass (YG j) (2 * YG j) :=
      fun j => dyadicPrimePoolMass_pos (YG j) (hYG j)
    have hpairF :
        independentPrimePairProbability YF (fun i => 2 * YF i)
          YG (fun j => 2 * YG j) (fun x y => ZF x) =
        independentPrimePoolProbability YF (fun i => 2 * YF i) ZF := by
      calc
        _ = independentPrimePoolProbability YF (fun i => 2 * YF i) ZF *
              independentPrimePoolProbability YG (fun j => 2 * YG j) (fun _ => True) := by
                simpa using (independentPrimePairProbability_product
                  YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) ZF (fun _ => True))
        _ = _ := by
          rw [independentPrimePoolProbability_true YG (fun j => 2 * YG j) hmassG]
          ring
    have hpairG :
        independentPrimePairProbability YF (fun i => 2 * YF i)
          YG (fun j => 2 * YG j) (fun x y => ZG y) =
        independentPrimePoolProbability YG (fun j => 2 * YG j) ZG := by
      calc
        _ = independentPrimePoolProbability YF (fun i => 2 * YF i) (fun _ => True) *
              independentPrimePoolProbability YG (fun j => 2 * YG j) ZG := by
                simpa using (independentPrimePairProbability_product
                  YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) (fun _ => True) ZG)
        _ = _ := by
          rw [independentPrimePoolProbability_true YF (fun i => 2 * YF i) hmassF]
          ring
    have hzeroF0 := hzeroF YF hYF
    have hzeroG0 := hzeroG YG hYG
    have hminF : 0 < kF → L ≤ smallestPrimeEndpoint YF := by
      intro hk
      change roughSmallestEndpoint YF YG ≤ smallestPrimeEndpoint YF
      unfold smallestPrimeEndpoint
      split_ifs with hS
      · rw [Finset.le_min'_iff]
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨i, _, rfl⟩
        exact roughSmallestEndpoint_le_left YF YG i
      · exact False.elim (hS ⟨YF ⟨0, hk⟩,
          Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩)
    have hminG : 0 < kG → L ≤ smallestPrimeEndpoint YG := by
      intro hk
      change roughSmallestEndpoint YF YG ≤ smallestPrimeEndpoint YG
      unfold smallestPrimeEndpoint
      split_ifs with hS
      · rw [Finset.le_min'_iff]
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨j, _, rfl⟩
        exact roughSmallestEndpoint_le_right YF YG j
      · exact False.elim (hS ⟨YG ⟨0, hk⟩,
          Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩)
    let rL : ℝ := Real.log (L : ℝ) / (L : ℝ)
    have hrL : 0 ≤ rL := by
      dsimp [rL]
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L)))
        (by positivity)
    have hzeroF : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (fun x y => ZF x) ≤ (2 * CF) * rL := by
      by_cases hk : 0 < kF
      · have hratio := dyadic_log_ratio_le_two hL (hminF hk)
        calc
          _ = independentPrimePoolProbability YF (fun i => 2 * YF i) ZF := hpairF
          _ ≤ CF * Real.log (smallestPrimeEndpoint YF : ℝ) /
                smallestPrimeEndpoint YF := hzeroF0
          _ ≤ CF * (2 * rL) := by
                calc
                  _ = CF * (Real.log (smallestPrimeEndpoint YF : ℝ) /
                        smallestPrimeEndpoint YF) := by ring
                  _ ≤ CF * (2 * rL) :=
                    mul_le_mul_of_nonneg_left (by simpa [rL] using hratio) hCF.le
          _ = (2 * CF) * rL := by ring
      · have hk0 : kF = 0 := Nat.eq_zero_of_not_pos hk
        have hmin : smallestPrimeEndpoint YF = 1 := by
          simp [smallestPrimeEndpoint, hk0]
        have hle0 : independentPrimePoolProbability YF (fun i => 2 * YF i) ZF ≤ 0 := by
          simpa [hmin] using hzeroF0
        rw [hpairF]
        have hnonneg : 0 ≤ (2 * CF) * rL := mul_nonneg (by positivity) hrL
        exact hle0.trans hnonneg
    have hzeroG : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (fun x y => ZG y) ≤ (2 * CG) * rL := by
      by_cases hk : 0 < kG
      · have hratio := dyadic_log_ratio_le_two hL (hminG hk)
        calc
          _ = independentPrimePoolProbability YG (fun j => 2 * YG j) ZG := hpairG
          _ ≤ CG * Real.log (smallestPrimeEndpoint YG : ℝ) /
                smallestPrimeEndpoint YG := hzeroG0
          _ ≤ CG * (2 * rL) := by
                calc
                  _ = CG * (Real.log (smallestPrimeEndpoint YG : ℝ) /
                        smallestPrimeEndpoint YG) := by ring
                  _ ≤ CG * (2 * rL) :=
                    mul_le_mul_of_nonneg_left (by simpa [rL] using hratio) hCG.le
          _ = (2 * CG) * rL := by ring
      · have hk0 : kG = 0 := Nat.eq_zero_of_not_pos hk
        have hmin : smallestPrimeEndpoint YG = 1 := by
          simp [smallestPrimeEndpoint, hk0]
        have hle0 : independentPrimePoolProbability YG (fun j => 2 * YG j) ZG ≤ 0 := by
          simpa [hmin] using hzeroG0
        rw [hpairG]
        have hnonneg : 0 ≤ (2 * CG) * rL := mul_nonneg (by positivity) hrL
        exact hle0.trans hnonneg
    have hzeroUnion := independentPrimePairProbability_or_le
      YF (fun i => 2 * YF i) YG (fun j => 2 * YG j)
        (fun x y => ZF x) (fun x y => ZG y)
    have hzeroBound : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) (fun x y => ZF x ∨ ZG y) ≤ C * rL := by
      calc
        _ ≤ independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) (fun x y => ZF x) +
            independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) (fun x y => ZG y) := hzeroUnion
        _ ≤ (2 * CF) * rL + (2 * CG) * rL := add_le_add hzeroF hzeroG
        _ = 2 * (CF + CG) * rL := by ring
        _ ≤ C * rL := by
          apply mul_le_mul_of_nonneg_right _ hrL
          dsimp [C]
          nlinarith [hCS.le, hCL.le]
    have hsubset : ∀ x y, ERough x y → ESmall x y ∨ ELarge x y := by
      intro x y hxy
      have hgcd : Nat.gcd
          (roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))))
          (roughPart w (evalIntegerPolynomial G (fun j => (y j : ℤ)))) > 1 := hxy.2.2
      have hgcdNe : Nat.gcd
          (roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))))
          (roughPart w (evalIntegerPolynomial G (fun j => (y j : ℤ)))) ≠ 1 := by omega
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcdNe
      have hpdvds :
          p ∣ roughPart w (evalIntegerPolynomial F (fun i => (x i : ℤ))) ∧
          p ∣ roughPart w (evalIntegerPolynomial G (fun j => (y j : ℤ))) :=
        (dvd_gcd_iff p _ _).mp hpdvd
      obtain ⟨hwp, hdivF⟩ := prime_dvd_roughPart hp hpdvds.1
      obtain ⟨_, hdivG⟩ := prime_dvd_roughPart hp hpdvds.2
      by_cases hp2 : p ^ 2 ≤ L
      · left
        exact ⟨hxy.1, hxy.2.1, p, hp, hwp, hp2, hdivF, hdivG⟩
      · right
        have hpow : (L : ℝ) < (p : ℝ) ^ 2 := by
          exact_mod_cast (Nat.lt_of_not_ge hp2)
        have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
        have hroot : Real.sqrt (L : ℝ) < (p : ℝ) := (Real.sqrt_lt' hpR).2 hpow
        exact ⟨hxy.1, hxy.2.1, p, hp, hroot, hdivF, hdivG⟩
    have hroughMono := independentPrimePairProbability_mono
      YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) ERough
      (fun x y => ESmall x y ∨ ELarge x y) hsubset
    have hroughUnion := independentPrimePairProbability_or_le
      YF (fun i => 2 * YF i) YG (fun j => 2 * YG j) ESmall ELarge
    have hw : 1 ≤ w := by omega
    have hsmallBound : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) ESmall ≤ CS / (w : ℝ) := by
      by_cases hwl : w < L
      · exact hsmall YF YG w L hLleft hLright hw hwl
      · have hempty : ∀ x y, ¬ ESmall x y := by
          intro x y hxy
          rcases hxy.2.2 with ⟨p, hp, hwp, hp2, _, _⟩
          have hpLe : p ≤ p ^ 2 := by
            calc
              p = p * 1 := by simp
              _ ≤ p * p := Nat.mul_le_mul_left p (by omega : 1 ≤ p)
              _ = p ^ 2 := by rw [pow_two]
          have hLw : L ≤ w := by omega
          omega
        have hprob0 : independentPrimePairProbability YF (fun i => 2 * YF i)
            YG (fun j => 2 * YG j) ESmall = 0 := by
          simp [independentPrimePairProbability, hempty]
        rw [hprob0]
        positivity
    have hlargeBound : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) ELarge ≤
        CL * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
      convert hlarge YF YG L hLleft hLright hL using 1 <;> ring
    have hroughBound : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) ERough ≤
        CS / (w : ℝ) + CL * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
      calc
        _ ≤ independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) (fun x y => ESmall x y ∨ ELarge x y) := hroughMono
        _ ≤ independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) ESmall +
            independentPrimePairProbability YF (fun i => 2 * YF i)
              YG (fun j => 2 * YG j) ELarge := hroughUnion
        _ ≤ CS / (w : ℝ) + CL * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) :=
              add_le_add hsmallBound hlargeBound
    have hCsmall : CS ≤ C := by dsimp [C]; nlinarith [hCF, hCG, hCL]
    have hClarge : CL ≤ C := by dsimp [C]; nlinarith [hCF, hCG, hCS]
    have hlogRoot : 0 ≤ Real.log (L : ℝ) / Real.sqrt (L : ℝ) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L)))
        (Real.sqrt_nonneg _)
    have hsec : independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun j => 2 * YG j) ERough ≤
        C * (1 / (w : ℝ) + Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
      calc
        _ ≤ CS / (w : ℝ) + CL * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := hroughBound
        _ ≤ C / (w : ℝ) + C * (Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by
              apply add_le_add
              · exact div_le_div_of_nonneg_right hCsmall (by positivity)
              · exact mul_le_mul_of_nonneg_right hClarge hlogRoot
        _ = C * (1 / (w : ℝ) + Real.log (L : ℝ) / Real.sqrt (L : ℝ)) := by ring
    constructor
    · convert hzeroBound using 1 <;> simp [L, rL, ZF, ZG, C] <;> ring
    · simpa [L, ERough, C] using hsec

/-- Restricting independent tuples to prime-only events of probability tending to one
preserves the rough-coprimality conclusion; this is the constructed-pool consequence at
§3 lines 434–438. -/
theorem rough_coprimality_survives_high_probability_restrictions
    {kF kG : ℕ} (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (poolF : ℕ → Fin kF → PrimePool) (poolG : ℕ → Fin kG → PrimePool)
    (EF : ℕ → (Fin kF → ℕ) → Prop) (EG : ℕ → (Fin kG → ℕ) → Prop)
    (hEF : Tendsto (fun N : ℕ => independentPrimePoolProbability
      (fun i => (poolF N i).lower) (fun i => (poolF N i).upper) (EF N))
      atTop (𝓝 1))
    (hEG : Tendsto (fun N : ℕ => independentPrimePoolProbability
      (fun i => (poolG N i).lower) (fun i => (poolG N i).upper) (EG N))
      atTop (𝓝 1))
    (hloF : ∀ i, Tendsto (fun N : ℕ => (poolF N i).lower) atTop atTop)
    (hloG : ∀ i, Tendsto (fun N : ℕ => (poolG N i).lower) atTop atTop) :
    Tendsto (fun N : ℕ => independentPrimePairProbability
      (fun i => (poolF N i).lower) (fun i => (poolF N i).upper)
      (fun i => (poolG N i).lower) (fun i => (poolG N i).upper)
      (fun x y => EF N x ∧ EG N y ∧
        Nat.gcd (roughPart (N + 1) (evalIntegerPolynomial F (fun i => (x i : ℤ))))
          (roughPart (N + 1) (evalIntegerPolynomial G (fun i => (y i : ℤ)))) = 1))
      atTop (𝓝 1) := by
  sorry

end
end HindmanSumsProducts
