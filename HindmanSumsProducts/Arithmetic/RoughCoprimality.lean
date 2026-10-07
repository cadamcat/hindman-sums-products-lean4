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

private def constantTwo : IntegerPolynomial 0 := MvPolynomial.C 2

private lemma constantTwo_ne_zero : constantTwo ≠ 0 := by
  norm_num [constantTwo]

private lemma constantTwo_eval (x : Fin 0 → ℤ) :
    evalIntegerPolynomial constantTwo x = 2 := by
  simp [constantTwo, evalIntegerPolynomial]

private lemma emptyTuple_pair_probability_true :
    independentPrimePairProbability
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun _ _ => True) = 1 := by
  classical
  simp [independentPrimePairProbability, independentPrimePoolMass]

private def smallPrimeCounterexampleEvent (x y : Fin 0 → ℕ) : Prop :=
  evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
    evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
    ∃ p : ℕ, p.Prime ∧ 0 < p ∧ p ^ 2 ≤ 4 ∧
      (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
      (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))

private lemma small_prime_counterexample_event_probability :
    independentPrimePairProbability
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      smallPrimeCounterexampleEvent = 1 := by
  change independentPrimePairProbability
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 0)
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 0)
      smallPrimeCounterexampleEvent = 1
  have hE : smallPrimeCounterexampleEvent = fun _ _ => True := by
    funext x y
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨by simp [constantTwo_eval], by simp [constantTwo_eval], ?_⟩
      refine ⟨2, Nat.prime_two, by norm_num, by norm_num, ?_, ?_⟩
      · rw [constantTwo_eval]
        norm_num
      · rw [constantTwo_eval]
        norm_num
  rw [hE]
  exact emptyTuple_pair_probability_true

private lemma no_small_prime_counterexample_constant :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin 0 → ℕ) (YG : Fin 0 → ℕ) (w L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → w < L →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p : ℕ, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
            (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))) ≤ C / w := by
  rintro ⟨C, _, hbound⟩
  have h := hbound (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) 0 4
    (by intro i; exact Fin.elim0 i) (by intro j; exact Fin.elim0 j) (by norm_num)
  have hE : (fun (x y : Fin 0 → ℕ) =>
      evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
      evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
      ∃ p : ℕ, p.Prime ∧ 0 < p ∧ p ^ 2 ≤ 4 ∧
        (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
        (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))) =
      smallPrimeCounterexampleEvent := rfl
  have hzero : independentPrimePairProbability
      (fun _ : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun _ : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      smallPrimeCounterexampleEvent ≤ C / (0 : ℝ) := by
    rw [← hE]
    simpa using h
  rw [small_prime_counterexample_event_probability] at hzero
  norm_num at hzero

private def largePrimeCounterexampleEvent (x y : Fin 0 → ℕ) : Prop :=
  evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
    evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
    ∃ p : ℕ, p.Prime ∧ Real.sqrt (1 : ℝ) < (p : ℝ) ∧
      (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
      (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))

private lemma large_prime_counterexample_event_probability :
    independentPrimePairProbability
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      largePrimeCounterexampleEvent = 1 := by
  change independentPrimePairProbability
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 0)
      (fun i : Fin 0 => 0) (fun i : Fin 0 => 0)
      largePrimeCounterexampleEvent = 1
  have hE : largePrimeCounterexampleEvent = fun _ _ => True := by
    funext x y
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨by simp [constantTwo_eval], by simp [constantTwo_eval], ?_⟩
      refine ⟨2, Nat.prime_two, by norm_num, ?_, ?_⟩
      · rw [constantTwo_eval]
        norm_num
      · rw [constantTwo_eval]
        norm_num
  rw [hE]
  exact emptyTuple_pair_probability_true

private lemma no_large_prime_counterexample_constant :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin 0 → ℕ) (YG : Fin 0 → ℕ) (L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
            (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))) ≤
        C * Real.log L / Real.sqrt L := by
  rintro ⟨C, _, hbound⟩
  have h := hbound (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) 1
    (by intro i; exact Fin.elim0 i) (by intro j; exact Fin.elim0 j)
  have hE : (fun (x y : Fin 0 → ℕ) =>
      evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ≠ 0 ∧
      evalIntegerPolynomial constantTwo (fun i => (y i : ℤ)) ≠ 0 ∧
      ∃ p : ℕ, p.Prime ∧ Real.sqrt (1 : ℝ) < (p : ℝ) ∧
        (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (x i : ℤ)) ∧
        (p : ℤ) ∣ evalIntegerPolynomial constantTwo (fun i => (y i : ℤ))) =
      largePrimeCounterexampleEvent := rfl
  have hzero : independentPrimePairProbability
      (fun _ : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      (fun _ : Fin 0 => 0) (fun i : Fin 0 => 2 * 0)
      largePrimeCounterexampleEvent ≤ C * Real.log 1 / Real.sqrt 1 := by
    rw [← hE]
    simpa using h
  rw [large_prime_counterexample_event_probability] at hzero
  norm_num at hzero

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
      (fun i p => primePoolLaw (Y i) (2 * Y i) p) α hmax hprob
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

private def primeTupleSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

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

private lemma roughPart_zero (w : ℕ) : roughPart w 0 = 1 := by
  simp [roughPart]

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
root-class tests and contribute `O(1/w)` (§3 lines 391–411). -/
theorem rough_coprimality_small_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (w L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) → w < L →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p, p.Prime ∧ w < p ∧ p ^ 2 ≤ L ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤ C / w := by
  sorry

/-- Large common rough prime divisors, `p>√L`, contribute `O(log L/√L)` by testing
the finitely many large prime factors of the polynomial with the smaller main endpoint
(§3 lines 413–432). -/
theorem rough_coprimality_large_prime_divisors {kF kG : ℕ}
    (F : IntegerPolynomial kF) (G : IntegerPolynomial kG)
    (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (YF : Fin kF → ℕ) (YG : Fin kG → ℕ) (L : ℕ),
      (∀ i, L ≤ YF i) → (∀ j, L ≤ YG j) →
      independentPrimePairProbability YF (fun i => 2 * YF i)
        YG (fun i => 2 * YG i)
        (fun x y =>
          evalIntegerPolynomial F (fun i => (x i : ℤ)) ≠ 0 ∧
          evalIntegerPolynomial G (fun i => (y i : ℤ)) ≠ 0 ∧
          ∃ p : ℕ, p.Prime ∧ Real.sqrt (L : ℝ) < (p : ℝ) ∧
            (p : ℤ) ∣ evalIntegerPolynomial F (fun i => (x i : ℤ)) ∧
            (p : ℤ) ∣ evalIntegerPolynomial G (fun i => (y i : ℤ))) ≤
        C * Real.log L / Real.sqrt L := by
  sorry

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
  sorry

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
