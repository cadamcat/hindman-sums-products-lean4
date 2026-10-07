import HindmanSumsProducts.Correlation.Defs
import HindmanSumsProducts.Correlation.Outside

/-! Helper lemmas for the uniform correlation test proof (lane `c-test2`). -/

namespace HindmanSumsProducts

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

private theorem c_test2_chainCoefficientData_eventually {K s m : ℕ}
    {Aset : Finset ℚ} {Dm : Finset (IntegerPolynomial s)}
    (S : FromArithmetic.MasterScales K Aset s Dm) (C : MasterChain K m)
    (a : Fin m → ℚ) (ha : ∀ d, a d ∈ Aset) :
    ∀ᶠ N in atTop, ∃ c : Fin m → ℤ,
      (∀ d, (c d : ℚ) = chainScale S.core.parameters C a N d) ∧
      (∀ d, 0 < c d) ∧
      (∀ u d, u < d → ∃ k : ℕ,
        c u = (primorial (N + 1) : ℤ) * (k : ℤ) * c d) ∧
      ∀ d,
        ((primorial (N + 1) ^ (S.primeStage.e0 N + 1) : ℕ) : ℤ) * c d ∣
          (S.core.parameters.M N : ℤ) := by
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

private theorem c_test2_masterSize_le_pivotGap_eventually {K s m : ℕ}
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

private theorem c_test2_previous_le_gap_eventually {n : ℕ}
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

private theorem c_test2_pivot_cutoff_le_previous {n m : ℕ}
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

end HindmanSumsProducts
