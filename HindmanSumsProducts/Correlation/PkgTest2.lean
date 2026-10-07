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
