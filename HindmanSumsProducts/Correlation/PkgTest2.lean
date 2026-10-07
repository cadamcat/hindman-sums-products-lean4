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

end HindmanSumsProducts
