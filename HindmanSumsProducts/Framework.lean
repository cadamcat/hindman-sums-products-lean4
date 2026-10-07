import OAI.Combinatorics.SumProduct.Alignment.RawMenu
import HindmanSumsProducts.Framework.Order
import HindmanSumsProducts.ChainSelection

/-!
# Framework: two principles and their combinatorial deduction

Definitions in this file follow §2 of `02_framework.tex`. Its asymptotic index is `N`, so the
paper's `w` is `N + 1`, and OAI's admissible parameter and model objects are reused literally.
-/

namespace HindmanSumsProducts

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- A block is OAI's pivot together with its nonempty earlier tail. -/
abbrev FrameworkBlock (n : ℕ) := OAI.SourceBlocks.Block n

/-- The paper's added-block relation `𝓔_B` (equation `eq:adding-blocks`). -/
def E_B {n : ℕ} (B : FrameworkBlock n) : Set (Finset (Fin n)) :=
  {A | OAI.SourceBlocks.Added B.1 B.2.val A}

/-- The product over a block's tail coordinates. -/
def tailValue {n : ℕ} (B : FrameworkBlock n) (t : Fin n → ℕ) : ℕ :=
  ∏ j ∈ B.2.val, t j

/-- An ordered list of OAI blocks is a chain precisely when its tails and pivots satisfy the
ordering condition `eq:block-chain`; this is the same predicate as `IsChain` in
`ChainSelection.lean`. -/
def IsBlockChain {n m : ℕ} (B : Fin m → FrameworkBlock n) : Prop :=
  IsChain (fun d => (B d).2.val) (fun d => (B d).1)

/-- Finite type of OAI block chains of a fixed length and ambient dimension. -/
abbrev BlockChains (n m : ℕ) := {B : Fin m → FrameworkBlock n // IsBlockChain B}

/-- The block-chain subtype is finite because its ambient list type is finite. -/
noncomputable instance blockChainsFintype (n m : ℕ) : Fintype (BlockChains n m) :=
  Fintype.ofFinite _

/-- A finite rational scale list viewed as a finite subtype. -/
noncomputable instance scaleListSubtypeFintype (vs : Finset ℚ) :
    Fintype {a : ℚ // a ∈ vs} := Fintype.ofFinite _

/-- The calibration triples `(B,a,c)` for fixed finite data. -/
abbrev CalibrationIndex (n r : ℕ) (vs : Finset ℚ) :=
  FrameworkBlock n × {a : ℚ // a ∈ vs} × Fin r

/-- Earlier blocks of a chain lie in the later block's added-block family; this is the
combinatorial reason for the tail-then-pivot ordering in `eq:block-chain`. -/
theorem earlier_chain_block_mem_E {n m : ℕ} (B : Fin m → FrameworkBlock n)
    (hB : IsBlockChain B) {k d : Fin m} (hkd : k < d) :
    OAI.SourceBlocks.Added (B d).1 (B d).2.val (B k).set := by
  rcases hB with ⟨htail, htails, htailPivot, hpivots⟩
  refine ⟨(B k).2.val, (B k).1, htail k, ?_, ?_, hpivots hkd, rfl⟩
  · intro p hp t ht
    exact htails k d hkd p hp t ht
  · intro t ht
    exact htailPivot d k t ht

theorem chain_block_set_injective {n m : ℕ} (B : Fin m → FrameworkBlock n)
    (hB : IsBlockChain B) : Function.Injective (fun d => (B d).set) := by
  intro i j hij
  change (B i).set = (B j).set at hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · have hmem : (B j).1 ∈ (B i).set := by
      change (B j).1 ∈ (B i).set
      rw [hij]
      simp [OAI.SourceBlocks.Block.set]
    have hle : (B j).1 ≤ (B i).1 := by
      simp only [OAI.SourceBlocks.Block.set, Finset.mem_insert] at hmem
      rcases hmem with hEq | hTail
      · exact hEq.le
      · exact (B i).2.property.2 _ hTail |>.le
    rcases hB with ⟨_, _, _, hpivots⟩
    exact (not_lt_of_ge hle) (hpivots hij')
  · have hmem : (B i).1 ∈ (B j).set := by
      change (B i).1 ∈ (B j).set
      rw [← hij]
      simp [OAI.SourceBlocks.Block.set]
    have hle : (B i).1 ≤ (B j).1 := by
      simp only [OAI.SourceBlocks.Block.set, Finset.mem_insert] at hmem
      rcases hmem with hEq | hTail
      · exact hEq.le
      · exact (B j).2.property.2 _ hTail |>.le
    rcases hB with ⟨_, _, _, hpivots⟩
    exact (not_lt_of_ge hle) (hpivots hji')

theorem tailValue_mul_pivot_eq_blockProduct {n : ℕ} (B : FrameworkBlock n)
    (t : Fin n → ℕ) :
    tailValue B t * t B.1 = ∏ j ∈ B.set, t j := by
  classical
  have hpivot : B.1 ∉ B.2.val := by
    intro hp
    exact (lt_irrefl _ (B.2.property.2 B.1 hp))
  change (∏ j ∈ B.2.val, t j) * t B.1 =
    ∏ j ∈ insert B.1 B.2.val, t j
  rw [Finset.prod_insert hpivot]
  ring

theorem sampledBlockHeight_eq {n : ℕ} (B : FrameworkBlock n) (t : Fin n → ℕ) :
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (fun j => (t j : ℤ)) B.set : ℚ) =
      ((tailValue B t * t B.1 : ℕ) : ℚ) := by
  have hpivot : B.1 ∉ B.2.val := by
    intro hp
    exact (lt_irrefl _ (B.2.property.2 B.1 hp))
  simp [OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height,
    OAI.SourceBlocks.Block.set, tailValue, hpivot, Finset.prod_insert, mul_comm]

/-- Repackage the tails and pivots returned by `chain_selection` as OAI blocks. -/
theorem blocksOfChainSelection {n m : ℕ} (T : Fin m → Finset (Fin n))
    (piv : Fin m → Fin n) (hT : IsChain T piv) :
    ∃ B : Fin m → FrameworkBlock n, IsBlockChain B ∧
      ∀ d, (B d).set = insert (piv d) (T d) := by
  refine ⟨fun d => ⟨piv d, ⟨T d, hT.1 d, ?_⟩⟩, ?_, fun d => rfl⟩
  · intro j hj
    exact hT.2.2.1 d d j hj
  · exact hT

/-- The rational scale vectors reused from OpenAI's word plan. -/
abbrev FrameworkScale (n : ℕ) := OAI.ConstructedWordPlan.GlobalWordPlan.Scale n

/-- The count triples `(b,𝐁,c)` for fixed finite data. -/
abbrev PredictionCountIndex (n m r : ℕ) (bs : Finset (FrameworkScale n)) :=
  {b : FrameworkScale n // b ∈ bs} × BlockChains n m × Fin r

/-- The value of a scale vector on a block, using OpenAI's `blockProduct`. -/
def blockScale {n : ℕ} (b : FrameworkScale n) (B : FrameworkBlock n) : ℚ :=
  OAI.ConstructedWordPlan.AlignmentScales.blockProduct b B.set

/-- The paper's scale-list closure condition `eq:scale-list-closure`. -/
def ScaleListsClosed {n : ℕ} (bs : Finset (FrameworkScale n)) (vs : Finset ℚ) : Prop :=
  ∀ b ∈ bs, ∀ B : FrameworkBlock n, blockScale b B ∈ vs

/-- The total law sequence: where the paper's interval lower bound holds this is exactly
`A.law N hX`; before that (a finite initial segment) it is the zero measure. -/
def frameworkLaw {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    Measure (Fin n → ℕ) :=
  if hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i then A.law N hX else 0

/-- On every index where OAI's interval hypothesis is available, the total law is exactly
`Parameters.law`; the proof argument is irrelevant by proof irrelevance. -/
theorem frameworkLaw_eq {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i) :
    frameworkLaw A N = A.law N hX := by
  simp [frameworkLaw, hX]

theorem eventually_denominator_dvd_primorial_pow (d : ℕ) (hd : 0 < d) :
    ∀ᶠ N in Filter.atTop, d ∣ primorial (N + 1) ^ (N + 1) := by
  filter_upwards [Filter.eventually_ge_atTop d] with N hN
  by_cases hd1 : d = 1
  · simp [hd1]
  · have hN' : d ≤ N + 1 := by omega
    apply (Nat.factorization_prime_le_iff_dvd (Nat.ne_of_gt hd)
      (pow_ne_zero _ (primorial_pos (N + 1)).ne')).mp
    intro p hp
    by_cases hpd : p ∣ d
    · have hpow : d ≤ p ^ (N + 1) := by
        exact hN'.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
      have hfac : d.factorization p ≤ N + 1 := Nat.factorization_le_of_le_pow hpow
      have hpW : p ∣ primorial (N + 1) :=
        hp.dvd_primorial_iff.mpr ((Nat.le_of_dvd hd hpd).trans hN')
      have hfacW : (primorial (N + 1)).factorization p = 1 :=
        Nat.factorization_eq_one_of_squarefree (squarefree_primorial _) hp hpW
      calc
        d.factorization p ≤ N + 1 := hfac
        _ = (primorial (N + 1) ^ (N + 1)).factorization p := by
          rw [Nat.factorization_pow]
          simp [hfacW]
    · rw [Nat.factorization_eq_zero_of_not_dvd hpd]
      exact Nat.zero_le _

theorem eventually_height_scale_integer {n : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (b : FrameworkScale n) (hb : ∀ i, 0 < b i) :
    ∀ᶠ N in Filter.atTop, ∀ i, ∃ x : ℕ, 0 < x ∧
      (A.ht N i : ℚ) * b i = x := by
  have heach (i : Fin n) : ∀ᶠ N in Filter.atTop,
      ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x := by
    have hden : ∀ᶠ N in Filter.atTop,
        (b i).den ∣ primorial (N + 1) ^ (N + 1) :=
      eventually_denominator_dvd_primorial_pow (b i).den (Rat.den_pos (b i))
    filter_upwards [hden] with N hden
    have hdenInt : ((b i).den : ℤ) ∣ A.ht N i := by
      have hdenPow : ((b i).den : ℤ) ∣ (primorial (N + 1) : ℤ) ^ (N + 1) := by
        exact_mod_cast hden
      exact hdenPow.trans (A.htdiv N i)
    obtain ⟨k, hk⟩ := hdenInt
    have hdivInt : ((b i).den : ℤ) ∣ (b i).num * A.ht N i := by
      rw [hk]
      refine ⟨(b i).num * k, ?_⟩
      ring
    have hdivNatCast : ((b i).den : ℤ) ∣
        (((b i).num * A.ht N i).natAbs : ℤ) := Int.dvd_natAbs.mpr hdivInt
    have hdivNat : (b i).den ∣ ((b i).num * A.ht N i).natAbs :=
      Int.natCast_dvd_natCast.mp hdivNatCast
    let q : ℚ := b i * (A.ht N i : ℚ)
    have hgcd : Nat.gcd ((b i).num * A.ht N i).natAbs (b i).den = (b i).den :=
      Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdivNat dvd_rfl)
    have hdenq : q.den = 1 := by
      dsimp [q]
      rw [Rat.mul_den]
      simp only [Rat.den_intCast, Rat.num_intCast, Nat.mul_one]
      rw [hgcd]
      exact Nat.div_self (Rat.den_pos (b i))
    have hqcast : (q.num : ℚ) = q := Rat.den_eq_one_iff q |>.mp hdenq
    let y : ℤ := q.num
    have hrat : (A.ht N i : ℚ) * b i = (y : ℚ) := by
      dsimp [y]
      calc
        (A.ht N i : ℚ) * b i = b i * (A.ht N i : ℚ) := mul_comm _ _
        _ = q := rfl
        _ = (q.num : ℚ) := hqcast.symm
    have hy : 0 < y := by
      have hprod : (0 : ℚ) < (A.ht N i : ℚ) * b i :=
        mul_pos (by exact_mod_cast A.htpos N i) (hb i)
      exact_mod_cast (hrat ▸ hprod)
    have hyIntCast : ((Int.toNat y : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy.le
    refine ⟨Int.toNat y, ?_, ?_⟩
    · have hpos : (0 : ℤ) < (Int.toNat y : ℤ) := by simpa [hyIntCast] using hy
      exact_mod_cast hpos
    · have hcast : (Int.toNat y : ℚ) = (y : ℚ) := by exact_mod_cast hyIntCast
      rw [hcast]
      exact hrat
  have hall : ∀ᶠ N in Filter.atTop, ∀ i : Fin n, i ∈ Finset.univ →
      ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x := by
    apply (eventually_all_finset (Finset.univ : Finset (Fin n))).2
    intro i hi
    exact heach i
  filter_upwards [hall] with N hN
  intro i
  exact hN i (Finset.mem_univ i)

theorem Parameters.eventually_X_dominates_earlier_square {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (i : Fin n) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ N in Filter.atTop,
      C * (A.M N : ℝ) * (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 <
        (A.X N i : ℝ) := by
  let S : ℕ → ℝ := fun N =>
    OAI.AdmissibleMicrocellBoundary.earlierScale A.M
      (fun N => OAI.SourceAdmissible.previous (A.X N) i) N
  have hHlim : Tendsto (fun N => (A.H N i : ℝ) / (S N)^4) Filter.atTop Filter.atTop := by
    have h := A.Hdom i 4 (by norm_num)
    simpa [S] using h
  have hXlim : Tendsto (fun N => Real.log (A.X N i : ℝ) / (A.H N i : ℝ))
      Filter.atTop Filter.atTop := by
    have h := A.Xdom i 1 (by norm_num)
    simpa using h
  have hH : ∀ᶠ N in Filter.atTop, C + 1 < (A.H N i : ℝ) / (S N)^4 :=
    hHlim.eventually_gt_atTop (C + 1)
  have hX : ∀ᶠ N in Filter.atTop, 1 <
      Real.log (A.X N i : ℝ) / (A.H N i : ℝ) := hXlim.eventually_gt_atTop 1
  filter_upwards [hH, hX] with N hHN hXN
  have hMpos : (0 : ℝ) < A.M N := by exact_mod_cast A.Mpos N
  have hPpos : (0 : ℝ) ≤ OAI.SourceAdmissible.previous (A.X N) i := by positivity
  have hSge1 : (1 : ℝ) ≤ S N := by
    dsimp [S, OAI.AdmissibleMicrocellBoundary.earlierScale]
    linarith [hMpos.le, hPpos]
  have hSgeM : (A.M N : ℝ) ≤ S N := by
    dsimp [S, OAI.AdmissibleMicrocellBoundary.earlierScale]
    linarith [hPpos]
  have hSgeP : (OAI.SourceAdmissible.previous (A.X N) i : ℝ) ≤ S N := by
    dsimp [S, OAI.AdmissibleMicrocellBoundary.earlierScale]
    linarith [hMpos.le]
  have hMP : (A.M N : ℝ) *
      (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 ≤ (S N)^3 := by
    calc
      (A.M N : ℝ) *
          (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 ≤ (S N) * (S N)^2 := by
        gcongr
      _ = (S N)^3 := by ring
  have hS34 : (S N)^3 ≤ (S N)^4 := by
    calc
      (S N)^3 = (S N)^3 * 1 := by ring
      _ ≤ (S N)^3 * S N :=
        mul_le_mul_of_nonneg_left hSge1 (pow_nonneg (le_trans (by norm_num) hSge1) 3)
      _ = (S N)^4 := by ring
  have hS4pos : 0 < (S N)^4 := pow_pos (lt_of_lt_of_le zero_lt_one hSge1) _
  have hCS4H : C * (S N)^4 < A.H N i := by
    have hh := (lt_div_iff₀ hS4pos).mp hHN
    nlinarith
  have hHlog : (A.H N i : ℝ) < Real.log (A.X N i : ℝ) := by
    have hHpos : (0 : ℝ) < A.H N i := by exact_mod_cast A.Hpos N i
    have hh := (lt_div_iff₀ hHpos).mp hXN
    nlinarith
  have hlogX : Real.log (A.X N i : ℝ) ≤ (A.X N i : ℝ) :=
    Real.log_le_self (by exact_mod_cast (A.Xpos N i).le)
  have hTarget : C * (A.M N : ℝ) *
      (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 ≤ C * (S N)^4 := by
    calc
      C * (A.M N : ℝ) *
          (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 =
          C * ((A.M N : ℝ) *
            (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2) := by ring
      _ ≤ C * (S N)^3 := mul_le_mul_of_nonneg_left hMP hC.le
      _ ≤ C * (S N)^4 := mul_le_mul_of_nonneg_left hS34 hC.le
  exact lt_of_le_of_lt hTarget
    (lt_of_lt_of_le (lt_trans hCS4H hHlog) hlogX)

theorem eventually_chain_coefficient_order {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (b : FrameworkScale n)
    (hb : ∀ i, 0 < b i) (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B) :
    ∀ᶠ N in Filter.atTop, ∀ z : Fin m → ℕ,
      (∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2) →
      StrictMono (fun d =>
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) * (z d : ℚ)) := by
  classical
  let coeff (N : ℕ) (d : Fin m) : ℚ :=
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  have hblockScalePos (d : Fin m) : 0 < blockScale b (B d) := by
    unfold blockScale
    apply Finset.prod_pos
    intro j hj
    exact hb j
  have hpair (d e : Fin m) (hde : d < e) :
      ∀ᶠ N in Filter.atTop, ∀ z : Fin m → ℕ,
        (∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2) →
        coeff N d * (z d : ℚ) < coeff N e * (z e : ℚ) := by
    let i := (B e).1
    let C : ℝ := (blockScale b (B d) : ℝ) / (blockScale b (B e) : ℝ)
    have hC : 0 < C := by
      dsimp [C]
      exact div_pos (by exact_mod_cast hblockScalePos d) (by exact_mod_cast hblockScalePos e)
    have hGrowth := Parameters.eventually_X_dominates_earlier_square A i C hC
    filter_upwards [hGrowth] with N hGrowth z hz
    have hPivotOrder : (B d).1 < (B e).1 := by
      rcases hB with ⟨_, _, _, hpivots⟩
      exact hpivots hde
    have hPrev : (A.X N (B d).1 : ℝ) ≤
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ) := by
      have hPrevNat : A.X N (B d).1 ≤ OAI.SourceAdmissible.previous (A.X N) i := by
        unfold OAI.SourceAdmissible.previous
        exact Finset.single_le_prod (f := fun j => A.X N j)
          (fun j hj => Nat.one_le_iff_ne_zero.mpr (A.Xpos N j).ne')
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPivotOrder⟩)
      exact_mod_cast hPrevNat
    have hHeightPos (x : Fin m) :
        0 < OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B x).set := by
      unfold OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      exact Finset.prod_pos fun j hj => A.htpos N j
    have hHeightLe (x : Fin m) :
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B x).set : ℝ) ≤ A.M N := by
      exact_mod_cast A.block_bound N (B x)
    have hHeightGe (x : Fin m) :
        (1 : ℝ) ≤
          (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B x).set : ℝ) := by
      have hh : 1 ≤
          OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B x).set := by
        have hpos := hHeightPos x
        omega
      exact_mod_cast hh
    have hzLowerD : (A.X N (B d).1 : ℝ) ≤ (z d : ℝ) := by
      exact_mod_cast (hz d).1
    have hzUpperD : (z d : ℝ) ≤ (A.X N (B d).1 : ℝ)^2 := by
      exact_mod_cast (hz d).2.le
    have hzLowerE : (A.X N (B e).1 : ℝ) ≤ (z e : ℝ) := by
      exact_mod_cast (hz e).1
    have hCoeffCast (x : Fin m) :
        (coeff N x : ℝ) =
          (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B x).set : ℝ) * (blockScale b (B x) : ℝ) := by
      dsimp [coeff]
      norm_cast
    have hScaleD0 : (0 : ℝ) ≤ (blockScale b (B d) : ℝ) := by
      exact_mod_cast (hblockScalePos d).le
    have hScaleE0 : (0 : ℝ) ≤ (blockScale b (B e) : ℝ) := by
      exact_mod_cast (hblockScalePos e).le
    have hleft : (coeff N d : ℝ) * (z d : ℝ) ≤
        (A.M N : ℝ) * (blockScale b (B d) : ℝ) *
          (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 := by
      rw [hCoeffCast d]
      calc
        _ ≤ (A.M N : ℝ) * (blockScale b (B d) : ℝ) * (z d : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hHeightLe d)
              (by exact_mod_cast (hblockScalePos d).le))
            (by positivity)
        _ ≤ (A.M N : ℝ) * (blockScale b (B d) : ℝ) *
            (A.X N (B d).1 : ℝ)^2 :=
          mul_le_mul_of_nonneg_left hzUpperD (by positivity)
        _ ≤ (A.M N : ℝ) * (blockScale b (B d) : ℝ) *
            (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 := by
          gcongr
    have hright :
        (blockScale b (B e) : ℝ) * (A.X N (B e).1 : ℝ) ≤
          (coeff N e : ℝ) * (z e : ℝ) := by
      rw [hCoeffCast e]
      calc
        (blockScale b (B e) : ℝ) * (A.X N (B e).1 : ℝ) ≤
            (blockScale b (B e) : ℝ) * (z e : ℝ) :=
          mul_le_mul_of_nonneg_left hzLowerE hScaleE0
        _ ≤ (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B e).set : ℝ) * (blockScale b (B e) : ℝ) * (z e : ℝ) := by
          have hz0 : (0 : ℝ) ≤ (z e : ℝ) := by positivity
          have hmul0 : (0 : ℝ) ≤ (blockScale b (B e) : ℝ) * (z e : ℝ) :=
            mul_nonneg hScaleE0 hz0
          nlinarith [mul_le_mul_of_nonneg_right (hHeightGe e) hmul0]
    have hscale : (A.M N : ℝ) * (blockScale b (B d) : ℝ) *
        (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 <
          (blockScale b (B e) : ℝ) * (A.X N (B e).1 : ℝ) := by
      have hg := hGrowth
      dsimp [C, i] at hg
      have hEq : (A.M N : ℝ) * (blockScale b (B d) : ℝ) *
          (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2 =
        (blockScale b (B e) : ℝ) *
          ((blockScale b (B d) : ℝ) / (blockScale b (B e) : ℝ) *
            (A.M N : ℝ) *
            (OAI.SourceAdmissible.previous (A.X N) i : ℝ)^2) := by
        field_simp [ne_of_gt (by exact_mod_cast hblockScalePos e)] <;> ring
      calc
        _ = _ := hEq
        _ < _ := mul_lt_mul_of_pos_left hg (by exact_mod_cast hblockScalePos e)
    have hreal : (coeff N d : ℝ) * (z d : ℝ) <
        (coeff N e : ℝ) * (z e : ℝ) := lt_of_le_of_lt hleft (lt_of_lt_of_le hscale hright)
    exact_mod_cast hreal
  let pairs : Finset (Fin m × Fin m) :=
    Finset.univ.filter fun p => p.1 < p.2
  have hall : ∀ᶠ N in Filter.atTop, ∀ p ∈ pairs,
      ∀ z : Fin m → ℕ,
        (∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2) →
        coeff N p.1 * (z p.1 : ℚ) < coeff N p.2 * (z p.2 : ℚ) := by
    apply (eventually_all_finset pairs).2
    intro p hp
    exact hpair p.1 p.2 (Finset.mem_filter.mp hp).2
  filter_upwards [hall] with N hN z hz
  intro d e hde
  have hp : (d, e) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hde⟩
  exact hN (d, e) hp z hz

theorem chain_offset_eq_sumForm {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B) (t : Fin n → ℕ)
    (J : Finset (Fin m)) (hJ : J.Nonempty) :
    OAI.SourceBlocks.offset (A.ht N) b t (B (J.max' hJ))
        ((J.erase (J.max' hJ)).image fun k => (B k).set) =
      ∑ k ∈ J.erase (J.max' hJ),
        (((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B k).set : ℚ) * blockScale b (B k)) /
          ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B (J.max' hJ)).set : ℚ) * blockScale b (B (J.max' hJ)))) *
          (tailValue (B k) t * t (B k).1 : ℚ) := by
  classical
  let d := J.max' hJ
  have hinj := chain_block_set_injective B hB
  let f : Finset (Fin n) → ℚ := fun A' =>
      (((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) A' : ℚ) * OAI.ConstructedWordPlan.AlignmentScales.blockProduct b A') /
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) (B d).set : ℚ) * blockScale b (B d))) *
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (t j : ℤ)) A' : ℚ)
  unfold OAI.SourceBlocks.offset
  change (∑ A' ∈ (J.erase d).image (fun k => (B k).set), f A') = _
  rw [Finset.sum_image (s := J.erase d) (f := f)
    (g := fun k => (B k).set) hinj.injOn]
  apply Finset.sum_congr rfl
  intro k hk
  simp [f, blockScale, d, sampledBlockHeight_eq]

/-- The total law is either OAI's probability law or the zero measure. -/
noncomputable instance frameworkLawIsZeroOrProbabilityMeasure {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    MeasureTheory.IsZeroOrProbabilityMeasure (frameworkLaw A N) := by
  rw [MeasureTheory.isZeroOrProbabilityMeasure_iff]
  unfold frameworkLaw
  split_ifs with hX
  · haveI : MeasureTheory.IsProbabilityMeasure (A.law N hX) :=
      OAI.SourceMenuAlignment.law_probability A N hX
    exact Or.inr MeasureTheory.IsProbabilityMeasure.measure_univ
  · simp

/-- The total law is finite at the whole sample space. -/
theorem frameworkLaw_ne_top_univ {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) :
    frameworkLaw A N Set.univ ≠ ⊤ := by
  have hcases : frameworkLaw A N Set.univ = 0 ∨ frameworkLaw A N Set.univ = 1 :=
    (MeasureTheory.isZeroOrProbabilityMeasure_iff).mp inferInstance
  rcases hcases with hzero | hone
  · simpa [hzero]
  · simpa [hone]

/-- Divisor weight `ν_B(y) = E_{σ=t_T} σ 1_{σ|y}` (equation `eq:divisor-weight`). The integral
is against the raw tail marginal of OAI's product law; the integrand depends only on the tail. -/
def divisorWeightUnder {n : ℕ} (μ : Measure (Fin n → ℕ))
    (B : FrameworkBlock n) (y : ℤ) : ℝ :=
  ∫ t, if (tailValue B t : ℤ) ∣ y then (tailValue B t : ℝ) else 0 ∂μ

/-- Divisor weight under the canonical extension of the admissible law. -/
def divisorWeight {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : FrameworkBlock n) (y : ℤ) : ℝ :=
  divisorWeightUnder (frameworkLaw A N) B y

/-- A rational argument is a colour hit only when it is an actual positive-integer-domain
argument. This is the paper's extension-by-zero convention for colour indicators. -/
def rationalColorHit {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) : Prop :=
  ∃ x : ℕ, 0 < x ∧ (x : ℚ) = q ∧ χ x = c

/-- The real-valued indicator associated to `rationalColorHit`. -/
noncomputable def rationalColorIndicator {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) : ℝ := by
  classical
  exact if rationalColorHit χ c q then 1 else 0

/-- The sum form `L_J` from equation `eq:sum-forms`. The last index is the maximum of `J`. -/
def sumForm {m : ℕ} (c : Fin m → ℚ) (J : Finset (Fin m)) (hJ : J.Nonempty)
    (z : Fin m → ℕ) : ℚ :=
  ∑ k ∈ J, (c k / c (J.max' hJ)) * (z k : ℚ)

theorem blockCoefficient_mul_sumForm {m : ℕ} (coeff : Fin m → ℚ)
    (J : Finset (Fin m)) (hJ : J.Nonempty) (z : Fin m → ℕ)
    (hcoeff : coeff (J.max' hJ) ≠ 0) :
    coeff (J.max' hJ) * sumForm coeff J hJ z =
      ∑ k ∈ J, coeff k * (z k : ℚ) := by
  unfold sumForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp [hcoeff] <;> ring

theorem sumForm_eq_blockPivot_add_offset {n m : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (b : FrameworkScale n)
    (hb : ∀ i, 0 < b i) (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B)
    (t : Fin n → ℕ) (J : Finset (Fin m)) (hJ : J.Nonempty) :
    sumForm (fun d =>
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) J hJ
        (fun d => tailValue (B d) t * t (B d).1) =
      (tailValue (B (J.max' hJ)) t * t (B (J.max' hJ)).1 : ℚ) +
        OAI.SourceBlocks.offset (A.ht N) b t (B (J.max' hJ))
          ((J.erase (J.max' hJ)).image fun k => (B k).set) := by
  classical
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
  let d := J.max' hJ
  have hcoeffPos : 0 < coeff d := by
    have hheight : 0 < OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) (B d).set := by
      unfold OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      exact Finset.prod_pos fun j hj => A.htpos N j
    have hbpos : 0 < blockScale b (B d) := by
      unfold blockScale
      exact Finset.prod_pos fun j hj => hb j
    dsimp [coeff]
    exact mul_pos (by exact_mod_cast hheight) hbpos
  have hoffset := chain_offset_eq_sumForm A N b B hB t J hJ
  unfold sumForm
  rw [← Finset.add_sum_erase J
    (fun k => coeff k / coeff d * (z k : ℚ)) (Finset.max'_mem J hJ)]
  rw [div_self hcoeffPos.ne', hoffset]
  simp [z, d, coeff]

theorem blockCoefficient_mul_sample_eq_prod {n : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (b : FrameworkScale n)
    (B : FrameworkBlock n) (t x : Fin n → ℕ)
    (hbase : ∀ j, (A.ht N j : ℚ) * b j * (t j : ℚ) = (x j : ℚ)) :
    ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) B.set : ℚ) * blockScale b B) *
        ((tailValue B t * t B.1 : ℕ) : ℚ) =
      ((∏ j ∈ B.set, x j : ℕ) : ℚ) := by
  have hheight :
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) B.set : ℚ) = ∏ j ∈ B.set, (A.ht N j : ℚ) := by
    simp [OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height]
  have htail : ((tailValue B t * t B.1 : ℕ) : ℚ) =
      ∏ j ∈ B.set, (t j : ℚ) := by
    rw [tailValue_mul_pivot_eq_blockProduct]
    norm_cast
  have hbscale : blockScale b B = ∏ j ∈ B.set, b j := by
    rfl
  calc
    _ = (∏ j ∈ B.set, (A.ht N j : ℚ)) *
          (∏ j ∈ B.set, b j) * (∏ j ∈ B.set, (t j : ℚ)) := by
        rw [hheight, hbscale, htail]
    _ = (∏ j ∈ B.set, (A.ht N j : ℚ) * b j) *
          (∏ j ∈ B.set, (t j : ℚ)) := by
        rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ B.set, ((A.ht N j : ℚ) * b j * (t j : ℚ)) := by
        rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ B.set, (x j : ℚ) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hbase j]
    _ = ((∏ j ∈ B.set, x j : ℕ) : ℚ) := by
        rw [Nat.cast_prod]

/-- All nonempty subset product colour indicators, the product mask `U` of
`eq:product-mask`. -/
abbrev NonemptySubsets (m : ℕ) := {J : Finset (Fin m) // J.Nonempty}

theorem block_chain_selection_color_hits {n m r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r)
    (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) (x t : Fin n → ℕ)
    (hbase : ∀ j, (A.ht N j : ℚ) * b j * (t j : ℚ) = (x j : ℚ))
    (hxpos : ∀ j, 0 < x j) (hcolors : ∀ J : Finset (Fin m), J.Nonempty →
      χ (∏ d ∈ J, ∏ j ∈ (B d).set, x j) = colour) :
    ∀ J : NonemptySubsets m,
      rationalColorHit χ colour
        (∏ d ∈ J.val,
          ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (B d).set : ℚ) * blockScale b (B d)) *
            (tailValue (B d) t * t (B d).1 : ℚ)) := by
  intro J
  have hblockPos (d : Fin m) : 0 < ∏ j ∈ (B d).set, x j := by
    apply Finset.prod_pos
    intro j hj
    exact hxpos j
  have hprodPos : 0 < ∏ d ∈ J.val, ∏ j ∈ (B d).set, x j := by
    apply Finset.prod_pos
    intro d hd
    exact hblockPos d
  have hcast : ((∏ d ∈ J.val, ∏ j ∈ (B d).set, x j : ℕ) : ℚ) =
      ∏ d ∈ J.val,
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) *
          (tailValue (B d) t * t (B d).1 : ℚ) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro d hd
    simpa only [Nat.cast_mul] using
      (blockCoefficient_mul_sample_eq_prod A N b (B d) t x hbase).symm
  refine ⟨∏ d ∈ J.val, ∏ j ∈ (B d).set, x j, hprodPos, hcast, ?_⟩
  exact hcolors J.val J.property

/-- Subsets indexing the nonsingleton sum factors in `eq:weighted-count`. -/
abbrev NonsingletonSubsets (m : ℕ) := {J : Finset (Fin m) // 2 ≤ J.val.card}

/-- All nonempty subset product colour indicators, the product mask `U` of
`eq:product-mask`. -/
def productMask {m r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (coeff : Fin m → ℚ)
    (z : Fin m → ℕ) : ℝ :=
  ∏ J : NonemptySubsets m,
    rationalColorIndicator χ c (∏ k ∈ J.val, coeff k * (z k : ℚ))

/-- A rational argument to a divisor weight is extended by zero off the integer lattice. -/
noncomputable def rationalDivisorWeightUnder {n : ℕ} (μ : Measure (Fin n → ℕ))
    (B : FrameworkBlock n) (q : ℚ) : ℝ := by
  classical
  exact if hq : ∃ y : ℤ, (y : ℚ) = q then
    divisorWeightUnder μ B (Classical.choose hq) else 0

/-- Rational divisor weight under the canonical law, extended by zero off integers. -/
noncomputable def rationalDivisorWeight {n : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : FrameworkBlock n) (q : ℚ) : ℝ :=
  rationalDivisorWeightUnder (frameworkLaw A N) B q

theorem rationalColorIndicator_nonneg {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) :
    0 ≤ rationalColorIndicator χ c q := by
  classical
  unfold rationalColorIndicator
  split_ifs <;> norm_num

theorem rationalColorIndicator_hit_of_pos {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ)
    (h : 0 < rationalColorIndicator χ c q) : rationalColorHit χ c q := by
  by_contra hn
  have hz : rationalColorIndicator χ c q = 0 := by
    simp [rationalColorIndicator, hn]
  linarith

theorem productMask_nonneg {m r : ℕ} (χ : ℕ → Fin r) (c : Fin r)
    (coeff : Fin m → ℚ) (z : Fin m → ℕ) : 0 ≤ productMask χ c coeff z := by
  unfold productMask
  exact Finset.prod_nonneg fun J hJ =>
    rationalColorIndicator_nonneg χ c (∏ k ∈ J.val, coeff k * (z k : ℚ))

theorem divisorWeightUnder_nonneg {n : ℕ} (μ : Measure (Fin n → ℕ))
    (B : FrameworkBlock n) (y : ℤ) : 0 ≤ divisorWeightUnder μ B y := by
  unfold divisorWeightUnder
  apply integral_nonneg
  intro t
  change (0 : ℝ) ≤ (if (tailValue B t : ℤ) ∣ y then (tailValue B t : ℝ) else 0)
  split_ifs <;> positivity

theorem rationalDivisorWeightUnder_nonneg {n : ℕ} (μ : Measure (Fin n → ℕ))
    (B : FrameworkBlock n) (q : ℚ) : 0 ≤ rationalDivisorWeightUnder μ B q := by
  classical
  unfold rationalDivisorWeightUnder
  split_ifs with h
  · exact divisorWeightUnder_nonneg μ B _
  · exact le_rfl

/-- Evaluate a piecewise model at a rational argument, extending by zero away from integers. -/
noncomputable def rationalModelValue {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (N : ℕ) (B : FrameworkBlock n)
    (v : ℚ) (c : Fin r) (q : ℚ) : ℝ := by
  classical
  exact if hq : ∃ k : ℤ, (k : ℚ) = q then
    S.model N B v c (Classical.choose hq)
  else 0

/-- Marginal law of the pivot coordinate of a block. -/
def pivotLaw {n m : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (B : Fin m → FrameworkBlock n) (d : Fin m) : Measure ℕ :=
  Measure.map (fun t : Fin n → ℕ => t (B d).1) (frameworkLaw A N)

/-- The integrand in `eq:weighted-count`, with the ambient law explicit. -/
def weightedCountIntegrandUnder {n m r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (μ : Measure (Fin n → ℕ)) (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r)
    (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) (z : Fin m → ℕ) : ℝ := by
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  exact productMask χ colour coeff z *
      (∏ d, rationalDivisorWeightUnder μ (B d) (z d : ℚ)) *
      (∏ J : NonsingletonSubsets m, by
        classical
        let hJ : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        let d := J.val.max' hJ
        exact rationalColorIndicator χ colour (coeff d * sumForm coeff J.val hJ z) *
          rationalDivisorWeightUnder μ (B d) (sumForm coeff J.val hJ z))

theorem weightedCountIntegrandUnder_nonneg {n m r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (μ : Measure (Fin n → ℕ)) (N : ℕ)
    (χ : ℕ → Fin r) (colour : Fin r) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) (z : Fin m → ℕ) :
    0 ≤ weightedCountIntegrandUnder A μ N χ colour b B z := by
  classical
  unfold weightedCountIntegrandUnder
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  have hmask := productMask_nonneg χ colour coeff z
  have hsingle : 0 ≤ ∏ d, rationalDivisorWeightUnder μ (B d) (z d : ℚ) :=
    Finset.prod_nonneg fun d hd => rationalDivisorWeightUnder_nonneg μ (B d) (z d : ℚ)
  have hsum : (0 : ℝ) ≤ ∏ J : NonsingletonSubsets m, by
      let hJ : J.val.Nonempty := by
        have hcard : 2 ≤ J.val.card := J.property
        exact Finset.card_pos.mp (by omega)
      let d := J.val.max' hJ
      exact rationalColorIndicator χ colour (coeff d * sumForm coeff J.val hJ z) *
        rationalDivisorWeightUnder μ (B d) (sumForm coeff J.val hJ z) :=
    Finset.prod_nonneg fun J hJ => by
      let hJn : J.val.Nonempty := by
        have hcard : 2 ≤ J.val.card := J.property
        exact Finset.card_pos.mp (by omega)
      let d := J.val.max' hJn
      exact mul_nonneg (rationalColorIndicator_nonneg χ colour _)
        (rationalDivisorWeightUnder_nonneg μ (B d) _)
  exact mul_nonneg (mul_nonneg hmask hsingle) hsum

/-- The same paper count with an explicit ambient law, as in the full Prediction Principle. -/
def weightedCountUnder {n m r : ℕ} (A : OAI.SourceAdmissible.Parameters n)
    (μ : Measure (Fin n → ℕ)) (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r)
    (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) : ℝ :=
  ∫ z, weightedCountIntegrandUnder A μ N χ colour b B z ∂ Measure.pi (fun d =>
    Measure.map (fun t : Fin n → ℕ => t (B d).1) μ)

/-- The weighted count `𝓘_{b,c,𝐁}` in equation `eq:weighted-count`. Independent divisor samples
are represented by separate factors of `divisorWeight`. -/
def weightedCount {n m r : ℕ} (A : OAI.SourceAdmissible.Parameters n) (N : ℕ)
    (χ : ℕ → Fin r) (colour : Fin r) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) : ℝ :=
  weightedCountUnder A (frameworkLaw A N) N χ colour b B

/-- The actual model integrand compared to the weighted count in
`eq:prediction-counting`, evaluated at `z(t)_d=t_{B_d}`. -/
def modelIntegrandMean {n m r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (N : ℕ) (χ : ℕ → Fin r)
    (colour : Fin r) (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) : ℝ :=
  ∫ t, by
    classical
    let coeff : Fin m → ℚ := fun d =>
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) (B d).set : ℚ) * blockScale b (B d)
    let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
    exact productMask χ colour coeff z *
      ∏ J : NonsingletonSubsets m, by
        have hJ : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        let d := J.val.max' hJ
        exact rationalModelValue S N (B d) (blockScale b (B d)) colour
          (sumForm coeff J.val hJ z)
  ∂ frameworkLaw A N

/-- The pointwise model integrand in `eq:prediction-counting`. -/
def modelIntegrand {n m r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (N : ℕ) (χ : ℕ → Fin r)
    (colour : Fin r) (b : FrameworkScale n) (B : Fin m → FrameworkBlock n)
    (t : Fin n → ℕ) : ℝ := by
  classical
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
  exact productMask χ colour coeff z *
    ∏ J : NonsingletonSubsets m, by
      have hJ : J.val.Nonempty := by
        have hcard : 2 ≤ J.val.card := J.property
        exact Finset.card_pos.mp (by omega)
      let d := J.val.max' hJ
      exact rationalModelValue S N (B d) (blockScale b (B d)) colour
        (sumForm coeff J.val hJ z)

/-- The model integrand mean under an explicit ambient law. -/
def modelIntegrandMeanUnder {n m r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (μ : Measure (Fin n → ℕ))
    (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) : ℝ :=
  ∫ t, modelIntegrand S N χ colour b B t ∂μ

theorem rationalColorIndicator_mem_Icc {r : ℕ} (χ : ℕ → Fin r) (c : Fin r) (q : ℚ) :
    rationalColorIndicator χ c q ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : rationalColorHit χ c q <;> simp [rationalColorIndicator, h]

theorem rationalModelValue_mem_Icc {n r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) {v : ℚ} (hv : v ∈ vs)
    (N : ℕ) (B : FrameworkBlock n) (c : Fin r) (q : ℚ) :
    rationalModelValue S N B v c q ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold rationalModelValue
  split_ifs with hq
  · rw [S.represents N B v hv c (Classical.choose hq)]
    exact (S.piece N B v hv c
      (Classical.choose hq / (A.H N B.1 : ℤ))
      (Classical.choose hq % (A.M N : ℤ))).range _
  · simp

theorem productMask_mem_Icc {m r : ℕ} (χ : ℕ → Fin r) (c : Fin r)
    (coeff : Fin m → ℚ) (z : Fin m → ℕ) :
    productMask χ c coeff z ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold productMask
    exact Finset.prod_nonneg fun J hJ =>
      (rationalColorIndicator_mem_Icc χ c
        (∏ k ∈ J.val, coeff k * (z k : ℚ))).1
  · unfold productMask
    exact Finset.prod_le_one₀
      (fun J hJ => (rationalColorIndicator_mem_Icc χ c
        (∏ k ∈ J.val, coeff k * (z k : ℚ))).1)
      (fun J hJ => (rationalColorIndicator_mem_Icc χ c
        (∏ k ∈ J.val, coeff k * (z k : ℚ))).2)

theorem modelIntegrand_mem_Icc {n m r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (bs : Finset (FrameworkScale n)) (hclosed : ScaleListsClosed bs vs)
    {b : FrameworkScale n} (hb : b ∈ bs) (N : ℕ) (χ : ℕ → Fin r)
    (colour : Fin r) (B : Fin m → FrameworkBlock n) (t : Fin n → ℕ) :
    modelIntegrand S N χ colour b B t ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold modelIntegrand
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
  have hmask := productMask_mem_Icc χ colour coeff z
  have hmodel (J : NonsingletonSubsets m) (hJ : J.val.Nonempty) :
      rationalModelValue S N (B (J.val.max' hJ)) (blockScale b (B (J.val.max' hJ))) colour
        (sumForm coeff J.val hJ z) ∈ Set.Icc (0 : ℝ) 1 := by
    let d := J.val.max' hJ
    have hv : blockScale b (B d) ∈ vs := hclosed b hb (B d)
    exact rationalModelValue_mem_Icc S hv N (B d) colour
      (sumForm coeff J.val hJ z)
  have hprod : (∏ J : NonsingletonSubsets m, by
      have hJ : J.val.Nonempty := by
        have hcard : 2 ≤ J.val.card := J.property
        exact Finset.card_pos.mp (by omega)
      let d := J.val.max' hJ
      exact rationalModelValue S N (B d) (blockScale b (B d)) colour
        (sumForm coeff J.val hJ z)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.prod_nonneg fun J hJ => by
        let hJn : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        exact (hmodel J hJn).1
    · exact Finset.prod_le_one₀ (fun J hJ => by
        let hJn : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        exact (hmodel J hJn).1) (fun J hJ => by
        let hJn : J.val.Nonempty := by
          have hcard : 2 ≤ J.val.card := J.property
          exact Finset.card_pos.mp (by omega)
        exact (hmodel J hJn).2)
  constructor
  · exact mul_nonneg hmask.1 hprod.1
  · calc
      productMask χ colour coeff z *
          (∏ J : NonsingletonSubsets m, by
            have hJ : J.val.Nonempty := by
              have hcard : 2 ≤ J.val.card := J.property
              exact Finset.card_pos.mp (by omega)
            let d := J.val.max' hJ
            exact rationalModelValue S N (B d) (blockScale b (B d)) colour
              (sumForm coeff J.val hJ z)) ≤ 1 *
          (∏ J : NonsingletonSubsets m, by
            have hJ : J.val.Nonempty := by
              have hcard : 2 ≤ J.val.card := J.property
              exact Finset.card_pos.mp (by omega)
            let d := J.val.max' hJ
            exact rationalModelValue S N (B d) (blockScale b (B d)) colour
              (sumForm coeff J.val hJ z)) :=
        mul_le_mul_of_nonneg_right hmask.2 hprod.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hprod.2 (by norm_num)
      _ = 1 := by norm_num

theorem modelIntegrand_integrable {n m r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (bs : Finset (FrameworkScale n)) (hclosed : ScaleListsClosed bs vs)
    {b : FrameworkScale n} (hb : b ∈ bs) (N : ℕ) (χ : ℕ → Fin r)
    (colour : Fin r) (B : Fin m → FrameworkBlock n) :
    Integrable (fun t => modelIntegrand S N χ colour b B t) (frameworkLaw A N) := by
  letI : IsFiniteMeasure (frameworkLaw A N) :=
    ⟨(lt_top_iff_ne_top).2 (frameworkLaw_ne_top_univ A N)⟩
  apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
  filter_upwards [] with t
  have h := modelIntegrand_mem_Icc S bs hclosed hb N χ colour B t
  exact abs_le.mpr ⟨by linarith [h.1], h.2⟩

/-- Calibration-failure event for one `(B,a,c)`: the centre colour is correct while the model is
at most `2τ`. -/
def calibrationFailureSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (B : FrameworkBlock n) (a : ℚ) (c : Fin r) (τ : ℝ) : Set (Fin n → ℕ) :=
  {t | rationalColorHit χ c
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (A.ht N) B.set : ℚ) * a *
        ((∏ j ∈ B.set, t j : ℕ) : ℚ)) ∧
    S.model N B a c
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (t j : ℤ)) B.set) ≤ 2 * τ}

/-- Calibration-failure probability under `A.law N _` (with the finite initial segment convention
of `frameworkLaw`). -/
def calibrationProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (B : FrameworkBlock n) (a : ℚ) (c : Fin r) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (calibrationFailureSet S χ N B a c τ)

/-- Calibration probability under an explicit member of the law sequence. -/
def calibrationProbabilityUnder {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (μ : Measure (Fin n → ℕ))
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (B : FrameworkBlock n) (a : ℚ) (c : Fin r) (τ : ℝ) : ℝ :=
  μ.real (calibrationFailureSet S χ N B a c τ)

/-- Calibration failure set at a finite triple `(B,a,c)`. -/
def calibrationFailureAt {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) (i : CalibrationIndex n r vs) : Set (Fin n → ℕ) :=
  calibrationFailureSet S χ N i.1 i.2.1 i.2.2 τ

/-- Union of the finitely many calibration-failure events. -/
def calibrationUnionSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) : Set (Fin n → ℕ) :=
  ⋃ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
    calibrationFailureAt S χ N τ i

/-- Probability that at least one calibration failure occurs. The index type is finite. -/
def calibrationUnionProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r) (N : ℕ)
    (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (calibrationUnionSet S χ N τ)

theorem aligned_model_integrand_positive_aux (m : ℕ) (_hm : 2 ≤ m) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (f : NonsingletonSubsets m → ℝ)
    (hf : ∀ J, τ < f J) :
    τ ^ (2 ^ m) ≤ ∏ J : NonsingletonSubsets m, f J := by
  have hcard : Fintype.card (NonsingletonSubsets m) ≤ 2 ^ m := by
    calc
      Fintype.card (NonsingletonSubsets m) ≤ Fintype.card (Finset (Fin m)) :=
        Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card (Fin m) := Fintype.card_finset
      _ = 2 ^ m := by simp
  have hprod : (∏ _J : NonsingletonSubsets m, τ) ≤ ∏ J : NonsingletonSubsets m, f J := by
    apply Finset.prod_le_prod₀
    · intro J hJ
      exact le_of_lt hτ0
    · intro J hJ
      exact le_of_lt (hf J)
  have hprod' : τ ^ Fintype.card (NonsingletonSubsets m) ≤
      ∏ J : NonsingletonSubsets m, f J := by
    convert hprod using 1
    all_goals simp [Finset.prod_const]
  exact (pow_le_pow_of_le_one (le_of_lt hτ0) hτ1 hcard).trans hprod'

theorem aligned_chain_modelIntegrand_lower {n m r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (bs : Finset (FrameworkScale n)) (hclosed : ScaleListsClosed bs vs)
    (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r) (b : FrameworkScale n)
    (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B) (t : Fin n → ℕ)
    (τ : ℝ) (hm : 2 ≤ m) (hb : b ∈ bs) (hbs : ∀ i, 0 < b i)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hAligned : OAI.SourceBlocks.aligned (S.model N) (A.ht N) b t τ)
    (hGood : t ∉ calibrationUnionSet S χ N τ)
    (hColors : ∀ J : NonemptySubsets m, rationalColorHit χ colour
      (∏ d ∈ J.val,
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) *
          ((∏ j ∈ (B d).set, t j : ℕ) : ℚ))) :
    τ ^ (2 ^ m) ≤ modelIntegrand S N χ colour b B t := by
  classical
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  let z : Fin m → ℕ := fun d => tailValue (B d) t * t (B d).1
  let modelVal : NonsingletonSubsets m → ℝ := fun J => by
    classical
    let hJ : J.val.Nonempty := by
      have hcard : 2 ≤ J.val.card := J.property
      exact Finset.card_pos.mp (by omega)
    let d := J.val.max' hJ
    exact rationalModelValue S N (B d) (blockScale b (B d)) colour
      (sumForm coeff J.val hJ z)
  have hMaskOne : productMask χ colour coeff z = 1 := by
    unfold productMask
    apply Finset.prod_eq_one
    intro J hJ
    have hhit : rationalColorHit χ colour
        (∏ k ∈ J.val, coeff k * (z k : ℚ)) := by
      simpa [coeff, z, tailValue_mul_pivot_eq_blockProduct] using hColors J
    simp [rationalColorIndicator, hhit]
  have hFactor (J : NonsingletonSubsets m) : τ < modelVal J := by
    let hJ : J.val.Nonempty := by
      have hcard : 2 ≤ J.val.card := J.property
      exact Finset.card_pos.mp (by omega)
    let d := J.val.max' hJ
    have hCenterHit : rationalColorHit χ colour (coeff d * (z d : ℚ)) := by
      simpa [coeff, z, tailValue_mul_pivot_eq_blockProduct] using
        hColors ⟨{d}, by simp⟩
    let index : CalibrationIndex n r vs :=
      ⟨B d, ⟨blockScale b (B d), hclosed b hb (B d)⟩, colour⟩
    have hNoFailure : t ∉ calibrationFailureSet S χ N (B d)
        (blockScale b (B d)) colour τ := by
      intro hfail
      apply hGood
      change t ∈ ⋃ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        calibrationFailureAt S χ N τ i
      refine Set.mem_iUnion.mpr ⟨index, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa [calibrationFailureAt, index] using hfail
    have hCenterModel : 2 * τ < S.model N (B d) (blockScale b (B d)) colour
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (fun j => (t j : ℤ)) (B d).set) := by
      by_contra hnot
      apply hNoFailure
      exact ⟨by
        simpa [coeff, z, tailValue_mul_pivot_eq_blockProduct] using hCenterHit,
        le_of_not_gt hnot⟩
    let D : Finset (Finset (Fin n)) :=
      (J.val.erase d).image fun k => (B k).set
    have hAdded : ∀ A' ∈ D,
        OAI.SourceBlocks.Added (B d).1 (B d).2.val A' := by
      intro A' hA'
      change A' ∈ (J.val.erase d).image (fun k => (B k).set) at hA'
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hA'
      have hkErase := Finset.mem_erase.mp hk
      have hkdle : k ≤ d := Finset.le_max' J.val k hkErase.2
      have hkd : k < d := lt_of_le_of_ne hkdle hkErase.1
      exact earlier_chain_block_mem_E B hB hkd
    obtain ⟨Δ, hΔ, hAlignedAt⟩ := hAligned (B d) D hAdded colour
    have hForm := sumForm_eq_blockPivot_add_offset A N b hbs B hB t J.val hJ
    have hBlockT :
        (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (fun j => (t j : ℤ)) (B d).set : ℚ) = (z d : ℚ) := by
      simpa [z] using sampledBlockHeight_eq (B d) t
    let k : ℤ :=
      OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (t j : ℤ)) (B d).set + Δ
    have hq : (k : ℚ) = sumForm coeff J.val hJ z := by
      dsimp [k]
      rw [Int.cast_add, hBlockT, hΔ]
      simpa [coeff, z] using hForm.symm
    let he : ∃ k' : ℤ, (k' : ℚ) = sumForm coeff J.val hJ z := ⟨k, hq⟩
    have hchoose : Classical.choose he = k := by
      exact Int.cast_injective ((Classical.choose_spec he).trans hq.symm)
    have hmodelEq : rationalModelValue S N (B d) (blockScale b (B d)) colour
        (sumForm coeff J.val hJ z) =
        S.model N (B d) (blockScale b (B d)) colour k := by
      unfold rationalModelValue
      rw [dif_pos he, hchoose]
    have hfactor : τ < rationalModelValue S N (B d) (blockScale b (B d)) colour
        (sumForm coeff J.val hJ z) := by
      rw [hmodelEq]
      exact hAlignedAt hCenterModel
    simpa [modelVal, hJ, d] using hfactor
  have hprodLower := aligned_model_integrand_positive_aux m hm hτ hτ1 modelVal hFactor
  calc
    τ ^ (2 ^ m) ≤ ∏ J : NonsingletonSubsets m, modelVal J := hprodLower
    _ = modelIntegrand S N χ colour b B t := by
      simp [modelIntegrand, modelVal, coeff, z, hMaskOne]

/-- Probability form of the union bound for the finite calibration family. -/
theorem calibration_failure_union_probability_le {n r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s} (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (χ : ℕ → Fin r) (N : ℕ) (τ : ℝ) :
    calibrationUnionProbability S χ N τ ≤
      ∑ i : CalibrationIndex n r vs,
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ := by
  classical
  unfold calibrationUnionProbability calibrationUnionSet
  calc
    (frameworkLaw A N).real (calibrationUnionSet S χ N τ) ≤
      ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        (frameworkLaw A N).real (calibrationFailureAt S χ N τ i) :=
      MeasureTheory.measureReal_biUnion_finset_le _ _
    _ = _ := by simp [calibrationFailureAt, calibrationProbability]

/-- The alignment event from OpenAI's model event predicate. -/
def alignmentEventSet {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (bs : Finset (FrameworkScale n))
    (N : ℕ) (τ : ℝ) : Set (Fin n → ℕ) :=
  OAI.SourceMenuAlignment.event bs (S.model N) (A.ht N) τ

/-- OAI alignment-event probability, evaluated using the total law sequence. -/
def alignmentProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (bs : Finset (FrameworkScale n))
    (N : ℕ) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real (alignmentEventSet S bs N τ)

/-- Mass of samples that align and avoid every calibration failure. -/
def goodAlignmentProbability {n r s : ℕ} {A : OAI.SourceAdmissible.Parameters n}
    {vs : Finset ℚ} {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F) (χ : ℕ → Fin r)
    (bs : Finset (FrameworkScale n)) (N : ℕ) (τ : ℝ) : ℝ :=
  (frameworkLaw A N).real
    (alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ)

theorem goodSample_modelIntegrand_sum_lower {n m r s : ℕ}
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s}
    (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (bs : Finset (FrameworkScale n)) (hclosed : ScaleListsClosed bs vs)
    (hbs : ∀ b ∈ bs, ∀ i, 0 < b i)
    (hselect : ∀ (χ : ℕ → Fin r) (x : Fin n → ℕ),
      ∃ T piv colour, IsChain T piv ∧
        ∀ J : Finset (Fin m), J.Nonempty →
          χ (∏ d ∈ J, ∏ j ∈ insert (piv d) (T d), x j) = colour)
    (N : ℕ) (χ : ℕ → Fin r) (hm : 2 ≤ m) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hbase : ∀ b ∈ bs, ∀ i, ∃ u : ℕ, 0 < u ∧ (A.ht N i : ℚ) * b i = u)
    (t : Fin n → ℕ)
    (hDomain : t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) )
    (hGood : t ∈ alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ) :
    τ ^ (2 ^ m) ≤
      ∑ i : PredictionCountIndex n m r bs,
        modelIntegrand S N χ i.2.2 i.1.val i.2.1.val t := by
  classical
  obtain ⟨b, hb, hAligned⟩ := hGood.1
  let base : Fin n → ℕ := fun i => Classical.choose (hbase b hb i)
  have hbasePos (i : Fin n) : 0 < base i := by
    simpa [base] using (Classical.choose_spec (hbase b hb i)).1
  have hbaseEq (i : Fin n) : (A.ht N i : ℚ) * b i = base i := by
    simpa [base] using (Classical.choose_spec (hbase b hb i)).2
  let x : Fin n → ℕ := fun i => base i * t i
  have htPos (i : Fin n) : 0 < t i := by
    have hunit : t i ∈
        OAI.RawHarmonicProbability.units (A.X N i) (primorial (N + 1)) :=
      (Fintype.mem_piFinset.mp hDomain) i
    have hIco : t i ∈ Finset.Ico (A.X N i) ((A.X N i)^2) := by
      simpa [OAI.RawHarmonicProbability.units] using (Finset.mem_filter.mp hunit).1
    exact lt_of_lt_of_le (A.Xpos N i) (Finset.mem_Ico.mp hIco).1
  have hxpos : ∀ i, 0 < x i := by
    intro i
    exact Nat.mul_pos (hbasePos i) (htPos i)
  have hbaseFull : ∀ i, (A.ht N i : ℚ) * b i * (t i : ℚ) = (x i : ℚ) := by
    intro i
    dsimp [x]
    rw [hbaseEq i]
    push_cast
    ring
  obtain ⟨T, piv, colour, hT, hcolors⟩ := hselect χ x
  obtain ⟨B, hB, hBset⟩ := blocksOfChainSelection T piv hT
  have hcolorsB : ∀ J : Finset (Fin m), J.Nonempty →
      χ (∏ d ∈ J, ∏ j ∈ (B d).set, x j) = colour := by
    intro J hJ
    simpa [hBset] using hcolors J hJ
  have hColorHits := block_chain_selection_color_hits A N χ colour b B x t
    hbaseFull hxpos hcolorsB
  have hColorHitsFull : ∀ J : NonemptySubsets m, rationalColorHit χ colour
      (∏ d ∈ J.val,
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) *
          ((∏ j ∈ (B d).set, t j : ℕ) : ℚ)) := by
    intro J
    simpa only [← Nat.cast_mul, tailValue_mul_pivot_eq_blockProduct, Nat.cast_prod]
      using hColorHits J
  have hNoCal : t ∉ calibrationUnionSet S χ N τ := by simpa using hGood.2
  have hmodelLower := aligned_chain_modelIntegrand_lower S bs hclosed N χ colour b B hB t
    τ hm hb (hbs b hb) hτ hτ1 hAligned hNoCal hColorHitsFull
  let g : PredictionCountIndex n m r bs → ℝ := fun i =>
    modelIntegrand S N χ i.2.2 i.1.val i.2.1.val t
  have hgnonneg (i : PredictionCountIndex n m r bs) : 0 ≤ g i := by
    have h := modelIntegrand_mem_Icc S bs hclosed i.1.property N χ i.2.2 i.2.1.val t
    exact h.1
  let selected : PredictionCountIndex n m r bs :=
    ⟨⟨b, hb⟩, ⟨⟨B, hB⟩, colour⟩⟩
  have hselected : τ ^ (2 ^ m) ≤ g selected := by
    simpa [g, selected] using hmodelLower
  have hsum : g selected ≤ ∑ i : PredictionCountIndex n m r bs, g i :=
    Finset.single_le_sum (fun i hi => hgnonneg i) (Finset.mem_univ selected)
  exact hselected.trans hsum

/-- Upper-bound notation for a limit along an ultrafilter. The sequences here are bounded
probabilities (or absolute differences of two `[0,1]` expectations), so this is equivalent to the
paper's `lim_U f ≤ bound`. -/
def UltrafilterLimLE (U : Ultrafilter ℕ) (f : ℕ → ℝ) (bound : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ N in (U : Filter ℕ), f N < bound + ε

/-- A pointwise smaller sequence has the same ultrafilter upper bound. -/
theorem UltrafilterLimLE.mono {U : Ultrafilter ℕ} {f g : ℕ → ℝ} {bound : ℝ}
    (hfg : ∀ N, f N ≤ g N) (hg : UltrafilterLimLE U g bound) :
    UltrafilterLimLE U f bound := by
  intro ε hε
  filter_upwards [hg ε hε] with N hN
  exact lt_of_le_of_lt (hfg N) hN

/-- Increasing the comparison bound preserves `UltrafilterLimLE`. -/
theorem UltrafilterLimLE.bound_mono {U : Ultrafilter ℕ} {f : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : UltrafilterLimLE U f a) : UltrafilterLimLE U f b := by
  intro ε hε
  filter_upwards [hf ε hε] with N hN
  exact lt_of_lt_of_le hN (by linarith)

/-- Extract eventual lower bounds from an ordinary lower limit for a sequence in `[0,1]`. -/
theorem liminf_bound_eventually {f : ℕ → ℝ} {δ : ℝ}
    (hf0 : ∀ N, 0 ≤ f N) (hf1 : ∀ N, f N ≤ 1)
    (hδ : δ ≤ Filter.liminf f Filter.atTop) :
    ∀ ε, 0 < ε → ∀ᶠ N in Filter.atTop, δ - ε < f N := by
  have hCob : Filter.IsCoboundedUnder (fun x y : ℝ => y ≤ x) Filter.atTop f :=
    Filter.IsCoboundedUnder.of_frequently_le
      (Filter.Frequently.of_forall fun N => hf1 N)
  have hBdd : Filter.IsBoundedUnder (fun x y : ℝ => y ≤ x) Filter.atTop f :=
    Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hf0)
  intro ε hε
  exact (Filter.le_liminf_iff (h₁ := hCob) (h₂ := hBdd)).mp hδ
    (δ - ε) (by linarith)

/-- For a finite measure, removing a bad event reduces event mass by at most the bad-event mass. -/
theorem measureReal_inter_compl_ge {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (hμ : μ Set.univ ≠ ⊤) (s t : Set α) :
    μ.real (s ∩ tᶜ) ≥ μ.real s - μ.real t := by
  have hsub : s ⊆ (s ∩ tᶜ) ∪ t := by
    intro x hx
    by_cases hxt : x ∈ t
    · exact Or.inr hxt
    · exact Or.inl ⟨hx, hxt⟩
  have hnot : μ ((s ∩ tᶜ) ∪ t) ≠ ⊤ := by
    intro hs
    have hle : μ ((s ∩ tᶜ) ∪ t) ≤ μ Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ ((s ∩ tᶜ) ∪ t))
    rw [hs] at hle
    exact hμ (top_unique hle)
  have hmono := MeasureTheory.measureReal_mono hsub hnot
  have hunion := MeasureTheory.measureReal_union_le (μ := μ) (s ∩ tᶜ) t
  linarith [hmono, hunion]

/-- The Prediction Principle `pr:prediction`, in OAI's admissible-parameter and charted-menu
vocabulary. The quantifier order makes `s` depend only on `m`. `U` may be any nonprincipal
ultrafilter; lists and tolerances are fixed before the parameters and models are supplied. -/
def PredictionPrinciple : Prop :=
  ∀ m, 2 ≤ m → ∃ s, ∀ (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ Filter.cofinite →
  ∀ n r (χ : ℕ → Fin r) (bs : Finset (FrameworkScale n)) (vs : Finset ℚ),
    (∀ b ∈ bs, ∀ j, 0 < b j) → (∀ v ∈ vs, 0 < v) → ScaleListsClosed bs vs →
    ∀ τ η : ℝ, 0 < τ → τ < 1/4 → 0 < η →
    ∃ (A : OAI.SourceAdmissible.Parameters n) (F : OAI.SourceChartedMenu.Menu s)
      (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F),
      ∀ (μ : ℕ → Measure (Fin n → ℕ)),
        (∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i), μ N = A.law N hX) →
        (∀ B : FrameworkBlock n, ∀ a : ℚ, a ∈ vs → ∀ c : Fin r,
          ∀ ε : ℝ, 0 < ε →
            ∀ᶠ N in (U : Filter ℕ),
              calibrationProbabilityUnder (μ N) S χ N B a c τ ≤ 3*τ+η+ε) ∧
        (∀ (B : Fin m → FrameworkBlock n), IsBlockChain B →
          ∀ b : FrameworkScale n, b ∈ bs → ∀ c : Fin r,
            ∀ ε : ℝ, 0 < ε →
              ∀ᶠ N in (U : Filter ℕ),
                |weightedCountUnder A (μ N) N χ c b B -
                    modelIntegrandMeanUnder S (μ N) N χ c b B| ≤ η+ε)

/-- Alignment Principle `pr:alignment`, using OpenAI's charted-menu theorem directly. -/
theorem alignment_principle (n r s : ℕ) :
    ∃ (bs : Finset (FrameworkScale n)) (vs : Finset ℚ) (δ : ℝ),
      0 < δ ∧
      (∀ b ∈ bs, ∀ j, 0 < b j) ∧ (∀ v ∈ vs, 0 < v) ∧ ScaleListsClosed bs vs ∧
      ∀ (A : OAI.SourceAdmissible.Parameters n) (F : OAI.SourceChartedMenu.Menu s)
        (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
        (μ : ℕ → Measure (Fin n → ℕ)),
        (∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i), μ N = A.law N hX) →
        ∀ τ : ℝ, 0 < τ →
          δ ≤ Filter.liminf
            (fun N => (μ N).real (alignmentEventSet S bs N τ)) Filter.atTop := by
  simpa [ScaleListsClosed, alignmentEventSet, blockScale] using
    OAI.SourceMenuLiteral.charted_finite_menu_alignment n r s

/-- The rational shift written in the paper's alignment implication. -/
def paperAlignmentShift {n : ℕ} (ht : Fin n → ℤ) (b : FrameworkScale n)
    (u : Fin n → ℕ) (B : FrameworkBlock n) (D : Finset (Finset (Fin n))) : ℚ :=
  ∑ A ∈ D,
    (((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height ht A : ℚ) *
        OAI.ConstructedWordPlan.AlignmentScales.blockProduct b A) /
      ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height ht B.set : ℚ) *
        blockScale b B)) *
      (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
        (fun j => (u j : ℤ)) A : ℚ)

/-- Bridge between the paper's displayed shift and OAI's `SourceBlocks.offset`. -/
theorem oai_alignment_event_bridge {n : ℕ} (ht : Fin n → ℤ) (b : FrameworkScale n)
    (u : Fin n → ℕ) (B : FrameworkBlock n) (D : Finset (Finset (Fin n))) :
    paperAlignmentShift ht b u B D = OAI.SourceBlocks.offset ht b u B D := by
  rfl

/-- Finite calibration-error union bound in the ultrafilter-limit form used at lines 289–330. -/
theorem calibration_union_bound {ι : Type} [DecidableEq ι] (U : Ultrafilter ℕ)
    (I : Finset ι) (p : ι → ℕ → ℝ) (bound : ℝ)
    (hp : ∀ i ∈ I, UltrafilterLimLE U (p i) bound) :
    UltrafilterLimLE U (fun N => ∑ i ∈ I, p i N) ((I.card : ℝ) * bound) := by
  intro ε hε
  let ε' : ℝ := ε / ((I.card : ℝ) + 1)
  have hε' : 0 < ε' := by
    dsimp [ε']
    positivity
  have hall : ∀ᶠ N in (U : Filter ℕ), ∀ i ∈ I, p i N < bound + ε' := by
    apply (eventually_all_finset I).2
    intro i hi
    exact hp i hi ε' hε'
  filter_upwards [hall] with N hN
  have hsum : (∑ i ∈ I, p i N) ≤ ∑ i ∈ I, (bound + ε') := by
    apply Finset.sum_le_sum
    intro i hi
    exact le_of_lt (hN i hi)
  have hsumConst : (∑ i ∈ I, (bound + ε')) = (I.card : ℝ) * (bound + ε') := by
    simp
    ring
  have hcardPos : 0 < (I.card : ℝ) + 1 := by positivity
  have hsmall : (I.card : ℝ) * ε' < ε := by
    calc
      (I.card : ℝ) * ε' = ((I.card : ℝ) * ε) / ((I.card : ℝ) + 1) := by
        dsimp [ε']
        ring
      _ < ε := (div_lt_iff₀ hcardPos).2 (by nlinarith)
  calc
    (∑ i ∈ I, p i N) ≤ (I.card : ℝ) * (bound + ε') := hsum.trans_eq hsumConst
    _ = (I.card : ℝ) * bound + (I.card : ℝ) * ε' := by ring
    _ < (I.card : ℝ) * bound + ε := by linarith

/-- Combine an ordinary alignment lower limit and an ultrafilter calibration upper limit
(lines 320–345). The conclusion is the lower bound for their pointwise difference. -/
theorem ultrafilter_alignment_intersection (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ Filter.cofinite) (alignment calibration : ℕ → ℝ)
    (δ ε : ℝ) (hε : 0 < ε)
    (halign : ∀ ε' > 0, ∀ᶠ N in Filter.atTop, δ - ε' < alignment N)
    (hcal : UltrafilterLimLE U calibration (δ / 2)) :
    ∀ᶠ N in (U : Filter ℕ), δ / 2 - ε < alignment N - calibration N := by
  have hAlignTop : ∀ᶠ N in Filter.atTop, δ - ε / 2 < alignment N :=
    halign (ε / 2) (by linarith)
  have hUtop : (U : Filter ℕ) ≤ Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hU
  have hAlign : ∀ᶠ N in (U : Filter ℕ), δ - ε / 2 < alignment N :=
    Filter.Eventually.filter_mono hUtop hAlignTop
  have hCal : ∀ᶠ N in (U : Filter ℕ), calibration N < δ / 2 + ε / 2 :=
    hcal (ε / 2) (by linarith)
  filter_upwards [hAlign, hCal] with N ha hc
  linarith

/-- The calibration union and the alignment event leave positive mass along the ultrafilter. -/
theorem goodAlignmentMass_eventually {n r s : ℕ}
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite)
    {A : OAI.SourceAdmissible.Parameters n} {vs : Finset ℚ}
    {F : OAI.SourceChartedMenu.Menu s} (S : OAI.SourceMenuLiteral.ModelsSystem A vs r F)
    (χ : ℕ → Fin r) (bs : Finset (FrameworkScale n)) (τ δ : ℝ)
    (hAlign : δ ≤ Filter.liminf (fun N => alignmentProbability S bs N τ) Filter.atTop)
    (hBad : UltrafilterLimLE U (fun N => calibrationUnionProbability S χ N τ) (δ/2)) :
    ∀ ε, 0 < ε → ∀ᶠ N in (U : Filter ℕ),
      δ/2 - ε < goodAlignmentProbability S χ bs N τ := by
  have hA0 : ∀ N, 0 ≤ alignmentProbability S bs N τ := by
    intro N
    exact MeasureTheory.measureReal_nonneg
  have hA1 : ∀ N, alignmentProbability S bs N τ ≤ 1 := by
    intro N
    exact MeasureTheory.measureReal_le_one
  have hAlignEventually := liminf_bound_eventually hA0 hA1 hAlign
  intro ε hε
  have hDiff := ultrafilter_alignment_intersection U hU
    (fun N => alignmentProbability S bs N τ)
    (fun N => calibrationUnionProbability S χ N τ) δ ε hε hAlignEventually hBad
  have hPoint : ∀ N,
      alignmentProbability S bs N τ - calibrationUnionProbability S χ N τ ≤
        goodAlignmentProbability S χ bs N τ := by
    intro N
    have hmass := measureReal_inter_compl_ge (frameworkLaw A N)
      (frameworkLaw_ne_top_univ A N)
      (alignmentEventSet S bs N τ) (calibrationUnionSet S χ N τ)
    exact hmass
  filter_upwards [hDiff] with N hN
  exact lt_of_lt_of_le hN (hPoint N)

/-- A lower bound for the model part of the aligned integrand (lines 330–355). The exponent
`2^m` safely dominates the number of nonsingleton subsets. -/
theorem aligned_model_integrand_positive (m : ℕ) (_hm : 2 ≤ m) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) (f : NonsingletonSubsets m → ℝ)
    (hf : ∀ J, τ < f J) :
    τ ^ (2 ^ m) ≤ ∏ J : NonsingletonSubsets m, f J := by
  have hcard : Fintype.card (NonsingletonSubsets m) ≤ 2 ^ m := by
    calc
      Fintype.card (NonsingletonSubsets m) ≤ Fintype.card (Finset (Fin m)) :=
        Fintype.card_subtype_le _
      _ = 2 ^ Fintype.card (Fin m) := Fintype.card_finset
      _ = 2 ^ m := by simp
  have hprod : (∏ _J : NonsingletonSubsets m, τ) ≤ ∏ J : NonsingletonSubsets m, f J := by
    apply Finset.prod_le_prod₀
    · intro J hJ
      exact le_of_lt hτ0
    · intro J hJ
      exact le_of_lt (hf J)
  have hprod' : τ ^ Fintype.card (NonsingletonSubsets m) ≤
      ∏ J : NonsingletonSubsets m, f J := by
    convert hprod using 1
    all_goals simp [Finset.prod_const]
  exact (pow_le_pow_of_le_one (le_of_lt hτ0) hτ1 hcard).trans hprod'

/-- A finite sum of nonnegative weighted counts with positive value has a positive summand; this
is applied after choosing an index in the ultrafilter-positive set (lines 355–366). -/
theorem positive_total_count_has_positive_summand {ι : Type} [DecidableEq ι]
    (I : Finset ι) (f : ι → ℝ) (hpos : 0 < ∑ i ∈ I, f i) : ∃ i ∈ I, 0 < f i := by
  by_contra h
  push Not at h
  have hsum : (∑ i ∈ I, f i) ≤ 0 := Finset.sum_nonpos h
  linarith

/-- The outer tolerances can be chosen after the alignment mass and the two finite index counts
are fixed, as in `eq:outer-tolerances`. -/
theorem existsFrameworkTolerances {C K δ : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hδ : 0 < δ) (m : ℕ) :
    ∃ τ η : ℝ, 0 < τ ∧ τ < 1/4 ∧ 3*C*τ < δ/4 ∧ 0 < η ∧
      C*η < δ/4 ∧ K*η < δ*τ^(2^m)/4 := by
  let τ : ℝ := min (1/8) (δ / (100 * (C + 1)))
  have hdenC : 0 < C + 1 := by linarith
  have hratioC : C / (C + 1) ≤ 1 := (div_le_iff₀ hdenC).2 (by linarith)
  have hτpos : 0 < τ := lt_min (by norm_num) (div_pos hδ (by positivity))
  have hτlt : τ < 1/4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hτsmall : τ ≤ δ / (100 * (C + 1)) := min_le_right _ _
  have hCτ : C * τ ≤ δ / 100 := by
    calc
      C * τ ≤ C * (δ / (100 * (C + 1))) := mul_le_mul_of_nonneg_left hτsmall hC
      _ = δ / 100 * (C / (C + 1)) := by field_simp
      _ ≤ δ / 100 := by
        simpa using mul_le_mul_of_nonneg_left (a := δ / 100) hratioC (by positivity)
  have hCτ' : 3 * C * τ < δ / 4 := by nlinarith
  let η : ℝ := min (δ / (100 * (C + 1)))
    (δ * τ ^ (2 ^ m) / (100 * (K + 1)))
  have hdenK : 0 < K + 1 := by linarith
  have hratioK : K / (K + 1) ≤ 1 := (div_le_iff₀ hdenK).2 (by linarith)
  have hηpos : 0 < η := lt_min (div_pos hδ (by positivity))
    (div_pos (mul_pos hδ (pow_pos hτpos _)) (by positivity))
  have hηCsmall : η ≤ δ / (100 * (C + 1)) := min_le_left _ _
  have hCη : C * η ≤ δ / 100 := by
    calc
      C * η ≤ C * (δ / (100 * (C + 1))) := mul_le_mul_of_nonneg_left hηCsmall hC
      _ = δ / 100 * (C / (C + 1)) := by field_simp
      _ ≤ δ / 100 := by
        simpa using mul_le_mul_of_nonneg_left (a := δ / 100) hratioC (by positivity)
  have hηKsmall : η ≤ δ * τ ^ (2 ^ m) / (100 * (K + 1)) := min_le_right _ _
  have hKη : K * η ≤ δ * τ ^ (2 ^ m) / 100 := by
    calc
      K * η ≤ K * (δ * τ ^ (2 ^ m) / (100 * (K + 1))) :=
        mul_le_mul_of_nonneg_left hηKsmall hK
      _ = δ * τ ^ (2 ^ m) / 100 * (K / (K + 1)) := by field_simp
      _ ≤ δ * τ ^ (2 ^ m) / 100 :=
        by
          simpa using mul_le_mul_of_nonneg_left (a := δ * τ ^ (2 ^ m) / 100)
            hratioK (by positivity)
  have hδτpos : 0 < δ * τ ^ (2 ^ m) := mul_pos hδ (pow_pos hτpos _)
  refine ⟨τ, η, hτpos, hτlt, hCτ', hηpos, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- A positive weighted count yields an actual finite-sums/products configuration (lines
366–375). This includes divisor-support, integer-lattice, and distinctness extraction from the
admissible growth hierarchy. -/
theorem positive_weighted_count_configuration {n m r : ℕ}
    (A : OAI.SourceAdmissible.Parameters n) (N : ℕ) (χ : ℕ → Fin r) (colour : Fin r)
    (b : FrameworkScale n) (B : Fin m → FrameworkBlock n) (hB : IsBlockChain B)
    (hN : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
    (hOrder : ∀ z : Fin m → ℕ,
      (∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2) →
      StrictMono (fun d =>
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (B d).set : ℚ) * blockScale b (B d)) * (z d : ℚ)))
    (hpositive : 0 < weightedCount A N χ colour b B) :
    ∃ (C : Finset ℕ), C.card = m ∧ (∀ a ∈ C, 0 < a) ∧
      (∀ D ⊆ C, D.Nonempty → χ (∑ a ∈ D, a) = colour ∧
        χ (∏ a ∈ D, a) = colour) := by
  classical
  let μ : Measure (Fin n → ℕ) := frameworkLaw A N
  let ν : Measure (Fin m → ℕ) := Measure.pi (fun d =>
    Measure.map (fun t : Fin n → ℕ => t (B d).1) μ)
  let f : (Fin m → ℕ) → ℝ :=
    weightedCountIntegrandUnder A μ N χ colour b B
  have hposIntegral : 0 < ∫ z, f z ∂ν := by
    simpa [f, ν, μ, weightedCount, weightedCountUnder] using hpositive
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [frameworkLaw_eq A N hN]
    exact OAI.SourceMenuAlignment.law_probability A N hN
  have hLawDomain : ∀ᵐ t ∂μ,
      t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) := by
    change ∀ᵐ t ∂frameworkLaw A N,
      t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1))
    rw [frameworkLaw_eq A N hN]
    exact OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
      (primorial_pos _) hN
  have hPivotInterval (d : Fin m) :
      ∀ᵐ y ∂Measure.map (fun t : Fin n → ℕ => t (B d).1) μ,
        A.X N (B d).1 ≤ y ∧ y < (A.X N (B d).1)^2 := by
    rw [MeasureTheory.ae_map_iff (measurable_of_countable _).aemeasurable
      MeasurableSet.of_discrete]
    filter_upwards [hLawDomain] with t ht
    have hunit : t (B d).1 ∈
        OAI.RawHarmonicProbability.units (A.X N (B d).1) (primorial (N + 1)) :=
      (Fintype.mem_piFinset.mp ht) (B d).1
    have hIco : t (B d).1 ∈ Finset.Ico (A.X N (B d).1) ((A.X N (B d).1)^2) := by
      simpa [OAI.RawHarmonicProbability.units] using
        (Finset.mem_filter.mp hunit).1
    exact Finset.mem_Ico.mp hIco
  have hPivotIntervals : ∀ᵐ z ∂ν,
      ∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2 := by
    rw [MeasureTheory.ae_all_iff]
    intro d
    exact (MeasureTheory.measurePreserving_eval (fun d =>
      Measure.map (fun t : Fin n → ℕ => t (B d).1) μ) d).quasiMeasurePreserving.ae
        (hPivotInterval d)
  have hfNonneg : ∀ z, 0 ≤ f z := by
    intro z
    exact weightedCountIntegrandUnder_nonneg A μ N χ colour b B z
  have hfint : Integrable f ν := Integrable.of_integral_ne_zero (ne_of_gt hposIntegral)
  have hSupportMass : 0 < ν (Function.support f) :=
    (integral_pos_iff_support_of_nonneg hfNonneg hfint).mp hposIntegral
  let P : Set (Fin m → ℕ) :=
    {z | ∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2}
  have hSupportIntersection : 0 < ν (Function.support f ∩ P) := by
    have heq : ν (Function.support f ∩ P) = ν (Function.support f) := by
      apply MeasureTheory.measure_congr
      filter_upwards [hPivotIntervals] with z hz
      simp [P, hz]
    rw [heq]
    exact hSupportMass
  have hIntersectionNonempty : (Function.support f ∩ P).Nonempty := by
    by_contra h
    have hempty : Function.support f ∩ P = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty, MeasureTheory.measure_empty] at hSupportIntersection
    exact (lt_irrefl 0) hSupportIntersection
  obtain ⟨z, hzSupport, hzIntervals⟩ := hIntersectionNonempty
  have hzPositive : 0 < weightedCountIntegrandUnder A μ N χ colour b B z := by
    have hne : f z ≠ 0 := by
      change z ∈ Function.support f at hzSupport
      simpa [Function.support] using hzSupport
    exact HindmanSumsProducts.Framework.nonneg_ne_zero_pos (hfNonneg z)
      (by simpa [f] using hne)
  have hzBounds : ∀ d, A.X N (B d).1 ≤ z d ∧ z d < (A.X N (B d).1)^2 := by
    change z ∈ P at hzIntervals
    exact hzIntervals
  let coeff : Fin m → ℚ := fun d =>
    (OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
      (A.ht N) (B d).set : ℚ) * blockScale b (B d)
  let sumFactor : NonsingletonSubsets m → ℝ := fun J => by
    classical
    let hJ : J.val.Nonempty := by
      have hcard : 2 ≤ J.val.card := J.property
      exact Finset.card_pos.mp (by omega)
    let d := J.val.max' hJ
    exact rationalColorIndicator χ colour (coeff d * sumForm coeff J.val hJ z) *
      rationalDivisorWeightUnder μ (B d) (sumForm coeff J.val hJ z)
  have hKernelPos :
      0 < productMask χ colour coeff z *
        (∏ d, rationalDivisorWeightUnder μ (B d) (z d : ℚ)) *
        (∏ J : NonsingletonSubsets m, sumFactor J) := by
    simpa [f, weightedCountIntegrandUnder, coeff, sumFactor] using hzPositive
  have hKernelNe := ne_of_gt hKernelPos
  have hMaskNe : productMask χ colour coeff z ≠ 0 := by
    intro hzero
    apply hKernelNe
    simp [hzero]
  have hSumProductNe :
      (∏ J : NonsingletonSubsets m, sumFactor J) ≠ 0 := by
    intro hzero
    apply hKernelNe
    rw [hzero]
    simp
  have hMaskProductNe :
      (∏ J : NonemptySubsets m,
        rationalColorIndicator χ colour (∏ k ∈ J.val, coeff k * (z k : ℚ))) ≠ 0 := by
    simpa [productMask] using hMaskNe
  have hMaskHit (J : NonemptySubsets m) :
      rationalColorHit χ colour (∏ k ∈ J.val, coeff k * (z k : ℚ)) := by
    have hneJ := (Finset.prod_ne_zero_iff.mp hMaskProductNe) J (Finset.mem_univ J)
    have hposJ := lt_of_le_of_ne (rationalColorIndicator_nonneg χ colour _) (Ne.symm hneJ)
    exact rationalColorIndicator_hit_of_pos χ colour _ hposJ
  have hSumFactorProductNe : (∏ J : NonsingletonSubsets m, sumFactor J) ≠ 0 := hSumProductNe
  have hSumHit (J : NonsingletonSubsets m) (hJ : J.val.Nonempty) :
      rationalColorHit χ colour
        (coeff (J.val.max' hJ) * sumForm coeff J.val hJ z) := by
    let d := J.val.max' hJ
    have hfactorNe := (Finset.prod_ne_zero_iff.mp hSumFactorProductNe) J
      (Finset.mem_univ J)
    have hindicatorNe : rationalColorIndicator χ colour (coeff d * sumForm coeff J.val hJ z) ≠ 0 := by
      intro hzero
      apply hfactorNe
      simp [sumFactor, d, hzero]
    have hindicatorPos := lt_of_le_of_ne
      (rationalColorIndicator_nonneg χ colour (coeff d * sumForm coeff J.val hJ z))
      (Ne.symm hindicatorNe)
    exact rationalColorIndicator_hit_of_pos χ colour _ hindicatorPos
  have hSingletonHit (d : Fin m) : rationalColorHit χ colour (coeff d * (z d : ℚ)) := by
    simpa using hMaskHit ⟨{d}, by simp⟩
  let a : Fin m → ℕ := fun d => Classical.choose (hSingletonHit d)
  have haPos (d : Fin m) : 0 < a d := by
    simpa [a] using (Classical.choose_spec (hSingletonHit d)).1
  have haEq (d : Fin m) : (a d : ℚ) = coeff d * (z d : ℚ) := by
    simpa [a] using (Classical.choose_spec (hSingletonHit d)).2.1
  have haColor (d : Fin m) : χ (a d) = colour := by
    simpa [a] using (Classical.choose_spec (hSingletonHit d)).2.2
  have hCoeffPos (d : Fin m) : 0 < coeff d := by
    have hzpos : (0 : ℚ) < (z d : ℚ) := by
      exact_mod_cast (lt_of_lt_of_le (A.Xpos N (B d).1) (hzBounds d).1)
    have hapos : (0 : ℚ) < (a d : ℚ) := by exact_mod_cast haPos d
    rw [haEq d] at hapos
    exact (mul_pos_iff_of_pos_right hzpos).mp hapos
  have hstrict : StrictMono (fun d => coeff d * (z d : ℚ)) := hOrder z hzBounds
  have hinj : Function.Injective a := by
    intro d e hde
    by_contra hne
    have hde' : d ≠ e := by
      intro h
      apply hne
      subst e
      rfl
    have hcoeffeq : coeff d * (z d : ℚ) = coeff e * (z e : ℚ) := by
      calc
        coeff d * (z d : ℚ) = (a d : ℚ) := (haEq d).symm
        _ = (a e : ℚ) := congrArg (fun x : ℕ => (x : ℚ)) hde
        _ = coeff e * (z e : ℚ) := haEq e
    rcases lt_or_gt_of_ne hde' with hlt | hgt
    · have hlt' := hstrict hlt
      change coeff d * (z d : ℚ) < coeff e * (z e : ℚ) at hlt'
      rw [hcoeffeq] at hlt'
      exact (lt_irrefl _ hlt')
    · have hlt' := hstrict hgt
      change coeff e * (z e : ℚ) < coeff d * (z d : ℚ) at hlt'
      rw [hcoeffeq.symm] at hlt'
      exact (lt_irrefl _ hlt')
  have hProducts (J : Finset (Fin m)) (hJ : J.Nonempty) :
      χ (∏ d ∈ J, a d) = colour := by
    obtain ⟨x, hxpos, hxeq, hxcolour⟩ := hMaskHit ⟨J, hJ⟩
    have hcastProd : ((∏ d ∈ J, a d : ℕ) : ℚ) =
        ∏ d ∈ J, coeff d * (z d : ℚ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro d hd
      rw [haEq d]
    have hxnat : x = ∏ d ∈ J, a d := by
      have hxcast : (x : ℚ) = (∏ d ∈ J, a d : ℕ) := by
        calc
          (x : ℚ) = ∏ d ∈ J, coeff d * (z d : ℚ) := hxeq
          _ = (∏ d ∈ J, a d : ℕ) := hcastProd.symm
      exact Nat.cast_inj.mp hxcast
    rw [← hxnat]
    exact hxcolour
  have hSums (J : Finset (Fin m)) (hJ : J.Nonempty) :
      χ (∑ d ∈ J, a d) = colour := by
    by_cases hcard : 2 ≤ J.card
    · let J' : NonsingletonSubsets m := ⟨J, hcard⟩
      obtain ⟨x, hxpos, hxeq, hxcolour⟩ := hSumHit J' hJ
      let d := J.max' hJ
      have hform := blockCoefficient_mul_sumForm coeff J hJ z (ne_of_gt (hCoeffPos d))
      have hcastSum : ((∑ k ∈ J, a k : ℕ) : ℚ) =
          ∑ k ∈ J, coeff k * (z k : ℚ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [haEq k]
      have hxnat : x = ∑ k ∈ J, a k := by
        have hxcast : (x : ℚ) = (∑ k ∈ J, a k : ℕ) := by
          calc
            (x : ℚ) = coeff d * sumForm coeff J hJ z := hxeq
            _ = ∑ k ∈ J, coeff k * (z k : ℚ) := hform
            _ = (∑ k ∈ J, a k : ℕ) := hcastSum.symm
        exact Nat.cast_inj.mp hxcast
      rw [← hxnat]
      exact hxcolour
    · have hcard1 : J.card = 1 := by
        have hcardPos := Finset.card_pos.mpr hJ
        omega
      obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp hcard1
      simpa using haColor d
  let C : Finset ℕ := Finset.univ.image a
  refine ⟨C, ?_, ?_, ?_⟩
  · simpa [C] using
      (Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) hinj)
  · intro x hx
    have hxC : x ∈ C := hx
    change x ∈ Finset.univ.image a at hxC
    obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hxC
    simpa [hdx] using haPos d
  · intro D hD hDne
    let J : Finset (Fin m) := Finset.univ.filter (fun d => a d ∈ D)
    have hDimage : D = J.image a := by
      ext x
      constructor
      · intro hx
        have hxC : x ∈ C := hD hx
        change x ∈ Finset.univ.image a at hxC
        obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hxC
        apply Finset.mem_image.mpr
        refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hdx⟩
        simpa [hdx] using hx
      · intro hx
        obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hx
        have hdD := (Finset.mem_filter.mp hd).2
        simpa [hdx] using hdD
    have hJ : J.Nonempty := by
      obtain ⟨x, hx⟩ := hDne
      have hxImage : x ∈ J.image a := by rw [← hDimage]; exact hx
      obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hxImage
      exact ⟨d, hd⟩
    have hsumD : (∑ x ∈ D, x) = ∑ d ∈ J, a d := by
      rw [hDimage]
      exact Finset.sum_image (s := J) (f := fun x : ℕ => x) (g := a) hinj.injOn
    have hprodD : (∏ x ∈ D, x) = ∏ d ∈ J, a d := by
      rw [hDimage]
      exact Finset.prod_image (s := J) (f := fun x : ℕ => x) (g := a) hinj.injOn
    rw [hsumD, hprodD]
    exact ⟨hSums J hJ, hProducts J hJ⟩

set_option maxHeartbeats 1000000
/-- Main deduction for `m≥2`, with its long proof packaged into the five claims above. -/
theorem main_of_principles_large (r : ℕ) (hr : 0 < r) (hP : PredictionPrinciple)
    (χ : ℕ → Fin r)
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  classical
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ Filter.cofinite := by
    exact Filter.hyperfilter_le_cofinite
  obtain ⟨s, hPstep⟩ := hP m hm
  obtain ⟨n, hchainSelection⟩ := chain_selection m r
  obtain ⟨bs, vs, δ, hδ, hbs, hvs, hclosed, hAlign⟩ :=
    alignment_principle n r s
  let C : ℝ := Fintype.card (CalibrationIndex n r vs)
  let K : ℝ := Fintype.card (PredictionCountIndex n m r bs)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨τ, η, hτ, hτlt, hτC, hη, hηC, hηK⟩ :=
    existsFrameworkTolerances hC hK hδ m
  obtain ⟨A, F, S, hPred⟩ :=
    hPstep U hU n r χ bs vs hbs hvs hclosed τ η hτ hτlt hη
  let μ : ℕ → Measure (Fin n → ℕ) := fun N => frameworkLaw A N
  have hμ : ∀ N (hX : ∀ i, 4 * primorial (N + 1) ≤ A.X N i), μ N = A.law N hX := by
    intro N hX
    exact frameworkLaw_eq A N hX
  obtain ⟨hcalibrationRaw, hcountRaw⟩ := hPred μ hμ
  have hcalibration : ∀ B : FrameworkBlock n, ∀ a : ℚ, a ∈ vs → ∀ c : Fin r,
      UltrafilterLimLE U (fun N => calibrationProbability S χ N B a c τ) (3*τ+η) := by
    intro B a ha c ε hε
    have hε' : 0 < ε / 2 := by linarith
    filter_upwards [hcalibrationRaw B a ha c (ε / 2) hε'] with N hN
    have heq : calibrationProbabilityUnder (μ N) S χ N B a c τ =
        calibrationProbability S χ N B a c τ := rfl
    rw [← heq]
    linarith
  have hcount : ∀ (B : Fin m → FrameworkBlock n), IsBlockChain B →
      ∀ b : FrameworkScale n, b ∈ bs → ∀ c : Fin r,
        UltrafilterLimLE U
          (fun N => |weightedCount A N χ c b B - modelIntegrandMean S N χ c b B|) η := by
    intro B hB b hb c ε hε
    have hε' : 0 < ε / 2 := by linarith
    filter_upwards [hcountRaw B hB b hb c (ε / 2) hε'] with N hN
    have heq : weightedCountUnder A (μ N) N χ c b B -
        modelIntegrandMeanUnder S (μ N) N χ c b B =
        weightedCount A N χ c b B - modelIntegrandMean S N χ c b B := rfl
    rw [← heq]
    exact lt_of_le_of_lt hN (by linarith)
  have hAlignMass : δ ≤ Filter.liminf (fun N => alignmentProbability S bs N τ) Filter.atTop := by
    apply hAlign A F S (fun N => frameworkLaw A N)
    · intro N hX
      exact frameworkLaw_eq A N hX
    · exact hτ
  have hCalibrationSum : UltrafilterLimLE U
      (fun N => ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ)
      ((Fintype.card (CalibrationIndex n r vs) : ℝ) * (3*τ+η)) := by
    apply calibration_union_bound U Finset.univ
    · intro i hi
      exact hcalibration i.1 i.2.1.val i.2.1.property i.2.2
  have hCalibrationUnion : UltrafilterLimLE U
      (fun N => calibrationUnionProbability S χ N τ) (C * (3*τ+η)) := by
    apply UltrafilterLimLE.mono (f := fun N => calibrationUnionProbability S χ N τ)
      (g := fun N => ∑ i ∈ (Finset.univ : Finset (CalibrationIndex n r vs)),
        calibrationProbability S χ N i.1 i.2.1 i.2.2 τ)
    · intro N
      simpa using calibration_failure_union_probability_le S χ N τ
    · simpa [C] using hCalibrationSum
  have hCalibrationUnionSmall : C * (3*τ+η) < δ/2 := by
    calc
      C * (3*τ+η) = 3*C*τ + C*η := by ring
      _ < δ/4 + δ/4 := add_lt_add hτC hηC
      _ = δ/2 := by ring
  have hCalibrationBound : UltrafilterLimLE U
      (fun N => calibrationUnionProbability S χ N τ) (δ/2) :=
    UltrafilterLimLE.bound_mono (le_of_lt hCalibrationUnionSmall) hCalibrationUnion
  have hGoodMass := goodAlignmentMass_eventually U hU S χ bs τ δ hAlignMass hCalibrationBound
  have hUtop : (U : Filter ℕ) ≤ Filter.atTop := by
    rw [← Nat.cofinite_eq_atTop]
    exact hU
  have hNTop : ∀ᶠ N in Filter.atTop, ∀ i, 4 * primorial (N + 1) ≤ A.X N i := by
    have hall : ∀ᶠ N in Filter.atTop, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        4 * primorial (N + 1) ≤ A.X N i := by
      apply (eventually_all_finset (Finset.univ : Finset (Fin n))).2
      intro i hi
      exact A.eventual_X i
    filter_upwards [hall] with N hN
    intro i
    exact hN i (Finset.mem_univ i)
  have hNU : ∀ᶠ N in (U : Filter ℕ), ∀ i, 4 * primorial (N + 1) ≤ A.X N i :=
    Filter.Eventually.filter_mono hUtop hNTop
  have hBaseTop : ∀ᶠ N in Filter.atTop, ∀ b ∈ bs, ∀ i,
      ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x := by
    apply (eventually_all_finset bs).2
    intro b hb
    exact eventually_height_scale_integer A b (hbs b hb)
  have hBaseU : ∀ᶠ N in (U : Filter ℕ), ∀ b ∈ bs, ∀ i,
      ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x :=
    Filter.Eventually.filter_mono hUtop hBaseTop
  have hOrderTop : ∀ᶠ N in Filter.atTop, ∀ b ∈ bs, ∀ CB : BlockChains n m,
      ∀ z : Fin m → ℕ,
        (∀ d, A.X N (CB.val d).1 ≤ z d ∧ z d < (A.X N (CB.val d).1)^2) →
        StrictMono (fun d =>
          ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (CB.val d).set : ℚ) * blockScale b (CB.val d)) * (z d : ℚ)) := by
    apply (eventually_all_finset bs).2
    intro b hb
    have hChains : ∀ᶠ N in Filter.atTop, ∀ CB ∈ (Finset.univ : Finset (BlockChains n m)),
        ∀ z : Fin m → ℕ,
          (∀ d, A.X N (CB.val d).1 ≤ z d ∧ z d < (A.X N (CB.val d).1)^2) →
          StrictMono (fun d =>
            ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (A.ht N) (CB.val d).set : ℚ) * blockScale b (CB.val d)) * (z d : ℚ)) := by
      apply (eventually_all_finset (Finset.univ : Finset (BlockChains n m))).2
      intro CB hCB
      exact eventually_chain_coefficient_order A b (hbs b hb) CB.val CB.property
    filter_upwards [hChains] with N hChains
    intro CB
    exact hChains CB (Finset.mem_univ CB)
  have hOrderU : ∀ᶠ N in (U : Filter ℕ), ∀ b ∈ bs, ∀ CB : BlockChains n m,
      ∀ z : Fin m → ℕ,
        (∀ d, A.X N (CB.val d).1 ≤ z d ∧ z d < (A.X N (CB.val d).1)^2) →
        StrictMono (fun d =>
          ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
            (A.ht N) (CB.val d).set : ℚ) * blockScale b (CB.val d)) * (z d : ℚ)) :=
    Filter.Eventually.filter_mono hUtop hOrderTop
  let countErr : PredictionCountIndex n m r bs → ℕ → ℝ := fun i N =>
    |weightedCount A N χ i.2.2 i.1.val i.2.1.val -
      modelIntegrandMean S N χ i.2.2 i.1.val i.2.1.val|
  have hCountErrSum : UltrafilterLimLE U
      (fun N => ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), countErr i N)
      (K * η) := by
    have h := calibration_union_bound U (Finset.univ : Finset (PredictionCountIndex n m r bs))
      countErr η (by
        intro i hi
        exact hcount i.2.1.val i.2.1.property i.1.val i.1.property i.2.2)
    simpa [K, countErr, PredictionCountIndex] using h
  let modelMeanTerm : PredictionCountIndex n m r bs → ℕ → ℝ := fun i N =>
    modelIntegrandMean S N χ i.2.2 i.1.val i.2.1.val
  let weightedTerm : PredictionCountIndex n m r bs → ℕ → ℝ := fun i N =>
    weightedCount A N χ i.2.2 i.1.val i.2.1.val
  let modelTotal : ℕ → ℝ := fun N =>
    ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), modelMeanTerm i N
  let weightedTotal : ℕ → ℝ := fun N =>
    ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), weightedTerm i N
  let errorTotal : ℕ → ℝ := fun N =>
    ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), countErr i N
  have hModelMinusWeighted (N : ℕ) : modelTotal N - weightedTotal N ≤ errorTotal N := by
    calc
      modelTotal N - weightedTotal N =
          ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)),
            (modelMeanTerm i N - weightedTerm i N) := by
        simp [modelTotal, weightedTotal, Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)),
            countErr i N := by
        apply Finset.sum_le_sum
        intro i hi
        dsimp [countErr, modelMeanTerm, weightedTerm]
        calc
          _ ≤ |modelIntegrandMean S N χ i.2.2 i.1.val i.2.1.val -
              weightedCount A N χ i.2.2 i.1.val i.2.1.val| := le_abs_self _
          _ = |weightedCount A N χ i.2.2 i.1.val i.2.1.val -
              modelIntegrandMean S N χ i.2.2 i.1.val i.2.1.val| := by rw [abs_sub_comm]
  let modelSampleTerm : PredictionCountIndex n m r bs → ℕ → (Fin n → ℕ) → ℝ :=
    fun i N t => modelIntegrand S N χ i.2.2 i.1.val i.2.1.val t
  let modelPoint : ℕ → (Fin n → ℕ) → ℝ := fun N t =>
    ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), modelSampleTerm i N t
  have hModelPointNonneg (N : ℕ) (t : Fin n → ℕ) : 0 ≤ modelPoint N t := by
    unfold modelPoint
    apply Finset.sum_nonneg
    intro i hi
    exact (modelIntegrand_mem_Icc S bs hclosed i.1.property N χ i.2.2 i.2.1.val t).1
  have hModelPointLe (N : ℕ) (t : Fin n → ℕ) :
      modelPoint N t ≤ (Fintype.card (PredictionCountIndex n m r bs) : ℝ) := by
    unfold modelPoint
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (modelIntegrand_mem_Icc S bs hclosed i.1.property N χ i.2.2 i.2.1.val t).2
      _ = (Fintype.card (PredictionCountIndex n m r bs) : ℝ) := by simp
  have hModelPointIntegrable (N : ℕ) :
      Integrable (modelPoint N) (frameworkLaw A N) := by
    letI : IsFiniteMeasure (frameworkLaw A N) :=
      ⟨(lt_top_iff_ne_top).2 (frameworkLaw_ne_top_univ A N)⟩
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
      (Fintype.card (PredictionCountIndex n m r bs) : ℝ)
    filter_upwards [] with t
    exact abs_le.mpr ⟨by linarith [hModelPointNonneg N t], hModelPointLe N t⟩
  have hSingleModelMean (N : ℕ) (i : PredictionCountIndex n m r bs) :
      modelMeanTerm i N = ∫ t, modelSampleTerm i N t ∂frameworkLaw A N := by rfl
  have hModelMeanIntegral (N : ℕ) :
      modelTotal N = ∫ t, modelPoint N t ∂frameworkLaw A N := by
    have hIntSum :
        ∫ t, modelPoint N t ∂frameworkLaw A N =
          ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)),
            ∫ t, modelSampleTerm i N t ∂frameworkLaw A N := by
      unfold modelPoint
      exact MeasureTheory.integral_finsetSum (Finset.univ : Finset (PredictionCountIndex n m r bs))
        (fun i hi => modelIntegrand_integrable S bs hclosed i.1.property N χ i.2.2 i.2.1.val)
    calc
      modelTotal N =
          ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)),
            ∫ t, modelSampleTerm i N t ∂frameworkLaw A N := by
        unfold modelTotal
        apply Finset.sum_congr rfl
        intro i hi
        exact hSingleModelMean N i
      _ = ∫ t, modelPoint N t ∂frameworkLaw A N := hIntSum.symm
  let goodSet : ℕ → Set (Fin n → ℕ) := fun N =>
    alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ
  let modelFloor : ℝ := τ ^ (2 ^ m)
  let goodIndicator : ℕ → (Fin n → ℕ) → ℝ := fun N =>
    (goodSet N).indicator (fun _ => modelFloor)
  have hGoodMassQuarter : ∀ᶠ N in (U : Filter ℕ),
      δ / 4 < goodAlignmentProbability S χ bs N τ := by
    filter_upwards [hGoodMass (δ / 4) (by linarith)] with N hN
    have hEq : δ / 2 - δ / 4 = δ / 4 := by ring
    rw [hEq] at hN
    exact hN
  have hGoodIndicatorIntegrable (N : ℕ) :
      Integrable (goodIndicator N) (frameworkLaw A N) := by
    letI : IsFiniteMeasure (frameworkLaw A N) :=
      ⟨(lt_top_iff_ne_top).2 (frameworkLaw_ne_top_univ A N)⟩
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable modelFloor
    have hFloor0 : 0 ≤ modelFloor := pow_nonneg hτ.le _
    filter_upwards [] with t
    change |(goodSet N).indicator (fun _ => modelFloor) t| ≤ modelFloor
    by_cases ht : t ∈ goodSet N
    · rw [Set.indicator_of_mem ht, abs_of_nonneg hFloor0]
    · rw [Set.indicator_of_notMem ht]
      simp [hFloor0]
  have hModelIndicatorLe (N : ℕ)
      (hXN : ∀ i, 4 * primorial (N + 1) ≤ A.X N i)
      (hBaseN : ∀ b ∈ bs, ∀ i, ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x) :
      ∀ᵐ t ∂frameworkLaw A N, goodIndicator N t ≤ modelPoint N t := by
    have hDomain : ∀ᵐ t ∂frameworkLaw A N,
        t ∈ OAI.ProductExposureLaw.outsideDomain (A.X N) (primorial (N + 1)) := by
      rw [frameworkLaw_eq A N hXN]
      exact OAI.ProductExposureLaw.outside_ae_domain (A.X N) (primorial (N + 1))
        (primorial_pos _) hXN
    filter_upwards [hDomain] with t ht
    by_cases hgood : t ∈ goodSet N
    · have hLower := goodSample_modelIntegrand_sum_lower S bs hclosed hbs
        hchainSelection N χ hm τ hτ (by linarith [hτlt]) hBaseN t ht
          (by simpa [goodSet] using hgood)
      have hLower' : modelFloor ≤ modelPoint N t := by
        simpa [modelFloor] using hLower
      change (goodSet N).indicator (fun _ => modelFloor) t ≤ modelPoint N t
      rw [Set.indicator_of_mem hgood]
      exact hLower'
    · have hzero : goodIndicator N t = 0 := by simp [goodIndicator, hgood]
      rw [hzero]
      exact hModelPointNonneg N t
  have hGoodIndicatorIntegral (N : ℕ) :
      ∫ t, goodIndicator N t ∂frameworkLaw A N =
        modelFloor * goodAlignmentProbability S χ bs N τ := by
    rw [MeasureTheory.integral_indicator_const modelFloor MeasurableSet.of_discrete]
    change ((frameworkLaw A N).real
      (alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ)) • modelFloor =
        modelFloor * (frameworkLaw A N).real
          (alignmentEventSet S bs N τ ∩ (calibrationUnionSet S χ N τ)ᶜ)
    simp [smul_eq_mul, mul_comm]
  have hModelTotalLower : ∀ᶠ N in (U : Filter ℕ),
      δ / 4 * modelFloor < modelTotal N := by
    filter_upwards [hGoodMassQuarter, hNU, hBaseU] with N hMass hXN hBaseN
    have hmono := MeasureTheory.integral_mono_ae (hGoodIndicatorIntegrable N)
      (hModelPointIntegrable N) (hModelIndicatorLe N hXN hBaseN)
    rw [hGoodIndicatorIntegral, ← hModelMeanIntegral N] at hmono
    have hFloor : 0 < modelFloor := pow_pos hτ _
    have hmul := mul_lt_mul_of_pos_left hMass hFloor
    calc
      δ / 4 * modelFloor < modelFloor * goodAlignmentProbability S χ bs N τ := by
        nlinarith [hmul]
      _ ≤ modelTotal N := hmono
  have hMargin : K * η < δ / 4 * modelFloor := by
    dsimp [modelFloor]
    nlinarith [hηK]
  let εerr : ℝ := (δ / 4 * modelFloor - K * η) / 2
  have hεerr : 0 < εerr := by
    dsimp [εerr]
    linarith
  have hErrorEvent : ∀ᶠ N in (U : Filter ℕ), errorTotal N < K * η + εerr := by
    have h := hCountErrSum εerr hεerr
    filter_upwards [h] with N hN
    exact hN
  have hWeightedTotalPos : ∀ᶠ N in (U : Filter ℕ), 0 < weightedTotal N := by
    have hErrorBelowFloor : K * η + εerr < δ / 4 * modelFloor := by
      dsimp [εerr]
      linarith
    filter_upwards [hModelTotalLower, hErrorEvent] with N hModel hError
    have hModelError : errorTotal N < modelTotal N :=
      lt_trans hError (lt_trans hErrorBelowFloor hModel)
    have hle : modelTotal N - errorTotal N ≤ weightedTotal N := by
      have h := hModelMinusWeighted N
      linarith
    exact lt_of_lt_of_le (sub_pos.mpr hModelError) hle
  have hAllAtN : ∀ᶠ N in (U : Filter ℕ),
      (∀ i, 4 * primorial (N + 1) ≤ A.X N i) ∧
      (∀ b ∈ bs, ∀ i, ∃ x : ℕ, 0 < x ∧ (A.ht N i : ℚ) * b i = x) ∧
      (∀ b ∈ bs, ∀ CB : BlockChains n m,
        ∀ z : Fin m → ℕ,
          (∀ d, A.X N (CB.val d).1 ≤ z d ∧ z d < (A.X N (CB.val d).1)^2) →
          StrictMono (fun d =>
            ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
              (A.ht N) (CB.val d).set : ℚ) * blockScale b (CB.val d)) * (z d : ℚ))) ∧
      0 < weightedTotal N := by
    filter_upwards [hNU, hBaseU, hOrderU, hWeightedTotalPos] with N hXN hBaseN hOrderN hPos
    exact ⟨hXN, hBaseN, hOrderN, hPos⟩
  obtain ⟨N, hXN, hBaseN, hOrderN, hPos⟩ := hAllAtN.exists
  have hCountSum : 0 <
      ∑ i ∈ (Finset.univ : Finset (PredictionCountIndex n m r bs)), weightedTerm i N := by
    simpa [weightedTotal] using hPos
  obtain ⟨idx, hidx, hidxPositive⟩ := positive_total_count_has_positive_summand
    (Finset.univ : Finset (PredictionCountIndex n m r bs)) (fun i => weightedTerm i N) hCountSum
  have hOrder : ∀ z : Fin m → ℕ,
      (∀ d, A.X N (idx.2.1.val d).1 ≤ z d ∧
        z d < (A.X N (idx.2.1.val d).1)^2) →
      StrictMono (fun d =>
        ((OAI.ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic.height
          (A.ht N) (idx.2.1.val d).set : ℚ) * blockScale idx.1.val (idx.2.1.val d)) *
          (z d : ℚ)) := hOrderN idx.1.val idx.1.property idx.2.1
  have hpositive : 0 < weightedCount A N χ idx.2.2 idx.1.val idx.2.1.val := by
    simpa [weightedTerm] using hidxPositive
  obtain ⟨C, hcard, hpositiveElems, hconfiguration⟩ :=
    positive_weighted_count_configuration A N χ idx.2.2 idx.1.val idx.2.1.val
      idx.2.1.property hXN hOrder hpositive
  exact ⟨C, idx.2.2, hcard, hpositiveElems, hconfiguration⟩
set_option maxHeartbeats 200000

/-- Deduction of the frozen finite sums/products statement from Prediction and Alignment. The
separation parameters in Theorem `thm:main` are omitted because `Challenge.lean` asks only for the
monochromatic configuration. -/
theorem main_of_principles (hP : PredictionPrinciple) (r : ℕ) (χ : ℕ → Fin r) (m : ℕ) :
    ∃ (A : Finset ℕ) (c : Fin r), A.card = m ∧ (∀ a ∈ A, 0 < a) ∧
      ∀ B ⊆ A, B.Nonempty → χ (∑ b ∈ B, b) = c ∧ χ (∏ b ∈ B, b) = c := by
  classical
  by_cases hr : r = 0
  · subst r
    exact (Fin.elim0 (χ 0))
  by_cases hm0 : m = 0
  · subst m
    obtain ⟨c⟩ : Nonempty (Fin r) := ⟨χ 0⟩
    refine ⟨∅, c, by simp, by simp, ?_⟩
    intro B hB hne
    have : B = ∅ := Finset.subset_empty.mp hB
    subst B
    simp at hne
  by_cases hm1 : m = 1
  · subst m
    refine ⟨{1}, χ 1, by simp, by simp, ?_⟩
    intro B hB hne
    have hcard : B.card = 1 := by
      have hsubset : B ⊆ ({1} : Finset ℕ) := hB
      have hle : B.card ≤ 1 := Finset.card_le_card hsubset |>.trans (by simp)
      have hpos : 0 < B.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨x, hxB⟩ := Finset.card_eq_one.mp hcard
    have hx : x = 1 := Finset.mem_singleton.mp (hB (by simp [hxB]))
    subst x
    simp [hxB]
  · have hm : 2 ≤ m := by omega
    exact main_of_principles_large r (Nat.pos_of_ne_zero hr) hP χ m hm

end
end HindmanSumsProducts
