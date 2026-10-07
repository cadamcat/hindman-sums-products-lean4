import HindmanSumsProducts.Prediction.PkgOpusDpo
import HindmanSumsProducts.Prediction.PkgB

namespace HindmanSumsProducts
namespace Prediction

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

noncomputable section

private noncomputable def l_dpre_poolRangeTupleEquiv {m M : ℕ} :
    {p : Fin m → ℕ // p ∈ Fintype.piFinset (fun _ : Fin m => Finset.range M)} ≃
      (Fin m → Fin M) where
  toFun p i := ⟨p.1 i, by
    have hi := Fintype.mem_piFinset.mp p.2 i
    exact Finset.mem_range.mp hi⟩
  invFun p := ⟨fun i => (p i).val, Fintype.mem_piFinset.mpr (fun i =>
    Finset.mem_range.mpr (p i).isLt)⟩
  left_inv := by
    intro p
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro p
    funext i
    apply Fin.ext
    rfl

private theorem l_dpre_poolProbability_finite {m : ℕ}
    (lo hi : Fin m → ℕ) (M : ℕ) (hhi : ∀ i, hi i ≤ M)
    (E : (Fin m → ℕ) → Prop) :
    independentPrimePoolProbability lo hi E =
      ∑ p : Fin m → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if E (fun i => (p i).val) then 1 else 0) := by
  classical
  let S : Finset (Fin m → ℕ) := Fintype.piFinset
    (fun _ : Fin m => Finset.range M)
  have htermZero (p : Fin m → ℕ) (hp : p ∉ S) :
      independentPrimePoolMass lo hi p * (if E p then 1 else 0) = 0 := by
    have hnot : ¬ ∀ i : Fin m, p i ∈ Finset.range M := by
      intro hall
      apply hp
      simpa [S, Fintype.mem_piFinset] using hall
    obtain ⟨i, hiMem⟩ := not_forall.mp hnot
    have hmass : independentPrimePoolMass lo hi p = 0 := by
      unfold independentPrimePoolMass
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      unfold primePoolLaw
      split_ifs with h
      · exact False.elim (hiMem (Finset.mem_range.mpr (lt_of_lt_of_le h.2.1 (hhi i))))
      · rfl
    simp [hmass]
  have hsum : independentPrimePoolProbability lo hi E =
      ∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then 1 else 0) := by
    unfold independentPrimePoolProbability
    exact tsum_eq_sum (s := S) htermZero
  have hattach :
      (∑ p ∈ S, independentPrimePoolMass lo hi p * (if E p then 1 else 0)) =
        ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then 1 else 0) := by
    rw [← Finset.sum_attach]
    simp
  calc
    independentPrimePoolProbability lo hi E =
        ∑ p : {p : Fin m → ℕ // p ∈ S},
          independentPrimePoolMass lo hi p.1 * (if E p.1 then 1 else 0) := by
            rw [hsum, hattach]
    _ = ∑ p : Fin m → Fin M,
          (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
            (if E (fun i => (p i).val) then 1 else 0) := by
          apply Fintype.sum_equiv (l_dpre_poolRangeTupleEquiv (m := m) (M := M))
          intro p
          have hval :
              (fun i => ((l_dpre_poolRangeTupleEquiv (m := m) (M := M) p) i).val) = p.1 := by
            funext i
            rfl
          simp only [independentPrimePoolMass]
          rw [← hval]

private noncomputable def l_dpre_blockTupleEquiv {b sl M : ℕ} :
    (Fin (b * sl) → Fin M) ≃ (Fin b → Fin sl → Fin M) where
  toFun p k j := p (pkgB2_replicaEmbedding k j)
  invFun p i := p ((finProdFinEquiv (m := b) (n := sl)).symm i).1
      ((finProdFinEquiv (m := b) (n := sl)).symm i).2
  left_inv := by
    intro p
    funext i
    exact congrArg p ((finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i)
  right_inv := by
    intro p
    funext k j
    exact congrArg (fun z : Fin b × Fin sl => p z.1 z.2)
      ((finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j))

private theorem l_dpre_independentPool_blockFactor {b sl : ℕ}
    (lo hi : Fin (b * sl) → ℕ) (loBlock hiBlock : Fin b → ℕ)
    (hlo : ∀ k j, lo (pkgB2_replicaEmbedding k j) = loBlock k)
    (hhi : ∀ k j, hi (pkgB2_replicaEmbedding k j) = hiBlock k)
    (G : ∀ k : Fin b, (Fin sl → ℕ) → Prop) :
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) =
      ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
        (fun _ => hiBlock k) (fun p => G k p) := by
  classical
  let M : ℕ := ∑ k : Fin b, hiBlock k
  let Btuple := l_dpre_blockTupleEquiv (b := b) (sl := sl) (M := M)
  let term : ∀ k, (Fin sl → Fin M) → ℝ := fun k q =>
    (∏ j, primePoolLaw (loBlock k) (hiBlock k) (q j).val) *
      (if G k (fun j => (q j).val) then 1 else 0)
  have hboundBlock (k : Fin b) : hiBlock k ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (hiBlock j)) (Finset.mem_univ k)
  have hboundFull (i : Fin (b * sl)) : hi i ≤ M := by
    let ij := (finProdFinEquiv (m := b) (n := sl)).symm i
    have hiEq : i = pkgB2_replicaEmbedding ij.1 ij.2 := by
      exact ((finProdFinEquiv (m := b) (n := sl)).apply_symm_apply i).symm
    calc
      hi i = hi (pkgB2_replicaEmbedding ij.1 ij.2) := by rw [hiEq]
      _ = hiBlock ij.1 := hhi ij.1 ij.2
      _ ≤ M := hboundBlock ij.1
  have hfinite := l_dpre_poolProbability_finite lo hi M hboundFull
    (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j)))
  have hmass (p : Fin (b * sl) → Fin M) :
      independentPrimePoolMass lo hi (fun i => (p i).val) =
        ∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
          (p (pkgB2_replicaEmbedding k j)).val := by
    unfold independentPrimePoolMass
    calc
      ∏ i : Fin (b * sl), primePoolLaw (lo i) (hi i) (p i).val =
          ∏ z : Fin b × Fin sl,
            primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
              (hi (finProdFinEquiv (m := b) (n := sl) z))
              (p (finProdFinEquiv (m := b) (n := sl) z)).val := by
                symm
                exact Fintype.prod_equiv (finProdFinEquiv (m := b) (n := sl))
                  (fun z => primePoolLaw (lo (finProdFinEquiv (m := b) (n := sl) z))
                    (hi (finProdFinEquiv (m := b) (n := sl) z))
                    (p (finProdFinEquiv (m := b) (n := sl) z)).val)
                  (fun i => primePoolLaw (lo i) (hi i) (p i).val) (by intro z; rfl)
      _ = ∏ k : Fin b, ∏ j : Fin sl,
            primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val := by
                rw [Fintype.prod_prod_type]
                apply Finset.prod_congr rfl
                intro k hk
                apply Finset.prod_congr rfl
                intro j hj
                have hlo' : lo (finProdFinEquiv (m := b) (n := sl) (k, j)) = loBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hlo k j
                have hhi' : hi (finProdFinEquiv (m := b) (n := sl) (k, j)) = hiBlock k := by
                  have he : pkgB2_replicaEmbedding k j =
                      finProdFinEquiv (m := b) (n := sl) (k, j) := rfl
                  rw [← he]
                  exact hhi k j
                rw [hlo', hhi']
                rfl
  have hterm (p : Fin (b * sl) → Fin M) :
      (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) =
        ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
    have hEvent :
        (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then (1 : ℝ) else 0) =
          ∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then (1 : ℝ) else 0 := by
      by_cases hall : ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val)
      · simp [hall]
      · obtain ⟨k, hk⟩ := not_forall.mp hall
        have hzero : ∏ k' : Fin b,
            (if G k' (fun j => (p (pkgB2_replicaEmbedding k' j)).val) then (1 : ℝ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
        simpa only [if_neg hall] using hzero.symm
    calc
      _ = independentPrimePoolMass lo hi (fun i => (p i).val) *
            (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
              rfl
      _ = (∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
              (p (pkgB2_replicaEmbedding k j)).val) *
            (∏ k, if G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
              rw [hmass p]
              exact congrArg (fun z : ℝ =>
                (∏ k, ∏ j, primePoolLaw (loBlock k) (hiBlock k)
                  (p (pkgB2_replicaEmbedding k j)).val) * z) hEvent
      _ = ∏ k, term k (fun j => p (pkgB2_replicaEmbedding k j)) := by
              simp only [term]
              rw [← Finset.prod_mul_distrib]
  have hfactor :
    (∑ p : Fin (b * sl) → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0)) =
        ∏ k, ∑ q : Fin sl → Fin M, term k q := by
    calc
      _ = ∑ q : Fin b → Fin sl → Fin M, ∏ k, term k (q k) := by
        apply Fintype.sum_equiv Btuple
        intro p
        have hB (k : Fin b) : Btuple p k = fun j => p (pkgB2_replicaEmbedding k j) := rfl
        simpa only [hB] using hterm p
      _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := by
        symm
        exact Fintype.prod_sum (fun k q => term k q)
  have hRHS (k : Fin b) :
      independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (fun p => G k p) =
        ∑ q : Fin sl → Fin M, term k q := by
    simpa [term, independentPrimePoolMass] using
      (l_dpre_poolProbability_finite (fun _ : Fin sl => loBlock k)
        (fun _ => hiBlock k) M (fun _ => hboundBlock k) (G k))
  calc
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) =
      ∑ p : Fin (b * sl) → Fin M,
        (∏ i, primePoolLaw (lo i) (hi i) (p i).val) *
          (if ∀ k, G k (fun j => (p (pkgB2_replicaEmbedding k j)).val) then 1 else 0) := by
            simpa using hfinite
    _ = ∏ k, ∑ q : Fin sl → Fin M, term k q := hfactor
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (fun p => G k p) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact (hRHS k).symm

private theorem l_dpre_repGoodProbability_eq_product {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) (N : ℕ)
    (hpool : ∀ k, 0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
      (MS.primeStage.pool N (gap k)).upper) :
    independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      ∏ k, gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let loBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).lower
  let hiBlock : Fin b → ℕ := fun k => (MS.primeStage.pool N (gap k)).upper
  let G : ∀ k : Fin b, (Fin sl → ℕ) → Prop := fun k q =>
    (T k).Good (corrScales MS) (gap k) N
      (fun j : Fin (T k).q => q ((Classical.choose (hT k)) j))
  have hlo : ∀ k : Fin b, ∀ j : Fin sl,
      lo (pkgB2_replicaEmbedding k j) = loBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).lower = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hhi : ∀ k : Fin b, ∀ j : Fin sl,
      hi (pkgB2_replicaEmbedding k j) = hiBlock k := by
    intro k j
    change (MS.primeStage.pool N
      (gap ((finProdFinEquiv (m := b) (n := sl)).symm
        (finProdFinEquiv (m := b) (n := sl) (k, j))).1)).upper = _
    rw [(finProdFinEquiv (m := b) (n := sl)).symm_apply_apply (k, j)]
  have hproject (p : Fin (b * sl) → ℕ) (k : Fin b) :
      pkgB2_repPrimeProject hT p k =
        fun j => p (pkgB2_replicaEmbedding k ((Classical.choose (hT k)) j)) := by
    funext j
    rfl
  have hfullEvent :
      (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
        (pkgB2_repPrimeProject hT p k)) =
      (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
    funext p
    apply propext
    apply forall_congr'
    intro k
    rw [hproject p k]
  have hfactor := l_dpre_independentPool_blockFactor
    lo hi loBlock hiBlock hlo hhi G
  have hmarginal (k : Fin b) :
      independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) =
        gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
    have h := independentPrimePoolProbability_iid_marginal
      (loBlock k) (hiBlock k) (hpool k) (Classical.choose (hT k))
      ((T k).Good (corrScales MS) (gap k) N)
    simpa [G, loBlock, hiBlock, gapSlotProbability, corrScales] using h.symm
  calc
    independentPrimePoolProbability lo hi
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) =
      independentPrimePoolProbability lo hi
        (fun p => ∀ k, G k (fun j => p (pkgB2_replicaEmbedding k j))) := by
          rw [hfullEvent]
    _ = ∏ k, independentPrimePoolProbability (fun _ : Fin sl => loBlock k)
          (fun _ => hiBlock k) (G k) := hfactor
    _ = _ := by
      apply Finset.prod_congr rfl
      intro k hk
      exact hmarginal k

private theorem l_dpre_repGoodProbability_lower_eventually {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (hT : ∀ k, Allowed Dm (T k)) :
    ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) ^ b ≤ independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
        (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
          (pkgB2_repPrimeProject hT p k)) := by
  have hgood (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have hlim := good_probability_tendsto_one MS (T k) (hT k) (gap k)
    exact hlim.eventually (Ioi_mem_nhds (by norm_num))
  have hpoolPos (k : Fin b) : ∀ᶠ N : ℕ in atTop,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have hratio := MS.primeStage.pool_harmonic_mass_dominates (gap k) 1 (by norm_num)
    have hlarge : ∀ᶠ N : ℕ in atTop,
        1 ≤ primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper /
            (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      simpa [pow_one] using hratio.eventually_ge_atTop (1 : ℝ)
    filter_upwards [hlarge] with N hN
    have hVpos : 0 < (masterScaleV MS.core.parameters N (gap k) : ℝ) := by
      unfold masterScaleV
      positivity
    have hmass := (le_div_iff₀ hVpos).mp hN
    have hmassPos :
        0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
          (MS.primeStage.pool N (gap k)).upper := by
      linarith
    exact hmassPos
  have hgoodAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (1 / 2 : ℝ) < gapSlotProbability (corrScales MS) (gap k) N
        ((T k).Good (corrScales MS) (gap k) N) := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hgood k)
    simpa using h
  have hpoolAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      0 < primePoolMass (MS.primeStage.pool N (gap k)).lower
        (MS.primeStage.pool N (gap k)).upper := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hpoolPos k)
    simpa using h
  filter_upwards [hgoodAll, hpoolAll] with N hgoodN hpoolN
  have hfactor := l_dpre_repGoodProbability_eq_product MS gap T hT N hpoolN
  rw [hfactor]
  calc
    (1 / 2 : ℝ) ^ b = ∏ k : Fin b, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ k, gapSlotProbability (corrScales MS) (gap k) N
          ((T k).Good (corrScales MS) (gap k) N) := by
        apply Finset.prod_le_prod₀
        · intro k hk
          norm_num
        · intro k hk
          linarith [hgoodN k]

private noncomputable def l_dpre_directionConstantBound {b : ℕ}
    (T : Fin b → CubeTemplate)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ) : ℕ := by
  classical
  exact ∑ r : pkgB2_Nonroot T,
    ((direction r 0).natAbs +
      ∑ ω : Finset (Fin (T r.1).d),
        (direction r 0 + ∑ j ∈ ω, direction r j.succ).natAbs)

private def l_dpre_momentPolynomialCoefficientMass {q : ℕ}
    (P : IntegerPolynomial q) : ℕ :=
  ∑ d ∈ P.support, (P.coeff d).natAbs

private noncomputable def l_dpre_momentShiftLengthLower {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (l : Fin K) (T : CubeTemplate) (J0 N : ℕ) : ℕ :=
  MS.core.parameters.H N l /
    (J0 * (MS.core.parameters.M N *
      ((l_dpre_momentPolynomialCoefficientMass T.D + 1) *
        ((MS.primeStage.pool N l).upper + 1) ^ T.D.totalDegree)))

private theorem l_dpre_baseRegular_of_allGood_eventually {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k) :
    ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      (∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)) →
        pkgB2_baseRegular MS B T J0 gap hT N p := by
  have hshift (k : Fin b) :
      ∀ᶠ N : ℕ in atTop,
        (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
          l_dpre_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
    exact pkgB2_shiftLengthFloor_ge_blockScale_pow MS B T J0 gap hgap hJ0 k 1
  have htrans (k : Fin b) :
      ∀ᶠ N : ℕ in atTop,
        (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
          pkgB2_translationLength MS T J0 gap k N := by
    simpa [pkgB2_translationLength] using
      (pkgB2_translationLength_ge_blockScale_pow MS B T J0 gap hgap hJ0 k 1)
  have hshiftAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
        l_dpre_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => hshift k)
    simpa using h
  have htransAll : ∀ᶠ N : ℕ in atTop, ∀ k : Fin b,
      (pkgB2_blockScale MS.core.parameters B N) ^ 1 ≤
        pkgB2_translationLength MS T J0 gap k N := by
    have h := (eventually_all_finset (Finset.univ : Finset (Fin b))).2
      (fun k _ => htrans k)
    simpa using h
  filter_upwards [hshiftAll, htransAll] with N hshiftN htransN
  intro p hpGood
  refine ⟨hpGood, ?_, ?_⟩
  · intro k
    have hactual := pkgB2_shiftLengthFloor_le_actual MS T J0 gap hJ0 N
      (fun k => pkgB2_repPrimeProject hT p k) hpGood k
    have hactual' : l_dpre_momentShiftLengthLower MS (gap k) (T k) (J0 k) N ≤
        (T k).length (corrScales MS) (gap k) (J0 k) N
          (pkgB2_repPrimeProject hT p k) := by
      exact hactual
    have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale]
      omega
    have hfloor : 0 <
        l_dpre_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
      have hk := hshiftN k
      have hk' : pkgB2_blockScale MS.core.parameters B N ≤
          l_dpre_momentShiftLengthLower MS (gap k) (T k) (J0 k) N := by
        simpa only [pow_one] using hk
      exact lt_of_lt_of_le (Nat.zero_lt_one.trans_le hV) hk'
    change 0 < (T k).length (corrScales MS) (gap k) (J0 k) N
      (pkgB2_repPrimeProject hT p k)
    exact lt_of_lt_of_le hfloor hactual'
  · intro k
    have hk := htransN k
    have hV : 1 ≤ pkgB2_blockScale MS.core.parameters B N := by
      dsimp [pkgB2_blockScale]
      omega
    have hk' : pkgB2_blockScale MS.core.parameters B N ≤
        pkgB2_translationLength MS T J0 gap k N := by
      simpa only [pow_one] using hk
    exact lt_of_lt_of_le (Nat.zero_lt_one.trans_le hV) hk'

private noncomputable def l_dpre_tailDivisorTemplate {K : ℕ} (B : Block K) :
    DivisorTemplate K K := by
  let D := HindmanSumsProducts.tailDivisorTemplate B.2.val
  exact { arity := D.arity, arity_le := D.arity_le, cutoff := D.cutoff }

private theorem l_dpre_tailDivisorTemplate_law_eq {K sl : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (N : ℕ)
    (hX : ∀ i, 4 * primorial (N + 1) ≤ MS.core.parameters.X N i) :
    divisorTemplateLaw MS.core.parameters N (l_dpre_tailDivisorTemplate B) =
      parameterTailProductLaw MS.core.parameters N B.2.val := by
  funext σ
  have h := HindmanSumsProducts.parameterTailProductLaw_eq_divisorTemplateLaw
    MS.core.parameters N B.2.val hX
  calc
    divisorTemplateLaw MS.core.parameters N (l_dpre_tailDivisorTemplate B) σ =
        FromArithmetic.divisorTemplateLaw MS.core.parameters N
          (HindmanSumsProducts.tailDivisorTemplate B.2.val) σ := rfl
    _ = FromArithmetic.parameterTailProductLaw MS.core.parameters N B.2.val σ :=
      (congrFun h σ).symm
    _ = parameterTailProductLaw MS.core.parameters N B.2.val σ := rfl

private def l_dpre_unitDivisorTemplate (K : ℕ) : DivisorTemplate K K :=
  { arity := 0, arity_le := Nat.zero_le K, cutoff := Fin.elim0 }

private noncomputable def l_dpre_divisorFamily {K q : ℕ} (B : Block K)
    (U : Finset (Fin q)) : Fin q → DivisorTemplate K K := by
  classical
  exact fun u =>
    if u ∈ U then l_dpre_tailDivisorTemplate B else l_dpre_unitDivisorTemplate K

private theorem l_dpre_divisorFamily_nuB {K sl q : ℕ} {As : Finset ℚ}
    {Dm : Finset (IntegerPolynomial sl)} (MS : MasterScales K As sl Dm)
    (B : Block K) (U : Finset (Fin q)) (u : Fin q) (N : ℕ) (y : ℤ) :
    nuB (divisorTemplateLaw MS.core.parameters N (l_dpre_divisorFamily B U u)) y =
      if u ∈ U then nu MS.core.parameters N B y else 1 := by
  classical
  by_cases hu : u ∈ U
  · simp only [l_dpre_divisorFamily, if_pos hu]
    have hLaw := l_dpre_tailDivisorTemplate_law_eq MS B N
      (MS.gapStage.valid_raw_cutoffs N)
    have h := congrArg (fun L : ℕ → ℝ => nuB L y) hLaw
    simpa [nu] using h
  · let D0 : FromArithmetic.DivisorTemplate K K :=
      { arity := 0, arity_le := Nat.zero_le K, cutoff := Fin.elim0 }
    have hFrom : nuB (FromArithmetic.divisorTemplateLaw MS.core.parameters N D0) y = 1 :=
      HindmanSumsProducts.nuB_divisorTemplate_arity_zero
        MS.core.parameters N D0 rfl y
    have hLaw :
        divisorTemplateLaw MS.core.parameters N (l_dpre_unitDivisorTemplate K) =
          FromArithmetic.divisorTemplateLaw MS.core.parameters N D0 := by
      rfl
    have hunitNu :
        nuB (divisorTemplateLaw MS.core.parameters N (l_dpre_unitDivisorTemplate K)) y = 1 := by
      have hEq := congrArg (fun L : ℕ → ℝ => nuB L y) hLaw
      exact hEq.trans hFrom
    simpa [l_dpre_divisorFamily, hu] using hunitNu

private noncomputable def l_dpre_stateMonomialAverage {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ) (hT : ∀ k, Allowed Dm (T k))
    (E : Finset (pkgB2_Nonroot T))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (N : ℕ) (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) : ℝ :=
  opus_dpo_average MS B gap T J0 hT N fun p x =>
    ∏ u ∈ U, nu MS.core.parameters N B
      (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x)

private theorem l_dpre_stateMonomialAverage_eq_wlf {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) (N : ℕ) :
    l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U =
      weightedLinearFormsAverage
          (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
            direction hdir k0 E U) N (pkgB2_goodPrimeEvent MS gap T hT N) /
        independentPrimePoolProbability
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
          (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper)
          (pkgB2_goodPrimeEvent MS gap T hT N) := by
  classical
  let D := pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
    direction hdir k0 E U
  let rootO : pkgB2_Occurrence T E := ⟨Sum.inl (), fun _ => 0⟩
  letI : Nonempty (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
    ⟨(pkgB2_occurrenceEnum T E).symm rootO⟩
  let Good := pkgB2_goodPrimeEvent MS gap T hT N
  let P := independentPrimePoolProbability
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
    (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) Good
  have hdiv (u : Fin (Fintype.card (pkgB2_Occurrence T E))) :
      D.divisor u = l_dpre_divisorFamily B U u := by
    rfl
  have hfactor (p : Fin (b * sl) → ℕ)
      (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
      ∏ u : Fin (Fintype.card (pkgB2_Occurrence T E)),
          nuB (divisorTemplateLaw MS.core.parameters N (D.divisor u))
            (linearRowValue D.rowCoeff N p u x).num =
        ∏ u ∈ U, nu MS.core.parameters N B
          (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x) := by
    calc
      _ = ∏ u : Fin (Fintype.card (pkgB2_Occurrence T E)),
            (if u ∈ U then
                nu MS.core.parameters N B
                  (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x)
              else 1) := by
              apply Finset.prod_congr rfl
              intro u hu
              rw [hdiv, l_dpre_divisorFamily_nuB]
              rfl
      _ = ∏ u ∈ U, nu MS.core.parameters N B
            (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x) := by
              rw [Finset.prod_ite_mem]
              simp
  let μp : (Fin (b * sl) → ℕ) → ℝ := fun p =>
    independentPrimePoolMass
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
      (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) p
  have houter :
      (∑' p : Fin (b * sl) → ℕ, μp p *
        (if Good p then ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x *
            ∏ u ∈ U, nu MS.core.parameters N B
              (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x)
        else 0)) = weightedLinearFormsAverage D N Good := by
    unfold weightedLinearFormsAverage
    apply tsum_congr
    intro p
    by_cases hp : Good p
    · simp only [if_pos hp, mul_one]
      apply congrArg (fun z : ℝ => μp p * z)
      apply tsum_congr
      intro x
      change pkgB2_baseMass MS B T J0 gap hT N p x *
            ∏ u ∈ U, nu MS.core.parameters N B
              (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x) =
          pkgB2_baseMass MS B T J0 gap hT N p x *
            ∏ u, nuB (divisorTemplateLaw MS.core.parameters N (D.divisor u))
              (linearRowValue D.rowCoeff N p u x).num
      rw [← hfactor p x]
    · simp only [if_neg hp, mul_zero, zero_mul]
  calc
    l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U =
        P⁻¹ * weightedLinearFormsAverage D N Good := by
          unfold l_dpre_stateMonomialAverage opus_dpo_average
          dsimp [Good, P, D]
          rw [houter]
    _ = weightedLinearFormsAverage D N Good / P := by
      rw [div_eq_mul_inv]
      ring

private theorem l_dpre_weightedGoodMonomial_tendsto_one {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) :
    Tendsto
      (fun N : ℕ =>
        weightedLinearFormsAverage
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)) /
          weightedLinearFormsEventProbability
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)))
      atTop (𝓝 1) := by
  classical
  let D := pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
    direction hdir k0 E U
  let good (N : ℕ) (p : Fin (b * sl) → ℕ) : Prop :=
    ∀ k, (T k).Good (corrScales MS) (gap k) N (pkgB2_repPrimeProject hT p k)
  let prob (N : ℕ) : ℝ := weightedLinearFormsEventProbability D N (good N)
  let average (N : ℕ) : ℝ := weightedLinearFormsAverage D N (good N)
  let c : ℝ := (1 / 2 : ℝ) ^ b
  have hc : 0 < c := by dsimp [c]; positivity
  have hgoodDomain : ∀ᶠ N : ℕ in atTop, ∀ p : Fin (b * sl) → ℕ,
      good N p → D.goodDomain N p := by
    have hreg := l_dpre_baseRegular_of_allGood_eventually MS B gap T J0 hgap hT hJ0
    have hN0 : ∀ᶠ N : ℕ in atTop,
        l_dpre_directionConstantBound T direction + 1 ≤ N :=
      eventually_ge_atTop _
    filter_upwards [hreg, hN0] with N hregN hN0 p hp
    change l_dpre_directionConstantBound T direction + 1 ≤ N ∧
      pkgB2_baseRegular MS B T J0 gap hT N p
    exact ⟨hN0, hregN p hp⟩
  obtain ⟨C, hC, hlinear⟩ := prop_linear_forms D
  have herr : Tendsto
      (fun N : ℕ => C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
        Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)))
      atTop (𝓝 0) := by
    have hCconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa using hCconst.mul (weighted_linear_forms_error_tends_zero D)
  have hlinearEventually : ∀ᶠ N : ℕ in atTop,
      |average N - prob N| ≤
        C * (1 / (N + 1 : ℝ) + (D.V N : ℝ) ^
          Fintype.card (pkgB2_Occurrence T E) * (D.epsilonBase N + D.epsilonCRT N)) := by
    filter_upwards [hgoodDomain] with N hN
    exact hlinear N (good N) (fun p hp => hN p hp)
  have habs : Tendsto (fun N => |average N - prob N|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      hlinearEventually herr
  have hrepLower : ∀ᶠ N : ℕ in atTop, c ≤
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) :=
    l_dpre_repGoodProbability_lower_eventually MS gap T hT
  have hprobEq (N : ℕ) : prob N =
      independentPrimePoolProbability
        (fun i : Fin (b * sl) =>
          (MS.primeStage.pool N (pkgB2_repGap gap i)).lower)
        (fun i => (MS.primeStage.pool N (pkgB2_repGap gap i)).upper) (good N) := by
    simp [prob, good, weightedLinearFormsEventProbability, D,
      pkgB2_weightedLinearFormsData, pkgB2_repScales, pkgB2_repScalesOfFacts]
  have hprobLower : ∀ᶠ N : ℕ in atTop, c ≤ prob N := by
    filter_upwards [hrepLower] with N hN
    rw [hprobEq]
    exact hN
  have hratioBound (N : ℕ) (hP : c ≤ prob N) :
      |average N / prob N - 1| ≤ |average N - prob N| / c := by
    have hPpos : 0 < prob N := lt_of_lt_of_le hc hP
    have heq : average N / prob N - 1 = (average N - prob N) / prob N := by
      field_simp [ne_of_gt hPpos]
    rw [heq, abs_div, abs_of_pos hPpos]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc hP
  have hratioError : Tendsto (fun N => |average N - prob N| / c) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using habs.mul_const c⁻¹
  have hratio : Tendsto (fun N => |average N / prob N - 1|) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _)
      (Filter.Eventually.mono hprobLower (fun N hP => hratioBound N hP)) hratioError
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hEq (N : ℕ) :
      (weightedLinearFormsAverage
          (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
            direction hdir k0 E U) N (good N) /
        weightedLinearFormsEventProbability
          (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
            direction hdir k0 E U) N (good N)) = average N / prob N := rfl
  simpa [Real.norm_eq_abs, D, good, average, prob] using hratio

private theorem l_dpre_stateMonomialAverage_tendsto_one {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T))
    (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E)))) :
    Tendsto (fun N => l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U)
      atTop (𝓝 1) := by
  have hlim := l_dpre_weightedGoodMonomial_tendsto_one MS B gap T J0
    hgap hT hJ0 direction hdir k0 E U
  have hEq :
      (fun N =>
        weightedLinearFormsAverage
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k)) /
          weightedLinearFormsEventProbability
            (pkgB2_weightedLinearFormsData MS B gap T J0 hgap hT hJ0
              direction hdir k0 E U) N
            (fun p => ∀ k, (T k).Good (corrScales MS) (gap k) N
              (pkgB2_repPrimeProject hT p k))) =ᶠ[atTop]
      fun N => l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U := by
    filter_upwards with N
    exact (l_dpre_stateMonomialAverage_eq_wlf MS B gap T J0 hgap hT hJ0
      direction hdir k0 E U N).symm
  exact hlim.congr' hEq

private theorem l_dpre_baseWeighted_summable {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ) (f : (Fin (Fintype.card (pkgB2_Coord T)) → ℤ) → ℝ) :
    Summable (fun x => pkgB2_baseMass MS B T J0 gap hT N p x * f x) := by
  classical
  let S := Fintype.piFinset
    (fun _ : Fin (Fintype.card (pkgB2_Coord T)) =>
      pkgB2_baseWindow MS B T J0 gap hT N p)
  apply summable_of_ne_finset_zero (s := S)
  intro x hx
  have hzero := pkgB2_baseMass_zero_outside MS B T J0 gap hT N p x (by simpa [S] using hx)
  rw [hzero]
  simp

private def l_dpre_finitePoolSupport {m : ℕ} (lo hi : Fin m → ℕ) :
    Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))

private theorem l_dpre_primePoolMass_zero_outside {m : ℕ}
    (lo hi : Fin m → ℕ) (p : Fin m → ℕ)
    (hp : p ∉ l_dpre_finitePoolSupport lo hi) :
    independentPrimePoolMass lo hi p = 0 := by
  classical
  have hnotall : ¬ ∀ i : Fin m, p i ∈ Finset.Ico (lo i) (hi i) := by
    intro hall
    apply hp
    simpa [l_dpre_finitePoolSupport] using hall
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  unfold independentPrimePoolMass
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  unfold primePoolLaw
  split_ifs with h
  · exact False.elim (hi (Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩))
  · rfl

private theorem l_dpre_primePoolMass_nonneg {m : ℕ}
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
      intro z hz
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · simp

private theorem l_dpre_primeWeighted_summable {m : ℕ}
    (lo hi : Fin m → ℕ) (f : (Fin m → ℕ) → ℝ) :
    Summable (fun p => independentPrimePoolMass lo hi p * f p) := by
  classical
  apply summable_of_ne_finset_zero (s := l_dpre_finitePoolSupport lo hi)
  intro p hp
  rw [l_dpre_primePoolMass_zero_outside lo hi p hp]
  simp

private theorem l_dpre_tendsto_finset_sum_of_pointwise {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ → ℝ) (g : α → ℝ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 (g i))) :
    Tendsto (fun n => ∑ i ∈ s, f i n) atTop (𝓝 (∑ i ∈ s, g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hf a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem l_dpre_prefactor_tendsto {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hgap : ∀ k, ValidGap B (gap k)) (hT : ∀ k, Allowed Dm (T k))
    (hJ0 : ∀ k, 0 < J0 k)
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (hdir : pkgB2_directionSpec T direction) (k0 : Fin b)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) :
    Tendsto (fun N => opus_dpo_prefactor MS B gap T J0 hT direction E s N)
      atTop (𝓝 ((2 : ℝ) ^ (Finset.univ.filter
        (fun o : Fin (Fintype.card (pkgB2_Occurrence T E)) =>
          (pkgB2_occurrenceEnum T E o).1 = Sum.inr s)).card)) := by
  classical
  let copies : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))) :=
    Finset.univ.filter fun o => (pkgB2_occurrenceEnum T E o).1 = Sum.inr s
  let lo (N : ℕ) : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi (N : ℕ) : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let good (N : ℕ) (p : Fin (b * sl) → ℕ) := pkgB2_goodPrimeEvent MS gap T hT N p
  let P (N : ℕ) := independentPrimePoolProbability (lo N) (hi N) (good N)
  let monomial (N : ℕ) (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))))
      (p : Fin (b * sl) → ℕ) (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :=
    ∏ u ∈ U, nu MS.core.parameters N B
      (pkgB2_stateRowValue MS T hT J0 gap direction E N p u x)
  have hinner (N : ℕ) (p : Fin (b * sl) → ℕ) :
      (∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
        pkgB2_baseMass MS B T J0 gap hT N p x *
          ∏ o ∈ copies, (1 + nu MS.core.parameters N B
            (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x))) =
      ∑ U ∈ copies.powerset,
        ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x * monomial N U p x := by
    have hpoint (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
        ∏ o ∈ copies, (1 + nu MS.core.parameters N B
          (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)) =
          ∑ U ∈ copies.powerset, monomial N U p x := by
      simpa [monomial] using
        (Finset.prod_one_add (s := copies) (f := fun o =>
          nu MS.core.parameters N B
            (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x)))
    have hsum := Summable.tsum_finsetSum
      (s := copies.powerset) (fun U hU =>
        l_dpre_baseWeighted_summable MS B T J0 gap hT N p (fun x => monomial N U p x))
    calc
      _ = ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x *
            ∑ U ∈ copies.powerset, monomial N U p x := by
              apply tsum_congr
              intro x
              rw [hpoint]
      _ = ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          ∑ U ∈ copies.powerset,
            pkgB2_baseMass MS B T J0 gap hT N p x * monomial N U p x := by
              apply tsum_congr
              intro x
              rw [Finset.mul_sum]
      _ = _ := hsum
  have houter (N : ℕ) :
      (∑' p : Fin (b * sl) → ℕ,
        independentPrimePoolMass (lo N) (hi N) p *
          (if good N p then
            ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
              pkgB2_baseMass MS B T J0 gap hT N p x *
                ∏ o ∈ copies, (1 + nu MS.core.parameters N B
                  (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x))
           else 0)) =
      ∑ U ∈ copies.powerset,
        ∑' p : Fin (b * sl) → ℕ,
          independentPrimePoolMass (lo N) (hi N) p *
            (if good N p then
              ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
                pkgB2_baseMass MS B T J0 gap hT N p x * monomial N U p x
             else 0) := by
    let term (U : Finset (Fin (Fintype.card (pkgB2_Occurrence T E))))
        (p : Fin (b * sl) → ℕ) :=
      if good N p then
        ∑' x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ,
          pkgB2_baseMass MS B T J0 gap hT N p x * monomial N U p x
      else 0
    have hsum := Summable.tsum_finsetSum
      (s := copies.powerset) (fun U hU =>
        l_dpre_primeWeighted_summable (lo N) (hi N) (fun p => term U p))
    calc
      _ = ∑' p : Fin (b * sl) → ℕ,
          independentPrimePoolMass (lo N) (hi N) p *
            ∑ U ∈ copies.powerset, term U p := by
              apply tsum_congr
              intro p
              by_cases hp : good N p
              · rw [if_pos hp, hinner]
                congr 1
                apply Finset.sum_congr rfl
                intro U hU
                simp [term, hp]
              · simp [term, hp]
      _ = ∑' p : Fin (b * sl) → ℕ,
          ∑ U ∈ copies.powerset,
            independentPrimePoolMass (lo N) (hi N) p * term U p := by
              apply tsum_congr
              intro p
              rw [Finset.mul_sum]
      _ = _ := hsum
  have hsumMono : Tendsto
      (fun N => ∑ U ∈ copies.powerset,
        l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U)
      atTop (𝓝 ((2 : ℝ) ^ copies.card)) := by
    have h := l_dpre_tendsto_finset_sum_of_pointwise copies.powerset
      (fun U N => l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U)
      (fun _ => (1 : ℝ)) (by
        intro U hU
        exact l_dpre_stateMonomialAverage_tendsto_one MS B gap T J0
          hgap hT hJ0 direction hdir k0 E U)
    simpa [Finset.card_powerset] using h
  have hEq :
      (fun N => opus_dpo_prefactor MS B gap T J0 hT direction E s N) =
        fun N => ∑ U ∈ copies.powerset,
          l_dpre_stateMonomialAverage MS B gap T J0 hT E direction N U := by
    funext N
    have houterN := houter N
    unfold opus_dpo_prefactor opus_dpo_average
    dsimp [lo, hi, good, P]
    rw [houterN]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    unfold l_dpre_stateMonomialAverage opus_dpo_average
    dsimp [lo, hi, good, monomial]
  rw [hEq]
  exact hsumMono

private theorem l_dpre_baseMass_nonneg {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (T : Fin b → CubeTemplate)
    (J0 : Fin b → ℕ) (gap : Fin b → Fin K) (hT : ∀ k, Allowed Dm (T k))
    (N : ℕ) (p : Fin (b * sl) → ℕ)
    (x : Fin (Fintype.card (pkgB2_Coord T)) → ℤ) :
    0 ≤ pkgB2_baseMass MS B T J0 gap hT N p x := by
  classical
  by_cases hreg : pkgB2_baseRegular MS B T J0 gap hT N p
  · simp [pkgB2_baseMass, hreg]
    apply Finset.prod_nonneg
    intro i hi
    exact pkgB2_baseCoordinateLaw_nonneg MS B T J0 gap hT N p
      (pkgB2_coordEnum T i) (x i)
  · by_cases hx : x = 0 <;> simp [pkgB2_baseMass, hreg, hx]

theorem l_dpre_prefactor_nonneg {K sl b : ℕ}
    {As : Finset ℚ} {Dm : Finset (IntegerPolynomial sl)}
    (MS : MasterScales K As sl Dm) (B : Block K) (gap : Fin b → Fin K)
    (T : Fin b → CubeTemplate) (J0 : Fin b → ℕ)
    (hT : ∀ k, Allowed Dm (T k))
    (direction : ∀ r : pkgB2_Nonroot T, Fin ((T r.1).d + 1) → ℤ)
    (E : Finset (pkgB2_Nonroot T)) (s : pkgB2_Nonroot T) (N : ℕ) :
    0 ≤ opus_dpo_prefactor MS B gap T J0 hT direction E s N := by
  classical
  let lo : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).lower
  let hi : Fin (b * sl) → ℕ := fun i =>
    (MS.primeStage.pool N (pkgB2_repGap gap i)).upper
  let Good := pkgB2_goodPrimeEvent MS gap T hT N
  unfold opus_dpo_prefactor opus_dpo_average
  apply mul_nonneg
  · exact inv_nonneg.mpr (independentPrimePoolProbability_nonneg lo hi Good)
  · apply tsum_nonneg
    intro p
    apply mul_nonneg
    · exact l_dpre_primePoolMass_nonneg lo hi p
    · by_cases hp : Good p
      · simp only [Good, if_pos hp]
        apply tsum_nonneg
        intro x
        apply mul_nonneg
        · exact l_dpre_baseMass_nonneg MS B T J0 gap hT N p x
        · apply Finset.prod_nonneg
          intro o ho
          exact add_nonneg (by norm_num)
            (pkgB_nu_nonneg MS.core.parameters N B
              (pkgB2_stateRowValue MS T hT J0 gap direction E N p o x))
      · simp [Good, hp]

end
end Prediction
end HindmanSumsProducts
